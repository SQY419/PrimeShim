package dev.primeshim.android;

import android.content.Context;
import android.content.res.AssetManager;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;
import android.graphics.Rect;
import android.graphics.RectF;
import android.graphics.RectF;
import android.util.Log;
import android.view.HapticFeedbackConstants;
import android.view.MotionEvent;
import android.view.View;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

/**
 * On-screen HP Prime keyboard built from the skin shipped in the official
 * com.hp.primecalculator application.
 *
 * Everything is expressed as a fraction of the skin bitmap, so it does not
 * matter whether the decoder hands us 1440x2560 or any other size: geometry and
 * hit testing stay in the same coordinate space.
 *
 * The skin's own numeric key codes are not the codes this shim expects, so keys
 * are mapped by name (falling back to the trailing #comment):
 *
 *   key12=12,513,911,568,1008,"down",{40},{},{},["d""D"] #down
 *                                          ^^ skin code    ^^^^ name
 */
public final class PrimeKeyboardView extends View {

    private static final String TAG = "PrimeKbd";

    /* The skin these coordinates were authored against. */
    private static final float SKIN_WIDTH = 1440f;
    private static final float SKIN_HEIGHT = 2560f;

    /* The .skin file uses its own coordinate space, ~1.35x smaller than the
     * shipped bitmap, so rectangles are normalised against the range the file
     * actually spans and mapped onto the measured key area of the bitmap. */
    private static final float SKIN_X0 = 66f;
    private static final float SKIN_Y0 = 742f;
    private static final float SKIN_X1 = 1013f;
    private static final float SKIN_Y1 = 1907f;

    private static final class Key {
        final float left, top, right, bottom; /* 0..1 inside the skin */
        final int code;
        final String name;

        Key(float left, float top, float right, float bottom, int code, String name) {
            this.left = left;
            this.top = top;
            this.right = right;
            this.bottom = bottom;
            this.code = code;
            this.name = name;
        }
    }

    private final List<Key> keys = new ArrayList<>();
    private final Rect source = new Rect();
    private final Rect destination = new Rect();
    private final Paint paint = new Paint(Paint.FILTER_BITMAP_FLAG);
    private Paint kEchoPaint;
    private Bitmap skin;
    private int pressedCode = -1;
    private int pressedIndex = -1;
    /** Shows "name 0xNN" for the last press so the mapping can be verified. */
    private String keyEcho = null;
    /** Whether the "name 0xNN" line is drawn after a press (debug aid). */
    private boolean keyEchoEnabled = false;
    private boolean hapticFeedbackEnabled = false;
    private String pressedName;
    private float lastScale;
    /** Red frame, magenta dots, pressed label: development aids, off by default. */
    private boolean debugOverlay = false;

    public PrimeKeyboardView(Context context) {
        super(context);
        setFocusable(false);
        /* The skin PNG is transparent around the keys; the official calculator
         * has a black keyboard bed, so let the black background show through. */
        setBackgroundColor(Color.BLACK);
        loadSkin();
    }

    /** Half the screen, shared with the activity so both agree. */
    public static int preferredHeight(Context context) {
        return (int) (context.getResources().getDisplayMetrics().heightPixels * 0.5f);
    }

    private void loadSkin() {
        AssetManager assets = getContext().getAssets();
        try {
            skin = BitmapFactory.decodeStream(assets.open("portrait_skin.png"));
        } catch (Exception error) {
            Log.w(TAG, "asset skin missing, falling back to the packaged resource", error);
        }
        if (skin == null) {
            skin = BitmapFactory.decodeResource(getResources(), R.drawable.portrait_skin);
        }
        if (skin != null) {
            skin.setDensity(Bitmap.DENSITY_NONE);
            measureContentBox();
            Log.i(TAG, "skin bitmap " + skin.getWidth() + "x" + skin.getHeight()
                    + " density=" + skin.getDensity());
        }

        Map<String, Integer> codes = buildKeyMap();
        try {
            BufferedReader reader = new BufferedReader(
                    new InputStreamReader(assets.open("hp_keyboard.skin"), "ISO-8859-1"));
            String line;
            while ((line = reader.readLine()) != null) {
                parseKey(line, codes);
            }
            reader.close();
        } catch (Exception error) {
            Log.e(TAG, "cannot read the skin description", error);
        }
        Log.i(TAG, "loaded " + keys.size() + " keys");
    }

    private void parseKey(String line, Map<String, Integer> codes) {
        if (line == null || !line.startsWith("key")) return;

        int hash = line.indexOf('#');
        String comment = hash >= 0 ? line.substring(hash + 1).trim() : "";

        String[] fields = line.split(",");
        if (fields.length < 6) return;

        String name = fields[5].replace("\"", "").trim();
        Integer code = codes.get(comment);
        if (code == null) code = codes.get(name);
        if (code == null) {
            Log.i(TAG, "unmapped key name='" + name + "' comment='" + comment + "'");
            return;
        }

        try {
            float x1 = (Float.parseFloat(fields[1].trim()) - SKIN_X0) / (SKIN_X1 - SKIN_X0);
            float y1 = (Float.parseFloat(fields[2].trim()) - SKIN_Y0) / (SKIN_Y1 - SKIN_Y0);
            float x2 = (Float.parseFloat(fields[3].trim()) - SKIN_X0) / (SKIN_X1 - SKIN_X0);
            float y2 = (Float.parseFloat(fields[4].trim()) - SKIN_Y0) / (SKIN_Y1 - SKIN_Y0);
            keys.add(new Key(x1, y1, x2, y2, code,
                    name.isEmpty() ? comment : name));
        } catch (NumberFormatException error) {
            Log.w(TAG, "bad key line: " + line);
        }
    }

    /** Skin names to the key codes PrimeShim's shim understands. */
    /** Key codes as the firmware itself numbers them.  The top cluster was
     *  verified key by key on the device (esc=0x01, left=0x02, up=0x03,
     *  right=0x04, down=0x05, help=0x95, plot=0xB2, views=0xB4, home=0xE047,
     *  1e/EEX=0x50) and the function row is contiguous from ^ = 0x46. */
    /** Resolve a script key name, or a numeric/hex code as a fallback. */
    public static int codeForName(String name) {
        if (name == null) return -1;
        Integer mapped = buildKeyMap().get(name.toLowerCase(Locale.US));
        if (mapped != null) return mapped;
        try {
            return Integer.decode(name);
        } catch (NumberFormatException ignored) {
            return -1;
        }
    }

    public static String[] keyNames() {
        return buildKeyMap().keySet().toArray(new String[0]);
    }

    private static Map<String, Integer> buildKeyMap() {
        Map<String, Integer> map = new HashMap<>();
        map.put("apps", 0xB1);
        map.put("symb", 0x91);
        map.put("help", 0x95);
        map.put("esc", 0x1);
        map.put("plot", 0xB2);
        map.put("views", 0xB4);
        map.put("cas", 0xB5);
        map.put("num", 0xB3);
        map.put("menu", 0x93);
        map.put("up", 0x3);
        map.put("down", 0x5);
        map.put("left", 0x2);
        map.put("right", 0x4);
        map.put("home", 0xE047);
        map.put("vars", 0x41);
        map.put("math", 0x42);
        map.put("templ", 0x43);
        map.put("xttn", 0x44);
        map.put("frac", 0x45);
        map.put("bksp", 0x0C);
        map.put("^", 0x46);
        map.put("sin", 0x47);
        map.put("cos", 0x48);
        map.put("tan", 0x49);
        map.put("ln", 0x4A);
        map.put("log", 0x4B);
        map.put("x^2", 0x4C);
        map.put("²", 0x4C);
        map.put("chs", 0x4D);
        map.put("(", 0x4E);   /* the real () key: one press gives a pair */
        map.put(")", 0x4F);   /* this rect is the comma key on the real keyboard */
        map.put("comma", 0x50);   /* this rect is physically the EEX/STO key */
        map.put("enter", 0xD);
        map.put("sto", 0xB6);
        map.put("alpha", 0x8B);
        map.put("shift", 0x83);
        map.put("7", 0x51);
        map.put("8", 0x52);
        map.put("9", 0x53);
        map.put("/", 0x54);
        map.put("4", 0x55);
        map.put("5", 0x56);
        map.put("6", 0x57);
        map.put("*", 0x58);
        map.put("1", 0x59);
        map.put("2", 0x5A);
        map.put("3", 0x33);
        map.put("minus", 0xB7);
        map.put("0", 0x30);
        map.put("dot", 0xB8);
        map.put("space", 0x20);
        map.put("+", 0xB9);
        map.put("div", 0x54);
        map.put("mult", 0x58);
        map.put("plus", 0xB9);
        map.put("min", 0xB7);
        map.put("dot2", 0xB8);
        return map;
    }


    /** Convert a Prime key code into the value this firmware expects.
     *
     * Empirically the firmware looks the code up 0x24 higher, which is why
     * 0x59 ("1") arrives as "1" only after subtracting: the raw value produced
     * other keys.  A few codes sit in a different region and need explicit
     * anchors (digits 0 and 3, plus the special keys that never took the
     * offset).
     */
    /** Codes go to the firmware untouched. */
    /** Codes go to the firmware untouched. */
    private static int wireCode(int code) {
        return code;
    }

    @Override
    protected void onMeasure(int widthSpec, int heightSpec) {
        int width = MeasureSpec.getSize(widthSpec);
        /* Honour an exact height from the layout; only fall back to our own
         * preference when the parent asks us to wrap content. */
        int height = MeasureSpec.getMode(heightSpec) == MeasureSpec.EXACTLY
                ? MeasureSpec.getSize(heightSpec)
                : preferredHeight(getContext());
        setMeasuredDimension(width, height);
    }

    private final Rect contentBox = new Rect();

    /** Find the pixels the key artwork occupies, ignoring the empty header. */
    private void measureContentBox() {
        int width = skin.getWidth();
        int height = skin.getHeight();
        int minX = width, maxX = 0, minY = height, maxY = 0;
        int[] row = new int[width];
        for (int y = (int) (height * 0.3f); y < height; ++y) {
            skin.getPixels(row, 0, width, 0, y, width, 1);
            for (int x = 0; x < width; ++x) {
                int pixel = row[x];
                int rgb = (pixel & 0xFF) + ((pixel >> 8) & 0xFF) + ((pixel >> 16) & 0xFF);
                if (rgb > 60) {
                    if (x < minX) minX = x;
                    if (x > maxX) maxX = x;
                    if (y < minY) minY = y;
                    if (y > maxY) maxY = y;
                }
            }
        }
        if (maxX <= minX || maxY <= minY) {
            contentBox.set(0, (int) (height * 0.3f), width, height);
        } else {
            contentBox.set(minX, minY, maxX + 1, maxY + 1);
        }
        Log.i(TAG, "content box " + contentBox.toShortString());
    }

    /** Pre-scaled copy of the key area, rebuilt when the view size changes. */
    private Bitmap scaledSkin;
    private int scaledWidth;
    private int scaledHeight;

    private void rebuildScaledSkin() {
        if (skin == null || getWidth() <= 0 || getHeight() <= 0) return;
        int cropLeft = contentBox.left;
        int cropTop = contentBox.top;
        int cropWidth = contentBox.width();
        int cropHeight = contentBox.height();
        if (cropWidth <= 0 || cropHeight <= 0) return;

        /* Fill the whole view: the bottom row used to end up outside the
         * touchable area, which is why "0" and "+" did nothing. */
        int width = Math.max(1, getWidth());
        int height = Math.max(1, getHeight());
        if (scaledSkin != null && width == scaledWidth && height == scaledHeight) return;

        Bitmap cropped = Bitmap.createBitmap(skin, cropLeft, cropTop, cropWidth, cropHeight);
        scaledSkin = Bitmap.createScaledBitmap(cropped, width, height, true);
        cropped.recycle();
        scaledSkin.setDensity(Bitmap.DENSITY_NONE);
        scaledWidth = width;
        scaledHeight = height;
    }

    private void layoutDestination() {
        int viewWidth = getWidth();
        int viewHeight = getHeight();
        if (viewWidth <= 0 || viewHeight <= 0 || skin == null) {
            destination.setEmpty();
            source.setEmpty();
            return;
        }
        int cropWidth = contentBox.width();
        int cropHeight = contentBox.height();
        if (cropWidth <= 0 || cropHeight <= 0) {
            destination.setEmpty();
            source.setEmpty();
            return;
        }
        destination.set(0, 0, viewWidth, viewHeight);
        source.set(contentBox);
        lastScale = 1.0f;
    }

    @Override
    protected void onDraw(Canvas canvas) {
        if (skin == null) return;
        layoutDestination();
        rebuildScaledSkin();
        if (scaledSkin != null && !destination.isEmpty()) {
            /* Plain blit of a pre-scaled bitmap: no canvas transform, so no
             * density or scale surprises. */
            canvas.drawBitmap(scaledSkin, destination.left, destination.top, paint);
        if (kEchoPaint == null) {
            kEchoPaint = new Paint();
            kEchoPaint.setColor(Color.rgb(255, 96, 0));
            kEchoPaint.setTextSize(28f);
            kEchoPaint.setAntiAlias(true);
        }
        if (keyEchoEnabled && keyEcho != null) canvas.drawText(keyEcho, 12, 34, kEchoPaint);
        }

        if (debugOverlay) {
        /* Probe: red frame on the destination rect plus a solid marker at its
         * top-left corner, so a screenshot shows whether the canvas is scaled
         * relative to the view. */
        Paint frame = new Paint();
        frame.setColor(0xFFFF0000);
        frame.setStyle(Paint.Style.STROKE);
        frame.setStrokeWidth(3f);
        canvas.drawRect(destination, frame);
        frame.setStyle(Paint.Style.FILL);
        canvas.drawRect(destination.left, destination.top,
                        destination.left + 16, destination.top + 16, frame);
        canvas.drawRect(destination.right - 16, destination.bottom - 16,
                        destination.right, destination.bottom, frame);

        /* Calibration dots: one magenta dot per key at the point the hit test
         * believes is its centre. */
        if (pressedIndex >= 0) {
            Key k = keys.get(pressedIndex);
            Paint hi = new Paint();
            hi.setColor(0x8000FF00);
            hi.setStyle(Paint.Style.FILL);
            RectF box = new RectF(
                    destination.left + k.left * destination.width(),
                    destination.top + k.top * destination.height(),
                    destination.left + k.right * destination.width(),
                    destination.top + k.bottom * destination.height());
            canvas.drawRect(box, hi);
        }
        if (pressedName != null) {
            Paint label = new Paint();
            label.setColor(0xFFFFFF00);
            label.setTextSize(26f);
            canvas.drawText("pressed: " + pressedName, 10, getHeight() - 14, label);
        }

        if (true) {
            Paint dot = new Paint();
            dot.setColor(0xFFFF00FF);
            dot.setStyle(Paint.Style.FILL);
            for (Key k : keys) {
                float cx = destination.left
                        + ((k.left + k.right) * 0.5f) * destination.width();
                float cy = destination.top
                        + ((k.top + k.bottom) * 0.5f) * destination.height();
                canvas.drawCircle(cx, cy, 5f, dot);
            }
        }

        Paint text = new Paint();
        text.setColor(0xFF00FF00);
        text.setTextSize(18f);
        canvas.drawText("view " + getWidth() + "x" + getHeight()
                        + " canvas " + canvas.getWidth() + "x" + canvas.getHeight()
                        + " bmp " + skin.getWidth() + "x" + skin.getHeight()
                        + " dst " + destination.width() + "x" + destination.height(),
                8, 24, text);
        }
    }

    /** Read-only accessors used by the calibration sweep. */
    public void setDebugOverlay(boolean enabled) {
        debugOverlay = enabled;
        invalidate();
    }

    public boolean isDebugOverlay() { return debugOverlay; }

    public void setKeyEchoEnabled(boolean enabled) {
        keyEchoEnabled = enabled;
        if (!enabled) keyEcho = null;
        invalidate();
    }

    public boolean isKeyEchoEnabled() { return keyEchoEnabled; }

    public void setHapticFeedbackEnabled(boolean enabled) {
        hapticFeedbackEnabled = enabled;
    }

    public boolean isHapticFeedbackEnabled() { return hapticFeedbackEnabled; }

    public int keyCount() { return keys.size(); }
    public String keyNameAt(int index) { return keys.get(index).name; }
    public int keyCodeAt(int index) { return keys.get(index).code; }
    public static int wire(int code) { return wireCode(code); }

    private int keyAt(float x, float y) {
        /* Recompute here: relying on the value left by the last onDraw made the
         * hit test use a stale (smaller) rectangle after a resize. */
        rebuildScaledSkin();
        layoutDestination();
        if (destination.isEmpty()) return -1;
        float nx = (x - destination.left) / destination.width();
        float ny = (y - destination.top) / destination.height();
        for (int i = 0; i < keys.size(); ++i) {
            Key k = keys.get(i);
            if (nx >= k.left && nx <= k.right && ny >= k.top && ny <= k.bottom) {
                Log.i(TAG, "hit x=" + x + " y=" + y + " n=" + nx + "," + ny
                        + " key=" + i + " code=0x" + Integer.toHexString(k.code));
                return i;
            }
        }
        Log.i(TAG, "miss x=" + x + " y=" + y + " n=" + nx + "," + ny);
        return -1;
    }

    @Override
    public boolean onTouchEvent(MotionEvent event) {
        switch (event.getActionMasked()) {
            case MotionEvent.ACTION_DOWN: {
                int index = keyAt(event.getX(), event.getY());
                if (index >= 0) {
                    Key k = keys.get(index);
                    pressedCode = k.code;
                    pressedIndex = index;
                    pressedName = k.name;
                    invalidate();
                    if (keyEchoEnabled) keyEcho = k.name + "  0x" + Integer.toHexString(wireCode(pressedCode)).toUpperCase();
                    invalidate();
                    PrimeShim.nativeKeyBatch(wireCode(pressedCode), 1);
                    if (hapticFeedbackEnabled) {
                        performHapticFeedback(HapticFeedbackConstants.KEYBOARD_TAP,
                                HapticFeedbackConstants.FLAG_IGNORE_GLOBAL_SETTING);
                    }
                }
                return true;
            }
            case MotionEvent.ACTION_MOVE: {
                if (pressedCode < 0) return true;
                if (keyAt(event.getX(), event.getY()) < 0) {
                    PrimeShim.nativeKeyBatch(wireCode(pressedCode), 0);
                    pressedCode = -1;
                    pressedIndex = -1;
                }
                return true;
            }
            case MotionEvent.ACTION_UP:
            case MotionEvent.ACTION_CANCEL: {
                if (pressedCode >= 0) {
                    PrimeShim.nativeKeyBatch(wireCode(pressedCode), 0);
                    pressedCode = -1;
                    pressedIndex = -1;
                    invalidate();
                }
                return true;
            }
            default:
                return super.onTouchEvent(event);
        }
    }
}
