package dev.primeshim.android;

import android.app.AlarmManager;
import android.app.PendingIntent;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.ContentValues;
import android.content.Context;
import android.content.Intent;
import android.content.res.AssetManager;
import android.animation.ValueAnimator;
import android.content.res.ColorStateList;
import android.graphics.Bitmap;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;
import android.graphics.Rect;
import android.graphics.Typeface;
import android.graphics.drawable.ColorDrawable;
import android.graphics.drawable.RippleDrawable;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.Looper;
import android.provider.MediaStore;
import android.text.Editable;
import android.text.InputType;
import android.text.TextWatcher;
import android.util.Log;
import android.util.SparseIntArray;
import android.util.TypedValue;
import android.view.Gravity;
import android.view.HapticFeedbackConstants;
import android.view.KeyEvent;
import android.view.MotionEvent;
import android.view.SurfaceHolder;
import android.view.SurfaceView;
import android.view.View;
import android.view.ViewGroup;
import android.view.WindowManager;
import android.view.animation.DecelerateInterpolator;
import android.widget.EditText;
import android.widget.FrameLayout;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.ScrollView;
import android.widget.TextView;

import androidx.appcompat.app.AppCompatDelegate;
import androidx.core.view.ViewCompat;
import androidx.core.view.WindowInsetsCompat;

import com.google.android.material.appbar.MaterialToolbar;
import com.google.android.material.bottomsheet.BottomSheetDialog;
import com.google.android.material.bottomsheet.BottomSheetDragHandleView;
import com.google.android.material.button.MaterialButton;
import com.google.android.material.card.MaterialCardView;
import com.google.android.material.color.MaterialColors;
import com.google.android.material.dialog.MaterialAlertDialogBuilder;
import com.google.android.material.divider.MaterialDivider;
import com.google.android.material.materialswitch.MaterialSwitch;
import com.google.android.material.slider.LabelFormatter;
import com.google.android.material.slider.Slider;
import com.google.android.material.snackbar.Snackbar;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.security.MessageDigest;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

/**
 * Hosts the HP Prime firmware inside a SurfaceView.
 *
 * Java owns the lifecycle, input translation and the on-screen log viewer; the
 * native library owns the guest, the patcher and the framebuffer.
 *
 * The firmware is not distributed with the app.  On first launch the activity
 * asks for an official HP Prime update package (zip) or PRIME_APP.DAT and
 * extracts both the ARM ELF and the A: FAT16 volume into a per-firmware
 * profile.  C: starts empty and can be restored from a user backup.
 */
public final class MainActivity extends androidx.appcompat.app.AppCompatActivity
        implements SurfaceHolder.Callback, Runnable {

    private static final String TAG = "PrimeShim";

    /** Native firmware resolution. */
    private static final int FW_WIDTH = 320;
    private static final int FW_HEIGHT = 240;

    private static final String WORK_DIR_NAME = "prime";
    private static final String FIRMWARE_NAME = "armfir.elf";

    /** An ARM Prime firmware is several megabytes; anything tiny is not one. */
    private static final long MIN_FIRMWARE_BYTES = 1L << 20;

    private static final int REQUEST_FIRMWARE = 1001;
    private static final int REQUEST_DATA_IMPORT = 1003;
    private static final int REQUEST_BACKUP_EXPORT = 1004;
    private static final int REQUEST_FM_IMPORT = 1005;
    private static final int REQUEST_FM_EXPORT = 1006;
    private static final int REQUEST_SCRIPT_IMPORT = 1007;
    private static final int REQUEST_SCRIPT_EXPORT = 1008;

    /** Restart after importing/clearing: the system splash is enough, do not
     *  play the in-app logo animation a second time. */
    private static final String EXTRA_SKIP_SPLASH =
            "dev.primeshim.android.SKIP_SPLASH";
    private static final String EXTRA_REVEAL_X =
            "dev.primeshim.android.REVEAL_X";
    private static final String EXTRA_REVEAL_Y =
            "dev.primeshim.android.REVEAL_Y";
    private static final String EXTRA_REVEAL_COLOR =
            "dev.primeshim.android.REVEAL_COLOR";

    private SurfaceView surfaceView;
    private SplashView splash;
    private int speedPercent = 100;
    private CrosshairView crosshair;
    private FrameLayout root;
    private ScriptRuntime scriptRuntime;
    private CodeEditorView scriptEditor;
    private TextView terminalText;
    private ScrollView terminalScroll;
    private LinearLayout terminalPage;
    private final StringBuilder terminalBuffer = new StringBuilder();
    private String scriptExportText;
    private LinearLayout docList;
    private List<ScriptDocs.Entry> docEntries;

    /** Android pointer id -> firmware touch slot (0..7). */
    private final SparseIntArray touchSlots = new SparseIntArray();

    /** Firmware-missing overlay: MD3 scrim plus a filled card. */
    private FrameLayout overlay;
    private MaterialCardView statusCard;
    private TextView statusView;
    private MaterialButton pickButton;
    private MaterialButton dismissButton;

    /** Floating menu affordance over the LCD (animated hamburger). */
    private MaterialCardView menuButton;
    private MenuIconView menuIcon;
    private boolean menuDragging;
    private float menuDownRawX;
    private float menuDownRawY;
    private int menuDownLeft;
    private int menuDownTop;

    private LinearLayout logPanel;
    private TextView logText;
    private ScrollView logScroll;

    private PrimeKeyboardView keyboardView;
    private File workDir;
    private File firmwareFile;
    private File profilesDir;
    private String activeProfile;

    /** Supporting line of the L.t("模拟速度") row, kept in sync with the slider. */
    private TextView speedSummary;

    private volatile boolean surfaceReady;
    private volatile boolean guestStarted;
    /** Process-wide: an Activity recreation must not start a second guest. */
    private static boolean nativeGuestRunning;
    private boolean traceEnabled = false;
    private boolean crashShown;
    /** Set while a profile is being replaced or the process is restarting. */
    private volatile boolean suppressCrash;

    private final Handler uiHandler = new Handler(Looper.getMainLooper());
    private final Runnable guestCrashWatch = new Runnable() {
        @Override
        public void run() {
            if (crashShown || suppressCrash) return;
            int signal;
            try {
                signal = PrimeShim.nativeCrashSignal();
            } catch (Throwable error) {
                signal = 0;
            }
            if (signal != 0) {
                crashShown = true;
                String report = PrimeShim.nativeCrashReport();
                if (report == null || report.isEmpty()) {
                    report = L.t("固件线程异常退出 signal ") + signal + "。";
                }
                settings().edit()
                        .putBoolean("guestCrashed", true)
                        .putString("lastCrash", report)
                        .apply();
                refreshLog();
                showGuestCrash(report);
                return;
            }
            uiHandler.postDelayed(this, 1000);
        }
    };
    private final Runnable logRefresh = new Runnable() {
        @Override
        public void run() {
            refreshLog();
            if (logPanel != null && logPanel.getVisibility() == View.VISIBLE) {
                uiHandler.postDelayed(this, 1000);
            }
        }
    };

    @Override
    protected void attachBaseContext(Context newBase) {
        L.init(newBase);
        android.content.res.Configuration config =
                new android.content.res.Configuration(
                        newBase.getResources().getConfiguration());
        config.fontScale = newBase.getSharedPreferences(
                "primeshim", MODE_PRIVATE).getFloat("fontScale", 1f);
        config.setLocale(L.locale());
        super.attachBaseContext(newBase.createConfigurationContext(config));
    }

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        androidx.core.view.WindowCompat.setDecorFitsSystemWindows(getWindow(), false);
        androidx.core.view.WindowInsetsControllerCompat bars =
                androidx.core.view.WindowCompat.getInsetsController(getWindow(),
                        getWindow().getDecorView());
        bars.hide(androidx.core.view.WindowInsetsCompat.Type.systemBars());
        bars.setSystemBarsBehavior(
                androidx.core.view.WindowInsetsControllerCompat.BEHAVIOR_SHOW_TRANSIENT_BARS_BY_SWIPE);

        speedPercent = settings().getInt("speed", 100);
        traceEnabled = settings().getBoolean("trace", false);

        root = new FrameLayout(this);
        root.setBackgroundColor(themeColor(
                com.google.android.material.R.attr.colorSurface));

        surfaceView = new SurfaceView(this);
        surfaceView.getHolder().addCallback(this);
        surfaceView.setFocusable(true);
        surfaceView.setFocusableInTouchMode(true);
        surfaceView.setOnTouchListener(new View.OnTouchListener() {
            @Override
            public boolean onTouch(View view, MotionEvent event) {
                return handleTouch(event);
            }
        });
        root.addView(surfaceView, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT));

        crosshair = new CrosshairView(this);
        crosshair.setVisibility(View.GONE);
        root.addView(crosshair, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT));

        /* No firmware yet: MD3 scrim (32% black) with a filled card, instead of
         * the old nearly-opaque black sheet. */
        overlay = new FrameLayout(this);
        overlay.setBackgroundColor(0x52000000);
        overlay.setClickable(true);
        overlay.setVisibility(View.GONE);

        statusCard = filledCard();
        LinearLayout statusContent = new LinearLayout(this);
        statusContent.setOrientation(LinearLayout.VERTICAL);
        statusContent.setPadding(dp(24), dp(24), dp(24), dp(24));

        statusView = new TextView(this);
        applyTextAppearance(statusView,
                com.google.android.material.R.attr.textAppearanceBodyLarge);
        statusView.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        statusView.setGravity(Gravity.START);
        statusView.setLineSpacing(dp(3), 1f);
        statusContent.addView(statusView, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        pickButton = filledButton(L.t("导入官方固件"), view -> pickFirmware());
        LinearLayout.LayoutParams buttonParams = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.WRAP_CONTENT,
                LinearLayout.LayoutParams.WRAP_CONTENT);
        buttonParams.gravity = Gravity.CENTER_HORIZONTAL;
        buttonParams.topMargin = dp(24);
        statusContent.addView(pickButton, buttonParams);

        dismissButton = textButton(L.t("关闭"), view -> overlay.setVisibility(View.GONE));
        LinearLayout.LayoutParams dismissParams = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.WRAP_CONTENT,
                LinearLayout.LayoutParams.WRAP_CONTENT);
        dismissParams.gravity = Gravity.CENTER_HORIZONTAL;
        dismissParams.topMargin = dp(8);
        statusContent.addView(dismissButton, dismissParams);
        statusCard.addView(statusContent, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.WRAP_CONTENT));

        int cardWidth = Math.min(
                getResources().getDisplayMetrics().widthPixels - dp(48), dp(420));
        overlay.addView(statusCard, new FrameLayout.LayoutParams(
                Math.max(dp(200), cardWidth),
                FrameLayout.LayoutParams.WRAP_CONTENT,
                Gravity.CENTER));
        root.addView(overlay, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT));

        keyboardView = new PrimeKeyboardView(this);
        keyboardView.setVisibility(View.GONE);
        keyboardView.setHapticFeedbackEnabled(settings().getBoolean("haptic", false));
        int keyboardHeight = (int) (getResources().getDisplayMetrics().heightPixels * 0.52f);
        root.addView(keyboardView, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                keyboardHeight,
                Gravity.BOTTOM));

        /* The only chrome on the calculator screen: a Material 3 filled tonal
         * icon button, inset from the display cutout. */
        menuButton = new MaterialCardView(this);
        menuButton.setRadius(dp(20));
        menuButton.setCardElevation(dp(1));
        menuButton.setCardBackgroundColor(themeColor(
                com.google.android.material.R.attr.colorSecondaryContainer));
        menuButton.setRippleColor(ColorStateList.valueOf(
                (themeColor(com.google.android.material.R.attr.colorOnSecondaryContainer)
                        & 0x00FFFFFF) | 0x1F000000));
        menuButton.setClickable(true);
        menuButton.setFocusable(true);
        menuButton.setContentDescription(L.t("菜单"));

        menuIcon = new MenuIconView(this);
        menuIcon.setColor(themeColor(
                com.google.android.material.R.attr.colorOnSecondaryContainer));
        menuButton.addView(menuIcon, new FrameLayout.LayoutParams(
                dp(24), dp(24), Gravity.CENTER));

        FrameLayout.LayoutParams menuParams = new FrameLayout.LayoutParams(
                dp(40), dp(40), Gravity.TOP | Gravity.START);
        menuParams.topMargin = settings().getInt("menuY", dp(8));
        menuParams.leftMargin = settings().getInt("menuX", dp(8));
        root.addView(menuButton, menuParams);
        root.post(this::clampMenuPosition);
        menuButton.setOnClickListener(view -> {
            menuIcon.animateTo(1f);
            showMainMenu();
        });
        menuButton.setOnLongClickListener(view -> {
            menuDragging = true;
            view.performHapticFeedback(HapticFeedbackConstants.LONG_PRESS);
            menuButton.setAlpha(0.82f);
            menuButton.setCardElevation(dp(6));
            menuButton.bringToFront();
            return true;
        });
        menuButton.setOnTouchListener((view, event) -> {
            FrameLayout.LayoutParams params =
                    (FrameLayout.LayoutParams) view.getLayoutParams();
            switch (event.getActionMasked()) {
            case MotionEvent.ACTION_DOWN:
                menuDownRawX = event.getRawX();
                menuDownRawY = event.getRawY();
                menuDownLeft = params.leftMargin;
                menuDownTop = params.topMargin;
                return false;
            case MotionEvent.ACTION_MOVE:
                if (!menuDragging) return false;
                params.leftMargin = clamp(
                        menuDownLeft + Math.round(event.getRawX() - menuDownRawX),
                        0, Math.max(0, root.getWidth() - params.width));
                params.topMargin = clamp(
                        menuDownTop + Math.round(event.getRawY() - menuDownRawY),
                        0, Math.max(0, root.getHeight() - params.height));
                view.setLayoutParams(params);
                return true;
            case MotionEvent.ACTION_UP:
            case MotionEvent.ACTION_CANCEL:
                if (!menuDragging) return false;
                menuDragging = false;
                menuButton.setAlpha(1f);
                menuButton.setCardElevation(dp(1));
                settings().edit()
                        .putInt("menuX", params.leftMargin)
                        .putInt("menuY", params.topMargin)
                        .apply();
                return true;
            default:
                return false;
            }
        });

        buildLogPanel();
        setContentView(root);

        int revealX = getIntent().getIntExtra(EXTRA_REVEAL_X, -1);
        int revealY = getIntent().getIntExtra(EXTRA_REVEAL_Y, -1);
        int revealColor = getIntent().getIntExtra(EXTRA_REVEAL_COLOR, 0);
        if (revealX >= 0 && revealY >= 0) {
            getIntent().removeExtra(EXTRA_REVEAL_X);
            getIntent().removeExtra(EXTRA_REVEAL_Y);
            getIntent().removeExtra(EXTRA_REVEAL_COLOR);
            getWindow().setBackgroundDrawable(new ColorDrawable(revealColor));
            root.setVisibility(View.INVISIBLE);
            root.post(() -> {
                root.setVisibility(View.VISIBLE);
                int width = root.getWidth();
                int height = root.getHeight();
                int cx = Math.max(0, Math.min(revealX, width));
                int cy = Math.max(0, Math.min(revealY, height));
                float radius = (float) Math.hypot(
                        Math.max(cx, width - cx),
                        Math.max(cy, height - cy));
                android.animation.Animator reveal =
                        android.view.ViewAnimationUtils.createCircularReveal(
                                root, cx, cy, 0f, radius);
                reveal.setDuration(420);
                reveal.setInterpolator(new DecelerateInterpolator());
                reveal.addListener(new android.animation.AnimatorListenerAdapter() {
                    @Override
                    public void onAnimationEnd(android.animation.Animator animation) {
                        getWindow().setBackgroundDrawable(new ColorDrawable(
                                themeColor(com.google.android.material.R.attr.colorSurface)));
                    }
                });
                reveal.start();
            });
        }

        boolean skipSplash = getIntent().getBooleanExtra(EXTRA_SKIP_SPLASH, false)
                || settings().getBoolean("skipSplash", false);
        if (!skipSplash) {
            menuButton.setVisibility(View.GONE);
            splash = new SplashView(this);
            splash.setOnFinished(() -> {
                splash = null;
                menuButton.setVisibility(View.VISIBLE);
                if (settings().getBoolean("autoKeyboard", false)
                        && keyboardView.getVisibility() != View.VISIBLE) {
                    toggleKeyboard();
                }
            });
            root.addView(splash, new FrameLayout.LayoutParams(
                    FrameLayout.LayoutParams.MATCH_PARENT,
                    FrameLayout.LayoutParams.MATCH_PARENT));
        } else {
            splash = null;
            menuButton.setVisibility(View.VISIBLE);
            if (settings().getBoolean("autoKeyboard", false)) {
                root.post(() -> {
                    if (keyboardView.getVisibility() != View.VISIBLE) {
                        toggleKeyboard();
                    }
                });
            }
        }

        prepareProfile();

        new Thread(this, "primeshim-bootstrap").start();
    }

    /** Runs off the UI thread: prepares the working directory, then either
     *  starts the guest or asks the user for a firmware image. */
    @Override
    public void run() {
        if (!workDir.isDirectory() && !workDir.mkdirs()) {
            setStatus(L.t("无法创建 ") + workDir, true);
            return;
        }

        extractAssets();
        repairAppIcons();

        File appRoot = new File(workDir, "prime_data/A");
        boolean hasAppDisk = new File(appRoot, "dummy.DAT").isFile()
                || new File(appRoot, "WINDOW/SYSTEM/SDKLIB.DLL").isFile();
        if (firmwareFile.isFile() && firmwareFile.length() >= MIN_FIRMWARE_BYTES
                && hasAppDisk) {
            if (settings().getBoolean("guestCrashed", false)) {
                showLastCrashPrompt();
            } else {
                startGuest();
            }
        } else if (firmwareFile.isFile()
                && firmwareFile.length() >= MIN_FIRMWARE_BYTES) {
            setStatus(L.t("固件存在，但 A: 系统盘缺失。\n\n")
                    + L.t("请重新导入 PRIME_APP.DAT；")
                    + L.t("只导入 armfir.elf 不足以启动固件。"), true);
        } else {
            setStatus(L.t("需要一个 HP Prime 固件\n\n")
                    + L.t("请选择官方升级包 zip，或包里的 PRIME_APP.DAT。\n")
                    + L.t("PRIME_MASTER.DAT 和 PRIME_OS.ROM 不需要导入。\n\n")
                    + L.t("选择后会自动解出 A: 系统盘并校验 ARM ELF。\n\n")
                    + "build " + BuildConfig.BUILD_STAMP, true);
        }
    }

    @Override
    public void onConfigurationChanged(android.content.res.Configuration config) {
        super.onConfigurationChanged(config);
        if (root != null) root.post(this::clampMenuPosition);
    }

    /* ---- Material 3 building blocks --------------------------------- */

    private int themeColor(int attr) {
        return MaterialColors.getColor(root, attr);
    }

    private int dp(float value) {
        return Math.round(value * getResources().getDisplayMetrics().density);
    }

    /** Applies a Material 3 type-scale role from the current theme. */
    private void applyTextAppearance(TextView view, int attr) {
        TypedValue value = new TypedValue();
        if (getTheme().resolveAttribute(attr, value, true) && value.resourceId != 0) {
            view.setTextAppearance(value.resourceId);
        }
    }

    /** MD3 state layer: onSurface at 12%. */
    private RippleDrawable ripple() {
        int colour = (themeColor(com.google.android.material.R.attr.colorOnSurface)
                & 0x00FFFFFF) | 0x1F000000;
        /* Bounded state layer: the white mask keeps the ripple to the row's
         * rectangle instead of a huge free-floating circle. */
        return new RippleDrawable(ColorStateList.valueOf(colour), null,
                new ColorDrawable(Color.WHITE));
    }

    /** Material 3 filled card (surfaceContainerHighest, 12dp corners). */
    private MaterialCardView filledCard() {
        MaterialCardView card = new MaterialCardView(this, null,
                R.attr.primeCardFilledStyle);
        card.setCardElevation(0);
        card.setClipToOutline(true);
        card.setClipChildren(true);
        return card;
    }

    /** Vertical content column for a filled card (MaterialCardView is a FrameLayout). */
    private LinearLayout cardColumn(MaterialCardView card) {
        LinearLayout column = new LinearLayout(this);
        column.setOrientation(LinearLayout.VERTICAL);
        column.setLayoutParams(new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.WRAP_CONTENT));
        card.addView(column);
        return column;
    }

    private MaterialButton filledButton(String text, View.OnClickListener action) {
        MaterialButton button = new MaterialButton(this);
        prepareButton(button, text, action);
        return button;
    }

    private MaterialButton tonalButton(String text, View.OnClickListener action) {
        MaterialButton button = (MaterialButton) getLayoutInflater().inflate(
                R.layout.view_button_tonal, root, false);
        prepareButton(button, text, action);
        return button;
    }

    private MaterialButton textButton(String text, View.OnClickListener action) {
        MaterialButton button = (MaterialButton) getLayoutInflater().inflate(
                R.layout.view_button_text, root, false);
        prepareButton(button, text, action);
        return button;
    }

    private void prepareButton(MaterialButton button, String text,
                               View.OnClickListener action) {
        button.setText(text);
        button.setAllCaps(false);
        button.setMinWidth(0);
        button.setMinimumWidth(0);
        button.setOnClickListener(action);
    }

    private LinearLayout buttonRow(int topMargin, MaterialButton... buttons) {
        LinearLayout row = new LinearLayout(this);
        row.setOrientation(LinearLayout.HORIZONTAL);
        for (int i = 0; i < buttons.length; ++i) {
            LinearLayout.LayoutParams params = new LinearLayout.LayoutParams(
                    0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
            params.leftMargin = i == 0 ? 0 : dp(4);
            params.rightMargin = i == buttons.length - 1 ? 0 : dp(4);
            row.addView(buttons[i], params);
        }
        LinearLayout.LayoutParams params = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT);
        params.topMargin = topMargin;
        row.setLayoutParams(params);
        return row;
    }

    /** A 64dp Material 3 small app bar with only a navigation icon. */
    private MaterialToolbar navigationBar(int iconRes, Runnable action) {
        MaterialToolbar bar = new MaterialToolbar(this);
        bar.setNavigationIcon(iconRes);
        bar.setNavigationContentDescription(
                iconRes == R.drawable.ic_close ? L.t("关闭") : L.t("返回"));
        bar.setNavigationIconTint(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        bar.setContentInsetsAbsolute(dp(4), dp(4));
        bar.setNavigationOnClickListener(v -> action.run());
        return bar;
    }

    private ImageView iconButton(int icon, String description, Runnable action) {
        ImageView button = new ImageView(this);
        button.setImageResource(icon);
        button.setImageTintList(ColorStateList.valueOf(themeColor(
                com.google.android.material.R.attr.colorOnSurfaceVariant)));
        button.setContentDescription(description);
        button.setBackground(ripple());
        button.setPadding(dp(9), dp(9), dp(9), dp(9));
        button.setClickable(true);
        button.setFocusable(true);
        button.setOnClickListener(v -> action.run());
        return button;
    }

    private MaterialDivider divider() {
        MaterialDivider divider = new MaterialDivider(this);
        divider.setDividerInsetStart(dp(16));
        divider.setDividerInsetEnd(dp(16));
        divider.setLayoutParams(new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
        return divider;
    }

    private void snack(final CharSequence text) {
        if (root == null) {
            return;
        }
        if (Looper.myLooper() != Looper.getMainLooper()) {
            uiHandler.post(() -> snack(text));
            return;
        }
        Snackbar.make(root, text, Snackbar.LENGTH_SHORT).show();
    }

    /** Material dialog for results the user must read (e.g. restart required). */
    private void notice(final CharSequence text) {
        runOnUiThread(() -> new MaterialAlertDialogBuilder(this)
                .setMessage(text)
                .setPositiveButton(L.t("知道了"), null)
                .show());
    }

    private static int clamp(int value, int min, int max) {
        return value < min ? min : (value > max ? max : value);
    }

    /** Keeps the draggable menu inside the window after a rotation or resize. */
    private void clampMenuPosition() {
        if (menuButton == null) return;
        FrameLayout.LayoutParams params =
                (FrameLayout.LayoutParams) menuButton.getLayoutParams();
        params.leftMargin = clamp(params.leftMargin, 0,
                Math.max(0, root.getWidth() - params.width));
        params.topMargin = clamp(params.topMargin, 0,
                Math.max(0, root.getHeight() - params.height));
        menuButton.setLayoutParams(params);
    }

    /** Keeps a view clear of the display cutout (status bar is immersive). */
    private void offsetForCutout(final View view, final int baseTop) {
        ViewGroup.LayoutParams params = view.getLayoutParams();
        if (!(params instanceof ViewGroup.MarginLayoutParams)) {
            return;
        }
        final ViewGroup.MarginLayoutParams margins = (ViewGroup.MarginLayoutParams) params;
        ViewCompat.setOnApplyWindowInsetsListener(view, (v, insets) -> {
            int top = insets.getInsets(WindowInsetsCompat.Type.displayCutout()).top;
            margins.topMargin = baseTop + top;
            v.setLayoutParams(margins);
            return insets;
        });
        ViewCompat.requestApplyInsets(view);
    }

    private void padForCutout(final View view) {
        final int left = view.getPaddingLeft();
        final int top = view.getPaddingTop();
        final int right = view.getPaddingRight();
        final int bottom = view.getPaddingBottom();
        ViewCompat.setOnApplyWindowInsetsListener(view, (v, insets) -> {
            int cutout = insets.getInsets(WindowInsetsCompat.Type.displayCutout()).top;
            v.setPadding(left, top + cutout, right, bottom);
            return insets;
        });
        ViewCompat.requestApplyInsets(view);
    }

    /* ---- on-screen log ---------------------------------------------- */

    private void buildLogPanel() {
        logPanel = new LinearLayout(this);
        logPanel.setOrientation(LinearLayout.VERTICAL);
        logPanel.setBackgroundColor(themeColor(
                com.google.android.material.R.attr.colorSurface));
        logPanel.setVisibility(View.GONE);
        logPanel.setClickable(true);

        logPanel.addView(navigationBar(R.drawable.ic_close, this::toggleLog),
                new LinearLayout.LayoutParams(
                        LinearLayout.LayoutParams.MATCH_PARENT, dp(64)));

        LinearLayout heading = new LinearLayout(this);
        heading.setOrientation(LinearLayout.VERTICAL);
        heading.setPadding(dp(16), dp(4), dp(16), dp(16));

        TextView title = new TextView(this);
        title.setText(L.t("日志"));
        applyTextAppearance(title,
                com.google.android.material.R.attr.textAppearanceHeadlineMedium);
        title.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        heading.addView(title, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        TextView build = new TextView(this);
        build.setText("build " + BuildConfig.BUILD_STAMP);
        applyTextAppearance(build,
                com.google.android.material.R.attr.textAppearanceLabelMedium);
        build.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurfaceVariant));
        build.setPadding(0, dp(2), 0, 0);
        heading.addView(build, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
        logPanel.addView(heading, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        MaterialCardView card = filledCard();
        LinearLayout.LayoutParams cardParams = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f);
        cardParams.leftMargin = dp(16);
        cardParams.rightMargin = dp(16);
        cardParams.bottomMargin = dp(16);
        logPanel.addView(card, cardParams);

        logText = new TextView(this);
        applyTextAppearance(logText,
                com.google.android.material.R.attr.textAppearanceBodySmall);
        logText.setTypeface(Typeface.MONOSPACE);
        logText.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        logText.setTextIsSelectable(true);
        logText.setLineSpacing(dp(2), 1f);
        logText.setPadding(dp(16), dp(16), dp(16), dp(16));

        logScroll = new ScrollView(this);
        logScroll.setFillViewport(true);
        logScroll.setClipToPadding(false);
        logScroll.addView(logText, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.WRAP_CONTENT));
        card.addView(logScroll, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT));

        LinearLayout actions = new LinearLayout(this);
        actions.setOrientation(LinearLayout.VERTICAL);
        actions.setPadding(dp(16), dp(8), dp(16), dp(16));
        actions.addView(buttonRow(0,
                tonalButton(traceEnabled ? L.t("停止") : L.t("追踪"),
                        v -> toggleTrace((MaterialButton) v)),
                tonalButton(L.t("导出"), v -> saveLogFile()),
                tonalButton(L.t("截图"), v -> saveSnapshot())));
        actions.addView(buttonRow(dp(4),
                textButton(L.t("复制"), v -> copyLog()),
                textButton(L.t("清空"), v -> {
                    PrimeShim.nativeClearLog();
                    refreshLog();
                })));
        logPanel.addView(actions, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
        padForCutout(logPanel);

        root.addView(logPanel, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT));
    }

    private void toggleTrace(MaterialButton button) {
        traceEnabled = !traceEnabled;
        PrimeShim.nativeSetTraceCalls(traceEnabled);
        settings().edit().putBoolean("trace", traceEnabled).apply();
        button.setText(traceEnabled ? L.t("停止") : L.t("追踪"));
        snack(traceEnabled ? L.t("开始记录每次 syscall") : L.t("已停止追踪"));
    }

    /** Show the keyboard and shrink the firmware surface to the space above it,
     *  so the two never overlap. */
    private void toggleKeyboard() {
        boolean show = keyboardView.getVisibility() != View.VISIBLE;
        if (show && logPanel.getVisibility() == View.VISIBLE) {
            logPanel.setVisibility(View.GONE);
            uiHandler.removeCallbacks(logRefresh);
        }
        android.util.DisplayMetrics metrics = getResources().getDisplayMetrics();
        int screenHeight = metrics.heightPixels;
        int screenWidth = metrics.widthPixels;

        int navBar = 0;
        int navId = getResources().getIdentifier(
                "navigation_bar_height", "dimen", "android");
        if (navId > 0) navBar = getResources().getDimensionPixelSize(navId);
        int available = screenHeight - navBar;

        /* Keep the calculator and keyboard as one centred column.  On a
         * tablet, filling the full width makes every key enormous and leaves
         * the 320x240 display as a tiny 240-pixel strip.  Cap the column at
         * 520dp, then shrink it until screen + keyboard fit the height. */
        int columnWidth = Math.min(screenWidth - dp(16), dp(520));
        if (columnWidth < dp(240)) columnWidth = screenWidth;
        int displayHeight = columnWidth * 3 / 4;
        int keyboardHeight = Math.round(columnWidth * 1.22f);
        if (displayHeight + keyboardHeight > available) {
            float scale = (float) available / (displayHeight + keyboardHeight);
            columnWidth = Math.max(dp(200), Math.round(columnWidth * scale));
            displayHeight = columnWidth * 3 / 4;
            keyboardHeight = Math.max(dp(160), available - displayHeight);
        }
        int topMargin = Math.max(0,
                (available - displayHeight - keyboardHeight) / 2);

        FrameLayout.LayoutParams keyParams =
                (FrameLayout.LayoutParams) keyboardView.getLayoutParams();
        keyParams.width = show ? columnWidth
                : FrameLayout.LayoutParams.MATCH_PARENT;
        keyParams.height = show ? keyboardHeight
                : FrameLayout.LayoutParams.MATCH_PARENT;
        keyParams.gravity = show
                ? (Gravity.BOTTOM | Gravity.CENTER_HORIZONTAL)
                : Gravity.CENTER;
        keyParams.bottomMargin = show ? navBar + topMargin : 0;
        keyboardView.setLayoutParams(keyParams);
        keyboardView.setVisibility(show ? View.VISIBLE : View.GONE);

        FrameLayout.LayoutParams params =
                (FrameLayout.LayoutParams) surfaceView.getLayoutParams();
        params.gravity = show
                ? (Gravity.TOP | Gravity.CENTER_HORIZONTAL) : Gravity.CENTER;
        params.width = show ? columnWidth
                : FrameLayout.LayoutParams.MATCH_PARENT;
        params.height = show ? displayHeight
                : FrameLayout.LayoutParams.MATCH_PARENT;
        params.topMargin = show ? topMargin : 0;
        surfaceView.setLayoutParams(params);

        if (show) keyboardView.bringToFront();
        PrimeShim.nativeRequestRedraw();
    }


    /* ---- menu + settings -------------------------------------------- */

    private void showMainMenu() {
        final BottomSheetDialog sheet = new BottomSheetDialog(this);
        LinearLayout content = new LinearLayout(this);
        content.setOrientation(LinearLayout.VERTICAL);
        content.addView(new BottomSheetDragHandleView(this),
                new LinearLayout.LayoutParams(
                        LinearLayout.LayoutParams.MATCH_PARENT,
                        LinearLayout.LayoutParams.WRAP_CONTENT));

        LinearLayout header = new LinearLayout(this);
        header.setOrientation(LinearLayout.VERTICAL);
        header.setPadding(dp(24), 0, dp(24), dp(12));

        TextView title = new TextView(this);
        title.setText("PrimeShim");
        applyTextAppearance(title,
                com.google.android.material.R.attr.textAppearanceHeadlineSmall);
        title.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        header.addView(title, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        TextView build = new TextView(this);
        build.setText(L.t("HP Prime 模拟器 · build ") + BuildConfig.BUILD_STAMP);
        applyTextAppearance(build,
                com.google.android.material.R.attr.textAppearanceBodyMedium);
        build.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurfaceVariant));
        build.setPadding(0, dp(2), 0, 0);
        header.addView(build, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
        content.addView(header, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        final String[] items = {L.t("设置"), L.t("日志"), L.t("键盘"), L.t("脚本"),
                L.t("固件"), L.t("文件管理"), L.t("备份"), L.t("关于")};
        final Runnable[] actions = {
                this::showSettings,
                this::toggleLog,
                this::toggleKeyboard,
                this::showScriptEditor,
                this::promptFirmwareImport,
                this::showFileManager,
                this::showBackupMenu,
                this::showAbout
        };
        for (int i = 0; i < items.length; ++i) {
            final Runnable action = actions[i];
            content.addView(sheetRow(items[i], () -> {
                sheet.dismiss();
                action.run();
            }, false));
        }
        content.setPadding(0, 0, 0, dp(8));
        sheet.setOnDismissListener(dialog -> {
            if (menuIcon != null) menuIcon.animateTo(0f);
        });
        ScrollView scroller = new ScrollView(this);
        scroller.setFillViewport(false);
        scroller.addView(content, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.WRAP_CONTENT));
        sheet.setContentView(scroller);
        sheet.show();
    }

    private TextView sheetRow(String label, Runnable action) {
        return sheetRow(label, action, false);
    }

    private TextView sheetRow(String label, Runnable action, boolean destructive) {
        TextView row = new TextView(this);
        row.setText(label);
        applyTextAppearance(row,
                com.google.android.material.R.attr.textAppearanceBodyLarge);
        row.setTextColor(themeColor(destructive
                ? com.google.android.material.R.attr.colorError
                : com.google.android.material.R.attr.colorOnSurface));
        row.setGravity(Gravity.CENTER_VERTICAL);
        row.setPadding(dp(24), 0, dp(24), 0);
        row.setMinHeight(dp(56));
        row.setBackground(ripple());
        row.setLayoutParams(new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
        row.setOnClickListener(v -> action.run());
        return row;
    }

    /* ---- tiny file manager ------------------------------------------- */

    private File fmDir;
    private File fmPendingExport;

    private String displayPath(File file) {
        String root = primeRoot().getAbsolutePath();
        String path = file.getAbsolutePath();
        if (!path.startsWith(root)) return path;
        String rest = path.substring(root.length());
        while (rest.startsWith("/") || rest.startsWith("\\")) {
            rest = rest.substring(1);
        }
        if (rest.isEmpty()) return "";
        String[] parts = rest.split("[/\\\\]", 2);
        String drive = parts[0].toUpperCase(java.util.Locale.US);
        String tail = parts.length > 1 ? parts[1] : "";
        return drive + ":\\" + tail.replace('/', '\\');
    }

    private LinearLayout fileList;
    private TextView filePathView;

    private void showFileManager() {
        if (fmDir == null || !fmDir.isDirectory()) {
            fmDir = cDrive();
        }

        LinearLayout content = new LinearLayout(this);
        content.setOrientation(LinearLayout.VERTICAL);

        filePathView = new TextView(this);
        applyTextAppearance(filePathView,
                com.google.android.material.R.attr.textAppearanceBodyMedium);
        filePathView.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurfaceVariant));
        filePathView.setPadding(dp(8), 0, dp(8), dp(12));
        content.addView(filePathView, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        MaterialCardView card = filledCard();
        fileList = cardColumn(card);
        content.addView(card, cardParams());

        renderFileManager();
        pushPage(buildPage(L.t("文件管理"), content, this::popPage));
    }

    private static final String SCRIPT_SAMPLE =
            "// PrimeShim JavaScript\n" +
            "// await prime.press('1');\n" +
            "// await prime.touchTap(0, 160, 120);\n" +
            "prime.log('Hello from JavaScript');\n" +
            "await prime.press('1');\n" +
            "await prime.press('+');\n" +
            "await prime.press('2');\n" +
            "await prime.press('enter');\n" +
            "prime.log('Keys sent');\n";

    private void showScriptEditor() {
        if (scriptRuntime == null) {
            scriptRuntime = new ScriptRuntime(this, root, new ScriptRuntime.Listener() {
                @Override public void onScriptLog(String line) {
                    scriptLogLine(line);
                }

                @Override public void onScriptFinished() {
                    // The bridge already appended the completion line.
                }
            });
        }

        LinearLayout content = new LinearLayout(this);
        content.setOrientation(LinearLayout.VERTICAL);

        MaterialCardView editorCard = filledCard();
        scriptEditor = new CodeEditorView(this);
        scriptEditor.setDark(isDarkTheme());
        scriptEditor.setText(settings().getString("script", SCRIPT_SAMPLE));
        scriptEditor.setHint(L.t("在此输入 JavaScript"));
        editorCard.addView(scriptEditor, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT));
        content.addView(editorCard, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f));

        View[] actions = {
                iconButton(R.drawable.ic_play, L.t("运行"), this::runScript),
                iconButton(R.drawable.ic_stop, L.t("停止"), this::stopScript),
                iconButton(R.drawable.ic_file_upload, L.t("导入"), this::pickScript),
                iconButton(R.drawable.ic_file_download, L.t("导出"), this::exportScript),
                iconButton(R.drawable.ic_code, L.t("示例"), () -> {
                    scriptEditor.setText(SCRIPT_SAMPLE);
                    saveScript();
                }),
                iconButton(R.drawable.ic_info, L.t("帮助"), this::showScriptHelp)
        };
        pushPage(buildFixedPage(L.t("脚本"), content, () -> {
            saveScript();
            popPage();
        }, actions));
    }

    private void showScriptHelp() {
        docEntries = ScriptDocs.forLanguage(L.code());
        LinearLayout content = new LinearLayout(this);
        content.setOrientation(LinearLayout.VERTICAL);

        EditText search = new EditText(this);
        search.setSingleLine(true);
        search.setHint(L.t("搜索函数"));
        search.setTextSize(16);
        search.setInputType(InputType.TYPE_CLASS_TEXT
                | InputType.TYPE_TEXT_FLAG_NO_SUGGESTIONS);
        search.setPadding(dp(8), dp(8), dp(8), dp(12));
        search.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        search.setHintTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurfaceVariant));
        content.addView(search, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        docList = new LinearLayout(this);
        docList.setOrientation(LinearLayout.VERTICAL);
        content.addView(docList, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        renderDocList("");
        search.addTextChangedListener(new TextWatcher() {
            @Override public void beforeTextChanged(CharSequence s, int start,
                                                     int count, int after) { }

            @Override public void onTextChanged(CharSequence s, int start,
                                                 int before, int count) {
                renderDocList(s == null ? "" : s.toString());
            }

            @Override public void afterTextChanged(Editable s) { }
        });
        pushPage(buildPage(L.t("文档"), content, this::popPage));
    }

    private void renderDocList(String query) {
        if (docList == null || docEntries == null) return;
        final String needle = query == null ? "" : query.trim().toLowerCase(Locale.US);
        docList.removeAllViews();
        int shown = 0;
        for (ScriptDocs.Entry entry : docEntries) {
            String haystack = (entry.name + " " + entry.signature + " "
                    + entry.description + " " + entry.parameters).toLowerCase(Locale.US);
            if (!needle.isEmpty() && !haystack.contains(needle)) continue;
            TextView row = new TextView(this);
            row.setText(entry.name);
            row.setTypeface(Typeface.MONOSPACE);
            row.setTextSize(16);
            row.setTextColor(themeColor(
                    com.google.android.material.R.attr.colorOnSurface));
            row.setGravity(Gravity.CENTER_VERTICAL);
            row.setPadding(dp(8), dp(16), dp(8), dp(16));
            row.setBackground(ripple());
            row.setOnClickListener(v -> showDocDetail(entry));
            docList.addView(row, new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT));
            docList.addView(divider());
            ++shown;
        }
        if (shown == 0) {
            TextView empty = new TextView(this);
            empty.setText(L.t("没有匹配的函数"));
            empty.setTextColor(themeColor(
                    com.google.android.material.R.attr.colorOnSurfaceVariant));
            empty.setPadding(dp(8), dp(24), dp(8), dp(24));
            docList.addView(empty);
        }
    }

    private void showDocDetail(ScriptDocs.Entry entry) {
        LinearLayout content = new LinearLayout(this);
        content.setOrientation(LinearLayout.VERTICAL);

        content.addView(docBody(entry.description), new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
        content.addView(sectionCaption(L.t("签名")));
        content.addView(docCodeBlock(entry.signature), cardParams());
        if (entry.parameters != null && !entry.parameters.isEmpty()) {
            content.addView(sectionCaption(L.t("参数")));
            content.addView(docBody(entry.parameters), new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT));
        }
        if (entry.returns != null && !entry.returns.isEmpty()) {
            content.addView(sectionCaption(L.t("返回值")));
            content.addView(docBody(entry.returns), new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT));
        }
        content.addView(sectionCaption(L.t("示例")));
        content.addView(docCodeBlock(entry.example), cardParams());

        pushPage(buildPage(entry.name, content, this::popPage));
    }

    private TextView docBody(String text) {
        TextView body = new TextView(this);
        body.setText(text);
        applyTextAppearance(body,
                com.google.android.material.R.attr.textAppearanceBodyMedium);
        body.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        body.setLineSpacing(dp(3), 1f);
        body.setPadding(dp(4), 0, dp(4), dp(4));
        body.setTextIsSelectable(true);
        return body;
    }

    private MaterialCardView docCodeBlock(String code) {
        MaterialCardView card = filledCard();
        TextView view = new TextView(this);
        view.setText(code);
        view.setTypeface(Typeface.MONOSPACE);
        view.setTextSize(13);
        view.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        view.setLineSpacing(dp(2), 1f);
        view.setPadding(dp(16), dp(14), dp(16), dp(14));
        view.setTextIsSelectable(true);
        card.addView(view, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.WRAP_CONTENT));
        return card;
    }

    private void runScript() {
        if (scriptEditor == null || scriptRuntime == null) return;
        String source = scriptEditor.getText().toString();
        if (source.trim().isEmpty()) {
            snack(L.t("脚本为空"));
            return;
        }
        saveScript();
        showScriptTerminal();
        appendTerminal("> " + L.t("脚本开始"));
        scriptRuntime.run(source);
    }

    private void stopScript() {
        if (scriptRuntime != null) scriptRuntime.stop();
        appendTerminal(L.t("已停止"));
    }

    private void showScriptTerminal() {
        terminalBuffer.setLength(0);
        terminalPage = new LinearLayout(this);
        terminalPage.setOrientation(LinearLayout.VERTICAL);
        terminalPage.setBackgroundColor(0xFF0D1117);
        terminalPage.setClickable(true);

        LinearLayout header = new LinearLayout(this);
        header.setOrientation(LinearLayout.HORIZONTAL);
        header.setGravity(Gravity.CENTER_VERTICAL);
        header.setPadding(dp(4), 0, dp(4), 0);

        ImageView back = iconButton(R.drawable.ic_arrow_back, L.t("返回"),
                () -> {
                    stopScript();
                    popPage();
                });
        back.setImageTintList(ColorStateList.valueOf(0xFFE6EDF3));
        header.addView(back, new LinearLayout.LayoutParams(dp(48), dp(48)));

        TextView title = new TextView(this);
        title.setText(L.t("终端"));
        title.setTextSize(18);
        title.setTypeface(Typeface.MONOSPACE);
        title.setTextColor(0xFFE6EDF3);
        title.setPadding(dp(8), 0, dp(8), 0);
        header.addView(title, new LinearLayout.LayoutParams(
                0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f));

        ImageView stop = iconButton(R.drawable.ic_stop, L.t("停止"), this::stopScript);
        stop.setImageTintList(ColorStateList.valueOf(0xFFFF7B72));
        header.addView(stop, new LinearLayout.LayoutParams(dp(48), dp(48)));
        terminalPage.addView(header, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, dp(64)));

        terminalScroll = new ScrollView(this);
        terminalScroll.setFillViewport(true);
        terminalScroll.setBackgroundColor(0xFF0D1117);
        terminalText = new TextView(this);
        terminalText.setTypeface(Typeface.MONOSPACE);
        terminalText.setTextSize(12);
        terminalText.setTextColor(0xFFC9D1D9);
        terminalText.setPadding(dp(16), dp(12), dp(16), dp(16));
        terminalText.setLineSpacing(dp(2), 1f);
        terminalText.setTextIsSelectable(true);
        terminalScroll.addView(terminalText, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.WRAP_CONTENT));
        terminalPage.addView(terminalScroll, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f));

        padForCutout(terminalPage);
        pushPage(terminalPage);
    }

    private void appendTerminal(String line) {
        if (line == null) return;
        if (terminalBuffer.length() > 0) terminalBuffer.append('\n');
        terminalBuffer.append(line);
        if (terminalBuffer.length() > 200000) {
            terminalBuffer.delete(0, terminalBuffer.length() - 160000);
        }
        if (terminalText != null) {
            terminalText.setText(terminalBuffer);
            if (terminalScroll != null) {
                terminalScroll.post(() -> terminalScroll.fullScroll(View.FOCUS_DOWN));
            }
        }
    }

    private void saveScript() {
        if (scriptEditor == null) return;
        settings().edit().putString("script", scriptEditor.getText().toString()).apply();
    }

    private void pickScript() {
        Intent intent = new Intent(Intent.ACTION_OPEN_DOCUMENT);
        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType("*/*");
        intent.putExtra(Intent.EXTRA_MIME_TYPES,
                new String[]{"text/*", "application/javascript", "application/x-javascript"});
        try {
            startActivityForResult(intent, REQUEST_SCRIPT_IMPORT);
        } catch (Exception error) {
            snack(L.t("没有可用的文件选择器"));
        }
    }

    private void exportScript() {
        if (scriptEditor == null) return;
        scriptExportText = scriptEditor.getText().toString();
        Intent intent = new Intent(Intent.ACTION_CREATE_DOCUMENT);
        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType("application/javascript");
        intent.putExtra(Intent.EXTRA_TITLE, "primeshim.js");
        try {
            startActivityForResult(intent, REQUEST_SCRIPT_EXPORT);
        } catch (Exception error) {
            scriptExportText = null;
            snack(L.t("没有可用的文件选择器"));
        }
    }

    private void writeScriptUri(final Uri uri, final String text) {
        new Thread(() -> {
            boolean ok = false;
            try (OutputStream out = getContentResolver().openOutputStream(uri)) {
                if (out != null) {
                    out.write(text.getBytes("UTF-8"));
                    out.flush();
                    ok = true;
                }
            } catch (Exception error) {
                Log.w(TAG, "cannot export script", error);
            }
            final boolean success = ok;
            runOnUiThread(() -> {
                if (success) snack(L.t("脚本已导出"));
                else snack(L.t("导出失败：") + uri);
            });
        }, "primeshim-script-export").start();
    }

    private void importScript(final Uri uri) {
        new Thread(() -> {
            String text = null;
            try (InputStream in = getContentResolver().openInputStream(uri)) {
                if (in != null) {
                    java.io.ByteArrayOutputStream out = new java.io.ByteArrayOutputStream();
                    byte[] buffer = new byte[8192];
                    int total = 0;
                    int read;
                    while ((read = in.read(buffer)) > 0) {
                        total += read;
                        if (total > 1024 * 1024) {
                            throw new IOException("script too large");
                        }
                        out.write(buffer, 0, read);
                    }
                    text = out.toString("UTF-8");
                }
            } catch (Exception error) {
                Log.w(TAG, "cannot import script", error);
            }
            final String imported = text;
            runOnUiThread(() -> {
                if (imported == null) {
                    snack(L.t("导入失败：") + uri);
                    return;
                }
                if (scriptEditor != null) {
                    scriptEditor.setText(imported);
                    saveScript();
                }
                snack(L.t("脚本已导入"));
            });
        }, "primeshim-script-import").start();
    }

    private void scriptLogLine(String line) {
        appendTerminal(line);
    }

    private String pathLabel(File file) {
        if (file == null) return "";
        if (file.equals(primeRoot())) return L.t("根目录");
        return displayPath(file);
    }

    private static String readableSize(long bytes) {
        if (bytes < 1024) return bytes + " B";
        if (bytes < 1024 * 1024) return (bytes / 1024) + " KB";
        return String.format(java.util.Locale.US, "%.1f MB", bytes / 1048576.0);
    }

    private MaterialDivider fileDivider() {
        MaterialDivider divider = divider();
        divider.setDividerInsetStart(dp(56));
        return divider;
    }

    private void renderFileManager() {
        if (fileList == null || filePathView == null) return;

        filePathView.setText(pathLabel(fmDir));
        fileList.removeAllViews();

        fileList.addView(fileRow(R.drawable.ic_file_upload,
                L.t("导入文件到此处"), L.t("复制到 ") + pathLabel(fmDir),
                com.google.android.material.R.attr.colorPrimary,
                this::pickFileForImport));

        if (!fmDir.equals(primeRoot())) {
            fileList.addView(fileDivider());
            fileList.addView(fileRow(R.drawable.ic_arrow_upward,
                    L.t("上一级"), pathLabel(fmDir.getParentFile()),
                    com.google.android.material.R.attr.colorOnSurfaceVariant,
                    () -> {
                        fmDir = fmDir.getParentFile();
                        renderFileManager();
                    }));
        }

        File[] children = fmDir.listFiles();
        int count = 0;
        if (children != null) {
            java.util.Arrays.sort(children, (a, b) -> {
                if (a.isDirectory() != b.isDirectory()) {
                    return a.isDirectory() ? -1 : 1;
                }
                return a.getName().compareToIgnoreCase(b.getName());
            });
            for (final File child : children) {
                fileList.addView(fileDivider());
                if (child.isDirectory()) {
                    fileList.addView(fileRow(R.drawable.ic_folder,
                            child.getName(), L.t("文件夹"),
                            com.google.android.material.R.attr.colorOnSurfaceVariant,
                            () -> {
                                fmDir = child;
                                renderFileManager();
                            }));
                } else {
                    fileList.addView(fileRow(R.drawable.ic_file,
                            child.getName(), readableSize(child.length()),
                            com.google.android.material.R.attr.colorOnSurfaceVariant,
                            () -> showFileActionsSheet(child)));
                }
                ++count;
            }
        }

        if (count == 0) {
            TextView empty = new TextView(this);
            empty.setText(L.t("这个文件夹是空的"));
            applyTextAppearance(empty,
                    com.google.android.material.R.attr.textAppearanceBodyMedium);
            empty.setTextColor(themeColor(
                    com.google.android.material.R.attr.colorOnSurfaceVariant));
            empty.setPadding(dp(24), dp(24), dp(24), dp(24));
            fileList.addView(empty, new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT));
        }
    }

    private View fileRow(int iconRes, String title, String supporting,
                         int tintAttr, Runnable action) {
        LinearLayout row = new LinearLayout(this);
        row.setOrientation(LinearLayout.HORIZONTAL);
        row.setGravity(Gravity.CENTER_VERTICAL);
        row.setPadding(dp(16), dp(12), dp(16), dp(12));
        row.setMinimumHeight(dp(64));
        row.setBackground(ripple());

        ImageView icon = new ImageView(this);
        icon.setImageResource(iconRes);
        icon.setImageTintList(ColorStateList.valueOf(themeColor(tintAttr)));
        icon.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
        LinearLayout.LayoutParams iconParams = new LinearLayout.LayoutParams(
                dp(24), dp(24));
        iconParams.rightMargin = dp(16);
        row.addView(icon, iconParams);

        LinearLayout texts = new LinearLayout(this);
        texts.setOrientation(LinearLayout.VERTICAL);

        TextView headline = new TextView(this);
        headline.setText(title);
        applyTextAppearance(headline,
                com.google.android.material.R.attr.textAppearanceBodyLarge);
        headline.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        texts.addView(headline, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        if (supporting != null && !supporting.isEmpty()) {
            TextView sub = new TextView(this);
            sub.setText(supporting);
            applyTextAppearance(sub,
                    com.google.android.material.R.attr.textAppearanceBodyMedium);
            sub.setTextColor(themeColor(
                    com.google.android.material.R.attr.colorOnSurfaceVariant));
            sub.setPadding(0, dp(2), 0, 0);
            texts.addView(sub, new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT));
        }
        row.addView(texts, new LinearLayout.LayoutParams(0,
                LinearLayout.LayoutParams.WRAP_CONTENT, 1f));

        ImageView chevron = new ImageView(this);
        chevron.setImageResource(R.drawable.ic_chevron_right);
        chevron.setImageTintList(ColorStateList.valueOf(themeColor(
                com.google.android.material.R.attr.colorOnSurfaceVariant)));
        chevron.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
        LinearLayout.LayoutParams chevronParams = new LinearLayout.LayoutParams(
                dp(24), dp(24));
        chevronParams.leftMargin = dp(8);
        row.addView(chevron, chevronParams);

        row.setLayoutParams(new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
        row.setOnClickListener(v -> action.run());
        return row;
    }

    private void showFileActionsSheet(final File file) {
        final BottomSheetDialog sheet = new BottomSheetDialog(this);
        LinearLayout content = new LinearLayout(this);
        content.setOrientation(LinearLayout.VERTICAL);
        content.addView(new BottomSheetDragHandleView(this),
                new LinearLayout.LayoutParams(
                        LinearLayout.LayoutParams.MATCH_PARENT,
                        LinearLayout.LayoutParams.WRAP_CONTENT));

        LinearLayout header = new LinearLayout(this);
        header.setOrientation(LinearLayout.VERTICAL);
        header.setPadding(dp(24), 0, dp(24), dp(12));

        TextView title = new TextView(this);
        title.setText(file.getName());
        applyTextAppearance(title,
                com.google.android.material.R.attr.textAppearanceHeadlineSmall);
        title.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        header.addView(title, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        TextView sub = new TextView(this);
        sub.setText(readableSize(file.length()) + " · "
                + pathLabel(file.getParentFile()));
        applyTextAppearance(sub,
                com.google.android.material.R.attr.textAppearanceBodyMedium);
        sub.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurfaceVariant));
        sub.setPadding(0, dp(2), 0, 0);
        header.addView(sub, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
        content.addView(header, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        content.addView(sheetActionRow(R.drawable.ic_file_download, L.t("导出到…"),
                com.google.android.material.R.attr.colorOnSurface, () -> {
                    sheet.dismiss();
                    fmPendingExport = file;
                    Intent intent = new Intent(Intent.ACTION_CREATE_DOCUMENT);
                    intent.addCategory(Intent.CATEGORY_OPENABLE);
                    intent.setType("*/*");
                    intent.putExtra(Intent.EXTRA_TITLE, file.getName());
                    try {
                        startActivityForResult(intent, REQUEST_FM_EXPORT);
                    } catch (Exception error) {
                        snack(L.t("没有可用的文件选择器"));
                    }
                }));

        content.addView(sheetActionRow(R.drawable.ic_delete, L.t("删除"),
                com.google.android.material.R.attr.colorError, () -> {
                    sheet.dismiss();
                    confirmDelete(file);
                }));

        content.setPadding(0, 0, 0, dp(8));
        sheet.setContentView(content);
        sheet.show();
    }

    private View sheetActionRow(int iconRes, String label, int tintAttr,
                                Runnable action) {
        LinearLayout row = new LinearLayout(this);
        row.setOrientation(LinearLayout.HORIZONTAL);
        row.setGravity(Gravity.CENTER_VERTICAL);
        row.setPadding(dp(24), 0, dp(24), 0);
        row.setMinimumHeight(dp(56));
        row.setBackground(ripple());

        ImageView icon = new ImageView(this);
        icon.setImageResource(iconRes);
        icon.setImageTintList(ColorStateList.valueOf(themeColor(tintAttr)));
        icon.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
        LinearLayout.LayoutParams iconParams = new LinearLayout.LayoutParams(
                dp(24), dp(24));
        iconParams.rightMargin = dp(16);
        row.addView(icon, iconParams);

        TextView text = new TextView(this);
        text.setText(label);
        applyTextAppearance(text,
                com.google.android.material.R.attr.textAppearanceBodyLarge);
        text.setTextColor(themeColor(tintAttr));
        row.addView(text, new LinearLayout.LayoutParams(0,
                LinearLayout.LayoutParams.WRAP_CONTENT, 1f));

        row.setLayoutParams(new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
        row.setOnClickListener(v -> action.run());
        return row;
    }

    private void confirmDelete(final File file) {
        new MaterialAlertDialogBuilder(this)
                .setMessage(L.t("删除 ") + file.getName() + "？")
                .setPositiveButton(L.t("删除"), (dialog, which) -> {
                    //noinspection ResultOfMethodCallIgnored
                    file.delete();
                    renderFileManager();
                })
                .setNegativeButton(L.t("取消"), null)
                .show();
    }

    private void pickFileForImport() {
        Intent intent = new Intent(Intent.ACTION_OPEN_DOCUMENT);
        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType("*/*");
        try {
            startActivityForResult(intent, REQUEST_FM_IMPORT);
        } catch (Exception error) {
            snack(L.t("没有可用的文件选择器"));
        }
    }

    private String displayNameOf(Uri uri, String fallback) {
        try {
            android.database.Cursor cursor = getContentResolver().query(uri, null, null, null, null);
            if (cursor != null) {
                try {
                    int index = cursor.getColumnIndex(android.provider.OpenableColumns.DISPLAY_NAME);
                    if (index >= 0 && cursor.moveToFirst()) {
                        String name = cursor.getString(index);
                        if (name != null && !name.isEmpty()) return name;
                    }
                } finally {
                    cursor.close();
                }
            }
        } catch (Exception ignored) {
        }
        String path = uri.getLastPathSegment();
        return path != null ? path : fallback;
    }

    private void copyUriToFile(final Uri uri, final File target) {
        setStatus(L.t("正在复制…"), false);
        new Thread(() -> {
            try {
                InputStream in = getContentResolver().openInputStream(uri);
                if (in == null) throw new IOException(L.t("无法读取所选文件"));
                OutputStream out = new FileOutputStream(target);
                try {
                    byte[] buffer = new byte[128 * 1024];
                    int read;
                    while ((read = in.read(buffer)) > 0) out.write(buffer, 0, read);
                } finally {
                    closeQuietly(out);
                    closeQuietly(in);
                }
                setStatus(L.t("已写入 ") + displayPath(target), false);
                runOnUiThread(this::renderFileManager);
            } catch (Exception error) {
                Log.e(TAG, "copy failed", error);
                setStatus(L.t("复制失败：") + error.getMessage(), false);
            }
        }, "primeshim-copy").start();
    }

    private void copyFileToUri(final File source, final Uri target) {
        setStatus(L.t("正在导出 ") + source.getName() + "…", false);
        new Thread(() -> {
            try {
                InputStream in = new FileInputStream(source);
                OutputStream out = getContentResolver().openOutputStream(target);
                if (out == null) throw new IOException(L.t("无法写入所选位置"));
                try {
                    byte[] buffer = new byte[128 * 1024];
                    int read;
                    while ((read = in.read(buffer)) > 0) out.write(buffer, 0, read);
                } finally {
                    closeQuietly(out);
                    closeQuietly(in);
                }
                setStatus(L.t("已导出 ") + source.getName(), false);
            } catch (Exception error) {
                Log.e(TAG, "export failed", error);
                setStatus(L.t("导出失败：") + error.getMessage(), false);
            }
        }, "primeshim-export").start();
    }


    /* ---- settings (Material 3) --------------------------------------- */

    private final java.util.ArrayList<LinearLayout> pageStack = new java.util.ArrayList<>();

    private void showSettings() {
        showSettingsPage(0);
    }

    private void clearRevealExtras() {
        getIntent().removeExtra(EXTRA_REVEAL_X);
        getIntent().removeExtra(EXTRA_REVEAL_Y);
        getIntent().removeExtra(EXTRA_REVEAL_COLOR);
    }

    /** Font-size change: no launch animation and no transition animation. */
    private void recreateForFont() {
        getIntent().putExtra(EXTRA_SKIP_SPLASH, true);
        clearRevealExtras();
        recreate();
        overridePendingTransition(0, 0);
    }

    /** Language change: play the normal SplashView again. */
    private void recreateWithSplash() {
        getIntent().removeExtra(EXTRA_SKIP_SPLASH);
        clearRevealExtras();
        recreate();
    }

    /** Theme change: reveal the new theme with a circular wipe from the
     *  tapped control.  The old window colour is passed to the new Activity;
     *  its root is clipped by ViewAnimationUtils and expands from the point. */
    private void applyThemeWithReveal(final int mode, View anchor) {
        final int current = settings().getInt("theme",
                AppCompatDelegate.MODE_NIGHT_FOLLOW_SYSTEM);
        if (mode == current) return;
        int[] point = new int[]{root.getWidth() / 2, root.getHeight() / 2};
        if (anchor != null) {
            int[] screen = new int[2];
            int[] rootScreen = new int[2];
            anchor.getLocationOnScreen(screen);
            root.getLocationOnScreen(rootScreen);
            point[0] = screen[0] - rootScreen[0] + anchor.getWidth() / 2;
            point[1] = screen[1] - rootScreen[1] + anchor.getHeight() / 2;
        }
        settings().edit().putInt("theme", mode).apply();
        getIntent().putExtra(EXTRA_SKIP_SPLASH, true);
        getIntent().putExtra(EXTRA_REVEAL_X, point[0]);
        getIntent().putExtra(EXTRA_REVEAL_Y, point[1]);
        getIntent().putExtra(EXTRA_REVEAL_COLOR,
                themeColor(com.google.android.material.R.attr.colorSurface));
        overridePendingTransition(0, 0);
        AppCompatDelegate.setDefaultNightMode(mode);
    }

    private void showLanguageDialog() {
        final String[] codes = {"zh", "en", "fr"};
        final String[] labels = {"中文", "English", "Français"};
        new MaterialAlertDialogBuilder(this)
                .setTitle(L.t("语言"))
                .setItems(labels, (dialog, which) -> {
                    L.setLanguage(this, codes[which]);
                    recreateWithSplash();
                })
                .show();
    }

    private String themeName() {
        int mode = settings().getInt("theme",
                AppCompatDelegate.MODE_NIGHT_FOLLOW_SYSTEM);
        if (mode == AppCompatDelegate.MODE_NIGHT_NO) return L.t("亮色");
        if (mode == AppCompatDelegate.MODE_NIGHT_YES) return L.t("暗色");
        return L.t("跟随系统");
    }

    private void showThemeDialog() {
        final int[] modes = {
                AppCompatDelegate.MODE_NIGHT_FOLLOW_SYSTEM,
                AppCompatDelegate.MODE_NIGHT_NO,
                AppCompatDelegate.MODE_NIGHT_YES
        };
        final String[] labels = {
                L.t("跟随系统"), L.t("亮色"), L.t("暗色")
        };
        new MaterialAlertDialogBuilder(this)
                .setTitle(L.t("主题"))
                .setItems(labels, (dialog, which) -> applyTheme(modes[which]))
                .show();
    }

    private void applyTheme(int mode) {
        applyThemeWithReveal(mode, null);
    }

    private void showSettingsPage(final int page) {
        LinearLayout box = new LinearLayout(this);
        box.setOrientation(LinearLayout.VERTICAL);
        box.setPadding(0, 0, 0, dp(16));

        if (page == 0) {
            box.addView(sectionCaption(L.t("通用")));
            MaterialCardView generalCard = filledCard();
            LinearLayout general = cardColumn(generalCard);
            SettingsRow speed = settingsRowView(L.t("模拟速度"),
                    L.t("当前 ") + speedPercent + "%",
                    () -> showSettingsPage(1));
            speedSummary = speed.supporting;
            general.addView(speed.view);
            general.addView(divider());
            general.addView(settingsRowView(L.t("语言"), L.languageName(),
                    this::showLanguageDialog).view);
            general.addView(divider());
            general.addView(settingsRowView(L.t("外观"), L.t("主题与字体大小"),
                    () -> showSettingsPage(3)).view);
            general.addView(divider());
            general.addView(settingsRowView(L.t("调试"), L.t("追踪与日志"),
                    () -> showSettingsPage(2)).view);
            box.addView(generalCard, cardParams());

            box.addView(sectionCaption(L.t("偏好设置")));
            MaterialCardView prefCard = filledCard();
            LinearLayout pref = cardColumn(prefCard);

            final MaterialSwitch autoKbd = new MaterialSwitch(this);
            autoKbd.setChecked(settings().getBoolean("autoKeyboard", false));
            SettingsRow autoKbdRow = settingsRowView(L.t("默认自动开启键盘"),
                    L.t("启动应用时自动展开键盘"), autoKbd::toggle, autoKbd);
            autoKbd.setOnCheckedChangeListener((button, checked) -> {
                settings().edit().putBoolean("autoKeyboard", checked).apply();
            });
            pref.addView(autoKbdRow.view);
            pref.addView(divider());

            final MaterialSwitch skipSplash = new MaterialSwitch(this);
            skipSplash.setChecked(settings().getBoolean("skipSplash", false));
            SettingsRow skipSplashRow = settingsRowView(L.t("跳过开屏动画"),
                    L.t("启动应用时直接进入计算器"), skipSplash::toggle, skipSplash);
            skipSplash.setOnCheckedChangeListener((button, checked) -> {
                settings().edit().putBoolean("skipSplash", checked).apply();
            });
            pref.addView(skipSplashRow.view);
            pref.addView(divider());

            final MaterialSwitch haptic = new MaterialSwitch(this);
            haptic.setChecked(settings().getBoolean("haptic", false));
            SettingsRow hapticRow = settingsRowView(L.t("按键震动反馈"),
                    L.t("按键点击时触发震动反馈"), haptic::toggle, haptic);
            haptic.setOnCheckedChangeListener((button, checked) -> {
                keyboardView.setHapticFeedbackEnabled(checked);
                settings().edit().putBoolean("haptic", checked).apply();
            });
            pref.addView(hapticRow.view);
            box.addView(prefCard, cardParams());

            box.addView(sectionCaption(L.t("数据")));
            MaterialCardView dataCard = filledCard();
            LinearLayout data = cardColumn(dataCard);
            data.addView(settingsRowView(L.t("固件"), L.t("导入官方升级包 zip 或 PRIME_APP.DAT"),
                    this::promptFirmwareImport).view);
            data.addView(divider());
            data.addView(settingsRowView(L.t("文件管理"), L.t("浏览 A: 与 C:，导入导出单个文件"),
                    this::showFileManager).view);
            box.addView(dataCard, cardParams());

            box.addView(sectionCaption(L.t("危险操作")));
            MaterialCardView dangerCard = filledCard();
            LinearLayout danger = cardColumn(dangerCard);
            SettingsRow clear = settingsRowView(L.t("清除数据"),
                    L.t("删除所有固件、A:/C: 数据和设置"), this::confirmClearData);
            clear.title.setTextColor(themeColor(
                    com.google.android.material.R.attr.colorError));
            danger.addView(clear.view);
            box.addView(dangerCard, cardParams());
        } else if (page == 1) {
            MaterialCardView card = filledCard();
            LinearLayout inner = new LinearLayout(this);
            inner.setOrientation(LinearLayout.VERTICAL);
            inner.setPadding(dp(24), dp(24), dp(24), dp(24));

            TextView label = new TextView(this);
            label.setText(L.t("模拟速度"));
            applyTextAppearance(label,
                    com.google.android.material.R.attr.textAppearanceBodyMedium);
            label.setTextColor(themeColor(
                    com.google.android.material.R.attr.colorOnSurfaceVariant));
            inner.addView(label, new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT));

            final TextView value = new TextView(this);
            value.setText(speedPercent + "%");
            applyTextAppearance(value,
                    com.google.android.material.R.attr.textAppearanceHeadlineMedium);
            value.setTextColor(themeColor(
                    com.google.android.material.R.attr.colorOnSurface));
            value.setPadding(0, dp(4), 0, 0);
            inner.addView(value, new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT));

            Slider slider = new Slider(this);
            slider.setValueFrom(20f);
            slider.setValueTo(200f);
            slider.setStepSize(5f);
            slider.setValue(Math.round((speedPercent - 20) / 5f) * 5f + 20f);
            slider.setLabelBehavior(LabelFormatter.LABEL_FLOATING);
            slider.setLabelFormatter(v -> Math.round(v) + "%");
            slider.addOnChangeListener((bar, progress, fromUser) -> {
                speedPercent = Math.round(progress);
                value.setText(speedPercent + "%");
                if (speedSummary != null) {
                    speedSummary.setText(L.t("当前 ") + speedPercent + "%");
                }
                PrimeShim.nativeSetSpeed(speedPercent);
                settings().edit().putInt("speed", speedPercent).apply();
            });
            LinearLayout.LayoutParams sliderParams = new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT);
            sliderParams.topMargin = dp(16);
            inner.addView(slider, sliderParams);

            TextView hint = new TextView(this);
            hint.setText(L.t("20% – 200%，默认 100%。修改立即生效。"));
            applyTextAppearance(hint,
                    com.google.android.material.R.attr.textAppearanceBodySmall);
            hint.setTextColor(themeColor(
                    com.google.android.material.R.attr.colorOnSurfaceVariant));
            hint.setPadding(0, dp(8), 0, 0);
            inner.addView(hint, new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT));

            card.addView(inner, new FrameLayout.LayoutParams(
                    FrameLayout.LayoutParams.MATCH_PARENT,
                    FrameLayout.LayoutParams.WRAP_CONTENT));
            box.addView(card, cardParams());
        } else if (page == 2) {
            box.addView(sectionCaption(L.t("调试")));
            MaterialCardView card = filledCard();
            LinearLayout debug = cardColumn(card);

            final MaterialSwitch trace = new MaterialSwitch(this);
            trace.setChecked(traceEnabled);
            SettingsRow traceRow = settingsRowView(L.t("追踪固件 syscall"),
                    traceEnabled ? L.t("已开启，会变慢") : L.t("关闭"), trace::toggle, trace);
            trace.setOnCheckedChangeListener((button, checked) -> {
                traceEnabled = checked;
                PrimeShim.nativeSetTraceCalls(checked);
                settings().edit().putBoolean("trace", checked).apply();
                if (traceRow.supporting != null) {
                    traceRow.supporting.setText(checked ? L.t("已开启，会变慢") : L.t("关闭"));
                }
                snack(checked ? L.t("开始追踪") : L.t("已停止追踪"));
            });
            debug.addView(traceRow.view);
            debug.addView(divider());

            final MaterialSwitch overlaySwitch = new MaterialSwitch(this);
            boolean overlayEnabled = settings().getBoolean("overlay", false);
            overlaySwitch.setChecked(overlayEnabled);
            SettingsRow overlayRow = settingsRowView(L.t("键盘调试"),
                    overlayEnabled ? L.t("红框与键位点位已显示") : L.t("关闭"),
                    overlaySwitch::toggle, overlaySwitch);
            overlaySwitch.setOnCheckedChangeListener((button, checked) -> {
                keyboardView.setDebugOverlay(checked);
                settings().edit().putBoolean("overlay", checked).apply();
                if (overlayRow.supporting != null) {
                    overlayRow.supporting.setText(
                            checked ? L.t("红框与键位点位已显示") : L.t("关闭"));
                }
            });
            debug.addView(overlayRow.view);
            debug.addView(divider());
            debug.addView(settingsRowView(L.t("日志面板"), L.t("查看原生输出"), () -> {
                popPage();
                if (logPanel.getVisibility() != View.VISIBLE) toggleLog();
            }).view);
            box.addView(card, cardParams());
        } else {
            box.addView(sectionCaption(L.t("主题")));
            MaterialCardView themeCard = filledCard();
            LinearLayout themeBox = cardColumn(themeCard);
            themeBox.addView(settingsRowView(L.t("主题"), themeName(),
                    this::showThemeDialog).view);
            box.addView(themeCard, cardParams());

            box.addView(sectionCaption(L.t("字体大小")));
            MaterialCardView fontCard = filledCard();
            LinearLayout fontBox = cardColumn(fontCard);
            TextView preview = new TextView(this);
            preview.setText(L.t("字体大小预览") + "  Aa 123");
            applyTextAppearance(preview,
                    com.google.android.material.R.attr.textAppearanceHeadlineSmall);
            preview.setTextColor(themeColor(
                    com.google.android.material.R.attr.colorOnSurface));
            preview.setPadding(dp(24), dp(20), dp(24), dp(8));
            fontBox.addView(preview);

            float currentScale = settings().getFloat("fontScale", 1f);
            int currentPercent = Math.round(currentScale * 100f);
            TextView value = new TextView(this);
            value.setText(currentPercent + "%");
            applyTextAppearance(value,
                    com.google.android.material.R.attr.textAppearanceBodyMedium);
            value.setTextColor(themeColor(
                    com.google.android.material.R.attr.colorOnSurfaceVariant));
            value.setPadding(dp(24), 0, dp(24), 0);
            fontBox.addView(value);

            Slider fontSlider = new Slider(this);
            fontSlider.setValueFrom(80f);
            fontSlider.setValueTo(140f);
            fontSlider.setStepSize(1f);
            fontSlider.setValue(currentPercent);
            fontSlider.setLabelBehavior(LabelFormatter.LABEL_FLOATING);
            fontSlider.setLabelFormatter(v -> Math.round(v) + "%");
            LinearLayout.LayoutParams sliderParams = new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT);
            sliderParams.leftMargin = dp(16);
            sliderParams.rightMargin = dp(16);
            fontBox.addView(fontSlider, sliderParams);
            fontSlider.addOnChangeListener((bar, progress, fromUser) -> {
                value.setText(Math.round(progress) + "%");
                preview.setTextSize(TypedValue.COMPLEX_UNIT_SP,
                        24f * progress / 100f);
            });
            fontSlider.addOnSliderTouchListener(new Slider.OnSliderTouchListener() {
                @Override
                public void onStartTrackingTouch(Slider slider) {
                }

                @Override
                public void onStopTrackingTouch(Slider slider) {
                    settings().edit()
                            .putFloat("fontScale", slider.getValue() / 100f)
                            .apply();
                    recreateForFont();
                }
            });
            box.addView(fontCard, cardParams());
        }

        String[] titles = {L.t("设置"), L.t("模拟速度"), L.t("调试"), L.t("外观")};
        LinearLayout pageView = buildPage(titles[page], box,
                page == 0 ? null : this::popPage, true);
        pushPage(pageView);
    }

    /** Adds a full-screen Material page above everything, hiding the LCD. */
    private void pushPage(LinearLayout pageView) {
        int width = getResources().getDisplayMetrics().widthPixels;
        if (pageStack.isEmpty()) {
            surfaceView.setVisibility(View.INVISIBLE);
        }
        root.addView(pageView, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT));
        if (!pageStack.isEmpty()) {
            LinearLayout below = pageStack.get(pageStack.size() - 1);
            below.animate().cancel();
            below.animate().translationX(-width / 2f).scaleX(0.7f).scaleY(0.7f)
                    .alpha(0.5f).setDuration(280)
                    .setInterpolator(new android.view.animation.DecelerateInterpolator(1.6f)).start();
        }
        pageView.setTranslationX(dp(24));
        pageView.setAlpha(1f);
        pageView.animate().translationX(0f).setDuration(220)
                .setInterpolator(new android.view.animation.DecelerateInterpolator(1.6f)).start();
        pageStack.add(pageView);
        pageView.bringToFront();
    }

    private void popPage() {
        if (pageStack.isEmpty()) return;
        int width = getResources().getDisplayMetrics().widthPixels;
        final LinearLayout top = pageStack.remove(pageStack.size() - 1);
        top.animate().cancel();
        top.animate().translationX(width).alpha(0f).setDuration(240)
                .setInterpolator(new android.view.animation.AccelerateInterpolator(1.4f))
                .withEndAction(() -> root.removeView(top)).start();
        if (!pageStack.isEmpty()) {
            LinearLayout below = pageStack.get(pageStack.size() - 1);
            below.animate().cancel();
            below.animate().translationX(0f).scaleX(1f).scaleY(1f).alpha(1f)
                    .setDuration(260)
                    .setInterpolator(new android.view.animation.DecelerateInterpolator(1.4f)).start();
        } else {
            surfaceView.setVisibility(View.VISIBLE);
            PrimeShim.nativeRequestRedraw();
        }
    }

    private boolean isDarkTheme() {
        int mode = AppCompatDelegate.getDefaultNightMode();
        if (mode == AppCompatDelegate.MODE_NIGHT_YES) return true;
        if (mode == AppCompatDelegate.MODE_NIGHT_NO) return false;
        return (getResources().getConfiguration().uiMode
                & android.content.res.Configuration.UI_MODE_NIGHT_MASK)
                == android.content.res.Configuration.UI_MODE_NIGHT_YES;
    }

    private void toggleTheme(View anchor) {
        int next = isDarkTheme() ? AppCompatDelegate.MODE_NIGHT_NO
                : AppCompatDelegate.MODE_NIGHT_YES;
        applyThemeWithReveal(next, anchor);
    }

    private LinearLayout buildPage(String title, View content, Runnable onBack) {
        return buildPage(title, content, onBack, false, true);
    }

    private LinearLayout buildPage(String title, View content, Runnable onBack,
                                   boolean themeToggle) {
        return buildPage(title, content, onBack, themeToggle, true);
    }

    private LinearLayout buildFixedPage(String title, View content, Runnable onBack,
                                        View... actions) {
        return buildPage(title, content, onBack, false, false, actions);
    }

    private LinearLayout buildPage(String title, View content, Runnable onBack,
                                   boolean themeToggle, boolean scrollable,
                                   View... actions) {
        LinearLayout page = new LinearLayout(this);
        page.setOrientation(LinearLayout.VERTICAL);
        page.setMinimumWidth(getResources().getDisplayMetrics().widthPixels);
        page.setMinimumHeight(getResources().getDisplayMetrics().heightPixels);
        page.setElevation(dp(8));
        page.setClickable(true);
        page.setBackgroundColor(themeColor(
                com.google.android.material.R.attr.colorSurface));

        int icon = onBack == null ? R.drawable.ic_close : R.drawable.ic_arrow_back;
        page.addView(navigationBar(icon, () -> {
            if (onBack != null) onBack.run();
            else popPage();
        }), new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, dp(64)));

        LinearLayout titleRow = new LinearLayout(this);
        titleRow.setOrientation(LinearLayout.HORIZONTAL);
        titleRow.setGravity(Gravity.CENTER_VERTICAL);

        TextView titleView = new TextView(this);
        titleView.setText(title);
        applyTextAppearance(titleView,
                com.google.android.material.R.attr.textAppearanceHeadlineMedium);
        titleView.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        titleView.setPadding(dp(16), dp(4), dp(12), dp(16));
        titleRow.addView(titleView, new LinearLayout.LayoutParams(
                0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f));

        if (themeToggle) {
            ImageView themeIcon = new ImageView(this);
            themeIcon.setImageResource(isDarkTheme()
                    ? R.drawable.ic_light_mode : R.drawable.ic_dark_mode);
            themeIcon.setImageTintList(ColorStateList.valueOf(themeColor(
                    com.google.android.material.R.attr.colorOnSurfaceVariant)));
            themeIcon.setContentDescription(L.t(isDarkTheme()
                    ? "切换到亮色主题" : "切换到暗色主题"));
            themeIcon.setBackground(ripple());
            themeIcon.setPadding(dp(12), dp(12), dp(12), dp(12));
            themeIcon.setClickable(true);
            themeIcon.setOnClickListener(this::toggleTheme);
            LinearLayout.LayoutParams iconParams = new LinearLayout.LayoutParams(
                    dp(48), dp(48));
            iconParams.rightMargin = dp(12);
            titleRow.addView(themeIcon, iconParams);
        }
        if (actions != null) {
            for (View action : actions) {
                LinearLayout.LayoutParams params = new LinearLayout.LayoutParams(
                        dp(40), dp(40));
                params.rightMargin = dp(2);
                titleRow.addView(action, params);
            }
        }
        page.addView(titleRow, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        if (scrollable) {
            ScrollView scroll = new ScrollView(this);
            scroll.setClipToPadding(false);
            scroll.setPadding(dp(16), 0, dp(16), dp(16));
            scroll.addView(content, new FrameLayout.LayoutParams(
                    FrameLayout.LayoutParams.MATCH_PARENT,
                    FrameLayout.LayoutParams.WRAP_CONTENT));
            page.addView(scroll, new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f));
        } else {
            FrameLayout body = new FrameLayout(this);
            body.setPadding(dp(16), 0, dp(16), dp(16));
            body.addView(content, new FrameLayout.LayoutParams(
                    FrameLayout.LayoutParams.MATCH_PARENT,
                    FrameLayout.LayoutParams.MATCH_PARENT));
            page.addView(body, new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f));
        }

        padForCutout(page);
        return page;
    }

    private LinearLayout.LayoutParams cardParams() {
        LinearLayout.LayoutParams params = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT);
        params.bottomMargin = dp(16);
        return params;
    }

    private TextView sectionCaption(String text) {
        TextView caption = new TextView(this);
        caption.setText(text);
        applyTextAppearance(caption,
                com.google.android.material.R.attr.textAppearanceLabelLarge);
        caption.setTextColor(themeColor(
                com.google.android.material.R.attr.colorPrimary));
        caption.setPadding(0, dp(16), 0, dp(8));
        caption.setLayoutParams(new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
        return caption;
    }

    private static final class SettingsRow {
        final LinearLayout view;
        final TextView title;
        final TextView supporting;

        SettingsRow(LinearLayout view, TextView title, TextView supporting) {
            this.view = view;
            this.title = title;
            this.supporting = supporting;
        }
    }

    private SettingsRow settingsRowView(String title, String supporting, Runnable action) {
        return settingsRowView(title, supporting, action, null);
    }

    private SettingsRow settingsRowView(String title, String supporting,
                                        Runnable action, View trailing) {
        LinearLayout row = new LinearLayout(this);
        row.setOrientation(LinearLayout.HORIZONTAL);
        row.setGravity(Gravity.CENTER_VERTICAL);
        row.setPadding(dp(16), dp(12), dp(16), dp(12));
        row.setMinimumHeight(dp(72));
        row.setBackground(ripple());

        LinearLayout texts = new LinearLayout(this);
        texts.setOrientation(LinearLayout.VERTICAL);

        TextView headline = new TextView(this);
        headline.setText(title);
        applyTextAppearance(headline,
                com.google.android.material.R.attr.textAppearanceBodyLarge);
        headline.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurface));
        texts.addView(headline, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        TextView sub = null;
        if (supporting != null && !supporting.isEmpty()) {
            sub = new TextView(this);
            sub.setText(supporting);
            applyTextAppearance(sub,
                    com.google.android.material.R.attr.textAppearanceBodyMedium);
            sub.setTextColor(themeColor(
                    com.google.android.material.R.attr.colorOnSurfaceVariant));
            sub.setPadding(0, dp(2), 0, 0);
            texts.addView(sub, new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.MATCH_PARENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT));
        }
        row.addView(texts, new LinearLayout.LayoutParams(0,
                LinearLayout.LayoutParams.WRAP_CONTENT, 1f));

        if (trailing != null) {
            LinearLayout.LayoutParams params = new LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.WRAP_CONTENT,
                    LinearLayout.LayoutParams.WRAP_CONTENT);
            params.leftMargin = dp(8);
            row.addView(trailing, params);
        } else if (action != null) {
            ImageView chevron = new ImageView(this);
            chevron.setImageResource(R.drawable.ic_chevron_right);
            chevron.setImageTintList(ColorStateList.valueOf(themeColor(
                    com.google.android.material.R.attr.colorOnSurfaceVariant)));
            chevron.setImportantForAccessibility(
                    View.IMPORTANT_FOR_ACCESSIBILITY_NO);
            LinearLayout.LayoutParams params = new LinearLayout.LayoutParams(dp(24), dp(24));
            params.leftMargin = dp(8);
            row.addView(chevron, params);
        }

        row.setLayoutParams(new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
        if (action != null) {
            row.setOnClickListener(v -> action.run());
        }
        return new SettingsRow(row, headline, sub);
    }

    private android.content.SharedPreferences settings() {
        return getSharedPreferences("primeshim", MODE_PRIVATE);
    }

    /* ---- about ------------------------------------------------------- */

    private void showAbout() {
        LinearLayout content = new LinearLayout(this);
        content.setOrientation(LinearLayout.VERTICAL);

        MaterialCardView avatarCard = filledCard();
        avatarCard.setCardBackgroundColor(themeColor(
                com.google.android.material.R.attr.colorPrimaryContainer));
        avatarCard.setRadius(dp(28));

        LinearLayout avatar = new LinearLayout(this);
        avatar.setOrientation(LinearLayout.VERTICAL);
        avatar.setGravity(Gravity.CENTER);
        avatar.setPadding(dp(24), dp(24), dp(24), dp(24));

        ImageView logo = new ImageView(this);
        logo.setImageResource(R.drawable.ic_nb_mark);
        logo.setImageTintList(ColorStateList.valueOf(themeColor(
                com.google.android.material.R.attr.colorOnPrimaryContainer)));
        avatar.addView(logo, new LinearLayout.LayoutParams(dp(64), dp(64)));

        TextView name = new TextView(this);
        name.setText("PrimeShim");
        applyTextAppearance(name,
                com.google.android.material.R.attr.textAppearanceHeadlineSmall);
        name.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnPrimaryContainer));
        name.setGravity(Gravity.CENTER);
        name.setPadding(0, dp(12), 0, 0);
        avatar.addView(name, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        TextView tagline = new TextView(this);
        tagline.setText(L.t("HP Prime 模拟器"));
        applyTextAppearance(tagline,
                com.google.android.material.R.attr.textAppearanceBodyMedium);
        tagline.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnPrimaryContainer));
        tagline.setGravity(Gravity.CENTER);
        tagline.setPadding(0, dp(2), 0, 0);
        avatar.addView(tagline, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        avatarCard.addView(avatar, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.WRAP_CONTENT));
        content.addView(avatarCard, cardParams());

        String version = "?";
        try {
            version = getPackageManager().getPackageInfo(getPackageName(), 0).versionName;
        } catch (Exception ignored) {
        }

        MaterialCardView infoCard = filledCard();
        LinearLayout info = cardColumn(infoCard);
        info.addView(settingsRowView(L.t("版本"),
                version + " · build " + BuildConfig.BUILD_STAMP, null).view);
        info.addView(divider());
        info.addView(settingsRowView(L.t("设备"),
                Build.MANUFACTURER + " " + Build.MODEL
                        + " · Android " + Build.VERSION.RELEASE,
                this::copyDeviceInfo).view);
        content.addView(infoCard, cardParams());

        content.addView(sectionCaption(L.t("链接")));
        MaterialCardView linksCard = filledCard();
        LinearLayout links = cardColumn(linksCard);
        links.addView(externalRow(L.t("源代码"), "github.com/SQY419/PrimeShim",
                "https://github.com/SQY419/PrimeShim").view);
        links.addView(divider());
        links.addView(externalRow(L.t("PrimeShim 上游"), "Natsuki-Min/PrimeShim",
                "https://github.com/Natsuki-Min/PrimeShim").view);
        links.addView(divider());
        links.addView(externalRow("PrimeU2", "telecomadm1145/PrimeU2",
                "https://github.com/telecomadm1145/PrimeU2").view);
        links.addView(divider());
        links.addView(externalRow("Material Components", "Apache License 2.0",
                "https://github.com/material-components/material-components-android").view);
        links.addView(divider());
        links.addView(externalRow("Material Icons", "Apache License 2.0",
                "https://github.com/google/material-design-icons").view);
        content.addView(linksCard, cardParams());

        content.addView(sectionCaption(L.t("说明")));
        TextView note = new TextView(this);
        note.setText(L.t("PrimeShim 是 HP Prime 固件的兼容层：运行时加载原始 ARM ELF，")
                + L.t("把 BESTA 系统调用和硬件访问接到 Linux 实现上。\n\n")
                + L.t("固件不随应用分发，请自行导入你有权使用的固件。"));
        applyTextAppearance(note,
                com.google.android.material.R.attr.textAppearanceBodyMedium);
        note.setTextColor(themeColor(
                com.google.android.material.R.attr.colorOnSurfaceVariant));
        note.setLineSpacing(dp(3), 1f);
        note.setPadding(dp(8), 0, dp(8), dp(16));
        content.addView(note, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        pushPage(buildPage(L.t("关于"), content, this::popPage));
    }

    private String deviceInfoText() {
        String version = "?";
        try {
            version = getPackageManager().getPackageInfo(
                    getPackageName(), 0).versionName;
        } catch (Exception ignored) {
        }
        android.util.DisplayMetrics metrics = getResources().getDisplayMetrics();
        StringBuilder text = new StringBuilder();
        text.append("PrimeShim ").append(version)
                .append(" · build ").append(BuildConfig.BUILD_STAMP).append('\n');
        text.append(L.t("设备: ")).append(Build.MANUFACTURER).append(' ')
                .append(Build.MODEL).append('\n');
        text.append(L.t("品牌/设备/硬件: ")).append(Build.BRAND).append(" / ")
                .append(Build.DEVICE).append(" / ").append(Build.HARDWARE).append('\n');
        text.append("Android: ").append(Build.VERSION.RELEASE)
                .append(" (API ").append(Build.VERSION.SDK_INT).append(")\n");
        text.append(L.t("屏幕: ")).append(metrics.widthPixels).append('x')
                .append(metrics.heightPixels).append(" @ ")
                .append(metrics.densityDpi).append("dpi")
                .append(" (density ").append(metrics.density).append(")\n");
        text.append("ABI: ");
        for (int i = 0; i < Build.SUPPORTED_ABIS.length; ++i) {
            if (i > 0) text.append(", ");
            text.append(Build.SUPPORTED_ABIS[i]);
        }
        text.append('\n');
        text.append(L.t("指纹: ")).append(Build.FINGERPRINT).append('\n');
        return text.toString();
    }

    /** The About device row copies this directly to the clipboard. */
    private void copyDeviceInfo() {
        String text = deviceInfoText();
        ClipboardManager clipboard =
                (ClipboardManager) getSystemService(Context.CLIPBOARD_SERVICE);
        if (clipboard == null) {
            snack(L.t("剪贴板不可用"));
            return;
        }
        clipboard.setPrimaryClip(ClipData.newPlainText("PrimeShim device", text));
        snack(L.t("设备信息已复制"));
    }

    private SettingsRow externalRow(String title, String supporting, final String url) {
        ImageView open = new ImageView(this);
        open.setImageResource(R.drawable.ic_open_in_new);
        open.setImageTintList(ColorStateList.valueOf(themeColor(
                com.google.android.material.R.attr.colorOnSurfaceVariant)));
        open.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
        return settingsRowView(title, supporting, () -> openLink(url), open);
    }

    private void openLink(String url) {
        try {
            startActivity(new Intent(Intent.ACTION_VIEW, Uri.parse(url)));
        } catch (Exception error) {
            snack(L.t("没有可用的浏览器"));
        }
    }

    /* ---- guest crash handling ---------------------------------------- */

    private void showLastCrashPrompt() {
        final String report = settings().getString("lastCrash",
                L.t("固件上次启动时崩溃，没有留下报告。"));
        runOnUiThread(() -> new MaterialAlertDialogBuilder(this)
                .setTitle(L.t("固件崩溃"))
                .setMessage(report)
                .setPositiveButton(L.t("仍然启动"), (dialog, which) -> {
                    settings().edit().putBoolean("guestCrashed", false)
                            .remove("lastCrash").apply();
                    crashShown = false;
                    startGuest();
                })
                .setNeutralButton(L.t("选择固件"), (dialog, which) -> pickFirmware())
                .setNegativeButton(L.t("关闭"), null)
                .show());
    }

    private void showGuestCrash(String report) {
        new MaterialAlertDialogBuilder(this)
                .setTitle(L.t("固件崩溃"))
                .setMessage(report)
                .setPositiveButton(L.t("查看日志"), (dialog, which) -> {
                    if (logPanel.getVisibility() != View.VISIBLE) toggleLog();
                })
                .setNegativeButton(L.t("关闭"), null)
                .show();
    }

    /* ---- reset / data ------------------------------------------------ */

    private void confirmClearData() {
        new MaterialAlertDialogBuilder(this)
                .setTitle(L.t("清除数据"))
                .setMessage(L.t("删除已导入的固件、A:/C: 数据和崩溃记录？\n\n")
                        + L.t("重启后是空白状态，需要重新导入官方升级包")
                        + L.t("zip 或 PRIME_APP.DAT。"))
                .setPositiveButton(L.t("清除并重启"), (dialog, which) -> clearAllData())
                .setNegativeButton(L.t("取消"), null)
                .show();
    }

    private void clearAllData() {
        suppressCrash = true;
        uiHandler.removeCallbacks(guestCrashWatch);
        try {
            PrimeShim.nativeStop();
        } catch (Throwable ignored) {
        }
        /* Delete every profile, not just the active one.  A stale profile is
         * keyed by ELF hash and would otherwise be reused when the same
         * firmware is imported again (with its old A:/dummy.DAT). */
        File profiles = profilesDir != null
                ? profilesDir : new File(getFilesDir(), "profiles");
        deleteRecursive(profiles);
        deleteRecursive(new File(getFilesDir(), WORK_DIR_NAME));
        //noinspection ResultOfMethodCallIgnored
        new File(getFilesDir(), "active_profile").delete();
        settings().edit().clear().apply();
        restartApp(true);
    }

    private static void deleteRecursive(File file) {
        if (file == null) return;
        File[] children = file.listFiles();
        if (children != null) {
            for (File child : children) {
                deleteRecursive(child);
            }
        }
        //noinspection ResultOfMethodCallIgnored
        file.delete();
    }

    private void restartApp() {
        restartApp(false);
    }

    private void restartApp(boolean skipSplash) {
        suppressCrash = true;
        uiHandler.removeCallbacks(guestCrashWatch);
        Intent intent = new Intent(this, MainActivity.class);
        intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK
                | Intent.FLAG_ACTIVITY_CLEAR_TASK);
        if (skipSplash) {
            intent.putExtra(EXTRA_SKIP_SPLASH, true);
        }
        PendingIntent pending = PendingIntent.getActivity(this, 0, intent,
                PendingIntent.FLAG_CANCEL_CURRENT | PendingIntent.FLAG_IMMUTABLE);
        AlarmManager alarm = (AlarmManager) getSystemService(ALARM_SERVICE);
        if (alarm != null) {
            alarm.set(AlarmManager.RTC, System.currentTimeMillis() + 600, pending);
        }
        finishAffinity();
        android.os.Process.killProcess(android.os.Process.myPid());
    }

    private void promptFirmwareImport() {
        new MaterialAlertDialogBuilder(this)
                .setTitle(L.t("固件"))
                .setMessage(L.t("导入官方升级包 zip 或 PRIME_APP.DAT？\n\n")
                        + L.t("也可以一次多选 PRIME_APP.DAT、PRIME_MASTER.DAT、")
                        + L.t("PRIME_OS.ROM；app 会自动使用 PRIME_APP.DAT，其余忽略。\n\n")
                        + L.t("A: 系统盘会从 PRIME_APP.DAT 里解出，C: 从空目录开始。"))
                .setPositiveButton(L.t("导入"), (dialog, which) -> pickFirmware())
                .setNegativeButton(L.t("取消"), null)
                .show();
    }

    private void toggleLog() {
        if (logPanel.getVisibility() != View.VISIBLE
                && keyboardView.getVisibility() == View.VISIBLE) {
            toggleKeyboard(); /* hide it, the panel needs the space */
        }
        if (logPanel.getVisibility() == View.VISIBLE) {
            logPanel.setVisibility(View.GONE);
            uiHandler.removeCallbacks(logRefresh);
            surfaceView.setVisibility(View.VISIBLE);
            PrimeShim.nativeRequestRedraw();
        } else {
            surfaceView.setVisibility(View.INVISIBLE);
            logPanel.setVisibility(View.VISIBLE);
            logPanel.bringToFront();
            refreshLog();
            uiHandler.removeCallbacks(logRefresh);
            uiHandler.postDelayed(logRefresh, 1000);
        }
    }

    private void refreshLog() {
        String text;
        try {
            text = PrimeShim.nativeLog();
        } catch (Throwable error) {
            text = L.t("无法读取日志: ") + error;
        }
        if (text == null || text.isEmpty()) {
            text = L.t("暂无日志");
        }
        logText.setText(text);
        logScroll.post(new Runnable() {
            @Override
            public void run() {
                logScroll.fullScroll(View.FOCUS_DOWN);
            }
        });
    }

    /** Writes the live firmware framebuffer into the gallery so it can be
     *  inspected outside the app (no accessibility service needed). */
    private void saveSnapshot() {
        int[] pixels;
        try {
            pixels = PrimeShim.nativeSnapshot();
        } catch (Throwable error) {
            snack(L.t("无法读取帧缓冲: ") + error);
            return;
        }
        if (pixels == null || pixels.length < FW_WIDTH * FW_HEIGHT) {
            snack(L.t("固件还没启动"));
            return;
        }

        Bitmap frame = Bitmap.createBitmap(FW_WIDTH, FW_HEIGHT, Bitmap.Config.ARGB_8888);
        frame.setPixels(pixels, 0, FW_WIDTH, 0, 0, FW_WIDTH, FW_HEIGHT);
        Bitmap scaled = Bitmap.createScaledBitmap(frame, FW_WIDTH * 3, FW_HEIGHT * 3, false);
        String name = "PrimeShim-" + BuildConfig.BUILD_STAMP + ".png";

        try {
            if (Build.VERSION.SDK_INT >= 29) {
                ContentValues values = new ContentValues();
                values.put(MediaStore.Images.Media.DISPLAY_NAME, name);
                values.put(MediaStore.Images.Media.MIME_TYPE, "image/png");
                values.put(MediaStore.Images.Media.RELATIVE_PATH,
                        Environment.DIRECTORY_PICTURES + "/PrimeShim");
                Uri target = getContentResolver()
                        .insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, values);
                if (target == null) {
                    throw new IOException(L.t("MediaStore 拒绝写入"));
                }
                OutputStream out = getContentResolver().openOutputStream(target);
                try {
                    scaled.compress(Bitmap.CompressFormat.PNG, 100, out);
                } finally {
                    closeQuietly(out);
                }
                snack(L.t("已保存到相册 Pictures/PrimeShim/") + name);
            } else {
                File dir = new File(getExternalFilesDir(null), "snapshots");
                if (!dir.isDirectory() && !dir.mkdirs()) {
                    throw new IOException("cannot create " + dir);
                }
                File target = new File(dir, name);
                OutputStream out = new FileOutputStream(target);
                try {
                    scaled.compress(Bitmap.CompressFormat.PNG, 100, out);
                } finally {
                    closeQuietly(out);
                }
                snack(L.t("已保存: ") + target);
            }
        } catch (Exception error) {
            Log.e(TAG, "snapshot failed", error);
            snack(L.t("保存失败: ") + error.getMessage());
        }
    }

    /** Writes the whole captured log next to the snapshots so it can be sent
     *  as a file instead of being pasted line by line. */
    private void saveLogFile() {
        String text;
        try {
            text = PrimeShim.nativeLog();
        } catch (Throwable error) {
            snack(L.t("无法读取日志: ") + error);
            return;
        }
        if (text == null || text.isEmpty()) {
            snack(L.t("日志为空"));
            return;
        }
        String name = "PrimeShim-" + BuildConfig.BUILD_STAMP + ".log";
        try {
            if (Build.VERSION.SDK_INT >= 29) {
                ContentValues values = new ContentValues();
                values.put(MediaStore.Downloads.DISPLAY_NAME, name);
                values.put(MediaStore.Downloads.MIME_TYPE, "text/plain");
                values.put(MediaStore.Downloads.RELATIVE_PATH,
                        Environment.DIRECTORY_DOWNLOADS + "/PrimeShim");
                Uri target = getContentResolver()
                        .insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, values);
                if (target == null) throw new IOException(L.t("MediaStore 拒绝写入"));
                OutputStream out = getContentResolver().openOutputStream(target);
                try {
                    out.write(text.getBytes("UTF-8"));
                } finally {
                    closeQuietly(out);
                }
                snack(L.t("已保存到 Download/PrimeShim/") + name);
            } else {
                File dir = new File(getExternalFilesDir(null), "logs");
                if (!dir.isDirectory() && !dir.mkdirs()) throw new IOException("mkdir");
                File target = new File(dir, name);
                OutputStream out = new FileOutputStream(target);
                try {
                    out.write(text.getBytes("UTF-8"));
                } finally {
                    closeQuietly(out);
                }
                snack(L.t("已保存: ") + target);
            }
        } catch (Exception error) {
            Log.e(TAG, "log export failed", error);
            snack(L.t("保存失败: ") + error.getMessage());
        }
    }


    /** One-shot calibration: presses every key in turn, diffs the firmware frame
     *  before and after, and lays the resulting glyph next to the key name. */
    private void runKeyCalibration() {
        setStatus(L.t("校准中：先确认画面停在有输入行的界面，例如函数应用"), false);
        new Thread(new Runnable() {
            @Override
            public void run() {
                int count = keyboardView.keyCount();
                java.util.ArrayList<String> labels = new java.util.ArrayList<>();
                java.util.ArrayList<Bitmap> glyphs = new java.util.ArrayList<>();

                int[] startFrame = PrimeShim.nativeSnapshot();
                if (startFrame != null) {
                    Bitmap first = Bitmap.createBitmap(320, 240, Bitmap.Config.ARGB_8888);
                    first.setPixels(startFrame, 0, 320, 0, 0, 320, 240);
                    saveBitmap(first, "keymap-start-" + BuildConfig.BUILD_STAMP + ".png");
                }

                for (int i = 0; i < count; ++i) {
                    int[] before = PrimeShim.nativeSnapshot();
                    int wire = PrimeKeyboardView.wire(keyboardView.keyCodeAt(i));
                    PrimeShim.nativeKeyBatch(wire, 1);
                    try { Thread.sleep(90); } catch (InterruptedException ignored) { }
                    PrimeShim.nativeKeyBatch(wire, 0);
                    try { Thread.sleep(280); } catch (InterruptedException ignored) { }
                    int[] after = PrimeShim.nativeSnapshot();
                    if (before == null || after == null || before.length < 320 * 240) break;

                    int minX = 320, maxX = -1, minY = 240, maxY = -1;
                    for (int y = 28; y < 210; ++y) { /* whole screen except clock and soft keys */
                        for (int x = 0; x < 320; ++x) {
                            int p = y * 320 + x;
                            if (before[p] != after[p]) {
                                if (x < minX) minX = x;
                                if (x > maxX) maxX = x;
                                if (y < minY) minY = y;
                                if (y > maxY) maxY = y;
                            }
                        }
                    }
                    labels.add(keyboardView.keyNameAt(i));
                    if (maxX < minX || maxY < minY) {
                        glyphs.add(null);
                        continue;
                    }
                    int w = maxX - minX + 1;
                    int h = maxY - minY + 1;
                    Bitmap crop = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888);
                    int[] pixels = new int[w * h];
                    for (int y = 0; y < h; ++y) {
                        System.arraycopy(after, (minY + y) * 320 + minX, pixels, y * w, w);
                    }
                    crop.setPixels(pixels, 0, w, 0, 0, w, h);
                    glyphs.add(crop);
                }

                Bitmap sheet = buildCalibrationSheet(labels, glyphs);
                saveBitmap(sheet, "keymap-" + BuildConfig.BUILD_STAMP + ".png");
                glyphs.clear();
                setStatus(null, false);
            }
        }, "primeshim-calib").start();
    }

    /** Tall image: key name on the left, the glyph it produced on the right. */
    private Bitmap buildCalibrationSheet(java.util.List<String> labels,
                                         java.util.List<Bitmap> glyphs) {
        int rowHeight = 34;
        int width = 420;
        Bitmap sheet = Bitmap.createBitmap(width, Math.max(1, labels.size() * rowHeight),
                Bitmap.Config.ARGB_8888);
        Canvas canvas = new Canvas(sheet);
        canvas.drawColor(Color.WHITE);
        Paint text = new Paint();
        text.setColor(Color.BLACK);
        text.setTextSize(16f);
        Paint frame = new Paint();
        frame.setColor(0xFF888888);
        frame.setStyle(Paint.Style.STROKE);
        for (int i = 0; i < labels.size(); ++i) {
            int top = i * rowHeight;
            canvas.drawText(labels.get(i), 6, top + 22, text);
            Bitmap glyph = glyphs.get(i);
            if (glyph == null) {
                canvas.drawText("(no change)", 180, top + 22, text);
            } else {
                Rect dst = new Rect(180, top + 2, 180 + Math.min(220, glyph.getWidth() * 2),
                        top + 2 + Math.min(30, glyph.getHeight() * 2));
                canvas.drawBitmap(glyph, null, dst, null);
            }
            canvas.drawLine(0, top + rowHeight - 1, width, top + rowHeight - 1, frame);
        }
        return sheet;
    }


    /** Writes a bitmap into Pictures/PrimeShim (or app storage before API 29). */
    private void saveBitmap(Bitmap bitmap, String name) {
        try {
            if (Build.VERSION.SDK_INT >= 29) {
                ContentValues values = new ContentValues();
                values.put(MediaStore.Images.Media.DISPLAY_NAME, name);
                values.put(MediaStore.Images.Media.MIME_TYPE, "image/png");
                values.put(MediaStore.Images.Media.RELATIVE_PATH,
                        Environment.DIRECTORY_PICTURES + "/PrimeShim");
                Uri target = getContentResolver()
                        .insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, values);
                if (target == null) throw new IOException(L.t("MediaStore 拒绝写入"));
                OutputStream out = getContentResolver().openOutputStream(target);
                try { bitmap.compress(Bitmap.CompressFormat.PNG, 100, out); }
                finally { closeQuietly(out); }
            } else {
                File dir = new File(getExternalFilesDir(null), "snapshots");
                if (!dir.isDirectory() && !dir.mkdirs()) throw new IOException("mkdir");
                OutputStream out = new FileOutputStream(new File(dir, name));
                try { bitmap.compress(Bitmap.CompressFormat.PNG, 100, out); }
                finally { closeQuietly(out); }
            }
            Log.i(TAG, "saved " + name);
        } catch (Exception error) {
            Log.e(TAG, "cannot save " + name, error);
        }
    }


    private void copyLog() {
        CharSequence text = logText.getText();
        if (text == null || text.length() == 0) {
            snack(L.t("没有可复制的日志"));
            return;
        }
        ClipboardManager clipboard =
                (ClipboardManager) getSystemService(Context.CLIPBOARD_SERVICE);
        if (clipboard == null) {
            snack(L.t("剪贴板不可用"));
            return;
        }
        clipboard.setPrimaryClip(ClipData.newPlainText("PrimeShim log", text));
        snack(L.t("已复制 ") + text.length() + L.t(" 字符"));
    }

    /* ---- firmware acquisition --------------------------------------- */

    /**
     * User app directories copied from an older firmware sometimes lost their
     * icon.png.  The 15xxx app launcher passes the icon handle straight into
     * the app object constructor, so a missing icon becomes a NULL+4 fault
     * when the library is opened.  Give every app directory a default icon.
     */
    private void repairAppIcons() {
        File data = dataFolder();
        File[] entries = data.listFiles();
        if (entries == null) return;
        for (File entry : entries) {
            if (!entry.isDirectory() || !entry.getName().endsWith(".hpappdir")
                    || entry.getName().startsWith("&")) {
                continue;
            }
            File icon = new File(entry, "icon.png");
            if (!icon.isFile()) {
                try {
                    copyAsset(getAssets(), "app_icon_default.png", icon);
                    Log.i(TAG, "restored missing app icon: " + icon);
                } catch (IOException error) {
                    Log.w(TAG, "cannot restore " + icon, error);
                }
            }
        }
    }

    /* ---- per-firmware profiles --------------------------------------- */
    /*
     * A firmware and its A:/C: data are a pair.  Switching the ELF while
     * keeping another generation's prime_data makes the app launcher read
     * stale offsets.  Keep one directory per firmware hash, and re-importing
     * the same firmware restores the data that belonged to it.
     */

    private void prepareProfile() {
        profilesDir = new File(getFilesDir(), "profiles");
        if (!profilesDir.isDirectory() && !profilesDir.mkdirs()) {
            Log.e(TAG, "cannot create profiles directory");
        }
        File activeFile = new File(getFilesDir(), "active_profile");
        String id = readActive(activeFile);
        if (id == null || !new File(profilesDir, id).isDirectory()) {
            File legacy = new File(getFilesDir(), WORK_DIR_NAME);
            File legacyFirmware = new File(legacy, FIRMWARE_NAME);
            File legacyData = new File(legacy, "prime_data");
            if (legacyFirmware.isFile()) {
                id = sha256(legacyFirmware).substring(0, 16);
            } else {
                id = "default";
            }
            File destination = new File(profilesDir, id);
            //noinspection ResultOfMethodCallIgnored
            destination.mkdirs();
            if (legacyFirmware.isFile()) {
                movePath(legacyFirmware, new File(destination, FIRMWARE_NAME));
            }
            if (legacyData.isDirectory()) {
                movePath(legacyData, new File(destination, "prime_data"));
            }
            writeActive(activeFile, id);
            Log.i(TAG, "migrated firmware profile " + id);
        }
        activeProfile = id;
        workDir = new File(profilesDir, id);
        //noinspection ResultOfMethodCallIgnored
        workDir.mkdirs();
        firmwareFile = new File(workDir, FIRMWARE_NAME);
    }

    private static String readActive(File file) {
        if (!file.isFile()) return null;
        try {
            byte[] data = new byte[(int) Math.min(file.length(), 256)];
            FileInputStream in = new FileInputStream(file);
            try {
                int count = in.read(data);
                if (count <= 0) return null;
                String text = new String(data, 0, count, "UTF-8").trim();
                return text.isEmpty() ? null : text;
            } finally {
                closeQuietly(in);
            }
        } catch (IOException error) {
            return null;
        }
    }

    private void writeActive(File file, String id) {
        try {
            FileOutputStream out = new FileOutputStream(file);
            try {
                out.write(id.getBytes("UTF-8"));
            } finally {
                closeQuietly(out);
            }
        } catch (IOException error) {
            Log.w(TAG, "cannot write active profile", error);
        }
    }

    private static String sha256(File file) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            InputStream in = new FileInputStream(file);
            try {
                byte[] buffer = new byte[128 * 1024];
                int count;
                while ((count = in.read(buffer)) > 0) {
                    digest.update(buffer, 0, count);
                }
            } finally {
                closeQuietly(in);
            }
            StringBuilder hex = new StringBuilder();
            for (byte value : digest.digest()) {
                hex.append(String.format(java.util.Locale.US, "%02x", value));
            }
            return hex.toString();
        } catch (Exception error) {
            Log.w(TAG, "cannot hash firmware", error);
            return Long.toHexString(file.length()) + Long.toHexString(file.lastModified());
        }
    }

    /**
     * Refreshes the A: volume from PRIME_APP.DAT while keeping C: intact.
     *
     * A: is system data and must always match the ELF; C: is the user's
     * partition.  Reusing an old profile by ELF hash must not keep an old
     * dummy.DAT or an old A: tree.
     */
    private void prepareProfileFromPackage(File profile, File container)
            throws IOException {
        File dataRoot = new File(profile, "prime_data");
        File dataC = new File(dataRoot, "C");
        if (!dataRoot.isDirectory() && !dataRoot.mkdirs()) {
            throw new IOException(L.t("无法创建 ") + dataRoot);
        }
        if (!dataC.isDirectory() && !dataC.mkdirs()) {
            throw new IOException(L.t("无法创建 ") + dataC);
        }

        File build = new File(profilesDir, ".build-A-" + profile.getName());
        deleteRecursive(build);
        File dataA = new File(build, "A");
        if (!dataA.mkdirs()) {
            throw new IOException(L.t("无法创建 ") + dataA);
        }

        FirmwarePackage.Result result = FirmwarePackage.extractAppDisk(
                container, dataA, path -> { });
        if (result.files == 0) {
            throw new IOException(L.t("PRIME_APP.DAT 里的 A: 盘是空的"));
        }
        if (result.manifestFiles > 0 && result.manifestMismatches > 0) {
            throw new IOException(L.t("A: 盘校验失败：")
                    + result.manifestMismatches + "/" + result.manifestFiles
                    + L.t(" 个文件与 APPSLIST.MD5 不一致"));
        }

        File targetA = new File(dataRoot, "A");
        File backup = new File(dataRoot, ".A-old");
        deleteRecursive(backup);
        if (targetA.exists() && !targetA.renameTo(backup)) {
            deleteRecursive(targetA);
        }
        if (!dataA.renameTo(targetA)) {
            copyRecursive(dataA, targetA);
            deleteRecursive(dataA);
        }
        deleteRecursive(backup);
        deleteRecursive(build);

        File firstRun = new File(profile, ".first_run");
        //noinspection ResultOfMethodCallIgnored
        firstRun.createNewFile();
        Log.i(TAG, "A: refreshed " + result.files + " files ("
                + result.bytes + " bytes), dummy=" + result.dummyCreated
                + ", manifest=" + (result.manifestFiles
                - result.manifestMismatches) + "/" + result.manifestFiles);
    }

    private static void movePath(File source, File target) {
        if (source.renameTo(target)) return;
        try {
            copyRecursive(source, target);
            deleteRecursive(source);
        } catch (IOException error) {
            Log.w(TAG, "cannot move " + source + " to " + target, error);
        }
    }

    private static void copyRecursive(File source, File target) throws IOException {
        if (source.isDirectory()) {
            if (!target.isDirectory() && !target.mkdirs()) {
                throw new IOException("cannot create " + target);
            }
            File[] children = source.listFiles();
            if (children == null) return;
            for (File child : children) {
                copyRecursive(child, new File(target, child.getName()));
            }
            return;
        }
        InputStream in = new FileInputStream(source);
        try {
            OutputStream out = new FileOutputStream(target);
            try {
                byte[] buffer = new byte[128 * 1024];
                int count;
                while ((count = in.read(buffer)) > 0) {
                    out.write(buffer, 0, count);
                }
            } finally {
                closeQuietly(out);
            }
        } finally {
            closeQuietly(in);
        }
    }

    /**
     * UI-only assets (keyboard skins, fallback icon).  Firmware, A: and C:
     * are never bundled: they come from the user's official PRIME_APP.DAT.
     */
    private void extractAssets() {
        /* Nothing to extract.  Kept as a named hook for the bootstrap flow. */
    }

    private void pickFirmware() {
        Intent intent = new Intent(Intent.ACTION_OPEN_DOCUMENT);
        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType("*/*");
        intent.putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true);
        try {
            startActivityForResult(intent, REQUEST_FIRMWARE);
        } catch (Exception e) {
            snack(L.t("没有可用的文件选择器: ") + e.getMessage());
        }
    }


    /* ---- backup / restore -------------------------------------------- */

    private File pendingExportDir;
    private String pendingExportLabel;

    private File primeRoot() { return new File(workDir, "prime_data"); }
    private File cDrive() { return new File(primeRoot(), "C"); }
    private File dataFolder() { return new File(cDrive(), "DATA"); }

    /** Menu entry for the two backup operations. */
    private void showBackupMenu() {
        new MaterialAlertDialogBuilder(this)
                .setTitle(L.t("备份"))
                .setItems(new String[]{L.t("备份 DATA"), L.t("备份 C 盘")}, (dialog, which) -> {
                    if (which == 0) {
                        showBackupDialog();
                    } else {
                        exportCdrive();
                    }
                })
                .show();
    }

    private void showBackupDialog() {
        new MaterialAlertDialogBuilder(this)
                .setTitle(L.t("备份 C:\\DATA"))
                .setItems(new String[]{L.t("导入"), L.t("导出")}, (dialog, which) -> {
                    if (which == 0) pickBackupZip();
                    else exportZip(dataFolder(), "data", "C:\\DATA");
                })
                .show();
    }

    private void exportCdrive() {
        exportZip(cDrive(), "cdrive", L.t("整个 C: 盘"));
    }

    private void pickBackupZip() {
        Intent intent = new Intent(Intent.ACTION_OPEN_DOCUMENT);
        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType("*/*");
        try {
            startActivityForResult(intent, REQUEST_DATA_IMPORT);
        } catch (Exception error) {
            snack(L.t("没有可用的文件选择器"));
        }
    }

    /** Asks the system picker where to put the archive, then zips into it. */
    private void exportZip(final File source, final String prefix, final String label) {
        if (source == null || !source.isDirectory()) {
            setStatus(L.t("找不到目录：") + source, false);
            return;
        }
        pendingExportDir = source;
        pendingExportLabel = label;
        Intent intent = new Intent(Intent.ACTION_CREATE_DOCUMENT);
        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType("application/zip");
        intent.putExtra(Intent.EXTRA_TITLE, prefix + "-" + BuildConfig.BUILD_STAMP + ".zip");
        try {
            startActivityForResult(intent, REQUEST_BACKUP_EXPORT);
        } catch (Exception error) {
            snack(L.t("没有可用的文件选择器"));
        }
    }

    private void writeZip(final Uri target, final File source, final String label) {
        setStatus(L.t("正在打包") + label + L.t("…，文件较多时需要一会儿"), false);
        new Thread(() -> {
            try {
                OutputStream raw = getContentResolver().openOutputStream(target);
                if (raw == null) throw new IOException(L.t("无法写入所选位置"));
                ZipOutputStream zip = new ZipOutputStream(new BufferedOutputStream(raw, 256 * 1024));
                int files;
                try {
                    files = addTree(zip, source, "");
                } finally {
                    zip.finish();
                    closeQuietly(zip);
                }
                setStatus(label + L.t(" 已导出 ") + files + L.t(" 个文件"), false);
            } catch (Exception error) {
                Log.e(TAG, "backup failed", error);
                setStatus(L.t("导出失败：") + error.getMessage(), false);
            }
        }, "primeshim-backup").start();
    }

    private Uri createDownloadEntry(String name) {
        if (Build.VERSION.SDK_INT < 29) return null;
        ContentValues values = new ContentValues();
        values.put(MediaStore.Downloads.DISPLAY_NAME, name);
        values.put(MediaStore.Downloads.MIME_TYPE, "application/zip");
        values.put(MediaStore.Downloads.RELATIVE_PATH,
                Environment.DIRECTORY_DOWNLOADS + "/PrimeShim");
        return getContentResolver().insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, values);
    }

    private int addTree(ZipOutputStream zip, File dir, String prefix) throws IOException {
        File[] children = dir.listFiles();
        if (children == null) return 0;
        int count = 0;
        byte[] buffer = new byte[128 * 1024];
        for (File child : children) {
            String entryName = prefix + child.getName();
            if (child.isDirectory()) {
                zip.putNextEntry(new ZipEntry(entryName + "/"));
                zip.closeEntry();
                count += addTree(zip, child, entryName + "/");
            } else {
                zip.putNextEntry(new ZipEntry(entryName));
                InputStream in = new java.io.BufferedInputStream(new FileInputStream(child), 128 * 1024);
                try {
                    int read;
                    while ((read = in.read(buffer)) > 0) zip.write(buffer, 0, read);
                } finally {
                    closeQuietly(in);
                }
                zip.closeEntry();
                ++count;
            }
        }
        return count;
    }

    /** Unpacks a chosen zip into C:\\DATA, replacing files with the same name. */
    private void importDataZip(final Uri uri) {
        setStatus(L.t("正在导入…"), false);
        new Thread(() -> {
            int files = 0;
            try {
                InputStream raw = getContentResolver().openInputStream(uri);
                if (raw == null) throw new IOException(L.t("无法打开所选文件"));
                ZipInputStream zip = new ZipInputStream(new java.io.BufferedInputStream(raw));
                try {
                    ZipEntry entry;
                    while ((entry = zip.getNextEntry()) != null) {
                        String name = entry.getName();
                        if (name.isEmpty() || name.startsWith("/") || name.contains("..")) continue;
                        File target = new File(dataFolder(), name);
                        if (entry.isDirectory()) {
                            //noinspection ResultOfMethodCallIgnored
                            target.mkdirs();
                            continue;
                        }
                        File parent = target.getParentFile();
                        if (parent != null && !parent.isDirectory()) {
                            //noinspection ResultOfMethodCallIgnored
                            parent.mkdirs();
                        }
                        OutputStream out = new FileOutputStream(target);
                        try {
                            byte[] chunk = new byte[64 * 1024];
                            int read;
                            while ((read = zip.read(chunk)) > 0) out.write(chunk, 0, read);
                        } finally {
                            closeQuietly(out);
                        }
                        ++files;
                    }
                } finally {
                    closeQuietly(zip);
                }
                notice(L.t("已导入 ") + files + L.t(" 个文件到 C:\\DATA\n\n请完全退出并重新打开 App"));
            } catch (Exception error) {
                Log.e(TAG, "backup import failed", error);
                setStatus(L.t("导入失败：") + error.getMessage(), false);
            }
        }, "primeshim-restore").start();
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, Intent data) {
        super.onActivityResult(requestCode, resultCode, data);
        if (requestCode == REQUEST_FM_IMPORT) {
            if (resultCode == RESULT_OK && data != null && data.getData() != null) {
                Uri uri = data.getData();
                File target = new File(fmDir, displayNameOf(uri, "import.bin"));
                copyUriToFile(uri, target);
            }
            return;
        }
        if (requestCode == REQUEST_FM_EXPORT) {
            if (resultCode == RESULT_OK && data != null && data.getData() != null
                    && fmPendingExport != null) {
                copyFileToUri(fmPendingExport, data.getData());
            }
            fmPendingExport = null;
            return;
        }
        if (requestCode == REQUEST_BACKUP_EXPORT) {
            if (resultCode == RESULT_OK && data != null && data.getData() != null
                    && pendingExportDir != null) {
                writeZip(data.getData(), pendingExportDir, pendingExportLabel);
            }
            pendingExportDir = null;
            return;
        }
        if (requestCode == REQUEST_SCRIPT_EXPORT) {
            if (resultCode == RESULT_OK && data != null && data.getData() != null
                    && scriptExportText != null) {
                writeScriptUri(data.getData(), scriptExportText);
            }
            scriptExportText = null;
            return;
        }
        if (requestCode == REQUEST_SCRIPT_IMPORT) {
            if (resultCode == RESULT_OK && data != null && data.getData() != null) {
                importScript(data.getData());
            }
            return;
        }
        if (requestCode == REQUEST_DATA_IMPORT) {
            if (resultCode == RESULT_OK && data != null && data.getData() != null) {
                importDataZip(data.getData());
            }
            return;
        }
        if (requestCode != REQUEST_FIRMWARE) {
            return;
        }
        if (resultCode != RESULT_OK || data == null) {
            return;
        }
        final List<Uri> uris = new ArrayList<>();
        ClipData clip = data.getClipData();
        if (clip != null) {
            for (int i = 0; i < clip.getItemCount(); ++i) {
                Uri uri = clip.getItemAt(i).getUri();
                if (uri != null) uris.add(uri);
            }
        } else if (data.getData() != null) {
            uris.add(data.getData());
        }
        if (uris.isEmpty()) {
            return;
        }
        setStatus(L.t("正在导入固件…"), true);
        new Thread(() -> importFirmware(uris), "primeshim-import").start();
    }

    /**
     * Accepts an official update zip, PRIME_APP.DAT, or a multi-selection of
     * the three official files.  PRIME_APP.DAT supplies both the ARM ELF and
     * the A: FAT16 volume; PRIME_MASTER.DAT/PRIME_OS.ROM are reported and
     * ignored because PrimeShim starts at the application ELF.
     */
    private void importFirmware(List<Uri> uris) {
        File staging = new File(getFilesDir(), "import");
        File extracted = new File(getFilesDir(), "import.elf");
        try {
            deleteRecursive(staging);
            if (!staging.mkdirs()) {
                throw new IOException(L.t("无法创建临时目录"));
            }
            List<File> files = stageSelection(uris, staging);
            File app = findFile(staging,
                    file -> FirmwarePackage.isAppContainer(file), 0);
            File elf = findFile(staging,
                    file -> FirmwarePackage.isElf(file), 0);

            List<String> ignored = new ArrayList<>();
            for (File file : files) {
                if (file.equals(app) || file.equals(elf)) continue;
                String name = file.getName();
                if (FirmwarePackage.isMasterContainer(file)) {
                    ignored.add(name + L.t("，boot 镜像，已忽略"));
                } else if (FirmwarePackage.looksLikeOsRom(file)) {
                    ignored.add(name + L.t("，1 MiB 启动 ROM，已忽略"));
                } else {
                    String upper = name.toUpperCase(Locale.US);
                    if (!upper.startsWith("VERSION_")
                            && !upper.startsWith("RELEASE_INFO")
                            && !upper.equals("PRIME_FW.MD5")) {
                        ignored.add(name + L.t("，未使用"));
                    }
                }
            }

            if (app == null && elf == null) {
                setStatus(L.t("这批文件里没有 PRIME_APP.DAT。\n\n")
                        + L.t("请选择官方升级包 zip，或包里的 PRIME_APP.DAT。\n")
                        + L.t("PRIME_MASTER.DAT / PRIME_OS.ROM 不能单独运行。"), true);
                return;
            }

            /* A raw ELF is only useful as an update to an existing profile;
             * without the A: volume the firmware has no SDKLIB.DLL. */
            if (app == null) {
                String existing = sha256(elf).substring(0, 16);
                File profile = new File(profilesDir, existing);
                if (!new File(profile, "prime_data/A/dummy.DAT").isFile()) {
                    setStatus(L.t("只找到 armfir.elf，但里面没有 A: 系统盘。\n\n")
                            + L.t("请选择官方升级包 zip 或 PRIME_APP.DAT；")
                            + L.t("A: 盘的 WINDOW\\SYSTEM、programs 必须来自同一个 DAT。"), true);
                    return;
                }
            }

            File source = app != null ? app : elf;
            String problem = PrimeShim.nativeImportFirmware(
                    source.getAbsolutePath(), extracted.getAbsolutePath());
            if (problem != null) {
                setStatus(L.t("这个文件不能用作固件：\n") + problem, true);
                return;
            }

            installProfile(extracted, app, ignored);
        } catch (Exception error) {
            suppressCrash = false;
            Log.e(TAG, "firmware import failed", error);
            setStatus(L.t("导入失败：") + error.getMessage(), true);
        } finally {
            deleteRecursive(staging);
            //noinspection ResultOfMethodCallIgnored
            extracted.delete();
        }
    }

    /** Copies every selected URI into staging and expands firmware zips. */
    private List<File> stageSelection(List<Uri> uris, File staging)
            throws IOException {
        for (int i = 0; i < uris.size(); ++i) {
            Uri uri = uris.get(i);
            String name = sanitizeFileName(displayNameOf(uri,
                    "firmware-" + (i + 1) + ".bin"));
            File target = new File(staging, (i + 1) + "-" + name);
            copyUriToFileSync(uri, target);
            if (isZip(target)) {
                int count = unzipFirmware(target, staging);
                Log.i(TAG, "zip " + name + ": " + count + " firmware entries");
                //noinspection ResultOfMethodCallIgnored
                target.delete();
            }
        }
        List<File> files = new ArrayList<>();
        collectFiles(staging, files, 0);
        return files;
    }

    /** Extracts only the files an HP Prime update package can contribute. */
    private int unzipFirmware(File archive, File staging) throws IOException {
        int count = 0;
        byte[] buffer = new byte[128 * 1024];
        ZipInputStream zip = new ZipInputStream(new java.io.BufferedInputStream(
                new FileInputStream(archive), 128 * 1024));
        try {
            ZipEntry entry;
            while ((entry = zip.getNextEntry()) != null) {
                String name = entry.getName();
                if (name == null || name.isEmpty() || entry.isDirectory()) {
                    continue;
                }
                String base = name;
                int slash = Math.max(base.lastIndexOf('/'),
                        base.lastIndexOf('\\'));
                if (slash >= 0) base = base.substring(slash + 1);
                if (!isFirmwareEntry(base)) continue;

                File target = new File(staging, sanitizeFileName(base));
                OutputStream out = new FileOutputStream(target);
                try {
                    int read;
                    while ((read = zip.read(buffer)) > 0) {
                        out.write(buffer, 0, read);
                    }
                } finally {
                    closeQuietly(out);
                }
                ++count;
            }
        } finally {
            closeQuietly(zip);
        }
        return count;
    }

    private static boolean isFirmwareEntry(String base) {
        String upper = base.toUpperCase(Locale.US);
        return upper.equals("PRIME_APP.DAT")
                || upper.equals("APPDISK.DAT")
                || upper.equals("PRIME_MASTER.DAT")
                || upper.equals("PRIME_OS.ROM")
                || upper.equals("PRIME_FW.MD5")
                || upper.endsWith(".ELF")
                || upper.startsWith("VERSION_")
                || upper.startsWith("RELEASE_INFO");
    }

    private static void collectFiles(File directory, List<File> files,
                                     int depth) {
        if (depth > 8) return;
        File[] children = directory.listFiles();
        if (children == null) return;
        for (File child : children) {
            if (child.isDirectory()) {
                collectFiles(child, files, depth + 1);
            } else {
                files.add(child);
            }
        }
    }

    private static File findFile(File directory, java.io.FileFilter filter,
                                 int depth) {
        if (depth > 8) return null;
        File[] children = directory.listFiles();
        if (children == null) return null;
        for (File child : children) {
            if (child.isFile() && filter.accept(child)) return child;
        }
        for (File child : children) {
            if (child.isDirectory()) {
                File found = findFile(child, filter, depth + 1);
                if (found != null) return found;
            }
        }
        return null;
    }

    /**
     * Publishes ELF + A: as one profile.  A: is always regenerated from the
     * package so font/dummy data matches the ELF; C: is preserved.
     */
    private void installProfile(File extracted, File container,
                                List<String> ignored) throws IOException {
        suppressCrash = true;
        uiHandler.removeCallbacks(guestCrashWatch);
        String id = sha256(extracted).substring(0, 16);
        File profile = new File(profilesDir, id);
        if (!profile.isDirectory() && !profile.mkdirs()) {
            throw new IOException(L.t("无法创建 profile"));
        }
        if (container != null) {
            prepareProfileFromPackage(profile, container);
        } else if (!new File(profile,
                "prime_data/A/dummy.DAT").isFile()) {
            throw new IOException(L.t("缺少 A: 盘，无法建立 profile"));
        }

        File target = new File(profile, FIRMWARE_NAME);
        //noinspection ResultOfMethodCallIgnored
        target.delete();
        if (!extracted.renameTo(target)) {
            FirmwarePackage.copyFile(extracted, target);
            //noinspection ResultOfMethodCallIgnored
            extracted.delete();
        }

        activeProfile = id;
        workDir = profile;
        firmwareFile = target;
        writeActive(new File(getFilesDir(), "active_profile"), id);

        Log.i(TAG, "firmware profile " + id + " ready: "
                + target.length() + " bytes");
        settings().edit()
                .putBoolean("guestCrashed", false)
                .remove("lastCrash")
                .apply();
        crashShown = false;
        setStatus(null, false);

        StringBuilder note = new StringBuilder(L.t("固件已导入"));
        if (container == null) {
            note.append(L.t("\n只更新了 armfir.elf，沿用现有 A:/C: 数据。"));
        }
        if (!ignored.isEmpty()) {
            note.append(L.t("\n\n已忽略："));
            for (String line : ignored) note.append('\n').append(line);
        }
        final String message = note.toString();
        runOnUiThread(() -> android.widget.Toast.makeText(MainActivity.this,
                message, android.widget.Toast.LENGTH_LONG).show());
        runOnUiThread(() -> restartApp(true));
    }

    private void copyUriToFileSync(Uri uri, File target) throws IOException {
        InputStream in = getContentResolver().openInputStream(uri);
        if (in == null) throw new IOException(L.t("无法打开所选文件"));
        OutputStream out = new BufferedOutputStream(
                new FileOutputStream(target), 128 * 1024);
        try {
            byte[] buffer = new byte[128 * 1024];
            int read;
            while ((read = in.read(buffer)) > 0) out.write(buffer, 0, read);
        } finally {
            try {
                out.close();
            } finally {
                closeQuietly(in);
            }
        }
    }

    private static boolean isZip(File file) {
        String name = file.getName().toLowerCase(Locale.US);
        if (name.endsWith(".zip")) return true;
        if (file.length() < 4) return false;
        try {
            FileInputStream in = new FileInputStream(file);
            try {
                byte[] header = new byte[4];
                int read = 0;
                while (read < 4) {
                    int count = in.read(header, read, 4 - read);
                    if (count <= 0) return false;
                    read += count;
                }
                return header[0] == 'P' && header[1] == 'K'
                        && (header[2] == 3 || header[2] == 5 || header[2] == 7);
            } finally {
                closeQuietly(in);
            }
        } catch (IOException error) {
            return false;
        }
    }

    private static String sanitizeFileName(String name) {
        String value = name.replace('/', '_').replace('\\', '_')
                .replace(':', '_');
        if (value.isEmpty() || value.equals(".") || value.equals("..")) {
            value = "firmware.bin";
        }
        if (value.length() > 120) value = value.substring(0, 120);
        return value;
    }

    /* ---- guest lifecycle -------------------------------------------- */

    private void startGuest() {
        /* Called from the bootstrap and import worker threads.  The guest
         * startup touches the keyboard/crosshair views and must run on the
         * UI thread; otherwise Android throws CalledFromWrongThreadException
         * as soon as the window is attached. */
        if (Looper.myLooper() != Looper.getMainLooper()) {
            runOnUiThread(this::startGuest);
            return;
        }
        if (guestStarted) {
            return;
        }
        traceEnabled = settings().getBoolean("trace", false);
        keyboardView.setKeyEchoEnabled(settings().getBoolean("keyEcho", false));
        keyboardView.setDebugOverlay(settings().getBoolean("overlay", false));
        keyboardView.setHapticFeedbackEnabled(settings().getBoolean("haptic", false));
        speedPercent = settings().getInt("speed", 100);
        PrimeShim.nativeSetSpeed(speedPercent);
        crosshair.setVisibility(settings().getBoolean("mouse", false)
                ? View.VISIBLE : View.GONE);
        PrimeShim.nativeSetTraceCalls(traceEnabled);
        if (nativeGuestRunning) {
            /* A theme/font/language recreation keeps the native guest alive. */
            guestStarted = true;
            crashShown = false;
            setStatus(null, false);
            PrimeShim.nativeRequestRedraw();
            return;
        }
        int result = PrimeShim.nativeStart(firmwareFile.getAbsolutePath(),
                workDir.getAbsolutePath(), PrimeShim.LOG_INFO);
        if (result != 0) {
            setStatus(L.t("nativeStart 失败：") + result, true);
            return;
        }
        guestStarted = true;
        nativeGuestRunning = true;
        crashShown = false;
        setStatus(null, false);
        uiHandler.removeCallbacks(guestCrashWatch);
        uiHandler.postDelayed(guestCrashWatch, 1000);
    }

    /* ---- surface ---------------------------------------------------- */

    @Override
    public void surfaceCreated(SurfaceHolder holder) {
        surfaceReady = true;
        PrimeShim.nativeSetSurface(holder.getSurface());
        surfaceView.requestFocus();
    }

    @Override
    public void surfaceChanged(SurfaceHolder holder, int format, int width, int height) {
        PrimeShim.nativeSetSurface(holder.getSurface());
    }

    @Override
    public void surfaceDestroyed(SurfaceHolder holder) {
        surfaceReady = false;
        PrimeShim.nativeSetSurface(null);
    }

    /* ---- input ------------------------------------------------------ */

    private int slotForPointer(int pointerId) {
        int slot = touchSlots.get(pointerId, -1);
        if (slot >= 0) return slot;
        for (int candidate = 0; candidate < 8; ++candidate) {
            boolean used = false;
            for (int i = 0; i < touchSlots.size(); ++i) {
                if (touchSlots.valueAt(i) == candidate) {
                    used = true;
                    break;
                }
            }
            if (!used) {
                touchSlots.put(pointerId, candidate);
                return candidate;
            }
        }
        return -1;
    }

    private boolean handleTouch(MotionEvent event) {
        int masked = event.getActionMasked();
        if (masked != MotionEvent.ACTION_DOWN
                && masked != MotionEvent.ACTION_MOVE
                && masked != MotionEvent.ACTION_UP
                && masked != MotionEvent.ACTION_CANCEL
                && masked != MotionEvent.ACTION_POINTER_DOWN
                && masked != MotionEvent.ACTION_POINTER_UP) {
            return false;
        }
        if (!guestStarted || !surfaceReady) {
            return true;
        }
        if (masked == MotionEvent.ACTION_DOWN) {
            touchSlots.clear();
        }

        int viewWidth = surfaceView.getWidth();
        int viewHeight = surfaceView.getHeight();
        if (viewWidth <= 0 || viewHeight <= 0) {
            return true;
        }
        /* Must match build_tables() in lcd_android.c: the firmware image is
         * scaled to the surface width (4:3), not by an integer factor. */
        int drawnWidth = viewWidth;
        int drawnHeight = drawnWidth * FW_HEIGHT / FW_WIDTH;
        if (drawnHeight > viewHeight) {
            drawnHeight = viewHeight;
            drawnWidth = drawnHeight * FW_WIDTH / FW_HEIGHT;
        }
        if (drawnWidth < 1 || drawnHeight < 1) {
            return true;
        }
        int offsetX = (viewWidth - drawnWidth) / 2;
        int offsetY = (viewHeight - drawnHeight) / 2;
        int actionIndex = event.getActionIndex();
        int count = Math.min(event.getPointerCount(), 8);
        int[] actions = new int[count];
        int[] slots = new int[count];
        int[] xs = new int[count];
        int[] ys = new int[count];
        int used = 0;

        for (int i = 0; i < count; ++i) {
            int pointerId = event.getPointerId(i);
            int action;
            switch (masked) {
            case MotionEvent.ACTION_DOWN:
                action = PrimeShim.TOUCH_DOWN;
                break;
            case MotionEvent.ACTION_POINTER_DOWN:
                action = i == actionIndex ? PrimeShim.TOUCH_DOWN
                        : PrimeShim.TOUCH_MOVE;
                break;
            case MotionEvent.ACTION_POINTER_UP:
                action = i == actionIndex ? PrimeShim.TOUCH_UP
                        : PrimeShim.TOUCH_MOVE;
                break;
            case MotionEvent.ACTION_UP:
            case MotionEvent.ACTION_CANCEL:
                action = PrimeShim.TOUCH_UP;
                break;
            default:
                action = PrimeShim.TOUCH_MOVE;
                break;
            }

            int slot = slotForPointer(pointerId);
            if (slot < 0) continue;
            int x = (int) ((event.getX(i) - offsetX) * FW_WIDTH / drawnWidth);
            int y = (int) ((event.getY(i) - offsetY) * FW_HEIGHT / drawnHeight);
            if (x < 0) x = 0;
            if (x >= FW_WIDTH) x = FW_WIDTH - 1;
            if (y < 0) y = 0;
            if (y >= FW_HEIGHT) y = FW_HEIGHT - 1;
            actions[used] = action;
            slots[used] = slot;
            xs[used] = x;
            ys[used] = y;
            ++used;

            if (action == PrimeShim.TOUCH_UP) {
                touchSlots.delete(pointerId);
            }
        }

        if (crosshair != null) {
            crosshair.show(event.getX(0), event.getY(0),
                    xs.length > 0 ? xs[0] : 0, ys.length > 0 ? ys[0] : 0);
        }
        if (used > 0) {
            int[] packedActions = new int[used];
            int[] packedSlots = new int[used];
            int[] packedXs = new int[used];
            int[] packedYs = new int[used];
            System.arraycopy(actions, 0, packedActions, 0, used);
            System.arraycopy(slots, 0, packedSlots, 0, used);
            System.arraycopy(xs, 0, packedXs, 0, used);
            System.arraycopy(ys, 0, packedYs, 0, used);
            PrimeShim.nativeTouchMulti(packedActions, packedSlots,
                    packedXs, packedYs);
        }
        if (masked == MotionEvent.ACTION_UP
                || masked == MotionEvent.ACTION_CANCEL) {
            touchSlots.clear();
        }
        return true;
    }

    @Override
    public boolean onKeyDown(int keyCode, KeyEvent event) {
        if (!guestStarted || keyCode == KeyEvent.KEYCODE_BACK) {
            return super.onKeyDown(keyCode, event);
        }
        PrimeShim.nativeKeyBatch(keyCode, 1);
        return true;
    }

    @Override
    public boolean onKeyUp(int keyCode, KeyEvent event) {
        if (!guestStarted || keyCode == KeyEvent.KEYCODE_BACK) {
            return super.onKeyUp(keyCode, event);
        }
        PrimeShim.nativeKeyBatch(keyCode, 0);
        return true;
    }

    /** Back pops the Material page stack before leaving the calculator. */
    @SuppressWarnings("deprecation")
    @Override
    public void onBackPressed() {
        if (!pageStack.isEmpty()) {
            if (pageStack.get(pageStack.size() - 1) == terminalPage) {
                stopScript();
            }
            if (scriptEditor != null) saveScript();
            popPage();
            return;
        }
        if (logPanel != null && logPanel.getVisibility() == View.VISIBLE) {
            toggleLog();
            return;
        }
        super.onBackPressed();
    }

    @Override
    protected void onPause() {
        if (scriptEditor != null) saveScript();
        super.onPause();
    }

    @Override
    protected void onDestroy() {
        uiHandler.removeCallbacks(logRefresh);
        uiHandler.removeCallbacks(guestCrashWatch);
        if (scriptRuntime != null) {
            scriptRuntime.destroy();
            scriptRuntime = null;
        }
        PrimeShim.nativeStop();
        super.onDestroy();
    }

    /* ---- helpers ---------------------------------------------------- */

    /** Three-line menu icon that morphs into an X while the sheet is open. */
    private static final class MenuIconView extends View {
        private final Paint paint = new Paint(Paint.ANTI_ALIAS_FLAG);
        private float progress;
        private ValueAnimator animator;

        MenuIconView(Context context) {
            super(context);
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(2f * context.getResources()
                    .getDisplayMetrics().density);
            paint.setStrokeCap(Paint.Cap.ROUND);
        }

        void setColor(int color) {
            paint.setColor(color);
            invalidate();
        }

        void animateTo(float target) {
            if (animator != null) animator.cancel();
            animator = ValueAnimator.ofFloat(progress, target);
            animator.setDuration(220);
            animator.setInterpolator(new DecelerateInterpolator());
            animator.addUpdateListener(animation -> {
                progress = (float) animation.getAnimatedValue();
                invalidate();
            });
            animator.start();
        }

        @Override
        protected void onDraw(Canvas canvas) {
            float w = getWidth();
            float h = getHeight();
            float left = w * 0.18f;
            float right = w * 0.82f;
            float top = h * 0.28f;
            float mid = h * 0.5f;
            float bottom = h * 0.72f;
            float p = Math.max(0f, Math.min(1f, progress));

            int alpha = paint.getAlpha();
            paint.setAlpha(Math.round(255 * (1f - p)));
            canvas.drawLine(left, mid, right, mid, paint);
            paint.setAlpha(alpha);

            canvas.save();
            canvas.rotate(45f * p, w / 2f, h / 2f);
            canvas.drawLine(left, top + (mid - top) * p,
                    right, top + (mid - top) * p, paint);
            canvas.restore();

            canvas.save();
            canvas.rotate(-45f * p, w / 2f, h / 2f);
            canvas.drawLine(left, bottom + (mid - bottom) * p,
                    right, bottom + (mid - bottom) * p, paint);
            canvas.restore();
        }
    }

    /** Full-screen crosshair showing where a touch lands on the 320x240 screen. */
    private static class CrosshairView extends View {
        private float px = -1, py = -1;
        private int fx, fy;
        private final Paint line = new Paint();
        private final Paint text = new Paint();

        CrosshairView(Context context) {
            super(context);
            line.setColor(0xFFFF3B30);
            line.setStrokeWidth(3f);
            line.setStyle(Paint.Style.STROKE);
            text.setColor(0xFFFF3B30);
            text.setTextSize(28f);
            text.setAntiAlias(true);
        }

        void show(float x, float y, int fwX, int fwY) {
            px = x; py = y; fx = fwX; fy = fwY;
            invalidate();
        }

        @Override
        protected void onDraw(Canvas canvas) {
            if (px < 0) return;
            canvas.drawLine(0, py, getWidth(), py, line);
            canvas.drawLine(px, 0, px, getHeight(), line);
            canvas.drawCircle(px, py, 22f, line);
            canvas.drawText(L.t("屏幕 ") + fx + ", " + fy, Math.min(px + 24, getWidth() - 320), Math.max(py - 24, 40), text);
        }
    }

    /**
     * Blocking status (firmware missing / fatal) shows the MD3 card; anything
     * transient goes through a Snackbar, which is the Material 3 pattern for
     * non-blocking feedback.
     */
    private void setStatus(final String text, final boolean blocking) {
        runOnUiThread(new Runnable() {
            @Override
            public void run() {
                if (text == null) {
                    overlay.setVisibility(View.GONE);
                    return;
                }
                if (!blocking) {
                    snack(text);
                    return;
                }
                statusView.setText(text);
                pickButton.setVisibility(View.VISIBLE);
                dismissButton.setVisibility(View.VISIBLE);
                overlay.setVisibility(View.VISIBLE);
                if (splash == null || splash.getParent() == null) {
                    overlay.bringToFront();
                }
            }
        });
    }

    private static void copyAsset(AssetManager assets, String name, File target)
            throws IOException {
        InputStream in = assets.open(name);
        try {
            OutputStream out = new FileOutputStream(target);
            try {
                byte[] buffer = new byte[64 * 1024];
                int count;
                while ((count = in.read(buffer)) > 0) {
                    out.write(buffer, 0, count);
                }
            } finally {
                closeQuietly(out);
            }
        } finally {
            closeQuietly(in);
        }
    }

    private static void closeQuietly(java.io.Closeable stream) {
        if (stream == null) {
            return;
        }
        try {
            stream.close();
        } catch (IOException ignored) {
            /* nothing useful to do */
        }
    }
}
