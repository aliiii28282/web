#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ربات چت ناشناس تلگرام — تک‌فایل، فقط کتابخانه‌های استاندارد پایتون (بدون pip)
اجرا در Termux:
    pkg install python -y
    python anon_chat_bot.py
بار اول توکن ربات و شناسه عددی مالک را می‌پرسد و در config.json ذخیره می‌کند.

ساختار فایل:
    1) تنظیمات و ابزارها     2) رمزنگاری   3) زمان تهران و تقویم شمسی
    4) دیتابیس و تنظیمات      5) فیلتر کلمات ممنوعه
    6) API تلگرام             7) منطق چت (اتصال/ارسال/پایان)
    8) پنل مدیریت مالک (+ سوئیچ به پنل کاربر)   9) کد Cloudflare Worker   10) حلقه‌ی اصلی
"""
import os, sys, re, json, time, uuid, base64, hmac, hashlib, secrets, sqlite3, threading, random
import urllib.request, urllib.error
import traceback
from datetime import datetime, timezone, timedelta
from concurrent.futures import ThreadPoolExecutor

# ───────────────────────── 1) تنظیمات ─────────────────────────
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.environ.get("CONFIG_PATH", os.path.join(BASE_DIR, "config.json"))
DB_PATH = os.environ.get("DB_PATH", os.path.join(BASE_DIR, "anonchat.db"))
KEY_PATH = os.environ.get("KEY_PATH", os.path.join(BASE_DIR, "secret.key"))
WORKER_FILE = os.path.join(BASE_DIR, "worker.js")

BOT_TOKEN = ""
OWNER_ID = 0
CFG_WORKER = ""         # آدرس Worker از config.json یا متغیر WORKER_URL
LOCK = threading.RLock()
DB = None
WAITING = []            # صف انتظار چت تصادفی
ADMIN_STATE = {}        # وضعیت ورودی‌های پنل مالک
_user_locks = {}
_processed_updates = set()
_processed_updates_lock = threading.Lock()
_MAX_PROCESSED_UPDATES = 4096
GAME_MODULE = None


def load_config():
    """توکن و شناسه مالک: متغیر محیطی ← config.json ← پرسش از کاربر."""
    token = os.environ.get("BOT_TOKEN", "")
    owner = os.environ.get("OWNER_ID", "")
    cfg = {}
    if os.path.exists(CONFIG_PATH):
        with open(CONFIG_PATH, encoding="utf-8") as f:
            cfg = json.load(f)
    token = token or cfg.get("token", "")
    owner = owner or str(cfg.get("owner", ""))
    if not token:
        if sys.stdin and sys.stdin.isatty():
            token = input("توکن ربات (از BotFather): ").strip()
        else:
            raise RuntimeError("BOT_TOKEN تنظیم نشده است؛ آن را در Railway → Variables وارد کنید.")
    if not owner.isdigit():
        if sys.stdin and sys.stdin.isatty():
            owner = input("شناسه عددی مالک (از @userinfobot): ").strip()
        else:
            raise RuntimeError("OWNER_ID معتبر نیست؛ شناسه عددی مالک را در Railway → Variables وارد کنید.")
    parent = os.path.dirname(os.path.abspath(CONFIG_PATH))
    os.makedirs(parent, exist_ok=True)
    for path in (DB_PATH, KEY_PATH):
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    global CFG_WORKER
    CFG_WORKER = (os.environ.get("WORKER_URL") or cfg.get("worker_url") or "").strip().rstrip("/")
    cfg.update({"token": token, "owner": int(owner)})
    with open(CONFIG_PATH, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)
    return token, int(owner)


# ───────────────────────── 2) رمزنگاری ─────────────────────────
# توجه: ربات واسطه‌ی پیام‌هاست و تلگرام برای ربات‌ها چت سرتاسری (Secret Chat) ندارد؛
# پس E2E واقعی ممکن نیست. اینجا شناسه‌ی طرف مقابل در دیتابیس رمز می‌شود
# (جریان خنثی + احراز یکپارچگی با HMAC) و هیچ متن پیامی ذخیره نمی‌شود.
def _load_key():
    if os.path.exists(KEY_PATH):
        with open(KEY_PATH, "rb") as f:
            return f.read()
    k = secrets.token_bytes(32)
    with open(KEY_PATH, "wb") as f:
        f.write(k)
    try:
        os.chmod(KEY_PATH, 0o600)
    except Exception:
        pass
    return k


_KEY = None


def _keys():
    global _KEY
    if _KEY is None:
        _KEY = _load_key()
    return hashlib.sha256(_KEY + b"enc").digest(), hashlib.sha256(_KEY + b"mac").digest()


def _stream(k, nonce, n):
    out, c = b"", 0
    while len(out) < n:
        out += hashlib.sha256(k + nonce + c.to_bytes(8, "big")).digest()
        c += 1
    return out[:n]


def seal(text):
    ek, mk = _keys()
    data = text.encode()
    nonce = secrets.token_bytes(12)
    ct = bytes(a ^ b for a, b in zip(data, _stream(ek, nonce, len(data))))
    tag = hmac.new(mk, nonce + ct, hashlib.sha256).digest()[:16]
    return base64.urlsafe_b64encode(nonce + tag + ct).decode()


def unseal(s):
    ek, mk = _keys()
    raw = base64.urlsafe_b64decode(s.encode())
    nonce, tag, ct = raw[:12], raw[12:28], raw[28:]
    if not hmac.compare_digest(tag, hmac.new(mk, nonce + ct, hashlib.sha256).digest()[:16]):
        raise ValueError("bad tag")
    return bytes(a ^ b for a, b in zip(ct, _stream(ek, nonce, len(ct)))).decode()


# ───────────────────────── 3) زمان تهران و شمسی ─────────────────────────
TEHRAN = timezone(timedelta(hours=3, minutes=30))   # ایران از ۱۴۰۱ ساعت تابستانی ندارد
J_MONTHS = ["فروردین", "اردیبهشت", "خرداد", "تیر", "مرداد", "شهریور",
            "مهر", "آبان", "آذر", "دی", "بهمن", "اسفند"]
J_DAYS = ["دوشنبه", "سه‌شنبه", "چهارشنبه", "پنجشنبه", "جمعه", "شنبه", "یکشنبه"]


def now():
    return datetime.now(TEHRAN)


def gregorian_to_jalali(gy, gm, gd):
    g_d_m = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    gy2 = gy + 1 if gm > 2 else gy
    days = 355666 + 365 * gy + (gy2 + 3) // 4 - (gy2 + 99) // 100 + (gy2 + 399) // 400 + gd + g_d_m[gm - 1]
    jy = -1595 + 33 * (days // 12053)
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm, jd = 1 + days // 31, 1 + days % 31
    else:
        jm, jd = 7 + (days - 186) // 30, 1 + (days - 186) % 30
    return jy, jm, jd


def jalali_str(dt=None):
    dt = dt or now()
    jy, jm, jd = gregorian_to_jalali(dt.year, dt.month, dt.day)
    return f"{J_DAYS[dt.weekday()]} {jd} {J_MONTHS[jm - 1]} {jy} — ساعت {dt:%H:%M}"


def _hm(s):
    h, m = s.split(":")
    return int(h) * 60 + int(m)


def valid_hm(s):
    return bool(re.fullmatch(r"([01]?\d|2[0-3]):[0-5]\d", s.strip()))


def in_window(start, end, dt=None):
    dt = dt or now()
    s, e, m = _hm(start), _hm(end), dt.hour * 60 + dt.minute
    if s == e:
        return True
    return s <= m < e if s < e else (m >= s or m < e)


# ───────────────────────── 4) دیتابیس و تنظیمات ─────────────────────────
# رنگ واقعی دکمه‌ها با فیلد رسمی «style» در Bot API تلگرام (نسخه 9.4 به بعد).
# تلگرام فقط این سه رنگ را پشتیبانی می‌کند: primary=آبی، success=سبز، danger=قرمز
# (none = رنگ پیش‌فرض اپ). روی نسخه‌های قدیمی اپ، دکمه بدون رنگ نمایش داده می‌شود.
STYLES = {"success": "سبز", "danger": "قرمز", "primary": "آبی", "none": "بی‌رنگ"}
STYLE_ORDER = list(STYLES)
_OLD_COLORS = {"green": "success", "red": "danger", "blue": "primary"}

DEFAULT_PRIVACY = """🔒 سیاست حفظ حریم خصوصی

• هویت شما برای طرف مقابل کاملاً ناشناس است؛ نام، نام‌کاربری و عکس شما نمایش داده نمی‌شود.
• متن پیام‌ها به‌طور پیش‌فرض ذخیره نمی‌شود. برای ثبت متن جهت رسیدگی، رضایت جداگانه‌ی هر دو طرف لازم است؛ رد رضایت اثری بر چت ندارد.
• کد ۹ نویسه‌ای نشست، زمان شروع/پایان و رویدادهای مدیریتی/بازی برای عیب‌یابی ثبت می‌شوند.
• شناسه‌ی طرف مقابل در دیتابیس به‌صورت رمزشده نگهداری می‌شود.
• توجه: این ربات چت سرتاسری (E2E) تلگرام نیست؛ پیام‌ها از سرور ربات عبور می‌کنند.
• برای حفظ امنیت، فحاشی به‌صورت خودکار شناسایی می‌شود و باعث اخطار و در صورت تکرار مسدودی می‌گردد.
• ممکن است پشتیبانی یا مدیریت ربات برای نظارت و پشتیبانی در گفتگوها حضور پیدا کند.
• اطلاعات شخصی (شماره، آدرس، رمز و...) را با غریبه‌ها به اشتراک نگذارید.

با استفاده از ربات، این شرایط را می‌پذیرید."""

DEFAULT_WELCOME = "👋 سلام {name}! به ربات چت ناشناس خوش آمدی.\nبا دکمه‌ی «جستجوی چت تصادفی» به یک نفر وصل شو."

DEFAULTS = {
    "bot_on": "1", "sched_on": "0", "sched_mode": "active",
    "sched_start": "08:00", "sched_end": "23:00",
    "max_warns": "3", "priv_show": "1", "priv_text": DEFAULT_PRIVACY,
    "welcome_text": DEFAULT_WELCOME, "owner_mode": "admin",
    "color_chat": "success", "color_next": "primary", "color_end": "danger", "color_priv": "primary",
    "worker_url": "", "worker_enabled": "0", "worker_auto_recover": "1",
    "btn_search": "1", "btn_next": "1", "btn_end": "1", "btn_priv": "0",
    "btn_nickname": "1", "btn_game": "1", "btn_leaderboard": "1", "btn_shop": "1",
    "cmd_search": "1", "cmd_next": "1", "cmd_end": "1",
    "cmd_start": "1", "cmd_privacy": "1", "cmd_game": "1",
    "cmd_leaderboard": "1", "cmd_shop": "1", "cmd_nickname": "1",
    "cmd_help": "1", "cmd_panel": "1",
    "file_apk": "1", "file_zip": "1", "file_photo": "1",
    "file_video": "1", "file_audio": "1", "file_document": "1",
    "game_reward": "10", "game_gender_cost": "100", "game_skip_cost": "10",
    "force_channels": "", "bot_enabled": "1",
    "keyboard_columns": "2", "keyboard_direction": "rtl",
    "keyboard_order": '["search","next","end","priv","nickname","game","leaderboard","shop"]',
    "keyboard_layout": '{"rows":[["search"],["next","end"],["nickname"],["game"],["leaderboard","shop"],["report"]]}',
    "version_notice": "v2.9", "version_description": "ثبت‌نام دو مرحله‌ای، چالش‌های ناشناس، گزارش شفاف، و منوی داینامیک.",
}
_SETTINGS = {}
START_TIME = time.time()
PROFILE_FLOW = {}
AUTO_EDIT_TARGET = {}
SECRET_AUTHENTICATED = {}
REPORT_FLOW = {}


def init_db():
    global DB
    DB = sqlite3.connect(DB_PATH, check_same_thread=False)
    DB.execute("PRAGMA journal_mode=WAL")
    DB.execute("PRAGMA synchronous=NORMAL")
    DB.execute("PRAGMA busy_timeout=10000")
    DB.executescript("""
        CREATE TABLE IF NOT EXISTS users(uid INTEGER PRIMARY KEY, partner TEXT, warns INTEGER DEFAULT 0,
                                         banned INTEGER DEFAULT 0, joined TEXT, last_seen TEXT);
        CREATE TABLE IF NOT EXISTS settings(k TEXT PRIMARY KEY, v TEXT);
        CREATE TABLE IF NOT EXISTS words(id INTEGER PRIMARY KEY AUTOINCREMENT, word TEXT UNIQUE);
        CREATE TABLE IF NOT EXISTS counters(k TEXT PRIMARY KEY, v INTEGER DEFAULT 0);
        CREATE TABLE IF NOT EXISTS broadcasts(id INTEGER PRIMARY KEY AUTOINCREMENT,source_chat INTEGER,
          source_mid INTEGER,created REAL,success INTEGER DEFAULT 0,failed INTEGER DEFAULT 0);
        CREATE TABLE IF NOT EXISTS broadcast_deliveries(broadcast_id INTEGER,user_id INTEGER,message_id INTEGER,
          PRIMARY KEY(broadcast_id,user_id));
        CREATE TABLE IF NOT EXISTS auto_replies(id INTEGER PRIMARY KEY AUTOINCREMENT,keyword TEXT UNIQUE,
          response TEXT NOT NULL,enabled INTEGER DEFAULT 1);
        CREATE TABLE IF NOT EXISTS chat_sessions(code TEXT PRIMARY KEY,user_a INTEGER,user_b INTEGER,
          started REAL NOT NULL,ended REAL,active INTEGER NOT NULL DEFAULT 1,
          consent_a INTEGER NOT NULL DEFAULT 0,consent_b INTEGER NOT NULL DEFAULT 0);
        CREATE INDEX IF NOT EXISTS idx_chat_sessions_users ON chat_sessions(user_a,user_b,started);
        CREATE TABLE IF NOT EXISTS chat_events(id INTEGER PRIMARY KEY AUTOINCREMENT,code TEXT NOT NULL,
          user_id INTEGER NOT NULL,event TEXT NOT NULL,created REAL NOT NULL,details TEXT);
        CREATE INDEX IF NOT EXISTS idx_chat_events_code ON chat_events(code,created);
        CREATE TABLE IF NOT EXISTS chat_messages(id INTEGER PRIMARY KEY AUTOINCREMENT,code TEXT NOT NULL,
          user_id INTEGER NOT NULL,content TEXT NOT NULL,created REAL NOT NULL);
        CREATE INDEX IF NOT EXISTS idx_chat_messages_code ON chat_messages(code,created);
        CREATE TABLE IF NOT EXISTS secret_auth(user_id INTEGER PRIMARY KEY,failures INTEGER NOT NULL DEFAULT 0,
          locked_until REAL NOT NULL DEFAULT 0);
        CREATE TABLE IF NOT EXISTS daily_requests(day TEXT PRIMARY KEY,count INTEGER NOT NULL DEFAULT 0);
        CREATE TABLE IF NOT EXISTS complaint_reports(
          id INTEGER PRIMARY KEY AUTOINCREMENT, code TEXT NOT NULL, reporter INTEGER NOT NULL,
          accused INTEGER NOT NULL, reason TEXT NOT NULL, details TEXT NOT NULL,
          created REAL NOT NULL, status TEXT NOT NULL DEFAULT 'open');
        CREATE TABLE IF NOT EXISTS user_notices(
          uid INTEGER NOT NULL, notice_key TEXT NOT NULL, shown_at REAL NOT NULL,
          PRIMARY KEY(uid,notice_key));
        CREATE TABLE IF NOT EXISTS user_mutes(uid INTEGER PRIMARY KEY, muted_until REAL NOT NULL, by_owner INTEGER NOT NULL);
        CREATE INDEX IF NOT EXISTS idx_complaints_created ON complaint_reports(created,status);
    """)
    cols = {r[1] for r in DB.execute("PRAGMA table_info(users)")}
    if "last_seen" not in cols:                      # مهاجرت دیتابیس نسخه‌ی قبلی
        DB.execute("ALTER TABLE users ADD COLUMN last_seen TEXT")
    for col, definition in (("nickname","TEXT"),("gender","TEXT"),("profile_complete","INTEGER NOT NULL DEFAULT 0"),
                            ("username","TEXT")):
        if col not in cols:
            DB.execute(f"ALTER TABLE users ADD COLUMN {col} {definition}")
    DB.execute("CREATE INDEX IF NOT EXISTS idx_users_last_seen ON users(last_seen)")
    DB.execute("CREATE INDEX IF NOT EXISTS idx_users_partner ON users(partner)")
    _SETTINGS.clear()
    _SETTINGS.update(DEFAULTS)
    for k, v in DB.execute("SELECT k,v FROM settings"):
        _SETTINGS[k] = v
    old_priv_line="• متن و محتوای پیام‌ها در ربات ذخیره نمی‌شود؛ فقط از شما به طرف مقابل عبور می‌کند."
    if old_priv_line in S("priv_text"):
        set_S("priv_text", S("priv_text").replace(old_priv_line,
            "• متن پیام‌ها به‌طور پیش‌فرض ذخیره نمی‌شود. ثبت متن برای رسیدگی فقط با رضایت جداگانه‌ی هر دو طرف انجام می‌شود؛ رد رضایت اثری بر چت ندارد.\n"
            "• کد ۹ نویسه‌ای نشست، زمان شروع/پایان و رویدادهای مدیریتی/بازی ثبت می‌شوند."))
    if "privacy_prefix_v29_applied" not in _SETTINGS:
        set_S("priv_text", "حریم خصوصی : v2.9\n\n" + S("priv_text").replace("حریم خصوصی : v2.9\n",""))
        set_S("privacy_prefix_v29_applied", "1")
    if DB.execute("SELECT COUNT(*) FROM words").fetchone()[0] == 0:
        for w in dict.fromkeys(x.strip() for x in BAD_WORDS_SEED.splitlines() if x.strip()):
            DB.execute("INSERT OR IGNORE INTO words(word) VALUES(?)", (w,))
    DB.commit()
    seed_auto_replies()
    for k in ("color_chat", "color_next", "color_end", "color_priv"):   # تبدیل رنگ‌های ایموجی قدیمی
        if S(k) not in STYLES:
            set_S(k, _OLD_COLORS.get(S(k), DEFAULTS[k]))
    if not S("worker_url") and CFG_WORKER:
        set_S("worker_url", CFG_WORKER)
    set_S("owner_mode", "admin")                      # بعد از ری‌استارت همیشه پنل ادمین
    reload_words()


def S(k):
    return _SETTINGS.get(k, DEFAULTS.get(k, ""))


def set_S(k, v):
    with LOCK:
        _SETTINGS[k] = str(v)
        DB.execute("INSERT INTO settings(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v", (k, str(v)))
        DB.commit()


def bump(k, n=1):
    with LOCK:
        DB.execute("INSERT INTO counters(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=v+excluded.v", (k, n))
        DB.commit()


def nickname(uid):
    with LOCK:
        row = DB.execute("SELECT nickname FROM users WHERE uid=?", (int(uid),)).fetchone()
    return (row[0] or "").strip() if row else ""


def user_gender(uid):
    with LOCK:
        row = DB.execute("SELECT gender FROM users WHERE uid=?", (int(uid),)).fetchone()
    return row[0] if row else None


def set_nickname(uid, value):
    value = re.sub(r"[\r\n\t]+", " ", (value or "")).strip()[:24]
    with LOCK:
        get_user(uid)
        DB.execute("UPDATE users SET nickname=? WHERE uid=?", (value or None, int(uid)))
        DB.commit()


AUTO_KEYWORDS = """سلام|درود|خوبی|چطوری|چه خبر|اسم|نام|لقب|سن|اهل کجایی|کجایی|علاقه|موسیقی|آهنگ|فیلم|سریال|کتاب|غذا|خوراکی|چای|قهوه|رنگ|ورزش|فوتبال|بازی|گیم|سرگرمی|خسته|حوصله|تنهایی|دوستی|دوست|عشق|احساس|خوشحال|ناراحت|غمگین|استرس|نگران|امروز|فردا|دیروز|شب بخیر|صبح بخیر|خداحافظ|فعلا|مرسی|ممنون|لطفا|ببخشید|چرا|چطور|چگونه|کجا|کی|چی|چه کسی|چند|کمک|سوال|جواب|حقیقت|جرأت|چالش|کوییز|معما|جوک|خنده|ایموجی|حیوان|گربه|سگ|سفر|مسافرت|دریا|کوه|شهر|مدرسه|دانشگاه|کار|شغل|خواب|رویا|هدف|آرزو|هوا|باران|برف|گرما|سرما|عالی|خوب|بد|باشه|اوکی|بله|نه|آره|نه مرسی"""
AUTO_DEFAULT_RESPONSES = """سلام! خوش اومدی 😊|ممنون که پرسیدی، تو چطوری؟|چه سؤال جالبی! تو چی فکر می‌کنی؟|من انتخابم را می‌گویم، بعد نوبت توست.|این موضوع همیشه جای گپ دارد.|یک جواب کوتاه: بستگی به حال‌وهوام دارد!|من هم دوست دارم بیشتر درباره‌اش بشنوم.|تو اول بگو، بعد من جواب می‌دهم.|برای شروع، یک سؤال بامزه از من بپرس.|این یکی را با یک ایموجی جواب می‌دهم 😊|چه خاطره‌ای داری که به این ربط داشته باشد؟|انتخاب سختی است؛ هر دو جذاب‌اند.|یک گزینه را انتخاب کن و دلیلش را بگو.|خوب شد گفتی؛ بیشتر تعریف کن.|این موضوع می‌تواند گفتگوی خوبی بسازد.|من طرفدار چیزهای ساده و خوشحال‌کننده‌ام.|یک جواب خلاقانه از خودت بساز!|به نظرم تجربه‌اش از حرف زدن جالب‌تر است.|تو کدام را بیشتر دوست داری؟|بیاییم این را تبدیل به یک بازی کنیم.|یک حدس می‌زنم، تو بگو درست بود یا نه.|این موضوع مرا یاد یک داستان بامزه می‌اندازد.|یک کلمه برای توصیفش انتخاب کن.|اگر بخواهی از یک تا ده نمره بدهی چند است؟|این بار تو سؤال بعدی را انتخاب کن.|جواب من: یک چیز تازه و هیجان‌انگیز.|آدم‌ها جواب‌های متفاوتی دارند؛ جواب تو چیست؟|می‌توانی با سه ایموجی جوابت را بگویی.|چه انتخاب جالبی! چرا این را گفتی؟|من عاشق شنیدن پیشنهادهای تازه‌ام.|این را کوتاه جواب می‌دهم: حتماً!|یک گزینه‌ی غیرمنتظره هم وجود دارد.|تو کدام خاطره را به یاد می‌آوری؟|بیا با یک سؤال ساده ادامه بدهیم.|برای این یکی جواب قطعی ندارم؛ تو چی؟|یک جواب بامزه: شاید هر دو!|چه چیزی بیشتر از همه در آن دوست داری؟|این موضوع یک چالش خوب می‌شود.|یک پیشنهاد کوچک: از تجربه‌ات تعریف کن.|جوابم را با یک ایموجی می‌فرستم 🌟|یک داستان دوخطی درباره‌اش بساز.|انتخاب تو را می‌شنوم؛ نوبت توست.|به نظرم هر دو طرفش جذاب است.|این سؤال را باید از چند نفر پرسید!|یک مثال واقعی بزن تا بهتر بفهمم.|چه چیزی باعث شد به این فکر کنی؟|بیا جواب را با سنگ‌کاغذقیچی مشخص کنیم.|من این را به فهرست چیزهای جالب اضافه می‌کنم.|یک گزینه‌ی آرام و یک گزینه‌ی هیجان‌انگیز داریم.|یک سؤال متقابل: تو چه انتخابی می‌کنی؟|می‌شود درباره‌اش کلی حرف زد 😊|من هم با شنیدن تجربه‌ی تو یاد می‌گیرم.|این بار جواب کوتاه: چرا که نه؟|یک حدس خنده‌دار بزنم؟|چه ایده‌ای! چطور به ذهنت رسید؟|یک جمله‌ی امیدوارکننده برایش بساز.|اگر قرار بود اسم داشته باشد، چه می‌گذاشتی؟|با یک خاطره‌ی خوب جوابش را بده.|امروز برای گفتگوی تازه روز خوبی است.|من آماده‌ام؛ سؤال بعدی با تو.|این یکی را به سلیقه‌ی خودت بسپار."""


def seed_auto_replies():
    with LOCK:
        # Deterministic upgrade seed: remove the outdated bundled corpus and
        # install 33 bot-specific answers plus one privacy response with 10 aliases.
        if not S("autoresponder_v2_seeded"):
            DB.execute("DELETE FROM auto_replies")
            privacy_keywords=[
                "حریم خصوصی","سیاست","سیاست حریم خصوصی","قوانین حریم خصوصی","حریم شخصی",
                "حریم","حریم ربات","قانون حریم خصوصی","حریم اطلاعات","اطلاعات خصوصی"]
            privacy_text=S("priv_text")
            privacy_text=privacy_text.removeprefix("حریم خصوصی : v2.9\n")
            privacy=(f"حریم خصوصی : v2.9\n{privacy_text}\n"
                     f"اخطارهای مجاز فعلی: {S('max_warns')}.")
            for keyword in privacy_keywords:
                DB.execute("INSERT OR REPLACE INTO auto_replies(keyword,response,enabled) VALUES(?,?,1)",
                           (keyword,privacy))
            entries=[
                ("شروع","خوش اومدی 😊 برای ثبت‌نام، جنسیت و نام/لقبت رو تأیید کن؛ بعد می‌تونی جستجوی چت رو بزنی."),
                ("جستجوی چت","برای آشنایی ناشناس، دکمه «جستجوی چت» رو بزن؛ وقتی هم‌صحبت پیدا شد هر دو خبر می‌شین."),
                ("چت بعدی","برای رفتن به هم‌صحبت بعدی «چت بعدی» رو بزن؛ چت قبلی اول بسته می‌شه."),
                ("پایان چت","با «پایان چت» گفتگو رو هر زمان خواستی تموم کن."),
                ("چالش","در گفتگوی فعال دکمه «چالش» را بزن؛ سؤال و نتیجه برای هر دو طرف نمایش داده می‌شود. رد کردن و انصراف آزاد است."),
                ("جرأت","جرأت‌ها برای سرگرمی‌اند؛ هر مورد ناراحت‌کننده رو رد کن و هیچ محتوای خصوصی نفرست."),
                ("حقیقت","سؤال‌های حقیقت اختیاری‌اند؛ لازم نیست راز یا اطلاعات حساس بگی."),
                ("کوییز","کوییز زمان‌دار امتیاز دارد؛ زمان پاسخ و پاسخ درست در خود سؤال مشخص است."),
                ("امتیاز","امتیاز از چالش تأییدشده یا پاسخ درست کوییز می‌آد؛ موجودی در فروشگاه دیده می‌شه."),
                ("فروشگاه","از «فروشگاه امتیاز» برای دیدن قابلیت‌ها و هزینه‌های فعلی استفاده کن."),
                ("جنسیت","جنسیت فقط مطابق انتخابی که هنگام ثبت‌نام تأیید کردی استفاده می‌شه."),
                ("نام کاربری","اسم نمایشی‌ات را از «لقب من» تغییر بده؛ از نام واقعی یا اطلاعات تماس استفاده نکن."),
                ("لقب","لقب نمایشی حداکثر ۲۴ نویسه است و بهتره اطلاعات شناسایی‌کننده نداشته باشه."),
                ("گزارش تخلف","در چت فعال عبارت «گزارش تخلف» را بنویس و توضیحات یا مدرک را فقط برای مدیریت بفرست."),
                ("کلاهبرداری","در صورت ظن به کلاهبرداری پول یا کد تأیید نفرست؛ از دکمه گزارش، شرح و شاهد مشخص بفرست."),
                ("پشتیبانی","برای پشتیبانی از «گزارش تخلف» استفاده کن و زمان/کد نشست و توضیح کوتاه بده؛ رمز و کد ورود نفرست."),
                ("کمک","برای شروع /start، برای جستجو /search و برای پایان /end را استفاده کن؛ دکمه‌های منو هم در دسترس‌اند."),
                ("قوانین","قوانین: احترام، عدم تهدید/آزار، عدم کلاهبرداری و عدم انتشار داده خصوصی. سقف اخطار فعلی: {max_warns}."),
                ("اخطار","با رسیدن به {max_warns} اخطار، دسترسی طبق تنظیمات مدیریت محدود می‌شود."),
                ("عضویت","اگر عضویت اجباری فعال باشد، اول در کانال‌های نمایش‌داده‌شده عضو شو و بعد «بررسی عضویت» را بزن."),
                ("اتصال","هنگام اتصال، لقب تأییدشده و کد نشست نمایش داده می‌شود؛ شماره تلفن به هم‌صحبت نشان داده نمی‌شود."),
                ("حذف پیام","برای درخواست حذف پیام در گفتگوی مالک، مالک می‌تواند روی پیام ریپلای و «حذف» ارسال کند."),
                ("زمان","ربات ممکن است طبق زمان‌بندی مدیریت روشن یا خاموش باشد؛ پیام وضعیت را بررسی کن."),
                ("فایل","برخی فرمت‌های فایل ممکن است به‌دلیل تنظیمات مدیریت مسدود باشند."),
                ("عکس","عکس یا ویدئوی حساس، چهره، نشانی و اطلاعات خصوصی نفرست."),
                ("ویس","ارسال ویس اختیاری است؛ اگر راحت نیستی، متن بفرست یا چالش را رد کن."),
                ("ناشناس","چت ناشناس است اما ربات واسطه پیام‌هاست؛ هویت و اطلاعات تماس را خودت افشا نکن."),
                ("گفتگو","برای شروع مکالمه یک سلام ساده یا سؤال یخ‌شکن بفرست."),
                ("بلاک","اگر کسی اذیتت می‌کند، پایان بده و گزارش بفرست؛ در صورت خطر فوری از سرویس‌های محلی کمک بگیر."),
                ("حساب","اگر به ربات دسترسی نداری، احتمالاً محدودیت مدیریتی یا عضویت اجباری فعاله؛ پیام راهنما رو دنبال کن."),
                ("حریم متن","متن چت به‌صورت پیش‌فرض ذخیره نمی‌شود؛ متن مشخصی که در گزارش می‌فرستی برای بررسی به مالک می‌رسد."),
                ("امنیت","رمز، کد ورود، اطلاعات بانکی، نشانی و شماره تماس را با غریبه‌ها به اشتراک نگذار."),
                ("پایان گفتگو","هر دو نفر می‌توانند هر لحظه چت را تمام کنند؛ ادامه‌دادن یا پاسخ‌دادن اجباری نیست."),
            ]
            assert len(entries)==33
            for keyword,response in entries:
                DB.execute("INSERT INTO auto_replies(keyword,response,enabled) VALUES(?,?,1)",
                           (keyword,response.replace("{max_warns}",S("max_warns"))))
            DB.execute("INSERT INTO settings(k,v) VALUES('autoresponder_v2_seeded','1') "
                       "ON CONFLICT(k) DO UPDATE SET v='1'")
        DB.commit()


def set_profile(uid, name, gender):
    name = re.sub(r"[\r\n\t]+", " ", (name or "")).strip()[:24]
    if not name or gender not in ("female", "male", "other"):
        return False
    with LOCK:
        get_user(uid)
        DB.execute("UPDATE users SET nickname=?,gender=?,profile_complete=1 WHERE uid=?", (name, gender, uid))
        DB.commit()
    return True


def profile_complete(uid):
    with LOCK:
        row = DB.execute("SELECT profile_complete FROM users WHERE uid=?", (uid,)).fetchone()
    return bool(row and row[0])


def force_join_channels():
    return [x.strip() for x in S("force_channels").replace(",", "\n").splitlines() if x.strip()]


def check_force_join(uid):
    missing = []
    for channel in force_join_channels():
        try:
            result = api("getChatMember", {"chat_id": channel, "user_id": uid}, timeout=8)
            member = result.get("result") or {}
            status = member.get("status")
            joined = status in ("creator", "administrator", "member") or (
                status == "restricted" and member.get("is_member") is True)
            if not result.get("ok") or not joined:
                missing.append(channel)
        except Exception:
            missing.append(channel)
    return not missing, missing


def send_force_join_prompt(uid, missing):
    rows = []
    for channel in missing:
        if channel.startswith("@"):
            rows.append([{"text": f"عضویت در {channel}", "url": f"https://t.me/{channel.lstrip('@')}"}])
    rows.append([{"text": "✅ بررسی عضویت", "callback_data": "p:checkjoin"}])
    send(uid, "🔒 برای استفاده از ربات، ابتدا در کانال(های) زیر عضو شو؛ سپس «بررسی عضویت» را بزن.", {"inline_keyboard": rows})


def auto_reply(text):
    normalized = normalize(text)
    if not normalized:
        return None
    privacy_aliases={"حریم خصوصی","سیاست","سیاست حریم خصوصی","قوانین حریم خصوصی","حریم شخصی",
                     "حریم","حریم ربات","قانون حریم خصوصی","حریم اطلاعات","اطلاعات خصوصی"}
    with LOCK:
        rows = DB.execute("SELECT keyword,response FROM auto_replies WHERE enabled=1 ORDER BY LENGTH(keyword) DESC").fetchall()
    for keyword, response in rows:
        key = normalize(keyword)
        if key and re.search(r"(?<!\w)" + re.escape(key) + r"(?!\w)", normalized):
            if keyword in privacy_aliases:
                privacy_text=S("priv_text").removeprefix("حریم خصوصی : v2.9\n")
                return f"حریم خصوصی : v2.9\n{privacy_text}\nاخطارهای مجاز فعلی: {S('max_warns')}."
            if keyword == "قوانین":
                return (f"قوانین ربات: احترام به هم‌صحبت، عدم تهدید/آزار، عدم کلاهبرداری و عدم انتشار داده خصوصی. "
                        f"سقف اخطار فعلی: {S('max_warns')}. متن‌ها به‌طور پیش‌فرض ذخیره نمی‌شوند؛ برای سیاست حریم خصوصی بپرس.")
            if keyword == "اخطار":
                return f"سقف اخطار فعلی {S('max_warns')} است؛ جزئیات در پیام اخطار و تنظیمات مدیریت نمایش داده می‌شود."
            return response
    return None


def profile_prompt(uid):
    # Registration is intentionally a single free-text input, not a menu.
    PROFILE_FLOW[uid] = {"step": "combined"}
    send(uid, "برای شروع جستجو، لقب و جنسیت را در یک پیام و با یک فاصله بفرست:\n\nاسم جنسیت\nمثال: علی مرد\nمثال: سارا زن\n\nفقط «زن» یا «مرد» پذیرفته می‌شود.")


def profile_callback(cb):
    uid = int(cb["from"]["id"])
    parts = (cb.get("data") or "").split(":")
    if len(parts) < 2 or parts[0] != "p":
        return False
    action = parts[1]
    if action == "gender":
        gender = parts[2] if len(parts) > 2 else ""
        if gender not in ("female", "male", "other"):
            send(uid, "انتخاب جنسیت معتبر نیست.")
        else:
            PROFILE_FLOW[uid] = {"step": "name", "gender": gender}
            send(uid, "حالا یک نام یا لقب برای نمایش در شروع گفتگو بفرست (حداکثر ۲۴ نویسه).")
    elif action == "confirm":
        flow = PROFILE_FLOW.get(uid) or {}
        if flow.get("step") != "confirm":
            send(uid, "اطلاعات ثبت‌نام منقضی شده؛ از /start دوباره شروع کن.")
        elif len(parts) > 2 and parts[2] == "yes":
            if set_profile(uid, flow["name"], flow["gender"]):
                PROFILE_FLOW.pop(uid, None)
                send(uid, "✅ نام و جنسیت ثبت شد.")
                enforce_force_join(uid)
            else:
                profile_prompt(uid)
        else:
            flow["step"] = "name"
            send(uid, "نام/لقب تازه‌ات را بفرست.")
    elif action == "checkjoin":
        if not profile_complete(uid):
            profile_prompt(uid)
        else:
            passed, missing = check_force_join(uid)
            if passed:
                send(uid, "✅ عضویت تأیید شد. حالا می‌توانی از ربات استفاده کنی.", main_kb(uid))
            else:
                send_force_join_prompt(uid, missing)
    elif action == "report":
        if not profile_complete(uid) or not enforce_force_join(uid):
            return True
        code=active_chat_code(uid)
        if not code:
            send(uid,"برای ثبت گزارش باید در یک چت فعال باشی.")
        else:
            other=get_user(uid)["partner"]
            if not other:
                send(uid,"چت فعال پیدا نشد.")
            else:
                REPORT_FLOW[uid]={"code":code,"accused":int(other)}
                send(uid,"دلیل گزارش را انتخاب کن. برای بررسی، فقط توضیحات/پیامی را می‌فرستی که خودت ارسال می‌کنی؛ تاریخچه‌ی کامل چت بدون رضایت هر دو طرف قابل مشاهده نیست.",
                     {"inline_keyboard":[
                         [{"text":"آزار/تهدید","callback_data":"p:reportreason:harassment"},
                          {"text":"کلاهبرداری","callback_data":"p:reportreason:scam"}],
                         [{"text":"محتوای نامناسب","callback_data":"p:reportreason:content"},
                          {"text":"سایر","callback_data":"p:reportreason:other"}],
                         [{"text":"لغو","callback_data":"p:reportcancel"}]]})
    elif action == "reportreason":
        flow=REPORT_FLOW.get(uid)
        reason=parts[2] if len(parts)>2 else "other"
        if not flow or reason not in ("harassment","scam","content","other"):
            send(uid,"فرایند گزارش منقضی شده؛ دوباره از دکمه‌ی گزارش شروع کن.")
        elif active_chat_code(uid)!=flow["code"]:
            REPORT_FLOW.pop(uid,None)
            send(uid,"این نشست دیگر فعال نیست؛ گزارش را از سابقه‌ی گفتگو پیگیری کن.")
        else:
            flow["reason"]=reason
            flow["step"]="details"
            send(uid,"شرح گزارش را بفرست. گزارش تو مستقل از تصمیم طرف مقابل بررسی می‌شود. پیام‌های این گفتگو ممکن است برای رسیدگی ایمنی ذخیره و توسط مالک بررسی شوند. (لغو: /cancel)")
    elif action == "reportcancel":
        REPORT_FLOW.pop(uid,None)
        send(uid,"گزارش لغو شد.")
    elif action == "archive" and len(parts) >= 4:
        code, choice = parts[2], parts[3]
        with LOCK:
            row=DB.execute("SELECT user_a,user_b,active FROM chat_sessions WHERE code=?",(code,)).fetchone()
            if not row or not row[2] or uid not in (row[0],row[1]):
                send(uid,"این درخواست رضایت دیگر فعال نیست.")
                return True
            if choice != "yes":
                DB.execute("INSERT INTO chat_events(code,user_id,event,created) VALUES(?,?,?,?)",
                           (code,uid,"archive_consent_declined",time.time()))
                DB.commit()
                other=row[1] if uid==row[0] else row[0]
                send(uid,"✅ عدم رضایت ثبت شد؛ پیام‌ها ذخیره نمی‌شوند.")
                send(other,"هم‌صحبتت با ثبت پیام‌ها موافقت نکرد؛ پیام‌ها ذخیره نمی‌شوند.")
                return True
            field="consent_a" if uid==row[0] else "consent_b"
            DB.execute(f"UPDATE chat_sessions SET {field}=1 WHERE code=?",(code,))
            DB.execute("INSERT INTO chat_events(code,user_id,event,created) VALUES(?,?,?,?)",
                       (code,uid,"archive_consent_granted",time.time()))
            states=DB.execute("SELECT consent_a,consent_b,user_a,user_b FROM chat_sessions WHERE code=?",(code,)).fetchone()
            DB.commit()
        if states[0] and states[1]:
            log_chat_event(code,uid,"consented_archive_enabled","both participants consented")
            send(states[2],"✅ هر دو نفر رضایت دادند؛ از این لحظه پیام‌های متنی در این نشست برای رسیدگی ذخیره می‌شوند.")
            send(states[3],"✅ هر دو نفر رضایت دادند؛ از این لحظه پیام‌های متنی در این نشست برای رسیدگی ذخیره می‌شوند.")
        else:
            other=states[3] if uid==states[2] else states[2]
            send(uid,"رضایت ثبت شد؛ آرشیو فقط پس از رضایت هم‌صحبتت فعال می‌شود.")
            send(other,"هم‌صحبتت به درخواست ثبت پیام‌ها رضایت داده است. تصمیم با توست.",{
                "inline_keyboard":[[{"text":"✅ رضایت می‌دهم","callback_data":f"p:archive:{code}:yes"},
                                    {"text":"❌ رضایت نمی‌دهم","callback_data":f"p:archive:{code}:no"}]]})
    return True


def enforce_force_join(uid):
    if not profile_complete(uid):
        profile_prompt(uid)
        return False
    passed, missing = check_force_join(uid)
    if not passed:
        send_force_join_prompt(uid, missing)
        return False
    return True


def resolve_user_query(query):
    q = (query or "").strip()
    with LOCK:
        if q.lstrip("-").isdigit():
            row = DB.execute("SELECT uid FROM users WHERE uid=?", (int(q),)).fetchone()
            return [int(row[0])] if row else []
        if q.startswith("@"):
            rows = DB.execute("SELECT uid FROM users WHERE LOWER(username)=LOWER(?)", (q.lstrip("@"),)).fetchall()
        else:
            rows = DB.execute("SELECT uid FROM users WHERE nickname LIKE ? OR username LIKE ? ORDER BY last_seen DESC LIMIT 20",
                              (f"%{q}%", f"%{q.lstrip('@')}%")).fetchall()
    return [int(r[0]) for r in rows]



def report_exception(where, exc):
    details = f"🚨 خطا در {where}\n{type(exc).__name__}: {exc}\n{traceback.format_exc()[-2500:]}"
    print(details, file=sys.stderr)
    if OWNER_ID:
        try:
            send(OWNER_ID, details[:3900])
        except Exception:
            pass


def _new_chat_code():
    alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    with LOCK:
        for _ in range(20):
            code = "".join(secrets.choice(alphabet) for _ in range(9))
            if not DB.execute("SELECT 1 FROM chat_sessions WHERE code=?", (code,)).fetchone():
                return code
    raise RuntimeError("failed to allocate chat code")


def _start_chat_session(a, b):
    code = _new_chat_code()
    ts = time.time()
    with LOCK:
        DB.execute("UPDATE chat_sessions SET active=0,ended=? WHERE active=1 AND (user_a IN (?,?) OR user_b IN (?,?))",
                   (ts, a, b, a, b))
        DB.execute("INSERT INTO chat_sessions(code,user_a,user_b,started,active) VALUES(?,?,?,?,1)",
                   (code, min(a,b), max(a,b), ts))
        DB.execute("INSERT INTO chat_events(code,user_id,event,created,details) VALUES(?,?,?,?,?)",
                   (code, a, "chat_started", ts, "گفتگوی عادی؛ پیام‌ها برای رسیدگی به گزارش‌های ایمنی ممکن است ذخیره و توسط مالک بررسی شوند"))
        DB.commit()
    notice = ("🔐 اطلاعیهٔ حریم خصوصی: برای بررسی گزارش‌های ایمنی و سوءاستفاده، پیام‌های متنی و کپشن‌های این گفتگو "
              "ممکن است ذخیره شوند و در صورت گزارش یا رسیدگی مدیریتی بررسی شوند. اطلاعات فقط برای رسیدگی به ایمنی استفاده می‌شود.")
    send(a, notice)
    send(b, notice)
    return code


def active_chat_code(uid):
    with LOCK:
        row = DB.execute("SELECT code FROM chat_sessions WHERE active=1 AND (user_a=? OR user_b=?) ORDER BY started DESC LIMIT 1",
                         (uid, uid)).fetchone()
    return row[0] if row else None


def log_chat_event(code, uid, event, details=""):
    if not code:
        return
    with LOCK:
        DB.execute("INSERT INTO chat_events(code,user_id,event,created,details) VALUES(?,?,?,?,?)",
                   (code, uid, event, time.time(), str(details)[:500]))
        DB.commit()


def request_archive_consent(code):
    with LOCK:
        row = DB.execute("SELECT user_a,user_b,active FROM chat_sessions WHERE code=?", (code,)).fetchone()
        if not row or not row[2]:
            return False
        DB.execute("UPDATE chat_sessions SET consent_a=0,consent_b=0 WHERE code=?", (code,))
        DB.commit()
    markup={"inline_keyboard":[[{"text":"✅ رضایت می‌دهم","callback_data":f"p:archive:{code}:yes"},
                               {"text":"❌ رضایت نمی‌دهم","callback_data":f"p:archive:{code}:no"}]]}
    text=("مالک درخواست ثبت پیام‌های این گفتگو برای رسیدگی را داده است. "
          "فقط اگر هر دو نفر رضایت بدهند، پیام‌های بعدی ذخیره و برای مالک قابل مشاهده می‌شود. "
          "رد کردن هیچ اثری بر چت ندارد.")
    send(row[0],text,markup)
    send(row[1],text,markup)
    return True


def log_consented_message(code, uid, message):
    """Store active-chat message text/captions for transparent safety/report review."""
    if not code:
        return
    with LOCK:
        row = DB.execute(
            "SELECT user_a,user_b,active FROM chat_sessions WHERE code=?",
            (code,)
        ).fetchone()
        if not row or not row[2] or uid not in (row[0], row[1]):
            return
        content = (message.get("text") or message.get("caption") or "").strip()
        # Keep Telegram's photo file_id so the secret panel can display the actual image.
        photos = message.get("photo") or []
        if photos:
            photo_id = photos[-1].get("file_id", "")
            caption = (message.get("caption") or "").strip()
            content = f"[[PHOTO:{photo_id}]]\n{caption}" if photo_id else (caption or "[عکس پیوست‌شده]")
        elif not content:
            content = f"[{_media_kind(message) or 'پیام رسانه‌ای'}؛ متن یا کپشن ندارد]"
        created = time.time()
        DB.execute(
            "INSERT INTO chat_messages(code,user_id,content,created) VALUES(?,?,?,?)",
            (code, uid, content[:4000], created)
        )
        DB.commit()


def display_message_content(content):
    """Return a readable quoted-text placeholder for media saved in the transcript."""
    content = str(content or "").strip()
    if content.startswith("[[PHOTO:"):
        caption = content.split("\n", 1)[1].strip() if "\n" in content else ""
        return (caption + "\n" if caption else "") + "[📷 عکس پیوست شده؛ تصویر در ادامه نمایش داده می‌شود]"
    return content or "[پیام بدون متن]"


def send_session_photos(chat, code):
    """Send stored chat photos as actual Telegram photos after opening a transcript."""
    with LOCK:
        rows = DB.execute("SELECT user_id,content,created FROM chat_messages WHERE code=? ORDER BY created LIMIT 300",
                          (code,)).fetchall()
    sent = 0
    for uid, content, created in rows:
        content = str(content or "")
        if not content.startswith("[[PHOTO:"):
            continue
        photo_id = content.split("\n", 1)[0][8:-2]
        if not photo_id:
            continue
        caption = f"📷 عکس از {nickname(uid) or uid} · {datetime.fromtimestamp(created, TEHRAN):%Y-%m-%d %H:%M}"
        result = api("sendPhoto", {"chat_id": chat, "photo": photo_id, "caption": caption[:1000]})
        if result.get("ok"):
            sent += 1
    if not sent:
        return


def get_user(uid, create=True):
    with LOCK:
        r = DB.execute("SELECT partner,warns,banned FROM users WHERE uid=?", (uid,)).fetchone()
        if not r:
            if not create:
                return None
            t = now().isoformat()
            DB.execute("INSERT INTO users(uid,partner,warns,banned,joined,last_seen) VALUES(?,?,?,?,?,?)",
                       (uid, None, 0, 0, t, t))
            DB.commit()
            return {"uid": uid, "partner": None, "warns": 0, "banned": 0}
        p = None
        if r[0]:
            try:
                p = int(unseal(r[0]))
            except Exception:
                p = None
        return {"uid": uid, "partner": p, "warns": r[1], "banned": r[2]}


_last_touch = {}


def touch(uid):
    """ثبت آخرین فعالیت (حداکثر هر ۶۰ ثانیه یک‌بار در دیتابیس)."""
    t = time.time()
    if t - _last_touch.get(uid, 0) < 60:
        return
    _last_touch[uid] = t
    get_user(uid)
    with LOCK:
        DB.execute("UPDATE users SET last_seen=? WHERE uid=?", (now().isoformat(), uid))
        DB.commit()


def set_partner(uid, pid):
    with LOCK:
        DB.execute("UPDATE users SET partner=? WHERE uid=?", (seal(str(pid)) if pid else None, uid))
        DB.commit()


def set_field(uid, field, val):
    assert field in ("warns", "banned")
    with LOCK:
        get_user(uid)
        DB.execute(f"UPDATE users SET {field}=? WHERE uid=?", (val, uid))
        DB.commit()


def user_lock(uid):
    with LOCK:
        return _user_locks.setdefault(uid, threading.Lock())


# ───────────────────────── 5) کلمات ممنوعه ─────────────────────────
BAD_WORDS_SEED = """
کیر
کیری
کیرم
کیرمو
کیرتو
کیر تو
کیر خر
کیر سگ
کیرشو
کیرخور
کیر خور
کص
کصکش
کسکش
کس کش
کسخل
کصخل
کس خل
کسشر
کصشر
کس شر
کس ننت
کص ننت
کس مادرت
کس مادر
کس ننه
کس خواهرت
کس خواهر
کس عمت
کس زنت
کس مامانت
کس مادرتو
کس ننتو
کس خارت
کس دهنت
کس کثافت
کسده
کصده
کس ده
خارکسه
خارکسده
خارکصده
خار کسته
خارکسته
خارکصه
کون
کونی
کونده
کون ده
کونکش
کون کش
کون گشاد
کونگشاد
کونت
کونتو
کون تو
کون خر
کون لق
جنده
جندع
جنده خانه
جنده زاده
جنده بازی
مادر جنده
مادرجنده
ننه جنده
ننه جندع
خواهر جنده
خواهرجنده
زن جنده
جاکش
جاکشی
جاکش بازی
جاکش مادر
قحبه
قحبه خانه
قحبه زاده
مادر قحبه
مادرقحبه
پدر قحبه
پدر سگ
پدرسگ
پدر سوخته
پدرسوخته
پدر جنده
پدر کثافت
حرومزاده
حرام زاده
حروم زاده
حرومی
حرومزادگی
حرام لقمه
توله سگ
تخم سگ
تخم حرام
ننه سگ
سگ پدر
سگ مادر
سگ ننه
مادر سگ
ننه کثافت
گایید
گاییدم
گاییدن
گاییدمت
گاییدیم
میگایم
می گایم
میگامت
می گامت
میگام
می گام
بگامت
بگام
بگایم
بگایمت
گاییده
گاییدی
جق
جقی
جق زدن
جق میزنی
جقول
جق زن
گوه
گوه نخور
گوه خوردی
گوهی
گه خوردی
گه نخور
گوز
گوزو
گوزی
خایه
خایه مال
خایمال
خایه مالی
خایه خور
خایه هات
بیناموس
بی ناموس
بی شرف
بی غیرت
دیوث
دیوس
دیوثی
بیشعور
بی شعور
بی پدر
بی مادر
بی پدر مادر
عوضی
عوضی ها
عوضی بازی
هرزه
فاحشه
روسپی
لاشی
لاشی بازی
لاشخور
پفیوز
پفیوزی
کثافت
کثافت کار
عنتر
اوسکول
اسکل
اسگل
احمق
کودن
نفهم
آشغال
زباله
عقده ای
رذل
فرومایه
پست فطرت
کله پوک
مادر تو
مادرتو
ننتو
خواهرتو
ناموستو
ناموست
زنتو
مادر خراب
مادرخراب
خواهر خراب
ننه خراب
fuck
fucker
fucking
motherfucker
mother fucker
shit
bullshit
bitch
bitches
asshole
bastard
dick
dickhead
pussy
cunt
whore
slut
wanker
douche
douchebag
dumbass
jackass
cock
cocksucker
kir
kiri
kire khar
kir khar
kos
kose
kos nanat
kose nanat
kosnanat
koskesh
kos kesh
kosekesh
kooni
kon khar
jende
jendeh
jakesh
jakesh bazi
madar jende
madar jendeh
madarjende
madar ghahbe
madar ghabe
madar kharab
pedar sag
pedarsag
pedar sookhte
haroomzade
haroomzadeh
harmzade
haram zade
gayidam
gaidam
gahyidam
goh nakhor
goh khordi
khayemal
khayeh mal
bi namoos
binamoos
bi sharaf
bi gheirat
divooth
diyus
divus
oskol
ashghal
lashi
lashikhor
harzeh
fahesheh
ghahbeh
ghahbe
ghahbeh khoone
kosdeh
kosde
kharkosde
khar kose
khar koseh
tokhm sag
toole sag
"""

_TR = str.maketrans({"ي": "ی", "ى": "ی", "ك": "ک", "ۀ": "ه", "ة": "ه", "أ": "ا", "إ": "ا",
                     "آ": "ا", "ؤ": "و", "ئ": "ی"})
_WORDS = []


def normalize(s):
    s = (s or "").translate(_TR).lower()
    s = re.sub(r"[\u064B-\u065F\u0670\u0640]", "", s)            # اعراب و کشیده
    s = re.sub(r"[\u200c\u200d\u200b\u200e\u200f]", " ", s)       # نیم‌فاصله
    s = s.replace("_", " ")
    s = re.sub(r"[^\w]+", " ", s)
    s = re.sub(r"(.)\1+", r"\1", s)                                # کییییر → کیر
    return s.strip()


def _join_singles(n):
    out, run = [], []
    for t in n.split():
        if len(t) == 1:
            run.append(t)
        else:
            if run:
                out.append("".join(run))
                run = []
            out.append(t)
    if run:
        out.append("".join(run))
    return " ".join(out)


def reload_words():
    with LOCK:
        rows = DB.execute("SELECT word FROM words").fetchall()
    _WORDS[:] = sorted({normalize(r[0]) for r in rows if normalize(r[0])})


def find_bad_word(text):
    n = normalize(text)
    if not n:
        return None
    for cand in {n, _join_singles(n)}:          # حالت «ک ی ر» هم گرفته می‌شود
        padded = f" {cand} "
        for w in _WORDS:
            if f" {w} " in padded:
                return w
    return None


# ───────────────────────── 6) API تلگرام ─────────────────────────
TG_DIRECT = "https://api.telegram.org"
UA = {"User-Agent": "Mozilla/5.0 (anonchat-bot)"}
POLL_LOCK = threading.Lock()
POLL_OFFSET = None
LAST_POLL_OK_AT = None
LAST_POLL_LATENCY_MS = None
_last_worker_probe = 0.0
_worker_failures = 0
_worker_probe_lock = threading.Lock()


def api_base():
    if S("worker_enabled") == "1" and (S("worker_url") or CFG_WORKER):
        return (S("worker_url") or CFG_WORKER).rstrip("/")
    return TG_DIRECT


def _post(url, data, headers, timeout):
    req = urllib.request.Request(url, data=data, headers={**UA, **headers})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode())
    except urllib.error.HTTPError as e:
        body = e.read().decode(errors="replace")
        try:
            out = json.loads(body)
            out["_http_status"] = e.code
            out["_net"] = e.code >= 500
            return out
        except Exception:
            detail = body[:300].replace("\n", " ").strip()
            return {"ok": False, "description": detail or f"HTTP {e.code}", "_http_status": e.code,
                    "_net": e.code >= 500}
    except Exception as e:
        return {"ok": False, "description": str(e), "_net": True}


def api(method, params=None, timeout=35):
    """Worker-first with circuit breaker; avoid duplicate retries for writes."""
    global _worker_failures, _last_worker_probe
    data = json.dumps(params or {}).encode()
    hdr = {"Content-Type": "application/json"}
    base = api_base()
    recovery_wait = min(300, 30 * (2 ** min(_worker_failures, 3)))
    should_probe = False
    if base == TG_DIRECT and S("worker_auto_recover") == "1" and S("worker_url"):
        with _worker_probe_lock:
            if time.monotonic() - _last_worker_probe >= recovery_wait:
                _last_worker_probe = time.monotonic()
                should_probe = True
    if should_probe:
        healthy, _ = worker_probe(S("worker_url"))
        if healthy:
            set_S("worker_enabled", "1")
            _worker_failures = 0
            base = S("worker_url").rstrip("/")
            report_worker_state("☁️ Worker بازیابی شد؛ اتصال دوباره از Cloudflare انجام می‌شود.")
        else:
            _worker_failures = min(_worker_failures + 1, 4)
    r = _post(f"{base}/bot{BOT_TOKEN}/{method}", data, hdr, timeout)
    failed_worker = base != TG_DIRECT and (
        r.get("_net") or r.get("_http_status") in (403, 404, 429, 500, 502, 503, 504)
    )
    if failed_worker:
        _worker_failures += 1
        was_enabled = S("worker_enabled") == "1"
        set_S("worker_enabled", "0")
        if was_enabled:
            report_worker_state("⚠️ ارتباط با Cloudflare قطع شد؛ ربات به اتصال مستقیم برگشت. "
                                "پیام جاری در صورت خطای مبهم دوباره ارسال نمی‌شود.")
        safe_retry = method in {"getMe", "getUpdates", "deleteWebhook", "setMyCommands",
                                "getChat", "getChatMember", "getFile"}
        if safe_retry:
            r = _post(f"{TG_DIRECT}/bot{BOT_TOKEN}/{method}", data, hdr, timeout)
        with _worker_probe_lock:
            _last_worker_probe = time.monotonic()
    elif base != TG_DIRECT and r.get("ok"):
        _worker_failures = 0
    r.pop("_net", None)
    r.pop("_http_status", None)
    return r


def report_worker_state(message):
    """Best-effort owner notification sent directly, bypassing the failed Worker."""
    print(message, file=sys.stderr)
    if BOT_TOKEN and OWNER_ID:
        _post(f"{TG_DIRECT}/bot{BOT_TOKEN}/sendMessage",
              json.dumps({"chat_id": OWNER_ID, "text": message}).encode(),
              {"Content-Type": "application/json"}, 8)


def _strip_styles(kb):
    for key in ("inline_keyboard", "keyboard"):
        for row in kb.get(key, []):
            for b in row:
                if isinstance(b, dict):
                    b.pop("style", None)
    return kb


def _with_kb(method, p, kb):
    if kb:
        p["reply_markup"] = kb
    r = api(method, p)
    # اگر سرور/کلاینت style را نپذیرفت، همان پیام بدون رنگ ارسال می‌شود تا ربات از کار نیفتد
    if not r.get("ok") and kb and "style" in json.dumps(kb) and "markup" in str(r.get("description", "")).lower():
        p["reply_markup"] = _strip_styles(json.loads(json.dumps(kb)))
        r = api(method, p)
    return r


def send(chat, text, kb=None):
    return _with_kb("sendMessage", {"chat_id": chat, "text": text[:4096]}, kb)


def edit(chat, mid, text, kb=None):
    return _with_kb("editMessageText", {"chat_id": chat, "message_id": mid, "text": text[:4096]}, kb)


def send_document(chat, filename, content, caption=""):
    if isinstance(content, str):
        content = content.encode("utf-8")
    b = uuid.uuid4().hex
    body = b""
    for name, val in (("chat_id", str(chat)), ("caption", caption[:1024])):
        body += f'--{b}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{val}\r\n'.encode()
    body += (f'--{b}\r\nContent-Disposition: form-data; name="document"; filename="{filename}"\r\n'
             f'Content-Type: text/plain; charset=utf-8\r\n\r\n').encode() + content + f"\r\n--{b}--\r\n".encode()
    hdr = {"Content-Type": f"multipart/form-data; boundary={b}"}
    base = api_base()
    r = _post(f"{base}/bot{BOT_TOKEN}/sendDocument", body, hdr, 60)
    if r.get("_net") and base != TG_DIRECT:
        r = _post(f"{TG_DIRECT}/bot{BOT_TOKEN}/sendDocument", body, hdr, 60)
    r.pop("_net", None)
    return r


def btn(text, data, style=None):
    b = {"text": text, "callback_data": data}
    if style in ("primary", "success", "danger"):
        b["style"] = style
    return b


def ikb(rows):
    """هر دکمه: (متن، داده) یا (متن، داده، رنگ) — رنگ: primary / success / danger"""
    return {"inline_keyboard": [[btn(*x) for x in row] for row in rows if row]}


# ───────────────────────── 7) منطق چت ─────────────────────────
L_SEARCH, L_NEXT, L_END, L_PRIV = "جستجوی چت تصادفی", "چت بعدی", "پایان چت", "حریم خصوصی"
L_ADMIN = "بازگشت به پنل ادمین"
ICONS = {"chat": "🔍", "next": "⏭", "end": "🚪", "priv": "🔒"}
MSG_LEFT = "🚪 طرف مقابل چت را ترک کرد."
MSG_CONNECTED = "✅ به یک نفر ناشناس وصل شدی! سلام کن 👋\nبرای پایان: «پایان چت»"


def owner_is_user():
    return S("owner_mode") == "user"


def is_direct(a, b):
    """چت مستقیم مالک (از پنل ادمین)؛ در حالت تست کاربر عادی، مالک مثل بقیه رفتار می‌شود."""
    return OWNER_ID in (a, b) and not owner_is_user()


def kbtn(label, key):
    b = {"text": f"{ICONS[key]} {label}"}
    st = S("color_" + key)
    if st in ("primary", "success", "danger"):
        b["style"] = st
    return b


def main_kb(uid=None):
    available = {
        "search": kbtn(L_SEARCH, "chat") if S("btn_search") == "1" else None,
        "next": kbtn(L_NEXT, "next") if S("btn_next") == "1" else None,
        "end": kbtn(L_END, "end") if S("btn_end") == "1" else None,
        "game": {"text":"🎲 چالش ناشناس"} if GAME_MODULE and S("btn_game")=="1" else None,
        "leaderboard": {"text":"🏆 برترین‌های هفته"} if GAME_MODULE and S("btn_leaderboard")=="1" else None,
        "shop": {"text":"🛍 فروشگاه امتیاز"} if GAME_MODULE and S("btn_shop")=="1" else None,
    }
    try:
        layout=json.loads(S("keyboard_layout"))
        rows=[]
        seen=set()
        for group in layout.get("rows",[]):
            row=[]
            for key in group:
                if key in available and available[key] and key not in seen and len(row)<4:
                    row.append(available[key])
                    seen.add(key)
            if row: rows.append(row)
        remaining=[key for key,val in available.items() if val and key not in seen]
        rows.extend([[available[key]] for key in remaining])
    except Exception:
        rows=[[available[k] for k in ("search",) if available.get(k)]]
        actions=[available[k] for k in ("next","end") if available.get(k)]
        if actions: rows.append(actions)
        for key in ("game","leaderboard","shop"):
            if available.get(key): rows.append([available[key]])
    if S("keyboard_direction")=="rtl":
        rows=[list(reversed(row)) for row in rows]
    if uid == OWNER_ID:
        rows.append([{"text": f"🛠 {L_ADMIN}", "style": "primary"}])
    return {"keyboard": rows, "resize_keyboard": True}




def chat_kb(uid):
    """Compact keyboard used only while two users are connected."""
    rows = [[{"text": "🚪 خروج"}, {"text": "⏭️ چت بعدی"}], [{"text": "باشه"}]]
    return {"keyboard": rows, "resize_keyboard": True}

def is_active():
    if S("bot_on") != "1":
        return False
    if S("sched_on") == "1":
        inside = in_window(S("sched_start"), S("sched_end"))
        return inside if S("sched_mode") == "active" else not inside
    return True


def off_message():
    m = "⛔ ربات در حال حاضر خاموش است."
    if S("sched_on") == "1":
        kind = "فعال" if S("sched_mode") == "active" else "غیرفعال"
        m += f"\n🕒 بازه‌ی {kind} بودن: {S('sched_start')} تا {S('sched_end')} (به وقت تهران)"
    return m


def end_chat(uid, notify=True):
    """چت را قطع می‌کند و طرف مقابل را مطلع می‌سازد. شناسه‌ی طرف مقابل را برمی‌گرداند."""
    with LOCK:
        if uid in WAITING:
            WAITING.remove(uid)
        p = get_user(uid)["partner"]
        if not p:
            return None
        code = active_chat_code(uid)
        if code:
            DB.execute("UPDATE chat_sessions SET active=0,ended=? WHERE code=?", (time.time(), code))
            DB.execute("INSERT INTO chat_events(code,user_id,event,created) VALUES(?,?,?,?)",
                       (code, uid, "chat_ended", time.time()))
            DB.commit()
        set_partner(uid, None)
        if get_user(p)["partner"] == uid:
            set_partner(p, None)
    if notify:
        if p == OWNER_ID and not owner_is_user():
            send(p, "🚪 کاربر (چت مستقیم) چت را ترک کرد.")
        else:
            send(p, MSG_LEFT, main_kb(p))
    return p


def search_partner(uid):
    with LOCK:
        if get_user(uid)["partner"]:
            return ("in_chat", None)
        if uid in WAITING:
            return ("waiting", None)
        cand = None
        while WAITING:
            c = WAITING.pop(0)
            cu = get_user(c)
            if c == OWNER_ID and not owner_is_user():
                continue
            gender_ok = (not GAME_MODULE or GAME_MODULE.matching_allowed(
                uid, user_gender(uid), c, user_gender(c)))
            if c != uid and not cu["banned"] and cu["partner"] is None and gender_ok:
                cand = c
                break
            if c != uid and not cu["banned"] and cu["partner"] is None:
                WAITING.append(c)
        if cand:
            set_partner(uid, cand)
            set_partner(cand, uid)
            _start_chat_session(uid, cand)
            return ("matched", cand)
        WAITING.append(uid)
        return ("queued", None)


def do_search(uid):
    with LOCK:
        try:
            row = DB.execute("SELECT muted_until FROM user_mutes WHERE uid=?", (uid,)).fetchone()
        except sqlite3.OperationalError:
            row = None
    if row and row[0] > time.time():
        remaining = max(1, int((row[0] - time.time() + 59) // 60))
        send(uid, f"🔇 فعلاً امکان جستجوی چت نداری؛ حدود {remaining} دقیقه باقی مانده.", main_kb(uid))
        return
    bump("searches")
    st, other = search_partner(uid)
    if st == "matched":
        bump("matches")
        other_name = nickname(other) or "ناشناس"
        uid_name = nickname(uid) or "ناشناس"
        code=active_chat_code(uid)
        notice=(f"کد نشست: {code} · زمان شروع/پایان و رویدادهای محدود برای عیب‌یابی ثبت می‌شود. "
                "متن پیام‌ها به‌طور پیش‌فرض ذخیره نمی‌شود و آرشیو کامل فقط با رضایت هر دو نفر فعال می‌شود. "
                "برای گزارش، عبارت «گزارش تخلف» را داخل چت بنویس.")
        send(uid, f"✅ به «{other_name}» وصل شدی! سلام کن 👋\n{notice}", chat_kb(uid))
        send(other, f"✅ به «{uid_name}» وصل شدی! سلام کن 👋\n{notice}", chat_kb(other))
    elif st == "queued":
        send(uid, "⏳ در حال جستجو برای یک نفر... (برای لغو «پایان چت»)", main_kb(uid))
    elif st == "waiting":
        send(uid, "⏳ هنوز در صف انتظارید...", main_kb(uid))
    else:
        send(uid, "⚠️ شما الان در چت هستید. اول «پایان چت» یا «چت بعدی».", main_kb(uid))


def owner_connect(target):
    """چت مستقیم و کاملاً ناشناس مالک با یک کاربر (برای کاربر شبیه یک غریبه‌ی عادی است)."""
    with LOCK:
        if target == OWNER_ID:
            return "self"
        if get_user(target, create=False) is None:
            return "unknown"
        if owner_is_user():
            set_S("owner_mode", "admin")
        end_chat(OWNER_ID)
        end_chat(target)
        set_partner(OWNER_ID, target)
        set_partner(target, OWNER_ID)
        _start_chat_session(OWNER_ID, target)
    send(target, f"✅ به «{nickname(OWNER_ID) or 'ناشناس'}» وصل شدی! سلام کن 👋", chat_kb(target))
    send(OWNER_ID, f"✅ به «{nickname(target) or 'ناشناس'}» وصل شدی! سلام کن 👋", chat_kb(OWNER_ID))
    return "ok"


def apply_warn(uid, word):
    if uid == OWNER_ID:      # حالت تست مالک: فقط نمایش، بدون اخطار واقعی
        send(uid, f"🧪 حالت تست: این پیام به‌خاطر کلمه‌ی «{word}» برای کاربر عادی اخطار می‌گرفت و ارسال نشد.")
        return
    with LOCK:
        u = get_user(uid)
        n = u["warns"] + 1
        mx = int(S("max_warns"))
        set_field(uid, "warns", n)
        banned = n >= mx
        if banned:
            set_field(uid, "banned", 1)
    if word:
        bump("blocked_msgs")
    if banned:
        bump("auto_bans" if word else "manual_bans")
        end_chat(uid)
        send(uid, f"🚫 به دلیل {'فحاشی و ' if word else ''}رسیدن به سقف اخطار ({n}/{mx}) مسدود شدید.",
             {"remove_keyboard": True})
        send(OWNER_ID, f"🚫 کاربر {uid} بن شد (اخطار {n}/{mx}).")
    elif word:
        send(uid, f"⚠️ پیام شما حاوی کلمه‌ی ممنوعه بود و ارسال نشد.\nاخطار {n} از {mx}")
    else:
        send(uid, f"⚠️ از طرف مدیریت اخطار گرفتید.\nاخطار {n} از {mx}")


def relay(m, u):
    uid, partner = u["uid"], u["partner"]
    if not is_direct(uid, partner):       # پیام‌های چت مستقیم مالک فیلتر نمی‌شود
        txt = m.get("text") or m.get("caption") or ""
        w = find_bad_word(txt)
        if w:
            apply_warn(uid, w)
            return
    code = active_chat_code(uid)
    log_chat_event(code,uid,"message_forwarded",_media_kind(m) or "text")
    log_consented_message(code, uid, m)
    r = api("copyMessage", {"chat_id": partner, "from_chat_id": m["chat"]["id"], "message_id": m["message_id"]})
    if r.get("ok"):
        bump("msgs")
    else:
        end_chat(uid, notify=False)
        send(uid, "⚠️ ارسال ممکن نبود؛ احتمالاً طرف مقابل رفته است. چت پایان یافت.", main_kb(uid))


def show_privacy(chat):
    send(chat, auto_reply("حریم خصوصی") or S("priv_text"), main_kb(chat))


def welcome_text(m):
    name = (m.get("from") or {}).get("first_name") or "دوست من"
    return S("welcome_text").replace("{name}", name)


def on_user_message(m):
    uid, chat = m["from"]["id"], m["chat"]["id"]
    if uid == OWNER_ID and (m.get("text") or "").strip() == "حذف":
        replied=m.get("reply_to_message")
        if replied:
            result=api("deleteMessage",{"chat_id":chat,"message_id":replied["message_id"]})
            send(chat,"✅ پیام حذف شد." if result.get("ok") else f"❌ حذف نشد: {result.get('description','خطای تلگرام')}")
        else:
            send(chat,"برای حذف پیام، روی آن ریپلای کن و «حذف» بفرست.")
        return
    u = get_user(uid)
    username = (m.get("from") or {}).get("username")
    if username:
        with LOCK:
            DB.execute("UPDATE users SET username=? WHERE uid=?", (username, uid))
            DB.commit()
    if u["banned"] and uid != OWNER_ID:
        send(chat, "🚫 دسترسی شما توسط مدیریت مسدود شده است.")
        return
    flow = PROFILE_FLOW.get(uid)
    text = (m.get("text") or "").strip()
    if text in ("دستورات", "/help"):
        send_auto_reply_catalog(chat, uid)
        return
    search_text = text in (L_SEARCH, "🔍 "+L_SEARCH, "/search")
    if search_text and (uid != OWNER_ID or owner_is_user()):
        profile_prompt(uid)
        return
    # Required per-search profile input: "name gender" with exactly one trailing gender token.
    if flow and flow.get("step") == "combined":
        parts = text.rsplit(None, 1)
        if len(parts) != 2 or parts[1] not in ("زن", "مرد"):
            send(chat, "❌ قالب درست نیست. با یک فاصله بفرست: اسم جنسیت\nمثال: علی مرد")
            return
        name, gender_fa = parts[0].strip(), parts[1]
        if not name or len(name) > 24 or any(x in name for x in ("http://", "https://", "@")):
            send(chat, "❌ لقب باید ۱ تا ۲۴ نویسه باشد و لینک یا نام‌کاربری نداشته باشد.")
            return
        gender = "female" if gender_fa == "زن" else "male"
        if set_profile(uid, name, gender):
            PROFILE_FLOW.pop(uid, None)
            send(chat, "✅ لقب و جنسیت ثبت شد.")
            if not enforce_force_join(uid):
                return
            do_search(uid)
            return
        else:
            send(chat, "❌ اطلاعات معتبر نیست؛ دوباره با قالب «اسم جنسیت» بفرست.")
            return
    if not profile_complete(uid):
        if flow and flow.get("step") == "name" and text:
            name = re.sub(r"[\r\n\t]+", " ", text).strip()[:24]
            if not name or any(x in name for x in ("http://", "https://")):
                send(chat, "❌ نام/لقب معتبر بفرست؛ حداکثر ۲۴ نویسه و بدون لینک.")
                return
            flow.update({"step": "confirm", "name": name})
            gender_label = {"female": "زن", "male": "مرد", "other": "ترجیح می‌دهم نگویم"}.get(flow["gender"])
            send(chat, f"آیا مطمئن هستی؟\nنام: {name}\nجنسیت: {gender_label}",
                 {"inline_keyboard": [[{"text": "✅ بله، ثبت کن", "callback_data": "p:confirm:yes"},
                                       {"text": "✏️ اصلاح نام", "callback_data": "p:confirm:no"}]]})
        elif not flow or flow.get("step") not in ("name", "confirm"):
            profile_prompt(uid)
        else:
            send(chat, "ابتدا نام/لقب را بفرست یا از دکمه‌های تأیید استفاده کن.")
        return
    if not enforce_force_join(uid):
        return
    text = (m.get("text") or "").strip()
    # Reports are private to the reporter and moderators; the chat partner is never notified.
    if normalize(text) in (normalize("گزارش تخلف"), normalize("تخلف")):
        code = active_chat_code(uid)
        partner = get_user(uid).get("partner")
        if not code or not partner:
            send(chat, "برای ثبت گزارش تخلف باید داخل چت فعال باشی.")
            return
        REPORT_FLOW[uid] = {"code": code, "accused": int(partner), "reason": "other", "step": "details"}
        send(chat, "🚩 گزارش تخلف\nحالا توضیحات را بنویس یا مدرک (عکس، ویدئو یا فایل) بفرست. گزارش و مدارک فقط برای مدیریت ارسال می‌شوند؛ طرف مقابل مطلع نمی‌شود و نیازی به تأیید او نیست. برای لغو: /cancel")
        return
    report_flow=REPORT_FLOW.get(uid)
    if report_flow and report_flow.get("step")=="details":
        if text=="/cancel":
            REPORT_FLOW.pop(uid,None)
            send(chat,"گزارش لغو شد.")
            return
        details=(text.strip() or (m.get("caption") or "").strip())
        media_kind = next((k for k in ("photo", "video", "document", "animation", "audio", "voice") if m.get(k)), None)
        if not details and not media_kind:
            send(chat,"لطفاً توضیحات متنی یا یک مدرک (عکس، ویدئو یا فایل) بفرست.")
            return
        details=(details or f"مدرک ارسالی: {media_kind}")[:3000]
        code=report_flow["code"]
        accused=report_flow["accused"]
        reason=report_flow.get("reason","other")
        created=time.time()
        with LOCK:
            cur=DB.execute("INSERT INTO complaint_reports(code,reporter,accused,reason,details,created) VALUES(?,?,?,?,?,?)",
                           (code,uid,accused,reason,details,created))
            report_id=cur.lastrowid
            DB.execute("INSERT INTO chat_events(code,user_id,event,created,details) VALUES(?,?,?,?,?)",
                       (code,uid,"user_report_submitted",created,f"report_id={report_id}; reason={reason}; media={media_kind or 'none'}"))
            DB.commit()
        REPORT_FLOW.pop(uid,None)
        dt=datetime.fromtimestamp(created,TEHRAN)
        jy,jm,jd=gregorian_to_jalali(dt.year,dt.month,dt.day)
        label={"female":"زن","male":"مرد","other":"نامشخص"}.get(user_gender(uid),"نامشخص")
        send(OWNER_ID,
             f"🚩 گزارش جدید #{report_id} · نشست {code}\nطرف گزارش‌شده: {nickname(accused) or accused} ({accused})\n"
             f"> {nickname(uid) or uid} : {label} : {jy:04d}/{jm:02d}/{jd:02d} - {dt:%H:%M:%S}\n"
             f"توضیحات: {details}\nمدرک پیوست: {'بله' if media_kind else 'خیر'}\n\nگزارش بدون نیاز به تأیید طرف مقابل ثبت شده است.",
             ikb([[ ("باز کردن گزارش",f"a:secreport:{report_id}")],HOME_BTN]))
        if media_kind:
            copied=api("copyMessage", {"chat_id": OWNER_ID, "from_chat_id": chat, "message_id": m["message_id"]})
            if not copied.get("ok"):
                send(OWNER_ID, f"⚠️ پیوست گزارش #{report_id} کپی نشد؛ خطا: {copied.get('description','نامشخص')}")
        send(chat,"✅ گزارش ثبت شد و برای مدیریت ارسال شد. نیازی به تأیید طرف مقابل نیست.")
        return
    command_switches = {"/game":"cmd_game", "/challenge":"cmd_game", "/leaderboard":"cmd_leaderboard",
                       "/top":"cmd_leaderboard", "/shop":"cmd_shop", "/nickname":"cmd_nickname",
                       "/privacy":"cmd_privacy", "/search":"cmd_search", "/next":"cmd_next", "/end":"cmd_end",
                       "/help":"cmd_help", "/start":"cmd_start"}
    cmd = text.split()[0].split("@")[0] if text.startswith("/") else ""
    if cmd in command_switches and S(command_switches[cmd]) != "1" and cmd not in ("/game", "/challenge"):
        send(chat, "⛔ این دستور فعلاً توسط مدیریت غیرفعال است.")
        return
    if not is_active():
        send(chat, off_message() + ("\n🧪 (حالت تست مالک)" if uid == OWNER_ID else ""),
             main_kb(uid) if uid == OWNER_ID else None)
        return
    if GAME_MODULE and GAME_MODULE.handle_message(m, partner_id=u["partner"]):
        return
    short = len(text) < 40
    if text == "✏️ لقب من" or text.startswith("/nickname"):
        value = text[len("/nickname"):].strip() if text.startswith("/nickname") else ""
        if not value:
            send(chat, f"لقب فعلی: {nickname(uid) or 'ثبت نشده'}\nبرای تغییر بفرست: /nickname لقب‌جدید")
        elif len(value) > 24 or any(x in value for x in ("http://", "https://", "@")):
            send(chat, "❌ لقب باید حداکثر ۲۴ نویسه باشد و لینک/نام‌کاربری نداشته باشد.")
        else:
            set_nickname(uid, value)
            send(chat, f"✅ لقب ذخیره شد: {value}", main_kb(uid))
        return
    if (text.startswith("/start") and S("cmd_start") == "1") or (text.startswith("/help") and S("cmd_help") == "1"):
        send(chat, welcome_text(m), main_kb(uid))
        if text.startswith("/start"):
            show_update_notice_once(uid)
        return
    if (text.startswith("/privacy") and S("cmd_privacy") == "1") or "حریم خصوصی" in normalize(text) or "حریم شخصی" in normalize(text):
        response=auto_reply("حریم خصوصی")
        send(chat,response or S("priv_text"),main_kb(uid))
        return
    if (text.startswith("/end") and S("cmd_end") == "1") or (L_END in text and short) or text == "🚪 خروج":
        p = end_chat(uid)
        send(chat, "✅ چت پایان یافت." if p else "ℹ️ شما در چت نیستید.", main_kb(uid))
        return
    if (text.startswith("/next") and S("cmd_next") == "1") or (L_NEXT in text and short) or text == "⏭️ چت بعدی":
        end_chat(uid)
        do_search(uid)
        return
    if (text.startswith("/search") and S("cmd_search") == "1") or (L_SEARCH in text and short):
        do_search(uid)
        return
    if u["partner"] and text == "باشه":
        send(chat, "👌")
        return
    if u["partner"] and uid == OWNER_ID and not owner_is_user():
        # Owner-only moderation commands work inside the active chat without exposing prompts to the partner.
        if text == "اخطار":
            target = u["partner"]
            apply_warn(target, None)
            send(chat, f"✅ دستور اخطار برای کاربر {target} اجرا شد.", chat_kb(uid))
            return
        mute_match = re.fullmatch(r"سکوت ([1-9][0-9]{0,3})", text)
        if text.startswith("سکوت"):
            if not mute_match or not (1 <= int(mute_match.group(1)) <= 1440):
                send(chat, "قالب درست: سکوت 14 (بین کلمه و عدد فاصله باشد؛ مدت ۱ تا ۱۴۴۰ دقیقه).", chat_kb(uid))
                return
            minutes = int(mute_match.group(1))
            target = int(u["partner"])
            until = time.time() + minutes * 60
            with LOCK:
                DB.execute("CREATE TABLE IF NOT EXISTS user_mutes(uid INTEGER PRIMARY KEY, muted_until REAL NOT NULL, by_owner INTEGER NOT NULL)")
                DB.execute("INSERT INTO user_mutes(uid,muted_until,by_owner) VALUES(?,?,?) ON CONFLICT(uid) DO UPDATE SET muted_until=excluded.muted_until,by_owner=excluded.by_owner", (target, until, OWNER_ID))
                code = active_chat_code(uid)
                if code:
                    DB.execute("UPDATE chat_sessions SET active=0,ended=? WHERE code=? AND active=1", (time.time(), code))
                    DB.execute("INSERT INTO chat_events(code,user_id,event,created,details) VALUES(?,?,?,?,?)", (code, OWNER_ID, "owner_mute", time.time(), f"target={target}; minutes={minutes}"))
                DB.commit()
            set_partner(uid, None); set_partner(target, None)
            if target in WAITING:
                WAITING.remove(target)
            send(target, f"🔇 دسترسی جستجوی چت شما به مدت {minutes} دقیقه محدود شد.", main_kb(target))
            send(chat, f"✅ سکوت {minutes} دقیقه‌ای ثبت شد. چت به وضعیت رسیدگی مدیریتی منتقل شد.", main_kb(uid))
            send(OWNER_ID, f"🚩 نشست {code or 'نامشخص'} برای رسیدگی مدیریتی علامت‌گذاری شد؛ کاربر {target} تا {datetime.fromtimestamp(until, TEHRAN):%Y-%m-%d %H:%M} سکوت است.")
            return
    if u["partner"]:
        media = _media_kind(m)
        if media and S("file_" + media) != "1":
            send(chat, f"⛔ ارسال این نوع فایل ({media}) فعلاً توسط مدیریت بسته شده است.")
            return
        relay(m, u)
    else:
        response = auto_reply(text)
        send(chat, response or "برای شروع «جستجوی چت تصادفی» را بزن 👇", main_kb(uid))


def _media_kind(m):
    if m.get("photo"): return "photo"
    if m.get("video") or m.get("animation"): return "video"
    if m.get("audio") or m.get("voice"): return "audio"
    doc = m.get("document")
    if doc:
        name = (doc.get("file_name") or "").lower()
        if name.endswith(".apk"): return "apk"
        if name.endswith(".zip"): return "zip"
        return "document"
    if m.get("sticker") or m.get("video_note"): return "video"
    return None


# ───────────────────────── 8) پنل مدیریت مالک ─────────────────────────
HOME_BTN = [("🏠 منوی اصلی", "a:home")]
BCAST = {"mid": None, "running": False}


def fmt_dt(iso):
    if not iso:
        return "—"
    try:
        return jalali_str(datetime.fromisoformat(iso).astimezone(TEHRAN))
    except Exception:
        return iso


def fmt_uptime():
    s = int(time.time() - START_TIME)
    d, s = divmod(s, 86400)
    h, s = divmod(s, 3600)
    return f"{d} روز و {h} ساعت و {s // 60} دقیقه"


def set_owner_mode(mode):
    end_chat(OWNER_ID)
    ADMIN_STATE.pop(OWNER_ID, None)
    set_S("owner_mode", mode)
    if mode == "user":
        send(OWNER_ID, "👤 وارد پنل کاربر عادی شدی (حالت تست).\nهمه‌چیز دقیقاً مثل یک کاربر معمولی کار می‌کند؛ "
                       "فیلتر کلمات فقط هشدار تستی می‌دهد و اخطار واقعی ثبت نمی‌شود.\n"
                       f"برای برگشت: دکمه‌ی «{L_ADMIN}» یا /panel", main_kb(OWNER_ID))
    else:
        send(OWNER_ID, "🛠 به پنل ادمین برگشتی.", {"remove_keyboard": True})
        show(OWNER_ID, None, panel_home())


def panel_home():
    st = "🟢 روشن" if is_active() else "🔴 خاموش"
    text = f"🛠 پنل مدیریت\n📅 {jalali_str()}\nوضعیت ربات: {st}"
    kb = ikb([
        [("⭐ قابلیت‌های مهم", "a:important")],
        [("🧰 قابلیت‌های دیگر", "a:other")],
        [("🔐 پنل محرمانه", "a:secret")],
    ])
    return text, kb


def panel_important():
    return ("⭐ قابلیت‌های مهم", ikb([
        [("📊 آمار کامل", "a:stats", "primary"), ("📤 خروجی آمار (txt)", "a:export", "primary")],
        [("📢 پیام همگانی", "a:bc", "success"), ("🔎 جست‌وجوی کاربر", "a:find", "primary")],
        [("🚷 بن‌شده‌ها", "a:bl:0", "danger"), ("💬 چت‌های فعال", "a:ac:0", "success")],
        [("👋 پیام خوش‌آمد", "a:wel"), ("🔌 روشن/خاموش", "a:power", "success" if S("bot_on") == "1" else "danger")],
        HOME_BTN]))


def panel_other():
    return ("🧰 قابلیت‌های دیگر", ikb([
        [("⏰ زمان‌بندی", "a:sched"), ("🚫 کلمات ممنوعه", "a:words:0")],
        [("⚠️ اخطار و بن", "a:warn"), ("🎨 رنگ دکمه‌ها", "a:colors")],
        [("🔒 حریم خصوصی", "a:priv"), ("🔗 چت مستقیم با کاربر", "a:connect")],
        [("☁️ Cloudflare Worker", "a:cf")],
        [GAME_MODULE.admin_button()] if GAME_MODULE else [],
        [("⚙️ دکمه‌ها و دستورات", "a:dyn"), ("📎 فرمت‌های فایل", "a:files")],
        [("🛍 نرخ امتیاز/محصول", "a:shopcfg")],
        [("🔒 عضویت اجباری", "a:fj"), ("🤖 پاسخگوی خودکار", "a:auto:0")],
        [("📣 آرشیو پیام‌های همگانی", "a:bcmgr:0")],
        [("👤 ورود به پنل کاربر عادی (تست)", "a:mode:user", "success")],
        HOME_BTN]))


def _secret_password_record():
    record = S("secret_password")
    if record:
        return record
    salt = secrets.token_bytes(16)
    digest = hashlib.pbkdf2_hmac("sha256", b"12345678", salt, 180000)
    record = base64.urlsafe_b64encode(salt).decode() + "$" + base64.urlsafe_b64encode(digest).decode()
    set_S("secret_password", record)
    return record


def _check_secret_password(value):
    try:
        salt_b64, digest_b64 = _secret_password_record().split("$", 1)
        salt = base64.urlsafe_b64decode(salt_b64)
        actual = hashlib.pbkdf2_hmac("sha256", value.encode(), salt, 180000)
        return hmac.compare_digest(actual, base64.urlsafe_b64decode(digest_b64))
    except Exception:
        return False


def _secret_lock_state(uid):
    with LOCK:
        row=DB.execute("SELECT failures,locked_until FROM secret_auth WHERE user_id=?",(uid,)).fetchone()
    return (int(row[0]), float(row[1])) if row else (0,0.0)


def secret_password_prompt(uid):
    failures, locked_until = _secret_lock_state(uid)
    remain = int(locked_until-time.time())
    if remain > 0:
        send(uid, f"🔒 پنل محرمانه موقتاً قفل است؛ {max(1,remain//60)} دقیقه دیگر تلاش کن.")
        return
    warning = ("\n⚠️ نباید رمز را زیاد اشتباه بزنید! در صورت تکرار، زمان مسدودی افزایش می‌یابد."
               if failures >= 4 else "")
    ADMIN_STATE[uid] = "secret_password"
    send(uid, "🔐 رمز پنل محرمانه را بفرست." + warning + "\n(لغو: /cancel)")


def _secret_auth(uid, password):
    now_ts=time.time()
    failures, locked_until=_secret_lock_state(uid)
    if locked_until>now_ts:
        return False, f"قفل است؛ {int((locked_until-now_ts+59)//60)} دقیقه دیگر تلاش کن."
    if _check_secret_password(password):
        with LOCK:
            DB.execute("INSERT INTO secret_auth(user_id,failures,locked_until) VALUES(?,0,0) "
                       "ON CONFLICT(user_id) DO UPDATE SET failures=0,locked_until=0",(uid,))
            DB.commit()
        SECRET_AUTHENTICATED[uid]=time.time()+600
        return True, ""
    failures += 1
    seconds = 60 if failures <= 3 else 180 if failures == 4 else 1800 if failures == 5 else 3600 if failures == 6 else 43200 if failures == 7 else 64800 if failures == 8 else 104400
    with LOCK:
        DB.execute("INSERT INTO secret_auth(user_id,failures,locked_until) VALUES(?,?,?) "
                   "ON CONFLICT(user_id) DO UPDATE SET failures=excluded.failures,locked_until=excluded.locked_until",
                   (uid,failures,now_ts+seconds))
        DB.commit()
    return False, f"❌ رمز اشتباه است. تلاش {failures}؛ پنل برای {seconds//60} دقیقه قفل شد."


def secret_panel():
    with LOCK:
        active=DB.execute("SELECT COUNT(*) FROM chat_sessions WHERE active=1").fetchone()[0]
        sessions=DB.execute("SELECT COUNT(*) FROM chat_sessions").fetchone()[0]
        completed=DB.execute("SELECT COUNT(*) FROM chat_sessions WHERE active=0").fetchone()[0]
        reports=DB.execute("SELECT COUNT(*) FROM complaint_reports WHERE status='open'").fetchone()[0]
    return (f"🔐 پنل محرمانه\nچت فعال: {active} · کل نشست‌ها: {sessions} · پایان‌یافته: {completed}\n"
            f"گزارش‌های ویژه باز: {reports}\nاین پنل عمومی فقط فراداده‌ی نشست‌ها را نشان می‌دهد؛ پرونده‌های گزارش جدا هستند.",
            ikb([[("🟢 نشست‌های فعال", "a:secactive:0"), ("🗂 سابقه نشست‌ها", "a:sechistory:0")],
                 [("🔎 جستجوی کد/کاربر", "a:secsearch")],
                 [("🚨 گزارش ویژه پنل", "a:secreports:0")],
                 [("🔑 تغییر رمز", "a:secpass")], HOME_BTN]))


def secret_reports(page=0):
    per=8
    with LOCK:
        rows=DB.execute("SELECT id,code,reporter,accused,reason,created,status FROM complaint_reports "
                        "ORDER BY created DESC LIMIT ? OFFSET ?",(per,page*per)).fetchall()
    labels={"harassment":"آزار/تهدید","scam":"کلاهبرداری","content":"محتوای نامناسب","other":"سایر"}
    buttons=[[(f"#{rid} · {code} · {labels.get(reason,reason)} · {status}",
               f"a:secreport:{rid}")] for rid,code,reporter,accused,reason,created,status in rows]
    nav=[]
    if page: nav.append(("◀️ قبلی",f"a:secreports:{page-1}"))
    if len(rows)==per: nav.append(("بعدی ▶️",f"a:secreports:{page+1}"))
    buttons += [nav,HOME_BTN]
    return "🚨 گزارش ویژه پنل · متن پیام‌ها و عکس‌های ثبت‌شده برای رسیدگی ایمنی در جزئیات گزارش نمایش داده می‌شوند.",ikb(buttons)


def secret_report_detail(report_id):
    with LOCK:
        r=DB.execute("SELECT id,code,reporter,accused,reason,details,created,status FROM complaint_reports WHERE id=?",
                     (report_id,)).fetchone()
        consent=DB.execute("SELECT consent_a,consent_b,user_a,user_b FROM chat_sessions WHERE code=?",(r[1],)).fetchone() if r else None
        messages=DB.execute("SELECT user_id,content,created FROM chat_messages WHERE code=? ORDER BY created LIMIT 300",
                            (r[1],)).fetchall() if r else []
        events=DB.execute("SELECT user_id,event,created,details FROM chat_events WHERE code=? ORDER BY created LIMIT 300",
                          (r[1],)).fetchall() if r else []
    if not r: return "گزارش پیدا نشد.",ikb([[("🔙 گزارش‌ها","a:secreports:0")],HOME_BTN])
    rid,code,reporter,accused,reason,details,created,status=r
    dt=datetime.fromtimestamp(created,TEHRAN)
    jy,jm,jd=gregorian_to_jalali(dt.year,dt.month,dt.day)
    reporter_name=nickname(reporter) or str(reporter)
    gender={"female":"زن","male":"مرد","other":"نامشخص"}.get(user_gender(reporter),"نامشخص")
    accused_name=nickname(accused) or str(accused)
    accused_gender={"female":"زن","male":"مرد","other":"نامشخص"}.get(user_gender(accused),"نامشخص")
    quote=f"> {reporter_name} : {gender} : {jy:04d}/{jm:02d}/{jd:02d} - {dt:%H:%M:%S}\n{details}"
    def timestamp(ts):
        d=datetime.fromtimestamp(ts,TEHRAN)
        year,month,day=gregorian_to_jalali(d.year,d.month,d.day)
        return f"{year:04d}/{month:02d}/{day:02d} - {d:%H:%M:%S}"
    text=(f"🚨 گزارش ویژه #{rid} · نشست {code}\n"
          f"گزارش‌دهنده: {reporter_name} · {gender} · ID {reporter}\n"
          f"طرف گزارش‌شده: {accused_name} · {accused_gender} · ID {accused}\n"
          f"دلیل: {reason} · وضعیت: {status} · ثبت: {jy:04d}/{jm:02d}/{jd:02d} {dt:%H:%M:%S}\n\n"
          f"{quote}\n\n")
    # Message text is only available for sessions archived after both participants consented.
    event_labels = {
        "chat_started": "شروع گفتگو",
        "message_forwarded": "پیام ارسال شد",
        "user_report_submitted": "گزارش کاربر ثبت شد",
        "game_challenge_requested": "چالش درخواست شد",
        "game_challenge_received": "چالش دریافت شد",
        "chat_ended": "گفتگو پایان یافت",
        "archive_consent_granted": "رضایت برای آرشیو ثبت شد",
        "archive_consent_declined": "عدم رضایت برای آرشیو ثبت شد",
        "consented_archive_enabled": "آرشیو با رضایت هر دو نفر فعال شد",
    }
    unused_messages = list(messages)
    text += "رویدادهای نشست:\n"
    for uid,event,created,extra in events:
        person_gender = {"female":"زن", "male":"مرد", "other":"نامشخص"}.get(user_gender(uid), "نامشخص")
        label = event_labels.get(event, event.replace("_", " "))
        detail = extra or ""
        for source, translated in (("idea_id=", "شناسه چالش: "), ("report_id=", "شناسه گزارش: "),
                                   ("reason=other", "دلیل: سایر"), ("reason=harassment", "دلیل: آزار و اذیت"),
                                   ("reason=scam", "دلیل: کلاهبرداری"), ("reason=content", "دلیل: محتوای نامناسب"),
                                   ("media=none", "پیوست: ندارد"), ("media=text", "پیوست: متن"),
                                   ("normal chat; transcript not retained unless both participants consent", "گفتگوی عادی؛ آرشیو پیام فقط با رضایت هر دو نفر"),
                                   ("both participants consented", "هر دو نفر رضایت داده‌اند")):
            detail = detail.replace(source, translated)
        if event == "message_forwarded":
            media_labels = {"text":"متن", "photo":"عکس", "video":"ویدئو", "voice":"پیام صوتی",
                            "audio":"صوت", "document":"فایل", "sticker":"استیکر", "animation":"گیف"}
            detail = media_labels.get(detail, detail)
        text += f"{timestamp(created)} · {nickname(uid) or uid} ({person_gender}) · {label}"
        if detail:
            text += f" · {detail}"
        text += "\n"
        if event == "message_forwarded" and unused_messages:
            candidates = [(abs(msg[2]-created), i, msg) for i,msg in enumerate(unused_messages)
                          if msg[0] == uid and abs(msg[2]-created) <= 8]
            if candidates:
                _, idx, msg = min(candidates, key=lambda item: item[0])
                unused_messages.pop(idx)
                content = display_message_content(msg[1])
                text += "\n".join(f"> {line}" for line in content.splitlines()) + "\n"
    if not messages:
        text += "\nℹ️ متن پیام‌های پیشین در پایگاه داده موجود نیست؛ پیام‌های جدید پس از نصب این نسخه ثبت می‌شوند.\n"
    return text[:3900],ikb([[ ("✅ بستن گزارش",f"a:reportclose:{rid}")],
                            [("🔙 فهرست گزارش‌ها","a:secreports:0")],HOME_BTN])


def secret_history_list(page=0):
    per=8
    with LOCK:
        rows=DB.execute("SELECT code,user_a,user_b,started,active FROM chat_sessions ORDER BY started DESC LIMIT ? OFFSET ?",
                        (per,page*per)).fetchall()
    buttons=[[(f"{code} · {nickname(a) or a} ⇄ {nickname(b) or b} · {datetime.fromtimestamp(ts,TEHRAN):%m-%d %H:%M} · {'فعال' if active else 'تمام'}",
               f"a:secview:{code}")] for code,a,b,ts,active in rows]
    nav=[]
    if page: nav.append(("◀️ قبلی",f"a:sechistory:{page-1}"))
    if len(rows)==per: nav.append(("بعدی ▶️",f"a:sechistory:{page+1}"))
    buttons += [nav,[("جستجوی کد/کاربر","a:secsearch")],HOME_BTN]
    return "🗂 سابقه نشست‌ها. پیام‌های ثبت‌شده برای رسیدگی به گزارش‌های ایمنی در پنل محرمانه نمایش داده می‌شوند.",ikb(buttons)


def secret_active(page=0):
    per=8
    with LOCK:
        rows=DB.execute("SELECT code,user_a,user_b,started,consent_a,consent_b FROM chat_sessions "
                        "WHERE active=1 ORDER BY started DESC LIMIT ? OFFSET ?",(per,page*per)).fetchall()
    buttons=[]
    for code,a,b,started,ca,cb in rows:
        consent="رضایت دوطرفه" if ca and cb else "بدون آرشیو"
        name_a=f"{nickname(a) or 'بدون لقب'} · {user_gender(a) or 'نامشخص'} · ID {a}"
        name_b=f"{nickname(b) or 'بدون لقب'} · {user_gender(b) or 'نامشخص'} · ID {b}"
        buttons.append([(f"{code} · {name_a} ⇄ {name_b} · {consent}",
                         f"a:secview:{code}")])
    nav=[]
    if page: nav.append(("◀️ قبلی",f"a:secactive:{page-1}"))
    if len(rows)==per: nav.append(("بعدی ▶️",f"a:secactive:{page+1}"))
    buttons += [nav, HOME_BTN]
    return "🟢 نشست‌های فعال؛ فهرست فقط شامل مشخصات و وضعیت آرشیو است، نه متن گفتگو.",ikb(buttons)


def secret_history(code):
    with LOCK:
        session=DB.execute("SELECT code,user_a,user_b,started,ended,active,consent_a,consent_b FROM chat_sessions WHERE code=?",
                           (code,)).fetchone()
        if not session:
            session=DB.execute("SELECT code,user_a,user_b,started,ended,active,consent_a,consent_b FROM chat_sessions WHERE user_a=? OR user_b=? ORDER BY started DESC LIMIT 1",
                               (int(code),int(code))).fetchone() if code.isdigit() else None
        if not session:
            return "❌ نشست/کد پیدا نشد.",ikb([[("🔎 جستجو", "a:secsearch")],HOME_BTN])
        events=DB.execute("SELECT user_id,event,created,details FROM chat_events WHERE code=? ORDER BY created LIMIT 100",
                          (session[0],)).fetchall()
        transcript=DB.execute("SELECT user_id,content,created FROM chat_messages WHERE code=? ORDER BY created LIMIT 300",
                              (session[0],)).fetchall()
    code,a,b,started,ended,active,ca,cb=session
    def time_label(ts):
        dt=datetime.fromtimestamp(ts,TEHRAN)
        jy,jm,jd=gregorian_to_jalali(dt.year,dt.month,dt.day)
        return f"{jy:04d}/{jm:02d}/{jd:02d} - {dt:%H:%M:%S}"
    status="فعال" if active else f"پایان‌یافته · {time_label(ended or started)}"
    count_a,count_b=0,0
    for uid,event,created,details in events:
        if event=="message_forwarded":
            if uid==a: count_a+=1
            elif uid==b: count_b+=1
    body=[f"🧾 کد گفتگو: {code}",
          f"{nickname(a) or 'بدون لقب'} : {user_gender(a) or 'نامشخص'} : ID {a}",
          f"{nickname(b) or 'بدون لقب'} : {user_gender(b) or 'نامشخص'} : ID {b}",
          f"شروع: {time_label(started)} · وضعیت: {status}",
          f"تعداد پیام‌های عبوری: {count_a+count_b} (طرف اول {count_a}، طرف دوم {count_b})",
          "وضعیت آرشیو رضایت‌محور: هر دو رضایت داده‌اند" if ca and cb else "وضعیت آرشیو رضایت‌محور: غیرفعال"]
    body += ["", "رویدادهای نشست:"]
    message_pool = list(transcript)
    event_labels = {
        "chat_started": "شروع گفتگو", "message_forwarded": "پیام ارسال شد",
        "user_report_submitted": "گزارش کاربر ثبت شد", "game_challenge_requested": "درخواست چالش",
        "game_challenge_received": "دریافت چالش", "chat_ended": "پایان گفتگو",
        "archive_consent_granted": "ثبت رضایت برای آرشیو",
        "archive_consent_declined": "رد رضایت برای آرشیو",
        "consented_archive_enabled": "فعال‌شدن آرشیو با رضایت دوطرفه",
    }
    for uid,event,ts,details in events:
        event_label = event_labels.get(event, event.replace("_", " "))
        detail = details or ""
        for source, translated in (("normal chat; transcript not retained unless both participants consent", "گفتگوی عادی؛ پیام‌ها برای رسیدگی به گزارش‌های ایمنی ممکن است ذخیره شوند"),
                                   ("both participants consented", "هر دو نفر رضایت دادند")):
            detail = detail.replace(source, translated)
        body.append(f"{time_label(ts)} · {nickname(uid) or uid} · {event_label} {detail}".strip())
        if event == "message_forwarded" and message_pool:
            candidates = [(abs(msg[2]-ts), i, msg) for i,msg in enumerate(message_pool)
                          if msg[0] == uid and abs(msg[2]-ts) <= 8]
            if candidates:
                _, idx, msg = min(candidates, key=lambda item: item[0])
                message_pool.pop(idx)
                body.extend(f"> {line}" for line in display_message_content(msg[1]).splitlines())
    if not transcript:
        body += ["", "ℹ️ متن پیام‌های قدیمی که ذخیره نشده‌اند قابل بازیابی نیست. پیام‌های جدید پس از نصب این نسخه ثبت می‌شوند."]
    buttons=[[ ("🔙 نشست‌های فعال", "a:secactive:0"), ("سابقه همه نشست‌ها","a:sechistory:0"),
               ("جستجو", "a:secsearch")],HOME_BTN]
    return ("\n".join(body)[:3900]+"\n\n🔐 پیام‌های ثبت‌شده برای رسیدگی ایمنی در پنل محرمانه قابل مشاهده‌اند."),ikb(buttons)



def secret_user_list(page=0):
    """List registered users inside the authenticated secret panel; numeric-ID lookup remains available."""
    per = 8
    with LOCK:
        rows = DB.execute(
            "SELECT uid,nickname,username,last_seen FROM users ORDER BY last_seen DESC LIMIT ? OFFSET ?",
            (per, page * per),
        ).fetchall()
        total = DB.execute("SELECT COUNT(*) FROM users").fetchone()[0]
    buttons = []
    for uid, nick, username, last_seen in rows:
        label = (nick or username or str(uid)).replace("\n", " ")[:28]
        extra = f" @{username}" if username else ""
        buttons.append([(f"{label}{extra} · ID {uid}", f"a:secuserpick:{uid}")])
    nav = []
    if page > 0:
        nav.append(("◀️ قبلی", f"a:secusers:{page-1}"))
    if (page + 1) * per < total:
        nav.append(("بعدی ▶️", f"a:secusers:{page+1}"))
    if nav:
        buttons.append(nav)
    buttons += [[("🔎 جستجو با آیدی/نام/کد گفتگو", "a:secsearch")], HOME_BTN]
    return f"👥 فهرست کاربران ({total} نفر)\nبرای دیدن سابقهٔ کاربر، روی نام او بزن؛ یا آیدی عددی/نام کاربری/لقب/کد گفتگو را جستجو کن.", ikb(buttons)

def secret_user_sessions(uid,page=0):
    per=8
    with LOCK:
        rows=DB.execute("SELECT code,user_a,user_b,started,active,consent_a,consent_b FROM chat_sessions "
                        "WHERE user_a=? OR user_b=? ORDER BY started DESC LIMIT ? OFFSET ?",
                        (uid,uid,per,page*per)).fetchall()
    if not rows:
        return f"برای کاربر {uid} سابقه‌ی گفتگویی پیدا نشد.",ikb([[("جستجو","a:secsearch")],HOME_BTN])
    buttons=[]
    for code,a,b,started,active,ca,cb in rows:
        other=b if uid==a else a
        buttons.append([(f"{code} · {nickname(other) or 'بدون لقب'} · {user_gender(other) or 'نامشخص'} · ID {other} · "
                         f"{datetime.fromtimestamp(started,TEHRAN):%m-%d %H:%M} · "
                         f"{'فعال' if active else 'تمام'} · {'رضایت دوطرفه' if ca and cb else 'بدون متن'}",
                         f"a:secview:{code}")])
    nav=[]
    if page: nav.append(("◀️ قبلی",f"a:secuser:{uid}:{page-1}"))
    if len(rows)==per: nav.append(("بعدی ▶️",f"a:secuser:{uid}:{page+1}"))
    buttons += [nav,[("جستجوی دیگر","a:secsearch")],HOME_BTN]
    return f"کاربر {nickname(uid) or uid} · نشست‌های ثبت‌شده:",ikb(buttons)


def screen_secret_password_change(chat):
    ADMIN_STATE[chat]="secret_new_password"
    send(chat,"رمز جدید را بفرست (حداقل ۸ نویسه). لغو: /cancel")


def secret_set_password(chat,new_password):
    if len(new_password)<8 or len(new_password)>128:
        send(chat,"رمز باید بین ۸ تا ۱۲۸ نویسه باشد."); return
    salt=secrets.token_bytes(16)
    digest=hashlib.pbkdf2_hmac("sha256",new_password.encode(),salt,180000)
    set_S("secret_password",base64.urlsafe_b64encode(salt).decode()+"$"+base64.urlsafe_b64encode(digest).decode())
    send(chat,"✅ رمز پنل محرمانه تغییر کرد.",ikb([HOME_BTN]))


# ── ۱) آمار کامل ──
def compute_stats():
    n = now()
    day0 = n.replace(hour=0, minute=0, second=0, microsecond=0).isoformat()
    d1, d7 = (n - timedelta(days=1)).isoformat(), (n - timedelta(days=7)).isoformat()
    with LOCK:
        q = lambda sql, *a: DB.execute(sql, a).fetchone()[0]
        st = {
            "total": q("SELECT COUNT(*) FROM users"),
            "new_today": q("SELECT COUNT(*) FROM users WHERE joined>=?", day0),
            "new_7d": q("SELECT COUNT(*) FROM users WHERE joined>=?", d7),
            "act_24h": q("SELECT COUNT(*) FROM users WHERE last_seen>=?", d1),
            "act_7d": q("SELECT COUNT(*) FROM users WHERE last_seen>=?", d7),
            "banned": q("SELECT COUNT(*) FROM users WHERE banned=1"),
            "warned": q("SELECT COUNT(*) FROM users WHERE warns>0 AND banned=0"),
            "words": q("SELECT COUNT(*) FROM words"),
            "requests": q("SELECT COALESCE((SELECT v FROM counters WHERE k='requests'),0)"),
            "requests_today": q("SELECT COALESCE((SELECT count FROM daily_requests WHERE day=?),0)",
                                n.strftime("%Y-%m-%d")),
            "chats_today": q("SELECT COUNT(*) FROM chat_sessions WHERE started>=?",
                             n.replace(hour=0,minute=0,second=0,microsecond=0).timestamp()),
        }
        st["c"] = dict(DB.execute("SELECT k,v FROM counters").fetchall())
    st["pairs"] = len(active_pairs())
    st["queue"] = len(WAITING)
    return st


def stats_text(st):
    c = st["c"].get
    return (f"📊 آمار کامل ربات\n📅 {jalali_str()}\n"
            f"وضعیت: {'🟢 روشن' if is_active() else '🔴 خاموش'} | مدت روشن بودن: {fmt_uptime()}\n\n"
            f"👥 کل کاربران: {st['total']}\n🆕 عضو جدید امروز: {st['new_today']} | ۷ روز اخیر: {st['new_7d']}\n"
            f"🔥 فعال ۲۴ ساعت: {st['act_24h']} | فعال ۷ روز: {st['act_7d']}\n\n"
            f"💬 چت‌های فعال: {st['pairs']} (نفر در چت: {st['pairs'] * 2})\n⏳ در صف انتظار: {st['queue']}\n"
            f"🔍 تعداد جست‌وجو: {c('searches', 0)} | اتصال موفق: {c('matches', 0)}\n"
            f"✉️ پیام‌های ردوبدل‌شده: {c('msgs', 0)}\n\n"
            f"🚫 بن‌شده: {st['banned']} | ⚠️ دارای اخطار: {st['warned']}\n"
            f"🧹 پیام فیلترشده: {c('blocked_msgs', 0)} | بن خودکار: {c('auto_bans', 0)}\n"
            f"📝 کلمات ممنوعه: {st['words']}\n📢 پیام همگانی ارسال‌شده: {c('broadcasts', 0)}\n"
            f"📥 کل درخواست‌های ورودی: {st['requests']} · امروز: {st['requests_today']}\n"
            f"📅 چت‌های شروع‌شده امروز: {st['chats_today']}")


def command_help_text(uid):
    owner = (uid == OWNER_ID and not owner_is_user())
    entries = [
        ("cmd_start", "/start", "شروع و نمایش منوی اصلی"),
        ("cmd_search", "/search", "جستجوی چت ناشناس"),
        ("cmd_next", "/next", "رفتن به هم‌صحبت بعدی"),
        ("cmd_end", "/end", "پایان چت فعلی"),
        ("cmd_privacy", "/privacy", "نمایش قوانین حریم خصوصی"),
        ("cmd_nickname", "/nickname", "مشاهده یا تغییر لقب؛ نمونه: /nickname علی"),
        ("cmd_game", "/game", "بخش چالش ناشناس"),
        ("cmd_leaderboard", "/leaderboard", "برترین‌های هفته"),
        ("cmd_shop", "/shop", "فروشگاه امتیاز"),
        ("cmd_help", "/help", "نمایش راهنمای دستورات"),
    ]
    lines = ["📋 دستورات کاربر:"]
    for key, command, description in entries:
        if S(key) == "1" and (key not in ("cmd_game", "cmd_leaderboard", "cmd_shop") or GAME_MODULE):
            lines.append(f"{command} — {description}")
    lines.append("\nبرای استفاده از دکمه‌ها هم می‌توانی از منوی پایین ربات کمک بگیری.")
    if owner:
        lines += ["", "🛠 دستورات مالک:", "/panel — باز کردن پنل مدیریت", "/stats — آمار ربات",
                  "/user — رفتن به حالت کاربر", "/connect شناسه — اتصال مستقیم به کاربر",
                  "/end — پایان چت مستقیم مالک", "حذف — روی پیام ریپلای کن و این کلمه را بفرست تا حذف شود."]
    return "\n".join(lines)


def auto_reply_catalog_text():
    """Return every configured autoresponder keyword and its actual response."""
    with LOCK:
        rows = DB.execute(
            "SELECT keyword,response,enabled FROM auto_replies ORDER BY keyword COLLATE NOCASE"
        ).fetchall()
    if not rows:
        return ["🤖 هنوز هیچ کلیدواژه‌ای برای پاسخگوی خودکار ثبت نشده است."]
    chunks = []
    current = "🤖 فهرست کامل کلیدواژه‌ها و پاسخ‌های پاسخگوی خودکار\n"
    for keyword, response, enabled in rows:
        status = "🟢 فعال" if enabled else "⚪ غیرفعال"
        item = f"\n🔑 کلیدواژه: {keyword} ({status})\n💬 پاسخ: {response or '—'}\n"
        if len(current) + len(item) > 3500 and current.strip():
            chunks.append(current.rstrip())
            current = "🤖 ادامهٔ فهرست پاسخگوی خودکار\n"
        current += item
    if current.strip():
        chunks.append(current.rstrip())
    return chunks


def send_auto_reply_catalog(chat, uid):
    """Send the full autoresponder keyword/response list in Telegram-safe chunks."""
    for part in auto_reply_catalog_text():
        send(chat, part, main_kb(uid))


def refresh_bot_commands():
    labels = {"start":"شروع","search":"جستجوی چت","next":"چت بعدی","end":"پایان چت",
              "privacy":"حریم خصوصی","game":"چالش ناشناس","leaderboard":"برترین‌های هفته",
              "shop":"فروشگاه امتیاز","nickname":"ثبت یا تغییر لقب","help":"راهنما","panel":"پنل مالک"}
    commands = [{"command": cmd, "description": desc} for cmd,desc in labels.items()
                if S("cmd_"+cmd) == "1"]
    return api("setMyCommands", {"commands": commands})


def show_update_notice_once(uid):
    notice_key = str(S("version_notice") or "v2.9")
    with LOCK:
        exists=DB.execute("SELECT 1 FROM user_notices WHERE uid=? AND notice_key=?",(uid,notice_key)).fetchone()
        if exists: return False
        DB.execute("INSERT OR IGNORE INTO user_notices(uid,notice_key,shown_at) VALUES(?,?,?)",
                   (uid,notice_key,time.time()))
        DB.commit()
    send(uid,f"🆕 نسخه {notice_key}\n{S('version_description')}")
    return True


def screen_stats():
    return stats_text(compute_stats()), ikb([[("🔄 بروزرسانی", "a:stats", "primary"),
                                              ("📤 خروجی txt", "a:export", "success")], HOME_BTN])


# ── ۷) خروجی آمار در فایل متنی ──
def build_report():
    st = compute_stats()
    with LOCK:
        banned = DB.execute("SELECT uid,warns,joined FROM users WHERE banned=1 ORDER BY uid").fetchall()
        warned = DB.execute("SELECT uid,warns FROM users WHERE warns>0 AND banned=0 ORDER BY warns DESC").fetchall()
    lines = ["گزارش آمار ربات چت ناشناس", "=" * 40, stats_text(st), "",
             "تنظیمات", "-" * 40,
             f"زمان‌بندی: {'فعال' if S('sched_on') == '1' else 'غیرفعال'} ({S('sched_start')} تا {S('sched_end')}، حالت {S('sched_mode')})",
             f"حداکثر اخطار: {S('max_warns')}", f"Worker: {S('worker_url') or '-'}",
             f"رنگ دکمه‌ها: جستجو={STYLES[S('color_chat')]}، بعدی={STYLES[S('color_next')]}، "
             f"پایان={STYLES[S('color_end')]}، حریم={STYLES[S('color_priv')]}", "",
             f"کاربران بن‌شده ({len(banned)})", "-" * 40]
    lines += [f"{u}\tاخطار {w}\tعضویت {fmt_dt(j)}" for u, w, j in banned] or ["-"]
    lines += ["", f"کاربران دارای اخطار ({len(warned)})", "-" * 40]
    lines += [f"{u}\tاخطار {w}" for u, w in warned] or ["-"]
    lines += ["", f"چت‌های فعال ({st['pairs']})", "-" * 40]
    lines += [f"{a} <-> {b}" for a, b in active_pairs()] or ["-"]
    lines += ["", f"صف انتظار ({len(WAITING)})", "-" * 40, " ".join(map(str, WAITING)) or "-"]
    return "\n".join(lines)


def send_report(chat):
    send_document(chat, f"anonchat_stats_{now():%Y%m%d_%H%M}.txt", build_report(), f"📤 گزارش آمار — {jalali_str()}")


# ── ۲) پیام همگانی ──
def broadcast_worker(chat, mid):
    with LOCK:
        uids = [r[0] for r in DB.execute("SELECT uid FROM users WHERE banned=0 AND uid!=?", (OWNER_ID,))]
        cur = DB.execute("INSERT INTO broadcasts(source_chat,source_mid,created) VALUES(?,?,?)",
                         (chat, mid, time.time()))
        broadcast_id = cur.lastrowid
        DB.commit()
    ok = fail = 0
    prog = send(chat, f"📢 در حال ارسال برای {len(uids)} کاربر...")
    pmid = (prog.get("result") or {}).get("message_id")
    for i, u in enumerate(uids, 1):
        for _ in range(3):
            r = api("copyMessage", {"chat_id": u, "from_chat_id": chat, "message_id": mid})
            if r.get("ok"):
                ok += 1
                copied_mid = (r.get("result") or {}).get("message_id")
                if copied_mid:
                    with LOCK:
                        DB.execute("INSERT OR IGNORE INTO broadcast_deliveries(broadcast_id,user_id,message_id) VALUES(?,?,?)",
                                   (broadcast_id, u, copied_mid))
                        DB.commit()
                break
            ra = (r.get("parameters") or {}).get("retry_after")
            if ra:
                time.sleep(int(ra) + 1)
                continue
            # Other failures are ambiguous for copyMessage. Retrying can
            # duplicate a message that Telegram already accepted.
            fail += 1
            break
        time.sleep(0.04)                      # حدود ۲۵ پیام در ثانیه (محدودیت تلگرام)
        if pmid and i % 50 == 0:
            edit(chat, pmid, f"📢 در حال ارسال... {i}/{len(uids)}")
    BCAST["running"] = False
    bump("broadcasts")
    with LOCK:
        DB.execute("UPDATE broadcasts SET success=?,failed=? WHERE id=?", (ok, fail, broadcast_id))
        DB.commit()
    send(chat, f"✅ پیام همگانی تمام شد.\nموفق: {ok}\nناموفق (ربات را بلاک کرده‌اند): {fail}",
         ikb([[("مدیریت پیام‌های همگانی", "a:bcmgr:0")], HOME_BTN]))


# ── ۳) جست‌وجوی کاربر ──
def screen_user(t, note=""):
    with LOCK:
        r = DB.execute("SELECT warns,banned,joined,last_seen FROM users WHERE uid=?", (t,)).fetchone()
    if not r:
        return (f"{note}\n❌ کاربری با شناسه‌ی {t} در ربات ثبت نشده (هنوز ربات را استارت نکرده).".strip(),
                ikb([[("🔎 جست‌وجوی دوباره", "a:find", "primary")], HOME_BTN]))
    warns, banned, joined, seen = r
    info = api("getChat", {"chat_id": t}).get("result") or {}
    name = " ".join(x for x in (info.get("first_name"), info.get("last_name")) if x) or "—"
    uname = "@" + info["username"] if info.get("username") else "—"
    p = get_user(t)["partner"]
    where = "💬 در چت" + (" (با مالک)" if p == OWNER_ID else "") if p else ("⏳ در صف" if t in WAITING else "💤 آزاد")
    txt = (f"{note}\n👤 اطلاعات کاربر {t}\nنام: {name}\nیوزرنیم: {uname}\n"
           f"وضعیت: {'🚫 بن‌شده' if banned else '✅ فعال'} | {where}\n"
           f"⚠️ اخطار: {warns} از {S('max_warns')}\n🗓 عضویت: {fmt_dt(joined)}\n🕒 آخرین فعالیت: {fmt_dt(seen)}").strip()
    rows = [[("⚠️ اخطار", f"a:u:warn:{t}"), ("♻️ ریست اخطار", f"a:u:reset:{t}", "primary")],
            [("✅ آنبن", f"a:u:unban:{t}", "success") if banned else ("🚫 بن", f"a:u:ban:{t}", "danger"),
             ("🔗 چت مستقیم", f"a:u:conn:{t}", "primary")]]
    if p:
        rows.append([("⛔ قطع چت فعلی", f"a:u:end:{t}", "danger")])
    rows += [[("🔄 بروزرسانی", f"a:u:view:{t}"), ("🔎 کاربر دیگر", "a:find")], HOME_BTN]
    return txt, ikb(rows)


def user_action(key, t):
    """اقدام مدیریتی روی یک کاربر؛ متن نتیجه را برمی‌گرداند."""
    if get_user(t, create=False) is None:
        return f"❌ کاربری با شناسه‌ی {t} در ربات ثبت نشده."
    if t == OWNER_ID:
        return "❌ روی مالک قابل اعمال نیست."
    if key == "warn":
        apply_warn(t, None)
        return "✅ اخطار ثبت شد."
    if key == "reset":
        set_field(t, "warns", 0)
        return "✅ اخطارها ریست شد."
    if key == "ban":
        set_field(t, "banned", 1)
        end_chat(t)
        bump("manual_bans")
        send(t, "🚫 دسترسی شما توسط مدیریت مسدود شد.", {"remove_keyboard": True})
        return "✅ بن شد."
    if key == "unban":
        set_field(t, "banned", 0)
        set_field(t, "warns", 0)
        send(t, "✅ دسترسی شما بازگردانده شد. /start")
        return "✅ آنبن شد."
    if key == "end":
        p = end_chat(t, notify=False)
        if not p:
            return "ℹ️ این کاربر در چت نیست."
        for x in (t, p):
            if x != OWNER_ID or owner_is_user():
                send(x, "⛔ این چت توسط مدیریت پایان یافت.", main_kb(x))
        return "✅ چت قطع شد."
    if key == "conn":
        return {"ok": "🔗 وصل شدید. پیام‌ها مستقیم به کاربر می‌رسد (او شما را یک غریبه‌ی عادی می‌بیند). پایان: /end",
                "self": "❌ نمی‌توانید به خودتان وصل شوید.",
                "unknown": "❌ این کاربر هرگز ربات را استارت نکرده است."}[owner_connect(t)]
    return ""


# ── ۴) مدیریت بن‌شده‌ها ──
def screen_banned(page):
    per = 8
    with LOCK:
        total = DB.execute("SELECT COUNT(*) FROM users WHERE banned=1").fetchone()[0]
        rows = DB.execute("SELECT uid,warns FROM users WHERE banned=1 ORDER BY uid LIMIT ? OFFSET ?",
                          (per, page * per)).fetchall()
    pages = max(1, (total + per - 1) // per)
    page = min(page, pages - 1)
    t = f"🚷 کاربران بن‌شده ({total}) — صفحه {page + 1}/{pages}\nبرای آنبن روی هر کاربر بزنید، برای جزئیات روی 👤."
    kb = [[(f"✅ آنبن {u} (اخطار {w})", f"a:ub:{u}:{page}", "success"), ("👤", f"a:u:view:{u}")] for u, w in rows]
    nav = []
    if page > 0:
        nav.append(("◀️ قبلی", f"a:bl:{page - 1}"))
    if page + 1 < pages:
        nav.append(("بعدی ▶️", f"a:bl:{page + 1}"))
    kb += [nav, [("➕ بن با شناسه", "a:warn:ban", "danger"), ("✅ آنبن با شناسه", "a:warn:unban", "success")]]
    if total:
        kb.append([("♻️ آنبن همه", "a:uball", "danger")])
    return t, ikb(kb + [HOME_BTN])


# ── ۵) چت‌های فعال ──
def active_pairs():
    with LOCK:
        rows = DB.execute("SELECT uid,partner FROM users WHERE partner IS NOT NULL").fetchall()
    seen, pairs = set(), []
    for uid, enc in rows:
        try:
            p = int(unseal(enc))
        except Exception:
            continue
        key = tuple(sorted((uid, p)))
        if key not in seen:
            seen.add(key)
            pairs.append(key)
    return pairs


def screen_active(page):
    per = 8
    pairs = active_pairs()
    pages = max(1, (len(pairs) + per - 1) // per)
    page = min(page, pages - 1)
    chunk = pairs[page * per:(page + 1) * per]
    lab = lambda x: "👑مالک" if x == OWNER_ID else str(x)
    body = "\n".join(f"{page * per + i}. {lab(a)} ⇄ {lab(b)}" for i, (a, b) in enumerate(chunk, 1)) or "— چت فعالی نیست —"
    q = " ، ".join(map(str, WAITING[:20])) or "—"
    t = f"💬 چت‌های فعال ({len(pairs)}) — صفحه {page + 1}/{pages}\n\n{body}\n\n⏳ صف انتظار ({len(WAITING)}): {q}"
    kb = [[(f"⛔ قطع چت {page * per + i}", f"a:ace:{a}:{page}", "danger"), ("👤", f"a:u:view:{a}")]
          for i, (a, b) in enumerate(chunk, 1)]
    nav = []
    if page > 0:
        nav.append(("◀️ قبلی", f"a:ac:{page - 1}"))
    if page + 1 < pages:
        nav.append(("بعدی ▶️", f"a:ac:{page + 1}"))
    kb += [nav, [("🔄 بروزرسانی", f"a:ac:{page}", "primary")]]
    if pairs:
        kb.append([("⛔ قطع همه‌ی چت‌ها", "a:acall", "danger")])
    return t, ikb(kb + [HOME_BTN])


# ── ۶) پیام خوش‌آمدگویی ──
def screen_welcome():
    t = f"👋 پیام خوش‌آمدگویی فعلی:\n\n{S('welcome_text')}\n\n(می‌توانید از {{name}} برای نام کاربر استفاده کنید)"
    return t, ikb([[("✏️ تغییر متن", "a:wel:set", "primary"), ("👁 پیش‌نمایش", "a:wel:pre")],
                   [("♻️ بازگشت به پیش‌فرض", "a:wel:def", "danger")], HOME_BTN])


def confirm_kb(yes_data, back_data):
    return ikb([[("✅ بله، انجام بده", yes_data, "danger"), ("↩️ نه، برگرد", back_data, "primary")]])


# ── سایر صفحه‌ها ──
def screen_power():
    on = S("bot_on") == "1"
    t = (f"🔌 روشن/خاموش دستی\nوضعیت دستی: {'🟢 روشن' if on else '🔴 خاموش'}\n"
         f"وضعیت نهایی (با زمان‌بندی): {'🟢 روشن' if is_active() else '🔴 خاموش'}")
    return t, ikb([[("خاموش کن", "a:power:t", "danger") if on else ("روشن کن", "a:power:t", "success")], HOME_BTN])


def screen_sched():
    on = S("sched_on") == "1"
    mode = "فعال" if S("sched_mode") == "active" else "غیرفعال"
    t = (f"⏰ زمان‌بندی (وقت تهران)\nزمان‌بندی: {'🟢 فعال' if on else '⚪ غیرفعال'}\n"
         f"در بازه‌ی {S('sched_start')} تا {S('sched_end')} ربات «{mode}» است.\n📅 {jalali_str()}")
    return t, ikb([
        [("🔁 غیرفعال کردن زمان‌بندی", "a:sched:t", "danger") if on else ("🔁 فعال کردن زمان‌بندی", "a:sched:t", "success")],
        [("🔄 تغییر نوع بازه (فعال/غیرفعال)", "a:sched:m", "primary")],
        [("✏️ ساعت شروع", "a:sched:s"), ("✏️ ساعت پایان", "a:sched:e")], HOME_BTN])


def screen_words(page):
    per = 20
    with LOCK:
        total = DB.execute("SELECT COUNT(*) FROM words").fetchone()[0]
        rows = DB.execute("SELECT id,word FROM words ORDER BY id LIMIT ? OFFSET ?", (per, page * per)).fetchall()
    pages = max(1, (total + per - 1) // per)
    body = "\n".join(f"{i}. {w}" for i, w in rows) or "—"
    t = f"🚫 کلمات ممنوعه ({total}) — صفحه {page + 1}/{pages}\n\n{body}"
    nav = []
    if page > 0:
        nav.append(("◀️ قبلی", f"a:words:{page - 1}"))
    if page + 1 < pages:
        nav.append(("بعدی ▶️", f"a:words:{page + 1}"))
    return t, ikb([nav, [("➕ افزودن", "a:w:add", "success"), ("🗑 حذف با شماره", "a:w:del", "danger")],
                   [("📤 خروجی txt", "a:w:exp", "primary")], HOME_BTN])


def screen_warn():
    t = f"⚠️ اخطار و بن\nحداکثر اخطار مجاز: {S('max_warns')}"
    return t, ikb([[("✏️ تعداد حداکثر اخطار", "a:warn:max", "primary")],
                   [("⚠️ اخطار دستی", "a:warn:warn"), ("♻️ ریست اخطار", "a:warn:reset")],
                   [("🚫 بن", "a:warn:ban", "danger"), ("✅ آنبن", "a:warn:unban", "success")],
                   [("📋 مدیریت بن‌شده‌ها", "a:bl:0")], HOME_BTN])


COLOR_NAMES = {"chat": L_SEARCH, "next": L_NEXT, "end": L_END, "priv": L_PRIV}


def screen_colors():
    rows = [[(f"{ICONS[k]} {v} ← {STYLES[S('color_' + k)]}", f"a:col:{k}", S("color_" + k))]
            for k, v in COLOR_NAMES.items()]
    t = ("🎨 رنگ دکمه‌های کاربران\nهر دکمه همین حالا با رنگ واقعی خودش نمایش داده شده؛ با زدن روی آن رنگ عوض می‌شود "
         "(سبز ← قرمز ← آبی ← بی‌رنگ).\nℹ️ رنگ دکمه‌ها از نسخه‌های جدید اپ تلگرام (بهمن ۱۴۰۴ به بعد) نمایش داده می‌شود.\n"
         "برای دیدن نتیجه در کیبورد اصلی، وارد «پنل کاربر عادی» شوید.")
    return t, ikb(rows + [[("👤 تست در پنل کاربر", "a:mode:user", "success")], HOME_BTN])


def screen_priv():
    shown = S("priv_show") == "1"
    privacy_text=S("priv_text").removeprefix("حریم خصوصی : v2.9\n")
    t = f"حریم خصوصی : v2.9\n🔒 تنظیمات\nنمایش کلیدواژه پاسخ خودکار: 🟢 فعال\n\n{privacy_text}"
    return t, ikb([[("✏️ تغییر متن", "a:priv:text", "primary")],
                   [(f"🎨 رنگ دکمه: {STYLES[S('color_priv')]}", "a:col:priv", S("color_priv"))],
                   [("👁 مخفی کردن دکمه", "a:priv:t", "danger") if shown else ("👁 نمایش دکمه", "a:priv:t", "success")],
                   HOME_BTN])


def screen_cf():
    u = S("worker_url") or "— تنظیم نشده (اتصال مستقیم به تلگرام) —"
    mode = "☁️ Cloudflare فعال" if S("worker_enabled") == "1" else "🔌 اتصال مستقیم فعال"
    t = (f"☁️ Cloudflare Worker\nآدرس فعلی: {u}\nوضعیت: {mode}\n\n"
         "کاربرد: اگر api.telegram.org روی اینترنت شما باز نمی‌شود، Worker مثل یک واسطه‌ی امن درخواست‌های ربات را "
         "به تلگرام می‌رساند.\n"
         "۱) «دریافت worker.js» را بزنید (کد کامل و آماده با شناسه‌ی همین ربات ساخته می‌شود)\n"
         "۲) dash.cloudflare.com ← Workers & Pages ← Create ← Hello World ← Deploy ← Edit code\n"
         "۳) کل کد را جایگزین کنید و Deploy بزنید\n۴) آدرس ‎*.workers.dev را اینجا ثبت کنید.\n"
         "🔎 تست سریع بدون Termux: آدرس Worker را در مرورگر باز کنید؛ /health باید پاسخ سبز بدهد.\n"
         "تست کامل /health و getMe و getUpdates کوتاه از داخل ربات انجام می‌شود؛ توکن در لینک عمومی قرار نمی‌گیرد.")
    rows = [[("📄 دریافت worker.js", "a:cf:file", "success")],
            [("✏️ ثبت آدرس Worker", "a:cf:set", "primary"), ("🩺 بررسی سلامت", "a:cf:chk")],
            [("☁️ فعال‌سازی Cloudflare", "a:cf:on", "success"),
             ("🔌 اتصال مستقیم", "a:cf:off", "danger")]]
    if S("worker_url"):
        rows.append([("🗑 حذف آدرس (اتصال مستقیم)", "a:cf:del", "danger")])
    return t, ikb(rows + [HOME_BTN])


def worker_probe(url):
    """Light recovery probe, deliberately not competing with active long-poll."""
    url = url.rstrip("/")
    try:
        with urllib.request.urlopen(urllib.request.Request(url + "/health", headers=UA), timeout=8) as r:
            health = json.loads(r.read().decode())
            if r.status != 200 or not health.get("ok"):
                return False, f"/health پاسخ سالم نداد: {health}"
        me = _post(f"{url}/bot{BOT_TOKEN}/getMe", b"{}",
                   {"Content-Type": "application/json"}, 10)
        return bool(me.get("ok")), me.get("description", "getMe ناموفق بود")
    except Exception as e:
        return False, str(e)


def health_check(url):
    """Full active test: health, getMe, and one serialized short getUpdates."""
    global POLL_OFFSET
    url = url.rstrip("/")
    started = time.monotonic()
    try:
        req = urllib.request.Request(url + "/health", headers=UA)
        with urllib.request.urlopen(req, timeout=10) as r:
            status, raw = r.status, r.read().decode()
        try:
            health = json.loads(raw)
        except json.JSONDecodeError:
            return False, f"پاسخ /health JSON نیست (HTTP {status}); آدرس Worker یا deployment را بررسی کنید."
        if status != 200 or not health.get("ok"):
            return False, f"/health ناموفق است (HTTP {status}): {health.get('description') or health}"
        t0 = time.monotonic()
        me = _post(f"{url}/bot{BOT_TOKEN}/getMe", b"{}",
                   {"Content-Type": "application/json"}, 12)
        me_ms = int((time.monotonic() - t0) * 1000)
        if not me.get("ok"):
            code, desc = me.get("error_code"), me.get("description", "پاسخ نامشخص")
            if "1102" in str(desc) or "CPU time" in str(desc).lower():
                return False, "Cloudflare خطای 1102/CPU Limit داده است؛ زمان اجرای Worker یا تنظیمات پلن را بررسی کنید."
            if me.get("_http_status") == 429:
                return False, "Worker یا Cloudflare درخواست‌ها را rate-limit کرده است (429)."
            if code == 401:
                return False, "Worker پاسخ می‌دهد ولی توکن ربات نامعتبر است (401)."
            if code == 403:
                return False, "403: شناسه‌ی ربات در Worker با توکن فعلی نمی‌خواند یا درخواست رد شده است."
            if code == 404:
                return False, "404: آدرس ثبت‌شده باید آدرس پایه‌ی Worker باشد، نه /health یا مسیر اضافی."
            if code in (502, 503, 504) or me.get("_net"):
                return False, f"Worker reachable است اما upstream تلگرام خطا داد ({code or 'timeout'}): {desc}"
            return False, f"getMe ناموفق بود ({code or 'خطا'}): {desc}"

        poll_params = {"timeout": 1, "allowed_updates": ["message", "callback_query"]}
        if POLL_OFFSET is not None:
            poll_params["offset"] = POLL_OFFSET
        updates = []
        with POLL_LOCK:
            t0 = time.monotonic()
            poll = _post(f"{url}/bot{BOT_TOKEN}/getUpdates",
                         json.dumps(poll_params).encode(),
                         {"Content-Type": "application/json"}, 8)
            poll_ms = int((time.monotonic() - t0) * 1000)
            if poll.get("ok"):
                updates = poll.get("result") or []
                if updates:
                    POLL_OFFSET = max(u["update_id"] for u in updates) + 1
        # Do not drop updates fetched by the health probe.
        for update in updates:
            handle_update(update)
        if not poll.get("ok"):
            reason = poll.get("description", "خطای نامشخص")
            if poll.get("error_code") == 409:
                reason = "409 Conflict: poll دیگری با همین توکن فعال است."
            return False, (f"✅ /health موفق\n✅ getMe موفق ({me_ms}ms)\n"
                           f"❌ getUpdates ناموفق: {reason}")
        elapsed = int((time.monotonic() - started) * 1000)
        return True, (f"✅ /health موفق\n✅ getMe موفق: @{me['result'].get('username', '?')} ({me_ms}ms)\n"
                      f"✅ getUpdates کوتاه موفق ({poll_ms}ms)\n⚡ latency کل: {elapsed}ms")
    except urllib.error.HTTPError as e:
        if e.code in (404, 405):
            return False, f"آدرس Worker پیدا نشد یا مسیر /health فعال نیست (HTTP {e.code})."
        return False, f"Worker با خطای HTTP {e.code} پاسخ داد."
    except urllib.error.URLError as e:
        return False, f"اتصال به Worker برقرار نشد: {e.reason}"
    except TimeoutError:
        return False, "Timeout: پاسخ Worker/upstream تلگرام بیش از زمان مجاز طول کشید."
    except Exception as e:
        return False, f"خطای بررسی Worker: {e}"


def show(chat, mid, screen):
    text, kb = screen
    if mid:
        r = edit(chat, mid, text, kb)
        if r.get("ok") or "not modified" in str(r.get("description", "")):
            return
    send(chat, text, kb)


PROMPTS = {
    "w_add": "➕ کلمه(ها) را بفرستید (هر کلمه در یک خط).",
    "w_del": "🗑 شماره‌ی کلمه(ها) را بفرستید (با فاصله یا ویرگول جدا کنید).",
    "max": "✏️ حداکثر تعداد اخطار را بفرستید (عدد ۱ تا ۲۰).",
    "warn": "⚠️ شناسه، @نام‌کاربری یا بخشی از لقب کاربر را برای «اخطار» بفرستید.",
    "reset": "♻️ شناسه، @نام‌کاربری یا بخشی از لقب کاربر را برای «ریست اخطار» بفرستید.",
    "ban": "🚫 شناسه، @نام‌کاربری یا بخشی از لقب کاربر را برای «بن» بفرستید.",
    "unban": "✅ شناسه، @نام‌کاربری یا بخشی از لقب کاربر را برای «آنبن» بفرستید.",
    "connect": "🔗 شناسه‌ی عددی کاربر را بفرستید. چت کاملاً ناشناس است. پایان: /end",
    "find": "🔎 شناسه‌ی عددی کاربر را بفرستید.",
    "bcast": "📢 پیامی که باید برای همه ارسال شود را بفرستید (متن، عکس، ویدیو، فایل، استیکر و...).",
    "welcome": "✏️ متن جدید پیام خوش‌آمدگویی را بفرستید. ({name} = نام کاربر)",
    "sched_s": "✏️ ساعت شروع را به شکل HH:MM بفرستید (مثلاً 08:30).",
    "sched_e": "✏️ ساعت پایان را به شکل HH:MM بفرستید (مثلاً 23:00).",
    "priv_text": "✏️ متن جدید سیاست حفظ حریم خصوصی را بفرستید.",
    "cf_url": "✏️ آدرس Worker را بفرستید (مثال: https://my-bot.username.workers.dev).",
    "force_channels": "🔒 کانال‌های عضویت اجباری را بفرستید (هر خط یک @username یا شناسه کانال؛ برای خاموش کردن: off). ربات باید در کانال ادمین باشد.",
}


def ask(chat, key):
    ADMIN_STATE[chat] = key
    send(chat, PROMPTS[key] + "\n(لغو: /cancel)")


def send_worker_file(chat):
    code = worker_code()
    try:
        with open(WORKER_FILE, "w", encoding="utf-8") as f:
            f.write(code)
    except Exception:
        pass
    r = send_document(chat, "worker.js", code,
                      "📄 کد کامل Cloudflare Worker (آماده‌ی استفاده، با شناسه‌ی همین ربات)\n"
                      "Cloudflare ← Workers & Pages ← Create ← Hello World ← Edit code ← جایگزینی کد ← Deploy")
    if not r.get("ok"):                       # اگر ارسال فایل ممکن نبود، کد به‌صورت متن فرستاده می‌شود
        for i in range(0, len(code), 3800):
            send(chat, code[i:i + 3800])


def screen_dynamic(chat):
    labels = {"btn_search":"دکمه جستجوی چت","btn_next":"دکمه چت بعدی","btn_end":"دکمه پایان چت",
              "btn_nickname":"دکمه لقب",
              "btn_game":"دکمه چالش","btn_leaderboard":"دکمه برترین‌های هفته","btn_shop":"دکمه فروشگاه",
              "cmd_start":"دستور /start","cmd_search":"دستور /search",
              "cmd_next":"دستور /next","cmd_end":"دستور /end","cmd_privacy":"دستور /privacy",
              "cmd_game":"دستور /game","cmd_leaderboard":"دستور /leaderboard",
              "cmd_shop":"دستور /shop","cmd_nickname":"دستور /nickname",
              "cmd_help":"دستور /help","cmd_panel":"دستور /panel (فقط مالک)"}
    rows = [[(f"{'✅' if S(k)=='1' else '⛔'} {v}", f"a:dyn:t:{k}")] for k,v in labels.items()]
    try: layout=json.loads(S("keyboard_layout")).get("rows",[])
    except Exception: layout=[["search"],["next","end"],["nickname"],["game"],["leaderboard","shop"],["report"]]
    for i,group in enumerate(layout):
        label=" · ".join(group) or "(خالی)"
        rows.append([(f"ردیف {i+1}: {label} [{len(group)}]",f"a:kbrow:{i}")])
    rows += [[("➕ افزودن ردیف","a:kbaddrow"),
              (f"جهت: {'راست‌چین' if S('keyboard_direction')=='rtl' else 'چپ‌چین'}","a:kbdirection")],
             [("👁 تست و پیش‌نمایش منو","a:kbpreview")]]
    rows.append(HOME_BTN)
    return "⚙️ مدیریت دکمه‌ها و دستورات\nهر ردیف جداگانه قابل تنظیم است؛ ۱ تا ۴ دکمه، جابه‌جایی ردیف‌ها و پیش‌نمایش زنده.", ikb(rows)


def keyboard_row_editor(index):
    try: layout=json.loads(S("keyboard_layout")).get("rows",[])
    except Exception: layout=[]
    if not isinstance(index,int) or index<0 or index>=len(layout):
        return "ردیف پیدا نشد.",ikb([[("بازگشت","a:dyn")],HOME_BTN])
    group=layout[index]
    labels={"search":"جستجوی چت","next":"چت بعدی","end":"پایان چت","nickname":"لقب",
            "game":"چالش","leaderboard":"برترین‌های هفته","shop":"فروشگاه","report":"گزارش تخلف"}
    keyboard=[]
    for key,label in labels.items():
        marker="✅" if key in group else "➕"
        keyboard.append([(f"{marker} {label}",f"a:kbitem:{index}:{key}")])
    # Per-button position controls: left/right reorder in the same row; up/down moves to adjacent row.
    for pos,key in enumerate(group):
        controls=[]
        if pos>0: controls.append(("⬅️ چپ",f"a:kbpos:left:{index}:{key}"))
        if pos+1<len(group): controls.append(("➡️ راست",f"a:kbpos:right:{index}:{key}"))
        if index>0: controls.append(("⬆️ بالا",f"a:kbpos:up:{index}:{key}"))
        if index+1<len(layout): controls.append(("⬇️ پایین",f"a:kbpos:down:{index}:{key}"))
        if controls:
            keyboard.append([(f"📍 {labels.get(key,key)}",f"a:kbrow:{index}")] + controls)
    controls=[]
    if index>0: controls.append(("⬆️ ردیف بالا",f"a:kbmove:up:{index}"))
    if index+1<len(layout): controls.append(("⬇️ ردیف پایین",f"a:kbmove:down:{index}"))
    controls.append((f"↔️ چرخش ترتیب ({len(group)}/4)",f"a:kbcycle:{index}"))
    keyboard += [controls,[("🗑 حذف ردیف",f"a:kbdelrow:{index}")],
                 [("👁 پیش‌نمایش زنده","a:kbpreview")],HOME_BTN]
    return f"تنظیم ردیف {index+1}: {', '.join(labels.get(k,k) for k in group) or '(خالی)'}\nهر ردیف ۱ تا ۴ دکمه دارد. دکمه‌ها را چپ/راست در ردیف یا بالا/پایین بین ردیف‌ها جابه‌جا کن.",ikb(keyboard)


def screen_file_rules():
    labels = {"apk":"APK","zip":"ZIP","photo":"Photo","video":"Video",
              "audio":"Audio/Voice","document":"سایر اسناد"}
    rows = [[(f"{'✅ مجاز' if S('file_'+k)=='1' else '⛔ مسدود'} · {name}",f"a:file:t:{k}")]
            for k,name in labels.items()]
    rows.append(HOME_BTN)
    return "📎 محدودیت ارسال فایل\nروی هر مورد بزن تا مجاز/مسدود شود.", ikb(rows)


def screen_shop_settings():
    return ("🛍 تنظیمات امتیاز\n"
            f"پاداش چالش: {S('game_reward')} · قیمت انتخاب جنسیت: {S('game_gender_cost')} · قیمت رد: {S('game_skip_cost')}",
            ikb([[("➕ پاداش", "a:shopcfg:inc:game_reward"), ("➖ پاداش", "a:shopcfg:dec:game_reward")],
                 [("➕ قیمت جنسیت", "a:shopcfg:inc:game_gender_cost"), ("➖ قیمت جنسیت", "a:shopcfg:dec:game_gender_cost")],
                 [("➕ قیمت رد", "a:shopcfg:inc:game_skip_cost"), ("➖ قیمت رد", "a:shopcfg:dec:game_skip_cost")],
                 HOME_BTN]))


def screen_auto_replies(page=0):
    per = 8
    with LOCK:
        total = DB.execute("SELECT COUNT(*) FROM auto_replies").fetchone()[0]
        rows = DB.execute("SELECT id,keyword,response,enabled FROM auto_replies ORDER BY keyword LIMIT ? OFFSET ?",
                          (per, page * per)).fetchall()
    pages = max(1, (total + per - 1) // per)
    page = min(page, pages - 1)
    kb = [[(f"{'✅' if r[3] else '⛔'} {r[1][:22]} · {r[2][:16]}",
            f"a:autoedit:{r[0]}:{page}"),
           ("🗑", f"a:autodel:{r[0]}:{page}")] for r in rows]
    nav = []
    if page: nav.append(("◀️ قبلی", f"a:auto:{page-1}"))
    if page+1 < pages: nav.append(("بعدی ▶️", f"a:auto:{page+1}"))
    kb += [nav, [("➕ افزودن کلیدواژه/پاسخ", "a:autoadd")], HOME_BTN]
    return f"🤖 پاسخگوی خودکار · {total} کلیدواژه · صفحه {page+1}/{pages}\nبرای ویرایش یا فعال/غیرفعال کردن روی ردیف بزن؛ 🗑 برای حذف.", ikb(kb)


def screen_broadcasts(page=0):
    per = 8
    with LOCK:
        total = DB.execute("SELECT COUNT(*) FROM broadcasts").fetchone()[0]
        rows = DB.execute("SELECT id,created,success,failed FROM broadcasts ORDER BY id DESC LIMIT ? OFFSET ?",
                          (per, page * per)).fetchall()
    pages=max(1,(total+per-1)//per)
    page=min(page,pages-1)
    kb=[[(f"📣 #{r[0]} · {datetime.fromtimestamp(r[1], TEHRAN):%m-%d %H:%M} · ✅{r[2]} ❌{r[3]}",
          f"a:bcmgritem:{r[0]}")] for r in rows]
    nav=[]
    if page: nav.append(("◀️ قبلی",f"a:bcmgr:{page-1}"))
    if page+1<pages: nav.append(("بعدی ▶️",f"a:bcmgr:{page+1}"))
    kb += [nav, HOME_BTN]
    return f"📣 پیام‌های همگانی · {total} مورد", ikb(kb)


def screen_broadcast_item(bid):
    with LOCK:
        row=DB.execute("SELECT created,success,failed FROM broadcasts WHERE id=?",(bid,)).fetchone()
    if not row:
        return "این پیام همگانی پیدا نشد.", ikb([[("🔙 فهرست", "a:bcmgr:0")], HOME_BTN])
    kb=ikb([[("📌 سنجاق در چت‌های دریافت‌کننده",f"a:bcpin:{bid}")],
            [("👍 واکنش",f"a:bcreact:{bid}:like"),("❤️ واکنش",f"a:bcreact:{bid}:heart")],
            [("🗑 حذف همه کپی‌ها",f"a:bcdelete:{bid}")],
            [("🔙 فهرست", "a:bcmgr:0")], HOME_BTN])
    return f"📣 پیام همگانی #{bid}\nموفق: {row[1]} · ناموفق: {row[2]}\nزمان: {datetime.fromtimestamp(row[0],TEHRAN):%Y-%m-%d %H:%M}",kb


def _on_callback_impl(cb):
    if profile_callback(cb):
        return
    uid = int(cb["from"]["id"])
    if uid != OWNER_ID:
        if not profile_complete(uid):
            profile_prompt(uid)
            return
        if not enforce_force_join(uid):
            return
        callback_data = cb.get("data") or ""
        blocked = {}  # Keep existing game/challenge callbacks usable; stale cmd_game settings must not disable them.
        if callback_data.startswith("gm:shop:"):
            blocked = {"gm:shop:":"cmd_shop"}
        if any(callback_data.startswith(prefix) and S(setting) != "1" for prefix,setting in blocked.items()):
            send(uid, "⛔ این قابلیت فعلاً غیرفعال است.")
            return
    if GAME_MODULE and GAME_MODULE.handle_callback(cb):
        return
    chat, mid = cb["message"]["chat"]["id"], cb["message"]["message_id"]
    if uid != OWNER_ID:
        api("answerCallbackQuery", {"callback_query_id": cb["id"], "text": "⛔ دسترسی ندارید"})
        return
    api("answerCallbackQuery", {"callback_query_id": cb["id"]})
    p = cb["data"].split(":")
    a = p[1] if len(p) > 1 else "home"
    sub = p[2] if len(p) > 2 else ""
    ADMIN_STATE.pop(chat, None)
    secret_actions={"secretmenu","secactive","sechistory","secuser","secview","secsearch","secrequest","secpass",
                    "secreports","secreport","reportclose","secusers","secuserpick"}
    if a in secret_actions and SECRET_AUTHENTICATED.get(OWNER_ID,0) < time.time():
        secret_password_prompt(OWNER_ID)
        return

    if a == "home":
        show(chat, mid, panel_home())
    elif a == "important":
        show(chat, mid, panel_important())
    elif a == "other":
        show(chat, mid, panel_other())
    elif a == "secret":
        secret_password_prompt(OWNER_ID)
    elif a == "secretmenu":
        show(chat, mid, secret_panel())
    elif a == "secactive":
        show(chat, mid, secret_active(int(sub or 0)))
    elif a == "sechistory":
        show(chat, mid, secret_history_list(int(sub or 0)))
    elif a == "secreports":
        show(chat,mid,secret_reports(int(sub or 0)))
    elif a == "secreport":
        text,kb=secret_report_detail(int(sub))
        send(chat,text,kb)
        with LOCK:
            report_row = DB.execute("SELECT code FROM complaint_reports WHERE id=?", (int(sub),)).fetchone()
        if report_row:
            send_session_photos(chat, report_row[0])
    elif a == "reportclose":
        with LOCK:
            DB.execute("UPDATE complaint_reports SET status='closed' WHERE id=?",(int(sub),))
            DB.commit()
        show(chat,mid,secret_reports(0))
    elif a == "secusers":
        show(chat, mid, secret_user_list(int(sub or 0)))
    elif a == "secuserpick":
        show(chat, mid, secret_user_sessions(int(sub or 0), 0))
    elif a == "secuser":
        target=int(sub or 0)
        page=int(p[3]) if len(p)>3 and p[3].isdigit() else 0
        show(chat,mid,secret_user_sessions(target,page))
    elif a == "secview":
        text,kb=secret_history(sub)
        send(chat,text,kb)
        send_session_photos(chat, sub)
    elif a == "secsearch":
        ADMIN_STATE[chat]="secret_search"
        text, kb = secret_user_list(0)
        send(chat, "🔎 جستجوی پنل محرمانه\nمی‌توانی آیدی عددی، نام کاربری، لقب یا کد ۹ حرفی گفتگو را هم بفرستی.\n\n" + text, kb)
    elif a == "secrequest":
        if request_archive_consent(sub):
            log_chat_event(sub,OWNER_ID,"owner_requested_consented_archive","both participants notified")
            send(chat,"درخواست رضایت برای هر دو نفر ارسال شد؛ بازرسی مخفیانه انجام نمی‌شود.")
        else:
            send(chat,"نشست فعال پیدا نشد.")
    elif a == "secpass":
        screen_secret_password_change(chat)
    elif a == "mode":
        set_owner_mode("user" if sub == "user" else "admin")
    elif a == "stats":
        show(chat, mid, screen_stats())
    elif a == "export":
        send_report(chat)
    elif a == "bc":
        if sub == "go" and BCAST["mid"] and not BCAST["running"]:
            BCAST["running"] = True
            m_id, BCAST["mid"] = BCAST["mid"], None
            edit(chat, mid, "📢 ارسال شروع شد...")
            threading.Thread(target=broadcast_worker, args=(chat, m_id), daemon=True).start()
        elif sub == "no":
            BCAST["mid"] = None
            show(chat, mid, ("❌ پیام همگانی لغو شد.", ikb([HOME_BTN])))
        elif BCAST["running"]:
            send(chat, "⏳ یک پیام همگانی در حال ارسال است؛ صبر کنید تا تمام شود.")
        else:
            ask(chat, "bcast")
    elif a == "find":
        ask(chat, "find")
    elif a == "u":
        act, t = sub, int(p[3]) if len(p) > 3 and p[3].isdigit() else 0
        note = "" if act == "view" else user_action(act, t)
        show(chat, mid, screen_user(t, note))
    elif a == "resolve":
        action, target = sub, int(p[3]) if len(p)>3 and p[3].isdigit() else 0
        if action in ("ban","unban","warn","reset"):
            show(chat,mid,screen_user(target,user_action(action,target)))
    elif a == "bl":
        show(chat, mid, screen_banned(int(sub or 0)))
    elif a == "ub":
        user_action("unban", int(sub))
        show(chat, mid, screen_banned(int(p[3]) if len(p) > 3 else 0))
    elif a == "uball":
        if sub == "yes":
            with LOCK:
                ids = [r[0] for r in DB.execute("SELECT uid FROM users WHERE banned=1")]
            for t in ids:
                user_action("unban", t)
            show(chat, mid, (f"✅ {len(ids)} کاربر آنبن شد.", ikb([[("🚷 بن‌شده‌ها", "a:bl:0")], HOME_BTN])))
        else:
            show(chat, mid, ("⚠️ همه‌ی کاربران بن‌شده آزاد شوند؟", confirm_kb("a:uball:yes", "a:bl:0")))
    elif a == "ac":
        show(chat, mid, screen_active(int(sub or 0)))
    elif a == "ace":
        user_action("end", int(sub))
        show(chat, mid, screen_active(int(p[3]) if len(p) > 3 else 0))
    elif a == "acall":
        if sub == "yes":
            pairs = active_pairs()
            for x, _ in pairs:
                user_action("end", x) if x != OWNER_ID else end_chat(OWNER_ID)
            show(chat, mid, (f"✅ {len(pairs)} چت قطع شد.", ikb([[("💬 چت‌های فعال", "a:ac:0")], HOME_BTN])))
        else:
            show(chat, mid, ("⚠️ همه‌ی چت‌های فعال قطع شوند؟", confirm_kb("a:acall:yes", "a:ac:0")))
    elif a == "wel":
        if sub == "set":
            ask(chat, "welcome")
            return
        if sub == "pre":
            send(chat, welcome_text(cb))
            return
        if sub == "def":
            set_S("welcome_text", DEFAULT_WELCOME)
        show(chat, mid, screen_welcome())
    elif a == "power":
        if sub == "t":
            set_S("bot_on", "0" if S("bot_on") == "1" else "1")
        show(chat, mid, screen_power())
    elif a == "sched":
        if sub == "t":
            set_S("sched_on", "0" if S("sched_on") == "1" else "1")
        elif sub == "m":
            set_S("sched_mode", "inactive" if S("sched_mode") == "active" else "active")
        elif sub in ("s", "e"):
            ask(chat, "sched_" + sub)
            return
        show(chat, mid, screen_sched())
    elif a == "words":
        show(chat, mid, screen_words(int(sub or 0)))
    elif a == "w":
        if sub == "add":
            ask(chat, "w_add")
        elif sub == "del":
            ask(chat, "w_del")
        elif sub == "exp":
            with LOCK:
                rows = DB.execute("SELECT id,word FROM words ORDER BY id").fetchall()
            data = "\n".join(f"{i}\t{w}" for i, w in rows)
            send_document(chat, "banned_words.txt", data, f"📤 {len(rows)} کلمه")
    elif a == "warn":
        if sub == "list":
            show(chat, mid, screen_banned(0))
        elif sub:
            ask(chat, sub)
        else:
            show(chat, mid, screen_warn())
    elif a == "colors":
        show(chat, mid, screen_colors())
    elif a == "col":
        k = sub
        cur = S("color_" + k)
        set_S("color_" + k, STYLE_ORDER[(STYLE_ORDER.index(cur) + 1) % len(STYLE_ORDER)])
        show(chat, mid, screen_priv() if k == "priv" else screen_colors())
    elif a == "priv":
        if sub == "t":
            set_S("priv_show", "0" if S("priv_show") == "1" else "1")
        elif sub == "text":
            ask(chat, "priv_text")
            return
        show(chat, mid, screen_priv())
    elif a == "connect":
        ask(chat, "connect")
    elif a == "dyn":
        if sub == "t" and len(p) > 3:
            key = p[3]
            if key in ("btn_search","btn_next","btn_end","btn_nickname","btn_game",
                       "btn_leaderboard","btn_shop","cmd_start","cmd_search","cmd_next",
                       "cmd_end","cmd_privacy","cmd_game","cmd_leaderboard","cmd_shop","cmd_nickname",
                       "cmd_help","cmd_panel"):
                set_S(key, "0" if S(key) == "1" else "1")
                refresh_bot_commands()
            show(chat, mid, screen_dynamic(chat))
        else:
            show(chat, mid, screen_dynamic(chat))
    elif a == "kbmove":
        direction=sub
        index=int(p[3]) if len(p)>3 and p[3].isdigit() else -1
        try:
            layout=json.loads(S("keyboard_layout")).get("rows",[])
            i=index
            j=i-1 if direction=="up" else i+1
            if 0<=i<len(layout) and 0<=j<len(layout):
                layout[i],layout[j]=layout[j],layout[i]
                set_S("keyboard_layout",json.dumps({"rows":layout},ensure_ascii=False))
        except Exception:
            pass
        show(chat,mid,screen_dynamic(chat))
    elif a == "kbrow":
        index=int(sub or 0)
        show(chat,mid,keyboard_row_editor(index))
    elif a == "kbaddrow":
        try: layout=json.loads(S("keyboard_layout")).get("rows",[])
        except Exception: layout=[]
        if len(layout)<12:
            layout.append([])
            set_S("keyboard_layout",json.dumps({"rows":layout},ensure_ascii=False))
        show(chat,mid,screen_dynamic(chat))
    elif a == "kbdelrow":
        index=int(sub or 0)
        try:
            layout=json.loads(S("keyboard_layout")).get("rows",[])
            if 0<=index<len(layout):
                layout.pop(index)
                set_S("keyboard_layout",json.dumps({"rows":layout},ensure_ascii=False))
        except Exception:
            pass
        show(chat,mid,screen_dynamic(chat))
    elif a == "kbitem":
        index=int(sub or 0)
        key=p[3] if len(p)>3 else ""
        allowed={"search","next","end","nickname","game","leaderboard","shop","report"}
        try:
            layout=json.loads(S("keyboard_layout")).get("rows",[])
            if 0<=index<len(layout) and key in allowed:
                if key in layout[index]:
                    layout[index].remove(key)
                elif len(layout[index])<4:
                    for group in layout:
                        if key in group: group.remove(key)
                    layout[index].append(key)
                set_S("keyboard_layout",json.dumps({"rows":layout},ensure_ascii=False))
        except Exception:
            pass
        show(chat,mid,keyboard_row_editor(index))
    elif a == "kbpos":
        direction=sub
        index=int(p[3]) if len(p)>3 and p[3].isdigit() else -1
        key=p[4] if len(p)>4 else ""
        labels={"search":"جستجوی چت","next":"چت بعدی","end":"پایان چت","nickname":"لقب",
                "game":"چالش","leaderboard":"برترین‌های هفته","shop":"فروشگاه","report":"گزارش تخلف"}
        try:
            layout=json.loads(S("keyboard_layout")).get("rows",[])
            if 0<=index<len(layout) and key in layout[index]:
                pos=layout[index].index(key)
                if direction=="left" and pos>0:
                    layout[index][pos-1],layout[index][pos]=layout[index][pos],layout[index][pos-1]
                elif direction=="right" and pos+1<len(layout[index]):
                    layout[index][pos+1],layout[index][pos]=layout[index][pos],layout[index][pos+1]
                elif direction in ("up","down"):
                    dest=index-1 if direction=="up" else index+1
                    if 0<=dest<len(layout) and key in layout[index] and len(layout[dest])<4:
                        layout[index].remove(key)
                        layout[dest].insert(min(pos,len(layout[dest])),key)
                set_S("keyboard_layout",json.dumps({"rows":layout},ensure_ascii=False))
                dest_index = index-1 if direction=="up" and index>0 else index+1 if direction=="down" and index+1<len(layout) else index
                show(chat,mid,keyboard_row_editor(dest_index))
            else:
                show(chat,mid,keyboard_row_editor(index))
        except Exception:
            show(chat,mid,keyboard_row_editor(index))
    elif a == "kbcycle":
        index=int(sub or 0)
        try:
            layout=json.loads(S("keyboard_layout")).get("rows",[])
            if 0<=index<len(layout) and len(layout[index])>1:
                layout[index]=layout[index][1:]+layout[index][:1]
                set_S("keyboard_layout",json.dumps({"rows":layout},ensure_ascii=False))
        except Exception:
            pass
        show(chat,mid,keyboard_row_editor(index))
    elif a == "kbpreview":
        preview_uid=(OWNER_ID+1) if chat==OWNER_ID else chat
        send(chat,"👁 پیش‌نمایش زنده‌ی منوی کاربر:",main_kb(preview_uid))
        show(chat,None,screen_dynamic(chat))
    elif a == "kbcols":
        current=int(S("keyboard_columns") or 2)
        set_S("keyboard_columns", 1 if current>=3 else current+1)
        show(chat,mid,screen_dynamic(chat))
    elif a == "kbdirection":
        set_S("keyboard_direction","ltr" if S("keyboard_direction")=="rtl" else "rtl")
        show(chat,mid,screen_dynamic(chat))
    elif a == "files":
        if sub == "t" and len(p) > 3 and p[3] in ("apk","zip","photo","video","audio","document"):
            key = "file_" + p[3]
            set_S(key, "0" if S(key) == "1" else "1")
        show(chat, mid, screen_file_rules())
    elif a == "file":
        if sub == "t" and len(p) > 3 and p[3] in ("apk","zip","photo","video","audio","document"):
            key = "file_" + p[3]
            set_S(key, "0" if S(key) == "1" else "1")
        show(chat, mid, screen_file_rules())
    elif a == "shopcfg":
        if sub in ("inc","dec") and len(p) > 3:
            key = p[3]
            if key in ("game_reward","game_gender_cost","game_skip_cost"):
                step = 5 if key == "game_reward" else 10
                val = max(0, int(S(key) or 0) + (step if sub == "inc" else -step))
                set_S(key, val)
        show(chat, mid, screen_shop_settings())
    elif a == "fj":
        ask(chat, "force_channels")
    elif a == "auto":
        show(chat, mid, screen_auto_replies(int(sub or 0)))
    elif a == "autoadd":
        ADMIN_STATE[chat] = "auto_add_keyword"
        send(chat, "کلیدواژه یا جمله را بفرست (حداقل ۸۸ مورد پشتیبانی می‌شود؛ هر ورودی یک trigger است).")
    elif a == "autoedit":
        rid = int(sub or 0)
        with LOCK:
            row = DB.execute("SELECT keyword,response,enabled FROM auto_replies WHERE id=?", (rid,)).fetchone()
            if row:
                DB.execute("UPDATE auto_replies SET enabled=1-enabled WHERE id=?", (rid,))
                DB.commit()
        if row:
            ADMIN_STATE[chat] = "auto_edit_response"
            AUTO_EDIT_TARGET[chat] = rid
            send(chat, f"کلیدواژه: {row[0]}\nپاسخ فعلی: {row[1]}\n{'غیرفعال شد' if row[2] else 'فعال شد'}؛ پاسخ جدید را بفرست (یا /cancel).")
        show(chat, mid, screen_auto_replies(int(p[3]) if len(p)>3 and p[3].isdigit() else 0))
    elif a == "autodel":
        rid=int(sub or 0)
        with LOCK:
            DB.execute("DELETE FROM auto_replies WHERE id=?",(rid,)); DB.commit()
        show(chat,mid,screen_auto_replies(int(p[3]) if len(p)>3 and p[3].isdigit() else 0))
    elif a == "bcmgr":
        show(chat,mid,screen_broadcasts(int(sub or 0)))
    elif a == "bcmgritem":
        show(chat,mid,screen_broadcast_item(int(sub)))
    elif a in ("bcpin","bcreact","bcdelete"):
        bid=int(sub)
        if a=="bcdelete":
            with LOCK:
                n=DB.execute("SELECT COUNT(*) FROM broadcast_deliveries WHERE broadcast_id=?",(bid,)).fetchone()[0]
            show(chat,mid,(f"حذف کپی‌های پیام #{bid} از {n} گفتگو؟",ikb([[("بله، حذف",f"a:bcdeleteconfirm:{bid}","danger"),
                                                                            ("لغو",f"a:bcmgritem:{bid}")]])))
        else:
            with LOCK:
                delivery=DB.execute("SELECT user_id,message_id FROM broadcast_deliveries WHERE broadcast_id=?",(bid,)).fetchall()
            ok=fail=0
            for target, message_id in delivery:
                if a=="bcpin":
                    r=api("pinChatMessage",{"chat_id":target,"message_id":message_id,"disable_notification":True})
                else:
                    emoji={"like":"👍","heart":"❤️"}.get(p[3],"👍")
                    r=api("setMessageReaction",{"chat_id":target,"message_id":message_id,
                        "reaction":[{"type":"emoji","emoji":emoji}]})
                if r.get("ok"): ok+=1
                else: fail+=1
            send(chat,f"عملیات انجام شد. موفق: {ok} · ناموفق: {fail}",ikb([[("بازگشت",f"a:bcmgritem:{bid}")],HOME_BTN]))
    elif a == "bcdeleteconfirm":
        bid=int(sub)
        with LOCK:
            delivery=DB.execute("SELECT user_id,message_id FROM broadcast_deliveries WHERE broadcast_id=?",(bid,)).fetchall()
        ok=fail=0
        for target,message_id in delivery:
            r=api("deleteMessage",{"chat_id":target,"message_id":message_id})
            if r.get("ok"): ok+=1
            else: fail+=1
        with LOCK:
            DB.execute("DELETE FROM broadcast_deliveries WHERE broadcast_id=?",(bid,))
            DB.execute("DELETE FROM broadcasts WHERE id=?",(bid,))
            DB.commit()
        send(chat,f"حذف انجام شد. موفق: {ok} · ناموفق: {fail}",ikb([[("📣 فهرست پیام‌ها","a:bcmgr:0")],HOME_BTN]))
    elif a == "cf":
        if sub == "set":
            ask(chat, "cf_url")
        elif sub == "del":
            set_S("worker_url", "")
            set_S("worker_enabled", "0")
            set_S("worker_auto_recover", "0")
            show(chat, mid, screen_cf())
        elif sub == "off":
            set_S("worker_enabled", "0")
            set_S("worker_auto_recover", "0")
            send(chat, "🔌 اتصال مستقیم فعال شد؛ بازگشت خودکار به Worker خاموش است.", ikb([HOME_BTN]))
        elif sub == "on":
            url = S("worker_url")
            if not url:
                send(chat, "⚠️ ابتدا آدرس Worker را ثبت کنید.")
            else:
                ok, info = health_check(url)
                set_S("worker_auto_recover", "1")
                set_S("worker_enabled", "1" if ok else "0")
                send(chat, ("☁️ Cloudflare فعال شد.\n" if ok else
                            "❌ فعال‌سازی نشد؛ اتصال مستقیم حفظ شد.\n") + str(info)[:700],
                     ikb([HOME_BTN]))
        elif sub == "chk":
            url = S("worker_url")
            if not url:
                send(chat, "⚠️ ابتدا آدرس Worker را ثبت کنید.")
            else:
                ok, info = health_check(url)
                send(chat, ("✅ Worker سالم است.\n" if ok else "❌ Worker پاسخ سالم نداد.\n") + str(info)[:700])
        elif sub == "file":
            send_worker_file(chat)
        else:
            show(chat, mid, screen_cf())


def on_callback(cb):
    try:
        _on_callback_impl(cb)
    except Exception as exc:
        report_exception("callback_query", exc)
    finally:
        # Always clear Telegram's callback spinner, even if a handler raises.
        try:
            api("answerCallbackQuery", {"callback_query_id": cb.get("id")})
        except Exception as exc:
            report_exception("answerCallbackQuery", exc)


def safe_user_message(m):
    try:
        on_user_message(m)
    except Exception as exc:
        report_exception("message handler", exc)


def safe_owner_message(m):
    try:
        on_owner_message(m)
    except Exception as exc:
        report_exception("owner message handler", exc)


def _ints(text):
    return [int(x) for x in re.findall(r"\d+", text)]


def handle_admin_user_lookup(chat, action, query):
    ids = resolve_user_query(query)
    if not ids:
        send(chat, "❌ کاربری مطابق این شناسه/نام‌کاربری/لقب پیدا نشد؛ کاربر باید قبلاً ربات را باز کرده باشد.")
        return
    if len(ids) == 1:
        target = ids[0]
        show(chat, None, screen_user(target, user_action(action, target)))
        return
    rows=[]
    with LOCK:
        for uid in ids[:12]:
            r=DB.execute("SELECT nickname,username,banned FROM users WHERE uid=?",(uid,)).fetchone()
            if r:
                label=f"{r[0] or 'بدون لقب'} · @{r[1] or '-'} · {uid} · {'بن' if r[2] else 'فعال'}"
                rows.append([(label[:60],f"a:resolve:{action}:{uid}")])
    send(chat,"چند کاربر پیدا شد؛ هدف را انتخاب کن:",ikb(rows+[HOME_BTN]))


def on_owner_input(chat, text):
    """پاسخ متنی مالک به پرسش‌های پنل."""
    key = ADMIN_STATE.pop(chat, None)
    if key == "force_channels":
        set_S("force_channels", "" if text.strip().lower() == "off" else "\n".join(
            x.strip() for x in text.replace(",", "\n").splitlines() if x.strip()))
        send(chat, "✅ تنظیم کانال‌های عضویت اجباری ذخیره شد. ربات باید در هر کانال دسترسی بررسی عضویت داشته باشد.",
             ikb([[("🔒 عضویت اجباری", "a:fj")], HOME_BTN]))
    elif key == "secret_password":
        ok,message=_secret_auth(OWNER_ID,text)
        if ok:
            send(chat,"✅ دسترسی پنل محرمانه تا ۱۰ دقیقه فعال شد.",secret_panel()[1])
        else:
            send(chat,message)
    elif key == "secret_new_password":
        secret_set_password(chat,text)
    elif key == "secret_search":
        query=text.strip()
        if not query:
            send(chat, *secret_user_list(0)); return
        if query.lstrip("-").isdigit():
            target = int(query)
            with LOCK:
                exists = DB.execute("SELECT 1 FROM users WHERE uid=?", (target,)).fetchone()
            if exists:
                show(chat, None, secret_user_sessions(target, 0))
            else:
                send(chat, "❌ کاربری با این آیدی پیدا نشد. فهرست کاربران:", secret_user_list(0)[1])
        elif len(query) == 9 and query.upper().isalnum():
            result = secret_history(query.upper())
            send(chat, *result)
        else:
            matches = resolve_user_query(query)
            if len(matches) == 1:
                show(chat, None, secret_user_sessions(matches[0], 0))
            elif matches:
                buttons = []
                with LOCK:
                    for target in matches[:20]:
                        row = DB.execute("SELECT nickname,username FROM users WHERE uid=?", (target,)).fetchone()
                        if row:
                            label = row[0] or ("@" + row[1] if row[1] else str(target))
                            buttons.append([(f"{label} · ID {target}", f"a:secuserpick:{target}")])
                buttons += [[("👥 فهرست همه کاربران", "a:secusers:0")], HOME_BTN]
                send(chat, f"🔎 {len(matches)} کاربر پیدا شد؛ یکی را انتخاب کن:", ikb(buttons))
            else:
                send(chat, "❌ کاربری با این نام پیدا نشد. آیدی عددی، نام کاربری یا لقب را امتحان کن.", secret_user_list(0)[1])
    elif key == "auto_add_keyword":
        if not text.strip() or len(text.strip()) > 80:
            send(chat, "کلیدواژه باید بین ۱ تا ۸۰ نویسه باشد."); return
        ADMIN_STATE[chat] = "auto_add_response"
        AUTO_EDIT_TARGET[chat] = text.strip()
        send(chat, "حالا پاسخ خودکار این کلیدواژه را بفرست.")
    elif key == "auto_add_response":
        keyword = AUTO_EDIT_TARGET.pop(chat, "")
        if not keyword or not text.strip():
            send(chat, "کلیدواژه/پاسخ خالی است؛ ذخیره نشد."); return
        with LOCK:
            DB.execute("INSERT INTO auto_replies(keyword,response,enabled) VALUES(?,?,1) "
                       "ON CONFLICT(keyword) DO UPDATE SET response=excluded.response,enabled=1",
                       (keyword, text.strip()[:1000]))
            DB.commit()
        send(chat, "✅ پاسخ خودکار ذخیره شد.", ikb([[("🤖 فهرست پاسخ‌ها", "a:auto:0")], HOME_BTN]))
    elif key == "auto_edit_response":
        rid = AUTO_EDIT_TARGET.pop(chat, None)
        if rid and text.strip():
            with LOCK:
                DB.execute("UPDATE auto_replies SET response=? WHERE id=?", (text.strip()[:1000], rid))
                DB.commit()
            send(chat, "✅ پاسخ ویرایش شد.", ikb([[("🤖 فهرست پاسخ‌ها", "a:auto:0")], HOME_BTN]))
    if key == "w_add":
        n = 0
        with LOCK:
            for w in dict.fromkeys(x.strip() for x in text.splitlines() if x.strip()):
                if normalize(w):
                    n += DB.execute("INSERT OR IGNORE INTO words(word) VALUES(?)", (w,)).rowcount
            DB.commit()
        reload_words()
        send(chat, f"✅ {n} کلمه‌ی جدید اضافه شد.", ikb([[("🚫 کلمات ممنوعه", "a:words:0")], HOME_BTN]))
    elif key == "w_del":
        ids = _ints(text)
        with LOCK:
            n = sum(DB.execute("DELETE FROM words WHERE id=?", (i,)).rowcount for i in ids)
            DB.commit()
        reload_words()
        send(chat, f"✅ {n} کلمه حذف شد.", ikb([[("🚫 کلمات ممنوعه", "a:words:0")], HOME_BTN]))
    elif key == "max":
        v = _ints(text)
        if v and 1 <= v[0] <= 20:
            set_S("max_warns", v[0])
            send(chat, f"✅ حداکثر اخطار: {v[0]}")
        else:
            send(chat, "❌ عدد معتبر ۱ تا ۲۰ بفرستید.")
    elif key in ("warn", "reset", "ban", "unban"):
        handle_admin_user_lookup(chat, key, text)
    elif key == "find":
        v = _ints(text)
        if not v:
            send(chat, "❌ یک شناسه‌ی عددی بفرستید.")
            return
        show(chat, None, screen_user(v[0]))
    elif key == "connect":
        v = _ints(text)
        send(chat, user_action("conn", v[0]) if v else "❌ یک شناسه‌ی عددی بفرستید.")
    elif key == "welcome":
        set_S("welcome_text", text.strip())
        show(chat, None, screen_welcome())
    elif key in ("sched_s", "sched_e"):
        if valid_hm(text):
            h, m = text.strip().split(":")
            set_S("sched_start" if key == "sched_s" else "sched_end", f"{int(h):02d}:{m}")
            send(chat, "✅ ثبت شد.", ikb([[("⏰ زمان‌بندی", "a:sched")], HOME_BTN]))
        else:
            send(chat, "❌ قالب باید HH:MM باشد.")
    elif key == "priv_text":
        value=text.strip().removeprefix("حریم خصوصی : v2.9\n").removeprefix("حریم خصوصی : v2.9")
        set_S("priv_text", "حریم خصوصی : v2.9\n\n"+value)
        send(chat, "✅ متن سیاست حفظ حریم خصوصی تغییر کرد؛ پاسخ کلیدواژه‌های حریم خصوصی از متن جدید ساخته می‌شود.")
    elif key == "cf_url":
        u = text.strip().rstrip("/")
        if re.fullmatch(r"https://[\w.-]+(:\d+)?(/[\w./-]*)?", u):
            ok, info = health_check(u)
            set_S("worker_url", u)
            set_S("worker_auto_recover", "1")
            set_S("worker_enabled", "1" if ok else "0")
            send(chat, ("✅ آدرس ثبت و Cloudflare فعال شد.\n" if ok else
                        "⚠️ آدرس ثبت شد، اما تست شکست خورد و اتصال مستقیم حفظ شد.\n") + str(info)[:700])
        else:
            send(chat, "❌ آدرس باید با https:// شروع شود.")


def on_owner_message(m):
    chat = m["chat"]["id"]
    text = (m.get("text") or "").strip()
    if text in ("دستورات", "/help"):
        send_auto_reply_catalog(chat, OWNER_ID)
        return
    if text == "حذف":
        replied = m.get("reply_to_message")
        if replied and int(m.get("from", {}).get("id", 0)) == OWNER_ID:
            result = api("deleteMessage", {"chat_id": chat, "message_id": replied["message_id"]})
            send(chat, "✅ پیام حذف شد." if result.get("ok") else
                 f"❌ حذف پیام انجام نشد: {result.get('description','خطای تلگرام')}")
        else:
            send(chat, "برای حذف، فقط مالک باید روی پیام موردنظر ریپلای کند و «حذف» بفرستد.")
        return
    if text == "/cancel":
        ADMIN_STATE.pop(chat, None)
        BCAST["mid"] = None
        send(chat, "لغو شد.", ikb([HOME_BTN]))
        return
    if ADMIN_STATE.get(chat) == "bcast":
        ADMIN_STATE.pop(chat, None)
        with LOCK:
            n = DB.execute("SELECT COUNT(*) FROM users WHERE banned=0 AND uid!=?", (OWNER_ID,)).fetchone()[0]
        BCAST["mid"] = m["message_id"]
        send(chat, f"📢 پیام بالا برای {n} کاربر ارسال شود؟",
             ikb([[(f"✅ ارسال برای {n} نفر", "a:bc:go", "success"), ("❌ لغو", "a:bc:no", "danger")]]))
        return
    if text in ("/start", "/panel", "/admin"):
        ADMIN_STATE.pop(chat, None)
        show(chat, None, panel_home())
        return
    if text in ("/user", "/test"):
        set_owner_mode("user")
        return
    if text == "/stats":
        show(chat, None, screen_stats())
        return
    if text == "/end":
        p = end_chat(OWNER_ID)
        send(chat, "✅ چت مستقیم پایان یافت." if p else "ℹ️ چت مستقیمی فعال نیست.")
        return
    if text.startswith("/connect"):
        v = _ints(text)
        if v:
            send(chat, user_action("conn", v[0]))
        else:
            ask(chat, "connect")
        return
    u = get_user(OWNER_ID)
    if u["partner"] and text == "اخطار":
        target = int(u["partner"])
        apply_warn(target, None)
        send(chat, f"✅ دستور اخطار برای کاربر {target} اجرا شد.", chat_kb(OWNER_ID))
        return
    if u["partner"] and text.startswith("سکوت"):
        match = re.fullmatch(r"سکوت ([1-9][0-9]{0,3})", text)
        if not match or not (1 <= int(match.group(1)) <= 1440):
            send(chat, "قالب درست: سکوت 14 (بین کلمه و عدد فاصله باشد؛ مدت ۱ تا ۱۴۴۰ دقیقه).", chat_kb(OWNER_ID))
            return
        minutes = int(match.group(1)); target = int(u["partner"]); until = time.time() + minutes * 60
        code = active_chat_code(OWNER_ID)
        with LOCK:
            DB.execute("INSERT INTO user_mutes(uid,muted_until,by_owner) VALUES(?,?,?) ON CONFLICT(uid) DO UPDATE SET muted_until=excluded.muted_until,by_owner=excluded.by_owner", (target, until, OWNER_ID))
            if code:
                created = time.time()
                DB.execute("UPDATE chat_sessions SET active=0,ended=? WHERE code=? AND active=1", (created, code))
                DB.execute("INSERT INTO chat_events(code,user_id,event,created,details) VALUES(?,?,?,?,?)", (code, OWNER_ID, "owner_mute_report", created, f"target={target}; minutes={minutes}"))
                DB.execute("INSERT INTO complaint_reports(code,reporter,accused,reason,details,created,status) VALUES(?,?,?,?,?,?, 'open')",
                            (code, OWNER_ID, target, "owner_mute", f"مالک در حین چت دستور سکوت {minutes} دقیقه‌ای ثبت کرد.", created))
            DB.commit()
        set_partner(OWNER_ID, None); set_partner(target, None)
        if target in WAITING: WAITING.remove(target)
        send(target, f"🔇 دسترسی جستجوی چت شما به مدت {minutes} دقیقه محدود شد.", main_kb(target))
        send(chat, f"✅ سکوت {minutes} دقیقه‌ای ثبت شد؛ چت از حالت عادی خارج شد و برای رسیدگی مدیریتی علامت خورد.", main_kb(OWNER_ID))
        send(OWNER_ID, f"🚩 نشست {code or 'نامشخص'} برای رسیدگی مدیریتی علامت‌گذاری شد؛ کاربر {target} تا {datetime.fromtimestamp(until, TEHRAN):%Y-%m-%d %H:%M} سکوت است.")
        return
    if chat in ADMIN_STATE and text:
        on_owner_input(chat, text)
        return
    if u["partner"]:
        relay(m, u)
    else:
        send(chat, "برای باز کردن پنل: /panel")


# ───────────────────────── 9) کد Cloudflare Worker ─────────────────────────
WORKER_TEMPLATE = r"""/**
 * Cloudflare Worker — پراکسی امن API تلگرام برای ربات چت ناشناس
 * ----------------------------------------------------------------
 * نصب: dash.cloudflare.com ← Workers & Pages ← Create ← Hello World ← Deploy
 *       ← Edit code ← کل این کد را جایگزین کنید ← Deploy
 * سپس آدرس https://<name>.<account>.workers.dev را در پنل ربات (☁️ Cloudflare) ثبت کنید.
 *
 * مسیرها:
 *   GET  /            و  /health        → بررسی سلامت  {"ok": true, ...}
 *   ANY  /bot<TOKEN>/<method>           → عبور به api.telegram.org
 *   GET  /file/bot<TOKEN>/<path>        → دانلود فایل‌های تلگرام
 */

// فقط همین ربات اجازه‌ی استفاده از Worker را دارد (عدد قبل از «:» در توکن).
// اگر خالی بماند، هر رباتی می‌تواند از این Worker عبور کند.
const ALLOWED_BOT_ID = "__BOT_ID__";

const TELEGRAM_API = "https://api.telegram.org";
const VERSION = "2.2.0";
// Bot long-poll is capped at 10s; keep upstream wall time below 13s.
const UPSTREAM_TIMEOUT_MS = 13000;

export default {
  async fetch(request) {
    const url = new URL(request.url);
    const path = url.pathname.replace(/\/{2,}/g, "/");

    if (request.method === "OPTIONS") {
      return new Response(null, { status: 204, headers: corsHeaders() });
    }

    if (path === "/" || path === "/health") {
      return json({
        ok: true,
        service: "anonchat-telegram-proxy",
        version: VERSION,
        restricted: Boolean(ALLOWED_BOT_ID),
        time: new Date().toISOString(),
      });
    }

    const m = path.match(/^\/(file\/)?bot(\d+):([A-Za-z0-9_-]+)(\/.*)?$/);
    if (!m) {
      return json({ ok: false, error_code: 400, description: "Bad path. Use /bot<TOKEN>/<method>" }, 400);
    }
    if (ALLOWED_BOT_ID && m[2] !== ALLOWED_BOT_ID) {
      return json({ ok: false, error_code: 403, description: "This proxy is locked to another bot" }, 403);
    }

    const headers = new Headers();
    const ct = request.headers.get("content-type");
    if (ct) headers.set("content-type", ct);

    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), UPSTREAM_TIMEOUT_MS);
    const init = {
      method: request.method,
      headers,
      redirect: "follow",
      signal: controller.signal,
    };
    if (request.method !== "GET" && request.method !== "HEAD") {
      // Forward the request stream instead of buffering uploads in Worker memory.
      init.body = request.body;
    }

    try {
      const upstream = await fetch(TELEGRAM_API + path + url.search, init);
      const out = new Headers(corsHeaders());
      out.set("cache-control", "no-store, no-cache, must-revalidate");
      const uct = upstream.headers.get("content-type");
      if (uct) out.set("content-type", uct);
      const ud = upstream.headers.get("content-disposition");
      if (ud) out.set("content-disposition", ud);
      const retryAfter = upstream.headers.get("retry-after");
      if (retryAfter) out.set("retry-after", retryAfter);
      return new Response(upstream.body, { status: upstream.status, headers: out });
    } catch (err) {
      const aborted = err && err.name === "AbortError";
      return json({
        ok: false,
        error_code: aborted ? 504 : 502,
        description: aborted
          ? "Telegram upstream timeout"
          : "Upstream error: " + String(err),
      }, aborted ? 504 : 502);
    } finally {
      clearTimeout(timer);
    }
  },
};

function corsHeaders() {
  return {
    "access-control-allow-origin": "*",
    "access-control-allow-methods": "GET, POST, OPTIONS",
    "access-control-allow-headers": "content-type",
  };
}

function json(obj, status = 200) {
  return new Response(JSON.stringify(obj), {
    status,
    headers: {
      "content-type": "application/json; charset=utf-8",
      "cache-control": "no-store, no-cache, must-revalidate",
      ...corsHeaders(),
    },
  });
}
"""


def worker_code():
    """کد کامل Worker با شناسه‌ی همین ربات؛ همیشه از داخل خود برنامه ساخته می‌شود (نیازی به فایل جدا نیست)."""
    bot_id = BOT_TOKEN.split(":")[0] if ":" in BOT_TOKEN else ""
    return WORKER_TEMPLATE.replace("__BOT_ID__", bot_id)


# ───────────────────────── 9.5) بازی‌ها و چالش‌ها ─────────────────────────
# این بخش عمداً در فایل اصلی قرار دارد و فقط از جداول gm_* خودش استفاده می‌کند.
GAME_TRUTHS = """آخرین باری که از ته دل خندیدی کی بود؟
یک عادت کوچک که کمتر کسی می‌داند چیست؟
یک آهنگ که همیشه حالت را بهتر می‌کند چیست؟
تا حالا از کسی خوشت آمده ولی نگفته باشی؟
خاطره‌ای که هر بار یادت می‌آید لبخند می‌زنی چیست؟
بزرگ‌ترین سوتی بامزه‌ات چه بوده؟
اگر یک روز نامرئی بودی، اولین کار بی‌ضررت چه بود؟
کدام ویژگی خودت را بیشتر دوست داری؟
یک مهارت که دوست داری یاد بگیری چیست؟
آخرین دروغ مصلحتی کوچکت چه بود؟
چه چیزی خیلی زود عصبانی‌ات می‌کند؟
بهترین تعریفی که تا حالا شنیده‌ای چه بوده؟
اگر با یک شخصیت فیلم شام می‌خوردی، چه کسی را انتخاب می‌کردی؟
از چه چیزی بی‌دلیل می‌ترسی؟
یک تصمیم کوچک که زندگی‌ات را بهتر کرد چه بود؟
کدام خوراکی را هیچ‌وقت رد نمی‌کنی؟
اگر اسم تازه‌ای انتخاب می‌کردی چه اسمی بود؟
در دوستی چه چیزی را از همه مهم‌تر می‌دانی؟
آخرین چیزی که در اینترنت جست‌وجو کردی چه بود؟
یک استعداد پنهانت چیست؟
کدام فیلم یا سریال را چند بار دیده‌ای؟
اگر یک ابرقدرت ساده داشتی چه می‌خواستی؟
بامزه‌ترین لقبی که داشته‌ای چه بوده؟
کدام پیام را چند بار نوشتی و پاک کردی؟
در کودکی چه چیزی را باور داشتی که حالا خنده‌دار است؟
اگر یک قانون روزمره را حذف می‌کردی، کدام بود؟
به چه چیزی بیشتر از حد لازم اهمیت می‌دهی؟
یک چیزی که از دیگران یاد گرفته‌ای چیست؟
کدام فصل سال را بیشتر دوست داری و چرا؟
آخرین بار برای چه چیزی هیجان‌زده شدی؟
کدام کار را همیشه به تعویق می‌اندازی؟
اگر یک روز بدون اینترنت بودی چه می‌کردی؟
کدام شخصیت خیالی شبیه توست؟
دوست داری مردم چه چیزی را درباره‌ات بهتر بفهمند؟
چه چیزی باعث می‌شود به یک نفر اعتماد کنی؟
یک خرید کوچک که خیلی خوشحالت کرد چه بود؟
اگر امروز را دوباره شروع می‌کردی چه چیزی را تغییر می‌دادی؟
کدام صدای روزمره برایت آرامش‌بخش است؟
یک آرزوی ساده برای ماه آینده‌ات چیست؟
چه چیزی را هیچ‌وقت در چمدانت جا نمی‌گذاری؟
کدام بازی دوران کودکی را دوست داشتی؟
اگر یک زبان را فوری بلد می‌شدی کدام بود؟
درباره چه موضوعی می‌توانی ساعت‌ها حرف بزنی؟
وقتی خجالت می‌کشی معمولاً چه واکنشی داری؟
کدام غذای معروف را دوست نداری؟
چه چیزی در یک روز بد حالت را بهتر می‌کند؟
اگر یک روز جای کسی بودی چه کسی را انتخاب می‌کردی؟
آخرین باری که به خودت افتخار کردی چه زمانی بود؟
کدام ایموجی را بیشتر از همه استفاده می‌کنی؟
چه کاری را دوست داری با دوست‌هایت انجام بدهی؟
یک حقیقت عجیب اما راحت درباره خودت بگو.
اگر یک خاطره را قاب می‌کردی کدام بود؟
کدام بو برایت خاطره‌انگیز است؟
یک چیز کوچک که امروز بابتش ممنونی چیست؟
دوست داری در آینده چه چیزی را امتحان کنی؟""".splitlines()

GAME_DARES = """در ۱۰ ثانیه سه حیوان را با ایموجی حدس بزن و بفرست.
یک تعریف صادقانه و محترمانه از هم‌صحبتت بکن.
با سه ایموجی حال امروزت را توصیف کن.
یک جمله را مثل گوینده اخبار بنویس.
اسم یک فیلم را فقط با ایموجی نمایش بده.
یک جمله سخت یا tongue twister را تایپ کن.
در یک پیام کوتاه خودت را مثل قهرمان فیلم معرفی کن.
یک شعر چهارمصراعی خنده‌دار بساز.
اگر مایلی با دست غیرغالب شکل ساده‌ای بکش و عکسش را بفرست.
اگر مایلی یک صدای بامزه را با ویس کوتاه اجرا کن.
یک آهنگ را بدون گفتن اسمش با ایموجی معرفی کن.
در ۱۵ ثانیه پنج چیز آبی پیدا کن و اسم ببر.
یک لقب دوستانه برای خودت انتخاب کن و تا دو دور با آن جواب بده.
یک داستان دو جمله‌ای بساز که کلمه پنگوئن در آن باشد.
یک حرکت ورزشی سبک و بی‌خطر انجام بده و تعدادش را بگو.
یک جمله بساز که هر کلمه‌اش با حرف بعدی الفبا شروع شود.
یک میم معروف را با متن توصیف کن.
با سه کلمه یک شعار تبلیغاتی برای چای بساز.
یک وسیله روی میزت را بدون اطلاعات شخصی توصیف کن.
یک پیام تشویقی کوتاه برای هم‌صحبتت بنویس.
یک حیوان را با پنج کلمه توصیف کن تا طرف حدس بزند.
تا یک دور فقط با سؤال جواب بده.
یک نام هنری بامزه برای خودت انتخاب کن.
یک خاطره خوب را در حداکثر ۱۲ کلمه تعریف کن.
اگر راحتی صدای طبیعت را با ویس بازسازی کن.
با ایموجی یک غذای محبوبت را معرفی کن.
یک جمله را از آخر به اول تایپ کن.
یک پانتومیم صوتی کوتاه مثل صدای باران یا گربه اجرا کن.
اگر راحتی یک ویس کوتاه با صدای شخصیت کارتونی بفرست.
اگر مایلی عکس یک شیء معمولی اطرافت را بفرست؛ بدون چهره یا اطلاعات خصوصی.
یک حرکت رقص ساده انجام بده؛ توضیح متنی کافی است، ویدئو اختیاری است.
یک راز بی‌خطر درباره سلیقه‌ات بگو؛ اطلاعات محرمانه لازم نیست.
اگر مایلی یک آهنگ را با زمزمه کوتاه در ویس اجرا کن.
مثل گزارشگر ورزشی یک اتفاق خیالی را در ویس تعریف کن.
اگر مایلی عکس یک نقاشی فوری بفرست؛ اطلاعات شخصی در کادر نباشد.
یک پانتومیم را فقط با سه ایموجی اجرا کن.
یک حرکت کششی ساده و ایمن انجام بده؛ اگر درد داری ردش کن.
یک جمله عاشقانه خیالی و محترمانه برای شخصیت کتاب بساز.
اگر مایلی یک صدای رباتی با ویس ۵ ثانیه‌ای اجرا کن.
یک شیء روزمره را مثل گوینده حراج معرفی کن.
یک داستان ترسناک دوخطی اما بامزه تعریف کن.
اگر مایلی جمله‌ای را با لحن تریلر فیلم در ویس بگو.
یک عکس از رنگ یا بافتی جالب بفرست؛ بدون آدم یا نشانی.
با سه حرکت دست یک ورزش را توصیف کن و اسمش را بگو.
یک راز کوچک و بی‌ضرر مثل خوراکی عجیب موردعلاقه‌ات بگو.
یک جمله را با لحن شخصیت کارتونی بنویس یا ویس کن.
یک پانتومیم صوتی از وسیله‌ای مثل جاروبرقی اجرا کن.
اگر مایلی یک تبلیغ ۵ ثانیه‌ای برای آب با ویس بساز.
یک حرکت نمایشی ساده و ایمن انجام بده؛ فیلم‌گرفتن لازم نیست.
از یک شیء بی‌خطر عکس بفرست؛ پس‌زمینه قابل‌شناسایی نباشد.
یک خاطره خنده‌دار و بی‌نام تعریف کن؛ نام افراد را نگو.
اگر راحتی ویدئوی چندثانیه‌ای از حرکت دست بفرست؛ چهره و محیط نباشد.
یک پیام را با لحن ربات خدمات مشتری بنویس.
اگر مایلی با ویس صدای یک حیوان خیالی را بساز.
یک وسیله را مثل گوینده مستند حیات‌وحش توصیف کن.""".splitlines()

# question|correct|wrong1|wrong2|wrong3
GAME_QUIZ_DATA = """پایتخت ژاپن کدام است؟|توکیو|اوساکا|کیوتو|ناگویا
کدام سیاره به سیاره سرخ معروف است؟|مریخ|زهره|مشتری|عطارد
نویسنده شاهنامه کیست؟|فردوسی|سعدی|حافظ|مولوی
کدام جانور پستاندار تخم‌گذار است؟|پلاتیپوس|خفاش|دلفین|گربه
عدد اول بعد از ۷ کدام است؟|۱۱|۸|۹|۱۰
کارگردان فیلم Inception کیست؟|کریستوفر نولان|جیمز کامرون|اسپیلبرگ|تارانتینو
نماد شیمیایی O برای کدام عنصر است؟|اکسیژن|طلا|اوزون|اسمیوم
بزرگ‌ترین اقیانوس زمین کدام است؟|آرام|اطلس|هند|منجمد شمالی
در شطرنج کدام مهره L شکل حرکت می‌کند؟|اسب|فیل|رخ|وزیر
کدام ساز معمولاً شش سیم دارد؟|گیتار|فلوت|تار|پیانو
کدام کشور شکل چکمه دارد؟|ایتالیا|یونان|پرتغال|نروژ
حاصل ۱۲ ضربدر ۸ چند است؟|۹۶|۸۶|۱۰۶|۹۸
سیمبا شخصیت کدام انیمیشن است؟|The Lion King|Finding Nemo|Shrek|Up
آب در فشار معمول در چند درجه می‌جوشد؟|۱۰۰|۹۰|۸۰|۱۲۰
کدام یک قمر طبیعی زمین است؟|ماه|فوبوس|تیتان|اروپا
مدرسه جادوگری هری پاتر چه نام دارد؟|هاگوارتز|نارنیا|کمپ نیمه‌خون|آرکامه
ترکیب آبی و زرد چه رنگی می‌سازد؟|سبز|بنفش|نارنجی|قرمز
سریع‌ترین حیوان خشکی کدام است؟|یوزپلنگ|شیر|اسب|شترمرغ
اهرام جیزه در کدام کشورند؟|مصر|مکزیک|هند|عراق
واحد اندازه‌گیری جریان برق چیست؟|آمپر|ولت|وات|اهم
شرلوک هولمز را چه کسی خلق کرد؟|آرتور کانن دویل|آگاتا کریستی|ادگار آلن پو|ژول ورن
کدام اندام خون را پمپاژ می‌کند؟|قلب|ریه|کبد|کلیه
عدد رومی X چند است؟|۱۰|۵|۵۰|۱۰۰
جک اسپارو در کدام فیلم است؟|Pirates of the Caribbean|Titanic|Avatar|Gladiator
بیشترین سهم جو زمین متعلق به کدام گاز است؟|نیتروژن|اکسیژن|دی‌اکسیدکربن|هیدروژن
یک بایت چند بیت است؟|۸|۴|۱۶|۳۲
نقاش مونالیزا کیست؟|لئوناردو داوینچی|ون‌گوگ|پیکاسو|مونه""".splitlines()
GAME_ICE = """اگر امروز یک لقب برای حال‌وهوایت انتخاب کنی چیست؟
بین سفر به کوه و دریا کدام را انتخاب می‌کنی؟
یک غذای خوشمزه که همه باید امتحان کنند چیست؟
اگر یک روز تعطیل اضافه داشتی چه می‌کردی؟
چای یا قهوه؟ با یک دلیل بامزه.
یک آهنگ برای تیتراژ ورودت انتخاب کن.
اگر حیوان خانگی خیالی داشتی چه حیوانی بود؟
دو حقیقت و یک دروغ درباره سلیقه‌ات بگو.
کدام شهر را دوست داری یک بار ببینی؟
یک فیلم برای تماشای دونفره پیشنهاد بده.
اگر در یک مهارت حرفه‌ای می‌شدی کدام بود؟
صبح زود یا شب‌بیداری؟
سه ایموجی بفرست که یک خاطره را نشان دهند.
یک خوراکی برای آخر شب انتخاب کن.
اگر ماشین زمان داشتی گذشته یا آینده؟
کدام بازی را برای آشنایی با یک نفر پیشنهاد می‌کنی؟
یک سؤال غیرمعمول اما بی‌خطر از من بپرس.
اگر کافه‌ای داشتی اسمش چه بود؟
بهترین فصل برای شروع ماجراجویی کدام است؟
تاس مجازی: عددی از ۱ تا ۶ انتخاب کن و یک سؤال بپرس.
سنگ، کاغذ، قیچی: یکی را انتخاب کنید و هم‌زمان بفرستید.
یک واژه بگو تا هر دو با آن داستان بسازید.
حدس بزن من امروز چه خورده‌ام؛ بعد نوبت تو.
هر کدام فیلمی با حرف آخر فیلم قبلی نام ببرید.
یک سؤال بله/خیر بپرس که جوابش غافلگیرت کند.
اگر فقط یک اپلیکیشن می‌ماند کدام را نگه می‌داشتی؟
بین قدرت پرواز و تلپورت کدام را انتخاب می‌کنی؟
با یک ایموجی موضوع گفتگوی بعدی را انتخاب کن.""".splitlines()


class GameModule:
    FREE_SKIPS = 2
    SKIP_COST = 10
    GAME_SECONDS = 20
    GENDER_COST = 100

    def __init__(self, db_path, owner_id):
        self.lock = threading.RLock()
        self.owner_id = int(owner_id)
        self.db = sqlite3.connect(db_path, check_same_thread=False, timeout=20)
        self.db.row_factory = sqlite3.Row
        self.db.execute("PRAGMA busy_timeout=20000")
        self.db.executescript("""
        CREATE TABLE IF NOT EXISTS gm_ideas(id INTEGER PRIMARY KEY,kind TEXT,category TEXT,prompt TEXT,
          options TEXT,answer INTEGER,bold INTEGER DEFAULT 0,enabled INTEGER DEFAULT 1,
          reward_enabled INTEGER DEFAULT 1);
        CREATE TABLE IF NOT EXISTS gm_sessions(id INTEGER PRIMARY KEY AUTOINCREMENT,pair_key TEXT,
          actor INTEGER,partner INTEGER,idea_id INTEGER,status TEXT,created REAL,expires REAL,result TEXT);
        CREATE UNIQUE INDEX IF NOT EXISTS gm_one_live_pair ON gm_sessions(pair_key)
          WHERE status IN ('active','verify');
        CREATE TABLE IF NOT EXISTS gm_scores(user_id INTEGER PRIMARY KEY,points INTEGER DEFAULT 0);
        CREATE TABLE IF NOT EXISTS gm_awards(session_id INTEGER,user_id INTEGER,reason TEXT,
          points INTEGER,created REAL,PRIMARY KEY(session_id,user_id,reason));
        CREATE TABLE IF NOT EXISTS gm_skips(pair_key TEXT,user_id INTEGER,free_used INTEGER DEFAULT 0,
          credits INTEGER DEFAULT 0,PRIMARY KEY(pair_key,user_id));
        CREATE TABLE IF NOT EXISTS gm_prefs(user_id INTEGER PRIMARY KEY,gender TEXT,expires REAL);
        """)
        idea_cols = {r[1] for r in self.db.execute("PRAGMA table_info(gm_ideas)")}
        if "reward_enabled" not in idea_cols:
            self.db.execute("ALTER TABLE gm_ideas ADD COLUMN reward_enabled INTEGER NOT NULL DEFAULT 1")
        ideas = []
        for p in GAME_TRUTHS:
            ideas.append(("truth", "جرأت و حقیقت", p, None, None, 0))
        for i, p in enumerate(GAME_DARES):
            ideas.append(("dare", "جرأت و حقیقت", p, None, None, int(i >= 27)))
        for line in GAME_QUIZ_DATA:
            q, correct, *wrong = line.split("|")
            options = list(wrong) + [correct]
            random.shuffle(options)
            ideas.append(("quiz", "کوییز", q, json.dumps(options, ensure_ascii=False), options.index(correct), 0))
        for p in GAME_ICE:
            ideas.append(("ice", "سرگرمی و یخ‌شکن", p, None, None, 0))
        if (len(GAME_TRUTHS), len(GAME_DARES), len(GAME_QUIZ_DATA), len(GAME_ICE), len(ideas)) != (55,55,27,28,165):
            raise RuntimeError("کاتالوگ بازی باید دقیقاً شامل ۱۶۵ ایده باشد.")
        with self.lock:
            for i, row in enumerate(ideas, 1):
                self.db.execute("INSERT OR IGNORE INTO gm_ideas(id,kind,category,prompt,options,answer,bold,enabled,reward_enabled) VALUES(?,?,?,?,?,?,?,1,1)", (i, *row))
            self.db.commit()
        self._stop = threading.Event()
        threading.Thread(target=self._timer, daemon=True, name="game-expiry").start()

    def close(self):
        self._stop.set()
        with self.lock:
            self.db.close()

    def keyboard_row(self):
        row=[]
        if S("btn_game")=="1": row.append({"text":"🎲 چالش ناشناس"})
        if S("btn_leaderboard")=="1": row.append({"text":"🏆 برترین‌های هفته"})
        if S("btn_shop")=="1": row.append({"text":"🛍 فروشگاه امتیاز"})
        return row

    def admin_button(self):
        return ("🎮 مدیریت چالش‌ها", "gm:admin")

    @staticmethod
    def _pair(a, b):
        return ":".join(map(str, sorted((int(a), int(b)))))

    @staticmethod
    def _kb(rows):
        return {"inline_keyboard":[[{"text":t,"callback_data":d} for t,d in row] for row in rows]}

    def _send(self, chat, text, kb=None):
        return send(chat, text, kb)

    def _answer(self, cb, text=""):
        api("answerCallbackQuery", {"callback_query_id": cb.get("id"), "text": text})

    def _idea(self, exclude=None):
        with self.lock:
            rows = self.db.execute("SELECT * FROM gm_ideas WHERE enabled=1 AND (? IS NULL OR id<>?)",
                                   (exclude, exclude)).fetchall()
            if not rows and exclude is not None:
                rows = self.db.execute("SELECT * FROM gm_ideas WHERE enabled=1").fetchall()
        return random.choice(rows) if rows else None

    def handle_message(self, m, partner_id):
        text = (m.get("text") or "").strip()
        uid = m["from"]["id"]
        if text in ("🎲 چالش ناشناس", "/game", "/challenge"):
            if not partner_id:
                send(uid, "برای بازی اول به یک هم‌صحبت وصل شو.")
            else:
                self.start(uid, int(partner_id))
            return True
        if text in ("🏆 برترین‌های هفته", "/leaderboard", "/top"):
            self.leaderboard(uid)
            return True
        if text in ("🛍 فروشگاه امتیاز", "/shop"):
            self.shop(uid)
            return True
        return False

    def start(self, actor, partner):
        if actor == partner:
            return False
        idea = self._idea()
        if not idea:
            send(actor, "فعلاً چالش فعالی موجود نیست.")
            return False
        pair = self._pair(actor, partner)
        now = time.time()
        try:
            with self.lock:
                cur = self.db.execute("INSERT INTO gm_sessions(pair_key,actor,partner,idea_id,status,created,expires) VALUES(?,?,?,?,?,?,?)",
                    # actor is the challenged player, partner is the player who
                    # requested the challenge. This keeps quiz/skip/verification
                    # permissions aligned with the person who must respond.
                    (pair, partner, actor, idea["id"], "active", now,
                     now + self.GAME_SECONDS if idea["kind"] == "quiz" else None))
                sid = cur.lastrowid
                self.db.commit()
        except sqlite3.IntegrityError:
            send(actor, "برای این گفتگوی دونفره هنوز یک بازی فعال است.")
            return False
        code=active_chat_code(actor)
        log_chat_event(code,actor,"game_challenge_requested",f"idea_id={idea['id']}")
        log_chat_event(code,partner,"game_challenge_received",f"idea_id={idea['id']}")
        self.deliver(sid, idea)
        return True

    def _session(self, sid):
        with self.lock:
            return self.db.execute("SELECT s.*,i.kind,i.prompt,i.options,i.answer,i.enabled,i.bold,i.reward_enabled "
                "FROM gm_sessions s JOIN gm_ideas i ON i.id=s.idea_id WHERE s.id=?", (sid,)).fetchone()

    def deliver(self, sid, idea):
        row = self._session(sid)
        actor, partner = row["actor"], row["partner"]
        if idea["kind"] == "quiz":
            options = json.loads(idea["options"])
            kb = self._kb([[(f"{i+1}. {v}", f"gm:q:{sid}:{i}")] for i,v in enumerate(options)])
            shared = f"🧠 کوییز ({self.GAME_SECONDS} ثانیه)\n{idea['prompt']}\n\nاین چالش برای هر دو طرف قابل مشاهده است."
            send(actor, shared, kb)
            send(partner, shared, kb)
            return
        label = {"truth":"حقیقت","dare":"جرأت","ice":"یخ‌شکن"}[idea["kind"]]
        kb = self._kb([[("✅ انجام دادم / پاسخ دادم",f"gm:done:{sid}:{idea['id']}"),
                        ("⏭️ رد کردن",f"gm:skip:{sid}:{idea['id']}")],
                       [("🏳️ انصراف",f"gm:cancel:{sid}:{idea['id']}")]])
        shared = f"🎲 چالش {label}: {idea['prompt']}\n\nاین چالش برای هر دو طرف قابل مشاهده است. ارسال عکس/صدا/ویدئو اختیاری است؛ اطلاعات خصوصی نفرست و هر زمان خواستی انصراف بده."
        send(actor, shared, kb)
        send(partner, shared, kb)

    def _award(self, sid, uid, pts, reason):
        with self.lock:
            self.db.execute("INSERT OR IGNORE INTO gm_scores(user_id,points) VALUES(?,0)", (uid,))
            cur = self.db.execute("INSERT OR IGNORE INTO gm_awards VALUES(?,?,?,?,?)",
                                  (sid,uid,reason,pts,time.time()))
            if cur.rowcount:
                self.db.execute("UPDATE gm_scores SET points=points+? WHERE user_id=?", (pts,uid))
            self.db.commit()

    def _balance(self, uid):
        with self.lock:
            r = self.db.execute("SELECT points FROM gm_scores WHERE user_id=?", (uid,)).fetchone()
        return int(r[0]) if r else 0

    def _finish_quiz(self, row, correct):
        with self.lock:
            cur = self.db.execute("UPDATE gm_sessions SET status=?,result=? WHERE id=? AND status='active'",
                ("done" if correct else "failed", "correct" if correct else "wrong", row["id"]))
            self.db.commit()
        if not cur.rowcount:
            return
        if correct and row["reward_enabled"]:
            reward = max(0, int(S("game_reward") or 10))
            self._award(row["id"],row["actor"],reward,"quiz")
            result = f"✅ درست بود! +{reward} امتیاز. پاسخ: {json.loads(row['options'])[row['answer']]}"
        elif correct:
            result = f"✅ درست بود! برای این کوییز امتیازی تعریف نشده. پاسخ: {json.loads(row['options'])[row['answer']]}"
        else:
            result = f"❌ پاسخ اشتباه بود؛ امتیازی نگرفتی. پاسخ درست: {json.loads(row['options'])[row['answer']]}"
        send(row["actor"],result); send(row["partner"],result)

    def _expire(self, sid):
        row = self._session(sid)
        if not row or row["status"] != "active" or not row["expires"] or row["expires"] > time.time():
            return
        with self.lock:
            cur = self.db.execute("UPDATE gm_sessions SET status='expired',result='timeout' WHERE id=? AND status='active' AND expires<=?",
                                  (sid,time.time()))
            self.db.commit()
        if cur.rowcount:
            answer = json.loads(row["options"])[row["answer"]]
            msg = f"⏰ زمان تمام شد؛ امتیازی داده نشد. پاسخ: {answer}"
            send(row["actor"],msg); send(row["partner"],msg)

    def _timer(self):
        while not self._stop.wait(2):
            try:
                with self.lock:
                    ids = [r[0] for r in self.db.execute("SELECT id FROM gm_sessions WHERE status='active' AND expires IS NOT NULL AND expires<=?",(time.time(),))]
                for sid in ids:
                    self._expire(sid)
            except Exception as e:
                print("game timer error:",repr(e),file=sys.stderr)

    def _skip(self, row, uid):
        pair = row["pair_key"]
        skip_cost = max(0, int(S("game_skip_cost") or self.SKIP_COST))
        with self.lock:
            self.db.execute("BEGIN IMMEDIATE")
            latest = self.db.execute("SELECT status,idea_id FROM gm_sessions WHERE id=?",(row["id"],)).fetchone()
            if not latest or latest["status"]!="active" or latest["idea_id"]!=row["idea_id"]:
                self.db.rollback()
                send(uid,"این چالش دیگر فعال نیست.")
                return
            self.db.execute("INSERT OR IGNORE INTO gm_skips(pair_key,user_id) VALUES(?,?)",(pair,uid))
            rec = self.db.execute("SELECT free_used,credits FROM gm_skips WHERE pair_key=? AND user_id=?",(pair,uid)).fetchone()
            paid = False
            if rec["free_used"] < self.FREE_SKIPS:
                self.db.execute("UPDATE gm_skips SET free_used=free_used+1 WHERE pair_key=? AND user_id=?",(pair,uid))
            elif rec["credits"] > 0:
                self.db.execute("UPDATE gm_skips SET credits=credits-1 WHERE pair_key=? AND user_id=?",(pair,uid)); paid="credit"
            else:
                wallet = self.db.execute("SELECT credits FROM gm_skips WHERE pair_key='*' AND user_id=?",(uid,)).fetchone()
                if wallet and wallet["credits"] > 0:
                    self.db.execute("UPDATE gm_skips SET credits=credits-1 WHERE pair_key='*' AND user_id=?",(uid,)); paid="credit"
                elif self._balance(uid) >= skip_cost:
                    self.db.execute("UPDATE gm_scores SET points=points-? WHERE user_id=?",(skip_cost,uid)); paid=True
                else:
                    self.db.commit(); send(uid,f"رد رایگان تمام شده؛ رد بعدی {skip_cost} امتیاز است."); return
            idea = self._idea(row["idea_id"])
            if not idea:
                self.db.rollback(); send(uid,"چالش دیگری فعال نیست."); return
            self.db.execute("UPDATE gm_sessions SET idea_id=?,status='active',expires=?,result=NULL WHERE id=? AND status='active'",
                (idea["id"], time.time()+self.GAME_SECONDS if idea["kind"]=="quiz" else None,row["id"]))
            self.db.commit()
        send(row["partner"],"⏭ هم‌صحبتت چالش را رد کرد؛ چالش تازه‌ای انتخاب شد.")
        send(uid,"⏭ رد رایگان ثبت شد." if paid is False else ("⏭ یک اعتبار اضافه خرج شد." if paid=="credit" else f"⏭ {skip_cost} امتیاز خرج شد."))
        self.deliver(row["id"],idea)

    def handle_callback(self, cb):
        data = (cb.get("data") or "").split(":")
        if len(data)<2 or data[0]!="gm":
            return False
        uid = int(cb["from"]["id"])
        action=data[1]
        if action in ("admin","adm") and uid!=self.owner_id:
            self._answer(cb,"دسترسی ندارید"); return True
        self._answer(cb)
        if action=="admin":
            self.show_admin(uid); return True
        if action=="adm":
            self.admin_action(uid,data[2:]); return True
        if action=="shop":
            self.shop_action(uid,data[2:]); return True
        if action=="q" and len(data)>=4:
            row=self._session(int(data[2]))
            if row and row["actor"]==uid and row["kind"]=="quiz" and row["status"]=="active":
                if row["expires"]<=time.time(): self._expire(row["id"])
                else: self._finish_quiz(row,int(data[3])==row["answer"])
            return True
        if len(data)<3: return True
        sid=int(data[2]); row=self._session(sid)
        if not row: send(uid,"این بازی دیگر فعال نیست."); return True
        idea_id=int(data[3]) if len(data)>3 and data[3].isdigit() else row["idea_id"]
        if idea_id != row["idea_id"]: send(uid,"این دکمه مربوط به چالش قبلی است."); return True
        if row["expires"] and row["expires"]<=time.time(): self._expire(sid); return True
        if action=="cancel":
            if uid not in (row["actor"],row["partner"]): return True
            with self.lock:
                self.db.execute("UPDATE gm_sessions SET status='cancelled' WHERE id=? AND status IN ('active','verify')",(sid,)); self.db.commit()
            send(row["actor"],"🏳️ بازی لغو شد."); send(row["partner"],"🏳️ بازی لغو شد."); return True
        if action=="done" and uid==row["actor"] and row["status"]=="active" and row["kind"]!="quiz":
            with self.lock:
                cur=self.db.execute("UPDATE gm_sessions SET status='verify' WHERE id=? AND status='active'",(sid,)); self.db.commit()
            if cur.rowcount:
                reward = max(0, int(S("game_reward") or 10))
                kb=self._kb([[ (f"👍 تأیید (+{reward} امتیاز)",f"gm:verify:{sid}:yes:{idea_id}"),("👎 رد تأیید",f"gm:verify:{sid}:no:{idea_id}")]])
                send(row["partner"],"آیا هم‌صحبت شما چالش را درست انجام داد؟",kb)
                send(row["actor"],"✅ پاسخ ثبت شد؛ منتظر تأیید هم‌صحبتت باش.")
            return True
        if action=="skip" and uid==row["actor"] and row["status"]=="active" and row["kind"]!="quiz":
            self._skip(row,uid); return True
        if action=="verify" and uid==row["partner"] and row["status"]=="verify":
            if len(data)>4 and data[4].isdigit() and int(data[4])!=row["idea_id"]:
                send(uid,"این تأیید مربوط به چالش قبلی است."); return True
            yes=data[3]=="yes"
            with self.lock:
                cur=self.db.execute("UPDATE gm_sessions SET status=?,result=? WHERE id=? AND status='verify'",
                    ("done" if yes else "rejected","approved" if yes else "rejected",sid)); self.db.commit()
            if cur.rowcount and yes and row["reward_enabled"]:
                self._award(sid,row["actor"],max(0,int(S("game_reward") or 10)),"verified")
            msg=(f"👍 تأیید شد؛ {max(0,int(S('game_reward') or 10))} امتیاز رسید!"
                 if yes and row["reward_enabled"] else
                 ("👍 تأیید شد؛ امتیازدهی این چالش خاموش است." if yes else "👎 تأیید نشد؛ امتیازی داده نشد."))
            send(row["actor"],msg); send(row["partner"],msg); return True
        return True

    def leaderboard(self, uid):
        with self.lock:
            rows=self.db.execute("SELECT user_id,SUM(points) p FROM gm_awards WHERE created>=? GROUP BY user_id ORDER BY p DESC LIMIT 10",(time.time()-7*86400,)).fetchall()
        if not rows: send(uid,"🏆 جدول هفتگی خالی است؛ یک چالش بازی کن."); return
        send(uid,"🏆 برترین‌های ۷ روز اخیر\n"+"\n".join(
            f"{i}. {nickname(r['user_id']) or 'بازیکن'} · {r['p']} امتیاز"
            for i,r in enumerate(rows,1)))

    def shop(self, uid):
        gender_cost = int(S("game_gender_cost") or 100)
        skip_pack_cost = max(0, int(S("game_skip_cost") or self.SKIP_COST)) * 3
        kb=self._kb([[ (f"🎫 انتخاب جنسیت · {gender_cost} امتیاز", "gm:shop:gender")],
                     [(f"⏭ خرید ۳ رد اضافه · {skip_pack_cost} امتیاز", "gm:shop:skip")]])
        send(uid,f"🛍 امتیاز: {self._balance(uid)}\nانتخاب جنسیت ۷ روز فعال می‌ماند؛ اعمال آن به matcher نیاز دارد.",kb)

    def shop_action(self,uid,args):
        if not args: return self.shop(uid)
        if args[0]=="gender":
            send(uid,"ترجیح را انتخاب کن:",self._kb([[("زن","gm:shop:pref:female"),("مرد","gm:shop:pref:male"),("بدون ترجیح","gm:shop:pref:any")]]))
        elif args[0]=="pref" and len(args)>1:
            pref=args[1]
            with self.lock:
                self.db.execute("BEGIN IMMEDIATE")
                cost = max(0, int(S("game_gender_cost") or self.GENDER_COST))
                if self._balance(uid)<cost:
                    self.db.rollback(); send(uid,"امتیاز کافی نیست."); return
                self.db.execute("UPDATE gm_scores SET points=points-? WHERE user_id=?",(cost,uid))
                self.db.execute("INSERT INTO gm_prefs VALUES(?,?,?) ON CONFLICT(user_id) DO UPDATE SET gender=excluded.gender,expires=excluded.expires",
                                (uid,pref,time.time()+7*86400)); self.db.commit()
            send(uid,"✅ ترجیح ۷ روزه ثبت شد؛ برای اعمال، matcher باید آن را بخواند.")
        elif args[0]=="skip":
            pack_cost = max(0, int(S("game_skip_cost") or self.SKIP_COST)) * 3
            with self.lock:
                self.db.execute("BEGIN IMMEDIATE")
                if self._balance(uid)<pack_cost: self.db.rollback(); send(uid,f"{pack_cost} امتیاز لازم است."); return
                self.db.execute("UPDATE gm_scores SET points=points-? WHERE user_id=?",(pack_cost,uid))
                self.db.execute("INSERT INTO gm_skips VALUES('*',?,0,3) ON CONFLICT(pair_key,user_id) DO UPDATE SET credits=credits+3",(uid,))
                self.db.commit()
            send(uid,"✅ سه رد اضافه به کیف پولت اضافه شد.")

    def get_match_preference(self,uid):
        with self.lock: row=self.db.execute("SELECT gender,expires FROM gm_prefs WHERE user_id=?",(uid,)).fetchone()
        return row["gender"] if row and row["expires"]>time.time() else "any"

    def matching_allowed(self,a,gender_a,b,gender_b):
        x,y=self.get_match_preference(a),self.get_match_preference(b)
        return (x=="any" or x==gender_b) and (y=="any" or y==gender_a)

    def show_admin(self,uid,page=0):
        if uid!=self.owner_id: return
        with self.lock:
            rows=self.db.execute("SELECT id,kind,prompt,enabled,bold,reward_enabled FROM gm_ideas ORDER BY id LIMIT 8 OFFSET ?",(page*8,)).fetchall()
            enabled=self.db.execute("SELECT COUNT(*) FROM gm_ideas WHERE enabled=1").fetchone()[0]
        kb=[]
        for r in rows:
            kb.append([(f"{'✅' if r['enabled'] else '⛔'} {r['id']} {'🔥' if r['bold'] else ''} {r['prompt'][:18]}",
                        f"gm:adm:toggle:{r['id']}:{page}"),
                       (f"{'💰امتیاز' if r['reward_enabled'] else '🚫بدون امتیاز'}",
                        f"gm:adm:reward:{r['id']}:{page}")])
        nav=[]
        if page: nav.append(("◀️ قبلی",f"gm:adm:page:{page-1}"))
        nav.extend([("📊 آمار","gm:adm:stats"),("دسته‌ها","gm:adm:cats")])
        if page<20: nav.append(("بعدی ▶️",f"gm:adm:page:{page+1}"))
        kb.append(nav); kb.append([("🏆 برترین‌ها","gm:adm:top")])
        send(uid,f"🎮 مدیریت چالش‌ها · فعال {enabled}/165 · صفحه {page+1}/21",self._kb(kb))

    def admin_action(self,uid,args):
        if not args: return self.show_admin(uid)
        if args[0]=="page": return self.show_admin(uid,int(args[1]))
        if args[0]=="toggle":
            with self.lock:
                self.db.execute("UPDATE gm_ideas SET enabled=1-enabled WHERE id=?",(int(args[1]),)); self.db.commit()
            return self.show_admin(uid,int(args[2]))
        if args[0]=="reward":
            with self.lock:
                self.db.execute("UPDATE gm_ideas SET reward_enabled=1-reward_enabled WHERE id=?",(int(args[1]),))
                self.db.commit()
            return self.show_admin(uid,int(args[2]))
        if args[0]=="cats":
            send(uid,"دسته‌ها: «همه» ۱۶۵، جرأت‌وحقیقت ۱۱۰، کوییز ۲۷، یخ‌شکن ۲۸.\nبرای دیدن/فعال‌سازی از فهرست صفحه‌ای استفاده کن.")
        elif args[0]=="top": self.leaderboard(uid)
        elif args[0]=="stats":
            with self.lock:
                counts={r["status"]:r["n"] for r in self.db.execute("SELECT status,COUNT(*) n FROM gm_sessions GROUP BY status")}
                winners=self.db.execute("SELECT user_id,points FROM gm_scores ORDER BY points DESC LIMIT 5").fetchall()
                on=self.db.execute("SELECT COUNT(*) FROM gm_ideas WHERE enabled=1").fetchone()[0]
            send(uid,f"📊 بازی‌های تکمیل‌شده: {counts.get('done',0)}\nایده‌های فعال: {on}/165\nبرترین امتیازها: "+
                 ", ".join(f"{nickname(r['user_id']) or 'بازیکن'} ({r['points']})" for r in winners))


# ───────────────────────── 10) حلقه‌ی اصلی ─────────────────────────
def handle_update(upd):
    update_id = upd.get("update_id")
    if update_id is not None:
        with _processed_updates_lock:
            if update_id in _processed_updates:
                return
            _processed_updates.add(update_id)
            if len(_processed_updates) > _MAX_PROCESSED_UPDATES:
                _processed_updates.pop()
    try:
        bump("requests")
        with LOCK:
            DB.execute("INSERT INTO daily_requests(day,count) VALUES(?,1) "
                       "ON CONFLICT(day) DO UPDATE SET count=count+1",
                       (now().strftime("%Y-%m-%d"),))
            DB.commit()
    except Exception as exc:
        print("request counter error:", repr(exc), file=sys.stderr)
    try:
        if "callback_query" in upd:
            on_callback(upd["callback_query"])
        elif "message" in upd:
            m = upd["message"]
            if m.get("chat", {}).get("type") != "private" or "from" not in m:
                return
            uid = m["from"]["id"]
            touch(uid)
            with user_lock(uid):               # ترتیب پیام‌های هر کاربر حفظ می‌شود
                if uid == OWNER_ID:
                    t = (m.get("text") or "").strip()
                    if owner_is_user():
                        if t in ("/panel", "/admin") or (L_ADMIN in t and len(t) < 40):
                            set_owner_mode("admin")
                        else:
                            safe_user_message(m)
                    else:
                        safe_owner_message(m)
                else:
                    safe_user_message(m)
    except Exception as e:
        report_exception("update dispatcher", e)



# ───────────────────────── پنل وب مدیریتی موبایل ─────────────────────────
def start_web_panel():
    """پنل وب سبک با دیتابیس مشترک؛ فقط با رمز مستقل پنل فعال می‌شود."""
    import html
    from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
    from urllib.parse import parse_qs

    panel_password = os.environ.get("ADMIN_PANEL_PASSWORD", "")
    if len(panel_password) < 12:
        print("پنل وب خاموش است: در Railway متغیر ADMIN_PANEL_PASSWORD با حداقل ۱۲ نویسه تنظیم کنید.")
        return
    secret = hashlib.sha256((panel_password + "|irconfig-anon-panel-v1").encode()).digest()
    csrf = hmac.new(secret, b"csrf", hashlib.sha256).hexdigest()
    cookie_value = hmac.new(secret, b"admin-session", hashlib.sha256).hexdigest()

    def esc(v): return html.escape(str(v if v is not None else ""), quote=True)
    def page(body, title="پنل مدیریت ربات"):
        return ("<!doctype html><html lang='fa' dir='rtl'><meta charset='utf-8'>"
          "<meta name='viewport' content='width=device-width,initial-scale=1,viewport-fit=cover'>"
          "<meta name='color-scheme' content='light dark'><title>"+esc(title)+"</title><style>"
          "*{box-sizing:border-box}body{margin:0;background:#f3f5f9;color:#182230;font:15px system-ui,Tahoma,sans-serif}"
          ".wrap{max-width:900px;margin:auto;padding:14px}.top{background:#172554;color:white;padding:18px;border-radius:18px;margin-bottom:12px}"
          ".card{background:white;border:1px solid #e3e8ef;border-radius:16px;padding:15px;margin:10px 0;overflow-wrap:anywhere}"
          "h1{font-size:21px;margin:0 0 6px}h2{font-size:17px;margin:0 0 12px}small,.muted{color:#64748b}"
          "input,textarea,select{width:100%;padding:11px;border:1px solid #cbd5e1;border-radius:10px;margin:5px 0 10px;font:inherit}"
          "textarea{min-height:95px}button,.btn{display:inline-block;border:0;background:#1d4ed8;color:white;padding:10px 13px;border-radius:10px;font:inherit;text-decoration:none;cursor:pointer;margin:3px 0}"
          ".danger{background:#b91c1c}.soft{background:#e2e8f0;color:#172033}.nav{display:flex;gap:6px;flex-wrap:wrap;margin:8px 0}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:8px}"
          ".stat{background:#eff6ff;border-radius:12px;padding:12px}.stat b{font-size:22px;display:block}table{width:100%;border-collapse:collapse}td,th{text-align:right;padding:8px;border-bottom:1px solid #e2e8f0;font-size:13px}"
          "form.inline{display:inline-block;margin:0}.pill{font-size:12px;background:#dbeafe;padding:4px 8px;border-radius:20px}"
          "@media(prefers-color-scheme:dark){body{background:#0b1220;color:#e5e7eb}.card{background:#111c2e;border-color:#28364c}.muted,small{color:#9ca3af}input,textarea,select{background:#0b1220;color:#e5e7eb;border-color:#475569}.stat{background:#172554}td,th{border-color:#28364c}.soft{background:#334155;color:#fff}}"
          "</style><div class='wrap'><header class='top'><h1>🛠 پنل مدیریت ربات</h1><div>اتصال به دیتابیس اصلی • مناسب گوشی</div></header>"+body+"</div></html>")

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *args): pass
        def authed(self):
            return ("panel_session="+cookie_value) in self.headers.get("Cookie", "")
        def send_html(self, text, status=200, cookie=None):
            data=text.encode('utf-8'); self.send_response(status)
            self.send_header('Content-Type','text/html; charset=utf-8'); self.send_header('Content-Length',str(len(data)))
            self.send_header('Cache-Control','no-store'); self.send_header('X-Content-Type-Options','nosniff'); self.send_header('X-Frame-Options','DENY'); self.send_header('Referrer-Policy','no-referrer')
            if cookie: self.send_header('Set-Cookie',cookie)
            self.end_headers(); self.wfile.write(data)
        def form(self):
            n=int(self.headers.get('Content-Length','0'))
            if n>20000: return {}
            return {k:v[0] for k,v in parse_qs(self.rfile.read(n).decode('utf-8','replace')).items()}
        def do_GET(self):
            if self.path == '/health': return self.send_html('ok')
            if not self.authed():
                body="<section class='card'><h2>ورود مدیر</h2><p class='muted'>رمز پنل را وارد کن. این رمز با رمز ربات فرق دارد.</p><form method='post' action='/login'><input type='password' name='password' required autocomplete='current-password' placeholder='رمز پنل'><button>ورود امن</button></form></section>"
                return self.send_html(page(body))
            try:
                conn=sqlite3.connect(DB_PATH,timeout=10); conn.row_factory=sqlite3.Row
                total=conn.execute('SELECT COUNT(*) n FROM users').fetchone()['n']
                banned=conn.execute('SELECT COUNT(*) n FROM users WHERE banned=1').fetchone()['n']
                active=conn.execute("SELECT COUNT(*) n FROM users WHERE last_seen >= ?",((datetime.now()-timedelta(days=1)).isoformat(),)).fetchone()['n']
                sessions=conn.execute('SELECT COUNT(*) n FROM chat_sessions WHERE active=1').fetchone()['n']
                reports=conn.execute("SELECT COUNT(*) n FROM complaint_reports WHERE status='open'").fetchone()['n']
                q=parse_qs(self.path.split('?',1)[1]) if '?' in self.path else {}
                search=(q.get('q',[''])[0])[:80]
                users=conn.execute('SELECT uid,username,nickname,banned,warns,last_seen FROM users WHERE CAST(uid AS TEXT) LIKE ? OR COALESCE(username,\'\') LIKE ? OR COALESCE(nickname,\'\') LIKE ? ORDER BY last_seen DESC LIMIT 40',('%'+search+'%','%'+search+'%','%'+search+'%')).fetchall()
                reps=conn.execute('SELECT id,code,reporter,accused,reason,details,status,created FROM complaint_reports ORDER BY CASE status WHEN \'open\' THEN 0 ELSE 1 END,created DESC LIMIT 30').fetchall()
                replies=conn.execute('SELECT id,keyword,response,enabled FROM auto_replies ORDER BY id DESC LIMIT 40').fetchall()
                settings=conn.execute('SELECT k,v FROM settings ORDER BY k').fetchall(); conn.close()
            except Exception as e:
                return self.send_html(page("<section class='card'>خواندن دیتابیس ناموفق بود. مسیر DB_PATH و لاگ Railway را بررسی کن؛ داده‌ای پاک نشده.</section>"),500)
            nav="<nav class='nav'><a class='btn soft' href='/'>داشبورد</a><a class='btn soft' href='#users'>کاربران</a><a class='btn soft' href='#reports'>گزارش‌ها</a><a class='btn soft' href='#broadcast'>پیام همگانی</a><a class='btn soft' href='#settings'>تنظیمات</a><form class='inline' method='post' action='/logout'><input type='hidden' name='csrf' value='"+csrf+"'><button class='danger'>خروج</button></form></nav>"
            body=nav+"<section class='card'><h2>آمار واقعی</h2><div class='grid'>"+''.join("<div class='stat'><small>"+a+"</small><b>"+str(v)+"</b></div>" for a,v in [('کل کاربران',total),('فعال در ۲۴ ساعت',active),('مسدودشده',banned),('چت فعال',sessions),('گزارش باز',reports)])+"</div></section>"
            body+="<section id='users' class='card'><h2>کاربران</h2><form method='get'><input name='q' value='"+esc(search)+"' placeholder='شناسه، نام کاربری یا لقب'><button>جست‌وجو</button></form><div style='overflow:auto'><table><tr><th>شناسه / نام</th><th>وضعیت</th><th>عملیات</th></tr>"
            for u in users:
                body+="<tr><td>"+esc(u['uid'])+"<br>"+esc(u['username'] or u['nickname'] or '—')+"<br><small>اخطار: "+esc(u['warns'])+"</small></td><td>"+('مسدود' if u['banned'] else 'فعال')+"</td><td><form method='post' action='/ban'><input type='hidden' name='csrf' value='"+csrf+"'><input type='hidden' name='uid' value='"+esc(u['uid'])+"'><input type='hidden' name='ban' value='"+('0' if u['banned'] else '1')+"'><button class='"+('soft' if u['banned'] else 'danger')+"'>"+('رفع مسدودی' if u['banned'] else 'مسدودسازی')+"</button></form></td></tr>"
            body+="</table></div><small>حداکثر ۴۰ نتیجه در هر جست‌وجو نمایش داده می‌شود.</small></section>"
            body+="<section id='reports' class='card'><h2>گزارش‌ها و شکایت‌ها</h2>"
            for r in reps:
                body+="<article class='card'><b>#"+esc(r['id'])+" · "+esc(r['reason'])+"</b><p>گزارش‌دهنده: "+esc(r['reporter'])+" | شناسه گزارش‌شده: "+esc(r['accused'])+"</p><p>"+esc(r['details'])+"</p><small>کد چت: "+esc(r['code'])+" · وضعیت: "+esc(r['status'])+"</small><form method='post' action='/report'><input type='hidden' name='csrf' value='"+csrf+"'><input type='hidden' name='id' value='"+esc(r['id'])+"'><select name='status'><option value='open'>باز</option><option value='reviewed'>بررسی‌شده</option><option value='closed'>بسته</option></select><button>ذخیره وضعیت</button></form></article>"
            body+="</section><section id='broadcast' class='card'><h2>پیام همگانی</h2><p class='muted'>پیام برای کاربران ثبت‌شده و غیرمسدود ارسال می‌شود. ارسال ممکن است زمان ببرد.</p><form method='post' action='/broadcast' onsubmit=\"return confirm('ارسال پیام همگانی را تأیید می‌کنی؟')\"><input type='hidden' name='csrf' value='"+csrf+"'><textarea name='message' maxlength='3500' required placeholder='متن پیام...'></textarea><button>ارسال پیام همگانی</button></form></section>"
            body+="<section id='settings' class='card'><h2>تنظیمات ربات</h2><form method='post' action='/settings'><input type='hidden' name='csrf' value='"+csrf+"'><label>متن خوشامدگویی</label><textarea name='welcome_text'>"+esc(next((x['v'] for x in settings if x['k']=='welcome_text'),''))+"</textarea><label>متن حریم خصوصی</label><textarea name='priv_text'>"+esc(next((x['v'] for x in settings if x['k']=='priv_text'),''))+"</textarea><label>ربات فعال باشد؟</label><select name='bot_enabled'><option value='1'>فعال</option><option value='0'>غیرفعال</option></select><button>ذخیره تنظیمات</button></form></section>"
            body+="<section class='card'><h2>پاسخ‌های خودکار</h2><form method='post' action='/reply'><input type='hidden' name='csrf' value='"+csrf+"'><label>کلمه کلیدی</label><input name='keyword' maxlength='120' required><label>متن پاسخ</label><textarea name='response' maxlength='3000' required></textarea><button>افزودن پاسخ</button></form>"
            for a in replies:
                body+="<div class='card'><b>"+esc(a['keyword'])+"</b> <span class='pill'>"+('فعال' if a['enabled'] else 'خاموش')+"</span><p>"+esc(a['response'])+"</p><form method='post' action='/reply_toggle'><input type='hidden' name='csrf' value='"+csrf+"'><input type='hidden' name='id' value='"+esc(a['id'])+"'><input type='hidden' name='enabled' value='"+('0' if a['enabled'] else '1')+"'><button class='soft'>"+('خاموش‌کردن' if a['enabled'] else 'فعال‌کردن')+"</button></form></div>"
            body+="</section><p class='muted'>داده‌ها از دیتابیس مشترک ربات خوانده می‌شوند؛ پنل دیتابیس جداگانه نمی‌سازد.</p>"
            self.send_html(page(body))
        def do_POST(self):
            f=self.form(); path=self.path
            if path=='/login':
                if hmac.compare_digest(f.get('password',''),panel_password):
                    return self.send_html(page("<section class='card'>ورود انجام شد. <a href='/'>رفتن به پنل</a></section>"),cookie='panel_session='+cookie_value+'; Path=/; HttpOnly; Secure; SameSite=Strict; Max-Age=28800')
                time.sleep(1); return self.send_html(page("<section class='card'>رمز نادرست است. <a href='/'>تلاش دوباره</a></section>"),401)
            if path=='/logout':
                return self.send_html(page("<section class='card'>از پنل خارج شدی. <a href='/'>ورود</a></section>"),cookie='panel_session=; Path=/; HttpOnly; Secure; SameSite=Strict; Max-Age=0')
            if not self.authed(): return self.send_html(page("<section class='card'>ابتدا وارد شو.</section>"),401)
            if not hmac.compare_digest(f.get('csrf',''),csrf): return self.send_html(page("<section class='card'>درخواست نامعتبر؛ صفحه را تازه‌سازی کن.</section>"),403)
            try:
                conn=sqlite3.connect(DB_PATH,timeout=15); conn.execute('PRAGMA busy_timeout=15000')
                if path=='/ban':
                    uid=int(f['uid']); ban=1 if f.get('ban')=='1' else 0
                    conn.execute('UPDATE users SET banned=? WHERE uid=?',(ban,uid)); conn.commit(); conn.close()
                    try: send(uid,'⛔ دسترسی شما توسط مدیر مسدود شد.' if ban else '✅ مسدودیت حساب شما برداشته شد.')
                    except Exception: pass
                    msg='وضعیت کاربر ذخیره شد.'
                elif path=='/report':
                    conn.execute('UPDATE complaint_reports SET status=? WHERE id=?',(f.get('status','open') if f.get('status') in ('open','reviewed','closed') else 'open',int(f['id']))); conn.commit(); conn.close(); msg='وضعیت گزارش ذخیره شد.'
                elif path=='/settings':
                    for k in ('welcome_text','priv_text','bot_enabled'):
                        v=f.get(k,'')[:3500]
                        conn.execute('INSERT INTO settings(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v',(k,v))
                        _SETTINGS[k]=v
                    conn.commit(); conn.close(); msg='تنظیمات ذخیره شد.'
                elif path=='/reply':
                    keyword=f.get('keyword','').strip()[:120]; response=f.get('response','').strip()[:3000]
                    if not keyword or not response: raise ValueError('کلمه و پاسخ الزامی است')
                    conn.execute('INSERT INTO auto_replies(keyword,response,enabled) VALUES(?,?,1) ON CONFLICT(keyword) DO UPDATE SET response=excluded.response,enabled=1',(keyword,response)); conn.commit(); conn.close(); msg='پاسخ خودکار ذخیره شد.'
                elif path=='/reply_toggle':
                    conn.execute('UPDATE auto_replies SET enabled=? WHERE id=?',(1 if f.get('enabled')=='1' else 0,int(f['id']))); conn.commit(); conn.close(); msg='وضعیت پاسخ خودکار ذخیره شد.'
                elif path=='/broadcast':
                    message=f.get('message','').strip()
                    if not message: raise ValueError('متن پیام خالی است')
                    rows=conn.execute('SELECT uid FROM users WHERE COALESCE(banned,0)=0').fetchall(); conn.close()
                    sent=failed=0
                    for (uid,) in rows:
                        try:
                            res=send(int(uid),message)
                            if res and res.get('ok'): sent+=1
                            else: failed+=1
                        except Exception: failed+=1
                        time.sleep(0.04)
                    msg=f'ارسال پایان یافت. موفق: {sent} | ناموفق: {failed}'
                else: return self.send_html(page('مسیر ناشناخته'),404)
                return self.send_html(page("<section class='card'><h2>نتیجه</h2><p>"+esc(msg)+"</p><a class='btn' href='/'>بازگشت به پنل</a></section>"))
            except Exception as e:
                return self.send_html(page("<section class='card'>عملیات انجام نشد: "+esc(type(e).__name__)+". لاگ Railway را بررسی کن.</section>"),400)
    try:
        port=int(os.environ.get('PORT','8080'))
        server=ThreadingHTTPServer(('0.0.0.0',port),Handler)
        server.daemon_threads=True
        threading.Thread(target=server.serve_forever,daemon=True,name='web-admin-panel').start()
        print(f'پنل وب روی پورت {port} آماده شد؛ ورود با رمز مستقل پنل.')
    except Exception as e:
        print('راه‌اندازی پنل وب ناموفق:', type(e).__name__, str(e), file=sys.stderr)


def main():
    global BOT_TOKEN, OWNER_ID, POLL_OFFSET, LAST_POLL_OK_AT, LAST_POLL_LATENCY_MS, GAME_MODULE
    BOT_TOKEN, OWNER_ID = load_config()
    init_db()
    GAME_MODULE = GameModule(DB_PATH, OWNER_ID)
    start_web_panel()
    try:                                       # worker.js همیشه کنار ربات ساخته/به‌روز می‌شود
        with open(WORKER_FILE, "w", encoding="utf-8") as f:
            f.write(worker_code())
    except Exception:
        pass
    startup_failures = 0
    while True:
        me = api("getMe", timeout=12)
        if me.get("ok"):
            break
        if me.get("error_code") == 401:
            print("❌ توکن ربات نامعتبر است (401). BOT_TOKEN/config.json را بررسی کنید.")
            sys.exit(1)
        startup_failures = min(startup_failures + 1, 6)
        delay = min(60, 2 ** startup_failures) + random.uniform(0, 1)
        print(f"اتصال تلگرام برقرار نشد؛ تلاش دوباره تا {delay:.1f} ثانیه دیگر: "
              f"{me.get('description')}", file=sys.stderr)
        time.sleep(delay)
    api("deleteWebhook")                       # حالت polling (Termux)
    refresh_bot_commands()
    print(f"✅ ربات @{me['result']['username']} آماده است — {jalali_str()} — مسیر API: {api_base()}")
    offset = None
    failures = 0
    with ThreadPoolExecutor(max_workers=16) as pool:
        while True:
            # Short long-poll leaves headroom under Worker request limits.
            t0 = time.monotonic()
            with POLL_LOCK:
                if POLL_OFFSET is not None and (offset is None or POLL_OFFSET > offset):
                    offset = POLL_OFFSET
                r = api("getUpdates", {"timeout": 10, "offset": offset,
                                       "allowed_updates": ["message", "callback_query"]}, timeout=18)
                LAST_POLL_LATENCY_MS = int((time.monotonic() - t0) * 1000)
            if not r.get("ok"):
                failures = min(failures + 1, 6)
                delay = min(30, 2 ** failures) + random.uniform(0, 0.75)
                print(f"getUpdates error; retrying in {delay:.1f}s: {r.get('description')}", file=sys.stderr)
                time.sleep(delay)
                continue
            failures = 0
            LAST_POLL_OK_AT = time.time()
            for upd in r["result"]:
                offset = upd["update_id"] + 1
                POLL_OFFSET = offset
                pool.submit(handle_update, upd)


if __name__ == "__main__":
    main()
