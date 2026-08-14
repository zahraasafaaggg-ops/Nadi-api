import io
import re
import json
import asyncio
import zipfile
import logging
import textwrap
import math
import unicodedata
import urllib.request
import gzip
import os
from datetime import datetime, timedelta
from typing import Optional, List, Tuple, Any, Dict

import discord
from discord import app_commands
from discord.ext import commands
import aiohttp
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from apscheduler.triggers.date import DateTrigger
from apscheduler.triggers.cron import CronTrigger
import pytz
import motor.motor_asyncio
from bson.binary import Binary

try:
    from PIL import Image, ImageDraw, ImageFont, ImageFilter
    PILLOW_OK = True
except ImportError:
    PILLOW_OK = False
    logging.warning("Pillow غير مثبت — pip install Pillow")

# ══════════════════════════════════════════════════════════════
#  إعدادات MongoDB
# ══════════════════════════════════════════════════════════════
MONGODB_URI = os.getenv("MONGODB_URI")

BAGHDAD_TZ = pytz.timezone("Asia/Baghdad")
UTC = pytz.utc

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
    handlers=[
        logging.FileHandler("bot.log", encoding="utf-8"),
        logging.StreamHandler()
    ]
)
log = logging.getLogger("RewayatBot")

OWNER_ID      = 656783724662226963
DEFAULT_TOKEN = "18a160a5d2ccc616fdbc6a8fd19a98304220c6ff"
BASE_URL      = "https://rewayat.club/api"
SITE_URL      = "https://rewayat.club"
NOVEL_URL     = "https://rewayat.club/novel/{slug}"
SEARCH_URL    = f"{BASE_URL}/novels/search/permitted/"
VERSION = "4.6.0"

# ── إضافة: خط Google (Amiri) يتم تحميله عند التشغيل ──
ARABIC_FONT_URL = "https://fonts.gstatic.com/s/amiri/v27/J7aRnpd8CGxBHqUpsjIw7w.ttf"
ARABIC_FONT_BYTES = None   # سيُخزن هنا بعد التحميل

# ── الخط العربي — unifont مثبت على النظام يدعم العربية كاملاً ──
ARABIC_FONT_PATH = "/usr/share/fonts/opentype/unifont/unifont.otf"
# فاصل وقت الانتظار بين الجداول التسلسلية المتقاربة (دقيقة)
SERIAL_CLUSTER_WINDOW_MINUTES = 120
SERIAL_RETRY_ATTEMPTS = 5
SERIAL_RETRY_BASE_DELAY = 3

# ══════════════════════════════════════════════════════════════
#  ملصق تيليجرام
# ══════════════════════════════════════════════════════════════
STICKER_FILE_ID = "CAACAgIAAxkBAAFOPNhqSbdXa2qIB1aqHA6YHc1fjRWxlgAChIEAAoyCGEkez0XwDFTIgDwE"

class Colors:
    PRIMARY = 0x5865F2
    SUCCESS = 0x57F287
    ERROR   = 0xED4245
    WARNING = 0xFEE75C
    INFO    = 0x5865F2
    PURPLE  = 0x9B59B6
    GOLD    = 0xF1C40F

# ══════════════════════════════════════════════════════════════
#  دوال مساعدة للتعامل مع MongoDB
# ══════════════════════════════════════════════════════════════

async def load_from_mongo(collection, doc_id: str, default: Any) -> Any:
    try:
        doc = await collection.find_one({"_id": doc_id})
        return doc["data"] if doc else default
    except Exception as e:
        log.error(f"خطأ تحميل {doc_id} من MongoDB: {e}")
        return default

async def save_to_mongo(collection, doc_id: str, data: Any) -> bool:
    try:
        await collection.update_one(
            {"_id": doc_id},
            {"$set": {"data": data}},
            upsert=True
        )
        return True
    except Exception as e:
        log.error(f"خطأ حفظ {doc_id} إلى MongoDB: {e}")
        return False

# ══════════════════════════════════════════════════════════════
#  تحويل الأرقام العربية والنصوص
# ══════════════════════════════════════════════════════════════

ARABIC_NUMBERS = {
    "صفر":0,"واحد":1,"اثنان":2,"اثنين":2,"ثلاثة":3,"ثلاث":3,
    "أربعة":4,"أربع":4,"خمسة":5,"خمس":5,"ستة":6,"ست":6,
    "سبعة":7,"سبع":7,"ثمانية":8,"ثمان":8,"تسعة":9,"تسع":9,
    "عشرة":10,"عشر":10,"أحد عشر":11,"اثنا عشر":12,
    "ثلاثة عشر":13,"أربعة عشر":14,"خمسة عشر":15,"ستة عشر":16,
    "سبعة عشر":17,"ثمانية عشر":18,"تسعة عشر":19,
    "عشرون":20,"عشرين":20,"ثلاثون":30,"ثلاثين":30,
    "أربعون":40,"أربعين":40,"خمسون":50,"خمسين":50,
    "ستون":60,"ستين":60,"سبعون":70,"سبعين":70,
    "ثمانون":80,"ثمانين":80,"تسعون":90,"تسعين":90,
    "مئة":100,"مائة":100,"ألف":1000
}

def arabic_to_latin(text: str) -> str:
    table = str.maketrans("٠١٢٣٤٥٦٧٨٩۰۱۲۳۴۵۶۷۸۹", "01234567890123456789")
    return text.translate(table)

def word_to_int(text: str) -> Optional[int]:
    text = re.sub(r"ال|ـ", "", text).strip()
    parts = re.split(r"\s*و\s*", text)
    total = 0
    for p in parts:
        p = p.strip()
        if p in ARABIC_NUMBERS:
            total += ARABIC_NUMBERS[p]
        else:
            for key, val in ARABIC_NUMBERS.items():
                if key in p:
                    total += val
                    break
    return total if total > 0 else None

def extract_chapter_number_from_filename(filename: str) -> Optional[int]:
    stem = os.path.splitext(os.path.basename(filename))[0]
    try:
        return int(arabic_to_latin(stem))
    except ValueError:
        pass
    nums = re.findall(r"[\d٠-٩۰-۹]+", stem)
    if nums:
        try:
            return int(arabic_to_latin(nums[0]))
        except ValueError:
            pass
    return None

def extract_chapter_info_from_content(content: str) -> Tuple[Optional[int], Optional[str]]:
    patterns = [
        r"#?\s*الفصل\s+([\u0660-\u0669\u06F0-\u06F90-9]+)\s*[:\-–]?\s*(.*)",
        r"#?\s*الفصل\s+([أ-ي]+(?:\s[أ-ي]+)*)\s*[:\-–]?\s*(.*)",
    ]
    for line in content.splitlines()[:10]:
        line = line.strip()
        if not line:
            continue
        for pattern in patterns:
            m = re.match(pattern, line)
            if m:
                num_str = m.group(1).strip()
                chap_title = m.group(2).strip() if len(m.groups()) > 1 else ""
                latin = arabic_to_latin(num_str)
                if re.match(r"^\d+$", latin):
                    num = int(latin)
                else:
                    num = word_to_int(num_str)
                if num:
                    return num, chap_title or f"الفصل {num}"
    return None, None

def decode_bytes(raw: bytes) -> str:
    for enc in ("utf-8-sig", "utf-8", "cp1256"):
        try:
            return raw.decode(enc)
        except Exception:
            pass
    return raw.decode("utf-8", errors="replace")

def normalize_content(text: str, to_html: bool = True) -> str:
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    lines = [line.rstrip() for line in text.split("\n")]
    if not to_html:
        return "\n".join(lines)
    paragraphs = []
    current_paragraph = []
    for line in lines:
        if line == "":
            if current_paragraph:
                paragraphs.append(current_paragraph)
                current_paragraph = []
        else:
            current_paragraph.append(line)
    if current_paragraph:
        paragraphs.append(current_paragraph)
    html_parts = []
    for para_lines in paragraphs:
        para_text = "<br>".join(para_lines)
        html_parts.append(f"<p>{para_text}</p>")
    return "\n".join(html_parts)


# ══════════════════════════════════════════════════════════════
#  مدير الحسابات
# ══════════════════════════════════════════════════════════════

class AccountManager:
    def __init__(self, collection):
        self.collection = collection
        self.data = {"accounts": [], "active_index": 0}

    async def initialize(self):
        self.data = await load_from_mongo(self.collection, "accounts", {"accounts": [], "active_index": 0})
        if not self.data["accounts"]:
            self.data["accounts"].append({
                "name": "الحساب الافتراضي",
                "email": "default@example.com",
                "token": DEFAULT_TOKEN,
                "stats": {"published": 0, "failed": 0}
            })
            await self.save()

    @property
    def active_account(self) -> dict:
        idx = self.data.get("active_index", 0)
        if 0 <= idx < len(self.data["accounts"]):
            return self.data["accounts"][idx]
        self.data["active_index"] = 0
        return self.data["accounts"][0]

    @property
    def active_token(self) -> str:
        return self.active_account["token"]

    def add_account(self, name: str, email: str, token: str) -> bool:
        if any(a["token"] == token for a in self.data["accounts"]):
            return False
        self.data["accounts"].append({
            "name": name, "email": email, "token": token,
            "stats": {"published": 0, "failed": 0}
        })
        asyncio.create_task(self.save())
        return True

    def remove_account(self, index: int) -> bool:
        if 0 <= index < len(self.data["accounts"]) and len(self.data["accounts"]) > 1:
            del self.data["accounts"][index]
            if self.data["active_index"] >= len(self.data["accounts"]):
                self.data["active_index"] = 0
            asyncio.create_task(self.save())
            return True
        return False

    def switch_account(self, index: int) -> bool:
        if 0 <= index < len(self.data["accounts"]):
            self.data["active_index"] = index
            asyncio.create_task(self.save())
            return True
        return False

    def record_publish(self, success: bool):
        acc = self.active_account
        key = "published" if success else "failed"
        acc["stats"][key] += 1
        asyncio.create_task(self.save())

    async def save(self):
        await save_to_mongo(self.collection, "accounts", self.data)

account_manager = None

# ══════════════════════════════════════════════════════════════
#  API
# ══════════════════════════════════════════════════════════════

class NovelAPI:
    @property
    def _headers(self) -> dict:
        return {
            "Authorization": f"Token {account_manager.active_token}",
            "User-Agent": "RewayatBot/4.6"
        }

    async def search(self, query: str) -> List[dict]:
        try:
            timeout = aiohttp.ClientTimeout(total=20)
            async with aiohttp.ClientSession(timeout=timeout) as s:
                async with s.get(f"{SEARCH_URL}?search={query}", headers=self._headers) as r:
                    if r.status == 200:
                        data = await r.json()
                        return data.get("results", [])
                    log.warning(f"بحث فشل [{r.status}]")
        except Exception as e:
            log.error(f"خطأ البحث: {e}")
        return []

    async def publish(self, slug: str, number: int, chap_title: str, content: str) -> Tuple[bool, str]:
        try:
            url  = f"{BASE_URL}/chapters/{slug}/create/"
            form = aiohttp.FormData()
            form.add_field("number",  str(number))
            form.add_field("title",   chap_title)
            form.add_field("content", content)
            timeout = aiohttp.ClientTimeout(total=30)
            async with aiohttp.ClientSession(timeout=timeout) as s:
                async with s.post(url, headers=self._headers, data=form) as r:
                    text = await r.text()
                    ok   = r.status in (200, 201)
                    if not ok:
                        log.warning(f"نشر فشل [{r.status}]: {text[:200]}")
                    return ok, text[:300]
        except Exception as e:
            log.error(f"خطأ النشر: {e}")
            return False, str(e)


# ══════════════════════════════════════════════════════════════
#  التخزين والإحصاءات
# ══════════════════════════════════════════════════════════════

class NovelStorage:
    def __init__(self, collection):
        self.collection = collection
        self._cfg = {"novels": []}

    async def initialize(self):
        self._cfg = await load_from_mongo(self.collection, "novels", {"novels": []})
        if "novels" not in self._cfg:
            self._cfg["novels"] = []

    @property
    def novels(self) -> List[dict]:
        return self._cfg["novels"]

    def add_novel(self, slug: str, arabic: str, english: str) -> bool:
        if any(n["slug"] == slug for n in self.novels):
            return False
        self.novels.append({
            "slug": slug, "arabic": arabic, "english": english,
            "added_at": datetime.now(BAGHDAD_TZ).isoformat(),
            "published_count": 0
        })
        asyncio.create_task(self.save())
        return True

    def remove_novel(self, slug: str) -> bool:
        before = len(self.novels)
        self._cfg["novels"] = [n for n in self.novels if n["slug"] != slug]
        if len(self.novels) < before:
            asyncio.create_task(self.save())
            return True
        return False

    def get_novel(self, slug: str) -> Optional[dict]:
        return next((n for n in self.novels if n["slug"] == slug), None)

    def inc_published(self, slug: str, count: int = 1):
        for n in self.novels:
            if n["slug"] == slug:
                n["published_count"] = n.get("published_count", 0) + count
                asyncio.create_task(self.save())
                break

    async def save(self):
        await save_to_mongo(self.collection, "novels", self._cfg)


class StatsManager:
    def __init__(self, collection):
        self.collection = collection
        self._s = {
            "total_published": 0, "total_failed": 0,
            "total_scheduled": 0, "daily": {}
        }

    async def initialize(self):
        self._s = await load_from_mongo(self.collection, "stats", self._s)

    def record(self, success: bool, count: int = 1):
        today = datetime.now(BAGHDAD_TZ).strftime("%Y-%m-%d")
        self._s["daily"].setdefault(today, {"published": 0, "failed": 0})
        key = "total_published" if success else "total_failed"
        dk  = "published"       if success else "failed"
        self._s[key] += count
        self._s["daily"][today][dk] += count
        asyncio.create_task(self._save())

    def record_scheduled(self):
        self._s["total_scheduled"] += 1
        asyncio.create_task(self._save())

    async def _save(self):
        await save_to_mongo(self.collection, "stats", self._s)

    @property
    def total_published(self): return self._s.get("total_published", 0)
    @property
    def total_failed(self):    return self._s.get("total_failed", 0)
    @property
    def total_scheduled(self): return self._s.get("total_scheduled", 0)

    def today(self) -> dict:
        return self._s["daily"].get(
            datetime.now(BAGHDAD_TZ).strftime("%Y-%m-%d"),
            {"published": 0, "failed": 0}
        )


novel_store = None
stats       = None
scheduler   = AsyncIOScheduler(timezone="UTC")

jobs_db     = {"jobs": []}   # للمهام العادية (غير التسلسلية)

async def save_jobs():
    global jobs_db
    await save_to_mongo(db_client.get_database("rewyat_bot").jobs, "jobs", jobs_db)

async def load_jobs(jobs_col):
    global jobs_db
    jobs_db = await load_from_mongo(jobs_col, "jobs", {"jobs": []})


# ══════════════════════════════════════════════════════════════
#  مساعدات Embed
# ══════════════════════════════════════════════════════════════

def make_embed(title: str, desc: str = "", color: int = Colors.PRIMARY,
               fields: list = None) -> discord.Embed:
    e = discord.Embed(title=title, description=desc, color=color)
    e.timestamp = datetime.now(BAGHDAD_TZ)
    e.set_footer(text=f"روايات Bot v{VERSION}")
    if fields:
        for f in fields:
            e.add_field(name=f["name"], value=f["value"], inline=f.get("inline", False))
    return e

def ok_embed(title: str,  desc: str = "") -> discord.Embed:
    return make_embed(f"✅ {title}", desc, Colors.SUCCESS)
def err_embed(title: str, desc: str = "") -> discord.Embed:
    return make_embed(f"❌ {title}", desc, Colors.ERROR)
def inf_embed(title: str, desc: str = "") -> discord.Embed:
    return make_embed(f"ℹ️ {title}", desc, Colors.INFO)
def warn_embed(title: str, desc: str = "") -> discord.Embed:
    return make_embed(f"⚠️ {title}", desc, Colors.WARNING)


# ══════════════════════════════════════════════════════════════
#  البوت
# ══════════════════════════════════════════════════════════════

intents = discord.Intents.default()
intents.message_content = True

class RewayatBot(commands.Bot):
    def __init__(self):
        super().__init__(command_prefix="!", intents=intents, help_command=None)
        self.start_time = datetime.now(BAGHDAD_TZ)

    async def setup_hook(self):
        await self.tree.sync()
        log.info("تم مزامنة الأوامر")

    async def on_ready(self):
        log.info(f"✅ {self.user} جاهز | {len(self.guilds)} سيرفر")
        await self.change_presence(
            activity=discord.Activity(type=discord.ActivityType.watching, name="📚 روايات")
        )
        if not scheduler.running:
            scheduler.start()
        await self._restore_jobs()

    async def _restore_jobs(self):
        restored = expired = 0
        now_utc = datetime.now(UTC)
        jobs_data = jobs_db.get("jobs", [])[:]
        for job in jobs_data[:]:
            rt = datetime.fromisoformat(job["run_time"])
            if rt.tzinfo is None:
                rt = UTC.localize(rt)
            else:
                rt = rt.astimezone(UTC)
            if rt > now_utc:
                try:
                    scheduler.add_job(
                        run_job,
                        DateTrigger(run_date=rt, timezone=UTC),
                        args=[job],
                        id=job["id"],
                        replace_existing=True
                    )
                    restored += 1
                except Exception as e:
                    log.error(f"فشل استعادة {job['id']}: {e}")
            else:
                jobs_db["jobs"].remove(job)
                expired += 1
        if expired:
            await save_jobs()
        log.info(f"استعادة المهام: {restored} نشطة، {expired} منتهية حُذفت")

        # استعادة الجداول التسلسلية من MongoDB مباشرة
        db = db_client.get_database("rewyat_bot")
        serial_restored = 0
        async for doc in db.serial_schedules.find({"finished": False, "paused": False}):
            sid = doc["_id"]
            try:
                for slot_doc in _serial_slots(doc):
                    scheduler.add_job(
                        run_serial_batch_for_slot,
                        CronTrigger(hour=slot_doc["hour"], minute=slot_doc["minute"], timezone=BAGHDAD_TZ),
                        args=[sid, slot_doc["slot"]],
                        id=f"serial_{sid}_{slot_doc['slot']}",
                        replace_existing=True
                    )
                    serial_restored += 1
                log.info(f"[Serial] استُعيد الجدول التسلسلي: {sid}")
            except Exception as e:
                log.error(f"[Serial] فشل استعادة {sid}: {e}")
        if serial_restored:
            log.info(f"[Serial] تم استعادة {serial_restored} جدول تسلسلي")


bot = RewayatBot()


def owner_only():
    async def predicate(inter: discord.Interaction):
        if inter.user.id == OWNER_ID:
            return True
        await inter.response.send_message(
            embed=err_embed("غير مصرح", "هذا الأمر للمالك فقط."),
            ephemeral=True
        )
        return False
    return app_commands.check(predicate)


# ══════════════════════════════════════════════════════════════
#  منطق المهام العادية
# ══════════════════════════════════════════════════════════════

async def run_job(job: dict):
    novel = novel_store.get_novel(job["slug"])
    api   = NovelAPI()
    ok, _ = await api.publish(job["slug"], job["number"], job["chap_title"], job["content"])
    stats.record(ok)
    account_manager.record_publish(ok)
    if ok:
        novel_store.inc_published(job["slug"])
        # announce_enabled: True بشكل افتراضي، False إذا أراد المستخدم النشر بدون إعلان
        if ann_queue is not None and job.get("announce_enabled", True):
            cover = await ann_cog.get_cover(job["slug"]) if ann_cog else None
            novel_arabic = novel["arabic"] if novel else job["slug"]
            await ann_queue.register_publish(
                novel_arabic=novel_arabic,
                slug=job["slug"],
                first_chapter=job["number"],
                last_chapter=job["number"],
                cover_bytes=cover,
                source="scheduled",
            )
    ch = bot.get_channel(job.get("channel_id"))
    if ch:
        novel_name = novel["arabic"] if novel else job["slug"]
        try:
            await ch.send(embed=make_embed(
                "نشر مجدول",
                f"**الرواية:** {novel_name}\n"
                f"**الفصل {job['number']}:** {job['chap_title']}\n"
                f"**الحالة:** {'تم النشر بنجاح' if ok else 'فشل النشر'}",
                Colors.SUCCESS if ok else Colors.ERROR
            ))
        except Exception as e:
            log.error(f"فشل إرسال نتيجة المهمة: {e}")
    jobs_db["jobs"] = [j for j in jobs_db["jobs"] if j["id"] != job["id"]]
    await save_jobs()


# ══════════════════════════════════════════════════════════════
#  نظام النشر التسلسلي اليومي (باستخدام MongoDB مباشرة)
# ══════════════════════════════════════════════════════════════

def _serial_bar(done: int, total: int, width: int = 14) -> str:
    pct    = (done / total) if total > 0 else 0
    filled = round(pct * width)
    return f"[{'█' * filled}{'░' * (width - filled)}] {round(pct * 100)}%"


def _is_duplicate_chapter_error(message: str) -> bool:
    """يتعرف على خطأ الفصل الموجود مسبقاً حتى لا ندخل في إعادة محاولات بلا فائدة."""
    normalized = unicodedata.normalize("NFKD", message or "")
    normalized = "".join(ch for ch in normalized if not unicodedata.combining(ch))
    normalized = normalized.replace("أ", "ا").replace("إ", "ا").replace("آ", "ا")
    return "فصل" in normalized and "بهذا الرقم" in normalized and "مسبقا" in normalized


async def run_serial_batch(serial_id: str):
    """تنفيذ دفعة النشر التسلسلي - تقرأ الجدول والفصول من MongoDB مباشرة."""
    await run_serial_batch_for_slot(serial_id)


async def _publish_with_serial_retry(api: NovelAPI, db, doc: dict, ch_data: dict) -> Tuple[bool, str]:
    """ينشر الفصل التسلسلي مع إعادة محاولة تلقائية وحفظ الفشل النهائي."""
    slug = doc["slug"]
    last_msg = ""
    for attempt in range(1, SERIAL_RETRY_ATTEMPTS + 1):
        ok, msg = await api.publish(slug, ch_data["number"], ch_data["title"], ch_data["content"])
        last_msg = msg
        if ok:
            await db.failed_serial_chapters.delete_one({
                "serial_id": doc["_id"],
                "number": ch_data["number"],
            })
            return True, msg
        if _is_duplicate_chapter_error(msg):
            await db.failed_serial_chapters.delete_one({
                "serial_id": doc["_id"],
                "number": ch_data["number"],
            })
            await db.duplicate_serial_chapters.update_one(
                {"serial_id": doc["_id"], "number": ch_data["number"]},
                {"$set": {
                    "serial_id": doc["_id"],
                    "slug": slug,
                    "novel_arabic": doc.get("novel_arabic", ""),
                    "number": ch_data["number"],
                    "title": ch_data["title"],
                    "message": msg[:500],
                    "skipped_at": datetime.now(BAGHDAD_TZ).isoformat(),
                }},
                upsert=True
            )
            log.info(
                f"[Serial] الفصل {ch_data['number']} موجود مسبقاً في {slug} — "
                "تم تسجيله وتخطي إعادة المحاولة."
            )
            return True, "duplicate chapter skipped"
        if attempt < SERIAL_RETRY_ATTEMPTS:
            await asyncio.sleep(SERIAL_RETRY_BASE_DELAY * attempt)

    await db.failed_serial_chapters.update_one(
        {"serial_id": doc["_id"], "number": ch_data["number"]},
        {"$set": {
            "serial_id": doc["_id"],
            "slug": slug,
            "novel_arabic": doc.get("novel_arabic", ""),
            "number": ch_data["number"],
            "title": ch_data["title"],
            "content_compressed": Binary(gzip.compress(ch_data["content"].encode("utf-8"))),
            "error": last_msg[:500],
            "failed_at": datetime.now(BAGHDAD_TZ).isoformat(),
            "attempts": SERIAL_RETRY_ATTEMPTS,
        }},
        upsert=True
    )
    return False, last_msg


def _serial_slots(doc: dict) -> List[dict]:
    slots = doc.get("slots")
    if slots:
        return slots
    return [{
        "slot": 1,
        "hour": doc.get("hour", 0),
        "minute": doc.get("minute", 0),
        "size": doc.get("batch_size", 1),
    }]


async def run_serial_batch_for_slot(serial_id: str, slot: Optional[int] = None, manual_date: Optional[str] = None):
    """تنفيذ دفعة نشر تسلسلي لموعد محدد أو للموعد الوحيد."""
    db = db_client.get_database("rewyat_bot")
    doc = await db.serial_schedules.find_one({"_id": serial_id})
    if not doc:
        log.warning(f"[Serial] الجدول {serial_id} غير موجود، إلغاء المهمة.")
        try:
            scheduler.remove_job(f"serial_{serial_id}")
        except Exception:
            pass
        return

    if doc.get("paused"):
        log.info(f"[Serial] الجدول {serial_id} متوقف، تخطي.")
        return

    published_count = doc.get("published_count", 0)
    total           = doc.get("total_chapters", 0)
    slots           = _serial_slots(doc)
    selected_slots  = [s for s in slots if slot is None or s.get("slot") == slot]
    batch_size      = sum(max(0, int(s.get("size", 0))) for s in selected_slots) or doc.get("batch_size", 1)

    if published_count >= total:
        log.info(f"[Serial] انتهت فصول الجدول {serial_id}.")
        try:
            scheduler.remove_job(f"serial_{serial_id}")
        except Exception:
            pass
        await db.serial_schedules.update_one(
            {"_id": serial_id},
            {"$set": {"finished": True}}
        )
        ch = bot.get_channel(doc["channel_id"])
        if ch:
            await ch.send(embed=make_embed(
                "انتهت جميع فصول الجدول",
                f"**{doc.get('novel_arabic','الرواية')}** — تم نشر جميع الـ {total} فصل بنجاح.\n"
                f"يمكنك رفع رواية جديدة باستخدام `/نشر_تسلسلي`",
                Colors.GOLD
            ))
        return

    # جلب الفصول التالية من serial_chapters
    chapters_cursor = db.serial_chapters.find(
        {"serial_id": serial_id, "number": {"$gt": published_count}}
    ).sort("number", 1).limit(batch_size)
    batch = []
    async for ch in chapters_cursor:
        # فك ضغط المحتوى
        try:
            content = gzip.decompress(ch["content_compressed"]).decode("utf-8")
        except Exception:
            content = ch.get("content", "")   # fallback (لن يكون موجوداً)
        batch.append({
            "number": ch["number"],
            "title": ch["title"],
            "content": content
        })

    if not batch:
        # لا توجد فصول (ربما بسبب مشكلة في الفهرس)
        log.warning(f"[Serial] لم يُعثر على فصول للجدول {serial_id} رغم published_count {published_count}")
        return

    api   = NovelAPI()
    slug  = doc["slug"]
    pub   = 0
    fail  = 0
    first_published_num = None
    last_published_num  = None

    for ch_data in batch:
        ok, _ = await _publish_with_serial_retry(api, db, doc, ch_data)
        if ok:
            pub += 1
            stats.record(True)
            account_manager.record_publish(True)
            if first_published_num is None:
                first_published_num = ch_data["number"]
            last_published_num = ch_data["number"]
        else:
            fail += 1
            stats.record(False)
            account_manager.record_publish(False)
        await asyncio.sleep(1.0)

    # تحديث عدد المنشورات بعدد الناجحين فقط (باستخدام $inc)
    if pub > 0:
        await db.serial_schedules.update_one(
            {"_id": serial_id},
            {"$inc": {"published_count": pub}}
        )
        novel_store.inc_published(slug, pub)

    # إرسال إعلان إذا طلب ذلك وتم نشر شيء
    if pub > 0 and ann_queue is not None and last_published_num is not None and doc.get("announce_enabled", True):
        cover = await ann_cog.get_cover(slug) if ann_cog else None
        await ann_queue.register_publish(
            novel_arabic=doc.get("novel_arabic", ""),
            slug=slug,
            first_chapter=first_published_num,
            last_chapter=last_published_num,
            cover_bytes=cover,
            source="serial",
        )

    # جلب القيم المحدثة لإرسال التقرير
    doc_updated = await db.serial_schedules.find_one({"_id": serial_id})
    new_count = doc_updated.get("published_count", published_count) if doc_updated else published_count
    remaining = total - new_count
    batches_left = max(0, (remaining + batch_size - 1) // batch_size)
    channel = bot.get_channel(doc["channel_id"])
    if channel:
        slot_label = "كل المواعيد" if slot is None and len(slots) > 1 else (f"الموعد {slot}" if slot else "الموعد اليومي")
        nums_str = "، ".join(f"**{ch_data['number']}**" for ch_data in batch)
        embed = make_embed(
            f"دفعة جديدة — {doc.get('novel_arabic','')}",
            f"**{slot_label}**\n"
            f"تم نشر الفصول: {nums_str}\n\n"
            f"`{_serial_bar(new_count, total)}`\n\n"
            f"المنشور: {new_count}/{total}  |  المتبقي: {remaining}  |  دفعات باقية: {batches_left}",
            Colors.SUCCESS if fail == 0 else Colors.WARNING
        )
        if fail > 0:
            embed.add_field(name="تنبيه", value=f"فشل نشر {fail} فصل من الدفعة.", inline=False)
        await channel.send(embed=embed)

    log.info(f"[Serial] دفعة {serial_id}: نُشر {pub}، فشل {fail} | متبقٍ: {remaining}")


# ══════════════════════════════════════════════════════════════
#  دوال مساعدة لواجهات المستخدم
# ══════════════════════════════════════════════════════════════

def baghdad_to_utc(baghdad_dt: datetime) -> datetime:
    if baghdad_dt.tzinfo is None:
        baghdad_dt = BAGHDAD_TZ.localize(baghdad_dt)
    return baghdad_dt.astimezone(UTC)


def _build_year_options() -> list:
    now = datetime.now(BAGHDAD_TZ)
    return [
        discord.SelectOption(label=str(now.year + i), value=str(now.year + i), emoji="📅")
        for i in range(3)
    ]

def _build_month_options() -> list:
    names = [
        "يناير","فبراير","مارس","إبريل","مايو","يونيو",
        "يوليو","أغسطس","سبتمبر","أكتوبر","نوفمبر","ديسمبر"
    ]
    return [
        discord.SelectOption(label=f"{i:02d} — {names[i-1]}", value=str(i), emoji="🗓️")
        for i in range(1, 13)
    ]

def _build_day_options(year: int, month: int) -> list:
    import calendar
    _, total = calendar.monthrange(year, month)
    return [
        discord.SelectOption(label=f"اليوم {d}", value=str(d), emoji="📆")
        for d in range(1, total + 1)
    ]

def _build_hour_options() -> list:
    opts = []
    for h in range(1, 13):
        opts.append(discord.SelectOption(label=f"{h:02d}  (صباحاً)", value=f"am_{h}", emoji="🌅"))
    for h in range(12, 0, -1):
        opts.append(discord.SelectOption(label=f"{h:02d}  (مساءً)", value=f"pm_{h}", emoji="🌆"))
    return opts

def _build_minute_options() -> list:
    labels = {0:"00 — رأس الساعة", 15:"15 — والربع", 30:"30 — والنصف", 45:"45 — إلا الربع"}
    return [
        discord.SelectOption(label=labels.get(m, f"{m:02d}"), value=str(m), emoji="⏱️")
        for m in range(0, 60, 5)
    ]

def _to_24h(period_val: str, hour12: int) -> int:
    if period_val == "pm":
        return hour12 if hour12 == 12 else hour12 + 12
    else:
        return 0 if hour12 == 12 else hour12

def _progress_bar(step: int, total: int = 5) -> str:
    filled = "🟦" * step
    empty  = "⬜" * (total - step)
    return f"{filled}{empty}  ({step}/{total})"


# ══════════════════════════════════════════════════════════════
#  Views
# ══════════════════════════════════════════════════════════════

class ChapterDataModal(discord.ui.Modal):
    chap_num = discord.ui.TextInput(
        label="رقم الفصل", placeholder="مثال: 21",
        required=True, max_length=6
    )
    chap_name = discord.ui.TextInput(
        label="عنوان الفصل", placeholder="مثال: هزيم الرعد",
        required=True, max_length=200
    )

    def __init__(self):
        super().__init__(title="بيانات الفصل")
        self.chap_number:    Optional[int] = None
        self.chap_title_val: Optional[str] = None
        self._done = asyncio.Event()

    async def on_submit(self, interaction: discord.Interaction):
        raw = arabic_to_latin(self.chap_num.value.strip())
        try:
            self.chap_number = int(raw)
        except ValueError:
            await interaction.response.send_message(
                embed=err_embed("رقم غير صالح", "أدخل رقمًا صحيحًا مثل: 21"),
                ephemeral=True
            )
            return
        self.chap_title_val = self.chap_name.value.strip()
        await interaction.response.defer()
        self._done.set()

    async def wait(self) -> bool:
        try:
            await asyncio.wait_for(self._done.wait(), timeout=300)
            return True
        except asyncio.TimeoutError:
            return False


class SchedulePickerView(discord.ui.View):
    STEPS = ["السنة", "الشهر", "اليوم", "الساعة", "الدقيقة"]

    def __init__(self, slug: str, number: int, chap_title: str, content: str,
                 channel_id: int, uid: int):
        super().__init__(timeout=300)
        self.slug = slug; self.number = number; self.chap_title = chap_title
        self.content = content; self.channel_id = channel_id; self.uid = uid
        self.year: Optional[int] = None; self.month: Optional[int] = None
        self.day:  Optional[int] = None; self.hour24: Optional[int] = None
        self.minute: Optional[int] = None
        self._render_step(1)

    def _guard(self, i: discord.Interaction) -> bool: return i.user.id == self.uid

    def _render_step(self, step: int):
        self.clear_items()
        if step == 1:
            sel = discord.ui.Select(placeholder="اختر السنة...", options=_build_year_options(), custom_id="year")
            sel.callback = self._on_year
        elif step == 2:
            sel = discord.ui.Select(placeholder="اختر الشهر...", options=_build_month_options(), custom_id="month")
            sel.callback = self._on_month
        elif step == 3:
            opts = _build_day_options(self.year, self.month)
            sel = discord.ui.Select(placeholder="اختر اليوم...", options=opts[:25], custom_id="day")
            sel.callback = self._on_day
            if len(opts) > 25:
                sel2 = discord.ui.Select(placeholder="أيام 26+...", options=opts[25:], custom_id="day2")
                sel2.callback = self._on_day
                self.add_item(sel2)
        elif step == 4:
            am_opts = [discord.SelectOption(label=f"{h:02d}:00 صباحاً", value=f"am_{h}", emoji="🌅") for h in range(1,13)]
            pm_opts = [discord.SelectOption(label=f"{h:02d}:00 مساءً",  value=f"pm_{h}", emoji="🌆") for h in range(1,13)]
            sel  = discord.ui.Select(placeholder="صباحاً — اختر الساعة...", options=am_opts, custom_id="hour_am")
            sel.callback = self._on_hour
            sel2 = discord.ui.Select(placeholder="مساءً — اختر الساعة...",  options=pm_opts, custom_id="hour_pm")
            sel2.callback = self._on_hour
            self.add_item(sel); self.add_item(sel2)
        elif step == 5:
            sel = discord.ui.Select(placeholder="اختر الدقيقة...", options=_build_minute_options()[:25], custom_id="minute")
            sel.callback = self._on_minute

        if step != 4:
            self.add_item(sel)
        cancel_btn = discord.ui.Button(label="إلغاء", style=discord.ButtonStyle.danger, custom_id="cancel_sched")
        cancel_btn.callback = self._on_cancel
        self.add_item(cancel_btn)

    def _summary_text(self) -> str:
        parts = []
        if self.year:   parts.append(f"**السنة:** {self.year}")
        if self.month:  parts.append(f"**الشهر:** {self.month:02d}")
        if self.day:    parts.append(f"**اليوم:** {self.day:02d}")
        if self.hour24 is not None:
            h12 = self.hour24 % 12 or 12
            period = "صباحاً" if self.hour24 < 12 else "مساءً"
            parts.append(f"**الساعة:** {h12:02d} {period}")
        if self.minute is not None:
            parts.append(f"**الدقيقة:** {self.minute:02d}")
        return "\n".join(parts) if parts else ""

    async def _update_msg(self, interaction: discord.Interaction, step: int, title: str):
        novel    = novel_store.get_novel(self.slug)
        novel_nm = novel["arabic"] if novel else self.slug
        desc = (
            f"**الرواية:** {novel_nm}\n"
            f"**الفصل {self.number}:** {self.chap_title}\n\n"
            f"{_progress_bar(step - 1)}\n\n"
            f"{self._summary_text()}"
        )
        self._render_step(step)
        await interaction.response.edit_message(
            embed=make_embed(f"{title}", desc, Colors.PURPLE), view=self
        )

    async def _on_year(self, i: discord.Interaction):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.year = int(i.data["values"][0])
        await self._update_msg(i, 2, f"اختر الشهر — {self.year}")

    async def _on_month(self, i: discord.Interaction):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.month = int(i.data["values"][0])
        await self._update_msg(i, 3, f"اختر اليوم — {self.month:02d}/{self.year}")

    async def _on_day(self, i: discord.Interaction):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.day = int(i.data["values"][0])
        await self._update_msg(i, 4, f"اختر الساعة — {self.day:02d}/{self.month:02d}/{self.year}")

    async def _on_hour(self, i: discord.Interaction):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        val = i.data["values"][0]; period, h = val.split("_")
        self.hour24 = _to_24h(period, int(h))
        h12 = int(h); per_ar = "صباحاً" if period == "am" else "مساءً"
        await self._update_msg(i, 5, f"اختر الدقيقة — {h12:02d} {per_ar} | {self.day:02d}/{self.month:02d}/{self.year}")

    async def _on_minute(self, i: discord.Interaction):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.minute = int(i.data["values"][0])
        try:
            rt_naive = datetime(self.year, self.month, self.day, self.hour24, self.minute)
        except ValueError as e:
            return await i.response.send_message(embed=err_embed("تاريخ غير صالح", str(e)), ephemeral=True)
        rt = BAGHDAD_TZ.localize(rt_naive)
        rt_utc = baghdad_to_utc(rt)
        now_utc = datetime.now(UTC)
        if rt_utc <= now_utc:
            novel_nm = (novel_store.get_novel(self.slug) or {}).get("arabic", self.slug)
            self._render_step(5)
            return await i.response.edit_message(
                embed=make_embed("الوقت في الماضي!", f"**الرواية:** {novel_nm}\nاختر دقيقةً أخرى أو ابدأ من جديد.", Colors.WARNING),
                view=self
            )
        self.clear_items()
        confirm_btn = discord.ui.Button(label="تأكيد الجدولة", style=discord.ButtonStyle.success)
        confirm_btn.callback = lambda inter: self._on_confirm(inter, rt)
        edit_btn = discord.ui.Button(label="تعديل", style=discord.ButtonStyle.secondary)
        edit_btn.callback = self._on_restart
        cancel_btn = discord.ui.Button(label="إلغاء", style=discord.ButtonStyle.danger)
        cancel_btn.callback = self._on_cancel
        self.add_item(confirm_btn); self.add_item(edit_btn); self.add_item(cancel_btn)
        novel_nm = (novel_store.get_novel(self.slug) or {}).get("arabic", self.slug)
        h12 = self.hour24 % 12 or 12; per_ar = "صباحاً" if self.hour24 < 12 else "مساءً"
        delta = rt - datetime.now(BAGHDAD_TZ)
        hd = int(delta.total_seconds() // 3600); md = int((delta.total_seconds() % 3600) // 60)
        await i.response.edit_message(
            embed=make_embed(
                "مراجعة موعد النشر",
                f"**الرواية:** {novel_nm}\n**الفصل {self.number}:** {self.chap_title}\n\n"
                f"{_progress_bar(5)}\n\n"
                f"**التاريخ:** {self.day:02d}/{self.month:02d}/{self.year}\n"
                f"**الوقت:** {h12:02d}:{self.minute:02d} {per_ar}\n"
                f"**بعد:** {hd} ساعة و {md} دقيقة\n\n"
                f"اضغط **تأكيد** للجدولة أو **تعديل** للبدء من جديد.",
                Colors.GOLD
            ),
            view=self
        )

    async def _on_confirm(self, i: discord.Interaction, rt: datetime):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        novel_nm = (novel_store.get_novel(self.slug) or {}).get("arabic", self.slug)
        job_id   = f"job_{i.user.id}_{int(datetime.utcnow().timestamp())}"
        rt_utc   = baghdad_to_utc(rt)
        job = {
            "id": job_id, "slug": self.slug, "number": self.number,
            "chap_title": self.chap_title, "content": self.content,
            "run_time": rt_utc.isoformat(), "run_time_baghdad": rt.isoformat(),
            "channel_id": self.channel_id, "created_at": datetime.now(UTC).isoformat(),
        }
        try:
            scheduler.add_job(run_job, DateTrigger(run_date=rt_utc, timezone=UTC),
                               args=[job], id=job_id, replace_existing=True)
            jobs_db["jobs"].append(job); await save_jobs(); stats.record_scheduled()
            delta = rt - datetime.now(BAGHDAD_TZ)
            hd = int(delta.total_seconds() // 3600); md = int((delta.total_seconds() % 3600) // 60)
            h12 = self.hour24 % 12 or 12; per_ar = "صباحاً" if self.hour24 < 12 else "مساءً"
            await i.response.edit_message(
                embed=ok_embed("تمت الجدولة",
                    f"**الرواية:** {novel_nm}\n**الفصل {self.number}:** {self.chap_title}\n"
                    f"**الموعد:** {self.day:02d}/{self.month:02d}/{self.year}  {h12:02d}:{self.minute:02d} {per_ar}\n"
                    f"**بعد:** {hd} ساعة و {md} دقيقة"),
                view=None
            )
        except Exception as e:
            log.error(f"فشل الجدولة: {e}")
            await i.response.send_message(embed=err_embed("خطأ في الجدولة", str(e)), ephemeral=True)
        self.stop()

    async def _on_restart(self, i: discord.Interaction):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.year = self.month = self.day = self.hour24 = self.minute = None
        novel_nm = (novel_store.get_novel(self.slug) or {}).get("arabic", self.slug)
        self._render_step(1)
        await i.response.edit_message(
            embed=make_embed("اختر السنة",
                f"**الرواية:** {novel_nm}\n**الفصل {self.number}:** {self.chap_title}\n\n{_progress_bar(0)}",
                Colors.PURPLE),
            view=self
        )

    async def _on_cancel(self, i: discord.Interaction):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        await i.response.edit_message(embed=warn_embed("تم الإلغاء"), view=None)
        self.stop()


class BatchSchedulePickerView(discord.ui.View):
    def __init__(self, slug: str, tasks: list, novel: Optional[dict], channel_id: int, uid: int):
        super().__init__(timeout=300)
        self.slug = slug; self.tasks = tasks; self.novel = novel
        self.channel_id = channel_id; self.uid = uid
        self.year: Optional[int] = None; self.month: Optional[int] = None
        self.day: Optional[int] = None; self.hour24: Optional[int] = None
        self.minute: Optional[int] = None; self.interval: Optional[float] = None
        self._render_step(1)

    def _guard(self, i): return i.user.id == self.uid
    def _novel_nm(self): return self.novel["arabic"] if self.novel else self.slug

    def _summary_text(self) -> str:
        parts = []
        if self.year:   parts.append(f"**السنة:** {self.year}")
        if self.month:  parts.append(f"**الشهر:** {self.month:02d}")
        if self.day:    parts.append(f"**اليوم:** {self.day:02d}")
        if self.hour24 is not None:
            h12 = self.hour24 % 12 or 12; per = "صباحاً" if self.hour24 < 12 else "مساءً"
            parts.append(f"**الساعة:** {h12:02d} {per}")
        if self.minute is not None: parts.append(f"**الدقيقة:** {self.minute:02d}")
        if self.interval is not None: parts.append(f"**الفاصل:** كل {self.interval:.0f} ساعة")
        return "\n".join(parts)

    def _render_step(self, step: int):
        self.clear_items()
        if step == 1:
            sel = discord.ui.Select(placeholder="اختر السنة...", options=_build_year_options())
            sel.callback = self._on_year
        elif step == 2:
            sel = discord.ui.Select(placeholder="اختر الشهر...", options=_build_month_options())
            sel.callback = self._on_month
        elif step == 3:
            opts = _build_day_options(self.year, self.month)
            sel  = discord.ui.Select(placeholder="اختر اليوم...", options=opts[:25])
            sel.callback = self._on_day
            if len(opts) > 25:
                sel2 = discord.ui.Select(placeholder="أيام 26+...", options=opts[25:])
                sel2.callback = self._on_day; self.add_item(sel2)
        elif step == 4:
            am_opts = [discord.SelectOption(label=f"{h:02d}:00 صباحاً", value=f"am_{h}", emoji="🌅") for h in range(1,13)]
            pm_opts = [discord.SelectOption(label=f"{h:02d}:00 مساءً",  value=f"pm_{h}", emoji="🌆") for h in range(1,13)]
            sel  = discord.ui.Select(placeholder="صباحاً...", options=am_opts); sel.callback = self._on_hour
            sel2 = discord.ui.Select(placeholder="مساءً...",  options=pm_opts); sel2.callback = self._on_hour
            self.add_item(sel); self.add_item(sel2)
        elif step == 5:
            sel = discord.ui.Select(placeholder="اختر الدقيقة...", options=_build_minute_options()[:25])
            sel.callback = self._on_minute
        elif step == 6:
            sel = discord.ui.Select(
                placeholder="الفاصل بين كل فصل...",
                options=[
                    discord.SelectOption(label="كل ساعة",              value="1",   emoji="⚡"),
                    discord.SelectOption(label="كل 3 ساعات",           value="3",   emoji="🕐"),
                    discord.SelectOption(label="كل 6 ساعات",           value="6",   emoji="🕕"),
                    discord.SelectOption(label="كل 12 ساعة",           value="12",  emoji="🕛"),
                    discord.SelectOption(label="كل 24 ساعة (يوم)",     value="24",  emoji="📅"),
                    discord.SelectOption(label="كل 48 ساعة (يومين)",   value="48",  emoji="📅"),
                    discord.SelectOption(label="كل أسبوع (168 ساعة)",  value="168", emoji="📅"),
                ]
            )
            sel.callback = self._on_interval
        if step != 4: self.add_item(sel)
        cancel_btn = discord.ui.Button(label="إلغاء", style=discord.ButtonStyle.danger)
        cancel_btn.callback = self._on_cancel
        self.add_item(cancel_btn)

    async def _update(self, i, step, title):
        self._render_step(step)
        await i.response.edit_message(
            embed=make_embed(f"{title}",
                f"**الرواية:** {self._novel_nm()}\n**{len(self.tasks)} فصل** للجدولة\n\n"
                f"{_progress_bar(step-1, 6)}\n\n{self._summary_text()}",
                Colors.PURPLE),
            view=self
        )

    async def _on_year(self, i):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.year = int(i.data["values"][0]); await self._update(i, 2, f"اختر الشهر — {self.year}")

    async def _on_month(self, i):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.month = int(i.data["values"][0]); await self._update(i, 3, f"اختر اليوم — {self.month:02d}/{self.year}")

    async def _on_day(self, i):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.day = int(i.data["values"][0]); await self._update(i, 4, f"اختر الساعة — {self.day:02d}/{self.month:02d}/{self.year}")

    async def _on_hour(self, i):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        val = i.data["values"][0]; period, h = val.split("_"); self.hour24 = _to_24h(period, int(h))
        per_ar = "صباحاً" if period == "am" else "مساءً"
        await self._update(i, 5, f"اختر الدقيقة — {int(h):02d} {per_ar}")

    async def _on_minute(self, i):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.minute = int(i.data["values"][0])
        try:
            rt_naive = datetime(self.year, self.month, self.day, self.hour24, self.minute)
        except ValueError as e:
            return await i.response.send_message(embed=err_embed("تاريخ غير صالح", str(e)), ephemeral=True)
        rt = BAGHDAD_TZ.localize(rt_naive)
        if rt <= datetime.now(BAGHDAD_TZ):
            self._render_step(5)
            return await i.response.edit_message(
                embed=make_embed("الوقت في الماضي!", "اختر دقيقةً أخرى أو ابدأ من جديد.", Colors.WARNING), view=self
            )
        await self._update(i, 6, "اختر الفاصل الزمني بين الفصول")

    async def _on_interval(self, i):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.interval = float(i.data["values"][0])
        rt_naive = datetime(self.year, self.month, self.day, self.hour24, self.minute)
        rt = BAGHDAD_TZ.localize(rt_naive)
        self.clear_items()
        confirm_btn = discord.ui.Button(label="تأكيد الجدولة", style=discord.ButtonStyle.success)
        confirm_btn.callback = lambda inter: self._on_confirm(inter, rt)
        edit_btn = discord.ui.Button(label="تعديل", style=discord.ButtonStyle.secondary)
        edit_btn.callback = self._on_restart
        cancel_btn = discord.ui.Button(label="إلغاء", style=discord.ButtonStyle.danger)
        cancel_btn.callback = self._on_cancel
        self.add_item(confirm_btn); self.add_item(edit_btn); self.add_item(cancel_btn)
        last_rt = rt + timedelta(hours=self.interval * (len(self.tasks) - 1))
        h12 = self.hour24 % 12 or 12; per_ar = "صباحاً" if self.hour24 < 12 else "مساءً"
        summary_tasks = "\n".join(
            f"ف**{num}** — `{rt + timedelta(hours=self.interval * idx):%Y-%m-%d %H:%M}`"
            for idx, (num, _, _) in enumerate(self.tasks[:8])
        )
        if len(self.tasks) > 8:
            summary_tasks += f"\n... و **{len(self.tasks)-8}** فصول أخرى"
        await i.response.edit_message(
            embed=make_embed("مراجعة الجدولة الجماعية",
                f"**الرواية:** {self._novel_nm()}\n**عدد الفصول:** {len(self.tasks)}\n\n"
                f"{_progress_bar(6, 6)}\n\n"
                f"**أول فصل:** {self.day:02d}/{self.month:02d}/{self.year}  {h12:02d}:{self.minute:02d} {per_ar}\n"
                f"**آخر فصل:** `{last_rt.strftime('%Y-%m-%d %H:%M')}`\n"
                f"**الفاصل:** كل {self.interval:.0f} ساعة\n\n"
                f"**جدول التواريخ:**\n{summary_tasks}",
                Colors.GOLD),
            view=self
        )

    async def _on_confirm(self, i, rt):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        await i.response.edit_message(
            embed=make_embed("جارٍ الجدولة...", f"يتم جدولة **{len(self.tasks)}** فصل...", Colors.WARNING), view=None
        )
        scheduled = 0
        for idx, (num, chap_t, content) in enumerate(self.tasks):
            chapter_rt_baghdad = rt + timedelta(hours=self.interval * idx)
            chapter_rt_utc     = baghdad_to_utc(chapter_rt_baghdad)
            job_id = f"job_{i.user.id}_{int(datetime.utcnow().timestamp())}_{num}"
            job = {
                "id": job_id, "slug": self.slug, "number": num, "chap_title": chap_t,
                "content": content, "run_time": chapter_rt_utc.isoformat(),
                "run_time_baghdad": chapter_rt_baghdad.isoformat(),
                "channel_id": self.channel_id, "created_at": datetime.now(UTC).isoformat(),
            }
            try:
                scheduler.add_job(run_job, DateTrigger(run_date=chapter_rt_utc, timezone=UTC),
                                   args=[job], id=job_id, replace_existing=True)
                jobs_db["jobs"].append(job); scheduled += 1; stats.record_scheduled()
            except Exception as e:
                log.error(f"فشل جدولة الفصل {num}: {e}")
        await save_jobs()
        last_rt = rt + timedelta(hours=self.interval * (len(self.tasks) - 1))
        await i.edit_original_response(
            embed=ok_embed("تمت الجدولة الجماعية",
                f"**الرواية:** {self._novel_nm()}\n**{scheduled}** فصل مجدول\n"
                f"**من:** `{rt.strftime('%Y-%m-%d %H:%M')}`\n"
                f"**حتى:** `{last_rt.strftime('%Y-%m-%d %H:%M')}`\n"
                f"**الفاصل:** {self.interval:.0f} ساعة")
        )
        self.stop()

    async def _on_restart(self, i):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.year = self.month = self.day = self.hour24 = self.minute = self.interval = None
        self._render_step(1)
        await i.response.edit_message(
            embed=make_embed("ابدأ من جديد — اختر السنة",
                f"**الرواية:** {self._novel_nm()}\n**{len(self.tasks)} فصل** للجدولة\n\n{_progress_bar(0, 6)}",
                Colors.PURPLE),
            view=self
        )

    async def _on_cancel(self, i):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        await i.response.edit_message(embed=warn_embed("تم الإلغاء"), view=None)
        self.stop()


class AddAccountModal(discord.ui.Modal):
    name_input  = discord.ui.TextInput(label="اسم الحساب",       placeholder="حسابي الشخصي",    required=True, max_length=100)
    email_input = discord.ui.TextInput(label="البريد الإلكتروني", placeholder="example@email.com", required=True, max_length=200)
    token_input = discord.ui.TextInput(label="توكن API",          placeholder="أدخل التوكن هنا",   required=True, min_length=10, max_length=100)

    def __init__(self):
        super().__init__(title="إضافة حساب جديد")

    async def on_submit(self, interaction: discord.Interaction):
        name = self.name_input.value.strip(); email = self.email_input.value.strip(); token = self.token_input.value.strip()
        if account_manager.add_account(name, email, token):
            await interaction.response.send_message(embed=ok_embed("تمت الإضافة", f"الحساب **{name}** ({email}) أُضيف بنجاح."))
        else:
            await interaction.response.send_message(embed=err_embed("خطأ", "التوكن موجود مسبقاً لحساب آخر."), ephemeral=True)


class NovelSelectView(discord.ui.View):
    def __init__(self, uid: int):
        super().__init__(timeout=90)
        self.uid = uid; self.slug: Optional[str] = None
        opts = [
            discord.SelectOption(label=n["english"][:80], description=f"{n['arabic'][:80]}", value=n["slug"], emoji="📚")
            for n in novel_store.novels[:25]
        ]
        if opts:
            sel = discord.ui.Select(placeholder="اختر رواية...", options=opts)
            sel.callback = self._cb; self.add_item(sel)

    async def _cb(self, i: discord.Interaction):
        if i.user.id != self.uid:
            return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.slug = i.data["values"][0]
        for c in self.children: c.disabled = True
        await i.response.edit_message(embed=inf_embed("تم الاختيار", f"الرواية: `{self.slug}`"), view=self)
        self.stop()


class SearchResultView(discord.ui.View):
    def __init__(self, results: list, uid: int):
        super().__init__(timeout=90)
        self.uid = uid; self._results = results; self.selected: Optional[dict] = None
        opts = [
            discord.SelectOption(label=n["english"][:80], description=n["arabic"][:80], value=n["slug"], emoji="🔍")
            for n in results[:25]
        ]
        sel = discord.ui.Select(placeholder="اختر من نتائج البحث...", options=opts)
        sel.callback = self._cb; self.add_item(sel)

    async def _cb(self, i: discord.Interaction):
        if i.user.id != self.uid:
            return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        slug = i.data["values"][0]; self.selected = next((n for n in self._results if n["slug"] == slug), None)
        for c in self.children: c.disabled = True
        await i.response.edit_message(view=self); self.stop()


class UploadTxtView(discord.ui.View):
    def __init__(self, uid: int, cid: int):
        super().__init__(timeout=180)
        self.uid = uid; self.cid = cid; self.content: Optional[str] = None; self._done = asyncio.Event()

    @discord.ui.button(label="رفع ملف TXT", style=discord.ButtonStyle.primary)
    async def upload_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.uid:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        button.disabled = True; button.label = "في انتظار الملف..."
        await interaction.response.edit_message(view=self)
        await interaction.followup.send(embed=inf_embed("أرسل الملف الآن", "أرسل ملف `.txt` في هذه القناة خلال 3 دقائق."))
        def check(m):
            return m.author.id == self.uid and m.channel.id == self.cid and m.attachments
        try:
            msg = await bot.wait_for("message", check=check, timeout=180)
            att = msg.attachments[0]
            if not att.filename.lower().endswith(".txt"):
                await interaction.followup.send(embed=err_embed("نوع خاطئ", "يجب أن يكون الملف `.txt`"))
                return
            self.content = normalize_content(decode_bytes(await att.read()), to_html=True)
            self._done.set()
            await interaction.followup.send(embed=ok_embed("تم الاستلام", f"`{att.filename}` — {len(self.content):,} حرف"))
        except asyncio.TimeoutError:
            await interaction.followup.send(embed=err_embed("انتهى الوقت", "لم يُرسل أي ملف."))

    @discord.ui.button(label="إلغاء", style=discord.ButtonStyle.danger)
    async def cancel_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.uid:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        await interaction.response.edit_message(embed=warn_embed("تم الإلغاء"), view=None); self.stop()

    async def wait_file(self) -> bool:
        try:
            await asyncio.wait_for(self._done.wait(), timeout=200); return self.content is not None
        except asyncio.TimeoutError:
            return False


class UploadZipView(discord.ui.View):
    def __init__(self, uid: int, cid: int):
        super().__init__(timeout=180)
        self.uid = uid; self.cid = cid; self.zip_bytes: Optional[bytes] = None; self._done = asyncio.Event()

    @discord.ui.button(label="رفع ملف ZIP", style=discord.ButtonStyle.primary)
    async def upload_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.uid:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        button.disabled = True; button.label = "في انتظار الملف..."
        await interaction.response.edit_message(view=self)
        await interaction.followup.send(embed=inf_embed("أرسل ملف ZIP", "أرسل ملف `.zip` في هذه القناة."))
        def check(m):
            return m.author.id == self.uid and m.channel.id == self.cid and m.attachments
        try:
            msg = await bot.wait_for("message", check=check, timeout=180)
            att = msg.attachments[0]
            if not att.filename.lower().endswith(".zip"):
                await interaction.followup.send(embed=err_embed("نوع خاطئ", "يجب أن يكون الملف `.zip`")); return
            self.zip_bytes = await att.read(); self._done.set()
            await interaction.followup.send(embed=ok_embed("تم الاستلام", f"حجم الملف: {len(self.zip_bytes):,} بايت"))
        except asyncio.TimeoutError:
            await interaction.followup.send(embed=err_embed("انتهى الوقت", "لم يُرسل أي ملف."))

    async def wait_zip(self) -> bool:
        try:
            await asyncio.wait_for(self._done.wait(), timeout=200); return self.zip_bytes is not None
        except asyncio.TimeoutError:
            return False


class ConfirmPublishView(discord.ui.View):
    def __init__(self, slug: str, number: int, chap_title: str, content: str, uid: int, cid: int):
        super().__init__(timeout=120)
        self.slug = slug; self.number = number; self.chap_title = chap_title
        self.content = content; self.uid = uid; self.cid = cid

    @discord.ui.button(label="نشر الآن", style=discord.ButtonStyle.success)
    async def publish_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.uid:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        await interaction.response.defer()
        novel = novel_store.get_novel(self.slug); api = NovelAPI()
        await interaction.edit_original_response(
            embed=make_embed("جارٍ النشر...", f"الفصل {self.number}: {self.chap_title}", Colors.WARNING), view=None
        )
        ok, msg = await api.publish(self.slug, self.number, self.chap_title, self.content)
        stats.record(ok); account_manager.record_publish(ok)
        if ok:
            novel_store.inc_published(self.slug)
            if ann_queue is not None:
                cover = await ann_cog.get_cover(self.slug) if ann_cog else None
                novel_arabic = novel["arabic"] if novel else self.slug
                await ann_queue.register_publish(
                    novel_arabic=novel_arabic,
                    slug=self.slug,
                    first_chapter=self.number,
                    last_chapter=self.number,
                    cover_bytes=cover,
                    source="manual",
                )
        novel_nm = novel["arabic"] if novel else self.slug
        await interaction.edit_original_response(
            embed=ok_embed("نُشر بنجاح",
                f"**الرواية:** {novel_nm}\n**الفصل {self.number}:** {self.chap_title}\n**الحجم:** {len(self.content):,} حرف"
            ) if ok else err_embed("فشل النشر", f"```{msg[:400]}```")
        )
        self.stop()

    @discord.ui.button(label="جدولة بدلاً من ذلك", style=discord.ButtonStyle.secondary)
    async def schedule_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.uid:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        novel_nm = (novel_store.get_novel(self.slug) or {}).get("arabic", self.slug)
        view = SchedulePickerView(self.slug, self.number, self.chap_title, self.content, self.cid, self.uid)
        await interaction.response.edit_message(
            embed=make_embed("اختر السنة",
                f"**الرواية:** {novel_nm}\n**الفصل {self.number}:** {self.chap_title}\n\n{_progress_bar(0)}",
                Colors.PURPLE),
            view=view
        ); self.stop()

    @discord.ui.button(label="إلغاء", style=discord.ButtonStyle.danger)
    async def cancel_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.uid:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        await interaction.response.edit_message(embed=warn_embed("تم الإلغاء"), view=None); self.stop()


class BatchConfirmView(discord.ui.View):
    def __init__(self, slug: str, tasks: list, novel: Optional[dict], uid: int, cid: int):
        super().__init__(timeout=120)
        self.slug = slug; self.tasks = tasks; self.novel = novel; self.uid = uid; self.cid = cid

    @discord.ui.button(label="نشر الكل الآن", style=discord.ButtonStyle.success)
    async def publish_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.uid:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        await interaction.response.defer()
        novel_nm = self.novel["arabic"] if self.novel else self.slug
        api = NovelAPI(); total = len(self.tasks); pub = fail = 0; failed_list = []
        prog = await interaction.channel.send(
            embed=make_embed(f"النشر الجماعي — {novel_nm}", f"جارٍ نشر **{total}** فصل...\n⬜ 0/{total}", Colors.INFO)
        )
        first_published_num = None
        last_published_num = None
        for i, (num, chap_t, content) in enumerate(self.tasks, 1):
            ok, _ = await api.publish(self.slug, num, chap_t, content)
            if ok:
                pub += 1; stats.record(True); account_manager.record_publish(True)
                if first_published_num is None:
                    first_published_num = num
                last_published_num = num
            else:
                fail += 1; failed_list.append(num); stats.record(False); account_manager.record_publish(False)
            filled = int(i / total * 20); bar = "🟩" * filled + "⬜" * (20 - filled)
            if i % 3 == 0 or i == total:
                await prog.edit(embed=make_embed(f"النشر الجماعي — {novel_nm}",
                    f"{bar}\n**{int(i/total*100)}%** — {i}/{total}\n✅ {pub} | ❌ {fail}", Colors.INFO))
            await asyncio.sleep(1.2)
        novel_store.inc_published(self.slug, pub)
        if pub > 0 and ann_queue is not None and last_published_num is not None:
            cover = await ann_cog.get_cover(self.slug) if ann_cog else None
            await ann_queue.register_publish(
                novel_arabic=novel_nm,
                slug=self.slug,
                first_chapter=first_published_num,
                last_chapter=last_published_num,
                cover_bytes=cover,
                source="batch",
            )
        failed_str = ", ".join(str(n) for n in failed_list) if failed_list else "لا شيء"
        await prog.edit(embed=make_embed(
            f"{'اكتمل النشر الجماعي' if fail==0 else 'اكتمل مع أخطاء'}",
            f"**الرواية:** {novel_nm}\nتم: {pub} | فشل: {fail}\n"
            + (f"**الفصول الفاشلة:** {failed_str}" if failed_list else ""),
            Colors.SUCCESS if fail == 0 else Colors.WARNING
        ))
        self.stop()

    @discord.ui.button(label="جدولة الكل", style=discord.ButtonStyle.secondary)
    async def sched_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.uid:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        novel_nm = self.novel["arabic"] if self.novel else self.slug
        view = BatchSchedulePickerView(self.slug, self.tasks, self.novel, self.cid, self.uid)
        await interaction.response.edit_message(
            embed=make_embed("جدولة جماعية — اختر السنة",
                f"**الرواية:** {novel_nm}\n**{len(self.tasks)} فصل** للجدولة\n\n{_progress_bar(0, 6)}",
                Colors.PURPLE),
            view=view
        ); self.stop()

    @discord.ui.button(label="إلغاء", style=discord.ButtonStyle.danger)
    async def cancel_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.uid:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        await interaction.response.edit_message(embed=warn_embed("تم الإلغاء"), view=None); self.stop()


# ══════════════════════════════════════════════════════════════
#  Views النشر التسلسلي (تم تعديلها لتستخدم MongoDB مباشرة)
# ══════════════════════════════════════════════════════════════

class DailyTimePickerView(discord.ui.View):
    def __init__(self, uid: int):
        super().__init__(timeout=180)
        self.uid     = uid
        self.hour24: Optional[int] = None
        self.minute: Optional[int] = None
        self.done    = False
        self._render_hour()

    def _guard(self, i: discord.Interaction) -> bool:
        return i.user.id == self.uid

    def _render_hour(self):
        self.clear_items()
        am_opts = [discord.SelectOption(label=f"{h:02d}:00 صباحاً", value=f"am_{h}", emoji="🌅") for h in range(1, 13)]
        pm_opts = [discord.SelectOption(label=f"{h:02d}:00 مساءً",  value=f"pm_{h}", emoji="🌆") for h in range(1, 13)]
        sel_am  = discord.ui.Select(placeholder="صباحاً — اختر الساعة...", options=am_opts)
        sel_am.callback = self._on_hour
        sel_pm  = discord.ui.Select(placeholder="مساءً — اختر الساعة...",  options=pm_opts)
        sel_pm.callback = self._on_hour
        self.add_item(sel_am); self.add_item(sel_pm)
        cancel = discord.ui.Button(label="إلغاء", style=discord.ButtonStyle.danger)
        cancel.callback = self._on_cancel
        self.add_item(cancel)

    def _render_minute(self):
        self.clear_items()
        sel = discord.ui.Select(placeholder="اختر الدقيقة...", options=_build_minute_options()[:25])
        sel.callback = self._on_minute
        back = discord.ui.Button(label="رجوع للساعة", style=discord.ButtonStyle.secondary)
        back.callback = self._on_back
        cancel = discord.ui.Button(label="إلغاء", style=discord.ButtonStyle.danger)
        cancel.callback = self._on_cancel
        self.add_item(sel); self.add_item(back); self.add_item(cancel)

    async def _on_hour(self, i: discord.Interaction):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        val = i.data["values"][0]; period, h = val.split("_")
        self.hour24 = _to_24h(period, int(h))
        h12 = int(h); per_ar = "صباحاً" if period == "am" else "مساءً"
        self._render_minute()
        await i.response.edit_message(
            embed=make_embed("اختر الدقيقة",
                f"الساعة المختارة: **{h12:02d} {per_ar}**\n\nالآن اختر الدقيقة:", Colors.PURPLE),
            view=self
        )

    async def _on_minute(self, i: discord.Interaction):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.minute = int(i.data["values"][0])
        self.done   = True
        h12 = self.hour24 % 12 or 12; per_ar = "صباحاً" if self.hour24 < 12 else "مساءً"
        self.clear_items()
        await i.response.edit_message(
            embed=make_embed("تم تحديد الوقت اليومي",
                f"سينشر البوت كل يوم الساعة **{h12:02d}:{self.minute:02d} {per_ar}** (بغداد)",
                Colors.SUCCESS),
            view=self
        )
        self.stop()

    async def _on_back(self, i: discord.Interaction):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.hour24 = None; self._render_hour()
        await i.response.edit_message(
            embed=make_embed("اختر الساعة", "اختر الساعة (صباحاً أو مساءً):", Colors.PURPLE), view=self
        )

    async def _on_cancel(self, i: discord.Interaction):
        if not self._guard(i): return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        await i.response.edit_message(embed=warn_embed("تم الإلغاء"), view=None); self.stop()


class SerialChaptersPreviewView(discord.ui.View):
    PER_PAGE = 10

    def __init__(self, chapters: list, doc: dict, uid: int):
        super().__init__(timeout=120)
        self.chapters = chapters; self.doc = doc; self.uid = uid; self.page = 0
        self._refresh_buttons()

    @property
    def total_pages(self):
        return max(1, (len(self.chapters) + self.PER_PAGE - 1) // self.PER_PAGE)

    def _build_embed(self) -> discord.Embed:
        doc   = self.doc; total = doc.get("total_chapters", len(self.chapters))
        done  = doc.get("published_count", 0); batch = doc.get("batch_size", 1)
        h, m  = doc.get("hour", 0), doc.get("minute", 0)
        h12   = h % 12 or 12; per_ar = "صباحاً" if h < 12 else "مساءً"
        remaining    = total - done
        batches_left = max(0, (remaining + batch - 1) // batch) if remaining > 0 else 0

        embed = make_embed(
            f"{doc.get('novel_arabic','الرواية')} — معاينة الجدول التسلسلي",
            f"`{_serial_bar(done, total)}`\n\n"
            f"**وقت النشر:** `{h12:02d}:{m:02d} {per_ar}` يومياً (بغداد)\n"
            f"**الدفعة:** `{batch}` فصل | **دفعات متبقية:** `{batches_left}`\n"
            f"**منشور:** `{done}` | **متبقٍ:** `{remaining}`",
            Colors.PURPLE
        )
        start = self.page * self.PER_PAGE
        page_chs = self.chapters[start: start + self.PER_PAGE]
        lines = []
        for idx, ch in enumerate(page_chs, start=start):
            icon = "✅" if idx < done else ("🔜" if idx == done else "⏳")
            lines.append(f"{icon} **{ch['number']}** — {str(ch.get('title',''))[:45]}")
        embed.add_field(name=f"الفصول (صفحة {self.page+1}/{self.total_pages})",
                        value="\n".join(lines) if lines else "—", inline=False)
        embed.set_footer(text=f"ID: {doc['_id'][:14]}... | روايات Bot v{VERSION}")
        return embed

    def _refresh_buttons(self):
        self.clear_items()
        if self.page > 0:
            prev = discord.ui.Button(label="السابق", style=discord.ButtonStyle.secondary)
            prev.callback = self._prev; self.add_item(prev)
        if self.page < self.total_pages - 1:
            nxt = discord.ui.Button(label="التالي", style=discord.ButtonStyle.secondary)
            nxt.callback = self._next; self.add_item(nxt)
        close = discord.ui.Button(label="إغلاق", style=discord.ButtonStyle.danger)
        close.callback = self._close; self.add_item(close)

    async def _prev(self, i: discord.Interaction):
        self.page -= 1; self._refresh_buttons()
        await i.response.edit_message(embed=self._build_embed(), view=self)

    async def _next(self, i: discord.Interaction):
        self.page += 1; self._refresh_buttons()
        await i.response.edit_message(embed=self._build_embed(), view=self)

    async def _close(self, i: discord.Interaction):
        await i.response.edit_message(view=None); self.stop()


class SerialActionView(discord.ui.View):
    """عرض لإدارة جدول تسلسلي واحد (يستلم doc من MongoDB)"""
    def __init__(self, doc: dict, uid: int):
        super().__init__(timeout=90)
        self.doc = doc; self.uid = uid
        self._build()

    def _build(self):
        self.clear_items()
        preview_btn = discord.ui.Button(label="معاينة الفصول", style=discord.ButtonStyle.primary)
        preview_btn.callback = self._preview; self.add_item(preview_btn)

        if self.doc.get("paused"):
            resume_btn = discord.ui.Button(label="استئناف النشر", style=discord.ButtonStyle.success)
            resume_btn.callback = self._resume; self.add_item(resume_btn)
        else:
            pause_btn = discord.ui.Button(label="إيقاف مؤقت", style=discord.ButtonStyle.secondary)
            pause_btn.callback = self._pause; self.add_item(pause_btn)

        # زر تبديل الإعلان
        ann_on = self.doc.get("announce_enabled", True)
        ann_label = "الإعلان: مفعّل" if ann_on else "الإعلان: معطّل"
        ann_style = discord.ButtonStyle.success if ann_on else discord.ButtonStyle.secondary
        ann_btn = discord.ui.Button(label=ann_label, style=ann_style, emoji="📢")
        ann_btn.callback = self._toggle_announce; self.add_item(ann_btn)

        delete_btn = discord.ui.Button(label="حذف الجدول", style=discord.ButtonStyle.danger)
        delete_btn.callback = self._delete; self.add_item(delete_btn)

    def _detail_embed(self) -> discord.Embed:
        doc   = self.doc; total = doc.get("total_chapters", 0)
        done  = doc.get("published_count", 0); batch = doc.get("batch_size", 1)
        h, m  = doc.get("hour", 0), doc.get("minute", 0)
        h12   = h % 12 or 12; per_ar = "صباحاً" if h < 12 else "مساءً"
        remaining = total - done
        status    = "متوقف مؤقتاً" if doc.get("paused") else ("مكتمل" if doc.get("finished") else "نشط")
        color     = Colors.WARNING if doc.get("paused") else (Colors.GOLD if doc.get("finished") else Colors.SUCCESS)
        ann_icon  = "📢 مفعّل" if doc.get("announce_enabled", True) else "🔕 معطّل"
        return make_embed(
            f"{doc.get('novel_arabic','الرواية')}",
            f"`{_serial_bar(done, total)}`\n\n"
            f"**الحالة:** {status}\n"
            f"**وقت النشر:** `{h12:02d}:{m:02d} {per_ar}` يومياً\n"
            f"**الدفعة:** `{batch}` فصل\n"
            f"**الإعلان التلقائي:** {ann_icon}\n"
            f"**منشور:** `{done}` | **متبقٍ:** `{remaining}`",
            color
        )

    async def _preview(self, i: discord.Interaction):
        if i.user.id != self.uid: return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        # جلب الفصول من serial_chapters (بدون المحتوى)
        db = db_client.get_database("rewyat_bot")
        chapters_cursor = db.serial_chapters.find(
            {"serial_id": self.doc["_id"]},
            {"content_compressed": 0}   # استبعاد المحتوى لتخفيف الحجم
        ).sort("number", 1)
        chapters = await chapters_cursor.to_list(length=10000)
        view = SerialChaptersPreviewView(chapters, self.doc, self.uid)
        view._refresh_buttons()
        await i.response.send_message(embed=view._build_embed(), view=view, ephemeral=True)

    async def _pause(self, i: discord.Interaction):
        if i.user.id != self.uid: return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        sid = self.doc["_id"]
        db = db_client.get_database("rewyat_bot")
        await db.serial_schedules.update_one({"_id": sid}, {"$set": {"paused": True}})
        self.doc["paused"] = True
        for slot_doc in _serial_slots(self.doc):
            try: scheduler.pause_job(f"serial_{sid}_{slot_doc['slot']}")
            except Exception: pass
        self._build()
        await i.response.edit_message(embed=self._detail_embed(), view=self)

    async def _resume(self, i: discord.Interaction):
        if i.user.id != self.uid: return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        sid = self.doc["_id"]
        db = db_client.get_database("rewyat_bot")
        await db.serial_schedules.update_one({"_id": sid}, {"$set": {"paused": False}})
        self.doc["paused"] = False
        try:
            for slot_doc in _serial_slots(self.doc):
                scheduler.resume_job(f"serial_{sid}_{slot_doc['slot']}")
        except Exception:
            try:
                for slot_doc in _serial_slots(self.doc):
                    scheduler.add_job(run_serial_batch_for_slot, CronTrigger(hour=slot_doc["hour"], minute=slot_doc["minute"], timezone=BAGHDAD_TZ),
                                      args=[sid, slot_doc["slot"]], id=f"serial_{sid}_{slot_doc['slot']}", replace_existing=True)
            except Exception as e:
                log.error(f"[Serial] فشل استئناف {sid}: {e}")
        self._build()
        await i.response.edit_message(embed=self._detail_embed(), view=self)

    async def _delete(self, i: discord.Interaction):
        if i.user.id != self.uid: return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        sid = self.doc["_id"]
        db = db_client.get_database("rewyat_bot")
        # حذف الجدول وجميع فصوله
        await db.serial_schedules.delete_one({"_id": sid})
        await db.serial_chapters.delete_many({"serial_id": sid})
        await db.failed_serial_chapters.delete_many({"serial_id": sid})
        for slot_doc in _serial_slots(self.doc):
            try: scheduler.remove_job(f"serial_{sid}_{slot_doc['slot']}")
            except Exception: pass
        self.clear_items()
        await i.response.edit_message(
            embed=ok_embed("تم الحذف", f"تم حذف جدول **{self.doc.get('novel_arabic','الرواية')}** بنجاح."),
            view=None
        ); self.stop()

    async def _toggle_announce(self, i: discord.Interaction):
        if i.user.id != self.uid: return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        new_val = not self.doc.get("announce_enabled", True)
        sid = self.doc["_id"]
        db = db_client.get_database("rewyat_bot")
        await db.serial_schedules.update_one({"_id": sid}, {"$set": {"announce_enabled": new_val}})
        self.doc["announce_enabled"] = new_val
        self._build()
        await i.response.edit_message(embed=self._detail_embed(), view=self)


class SerialListView(discord.ui.View):
    def __init__(self, docs: list, uid: int):
        super().__init__(timeout=120)
        self.docs = docs; self.uid = uid
        if docs:
            options = [
                discord.SelectOption(
                    label=f"{d.get('novel_arabic','?')[:40]} — {d.get('batch_size',1)} فصل/يوم",
                    value=d["_id"],
                    description=f"{'متوقف' if d.get('paused') else ('مكتمل' if d.get('finished') else 'نشط')} {d.get('published_count',0)}/{d.get('total_chapters',0)} فصل",
                    emoji="📖"
                ) for d in docs[:25]
            ]
            sel = discord.ui.Select(placeholder="اختر جدولاً لإدارته...", options=options)
            sel.callback = self._on_select; self.add_item(sel)

    async def _on_select(self, i: discord.Interaction):
        if i.user.id != self.uid: return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        sid = i.data["values"][0]; doc = next((d for d in self.docs if d["_id"] == sid), None)
        if not doc: return await i.response.send_message(embed=err_embed("غير موجود"), ephemeral=True)
        action_view = SerialActionView(doc, self.uid)
        await i.response.send_message(embed=action_view._detail_embed(), view=action_view, ephemeral=True)


# ══════════════════════════════════════════════════════════════
#  معالج النشر التسلسلي (SerialPublisher) — تم تعديل حفظ الفصول
# ══════════════════════════════════════════════════════════════

class SerialPublisher:
    def __init__(self, interaction: discord.Interaction):
        self.interaction      = interaction
        self.slug:            Optional[str]  = None
        self.novel:           Optional[dict] = None
        self.chapters:        List[dict]     = []
        self.zip_bytes:       Optional[bytes]= None
        self.batch_size:      int            = 1
        self.hour24:          int            = 10
        self.minute:          int            = 0
        self.second_hour24:   Optional[int]  = None
        self.second_minute:   Optional[int]  = None
        self.announce_enabled: bool          = True

    async def run(self):
        try:
            await self._step_select_novel()
            await self._step_upload_zip()
            await self._step_extract_chapters()
            await self._step_batch_size()
            await self._step_daily_time()
            await self._step_announce_option()
            await self._step_preview_confirm()
            await self._step_create_schedule()
        except asyncio.TimeoutError:
            return

    async def _step_select_novel(self):
        novels = novel_store.novels
        if not novels:
            await self.interaction.followup.send(
                embed=err_embed("لا روايات", "استخدم `/بحث_رواية` لإضافة روايات أولاً.")
            )
            raise asyncio.TimeoutError()

        if len(novels) == 1:
            self.slug  = novels[0]["slug"]
            self.novel = novels[0]
            await self.interaction.followup.send(
                embed=ok_embed("تم اختيار الرواية", f"**{self.novel['arabic']}** — `{self.slug}`")
            )
            return

        view = NovelSelectView(self.interaction.user.id)
        await self.interaction.followup.send(
            embed=inf_embed("نشر تسلسلي — الخطوة 1/5", "اختر الرواية التي تريد رفع فصولها بشكل يومي تسلسلي."),
            view=view
        )
        await view.wait()
        if not view.slug:
            raise asyncio.TimeoutError()
        self.slug  = view.slug
        self.novel = novel_store.get_novel(self.slug)

    async def _step_upload_zip(self):
        novel_nm = self.novel["arabic"] if self.novel else self.slug
        zip_view = UploadZipView(self.interaction.user.id, self.interaction.channel_id)
        await self.interaction.followup.send(
            embed=make_embed("نشر تسلسلي — الخطوة 2/5",
                f"**الرواية:** {novel_nm}\n\n"
                "أرسل ملف **ZIP** يحتوي على **جميع** فصول الرواية.\n"
                "الصيغ المدعومة: `.txt`\n\n"
                "اضغط الزر لرفع الملف.",
                Colors.PURPLE),
            view=zip_view
        )
        if not await zip_view.wait_zip():
            await self.interaction.followup.send(embed=err_embed("انتهى الوقت", "لم يُرفع أي ملف."))
            raise asyncio.TimeoutError()
        self.zip_bytes = zip_view.zip_bytes

    async def _step_extract_chapters(self):
        novel_nm = self.novel["arabic"] if self.novel else self.slug
        status = await self.interaction.followup.send(
            embed=make_embed("جاري استخراج الفصول...", "جاري المعالجة...", Colors.WARNING)
        )

        tasks = await process_zip(self.zip_bytes)
        if not tasks:
            await status.edit(embed=err_embed("ZIP فارغ", "لم يُعثر على فصول صالحة."))
            raise asyncio.TimeoutError()

        self.chapters = [
            {"number": num, "title": title, "content": content}
            for num, title, content in tasks
        ]

        preview_text = "\n".join(
            f"**{ch['number']}** — {ch['title'][:50]}"
            for ch in self.chapters[:10]
        )
        if len(self.chapters) > 10:
            preview_text += f"\n... و **{len(self.chapters) - 10}** فصول أخرى"

        await status.edit(
            embed=make_embed(f"تم استخراج {len(self.chapters)} فصل",
                f"**الرواية:** {novel_nm}\n\n{preview_text}",
                Colors.SUCCESS)
        )

    async def _step_batch_size(self):
        total = len(self.chapters)
        view = discord.ui.View(timeout=120)
        options = [
            discord.SelectOption(label=f"{n} فصل في كل مرة", value=str(n), emoji="📦")
            for n in [1, 2, 3, 5, 10, 15, 20, 25, 30]
        ]
        sel = discord.ui.Select(placeholder=f"اختر عدد الفصول لكل دفعة يومية (المجموع: {total} فصل)...", options=options)
        chosen = {}

        async def sel_cb(interaction: discord.Interaction):
            if interaction.user.id != self.interaction.user.id:
                return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
            chosen["n"] = int(interaction.data["values"][0])
            batches = (total + chosen["n"] - 1) // chosen["n"]
            await interaction.response.edit_message(
                embed=make_embed("تم الاختيار",
                    f"ستُنشر **{chosen['n']}** فصل يومياً.\n"
                    f"إجمالي الدفعات: **{batches}** دفعة\n"
                    f"المدة التقريبية: **{batches}** يوم",
                    Colors.SUCCESS),
                view=None
            )
            view.stop()

        sel.callback = sel_cb
        view.add_item(sel)
        novel_nm = self.novel["arabic"] if self.novel else self.slug
        await self.interaction.followup.send(
            embed=make_embed("نشر تسلسلي — الخطوة 3/5",
                f"**الرواية:** {novel_nm}\n"
                f"عدد الفصول: **{total}**\n\n"
                f"كم فصلاً تريد نشره في كل مرة (يومياً)؟",
                Colors.PURPLE),
            view=view
        )
        await view.wait()
        if "n" not in chosen:
            raise asyncio.TimeoutError()
        self.batch_size = chosen["n"]

    async def _step_daily_time(self):
        novel_nm = self.novel["arabic"] if self.novel else self.slug
        time_view = DailyTimePickerView(self.interaction.user.id)
        await self.interaction.followup.send(
            embed=make_embed("نشر تسلسلي — الخطوة 4/5",
                f"**الرواية:** {novel_nm}\n\n"
                "حدد الوقت الذي يتم فيه النشر كل يوم.\n"
                "اختر الساعة (صباحاً أو مساءً) ثم الدقيقة.",
                Colors.PURPLE),
            view=time_view
        )
        await time_view.wait()
        if not time_view.done:
            raise asyncio.TimeoutError()
        self.hour24 = time_view.hour24
        self.minute = time_view.minute
        view = discord.ui.View(timeout=60)
        chosen = {}
        add_btn = discord.ui.Button(label="إضافة موعد ثانٍ اختياري", style=discord.ButtonStyle.primary, emoji="➕")
        skip_btn = discord.ui.Button(label="وقت واحد فقط", style=discord.ButtonStyle.secondary)

        async def add_cb(interaction: discord.Interaction):
            if interaction.user.id != self.interaction.user.id:
                return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
            chosen["add"] = True
            await interaction.response.edit_message(embed=inf_embed("اختيار الموعد الثاني", "اختر الموعد الثاني في الرسالة التالية."), view=None)
            view.stop()

        async def skip_cb(interaction: discord.Interaction):
            if interaction.user.id != self.interaction.user.id:
                return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
            chosen["add"] = False
            await interaction.response.edit_message(embed=ok_embed("وقت واحد", "سيتم نشر كامل الدفعة اليومية في موعد واحد."), view=None)
            view.stop()

        add_btn.callback = add_cb; skip_btn.callback = skip_cb
        view.add_item(add_btn); view.add_item(skip_btn)
        await self.interaction.followup.send(
            embed=make_embed("موعد ثانٍ اختياري",
                "هل تريد تقسيم دفعة اليوم على موعدين؟\n"
                "إذا اخترت موعداً ثانياً سيُقسّم عدد الفصول اليومي بين الموعدين.",
                Colors.PURPLE),
            view=view
        )
        await view.wait()
        if chosen.get("add"):
            second_view = DailyTimePickerView(self.interaction.user.id)
            await self.interaction.followup.send(embed=make_embed("اختر الموعد الثاني", color=Colors.PURPLE), view=second_view)
            await second_view.wait()
            if not second_view.done:
                raise asyncio.TimeoutError()
            self.second_hour24 = second_view.hour24
            self.second_minute = second_view.minute

    async def _step_announce_option(self):
        novel_nm = self.novel["arabic"] if self.novel else self.slug
        view = discord.ui.View(timeout=60)
        chosen = {}

        yes_btn = discord.ui.Button(label="نعم — إعلان تلقائي", style=discord.ButtonStyle.success, emoji="📢")
        no_btn  = discord.ui.Button(label="لا — أنشر بدون إعلان", style=discord.ButtonStyle.secondary, emoji="🔕")

        async def yes_cb(interaction: discord.Interaction):
            if interaction.user.id != self.interaction.user.id: return
            chosen["v"] = True
            for item in view.children: item.disabled = True
            await interaction.response.edit_message(
                embed=ok_embed("إعلان تلقائي مفعّل", "سيُعلن البوت بعد كل دفعة تلقائياً."), view=view)
            view.stop()

        async def no_cb(interaction: discord.Interaction):
            if interaction.user.id != self.interaction.user.id: return
            chosen["v"] = False
            for item in view.children: item.disabled = True
            await interaction.response.edit_message(
                embed=inf_embed("بدون إعلان تلقائي", "يمكنك الإعلان يدوياً عبر `/إعلان_يدوي`."), view=view)
            view.stop()

        yes_btn.callback = yes_cb
        no_btn.callback  = no_cb
        view.add_item(yes_btn); view.add_item(no_btn)

        await self.interaction.followup.send(
            embed=make_embed("نشر تسلسلي — الإعلان",
                f"**الرواية:** {novel_nm}\n\n"
                "هل تريد من البوت أن يُرسل إعلاناً تلقائياً في قناة الإعلانات بعد كل دفعة نشر؟\n\n"
                "يمكنك تغيير هذا لاحقاً من إعدادات الجدول.",
                Colors.PURPLE),
            view=view
        )
        await view.wait()
        self.announce_enabled = chosen.get("v", True)

    async def _step_preview_confirm(self):
        novel_nm = self.novel["arabic"] if self.novel else self.slug
        total = len(self.chapters)
        batches = (total + self.batch_size - 1) // self.batch_size
        h12 = self.hour24 % 12 or 12
        per_ar = "صباحاً" if self.hour24 < 12 else "مساءً"
        time_text = f"**{h12:02d}:{self.minute:02d} {per_ar}** يومياً"
        if self.second_hour24 is not None:
            h12b = self.second_hour24 % 12 or 12
            per_arb = "صباحاً" if self.second_hour24 < 12 else "مساءً"
            first_size = (self.batch_size + 1) // 2
            second_size = self.batch_size - first_size
            time_text = (
                f"الأول: **{h12:02d}:{self.minute:02d} {per_ar}** ({first_size} فصل)\n"
                f"الثاني: **{h12b:02d}:{self.second_minute:02d} {per_arb}** ({second_size} فصل)"
            )

        confirm_view = discord.ui.View(timeout=120)
        confirmed = {}

        confirm_btn = discord.ui.Button(label="بدء الجدول", style=discord.ButtonStyle.success)
        preview_btn = discord.ui.Button(label="معاينة الفصول", style=discord.ButtonStyle.primary)
        cancel_btn  = discord.ui.Button(label="إلغاء", style=discord.ButtonStyle.danger)

        async def confirm_cb(interaction: discord.Interaction):
            if interaction.user.id != self.interaction.user.id:
                return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
            confirmed["yes"] = True
            for item in confirm_view.children: item.disabled = True
            await interaction.response.edit_message(view=confirm_view)
            confirm_view.stop()

        async def preview_cb(interaction: discord.Interaction):
            if interaction.user.id != self.interaction.user.id:
                return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
            lines = []
            for ch in self.chapters[:15]:
                lines.append(f"**{ch['number']}** — {str(ch.get('title',''))[:50]}")
            if len(self.chapters) > 15:
                lines.append(f"*...و {len(self.chapters) - 15} فصل آخر*")
            preview_embed = make_embed(f"معاينة — {novel_nm}", "\n".join(lines), Colors.PURPLE)
            preview_embed.set_footer(text=f"إجمالي: {len(self.chapters)} فصل")
            await interaction.response.send_message(embed=preview_embed, ephemeral=True)

        async def cancel_cb(interaction: discord.Interaction):
            if interaction.user.id != self.interaction.user.id:
                return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
            confirmed["no"] = True
            await interaction.response.edit_message(embed=warn_embed("تم الإلغاء"), view=None)
            confirm_view.stop()

        confirm_btn.callback = confirm_cb
        preview_btn.callback = preview_cb
        cancel_btn.callback  = cancel_cb
        confirm_view.add_item(confirm_btn)
        confirm_view.add_item(preview_btn)
        confirm_view.add_item(cancel_btn)

        embed = make_embed("مراجعة الجدول التسلسلي", color=Colors.GOLD)
        embed.description = "**تأكد من التفاصيل قبل البدء:**\n" + "━" * 30
        embed.add_field(name="الرواية",          value=novel_nm,                                         inline=True)
        embed.add_field(name="إجمالي الفصول",    value=f"**{total}** فصل",                               inline=True)
        embed.add_field(name="الدفعة اليومية",   value=f"**{self.batch_size}** فصل/يوم",                  inline=True)
        embed.add_field(name="وقت النشر",         value=time_text, inline=True)
        embed.add_field(name="المدة التقريبية",   value=f"**{batches}** يوم",                             inline=True)
        embed.set_footer(text="اضغط 'بدء الجدول' للتأكيد أو 'معاينة الفصول' لمراجعتها")

        await self.interaction.followup.send(embed=embed, view=confirm_view)
        await confirm_view.wait()
        if "yes" not in confirmed:
            raise asyncio.TimeoutError()

    async def _step_create_schedule(self):
        """يحفظ الجدول والفصول في MongoDB مع ضغط المحتوى باستخدام gzip و Binary."""
        novel_nm = self.novel["arabic"] if self.novel else self.slug
        serial_id = f"serial_{self.interaction.user.id}_{int(datetime.utcnow().timestamp())}"

        db = db_client.get_database("rewyat_bot")

        # 1. حفظ الجدول الأساسي
        first_slot_size = self.batch_size
        slots = [{"slot": 1, "hour": self.hour24, "minute": self.minute, "size": self.batch_size}]
        if self.second_hour24 is not None:
            first_slot_size = (self.batch_size + 1) // 2
            second_slot_size = self.batch_size - first_slot_size
            slots = [
                {"slot": 1, "hour": self.hour24, "minute": self.minute, "size": first_slot_size},
                {"slot": 2, "hour": self.second_hour24, "minute": self.second_minute, "size": second_slot_size},
            ]

        schedule_doc = {
            "_id": serial_id,
            "slug": self.slug,
            "novel_arabic": novel_nm,
            "novel_english": self.novel["english"] if self.novel else "",
            "batch_size": self.batch_size,
            "total_chapters": len(self.chapters),
            "published_count": 0,
            "hour": self.hour24,
            "minute": self.minute,
            "slots": slots,
            "channel_id": self.interaction.channel_id,
            "guild_id": self.interaction.guild_id if self.interaction.guild else None,
            "created_by": self.interaction.user.id,
            "paused": False,
            "finished": False,
            "announce_enabled": self.announce_enabled,
            "created_at": datetime.now(BAGHDAD_TZ).isoformat()
        }
        await db.serial_schedules.update_one(
            {"_id": serial_id},
            {"$set": schedule_doc},
            upsert=True
        )

        # 2. حفظ الفصول في serial_chapters مع ضغط المحتوى
        chapters_col = db.serial_chapters
        for ch in self.chapters:
            compressed = gzip.compress(ch["content"].encode("utf-8"))
            await chapters_col.update_one(
                {"serial_id": serial_id, "number": ch["number"]},
                {"$set": {
                    "serial_id": serial_id,
                    "number": ch["number"],
                    "title": ch["title"],
                    "content_compressed": Binary(compressed)
                }},
                upsert=True
            )

        # 3. جدولة المهمة
        for slot_doc in slots:
            scheduler.add_job(
                run_serial_batch_for_slot,
                CronTrigger(hour=slot_doc["hour"], minute=slot_doc["minute"], timezone=BAGHDAD_TZ),
                args=[serial_id, slot_doc["slot"]],
                id=f"serial_{serial_id}_{slot_doc['slot']}",
                replace_existing=True
            )

        total = len(self.chapters)
        batches = (total + self.batch_size - 1) // self.batch_size
        h12 = self.hour24 % 12 or 12
        per_ar = "صباحاً" if self.hour24 < 12 else "مساءً"
        time_text = f"`{h12:02d}:{self.minute:02d} {per_ar}` يومياً"
        if self.second_hour24 is not None:
            h12b = self.second_hour24 % 12 or 12
            per_arb = "صباحاً" if self.second_hour24 < 12 else "مساءً"
            time_text = (
                f"الأول: `{h12:02d}:{self.minute:02d} {per_ar}` ({slots[0]['size']} فصل)\n"
                f"الثاني: `{h12b:02d}:{self.second_minute:02d} {per_arb}` ({slots[1]['size']} فصل)"
            )

        success_embed = make_embed("تم إنشاء الجدول التسلسلي بنجاح!", color=Colors.SUCCESS)
        success_embed.description = f"سينشر البوت فصول **{novel_nm}** تلقائياً كل يوم.\n\n`{_serial_bar(0, total)}`"
        success_embed.add_field(name="وقت النشر",      value=time_text, inline=True)
        success_embed.add_field(name="الدفعة",         value=f"`{self.batch_size}` فصل/مرة",                    inline=True)
        success_embed.add_field(name="عدد الدفعات",    value=f"`{batches}` دفعة",                              inline=True)
        success_embed.add_field(name="إجمالي الفصول",  value=f"`{total}` فصل",                                  inline=True)

        first_batch = self.chapters[:self.batch_size][:3]
        if first_batch:
            success_embed.add_field(
                name="أول 3 فصول",
                value="\n".join(f"**{ch['number']}** — {ch.get('title','')[:40]}" for ch in first_batch),
                inline=False
            )
        success_embed.set_footer(text=f"أنشأه: {self.interaction.user.display_name} | /جداولي_التسلسلية لإدارة الجداول")
        success_embed.timestamp = datetime.now(BAGHDAD_TZ)
        await self.interaction.followup.send(embed=success_embed)


# ══════════════════════════════════════════════════════════════
#  دوال مساعدة موجودة
# ══════════════════════════════════════════════════════════════

async def chapter_workflow(interaction: discord.Interaction, slug: str):
    modal = ChapterDataModal()
    await interaction.response.send_modal(modal)
    if not await modal.wait(): return
    number = modal.chap_number; chap_title = modal.chap_title_val
    novel  = novel_store.get_novel(slug); novel_nm = novel["arabic"] if novel else slug
    txt_view = UploadTxtView(interaction.user.id, interaction.channel_id)
    await interaction.followup.send(
        embed=inf_embed("رفع ملف الفصل",
            f"**الرواية:** {novel_nm}\n**الفصل {number}:** {chap_title}\n\nاضغط الزر لرفع ملف `.txt`"),
        view=txt_view
    )
    if not await txt_view.wait_file():
        await interaction.followup.send(embed=err_embed("انتهى الوقت", "لم يُرفع أي ملف.")); return
    content = txt_view.content; preview = content[:200].replace("\n", " ") + "..."
    confirm_view = ConfirmPublishView(slug, number, chap_title, content, interaction.user.id, interaction.channel_id)
    await interaction.followup.send(
        embed=make_embed("مراجعة قبل النشر",
            f"**الرواية:** {novel_nm}\n**الفصل {number}:** {chap_title}\n"
            f"**الحجم:** {len(content):,} حرف\n**معاينة:**\n```\n{preview}\n```", Colors.GOLD),
        view=confirm_view
    )

async def process_zip(data: bytes) -> List[Tuple[int, str, str]]:
    tasks = []
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as zf:
            files = [
                f for f in zf.namelist()
                if f.lower().endswith(".txt") and not f.startswith("__MACOSX") and not os.path.basename(f).startswith(".")
            ]
            for fname in files:
                try:
                    content = normalize_content(decode_bytes(zf.read(fname)), to_html=True)
                    num = extract_chapter_number_from_filename(os.path.basename(fname))
                    if num is None: num, ct = extract_chapter_info_from_content(content)
                    else: _, ct = extract_chapter_info_from_content(content)
                    if not ct: ct = f"الفصل {num}"
                    if num is not None: tasks.append((num, ct, content))
                except Exception as e:
                    log.warning(f"فشل قراءة {fname}: {e}")
        tasks.sort(key=lambda x: x[0])
    except zipfile.BadZipFile:
        log.error("ملف ZIP تالف")
    return tasks


# ══════════════════════════════════════════════════════════════
#  الأوامر
# ══════════════════════════════════════════════════════════════

@bot.tree.command(name="بحث_رواية", description="ابحث عن رواية وأضفها")
@owner_only()
async def cmd_search(interaction: discord.Interaction, اسم_الرواية: str):
    await interaction.response.defer()
    results = await NovelAPI().search(اسم_الرواية)
    if not results:
        return await interaction.followup.send(embed=err_embed("لا نتائج", f"لم يُعثر على: `{اسم_الرواية}`"))
    view = SearchResultView(results, interaction.user.id)
    await interaction.followup.send(embed=inf_embed(f"نتائج البحث ({len(results)})", "اختر رواية:"), view=view)
    await view.wait()
    if not view.selected: return
    s = view.selected
    added = novel_store.add_novel(s["slug"], s["arabic"], s["english"])
    if ann_cog:
        await ann_cog.prompt_cover_upload(interaction, s["slug"], s["arabic"])
    await interaction.followup.send(
        embed=ok_embed("أُضيفت", f"**{s['arabic']}** — `{s['slug']}`") if added
        else warn_embed("موجودة مسبقًا", f"`{s['slug']}`")
    )


@bot.tree.command(name="رواياتي", description="عرض الروايات المحفوظة")
@owner_only()
async def cmd_list(interaction: discord.Interaction):
    novels = novel_store.novels
    if not novels:
        return await interaction.response.send_message(embed=inf_embed("لا روايات", "استخدم `/بحث_رواية` لإضافة روايات."))
    desc = ""
    for i, n in enumerate(novels, 1):
        added = n.get("added_at", "")[:10]
        desc += f"**{i}.** {n['arabic']}\n   `{n['slug']}` | {n.get('published_count',0)} فصل | {added}\n\n"
    await interaction.response.send_message(embed=make_embed(f"رواياتي ({len(novels)})", desc.strip(), Colors.PURPLE))


@bot.tree.command(name="حذف_رواية", description="حذف رواية من قائمتك")
@owner_only()
async def cmd_remove(interaction: discord.Interaction):
    if not novel_store.novels:
        return await interaction.response.send_message(embed=inf_embed("لا روايات", "قائمتك فارغة."))
    view = NovelSelectView(interaction.user.id)
    await interaction.response.send_message(embed=warn_embed("حذف رواية", "اختر الرواية التي تريد حذفها:"), view=view)
    await view.wait()
    if not view.slug: return
    novel = novel_store.get_novel(view.slug)

    class ConfirmDel(discord.ui.View):
        def __init__(self_):
            super().__init__(timeout=30)

        @discord.ui.button(label="تأكيد الحذف", style=discord.ButtonStyle.danger)
        async def yes(self_, btn_inter: discord.Interaction, button: discord.ui.Button):
            if btn_inter.user.id != interaction.user.id:
                return await btn_inter.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
            novel_store.remove_novel(view.slug)
            await btn_inter.response.edit_message(embed=ok_embed("تم الحذف", f"**{novel['arabic']}**"), view=None); self_.stop()

        @discord.ui.button(label="إلغاء", style=discord.ButtonStyle.secondary)
        async def no(self_, btn_inter: discord.Interaction, button: discord.ui.Button):
            await btn_inter.response.edit_message(embed=inf_embed("تم الإلغاء"), view=None); self_.stop()

    await interaction.followup.send(
        embed=warn_embed("تأكيد الحذف", f"هل تريد حذف **{novel['arabic']}**؟\n(لن تُحذف من الموقع)"),
        view=ConfirmDel()
    )


@bot.tree.command(name="نشر_فصل", description="نشر فصل جديد")
@owner_only()
async def cmd_publish(interaction: discord.Interaction):
    novels = novel_store.novels
    if not novels:
        return await interaction.response.send_message(embed=err_embed("لا روايات", "استخدم `/بحث_رواية` أولاً."))
    if len(novels) == 1:
        await chapter_workflow(interaction, novels[0]["slug"]); return
    view = NovelSelectView(interaction.user.id)
    await interaction.response.send_message(embed=inf_embed("اختر الرواية", "من أي رواية تريد نشر فصل؟"), view=view)
    await view.wait()
    if not view.slug: return
    slug = view.slug; novel = novel_store.get_novel(slug)

    class StartView(discord.ui.View):
        def __init__(self_):
            super().__init__(timeout=60)

        @discord.ui.button(label="إدخال بيانات الفصل", style=discord.ButtonStyle.primary)
        async def go(self_, btn: discord.Interaction, button: discord.ui.Button):
            if btn.user.id != interaction.user.id:
                return await btn.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
            for c in self_.children: c.disabled = True
            await btn.message.edit(view=self_)
            await chapter_workflow(btn, slug); self_.stop()

    await interaction.followup.send(
        embed=ok_embed("تم اختيار الرواية", f"**{novel['arabic']}**\nاضغط الزر للمتابعة."), view=StartView()
    )


@bot.tree.command(name="جدولة_فصل", description="جدولة نشر فصل في وقت معين")
@owner_only()
async def cmd_schedule(interaction: discord.Interaction):
    novels = novel_store.novels
    if not novels:
        return await interaction.response.send_message(embed=err_embed("لا روايات", "استخدم `/بحث_رواية` أولاً."))
    if len(novels) == 1:
        await chapter_workflow(interaction, novels[0]["slug"]); return
    view = NovelSelectView(interaction.user.id)
    await interaction.response.send_message(embed=inf_embed("اختر الرواية", "اختر الرواية للجدولة:"), view=view)
    await view.wait()
    if not view.slug: return
    slug = view.slug; novel = novel_store.get_novel(slug)

    class StartView(discord.ui.View):
        def __init__(self_):
            super().__init__(timeout=60)

        @discord.ui.button(label="إدخال بيانات الفصل", style=discord.ButtonStyle.primary)
        async def go(self_, btn: discord.Interaction, button: discord.ui.Button):
            if btn.user.id != interaction.user.id:
                return await btn.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
            for c in self_.children: c.disabled = True
            await btn.message.edit(view=self_)
            await chapter_workflow(btn, slug); self_.stop()

    await interaction.followup.send(
        embed=ok_embed("تم اختيار الرواية", f"**{novel['arabic']}**\nاضغط الزر للمتابعة."), view=StartView()
    )


@bot.tree.command(name="نشر_مجموعة", description="نشر مجموعة فصول من ملف ZIP")
@owner_only()
async def cmd_batch(interaction: discord.Interaction):
    novels = novel_store.novels
    if not novels:
        return await interaction.response.send_message(embed=err_embed("لا روايات", "استخدم `/بحث_رواية` أولاً."))
    if len(novels) == 1:
        slug = novels[0]["slug"]; novel = novels[0]; await interaction.response.defer()
    else:
        view = NovelSelectView(interaction.user.id)
        await interaction.response.send_message(embed=inf_embed("اختر الرواية", "اختر الرواية للنشر الجماعي:"), view=view)
        await view.wait()
        if not view.slug: return
        slug = view.slug; novel = novel_store.get_novel(slug)
    zip_view = UploadZipView(interaction.user.id, interaction.channel_id)
    await interaction.followup.send(
        embed=inf_embed("رفع ملف ZIP",
            f"**الرواية:** {novel['arabic'] if novel else slug}\n\n"
            "اضغط الزر لرفع ملف `.zip` يحتوي على ملفات `.txt` مرقّمة."),
        view=zip_view
    )
    if not await zip_view.wait_zip():
        await interaction.followup.send(embed=err_embed("انتهى الوقت", "لم يُرفع أي ملف.")); return
    tasks = await process_zip(zip_view.zip_bytes)
    if not tasks:
        return await interaction.followup.send(embed=err_embed("ZIP فارغ", "لم يُعثر على فصول صالحة."))
    summary = "\n".join(f"الفصل **{n}** — {t[:40]}" for n, t, _ in tasks[:10])
    if len(tasks) > 10: summary += f"\n... و **{len(tasks)-10}** فصول أخرى"
    batch_view = BatchConfirmView(slug, tasks, novel, interaction.user.id, interaction.channel_id)
    await interaction.followup.send(
        embed=make_embed(f"ملخص النشر الجماعي ({len(tasks)} فصل)",
            f"**الرواية:** {novel['arabic'] if novel else slug}\n\n{summary}", Colors.GOLD),
        view=batch_view
    )


@bot.tree.command(name="مهامي", description="عرض المهام المجدولة")
@owner_only()
async def cmd_jobs(interaction: discord.Interaction):
    jobs = sorted(jobs_db.get("jobs", []), key=lambda j: j["run_time"])
    if not jobs:
        return await interaction.response.send_message(embed=inf_embed("لا مهام", "لا توجد مهام مجدولة."))
    desc = ""; now_baghdad = datetime.now(BAGHDAD_TZ)
    for j in jobs[:15]:
        t = datetime.fromisoformat(j["run_time"])
        if t.tzinfo is None: t = BAGHDAD_TZ.localize(t)
        else: t = t.astimezone(BAGHDAD_TZ)
        nv = novel_store.get_novel(j["slug"]); nm = nv["arabic"][:20] if nv else j["slug"]
        dlt = t - now_baghdad; h = max(0, int(dlt.total_seconds() // 3600))
        desc += f"**`{j['id'][:10]}`** — {nm}\n   ف{j['number']} | {t.strftime('%Y-%m-%d %H:%M')} | {h} ساعة\n\n"
    if len(jobs) > 15: desc += f"... و **{len(jobs)-15}** مهمة أخرى"
    await interaction.response.send_message(embed=make_embed(f"المهام ({len(jobs)})", desc.strip(), Colors.PURPLE))


@bot.tree.command(name="إلغاء_مهمة", description="إلغاء مهمة مجدولة")
@owner_only()
async def cmd_cancel(interaction: discord.Interaction, معرف_المهمة: str):
    target = next((j for j in jobs_db["jobs"] if j["id"].startswith(معرف_المهمة)), None)
    if not target:
        return await interaction.response.send_message(embed=err_embed("غير موجودة", f"`{معرف_المهمة}`"))
    try: scheduler.remove_job(target["id"])
    except Exception: pass
    jobs_db["jobs"] = [j for j in jobs_db["jobs"] if j["id"] != target["id"]]
    await save_jobs()
    nv = novel_store.get_novel(target["slug"])
    await interaction.response.send_message(
        embed=ok_embed("تم الإلغاء", f"**{nv['arabic'] if nv else target['slug']}**\nف{target['number']}: {target['chap_title']}")
    )


@bot.tree.command(name="إحصاءات", description="إحصاءات النشر")
@owner_only()
async def cmd_stats(interaction: discord.Interaction):
    td = stats.today()
    up = datetime.now(BAGHDAD_TZ) - bot.start_time
    h, rem = divmod(int(up.total_seconds()), 3600); m = rem // 60

    db = db_client.get_database("rewyat_bot")
    # إحصائيات الجداول التسلسلية من MongoDB
    serial_total = await db.serial_schedules.count_documents({})
    serial_active = await db.serial_schedules.count_documents({"finished": False, "paused": False})
    serial_finished = await db.serial_schedules.count_documents({"finished": True})
    failed_serial = await db.failed_serial_chapters.count_documents({})

    await interaction.response.send_message(
        embed=make_embed("الإحصاءات", f"بوت النشر v{VERSION}", Colors.GOLD, fields=[
            {"name": "إجمالي المنشور",    "value": f"`{stats.total_published}` فصل", "inline": True},
            {"name": "إجمالي الفاشل",    "value": f"`{stats.total_failed}` فصل",    "inline": True},
            {"name": "المجدول",           "value": f"`{stats.total_scheduled}` مهمة","inline": True},
            {"name": "اليوم (نشر)",       "value": f"`{td['published']}` فصل",       "inline": True},
            {"name": "اليوم (فشل)",       "value": f"`{td['failed']}` فصل",          "inline": True},
            {"name": "مهام عادية نشطة",   "value": f"`{len(jobs_db['jobs'])}` مهمة", "inline": True},
            {"name": "الروايات",          "value": f"`{len(novel_store.novels)}`",    "inline": True},
            {"name": "وقت التشغيل",      "value": f"`{h}h {m}m`",                   "inline": True},
            {"name": "فصول تسلسلية فاشلة", "value": f"`{failed_serial}` فصل",        "inline": True},
            {"name": "جداول تسلسلية",    "value": f"نشطة: `{serial_active}` | مكتملة: `{serial_finished}` | الكل: `{serial_total}`", "inline": False},
        ])
    )


@bot.tree.command(name="اضافة_حساب", description="إضافة حساب API جديد")
@owner_only()
async def cmd_add_account(interaction: discord.Interaction):
    await interaction.response.send_modal(AddAccountModal())


@bot.tree.command(name="حساباتي", description="عرض الحسابات المضافة")
@owner_only()
async def cmd_accounts(interaction: discord.Interaction):
    accs = account_manager.data["accounts"]; active_idx = account_manager.data["active_index"]
    desc = ""
    for i, a in enumerate(accs):
        marker = "✅" if i == active_idx else "⬜"
        desc += f"{marker} **{i+1}. {a['name']}**\n   {a['email']}\n   نُشر: {a['stats']['published']} | فشل: {a['stats']['failed']}\n\n"
    await interaction.response.send_message(embed=make_embed(f"الحسابات ({len(accs)})", desc.strip(), Colors.INFO))


@bot.tree.command(name="تبديل_حساب", description="التبديل إلى حساب آخر")
@owner_only()
async def cmd_switch_account(interaction: discord.Interaction, رقم_الحساب: int):
    idx = رقم_الحساب - 1
    if account_manager.switch_account(idx):
        acc = account_manager.active_account
        await interaction.response.send_message(embed=ok_embed("تم التبديل", f"الحساب النشط الآن: **{acc['name']}** ({acc['email']})"))
    else:
        await interaction.response.send_message(embed=err_embed("رقم غير صالح", "تأكد من رقم الحساب."), ephemeral=True)


@bot.tree.command(name="مساعدة", description="قائمة الأوامر")
@owner_only()
async def cmd_help(interaction: discord.Interaction):
    await interaction.response.send_message(
        embed=make_embed("دليل الأوامر", f"بوت النشر v{VERSION}", Colors.INFO, fields=[
            {"name": "إدارة الروايات",    "value": "`/بحث_رواية` `/رواياتي` `/حذف_رواية`",        "inline": False},
            {"name": "النشر",             "value": "`/نشر_فصل` `/نشر_مجموعة`",                    "inline": False},
            {"name": "الجدولة",           "value": "`/جدولة_فصل` `/مهامي` `/إلغاء_مهمة`",         "inline": False},
            {"name": "الحسابات",          "value": "`/اضافة_حساب` `/حساباتي` `/تبديل_حساب`",     "inline": False},
            {"name": "النشر التسلسلي",   "value": "`/نشر_تسلسلي` `/جداولي_التسلسلية` `/معاينة_تسلسلي`", "inline": False},
            {"name": "أخرى",             "value": "`/إحصاءات` `/مساعدة`",                         "inline": False},
            {"name": "ملاحظات",
             "value": (
                 "جدولة الفصل: اختر السنة، الشهر، اليوم، الساعة والدقيقة.\n"
                 "التسلسلي: ارفع ZIP كامل للرواية، حدد الدفعة والوقت اليومي.\n"
                 "ZIP: سمِّ الملفات 1.txt, 2.txt ...\n"
                 "البوت يعمل بتوقيت العراق (Asia/Baghdad)."
             ), "inline": False},
        ])
    )


# ══════════════════════════════════════════════════════════════
#  أوامر النشر التسلسلي (تم تعديلها لاستخدام MongoDB مباشرة)
# ══════════════════════════════════════════════════════════════

@bot.tree.command(name="نشر_تسلسلي", description="رفع رواية كاملة ونشر فصولها يومياً بشكل تلقائي")
@owner_only()
async def cmd_serial_publish(interaction: discord.Interaction):
    await interaction.response.defer()
    publisher = SerialPublisher(interaction)
    await publisher.run()


@bot.tree.command(name="جداولي_التسلسلية", description="عرض وإدارة جداول النشر التسلسلي اليومي")
@owner_only()
async def cmd_list_serial_schedules(interaction: discord.Interaction):
    db = db_client.get_database("rewyat_bot")
    docs = await db.serial_schedules.find({}).to_list(length=200)
    if not docs:
        await interaction.response.send_message(
            embed=make_embed(
                "لا توجد جداول تسلسلية",
                "لم تُنشئ أي جدول نشر تسلسلي بعد.\n\n"
                "ابدأ باستخدام `/نشر_تسلسلي` لرفع رواية كاملة ونشرها يومياً.",
                Colors.INFO
            )
        )
        return

    total_series   = len(docs)
    active         = sum(1 for d in docs if not d.get("paused") and not d.get("finished"))
    paused         = sum(1 for d in docs if d.get("paused"))
    finished       = sum(1 for d in docs if d.get("finished"))
    total_chapters = sum(d.get("total_chapters", 0) for d in docs)
    published_sum  = sum(d.get("published_count", 0) for d in docs)

    header_embed = make_embed("جداول النشر التسلسلي", color=Colors.PURPLE)
    header_embed.description = (
        f"**الجداول الكلية:** {total_series}\n"
        f"**نشطة:** {active}\n"
        f"**متوقفة:** {paused}\n"
        f"**مكتملة:** {finished}\n"
        f"**فصول منشورة:** {published_sum}/{total_chapters}\n"
    )
    header_embed.set_footer(text="اختر جدولاً من القائمة أدناه لإدارته")
    await interaction.response.send_message(embed=header_embed)

    view = SerialListView(docs, interaction.user.id)
    await interaction.followup.send(
        embed=make_embed("اختر جدولاً للإدارة", color=Colors.PURPLE),
        view=view
    )


@bot.tree.command(name="معاينة_تسلسلي", description="معاينة فصول جدول نشر تسلسلي محدد")
@owner_only()
async def cmd_preview_serial(interaction: discord.Interaction):
    db = db_client.get_database("rewyat_bot")
    docs = await db.serial_schedules.find({"finished": False}).to_list(length=50)
    if not docs:
        await interaction.response.send_message(
            embed=make_embed("لا توجد جداول نشطة", "استخدم `/نشر_تسلسلي` لإنشاء جدول أولاً.", Colors.INFO)
        )
        return

    if len(docs) == 1:
        doc = docs[0]
        # جلب الفصول (بدون المحتوى)
        chapters_cursor = db.serial_chapters.find(
            {"serial_id": doc["_id"]},
            {"content_compressed": 0}
        ).sort("number", 1)
        chapters = await chapters_cursor.to_list(length=10000)
        view = SerialChaptersPreviewView(chapters, doc, interaction.user.id)
        view._refresh_buttons()
        await interaction.response.send_message(embed=view._build_embed(), view=view)
        return

    options = [
        discord.SelectOption(
            label=f"{d.get('novel_arabic','?')[:50]}",
            value=d["_id"],
            description=f"{d.get('published_count',0)}/{d.get('total_chapters',0)} فصل منشور"
        )
        for d in docs[:25]
    ]
    sel_view = discord.ui.View(timeout=60)
    sel      = discord.ui.Select(placeholder="اختر الجدول للمعاينة...", options=options)

    async def sel_cb(interaction_btn: discord.Interaction):
        if interaction_btn.user.id != interaction.user.id:
            return await interaction_btn.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        sid = interaction_btn.data["values"][0]
        doc = await db.serial_schedules.find_one({"_id": sid})
        if not doc:
            return await interaction_btn.response.send_message(embed=err_embed("غير موجود"), ephemeral=True)
        chapters_cursor = db.serial_chapters.find(
            {"serial_id": sid},
            {"content_compressed": 0}
        ).sort("number", 1)
        chapters = await chapters_cursor.to_list(length=10000)
        pv = SerialChaptersPreviewView(chapters, doc, interaction.user.id)
        pv._refresh_buttons()
        await interaction_btn.response.send_message(embed=pv._build_embed(), view=pv, ephemeral=True)

    sel.callback = sel_cb
    sel_view.add_item(sel)
    await interaction.response.send_message(
        embed=make_embed("اختر الجدول للمعاينة", color=Colors.PURPLE),
        view=sel_view
    )


async def _send_serial_now_picker(interaction: discord.Interaction, docs: List[dict], title: str):
    view = discord.ui.View(timeout=90)
    options = [
        discord.SelectOption(
            label=d.get("novel_arabic", "?")[:50],
            value=d["_id"],
            description=f"{d.get('published_count',0)}/{d.get('total_chapters',0)} فصل"
        )
        for d in docs[:25]
    ]
    sel = discord.ui.Select(placeholder="اختر جدولاً تسلسلياً...", options=options)

    async def sel_cb(i: discord.Interaction):
        if i.user.id != interaction.user.id:
            return await i.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        sid = i.data["values"][0]
        db = db_client.get_database("rewyat_bot")
        doc = await db.serial_schedules.find_one({"_id": sid})
        if not doc:
            return await i.response.send_message(embed=err_embed("غير موجود"), ephemeral=True)
        slots = _serial_slots(doc)
        if len(slots) == 1:
            await i.response.edit_message(embed=make_embed("جارٍ النشر اليدوي...", f"سيتم نشر دفعة **{doc.get('novel_arabic','')}** الآن.", Colors.WARNING), view=None)
            await run_serial_batch_for_slot(sid, slots[0]["slot"])
            return await i.followup.send(embed=ok_embed("تم تنفيذ الأمر", "اكتمل طلب النشر التسلسلي اليدوي."))

        slot_view = discord.ui.View(timeout=60)
        for slot_doc in slots:
            h = slot_doc["hour"]; m = slot_doc["minute"]
            h12 = h % 12 or 12; per_ar = "ص" if h < 12 else "م"
            btn = discord.ui.Button(label=f"الموعد {slot_doc['slot']} ({h12:02d}:{m:02d} {per_ar})", style=discord.ButtonStyle.primary)

            async def slot_cb(ii: discord.Interaction, chosen_slot=slot_doc["slot"]):
                if ii.user.id != interaction.user.id:
                    return await ii.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
                await ii.response.edit_message(embed=make_embed("جارٍ النشر اليدوي...", f"سيتم نشر الموعد **{chosen_slot}** الآن.", Colors.WARNING), view=None)
                await run_serial_batch_for_slot(sid, chosen_slot)
                await ii.followup.send(embed=ok_embed("تم تنفيذ الأمر", "اكتمل طلب النشر التسلسلي اليدوي."))

            btn.callback = slot_cb
            slot_view.add_item(btn)

        both_btn = discord.ui.Button(label="نشر الموعدين معاً", style=discord.ButtonStyle.success)
        async def both_cb(ii: discord.Interaction):
            if ii.user.id != interaction.user.id:
                return await ii.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
            await ii.response.edit_message(embed=make_embed("جارٍ النشر اليدوي...", "سيتم نشر الموعدين الآن.", Colors.WARNING), view=None)
            await run_serial_batch_for_slot(sid, None)
            await ii.followup.send(embed=ok_embed("تم تنفيذ الأمر", "اكتمل طلب النشر التسلسلي اليدوي."))
        both_btn.callback = both_cb
        slot_view.add_item(both_btn)
        await i.response.edit_message(embed=make_embed("اختر الموعد", "هذا الجدول لديه أكثر من موعد. اختر ما تريد نشره الآن.", Colors.PURPLE), view=slot_view)

    sel.callback = sel_cb
    view.add_item(sel)
    await interaction.response.send_message(embed=make_embed(title, color=Colors.PURPLE), view=view)


@bot.tree.command(name="نشر_تسلسلي_الآن", description="نشر دفعة اليوم يدوياً الآن لجدول تسلسلي")
@owner_only()
async def cmd_serial_publish_now(interaction: discord.Interaction):
    db = db_client.get_database("rewyat_bot")
    docs = await db.serial_schedules.find({"finished": False, "paused": False}).to_list(length=50)
    if not docs:
        return await interaction.response.send_message(embed=warn_embed("لا توجد جداول نشطة"))
    await _send_serial_now_picker(interaction, docs, "نشر تسلسلي يدوي الآن")


@bot.tree.command(name="نشر_تسلسلي_دفعة_اليوم", description="نشر دفعة اليوم لكل الجداول التسلسلية النشطة الآن")
@owner_only()
async def cmd_serial_publish_today_all(interaction: discord.Interaction):
    db = db_client.get_database("rewyat_bot")
    docs = await db.serial_schedules.find({"finished": False, "paused": False}).to_list(length=200)
    if not docs:
        return await interaction.response.send_message(embed=warn_embed("لا توجد جداول نشطة"))
    await interaction.response.send_message(embed=make_embed("جارٍ نشر دفعة اليوم", f"سيتم تنفيذ **{len(docs)}** جدول تسلسلي الآن.", Colors.WARNING))
    for doc in docs:
        await run_serial_batch_for_slot(doc["_id"], None)
    await interaction.followup.send(embed=ok_embed("انتهى النشر اليدوي", f"تم تنفيذ دفعة اليوم لـ **{len(docs)}** جدول."))


async def _retry_failed_doc(db, failed: dict) -> bool:
    try:
        content = gzip.decompress(failed["content_compressed"]).decode("utf-8")
    except Exception:
        content = failed.get("content", "")
    api = NovelAPI()
    ok, msg = await api.publish(failed["slug"], failed["number"], failed.get("title", ""), content)
    if ok:
        await db.failed_serial_chapters.delete_one({"_id": failed["_id"]})
    else:
        await db.failed_serial_chapters.update_one({"_id": failed["_id"]}, {"$set": {"error": msg[:500], "failed_at": datetime.now(BAGHDAD_TZ).isoformat()}})
    return ok


@bot.tree.command(name="فصول_فاشلة", description="عرض الفصول التسلسلية الفاشلة")
@owner_only()
async def cmd_failed_chapters(interaction: discord.Interaction):
    db = db_client.get_database("rewyat_bot")
    failed = await db.failed_serial_chapters.find({}).sort("failed_at", -1).to_list(length=100)
    if not failed:
        return await interaction.response.send_message(embed=ok_embed("لا توجد فصول فاشلة"))
    groups: Dict[str, List[str]] = {}
    for f in failed:
        groups.setdefault(f.get("novel_arabic") or f.get("slug", "?"), []).append(str(f.get("number", "?")))
    lines = [f"**{name}:** {', '.join(nums[:20])}" for name, nums in groups.items()]
    await interaction.response.send_message(embed=make_embed("الفصول الفاشلة", "\n".join(lines)[:3900], Colors.WARNING))


@bot.tree.command(name="اعادة_نشر_فصل", description="إعادة نشر فصل فاشل محدد")
@owner_only()
async def cmd_retry_failed_chapter(interaction: discord.Interaction, slug: str, number: int):
    db = db_client.get_database("rewyat_bot")
    failed = await db.failed_serial_chapters.find_one({"slug": slug, "number": number})
    if not failed:
        return await interaction.response.send_message(embed=warn_embed("غير موجود", "لم أجد هذا الفصل ضمن الفصول الفاشلة."))
    await interaction.response.defer()
    ok = await _retry_failed_doc(db, failed)
    await interaction.followup.send(embed=(ok_embed("تمت إعادة النشر") if ok else err_embed("فشلت إعادة النشر")))


@bot.tree.command(name="اعادة_نشر_كل_فصول_رواية", description="إعادة نشر كل الفصول الفاشلة لرواية")
@owner_only()
async def cmd_retry_failed_novel(interaction: discord.Interaction, slug: str):
    db = db_client.get_database("rewyat_bot")
    failed = await db.failed_serial_chapters.find({"slug": slug}).to_list(length=500)
    await interaction.response.defer()
    ok_count = 0
    for f in failed:
        ok_count += 1 if await _retry_failed_doc(db, f) else 0
    await interaction.followup.send(embed=ok_embed("انتهت إعادة المحاولة", f"نجح **{ok_count}** من **{len(failed)}**."))


@bot.tree.command(name="اعادة_نشر_كل_الفصول", description="إعادة نشر كل الفصول الفاشلة في النظام")
@owner_only()
async def cmd_retry_all_failed(interaction: discord.Interaction):
    db = db_client.get_database("rewyat_bot")
    failed = await db.failed_serial_chapters.find({}).to_list(length=1000)
    await interaction.response.defer()
    ok_count = 0
    for f in failed:
        ok_count += 1 if await _retry_failed_doc(db, f) else 0
    await interaction.followup.send(embed=ok_embed("انتهت إعادة المحاولة", f"نجح **{ok_count}** من **{len(failed)}**."))


# ══════════════════════════════════════════════════════════════
#  بناء رابط الرواية
# ══════════════════════════════════════════════════════════════

def _build_novel_url(slug: str) -> str:
    return NOVEL_URL.format(slug=slug)


# ══════════════════════════════════════════════════════════════
#  نصوص الإعلانات — حسب عدد الروايات ونوع النشر
# ══════════════════════════════════════════════════════════════

def _chapter_range_str(first: int, last: int) -> str:
    if first == last:
        return f"الفصل {last}"
    return f"الفصول {first} الى {last}"


def _build_announcement_text(
    entries: List[Dict],
    source: str,
    date_str: str,
) -> str:
    """
    يبني نص الإعلان المناسب بحسب عدد الروايات ونوع النشر.

    entries: قائمة dict تحتوي كل منها على:
        novel_arabic, slug, first_chapter, last_chapter

    source: "serial" | "manual" | "batch" | "scheduled"
    """
    n = len(entries)

    # ── إعلان رواية واحدة ──
    if n == 1:
        e   = entries[0]
        url = _build_novel_url(e["slug"])
        rng = _chapter_range_str(e["first_chapter"], e["last_chapter"])

        if source == "serial":
            return (
                f"تم بحمد الله تعالى تنزيل دفعة اليوم من فصول رواية\n"
                f" {e['novel_arabic']} \n\n"
                f"الفصول المضافة: {rng}\n\n"
                f"استمتعوا بالقراءة، ولا تنسونا في تعليقات جميلة لتحفيزي، "
                f"ونلتقي في موعدنا غدا ان شاء الله.\n\n"
                f"────\n{date_str}\n────\n\n"
                f"رابط الرواية:\n{url}"
            )
        elif source in ("manual", "scheduled"):
            return (
                f"تم نشر فصل جديد من رواية\n"
                f" {e['novel_arabic']} \n\n"
                f"{rng} متاح الان على الموقع\n\n"
                f"لا تنسوا التعليق وابداء رايكم!\n\n"
                f"────\n{date_str}\n────\n\n"
                f"رابط الرواية:\n{url}"
            )
        else:  # batch
            return (
                f"تم نشر دفعة جديدة من رواية\n"
                f" {e['novel_arabic']} \n\n"
                f"الفصول المضافة: {rng}\n\n"
                f"استمتعوا بالقراءة ولا تنسوا دعمنا بتعليقاتكم!\n\n"
                f"────\n{date_str}\n────\n\n"
                f"رابط الرواية:\n{url}"
            )

    # ── روايتان ──
    elif n == 2:
        names = " مع ".join(f" {e['novel_arabic']} " for e in entries)
        details = "\n".join(
            f"{e['novel_arabic']}: {_chapter_range_str(e['first_chapter'], e['last_chapter'])}"
            for e in entries
        )
        urls = "\n".join(
            f"{e['novel_arabic']}:\n{_build_novel_url(e['slug'])}"
            for e in entries
        )

        if source == "serial":
            return (
                f"تم بحمد الله تعالى تنزيل دفعة اليوم من فصول\n"
                f"{names}\n\n"
                f"الفصول المضافة:\n{details}\n\n"
                f"استمتعوا بالقراءة، ولا تنسونا في تعليقات جميلة لتحفيزي، "
                f"ونلتقي في موعدنا غدا ان شاء الله.\n\n"
                f"────\n{date_str}\n────\n\n"
                f"روابط الروايات:\n{urls}"
            )
        else:
            return (
                f"تم نشر فصول جديدة من\n"
                f"{names}\n\n"
                f"الفصول المضافة:\n{details}\n\n"
                f"استمتعوا بالقراءة ولا تنسوا دعمنا بتعليقاتكم!\n\n"
                f"────\n{date_str}\n────\n\n"
                f"روابط الروايات:\n{urls}"
            )

    # ── ثلاث روايات أو أكثر ──
    else:
        return (
            f"تم بحمد الله تعالى تنزيل دفعة اليوم من الفصول لجميع الروايات كما موضح في الصورة.\n\n"
            f"استمتعوا بالقراءة، ولا تنسونا في تعليقات جميلة لتحفيزي، "
            f"ونلتقي في موعدنا غدا ان شاء الله.\n\n"
            f"────\n{date_str}\n────\n\n"
            f"رابط الموقع لسهولة الوصول:\n{SITE_URL}"
        )


# ══════════════════════════════════════════════════════════════
#  معالج النص العربي — بدون مكتبات خارجية (يعمل بدون libraqm)
# ══════════════════════════════════════════════════════════════

_AR_JOIN = {
    '\u0627':1,'\u062F':1,'\u0630':1,'\u0631':1,'\u0632':1,'\u0648':1,
    '\u0622':1,'\u0623':1,'\u0625':1,'\u0624':1,'\u0671':1,'\u0621':0,
    '\u0649':1,'\u0629':2,'\u0628':2,'\u062A':2,'\u062B':2,'\u062C':2,
    '\u062D':2,'\u062E':2,'\u0633':2,'\u0634':2,'\u0635':2,'\u0636':2,
    '\u0637':2,'\u0638':2,'\u0639':2,'\u063A':2,'\u0641':2,'\u0642':2,
    '\u0643':2,'\u0644':2,'\u0645':2,'\u0646':2,'\u0647':2,'\u064A':2,
    '\u0626':2,'\u06CC':2,
}
_AR_FORMS = {
    '\u0627':('\uFE8D','\uFE8E','\uFE8D','\uFE8E'),
    '\u0628':('\uFE8F','\uFE90','\uFE91','\uFE92'),
    '\u062A':('\uFE95','\uFE96','\uFE97','\uFE98'),
    '\u062B':('\uFE99','\uFE9A','\uFE9B','\uFE9C'),
    '\u062C':('\uFE9D','\uFE9E','\uFE9F','\uFEA0'),
    '\u062D':('\uFEA1','\uFEA2','\uFEA3','\uFEA4'),
    '\u062E':('\uFEA5','\uFEA6','\uFEA7','\uFEA8'),
    '\u062F':('\uFEA9','\uFEAA','\uFEA9','\uFEAA'),
    '\u0630':('\uFEAB','\uFEAC','\uFEAB','\uFEAC'),
    '\u0631':('\uFEAD','\uFEAE','\uFEAD','\uFEAE'),
    '\u0632':('\uFEAF','\uFEB0','\uFEAF','\uFEB0'),
    '\u0633':('\uFEB1','\uFEB2','\uFEB3','\uFEB4'),
    '\u0634':('\uFEB5','\uFEB6','\uFEB7','\uFEB8'),
    '\u0635':('\uFEB9','\uFEBA','\uFEBB','\uFEBC'),
    '\u0636':('\uFEBD','\uFEBE','\uFEBF','\uFEC0'),
    '\u0637':('\uFEC1','\uFEC2','\uFEC3','\uFEC4'),
    '\u0638':('\uFEC5','\uFEC6','\uFEC7','\uFEC8'),
    '\u0639':('\uFEC9','\uFECA','\uFECB','\uFECC'),
    '\u063A':('\uFECD','\uFECE','\uFECF','\uFED0'),
    '\u0641':('\uFED1','\uFED2','\uFED3','\uFED4'),
    '\u0642':('\uFED5','\uFED6','\uFED7','\uFED8'),
    '\u0643':('\uFED9','\uFEDA','\uFEDB','\uFEDC'),
    '\u0644':('\uFEDD','\uFEDE','\uFEDF','\uFEE0'),
    '\u0645':('\uFEE1','\uFEE2','\uFEE3','\uFEE4'),
    '\u0646':('\uFEE5','\uFEE6','\uFEE7','\uFEE8'),
    '\u0647':('\uFEE9','\uFEEA','\uFEEB','\uFEEC'),
    '\u0648':('\uFEED','\uFEEE','\uFEED','\uFEEE'),
    '\u064A':('\uFEF1','\uFEF2','\uFEF3','\uFEF4'),
    '\u0649':('\uFEEF','\uFEF0','\uFEEF','\uFEF0'),
    '\u0622':('\uFE81','\uFE82','\uFE81','\uFE82'),
    '\u0623':('\uFE83','\uFE84','\uFE83','\uFE84'),
    '\u0625':('\uFE87','\uFE88','\uFE87','\uFE88'),
    '\u0624':('\uFE85','\uFE86','\uFE85','\uFE86'),
    '\u0626':('\uFE89','\uFE8A','\uFE8B','\uFE8C'),
    '\u0621':('\uFE80','\uFE80','\uFE80','\uFE80'),
    '\u0629':('\uFE93','\uFE94','\uFE93','\uFE94'),
    '\u06CC':('\uFBFC','\uFBFD','\uFBFE','\uFBFF'),
}
_AR_LAM_ALEF = {
    '\u0644\u0622':'\uFEF5','\u0644\u0623':'\uFEF7',
    '\u0644\u0625':'\uFEF9','\u0644\u0627':'\uFEFB',
}


def _reshape_arabic(text: str) -> str:
    """
    يُحوِّل النص العربي إلى أشكال عرض صحيحة (Presentation Forms)
    ويعكس الترتيب للعرض RTL — بدون مكتبات خارجية ودون الحاجة لـ libraqm.
    """
    chars = list(str(text))
    result = []
    i = 0
    while i < len(chars):
        ch = chars[i]
        # لام-ألف ليغاتشر
        if ch == '\u0644' and i+1 < len(chars) and chars[i+1] in '\u0622\u0623\u0625\u0627':
            pair = ch + chars[i+1]
            if pair in _AR_LAM_ALEF:
                pj = i > 0 and _AR_JOIN.get(chars[i-1], 0) == 2
                lc = _AR_LAM_ALEF[pair]
                result.append(chr(ord(lc)+1) if pj else lc)
                i += 2; continue
        if ch not in _AR_FORMS:
            result.append(ch); i += 1; continue
        jt = _AR_JOIN.get(ch, 0)
        if jt == 0:
            result.append(_AR_FORMS[ch][0]); i += 1; continue
        pj = i > 0 and _AR_JOIN.get(chars[i-1], 0) == 2
        nj = i+1 < len(chars) and _AR_JOIN.get(chars[i+1], 0) in (1, 2)
        f  = _AR_FORMS[ch]
        if   pj and jt == 2 and nj: result.append(f[3])
        elif pj and jt == 2:         result.append(f[1])
        elif jt == 2 and nj:         result.append(f[2])
        elif jt == 1 and pj:         result.append(f[1])
        else:                         result.append(f[0])
        i += 1
    return ''.join(reversed(result))


def _ar(text: str) -> str:
    """اختصار: يُشكّل النص ويعكسه للعرض الصحيح."""
    return _reshape_arabic(str(text))


# مسارات خطوط احتياطية إضافية (موجودة غالباً على أغلب صور Docker/Linux)
FALLBACK_FONT_PATHS = [
    ARABIC_FONT_PATH,
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
]

def _load_arabic_font(size: int) -> "ImageFont.FreeTypeFont":
    """يحمّل خط قابل للتحجيم من Google (Amiri) أو من مسارات محلية احتياطية."""
    if not PILLOW_OK:
        return ImageFont.load_default()

    # 1. حاول استخدام الخط المحمّل من Google (إن وجد)
    if ARABIC_FONT_BYTES is not None:
        try:
            return ImageFont.truetype(io.BytesIO(ARABIC_FONT_BYTES), size)
        except Exception as e:
            log.warning(f"فشل استخدام خط Amiri المحمّل: {e}")

    # 2. احتياطي: جرّب عدّة مسارات محلية قابلة للتحجيم
    for path in FALLBACK_FONT_PATHS:
        if os.path.exists(path):
            try:
                return ImageFont.truetype(path, size)
            except Exception as e:
                log.warning(f"فشل تحميل الخط من {path}: {e}")

    # 3. فشل الجميع → الخط الافتراضي (تحذير: لا يستجيب لتغيير الحجم في أغلب الحالات)
    log.error(
        f"⚠️ لا يوجد أي خط TTF قابل للتحجيم على هذا السيرفر — سيظهر النص بحجم ثابت "
        f"بدل الحجم المطلوب ({size}px). ثبّت خط unifont أو تأكد من نجاح تحميل Amiri."
    )
    try:
        return ImageFont.load_default(size=size)   # يعمل فقط على Pillow >= 10.1
    except TypeError:
        return ImageFont.load_default()


def _text_width(draw: "ImageDraw.Draw", text: str, font) -> int:
    """يقيس عرض نص بالبكسل."""
    try:
        bb = draw.textbbox((0, 0), text, font=font)
        return bb[2] - bb[0]
    except Exception:
        return len(text) * (font.size if hasattr(font, 'size') else 10)


def _wrap_ar_text(text: str, font, max_w: int, draw_ref: "ImageDraw.Draw",
                  max_lines: int = 2) -> List[str]:
    """يكسر النص العربي المُشكَّل إلى سطور حسب العرض المتاح."""
    words = str(text).split()
    lines: List[str] = []
    cur: List[str] = []
    for w in words:
        test = ' '.join(cur + [w])
        if _text_width(draw_ref, test, font) > max_w and cur:
            lines.append(' '.join(cur))
            cur = [w]
            if len(lines) >= max_lines:
                last = lines[-1]
                while last and _text_width(draw_ref, last + '...', font) > max_w:
                    last = last.rsplit(' ', 1)[0]
                lines[-1] = last + ('...' if last != lines[-1] else '')
                return lines
        else:
            cur.append(w)
    if cur and len(lines) < max_lines:
        lines.append(' '.join(cur))
    return lines or [str(text)]


# ══════════════════════════════════════════════════════════════
#  Canvas الإعلان — تصميم يطابق تصميم الموقع بألوان ذهبية
# ══════════════════════════════════════════════════════════════

# ── ألوان التصميم ──
_C_BG         = (22,  22,  34)   # خلفية داكنة
_C_CARD       = (32,  32,  50)   # خلفية البطاقة
_C_DIVIDER    = (55,  50,  90)   # فاصل بين البطاقات
_C_COVER_PH   = (45,  35,  75)   # placeholder الغلاف
_C_COVER_BRD  = (80,  60, 120)   # إطار placeholder
_C_GOLD_TITLE = (212, 175,  55)  # لون اسم الرواية
_C_GOLD_CH    = (255, 200,  80)  # لون رقم الفصل
_C_META       = (140, 135, 165)  # لون النصوص الثانوية
_C_FOOTER_URL = (180, 150,  60)  # لون رابط الموقع في الذيل
_C_FOOTER_DT  = (120, 115, 145)  # لون التاريخ

# ── أبعاد ──
_CARD_H     = 170    # ارتفاع البطاقة
_COLS       = 2      # أعمدة
_CARD_PAD   = 0      # لا padding خارجي (مثل الموقع)
_ROW_GAP    = 1      # مسافة بين الصفوف
_COVER_W    = 108    # عرض الغلاف
_COVER_H    = 150    # ارتفاع الغلاف
_COVER_PAD  = 10     # مسافة الغلاف من حافة البطاقة
_TEXT_LPAD  = 16     # padding يسار النص
_FOOTER_H   = 44
_TOTAL_W    = 1060   # عرض الصورة لعمودين، 530 لعمود واحد



# ── صورة الخلفية محفوظة في الذاكرة عند التهيئة ──
ANN_BG_BYTES: Optional[bytes] = None   # يُضبط في main() من المسار المحفوظ في DB

# ── ثوابت تصميم ZEUS ──
_ZEUS_BG_W   = 1983
_ZEUS_BG_H   = 793
_GOLD_BRD    = (180, 120, 20)
_GOLD_TEXT   = (255, 220, 100)
_CHAP_BG     = (18, 12, 6)
_BRD_PX      = 3     # سماكة الإطار الذهبي


class AnnouncementCanvas:
    """
    يرسم صورة إعلان بتصميم ZEUS:
    - خلفية ثابتة (صورة ZEUS المحفوظة)، تُمدّ رأسياً عند الحاجة
    - كل رواية: بطاقة (غلاف + إطار ذهبي) + مربع رقم الفصول تحتها
    - 1 رواية: كانفاس ضيق (نصف العرض)
    - 2-4: على صف واحد
    - 5+ : 4 في الصف الأول ثم 4 في الصف التالي...
    entries: [{"first_chapter", "last_chapter", "cover_bytes"}]
    """

    def __init__(self, entries: List[Dict]):
        self.entries = entries

    @staticmethod
    def _rounded_mask(w: int, h: int, r: int) -> "Image.Image":
        m = Image.new("L", (w, h), 0)
        ImageDraw.Draw(m).rounded_rectangle([0, 0, w-1, h-1], radius=r, fill=255)
        return m

    @staticmethod
    def _paste_cover(canvas: "Image.Image", entry: Dict,
                     cx: int, cy: int, cw: int, ch: int, radius: int = 8):
        """يرسم غلاف الرواية أو placeholder داخل البطاقة."""
        draw = ImageDraw.Draw(canvas)
        if entry.get("cover_bytes"):
            try:
                cimg = Image.open(io.BytesIO(entry["cover_bytes"])).convert("RGB")
                tr = cw / ch
                sr = cimg.width / cimg.height
                if sr > tr:
                    nw = int(cimg.height * tr)
                    off = (cimg.width - nw) // 2
                    cimg = cimg.crop((off, 0, off+nw, cimg.height))
                else:
                    nh = int(cimg.width / tr)
                    cimg = cimg.crop((0, 0, cimg.width, nh))
                cimg = cimg.resize((cw, ch), Image.LANCZOS)
                mask = AnnouncementCanvas._rounded_mask(cw, ch, radius)
                rgba = cimg.convert("RGBA"); rgba.putalpha(mask)
                canvas.paste(rgba, (cx, cy), rgba)
                return
            except Exception:
                pass
        # placeholder داكن بتدرج
        for y_off in range(ch):
            ratio = y_off / ch
            r = int(20 + ratio * 20); g = int(10 + ratio * 10); b = int(40 + ratio * 30)
            draw.line([(cx, cy+y_off), (cx+cw, cy+y_off)], fill=(r,g,b))

    def render(self) -> bytes:
        if not PILLOW_OK:
            raise RuntimeError("Pillow غير مثبت — pip install Pillow")
        n = len(self.entries)
        if n == 0:
            raise ValueError("لا روايات")

        # ── حجم البطاقة حسب العدد ──
        # 4 أعمدة حتى 8 روايات، و5 أعمدة لما يزيد عن ذلك، مع عدد أسطر مفتوح.
        CARDS_PER_ROW = 5 if n > 8 else min(4, max(1, n))

        if n == 1:
            cw, ch = 380, 560
        elif n == 2:
            cw, ch = 400, 590
        elif n == 3:
            cw, ch = 360, 555
        else:
            # 4 أو أكثر: نحسب حجماً يناسب الخلفية
            cw = max(200, (_ZEUS_BG_W - 160) // CARDS_PER_ROW - 40)
            ch = int(cw * (560 / 380))

        CHAP_H    = max(44, int(ch * 0.08))
        CHAP_GAP  = 10
        CARD_TOT  = ch + CHAP_GAP + CHAP_H   # ارتفاع البطاقة الكاملة
        CARD_GAP  = max(24, int(cw * 0.07))  # مسافة بين البطاقات

        rows = math.ceil(n / CARDS_PER_ROW)

        # ── أبعاد الكانفاس ──
        ROW_W = CARDS_PER_ROW * cw + (CARDS_PER_ROW - 1) * CARD_GAP
        if n == 1:
            CANVAS_W = cw + 120
        else:
            CANVAS_W = max(_ZEUS_BG_W, ROW_W + 160)

        VERT_PAD = max(40, (_ZEUS_BG_H - CARD_TOT) // 2)
        CANVAS_H = max(_ZEUS_BG_H, VERT_PAD * 2 + rows * CARD_TOT + (rows-1) * 50)

        # ── الخلفية ──
        if ANN_BG_BYTES and n > 1:
            try:
                bg = Image.open(io.BytesIO(ANN_BG_BYTES)).convert("RGB")
                # مدّ رأسياً إذا لزم
                if CANVAS_H > _ZEUS_BG_H or CANVAS_W != bg.width:
                    bg = bg.resize((CANVAS_W, CANVAS_H), Image.LANCZOS)
                canvas = bg.copy()
            except Exception:
                canvas = Image.new("RGB", (CANVAS_W, CANVAS_H), (0, 0, 0))
        else:
            canvas = Image.new("RGB", (CANVAS_W, CANVAS_H), (0, 0, 0))

        draw = ImageDraw.Draw(canvas)
        font_chap = _load_arabic_font(max(24, int(CHAP_H * 0.62)))

        for idx, entry in enumerate(self.entries):
            row = idx // CARDS_PER_ROW
            col = idx % CARDS_PER_ROW

            cards_this_row = min(CARDS_PER_ROW, n - row * CARDS_PER_ROW)
            row_total_w = cards_this_row * cw + (cards_this_row - 1) * CARD_GAP
            x_start = (CANVAS_W - row_total_w) // 2
            cx = x_start + col * (cw + CARD_GAP)
            cy = VERT_PAD + row * (CARD_TOT + 50)

            # الإطار الذهبي
            draw.rounded_rectangle(
                [cx - _BRD_PX, cy - _BRD_PX, cx + cw + _BRD_PX, cy + ch + _BRD_PX],
                radius=10, fill=_GOLD_BRD)

            # الغلاف
            self._paste_cover(canvas, entry, cx, cy, cw, ch, radius=7)

            # مربع الفصل
            first = entry.get("first_chapter", 0)
            last  = entry.get("last_chapter", first)
            ch_text = str(first) if first == last else f"{first}-{last}"

            try:
                bb = draw.textbbox((0, 0), ch_text, font=font_chap)
                tw = bb[2] - bb[0]
            except Exception:
                tw = len(ch_text) * 14

            box_w = max(int(cw * 0.55), tw + 40)
            bx = cx + (cw - box_w) // 2
            by = cy + ch + CHAP_GAP

            # إطار ذهبي للمربع
            draw.rounded_rectangle(
                [bx - 2, by - 2, bx + box_w + 2, by + CHAP_H + 2],
                radius=9, fill=_GOLD_BRD)
            # داخل المربع
            draw.rounded_rectangle(
                [bx, by, bx + box_w, by + CHAP_H],
                radius=7, fill=_CHAP_BG)
            # النص — anchor="mm" يتوسط النص فعلياً (أفقياً وعمودياً) اعتماداً
            # على مركز الصندوق الهندسي، بدل الاعتماد على th/tw اليدوي الذي
            # كان يتجاهل الإزاحة العلوية للخط (bb[1]) ويسبب نزول النص للأسفل
            draw.text(
                (bx + box_w / 2, by + CHAP_H / 2),
                ch_text, font=font_chap, fill=_GOLD_TEXT, anchor="mm"
            )

        buf = io.BytesIO()
        canvas.save(buf, format="JPEG", quality=94, optimize=True)
        buf.seek(0)
        return buf.read()

		

# ══════════════════════════════════════════════════════════════
#  طابور الإعلانات — المنطق المحسّن (تم تعديل _get_upcoming_serial_times)
# ══════════════════════════════════════════════════════════════

class AnnouncementQueue:
    """
    طابور الإعلانات الذكي.

    قواعد الانتظار:
    - نشر منفرد / جماعي / مجدول → إعلان فوري (لا انتظار)
    - نشر تسلسلي واحد انتهى → إعلان فوري
    - نشر تسلسلي + جداول أخرى ستنتهي خلال SERIAL_CLUSTER_WINDOW_MINUTES →
      ينتظر حتى آخر جدول في النافذة، ثم يُعلن الجميع معاً
    - إذا كان الجدول التالي بعد النافذة → يُعلن الموجودين فوراً
    """

    def __init__(self, db_collection, bot: commands.Bot, settings_collection):
        self.col      = db_collection
        self.settings = settings_collection
        self.bot      = bot
        self._lock    = asyncio.Lock()
        self._pending_recheck: Optional[asyncio.Task] = None

    async def register_publish(
        self,
        novel_arabic: str,
        slug: str,
        first_chapter: int,
        last_chapter: int,
        cover_bytes: Optional[bytes] = None,
        source: str = "manual",
    ):
        doc = {
            "novel_arabic":  novel_arabic,
            "slug":          slug,
            "first_chapter": first_chapter,
            "last_chapter":  last_chapter,
            "cover_bytes":   cover_bytes,
            "source":        source,
            "published_at":  datetime.now(BAGHDAD_TZ).isoformat(),
            "announced":     False,
        }
        await self.col.insert_one(doc)
        log.info(f"[Queue] سُجِّل: {novel_arabic} ف{first_chapter}-{last_chapter} ({source})")
        asyncio.create_task(self._check_and_announce())

    async def _check_and_announce(self):
        async with self._lock:
            pending = await self.col.find({"announced": False}).to_list(length=1000)
            if not pending:
                return

            # هل جميع العناصر المعلقة من نشر غير تسلسلي؟ → أعلن فوراً
            all_non_serial = all(p.get("source") != "serial" for p in pending)
            if all_non_serial:
                log.info(f"[Queue] نشر غير تسلسلي — إعلان فوري ({len(pending)} عنصر)")
                await self._fire_announcement(pending)
                return

            # احسب الجداول التسلسلية القادمة ضمن النافذة
            now           = datetime.now(BAGHDAD_TZ)
            window_end    = now + timedelta(minutes=SERIAL_CLUSTER_WINDOW_MINUTES)
            upcoming      = await self._get_upcoming_serial_times(now)
            within_window = [t for t in upcoming if now < t <= window_end]

            if within_window:
                # ينتظر حتى آخر جدول في النافذة + 90 ثانية هامش
                latest       = max(within_window)
                wait_seconds = (latest - now).total_seconds() + 90
                log.info(
                    f"[Queue] ينتظر {len(within_window)} جدول تسلسلي ضمن النافذة. "
                    f"آخرها: {latest.strftime('%H:%M')} بغداد. "
                    f"الانتظار: {wait_seconds/60:.1f} دقيقة"
                )
                # إلغاء مهمة إعادة الفحص القديمة إن وجدت
                if self._pending_recheck and not self._pending_recheck.done():
                    self._pending_recheck.cancel()
                self._pending_recheck = asyncio.create_task(
                    self._delayed_recheck(wait_seconds)
                )
            else:
                # لا جداول قادمة ضمن النافذة → أعلن الآن
                log.info(f"[Queue] لا جداول ضمن النافذة — إعلان فوري ({len(pending)} عنصر)")
                await self._fire_announcement(pending)

    async def _delayed_recheck(self, delay_seconds: float):
        try:
            await asyncio.sleep(max(30, delay_seconds))
            await self._check_and_announce()
        except asyncio.CancelledError:
            log.info("[Queue] مهمة إعادة الفحص أُلغيت (جدول جديد سيتولى)")

    async def _get_upcoming_serial_times(self, now: datetime) -> List[datetime]:
        """يعيد أوقات الجداول التسلسلية النشطة القادمة خلال اليوم من MongoDB."""
        db = db_client.get_database("rewyat_bot")
        upcoming = []
        async for doc in db.serial_schedules.find({"finished": False, "paused": False}):
            published = doc.get("published_count", 0)
            total     = doc.get("total_chapters", 0)
            if published >= total:
                continue
            for slot_doc in _serial_slots(doc):
                h = slot_doc.get("hour", 0); m = slot_doc.get("minute", 0)
                candidate = now.replace(hour=h, minute=m, second=0, microsecond=0)
                if candidate <= now:
                    candidate += timedelta(days=1)
                upcoming.append(candidate)
        return upcoming

    async def _fire_announcement(self, pending: list):
        """يُرسل إعلاناً واحداً يجمع كل الروايات المعلقة."""
        log.info(f"[Queue] إطلاق إعلان لـ {len(pending)} رواية")

        date_str = datetime.now(BAGHDAD_TZ).strftime("%Y/%m/%d")
        settings = await self._get_settings()

        # أعد بناء قائمة الإدخالات مع الأغلفة
        entries: List[Dict] = []
        for p in pending:
            cover = p.get("cover_bytes")
            if not cover and ann_cog:
                cover = await ann_cog.get_cover(p.get("slug", ""))
            entries.append({
                "novel_arabic":  p["novel_arabic"],
                "slug":          p.get("slug", ""),
                "first_chapter": p.get("first_chapter", p.get("last_chapter", 0)),
                "last_chapter":  p.get("last_chapter", 0),
                "cover_bytes":   cover,
            })

        # تحديد source للنص: إذا وجد serial فهو serial، وإلا أكثر تكرار
        sources = [p.get("source", "manual") for p in pending]
        if "serial" in sources:
            source_for_text = "serial"
        else:
            source_for_text = max(set(sources), key=sources.count)

        # بناء النص والصورة
        text = _build_announcement_text(entries, source_for_text, date_str)

        image_bytes = None
        try:
            canvas      = AnnouncementCanvas(entries)
            image_bytes = canvas.render()
        except Exception as e:
            log.error(f"[Queue] فشل رسم Canvas: {e}")

        # إرسال
        await self._send_discord(settings, text, image_bytes)
        await self._send_telegram(settings, text, image_bytes)

        # تعليم الكل كمُعلَن
        ids = [p["_id"] for p in pending]
        await self.col.update_many(
            {"_id": {"$in": ids}},
            {"$set": {"announced": True, "announced_at": datetime.now(BAGHDAD_TZ).isoformat()}}
        )
        log.info(f"[Queue] تم الإعلان عن {len(pending)} رواية في رسالة واحدة")

    async def _send_discord(self, settings: dict, text: str, image_bytes: Optional[bytes]):
        channel_id = settings.get("discord_announce_channel")
        if not channel_id:
            log.warning("[Queue] لم يُحدَّد قناة ديسكورد للإعلانات")
            return
        try:
            channel = self.bot.get_channel(int(channel_id))
            if not channel:
                channel = await self.bot.fetch_channel(int(channel_id))
            if not channel:
                log.error(f"[Queue] لم يُعثر على قناة ديسكورد {channel_id}")
                return
            if image_bytes:
                file = discord.File(io.BytesIO(image_bytes), filename="announcement.jpg")
                await channel.send(content=text, file=file)
            else:
                await channel.send(content=text)
            log.info(f"[Queue] أُرسل الإعلان لديسكورد #{channel.name}")
        except Exception as e:
            log.error(f"[Queue] فشل إرسال ديسكورد: {e}")

    async def _send_telegram(self, settings: dict, text: str, image_bytes: Optional[bytes]):
        tg_token   = settings.get("telegram_bot_token")
        tg_chat_id = settings.get("telegram_channel_id")
        if not tg_token or not tg_chat_id:
            return
        base = f"https://api.telegram.org/bot{tg_token}"
        try:
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=30)) as session:
                # ملصق أولاً
                try:
                    await session.post(f"{base}/sendSticker", json={
                        "chat_id": tg_chat_id,
                        "sticker": STICKER_FILE_ID
                    })
                except Exception as e:
                    log.error(f"[Queue] فشل إرسال الملصق: {e}")

                if image_bytes:
                    form = aiohttp.FormData()
                    form.add_field("chat_id", str(tg_chat_id))
                    form.add_field("caption", text[:1024])
                    form.add_field("photo", io.BytesIO(image_bytes),
                                   filename="announcement.jpg", content_type="image/jpeg")
                    async with session.post(f"{base}/sendPhoto", data=form) as r:
                        result = await r.json()
                        if result.get("ok"):
                            log.info("[Queue] أُرسل الإعلان لتليجرام")
                        else:
                            log.error(f"[Queue] فشل تليجرام: {result}")
                else:
                    async with session.post(f"{base}/sendMessage", json={
                        "chat_id": tg_chat_id, "text": text[:4096],
                    }) as r:
                        result = await r.json()
                        if not result.get("ok"):
                            log.error(f"[Queue] فشل تليجرام: {result}")
        except Exception as e:
            log.error(f"[Queue] خطأ تليجرام: {e}")

    async def _get_settings(self) -> dict:
        doc = await self.settings.find_one({"_id": "bot_settings"})
        return doc or {}

    async def update_setting(self, key: str, value):
        await self.settings.update_one(
            {"_id": "bot_settings"}, {"$set": {key: value}}, upsert=True
        )

    async def get_pending_count(self) -> int:
        return await self.col.count_documents({"announced": False})

    async def get_pending_entries(self) -> List[dict]:
        return await self.col.find({"announced": False}).to_list(length=1000)

    async def clear_pending(self):
        await self.col.update_many(
            {"announced": False},
            {"$set": {"announced": True, "cancelled": True}}
        )


# ══════════════════════════════════════════════════════════════
#  CoverUploadView
# ══════════════════════════════════════════════════════════════

class CoverUploadView(discord.ui.View):
    def __init__(self, uid: int, bot: commands.Bot, channel_id: int):
        super().__init__(timeout=180)
        self.uid        = uid
        self.bot        = bot
        self.channel_id = channel_id
        self.cover_bytes: Optional[bytes] = None
        self._done = asyncio.Event()

    @discord.ui.button(label="إرسال الصورة", style=discord.ButtonStyle.primary, emoji="🖼️")
    async def upload_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.uid:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        button.disabled = True; button.label = "في انتظار الصورة..."
        await interaction.response.edit_message(view=self)
        await interaction.followup.send(
            embed=inf_embed("أرسل الصورة الآن", "أرسل صورة الغلاف (JPG/PNG) في هذه القناة خلال 3 دقائق.")
        )
        def check(m):
            return (m.author.id == self.uid and
                    m.channel.id == self.channel_id and
                    m.attachments)
        try:
            msg = await self.bot.wait_for("message", check=check, timeout=180)
            att = msg.attachments[0]
            if not att.content_type or not att.content_type.startswith("image/"):
                await interaction.followup.send(embed=err_embed("نوع خاطئ", "يجب أن يكون الملف صورة (JPG/PNG)."))
                return
            if att.size > 10 * 1024 * 1024:
                await interaction.followup.send(embed=err_embed("الصورة كبيرة جداً", "الحد الأقصى 10MB."))
                return
            raw = await att.read()
            if PILLOW_OK:
                try:
                    img = Image.open(io.BytesIO(raw)).convert("RGB")
                    if max(img.size) > 1200:
                        img.thumbnail((1200, 1200), Image.LANCZOS)
                    buf = io.BytesIO()
                    img.save(buf, format="JPEG", quality=88)
                    raw = buf.getvalue()
                except Exception:
                    pass
            self.cover_bytes = raw
            self._done.set()
            await interaction.followup.send(
                embed=ok_embed("تم استلام الغلاف", f"الحجم: {len(raw)//1024} KB")
            )
        except asyncio.TimeoutError:
            await interaction.followup.send(embed=err_embed("انتهى الوقت", "لم تُرسل أي صورة."))

    @discord.ui.button(label="تخطي", style=discord.ButtonStyle.secondary)
    async def skip_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.uid:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        await interaction.response.edit_message(
            embed=warn_embed("تم التخطي", "يمكنك رفع الغلاف لاحقاً عبر `/رفع_غلاف`"),
            view=None
        )
        self.stop()

    async def wait(self):
        try:
            await asyncio.wait_for(self._done.wait(), timeout=200)
        except asyncio.TimeoutError:
            pass
        return self


class DiscordChannelPickerView(discord.ui.View):
    def __init__(self, ctx: commands.Context, bot: commands.Bot):
        super().__init__(timeout=120)
        self.ctx = ctx; self.bot = bot; self.chosen_channel_id: Optional[str] = None
        self._build()

    def _build(self):
        self.clear_items()
        if self.ctx.guild:
            text_channels = [ch for ch in self.ctx.guild.channels if isinstance(ch, discord.TextChannel)][:25]
            if text_channels:
                opts = [
                    discord.SelectOption(label=f"#{ch.name}"[:80], value=str(ch.id), description=f"القناة {ch.id}")
                    for ch in text_channels
                ]
                sel = discord.ui.Select(placeholder="اختر قناة من هذا السيرفر...", options=opts)
                sel.callback = self._on_select; self.add_item(sel)
        manual_btn = discord.ui.Button(label="إدخال ID قناة يدوياً", style=discord.ButtonStyle.secondary)
        manual_btn.callback = self._on_manual; self.add_item(manual_btn)
        cancel_btn = discord.ui.Button(label="إلغاء", style=discord.ButtonStyle.danger)
        cancel_btn.callback = self._on_cancel; self.add_item(cancel_btn)

    async def _on_select(self, interaction: discord.Interaction):
        if interaction.user.id != self.ctx.author.id:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        self.chosen_channel_id = interaction.data["values"][0]
        ch = self.ctx.guild.get_channel(int(self.chosen_channel_id))
        await interaction.response.edit_message(
            embed=ok_embed("تم الاختيار", f"قناة الإعلانات: #{ch.name if ch else self.chosen_channel_id}"),
            view=None
        ); self.stop()

    async def _on_manual(self, interaction: discord.Interaction):
        if interaction.user.id != self.ctx.author.id:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        await interaction.response.edit_message(
            embed=inf_embed("أرسل ID القناة", "أرسل ID القناة (أرقام فقط) في هذه القناة:"), view=None
        )
        def check(m): return m.author.id == self.ctx.author.id and m.channel.id == self.ctx.channel.id
        try:
            msg = await self.ctx.bot.wait_for("message", check=check, timeout=60)
            cid = msg.content.strip()
            if cid.isdigit():
                self.chosen_channel_id = cid; self.stop()
            else:
                await self.ctx.send(embed=err_embed("ID غير صالح", "يجب أن يكون أرقاماً فقط."))
        except asyncio.TimeoutError:
            await self.ctx.send(embed=err_embed("انتهى الوقت"))

    async def _on_cancel(self, interaction: discord.Interaction):
        await interaction.response.edit_message(embed=warn_embed("تم الإلغاء"), view=None); self.stop()


class AnnouncementSettingsView(discord.ui.View):
    def __init__(self, ctx: commands.Context, queue: AnnouncementQueue, settings: dict):
        super().__init__(timeout=120)
        self.ctx = ctx; self.queue = queue; self.settings = settings

    def build_embed(self) -> discord.Embed:
        s  = self.settings
        dc = s.get("discord_announce_channel", "غير مُحدَّد")
        tg = s.get("telegram_channel_id", "غير مُحدَّد")
        tk = "مُهيأ" if s.get("telegram_bot_token") else "غير مُهيأ"
        embed = make_embed("إعدادات نظام الإعلانات", color=Colors.INFO)
        embed.add_field(name="قناة ديسكورد", value=f"`{dc}`", inline=False)
        embed.add_field(name="قناة تليجرام", value=f"`{tg}`", inline=True)
        embed.add_field(name="بوت تليجرام",  value=tk,        inline=True)
        embed.add_field(name="نافذة انتظار التسلسلي",
                        value=f"`{SERIAL_CLUSTER_WINDOW_MINUTES}` دقيقة", inline=False)
        embed.add_field(
            name="كيف يعمل النظام",
            value=(
                "- نشر منفرد/جماعي/مجدول: إعلان فوري\n"
                "- تسلسلي واحد: إعلان فوري\n"
                "- تسلسليان بنفس الوقت: إعلان مجمع\n"
                "- تسلسليان فارقهما اقل من ساعتين: ينتظر الثاني\n"
                "- فارق اكثر من ساعتين: يُعلن الأول ثم الثاني كل في وقته"
            ),
            inline=False
        )
        return embed

    @discord.ui.button(label="تغيير نافذة الانتظار", style=discord.ButtonStyle.secondary)
    async def change_window(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.ctx.author.id:
            return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
        opts = [
            discord.SelectOption(label="30 دقيقة",             value="30"),
            discord.SelectOption(label="ساعة (60 دقيقة)",      value="60"),
            discord.SelectOption(label="ساعتان (120 — افتراضي)", value="120"),
            discord.SelectOption(label="3 ساعات (180 دقيقة)",   value="180"),
            discord.SelectOption(label="6 ساعات (360 دقيقة)",   value="360"),
        ]
        sel_view = discord.ui.View(timeout=30)
        sel      = discord.ui.Select(placeholder="اختر المدة...", options=opts)
        async def sel_cb(i):
            if i.user.id != self.ctx.author.id: return
            global SERIAL_CLUSTER_WINDOW_MINUTES
            SERIAL_CLUSTER_WINDOW_MINUTES = int(i.data["values"][0])
            await self.queue.update_setting("announcement_wait_minutes", SERIAL_CLUSTER_WINDOW_MINUTES)
            await i.response.edit_message(
                embed=ok_embed("تم التحديث", f"نافذة الانتظار: **{SERIAL_CLUSTER_WINDOW_MINUTES}** دقيقة"), view=None
            )
        sel.callback = sel_cb; sel_view.add_item(sel)
        await interaction.response.send_message(view=sel_view, ephemeral=True)


# ══════════════════════════════════════════════════════════════
#  AnnouncementCog
# ══════════════════════════════════════════════════════════════

class AnnouncementCog(commands.Cog):
    def __init__(self, bot: commands.Bot, db, announcement_queue: AnnouncementQueue):
        self.bot   = bot
        self.db    = db
        self.queue = announcement_queue

    def _is_owner(self, uid: int) -> bool:
        return uid == OWNER_ID

    async def prompt_cover_upload(
        self, interaction: discord.Interaction, slug: str, novel_arabic: str
    ) -> Optional[bytes]:
        uid  = interaction.user.id
        view = CoverUploadView(uid, self.bot, interaction.channel_id)
        await interaction.followup.send(
            embed=make_embed(
                "رفع غلاف الرواية",
                f"**{novel_arabic}**\n\n"
                "أرسل صورة غلاف الرواية (JPG/PNG) لاستخدامها في الإعلانات.\n"
                "أو اضغط **تخطي** لإضافة الغلاف لاحقاً.",
                Colors.PURPLE
            ),
            view=view
        )
        await view.wait()
        if view.cover_bytes:
            await self.db.novels_covers.update_one(
                {"slug": slug},
                {"$set": {
                    "slug": slug, "novel_arabic": novel_arabic,
                    "cover_bytes": view.cover_bytes,
                    "updated_at": datetime.now(BAGHDAD_TZ).isoformat()
                }},
                upsert=True
            )
            return view.cover_bytes
        return None

    async def get_cover(self, slug: str) -> Optional[bytes]:
        doc = await self.db.novels_covers.find_one({"slug": slug})
        return doc.get("cover_bytes") if doc else None

    @commands.hybrid_command(name="قناة_الإعلانات", description="تحديد قناة ديسكورد لإعلانات الفصول")
    @commands.has_permissions(manage_guild=True)
    async def set_discord_channel(self, ctx: commands.Context):
        if not self._is_owner(ctx.author.id):
            return await ctx.send(embed=err_embed("غير مصرح"), ephemeral=True)
        view = DiscordChannelPickerView(ctx, self.bot)
        await ctx.send(
            embed=make_embed("قناة إعلانات ديسكورد", "اختر طريقة تحديد القناة:", Colors.INFO),
            view=view
        )
        await view.wait()
        if view.chosen_channel_id:
            await self.queue.update_setting("discord_announce_channel", view.chosen_channel_id)
            try:
                ch = self.bot.get_channel(int(view.chosen_channel_id))
                ch_name = f"#{ch.name}" if ch else str(view.chosen_channel_id)
            except Exception:
                ch_name = str(view.chosen_channel_id)
            await ctx.send(embed=ok_embed("تم الحفظ", f"قناة الإعلانات: {ch_name}"))

    @commands.hybrid_command(name="قناة_تليجرام", description="ربط قناة تليجرام لإعلانات الفصول")
    async def set_telegram_channel(self, ctx: commands.Context):
        if not self._is_owner(ctx.author.id):
            return await ctx.send(embed=err_embed("غير مصرح"), ephemeral=True)
        await ctx.send(
            embed=make_embed(
                "إعداد تليجرام",
                "أرسل رسالتين في هذه القناة:\n"
                "**1)** Token بوت تليجرام (من @BotFather)\n"
                "**2)** معرّف قناتك (مثال: `@MyChannel` أو `-100xxxxxxxxx`)\n\n"
                "اكتب `إلغاء` للتراجع.",
                Colors.INFO
            )
        )
        def check(m): return m.author.id == ctx.author.id and m.channel.id == ctx.channel.id
        try:
            msg1 = await self.bot.wait_for("message", check=check, timeout=120)
            if msg1.content.strip() == "إلغاء":
                return await ctx.send(embed=warn_embed("تم الإلغاء"))
            token = msg1.content.strip()
            await ctx.send(embed=inf_embed("الآن أرسل معرّف القناة..."))
            msg2 = await self.bot.wait_for("message", check=check, timeout=60)
            if msg2.content.strip() == "إلغاء":
                return await ctx.send(embed=warn_embed("تم الإلغاء"))
            chat_id = msg2.content.strip()
            valid = await self._test_telegram(token, chat_id)
            if not valid:
                return await ctx.send(embed=err_embed("فشل الاختبار",
                    "تأكد من صحة التوكن ومعرّف القناة وأن البوت مُضاف للقناة كمشرف."))
            await self.queue.update_setting("telegram_bot_token", token)
            await self.queue.update_setting("telegram_channel_id", chat_id)
            await ctx.send(embed=ok_embed("تم ربط تليجرام",
                f"القناة: `{chat_id}`\nسيرسل البوت الإعلانات لتليجرام تلقائياً."))
        except asyncio.TimeoutError:
            await ctx.send(embed=err_embed("انتهى الوقت"))

    async def _test_telegram(self, token: str, chat_id: str) -> bool:
        url = f"https://api.telegram.org/bot{token}/sendMessage"
        try:
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10)) as s:
                async with s.post(url, json={
                    "chat_id": chat_id,
                    "text": "تم ربط البوت بنجاح. سيُرسل الإعلانات هنا."
                }) as r:
                    data = await r.json()
                    return data.get("ok", False)
        except Exception:
            return False

    @commands.hybrid_command(name="رفع_غلاف", description="رفع أو تحديث غلاف رواية موجودة")
    async def upload_cover(self, ctx: commands.Context):
        if not self._is_owner(ctx.author.id):
            return await ctx.send(embed=err_embed("غير مصرح"), ephemeral=True)
        novels_doc = await self.db.config.find_one({"_id": "novels"})
        novels = (novels_doc.get("data", {}).get("novels", []) if novels_doc else [])
        if not novels:
            return await ctx.send(embed=err_embed("لا روايات", "استخدم `/بحث_رواية` لإضافة روايات أولاً."))
        opts = [
            discord.SelectOption(
                label=n["arabic"][:80], value=n["slug"],
                description=f"slug: {n['slug'][:50]}", emoji="📚"
            )
            for n in novels[:25]
        ]
        sel_view = discord.ui.View(timeout=90)
        sel      = discord.ui.Select(placeholder="اختر الرواية...", options=opts)
        chosen   = {}
        async def sel_cb(interaction: discord.Interaction):
            if interaction.user.id != ctx.author.id:
                return await interaction.response.send_message(embed=err_embed("غير مسموح"), ephemeral=True)
            chosen["slug"]   = interaction.data["values"][0]
            chosen["arabic"] = next(n["arabic"] for n in novels if n["slug"] == chosen["slug"])
            for c in sel_view.children: c.disabled = True
            await interaction.response.edit_message(view=sel_view); sel_view.stop()
        sel.callback = sel_cb; sel_view.add_item(sel)
        await ctx.send(embed=inf_embed("اختر الرواية", "اختر الرواية التي تريد رفع غلافها:"), view=sel_view)
        await sel_view.wait()
        if "slug" not in chosen: return
        upload_view = CoverUploadView(ctx.author.id, self.bot, ctx.channel.id)
        await ctx.send(
            embed=make_embed(
                f"غلاف — {chosen['arabic']}",
                "أرسل صورة الغلاف (JPG/PNG) أو اضغط **تخطي**.", Colors.PURPLE
            ),
            view=upload_view
        )
        await upload_view.wait()
        if upload_view.cover_bytes:
            await self.db.novels_covers.update_one(
                {"slug": chosen["slug"]},
                {"$set": {
                    "slug": chosen["slug"], "novel_arabic": chosen["arabic"],
                    "cover_bytes": upload_view.cover_bytes,
                    "updated_at": datetime.now(BAGHDAD_TZ).isoformat()
                }},
                upsert=True
            )
            await ctx.send(embed=ok_embed("تم حفظ الغلاف", f"**{chosen['arabic']}**"))
        else:
            await ctx.send(embed=warn_embed("تم التخطي", "لم يُرفع أي غلاف."))

    @commands.hybrid_command(name="تجربة_إعلان", description="معاينة كيف ستبدو صورة الإعلان")
    async def preview_announcement(self, ctx: commands.Context):
        if not self._is_owner(ctx.author.id):
            return await ctx.send(embed=err_embed("غير مصرح"), ephemeral=True)
        if not PILLOW_OK:
            return await ctx.send(embed=err_embed("Pillow غير مثبت", "قم بتشغيل: `pip install Pillow`"))
        thinking = await ctx.send(embed=make_embed("جاري الرسم...", "يتم رسم الصورة التجريبية...", Colors.WARNING))
        pending = await self.queue.get_pending_entries()

        if pending:
            entries = []
            for p in pending:
                cover = p.get("cover_bytes")
                if not cover:
                    cover = await self.get_cover(p.get("slug", ""))
                entries.append({
                    "novel_arabic":  p["novel_arabic"],
                    "slug":          p.get("slug", ""),
                    "first_chapter": p.get("first_chapter", p.get("last_chapter", 0)),
                    "last_chapter":  p["last_chapter"],
                    "cover_bytes":   cover,
                })
        else:
            serial_docs = await self.db.serial_schedules.find({"finished": False, "paused": False}).to_list(length=100)
            entries = []
            for n in serial_docs:
                cover = await self.get_cover(n["slug"])
                pc = n.get("published_count", 0)
                batch = n.get("batch_size", 1)
                entries.append({
                    "novel_arabic":  n.get("novel_arabic", n["slug"]),
                    "slug":          n["slug"],
                    "first_chapter": pc + 1,
                    "last_chapter":  min(n.get("total_chapters", pc + batch), pc + batch),
                    "cover_bytes":   cover,
                })
            if not entries:
                entries = [
                    {"novel_arabic": f"رواية تجريبية {i}", "slug": f"test-{i}",
                     "first_chapter": i*10, "last_chapter": i*10+5, "cover_bytes": None}
                    for i in range(1, 5)
                ]

        try:
            canvas    = AnnouncementCanvas(entries)
            img_bytes = canvas.render()
            file      = discord.File(io.BytesIO(img_bytes), filename="preview.jpg")
            date_str  = datetime.now(BAGHDAD_TZ).strftime("%Y/%m/%d")
            sources   = [p.get("source", "serial") for p in (pending or [{"source":"serial"}])]
            src       = "serial" if "serial" in sources else sources[0]
            text_prev = _build_announcement_text(entries[:2], src, date_str)
            await thinking.delete()
            await ctx.send(
                content=f"**معاينة النص:**\n```\n{text_prev[:500]}\n```",
                file=file,
                embed=make_embed(
                    "معاينة الإعلان",
                    f"هكذا ستبدو الصورة والنص.\n"
                    f"{'بيانات معلقة حقيقية' if pending else 'بيانات تجريبية'}",
                    Colors.PURPLE
                )
            )
        except Exception as e:
            await thinking.edit(embed=err_embed("فشل الرسم", f"```{str(e)[:400]}```"))

    @commands.hybrid_command(name="إعلان_يدوي", description="إرسال الإعلان الآن بدون انتظار")
    async def manual_announce(self, ctx: commands.Context):
        if not self._is_owner(ctx.author.id):
            return await ctx.send(embed=err_embed("غير مصرح"), ephemeral=True)
        pending = await self.queue.get_pending_entries()
        if not pending:
            return await ctx.send(embed=warn_embed("لا يوجد شيء للإعلان", "لا توجد فصول منشورة غير مُعلَن عنها."))
        confirm_view = discord.ui.View(timeout=30)
        confirmed = {}
        yes_btn = discord.ui.Button(label=f"إعلان الآن ({len(pending)} رواية)", style=discord.ButtonStyle.success)
        no_btn  = discord.ui.Button(label="إلغاء", style=discord.ButtonStyle.danger)
        async def yes_cb(i):
            if i.user.id != ctx.author.id: return
            confirmed["ok"] = True
            for c in confirm_view.children: c.disabled = True
            await i.response.edit_message(view=confirm_view); confirm_view.stop()
        async def no_cb(i):
            if i.user.id != ctx.author.id: return
            await i.response.edit_message(embed=warn_embed("تم الإلغاء"), view=None); confirm_view.stop()
        yes_btn.callback = yes_cb; no_btn.callback = no_cb
        confirm_view.add_item(yes_btn); confirm_view.add_item(no_btn)
        novels_list = "\n".join(
            f"{p['novel_arabic']} — ف{p.get('first_chapter', p['last_chapter'])}-{p['last_chapter']} ({p.get('source','?')})"
            for p in pending[:10]
        )
        if len(pending) > 10: novels_list += f"\n... و {len(pending)-10} أخرى"
        await ctx.send(
            embed=make_embed("تأكيد الإعلان", f"سيتم الإعلان الآن عن:\n{novels_list}", Colors.WARNING),
            view=confirm_view
        )
        await confirm_view.wait()
        if "ok" not in confirmed: return
        thinking = await ctx.send(embed=make_embed("جاري الإرسال...", "", Colors.WARNING))
        await self.queue._fire_announcement(pending)
        await thinking.edit(embed=ok_embed("تم الإعلان", f"أُعلن عن **{len(pending)}** رواية."))

    @commands.hybrid_command(name="حالة_الإعلانات", description="عرض حالة طابور الإعلانات")
    async def announcement_status(self, ctx: commands.Context):
        if not self._is_owner(ctx.author.id):
            return await ctx.send(embed=err_embed("غير مصرح"), ephemeral=True)
        pending  = await self.queue.get_pending_entries()
        settings = await self.queue._get_settings()
        dc_ch = settings.get("discord_announce_channel", "غير مُحدَّد")
        tg_ch = settings.get("telegram_channel_id", "غير مُحدَّد")
        tg_ok = "مُهيأ" if settings.get("telegram_bot_token") else "غير مُهيأ"

        now      = datetime.now(BAGHDAD_TZ)
        upcoming = await self.queue._get_upcoming_serial_times(now)
        window_end = now + timedelta(minutes=SERIAL_CLUSTER_WINDOW_MINUTES)
        within   = [t for t in upcoming if now < t <= window_end]

        pending_text = "\n".join(
            f"{p['novel_arabic']} — ف{p.get('first_chapter', p['last_chapter'])}-{p['last_chapter']} ({p.get('source','?')})"
            for p in pending[:10]
        ) if pending else "لا يوجد"
        if len(pending) > 10: pending_text += f"\n... و {len(pending)-10} أخرى"

        serial_info = "\n".join(f"{t.strftime('%H:%M')} (بغداد)" for t in sorted(within)) if within else "لا توجد ضمن النافذة"

        embed = make_embed("حالة نظام الإعلانات", color=Colors.INFO)
        embed.add_field(name="قناة ديسكورد", value=f"`{dc_ch}`", inline=True)
        embed.add_field(name="تليجرام", value=f"`{tg_ch}` ({tg_ok})", inline=True)
        embed.add_field(name=f"في الطابور ({len(pending)})", value=pending_text, inline=False)
        embed.add_field(name=f"جداول ضمن {SERIAL_CLUSTER_WINDOW_MINUTES} دقيقة", value=serial_info, inline=False)
        if not PILLOW_OK:
            embed.add_field(name="تحذير", value="Pillow غير مثبت — لن تُرسم صورة", inline=False)
        view = discord.ui.View(timeout=30)
        if pending:
            ann_btn = discord.ui.Button(label="إعلان يدوي", style=discord.ButtonStyle.primary)
            ann_btn.callback = lambda i: self._quick_announce(i, ctx)
            view.add_item(ann_btn)
            clr_btn = discord.ui.Button(label="مسح الطابور", style=discord.ButtonStyle.danger)
            clr_btn.callback = lambda i: self._quick_clear(i, ctx)
            view.add_item(clr_btn)
        await ctx.send(embed=embed, view=view)

    async def _quick_announce(self, interaction: discord.Interaction, ctx):
        if interaction.user.id != ctx.author.id: return
        pending = await self.queue.get_pending_entries()
        await interaction.response.defer()
        await self.queue._fire_announcement(pending)
        await interaction.followup.send(embed=ok_embed("تم الإعلان"))

    async def _quick_clear(self, interaction: discord.Interaction, ctx):
        if interaction.user.id != ctx.author.id: return
        await self.queue.clear_pending()
        await interaction.response.send_message(embed=ok_embed("تم مسح الطابور"))

    @commands.hybrid_command(name="إعدادات_الإعلانات", description="عرض وتعديل إعدادات نظام الإعلانات")
    async def announcement_settings(self, ctx: commands.Context):
        if not self._is_owner(ctx.author.id):
            return await ctx.send(embed=err_embed("غير مصرح"), ephemeral=True)
        settings = await self.queue._get_settings()
        view = AnnouncementSettingsView(ctx, self.queue, settings)
        await ctx.send(embed=view.build_embed(), view=view)


# ══════════════════════════════════════════════════════════════
#  دالة دمج النظام
# ══════════════════════════════════════════════════════════════

ann_queue = None
ann_cog   = None

async def setup_announcement_system(bot: commands.Bot, db) -> Tuple[AnnouncementQueue, AnnouncementCog]:
    global ann_queue, ann_cog
    queue = AnnouncementQueue(
        db_collection       = db.announcement_queue,
        bot                 = bot,
        settings_collection = db.bot_settings
    )
    cog = AnnouncementCog(bot, db, queue)
    ann_queue = queue
    ann_cog   = cog
    return queue, cog


# ══════════════════════════════════════════════════════════════
#  تهيئة MongoDB وتشغيل البوت
# ══════════════════════════════════════════════════════════════

async def main():
    global db_client, novel_store, stats, account_manager

    try:
        db_client = motor.motor_asyncio.AsyncIOMotorClient(MONGODB_URI)
        db = db_client.get_database("rewyat_bot")
        log.info("تم الاتصال بـ MongoDB")
    except Exception as e:
        log.critical(f"فشل الاتصال بـ MongoDB: {e}")
        return

    # إنشاء الفهارس المطلوبة
    try:
        await db.serial_schedules.create_index("finished")
        await db.serial_schedules.create_index("paused")
        await db.serial_chapters.create_index([("serial_id", 1), ("number", 1)], unique=True)
        log.info("تم إنشاء الفهارس اللازمة")
    except Exception as e:
        log.warning(f"فشل إنشاء بعض الفهارس: {e}")

    config_col   = db.config
    jobs_col     = db.jobs
    stats_col    = db.stats
    accounts_col = db.accounts

    novel_store = NovelStorage(config_col)
    await novel_store.initialize()

    stats = StatsManager(stats_col)
    await stats.initialize()

    account_manager = AccountManager(accounts_col)
    await account_manager.initialize()

    await load_jobs(jobs_col)

    await setup_announcement_system(bot, db)
    await bot.add_cog(ann_cog)

    # تحميل خلفية الإعلان من الرابط
    async with aiohttp.ClientSession() as session:
        async with session.get("https://iili.io/C4oHOVS.png") as resp:
            if resp.status == 200:
                global ANN_BG_BYTES
                ANN_BG_BYTES = await resp.read()
                log.info("تم تحميل خلفية الإعلان بنجاح")
            else:
                log.warning(f"فشل تحميل الخلفية، رمز الحالة: {resp.status}")
        
        # ── إضافة: تحميل خط Amiri من Google ──
        async with session.get(ARABIC_FONT_URL) as resp2:
            if resp2.status == 200:
                global ARABIC_FONT_BYTES
                ARABIC_FONT_BYTES = await resp2.read()
                log.info("تم تحميل خط Amiri من Google بنجاح")
            else:
                log.warning(f"فشل تحميل الخط، رمز الحالة: {resp2.status}")

    token = (
        os.getenv("DISCORD_TOKEN")
        
    )
    log.info(f"بدء تشغيل بوت روايات v{VERSION}")
    await bot.start(token)


if __name__ == "__main__":
    asyncio.run(main())
