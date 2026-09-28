#!/usr/bin/env python3
"""
myhome.ge -> Telegram: нові оголошення від власників.

Команди:
  python watcher.py             перевіряти безперервно (кожні LOOP_MINUTES хв)
  python watcher.py --once      одна перевірка (для GitHub Actions / cron)
  python watcher.py --test      показати 3 свіжі оголошення й надіслати одне тестове в Telegram
  python watcher.py --chat-id   дізнатися chat_id (спершу напишіть боту /start)
  python watcher.py --reset     забути базу й наступного разу заново «запам'ятати» поточні оголошення
  python watcher.py --dump      зберегти «сирі» відповіді сайту у dump_list.json і dump_detail.json
  python watcher.py --preview ID  надіслати в робочий чат, як оголошення ID виглядатиме в каналі
  python watcher.py --post ID     одразу опублікувати оголошення ID у канал

Посилання на пошук беруться з searches.txt, база побачених оголошень — state.json,
шаблон поста для каналу — channel_template.txt.
"""

import argparse
import hashlib
import hmac
import html
import json
import os
import random
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from pathlib import Path

# ─────────────────────────────── НАЛАШТУВАННЯ ───────────────────────────────
# Токен і chat_id беруться зі змінних середовища (на GitHub — Secrets),
# а на своєму комп'ютері — з файлу telegram.json поруч зі скриптом.
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "")  # кілька чатів — через кому
TELEGRAM_CHANNEL_ID = os.getenv("TELEGRAM_CHANNEL_ID", "")  # канал для кнопки «Додати в канал»: @назва або -100...
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY", "")  # якщо задано — текст поста для каналу допише ШІ
OPENAI_MODEL = os.getenv("OPENAI_MODEL") or "gpt-5-mini"

LANG = "ru"                    # мова назв і посилань з myhome.ge: ru / en / ka
ONLY_OWNERS = True             # завжди додавати фільтр «Власник» (owner_type=physical)
PAGES_PER_RUN = 3              # скільки сторінок видачі перевіряти за один запуск
SEED_PAGES = 10                # скільки сторінок «запам'ятати» при першому запуску пошуку
FETCH_DETAILS = True           # догружати картку нового оголошення (телефон, автор)
AGENT_THRESHOLD = 3            # від скількох оголошень в одного автора ставити позначку ⚠️
SKIP_SUSPECTED_AGENTS = False  # True — такі оголошення взагалі не надсилати
MAX_ALERTS_PER_RUN = 25        # запобіжник від спаму; решта прийде наступного запуску
LOOP_MINUTES = 10              # інтервал у безперервному режимі
FAIL_ALERT_AFTER = 6           # після скількох невдалих перевірок поспіль написати в Telegram
KEEP_DAYS = 60                 # скільки днів пам'ятати побачені оголошення
CHANNEL_MAX_PHOTOS = 10        # скільки фото брати в пост каналу (Telegram дозволяє до 10)
CHANNEL_HIDE_PHONES = True     # прибирати телефони власника з опису в каналі
CHANNEL_DESCRIPTION_MAX = 350  # скільки символів опису власника брати в пост (0 — весь, скільки влізе)
TRANSLATE_ALERTS = True        # з OPENAI_API_KEY: перекладати російською грузинські/англійські опис і адресу в чаті
TRANSLATE_BUDGET_SECONDS = 180 # не більше стільки секунд на переклади за одну перевірку (запобіжник для GitHub)
# ──────────────────────────────────────────────────────────────────────────────

BASE_DIR = Path(__file__).resolve().parent
SEARCHES_FILE = BASE_DIR / "searches.txt"
STATE_FILE = BASE_DIR / "state.json"
TELEGRAM_FILE = BASE_DIR / "telegram.json"  # {"token": "...", "chat_id": "...", "channel_id": "..."} — не викладати на GitHub!
CHANNEL_TEMPLATE_FILE = BASE_DIR / "channel_template.txt"

API_URL = "https://api-statements.tnet.ge/v1/statements"
SITE = "https://www.myhome.ge"
LISTING_PATHS = {
    "ru": "/ru/nedvizhimost/{slug}-{id}/",
    "en": "/en/real-estate/{slug}-{id}/",
    "ka": "/udzravi-qoneba/{slug}-{id}/",
}
GEORGIA_TZ = timezone(timedelta(hours=4))  # у Грузії немає переходу на літній час
USER_AGENT = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36")

try:  # curl_cffi відправляє запит «як справжній Chrome» — так менше шансів натрапити на блок
    from curl_cffi import requests as cffi_requests
except ImportError:
    cffi_requests = None

def ssl_context():
    """Набір сертифікатів certifi: на Mac вбудований Python часто їх не бачить."""
    import ssl
    try:
        import certifi
        return ssl.create_default_context(cafile=certifi.where())
    except ImportError:
        return ssl.create_default_context()


if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(errors="replace")


def load_telegram_file():
    """Доповнює токен, chat_id і канал з telegram.json, якщо їх не задано змінними середовища."""
    global TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID, TELEGRAM_CHANNEL_ID, OPENAI_API_KEY
    if not TELEGRAM_FILE.exists():
        return
    try:
        cfg = json.loads(TELEGRAM_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError) as e:
        print(f"telegram.json не читається ({e}) — перевірте лапки й коми", flush=True)
        return
    TELEGRAM_BOT_TOKEN = TELEGRAM_BOT_TOKEN or str(cfg.get("token") or "").strip()
    TELEGRAM_CHAT_ID = TELEGRAM_CHAT_ID or str(cfg.get("chat_id") or "").strip()
    TELEGRAM_CHANNEL_ID = TELEGRAM_CHANNEL_ID or str(cfg.get("channel_id") or "").strip()
    OPENAI_API_KEY = OPENAI_API_KEY or str(cfg.get("openai_key") or "").strip()


load_telegram_file()


def normalize_channel(value):
    """«https://t.me/arendabatumi3», «t.me/arendabatumi3», «arendabatumi3» → «@arendabatumi3»; -100... лишається."""
    value = str(value or "").strip()
    match = re.fullmatch(r"(?:https?://)?(?:t\.me|telegram\.me)/([A-Za-z0-9_]{4,})/?", value)
    if match:
        return "@" + match.group(1)
    if re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{3,}", value):
        return "@" + value
    return value


TELEGRAM_CHANNEL_ID = normalize_channel(TELEGRAM_CHANNEL_ID)


class FetchError(Exception):
    pass


class ConfigError(Exception):
    pass


def log(msg):
    print(f"[{datetime.now(GEORGIA_TZ):%Y-%m-%d %H:%M:%S}] {msg}", flush=True)


def today():
    return datetime.now(GEORGIA_TZ).strftime("%Y-%m-%d")


def clean(value):
    return re.sub(r"\s+", " ", str(value if value is not None else "")).strip()


def plain_text(value):
    """Опис з сайту буває з HTML: <br />, &quot; тощо — робимо звичайний текст."""
    text = re.sub(r"(?i)<br\s*/?>", " ", str(value or ""))
    text = re.sub(r"<[^>]+>", " ", text)
    return clean(html.unescape(text))


def as_dict(value):
    return value if isinstance(value, dict) else {}


# ─────────────────────────────── myhome.ge ───────────────────────────────

def http_get_json(url, headers):
    try:
        if cffi_requests:
            resp = cffi_requests.get(url, headers=headers, impersonate="chrome", timeout=30)
            status, body = resp.status_code, resp.text
        else:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, **headers})
            try:
                with urllib.request.urlopen(req, timeout=30, context=ssl_context()) as resp:
                    status, body = resp.status, resp.read().decode("utf-8", "replace")
            except urllib.error.HTTPError as e:
                status, body = e.code, e.read().decode("utf-8", "replace")
    except Exception as e:
        raise FetchError(f"мережева помилка: {e}") from e
    if status != 200:
        hint = " — схоже на захист від ботів" if status in (403, 429, 503) else ""
        raise FetchError(f"HTTP {status}{hint}")
    try:
        return json.loads(body)
    except ValueError:
        raise FetchError("відповідь не JSON — можливо, сторінка перевірки від Cloudflare")


def api_headers():
    return {
        "Accept": "application/json, text/plain, */*",
        "x-website-key": "myhome",
        "locale": LANG,
        "Origin": SITE,
        "Referer": SITE + "/",
    }


def load_searches():
    if not SEARCHES_FILE.exists():
        raise ConfigError(f"немає файлу {SEARCHES_FILE.name} — створіть його поруч зі скриптом")
    searches = []
    for line in SEARCHES_FILE.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        label, url = ("", line)
        if "|" in line:
            label, url = (part.strip() for part in line.split("|", 1))
        if "myhome.ge" not in url:
            continue  # рядок-заглушка або щось стороннє
        searches.append((label or "myhome.ge", url))
    if not searches:
        raise ConfigError(f"у {SEARCHES_FILE.name} немає жодного посилання на myhome.ge — "
                          "вставте туди адресу сторінки пошуку (інструкція всередині файлу)")
    return searches


def search_params(search_url):
    """Перетворює адресу сторінки пошуку myhome.ge на параметри API."""
    query = urllib.parse.urlsplit(search_url.strip()).query
    skip = {"page", "cardview", "locale"} | ({"owner_type"} if ONLY_OWNERS else set())
    params = [(k, v) for k, v in urllib.parse.parse_qsl(query, keep_blank_values=True)
              if k.lower() not in skip]
    if not {k.lower() for k, _ in params} & {"cities", "urbans", "districts"}:
        raise ConfigError(
            "у посиланні немає фільтра міста (cities=...). Оберіть на сайті Батумі, застосуйте "
            "фільтри й скопіюйте адресу ще раз — у ній має бути «?deal_types=...&cities=...»")
    if ONLY_OWNERS:
        params.append(("owner_type", "physical"))
    return params


def list_url(params, page):
    query = urllib.parse.urlencode(params + [("page", str(page)), ("locale", LANG)], safe=",")
    return f"{API_URL}?{query}"


def detail_url(listing_id):
    return f"{API_URL}/{listing_id}?locale={LANG}"


def fetch_page(params, page):
    data = http_get_json(list_url(params, page), api_headers())
    if not isinstance(data, dict) or data.get("result") is False:
        raise FetchError(f"API повернуло помилку: {str(data)[:200]}")
    items = as_dict(data.get("data")).get("data")
    if not isinstance(items, list):
        raise FetchError("неочікуваний формат відповіді — можливо, сайт змінив API")
    return [it for it in items if isinstance(it, dict) and str(it.get("id", "")).isdigit()]


DETAIL_FIELDS = ("user_id", "user_phone_number", "additional_phone_number", "user_title",
                 "floor", "total_floors", "created_at", "create_date", "last_updated", "address")


def to_int(value):
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, str) and value.strip().isdigit():
        return int(value.strip())
    return None


def _walk(obj, path=""):
    if isinstance(obj, dict):
        for key, value in obj.items():
            sub = f"{path}.{key}" if path else str(key)
            if isinstance(value, (dict, list)):
                yield from _walk(value, sub)
            else:
                yield sub, str(key), value
    elif isinstance(obj, list):
        for i, value in enumerate(obj[:20]):
            yield from _walk(value, f"{path}[{i}]")


KNOWN_COUNT_KEYS = ("user_statements_count", "user_statement_count", "statements_count",
                    "user_active_statements_count", "active_statements_count",
                    "userApplicationCount", "user_applications_count")
COUNT_KEY_RE = re.compile(r"(statements?|applications?|listings?|announcements?)_?count$|(^|_)ads?_?count$",
                          re.IGNORECASE)
NOT_AUTHOR_PATH_RE = re.compile(r"similar|related|recommend|view|favou?rite|photo|image|comment|like",
                                re.IGNORECASE)


def find_author_listing_count(data):
    """Шукає в даних оголошення лічильник оголошень автора на сайті.
    Повертає (число, назва поля) або (None, None)."""
    data = as_dict(data)
    for scope, prefix in ((data, ""), (as_dict(data.get("user")), "user."), (as_dict(data.get("owner")), "owner.")):
        for key in KNOWN_COUNT_KEYS:
            number = to_int(scope.get(key))
            if number is not None and 0 < number < 100000:
                return number, prefix + key
    for path, key, value in _walk(data):
        number = to_int(value)
        if (number is not None and 0 < number < 100000
                and COUNT_KEY_RE.search(key) and not NOT_AUTHOR_PATH_RE.search(path)):
            return number, path
    return None, None


def apply_author_listing_count(item, data):
    number, field = find_author_listing_count(data)
    if number is not None:
        item["_site_count"], item["_site_count_field"] = number, field


def enrich_with_details(item):
    """Догружає картку оголошення: телефон, id автора, повніший опис і кількість оголошень автора."""
    apply_author_listing_count(item, item)  # раптом лічильник є вже у видачі
    try:
        data = http_get_json(detail_url(item["id"]), api_headers())
    except FetchError as e:
        log(f"  картка {item['id']}: {e}")
        return item
    detail = as_dict(as_dict(as_dict(data).get("data")).get("statement"))
    if "_site_count" not in item:
        apply_author_listing_count(item, detail)
    for key in DETAIL_FIELDS:
        if clean(item.get(key)) == "" and clean(detail.get(key)) != "":
            item[key] = detail[key]
    if len(clean(detail.get("comment"))) > len(clean(item.get("comment"))):
        item["comment"] = detail["comment"]
    if len(image_urls(detail)) > len(image_urls(item)):
        item["images"] = detail["images"]
    return item


def fetch_listing(listing_id):
    """Повна картка оголошення за id (для публікації в канал)."""
    data = http_get_json(detail_url(listing_id), api_headers())
    detail = as_dict(as_dict(as_dict(data).get("data")).get("statement"))
    if not detail:
        raise FetchError(f"оголошення {listing_id} не знайдено — можливо, його вже зняли")
    detail.setdefault("id", listing_id)
    return detail


# ─────────────────────────── аналіз оголошення ───────────────────────────

PHONE_RE = re.compile(r"(?<![\d+])(?:\+?995[\s\-.]?)?(5\d{2}(?:[\s\-.]?\d){6})(?!\d)")
PHONE_WITH_LABEL_RE = re.compile(  # «Тел.: 599 12 34 56», «звоните 599123456» — прибирається цілком
    r"(?i)(?:\b(?:тел(?:ефон)?|моб(?:ильный)?|звоните|пишите|whats\s?app|viber|telegram|phone|tel|"
    r"вотсап|ватсап|вайбер|ტელ(?:ეფონი)?)\b\.?[\s:.\-–—]*(?:по\s+)?)?" + PHONE_RE.pattern)


def find_phone(*texts):
    for text in texts:
        match = PHONE_RE.search(str(text or ""))
        if match:
            d = re.sub(r"\D", "", match.group(1))
            return f"+995 {d[:3]} {d[3:5]} {d[5:7]} {d[7:]}"
    return ""


AGENT_WORD = re.compile(
    r"агентств\w*|агенц\w*|агент\w*|риелтор\w*|риэлтор\w*|рієлтор\w*|маклер\w*|брокер\w*|"
    r"посредни\w*|посередни\w*|комисси\w*|коміс\w*|"
    r"agenc\w*|agent\w*|realtor\w*|broker\w*|commission\w*|"
    r"სააგენტო\w*|აგენტ\w*|რიელტორ\w*|მაკლერ\w*|ბროკერ\w*|საკომისიო\w*|შუამავ\w*",
    re.IGNORECASE)
NEGATION_BEFORE = re.compile(r"\b(без|не|no|non|without)\W*$", re.IGNORECASE)
NEGATION_AFTER = re.compile(
    r"^\W*(?:\w+\W+){0,4}?(?:просьба\W+|прошу\W+|пожалуйста\W+|please\W+|გთხოვთ\W+)?"
    r"(?:не\W+(?:звон|беспок|пис|обращ|турб|дзвон|пиш)"
    r"|(?:do\W+not|don'?t|not)\W+(?:call|contact|disturb|bother|text|write)"
    r"|(?:არ|ნუ)\W|გარეშე)",
    re.IGNORECASE)


def text_signals(text):
    """(є ознаки агенції в тексті, автор пише «без посередників»)."""
    text = str(text or "")
    agent = owner = False
    for m in AGENT_WORD.finditer(text):
        before = text[max(0, m.start() - 9):m.start()]
        after = text[m.end():m.end() + 60]
        if NEGATION_BEFORE.search(before) or NEGATION_AFTER.search(after):
            owner = True   # «агентствам не звонить», «без комиссии», «no agents»...
        else:
            agent = True   # «комиссия агентства 50%», «real estate agency»...
    return agent, owner


def phone_fingerprint(digits):
    """Відбиток телефону замість самого номера.

    У state.json (він лежить у публічному репозиторії) не має бути чужих
    телефонів. Відбиток рахується з токеном бота як секретним ключем, тож
    підібрати номер перебором ззовні не вийде, а бот далі бачить, що два
    оголошення — від одного телефону.
    """
    key = (TELEGRAM_BOT_TOKEN or "myhome-watcher").encode("utf-8")
    return hmac.new(key, digits.encode("utf-8"), hashlib.sha256).hexdigest()[:16]


def author_keys(item):
    """Ключі автора: id на myhome.ge та/або відбиток номера телефону."""
    keys = []
    uid = item.get("user_id") or item.get("userId") or as_dict(item.get("user")).get("id")
    if uid:
        keys.append(f"u:{uid}")
    phone = find_phone(item.get("user_phone_number"), item.get("additional_phone_number"),
                       item.get("comment"))
    if phone:
        keys.append("p:" + phone_fingerprint(re.sub(r"\D", "", phone)[-9:]))
    return keys


def author_count(state, item):
    """Скільки оголошень цього автора буде в базі разом із поточним (0 — автор невідомий)."""
    keys = author_keys(item)
    if not keys:
        return 0
    return max(state["authors"].get(k, [0])[0] for k in keys) + 1


def register_author(state, item, day):
    for k in author_keys(item):
        count = state["authors"].get(k, [0])[0]
        state["authors"][k] = [count + 1, day]


# ─────────────────────────────── повідомлення ───────────────────────────────

def fmt_num(value):
    try:
        return f"{float(value):,.0f}".replace(",", " ")
    except (TypeError, ValueError):
        return clean(value)


def fmt_area(value):
    try:
        return f"{float(value):.1f}".rstrip("0").rstrip(".")
    except (TypeError, ValueError):
        return clean(value)


def price_text(item):
    price = as_dict(item.get("price"))
    gel = as_dict(price.get("1")).get("price_total")
    usd = as_dict(price.get("2")).get("price_total")
    parts = []
    if gel:
        parts.append(f"{fmt_num(gel)} ₾")
    if usd:
        parts.append(f"${fmt_num(usd)}")
    return " · ".join(parts)


def _parse_time(raw):
    raw = clean(raw)
    if not raw:
        return None
    try:
        dt = datetime.fromisoformat(raw.replace("Z", "+00:00").replace(" ", "T", 1))
    except ValueError:
        return None
    return dt.astimezone(GEORGIA_TZ) if dt.tzinfo else dt


def facts_text(item):
    """«45 м² · кімнат: 2 · спалень: 1 · поверх 5/12»."""
    facts = []
    if clean(item.get("area")):
        facts.append(f"{fmt_area(item['area'])} м²")
    if clean(item.get("room")):
        facts.append(f"кімнат: {clean(item['room'])}")
    if clean(item.get("bedroom")):
        facts.append(f"спалень: {clean(item['bedroom'])}")
    if clean(item.get("floor")):
        total = clean(item.get("total_floors"))
        facts.append(f"поверх {clean(item['floor'])}" + (f"/{total}" if total else ""))
    return " · ".join(facts)


def listing_time(item):
    """«25.09 02:01», а якщо оголошення потім піднімали — «25.09 02:01, оновлено 27.09 14:03»."""
    created = _parse_time(item.get("created_at") or item.get("create_date"))
    updated = _parse_time(item.get("last_updated"))
    if created and updated and updated.date() != created.date():
        return f"{created:%d.%m %H:%M}, оновлено {updated:%d.%m %H:%M}"
    moment = created or updated
    return moment.strftime("%d.%m %H:%M") if moment else ""


def listing_url(item):
    slug = clean(item.get("dynamic_slug"))
    if slug:
        return SITE + LISTING_PATHS.get(LANG, LISTING_PATHS["ru"]).format(slug=slug, id=item["id"])
    return f"{SITE}/{LANG}/pr/{item['id']}/"


def image_urls(item):
    """Адреси всіх фото оголошення, головне — першим."""
    images = item.get("images") if isinstance(item.get("images"), list) else []
    images = sorted(images, key=lambda im: not (isinstance(im, dict) and im.get("is_main")))
    urls = []
    for im in images:
        url = im if isinstance(im, str) else (im.get("large") or im.get("thumb")) if isinstance(im, dict) else ""
        if isinstance(url, str) and url.startswith("http") and url not in urls:
            urls.append(url)
    return urls


def main_image(item):
    urls = image_urls(item)
    return urls[0] if urls else ""


def plural(n, one, few, many):
    n = abs(n) % 100
    if 11 <= n <= 14:
        return many
    n %= 10
    return one if n == 1 else few if 2 <= n <= 4 else many


def visible_len(text):
    return len(html.unescape(re.sub(r"<[^>]+>", "", text)))


def build_message(item, label, count, max_len=4096):
    def esc(value):
        return html.escape(clean(value), quote=False)

    lines = [f"🏠 <b>{esc(item.get('dynamic_title')) or 'Нове оголошення'}</b>"]
    if price_text(item):
        lines.append(f"💵 {esc(price_text(item))}")

    facts = esc(facts_text(item))
    if facts:
        lines.append("📐 " + facts)

    place = ", ".join(p for p in (clean(item.get("urban_name")),
                                  item.get("_ru_address") or clean(item.get("address"))) if p)
    if place:
        lines.append(f"📍 {esc(place)}")

    who = [esc(item.get("user_title"))] if clean(item.get("user_title")) else []
    phone = find_phone(item.get("user_phone_number"), item.get("additional_phone_number"),
                       item.get("comment"))
    masked = clean(item.get("user_phone_number"))
    if phone:
        who.append(f"📞 {phone}")
    elif "*" in masked:
        who.append(f"📞 {esc(masked)} (повністю — на сайті)")
    if who:
        lines.append("👤 " + " · ".join(who))

    when = listing_time(item)
    lines.append(" · ".join(x for x in (f"🕒 {when}" if when else "", f"🔎 {esc(label)}") if x))

    agent_text, owner_text = text_signals(plain_text(item.get("comment")))
    site = item.get("_site_count")
    if isinstance(site, int):
        words = plural(site, "оголошення", "оголошення", "оголошень")
        if site >= AGENT_THRESHOLD:
            lines.append(f"⚠️ У автора {site} {words} на myhome.ge — агент або інвестор")
        else:
            lines.append(f"✅ У автора {site} {words} на myhome.ge")
    if count >= AGENT_THRESHOLD and (not isinstance(site, int) or count > site):
        words = plural(count, "оголошенні", "оголошеннях", "оголошеннях")
        lines.append(f"⚠️ Цей автор або телефон уже трапився в {count} {words} — агент або інвестор")
    if agent_text:
        lines.append("⚠️ В описі згадується агенція або комісія")
    elif owner_text:
        lines.append("✍️ Пише, що без посередників")

    link = f'🔗 <a href="{html.escape(listing_url(item))}">Відкрити на myhome.ge</a>'
    message = "\n".join(lines)
    desc = item.get("_ru_comment") or plain_text(item.get("comment"))
    budget = min(400, max_len - visible_len(message) - visible_len(link) - 10)
    if desc and budget > 40:
        snippet = desc if len(desc) <= budget else desc[:budget - 1].rstrip() + "…"
        message += f"\n\n<i>{esc(snippet)}</i>"
    return message + "\n\n" + link


def print_listing(item, label, count):
    plain = html.unescape(re.sub(r"<[^>]+>", "", build_message(item, label, count)))
    print("-" * 60)
    print(plain.replace("Відкрити на myhome.ge", listing_url(item)), flush=True)


# ─────────────────────────────── Telegram ───────────────────────────────

def chat_ids():
    return [c.strip() for c in str(TELEGRAM_CHAT_ID).split(",") if c.strip()]


def telegram_ready():
    return bool(TELEGRAM_BOT_TOKEN and chat_ids())


def _post_json(url, payload, headers=None, timeout=30):
    """POST з JSON → (код, текст відповіді). Спершу через curl_cffi, інакше — urllib."""
    if cffi_requests:
        resp = cffi_requests.post(url, json=payload, headers=headers, timeout=timeout)
        return resp.status_code, resp.text
    req = urllib.request.Request(url, data=json.dumps(payload).encode("utf-8"),
                                 headers={"Content-Type": "application/json", **(headers or {})})
    try:
        with urllib.request.urlopen(req, timeout=timeout, context=ssl_context()) as resp:
            return resp.status, resp.read().decode("utf-8", "replace")
    except urllib.error.HTTPError as e:
        return e.code, e.read().decode("utf-8", "replace")


def tg_call(method, payload):
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/{method}"
    for attempt in range(3):
        try:
            status, body = _post_json(url, payload)
        except Exception as e:
            if attempt < 2:
                time.sleep(3)
                continue
            return {"ok": False, "description": str(e)}
        try:
            result = json.loads(body)
        except ValueError:
            result = {"ok": False, "description": f"HTTP {status}"}
        wait = as_dict(result.get("parameters")).get("retry_after")
        if status == 429 and wait and attempt < 2:
            time.sleep(int(wait) + 1)
            continue
        return result
    return {"ok": False, "description": "забагато спроб"}


def send_text(text):
    for chat in chat_ids():
        result = tg_call("sendMessage", {"chat_id": chat, "text": text, "parse_mode": "HTML",
                                         "link_preview_options": {"is_disabled": True}})
        if not result.get("ok"):
            log(f"Telegram ({chat}): {result.get('description')}")


def channel_button(listing_id):
    """Кнопка під оголошенням у робочому чаті (лише якщо канал налаштований)."""
    if not TELEGRAM_CHANNEL_ID:
        return {}
    return {"reply_markup": {"inline_keyboard": [[
        {"text": "📢 Додати в канал", "callback_data": f"ch:{listing_id}"}]]}}


def send_listing(item, label, count):
    """Надсилає оголошення у всі чати. True, якщо дійшло хоча б в один."""
    photo = main_image(item)
    caption = build_message(item, label, count, max_len=1024)
    full_text = build_message(item, label, count)
    button = channel_button(item["id"])
    delivered = False
    for chat in chat_ids():
        result = {"ok": False}
        if photo:
            result = tg_call("sendPhoto", {"chat_id": chat, "photo": photo, "caption": caption,
                                           "parse_mode": "HTML", **button})
        if not result.get("ok"):  # фото не підійшло — шлемо текстом
            result = tg_call("sendMessage", {"chat_id": chat, "text": full_text,
                                             "parse_mode": "HTML", **button})
        if result.get("ok"):
            delivered = True
        else:
            log(f"Telegram ({chat}): {result.get('description')}")
        time.sleep(1.1)
    return delivered


# ─────────────────────────────── канал ───────────────────────────────

DEFAULT_CHANNEL_TEMPLATE = """{deal_tag} {bedrooms_tag} {plan_tag} {district_tag} {city_tag}
🏠 <b>{rooms_title}</b>
💰 {price}
📍 {place}
📐 {facts}

{description}"""
DEAL_NAMES = {1: "Продаж", 2: "Оренда"}
PLACEHOLDER_RE = re.compile(r"\{(\w+)\}")


def description_text(item):
    """Опис для каналу: одним абзацом, без HTML і (за бажанням) без телефонів власника."""
    text = re.sub(r"(?i)<br\s*/?>|</?(?:p|div|li)\b[^>]*>", "\n", str(item.get("comment") or ""))
    text = html.unescape(re.sub(r"<[^>]+>", "", text))
    lines = []
    for line in text.splitlines():
        if CHANNEL_HIDE_PHONES and PHONE_RE.search(line):
            line = re.sub(r"\s+([.,;!?])", r"\1", PHONE_WITH_LABEL_RE.sub("", line))
            if len(re.sub(r"\W", "", line)) < 20:  # лишилось щось на кшталт «Тел.:» — рядок геть
                continue
        line = re.sub(r"[ \t]+", " ", line).strip()
        if line:  # в один абзац: рядок без розділового знака в кінці закриваємо крапкою
            lines.append(line if line[-1] in ".!?:;,…" else line + ".")
    return " ".join(lines)


def hashtag(value, prefix="", camel=False):
    """«Старый Батуми» → #старыйбатуми, з camel=True і prefix="сдамквартиру" → #сдамквартируСтарыйБатуми."""
    words = re.findall(r"[^\W_]+", clean(value))
    if not words:
        return ""
    tag = "".join(w[:1].upper() + w[1:] for w in words) if camel else "".join(words).lower()
    return f"#{prefix}{tag}"


def layout(item):
    """Планування в місцевому форматі: (кімнат, спалень, «1+1» або «студия»)."""
    rooms, beds = to_int(clean(item.get("room"))), to_int(clean(item.get("bedroom")))
    if rooms == 1 or beds == 0:
        return rooms, beds, "студия"
    if beds is None and rooms:
        beds = rooms - 1
    return rooms, beds, f"{beds}+1" if beds else ""


def plan_values(item):
    rooms, beds, plan = layout(item)
    if plan == "студия":
        return {"rooms_title": "квартира-студия", "plan": "студия (кухня-гостиная и спальная зона)",
                "plan_tag": "#студия", "bedrooms_tag": ""}
    if not plan:
        return {"rooms_title": f"{rooms}-комнатная квартира" if rooms else "квартира",
                "plan": "", "plan_tag": "", "bedrooms_tag": ""}
    bed_words = "отдельная спальня" if beds == 1 else f"{beds} {plural(beds, 'спальня', 'спальни', 'спален')}"
    return {"rooms_title": f"{rooms or beds + 1}-комнатная квартира ({plan})",
            "plan": f"{plan} ({bed_words} + кухня-гостиная)",
            "plan_tag": f"#{beds}плюс1",
            "bedrooms_tag": f"#{beds}{plural(beds, 'спальня', 'спальни', 'спален')}"}


def channel_values(item):
    """Значення для {назв} у channel_template.txt."""
    price = as_dict(item.get("price"))
    gel = as_dict(price.get("1")).get("price_total")
    usd = as_dict(price.get("2")).get("price_total")
    deal = DEAL_NAMES.get(to_int(item.get("deal_type_id")) or to_int(item.get("deal_type")), "")
    floor, floors = clean(item.get("floor")), clean(item.get("total_floors"))
    desc = description_text(item)
    if CHANNEL_DESCRIPTION_MAX and len(desc) > CHANNEL_DESCRIPTION_MAX:
        cut = desc[:CHANNEL_DESCRIPTION_MAX - 1]
        cut = cut[:cut.rfind(" ")] if " " in cut[CHANNEL_DESCRIPTION_MAX // 2:] else cut
        desc = cut.rstrip(" ,.;:\n") + "…"
    plan = plan_values(item)
    ai = as_dict(item.get("_ai"))
    district = clean(item.get("urban_name"))
    headline = ai.get("headline") or " ".join(
        x for x in ("Уютная", plan["rooms_title"] + ("," if district else ""), district) if x)
    points = [f"✔️ {p}" for p in ai.get("points") or []] or ([f"✔️ {desc}"] if desc else [])
    address = ai.get("address") or clean(item.get("address"))
    place = ", ".join(p for p in (district, address) if p)
    return {
        **plan,
        "headline": headline,
        "points": "\n".join(points),
        "terms": ai.get("terms") or "",
        "id": clean(item.get("id")),
        "title": clean(item.get("dynamic_title")),
        "price": price_text(item),
        "price_usd": f"{fmt_num(usd)}$" if usd else "",
        "price_gel": f"{fmt_num(gel)} ₾" if gel else "",
        "price_main": f"{fmt_num(usd)}$" if usd else f"{fmt_num(gel)} ₾" if gel else "",
        "facts": facts_text(item),
        "area": fmt_area(item["area"]) if clean(item.get("area")) else "",
        "rooms": clean(item.get("room")),
        "bedrooms": clean(item.get("bedroom")),
        "floor": floor,
        "floors": floors,
        "floor_full": f"{floor}/{floors}" if floor and floors else floor,
        "place": place,
        "city": clean(item.get("city_name")),
        "district": clean(item.get("urban_name")),
        "address": address,
        "deal": deal,
        "deal_tag": hashtag(deal),
        "district_tag": hashtag(item.get("urban_name")),
        "district_rent_tag": hashtag(item.get("urban_name"), "сдамквартиру", camel=True),
        "city_tag": hashtag(item.get("city_name")),
        "owner_phone": find_phone(item.get("user_phone_number"), item.get("additional_phone_number"),
                                  item.get("comment")),
        "link": listing_url(item),
        "description": desc,
    }


AI_PROMPT = """Ты помогаешь вести Telegram-канал «Аренда Батуми» с объявлениями об аренде квартир.
По данным объявления с myhome.ge подготовь части поста на русском языке.

Верни JSON:
{"headline": "...", "points": ["...", "..."], "terms": "...", "address": "..."}

headline — одна строка вида «Уютная 2-комнатная квартира (1+1) в Квариати»: прилагательное
(уютная, светлая, просторная, современная — по описанию), тип квартиры и район с правильным
падежом («в Старом Батуми», «на Новом бульваре», «в районе Аэропорта»). Без эмодзи.

points — 2–4 коротких пункта «Название: значение», только то, что реально есть в описании:
Срок, Состояние, Мебель и техника, Дом, Вид, Парковка, Животные, Особенности и т.п.
Не повторяй планировку, площадь, этаж, цену и адрес — они уже есть в посте.
Пример: «Срок: Аренда на 9 месяцев (до летнего сезона)», «Состояние: Новый ремонт, всё необходимое для проживания».

terms — условия оплаты и договора в скобках, если они есть в описании, например
«(договор, оплата за первый и последний месяцы)». Если не указаны — пустая строка.

address — адрес по-русски: грузинский переведи («რუსთაველის ქ. 15» → «ул. Руставели 15»),
русский оставь как есть; если адреса нет — пустая строка.

Правила: ничего не выдумывай — если чего-то нет в данных, не пиши об этом. Не упоминай
собственника, агентства, комиссию, телефоны, имена и ссылки. Если описание на грузинском
или английском — переведи. Весь ответ вместе — не длиннее 400 символов."""


def ai_parts(item):
    """Просить OpenAI дописати заголовок, пункти й умови. Повертає dict або кидає FetchError."""
    facts = {
        "тип": plan_values(item)["rooms_title"], "планировка": plan_values(item)["plan"],
        "площадь_м2": fmt_area(item["area"]) if clean(item.get("area")) else "",
        "этаж": clean(item.get("floor")), "этажей_в_доме": clean(item.get("total_floors")),
        "город": clean(item.get("city_name")), "район": clean(item.get("urban_name")),
        "адрес": clean(item.get("address")), "заголовок_на_сайте": clean(item.get("dynamic_title")),
        "цена": price_text(item), "описание": description_text(item),
    }
    parts = openai_json(AI_PROMPT, facts)
    points = parts.get("points") if isinstance(parts.get("points"), list) else []
    points = [clean(p).lstrip("✔️-•· ").strip() for p in points if clean(p)]
    while len("".join(points)) > 450:  # щоб пост влазив у підпис до фото
        points.pop()
    terms = clean(parts.get("terms"))
    if terms and not terms.startswith("("):
        terms = f"({terms.strip('()')})"
    return {"headline": clean(parts.get("headline")).rstrip("."), "points": points, "terms": terms,
            "address": clean(parts.get("address"))}


def openai_json(system, data):
    """Запит до OpenAI з відповіддю-JSON. Повертає dict або кидає FetchError."""
    payload = {"model": OPENAI_MODEL, "response_format": {"type": "json_object"},
               "max_completion_tokens": 4000,
               "messages": [{"role": "system", "content": system},
                            {"role": "user", "content": json.dumps(data, ensure_ascii=False)}]}
    try:
        status, body = _post_json("https://api.openai.com/v1/chat/completions", payload,
                                  {"Authorization": f"Bearer {OPENAI_API_KEY}"}, timeout=120)
    except Exception as e:
        raise FetchError(f"мережева помилка: {e}") from e
    try:
        data = json.loads(body)
    except ValueError:
        raise FetchError(f"HTTP {status}")
    if status != 200:
        raise FetchError(clean(as_dict(data.get("error")).get("message")) or f"HTTP {status}")
    try:
        parts = json.loads(data["choices"][0]["message"]["content"])
    except (KeyError, IndexError, TypeError, ValueError):
        raise FetchError("відповідь не в очікуваному форматі")
    if not isinstance(parts, dict):
        raise FetchError("відповідь не в очікуваному форматі")
    return parts


TRANSLATE_PROMPT = """Переведи на русский язык описание и адрес объявления об аренде квартиры в Батуми.
Верни JSON: {"description": "...", "address": "..."}.
Переводи точно, ничего не добавляй и не сокращай, эмодзи оставь. Названия улиц передавай
по-русски: «რუსთაველის ქ. 15» → «ул. Руставели 15», «ჭავჭავაძის ქ.» → «ул. Чавчавадзе».
Если поле пустое или уже на русском — верни его как есть."""


def needs_translation(text):
    """Грузинські літери або латиниці більше, ніж кирилиці."""
    text = str(text or "")
    if re.search(r"[\u10A0-\u10FF]", text):
        return True
    latin = len(re.findall(r"[A-Za-z]", text))
    return latin > 20 and latin > len(re.findall(r"[А-Яа-яЁёІіЇїЄє]", text))


def translate_listing(item):
    """Перекладає опис і адресу для повідомлення в чаті (item["_ru_comment"], item["_ru_address"])."""
    desc, address = plain_text(item.get("comment"))[:1500], clean(item.get("address"))
    if not (needs_translation(desc) or needs_translation(address)):
        return False
    try:
        parts = openai_json(TRANSLATE_PROMPT, {"description": desc, "address": address})
    except FetchError as e:
        log(f"  переклад {item['id']}: {e}")
        return True
    if clean(parts.get("description")):
        item["_ru_comment"] = clean(parts["description"])
    if clean(parts.get("address")):
        item["_ru_address"] = clean(parts["address"])
    return True


def add_ai_parts(item):
    """Один раз на оголошення дописує item["_ai"]; помилку кладе в item["_ai_error"]."""
    if not OPENAI_API_KEY or "_ai" in item or "_ai_error" in item:
        return
    try:
        item["_ai"] = ai_parts(item)
    except FetchError as e:
        item["_ai_error"] = str(e)
        log(f"OpenAI, оголошення {item.get('id')}: {e}")


def load_channel_template():
    if CHANNEL_TEMPLATE_FILE.exists():
        text = CHANNEL_TEMPLATE_FILE.read_text(encoding="utf-8").strip()
        if text:
            return text
    return DEFAULT_CHANNEL_TEMPLATE


def render_template(template, values):
    """Підставляє значення. Рядок, де всі {назви} порожні, викидається цілком."""
    out = []
    for line in template.splitlines():
        names = PLACEHOLDER_RE.findall(line)
        known = [n for n in names if n in values]
        if known and not any(values[n] for n in known):
            continue
        line = PLACEHOLDER_RE.sub(
            lambda m: html.escape(values[m.group(1)], quote=False) if m.group(1) in values else m.group(0),
            line)
        out.append(re.sub(r"(?<=\S) {2,}", " ", line).rstrip() if known else line)
    text = re.sub(r"<(b|i|u|s)>\s*</\1>", "", "\n".join(out))  # порожні <i></i> від порожніх {назв}
    text = re.sub(r"[ \t]+\n", "\n", text)
    return re.sub(r"\n{3,}", "\n\n", text).strip()


def build_channel_post(item, max_len=1024):
    """Текст поста для каналу; опис скорочується, щоб усе влізло в підпис до фото."""
    template, values = load_channel_template(), channel_values(item)
    desc = values["description"]
    text = render_template(template, values)
    if visible_len(text) <= max_len:
        return text
    budget = max_len - visible_len(render_template(template, {**values, "description": ""})) - 3
    if budget < 40:
        values["description"] = ""
    else:
        cut = desc[:budget - 1]
        cut = cut[:cut.rfind(" ")] if " " in cut[budget // 2:] else cut
        values["description"] = cut.rstrip(" ,.;:\n") + "…"
    text = render_template(template, values)
    return text if visible_len(text) <= max_len else text[:max_len]  # запобіжник


def message_link(message):
    chat = as_dict(message.get("chat"))
    if chat.get("username"):
        return f"https://t.me/{chat['username']}/{message.get('message_id')}"
    cid = str(chat.get("id", ""))
    if cid.startswith("-100"):
        return f"https://t.me/c/{cid[4:]}/{message.get('message_id')}"
    return ""


def publish_post(chat_id, item, fallback_photo=""):
    """Шле альбом із підписом (або одне фото, або текст). Повертає (перше повідомлення, помилка)."""
    add_ai_parts(item)
    caption = build_channel_post(item, 1024)
    photos = image_urls(item)[:CHANNEL_MAX_PHOTOS] or ([fallback_photo] if fallback_photo else [])
    errors = []
    if len(photos) > 1:
        media = [{"type": "photo", "media": url} for url in photos]
        media[0].update(caption=caption, parse_mode="HTML")
        result = tg_call("sendMediaGroup", {"chat_id": chat_id, "media": media})
        if result.get("ok") and result.get("result"):
            return result["result"][0], ""
        errors.append(result.get("description"))
    for photo in [p for p in (photos[:1] + [fallback_photo]) if p][:2]:
        result = tg_call("sendPhoto", {"chat_id": chat_id, "photo": photo,
                                       "caption": caption, "parse_mode": "HTML"})
        if result.get("ok"):
            return result["result"], ""
        errors.append(result.get("description"))
    result = tg_call("sendMessage", {"chat_id": chat_id, "text": build_channel_post(item, 4096),
                                     "parse_mode": "HTML", "link_preview_options": {"is_disabled": True}})
    if result.get("ok"):
        return result["result"], ""
    errors.append(result.get("description"))
    return None, "; ".join(str(e) for e in errors if e)


def largest_photo(message):
    sizes = [p for p in (message.get("photo") or []) if isinstance(p, dict)]
    return max(sizes, key=lambda p: p.get("width", 0) * p.get("height", 0))["file_id"] if sizes else ""


def post_to_channel(state, listing_id, fallback_photo=""):
    """Публікує оголошення в канал. Повертає (посилання на пост або "", помилка або "", помилка ШІ або "")."""
    key = str(listing_id)
    if key in state["posted"]:
        return state["posted"][key][0], "", ""
    try:
        item = fetch_listing(listing_id)
    except FetchError as e:
        return "", f"myhome.ge: {e}", ""
    message, error = publish_post(TELEGRAM_CHANNEL_ID, item, fallback_photo)
    if not message:
        return "", f"Telegram: {error}", ""
    link = message_link(message)
    state["posted"][key] = [link, today()]
    log(f"оголошення {listing_id} опубліковано в канал {link}")
    return link, "", item.get("_ai_error", "")


def handle_callback(state, query):
    chat_msg = as_dict(query.get("message"))
    chat_id = str(as_dict(chat_msg.get("chat")).get("id", ""))
    data = str(query.get("data") or "")
    if chat_id not in chat_ids() or not re.fullmatch(r"ch:\d+", data):
        tg_call("answerCallbackQuery", {"callback_query_id": query.get("id")})
        return
    listing_id = int(data[3:])
    if not TELEGRAM_CHANNEL_ID:
        link, error, ai_error = "", "канал не налаштований (TELEGRAM_CHANNEL_ID)", ""
    else:
        link, error, ai_error = post_to_channel(state, listing_id, largest_photo(chat_msg))
    tg_call("answerCallbackQuery", {"callback_query_id": query.get("id"),
                                    "text": "❌ Не вдалося, деталі в чаті" if error else "✅ Опубліковано в каналі"})
    if error:
        log(f"канал, оголошення {listing_id}: {error}")
        tg_call("sendMessage", {"chat_id": chat_id,
                                "text": f"❌ Не вдалося опублікувати в канал: {html.escape(error)}\n"
                                        "Натисніть кнопку ще раз, коли виправите.",
                                "parse_mode": "HTML",
                                "reply_parameters": {"message_id": chat_msg.get("message_id"),
                                                     "allow_sending_without_reply": True}})
        return
    if ai_error:
        tg_call("sendMessage", {"chat_id": chat_id,
                                "text": f"⚠️ OpenAI не відповів ({html.escape(ai_error)}), тому пост "
                                        "зібрано за звичайним шаблоном — за потреби підправте його в каналі.",
                                "parse_mode": "HTML",
                                "reply_parameters": {"message_id": chat_msg.get("message_id"),
                                                     "allow_sending_without_reply": True}})
    done = {"text": "✅ В каналі", "url": link} if link else {"text": "✅ В каналі", "callback_data": data}
    tg_call("editMessageReplyMarkup", {"chat_id": chat_id, "message_id": chat_msg.get("message_id"),
                                       "reply_markup": {"inline_keyboard": [[done]]}})


def process_updates(state, wait=0):
    """Обробляє натискання кнопок «Додати в канал». wait — скільки секунд чекати нових (long polling)."""
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHANNEL_ID:
        return
    payload = {"timeout": wait, "allowed_updates": ["callback_query"]}
    if state["tg_offset"]:
        payload["offset"] = state["tg_offset"]
    result = tg_call("getUpdates", payload)
    if not result.get("ok"):
        log(f"Telegram getUpdates: {result.get('description')}")
        return
    for update in result.get("result", []):
        state["tg_offset"] = int(update["update_id"]) + 1
        query = as_dict(update.get("callback_query"))
        if query:
            try:
                handle_callback(state, query)
            except Exception as e:  # одна невдала кнопка не має ламати перевірку оголошень
                log(f"кнопка: {e}")


# ─────────────────────────────── база (state.json) ───────────────────────────────

def new_state():
    return {"version": 1, "searches": {}, "seen": {}, "authors": {}, "fail_streak": 0,
            "tg_offset": 0, "posted": {}}


def load_state():
    if not STATE_FILE.exists():
        return new_state()
    try:
        state = json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except (ValueError, OSError) as e:
        log(f"state.json пошкоджений ({e}) — починаю з нуля")
        return new_state()
    for key, default in new_state().items():
        state.setdefault(key, default)
    return state


def save_state(state):
    cutoff = (datetime.now(GEORGIA_TZ) - timedelta(days=KEEP_DAYS)).strftime("%Y-%m-%d")
    state["seen"] = {day: sorted(set(ids)) for day, ids in state["seen"].items() if day >= cutoff}
    state["authors"] = {k: v for k, v in state["authors"].items() if v[1] >= cutoff}
    state["posted"] = {k: v for k, v in state["posted"].items() if v[1] >= cutoff}
    tmp = STATE_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(state, ensure_ascii=False, sort_keys=True, indent=0), encoding="utf-8")
    tmp.replace(STATE_FILE)


def seen_ids(state):
    return {int(i) for ids in state["seen"].values() for i in ids}


def mark_seen(state, listing_id, day):
    state["seen"].setdefault(day, []).append(int(listing_id))


def update_fail_streak(state, any_ok):
    if any_ok:
        if state["fail_streak"] >= FAIL_ALERT_AFTER and telegram_ready():
            send_text("✅ myhome.ge знову віддає дані, моніторинг працює.")
        state["fail_streak"] = 0
        return
    state["fail_streak"] += 1
    if state["fail_streak"] == FAIL_ALERT_AFTER and telegram_ready():
        send_text("⚠️ Кілька перевірок поспіль myhome.ge не віддає дані. Можливо, сайт змінив "
                  "API або блокує запити — варто глянути лог запусків.")


# ─────────────────────────────── основна логіка ───────────────────────────────

def run_once(state):
    searches = load_searches()
    day = today()
    seen = seen_ids(state)
    candidates, batch, any_ok = [], set(), False

    for label, url in searches:
        try:
            params = search_params(url)
        except ConfigError as e:
            log(f"[{label}] {e}")
            continue
        key = urllib.parse.urlencode(sorted(params), safe=",")
        seeding = key not in state["searches"]
        pages = SEED_PAGES if seeding else PAGES_PER_RUN

        found, ok = [], False
        for page in range(1, pages + 1):
            try:
                items = fetch_page(params, page)
            except FetchError as e:
                log(f"[{label}] сторінка {page}: {e}")
                break
            ok = True
            if not items:
                break
            found.extend(items)
            if page < pages:
                time.sleep(random.uniform(1.0, 2.0))
        if not ok:
            continue
        any_ok = True

        if seeding:  # перший запуск цього пошуку: запам'ятовуємо все, нічого не шлемо
            for item in found:
                listing_id = int(item["id"])
                if listing_id not in seen and listing_id not in batch:
                    seen.add(listing_id)
                    mark_seen(state, listing_id, day)
                    register_author(state, item, day)
            state["searches"][key] = day
            log(f"[{label}] перший запуск: запам'ятав {len(found)} оголошень, далі — лише нові")
            if telegram_ready():
                send_text(f"✅ Стежу за пошуком «{html.escape(label)}». Поточні {len(found)} "
                          "оголошень запам'ятав — надсилатиму тільки нові.")
            continue

        for item in found:
            listing_id = int(item["id"])
            if listing_id not in seen and listing_id not in batch:
                batch.add(listing_id)
                candidates.append((label, item))

    update_fail_streak(state, any_ok)
    if not candidates:
        log("нових оголошень немає" if any_ok else "не вдалося отримати дані з myhome.ge")
        return

    candidates.sort(key=lambda c: int(c[1]["id"]), reverse=True)  # новіші мають більший id
    if len(candidates) > MAX_ALERTS_PER_RUN:
        log(f"нових {len(candidates)}, надсилаю {MAX_ALERTS_PER_RUN}, решту — наступного разу")
        candidates = candidates[:MAX_ALERTS_PER_RUN]
    candidates.reverse()  # у чаті йдуть від старших до новіших

    sent, translate_deadline = 0, time.time() + TRANSLATE_BUDGET_SECONDS
    for label, item in candidates:
        if FETCH_DETAILS:
            enrich_with_details(item)
            time.sleep(random.uniform(0.5, 1.2))
        if OPENAI_API_KEY and TRANSLATE_ALERTS and time.time() < translate_deadline:
            translate_listing(item)
        count = author_count(state, item)
        suspect = max(count, item.get("_site_count") or 0)
        if SKIP_SUSPECTED_AGENTS and suspect >= AGENT_THRESHOLD:
            log(f"  пропускаю {item['id']}: у автора {suspect} оголошень")
            delivered = True
        elif telegram_ready():
            delivered = send_listing(item, label, count)
        else:
            print_listing(item, label, count)
            delivered = True
        if delivered:  # не дійшло — спробуємо наступного запуску
            mark_seen(state, item["id"], day)
            register_author(state, item, day)
            sent += 1
    log(f"оброблено нових оголошень: {sent} з {len(candidates)}")


def cmd_once():
    state = load_state()
    try:
        process_updates(state)  # спершу — натискання «Додати в канал» з минулих разів
        run_once(state)
    finally:
        save_state(state)
    return 0


def cmd_loop():
    log(f"Старт. Перевірка кожні {LOOP_MINUTES} хв. Зупинити — Ctrl+C.")
    if not telegram_ready():
        log("Telegram не налаштований — оголошення друкуватимуться тут, у консолі.")
    while True:
        cmd_once()
        next_check = time.time() + LOOP_MINUTES * 60 + random.randint(0, 45)
        while time.time() < next_check:
            if not TELEGRAM_CHANNEL_ID:
                time.sleep(max(0, next_check - time.time()))
                break
            state = load_state()  # між перевірками одразу реагуємо на кнопки
            process_updates(state, wait=int(min(50, max(1, next_check - time.time()))))
            save_state(state)


def cmd_preview(listing_id):
    """Надсилає в робочий чат пост у тому вигляді, в якому він піде в канал."""
    if not telegram_ready():
        raise ConfigError("спершу вкажіть TELEGRAM_BOT_TOKEN і TELEGRAM_CHAT_ID")
    item = fetch_listing(listing_id)
    for chat in chat_ids():
        message, error = publish_post(chat, item)
        log(f"прев'ю надіслано в {chat} ✅" if message else f"прев'ю в {chat} не вдалося: {error}")
    return 0


def cmd_post(listing_id):
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHANNEL_ID:
        raise ConfigError("спершу вкажіть TELEGRAM_BOT_TOKEN і TELEGRAM_CHANNEL_ID")
    state = load_state()
    try:
        link, error, _ = post_to_channel(state, listing_id)
    finally:
        save_state(state)
    log(f"Опубліковано: {link or '✅'}" if not error else f"Не вдалося: {error}")
    return 0 if not error else 1


def cmd_test():
    label, url = load_searches()[0]
    params = search_params(url)
    log(f"[{label}] запит до myhome.ge...")
    items = fetch_page(params, 1)
    cities = sorted({clean(it.get("city_name")) for it in items if clean(it.get("city_name"))})
    log(f"[{label}] на першій сторінці {len(items)} оголошень; міста: {', '.join(cities) or '—'}")
    for item in items[:3]:
        print_listing(item, label, 0)
    if not items:
        log("Порожньо. Перевірте, що за цим посиланням на сайті є оголошення.")
        return 0
    item = enrich_with_details(items[0])
    if "_site_count" in item:
        log(f"Кількість оголошень автора на сайті: {item['_site_count']} "
            f"(поле «{item['_site_count_field']}») ✅")
    else:
        log("Кількість оголошень автора в даних сайту не знайдено. Запустіть "
            "python watcher.py --dump і надішліть файли dump_list.json та dump_detail.json.")
    if telegram_ready():
        ok = send_listing(item, f"🧪 ТЕСТ · {label}", 0)
        log("Тестове повідомлення надіслано ✅" if ok else "Не вдалося надіслати в Telegram ❌")
    else:
        log("Telegram ще не налаштований: вкажіть TELEGRAM_BOT_TOKEN і TELEGRAM_CHAT_ID.")
    return 0


def cmd_dump():
    """Зберігає «сирі» відповіді сайту, щоб подивитися, які поля там є."""
    label, url = load_searches()[0]
    raw_list = http_get_json(list_url(search_params(url), 1), api_headers())
    (BASE_DIR / "dump_list.json").write_text(
        json.dumps(raw_list, ensure_ascii=False, indent=2), encoding="utf-8")
    items = as_dict(as_dict(raw_list).get("data")).get("data") or []
    log(f"[{label}] збережено dump_list.json ({len(items)} оголошень)")
    if items and isinstance(items[0], dict) and items[0].get("id"):
        raw_detail = http_get_json(detail_url(items[0]["id"]), api_headers())
        (BASE_DIR / "dump_detail.json").write_text(
            json.dumps(raw_detail, ensure_ascii=False, indent=2), encoding="utf-8")
        log("збережено dump_detail.json (картка першого оголошення)")
    return 0


def cmd_chat_id():
    if not TELEGRAM_BOT_TOKEN:
        raise ConfigError("спершу вкажіть TELEGRAM_BOT_TOKEN")
    result = tg_call("getUpdates", {"limit": 100, "allowed_updates": [
        "message", "edited_message", "channel_post", "my_chat_member", "callback_query"]})
    if not result.get("ok"):
        raise ConfigError(f"Telegram відповів: {result.get('description')}")
    chats, migrated, channels = {}, set(), set()
    for update in result.get("result", []):
        for kind in ("message", "edited_message", "channel_post", "my_chat_member"):
            event = as_dict(update.get(kind))
            chat = as_dict(event.get("chat"))
            if chat.get("id"):
                name = chat.get("title") or " ".join(
                    filter(None, (chat.get("first_name"), chat.get("last_name")))) or chat.get("username")
                chats[chat["id"]] = name or ""
                if chat.get("type") == "channel":
                    channels.add(chat["id"])
            if event.get("migrate_to_chat_id"):  # група стала супергрупою й отримала новий id
                migrated.add(chat.get("id"))
                chats.setdefault(event["migrate_to_chat_id"], chats.get(chat.get("id"), ""))
    for old_id in migrated:
        chats.pop(old_id, None)
    if not chats:
        log("Порожньо. Напишіть у групі (або боту) /start і запустіть ще раз.")
        return 0
    for chat_id, name in chats.items():
        kind = "  ← канал: це значення для TELEGRAM_CHANNEL_ID" if chat_id in channels else ""
        print(f"chat_id = {chat_id}    ({name}){kind}")
    for cid in channels:
        chats.pop(cid, None)
    if not chats:
        log("Робочого чату не знайдено. Напишіть у групі (або боту) /start і запустіть ще раз.")
        return 0

    groups = [cid for cid in chats if int(cid) < 0]
    choice = groups[0] if len(groups) == 1 else (next(iter(chats)) if not groups and len(chats) == 1 else None)
    if choice is None:
        log("Знайдено кілька чатів — впишіть потрібний chat_id у telegram.json вручну.")
        return 0
    global TELEGRAM_CHAT_ID
    TELEGRAM_CHAT_ID = str(choice)
    config = {"token": TELEGRAM_BOT_TOKEN, "chat_id": TELEGRAM_CHAT_ID}
    if TELEGRAM_CHANNEL_ID:
        config["channel_id"] = TELEGRAM_CHANNEL_ID
    TELEGRAM_FILE.write_text(json.dumps(config, ensure_ascii=False, indent=2), encoding="utf-8")
    send_text("✅ Бот підключено! Сюди приходитимуть нові оголошення від власників з myhome.ge.")
    log(f"chat_id {choice} ({chats[choice]}) збережено в telegram.json, у чат надіслано привітання")
    return 0


def cmd_reset():
    if STATE_FILE.exists():
        STATE_FILE.unlink()
    log("Базу очищено. Наступний запуск тихо запам'ятає поточні оголошення.")
    return 0


def main():
    parser = argparse.ArgumentParser(description="myhome.ge -> Telegram: нові оголошення від власників")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--once", action="store_true", help="одна перевірка і вихід")
    group.add_argument("--test", action="store_true", help="тестовий прогін")
    group.add_argument("--chat-id", action="store_true", help="показати chat_id з повідомлень боту")
    group.add_argument("--reset", action="store_true", help="забути базу побачених оголошень")
    group.add_argument("--dump", action="store_true", help="зберегти сирі відповіді сайту у файли")
    group.add_argument("--preview", type=int, metavar="ID", help="показати в чаті, як оголошення виглядатиме в каналі")
    group.add_argument("--post", type=int, metavar="ID", help="опублікувати оголошення в канал")
    args = parser.parse_args()
    try:
        if args.chat_id:
            return cmd_chat_id()
        if args.reset:
            return cmd_reset()
        if args.test:
            return cmd_test()
        if args.dump:
            return cmd_dump()
        if args.preview:
            return cmd_preview(args.preview)
        if args.post:
            return cmd_post(args.post)
        if args.once:
            return cmd_once()
        return cmd_loop()
    except ConfigError as e:
        log(f"Помилка налаштувань: {e}")
        return 1
    except FetchError as e:
        log(f"myhome.ge: {e}")
        return 1
    except KeyboardInterrupt:
        log("Зупинено.")
        return 0


if __name__ == "__main__":
    sys.exit(main())
