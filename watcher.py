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

Посилання на пошук беруться з searches.txt, база побачених оголошень — state.json.
Оренда йде в основну групу (українською), продаж («| sale» у searches.txt) — у групу продажу (російською).
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

import no_realtors  # фільтр «не сотрудничаю с риелторами» — лише для груп із SKIP_NO_REALTORS (продаж)

# ─────────────────────────────── НАЛАШТУВАННЯ ───────────────────────────────
# Токен і chat_id беруться зі змінних середовища (на GitHub — Secrets),
# а на своєму комп'ютері — з файлу telegram.json поруч зі скриптом.
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "")  # кілька чатів — через кому
# Інші групи: пошук у searches.txt з третьою частиною «| sale» іде в чат з TELEGRAM_CHAT_ID_SALE
# (у telegram.json — "chat_id_sale"). Без нього такий пошук пропускається, в основну групу не йде.
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY", "")  # якщо задано — грузинські/англійські описи в чаті перекладаються
AI_MODEL = "claude-haiku-5-5"  # до 14.10.2026 — OpenAI gpt-5-mini

LANG = "ru"                    # мова назв і посилань з myhome.ge: ru / en / ka
ONLY_OWNERS = True             # завжди додавати фільтр «Власник» (owner_type=physical)
REGULAR_PER_RUN = 48           # скільки щонайменше звичайних (не VIP) оголошень переглядати за запуск
SEED_REGULAR = 120             # скільки звичайних оголошень «запам'ятати» при першому запуску пошуку
MAX_PAGES_PER_RUN = 40         # запобіжник: більше сторінок одного пошуку за запуск не гортати
FETCH_DETAILS = True           # догружати картку нового оголошення (телефон, автор)
AGENT_THRESHOLD = 3            # від скількох оголошень в одного автора ставити позначку ⚠️
SKIP_SUSPECTED_AGENTS = False  # True — такі оголошення взагалі не надсилати
SKIP_SITE_AGENTS = True        # сайт сам позначив автора «Агент» — не надсилати (False — надсилати з ⚠️)
SKIP_SELF_DECLARED_AGENTS = True  # автор сам пише в описі «я агент» — не надсилати (False — надсилати з ⚠️)
SKIP_NO_REALTORS = ("sale",)   # у цих групах не надсилати, якщо автор пише «с агентствами не сотрудничаю»,
                               # «агентам не звонить» («сотрудничаю 50%» — надсилати); оренда — без фільтра
GROUP_LANGS = {"sale": "ru"}   # мова повідомлень групи; основна (оренда для Олі) — українською
MAX_ALERTS_PER_RUN = 25        # запобіжник від спаму; решта прийде наступного запуску
LOOP_MINUTES = 10              # інтервал у безперервному режимі
FAIL_ALERT_AFTER = 6           # після скількох невдалих перевірок поспіль написати в Telegram
KEEP_DAYS = 60                 # скільки днів пам'ятати побачені оголошення
TRANSLATE_ALERTS = True        # з ANTHROPIC_API_KEY: перекладати російською грузинські/англійські опис і адресу в чаті
TRANSLATE_BUDGET_SECONDS = 180 # не більше стільки секунд на переклади за одну перевірку (запобіжник для GitHub)
# ──────────────────────────────────────────────────────────────────────────────

BASE_DIR = Path(__file__).resolve().parent
SEARCHES_FILE = BASE_DIR / "searches.txt"
STATE_FILE = BASE_DIR / "state.json"
TELEGRAM_FILE = BASE_DIR / "telegram.json"  # {"token": "...", "chat_id": "...", "chat_id_sale": "...", "anthropic_key": "..."} — не викладати на GitHub!

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

try:  # без бібліотеки anthropic не працює лише переклад: pip install anthropic
    import anthropic
except ImportError:
    anthropic = None

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
    """Доповнює токен, chat_id і ключ Anthropic з telegram.json, якщо їх не задано змінними середовища."""
    global TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID, ANTHROPIC_API_KEY, FILE_GROUP_CHATS
    if not TELEGRAM_FILE.exists():
        return
    try:
        cfg = json.loads(TELEGRAM_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError) as e:
        print(f"telegram.json не читається ({e}) — перевірте лапки й коми", flush=True)
        return
    TELEGRAM_BOT_TOKEN = TELEGRAM_BOT_TOKEN or str(cfg.get("token") or "").strip()
    TELEGRAM_CHAT_ID = TELEGRAM_CHAT_ID or str(cfg.get("chat_id") or "").strip()
    ANTHROPIC_API_KEY = ANTHROPIC_API_KEY or str(cfg.get("anthropic_key") or "").strip()
    FILE_GROUP_CHATS = {k[len("chat_id_"):].lower(): str(v or "").strip()
                        for k, v in cfg.items() if k.startswith("chat_id_")}


FILE_GROUP_CHATS = {}  # chat_id інших груп з telegram.json: {"sale": "-100…"}
load_telegram_file()


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

def http_get(url, headers):
    """GET → текст відповіді або FetchError."""
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
    return body


def http_get_json(url, headers):
    try:
        return json.loads(http_get(url, headers))
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
        parts = [part.strip() for part in line.split("|")]
        if len(parts) == 1:  # лише посилання, без назви
            parts.insert(0, "")
        label, url, group = (parts + [""])[:3]
        if "myhome.ge" not in url:
            continue  # рядок-заглушка або щось стороннє
        if group and not re.fullmatch(r"[A-Za-z0-9_]+", group):
            raise ConfigError(f"назва групи «{group}» — лише латинські літери, цифри й _ (наприклад, sale)")
        searches.append((label or "myhome.ge", url, group.lower()))
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
    """Сторінка пошуку на сайті, а не API.

    З 07.10.2026 API пошуку (/v1/statements) без входу в акаунт відповідає 401. Але сторінку
    пошуку сайт збирає на сервері для будь-якого відвідувача й кладе в неї той самий список
    оголошень, що раніше віддавало API, — його й беремо (page_statements).
    """
    query = urllib.parse.urlencode(params + [("page", str(page))], safe=",")
    return f"{SITE}{'' if LANG == 'ka' else '/' + LANG}/s/?{query}"


def page_query(html_text, kind):
    """Відповідь API, яку сайт вбудовує в сторінку (__NEXT_DATA__ → запит ["statements", kind, …])."""
    match = re.search(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', html_text, re.S)
    if not match:
        raise FetchError("на сторінці немає даних — можливо, сторінка перевірки від Cloudflare")
    try:
        props = as_dict(as_dict(json.loads(match.group(1))).get("props"))
    except ValueError:
        raise FetchError("дані сторінки не читаються — можливо, сайт змінився")
    for query in as_dict(as_dict(props.get("pageProps")).get("dehydratedState")).get("queries") or []:
        key = as_dict(query).get("queryKey")
        if isinstance(key, list) and key[:2] == ["statements", kind]:
            return as_dict(as_dict(query.get("state")).get("data"))
    raise FetchError(f"на сторінці немає даних «{kind}» — можливо, сайт змінився")


def page_statements(html_text):
    """Список оголошень зі сторінки пошуку."""
    return page_query(html_text, "list")


def detail_url(listing_id):
    """Сторінка оголошення, а не API.

    З 09.10.2026 ~13:40 і картка в API (/v1/statements/{id}) без входу в акаунт відповідає 401.
    Але сторінку оголошення сайт збирає на сервері з тією самою карткою — її й беремо.
    """
    return f"{SITE}{'' if LANG == 'ka' else '/' + LANG}/pr/{listing_id}/"


def fetch_detail(listing_id):
    """Картка оголошення у форматі колишнього API: {"result": …, "data": {"statement": {…}}}."""
    return page_query(http_get(detail_url(listing_id), {"Accept-Language": LANG}), "details")


def fetch_page(params, page):
    data = page_statements(http_get(list_url(params, page), {"Accept-Language": LANG}))
    if data.get("result") is False:
        raise FetchError(f"сайт повернув помилку: {str(data)[:200]}")
    items = as_dict(data.get("data")).get("data")
    if not isinstance(items, list):
        raise FetchError("неочікуваний формат відповіді — можливо, сайт змінив API")
    return [it for it in items if isinstance(it, dict) and str(it.get("id", "")).isdigit()]


def is_paid(item):
    """Платне оголошення (Super VIP, VIP+, VIP).

    У видачі myhome.ge платні завжди стоять першими — блоками Super VIP → VIP+ → VIP, кожен від
    свіжіших до старших, — і лише за ними звичайні; ні сортування, ні фільтра «без VIP» на сайті
    немає (перевірено в Тбілісі 15.10.2026). В оренді Батумі платних ~59 (2,5 сторінки), у продажу
    квартир ~52, будинків 4, комерції 1 (16.10.2026).
    """
    return any(item.get(k) for k in ("is_super_vip", "is_vip_plus", "is_vip"))


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


def site_user_type(item):
    """Хто автор за версією сайту: "physical" (власник), "agent"… або "" — невідомо."""
    return clean(as_dict(item.get("user_type")).get("type")).lower()


def is_site_agent(item):
    """Сайт показує біля автора плашку «Агент» (чи інший тип, не «власник»)."""
    return site_user_type(item) not in ("", "physical")


def apply_author_listing_count(item, data):
    number, field = find_author_listing_count(data)
    if number is not None:
        item["_site_count"], item["_site_count_field"] = number, field


def enrich_with_details(item):
    """Догружає картку оголошення: телефон, id автора, повніший опис і кількість оголошень автора."""
    apply_author_listing_count(item, item)  # раптом лічильник є вже у видачі
    try:
        data = fetch_detail(item["id"])
    except FetchError as e:
        log(f"  картка {item['id']}: {e}")
        return item
    detail = as_dict(as_dict(as_dict(data).get("data")).get("statement"))
    if site_user_type(detail):  # картка свіжіша за видачу: у видачі автор ще міг бути «власником»
        item["user_type"] = detail["user_type"]
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


# ─────────────────────────── аналіз оголошення ───────────────────────────

PHONE_RE = re.compile(r"(?<![\d+])(?:\+?995[\s\-.]?)?(5\d{2}(?:[\s\-.]?\d){6})(?!\d)")


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
COOPERATE = r"(?:сотрудн\w*|работ\w*|звон\w*|пиш\w*|обращ\w*|беспок\w*|прац\w*|співпрац\w*|work\w*|deal\w*|cooperat\w*)"
NEGATION_BEFORE = re.compile(
    r"(?:\b(?:без|не|no|non|without)\W*"                                              # «без комиссии», «не агентство»
    r"|\b(?:не|not|don'?t|do\W+not)\W+" + COOPERATE + r"(?:\W+(?:с|со|з|із|with))?\W*"  # «не сотрудничаю с риелторами»
    r"|(?:არ|ნუ)\W+(?:ვთანამშრომლ|ვმუშა|ვითანამშრომლ|ვიმუშავ)[^\W\d_]*\W*)$",         # «არ ვთანამშრომლობ სააგენტოებთან»
    re.IGNORECASE)
NEGATION_AFTER = re.compile(
    r"^\W*(?:\w+\W+){0,4}?(?:просьба\W+|прошу\W+|пожалуйста\W+|please\W+|გთხოვთ\W+)?"
    r"(?:не\W+(?:звон|беспок|пис|обращ|турб|дзвон|пиш|работ|сотрудн|нуж|интерес|рассматр|прац|співпрац)"
    r"|(?:do\W+not|don'?t|not)\W+(?:call|contact|disturb|bother|text|write|work|need)"
    r"|(?:არ|ნუ)\W|გარეშე)",
    re.IGNORECASE)
JOINED = re.compile(r"^\W*(?:и|і|й|та|или|або|and|or)?\W*$", re.IGNORECASE)  # «с агентствами и риелторами»
# Автор прямо називає себе агентом — це вже не підозра, а факт (SKIP_SELF_DECLARED_AGENTS)
SELF_AGENT_WORD = r"(?:агент(?:ом)?|агентство|риелтор(?:ом)?|риэлтор(?:ом)?|рієлтор(?:ом)?|маклер(?:ом)?|брокер(?:ом)?)\b"
SELF_AGENT = re.compile(  # «я агент», «являюсь агентом»; але не «я агентствам не сдаю», «я не агент»
    r"\bя\W+(?:являюсь\W+|-\W*)?" + SELF_AGENT_WORD +
    r"|\bявляюсь\W+" + SELF_AGENT_WORD +
    r"|\bi(?:\W+am|'m)\W+(?:an?\W+)?(?:real\W+estate\W+)?(?:agent|realtor|broker)\b"
    r"|(?<!არ )\bვარ\W+(?:აგენტი|რიელტორი|მაკლერი|ბროკერი)\b|(?:აგენტი|რიელტორი|მაკლერი|ბროკერი)\W+ვარ\b",
    re.IGNORECASE)


def text_signals(text):
    """(є ознаки агенції в тексті, автор пише «без посередників»)."""
    text = str(text or "")
    agent = owner = False
    prev_end, prev_negated = None, False
    for m in AGENT_WORD.finditer(text):
        before = text[max(0, m.start() - 40):m.start()]
        after = text[m.end():m.end() + 60]
        negated = bool(NEGATION_BEFORE.search(before) or NEGATION_AFTER.search(after)
                       or (prev_negated and JOINED.match(text[prev_end:m.start()])))
        if negated:
            owner = True   # «агентствам не звонить», «без комиссии», «не сотрудничаю с риелторами»...
        else:
            agent = True   # «комиссия агентства 50%», «real estate agency», «я являюсь агентом»...
        prev_end, prev_negated = m.end(), negated
    return agent, owner


def self_declared_agent(item):
    """Автор сам пише в описі, що він агент («я агент», «являюсь агентом», «I am an agent»)."""
    return bool(SELF_AGENT.search(plain_text(item.get("comment")) + " " + str(item.get("_ru_comment") or "")))


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


def say(lang, uk, ru):
    """Текст мовою групи (GROUP_LANGS): основна — українською, продаж — російською."""
    return ru if lang == "ru" else uk


def group_lang(group):
    return GROUP_LANGS.get(group, "uk")


def facts_text(item, lang="uk"):
    """«45 м² · кімнат: 2 · спалень: 1 · поверх 5/12»."""
    facts = []
    if clean(item.get("area")):
        facts.append(f"{fmt_area(item['area'])} м²")
    if clean(item.get("room")):
        facts.append(say(lang, "кімнат", "комнат") + f": {clean(item['room'])}")
    if clean(item.get("bedroom")):
        facts.append(say(lang, "спалень", "спален") + f": {clean(item['bedroom'])}")
    if clean(item.get("floor")):
        total = clean(item.get("total_floors"))
        facts.append(say(lang, "поверх", "этаж") + f" {clean(item['floor'])}" + (f"/{total}" if total else ""))
    return " · ".join(facts)


def listing_time(item, lang="uk"):
    """«25.09 02:01», а якщо оголошення потім піднімали — «25.09 02:01, оновлено 27.09 14:03»."""
    created = _parse_time(item.get("created_at") or item.get("create_date"))
    updated = _parse_time(item.get("last_updated"))
    if created and updated and updated.date() != created.date():
        return f"{created:%d.%m %H:%M}, " + say(lang, "оновлено", "обновлено") + f" {updated:%d.%m %H:%M}"
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


def build_message(item, label, count, max_len=4096, lang="uk"):
    def esc(value):
        return html.escape(clean(value), quote=False)

    lines = [f"🏠 <b>{esc(item.get('dynamic_title')) or say(lang, 'Нове оголошення', 'Новое объявление')}</b>"]
    if price_text(item):
        lines.append(f"💵 {esc(price_text(item))}")

    facts = esc(facts_text(item, lang))
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
        who.append(f"📞 {esc(masked)} " + say(lang, "(повністю — на сайті)", "(полностью — на сайте)"))
    if who:
        lines.append("👤 " + " · ".join(who))

    when = listing_time(item, lang)
    lines.append(" · ".join(x for x in (f"🕒 {when}" if when else "", f"🔎 {esc(label)}") if x))

    agent_text, owner_text = text_signals(plain_text(item.get("comment")))
    if is_site_agent(item):
        lines.append(say(lang, "⚠️ На myhome.ge автор позначений як агент", "⚠️ На myhome.ge автор отмечен как агент"))
    site = item.get("_site_count")
    if isinstance(site, int):
        words = plural(site, *say(lang, ("оголошення", "оголошення", "оголошень"),
                                  ("объявление", "объявления", "объявлений")))
        if site >= AGENT_THRESHOLD:
            lines.append(f"⚠️ У автора {site} {words} на myhome.ge — " + say(lang, "агент або інвестор", "агент или инвестор"))
        else:
            lines.append(f"✅ У автора {site} {words} на myhome.ge")
    if count >= AGENT_THRESHOLD and (not isinstance(site, int) or count > site):
        words = plural(count, *say(lang, ("оголошенні", "оголошеннях", "оголошеннях"),
                                   ("объявлении", "объявлениях", "объявлениях")))
        lines.append(say(lang, f"⚠️ Цей автор або телефон уже трапився в {count} {words} — агент або інвестор",
                         f"⚠️ Этот автор или телефон уже встречался в {count} {words} — агент или инвестор"))
    if agent_text:
        lines.append(say(lang, "⚠️ В описі згадується агенція або комісія", "⚠️ В описании упоминается агентство или комиссия"))
    elif owner_text:
        lines.append(say(lang, "✍️ Пише, що без посередників", "✍️ Пишет, что без посредников"))

    link = f'🔗 <a href="{html.escape(listing_url(item))}">{say(lang, "Відкрити на myhome.ge", "Открыть на myhome.ge")}</a>'
    message = "\n".join(lines)
    desc = item.get("_ru_comment") or plain_text(item.get("comment"))
    budget = min(400, max_len - visible_len(message) - visible_len(link) - 10)
    if desc and budget > 40:
        snippet = desc if len(desc) <= budget else desc[:budget - 1].rstrip() + "…"
        message += f"\n\n<i>{esc(snippet)}</i>"
    return message + "\n\n" + link


def print_listing(item, label, count, lang="uk"):
    plain = html.unescape(re.sub(r"<[^>]+>", "", build_message(item, label, count, lang=lang)))
    print("-" * 60)
    print(plain.replace(say(lang, "Відкрити на myhome.ge", "Открыть на myhome.ge"), listing_url(item)), flush=True)


# ─────────────────────────────── Telegram ───────────────────────────────

def chat_ids(group=""):
    """Чати групи: основна — TELEGRAM_CHAT_ID, інша (sale) — TELEGRAM_CHAT_ID_SALE."""
    raw = (os.getenv(f"TELEGRAM_CHAT_ID_{group.upper()}") or FILE_GROUP_CHATS.get(group, "")
           if group else TELEGRAM_CHAT_ID)
    return [c.strip() for c in str(raw).split(",") if c.strip()]


def telegram_ready(group=""):
    return bool(TELEGRAM_BOT_TOKEN and chat_ids(group))


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


def send_text(text, group=""):
    for chat in chat_ids(group):
        result = tg_call("sendMessage", {"chat_id": chat, "text": text, "parse_mode": "HTML",
                                         "link_preview_options": {"is_disabled": True}})
        if not result.get("ok"):
            log(f"Telegram ({chat}): {result.get('description')}")


def download_image(url):
    """Завантажує фото з сайту (для випадків, коли Telegram не може взяти його за посиланням)."""
    try:
        if cffi_requests:
            resp = cffi_requests.get(url, headers={"Referer": SITE + "/"}, impersonate="chrome", timeout=30)
            status, body = resp.status_code, resp.content
        else:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Referer": SITE + "/"})
            with urllib.request.urlopen(req, timeout=30, context=ssl_context()) as resp:
                status, body = resp.status, resp.read()
    except Exception as e:
        log(f"  фото {url}: {e}")
        return None
    if status != 200 or not body or len(body) > 10 * 1024 * 1024:
        log(f"  фото {url}: HTTP {status}, {len(body or b'')} байт")
        return None
    return body


def tg_upload(method, fields, files):
    """Запит до Telegram з файлами (multipart). files: {назва: (ім'я файлу, bytes)}."""
    boundary = f"----myhome{random.getrandbits(64):x}"
    parts = []
    for name, value in fields.items():
        if not isinstance(value, str):
            value = json.dumps(value, ensure_ascii=False)
        parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n'
                     f"{value}\r\n".encode("utf-8"))
    for name, (filename, data) in files.items():
        parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"; filename="{filename}"\r\n'
                     "Content-Type: image/jpeg\r\n\r\n".encode("utf-8") + data + b"\r\n")
    body = b"".join(parts) + f"--{boundary}--\r\n".encode("utf-8")
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/{method}"
    headers = {"Content-Type": f"multipart/form-data; boundary={boundary}"}
    try:
        if cffi_requests:
            resp = cffi_requests.post(url, data=body, headers=headers, timeout=120)
            text = resp.text
        else:
            req = urllib.request.Request(url, data=body, headers=headers)
            try:
                with urllib.request.urlopen(req, timeout=120, context=ssl_context()) as resp:
                    text = resp.read().decode("utf-8", "replace")
            except urllib.error.HTTPError as e:
                text = e.read().decode("utf-8", "replace")
        return json.loads(text)
    except Exception as e:
        return {"ok": False, "description": str(e)}


def send_photo(chat, urls, caption):
    """Фото з підписом: спершу за посиланням, інакше завантажує й шле файлом; пробує до 3 фото."""
    result = {"ok": False, "description": "немає фото"}
    for url in urls[:3]:
        result = tg_call("sendPhoto", {"chat_id": chat, "photo": url, "caption": caption,
                                       "parse_mode": "HTML"})
        if result.get("ok"):
            return result
        log(f"  sendPhoto за посиланням не вдався ({result.get('description')}) — шлю файлом")
        data = download_image(url)
        if data:
            result = tg_upload("sendPhoto", {"chat_id": chat, "caption": caption, "parse_mode": "HTML"},
                                {"photo": ("photo.jpg", data)})
            if result.get("ok"):
                return result
            log(f"  sendPhoto файлом не вдався: {result.get('description')}")
    return result


def send_listing(item, label, count, group=""):
    """Надсилає оголошення у всі чати групи її мовою. True, якщо дійшло хоча б в один."""
    photos = image_urls(item)
    lang = group_lang(group)
    caption = build_message(item, label, count, max_len=1024, lang=lang)
    full_text = build_message(item, label, count, lang=lang)
    if not photos:
        log(f"  оголошення {item['id']}: на сайті немає фото")
    delivered = False
    for chat in chat_ids(group):
        result = send_photo(chat, photos, caption) if photos else {"ok": False}
        if not result.get("ok"):  # фото не підійшло — шлемо текстом
            result = tg_call("sendMessage", {"chat_id": chat, "text": full_text,
                                             "parse_mode": "HTML"})
        if result.get("ok"):
            delivered = True
        else:
            log(f"Telegram ({chat}): {result.get('description')}")
        time.sleep(1.1)
    return delivered


# ─────────────────────────────── переклад (Claude) ───────────────────────────────

def claude_json(system, data, schema):
    """Запит до Claude з відповіддю-JSON за схемою. Повертає dict або кидає FetchError."""
    if anthropic is None:
        raise FetchError("немає бібліотеки anthropic (pip install anthropic)")
    try:
        # бібліотека сама повторює запит при 429, 5xx і обриві зв'язку
        response = anthropic.Anthropic(api_key=ANTHROPIC_API_KEY, timeout=60, max_retries=2).messages.create(
            model=AI_MODEL,
            max_tokens=4000,
            system=system,
            messages=[{"role": "user", "content": json.dumps(data, ensure_ascii=False)}],
            # "low" — найнижчий рівень мислення (рівня "minimal" у Claude немає); temperature не задається
            output_config={"effort": "low", "format": {"type": "json_schema", "schema": schema}},
        )
    except anthropic.APIStatusError as e:
        raise FetchError(f"HTTP {e.status_code}: {str(e.message)[:200]}")
    except anthropic.APIConnectionError as e:
        raise FetchError(f"мережева помилка: {str(e)[:150]}")
    if response.stop_reason == "refusal":
        raise FetchError("модель відмовилась")
    if response.stop_reason == "max_tokens":
        raise FetchError("модель не встигла відповісти (ліміт токенів)")
    # першим може прийти блок мислення — відповідь шукати за типом блоку
    text = next((b.text for b in response.content if b.type == "text"), "")
    try:
        parts = json.loads(text)
    except ValueError:
        raise FetchError("відповідь не в очікуваному форматі")
    if not isinstance(parts, dict):
        raise FetchError("відповідь не в очікуваному форматі")
    return parts


TRANSLATE_PROMPT = """Переведи на русский язык описание и адрес объявления о недвижимости в Батуми и окрестностях.
Верни JSON: {"description": "...", "address": "..."}.
Переводи точно, ничего не добавляй и не сокращай, эмодзи оставь. Названия улиц передавай
по-русски: «რუსთაველის ქ. 15» → «ул. Руставели 15», «ჭავჭავაძის ქ.» → «ул. Чавчавадзе».
Если поле пустое или уже на русском — верни его как есть."""
TRANSLATE_SCHEMA = {"type": "object", "additionalProperties": False, "required": ["description", "address"],
                    "properties": {"description": {"type": "string"}, "address": {"type": "string"}}}


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
        parts = claude_json(TRANSLATE_PROMPT, {"description": desc, "address": address}, TRANSLATE_SCHEMA)
    except FetchError as e:
        log(f"  переклад {item['id']}: {e}")
        return True
    if clean(parts.get("description")):
        item["_ru_comment"] = clean(parts["description"])
    if clean(parts.get("address")):
        item["_ru_address"] = clean(parts["address"])
    return True


# ─────────────────────────────── база (state.json) ───────────────────────────────

def new_state():
    # regular_seeded — пошуки, які вже гортають повз платні оголошення (див. run_once)
    return {"version": 1, "searches": {}, "seen": {}, "authors": {}, "fail_streak": 0, "regular_seeded": []}


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
    for key in ("tg_offset", "posted", "facts"):  # залишки кнопки «Додати в канал»
        state.pop(key, None)
    return state


def save_state(state):
    cutoff = (datetime.now(GEORGIA_TZ) - timedelta(days=KEEP_DAYS)).strftime("%Y-%m-%d")
    state["seen"] = {day: sorted(set(ids)) for day, ids in state["seen"].items() if day >= cutoff}
    state["authors"] = {k: v for k, v in state["authors"].items() if v[1] >= cutoff}
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

    for label, url, group in searches:
        if group and telegram_ready() and not telegram_ready(group):
            log(f"[{label}] не задано чат групи «{group}» (секрет TELEGRAM_CHAT_ID_{group.upper()}) — "
                "пропускаю пошук")
            continue
        try:
            params = search_params(url)
        except ConfigError as e:
            log(f"[{label}] {e}")
            continue
        key = urllib.parse.urlencode(sorted(params), safe=",")
        seeding = key not in state["searches"]
        # Пошук, засіяний до 15.10.2026, коли бот ще не гортав повз платні: звичайні оголошення, яких
        # він тоді не бачив, один раз тихо запам'ятовуємо — інакше прийшли б у групу пачкою.
        catching_up = not seeding and key not in state["regular_seeded"]
        quiet = seeding or catching_up
        need = SEED_REGULAR if quiet else REGULAR_PER_RUN

        # Гортаємо, доки не пройдемо всі платні (is_paid) і не переглянемо щонайменше need звичайних;
        # у звичайному запуску — ще й доти, доки на сторінці трапляються незнайомі звичайні (бот пропустив
        # кілька запусків). MAX_PAGES_PER_RUN — запобіжник.
        found, ok, failed, regular = [], False, False, 0
        for page in range(1, MAX_PAGES_PER_RUN + 1):
            try:
                items = fetch_page(params, page)
            except FetchError as e:
                log(f"[{label}] сторінка {page}: {e}")
                failed = True
                break
            ok = True
            if not items:
                break
            found.extend(items)
            fresh = [it for it in items if not is_paid(it)]
            regular += len(fresh)
            if regular >= need and (quiet or all(int(it["id"]) in seen for it in fresh)):
                break
            time.sleep(random.uniform(1.0, 2.0))
        else:
            log(f"[{label}] {MAX_PAGES_PER_RUN} сторінок, а звичайних оголошень лише {regular} — "
                "платних стало забагато?")
        if not ok:
            continue
        any_ok = True

        if quiet:  # перший запуск цього пошуку чи перший після 15.10.2026: запам'ятовуємо все, нічого не шлемо
            added = 0
            for item in found:
                listing_id = int(item["id"])
                if listing_id not in seen and listing_id not in batch:
                    seen.add(listing_id)
                    mark_seen(state, listing_id, day)
                    register_author(state, item, day)
                    added += not is_paid(item)
            if failed:  # не дочитали — наступного запуску ще раз тихо, інакше решта прийде пачкою
                log(f"[{label}] не дочитав видачу: тихо запам'ятав {added} звичайних, "
                    "решту — наступного запуску")
                continue
            state["regular_seeded"].append(key)
            if catching_up:
                log(f"[{label}] гортаю повз платні оголошення: тихо запам'ятав {added} звичайних, "
                    "яких раніше не бачив")
                continue
            state["searches"][key] = day
            log(f"[{label}] перший запуск: запам'ятав {len(found)} оголошень, далі — лише нові")
            if telegram_ready(group):
                send_text(say(group_lang(group),
                              f"✅ Стежу за пошуком «{html.escape(label)}». Поточні {len(found)} "
                              "оголошень запам'ятав — надсилатиму тільки нові.",
                              f"✅ Слежу за поиском «{html.escape(label)}». Текущие {len(found)} "
                              "объявлений запомнил — буду присылать только новые."), group)
            continue

        for item in found:
            listing_id = int(item["id"])
            if listing_id not in seen and listing_id not in batch:
                batch.add(listing_id)
                candidates.append((label, group, item))

    update_fail_streak(state, any_ok)
    if not candidates:
        log("нових оголошень немає" if any_ok else "не вдалося отримати дані з myhome.ge")
        return

    candidates.sort(key=lambda c: int(c[2]["id"]), reverse=True)  # новіші мають більший id
    if len(candidates) > MAX_ALERTS_PER_RUN:
        log(f"нових {len(candidates)}, надсилаю {MAX_ALERTS_PER_RUN}, решту — наступного разу")
        candidates = candidates[:MAX_ALERTS_PER_RUN]
    candidates.reverse()  # у чаті йдуть від старших до новіших

    sent, translate_deadline = 0, time.time() + TRANSLATE_BUDGET_SECONDS
    for label, group, item in candidates:
        if FETCH_DETAILS:
            enrich_with_details(item)
            time.sleep(random.uniform(0.5, 1.2))
        count = author_count(state, item)
        suspect = max(count, item.get("_site_count") or 0)
        if SKIP_SITE_AGENTS and is_site_agent(item):
            log(f"  пропускаю {item['id']}: на сайті автор позначений як «{site_user_type(item)}»")
            delivered = True
        elif SKIP_SELF_DECLARED_AGENTS and self_declared_agent(item):
            log(f"  пропускаю {item['id']}: автор сам пише в описі, що він агент")
            delivered = True
        elif SKIP_SUSPECTED_AGENTS and suspect >= AGENT_THRESHOLD:
            log(f"  пропускаю {item['id']}: у автора {suspect} оголошень")
            delivered = True
        else:
            if ANTHROPIC_API_KEY and TRANSLATE_ALERTS and time.time() < translate_deadline:
                translate_listing(item)
            if group in SKIP_NO_REALTORS and no_realtors.refuses_realtors(
                    plain_text(item.get("comment")) + " " + str(item.get("_ru_comment") or "")):
                log(f"  пропускаю {item['id']}: автор пише, що не співпрацює з рієлторами")
                delivered = True
            elif telegram_ready(group):
                delivered = send_listing(item, label, count, group)
            else:
                print_listing(item, label, count, group_lang(group))
                delivered = True
        if delivered:  # не дійшло — спробуємо наступного запуску
            mark_seen(state, item["id"], day)
            register_author(state, item, day)
            sent += 1
    log(f"оброблено нових оголошень: {sent} з {len(candidates)}")


def cmd_once():
    state = load_state()
    try:
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
        time.sleep(LOOP_MINUTES * 60 + random.randint(0, 45))


def cmd_test():
    label, url, group = load_searches()[0]
    params = search_params(url)
    log(f"[{label}] запит до myhome.ge...")
    items = fetch_page(params, 1)
    cities = sorted({clean(it.get("city_name")) for it in items if clean(it.get("city_name"))})
    log(f"[{label}] на першій сторінці {len(items)} оголошень; міста: {', '.join(cities) or '—'}")
    for item in items[:3]:
        print_listing(item, label, 0, group_lang(group))
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
    if telegram_ready(group):
        ok = send_listing(item, f"🧪 ТЕСТ · {label}", 0, group)
        log("Тестове повідомлення надіслано ✅" if ok else "Не вдалося надіслати в Telegram ❌")
    else:
        log("Telegram ще не налаштований: вкажіть TELEGRAM_BOT_TOKEN і TELEGRAM_CHAT_ID.")
    return 0


def cmd_dump():
    """Зберігає «сирі» відповіді сайту, щоб подивитися, які поля там є."""
    label, url, _ = load_searches()[0]
    raw_list = page_statements(http_get(list_url(search_params(url), 1), {"Accept-Language": LANG}))
    (BASE_DIR / "dump_list.json").write_text(
        json.dumps(raw_list, ensure_ascii=False, indent=2), encoding="utf-8")
    items = as_dict(as_dict(raw_list).get("data")).get("data") or []
    log(f"[{label}] збережено dump_list.json ({len(items)} оголошень)")
    if items and isinstance(items[0], dict) and items[0].get("id"):
        raw_detail = fetch_detail(items[0]["id"])
        (BASE_DIR / "dump_detail.json").write_text(
            json.dumps(raw_detail, ensure_ascii=False, indent=2), encoding="utf-8")
        log("збережено dump_detail.json (картка першого оголошення)")
    return 0


def cmd_chat_id():
    if not TELEGRAM_BOT_TOKEN:
        raise ConfigError("спершу вкажіть TELEGRAM_BOT_TOKEN")
    result = tg_call("getUpdates", {"limit": 100, "allowed_updates": [
        "message", "edited_message", "channel_post", "my_chat_member"]})
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
        kind = "  ← канал, для оголошень не підходить" if chat_id in channels else ""
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
    config.update({f"chat_id_{group}": chats for group, chats in FILE_GROUP_CHATS.items() if chats})
    if ANTHROPIC_API_KEY:
        config["anthropic_key"] = ANTHROPIC_API_KEY
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
