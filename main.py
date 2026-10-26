#!/usr/bin/env python3
"""Fetch news feeds, group items into stories, and send a short summary for
stories confirmed by at least `min_sources` independent outlets.

Usage:
    python main.py --once
    python main.py --loop --interval 300
"""
from __future__ import annotations

import argparse
import calendar
import hashlib
import html
import json
import os
import re
import smtplib
import sys
import time
import unicodedata
from collections import Counter
from datetime import datetime, timezone
from email.message import EmailMessage
from pathlib import Path

import feedparser
import requests
import yaml

BASE = Path(__file__).resolve().parent
NOW = lambda: time.time()  # noqa: E731

# ----------------------------------------------------------------- utils

QUIET = False
_ERRORS: Counter = Counter()


def log(msg: str) -> None:
    if QUIET:
        return
    ts = datetime.now(timezone.utc).strftime("%H:%M:%S")
    print(f"[{ts}] {redact(msg)}", flush=True)


def warn(kind: str, msg: str) -> None:
    """Count an error; only print its text when not in quiet mode."""
    _ERRORS[kind] += 1
    log(f"  ! {kind}: {msg}")


SECRET_VARS = ("GEMINI_API_KEY", "TELEGRAM_BOT_TOKEN", "TELEGRAM_CHAT_ID", "SMTP_PASSWORD", "SMTP_USER",
               "DISCORD_WEBHOOK_URL", "NTFY_TOPIC", "NTFY_TOKEN")


def redact(text: str) -> str:
    for k in SECRET_VARS:
        v = os.environ.get(k)
        if v and len(v) > 3:
            text = text.replace(v, "***")
    hook = os.environ.get("DISCORD_WEBHOOK_URL", "")
    m = re.search(r"/webhooks/(\d+)/([\w-]+)", hook)
    if m:  # also hide the webhook id/token if they show up on their own
        for part in m.groups():
            text = text.replace(part, "***")
    text = re.sub(r"(discord(?:app)?\.com/api/webhooks/)\S+", r"\1***", text)
    return text


def load_env_file(path: Path) -> None:
    """Tiny .env reader so we don't need python-dotenv. Real env vars win."""
    if not path.exists():
        return
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        k, v = line.split("=", 1)
        k, v = k.strip(), v.split(" #")[0].strip().strip('"').strip("'")
        if k and k not in os.environ:
            os.environ[k] = v


def load_config(path: Path) -> dict:
    with open(path, encoding="utf-8") as f:
        return yaml.safe_load(f)


def strip_html(text: str) -> str:
    text = re.sub(r"<[^>]+>", " ", text or "")
    text = html.unescape(text)
    return re.sub(r"\s+", " ", text).strip()


STOPWORDS = set("""
a about above after again against all also am an and any are as at be because been before being
below between both but by can could did do does doing down during each few for from further had has
have having he her here hers him his how i if in into is it its itself just me more most my no nor
not now of off on once only or other our out over own same she should so some such than that the
their them then there these they this those through to too under until up very was we were what
when where which while who whom why will with would you your says said say new news live latest
update updates report reports reported amid over after year years day days week weeks first last
one two us via could may might world video watch photos analysis opinion here how what why
make makes made take takes call calls back get gets set sets vs since still yet near
""".split())

_PLURAL = re.compile(r"(?<=[a-z]{3})(s|es)$")


def norm_token(tok: str) -> str:
    tok = unicodedata.normalize("NFKD", tok).encode("ascii", "ignore").decode().lower()
    tok = tok.strip("'’-.")
    if tok.endswith("'s"):
        tok = tok[:-2]
    if not tok.isdigit():
        tok = _PLURAL.sub("", tok)
    return tok


def keywords(text: str) -> dict[str, int]:
    """Return {token: weight}. Capitalised words (names/places) and numbers weigh 2."""
    out: dict[str, int] = {}
    words = re.findall(r"[A-Za-zÀ-ÿ0-9][A-Za-zÀ-ÿ0-9'’\-.]*", text)
    for i, w in enumerate(words):
        t = norm_token(w)
        if len(t) < 3 and not t.isdigit():
            continue
        if t in STOPWORDS:
            continue
        weight = 2 if (w[0].isupper() and i > 0) or t.isdigit() or w.isupper() else 1
        out[t] = max(out.get(t, 0), weight)
    return out


def numbers_in(text: str) -> set[str]:
    return {n.replace(",", "") for n in re.findall(r"\d[\d,]*(?:\.\d+)?", text)}


def short_hash(s: str) -> str:
    return hashlib.sha1(s.encode("utf-8")).hexdigest()[:12]

# ----------------------------------------------------------------- feeds

TITLE_SUFFIX = re.compile(r"\s+[-–|]\s+(Reuters|AP News|The Associated Press|Associated Press|AP)\s*$", re.I)
TITLE_PREFIX = re.compile(r"^(live updates?|live|the latest|watch|video|in pictures|explainer|analysis|opinion)\s*[:|–-]\s*", re.I)
LIVE_SUFFIX = re.compile(r"\s+[–-]\s+[\w\s]*\blive\b\s*$", re.I)


def clean_title(t: str) -> str:
    t = TITLE_SUFFIX.sub("", strip_html(t))
    t = TITLE_PREFIX.sub("", t)
    t = LIVE_SUFFIX.sub("", t)
    t = re.sub(r"\s+live(\s+updates?|\s+blog)?\s*:", ":", t, flags=re.I)  # "Brazil runoff live updates: ..."
    return t.strip()


def wire_outlet(outlet: str, link: str, summary: str) -> str:
    """Syndicated wire copy counts as the wire, not the outlet that reprinted it."""
    if "/wireStory/" in link or re.search(r"\(AP\)\s*[—-]", summary):
        return "AP"
    if re.search(r"\(Reuters\)\s*[—-]", summary):
        return "Reuters"
    return outlet


def fetch_feeds(cfg: dict) -> list[dict]:
    ua = cfg.get("http", {}).get("user_agent", "Mozilla/5.0")
    timeout = cfg.get("http", {}).get("timeout_seconds", 20)
    max_age = cfg.get("max_item_age_hours", 6) * 3600
    ex = cfg.get("exclude_keywords") or []
    exclude = re.compile(r"\b(" + "|".join(re.escape(w) for w in ex) + r")\b", re.I) if ex else None
    items: list[dict] = []
    for feed in cfg["feeds"]:
        outlet, url = feed["outlet"], feed["url"]
        try:
            r = requests.get(url, headers={"User-Agent": ua}, timeout=timeout)
            r.raise_for_status()
            parsed = feedparser.parse(r.content)
        except Exception as e:  # one bad feed must never stop the bot
            warn("feed", f"{outlet}: {e}")
            continue
        kept = 0
        for e in parsed.entries:
            title = clean_title(e.get("title", ""))
            if len(title.split()) < 5 or " | " in title:
                continue  # topic pages, section fronts, "Trending News" etc.
            if exclude and exclude.search(title):
                continue
            ts = None
            for key in ("published_parsed", "updated_parsed"):
                if e.get(key):
                    ts = calendar.timegm(e[key])
                    break
            if ts is None:
                ts = NOW()  # undated item: treat as fresh
            if NOW() - ts > max_age:
                continue
            link = e.get("link", "")
            summary = strip_html(e.get("summary", ""))
            if "news.google.com" in url or summary.lower().startswith(title.lower()[:40]):
                summary = ""  # Google News summaries only repeat the headline
            items.append({
                "id": short_hash(link or (outlet + title)),
                "outlet": wire_outlet(outlet, link, summary),
                "title": title,
                "summary": summary[:400],
                "link": link,
                "ts": ts,
                "kw": keywords(title + " " + summary[:160]),
                "title_kw": keywords(title),
            })
            kept += 1
        log(f"  {outlet}: {len(parsed.entries)} items, {kept} recent")
    return items

# ----------------------------------------------------------------- clustering

def similarity(a: dict[str, int], b: dict[str, int]) -> tuple[float, int]:
    shared = set(a) & set(b)
    if not shared:
        return 0.0, 0
    w = sum(max(a[t], b[t]) for t in shared)
    overlap = len(shared) / max(1, min(len(a), len(b)))
    return overlap, w


def same_story(a: dict[str, int], b: dict[str, int], cc: dict) -> bool:
    ov, w = similarity(a, b)
    return ov >= cc.get("min_overlap", 0.34) and w >= cc.get("min_shared", 4)


def cluster_items(items: list[dict], cc: dict) -> list[list[dict]]:
    """Greedy clustering: an item joins the first cluster containing a similar item."""
    clusters: list[list[dict]] = []
    for it in sorted(items, key=lambda x: x["ts"]):
        home = None
        for c in clusters:
            if any(same_story(it["kw"], o["kw"], cc) or same_story(it["title_kw"], o["title_kw"], cc) for o in c):
                home = c
                break
        if home is None:
            clusters.append([it])
        else:
            home.append(it)
    return clusters

# ----------------------------------------------------------------- state

def load_state(path: Path) -> dict:
    if path.exists():
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            warn("state", "stories.json was corrupt; starting fresh (old file kept as .bak)")
            path.rename(path.with_suffix(".json.bak"))
    return {"stories": {}, "seen_items": {}}


def save_state(path: Path, state: dict) -> None:
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(state, indent=1, ensure_ascii=False), encoding="utf-8")
    tmp.replace(path)


def prune_state(state: dict, days: int) -> int:
    cutoff = NOW() - days * 86400
    old = [sid for sid, s in state["stories"].items() if s["last_seen"] < cutoff]
    for sid in old:
        del state["stories"][sid]
    state["seen_items"] = {k: v for k, v in state["seen_items"].items() if v >= cutoff}
    return len(old)


def independent_sources(story: dict) -> int:
    """Distinct outlets, merging outlets that ran the exact same headline (syndicated copy)."""
    groups: dict[str, set] = {}
    for it in story["items"]:
        key = re.sub(r"\W+", "", it["title"].lower())
        groups.setdefault(key, set()).add(it["outlet"])
    outlets = {it["outlet"] for it in story["items"]}
    # union-find over outlets that share an identical headline
    parent = {o: o for o in outlets}

    def find(o):
        while parent[o] != o:
            o = parent[o]
        return o
    for g in groups.values():
        g = list(g)
        for o in g[1:]:
            parent[find(o)] = find(g[0])
    return len({find(o) for o in outlets})


def match_story(cluster: list[dict], state: dict, cc: dict) -> str | None:
    best, best_w = None, 0
    for sid, s in state["stories"].items():
        for it in cluster:
            for t in s["titles"][-8:]:
                tkw = keywords(t)
                if same_story(it["title_kw"], tkw, cc):
                    _, w = similarity(it["title_kw"], tkw)
                    if w > best_w:
                        best, best_w = sid, w
    return best

# ----------------------------------------------------------------- LLM

RULES = """Write a short, neutral news summary of ONE story.
STRICT RULES:
1. Use ONLY facts stated in the SOURCE REPORTS below. Do not add numbers, names, places, causes, quotes or context that are not in them. If reports disagree, use the more cautious wording or say "reports say".
2. Name the outlets the facts come from (e.g. "according to Reuters and BBC News").
3. Two or three plain sentences, at most {limit} characters in total. No links, no lists, no emojis, no headings.
4. Neutral, factual tone. No sensational words, no opinions, no speculation. Do not say or imply anyone is guilty unless the reports say they were convicted (use "accused", "suspected", "charged"). No graphic detail. Do not name private individuals who are victims, or anyone under 18.
5. Output ONLY the summary text."""


def build_prompt(story: dict, new_items: list[dict], is_update: bool, cfg: dict, limit: int) -> str:
    lines = [RULES.format(limit=limit), ""]
    if is_update:
        lines += [
            "This is a FOLLOW-UP. The previous summary was:",
            f'"{story["messages"][-1]["text"]}"',
            "",
            "Summarise ONLY what is new compared with the previous summary, using the NEW REPORTS. "
            "Keep it understandable on its own.",
            "",
            "NEW REPORTS:",
        ]
        reports = new_items
    else:
        lines += ["SOURCE REPORTS:"]
        reports = story_items_for_prompt(story)
    for it in reports[:8]:
        s = f"- [{it['outlet']}] {it['title']}"
        if it.get("summary"):
            s += f" — {it['summary'][:300]}"
        lines.append(s)
    lines += ["", "Summary:"]
    return "\n".join(lines)


WIRES = ["Reuters", "AP", "BBC News", "Al Jazeera", "The Guardian", "France 24", "DW", "NPR"]
WEAK_HEADLINE = re.compile(r"\?|\b(reactions?|who is|what (we know|to know)|explained|how|why|opinion|analysis|in pictures)\b", re.I)


def headline_score(it: dict) -> float:
    score = 0.0
    if WEAK_HEADLINE.search(it["title"]):
        score -= 5
    if it["outlet"] in WIRES:
        score += 3 - WIRES.index(it["outlet"]) * 0.2
    n = len(it["title"].split())
    score -= abs(n - 12) * 0.1
    score -= max(0.0, (NOW() - it["ts"]) / 3600) * 0.8  # newer reports win
    return score


def story_items_for_prompt(story: dict) -> list[dict]:
    """Best item per outlet, best first."""
    seen, out = set(), []
    for it in sorted(story["items"], key=lambda x: -headline_score(x)):
        if it["outlet"] in seen:
            continue
        seen.add(it["outlet"])
        out.append(it)
    return out


class LLMError(Exception):
    pass


def call_ollama(prompt: str, cfg: dict) -> str:
    oc = cfg["llm"].get("ollama", {})
    url = os.environ.get("OLLAMA_URL", oc.get("url", "http://localhost:11434")).rstrip("/")
    model = os.environ.get("OLLAMA_MODEL", oc.get("model", "llama3.1:8b"))
    try:
        r = requests.post(f"{url}/api/chat", json={
            "model": model, "stream": False,
            "messages": [{"role": "user", "content": prompt}],
            "options": {"temperature": cfg["llm"].get("temperature", 0.3)},
        }, timeout=cfg["llm"].get("timeout_seconds", 120))
        r.raise_for_status()
        return r.json()["message"]["content"]
    except Exception as e:
        raise LLMError(f"ollama: {e}") from e


def call_gemini(prompt: str, cfg: dict) -> str:
    key = os.environ.get("GEMINI_API_KEY")
    if not key:
        raise LLMError("gemini: GEMINI_API_KEY is not set")
    models = [os.environ["GEMINI_MODEL"]] if os.environ.get("GEMINI_MODEL") else cfg["llm"].get("gemini", {}).get("models", ["gemini-3.8-flash"])
    last = None
    for model in models:
        try:
            r = requests.post(
                f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent",
                headers={"x-goog-api-key": key, "Content-Type": "application/json"},
                json={"contents": [{"role": "user", "parts": [{"text": prompt}]}],
                      "generationConfig": {"temperature": cfg["llm"].get("temperature", 0.3), "maxOutputTokens": 2048}},
                timeout=cfg["llm"].get("timeout_seconds", 120))
            if r.status_code != 200:
                last = f"{model}: HTTP {r.status_code}"
                continue
            parts = r.json()["candidates"][0]["content"]["parts"]
            return "".join(p.get("text", "") for p in parts if not p.get("thought"))
        except Exception as e:
            last = f"{model}: {type(e).__name__}"
    raise LLMError(f"gemini: {last}")


def backend_name(cfg: dict) -> str:
    return os.environ.get("LLM_BACKEND", cfg["llm"].get("backend", "ollama")).lower()


def call_llm(prompt: str, cfg: dict) -> str:
    b = backend_name(cfg)
    if b == "ollama":
        return call_ollama(prompt, cfg)
    if b == "gemini":
        return call_gemini(prompt, cfg)
    raise LLMError(f"backend '{b}' has no LLM (template mode)")

# ----------------------------------------------------------------- checks

TONE = re.compile(r"\b(shocking|horrifying|you won'?t believe|unbelievable|insane|jaw-dropping|mind-blowing|gruesome|bloodbath|slaughter(ed)?|decapitat\w*|mutilat\w*|dismember\w*)\b", re.I)


def clean_text(text: str) -> str:
    text = re.sub(r"<think>.*?</think>", "", text, flags=re.S)
    text = re.sub(r"^\s*(here('s| is) (the|a) summary:?|summary:)\s*", "", text, flags=re.I)
    text = text.strip().strip('"“”').strip()
    text = re.sub(r"https?://\S+", "", text)
    text = re.sub(r"[\U0001F300-\U0001FAFF\u2600-\u27BF]", "", text)
    text = re.sub(r"(\s*#\w+)+\s*$", "", text)  # drop trailing tag words
    text = re.sub(r"(^|\s)#(\w+)", r"\1\2", text)
    text = re.sub(r"^\s*(NEW|UPDATE|BREAKING)\s*:\s*", "", text, flags=re.I)  # prefix is added by us
    return re.sub(r"\s+", " ", text).strip()


def check_text(text: str, story_text: str, limit: int) -> list[str]:
    problems = []
    if len(text) < 20:
        problems.append("empty or too short")
    if len(text) > limit:
        problems.append(f"too long ({len(text)} > {limit} chars)")
    if TONE.search(text):
        problems.append("sensational or graphic wording")
    allowed = numbers_in(story_text)
    invented = {n for n in numbers_in(text) if n not in allowed}
    if invented:
        problems.append(f"numbers not in sources: {', '.join(sorted(invented))}")
    return problems


def trim_to_fit(text: str, limit: int) -> str:
    if len(text) <= limit:
        return text
    out = ""
    for s in re.split(r"(?<=[.!?])\s+", text):
        cand = (out + " " + s).strip()
        if len(cand) <= limit:
            out = cand
        else:
            break
    return out or text[: limit - 1].rsplit(" ", 1)[0].rstrip(",;:") + "…"


def outlets_phrase(outlets: list[str]) -> str:
    o = outlets[:4]
    return o[0] if len(o) == 1 else ", ".join(o[:-1]) + " and " + o[-1]


def template_text(story: dict, new_items: list[dict], is_update: bool, limit: int) -> str:
    """No-AI summary: best headline, a second headline from another outlet, and who reported it."""
    src = story_items_for_prompt({"items": new_items}) if is_update else story_items_for_prompt(story)
    lead = src[0]
    parts = [lead["title"].rstrip(".") + "."]
    lead_kw = set(lead["title_kw"]) if "title_kw" in lead else set(keywords(lead["title"]))
    for other in src[1:]:
        if len(set(keywords(other["title"])) - lead_kw) >= 3:
            parts.append(f"{other['outlet']}: {other['title'].rstrip('.')}.")
            break
    outlets = list(dict.fromkeys(i["outlet"] for i in src))
    parts.append(f"Reported by {outlets_phrase(outlets)}.")
    return trim_to_fit(" ".join(parts), limit)


def write_summary(story: dict, new_items: list[dict], is_update: bool, cfg: dict) -> tuple[str, str]:
    """Returns (text, how_it_was_made)."""
    limit = int(cfg.get("max_summary_chars", 600))
    src_items = new_items + story["items"] if is_update else story["items"]
    story_text = " ".join(i["title"] + " " + i.get("summary", "") for i in src_items)
    if is_update:
        story_text += " " + story["messages"][-1]["text"]
    if backend_name(cfg) not in ("template", "mock", "none"):
        prompt = build_prompt(story, new_items, is_update, cfg, limit=limit - 50)
        for _ in range(3):
            try:
                raw = call_llm(prompt, cfg)
            except LLMError as e:
                warn("llm", str(e))
                break
            text = clean_text(raw)
            problems = check_text(text, story_text, limit)
            if problems and problems[0].startswith("too long") and len(problems) == 1:
                text = trim_to_fit(text, limit)
                problems = check_text(text, story_text, limit)
            if not problems:
                return text, backend_name(cfg)
            warn("rejected", "; ".join(problems))
            prompt += f"\n\nYour previous answer was rejected because: {'; '.join(problems)}. Fix this. Summary:"
    return template_text(story, new_items, is_update, limit), "template"

# ----------------------------------------------------------------- delivery

def telegram_ready() -> bool:
    return bool(os.environ.get("TELEGRAM_BOT_TOKEN") and os.environ.get("TELEGRAM_CHAT_ID"))


def discord_ready() -> bool:
    return bool(os.environ.get("DISCORD_WEBHOOK_URL"))


def ntfy_ready() -> bool:
    return bool(os.environ.get("NTFY_TOPIC", "").strip())


def any_channel() -> bool:
    return telegram_ready() or email_ready() or discord_ready() or ntfy_ready()


def email_ready() -> bool:
    return bool(os.environ.get("SMTP_HOST") and os.environ.get("EMAIL_TO"))


def format_message(m: dict) -> str:
    links = "\n".join(f"- {s['outlet']}: {s['link']}" for s in m["sources"][:5])
    return f"{m['kind']}: {m['text']}\n\nSources:\n{links}"


def deliver(messages: list[dict], cfg: dict) -> int:
    """Send messages; returns how many were delivered to at least one channel."""
    if not messages:
        return 0
    if not QUIET:
        for m in messages:
            print("\n" + "-" * 70 + f"\n{format_message(m)}\n(written by: {m['made_by']})\n" + "-" * 70, flush=True)
        out = cfg.get("files", {}).get("output")
        if out:  # optional local log file, never used in quiet/CI mode
            with open(BASE / out, "a", encoding="utf-8") as f:
                for m in messages:
                    when = datetime.fromtimestamp(m["ts"], timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
                    f.write(f"## {when}\n\n{format_message(m)}\n\n")
    sent = 0
    if telegram_ready():
        sent = max(sent, send_telegram(messages))
    if discord_ready():
        sent = max(sent, send_discord(messages))
    if ntfy_ready():
        sent = max(sent, send_ntfy(messages))
    if email_ready() and send_email(messages):
        sent = len(messages)
    return sent if any_channel() else len(messages)


DISCORD_LIMIT = 2000
DISCORD_DELAY = 1.0  # seconds between posts


def discord_text(m: dict) -> str:
    text = format_message(m)
    if len(text) <= DISCORD_LIMIT:
        return text
    # trim the summary first, keep the sources list
    head, _, tail = text.partition("\n\nSources:")
    tail = "\n\nSources:" + tail if tail else ""
    room = DISCORD_LIMIT - len(tail)
    if room < 200:
        return text[: DISCORD_LIMIT - 1] + "…"
    return trim_to_fit(head, room) + tail


def send_discord(messages: list[dict]) -> int:
    url = os.environ["DISCORD_WEBHOOK_URL"].strip()
    ok = 0
    for n, m in enumerate(messages):
        if n:
            time.sleep(DISCORD_DELAY)
        payload = {"content": discord_text(m), "flags": 4,  # 4 = SUPPRESS_EMBEDS (no link previews)
                   "allowed_mentions": {"parse": []}}
        for _ in range(4):
            try:
                r = requests.post(url, json=payload, params={"wait": "true"}, timeout=20)
            except Exception as e:
                warn("discord", type(e).__name__)
                break
            if r.status_code == 429:
                try:
                    wait = float(r.json().get("retry_after", 1))
                except Exception:
                    wait = float(r.headers.get("Retry-After", 1) or 1)
                time.sleep(min(max(wait, 0.5), 30))
                continue
            if r.ok:
                ok += 1
            else:
                warn("discord", f"HTTP {r.status_code}")
            break
        else:
            warn("discord", "rate limited")
    return ok


def send_telegram(messages: list[dict]) -> int:
    token, chat = os.environ["TELEGRAM_BOT_TOKEN"], os.environ["TELEGRAM_CHAT_ID"]
    ok = 0
    for m in messages:
        try:
            r = requests.post(f"https://api.telegram.org/bot{token}/sendMessage",
                              json={"chat_id": chat, "text": format_message(m)[:4000], "disable_web_page_preview": True},
                              timeout=20)
            if r.ok:
                ok += 1
            else:
                warn("telegram", f"HTTP {r.status_code}")
        except Exception as e:
            warn("telegram", type(e).__name__)
    return ok


NTFY_MAX_BYTES = 4000
NTFY_DELAY = 0.5


def ntfy_title(m: dict) -> str:
    """'NEW: <short headline>' as a header-safe string (RFC 2047 if not plain ASCII)."""
    head = m["sources"][0]["title"] if m.get("sources") and m["sources"][0].get("title") else m["text"]
    head = re.sub(r"\s+", " ", head).strip()
    if len(head) > 90:
        head = head[:89].rsplit(" ", 1)[0] + "…"
    title = f"{m['kind']}: {head}"
    try:
        title.encode("ascii")
        return title
    except UnicodeEncodeError:
        import base64
        return "=?UTF-8?B?" + base64.b64encode(title.encode("utf-8")).decode("ascii") + "?="


def ntfy_body(m: dict) -> bytes:
    body = format_message(m).encode("utf-8")
    if len(body) <= NTFY_MAX_BYTES:
        return body
    return body[: NTFY_MAX_BYTES - 3].decode("utf-8", "ignore").encode("utf-8") + "…".encode("utf-8")


def send_ntfy(messages: list[dict]) -> int:
    server = (os.environ.get("NTFY_SERVER") or "https://ntfy.sh").strip().rstrip("/")
    url = f"{server}/{os.environ['NTFY_TOPIC'].strip()}"
    token = os.environ.get("NTFY_TOKEN", "").strip()
    try:
        prio = str(min(5, max(1, int(os.environ.get("NTFY_PRIORITY") or 3))))
    except ValueError:
        prio = "3"
    ok = 0
    for n, m in enumerate(messages):
        if n:
            time.sleep(NTFY_DELAY)
        headers = {"Title": ntfy_title(m), "Tags": "newspaper", "Priority": prio,
                   "Content-Type": "text/plain; charset=utf-8"}
        if m.get("sources") and m["sources"][0].get("link", "").startswith("http"):
            headers["Click"] = m["sources"][0]["link"]
        if token:
            headers["Authorization"] = f"Bearer {token}"
        delay = 2.0
        for _ in range(4):
            try:
                r = requests.post(url, data=ntfy_body(m), headers=headers, timeout=20)
            except Exception as e:
                warn("ntfy", type(e).__name__)
                break
            if r.status_code == 429:
                try:
                    wait = float(r.headers.get("Retry-After") or delay)
                except ValueError:
                    wait = delay
                time.sleep(min(max(wait, 0.5), 60))
                delay *= 2
                continue
            if r.ok:
                ok += 1
            else:
                warn("ntfy", f"HTTP {r.status_code}")
            break
        else:
            warn("ntfy", "rate limited")
    return ok


def send_email(messages: list[dict]) -> bool:
    host, to = os.environ["SMTP_HOST"], os.environ["EMAIL_TO"]
    port = int(os.environ.get("SMTP_PORT") or 587)
    user, pw = os.environ.get("SMTP_USER"), os.environ.get("SMTP_PASSWORD")
    msg = EmailMessage()
    msg["Subject"] = f"Notes ({len(messages)})"
    msg["From"] = os.environ.get("EMAIL_FROM") or user or to
    msg["To"] = to
    msg.set_content("\n\n-----\n\n".join(format_message(m) for m in messages))
    try:
        if port == 465:
            with smtplib.SMTP_SSL(host, port, timeout=30) as s:
                if user:
                    s.login(user, pw or "")
                s.send_message(msg)
        else:
            with smtplib.SMTP(host, port, timeout=30) as s:
                s.starttls()
                if user:
                    s.login(user, pw or "")
                s.send_message(msg)
        return True
    except Exception as e:
        warn("email", type(e).__name__)
        return False

# ----------------------------------------------------------------- main logic

def slim(it: dict) -> dict:
    return {k: it[k] for k in ("id", "outlet", "title", "summary", "link", "ts")}


def is_material(story: dict, new_items: list[dict], uc: dict) -> bool:
    old_kw = set(story["kw"])
    old_nums = numbers_in(" ".join(t["text"] for t in story["messages"]) + " " + " ".join(story["titles"]))
    for it in new_items:
        new_kw = set(it["title_kw"]) - old_kw
        new_nums = numbers_in(it["title"]) - old_nums
        if new_nums or len(new_kw) >= uc.get("min_new_keywords", 4):
            return True
    return False


def run_once(cfg: dict) -> list[dict]:
    _ERRORS.clear()
    state_path = BASE / cfg.get("files", {}).get("state", "stories.json")
    state = load_state(state_path)
    cc, uc = cfg.get("clustering", {}), cfg.get("updates", {})
    min_src = int(os.environ.get("MIN_SOURCES") or cfg.get("min_sources", 2))
    log(f"Checking {len(cfg['feeds'])} feeds (backend: {backend_name(cfg)}, min sources: {min_src})")
    items = fetch_feeds(cfg)
    fresh = [i for i in items if i["id"] not in state["seen_items"]]
    clusters = cluster_items(items, cc)
    log(f"{len(items)} recent items, {len(fresh)} unseen, {len(clusters)} story clusters")

    candidates: dict = {}  # story_id -> (score, story_id, new_items, is_update)
    for cl in clusters:
        new_in_cluster = [i for i in cl if i["id"] not in state["seen_items"]]
        sid = match_story(cl, state, cc)
        if sid is None:
            sid = short_hash(cl[0]["title"] + str(cl[0]["ts"]))
            state["stories"][sid] = {"id": sid, "created": NOW(), "last_seen": NOW(), "titles": [],
                                     "kw": {}, "outlets": [], "items": [], "messages": [], "last_sent": 0}
        s = state["stories"][sid]
        s["last_seen"] = NOW()
        already_sent = bool(s["messages"])
        known = {x["id"] for x in s["items"]}
        for it in cl:
            if it["id"] in known:
                continue
            s["items"].append(slim(it))
            s["titles"].append(it["title"])
            if it["outlet"] not in s["outlets"]:
                s["outlets"].append(it["outlet"])
            if not already_sent:  # keywords grow freely until the first message
                for k, v in it["kw"].items():
                    s["kw"][k] = max(s["kw"].get(k, 0), v)
        s["items"] = s["items"][-40:]
        s["titles"] = s["titles"][-40:]
        if not already_sent:
            if independent_sources(s) >= min_src:
                candidates[sid] = (independent_sources(s) + 100, sid, [], False)
        elif new_in_cluster:
            cooled = NOW() - s["last_sent"] >= uc.get("min_update_minutes", 30) * 60
            under_cap = len(s["messages"]) <= uc.get("max_updates_per_story", 6)
            if cooled and under_cap and is_material(s, new_in_cluster, uc):
                prev = candidates.get(sid)
                merged = (prev[2] if prev and prev[3] else []) + new_in_cluster
                candidates[sid] = (independent_sources(s), sid, merged, True)
        for it in cl:
            state["seen_items"][it["id"]] = it["ts"]

    ranked = sorted(candidates.values(), key=lambda c: -c[0])
    messages = []
    for _, sid, new_items, is_update in ranked[: cfg.get("max_messages_per_run", 5)]:
        s = state["stories"][sid]
        text, made_by = write_summary(s, new_items, is_update, cfg)
        if any(t["text"] == text for t in s["messages"]):
            continue
        kind = "UPDATE" if is_update else "NEW"
        s["messages"].append({"text": text, "ts": NOW(), "kind": kind})
        s["last_sent"] = NOW()
        if is_update:
            for it in new_items:
                for k, v in it["kw"].items():
                    s["kw"][k] = max(s["kw"].get(k, 0), v)
        src = story_items_for_prompt({"items": new_items}) if is_update else story_items_for_prompt(s)
        messages.append({"story_id": sid, "kind": kind, "text": text, "made_by": made_by,
                         "ts": NOW(), "sources": src[:5]})
    pruned = prune_state(state, cfg.get("prune_days", 7))
    for sid in [k for k, v in state["stories"].items() if not v["messages"] and NOW() - v["created"] > 86400]:
        del state["stories"][sid]
    save_state(state_path, state)
    sent = deliver(messages, cfg)
    tracked = sum(1 for s in state["stories"].values() if s["messages"])
    log(f"Done: {len(messages)} message(s), {tracked} stories tracked, {len(state['stories'])} total, pruned {pruned}")
    if QUIET:
        errs = sum(_ERRORS.values())
        print(f"ok: {sent} sent" + (f", {errs} warnings" if errs else ""), flush=True)
    return messages


def main() -> int:
    global QUIET
    ap = argparse.ArgumentParser(description="Fetch, verify and summarise news stories.")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--once", action="store_true", help="run one check and exit (default)")
    g.add_argument("--loop", action="store_true", help="keep checking forever")
    ap.add_argument("--interval", type=int, default=300, help="seconds between checks in --loop mode")
    ap.add_argument("--config", default=str(BASE / "config.yaml"))
    ap.add_argument("--backend", help="ollama | gemini | template")
    ap.add_argument("--quiet", action="store_true", help="print counts only")
    args = ap.parse_args()

    load_env_file(BASE / ".env")
    QUIET = args.quiet or os.environ.get("QUIET") == "1" or os.environ.get("GITHUB_ACTIONS") == "true"
    if args.backend:
        os.environ["LLM_BACKEND"] = args.backend
    cfg = load_config(Path(args.config))

    if QUIET and not any_channel():
        print("ok: 0 sent", flush=True)  # nowhere to deliver: do nothing
        return 0

    def safe_run():
        try:
            run_once(cfg)
            return True
        except KeyboardInterrupt:
            raise
        except Exception as e:
            if QUIET:
                print("error: run failed", flush=True)
            else:
                log(f"  ! run crashed: {e!r}")
            return False

    if not args.loop:
        return 0 if safe_run() else 1
    log(f"Loop mode: checking every {args.interval}s. Press Ctrl+C to stop.")
    while True:
        safe_run()
        try:
            time.sleep(max(30, args.interval))
        except KeyboardInterrupt:
            log("Stopped.")
            return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(0)
