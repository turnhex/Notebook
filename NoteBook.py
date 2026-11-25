#!/usr/bin/env python3
"""
Study Notebook - a personal "book" for study notes.

Run:   python study_notebook.py
Open:  http://127.0.0.1:8000   (opens automatically)

Features
  * Headers (sections) -> each has many pages
  * Rich text editor (bold, italic, headings, lists, checklists, highlight, links...)
  * Insert images (button, paste, or drag & drop) and resize them (drag handle / presets)
  * Attach any files to a page (download / delete)
  * Sticky notes on the page (drag, resize, change colour, delete)
  * Search by section title, page title, content, file names, sticky text
  * Add / rename / edit / move / delete everything
  * Favorites, tags, colored headers, trash, version history, page-to-page links, duplicate
  * Flashcards (spaced repetition), to-dos, exam countdown, Pomodoro timer with study stats
  * Automatic backup to Telegram (zip of database + files), plus manual zip download
  * Responsive Bootstrap UI with a notebook-opening and page-flip animation

Only the Python standard library is used. Data is stored in ./notebook_data
(notebook.db = SQLite database, uploads/ = images and attachments).
Bootstrap is loaded from a CDN, so the browser needs internet for styling.
"""
import argparse
import hashlib
import html as htmllib
import ipaddress
import json
import mimetypes
import os
import re
import shutil
import socket
import sqlite3
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.request
import uuid
import webbrowser
import zipfile
from contextlib import contextmanager
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, urljoin, quote

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "notebook_data")
UPLOAD_DIR = os.path.join(DATA_DIR, "uploads")
DB_PATH = os.path.join(DATA_DIR, "notebook.db")
MAX_UPLOAD = 200 * 1024 * 1024  # 200 MB per file

os.makedirs(UPLOAD_DIR, exist_ok=True)


# --------------------------------------------------------------------------
# Database
# --------------------------------------------------------------------------
@contextmanager
def db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    try:
        yield conn
        conn.commit()
    finally:
        conn.close()


def now():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def init_db():
    with db() as c:
        c.executescript(
            """
            CREATE TABLE IF NOT EXISTS sections(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                title TEXT NOT NULL,
                position INTEGER NOT NULL DEFAULT 0,
                created TEXT
            );
            CREATE TABLE IF NOT EXISTS pages(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                section_id INTEGER NOT NULL REFERENCES sections(id) ON DELETE CASCADE,
                title TEXT NOT NULL DEFAULT 'Untitled page',
                content TEXT NOT NULL DEFAULT '',
                position INTEGER NOT NULL DEFAULT 0,
                created TEXT,
                updated TEXT
            );
            CREATE TABLE IF NOT EXISTS attachments(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                page_id INTEGER NOT NULL REFERENCES pages(id) ON DELETE CASCADE,
                name TEXT NOT NULL,
                stored TEXT NOT NULL UNIQUE,
                size INTEGER NOT NULL DEFAULT 0,
                inline INTEGER NOT NULL DEFAULT 0,
                created TEXT
            );
            CREATE TABLE IF NOT EXISTS stickies(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                page_id INTEGER NOT NULL REFERENCES pages(id) ON DELETE CASCADE,
                text TEXT NOT NULL DEFAULT '',
                color TEXT NOT NULL DEFAULT '#fff176',
                x INTEGER NOT NULL DEFAULT 40,
                y INTEGER NOT NULL DEFAULT 40,
                w INTEGER NOT NULL DEFAULT 200,
                h INTEGER NOT NULL DEFAULT 160
            );
            """
        )
        if "anchor" not in [r[1] for r in c.execute("PRAGMA table_info(stickies)")]:
            c.execute("ALTER TABLE stickies ADD COLUMN anchor TEXT NOT NULL DEFAULT ''")
        def ensure_col(table, col, ddl):
            if col not in [r[1] for r in c.execute(f"PRAGMA table_info({table})")]:
                c.execute(f"ALTER TABLE {table} ADD COLUMN {col} {ddl}")
        ensure_col("sections", "color", "TEXT NOT NULL DEFAULT '#f0b429'")
        ensure_col("sections", "deleted_at", "TEXT NOT NULL DEFAULT ''")
        ensure_col("pages", "tags", "TEXT NOT NULL DEFAULT ''")
        ensure_col("pages", "fav", "INTEGER NOT NULL DEFAULT 0")
        ensure_col("pages", "deleted_at", "TEXT NOT NULL DEFAULT ''")
        ensure_col("pages", "parent_id", "INTEGER")
        c.execute("CREATE TABLE IF NOT EXISTS page_versions(id INTEGER PRIMARY KEY AUTOINCREMENT, "
                  "page_id INTEGER NOT NULL REFERENCES pages(id) ON DELETE CASCADE, title TEXT, content TEXT, saved TEXT)")
        c.executescript("""
            CREATE TABLE IF NOT EXISTS flashcards(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                page_id INTEGER NOT NULL REFERENCES pages(id) ON DELETE CASCADE,
                front TEXT NOT NULL DEFAULT '', back TEXT NOT NULL DEFAULT '',
                due TEXT NOT NULL DEFAULT '', interval INTEGER NOT NULL DEFAULT 0,
                ease REAL NOT NULL DEFAULT 2.5, reps INTEGER NOT NULL DEFAULT 0, created TEXT);
            CREATE TABLE IF NOT EXISTS tasks(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                kind TEXT NOT NULL DEFAULT 'todo', text TEXT NOT NULL DEFAULT '',
                due TEXT NOT NULL DEFAULT '', done INTEGER NOT NULL DEFAULT 0, created TEXT);
            CREATE TABLE IF NOT EXISTS study_log(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                section_id INTEGER, day TEXT NOT NULL, seconds INTEGER NOT NULL DEFAULT 0);
        """)
        cut = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(time.time() - 30 * 86400))
        purge_pages(c, page_subtree_ids(c, [r[0] for r in c.execute("SELECT id FROM pages WHERE deleted_at!='' AND deleted_at<?", (cut,))]))
        purge_sections(c, [r[0] for r in c.execute("SELECT id FROM sections WHERE deleted_at!='' AND deleted_at<?", (cut,))])
        if c.execute("SELECT COUNT(*) FROM sections").fetchone()[0] == 0:
            t = now()
            cur = c.execute(
                "INSERT INTO sections(title, position, created) VALUES('Getting Started', 1, ?)", (t,)
            )
            sid = cur.lastrowid
            welcome = (
                "<h2>Welcome to your Study Notebook \U0001F4D6</h2>"
                "<ul>"
                "<li>Use the <b>+ Header</b> button on the left to add headers (subjects).</li>"
                "<li>Click the <b>+</b> on a header to add pages under it.</li>"
                "<li>Insert images with the toolbar, paste them, or drag &amp; drop. "
                "<i>Click an image</i> to resize it.</li>"
                "<li>Attach files at the bottom of the page.</li>"
                "<li>Add a <b>sticky note</b> with the yellow note button.</li>"
                "<li>Everything saves automatically.</li>"
                "</ul><p><br></p>"
            )
            c.execute(
                "INSERT INTO pages(section_id,title,content,position,created,updated) VALUES(?,?,?,?,?,?)",
                (sid, "Welcome", welcome, 1, t, t),
            )


def rows(cur):
    return [dict(r) for r in cur.fetchall()]


HEX_CHUNK = 4096


def hex_dump(data, offset):
    out = []
    for i in range(0, len(data), 16):
        row = data[i:i + 16]
        hexpart = " ".join(f"{b:02x}" for b in row)
        hexpart = hexpart[:23] + " " + hexpart[23:] if len(row) > 8 else hexpart
        ascii_part = "".join(chr(b) if 32 <= b < 127 else "." for b in row)
        out.append(f"{offset + i:08x}  {hexpart:<48}  {ascii_part}")
    return "\n".join(out)


def strip_tags(html):
    html = re.sub(r"(?is)<(script|style).*?>.*?</\1>", " ", html or "")
    html = re.sub(r"(?i)<br\s*/?>|</(p|div|li|h[1-6]|tr)>", "\n", html)
    html = re.sub(r"<[^>]+>", " ", html)
    html = (
        html.replace("&nbsp;", " ")
        .replace("&amp;", "&")
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", '"')
    )
    return re.sub(r"[ \t\r\f\v]+", " ", html).strip()


def remove_files(stored_names):
    for s in stored_names:
        try:
            os.remove(os.path.join(UPLOAD_DIR, s))
        except OSError:
            pass


# --------------------------------------------------------------------------
# API logic
# --------------------------------------------------------------------------
def purge_pages(c, ids):
    if not ids:
        return
    q = ",".join("?" * len(ids))
    names = [r[0] for r in c.execute(f"SELECT stored FROM attachments WHERE page_id IN ({q})", ids)]
    c.execute(f"DELETE FROM pages WHERE id IN ({q})", ids)
    remove_files(names)


def page_subtree_ids(c, root_ids):
    """root_ids plus every descendant (sub-page, sub-sub-page, ...), each id once."""
    ids = list(dict.fromkeys(root_ids))
    frontier = list(ids)
    while frontier:
        q = ",".join("?" * len(frontier))
        kids = [r[0] for r in c.execute(f"SELECT id FROM pages WHERE parent_id IN ({q})", frontier)]
        kids = [k for k in kids if k not in ids]
        ids.extend(kids)
        frontier = kids
    return ids


def propagate_section(c, root_id, sid):
    """When root_id moves to section sid, carry every descendant along with it."""
    frontier = [root_id]
    while frontier:
        q = ",".join("?" * len(frontier))
        kids = [r[0] for r in c.execute(f"SELECT id FROM pages WHERE parent_id IN ({q})", frontier)]
        if kids:
            qk = ",".join("?" * len(kids))
            c.execute(f"UPDATE pages SET section_id=? WHERE id IN ({qk})", [sid] + kids)
        frontier = kids


def purge_sections(c, ids):
    for sid in ids:
        purge_pages(c, [r[0] for r in c.execute("SELECT id FROM pages WHERE section_id=?", (sid,))])
        c.execute("DELETE FROM sections WHERE id=?", (sid,))


def age_seconds(ts):
    try:
        return time.time() - time.mktime(time.strptime(ts, "%Y-%m-%d %H:%M:%S"))
    except Exception:
        return 1e9


def snapshot_version(c, pid, new_content, force=False):
    old = c.execute("SELECT title,content FROM pages WHERE id=?", (pid,)).fetchone()
    if not old or not old["content"].strip() or old["content"] == new_content:
        return
    last = c.execute("SELECT saved FROM page_versions WHERE page_id=? ORDER BY id DESC LIMIT 1", (pid,)).fetchone()
    if force or not last or age_seconds(last["saved"]) >= 300:
        c.execute("INSERT INTO page_versions(page_id,title,content,saved) VALUES(?,?,?,?)",
                  (pid, old["title"], old["content"], now()))
        c.execute("DELETE FROM page_versions WHERE page_id=? AND id NOT IN "
                  "(SELECT id FROM page_versions WHERE page_id=? ORDER BY id DESC LIMIT 30)", (pid, pid))


def clean_tags(raw):
    out = []
    for t in str(raw).replace("#", "").split(","):
        t = re.sub(r"\s+", " ", t).strip()[:30]
        if t and t.lower() not in [x.lower() for x in out]:
            out.append(t)
    return ",".join(out[:20])


def duplicate_page(c, pid, parent_id=None, root=True):
    p = c.execute("SELECT * FROM pages WHERE id=?", (pid,)).fetchone()
    if not p:
        return None
    target_parent = p["parent_id"] if root else parent_id
    pos = c.execute("SELECT COALESCE(MAX(position),0)+1 FROM pages WHERE section_id=? AND parent_id IS ?",
                    (p["section_id"], target_parent)).fetchone()[0]
    t = now()
    content = p["content"]
    title = (p["title"] + " (copy)")[:300] if root else p["title"]
    cur = c.execute("INSERT INTO pages(section_id,parent_id,title,content,position,created,updated,tags) VALUES(?,?,?,?,?,?,?,?)",
                    (p["section_id"], target_parent, title, "", pos, t, t, p["tags"]))
    nid = cur.lastrowid
    for a in c.execute("SELECT * FROM attachments WHERE page_id=?", (pid,)).fetchall():
        ext = os.path.splitext(a["stored"])[1]
        new = uuid.uuid4().hex + ext
        try:
            shutil.copyfile(os.path.join(UPLOAD_DIR, a["stored"]), os.path.join(UPLOAD_DIR, new))
        except OSError:
            continue
        c.execute("INSERT INTO attachments(page_id,name,stored,size,inline,created) VALUES(?,?,?,?,?,?)",
                  (nid, a["name"], new, a["size"], a["inline"], t))
        content = content.replace(a["stored"], new)
    mp = {}
    for st in c.execute("SELECT * FROM stickies WHERE page_id=?", (pid,)).fetchall():
        cur = c.execute("INSERT INTO stickies(page_id,text,color,x,y,w,h) VALUES(?,?,?,?,?,?,?)",
                        (nid, st["text"], st["color"], st["x"], st["y"], st["w"], st["h"]))
        mp["s%d" % st["id"]] = "s%d" % cur.lastrowid
        if st["anchor"]:
            c.execute("UPDATE stickies SET anchor=? WHERE id=?", ("s%d" % cur.lastrowid, cur.lastrowid))
    content = re.sub(r'data-anchor="([^"]*)"',
                     lambda m: 'data-anchor="%s"' % " ".join(mp.get(x, x) for x in m.group(1).split()), content)
    c.execute("UPDATE pages SET content=? WHERE id=?", (content, nid))
    for child in c.execute("SELECT id FROM pages WHERE parent_id=? ORDER BY position,id", (pid,)).fetchall():
        duplicate_page(c, child["id"], parent_id=nid, root=False)
    return nid


def check_public_url(url):
    u = urlparse(url)
    if u.scheme not in ("http", "https") or not u.hostname:
        raise ValueError("Only http(s) links are supported")
    if os.environ.get("NB_ALLOW_PRIVATE") == "1":
        return u
    try:
        infos = socket.getaddrinfo(u.hostname, u.port or (443 if u.scheme == "https" else 80))
    except OSError:
        raise ValueError("Cannot find that address")
    for i in infos:
        ip = ipaddress.ip_address(i[4][0])
        if ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_reserved or ip.is_multicast or ip.is_unspecified:
            raise ValueError("That address is not allowed")
    return u


class _SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        check_public_url(newurl)
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def http_get(url, limit, timeout=7):
    check_public_url(url)
    req = urllib.request.Request(url, headers={
        "User-Agent": "Mozilla/5.0 (compatible; StudyNotebook/1.0)", "Accept-Language": "en",
        "Accept": "text/html,application/xhtml+xml,image/*;q=0.8,*/*;q=0.5"})
    with urllib.request.build_opener(_SafeRedirect).open(req, timeout=timeout) as r:
        return r.read(limit + 1)[:limit], r.headers, r.geturl()


def youtube_id(url):
    u = urlparse(url)
    h = re.sub(r"^www\.", "", (u.hostname or "").lower())
    vid = None
    if h == "youtu.be":
        vid = u.path.strip("/").split("/")[0]
    elif h in ("youtube.com", "m.youtube.com", "music.youtube.com", "youtube-nocookie.com"):
        if u.path == "/watch":
            vid = (parse_qs(u.query).get("v") or [None])[0]
        else:
            m = re.match(r"^/(?:shorts|embed|live|v)/([\w-]{6,20})", u.path)
            vid = m.group(1) if m else None
    return vid if vid and re.fullmatch(r"[\w-]{6,20}", vid) else None


def meta_content(doc, names):
    for n in names:
        e = re.escape(n)
        for pat in (r'<meta[^>]+(?:property|name)=["\']' + e + r'["\'][^>]*content=["\']([^"\']*)["\']',
                    r'<meta[^>]+content=["\']([^"\']*)["\'][^>]*(?:property|name)=["\']' + e + r'["\']'):
            m = re.search(pat, doc, re.I)
            if m and m.group(1).strip():
                return htmllib.unescape(m.group(1)).strip()
    return ""


def save_thumb(c, page_id, img_url):
    try:
        data, hdr, _ = http_get(img_url, 3 * 1024 * 1024)
    except Exception:
        return ""
    ext = {"image/jpeg": ".jpg", "image/png": ".png", "image/webp": ".webp", "image/gif": ".gif"}.get(hdr.get_content_type())
    if not ext or len(data) < 200:
        return ""
    stored = uuid.uuid4().hex + ext
    with open(os.path.join(UPLOAD_DIR, stored), "wb") as f:
        f.write(data)
    c.execute("INSERT INTO attachments(page_id,name,stored,size,inline,created) VALUES(?,?,?,?,?,?)",
              (page_id, "link-thumbnail" + ext, stored, len(data), 1, now()))
    return "/files/" + stored


def link_card(c, page_id, url):
    check_public_url(url)
    host = re.sub(r"^www\.", "", urlparse(url).hostname or "")
    vid = youtube_id(url)
    if vid:
        title, author, thumb_url = "YouTube video", "", "https://i.ytimg.com/vi/%s/hqdefault.jpg" % vid
        try:
            data, _, _ = http_get("https://www.youtube.com/oembed?format=json&url=" + quote(url, safe=""), 200000, 6)
            j = json.loads(data.decode("utf-8", "replace"))
            title, author, thumb_url = j.get("title") or title, j.get("author_name") or "", j.get("thumbnail_url") or thumb_url
        except Exception:
            pass
        return {"kind": "youtube", "video_id": vid, "url": url, "title": title,
                "site": "YouTube" + (" · " + author if author else ""), "description": "",
                "thumb": save_thumb(c, page_id, thumb_url)}
    data, hdr, final = http_get(url, 400 * 1024)
    ct = hdr.get_content_type() or ""
    if ct.startswith("image/"):
        return {"kind": "web", "video_id": "", "url": url, "title": os.path.basename(urlparse(url).path) or host,
                "site": host, "description": "", "thumb": save_thumb(c, page_id, url)}
    cs = hdr.get_content_charset()
    if not cs:
        m = re.search(rb'<meta[^>]+charset=["\']?([\w-]+)', data[:4096], re.I)
        cs = m.group(1).decode("ascii", "ignore") if m else "utf-8"
    try:
        doc = data.decode(cs, "replace")
    except LookupError:
        doc = data.decode("utf-8", "replace")
    title = meta_content(doc, ["og:title", "twitter:title"])
    if not title:
        m = re.search(r"<title[^>]*>(.*?)</title>", doc, re.I | re.S)
        title = htmllib.unescape(re.sub(r"\s+", " ", m.group(1))).strip() if m else ""
    desc = meta_content(doc, ["og:description", "twitter:description", "description"])
    img = meta_content(doc, ["og:image", "twitter:image"])
    site = meta_content(doc, ["og:site_name"]) or host
    return {"kind": "web", "video_id": "", "url": url, "title": (title or host)[:200], "site": site[:80],
            "description": desc[:240], "thumb": save_thumb(c, page_id, urljoin(final, img)) if img else ""}


def today_str(offset_days=0):
    return time.strftime("%Y-%m-%d", time.localtime(time.time() + offset_days * 86400))


def review_card(c, cid, grade):
    r = c.execute("SELECT * FROM flashcards WHERE id=?", (cid,)).fetchone()
    if not r:
        return None
    ease, interval, reps = r["ease"], r["interval"], r["reps"]
    if grade <= 0:
        reps, interval, ease = 0, 0, max(1.3, ease - 0.2)
    elif grade == 1:
        reps += 1
        interval, ease = max(1, round(max(interval, 1) * 1.2)), max(1.3, ease - 0.15)
    elif grade == 2:
        reps += 1
        interval = 1 if reps == 1 else (3 if reps == 2 else max(1, round(interval * ease)))
    else:
        reps += 1
        interval = 4 if reps == 1 else max(4, round(max(interval, 1) * ease * 1.3))
        ease += 0.15
    due = today_str(interval)
    c.execute("UPDATE flashcards SET due=?, interval=?, ease=?, reps=? WHERE id=?", (due, interval, ease, reps, cid))
    return dict(c.execute("SELECT * FROM flashcards WHERE id=?", (cid,)).fetchone())


def study_stats(c):
    days = []
    for i in range(6, -1, -1):
        d = today_str(-i)
        n = c.execute("SELECT COALESCE(SUM(seconds),0) FROM study_log WHERE day=?", (d,)).fetchone()[0]
        days.append({"day": d, "seconds": n})
    since = today_str(-6)
    secs = rows(c.execute("SELECT COALESCE(s.title,'Other') AS title, SUM(l.seconds) AS seconds FROM study_log l "
                          "LEFT JOIN sections s ON s.id=l.section_id WHERE l.day>=? GROUP BY l.section_id ORDER BY 2 DESC", (since,)))
    return {"today": days[-1]["seconds"], "week": sum(d["seconds"] for d in days), "days": days, "sections": secs}


def nest_pages(flat_pages):
    by_parent = {}
    for p in flat_pages:
        by_parent.setdefault(p["parent_id"], []).append(p)

    def build(pid):
        kids = by_parent.get(pid, [])
        for k in kids:
            k["children"] = build(k["id"])
        return kids

    return build(None)


def api_tree(c):
    secs = rows(c.execute("SELECT id,title,color FROM sections WHERE deleted_at='' ORDER BY position,id"))
    pages = rows(c.execute("SELECT id,section_id,parent_id,title,fav,tags FROM pages WHERE deleted_at='' ORDER BY position,id"))
    for s in secs:
        sec_pages = [{"id": p["id"], "title": p["title"], "fav": p["fav"], "tags": p["tags"], "parent_id": p["parent_id"]}
                    for p in pages if p["section_id"] == s["id"]]
        s["pages"] = nest_pages(sec_pages)
    return secs


def page_ancestors(c, pid):
    out = []
    seen = set()
    row = c.execute("SELECT parent_id FROM pages WHERE id=?", (pid,)).fetchone()
    nxt = row["parent_id"] if row else None
    while nxt and nxt not in seen:
        seen.add(nxt)
        row = c.execute("SELECT id,title,parent_id FROM pages WHERE id=?", (nxt,)).fetchone()
        if not row:
            break
        out.append({"id": row["id"], "title": row["title"]})
        nxt = row["parent_id"]
    out.reverse()
    return out


def api_get_page(c, pid):
    p = c.execute("SELECT * FROM pages WHERE id=?", (pid,)).fetchone()
    if not p:
        return None
    p = dict(p)
    sec = c.execute("SELECT title FROM sections WHERE id=?", (p["section_id"],)).fetchone()
    atts = rows(
        c.execute(
            "SELECT id,name,stored,size FROM attachments WHERE page_id=? AND inline=0 ORDER BY id", (pid,)
        )
    )
    st = rows(c.execute("SELECT * FROM stickies WHERE page_id=? ORDER BY id", (pid,)))
    back = rows(c.execute("SELECT id,title FROM pages WHERE deleted_at='' AND id!=? AND content LIKE ?",
                          (pid, '%data-page="' + str(pid) + '"%')))
    return {"page": p, "section_title": sec["title"] if sec else "", "attachments": atts, "stickies": st,
            "backlinks": back, "ancestors": page_ancestors(c, pid)}


def api_search(c, q):
    words = [w.lower() for w in q.split() if w.strip()]
    if not words:
        return []
    out = []
    pages = rows(
        c.execute(
            "SELECT p.id,p.title,p.content,p.tags,s.title AS section FROM pages p "
            "JOIN sections s ON s.id=p.section_id WHERE p.deleted_at='' AND s.deleted_at='' ORDER BY s.position,p.position,p.id"
        )
    )
    atts = {}
    for a in c.execute("SELECT page_id,name FROM attachments WHERE inline=0"):
        atts.setdefault(a["page_id"], []).append(a["name"])
    stk = {}
    for s in c.execute("SELECT page_id,text FROM stickies"):
        stk.setdefault(s["page_id"], []).append(s["text"])
    for p in pages:
        body = strip_tags(p["content"])
        extra_att = " ".join(atts.get(p["id"], []))
        extra_stk = " ".join(stk.get(p["id"], []))
        hay = " \n ".join([p["section"], p["title"], p["tags"].replace(",", " "), body, extra_att, extra_stk]).lower()
        if all(w in hay for w in words):
            # snippet: look in body, then stickies, then attachments
            snippet = ""
            for source in (body, extra_stk, extra_att):
                low = source.lower()
                idx = low.find(words[0])
                if idx >= 0:
                    a = max(0, idx - 40)
                    snippet = ("…" if a else "") + source[a : idx + 100].replace("\n", " ")
                    break
            if not snippet:
                snippet = body[:100].replace("\n", " ")
            out.append(
                {"id": p["id"], "title": p["title"], "section": p["section"], "snippet": snippet}
            )
    return out


# --------------------------------------------------------------------------
# Telegram backup
# --------------------------------------------------------------------------
CONFIG_PATH = os.path.join(DATA_DIR, "config.json")
CFG_LOCK = threading.Lock()
BACKUP_LOCK = threading.Lock()
TG_CHUNK = 45 * 1024 * 1024  # Telegram bots may upload up to 50 MB per file
_last_check = [0.0]

DEFAULT_CFG = {
    "enabled": False,
    "token": "",
    "chat_id": "",
    "interval_hours": 6.0,
    "last_backup_ts": 0,
    "last_status": "",
    "last_fingerprint": "",
}


def load_cfg():
    cfg = dict(DEFAULT_CFG)
    try:
        with open(CONFIG_PATH, encoding="utf-8") as f:
            cfg.update(json.load(f))
    except (OSError, ValueError):
        pass
    return cfg


def save_cfg(cfg):
    with CFG_LOCK:
        tmp = CONFIG_PATH + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cfg, f, indent=2)
        try:
            os.chmod(tmp, 0o600)  # the bot token is a secret
        except OSError:
            pass
        os.replace(tmp, CONFIG_PATH)


def public_cfg(cfg):
    t = cfg.get("token", "")
    masked = ""
    if t:
        masked = (t.split(":")[0] + ":\u2022\u2022\u2022\u2022" + t[-4:]) if ":" in t else "\u2022\u2022\u2022\u2022"
    last = cfg.get("last_backup_ts") or 0
    return {
        "enabled": bool(cfg["enabled"]),
        "token_masked": masked,
        "has_token": bool(t),
        "chat_id": cfg.get("chat_id", ""),
        "interval_hours": cfg.get("interval_hours", 6),
        "last_backup": time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(last)) if last else "",
        "last_status": cfg.get("last_status", ""),
    }


def data_fingerprint():
    """Changes whenever the database or an uploaded file changes."""
    h = hashlib.sha1()
    try:
        st = os.stat(DB_PATH)
        h.update(f"db:{st.st_mtime_ns}:{st.st_size}".encode())
    except OSError:
        pass
    for n in sorted(os.listdir(UPLOAD_DIR)):
        try:
            h.update(f"{n}:{os.path.getsize(os.path.join(UPLOAD_DIR, n))}".encode())
        except OSError:
            pass
    return h.hexdigest()


def make_backup_zip():
    """Consistent snapshot of the database + all uploads in a zip (config/token is NOT included)."""
    fd, zpath = tempfile.mkstemp(suffix=".zip")
    os.close(fd)
    tmpdir = tempfile.mkdtemp()
    try:
        snap = os.path.join(tmpdir, "notebook.db")
        src = sqlite3.connect(DB_PATH)
        dst = sqlite3.connect(snap)
        try:
            src.backup(dst)
        finally:
            dst.close()
            src.close()
        with zipfile.ZipFile(zpath, "w", zipfile.ZIP_DEFLATED) as z:
            z.write(snap, "notebook.db")
            for n in sorted(os.listdir(UPLOAD_DIR)):
                z.write(os.path.join(UPLOAD_DIR, n), "uploads/" + n)
    except Exception:
        os.remove(zpath)
        raise
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)
    return zpath


def tg_call(token, method, fields, file=None, timeout=180):
    base = os.environ.get("TELEGRAM_API", "https://api.telegram.org").rstrip("/")
    url = f"{base}/bot{token}/{method}"
    if file:
        boundary = "----nb" + uuid.uuid4().hex
        parts = []
        for k, v in fields.items():
            parts.append(
                f'--{boundary}\r\nContent-Disposition: form-data; name="{k}"\r\n\r\n{v}\r\n'.encode("utf-8")
            )
        fname, data = file
        parts.append(
            (
                f'--{boundary}\r\nContent-Disposition: form-data; name="document"; filename="{fname}"\r\n'
                "Content-Type: application/octet-stream\r\n\r\n"
            ).encode("utf-8")
        )
        parts.append(data)
        parts.append(f"\r\n--{boundary}--\r\n".encode())
        body = b"".join(parts)
        ctype = f"multipart/form-data; boundary={boundary}"
    else:
        body = json.dumps(fields).encode("utf-8")
        ctype = "application/json"
    req = urllib.request.Request(url, data=body, headers={"Content-Type": ctype}, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            resp = json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        try:
            resp = json.loads(e.read().decode("utf-8"))
        except Exception:
            resp = {"ok": False, "description": f"HTTP {e.code}"}
    except Exception as e:
        raise RuntimeError("Cannot reach Telegram: " + str(e).replace(token, "***"))
    if not resp.get("ok"):
        raise RuntimeError(str(resp.get("description", "Telegram error")).replace(token, "***"))
    return resp


def human(n):
    for u in ("B", "KB", "MB", "GB"):
        if n < 1024 or u == "GB":
            return f"{n:.0f} {u}" if u == "B" else f"{n:.1f} {u}"
        n /= 1024


def run_backup(force=False):
    if not BACKUP_LOCK.acquire(blocking=False):
        return {"ok": False, "message": "A backup is already running"}
    try:
        cfg = load_cfg()
        if not cfg["token"] or not cfg["chat_id"]:
            return {"ok": False, "message": "Set the bot token and chat ID first"}
        fp = data_fingerprint()
        stamp = time.strftime("%Y-%m-%d %H:%M:%S")
        if not force and fp == cfg.get("last_fingerprint"):
            c2 = load_cfg()
            c2["last_status"] = f"No changes since last backup (checked {stamp})"
            save_cfg(c2)
            return {"ok": True, "skipped": True, "message": c2["last_status"]}
        zpath = None
        try:
            zpath = make_backup_zip()
            size = os.path.getsize(zpath)
            base = "study_notebook_backup_" + time.strftime("%Y%m%d_%H%M%S")
            note = f"\U0001F4DA Codex backup\n{stamp} \u00b7 {human(size)}"
            if size <= TG_CHUNK:
                with open(zpath, "rb") as f:
                    tg_call(cfg["token"], "sendDocument", {"chat_id": cfg["chat_id"], "caption": note},
                            file=(base + ".zip", f.read()))
                sent = "1 file"
            else:
                n = 0
                with open(zpath, "rb") as f:
                    while True:
                        chunk = f.read(TG_CHUNK)
                        if not chunk:
                            break
                        n += 1
                        cap = note + f"\nPart {n} - join all parts with:  cat {base}.zip.* > {base}.zip"
                        tg_call(cfg["token"], "sendDocument", {"chat_id": cfg["chat_id"], "caption": cap},
                                file=(f"{base}.zip.{n:03d}", chunk))
                sent = f"{n} parts"
            c2 = load_cfg()
            c2.update(last_backup_ts=int(time.time()), last_fingerprint=fp,
                      last_status=f"Backup sent {stamp} ({human(size)}, {sent})")
            save_cfg(c2)
            return {"ok": True, "message": c2["last_status"]}
        except Exception as e:
            c2 = load_cfg()
            c2["last_status"] = f"Failed {stamp}: {e}"
            save_cfg(c2)
            return {"ok": False, "message": c2["last_status"]}
        finally:
            if zpath and os.path.exists(zpath):
                os.remove(zpath)
    finally:
        BACKUP_LOCK.release()


def backup_loop():
    time.sleep(20)
    while True:
        try:
            cfg = load_cfg()
            if cfg["enabled"] and cfg["token"] and cfg["chat_id"]:
                iv = max(0.25, float(cfg["interval_hours"])) * 3600
                last = max(cfg.get("last_backup_ts") or 0, _last_check[0])
                if time.time() - last >= iv:
                    res = run_backup(False)
                    _last_check[0] = time.time() if res.get("ok") else time.time() - iv + 600  # retry in 10 min
        except Exception:
            pass
        time.sleep(60)


def backup_api(handler, method, path):
    """Returns True when the request was handled."""
    if method == "GET" and path == "/api/backup/config":
        handler.send_json(public_cfg(load_cfg()))
        return True
    if method == "PUT" and path == "/api/backup/config":
        d = handler.read_json()
        cfg = load_cfg()
        tok = (d.get("token") or "").strip()
        if tok and "\u2022" not in tok:
            cfg["token"] = tok
        if d.get("clear_token"):
            cfg["token"] = ""
        if "chat_id" in d:
            cfg["chat_id"] = str(d["chat_id"]).strip()
        if "interval_hours" in d:
            cfg["interval_hours"] = min(168.0, max(0.25, float(d["interval_hours"])))
        if "enabled" in d:
            cfg["enabled"] = bool(d["enabled"])
        save_cfg(cfg)
        handler.send_json(public_cfg(cfg))
        return True
    if method == "POST" and path == "/api/backup/test":
        cfg = load_cfg()
        try:
            if not cfg["token"] or not cfg["chat_id"]:
                raise RuntimeError("Set the bot token and chat ID first")
            tg_call(cfg["token"], "sendMessage",
                    {"chat_id": cfg["chat_id"], "text": "\u2705 Codex is connected. Backups will arrive here."})
            handler.send_json({"ok": True, "message": "Test message sent - check Telegram"})
        except Exception as e:
            handler.send_json({"ok": False, "message": str(e)})
        return True
    if method == "POST" and path == "/api/backup/detect":
        cfg = load_cfg()
        try:
            if not cfg["token"]:
                raise RuntimeError("Save the bot token first")
            resp = tg_call(cfg["token"], "getUpdates", {"limit": 30, "timeout": 0}, timeout=30)
            chat = None
            for u in reversed(resp.get("result", [])):
                m = (u.get("message") or u.get("edited_message") or u.get("channel_post")
                     or u.get("my_chat_member") or {})
                if m.get("chat"):
                    chat = m["chat"]
                    break
            if not chat:
                raise RuntimeError("No messages found. Open your bot in Telegram, press Start / send it any message, then try again")
            cfg["chat_id"] = str(chat["id"])
            save_cfg(cfg)
            name = chat.get("title") or chat.get("username") or chat.get("first_name") or ""
            handler.send_json({"ok": True, "chat_id": cfg["chat_id"], "message": f"Found chat: {name} ({cfg['chat_id']})"})
        except Exception as e:
            handler.send_json({"ok": False, "message": str(e)})
        return True
    if method == "POST" and path == "/api/backup/run":
        handler.send_json(run_backup(force=True))
        return True
    if method == "GET" and path == "/api/backup/download":
        z = make_backup_zip()
        try:
            with open(z, "rb") as f:
                data = f.read()
        finally:
            os.remove(z)
        name = "study_notebook_backup_" + time.strftime("%Y%m%d_%H%M%S") + ".zip"
        handler.send_bytes(200, data, "application/zip",
                           {"Content-Disposition": f'attachment; filename="{name}"'})
        return True
    return False


class Handler(BaseHTTPRequestHandler):
    server_version = "StudyNotebook/1.0"
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):  # quiet
        pass

    # ---- helpers ----
    def send_bytes(self, code, data, ctype, extra=None):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)

    def send_json(self, obj, code=200):
        self.send_bytes(code, json.dumps(obj).encode("utf-8"), "application/json; charset=utf-8")

    def read_body(self):
        n = int(self.headers.get("Content-Length") or 0)
        if n > MAX_UPLOAD:
            raise ValueError("File too large")
        buf = bytearray()
        while len(buf) < n:
            chunk = self.rfile.read(min(1 << 20, n - len(buf)))
            if not chunk:
                break
            buf.extend(chunk)
        return bytes(buf)

    def read_json(self):
        raw = self.read_body()
        return json.loads(raw.decode("utf-8")) if raw else {}

    # ---- dispatch ----
    def do_GET(self):
        self.route("GET")

    def do_POST(self):
        self.route("POST")

    def do_PUT(self):
        self.route("PUT")

    def do_DELETE(self):
        self.route("DELETE")

    def route(self, method):
        try:
            u = urlparse(self.path)
            path = u.path
            qs = parse_qs(u.query)

            if method == "GET" and path == "/":
                return self.send_bytes(200, INDEX_HTML.encode("utf-8"), "text/html; charset=utf-8")

            m = re.fullmatch(r"/files/([0-9a-f]{32}(?:\.[A-Za-z0-9]{1,10})?)", path)
            if method == "GET" and m:
                return self.serve_file(m.group(1), "dl" in qs)

            if not path.startswith("/api/"):
                return self.send_json({"error": "not found"}, 404)

            if path.startswith("/api/backup/") and backup_api(self, method, path):
                return

            with db() as c:
                # ----- tree & search -----
                if method == "GET" and path == "/api/tree":
                    return self.send_json(api_tree(c))
                if method == "GET" and path == "/api/search":
                    return self.send_json(api_search(c, (qs.get("q") or [""])[0]))

                m = re.fullmatch(r"/api/pages/(\d+)/linkcard", path)
                if method == "POST" and m:
                    url = (self.read_json().get("url") or "").strip()
                    if url and not re.match(r"^https?://", url, re.I):
                        url = "https://" + url
                    try:
                        return self.send_json(link_card(c, int(m.group(1)), url))
                    except ValueError as e:
                        return self.send_json({"error": str(e)}, 400)
                    except Exception as e:
                        return self.send_json({"error": "Could not read that link: " + str(e)[:120]}, 502)
                # ----- flashcards / tasks / study log -----
                if method == "GET" and path == "/api/cards":
                    return self.send_json(rows(c.execute(
                        "SELECT f.*, p.title AS page_title FROM flashcards f JOIN pages p ON p.id=f.page_id "
                        "WHERE p.deleted_at='' ORDER BY f.due, f.id")))
                if method == "GET" and path == "/api/cards/stats":
                    tot = c.execute("SELECT COUNT(*) FROM flashcards f JOIN pages p ON p.id=f.page_id WHERE p.deleted_at=''").fetchone()[0]
                    due = c.execute("SELECT COUNT(*) FROM flashcards f JOIN pages p ON p.id=f.page_id "
                                    "WHERE p.deleted_at='' AND f.due<=?", (today_str(),)).fetchone()[0]
                    return self.send_json({"total": tot, "due": due})
                m = re.fullmatch(r"/api/pages/(\d+)/cards", path)
                if method == "POST" and m:
                    d = self.read_json()
                    front, back = (d.get("front") or "").strip(), (d.get("back") or "").strip()
                    if not front:
                        return self.send_json({"error": "Front is empty"}, 400)
                    cur = c.execute("INSERT INTO flashcards(page_id,front,back,due,created) VALUES(?,?,?,?,?)",
                                    (int(m.group(1)), front[:2000], back[:4000], today_str(), now()))
                    return self.send_json({"id": cur.lastrowid})
                m = re.fullmatch(r"/api/cards/(\d+)", path)
                if m:
                    cid = int(m.group(1))
                    if method == "PUT":
                        d = self.read_json()
                        for k, lim in (("front", 2000), ("back", 4000)):
                            if k in d:
                                c.execute(f"UPDATE flashcards SET {k}=? WHERE id=?", (str(d[k]).strip()[:lim], cid))
                        if "page_id" in d:
                            c.execute("UPDATE flashcards SET page_id=? WHERE id=?", (int(d["page_id"]), cid))
                        return self.send_json({"ok": True})
                    if method == "DELETE":
                        c.execute("DELETE FROM flashcards WHERE id=?", (cid,))
                        return self.send_json({"ok": True})
                m = re.fullmatch(r"/api/cards/(\d+)/review", path)
                if method == "POST" and m:
                    r = review_card(c, int(m.group(1)), int(self.read_json().get("grade", 2)))
                    return self.send_json(r if r else {"error": "not found"}, 200 if r else 404)
                if method == "GET" and path == "/api/tasks":
                    return self.send_json(rows(c.execute("SELECT * FROM tasks ORDER BY done, due='', due, id")))
                if method == "POST" and path == "/api/tasks":
                    d = self.read_json()
                    kind = "exam" if d.get("kind") == "exam" else "todo"
                    text = (d.get("text") or "").strip()[:300]
                    if not text:
                        return self.send_json({"error": "Text is empty"}, 400)
                    due = d.get("due") or ""
                    due = due if re.fullmatch(r"\d{4}-\d{2}-\d{2}", due) else ""
                    cur = c.execute("INSERT INTO tasks(kind,text,due,created) VALUES(?,?,?,?)", (kind, text, due, now()))
                    return self.send_json({"id": cur.lastrowid})
                m = re.fullmatch(r"/api/tasks/(\d+)", path)
                if m:
                    tid = int(m.group(1))
                    if method == "PUT":
                        d = self.read_json()
                        if "text" in d and str(d["text"]).strip():
                            c.execute("UPDATE tasks SET text=? WHERE id=?", (str(d["text"]).strip()[:300], tid))
                        if "due" in d:
                            due = d["due"] if re.fullmatch(r"\d{4}-\d{2}-\d{2}", str(d["due"])) else ""
                            c.execute("UPDATE tasks SET due=? WHERE id=?", (due, tid))
                        if "done" in d:
                            c.execute("UPDATE tasks SET done=? WHERE id=?", (1 if d["done"] else 0, tid))
                        return self.send_json({"ok": True})
                    if method == "DELETE":
                        c.execute("DELETE FROM tasks WHERE id=?", (tid,))
                        return self.send_json({"ok": True})
                if method == "POST" and path == "/api/study":
                    d = self.read_json()
                    secs = max(0, min(int(d.get("seconds", 0)), 6 * 3600))
                    sid = d.get("section_id")
                    c.execute("INSERT INTO study_log(section_id,day,seconds) VALUES(?,?,?)",
                              (int(sid) if sid is not None else None, today_str(), secs))
                    return self.send_json({"ok": True})
                if method == "GET" and path == "/api/study/stats":
                    return self.send_json(study_stats(c))

                # ----- trash / restore / duplicate / history -----
                if method == "GET" and path == "/api/trash":
                    pg = rows(c.execute("SELECT p.id,p.title,p.deleted_at,p.parent_id,s.title AS section FROM pages p JOIN sections s "
                                        "ON s.id=p.section_id WHERE p.deleted_at!='' AND s.deleted_at='' ORDER BY p.deleted_at DESC"))
                    sc = rows(c.execute("SELECT s.id,s.title,s.deleted_at,(SELECT COUNT(*) FROM pages p WHERE p.section_id=s.id) AS n "
                                        "FROM sections s WHERE s.deleted_at!='' ORDER BY s.deleted_at DESC"))
                    return self.send_json({"pages": pg, "sections": sc})
                if method == "DELETE" and path == "/api/trash":
                    purge_pages(c, [r[0] for r in c.execute("SELECT id FROM pages WHERE deleted_at!=''")])
                    purge_sections(c, [r[0] for r in c.execute("SELECT id FROM sections WHERE deleted_at!=''")])
                    return self.send_json({"ok": True})
                m = re.fullmatch(r"/api/(pages|sections)/(\d+)/restore", path)
                if method == "POST" and m:
                    rid = int(m.group(2))
                    if m.group(1) == "sections":
                        c.execute("UPDATE sections SET deleted_at='' WHERE id=?", (rid,))
                    else:
                        ids = page_subtree_ids(c, [rid])
                        q = ",".join("?" * len(ids))
                        c.execute(f"UPDATE pages SET deleted_at='' WHERE id IN ({q})", ids)
                        c.execute("UPDATE sections SET deleted_at='' WHERE id=(SELECT section_id FROM pages WHERE id=?)", (rid,))
                    return self.send_json({"ok": True})
                m = re.fullmatch(r"/api/pages/(\d+)/duplicate", path)
                if method == "POST" and m:
                    nid = duplicate_page(c, int(m.group(1)))
                    return self.send_json({"id": nid} if nid else {"error": "not found"}, 200 if nid else 404)
                m = re.fullmatch(r"/api/pages/(\d+)/versions", path)
                if method == "GET" and m:
                    out = []
                    for v in c.execute("SELECT id,saved,title,content FROM page_versions WHERE page_id=? ORDER BY id DESC", (int(m.group(1)),)):
                        out.append({"id": v["id"], "saved": v["saved"], "title": v["title"], "snippet": strip_tags(v["content"])[:100]})
                    return self.send_json(out)
                m = re.fullmatch(r"/api/versions/(\d+)", path)
                if method == "GET" and m:
                    v = c.execute("SELECT * FROM page_versions WHERE id=?", (int(m.group(1)),)).fetchone()
                    return self.send_json(dict(v) if v else {"error": "not found"}, 200 if v else 404)
                m = re.fullmatch(r"/api/versions/(\d+)/restore", path)
                if method == "POST" and m:
                    v = c.execute("SELECT * FROM page_versions WHERE id=?", (int(m.group(1)),)).fetchone()
                    if not v:
                        return self.send_json({"error": "not found"}, 404)
                    snapshot_version(c, v["page_id"], v["content"], force=True)
                    c.execute("UPDATE pages SET title=?, content=?, updated=? WHERE id=?",
                              (v["title"], v["content"], now(), v["page_id"]))
                    return self.send_json({"ok": True})

                # ----- sections -----
                if method == "POST" and path == "/api/sections":
                    d = self.read_json()
                    pos = c.execute("SELECT COALESCE(MAX(position),0)+1 FROM sections").fetchone()[0]
                    cur = c.execute(
                        "INSERT INTO sections(title,position,created) VALUES(?,?,?)",
                        ((d.get("title") or "New header").strip()[:200], pos, now()),
                    )
                    return self.send_json({"id": cur.lastrowid})
                m = re.fullmatch(r"/api/sections/(\d+)", path)
                if m:
                    sid = int(m.group(1))
                    if method == "PUT":
                        d = self.read_json()
                        if "title" in d:
                            c.execute(
                                "UPDATE sections SET title=? WHERE id=?",
                                ((d["title"].strip() or "Untitled")[:200], sid),
                            )
                        if re.fullmatch(r"#[0-9a-fA-F]{6}", str(d.get("color", ""))):
                            c.execute("UPDATE sections SET color=? WHERE id=?", (d["color"], sid))
                        return self.send_json({"ok": True})
                    if method == "DELETE":
                        if (qs.get("purge") or ["0"])[0] == "1":
                            purge_sections(c, [sid])
                        else:
                            c.execute("UPDATE sections SET deleted_at=? WHERE id=?", (now(), sid))
                        return self.send_json({"ok": True})

                # ----- pages -----
                if method == "POST" and path == "/api/pages":
                    d = self.read_json()
                    parent_id = d.get("parent_id")
                    if parent_id:
                        parent_id = int(parent_id)
                        pr = c.execute("SELECT section_id FROM pages WHERE id=? AND deleted_at=''", (parent_id,)).fetchone()
                        if not pr:
                            return self.send_json({"error": "parent page not found"}, 404)
                        sid = pr["section_id"]
                    else:
                        parent_id = None
                        sid = int(d["section_id"])
                    pos = c.execute(
                        "SELECT COALESCE(MAX(position),0)+1 FROM pages WHERE section_id=? AND parent_id IS ?", (sid, parent_id)
                    ).fetchone()[0]
                    t = now()
                    cur = c.execute(
                        "INSERT INTO pages(section_id,parent_id,title,content,position,created,updated) "
                        "VALUES(?,?,?,?,?,?,?)",
                        (sid, parent_id, (d.get("title") or "Untitled page")[:300], "", pos, t, t),
                    )
                    return self.send_json({"id": cur.lastrowid})
                m = re.fullmatch(r"/api/pages/(\d+)", path)
                if m:
                    pid = int(m.group(1))
                    if method == "GET":
                        r = api_get_page(c, pid)
                        return self.send_json(r if r else {"error": "not found"}, 200 if r else 404)
                    if method == "PUT":
                        d = self.read_json()
                        if "title" in d:
                            c.execute(
                                "UPDATE pages SET title=? WHERE id=?",
                                ((d["title"].strip() or "Untitled page")[:300], pid),
                            )
                        if "content" in d:
                            snapshot_version(c, pid, d["content"])
                            c.execute("UPDATE pages SET content=? WHERE id=?", (d["content"], pid))
                        if "tags" in d:
                            c.execute("UPDATE pages SET tags=? WHERE id=?", (clean_tags(d["tags"]), pid))
                        if "fav" in d:
                            c.execute("UPDATE pages SET fav=? WHERE id=?", (1 if d["fav"] else 0, pid))
                        if "parent_id" in d or "section_id" in d:
                            if "parent_id" in d:
                                newp = d["parent_id"]
                                newp = int(newp) if newp not in (None, "", 0, "0") else None
                                if newp == pid:
                                    return self.send_json({"error": "a page can't be a sub-page of itself"}, 400)
                                if newp is not None:
                                    if newp in page_subtree_ids(c, [pid]):
                                        return self.send_json({"error": "can't move a page under its own sub-page"}, 400)
                                    pr = c.execute("SELECT section_id FROM pages WHERE id=? AND deleted_at=''", (newp,)).fetchone()
                                    if not pr:
                                        return self.send_json({"error": "target page not found"}, 404)
                                    target_section = pr["section_id"]
                                else:
                                    cur_row = c.execute("SELECT section_id FROM pages WHERE id=?", (pid,)).fetchone()
                                    target_section = int(d["section_id"]) if d.get("section_id") else cur_row["section_id"]
                            else:
                                newp = None
                                target_section = int(d["section_id"])
                            pos = c.execute(
                                "SELECT COALESCE(MAX(position),0)+1 FROM pages WHERE section_id=? AND parent_id IS ?",
                                (target_section, newp)
                            ).fetchone()[0]
                            c.execute(
                                "UPDATE pages SET parent_id=?, section_id=?, position=? WHERE id=?",
                                (newp, target_section, pos, pid)
                            )
                            propagate_section(c, pid, target_section)
                        c.execute("UPDATE pages SET updated=? WHERE id=?", (now(), pid))
                        tg = c.execute("SELECT tags FROM pages WHERE id=?", (pid,)).fetchone()
                        return self.send_json({"ok": True, "updated": now(), "tags": tg[0] if tg else ""})
                    if method == "DELETE":
                        ids = page_subtree_ids(c, [pid])
                        if (qs.get("purge") or ["0"])[0] == "1":
                            purge_pages(c, ids)
                        else:
                            q = ",".join("?" * len(ids))
                            c.execute(f"UPDATE pages SET deleted_at=? WHERE id IN ({q})", [now()] + ids)
                        return self.send_json({"ok": True})

                m = re.fullmatch(r"/api/pages/(\d+)/move", path)
                if method == "POST" and m:  # reorder: {"dir": -1|1}
                    pid = int(m.group(1))
                    d = self.read_json()
                    p = c.execute("SELECT id,section_id,parent_id FROM pages WHERE id=?", (pid,)).fetchone()
                    if p:
                        lst = [
                            r[0]
                            for r in c.execute(
                                "SELECT id FROM pages WHERE section_id=? AND parent_id IS ? AND deleted_at='' ORDER BY position,id",
                                (p["section_id"], p["parent_id"]),
                            )
                        ]
                        i = lst.index(pid)
                        j = i + (1 if int(d.get("dir", 1)) > 0 else -1)
                        if 0 <= j < len(lst):
                            lst[i], lst[j] = lst[j], lst[i]
                            for n, x in enumerate(lst, 1):
                                c.execute("UPDATE pages SET position=? WHERE id=?", (n, x))
                    return self.send_json({"ok": True})

                m = re.fullmatch(r"/api/sections/(\d+)/move", path)
                if method == "POST" and m:
                    sid = int(m.group(1))
                    d = self.read_json()
                    lst = [r[0] for r in c.execute("SELECT id FROM sections WHERE deleted_at='' ORDER BY position,id")]
                    if sid in lst:
                        i = lst.index(sid)
                        j = i + (1 if int(d.get("dir", 1)) > 0 else -1)
                        if 0 <= j < len(lst):
                            lst[i], lst[j] = lst[j], lst[i]
                            for n, x in enumerate(lst, 1):
                                c.execute("UPDATE sections SET position=? WHERE id=?", (n, x))
                    return self.send_json({"ok": True})

                # ----- uploads (raw body) -----
                m = re.fullmatch(r"/api/pages/(\d+)/upload", path)
                if method == "POST" and m:
                    pid = int(m.group(1))
                    if not c.execute("SELECT 1 FROM pages WHERE id=?", (pid,)).fetchone():
                        return self.send_json({"error": "page not found"}, 404)
                    name = os.path.basename((qs.get("name") or ["file"])[0]) or "file"
                    inline = 1 if (qs.get("inline") or ["0"])[0] == "1" else 0
                    data = self.read_body()
                    ext = os.path.splitext(name)[1].lower()
                    if not re.fullmatch(r"\.[a-z0-9]{1,10}", ext):
                        ext = ""
                    stored = uuid.uuid4().hex + ext
                    with open(os.path.join(UPLOAD_DIR, stored), "wb") as f:
                        f.write(data)
                    cur = c.execute(
                        "INSERT INTO attachments(page_id,name,stored,size,inline,created) VALUES(?,?,?,?,?,?)",
                        (pid, name, stored, len(data), inline, now()),
                    )
                    return self.send_json(
                        {
                            "id": cur.lastrowid,
                            "name": name,
                            "stored": stored,
                            "size": len(data),
                            "url": "/files/" + stored,
                        }
                    )

                m = re.fullmatch(r"/api/attachments/(\d+)/hex", path)
                if method == "GET" and m:
                    r = c.execute("SELECT stored,name,size FROM attachments WHERE id=?", (int(m.group(1)),)).fetchone()
                    if not r:
                        return self.send_json({"error": "not found"}, 404)
                    off = max(0, int((qs.get("offset") or ["0"])[0]))
                    full = os.path.join(UPLOAD_DIR, r["stored"])
                    try:
                        with open(full, "rb") as f:
                            f.seek(off)
                            chunk = f.read(HEX_CHUNK)
                    except OSError:
                        return self.send_json({"error": "could not read file"}, 500)
                    return self.send_json({"text": hex_dump(chunk, off), "offset": off, "read": len(chunk),
                                           "size": r["size"], "name": r["name"], "eof": off + len(chunk) >= r["size"]})
                m = re.fullmatch(r"/api/attachments/(\d+)", path)
                if method == "DELETE" and m:
                    r = c.execute("SELECT stored FROM attachments WHERE id=?", (int(m.group(1)),)).fetchone()
                    if r:
                        c.execute("DELETE FROM attachments WHERE id=?", (int(m.group(1)),))
                        remove_files([r[0]])
                    return self.send_json({"ok": True})

                # ----- sticky notes -----
                m = re.fullmatch(r"/api/pages/(\d+)/stickies", path)
                if method == "POST" and m:
                    pid = int(m.group(1))
                    d = self.read_json()
                    n = c.execute("SELECT COUNT(*) FROM stickies WHERE page_id=?", (pid,)).fetchone()[0]
                    x = int(d.get("x", 60 + (n % 6) * 28))
                    y = int(d.get("y", 60 + (n % 6) * 28))
                    cur = c.execute(
                        "INSERT INTO stickies(page_id,text,color,x,y,w,h) VALUES(?,?,?,?,?,?,?)",
                        (pid, "", d.get("color", "#fff176"), x, y, 210, 170),
                    )
                    r = c.execute("SELECT * FROM stickies WHERE id=?", (cur.lastrowid,)).fetchone()
                    return self.send_json(dict(r))
                m = re.fullmatch(r"/api/stickies/(\d+)", path)
                if m:
                    kid = int(m.group(1))
                    if method == "PUT":
                        d = self.read_json()
                        for k in ("text", "color", "x", "y", "w", "h", "anchor"):
                            if k in d:
                                v = d[k]
                                if k in ("x", "y", "w", "h"):
                                    v = int(v)
                                c.execute(f"UPDATE stickies SET {k}=? WHERE id=?", (v, kid))
                        return self.send_json({"ok": True})
                    if method == "DELETE":
                        c.execute("DELETE FROM stickies WHERE id=?", (kid,))
                        return self.send_json({"ok": True})

            return self.send_json({"error": "not found"}, 404)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:  # noqa
            try:
                self.send_json({"error": str(e)}, 500)
            except Exception:
                pass

    def serve_file(self, stored, download):
        full = os.path.join(UPLOAD_DIR, stored)
        if not os.path.isfile(full):
            return self.send_json({"error": "not found"}, 404)
        with db() as c:
            r = c.execute("SELECT name FROM attachments WHERE stored=?", (stored,)).fetchone()
        name = r["name"] if r else stored
        ctype = mimetypes.guess_type(name)[0] or "application/octet-stream"
        with open(full, "rb") as f:
            data = f.read()
        headers = {"Cache-Control": "private, max-age=3600", "X-Content-Type-Options": "nosniff"}
        if ctype in ("text/html", "image/svg+xml", "application/xhtml+xml", "text/xml", "application/xml"):
            headers["Content-Security-Policy"] = "sandbox"
        safe = name.replace('"', "").replace("\r", "").replace("\n", "")
        try:
            safe.encode("latin-1")
            disp_name = f'filename="{safe}"'
        except UnicodeEncodeError:
            from urllib.parse import quote

            disp_name = "filename*=UTF-8''" + quote(safe)
        headers["Content-Disposition"] = ("attachment; " if download else "inline; ") + disp_name
        self.send_bytes(200, data, ctype, headers)


# --------------------------------------------------------------------------
# Front-end (single page, Bootstrap 5)
# --------------------------------------------------------------------------
INDEX_HTML = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Codex</title>
<link href="https://cdn.jsdelivr.net/npm/bootstrap@5.3.3/dist/css/bootstrap.min.css" rel="stylesheet">
<link href="https://cdn.jsdelivr.net/npm/bootstrap-icons@1.11.3/font/bootstrap-icons.min.css" rel="stylesheet">
<link href="https://cdn.jsdelivr.net/npm/@highlightjs/cdn-assets@11.9.0/styles/atom-one-dark.min.css" rel="stylesheet">
<link href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css" rel="stylesheet">
<script>try{var _s=JSON.parse(localStorage.getItem('nbSettings')||'{}');var _d=_s.mode==='dark'||(_s.mode==='auto'&&matchMedia('(prefers-color-scheme: dark)').matches);var _r=document.documentElement;_r.dataset.mode=_d?'dark':'light';_r.setAttribute('data-bs-theme',_d?'dark':'light');_r.dataset.theme=_s.theme||'classic';}catch(e){}</script>
<link href="https://fonts.googleapis.com/css2?family=Caveat:wght@500&family=Fira+Code&family=Inter:wght@400;600&family=Lora&family=Merriweather&family=Patrick+Hand&display=swap" rel="stylesheet">
<style>
:root{
  --leather:#3a2c28; --leather2:#4b3a34; --accent:#f0b429; --paper:#fffef9; --ink:#2b2b33;
  --line:#d6e4f2; --margin:#f1a7a7;
  --leather-d:#2a1f1c; --panel:#fffef9; --panel-b:#e6dfcf; --btn-ink:#4a4a55; --btn-hover:#f1e9d6; --muted:#8a7d6a; --muted2:#9a8f7c; --soft:#fffbee; --soft-b:#eadfc6;
  --link:#0b6bcb; --bg1:#f4efe4; --bg2:#ddd5c4; --edge1:#c9b79c; --edge2:#b39c7b; --quote:#555; --dash:#e0d6bf; --cover1:#7a2f2f; --cover2:#4f1c1c; --hole:#b9a78c; --sepc:#ddd2bb;
  --edfont:system-ui,"Segoe UI",Roboto,sans-serif; --edsize:1.05rem;
}
html,body{height:100%}
body{background:var(--bg2) radial-gradient(circle at 20% 0%,var(--bg1),var(--bg2));color:var(--ink);font-family:system-ui,"Segoe UI",Roboto,sans-serif;overflow:hidden}
.app{display:flex;height:100vh}

/* ---------- sidebar ---------- */
#sidebar{width:310px;background:linear-gradient(180deg,var(--leather),var(--leather-d));color:#f3e9dc;flex-shrink:0;display:flex;flex-direction:column}
#sidebar .offcanvas-body{padding:0;display:flex;flex-direction:column;height:100%}
.brand{padding:16px 16px 8px;font-weight:700;font-size:1.25rem;letter-spacing:.5px;display:flex;align-items:center;gap:10px}
.brand i{color:var(--accent)}
.side-tools{padding:8px 14px 10px;display:flex;flex-direction:column;gap:8px}
.side-tools .form-control{background:var(--leather-d);border:1px solid #6a5750;color:#fff}
.side-tools .form-control::placeholder{color:#b9a89a}
#tree{overflow:auto;flex:1;padding:4px 8px 20px}
.sec{margin-bottom:4px}
.sec-head{display:flex;align-items:center;gap:6px;padding:8px 10px;border-radius:8px;cursor:pointer;font-weight:600;user-select:none}
.sec-head:hover{background:rgba(255,255,255,.08)}
.sec-title{flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.sec-actions,.page-actions{display:none;gap:2px}
.sec-head:hover .sec-actions,.page-item:hover .page-actions{display:flex}
.sec-actions button,.page-actions button{background:none;border:0;color:#e9d9c6;padding:0 4px;font-size:.85rem;opacity:.85}
.sec-actions button:hover,.page-actions button:hover{color:var(--accent);opacity:1}
.page-item{display:flex;align-items:center;gap:6px;margin:1px 0 1px 18px;padding:6px 10px;border-radius:8px;cursor:pointer;font-size:.93rem;color:#e6d8c7;border-left:3px solid transparent;animation:slideIn .25s ease both}
.page-item:hover{background:rgba(255,255,255,.07)}
.page-item.active{background:color-mix(in srgb,var(--accent) 22%,transparent);border-left-color:var(--accent);color:#fff}
.page-item span.t{flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.res{padding:8px 12px;border-radius:8px;margin:4px 6px;cursor:pointer;background:rgba(255,255,255,.05);animation:slideIn .25s ease both}
.res:hover{background:rgba(255,255,255,.12)}
.res small{color:#cdbca9;display:block}
.res .sn{font-size:.82rem;color:#e3d4c2}
mark{background:#ffe27a;padding:0 2px;border-radius:3px}
@keyframes slideIn{from{opacity:0;transform:translateX(-10px)}to{opacity:1;transform:none}}

/* ---------- main ---------- */
main{flex:1;min-width:0;overflow:auto;padding:22px 24px 22px;scroll-behavior:smooth}
.topbar{display:none;align-items:center;gap:10px;margin-bottom:12px}
.book{max-width:960px;margin:0 auto;perspective:1800px}
.paper{position:relative;background:var(--paper);border-radius:6px 14px 14px 6px;box-shadow:0 12px 35px rgba(0,0,0,.25),-6px 0 0 var(--edge1),-10px 0 0 var(--edge2);padding:26px 34px 30px 70px;min-height:calc(100vh - 44px);display:flex;flex-direction:column;transform-origin:left center;
  background-image:linear-gradient(90deg,transparent 54px,var(--margin) 54px,var(--margin) 56px,transparent 56px)}
.paper::before{content:"";position:absolute;left:14px;top:0;bottom:0;width:20px;background:radial-gradient(circle at 10px 28px,var(--hole) 0 6px,transparent 7px) 0 0/20px 56px repeat-y;opacity:.8}
.paper.dir-next{--d:1}.paper.dir-prev{--d:-1}
.paper.dir-next.flip-out{transform-origin:left center}.paper.dir-prev.flip-out{transform-origin:right center}
.paper.dir-next.flip-in{transform-origin:right center}.paper.dir-prev.flip-in{transform-origin:left center}
.flip-out{animation:flipOut .24s cubic-bezier(.5,0,.9,.5) forwards}
.flip-in{animation:flipIn .38s cubic-bezier(.2,.7,.2,1) both}
@keyframes flipOut{to{transform:rotateY(calc(var(--d) * -75deg));opacity:0}}
@keyframes flipIn{from{transform:rotateY(calc(var(--d) * 75deg));opacity:0}to{transform:none;opacity:1}}
.pop{animation:pop .3s ease both}
@keyframes pop{from{opacity:0;transform:scale(.85)}to{opacity:1;transform:none}}

.crumb{font-size:.85rem;color:var(--muted);margin-bottom:2px;display:flex;align-items:center;gap:8px;flex-wrap:wrap}
#pageTitle{border:0;background:transparent;font-size:2rem;font-weight:700;width:100%;outline:none;padding:0;border-bottom:2px dashed transparent;font-family:Georgia,serif}
#pageTitle:focus{border-bottom-color:var(--accent)}
.meta{font-size:.78rem;color:var(--muted2)}
.toolbar{position:fixed;left:50%;top:70px;z-index:1500;max-width:min(94vw,660px);background:var(--panel);border:1px solid var(--panel-b);border-radius:12px;padding:5px 6px;display:flex;flex-wrap:wrap;gap:3px;align-items:center;box-shadow:0 10px 30px rgba(0,0,0,.28);animation:pop .2s ease both}
.toolbar .btn{padding:3px 8px;border:0;background:transparent;color:var(--btn-ink)}
.toolbar .btn:hover{background:var(--btn-hover)}
.toolbar .sep{width:1px;height:22px;background:var(--sepc);margin:0 4px}
.toolbar input[type=color]{width:28px;height:28px;border:0;background:none;padding:0;cursor:pointer}
#editor{outline:none;margin-top:14px;min-height:340px;flex:1 0 auto;cursor:text;font-family:var(--edfont);font-size:var(--edsize);line-height:32px;
  background-image:linear-gradient(transparent 31px,var(--line) 32px);background-size:100% 32px;background-position:0 -1px;padding-bottom:40px;word-wrap:break-word}
#editor h2,#editor h3{line-height:1.3;margin:14px 0 6px;font-family:Georgia,serif}
#editor p,#editor li,#editor div{margin:0}
#editor img{max-width:100%;height:auto;border-radius:6px;cursor:pointer;box-shadow:0 2px 8px rgba(0,0,0,.15);vertical-align:middle;margin:4px 0}
#editor blockquote{border-left:4px solid var(--accent);margin:8px 0;padding:0 14px;color:var(--quote);background:color-mix(in srgb,var(--accent) 10%,transparent)}
#editor pre{background:#2b2b33;color:#f6f6f6;padding:10px 14px;border-radius:8px;line-height:1.4;line-height:24px;white-space:pre-wrap}
#editor a{color:var(--link)}
#editor input[type=checkbox]{transform:scale(1.2);margin-right:8px;cursor:pointer}
#editor:empty::before{content:"Start writing your notes here… (paste or drop images too)";color:#b6ae9d}

#imgBox{position:absolute;border:2px dashed #0d6efd;pointer-events:none;display:none;z-index:15}
#imgBox .handle{position:absolute;right:-9px;bottom:-9px;width:18px;height:18px;background:#0d6efd;border:2px solid #fff;border-radius:50%;cursor:nwse-resize;pointer-events:auto;box-shadow:0 1px 4px rgba(0,0,0,.4)}
#imgBox .mini{position:absolute;left:0;top:-40px;background:#212529;border-radius:8px;padding:3px;display:flex;gap:2px;pointer-events:auto;white-space:nowrap}
#imgBox .mini button{background:none;border:0;color:#fff;font-size:.78rem;padding:3px 7px;border-radius:5px}
#imgBox .mini button:hover{background:#495057}

#stickyLayer{position:absolute;inset:0;pointer-events:none;z-index:12;overflow:visible}
.sticky{position:absolute;pointer-events:auto;display:flex;flex-direction:column;border-radius:3px 3px 14px 3px;box-shadow:3px 6px 14px rgba(0,0,0,.28);min-width:120px;min-height:90px;resize:both;overflow:hidden;transform:rotate(-1.2deg);animation:pop .3s ease both}
.sticky:nth-child(even){transform:rotate(1.4deg)}
.sticky .bar{display:flex;align-items:center;gap:4px;padding:3px 6px;background:rgba(0,0,0,.09);cursor:grab;touch-action:none;user-select:none}
.sticky .bar:active{cursor:grabbing}
.sticky .bar .grow{flex:1;font-size:.7rem;opacity:.55}
.sticky .bar button{background:none;border:0;padding:0 3px;font-size:.85rem;opacity:.65}
.sticky .bar button:hover{opacity:1}
.sticky textarea{flex:1;border:0;background:transparent;resize:none;outline:none;padding:8px 10px;font-family:"Comic Sans MS","Segoe Print",cursive;font-size:.95rem;line-height:1.35;width:100%}

.attach{margin-top:26px;border-top:2px dashed var(--dash);padding-top:14px}
.att{display:flex;align-items:center;gap:10px;padding:8px 12px;border:1px solid var(--soft-b);border-radius:10px;background:var(--soft);margin-bottom:6px;animation:slideIn .25s ease both}
.att i.big{font-size:1.4rem;color:#c58a00}
.att .n{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.att a{text-decoration:none;color:inherit}
.dropzone-active{outline:3px dashed var(--accent);outline-offset:-8px}
#savestate{font-size:.78rem}
.empty{max-width:520px;margin:12vh auto;text-align:center;color:var(--muted)}
.empty i{font-size:4rem;color:#c9b79c}

/* ---------- cover animation ---------- */
#cover{position:fixed;inset:0;z-index:2000;display:flex;align-items:center;justify-content:center;background:var(--leather-d);perspective:2200px;transition:background .9s ease .3s}
#cover.open{background:transparent;pointer-events:none}
#cover .cv{width:min(380px,82vw);height:min(520px,70vh);transform-origin:left center;transition:transform 1.3s cubic-bezier(.6,0,.2,1),opacity .6s ease 1s;background:linear-gradient(135deg,var(--cover1),var(--cover2));border-radius:6px 16px 16px 6px;box-shadow:0 20px 60px rgba(0,0,0,.6),inset 0 0 0 6px rgba(240,180,41,.35),inset 12px 0 18px rgba(0,0,0,.35);color:#f6dca0;display:flex;flex-direction:column;align-items:center;justify-content:center;text-align:center;cursor:pointer;padding:20px}
#cover.open .cv{transform:rotateY(-165deg);opacity:0}
#cover .cv i{font-size:4rem}
#cover .cv h1{font-family:Georgia,serif;font-size:2.2rem;margin:14px 0 6px}
#cover .cv small{opacity:.7;letter-spacing:2px;text-transform:uppercase}

.tb-grip{cursor:grab;padding:0 6px;color:#9a8f7c;touch-action:none;user-select:none;font-size:1.1rem}
.tb-grip:active{cursor:grabbing}
#btnTools.active{background:#212529;color:#fff}
[data-anchor]{box-shadow:inset -5px 0 0 #f0b429}
.sticky.linked{outline:2px solid rgba(240,180,41,.95)}
.sticky .bar{padding:6px 8px}
.pglink{color:#7b3fe4;text-decoration:underline dotted;cursor:pointer}
#trashBody .grow{min-width:0}
.study-panel{position:fixed;inset:0;z-index:1040;background:var(--bg1);display:flex;flex-direction:column;animation:pop .25s ease both}
.sp-head{display:flex;align-items:center;gap:10px;padding:10px 16px;background:var(--leather);color:#fff;flex-wrap:wrap}
.sp-head .nav-link{color:#e9d9c6}.sp-head .nav-link.active{background:var(--accent);color:#2a1f1c}
.sp-body{flex:1;overflow:auto;padding:18px 16px 40px;width:100%;max-width:960px;margin:0 auto}
.fc-front{font-size:1.5rem;font-family:Georgia,serif;text-align:center;padding:28px 10px;white-space:pre-wrap;min-height:120px}
.fc-back{font-size:1.15rem;text-align:center;padding:14px 10px;white-space:pre-wrap;color:#1c6b3a;animation:pop .25s ease both}
.big-time{font-size:4.5rem;font-weight:700;font-variant-numeric:tabular-nums;line-height:1}
#pageTitle{color:var(--ink)}
.sticky,.sticky textarea{color:#222}
/* ---------- themes ---------- */
[data-theme="ocean"]{--leather:#16324a;--leather2:#1f4466;--leather-d:#0e2233;--accent:#4fc3f7;--paper:#fbfeff;--line:#cfe6f5;--margin:#9ccbe8;--cover1:#1d5b8a;--cover2:#103a5a;--bg1:#eef6fb;--bg2:#d3e3ee;--edge1:#9fbdd1;--edge2:#86a7bf;--hole:#9db8cb}
[data-theme="forest"]{--leather:#243b2f;--leather2:#2f4d3d;--leather-d:#16271f;--accent:#9be564;--paper:#fbfff7;--line:#dcebd3;--margin:#b6d7a8;--cover1:#2f6b45;--cover2:#1b4029;--bg1:#f0f6ea;--bg2:#d6e2cc;--edge1:#a9bf9a;--edge2:#92ab82;--hole:#a5b99a}
[data-theme="rose"]{--leather:#4a2735;--leather2:#5e3345;--leather-d:#321a24;--accent:#ff8fab;--paper:#fffafb;--line:#f3dbe3;--margin:#f4a6bb;--cover1:#9a3a58;--cover2:#5e1f35;--bg1:#fbeff2;--bg2:#ebd3da;--edge1:#d5a9b6;--edge2:#c18d9d;--hole:#cba3b0}
[data-theme="violet"]{--leather:#3b2a5a;--leather2:#4b3774;--leather-d:#27193d;--accent:#ffb86b;--paper:#fdfbff;--line:#e5def2;--margin:#c9b6ea;--cover1:#5a3a96;--cover2:#33205b;--bg1:#f3effa;--bg2:#d9d0ea;--edge1:#b6a6d4;--edge2:#9f8cc4;--hole:#ae9fcb}
[data-theme="slate"]{--leather:#2b2f36;--leather2:#383d46;--leather-d:#1c1f24;--accent:#8ab4f8;--paper:#ffffff;--line:#e3e6ea;--margin:#e5a3a3;--cover1:#3d4452;--cover2:#22262d;--bg1:#f1f2f4;--bg2:#d9dce1;--edge1:#b4b9c2;--edge2:#9ba1ac;--hole:#adb2bb}
[data-mode="dark"]{--paper:#1f2128;--ink:#e6e6ea;--line:#2c3140;--margin:#7a3a3a;--panel:#272a33;--panel-b:#3a3e4a;--btn-ink:#d7d9e0;--btn-hover:#343846;--muted:#9aa0ad;--muted2:#8b91a0;--soft:#2b2a22;--soft-b:#4a4630;--link:#7db4ff;--bg1:#16181d;--bg2:#0d0f12;--edge1:#2f323c;--edge2:#262932;--quote:#b8bcc8;--dash:#3a3e4a;--hole:#454a58;--sepc:#3d4150}
[data-mode="dark"] .fc-back{color:#7bd99c}
[data-mode="dark"] .btn-outline-dark{--bs-btn-color:#d7d9e0;--bs-btn-border-color:#5a5f6e;--bs-btn-hover-bg:#d7d9e0;--bs-btn-hover-color:#111;--bs-btn-active-bg:#d7d9e0;--bs-btn-active-color:#111}
[data-mode="dark"] #btnTools.active{background:var(--accent);color:#222;border-color:var(--accent)}
[data-mode="dark"] .text-bg-light{background:#343846!important;color:#d7d9e0!important}
.swatch{width:58px;height:42px;border-radius:10px;border:3px solid transparent;position:relative;cursor:pointer}
.swatch i{position:absolute;right:5px;bottom:5px;width:14px;height:14px;border-radius:50%}
.swatch.on{border-color:#0d6efd}
#editor table.nb-table{width:100%;border-collapse:collapse;table-layout:fixed;margin:10px 0;background:var(--paper)}
#editor .nb-table td,#editor .nb-table th{border:1px solid color-mix(in srgb,var(--ink) 28%,transparent);padding:0 8px;line-height:30px;min-height:32px;vertical-align:top;word-break:break-word}
#editor .nb-table th{background:color-mix(in srgb,var(--accent) 24%,var(--paper));font-weight:600;text-align:left}
#tblBox{position:absolute;z-index:16;background:#212529;border-radius:8px;padding:3px;gap:2px;white-space:nowrap;flex-wrap:wrap;max-width:96%}
#tblBox button{background:none;border:0;color:#fff;font-size:.76rem;padding:3px 7px;border-radius:5px}
#tblBox button:hover{background:#495057}
#editor pre{position:relative;font-family:"Fira Code",ui-monospace,Consolas,monospace;font-size:.92rem;tab-size:4}
#editor pre[data-lang]:not([data-lang="auto"])::after{content:attr(data-lang);position:absolute;top:3px;right:10px;font-size:.68rem;opacity:.55;text-transform:uppercase;pointer-events:none}
.tpl{border-width:2px!important}
.tpl.on{border-color:#0d6efd!important;box-shadow:0 0 0 3px rgba(13,110,253,.25)}
.math-node{cursor:pointer;padding:0 2px;border-radius:4px}
.math-node:hover,.diagram-node:hover{background:color-mix(in srgb,var(--accent) 16%,transparent)}
.math-node[data-display="1"]{display:block;text-align:center;margin:8px 0;font-size:1.2em}
.math-node.err{color:#d63384;font-family:monospace}
.diagram-node{margin:10px 0;text-align:center;cursor:pointer;background:var(--paper);border-radius:8px;padding:6px;overflow-x:auto}
.diagram-node svg{max-width:100%;height:auto}
.diagram-node:empty::before{content:"Rendering diagram\2026";color:var(--muted)}
.diagram-err{color:#d63384;text-align:left;white-space:pre-wrap;font-size:.8rem;font-family:monospace;margin:0}
.link-card{display:flex;flex-wrap:wrap;gap:12px;margin:10px 0;border:1px solid var(--soft-b);border-radius:12px;background:var(--soft);padding:10px;position:relative;max-width:640px;user-select:none}
.link-card .lc-thumb{position:relative;flex:0 0 170px;max-width:42%;display:block;border-radius:8px;overflow:hidden;align-self:flex-start;cursor:pointer}
#editor .link-card .lc-thumb img{width:100%;aspect-ratio:16/9;object-fit:cover;display:block;box-shadow:none;margin:0;border-radius:0;cursor:pointer}
.lc-play{position:absolute;inset:0;display:flex;align-items:center;justify-content:center;color:#fff;font-size:1.8rem;background:rgba(0,0,0,.28)}
.lc-play::before{content:"\25B6"}
.link-card .lc-body{flex:1;min-width:0;line-height:1.4}
#editor .link-card a.lc-title{font-weight:600;text-decoration:none;display:block;overflow-wrap:anywhere;cursor:pointer}
.lc-title{font-weight:600}
.lc-site{font-size:.78rem;color:var(--muted)}
.lc-desc{font-size:.85rem;color:var(--quote);max-height:4.3em;overflow:hidden;margin-top:2px}
.lc-x{position:absolute;top:2px;right:9px;cursor:pointer;opacity:0;font-size:1.3rem;line-height:1.2;color:var(--muted)}
.link-card:hover .lc-x{opacity:1}
.lc-player{flex:0 0 100%}.lc-player iframe{width:100%;aspect-ratio:16/9;border:0;border-radius:8px;display:block}
.link-card.loading{opacity:.7}
.sub-toggle{font-size:.65rem;opacity:.65;width:12px;display:inline-block;text-align:center;cursor:pointer}
.sub-toggle:hover{opacity:1}
.sub-toggle-spacer{width:12px;display:inline-block}
#pageIdBadge:hover{opacity:.75}
#crumbSec a{color:inherit;opacity:.7}
#crumbSec a:hover{opacity:1;text-decoration:underline}
/* ---------- responsive ---------- */
@media (max-width: 991.98px){
  #sidebar{width:300px}
  .topbar{display:flex}
  main{padding:12px 10px 12px}
  .paper{min-height:calc(100vh - 90px);padding:18px 16px 24px 42px;background-image:linear-gradient(90deg,transparent 30px,var(--margin) 30px,var(--margin) 32px,transparent 32px)}
  .paper::before{left:6px;width:14px}
  #pageTitle{font-size:1.5rem}
}
@media (min-width: 992px){
  #sidebar.offcanvas-lg{position:static;transform:none!important;visibility:visible!important}
}
</style>
</head>
<body>

<div id="cover"><div class="cv" id="cvBox"><i class="bi bi-journal-bookmark-fill"></i><h1>Codex</h1><small>Tap to open</small></div></div>

<div class="app">
  <aside id="sidebar" class="offcanvas-lg offcanvas-start" tabindex="-1">
    <div class="offcanvas-body">
      <div class="brand"><i class="bi bi-journal-richtext"></i> Codex
        <button class="btn btn-sm btn-outline-light ms-auto" id="btnDark" title="Dark / light mode"><i class="bi bi-moon-stars"></i></button>
        <button class="btn btn-sm btn-outline-light" id="openSettings" title="Appearance: theme and font"><i class="bi bi-palette2"></i></button>
        <button class="btn btn-sm btn-outline-light d-lg-none" data-bs-dismiss="offcanvas"><i class="bi bi-x-lg"></i></button></div>
      <div class="side-tools">
        <div class="input-group input-group-sm">
          <span class="input-group-text bg-dark border-secondary text-light"><i class="bi bi-search"></i></span>
          <input id="search" class="form-control" placeholder="Search titles, notes, files…" autocomplete="off">
          <button id="clearSearch" class="btn btn-outline-secondary d-none"><i class="bi bi-x"></i></button>
        </div>
        <div class="d-flex gap-2">
          <button id="addSection" class="btn btn-warning btn-sm fw-semibold flex-grow-1"><i class="bi bi-plus-lg"></i> Header</button>
          <button id="openBackup" class="btn btn-outline-light btn-sm" title="Telegram backup"><i class="bi bi-cloud-arrow-up"></i> Backup</button>
          <button id="openTrash" class="btn btn-outline-light btn-sm" title="Trash"><i class="bi bi-trash3"></i></button>
        </div>
        <button id="openStudy" class="btn btn-outline-warning btn-sm"><i class="bi bi-mortarboard"></i> Study tools</button>
      </div>
      <div id="sideInfo" class="px-3 pb-2" style="font-size:.82rem;color:#e6d8c7">
        <div class="d-flex align-items-center gap-2"><i class="bi bi-alarm"></i><span id="pmTime" style="font-variant-numeric:tabular-nums;font-weight:600">25:00</span><span id="pmMode" class="opacity-75">Focus</span>
          <button class="btn btn-sm btn-outline-light py-0 px-2 ms-auto" id="pmBtn" title="Start / pause timer"><i class="bi bi-play-fill"></i></button>
          <button class="btn btn-sm btn-outline-light py-0 px-2" id="pmRst" title="Reset timer"><i class="bi bi-arrow-counterclockwise"></i></button></div>
        <div id="sideExtra" class="mt-1" style="line-height:1.7"></div>
      </div>
      <div id="tree"></div>
    </div>
  </aside>

  <main id="main">
    <div class="topbar">
      <button class="btn btn-dark" data-bs-toggle="offcanvas" data-bs-target="#sidebar"><i class="bi bi-list"></i></button>
      <strong>Codex</strong>
    </div>
    <div class="book" id="book">
      <div class="paper" id="paper" style="display:none">
        <div class="crumb"><span id="crumbSec"></span>
          <span class="ms-auto d-flex gap-1 align-items-center">
            <span id="pageIdBadge" class="badge bg-secondary-subtle text-secondary-emphasis" style="cursor:pointer" title="Click to copy this page's ID"></span>
            <span id="savestate" class="text-muted"></span>
            <button class="btn btn-sm btn-outline-dark" id="btnTools" title="Show / hide editing tools"><i class="bi bi-pencil-square"></i> Edit tools</button>
            <button class="btn btn-sm btn-outline-warning" id="btnStickyTop" title="Add sticky note"><i class="bi bi-sticky-fill"></i></button>
            <select id="moveSec" class="form-select form-select-sm" style="width:auto" title="Move page to another header"></select>
            <div class="dropdown"><button class="btn btn-sm btn-outline-secondary" data-bs-toggle="dropdown" title="More"><i class="bi bi-three-dots-vertical"></i></button>
              <ul class="dropdown-menu dropdown-menu-end">
                <li><a class="dropdown-item" href="#" id="miFav"><i class="bi bi-star"></i> <span>Add to favorites</span></a></li>
                <li><a class="dropdown-item" href="#" id="miAddSub"><i class="bi bi-diagram-2"></i> Add sub-page…</a></li>
                <li><a class="dropdown-item" href="#" id="miMove"><i class="bi bi-arrow-left-right"></i> Move to…</a></li>
                <li><a class="dropdown-item" href="#" id="miDup"><i class="bi bi-copy"></i> Duplicate page</a></li>
                <li><a class="dropdown-item" href="#" id="miHist"><i class="bi bi-clock-history"></i> Version history</a></li>
                <li><a class="dropdown-item" href="#" id="miCard"><i class="bi bi-card-text"></i> Make flashcard…</a></li>
                <li><a class="dropdown-item" href="#" id="miTpl"><i class="bi bi-layout-text-window-reverse"></i> Insert template…</a></li>
                <!--MORE-ITEMS-->
              </ul></div>
            <button class="btn btn-sm btn-outline-secondary" id="pgUp" title="Move page up"><i class="bi bi-arrow-up"></i></button>
            <button class="btn btn-sm btn-outline-secondary" id="pgDown" title="Move page down"><i class="bi bi-arrow-down"></i></button>
            <button class="btn btn-sm btn-outline-danger" id="delPage" title="Delete page"><i class="bi bi-trash"></i></button>
          </span>
        </div>
        <input id="pageTitle" placeholder="Page title" maxlength="300">
        <div class="meta" id="meta"></div>
        <div id="tagRow" class="d-flex flex-wrap gap-1 align-items-center my-1"></div>


        <div id="editor" contenteditable="true" spellcheck="true"></div>

        <div class="attach">
          <div class="d-flex align-items-center mb-2">
            <strong><i class="bi bi-paperclip"></i> Attachments</strong>
            <button class="btn btn-sm btn-outline-dark ms-auto" id="btnAttach"><i class="bi bi-upload"></i> Attach files</button>
          </div>
          <div id="attList"></div>
          <div id="backlinks" class="mt-3"></div>
        </div>

        <div id="stickyLayer"></div>
        <div id="tblBox" style="display:none">
          <button data-op="rowUp" title="Insert row above"><i class="bi bi-arrow-bar-up"></i> Row</button><button data-op="rowDown" title="Insert row below"><i class="bi bi-arrow-bar-down"></i> Row</button>
          <button data-op="colLeft" title="Insert column left"><i class="bi bi-arrow-bar-left"></i> Col</button><button data-op="colRight" title="Insert column right"><i class="bi bi-arrow-bar-right"></i> Col</button>
          <button data-op="delRow" title="Delete row"><i class="bi bi-dash-circle"></i> Row</button><button data-op="delCol" title="Delete column"><i class="bi bi-dash-circle"></i> Col</button>
          <button data-op="hdr" title="Toggle header row"><i class="bi bi-layout-text-window"></i> Header</button><button data-op="delTable" title="Delete table"><i class="bi bi-trash"></i></button></div>
        <div id="imgBox"><div class="mini">
            <button data-w="25">25%</button><button data-w="50">50%</button><button data-w="75">75%</button><button data-w="100">100%</button>
            <button data-al="left" title="Left"><i class="bi bi-text-left"></i></button>
            <button data-al="center" title="Center"><i class="bi bi-text-center"></i></button>
            <button data-al="right" title="Right"><i class="bi bi-text-right"></i></button>
            <button data-del="1" title="Remove image"><i class="bi bi-trash"></i></button>
          </div><div class="handle" id="imgHandle"></div></div>
      </div>

      <div class="empty" id="emptyState">
        <i class="bi bi-journal-plus"></i>
        <h4 class="mt-3">No page open</h4>
        <p>Create a header on the left, then add a page to start taking notes.</p>
      </div>
    </div>
  </main>
</div>

        <div class="toolbar" id="toolbar" style="display:none"><span class="tb-grip" id="tbGrip" title="Drag to move anywhere"><i class="bi bi-grip-vertical"></i></span>
          <button class="btn" data-cmd="bold" title="Bold"><i class="bi bi-type-bold"></i></button>
          <button class="btn" data-cmd="italic" title="Italic"><i class="bi bi-type-italic"></i></button>
          <button class="btn" data-cmd="underline" title="Underline"><i class="bi bi-type-underline"></i></button>
          <button class="btn" data-cmd="strikeThrough" title="Strike"><i class="bi bi-type-strikethrough"></i></button>
          <span class="sep"></span>
          <button class="btn" data-block="h2" title="Heading"><i class="bi bi-type-h2"></i></button>
          <button class="btn" data-block="h3" title="Sub-heading"><i class="bi bi-type-h3"></i></button>
          <button class="btn" data-block="p" title="Paragraph"><i class="bi bi-paragraph"></i></button>
          <button class="btn" data-block="blockquote" title="Quote"><i class="bi bi-quote"></i></button>
          <button class="btn" id="btnCode" title="Code block (syntax highlighted)"><i class="bi bi-code-slash"></i></button>
          <select id="codeLang" class="form-select form-select-sm" style="width:auto" title="Code language"><option value="auto">auto</option><option>python</option><option>javascript</option><option>typescript</option><option>java</option><option>c</option><option>cpp</option><option>csharp</option><option>go</option><option>rust</option><option>php</option><option>ruby</option><option>sql</option><option value="xml">html</option><option>css</option><option>bash</option><option>json</option><option>yaml</option><option>markdown</option><option value="x86asm">assembly (x86)</option><option value="plaintext">plain</option></select>
          <span class="sep"></span>
          <button class="btn" data-cmd="insertUnorderedList" title="Bullets"><i class="bi bi-list-ul"></i></button>
          <button class="btn" data-cmd="insertOrderedList" title="Numbers"><i class="bi bi-list-ol"></i></button>
          <button class="btn" id="btnCheck" title="Checklist item"><i class="bi bi-check2-square"></i></button>
          <button class="btn" id="btnTable" title="Insert table"><i class="bi bi-table"></i></button>
          <button class="btn" id="btnMath" title="Math formula (LaTeX)"><i class="bi bi-calculator"></i></button>
          <button class="btn" id="btnDiagram" title="Diagram (flowchart, mind map, ...)"><i class="bi bi-diagram-3"></i></button>
          <button class="btn" id="btnLinkCard" title="Link card (YouTube or web page)"><i class="bi bi-window-stack"></i></button>
          <span class="sep"></span>
          <input type="color" id="hiColor" value="#fff176" title="Highlight colour">
          <button class="btn" id="btnHi" title="Highlight"><i class="bi bi-highlighter"></i></button>
          <input type="color" id="fgColor" value="#d6336c" title="Text colour">
          <button class="btn" id="btnFg" title="Text colour"><i class="bi bi-palette"></i></button>
          <button class="btn" id="btnLink" title="Link"><i class="bi bi-link-45deg"></i></button>
          <button class="btn" id="btnPgLink" title="Link to another page"><i class="bi bi-journal-arrow-up"></i></button>
          <button class="btn" data-cmd="removeFormat" title="Clear formatting"><i class="bi bi-eraser"></i></button>
          <span class="sep"></span>
          <button class="btn" id="btnImg" title="Insert image"><i class="bi bi-image"></i></button>
          <button class="btn" id="btnSticky" title="Add sticky note"><i class="bi bi-sticky-fill text-warning"></i></button>
          <span class="sep"></span>
          <button class="btn" data-cmd="undo" title="Undo"><i class="bi bi-arrow-counterclockwise"></i></button>
          <button class="btn" data-cmd="redo" title="Redo"><i class="bi bi-arrow-clockwise"></i></button>
        <span class="sep"></span><button class="btn" id="tbClose" title="Hide tools"><i class="bi bi-x-lg"></i></button>
        </div>

<input type="file" id="imgFile" accept="image/*" multiple hidden>
<input type="file" id="attFile" multiple hidden>

<!-- backup modal -->
<div class="modal fade" id="bkModal" tabindex="-1"><div class="modal-dialog modal-dialog-centered modal-dialog-scrollable"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title"><i class="bi bi-telegram text-primary"></i> Telegram backup</h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body">
    <details class="mb-3 small"><summary class="fw-semibold">How to set it up (1 minute)</summary>
      <ol class="mt-2 mb-0">
        <li>In Telegram open <b>@BotFather</b>, send <code>/newbot</code>, follow the steps and copy the <b>token</b>.</li>
        <li>Open your new bot and press <b>Start</b> (or send it any message). For a group/channel, add the bot there first.</li>
        <li>Paste the token below, click <b>Save</b>, then <b>Detect chat ID</b>, then <b>Send test</b>.</li>
      </ol>
      <div class="text-muted mt-2">Each backup is a .zip of your database and all uploaded files. The token is stored only in <code>notebook_data/config.json</code> on this computer and is never put inside the backup.</div>
    </details>
    <div class="mb-2"><label class="form-label mb-1">Bot token</label>
      <input id="bkToken" type="password" class="form-control" autocomplete="off" placeholder="123456789:ABC..."></div>
    <div class="mb-2"><label class="form-label mb-1">Chat ID</label>
      <div class="input-group"><input id="bkChat" class="form-control" placeholder="e.g. 123456789 or -100123..."><button class="btn btn-outline-secondary" id="bkDetect">Detect chat ID</button></div></div>
    <div class="row g-2 align-items-end mb-3">
      <div class="col-7"><label class="form-label mb-1">Back up every</label>
        <select id="bkInterval" class="form-select">
          <option value="0.25">15 minutes</option><option value="1">1 hour</option><option value="3">3 hours</option>
          <option value="6">6 hours</option><option value="12">12 hours</option><option value="24">24 hours</option><option value="168">7 days</option>
        </select></div>
      <div class="col-5"><div class="form-check form-switch fs-6"><input class="form-check-input" type="checkbox" id="bkEnabled"><label class="form-check-label" for="bkEnabled">Automatic</label></div></div>
    </div>
    <div class="small text-muted mb-2">Automatic backups only send when something changed, and only while this program is running.</div>
    <div id="bkMsg" class="alert alert-secondary py-2 small mb-0">&nbsp;</div>
  </div>
  <div class="modal-footer justify-content-between flex-wrap gap-2">
    <div class="d-flex gap-2 flex-wrap">
      <button class="btn btn-outline-primary btn-sm" id="bkTest"><i class="bi bi-send"></i> Send test</button>
      <button class="btn btn-outline-success btn-sm" id="bkRun"><i class="bi bi-cloud-upload"></i> Back up now</button>
      <a class="btn btn-outline-secondary btn-sm" href="/api/backup/download"><i class="bi bi-download"></i> Download zip</a>
    </div>
    <button class="btn btn-primary" id="bkSave">Save</button>
  </div>
</div></div></div>

<!-- new page / template modal -->
<div class="modal fade" id="npModal" tabindex="-1"><div class="modal-dialog modal-lg modal-dialog-centered modal-dialog-scrollable"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title" id="npHead">New page</h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body">
    <div id="npTitleRow" class="mb-3"><input id="npTitle" class="form-control" placeholder="Page title" maxlength="300"></div>
    <div class="small fw-semibold mb-2">Start from a template</div><div class="row g-2" id="npGrid"></div></div>
  <div class="modal-footer"><button class="btn btn-secondary" data-bs-dismiss="modal">Cancel</button><button class="btn btn-primary" id="npOk">Create page</button></div>
</div></div></div>
<!-- math modal -->
<div class="modal fade" id="mathModal" tabindex="-1"><div class="modal-dialog modal-lg modal-dialog-centered modal-dialog-scrollable"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title"><i class="bi bi-calculator"></i> Math formula (LaTeX)</h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body">
    <div class="d-flex flex-wrap gap-1 mb-2" id="mathSyms"></div>
    <textarea id="mathSrc" class="form-control mb-2" rows="3" style="font-family:monospace" placeholder="e.g.  x = \frac{-b \pm \sqrt{b^2-4ac}}{2a}"></textarea>
    <div class="form-check mb-2"><input class="form-check-input" type="checkbox" id="mathDisp"><label class="form-check-label" for="mathDisp">Display mode (centered, on its own line)</label></div>
    <div id="mathPrev" class="border rounded text-center p-3" style="min-height:70px;font-size:1.25rem"></div>
    <div class="small text-muted mt-2">Click a formula in your page any time to edit it. Needs internet the first time to load the math renderer.</div></div>
  <div class="modal-footer"><button class="btn btn-outline-danger me-auto" id="mathDel">Delete</button><button class="btn btn-secondary" data-bs-dismiss="modal">Cancel</button><button class="btn btn-primary" id="mathOk">Insert</button></div>
</div></div></div>
<!-- diagram modal -->
<div class="modal fade" id="diaModal" tabindex="-1"><div class="modal-dialog modal-xl modal-dialog-centered modal-dialog-scrollable"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title"><i class="bi bi-diagram-3"></i> Diagram</h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body"><div class="row g-3">
    <div class="col-lg-5"><select id="diaPreset" class="form-select form-select-sm mb-2"></select>
      <textarea id="diaSrc" class="form-control" rows="14" style="font-family:monospace;font-size:.85rem" spellcheck="false"></textarea>
      <div class="small text-muted mt-2">Written in Mermaid syntax. Pick a type above to start from an example. Click a diagram in your page to edit it.</div></div>
    <div class="col-lg-7"><div id="diaPrev" class="border rounded p-2 text-center" style="min-height:260px;overflow:auto"></div></div></div></div>
  <div class="modal-footer"><button class="btn btn-outline-danger me-auto" id="diaDel">Delete</button><button class="btn btn-secondary" data-bs-dismiss="modal">Cancel</button><button class="btn btn-primary" id="diaOk">Insert</button></div>
</div></div></div>
<!-- table modal -->
<div class="modal fade" id="tblModal" tabindex="-1"><div class="modal-dialog modal-dialog-centered modal-sm"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title"><i class="bi bi-table"></i> Insert table</h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body"><div class="row g-2"><div class="col-6"><label class="small">Rows</label><input id="tblRows" type="number" min="1" max="30" value="3" class="form-control"></div>
    <div class="col-6"><label class="small">Columns</label><input id="tblCols" type="number" min="1" max="10" value="3" class="form-control"></div></div>
    <div class="form-check mt-3"><input class="form-check-input" type="checkbox" id="tblHdr" checked><label class="form-check-label" for="tblHdr">First row is a header</label></div></div>
  <div class="modal-footer"><button class="btn btn-primary" id="tblOk">Insert</button></div>
</div></div></div>
<!-- hex viewer -->
<div class="modal fade" id="hexModal" tabindex="-1"><div class="modal-dialog modal-xl modal-dialog-centered modal-dialog-scrollable"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title"><i class="bi bi-code-square"></i> <span id="hexName"></span></h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body"><pre id="hexBody" class="mb-0" style="font-family:'Fira Code',ui-monospace,Consolas,monospace;font-size:.82rem;white-space:pre-wrap;word-break:break-all"></pre>
    <div class="text-center mt-2"><button class="btn btn-sm btn-outline-secondary" id="hexMore">Load more</button></div></div>
  <div class="modal-footer"><span class="small text-muted me-auto" id="hexInfo"></span></div>
</div></div></div>
<!-- settings modal -->
<div class="modal fade" id="setModal" tabindex="-1"><div class="modal-dialog modal-dialog-centered"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title"><i class="bi bi-palette2"></i> Appearance</h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body">
    <label class="form-label fw-semibold mb-1">Mode</label>
    <div class="btn-group w-100 mb-3" id="setMode"><button class="btn btn-outline-secondary" data-v="light"><i class="bi bi-sun"></i> Light</button><button class="btn btn-outline-secondary" data-v="dark"><i class="bi bi-moon-stars"></i> Dark</button><button class="btn btn-outline-secondary" data-v="auto"><i class="bi bi-circle-half"></i> Auto</button></div>
    <label class="form-label fw-semibold mb-1">Theme</label><div class="d-flex flex-wrap gap-2 mb-3" id="setThemes"></div>
    <label class="form-label fw-semibold mb-1">Notes font</label><select id="setFont" class="form-select mb-3"></select>
    <label class="form-label fw-semibold mb-1">Text size</label>
    <div class="btn-group w-100" id="setSize"><button class="btn btn-outline-secondary" data-v="s">Small</button><button class="btn btn-outline-secondary" data-v="m">Medium</button><button class="btn btn-outline-secondary" data-v="l">Large</button><button class="btn btn-outline-secondary" data-v="xl">X-large</button></div>
    <div class="form-check form-switch mt-3"><input class="form-check-input" type="checkbox" id="setAutoCard" checked><label class="form-check-label" for="setAutoCard">Turn a pasted link into a card</label></div>
    <div class="border rounded p-3 mt-3" id="setPreview" style="font-family:var(--edfont);font-size:var(--edsize);line-height:1.6">The quick brown fox jumps over the lazy dog. 0123456789</div>
  </div>
  <div class="modal-footer"><span class="small text-muted me-auto">Saved in this browser.</span><button class="btn btn-outline-secondary btn-sm" id="setReset">Reset</button><button class="btn btn-primary" data-bs-dismiss="modal">Done</button></div>
</div></div></div>
<!-- study panel -->
<div id="studyPanel" class="study-panel" style="display:none">
  <div class="sp-head"><strong class="me-2"><i class="bi bi-mortarboard-fill" style="color:var(--accent)"></i> Study tools</strong>
    <div class="nav nav-pills" id="spTabs"><button class="nav-link active" data-tab="cards">Flashcards</button><button class="nav-link" data-tab="planner">Planner</button><button class="nav-link" data-tab="focus">Focus timer</button></div>
    <button class="btn-close btn-close-white ms-auto" id="spClose" title="Close"></button></div>
  <div class="sp-body" id="spBody"></div>
</div>
<!-- move / reparent modal -->
<div class="modal fade" id="moveModal" tabindex="-1"><div class="modal-dialog modal-dialog-centered"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title"><i class="bi bi-arrow-left-right"></i> Move page</h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body"><label class="form-label mb-1">Move to the top level of a header, or make it a sub-page of:</label><select id="moveSel" class="form-select"></select></div>
  <div class="modal-footer"><button class="btn btn-secondary" data-bs-dismiss="modal">Cancel</button><button class="btn btn-primary" id="moveOk">Move</button></div>
</div></div></div>
<!-- trash modal -->
<div class="modal fade" id="trashModal" tabindex="-1"><div class="modal-dialog modal-dialog-centered modal-dialog-scrollable"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title"><i class="bi bi-trash3"></i> Trash</h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body" id="trashBody"></div>
  <div class="modal-footer"><span class="small text-muted me-auto">Items are deleted forever after 30 days.</span><button class="btn btn-outline-danger btn-sm" id="trashEmpty">Empty trash</button></div>
</div></div></div>
<!-- history modal -->
<div class="modal fade" id="histModal" tabindex="-1"><div class="modal-dialog modal-lg modal-dialog-centered modal-dialog-scrollable"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title"><i class="bi bi-clock-history"></i> Version history</h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body"><div class="row g-3">
    <div class="col-md-4" style="max-height:55vh;overflow:auto"><div class="list-group" id="histList"></div></div>
    <div class="col-md-8"><iframe id="histFrame" sandbox="" style="width:100%;height:55vh;border:1px solid #ddd;border-radius:8px;background:#fff"></iframe></div></div></div>
  <div class="modal-footer"><span class="small text-muted me-auto">A snapshot is kept automatically while you edit (at most one per 5 minutes).</span><button class="btn btn-primary" id="histRestore" disabled>Restore this version</button></div>
</div></div></div>
<!-- pick page modal -->
<div class="modal fade" id="pickModal" tabindex="-1"><div class="modal-dialog modal-dialog-centered"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title">Link to page</h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body"><select id="pickSel" class="form-select"></select><div class="small text-muted mt-2">Select text first to use it as the link text. Click a page link to jump to that page.</div></div>
  <div class="modal-footer"><button class="btn btn-secondary" data-bs-dismiss="modal">Cancel</button><button class="btn btn-primary" id="pickOk">Insert link</button></div>
</div></div></div>

<!-- text prompt modal -->
<div class="modal fade" id="askModal" tabindex="-1"><div class="modal-dialog modal-dialog-centered"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title" id="askTitle"></h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body"><input id="askInput" class="form-control" maxlength="200"></div>
  <div class="modal-footer"><button class="btn btn-secondary" data-bs-dismiss="modal">Cancel</button><button class="btn btn-primary" id="askOk">OK</button></div>
</div></div></div>

<!-- confirm modal -->
<div class="modal fade" id="confModal" tabindex="-1"><div class="modal-dialog modal-dialog-centered"><div class="modal-content">
  <div class="modal-header"><h5 class="modal-title">Please confirm</h5><button class="btn-close" data-bs-dismiss="modal"></button></div>
  <div class="modal-body" id="confText"></div>
  <div class="modal-footer"><button class="btn btn-secondary" data-bs-dismiss="modal">Cancel</button><button class="btn btn-danger" id="confOk">Delete</button></div>
</div></div></div>

<script src="https://cdn.jsdelivr.net/npm/bootstrap@5.3.3/dist/js/bootstrap.bundle.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/@highlightjs/cdn-assets@11.9.0/highlight.min.js"></script>
<script>
const $ = s => document.querySelector(s);
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const sleep = ms => new Promise(r => setTimeout(r, ms));
let tree = [], openSecs = new Set(), openPages = new Set(), currentId = null, dirty = false, saveTimer = null, savedRange = null;
function flattenPages(pages){
  const out = [];
  for(const p of pages){ out.push(p); if(p.children && p.children.length) out.push(...flattenPages(p.children)); }
  return out;
}
function allPages(){ return tree.flatMap(s => flattenPages(s.pages).map(p => ({...p, sectionId: s.id, sectionTitle: s.title}))); }
function sectionOf(id){ for(const s of tree) if(flattenPages(s.pages).some(p => p.id === id)) return s; return null; }
function findAncestorIds(pages, id, trail){
  for(const p of pages){
    if(p.id === id) return trail;
    if(p.children && p.children.length){ const r = findAncestorIds(p.children, id, [...trail, p.id]); if(r) return r; }
  }
  return null;
}
function ancestorIdsOf(id){ for(const s of tree){ const r = findAncestorIds(s.pages, id, []); if(r) return r; } return []; }
let searchMode = false;

async function api(method, url, body){
  const opt = {method, headers:{}};
  if(body !== undefined){ opt.body = JSON.stringify(body); opt.headers['Content-Type'] = 'application/json'; }
  const r = await fetch(url, opt);
  if(!r.ok) throw new Error((await r.json().catch(()=>({}))).error || r.statusText);
  return r.json();
}

/* ---------- modals ---------- */
function askText(title, value=''){
  return new Promise(res => {
    const el = $('#askModal'), m = bootstrap.Modal.getOrCreateInstance(el);
    $('#askTitle').textContent = title; const inp = $('#askInput'); inp.value = value;
    let done = false;
    const ok = () => { if(done) return; done = true; m.hide(); res(inp.value.trim()); };
    $('#askOk').onclick = ok; inp.onkeydown = e => { if(e.key === 'Enter') ok(); };
    el.addEventListener('hidden.bs.modal', () => { if(!done){ done = true; res(null); } }, {once:true});
    el.addEventListener('shown.bs.modal', () => { inp.focus(); inp.select(); }, {once:true});
    m.show();
  });
}
function confirmBox(text){
  return new Promise(res => {
    const el = $('#confModal'), m = bootstrap.Modal.getOrCreateInstance(el);
    $('#confText').textContent = text; let done = false;
    $('#confOk').onclick = () => { done = true; m.hide(); res(true); };
    el.addEventListener('hidden.bs.modal', () => { if(!done) res(false); }, {once:true});
    m.show();
  });
}

/* ---------- sidebar tree ---------- */
const flat = () => allPages().map(p => p.id);
async function loadTree(){ tree = await api('GET', '/api/tree'); renderTree(); }

function renderTree(){
  const box = $('#tree'); box.innerHTML = '';
  if(searchMode) return;
  renderFavs(box);
  tree.forEach((s, si) => {
    const open = openSecs.has(s.id);
    const el = document.createElement('div'); el.className = 'sec';
    el.innerHTML = `<div class="sec-head"><i class="bi bi-chevron-${open?'down':'right'}"></i>
      <i class="bi bi-folder2${open?'-open':''}" style="color:${s.color || '#f0b429'}"></i>
      <span class="sec-title">${esc(s.title)}</span>
      <span class="sec-actions">
        <button data-a="up" title="Move up"><i class="bi bi-arrow-up"></i></button>
        <button data-a="down" title="Move down"><i class="bi bi-arrow-down"></i></button>
        <button data-a="col" title="Change colour"><i class="bi bi-palette"></i></button>
        <button data-a="add" title="Add page"><i class="bi bi-plus-lg"></i></button>
        <button data-a="ren" title="Rename"><i class="bi bi-pencil"></i></button>
        <button data-a="del" title="Delete header"><i class="bi bi-trash"></i></button></span></div>`;
    const head = el.firstElementChild;
    head.addEventListener('click', async e => {
      const a = e.target.closest('button')?.dataset.a;
      if(!a){ open ? openSecs.delete(s.id) : openSecs.add(s.id); return renderTree(); }
      e.stopPropagation();
      if(a === 'col'){ const i = (SEC_COLORS.indexOf(s.color) + 1) % SEC_COLORS.length; await api('PUT', '/api/sections/' + s.id, {color: SEC_COLORS[i]}); return loadTree(); }
      if(a === 'add') return newPage(s.id);
      if(a === 'ren'){ const t = await askText('Rename header', s.title); if(t){ await api('PUT', '/api/sections/'+s.id, {title:t}); await loadTree(); if(currentId){ const sc = sectionOf(currentId); $('#crumbSec').textContent = sc?.title || ''; } refreshMoveSelect(); } }
      if(a === 'del'){
        if(await confirmBox(`Move header "${s.title}" and its ${flattenPages(s.pages).length} page(s) to the trash? You can restore them from Trash.`)){
          const had = flattenPages(s.pages).some(p => p.id === currentId);
          await api('DELETE', '/api/sections/'+s.id); await loadTree();
          if(had) { currentId = null; await openFirstOrEmpty(); }
        }
      }
      if(a === 'up' || a === 'down'){ await api('POST', `/api/sections/${s.id}/move`, {dir: a==='up'?-1:1}); await loadTree(); }
    });
    box.appendChild(el);
    if(open){
      s.pages.forEach((p, i) => renderPageNode(p, 0, box, i));
      if(!s.pages.length){
        const em = document.createElement('div'); em.className='page-item'; em.style.opacity='.6';
        em.innerHTML = '<i class="bi bi-plus-circle"></i><span class="t">Add first page</span>';
        em.onclick = () => newPage(s.id); box.appendChild(em);
      }
    }
  });
}
function renderPageNode(p, depth, box, i){
  const hasKids = p.children && p.children.length > 0, expanded = openPages.has(p.id);
  const it = document.createElement('div');
  it.className = 'page-item' + (p.id === currentId ? ' active' : ''); it.dataset.id = p.id;
  it.style.marginLeft = (18 + depth * 16) + 'px'; it.style.animationDelay = (Math.min(i,8)*30)+'ms';
  it.innerHTML = `${hasKids ? `<i class="bi bi-chevron-${expanded?'down':'right'} sub-toggle"></i>` : '<i class="sub-toggle-spacer"></i>'}<i class="bi bi-file-earmark-text"></i><span class="t">${esc(p.title)}</span>${p.fav ? '<i class="bi bi-star-fill" style="color:#f0b429;font-size:.72rem"></i>' : ''}
    <span class="page-actions">
      <button data-p="addsub" title="Add sub-page"><i class="bi bi-plus-lg"></i></button>
      <button data-p="fav" title="Favorite"><i class="bi bi-star"></i></button>
      <button data-p="dup" title="Duplicate"><i class="bi bi-copy"></i></button>
      <button data-p="move" title="Move to…"><i class="bi bi-arrow-left-right"></i></button>
      <button data-p="del" title="Move to trash"><i class="bi bi-trash"></i></button></span>`;
  it.addEventListener('click', async e => {
    if(e.target.closest('.sub-toggle')){ e.stopPropagation(); expanded ? openPages.delete(p.id) : openPages.add(p.id); return renderTree(); }
    if(e.target.closest('.page-actions')){ e.stopPropagation(); return pageAction(e.target.closest('button')?.dataset.p, p); }
    openPage(p.id); closeDrawer();
  });
  box.appendChild(it);
  if(hasKids && expanded) p.children.forEach((c, j) => renderPageNode(c, depth + 1, box, j));
}
function moveOptionsHtml(excludeIds){
  const walk = (pages, depth) => {
    let html = '';
    for(const pg of pages){
      if(!excludeIds.has(pg.id)) html += `<option value="${pg.id}">${'—'.repeat(depth)} ${esc(pg.title)}</option>`;
      if(pg.children && pg.children.length) html += walk(pg.children, depth + 1);
    }
    return html;
  };
  return tree.map(s => `<optgroup label="${esc(s.title)}"><option value="top:${s.id}">(top level of this header)</option>${walk(s.pages, 1)}</optgroup>`).join('');
}
async function movePageDialog(p){
  const excl = new Set([p.id, ...flattenPages(p.children || []).map(c => c.id)]);
  const el = $('#moveModal'), m = bootstrap.Modal.getOrCreateInstance(el);
  $('#moveSel').innerHTML = moveOptionsHtml(excl);
  const curSec = sectionOf(p.id); if(curSec) $('#moveSel').value = p.parent_id ? String(p.parent_id) : 'top:' + curSec.id;
  m.show();
  const choice = await new Promise(res => {
    let done = false;
    $('#moveOk').onclick = () => { done = true; m.hide(); res($('#moveSel').value); };
    el.addEventListener('hidden.bs.modal', () => { if(!done) res(null); }, {once: true});
  });
  if(choice === null) return;
  await saveNow();
  if(choice.startsWith('top:')) await api('PUT', `/api/pages/${p.id}`, {section_id: Number(choice.slice(4))});
  else await api('PUT', `/api/pages/${p.id}`, {parent_id: Number(choice)});
  await loadTree();
  if(p.id === currentId) await openPage(p.id, false);
  toast('Page moved');
}
function closeDrawer(){ const el = $('#sidebar'); const o = bootstrap.Offcanvas.getInstance(el); if(o) o.hide(); }

$('#addSection').onclick = async () => {
  const t = await askText('New header (subject)', ''); if(!t) return;
  const r = await api('POST', '/api/sections', {title:t}); openSecs.add(r.id); await loadTree();
};
async function newPage(sectionId, parentId){
  const r0 = await pickTemplate(true); if(!r0) return;
  const t = TEMPLATES.find(x => x.id === r0.tpl) || TEMPLATES[0];
  const title = r0.title || t.title || 'Untitled page';
  const body = parentId ? {parent_id: parentId, title} : {section_id: sectionId, title};
  const r = await api('POST', '/api/pages', body);
  if(t.html) await api('PUT', '/api/pages/' + r.id, {content: tplHtml(t)});
  if(parentId){ openPages.add(parentId); const sec = sectionOf(parentId); if(sec) openSecs.add(sec.id); }
  else openSecs.add(sectionId);
  await loadTree(); await openPage(r.id); closeDrawer();
  $('#editor').focus();
}
async function deletePage(id, title){
  if(!await confirmBox(`Move page "${title}" to the trash? You can restore it from Trash.`)) return;
  await api('DELETE', '/api/pages/'+id); await loadTree();
  if(id === currentId){ currentId = null; await openFirstOrEmpty(); }
}
$('#delPage').onclick = () => { const t = $('#pageTitle').value; if(currentId) deletePage(currentId, t); };
$('#pgUp').onclick = () => movePage(-1);
$('#pgDown').onclick = () => movePage(1);
async function movePage(d){ if(!currentId) return; await saveNow(); await api('POST', `/api/pages/${currentId}/move`, {dir:d}); await loadTree(); }

async function openFirstOrEmpty(){
  const last = Number(localStorage.getItem('lastPage'));
  const ids = flat();
  const id = ids.includes(last) ? last : ids[0];
  if(id){ const s = sectionOf(id); if(s) openSecs.add(s.id); ancestorIdsOf(id).forEach(a => openPages.add(a)); renderTree(); await openPage(id, false); }
  else { $('#paper').style.display = 'none'; $('#emptyState').style.display = ''; currentId = null; renderTree(); }
}

/* ---------- search ---------- */
let searchTimer = null;
$('#search').addEventListener('input', () => {
  clearTimeout(searchTimer);
  const q = $('#search').value.trim();
  $('#clearSearch').classList.toggle('d-none', !q);
  searchTimer = setTimeout(async () => {
    if(!q){ searchMode = false; return renderTree(); }
    searchMode = true;
    const res = await api('GET', '/api/search?q=' + encodeURIComponent(q));
    const words = q.split(/\s+/).filter(Boolean);
    const hl = t => { let h = esc(t); words.forEach(w => { h = h.replace(new RegExp('(' + w.replace(/[.*+?^${}()|[\]\\]/g,'\\$&') + ')', 'ig'), '<mark>$1</mark>'); }); return h; };
    const box = $('#tree');
    box.innerHTML = res.length ? '' : '<div class="text-center text-secondary mt-4">No results</div>';
    res.forEach((r, i) => {
      const d = document.createElement('div'); d.className = 'res'; d.style.animationDelay = (i*25)+'ms';
      d.innerHTML = `<div class="fw-semibold">${hl(r.title)}</div><small>${hl(r.section)}</small><div class="sn">${hl(r.snippet)}</div>`;
      d.onclick = () => { openPage(r.id); closeDrawer(); };
      box.appendChild(d);
    });
  }, 220);
});
$('#clearSearch').onclick = () => { $('#search').value = ''; $('#search').dispatchEvent(new Event('input')); };

/* ---------- opening a page ---------- */
async function openPage(id, animate = true){
  if(id === currentId && animate) return;
  if(currentId && dirty) await saveNow();
  clearImgSel();
  const data = await api('GET', '/api/pages/' + id);
  const ids = flat();
  const dir = (currentId === null || ids.indexOf(id) >= ids.indexOf(currentId)) ? 'next' : 'prev';
  const paper = $('#paper');
  const wasVisible = paper.style.display !== 'none';
  if(animate && wasVisible){
    paper.className = 'paper dir-' + dir + ' flip-out'; await sleep(230);
  }
  $('#emptyState').style.display = 'none'; paper.style.display = '';
  currentId = id; localStorage.setItem('lastPage', id);
  renderPage(data);
  paper.className = 'paper dir-' + dir + ' flip-in';
  $('#main').scrollTo({top: 0, behavior: 'auto'});
  renderTree();
}
function renderPage(d){
  const p = d.page;
  $('#pageTitle').value = p.title;
  $('#editor').innerHTML = p.content || '';
  $('#editor').querySelectorAll('input[type=checkbox]').forEach(cb => cb.checked = cb.hasAttribute('checked'));
  ensureTrailingLine(); hlAll(); fixLoadingCards(); renderRich();
  if(window.showTools) showTools(false);
  $('#crumbSec').innerHTML = '<i class="bi bi-folder2-open"></i> ' + esc(d.section_title) +
    ((d.ancestors || []).map(a => ` <span class="opacity-50">›</span> <a href="#" data-anc="${a.id}">${esc(a.title)}</a>`).join(''));
  $('#pageIdBadge').textContent = '#' + p.id;
  $('#meta').textContent = 'Created ' + p.created + '  ·  Updated ' + p.updated;
  $('#savestate').textContent = '';
  refreshMoveSelect(p.section_id);
  curPage = p; renderTags(p.tags); renderBacklinks(d.backlinks || []); updateFavMenu();
  renderAttachments(d.attachments);
  $('#stickyLayer').innerHTML = ''; d.stickies.forEach(addStickyEl); setTimeout(layoutStickies, 50);
  dirty = false;
}
function refreshMoveSelect(sel){
  const s = $('#moveSec');
  if(sel === undefined) sel = Number(s.value);
  s.innerHTML = tree.map(x => `<option value="${x.id}" ${x.id===sel?'selected':''}>${esc(x.title)}</option>`).join('');
}
$('#moveSec').onchange = async () => {
  await saveNow(); const sid = Number($('#moveSec').value);
  await api('PUT', '/api/pages/' + currentId, {section_id: sid}); openSecs.add(sid);
  await loadTree(); $('#crumbSec').innerHTML = '<i class="bi bi-folder2-open"></i> ' + esc(tree.find(s=>s.id===sid).title);
};

/* ---------- saving ---------- */
function editorHTML(){
  const c = $('#editor').cloneNode(true);
  c.querySelectorAll('input[type=checkbox]').forEach(cb => { cb.checked ? cb.setAttribute('checked','') : cb.removeAttribute('checked'); });
  c.querySelectorAll('pre').forEach(p => { if(p.classList.contains('hl') || p.querySelector('span,br')) p.textContent = preText(p); p.classList.remove('hl'); if(!p.className) p.removeAttribute('class'); });
  c.querySelectorAll('.lc-player').forEach(n => n.remove());
  c.querySelectorAll('.math-node,.diagram-node').forEach(n => { n.innerHTML = ''; n.classList.remove('rendered', 'err'); n.removeAttribute('title'); });
  return c.innerHTML;
}
function scheduleSave(){
  dirty = true; $('#savestate').textContent = 'Editing…';
  clearTimeout(saveTimer); saveTimer = setTimeout(saveNow, 700);
}
async function saveNow(){
  clearTimeout(saveTimer);
  if(!currentId || !dirty) return;
  const id = currentId, title = $('#pageTitle').value, content = editorHTML();
  dirty = false;
  try{
    const r = await api('PUT', '/api/pages/' + id, {title, content});
    if(id === currentId){
      $('#savestate').innerHTML = '<i class="bi bi-check2-circle text-success"></i> Saved';
      $('#meta').textContent = $('#meta').textContent.replace(/Updated .*/, 'Updated ' + r.updated);
    }
  }catch(e){ dirty = true; $('#savestate').innerHTML = '<span class="text-danger">Save failed</span>'; }
}
$('#pageTitle').addEventListener('input', () => {
  scheduleSave();
  const el = document.querySelector(`.page-item[data-id="${currentId}"] .t`); if(el) el.textContent = $('#pageTitle').value || 'Untitled page';
  const p = allPages().find(p=>p.id===currentId); if(p) p.title = $('#pageTitle').value;
});
$('#editor').addEventListener('input', scheduleSave);

/* keep a free line after code/quote/list/image so you can always click below and keep typing */
const ed = $('#editor');
function ensureTrailingLine(){
  const last = ed.lastElementChild;
  if(!last || /^(PRE|BLOCKQUOTE|UL|OL|H2|H3|IMG|TABLE)$/.test(last.tagName) || last.classList.contains('diagram-node') || last.classList.contains('math-node')){
    const p = document.createElement('p'); p.innerHTML = '<br>'; ed.appendChild(p); return p;
  }
  return null;
}
function placeCaret(el){ const r = document.createRange(); r.selectNodeContents(el); r.collapse(true); const s = getSelection(); s.removeAllRanges(); s.addRange(r); rememberRange(); }
ed.addEventListener('mousedown', e => {          // click on empty space below the content
  if(e.target === ed){
    const lastRect = ed.lastElementChild?.getBoundingClientRect();
    if(lastRect && e.clientY > lastRect.bottom){
      e.preventDefault(); ed.focus();
      const p = ensureTrailingLine() || ed.lastElementChild; placeCaret(p); scheduleSave();
    }
  }
});
ed.addEventListener('keydown', e => {            // Enter on an empty line inside code/quote -> leave the block
  if(e.key !== 'Enter' || e.shiftKey) return;
  const s = getSelection(); if(!s.rangeCount) return;
  let n = s.anchorNode; n = n.nodeType === 3 ? n.parentElement : n;
  const blk = n.closest && n.closest('blockquote');
  if(!blk || !ed.contains(blk)) return;
  const txt = blk.textContent;
  if(/(\n\s*|^\s*)$/.test(txt) && (txt.endsWith('\n') || txt.trim() === '' || blk.lastChild?.nodeName === 'BR' || /\n$/.test(txt))){
    e.preventDefault();
    // strip the trailing blank line, then add a normal paragraph after the block
    if(blk.tagName === 'PRE') blk.innerHTML = blk.innerHTML.replace(/(\n|<br\s*\/?>)\s*$/i, '');
    else blk.querySelectorAll('br:last-child').forEach(b => b.remove());
    const p = document.createElement('p'); p.innerHTML = '<br>'; blk.after(p); placeCaret(p); scheduleSave();
  }
});
ed.addEventListener('keyup', e => { if(e.key === 'ArrowDown' || e.key === 'End') { /* allow reaching the free line */ ensureTrailingLine(); } });
$('#editor').addEventListener('change', e => { if(e.target.type === 'checkbox') scheduleSave(); });
window.addEventListener('beforeunload', () => {
  if(dirty && currentId) navigator.sendBeacon && fetch('/api/pages/' + currentId, {method:'PUT', keepalive:true, headers:{'Content-Type':'application/json'}, body: JSON.stringify({title:$('#pageTitle').value, content:editorHTML()})});
});
document.addEventListener('keydown', e => { if((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 's'){ e.preventDefault(); dirty = true; saveNow(); } });

/* ---------- toolbar ---------- */
function rememberRange(){ const s = getSelection(); if(s.rangeCount){ const r = s.getRangeAt(0); if($('#editor').contains(r.commonAncestorContainer)) savedRange = r.cloneRange(); } }
['mouseup','keyup','focus','input'].forEach(ev => $('#editor').addEventListener(ev, rememberRange));
function restoreRange(){ $('#editor').focus(); if(savedRange){ const s = getSelection(); s.removeAllRanges(); s.addRange(savedRange); } }
$('#toolbar').addEventListener('mousedown', e => { if(!e.target.closest('input, select')) e.preventDefault(); });
$('#toolbar').addEventListener('click', e => {
  const b = e.target.closest('button'); if(!b) return;
  if(b.dataset.cmd){ restoreRange(); document.execCommand(b.dataset.cmd, false, null); scheduleSave(); }
  if(b.dataset.block){ restoreRange(); document.execCommand('formatBlock', false, b.dataset.block); ensureTrailingLine(); scheduleSave(); }
});
$('#btnHi').onclick = () => { restoreRange(); document.execCommand('hiliteColor', false, $('#hiColor').value); scheduleSave(); };
$('#btnFg').onclick = () => { restoreRange(); document.execCommand('foreColor', false, $('#fgColor').value); scheduleSave(); };
$('#btnLink').onclick = async () => {
  rememberRange(); const u = await askText('Link URL (https://…)', 'https://'); if(!u) return;
  restoreRange(); document.execCommand('createLink', false, u); scheduleSave();
};
$('#btnCheck').onclick = () => { restoreRange(); document.execCommand('insertHTML', false, '<div><input type="checkbox">&nbsp;</div>'); scheduleSave(); };

/* ---------- images ---------- */
async function upload(file, inline){
  const name = file.name || ('pasted-' + Date.now() + '.png');
  const r = await fetch(`/api/pages/${currentId}/upload?name=${encodeURIComponent(name)}&inline=${inline?1:0}`, {method:'POST', body:file, headers:{'Content-Type':'application/octet-stream'}});
  if(!r.ok) throw new Error('Upload failed'); return r.json();
}
async function insertImageFile(file){
  const r = await upload(file, true);
  restoreRange(); document.execCommand('insertHTML', false, `<img src="${r.url}" alt="${esc(r.name)}" style="width:50%"><br>`);
  scheduleSave();
}
$('#btnImg').onclick = () => { rememberRange(); $('#imgFile').click(); };
$('#imgFile').onchange = async e => { for(const f of e.target.files) await insertImageFile(f); e.target.value = ''; };
$('#editor').addEventListener('paste', async e => {
  const files = [...(e.clipboardData?.files || [])].filter(f => f.type.startsWith('image/'));
  if(files.length){ e.preventDefault(); for(const f of files) await insertImageFile(f); }
});
const paperEl = $('#paper');
['dragenter','dragover'].forEach(ev => paperEl.addEventListener(ev, e => { if(e.dataTransfer?.types?.includes('Files')){ e.preventDefault(); paperEl.classList.add('dropzone-active'); } }));
['dragleave','drop'].forEach(ev => paperEl.addEventListener(ev, e => { if(ev==='dragleave' && paperEl.contains(e.relatedTarget)) return; paperEl.classList.remove('dropzone-active'); }));
paperEl.addEventListener('drop', async e => {
  if(!e.dataTransfer?.files?.length) return; e.preventDefault();
  for(const f of e.dataTransfer.files){ f.type.startsWith('image/') ? await insertImageFile(f) : await attachFile(f); }
});

/* image selection + resize */
let selImg = null;
const imgBox = $('#imgBox');
function placeImgBox(){
  if(!selImg || !document.contains(selImg)) return clearImgSel();
  const pr = paperEl.getBoundingClientRect(), r = selImg.getBoundingClientRect();
  Object.assign(imgBox.style, {display:'block', left:(r.left-pr.left)+'px', top:(r.top-pr.top)+'px', width:r.width+'px', height:r.height+'px'});
  imgBox.querySelector('.mini').style.top = (r.top - pr.top < 50 ? r.height + 12 : -40) + 'px';
}
function clearImgSel(){ selImg = null; imgBox.style.display = 'none'; }
$('#editor').addEventListener('click', e => { if(e.target.tagName === 'IMG' && !e.target.closest('.link-card')){ selImg = e.target; placeImgBox(); } else clearImgSel(); });
document.addEventListener('mousedown', e => { if(!e.target.closest('#editor') && !e.target.closest('#imgBox')) clearImgSel(); });
window.addEventListener('resize', placeImgBox);
imgBox.querySelector('.mini').addEventListener('click', e => {
  const b = e.target.closest('button'); if(!b || !selImg) return;
  if(b.dataset.w){ selImg.style.width = b.dataset.w + '%'; selImg.style.height = 'auto'; }
  if(b.dataset.al){ selImg.style.display = 'block'; selImg.style.margin = {left:'8px auto 8px 0', center:'8px auto', right:'8px 0 8px auto'}[b.dataset.al]; }
  if(b.dataset.del){ selImg.remove(); clearImgSel(); }
  scheduleSave(); placeImgBox();
});
(() => {
  const h = $('#imgHandle'); let sx, sw, active = false;
  const move = e => { if(!active || !selImg) return; const w = Math.max(40, sw + (e.clientX - sx)); selImg.style.width = w + 'px'; selImg.style.height = 'auto'; placeImgBox(); };
  const up = () => { if(active){ active = false; scheduleSave(); document.removeEventListener('pointermove', move); document.removeEventListener('pointerup', up); } };
  h.addEventListener('pointerdown', e => { e.preventDefault(); if(!selImg) return; active = true; sx = e.clientX; sw = selImg.getBoundingClientRect().width; document.addEventListener('pointermove', move); document.addEventListener('pointerup', up); });
})();

/* ---------- attachments ---------- */
const fmtSize = n => n < 1024 ? n + ' B' : n < 1048576 ? (n/1024).toFixed(1) + ' KB' : (n/1048576).toFixed(1) + ' MB';
function fileIcon(name){
  const e = (name.split('.').pop() || '').toLowerCase();
  if(['png','jpg','jpeg','gif','webp','svg','bmp'].includes(e)) return 'bi-file-earmark-image';
  if(e === 'pdf') return 'bi-file-earmark-pdf'; if(['doc','docx','odt','rtf'].includes(e)) return 'bi-file-earmark-word';
  if(['xls','xlsx','csv','ods'].includes(e)) return 'bi-file-earmark-excel'; if(['ppt','pptx','odp'].includes(e)) return 'bi-file-earmark-slides';
  if(['zip','rar','7z','tar','gz'].includes(e)) return 'bi-file-earmark-zip'; if(['mp3','wav','m4a','ogg'].includes(e)) return 'bi-file-earmark-music';
  if(['mp4','mkv','mov','webm','avi'].includes(e)) return 'bi-file-earmark-play'; if(['py','js','html','css','json','java','c','cpp','txt','md'].includes(e)) return 'bi-file-earmark-code';
  return 'bi-file-earmark';
}
function renderAttachments(list){
  const box = $('#attList');
  box.innerHTML = list.length ? '' : '<div class="text-muted small">No files attached. Click “Attach files” or drop files onto the page.</div>';
  list.forEach(a => {
    const d = document.createElement('div'); d.className = 'att';
    d.innerHTML = `<i class="bi ${fileIcon(a.name)} big"></i>
      <a class="n" href="/files/${a.stored}" target="_blank" rel="noopener" title="Open">${esc(a.name)}</a>
      <span class="text-muted small">${fmtSize(a.size)}</span>
      <a class="btn btn-sm btn-outline-secondary" href="/files/${a.stored}?dl=1" title="Download"><i class="bi bi-download"></i></a>
      <button class="btn btn-sm btn-outline-secondary" title="View as hex"><i class="bi bi-code-square"></i></button>
      <button class="btn btn-sm btn-outline-danger" title="Remove"><i class="bi bi-x-lg"></i></button>`;
    const btns = d.querySelectorAll('button');
    btns[0].onclick = () => openHex(a);
    btns[1].onclick = async () => { await api('DELETE', '/api/attachments/' + a.id); d.remove(); if(!box.querySelector('.att')) renderAttachments([]); };
    box.appendChild(d);
  });
}
async function attachFile(f){
  await upload(f, false);
  const d = await api('GET', '/api/pages/' + currentId); renderAttachments(d.attachments);
}
$('#btnAttach').onclick = () => $('#attFile').click();
$('#attFile').onchange = async e => { for(const f of e.target.files) await attachFile(f); e.target.value = ''; };

/* ---------- sticky notes ---------- */
const COLORS = ['#fff176','#ffab91','#a5d6a7','#81d4fa','#ce93d8','#ffe0b2','#f8bbd0'];
function toast(t){
  const d = document.createElement('div'); d.className = 'alert alert-dark py-2 px-3 shadow';
  d.style.cssText = 'position:fixed;left:0;right:0;bottom:24px;margin:auto;width:max-content;max-width:90vw;z-index:3000;animation:pop .2s ease both';
  d.textContent = t; document.body.appendChild(d); setTimeout(() => d.remove(), 2800);
}
const anchorEl = st => st.anchor ? ed.querySelector(`[data-anchor~="${st.anchor}"]`) : null;
const anchorTop = a => a.getBoundingClientRect().top - paperEl.getBoundingClientRect().top;
function blockAtCaret(){
  if(!savedRange) return null;
  let n = savedRange.startContainer;
  if(n === ed) n = ed.childNodes[Math.min(savedRange.startOffset, ed.childNodes.length - 1)];
  while(n && n.parentNode !== ed) n = n.parentNode;
  if(n && n.nodeType === 3){ const d = document.createElement('div'); n.replaceWith(d); d.appendChild(n); n = d; }
  return n && n.nodeType === 1 ? n : null;
}
function setAnchorAttr(blk, key, on){
  const cur = (blk.getAttribute('data-anchor') || '').split(' ').filter(x => x && x !== key);
  if(on) cur.push(key);
  cur.length ? blk.setAttribute('data-anchor', cur.join(' ')) : blk.removeAttribute('data-anchor');
}
function layoutSticky(el){
  const st = el._st, a = anchorEl(st);
  el.style.left = st.x + 'px';
  el.style.top = Math.max(0, a ? anchorTop(a) + st.y : st.y) + 'px';
  el.classList.toggle('linked', !!a);
  el.querySelector('.grow').textContent = a ? 'linked to line' : 'drag to move';
}
function layoutStickies(){ document.querySelectorAll('#stickyLayer .sticky').forEach(layoutSticky); }
ed.addEventListener('input', layoutStickies);
ed.addEventListener('load', layoutStickies, true);
window.addEventListener('resize', layoutStickies);
new ResizeObserver(layoutStickies).observe(ed);

function addStickyEl(st){
  const el = document.createElement('div'); el.className = 'sticky'; el._st = st;
  Object.assign(el.style, {width:st.w + 'px', height:st.h + 'px', background:st.color});
  el.innerHTML = `<div class="bar"><i class="bi bi-arrows-move"></i><span class="grow">drag to move</span>
    <button class="lnk" title="Link to a line of text / unlink"><i class="bi bi-link-45deg"></i></button>
    <button class="col" title="Change colour"><i class="bi bi-palette-fill"></i></button>
    <button class="del" title="Delete"><i class="bi bi-x-lg"></i></button></div>
    <textarea placeholder="Write a quick note…"></textarea>`;
  const ta = el.querySelector('textarea'); ta.value = st.text;
  let t; const put = o => api('PUT', '/api/stickies/' + st.id, o).catch(() => {});
  ta.addEventListener('input', () => { clearTimeout(t); t = setTimeout(() => put({text: ta.value}), 500); });
  el.querySelector('.col').onclick = () => { const i = (COLORS.indexOf(st.color) + 1) % COLORS.length; st.color = COLORS[i]; el.style.background = st.color; put({color: st.color}); };
  const unlink = () => {
    const a = anchorEl(st); const abs = el.offsetTop;
    if(a) setAnchorAttr(a, st.anchor, false);
    st.anchor = ''; st.y = abs; put({anchor: '', y: abs}); layoutSticky(el); scheduleSave();
  };
  el.querySelector('.lnk').onclick = () => {
    if(st.anchor) { unlink(); return toast('Sticky note unlinked'); }
    const blk = blockAtCaret();
    if(!blk) return toast('Click on a line of text first, then press the link button on the sticky note');
    const key = 's' + st.id, abs = el.offsetTop;
    setAnchorAttr(blk, key, true); st.anchor = key; st.y = abs - anchorTop(blk);
    put({anchor: key, y: st.y}); layoutSticky(el); scheduleSave(); toast('Linked: the note now follows that line');
  };
  el.querySelector('.del').onclick = async () => {
    if(ta.value && !await confirmBox('Delete this sticky note?')) return;
    if(st.anchor){ const a = anchorEl(st); if(a){ setAnchorAttr(a, st.anchor, false); scheduleSave(); } }
    await api('DELETE', '/api/stickies/' + st.id); el.remove();
  };
  // drag anywhere on the page
  const bar = el.querySelector('.bar'); let ox, oy, sx, sy, drag = false;
  bar.addEventListener('pointerdown', e => { if(e.target.closest('button')) return; drag = true; bar.setPointerCapture(e.pointerId); sx = e.clientX; sy = e.clientY; ox = el.offsetLeft; oy = el.offsetTop; el.style.zIndex = 50; });
  bar.addEventListener('pointermove', e => { if(!drag) return;
    el.style.left = Math.min(paperEl.clientWidth - 60, Math.max(0, ox + e.clientX - sx)) + 'px';
    el.style.top = Math.min(paperEl.clientHeight - 40, Math.max(0, oy + e.clientY - sy)) + 'px'; });
  bar.addEventListener('pointerup', () => {
    if(!drag) return; drag = false; el.style.zIndex = '';
    const a = anchorEl(st); st.x = el.offsetLeft; st.y = a ? el.offsetTop - anchorTop(a) : el.offsetTop;
    put({x: st.x, y: st.y}); });
  let first = true, rt;
  new ResizeObserver(() => { if(first){ first = false; return; } clearTimeout(rt); rt = setTimeout(() => put({w: el.offsetWidth, h: el.offsetHeight}), 400); }).observe(el);
  $('#stickyLayer').appendChild(el); layoutSticky(el); return el;
}
$('#btnSticky').onclick = async () => {
  if(!currentId) return;
  const sc = $('#main').scrollTop, top = Math.max(20, sc - paperEl.offsetTop + 120);
  const st = await api('POST', `/api/pages/${currentId}/stickies`, {x: Math.max(20, paperEl.clientWidth - 260 - Math.random()*80), y: top + Math.random()*40, color: COLORS[Math.floor(Math.random()*COLORS.length)]});
  const el = addStickyEl(st); el.querySelector('textarea').focus();
};

/* ---------- floating edit tools ---------- */
(() => {
  const tb = $('#toolbar'), grip = $('#tbGrip');
  let pos = null; try{ pos = JSON.parse(localStorage.getItem('tbPos')); }catch(e){}
  const clamp = () => {
    const w = tb.offsetWidth, h = tb.offsetHeight;
    let x = pos ? pos.x : (innerWidth - w) / 2, y = pos ? pos.y : 70;
    x = Math.min(Math.max(0, x), Math.max(0, innerWidth - w)); y = Math.min(Math.max(0, y), Math.max(0, innerHeight - h));
    tb.style.left = x + 'px'; tb.style.top = y + 'px';
  };
  window.showTools = on => { tb.style.display = on ? 'flex' : 'none'; $('#btnTools').classList.toggle('active', on); if(on) clamp(); };
  $('#btnTools').onclick = () => showTools(tb.style.display === 'none');
  $('#tbClose').onclick = () => showTools(false);
  $('#btnStickyTop').onclick = () => $('#btnSticky').click();
  window.addEventListener('resize', () => { if(tb.style.display !== 'none') clamp(); });
  let sx, sy, ox, oy, drag = false;
  grip.addEventListener('pointerdown', e => { drag = true; grip.setPointerCapture(e.pointerId); sx = e.clientX; sy = e.clientY; ox = tb.offsetLeft; oy = tb.offsetTop; });
  grip.addEventListener('pointermove', e => { if(!drag) return; pos = {x: ox + e.clientX - sx, y: oy + e.clientY - sy}; clamp(); });
  grip.addEventListener('pointerup', () => { if(!drag) return; drag = false; try{ localStorage.setItem('tbPos', JSON.stringify(pos)); }catch(e){} });
})();

/* ---------- organization: favorites, tags, colours, trash, history, page links ---------- */
const SEC_COLORS = ['#f0b429','#ef6f6c','#6fcf97','#56ccf2','#bb86fc','#ff9f6b','#f78fb3','#b8c0cc'];
let curPage = null;
function renderFavs(box){
  const favs = allPages().filter(p => p.fav).map(p => ({...p, sec: p.sectionTitle}));
  if(!favs.length) return;
  const h = document.createElement('div'); h.className = 'mb-2';
  h.innerHTML = '<div class="small text-uppercase px-2 pt-1" style="color:#d8c3a5;letter-spacing:1px"><i class="bi bi-star-fill" style="color:#f0b429"></i> Favorites</div>';
  favs.forEach(p => {
    const it = document.createElement('div'); it.className = 'page-item' + (p.id === currentId ? ' active' : ''); it.style.marginLeft = '8px';
    it.innerHTML = `<i class="bi bi-star"></i><span class="t">${esc(p.title)}</span><small style="opacity:.6">${esc(p.sec)}</small>`;
    it.onclick = () => { openPage(p.id); closeDrawer(); }; h.appendChild(it);
  });
  box.appendChild(h);
}
async function pageAction(act, p){
  if(act === 'fav'){ const f = p.fav ? 0 : 1; await api('PUT', '/api/pages/' + p.id, {fav: f}); if(curPage && curPage.id === p.id) curPage.fav = f; await loadTree(); updateFavMenu(); }
  else if(act === 'dup') duplicateCurrent(p.id);
  else if(act === 'addsub'){ openPages.add(p.id); newPage(null, p.id); }
  else if(act === 'move') movePageDialog(p);
  else deletePage(p.id, p.title);
}
async function duplicateCurrent(id){ await saveNow(); const r = await api('POST', `/api/pages/${id}/duplicate`); await loadTree(); openPage(r.id); toast('Page duplicated'); }
function updateFavMenu(){
  const f = curPage && curPage.fav;
  $('#miFav span').textContent = f ? 'Remove from favorites' : 'Add to favorites'; $('#miFav i').className = 'bi bi-star' + (f ? '-fill text-warning' : '');
}
$('#crumbSec').addEventListener('click', e => { const a = e.target.closest('[data-anc]'); if(a){ e.preventDefault(); openPage(Number(a.dataset.anc)); } });
$('#pageIdBadge').addEventListener('click', async () => {
  if(!currentId) return;
  try{ await navigator.clipboard.writeText(String(currentId)); toast('Copied page ID #' + currentId); }
  catch(e){ toast('Page ID: #' + currentId); }
});
$('#miAddSub').onclick = e => { e.preventDefault(); if(!currentId) return; openPages.add(currentId); newPage(null, currentId); };
$('#miMove').onclick = e => { e.preventDefault(); if(curPage) movePageDialog(curPage); };
$('#miFav').onclick = async e => { e.preventDefault(); if(!curPage) return; curPage.fav = curPage.fav ? 0 : 1; await api('PUT', '/api/pages/' + currentId, {fav: curPage.fav}); await loadTree(); updateFavMenu(); };
$('#miDup').onclick = e => { e.preventDefault(); if(currentId) duplicateCurrent(currentId); };
$('#miHist').onclick = e => { e.preventDefault(); if(currentId) openHistory(); };

/* tags */
function renderTags(tags){
  const list = (tags || '').split(',').filter(Boolean);
  $('#tagRow').innerHTML = '<i class="bi bi-tags text-muted"></i>' + list.map(t => `<span class="badge rounded-pill text-bg-light border" data-t="${esc(t)}" style="cursor:pointer">#${esc(t)} <i class="bi bi-x" data-x="1"></i></span>`).join('') +
    '<input id="tagInput" class="form-control form-control-sm" style="width:120px;border-style:dashed" placeholder="+ add tag" maxlength="30">';
}
async function saveTags(list){ const r = await api('PUT', '/api/pages/' + currentId, {tags: list.join(',')}); curPage.tags = r.tags; renderTags(r.tags); const p = allPages().find(x => x.id === currentId); if(p) p.tags = r.tags; }
$('#tagRow').addEventListener('click', e => {
  const chip = e.target.closest('[data-t]'); if(!chip) return; const t = chip.dataset.t;
  if(e.target.dataset.x) saveTags((curPage.tags || '').split(',').filter(x => x && x !== t));
  else { $('#search').value = t; $('#search').dispatchEvent(new Event('input')); }
});
$('#tagRow').addEventListener('keydown', e => {
  if(e.target.id === 'tagInput' && (e.key === 'Enter' || e.key === ',')){
    e.preventDefault(); const v = e.target.value.trim().replace(/,/g, '');
    if(v) saveTags([...(curPage.tags || '').split(',').filter(Boolean), v]).then(() => $('#tagInput').focus());
  }
});

/* backlinks + page links */
function renderBacklinks(list){
  $('#backlinks').innerHTML = list.length ? '<span class="small fw-semibold"><i class="bi bi-arrow-return-right"></i> Linked from:</span> ' +
    list.map(b => `<a href="#" class="badge text-bg-warning text-decoration-none" data-id="${b.id}">${esc(b.title)}</a>`).join(' ') : '';
}
$('#backlinks').addEventListener('click', e => { const a = e.target.closest('[data-id]'); if(a){ e.preventDefault(); openPage(Number(a.dataset.id)); } });
ed.addEventListener('click', e => { const a = e.target.closest && e.target.closest('a[data-page]'); if(a){ e.preventDefault(); openPage(Number(a.dataset.page)); } });
function pickPage(){
  return new Promise(res => {
    const el = $('#pickModal'), m = bootstrap.Modal.getOrCreateInstance(el), sel = $('#pickSel'); let done = false;
    const walk = (pages, depth) => pages.map(pg => (pg.id !== currentId ? `<option value="${pg.id}">${'\u2014'.repeat(depth)} ${esc(pg.title)}</option>` : '') + (pg.children && pg.children.length ? walk(pg.children, depth + 1) : '')).join('');
    sel.innerHTML = tree.map(s => `<optgroup label="${esc(s.title)}">${walk(s.pages, 0)}</optgroup>`).join('');
    $('#pickOk').onclick = () => { done = true; m.hide(); res(sel.value ? {id: Number(sel.value), title: sel.options[sel.selectedIndex].text} : null); };
    el.addEventListener('hidden.bs.modal', () => { if(!done) res(null); }, {once: true}); m.show();
  });
}
$('#btnPgLink').onclick = async () => {
  rememberRange(); const r = await pickPage(); if(!r) return;
  const txt = savedRange && !savedRange.collapsed ? savedRange.toString() : r.title;
  restoreRange(); document.execCommand('insertHTML', false, `<a href="#" data-page="${r.id}" class="pglink">${esc(txt)}</a>&nbsp;`); ed.querySelectorAll('a.pglink[style]').forEach(a => a.removeAttribute('style')); scheduleSave();
};

/* trash */
async function openTrash(){
  const t = await api('GET', '/api/trash');
  const row = (k, id, title, sub) => `<div class="d-flex align-items-center gap-2 border-bottom py-2"><i class="bi ${k === 'sections' ? 'bi-folder2' : 'bi-file-earmark-text'}"></i>
    <div class="grow flex-grow-1"><div class="text-truncate">${esc(title)}</div><small class="text-muted">${esc(sub)}</small></div>
    <button class="btn btn-sm btn-outline-success" data-r="${k}:${id}">Restore</button><button class="btn btn-sm btn-outline-danger" data-d="${k}:${id}" title="Delete forever"><i class="bi bi-x-lg"></i></button></div>`;
  $('#trashBody').innerHTML = (t.sections.length || t.pages.length)
    ? t.sections.map(x => row('sections', x.id, x.title, `Header · ${x.n} page(s) · deleted ${x.deleted_at}`)).join('') + t.pages.map(x => row('pages', x.id, x.title, `In "${x.section}" · deleted ${x.deleted_at}`)).join('')
    : '<div class="text-center text-muted py-4">Trash is empty</div>';
  bootstrap.Modal.getOrCreateInstance($('#trashModal')).show();
}
$('#trashBody').addEventListener('click', async e => {
  const r = e.target.closest('[data-r]'), d = e.target.closest('[data-d]');
  if(r){ const [k, id] = r.dataset.r.split(':'); await api('POST', `/api/${k}/${id}/restore`); await loadTree(); if(!currentId) await openFirstOrEmpty(); openTrash(); }
  if(d && confirm('Delete forever? This cannot be undone.')){ const [k, id] = d.dataset.d.split(':'); await api('DELETE', `/api/${k}/${id}?purge=1`); openTrash(); }
});
$('#trashEmpty').onclick = async () => { if(confirm('Delete everything in the trash forever?')){ await api('DELETE', '/api/trash'); openTrash(); } };
$('#openTrash').onclick = () => { openTrash(); closeDrawer(); };

/* version history */
let histSel = null;
async function openHistory(){
  await saveNow(); const list = await api('GET', `/api/pages/${currentId}/versions`);
  histSel = null; $('#histRestore').disabled = true;
  $('#histFrame').srcdoc = '<p style="font-family:sans-serif;color:#888;padding:12px">Select a version to preview it.</p>';
  $('#histList').innerHTML = list.length ? list.map(v => `<button class="list-group-item list-group-item-action" data-v="${v.id}"><div class="small fw-semibold">${esc(v.saved)}</div><div class="small text-muted text-truncate">${esc(v.title)} — ${esc(v.snippet)}</div></button>`).join('')
    : '<div class="text-muted small p-2">No earlier versions yet. They are saved automatically as you edit.</div>';
  bootstrap.Modal.getOrCreateInstance($('#histModal')).show();
}
$('#histList').addEventListener('click', async e => {
  const b = e.target.closest('[data-v]'); if(!b) return;
  const v = await api('GET', '/api/versions/' + b.dataset.v); histSel = v.id; $('#histRestore').disabled = false;
  $('#histList').querySelectorAll('.active').forEach(x => x.classList.remove('active')); b.classList.add('active');
  $('#histFrame').srcdoc = '<meta charset="utf-8"><body style="font-family:Georgia,serif;padding:14px;line-height:1.6"><h2>' + esc(v.title) + '</h2>' + v.content + '</body>';
});
$('#histRestore').onclick = async () => {
  if(!histSel) return; await api('POST', `/api/versions/${histSel}/restore`);
  bootstrap.Modal.getInstance($('#histModal')).hide(); const id = currentId; await openPage(id, false); await loadTree(); toast('Version restored');
};

/* ---------- study tools: flashcards, planner, pomodoro ---------- */
const spPanel = $('#studyPanel');
let spTab = 'cards', rq = null, showBack = false, cardDraft = null, cardCache = [];
const today = () => { const d = new Date(); return d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0'); };
const daysUntil = s => Math.round((new Date(s + 'T00:00:00') - new Date(today() + 'T00:00:00')) / 86400000);
function openStudy(tab){
  if(window.showTools) showTools(false);
  if(spPanel.style.display === 'none') rq = null;
  spTab = tab || spTab; spPanel.style.display = 'flex';
  document.querySelectorAll('#spTabs [data-tab]').forEach(b => b.classList.toggle('active', b.dataset.tab === spTab));
  ({cards: renderCards, planner: renderPlanner, focus: renderFocus})[spTab]();
}
function closeStudy(){ spPanel.style.display = 'none'; refreshSideInfo(); }
$('#spClose').onclick = closeStudy;
$('#openStudy').onclick = () => { openStudy(); closeDrawer(); };
$('#spTabs').addEventListener('click', e => { const b = e.target.closest('[data-tab]'); if(b) openStudy(b.dataset.tab); });
$('#miCard').onclick = e => {
  e.preventDefault(); const sel = savedRange && !savedRange.collapsed ? savedRange.toString().trim() : '';
  cardDraft = {page_id: currentId, front: sel, back: ''}; openStudy('cards');
};

/* flashcards */
async function renderCards(){
  const all = await api('GET', '/api/cards'); cardCache = all; const t = today();
  if(rq === null) rq = all.filter(c => c.due <= t);
  const pages = allPages().map(p => ({id: p.id, label: p.sectionTitle + ' › ' + p.title}));
  const dp = cardDraft ? cardDraft.page_id : currentId;
  $('#spBody').innerHTML = `<div class="row g-3">
   <div class="col-lg-7"><div class="card shadow-sm h-100"><div class="card-body" id="review"></div></div></div>
   <div class="col-lg-5"><div class="card shadow-sm"><div class="card-body">
     <h6 class="mb-2">${cardDraft && cardDraft.id ? 'Edit flashcard' : 'New flashcard'}</h6>
     <select id="cdPage" class="form-select form-select-sm mb-2">${pages.map(p => `<option value="${p.id}" ${p.id === dp ? 'selected' : ''}>${esc(p.label)}</option>`).join('')}</select>
     <textarea id="cdFront" class="form-control mb-2" rows="2" placeholder="Front (question or term)"></textarea>
     <textarea id="cdBack" class="form-control mb-2" rows="3" placeholder="Back (answer)"></textarea>
     <button class="btn btn-primary btn-sm" id="cdSave">Save card</button> <button class="btn btn-link btn-sm" id="cdClear">Clear</button></div></div></div></div>
   <h6 class="mt-4">All cards (${all.length})</h6>
   <div class="card shadow-sm"><div class="list-group list-group-flush">${all.map(c => `<div class="list-group-item d-flex gap-2 align-items-start">
     <div class="flex-grow-1" style="min-width:0"><div class="fw-semibold" style="white-space:pre-wrap">${esc(c.front)}</div><div class="small text-muted" style="white-space:pre-wrap">${esc(c.back)}</div>
     <div class="small"><a href="#" data-gopage="${c.page_id}">${esc(c.page_title)}</a> · due ${c.due <= t ? '<b class="text-danger">now</b>' : esc(c.due)}</div></div>
     <button class="btn btn-sm btn-outline-secondary" data-editcard="${c.id}"><i class="bi bi-pencil"></i></button>
     <button class="btn btn-sm btn-outline-danger" data-delcard="${c.id}"><i class="bi bi-trash"></i></button></div>`).join('') || '<div class="p-3 text-muted">No cards yet.</div>'}</div></div>`;
  $('#cdFront').value = cardDraft?.front || ''; $('#cdBack').value = cardDraft?.back || '';
  drawReview();
  if(cardDraft && !cardDraft.id) $(cardDraft.front ? '#cdBack' : '#cdFront').focus();
}
function drawReview(){
  const r = $('#review'); if(!r) return;
  if(!rq.length){
    r.innerHTML = `<div class="text-center py-5"><i class="bi bi-${cardCache.length ? 'emoji-smile' : 'card-text'} fs-1 text-success"></i><h5 class="mt-2">${cardCache.length ? 'All caught up!' : 'No flashcards yet'}</h5>
      <div class="text-muted small">${cardCache.length ? 'No cards are due right now. Come back later.' : 'Create one with the form, or select text in a page and use ⋮ → Make flashcard.'}</div></div>`; return;
  }
  const c = rq[0];
  r.innerHTML = `<div class="d-flex justify-content-between small text-muted"><span>${rq.length} left to review</span><a href="#" data-gopage="${c.page_id}">${esc(c.page_title)}</a></div>
    <div class="fc-front">${esc(c.front)}</div>` + (showBack
    ? `<hr><div class="fc-back">${esc(c.back) || '<span class="text-muted">(no answer written)</span>'}</div>
       <div class="d-flex gap-2 justify-content-center mt-3 flex-wrap">
        <button class="btn btn-outline-danger" data-grade="0">Again <small>(1)</small></button><button class="btn btn-outline-warning" data-grade="1">Hard <small>(2)</small></button>
        <button class="btn btn-outline-success" data-grade="2">Good <small>(3)</small></button><button class="btn btn-outline-primary" data-grade="3">Easy <small>(4)</small></button></div>`
    : `<div class="text-center mt-3"><button class="btn btn-dark" data-act="show">Show answer <small>(Space)</small></button></div>`);
}
async function gradeCard(g){
  const c = rq[0]; if(!c) return;
  const upd = await api('POST', `/api/cards/${c.id}/review`, {grade: g});
  rq.shift(); if(g === 0) rq.push({...c, ...upd}); showBack = false; drawReview();
  if(!rq.length) renderCards();
}
document.addEventListener('keydown', e => {
  if(spPanel.style.display === 'none' || spTab !== 'cards' || !rq || !rq.length || document.querySelector('.modal.show')) return;
  if(/INPUT|TEXTAREA|SELECT/.test(document.activeElement.tagName)) return;
  if(!showBack && (e.key === ' ' || e.key === 'Enter')){ e.preventDefault(); showBack = true; drawReview(); }
  else if(showBack && '1234'.includes(e.key) && e.key) gradeCard(Number(e.key) - 1);
});

/* planner */
async function renderPlanner(){
  const t = await api('GET', '/api/tasks');
  const todos = t.filter(x => x.kind === 'todo'), exams = t.filter(x => x.kind === 'exam').sort((a, b) => (a.due || '9') < (b.due || '9') ? -1 : 1);
  const badge = x => { if(!x.due) return ''; const n = daysUntil(x.due), cls = x.done ? 'secondary' : n < 0 ? 'danger' : n === 0 ? 'warning' : 'info';
    return `<span class="badge text-bg-${cls}">${n < 0 ? Math.abs(n) + 'd overdue' : n === 0 ? 'today' : 'in ' + n + 'd'} · ${x.due}</span>`; };
  $('#spBody').innerHTML = `<div class="row g-3">
   <div class="col-lg-7"><div class="card shadow-sm"><div class="card-body"><h6><i class="bi bi-check2-square"></i> To-do list</h6>
     <div class="input-group input-group-sm mb-3"><input id="tdText" class="form-control" placeholder="Add a task…"><input id="tdDue" type="date" class="form-control" style="max-width:150px"><button class="btn btn-primary" data-act="addtodo">Add</button></div>
     ${todos.map(x => `<div class="d-flex align-items-center gap-2 border-bottom py-2"><input type="checkbox" class="form-check-input mt-0" data-tdone="${x.id}" ${x.done ? 'checked' : ''}>
       <span class="flex-grow-1 ${x.done ? 'text-decoration-line-through text-muted' : ''}" data-tedit="${x.id}" style="cursor:text" title="Click to edit">${esc(x.text)}</span>${badge(x)}
       <button class="btn btn-sm btn-outline-danger" data-tdel="${x.id}"><i class="bi bi-x-lg"></i></button></div>`).join('') || '<div class="text-muted small">Nothing to do — nice!</div>'}
   </div></div></div>
   <div class="col-lg-5"><div class="card shadow-sm"><div class="card-body"><h6><i class="bi bi-calendar-event"></i> Exam countdown</h6>
     <div class="input-group input-group-sm mb-3"><input id="exText" class="form-control" placeholder="Exam name"><input id="exDue" type="date" class="form-control" style="max-width:150px"><button class="btn btn-primary" data-act="addexam">Add</button></div>
     ${exams.map(x => { const n = x.due ? daysUntil(x.due) : null; return `<div class="d-flex align-items-center gap-2 border-bottom py-2">
       <div class="text-center" style="width:62px"><div class="fs-3 fw-bold lh-1 ${n !== null && n >= 0 && n <= 3 ? 'text-danger' : ''}">${n === null ? '–' : n < 0 ? '✓' : n}</div><small class="text-muted">${n === null ? 'no date' : n < 0 ? 'passed' : n === 0 ? 'TODAY' : n === 1 ? 'day' : 'days'}</small></div>
       <div class="flex-grow-1"><div data-tedit="${x.id}" style="cursor:text" title="Click to edit">${esc(x.text)}</div><small class="text-muted">${esc(x.due || '')}</small></div>
       <button class="btn btn-sm btn-outline-danger" data-tdel="${x.id}"><i class="bi bi-x-lg"></i></button></div>`; }).join('') || '<div class="text-muted small">No exams added.</div>'}
   </div></div></div></div>`;
}

/* pomodoro */
const PM = {mode: 'focus', running: false, left: 0, last: 0, elapsed: 0, timer: null, ac: null,
  focusMin: Number(localStorage.getItem('pmF')) || 25, breakMin: Number(localStorage.getItem('pmB')) || 5};
PM.left = PM.focusMin * 60;
const pmFmt = s => { s = Math.max(0, Math.round(s)); return String(Math.floor(s / 60)).padStart(2, '0') + ':' + String(s % 60).padStart(2, '0'); };
const curSectionId = () => sectionOf(currentId)?.id ?? null;
function beep(){
  try{ const ac = PM.ac; if(!ac) return; ac.resume();
    [0, .25, .5].forEach(t => { const o = ac.createOscillator(), g = ac.createGain(); o.frequency.value = 880; o.connect(g); g.connect(ac.destination);
      g.gain.setValueAtTime(.2, ac.currentTime + t); g.gain.exponentialRampToValueAtTime(.001, ac.currentTime + t + .2); o.start(ac.currentTime + t); o.stop(ac.currentTime + t + .22); }); }catch(e){}
}
function pmDraw(){
  const t = pmFmt(PM.left), mode = PM.mode === 'focus' ? 'Focus' : 'Break';
  $('#pmTime').textContent = t; $('#pmMode').textContent = mode;
  $('#pmBtn').innerHTML = `<i class="bi bi-${PM.running ? 'pause' : 'play'}-fill"></i>`;
  const bt = $('#bigTime');
  if(bt){ bt.textContent = t; $('#bigMode').textContent = PM.mode === 'focus' ? 'Focus session' : 'Break time';
    $('#bigBtn').innerHTML = PM.running ? '<i class="bi bi-pause-fill"></i> Pause' : '<i class="bi bi-play-fill"></i> Start'; }
  document.title = PM.running ? `${t} · ${mode}` : 'Codex';
}
async function pmFlush(){
  const secs = Math.round(PM.elapsed); PM.elapsed = 0;
  if(secs >= 60) await api('POST', '/api/study', {seconds: secs, section_id: curSectionId()}).catch(() => {});
}
function pmTick(){
  const now = Date.now(), dt = (now - PM.last) / 1000; PM.last = now; PM.left -= dt;
  if(PM.mode === 'focus') PM.elapsed += dt;
  if(PM.left <= 0) pmDone(); else pmDraw();
}
function pmStart(){
  if(PM.running) return; PM.running = true; PM.last = Date.now(); PM.timer = setInterval(pmTick, 500);
  try{ PM.ac = PM.ac || new (window.AudioContext || window.webkitAudioContext)(); }catch(e){}
  if('Notification' in window && Notification.permission === 'default') Notification.requestPermission();
  pmDraw();
}
function pmPause(){ PM.running = false; clearInterval(PM.timer); pmDraw(); }
function pmToggle(){ PM.running ? pmPause() : pmStart(); }
function pmReset(){ pmPause(); pmFlush(); PM.mode = 'focus'; PM.left = PM.focusMin * 60; pmDraw(); if(spPanel.style.display !== 'none' && spTab === 'focus') renderFocus(); }
function pmDone(){
  const wasFocus = PM.mode === 'focus'; beep(); if(wasFocus) pmFlush();
  PM.mode = wasFocus ? 'break' : 'focus'; PM.left = (wasFocus ? PM.breakMin : PM.focusMin) * 60;
  toast(wasFocus ? 'Focus session done — take a break!' : 'Break over — back to studying.');
  if(document.hidden && 'Notification' in window && Notification.permission === 'granted') new Notification('Notebook', {body: wasFocus ? 'Focus session done — take a break' : 'Break over'});
  pmDraw(); if(spPanel.style.display !== 'none' && spTab === 'focus') renderFocus();
}
$('#pmBtn').onclick = pmToggle; $('#pmRst').onclick = pmReset;
async function renderFocus(){
  const st = await api('GET', '/api/study/stats'), mins = s => Math.round(s / 60), maxd = Math.max(60, ...st.days.map(d => d.seconds));
  $('#spBody').innerHTML = `<div class="row g-3"><div class="col-lg-6"><div class="card shadow-sm"><div class="card-body text-center">
     <div class="text-muted" id="bigMode"></div><div class="big-time my-3" id="bigTime">25:00</div>
     <div class="d-flex gap-2 justify-content-center"><button class="btn btn-dark btn-lg" id="bigBtn" data-act="pmtoggle"></button>
       <button class="btn btn-outline-secondary btn-lg" data-act="pmreset" title="Reset"><i class="bi bi-arrow-counterclockwise"></i></button>
       <button class="btn btn-outline-secondary btn-lg" data-act="pmskip" title="Skip to next phase"><i class="bi bi-skip-forward-fill"></i></button></div>
     <div class="row g-2 mt-3 justify-content-center"><div class="col-5"><label class="small text-muted">Focus (min)</label><input id="pmF" type="number" min="1" max="180" class="form-control form-control-sm" value="${PM.focusMin}"></div>
       <div class="col-5"><label class="small text-muted">Break (min)</label><input id="pmB" type="number" min="1" max="60" class="form-control form-control-sm" value="${PM.breakMin}"></div></div>
     <div class="small text-muted mt-3">Finished focus time is added to the header of the page you are studying.</div></div></div></div>
   <div class="col-lg-6"><div class="card shadow-sm"><div class="card-body"><h6><i class="bi bi-bar-chart"></i> Study time</h6>
     <div class="d-flex gap-4 mb-3"><div><div class="fs-3 fw-bold">${mins(st.today)}<small class="fs-6"> min</small></div><small class="text-muted">today</small></div>
       <div><div class="fs-3 fw-bold">${(st.week / 3600).toFixed(1)}<small class="fs-6"> h</small></div><small class="text-muted">last 7 days</small></div></div>
     <div class="d-flex align-items-end gap-2" style="height:90px">${st.days.map(d => `<div class="flex-fill text-center" title="${d.day}: ${mins(d.seconds)} min"><div style="height:${Math.max(3, d.seconds / maxd * 70)}px;background:var(--accent);border-radius:4px 4px 0 0"></div><small class="text-muted" style="font-size:.65rem">${d.day.slice(8)}</small></div>`).join('')}</div>
     <hr><div class="small fw-semibold mb-1">By header (7 days)</div>${st.sections.map(x => `<div class="d-flex justify-content-between small"><span>${esc(x.title)}</span><span>${mins(x.seconds)} min</span></div>`).join('') || '<div class="text-muted small">No sessions yet — start the timer!</div>'}
   </div></div></div></div>`;
  pmDraw();
}

/* sidebar reminders */
async function refreshSideInfo(){
  try{
    const [tasks, st] = await Promise.all([api('GET', '/api/tasks'), api('GET', '/api/cards/stats')]); const td = today();
    const ex = tasks.filter(x => x.kind === 'exam' && x.due && x.due >= td).sort((a, b) => a.due < b.due ? -1 : 1)[0];
    const open = tasks.filter(x => x.kind === 'todo' && !x.done).length;
    $('#sideExtra').innerHTML =
      (ex ? `<div role="button" data-go="planner"><i class="bi bi-calendar-event"></i> ${esc(ex.text)} — <b>${daysUntil(ex.due) === 0 ? 'today' : daysUntil(ex.due) + ' day(s)'}</b></div>` : '') +
      (st.due ? `<div role="button" data-go="cards"><i class="bi bi-card-text"></i> <b>${st.due}</b> flashcard(s) due</div>` : '') +
      (open ? `<div role="button" data-go="planner"><i class="bi bi-check2-square"></i> ${open} open task(s)</div>` : '');
  }catch(e){}
}
$('#sideExtra').addEventListener('click', e => { const g = e.target.closest('[data-go]'); if(g){ openStudy(g.dataset.go); closeDrawer(); } });

/* one click handler for everything inside the panel */
$('#spBody').addEventListener('click', async e => {
  const q = s => e.target.closest(s);
  let el;
  if(q('#cdSave')){
    const front = $('#cdFront').value.trim(), back = $('#cdBack').value.trim(), pid = $('#cdPage').value;
    if(!front) return toast('Write the front of the card first'); if(!pid) return toast('Create a page first');
    if(cardDraft && cardDraft.id) await api('PUT', '/api/cards/' + cardDraft.id, {front, back, page_id: Number(pid)});
    else await api('POST', `/api/pages/${pid}/cards`, {front, back});
    cardDraft = null; rq = null; toast('Card saved'); return renderCards();
  }
  if(q('#cdClear')){ cardDraft = null; return renderCards(); }
  if(q('[data-act="show"]')){ showBack = true; return drawReview(); }
  if((el = q('[data-grade]'))) return gradeCard(Number(el.dataset.grade));
  if((el = q('[data-editcard]'))){ cardDraft = cardCache.find(c => c.id === Number(el.dataset.editcard)); await renderCards(); return $('#spBody').scrollTo(0, 0); }
  if((el = q('[data-delcard]'))){ if(await confirmBox('Delete this flashcard?')){ await api('DELETE', '/api/cards/' + el.dataset.delcard); rq = null; renderCards(); } return; }
  if((el = q('[data-gopage]'))){ e.preventDefault(); closeStudy(); return openPage(Number(el.dataset.gopage)); }
  if(q('[data-act="addtodo"]') || q('[data-act="addexam"]')){
    const exam = !!q('[data-act="addexam"]'), text = $(exam ? '#exText' : '#tdText').value.trim(), due = $(exam ? '#exDue' : '#tdDue').value;
    if(!text) return toast('Write a name first');
    await api('POST', '/api/tasks', {kind: exam ? 'exam' : 'todo', text, due}); return renderPlanner();
  }
  if((el = q('[data-tdone]'))){ await api('PUT', '/api/tasks/' + el.dataset.tdone, {done: el.checked}); return renderPlanner(); }
  if((el = q('[data-tdel]'))){ await api('DELETE', '/api/tasks/' + el.dataset.tdel); return renderPlanner(); }
  if((el = q('[data-tedit]'))){ const t = await askText('Edit', el.textContent); if(t){ await api('PUT', '/api/tasks/' + el.dataset.tedit, {text: t}); renderPlanner(); } return; }
  if(q('[data-act="pmtoggle"]')) return pmToggle();
  if(q('[data-act="pmreset"]')) return pmReset();
  if(q('[data-act="pmskip"]')) return pmDone();
});
$('#spBody').addEventListener('change', e => {
  if(e.target.id === 'pmF' || e.target.id === 'pmB'){
    const f = e.target.id === 'pmF', v = Math.min(f ? 180 : 60, Math.max(1, Math.round(Number(e.target.value)) || 1)); e.target.value = v;
    PM[f ? 'focusMin' : 'breakMin'] = v; try{ localStorage.setItem(f ? 'pmF' : 'pmB', v); }catch(x){}
    if(!PM.running && ((f && PM.mode === 'focus') || (!f && PM.mode === 'break'))){ PM.left = v * 60; pmDraw(); }
  }
});
$('#spBody').addEventListener('keydown', e => {
  if(e.key === 'Enter' && (e.target.id === 'tdText' || e.target.id === 'exText')) $(e.target.id === 'tdText' ? '[data-act="addtodo"]' : '[data-act="addexam"]').click();
});
document.addEventListener('keydown', e => { if(e.key === 'Escape' && spPanel.style.display !== 'none' && !document.querySelector('.modal.show')) closeStudy(); });

/* ---------- appearance: dark mode, themes, fonts ---------- */
const THEMES = {classic: ['Classic leather', '#3a2c28', '#f0b429'], ocean: ['Ocean', '#16324a', '#4fc3f7'], forest: ['Forest', '#243b2f', '#9be564'], rose: ['Rose', '#4a2735', '#ff8fab'], violet: ['Violet', '#3b2a5a', '#ffb86b'], slate: ['Slate', '#2b2f36', '#8ab4f8']};
const FONTS = {default: ['System sans', 'system-ui,"Segoe UI",Roboto,sans-serif'], serif: ['Georgia (serif)', 'Georgia,"Times New Roman",serif'], merri: ['Merriweather', '"Merriweather",Georgia,serif'], lora: ['Lora', '"Lora",Georgia,serif'], inter: ['Inter', '"Inter",system-ui,sans-serif'], hand: ['Handwriting (Caveat)', '"Caveat","Segoe Print","Comic Sans MS",cursive'], patrick: ['Patrick Hand', '"Patrick Hand","Segoe Print",cursive'], mono: ['Monospace', '"Fira Code",ui-monospace,Consolas,monospace']};
const SIZES = {s: '.95rem', m: '1.05rem', l: '1.2rem', xl: '1.35rem'};
let SET = {mode: 'light', theme: 'classic', font: 'default', size: 'm'};
try{ Object.assign(SET, JSON.parse(localStorage.getItem('nbSettings') || '{}')); }catch(e){}
const isDark = () => SET.mode === 'dark' || (SET.mode === 'auto' && matchMedia('(prefers-color-scheme: dark)').matches);
function applySettings(save){
  const r = document.documentElement, dark = isDark();
  r.dataset.mode = dark ? 'dark' : 'light'; r.setAttribute('data-bs-theme', dark ? 'dark' : 'light'); r.dataset.theme = THEMES[SET.theme] ? SET.theme : 'classic';
  r.style.setProperty('--edfont', (FONTS[SET.font] || FONTS.default)[1]); r.style.setProperty('--edsize', SIZES[SET.size] || SIZES.m);
  $('#btnDark').innerHTML = `<i class="bi bi-${dark ? 'sun' : 'moon-stars'}"></i>`;
  if(save){ try{ localStorage.setItem('nbSettings', JSON.stringify(SET)); }catch(e){} }
  document.querySelectorAll('#setMode [data-v]').forEach(b => b.classList.toggle('active', b.dataset.v === SET.mode));
  document.querySelectorAll('#setSize [data-v]').forEach(b => b.classList.toggle('active', b.dataset.v === SET.size));
  document.querySelectorAll('#setThemes .swatch').forEach(b => b.classList.toggle('on', b.dataset.v === SET.theme));
  $('#setFont').value = SET.font; $('#setAutoCard').checked = SET.autoCard !== false;
  if(window.onThemeChange) window.onThemeChange(dark);
}
$('#setThemes').innerHTML = Object.entries(THEMES).map(([k, v]) => `<div class="swatch" data-v="${k}" title="${v[0]}" style="background:${v[1]}"><i style="background:${v[2]}"></i></div>`).join('');
$('#setFont').innerHTML = Object.entries(FONTS).map(([k, v]) => `<option value="${k}">${v[0]}</option>`).join('');
$('#setMode').onclick = e => { const b = e.target.closest('[data-v]'); if(b){ SET.mode = b.dataset.v; applySettings(true); } };
$('#setSize').onclick = e => { const b = e.target.closest('[data-v]'); if(b){ SET.size = b.dataset.v; applySettings(true); } };
$('#setThemes').onclick = e => { const b = e.target.closest('.swatch'); if(b){ SET.theme = b.dataset.v; applySettings(true); } };
$('#setAutoCard').onchange = e => { SET.autoCard = e.target.checked; applySettings(true); };
$('#setFont').onchange = e => { SET.font = e.target.value; applySettings(true); };
$('#setReset').onclick = () => { SET = {mode: 'light', theme: 'classic', font: 'default', size: 'm'}; applySettings(true); };
$('#btnDark').onclick = () => { SET.mode = isDark() ? 'light' : 'dark'; applySettings(true); };
$('#openSettings').onclick = () => { bootstrap.Modal.getOrCreateInstance($('#setModal')).show(); closeDrawer(); };
matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => { if(SET.mode === 'auto') applySettings(false); });
applySettings(false);

/* ---------- tables ---------- */
const tblBox = $('#tblBox');
function cellAtCaret(){
  const s = getSelection(); if(!s.rangeCount) return null; let n = s.anchorNode; n = n && (n.nodeType === 3 ? n.parentElement : n);
  const c = n && n.closest && n.closest('td,th'); return c && ed.contains(c) ? c : null;
}
function placeTblBox(){
  const c = cellAtCaret(); if(!c){ tblBox.style.display = 'none'; return; }
  const pr = paperEl.getBoundingClientRect(), r = c.closest('table').getBoundingClientRect();
  tblBox.style.display = 'flex'; tblBox.style.left = Math.max(0, r.left - pr.left) + 'px'; tblBox.style.top = Math.max(0, r.top - pr.top - 36) + 'px';
}
tblBox.addEventListener('mousedown', e => e.preventDefault());
function tblOp(op){
  const c = cellAtCaret(); if(!c) return;
  const tr = c.parentElement, t = c.closest('table'), rows = [...t.rows], ri = rows.indexOf(tr), ci = c.cellIndex;
  const mk = tag => { const x = document.createElement(tag || 'td'); x.innerHTML = '<br>'; return x; };
  let focus = null;
  if(op === 'rowUp' || op === 'rowDown'){
    const nr = document.createElement('tr'); [...tr.cells].forEach(() => nr.appendChild(mk('td')));
    tr.parentNode.insertBefore(nr, op === 'rowUp' ? tr : tr.nextSibling); focus = nr.cells[Math.min(ci, nr.cells.length - 1)];
  } else if(op === 'colLeft' || op === 'colRight'){
    rows.forEach(r => { const ref = r.cells[ci]; if(!ref) return; const nc = mk(ref.tagName === 'TH' ? 'th' : 'td'); r.insertBefore(nc, op === 'colLeft' ? ref : ref.nextSibling); if(r === tr) focus = nc; });
  } else if(op === 'delRow'){
    if(rows.length <= 1) return tblOp('delTable'); const next = rows[ri + 1] || rows[ri - 1]; tr.remove(); focus = next.cells[Math.min(ci, next.cells.length - 1)];
  } else if(op === 'delCol'){
    if(tr.cells.length <= 1) return tblOp('delTable'); rows.forEach(r => r.cells[ci] && r.cells[ci].remove()); focus = tr.cells[Math.min(ci, tr.cells.length - 1)];
  } else if(op === 'hdr'){
    const first = rows[0], allTh = [...first.cells].every(x => x.tagName === 'TH');
    [...first.cells].forEach(x => { const n = document.createElement(allTh ? 'td' : 'th'); n.innerHTML = x.innerHTML; x.replaceWith(n); }); focus = first.cells[Math.min(ci, first.cells.length - 1)];
  } else if(op === 'delTable'){ t.remove(); ensureTrailingLine(); tblBox.style.display = 'none'; scheduleSave(); return; }
  if(focus) placeCaret(focus); scheduleSave(); placeTblBox();
}
tblBox.addEventListener('click', e => { const b = e.target.closest('[data-op]'); if(b) tblOp(b.dataset.op); });
$('#btnTable').onclick = () => { rememberRange(); bootstrap.Modal.getOrCreateInstance($('#tblModal')).show(); };
$('#tblOk').onclick = () => {
  const clampN = (v, a, b) => Math.min(b, Math.max(a, Math.round(Number(v)) || a));
  const r = clampN($('#tblRows').value, 1, 30), c = clampN($('#tblCols').value, 1, 10), h = $('#tblHdr').checked;
  const row = (tag) => '<tr>' + `<${tag}><br></${tag}>`.repeat(c) + '</tr>';
  const html = '<table class="nb-table"><tbody>' + (h ? row('th') : '') + row('td').repeat(h ? r - 1 : r) + '</tbody></table><p><br></p>';
  $('#tblModal').addEventListener('hidden.bs.modal', () => { restoreRange(); document.execCommand('insertHTML', false, html); scheduleSave(); }, {once: true});
  bootstrap.Modal.getInstance($('#tblModal')).hide();
};
ed.addEventListener('keydown', e => {
  if(e.key !== 'Tab') return;
  const c = cellAtCaret();
  if(c){
    e.preventDefault(); const cells = [...c.closest('table').querySelectorAll('td,th')], i = cells.indexOf(c) + (e.shiftKey ? -1 : 1);
    if(i >= cells.length) tblOp('rowDown'); else if(i >= 0) placeCaret(cells[i]); return;
  }
  if(preOf(getSelection().anchorNode)){ e.preventDefault(); document.execCommand('insertText', false, '    '); }
});

/* ---------- code blocks with syntax highlighting ---------- */
let activePre = null;
ed.addEventListener('keydown', e => {          // Enter inside code = new line in the SAME block; Ctrl+Enter = leave the block
  if(e.key !== 'Enter' || e.defaultPrevented) return;
  const p = preOf(getSelection().anchorNode); if(!p) return;
  e.preventDefault();
  if(e.ctrlKey || e.metaKey){ const np = document.createElement('p'); np.innerHTML = '<br>'; p.after(np); placeCaret(np); }
  else document.execCommand('insertLineBreak');
  scheduleSave();
});
const preOf = n => { n = n && (n.nodeType === 3 ? n.parentElement : n); const p = n && n.closest && n.closest('pre'); return p && ed.contains(p) ? p : null; };
function preText(pre){ const c = pre.cloneNode(true); c.querySelectorAll('br').forEach(b => b.replaceWith('\n')); return c.textContent; }
async function ensureLang(lang){
  if(lang === 'auto' || lang === 'plaintext' || (window.hljs && hljs.getLanguage(lang))) return;
  const extra = {x86asm: 'x86asm'}[lang]; if(!extra) return;
  await loadLib('hljs' + extra, 'https://cdn.jsdelivr.net/npm/@highlightjs/cdn-assets@11.9.0/languages/' + extra + '.min.js');
}
async function hlCode(pre){
  if(!window.hljs || pre.classList.contains('hl')) return;
  const lang = pre.dataset.lang || 'auto'; if(lang === 'plaintext') return;
  const code = preText(pre).replace(/\n+$/, ''); if(!code.trim()) return;
  await ensureLang(lang);
  let r; try{ r = (lang !== 'auto' && hljs.getLanguage(lang)) ? hljs.highlight(code, {language: lang, ignoreIllegals: true}) : hljs.highlightAuto(code); }catch(e){ return; }
  if(pre.classList.contains('hl') || preText(pre).replace(/\n+$/, '') !== code) return;
  pre.innerHTML = r.value; pre.classList.add('hl');
}
function unhlCode(pre){
  if(!pre.classList.contains('hl')) return;
  const s = getSelection(); let off = null;
  if(s.rangeCount && pre.contains(s.anchorNode)){ const r = document.createRange(); r.selectNodeContents(pre); r.setEnd(s.anchorNode, s.anchorOffset); off = r.toString().length; }
  pre.textContent = preText(pre); pre.classList.remove('hl');
  if(off !== null && pre.firstChild){ const r = document.createRange(); r.setStart(pre.firstChild, Math.min(off, pre.firstChild.length)); r.collapse(true); s.removeAllRanges(); s.addRange(r); }
}
function hlAll(){ activePre = null; ed.querySelectorAll('pre').forEach(hlCode); }
function trackPre(){
  const s = getSelection(), p = s.rangeCount && ed.contains(s.anchorNode) ? preOf(s.anchorNode) : null;
  if(p === activePre) return; const prev = activePre; activePre = p;
  if(prev && prev.isConnected) hlCode(prev);
  if(p){ unhlCode(p); $('#codeLang').value = p.dataset.lang || 'auto'; }
}
document.addEventListener('selectionchange', () => { placeTblBox(); trackPre(); });
ed.addEventListener('blur', () => { if(activePre && activePre.isConnected){ const p = activePre; activePre = null; hlCode(p); } });
$('#btnCode').onclick = () => {
  restoreRange(); const cur = preOf(getSelection().anchorNode);
  document.execCommand('formatBlock', false, cur ? 'p' : 'pre');
  const p = preOf(getSelection().anchorNode); if(p && !cur) p.dataset.lang = $('#codeLang').value;
  ensureTrailingLine(); trackPre(); scheduleSave();
};
$('#codeLang').onchange = () => {
  const p = activePre || preOf(savedRange && savedRange.startContainer); if(!p) return toast('Click inside a code block first');
  p.dataset.lang = $('#codeLang').value; scheduleSave(); if(p !== activePre){ unhlCode(p); hlCode(p); }
};
ed.addEventListener('paste', e => {
  const p = preOf(getSelection().anchorNode); if(!p) return;
  e.preventDefault(); document.execCommand('insertText', false, e.clipboardData.getData('text/plain'));
}, true);

/* ---------- page templates ---------- */
const CHK = t => `<div><input type="checkbox">&nbsp;${t}</div>`;
const TEMPLATES = [
 {id: 'ctf', name: 'CTF writeup', title: 'CTF writeup', icon: 'flag', desc: 'Challenge info, recon, approach, flag and lessons learned.',
  html: '<h2>Challenge: </h2><p><b>CTF / Event:</b> &nbsp; <b>Category:</b> &nbsp; <b>Points:</b> &nbsp; <b>Date:</b> {{date}}</p>'
    + '<h3>Challenge description</h3><p><br></p><h3>Files / tools given</h3><ul><li><br></li></ul>'
    + '<h3>Recon</h3><ul><li><br></li></ul><h3>Approach</h3><ol><li><br></li></ol>'
    + '<h3>Solution</h3><pre data-lang="auto"><br></pre><h3>Flag</h3><p><br></p><h3>Lessons learned</h3><ul><li><br></li></ul>'},
 {id: 'vulnresearch', name: 'Vulnerability research', title: 'Vulnerability research', icon: 'bug', desc: 'Target, mitigations, root cause, crash triage and impact.',
  html: '<h2>Target: </h2><p><b>Version / build:</b> &nbsp; <b>Date:</b> {{date}}</p>'
    + '<h3>Protections enabled</h3>' + CHK('ASLR') + CHK('NX / DEP') + CHK('PIE') + CHK('Stack canary') + CHK('RELRO (full)') + CHK('CFI / CET')
    + '<h3>Attack surface</h3><ul><li><br></li></ul><h3>Root cause</h3><p><br></p>'
    + '<h3>Crash triage</h3><table class="nb-table"><tbody><tr><th style="width:28%">Field</th><th>Value</th></tr>'
    + ['Signal / exception', 'Faulting instruction', 'Register state', 'Reproduction rate'].map(k => `<tr><td>${k}</td><td><br></td></tr>`).join('') + '</tbody></table>'
    + '<h3>Impact</h3><p><br></p><h3>Disclosure status</h3><p>Not reported yet</p><h3>Notes</h3><p><br></p>'},
 {id: 'reverse', name: 'Reverse engineering', title: 'Reverse engineering notes', icon: 'cpu', desc: 'Binary info, tools, function map and annotated findings.',
  html: '<h2>Binary: </h2><p><b>Arch:</b> &nbsp; <b>Format:</b> &nbsp; <b>Compiler / packer:</b> &nbsp; <b>Date:</b> {{date}}</p>'
    + '<h3>Tools used</h3><ul><li><br></li></ul><h3>Function map</h3><table class="nb-table"><tbody><tr><th>Address</th><th>Name</th><th>Notes</th></tr>'
    + '<tr><td><br></td><td><br></td><td><br></td></tr>'.repeat(5) + '</tbody></table>'
    + '<h3>Interesting strings / constants</h3><ul><li><br></li></ul><h3>Annotated snippet</h3><pre data-lang="x86asm"><br></pre><h3>Findings</h3><p><br></p>'},
 {id: 'bounty', name: 'Bug bounty report', title: 'Bug bounty report', icon: 'shield-exclamation', desc: 'Scope, reproduction steps, impact and remediation.',
  html: '<h2>Report: </h2><p><b>Program:</b> &nbsp; <b>Target / asset:</b> &nbsp; <b>Date found:</b> {{date}}</p>'
    + '<h3>Summary</h3><p><br></p><h3>Severity</h3><p>CVSS: &nbsp; Rating: </p>'
    + '<h3>Steps to reproduce</h3><ol><li><br></li></ol><h3>Impact</h3><p><br></p>'
    + '<h3>Proof of concept</h3><pre data-lang="auto"><br></pre><h3>Suggested remediation</h3><p><br></p>'
    + '<h3>Status</h3>' + CHK('Submitted') + CHK('Triaged') + CHK('Fixed') + CHK('Rewarded')},
 {id: 'blank', name: 'Blank page', title: '', icon: 'file-earmark', desc: 'Start with an empty page.', html: ''},
 {id: 'cornell', name: 'Cornell notes', title: 'Cornell notes', icon: 'layout-sidebar', desc: 'Cues on the left, notes on the right, summary below.',
  html: '<h2>Topic: </h2><p><b>Course:</b> &nbsp; <b>Date:</b> {{date}}</p><table class="nb-table"><tbody><tr><th style="width:32%">Cues / Questions</th><th>Notes</th></tr><tr><td style="height:260px"><br></td><td><br></td></tr></tbody></table><h3>Summary</h3><p><br></p><p><br></p>'},
 {id: 'lecture', name: 'Lecture outline', title: 'Lecture outline', icon: 'easel', desc: 'Objectives, outline, key terms and review questions.',
  html: '<h2>Lecture: </h2><p><b>Course:</b> &nbsp; <b>Date:</b> {{date}}</p><h3>Learning objectives</h3><ul><li><br></li></ul><h3>Outline</h3><ol><li>Main idea<ul><li>Supporting detail</li></ul></li><li><br></li></ol><h3>Key terms</h3><ul><li><br></li></ul><h3>Questions to review</h3><ul><li><br></li></ul>'},
 {id: 'guide', name: 'Exam study guide', title: 'Study guide', icon: 'journal-check', desc: 'Topic checklist, formulas and practice questions.',
  html: '<h2>Study guide: </h2><p><b>Exam date:</b> </p><h3>Topics to cover</h3>' + CHK('Topic 1') + CHK('Topic 2') + CHK('Topic 3') + '<h3>Key formulas / facts</h3><ul><li><br></li></ul><h3>Practice questions</h3><ol><li><br></li></ol><h3>Things I find hard</h3><ul><li><br></li></ul>'},
 {id: 'reading', name: 'Reading notes', title: 'Reading notes', icon: 'book', desc: 'Source, main argument, quotes and your thoughts.',
  html: '<h2>Reading notes</h2><p><b>Title / author:</b> </p><p><b>Date read:</b> {{date}}</p><h3>Main argument</h3><p><br></p><h3>Key points</h3><ul><li><br></li></ul><h3>Quotes</h3><blockquote>Quote… (page )</blockquote><h3>My thoughts / questions</h3><p><br></p>'},
 {id: 'problem', name: 'Problem solving', title: 'Problem solving', icon: 'calculator', desc: 'Given, find, plan, solution and check.',
  html: '<h2>Problem</h2><p><br></p><h3>Given</h3><ul><li><br></li></ul><h3>Find</h3><p><br></p><h3>Plan / formulas</h3><ul><li><br></li></ul><h3>Solution</h3><ol><li><br></li></ol><h3>Check</h3>' + CHK('Units / signs correct') + CHK('Answer makes sense')},
 {id: 'vocab', name: 'Vocabulary table', title: 'Vocabulary', icon: 'translate', desc: 'Term, definition and example in a table.',
  html: '<h2>Vocabulary</h2><table class="nb-table"><tbody><tr><th>Term</th><th>Definition</th><th>Example</th></tr>' + '<tr><td><br></td><td><br></td><td><br></td></tr>'.repeat(6) + '</tbody></table><p><br></p>'},
 {id: 'week', name: 'Weekly study plan', title: 'Weekly study plan', icon: 'calendar-week', desc: 'A table for the days of the week with checkboxes.',
  html: '<h2>Week of {{date}}</h2><table class="nb-table"><tbody><tr><th style="width:16%">Day</th><th>Subject</th><th>Plan</th><th style="width:12%">Done</th></tr>' + ['Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat', 'Sun'].map(d => `<tr><td>${d}</td><td><br></td><td><br></td><td><input type="checkbox"></td></tr>`).join('') + '</tbody></table><h3>Goals this week</h3><ul><li><br></li></ul>'},
];
const tplHtml = t => t.html.replace(/\{\{date\}\}/g, today());
function pickTemplate(withTitle){
  return new Promise(res => {
    const el = $('#npModal'), m = bootstrap.Modal.getOrCreateInstance(el); let sel = 'blank', done = false;
    $('#npHead').textContent = withTitle ? 'New page' : 'Insert template'; $('#npOk').textContent = withTitle ? 'Create page' : 'Insert';
    $('#npTitleRow').style.display = withTitle ? '' : 'none'; $('#npTitle').value = '';
    const grid = $('#npGrid');
    grid.innerHTML = TEMPLATES.filter(t => withTitle || t.html).map(t => `<div class="col-6 col-md-4"><button class="btn btn-outline-secondary w-100 h-100 text-start p-3 tpl ${t.id === sel ? 'on' : ''}" data-v="${t.id}">
      <i class="bi bi-${t.icon} fs-4"></i><div class="fw-semibold mt-1">${esc(t.name)}</div><div class="small text-muted">${esc(t.desc)}</div></button></div>`).join('');
    if(!withTitle){ sel = TEMPLATES[1].id; grid.querySelector(`[data-v="${sel}"]`).classList.add('on'); }
    grid.onclick = e => { const b = e.target.closest('[data-v]'); if(!b) return; sel = b.dataset.v; grid.querySelectorAll('.tpl').forEach(x => x.classList.toggle('on', x === b)); };
    const ok = () => { if(done) return; done = true; m.hide(); res({title: $('#npTitle').value.trim(), tpl: sel}); };
    $('#npOk').onclick = ok; $('#npTitle').onkeydown = e => { if(e.key === 'Enter') ok(); };
    el.addEventListener('hidden.bs.modal', () => { if(!done){ done = true; res(null); } }, {once: true});
    el.addEventListener('shown.bs.modal', () => { if(withTitle) $('#npTitle').focus(); }, {once: true});
    m.show();
  });
}
$('#miTpl').onclick = async e => {
  e.preventDefault(); if(!currentId) return; rememberRange();
  const r = await pickTemplate(false); if(!r) return; const t = TEMPLATES.find(x => x.id === r.tpl); if(!t || !t.html) return;
  restoreRange(); document.execCommand('insertHTML', false, tplHtml(t) + '<p><br></p>'); ensureTrailingLine(); scheduleSave();
};

/* ---------- math (KaTeX) and diagrams (Mermaid) ---------- */
const LIBS = {katex: 'https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js', mermaid: 'https://cdn.jsdelivr.net/npm/mermaid@10.9.1/dist/mermaid.min.js'};
const libP = {};
function loadLib(name, srcOverride){
  if(!srcOverride && window[name]) return Promise.resolve(window[name]);
  return libP[name] || (libP[name] = new Promise((res, rej) => {
    const sc = document.createElement('script'); sc.src = srcOverride || LIBS[name]; sc.onload = () => res(window[name]);
    sc.onerror = () => { delete libP[name]; rej(new Error(name + ' could not be loaded (internet needed)')); }; document.head.appendChild(sc);
  }));
}
async function renderMath(el){
  const tex = el.dataset.tex || '', disp = el.dataset.display === '1';
  try{ const k = await loadLib('katex'); k.render(tex, el, {throwOnError: false, displayMode: disp}); el.classList.remove('err'); el.title = 'Click to edit'; }
  catch(e){ el.textContent = (disp ? '$$' : '$') + tex + (disp ? '$$' : '$'); el.classList.add('err'); el.title = String(e.message || e); }
  el.classList.add('rendered');
}
let mmCount = 0;
async function renderDiagram(el){
  const src = el.dataset.src || ''; el.classList.add('rendered');
  try{
    const mm = await loadLib('mermaid'); mm.initialize({startOnLoad: false, securityLevel: 'strict', theme: isDark() ? 'dark' : 'default'});
    const id = 'mmd' + (++mmCount);
    try{ const r = await mm.render(id, src); el.innerHTML = r.svg; }
    finally{ const t = document.getElementById('d' + id); if(t) t.remove(); }
  }catch(e){ el.innerHTML = '<pre class="diagram-err"></pre>'; el.firstChild.textContent = 'Diagram error: ' + String(e.message || e).split('\n')[0] + '\n\n' + src; }
}
function renderRich(){
  ed.querySelectorAll('.math-node:not(.rendered)').forEach(renderMath);
  ed.querySelectorAll('.diagram-node:not(.rendered)').forEach(renderDiagram);
  ed.querySelectorAll('pre:not(.hl)').forEach(hlCode);
}
window.onThemeChange = () => { ed.querySelectorAll('.diagram-node').forEach(n => n.classList.remove('rendered')); if(window.mermaid) renderRich(); };

/* math dialog */
let mathTarget = null;
const MSYMS = [['a/b', '\\frac{a}{b}'], ['\u221ax', '\\sqrt{x}'], ['x\u00b2', 'x^{2}'], ['x\u2081', 'x_{1}'], ['\u03a3', '\\sum_{i=1}^{n}'], ['\u222b', '\\int_{a}^{b}'], ['lim', '\\lim_{x \\to \\infty}'], ['\u03b1', '\\alpha'], ['\u03b2', '\\beta'], ['\u03b8', '\\theta'], ['\u03bb', '\\lambda'], ['\u03bc', '\\mu'], ['\u03c0', '\\pi'], ['\u03c3', '\\sigma'], ['\u0394', '\\Delta'], ['\u03c9', '\\omega'], ['\u2264', '\\leq'], ['\u2265', '\\geq'], ['\u2260', '\\neq'], ['\u2248', '\\approx'], ['\u00b1', '\\pm'], ['\u00d7', '\\times'], ['\u2192', '\\to'], ['\u221e', '\\infty'], ['v\u20d7', '\\vec{v}'], ['matrix', '\\begin{bmatrix} a & b \\\\ c & d \\end{bmatrix}']];
$('#mathSyms').innerHTML = MSYMS.map((x, i) => `<button class="btn btn-sm btn-outline-secondary" data-i="${i}" type="button">${esc(x[0])}</button>`).join('');
$('#mathSyms').onclick = e => { const b = e.target.closest('[data-i]'); if(!b) return; const t = $('#mathSrc'), v = MSYMS[b.dataset.i][1], a = t.selectionStart, z = t.selectionEnd;
  t.value = t.value.slice(0, a) + v + t.value.slice(z); t.focus(); t.selectionStart = t.selectionEnd = a + v.length; previewMath(); };
function previewMath(){
  const box = $('#mathPrev'), t = $('#mathSrc').value;
  if(!t.trim()){ box.textContent = 'Preview appears here'; box.className = 'border rounded text-center p-3 text-muted'; return; }
  box.className = 'border rounded text-center p-3'; box.dataset.tex = t; box.dataset.display = $('#mathDisp').checked ? '1' : '0'; renderMath(box);
}
$('#mathSrc').addEventListener('input', previewMath); $('#mathDisp').addEventListener('change', previewMath);
function openMath(node){
  mathTarget = node || null;
  $('#mathSrc').value = node ? node.dataset.tex : (savedRange && !savedRange.collapsed ? savedRange.toString() : '');
  $('#mathDisp').checked = node ? node.dataset.display === '1' : false;
  $('#mathDel').style.display = node ? '' : 'none'; $('#mathOk').textContent = node ? 'Update' : 'Insert';
  const el = $('#mathModal'); bootstrap.Modal.getOrCreateInstance(el).show(); el.addEventListener('shown.bs.modal', () => $('#mathSrc').focus(), {once: true}); previewMath();
}
$('#btnMath').onclick = () => { rememberRange(); openMath(null); };
$('#mathOk').onclick = () => {
  const tex = $('#mathSrc').value.trim(); if(!tex) return; const disp = $('#mathDisp').checked ? '1' : '0', tgt = mathTarget, el = $('#mathModal');
  el.addEventListener('hidden.bs.modal', () => {
    if(tgt){ tgt.dataset.tex = tex; tgt.dataset.display = disp; tgt.classList.remove('rendered'); renderMath(tgt); }
    else{ restoreRange(); document.execCommand('insertHTML', false, `<span class="math-node" data-tex="${esc(tex)}" data-display="${disp}" contenteditable="false"></span>${disp === '1' ? '<p><br></p>' : '&nbsp;'}`); renderRich(); }
    scheduleSave();
  }, {once: true});
  bootstrap.Modal.getInstance(el).hide();
};
$('#mathDel').onclick = () => { const tgt = mathTarget; $('#mathModal').addEventListener('hidden.bs.modal', () => { if(tgt){ tgt.remove(); scheduleSave(); } }, {once: true}); bootstrap.Modal.getInstance($('#mathModal')).hide(); };

/* diagram dialog */
let diaTarget = null, diaTimer = null;
const DIA = {
  'Flowchart': 'flowchart TD\n  A[Start] --> B{Decision}\n  B -- Yes --> C[Do it]\n  B -- No --> D[Skip]\n  C --> E[End]\n  D --> E',
  'Mind map': 'mindmap\n  root((Topic))\n    Idea 1\n      Detail A\n      Detail B\n    Idea 2\n      Detail C',
  'Sequence': 'sequenceDiagram\n  Student->>Teacher: Question\n  Teacher-->>Student: Answer',
  'Timeline': 'timeline\n  title History\n  1900 : Event A\n  1950 : Event B\n  2000 : Event C',
  'Class diagram': 'classDiagram\n  class Animal {\n    +name\n    +eat()\n  }\n  Animal <|-- Dog\n  Animal <|-- Cat',
  'State diagram': 'stateDiagram-v2\n  [*] --> Idle\n  Idle --> Running : start\n  Running --> Idle : stop\n  Running --> [*]',
  'ER diagram': 'erDiagram\n  STUDENT ||--o{ ENROLLMENT : has\n  COURSE ||--o{ ENROLLMENT : includes',
  'Pie chart': 'pie title Time spent\n  "Study" : 40\n  "Sleep" : 35\n  "Free" : 25',
  'Gantt plan': 'gantt\n  title Study plan\n  dateFormat YYYY-MM-DD\n  section Revision\n  Chapter 1 :a1, 2026-01-01, 5d\n  Chapter 2 :after a1, 5d',
  'Stack frame': 'flowchart TD\n  subgraph Stack[" "]\n    direction TB\n    A["high addresses"]\n    B["saved RBP / EBP"]\n    C["return address"]\n    D["local variables / buffer"]\n    E["low addresses \u2193 grows down"]\n    A --> B --> C --> D --> E\n  end',
  'Heap chunk layout': 'flowchart TD\n  subgraph Chunk["malloc chunk"]\n    direction TB\n    A["prev_size (if prev free)"]\n    B["size | flags (A/M/P)"]\n    C["user data / fd, bk if free"]\n    D["next chunk..."]\n    A --> B --> C --> D\n  end',
  'Exploit chain (concept)': 'flowchart LR\n  A[Recon] --> B[Find vulnerable path]\n  B --> C[Confirm crash / trigger]\n  C --> D[Identify primitive]\n  D --> E[Build control over execution]\n  E --> F[Bypass mitigations]\n  F --> G[Achieve goal]',
  'Protocol / format state machine': 'stateDiagram-v2\n  [*] --> Header\n  Header --> Field1 : parse\n  Field1 --> Field2 : parse\n  Field2 --> Done : validate\n  Field2 --> Error : malformed\n  Error --> [*]\n  Done --> [*]'
};
$('#diaPreset').innerHTML = '<option value="">Start from an example\u2026</option>' + Object.keys(DIA).map(k => `<option>${esc(k)}</option>`).join('');
$('#diaPreset').onchange = e => { if(DIA[e.target.value]){ $('#diaSrc').value = DIA[e.target.value]; previewDia(); } e.target.value = ''; };
async function previewDia(){
  const box = $('#diaPrev'), src = $('#diaSrc').value; if(!src.trim()){ box.innerHTML = '<span class="text-muted">Preview appears here</span>'; return; }
  const tmp = document.createElement('div'); tmp.dataset.src = src; await renderDiagram(tmp);
  if($('#diaSrc').value === src) box.replaceChildren(...tmp.childNodes);
}
$('#diaSrc').addEventListener('input', () => { clearTimeout(diaTimer); diaTimer = setTimeout(previewDia, 450); });
function openDiagram(node){
  diaTarget = node || null; $('#diaSrc').value = node ? node.dataset.src : DIA['Flowchart'];
  $('#diaDel').style.display = node ? '' : 'none'; $('#diaOk').textContent = node ? 'Update' : 'Insert';
  bootstrap.Modal.getOrCreateInstance($('#diaModal')).show(); previewDia();
}
$('#btnDiagram').onclick = () => { rememberRange(); openDiagram(null); };
$('#diaOk').onclick = () => {
  const src = $('#diaSrc').value.trim(); if(!src) return; const tgt = diaTarget, el = $('#diaModal');
  el.addEventListener('hidden.bs.modal', () => {
    if(tgt){ tgt.dataset.src = src; tgt.classList.remove('rendered'); tgt.innerHTML = ''; renderDiagram(tgt); }
    else{ restoreRange(); document.execCommand('insertHTML', false, `<div class="diagram-node" data-src="${esc(src)}" contenteditable="false"></div><p><br></p>`); renderRich(); }
    scheduleSave();
  }, {once: true});
  bootstrap.Modal.getInstance(el).hide();
};
$('#diaDel').onclick = () => { const tgt = diaTarget; $('#diaModal').addEventListener('hidden.bs.modal', () => { if(tgt){ tgt.remove(); scheduleSave(); } }, {once: true}); bootstrap.Modal.getInstance($('#diaModal')).hide(); };
ed.addEventListener('click', e => {
  const m = e.target.closest && e.target.closest('.math-node'); if(m){ rememberRange(); return openMath(m); }
  const d = e.target.closest && e.target.closest('.diagram-node'); if(d) openDiagram(d);
});

/* ---------- link cards (YouTube / web) ---------- */
function cardHtml(d){
  const u = esc(d.url), yt = d.kind === 'youtube';
  return `<div class="link-card" contenteditable="false" data-url="${u}" data-kind="${esc(d.kind)}" data-vid="${esc(d.video_id || '')}">` +
    (d.thumb ? `<a class="lc-thumb" href="${u}" target="_blank" rel="noopener"><img src="${esc(d.thumb)}" alt="">${yt ? '<span class="lc-play"></span>' : ''}</a>` : '') +
    `<div class="lc-body"><a class="lc-title" href="${u}" target="_blank" rel="noopener">${esc(d.title)}</a><div class="lc-site">${yt ? '▶ ' : ''}${esc(d.site)}</div>` +
    (d.description ? `<div class="lc-desc">${esc(d.description)}</div>` : '') + `</div><span class="lc-x" title="Remove card">×</span></div>`;
}
const hostOf = u => { try{ return new URL(u).hostname.replace(/^www\./, ''); }catch(e){ return u; } };
function fixLoadingCards(){   // a page saved while a card was still loading
  ed.querySelectorAll('.link-card.loading').forEach(n => { const u = (n.querySelector('.lc-site') || {}).textContent || '';
    n.outerHTML = cardHtml({url: u, kind: 'web', title: u, site: hostOf(u), description: '', thumb: ''}); });
}
async function insertLinkCard(url){
  if(!currentId) return; const pid = currentId, key = 'lc' + Date.now();
  restoreRange();
  document.execCommand('insertHTML', false, `<div class="link-card loading" contenteditable="false" data-lc="${key}"><div class="lc-body"><span class="lc-title">Loading link…</span><div class="lc-site">${esc(url)}</div></div></div><p><br></p>`);
  scheduleSave();
  let d; try{ d = await api('POST', `/api/pages/${pid}/linkcard`, {url}); }
  catch(e){ d = {url, kind: 'web', title: url, site: hostOf(url), description: '', thumb: ''}; toast('Could not read the link details — added a simple card'); }
  const ph = ed.querySelector(`[data-lc="${key}"]`);
  if(ph && pid === currentId){ ph.outerHTML = cardHtml(d); scheduleSave(); }
  else if(pid !== currentId){ // user left the page: patch the saved copy instead
    const pg = await api('GET', '/api/pages/' + pid); const div = document.createElement('div'); div.innerHTML = pg.page.content;
    const n = div.querySelector(`[data-lc="${key}"]`); if(n){ n.outerHTML = cardHtml(d); await api('PUT', '/api/pages/' + pid, {content: div.innerHTML}); } }
}
$('#btnLinkCard').onclick = async () => {
  rememberRange(); let u = await askText('Link to show as a card (YouTube or any web page)', 'https://'); if(!u || u === 'https://') return;
  if(!/^https?:\/\//i.test(u)) u = 'https://' + u; insertLinkCard(u);
};
ed.addEventListener('paste', e => {
  if(e.defaultPrevented || SET.autoCard === false) return;
  const t = ((e.clipboardData && e.clipboardData.getData('text/plain')) || '').trim(), s = getSelection();
  if(!/^https?:\/\/\S+$/i.test(t) || !s.rangeCount || !s.isCollapsed) return;
  e.preventDefault(); insertLinkCard(t);
});
ed.addEventListener('click', e => {
  const card = e.target.closest && e.target.closest('.link-card'); if(!card) return;
  if(e.target.closest('.lc-x')){ card.remove(); ensureTrailingLine(); scheduleSave(); return; }
  if(e.target.closest('.lc-thumb') && card.dataset.kind === 'youtube' && /^[\w-]{6,20}$/.test(card.dataset.vid || '')){
    e.preventDefault(); const old = card.querySelector('.lc-player');
    if(old) old.remove(); else { const d = document.createElement('div'); d.className = 'lc-player';
      d.innerHTML = `<iframe src="https://www.youtube-nocookie.com/embed/${card.dataset.vid}?autoplay=1&rel=0" allow="autoplay; encrypted-media; picture-in-picture; fullscreen" allowfullscreen></iframe>`; card.appendChild(d); }
    return;
  }
  const a = e.target.closest('a'); if(a){ e.preventDefault(); window.open(a.href, '_blank', 'noopener'); }
});

/* ---------- hex viewer ---------- */
let hexAtt = null, hexOffset = 0;
async function loadHexChunk(){
  const d = await api('GET', `/api/attachments/${hexAtt.id}/hex?offset=${hexOffset}`);
  $('#hexBody').textContent += (hexOffset ? '\n' : '') + d.text; hexOffset = d.offset + d.read;
  $('#hexInfo').textContent = `${hexOffset.toLocaleString()} / ${d.size.toLocaleString()} bytes shown`;
  $('#hexMore').style.display = d.eof ? 'none' : '';
}
async function openHex(a){
  hexAtt = a; hexOffset = 0; $('#hexBody').textContent = ''; $('#hexName').textContent = a.name; $('#hexInfo').textContent = 'Loading\u2026';
  bootstrap.Modal.getOrCreateInstance($('#hexModal')).show();
  try{ await loadHexChunk(); }catch(e){ $('#hexBody').textContent = 'Could not read this file.'; $('#hexMore').style.display = 'none'; }
}
$('#hexMore').onclick = () => loadHexChunk().catch(() => toast('Could not read more of this file'));

/* ---------- telegram backup ---------- */
(() => {
  const el = $('#bkModal'); const modal = () => bootstrap.Modal.getOrCreateInstance(el);
  const msg = (t, kind='secondary') => { const m = $('#bkMsg'); m.className = 'alert alert-' + kind + ' py-2 small mb-0'; m.textContent = t || '\u00a0'; };
  async function load(){
    const c = await api('GET', '/api/backup/config');
    $('#bkToken').value = ''; $('#bkToken').placeholder = c.has_token ? c.token_masked + '  (saved - leave empty to keep)' : '123456789:ABC...';
    $('#bkChat').value = c.chat_id; $('#bkInterval').value = String(c.interval_hours); $('#bkEnabled').checked = c.enabled;
    const sel = $('#bkInterval'); if(sel.value !== String(c.interval_hours)){ sel.value = '6'; }
    msg(c.last_status ? c.last_status : 'Not backed up yet', c.last_status.startsWith('Failed') ? 'danger' : 'secondary');
    return c;
  }
  async function save(){
    const body = {chat_id: $('#bkChat').value.trim(), interval_hours: Number($('#bkInterval').value), enabled: $('#bkEnabled').checked};
    const t = $('#bkToken').value.trim(); if(t) body.token = t;
    const c = await api('PUT', '/api/backup/config', body);
    $('#bkToken').value = ''; $('#bkToken').placeholder = c.has_token ? c.token_masked + '  (saved - leave empty to keep)' : '123456789:ABC...';
    return c;
  }
  async function act(btn, fn){
    btn.disabled = true; const old = btn.innerHTML; btn.innerHTML = '<span class="spinner-border spinner-border-sm"></span>';
    try{ await fn(); } catch(e){ msg(e.message, 'danger'); } finally { btn.disabled = false; btn.innerHTML = old; }
  }
  $('#openBackup').onclick = async () => { await load(); modal().show(); closeDrawer(); };
  $('#bkSave').onclick = e => act(e.currentTarget, async () => {
    const c = await save(); msg('Saved. ' + (c.enabled ? 'Automatic backup is ON every ' + c.interval_hours + ' h.' : 'Automatic backup is OFF.'), 'success');
  });
  $('#bkDetect').onclick = e => act(e.currentTarget, async () => {
    await save(); const r = await api('POST', '/api/backup/detect');
    if(r.ok) $('#bkChat').value = r.chat_id; msg(r.message, r.ok ? 'success' : 'warning');
  });
  $('#bkTest').onclick = e => act(e.currentTarget, async () => { await save(); const r = await api('POST', '/api/backup/test'); msg(r.message, r.ok ? 'success' : 'danger'); });
  $('#bkRun').onclick = e => act(e.currentTarget, async () => { await save(); msg('Sending backup\u2026'); const r = await api('POST', '/api/backup/run'); msg(r.message, r.ok ? 'success' : 'danger'); });
})();

/* ---------- cover / start ---------- */
(async function start(){
  await loadTree(); refreshSideInfo();
  if(tree.length) openSecs.add(tree[0].id);
  await openFirstOrEmpty();
  const cover = $('#cover'); let opened = false;
  const open = () => { if(opened) return; opened = true; cover.classList.add('open'); setTimeout(() => cover.remove(), 1800); };
  cover.addEventListener('click', open); setTimeout(open, 1700);
})();
</script>
</body>
</html>
"""


# --------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="Codex")
    ap.add_argument("--host", default="127.0.0.1", help="use 0.0.0.0 to open from phone on same Wi-Fi")
    ap.add_argument("--port", type=int, default=9000)
    ap.add_argument("--no-browser", action="store_true")
    args = ap.parse_args()

    init_db()
    threading.Thread(target=backup_loop, daemon=True).start()
    srv = ThreadingHTTPServer((args.host, args.port), Handler)
    url = f"http://{'127.0.0.1' if args.host == '0.0.0.0' else args.host}:{args.port}"
    print(f"Codex running at {url}   (Ctrl+C to stop)")
    print(f"Your data lives in: {DATA_DIR}")
    if not args.no_browser:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nBye!")
    finally:
        srv.server_close()


if __name__ == "__main__":
    sys.exit(main())
