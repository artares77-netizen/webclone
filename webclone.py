
"""webclone - mirror a website for offline use.

No limits on pages, depth or file size unless you set them yourself.
Standard library only (Python 3.8+). Use it on sites you own or have permission to copy.

    python webclone.py https://example.com
    python webclone.py https://example.com -o my_copy -w 16 --delay 0
"""
import argparse
import codecs
import gzip
import hashlib
import html
import http.client
import mimetypes
import os
import queue
import re
import shutil
import sys
import threading
import time
import urllib.error
import urllib.request
import urllib.robotparser
from http.cookiejar import CookieJar
from urllib.parse import quote, unquote, urldefrag, urljoin, urlparse, urlunparse

UA = "Mozilla/5.0 (compatible; webclone/1.0)"
SAFE = "%/:=&?~#+!$,;'@()*[]"
SKIP = ("#", "data:", "javascript:", "mailto:", "tel:", "sms:", "about:", "blob:", "file:", "ftp:")
URL_ATTRS = {"href", "src", "poster", "srcset", "data-src", "data-srcset",
             "data-original", "data-lazy-src", "background", "xlink:href"}
ASSET_RELS = {"stylesheet", "icon", "shortcut", "apple-touch-icon", "preload",
              "prefetch", "modulepreload", "manifest", "mask-icon"}
TAG_RE = re.compile(r"""<([a-zA-Z][\w:-]*)((?:"[^"]*"|'[^']*'|[^'">])*)>""")
ATTR_RE = re.compile(r"""([^\s"'<>/=]+)(\s*=\s*)(?:"([^"]*)"|'([^']*)'|([^\s"'=<>`]+))""")
CSS_URL_RE = re.compile(r"""url\(\s*(?:"([^"\n]*)"|'([^'\n]*)'|([^)\s'"]+))\s*\)""", re.I)
CSS_IMPORT_RE = re.compile(r"""@import\s+(?:"([^"\n]+)"|'([^'\n]+)')""", re.I)
BASE_RE = re.compile(r"""<base\s[^>]*?href\s*=\s*["']([^"']+)["'][^>]*>""", re.I)
CSP_RE = re.compile(r"""<meta\s[^>]*http-equiv\s*=\s*["']?content-security-policy["']?[^>]*>""", re.I)


class Cloner:
    def __init__(self, a):
        self.a = a
        u = a.url if "://" in a.url else "https://" + a.url
        p = urlparse(u)
        self.scheme, self.host = p.scheme.lower(), p.netloc.lower()
        self.root = self.host[4:] if self.host.startswith("www.") else self.host
        self.start = self.norm(u)
        self.out = os.path.abspath(a.output or "clone_" + self.host.replace(":", "_"))
        self.lock, self.robots_lock = threading.Lock(), threading.Lock()
        self.q = queue.Queue()
        self.seen, self.url_map, self.owner, self.texts = set(), {}, {}, {}
        self.next_ok, self.robots = {}, {}
        self.pages = self.files = self.errors = self.bytes = 0
        self.stop = False
        self.opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(CookieJar()))

    # ---------- URL helpers ----------
    def in_scope(self, netloc):
        h = netloc.lower()
        h = h[4:] if h.startswith("www.") else h
        return h == self.root or (self.a.subdomains and h.endswith("." + self.root))

    def norm(self, url):
        p = urlparse(urldefrag(url)[0])
        host, scheme = p.netloc.lower(), p.scheme.lower()
        if self.in_scope(host):
            scheme = self.scheme
            if host in (self.root, "www." + self.root):
                host = self.host
        return urlunparse((scheme, host, p.path or "/", p.params, p.query, ""))

    @staticmethod
    def resolve(ref, base, unesc=False):
        if unesc:
            ref = html.unescape(ref)
        ref = ref.strip()
        if not ref or ref.lower().startswith(SKIP):
            return None
        return urljoin(base, ref)

    def localize(self, ref, base, rel, unesc=False):
        u = self.resolve(ref, base, unesc)
        if u is None:
            return None
        target = self.url_map.get(self.norm(u))
        if target is None:
            return u  # not downloaded: keep pointing at the live site
        frag = urldefrag(u)[1]
        r = os.path.relpath(target, os.path.dirname(rel) or ".").replace(os.sep, "/")
        return quote(r, safe="/") + ("#" + frag if frag else "")

    @staticmethod
    def path_for(url, ctype):
        p = urlparse(url)
        parts = [c for c in unquote(p.path).split("/") if c not in ("", ".", "..")]
        if p.path.endswith("/") or not parts:
            parts.append("index")
        stem, ext = os.path.splitext(parts[-1])
        if "html" in ctype:
            if ext.lower() not in (".html", ".htm"):
                stem, ext = parts[-1], ".html"
        elif not ext:
            ext = mimetypes.guess_extension(ctype) or ".bin"
        if p.query:
            stem += "_" + hashlib.sha1(p.query.encode()).hexdigest()[:8]
        parts[-1] = stem + ext
        safe = []
        for c in [p.netloc.replace(":", "_")] + parts:
            c = re.sub(r'[<>:"|?*\\\x00-\x1f]', "_", c).strip(" .") or "_"
            if len(c) > 120:
                c = c[:80] + "_" + hashlib.sha1(c.encode()).hexdigest()[:8] + os.path.splitext(c)[1][:10]
            safe.append(c)
        return "/".join(safe)

    def assign(self, url, ctype):
        with self.lock:
            if url in self.url_map:
                return self.url_map[url]
            rel = self.path_for(url, ctype)
            if self.owner.get(rel.lower(), url) != url:
                stem, ext = os.path.splitext(rel)
                rel = f"{stem}_{hashlib.sha1(url.encode()).hexdigest()[:8]}{ext}"
            self.owner[rel.lower()] = url
            self.url_map[url] = rel
            return rel

    # ---------- reference scanning (used for both discovery and rewriting) ----------
    def scan_html(self, text, fn, rewrite):
        def tag(m):
            name, attrs = m.group(1).lower(), m.group(2)
            vals = {a.group(1).lower(): (a.group(3) or a.group(4) or a.group(5) or "")
                    for a in ATTR_RE.finditer(attrs)}
            rels = set(vals.get("rel", "").lower().split())
            page = name in ("a", "area", "iframe", "frame") or (name == "link" and not rels & ASSET_RELS)
            refresh = name == "meta" and "refresh" in vals.get("http-equiv", "").lower()

            def attr(a):
                key = a.group(1).lower()
                if rewrite and key == "integrity":
                    return ""
                raw = a.group(3) if a.group(3) is not None else a.group(4) if a.group(4) is not None else a.group(5)
                if refresh and key == "content":
                    mm = re.match(r"(\s*\d+\s*;\s*url\s*=\s*)(.*)", raw or "", re.I | re.S)
                    new = fn(mm.group(2).strip("'\" "), True) if mm else None
                    new = None if new is None else mm.group(1) + new
                elif key in URL_ATTRS:
                    if "srcset" in key:
                        out = []
                        for part in re.split(r",\s+", raw.strip()):
                            bits = part.split(None, 1)
                            if bits:
                                u = fn(bits[0], False)
                                out.append(" ".join([u if u is not None else html.unescape(bits[0])]
                                                    + [html.unescape(b) for b in bits[1:]]))
                        new = ", ".join(out)
                    else:
                        new = fn(raw, page and key in ("href", "src"))
                else:
                    return a.group(0)
                if new is None:
                    return a.group(0)
                q = "'" if a.group(4) is not None else '"'
                return f"{a.group(1)}{a.group(2)}{q}{html.escape(new, quote=True)}{q}"

            new_attrs = ATTR_RE.sub(attr, attrs)
            return m.group(0) if new_attrs == attrs else f"<{m.group(1)}{new_attrs}>"

        return TAG_RE.sub(tag, text)

    @staticmethod
    def scan_css(text, fn):
        def url(m):
            val = next(g for g in m.groups() if g is not None)
            q = '"' if m.group(1) is not None else "'" if m.group(2) is not None else ""
            new = fn(val)
            return m.group(0) if new is None else f"url({q}{new}{q})"

        def imp(m):
            val = m.group(1) if m.group(1) is not None else m.group(2)
            q = '"' if m.group(1) is not None else "'"
            new = fn(val)
            return m.group(0) if new is None else f"@import {q}{new}{q}"

        return CSS_IMPORT_RE.sub(imp, CSS_URL_RE.sub(url, text))

    # ---------- crawling ----------
    def enqueue(self, url, kind, depth):
        url = self.norm(url)
        p = urlparse(url)
        if self.stop or p.scheme not in ("http", "https") or not p.netloc:
            return
        if not self.in_scope(p.netloc) and (kind == "page" or self.a.no_external_assets):
            return
        with self.lock:
            if url in self.seen:
                return
            if kind == "page":
                if (self.a.max_depth and depth > self.a.max_depth) or \
                        (self.a.max_pages and self.pages >= self.a.max_pages):
                    return
                self.pages += 1
            self.seen.add(url)
        self.q.put((url, kind, depth))

    def discover(self, text, url, typ, depth):
        base = url
        if typ == "html":
            m = BASE_RE.search(text)
            if m:
                base = urljoin(url, html.unescape(m.group(1)))

            def on_html(ref, is_page):
                u = self.resolve(ref, base, True)
                if u:
                    self.enqueue(u, "page" if is_page else "asset", depth + 1)

            self.scan_html(text, on_html, False)

        def on_css(ref):
            u = self.resolve(ref, base)
            if u:
                self.enqueue(u, "asset", depth)

        self.scan_css(text, on_css)

    def robots_for(self, url):
        p = urlparse(url)
        with self.robots_lock:
            rp = self.robots.get(p.netloc)
            if rp is None:
                rp = urllib.robotparser.RobotFileParser()
                try:
                    req = urllib.request.Request(f"{p.scheme}://{p.netloc}/robots.txt", headers={"User-Agent": UA})
                    with self.opener.open(req, timeout=self.a.timeout) as r:
                        rp.parse(r.read().decode("utf-8", "replace").splitlines())
                    rp.modified()
                except Exception:
                    rp.allow_all = True
                self.robots[p.netloc] = rp
            return rp

    def throttle(self, host, delay):
        with self.lock:
            now = time.monotonic()
            t = max(now, self.next_ok.get(host, 0.0))
            self.next_ok[host] = t + delay
        if t > now:
            time.sleep(t - now)

    def download(self, url):
        req = urllib.request.Request(quote(url, safe=SAFE), headers={
            "User-Agent": UA, "Accept": "*/*", "Accept-Encoding": "gzip"})
        with self.opener.open(req, timeout=self.a.timeout) as r:
            final, ctype = self.norm(r.geturl()), r.headers.get_content_type()
            if "html" in ctype:
                typ = "html"
            elif ctype == "text/css" or urlparse(final).path.endswith(".css"):
                typ = "css"
            else:
                typ = "other"
            rel = self.assign(final, ctype)
            with self.lock:
                self.url_map[url] = rel
            full = os.path.join(self.out, *rel.split("/"))
            os.makedirs(os.path.dirname(full), exist_ok=True)
            gz = "gzip" in (r.headers.get("Content-Encoding") or "").lower()
            src = gzip.GzipFile(fileobj=r) if gz else r
            if typ == "other":  # stream to disk, so file size is never a problem
                part = full + ".part"
                try:
                    with open(part, "wb") as f:
                        shutil.copyfileobj(src, f, 1 << 16)
                    os.replace(part, full)
                finally:
                    if os.path.exists(part):
                        os.remove(part)
                return final, typ, rel, None, os.path.getsize(full), None
            data = src.read()
            with open(full, "wb") as f:
                f.write(data)
            return final, typ, rel, data, len(data), r.headers.get_content_charset()

    def fail(self, url, why):
        with self.lock:
            self.errors += 1
        print(f"  ! {why}: {url}", file=sys.stderr)

    def fetch(self, url, kind, depth):
        host = urlparse(url).netloc
        delay = self.a.delay
        if self.in_scope(host) and not self.a.ignore_robots:
            rp = self.robots_for(url)
            if not rp.can_fetch("webclone", url):
                print(f"  - robots.txt blocks: {url}")
                return
            delay = max(delay, rp.crawl_delay("webclone") or 0)
        for attempt in range(3):
            self.throttle(host, delay)
            try:
                final, typ, rel, data, size, cs = self.download(url)
                break
            except urllib.error.HTTPError as e:
                if e.code in (429, 500, 502, 503, 504) and attempt < 2:
                    time.sleep(2 * (attempt + 1))
                    continue
                return self.fail(url, f"HTTP {e.code}")
            except (urllib.error.URLError, OSError, EOFError, http.client.HTTPException) as e:
                if attempt == 2:
                    return self.fail(url, str(e))
                time.sleep(attempt + 1)
        with self.lock:
            self.files += 1
            self.bytes += size
            n = self.files
        print(f"  [{n}] {url}")
        if data is None:
            return
        if not cs and typ == "html":
            m = re.search(rb"""charset\s*=\s*["']?([\w-]+)""", data[:4096], re.I)
            cs = m.group(1).decode("ascii") if m else None
        try:
            enc = codecs.lookup(cs or "utf-8").name
        except LookupError:
            enc = "utf-8"
        with self.lock:
            self.texts[rel] = (final, typ, enc)
        if typ == "html" and not self.in_scope(urlparse(final).netloc):
            return  # never crawl pages of other sites
        self.discover(data.decode(enc, "surrogateescape"), final, typ, depth)

    def worker(self):
        while True:
            item = self.q.get()
            try:
                if item is None:
                    return
                if not self.stop:
                    self.fetch(*item)
            except Exception as e:
                self.fail(item[0], repr(e))
            finally:
                self.q.task_done()

    # ---------- offline rewrite ----------
    def rewrite(self):
        for rel, (url, typ, enc) in list(self.texts.items()):
            full = os.path.join(self.out, *rel.split("/"))
            try:
                with open(full, "rb") as f:
                    text = f.read().decode(enc, "surrogateescape")
                base = url
                if typ == "html":
                    m = BASE_RE.search(text)
                    if m:
                        base = urljoin(url, html.unescape(m.group(1)))
                        text = BASE_RE.sub("", text)
                    text = CSP_RE.sub("", text)
                    text = self.scan_html(text, lambda ref, pg: self.localize(ref, base, rel, True), True)
                text = self.scan_css(text, lambda ref: self.localize(ref, base, rel))
                with open(full, "wb") as f:
                    f.write(text.encode(enc, "surrogateescape"))
            except Exception as e:
                self.fail(rel, f"rewrite failed ({e})")

    def run(self):
        os.makedirs(self.out, exist_ok=True)
        t0 = time.time()
        print(f"Cloning {self.start}\n  -> {self.out}")
        self.enqueue(self.start, "page", 0)
        threads = [threading.Thread(target=self.worker, daemon=True) for _ in range(max(1, self.a.workers))]
        for t in threads:
            t.start()
        try:
            self.q.join()
        except KeyboardInterrupt:
            print("\nStopping - keeping what was downloaded so far...")
            self.stop = True
            try:
                while True:
                    self.q.get_nowait()
                    self.q.task_done()
            except queue.Empty:
                pass
        for _ in threads:
            self.q.put(None)
        try:
            for t in threads:
                t.join()
        except KeyboardInterrupt:
            self.stop = True
            print("Not waiting for downloads still in flight...")
        for d, _, fs in os.walk(self.out):
            for f in fs:
                if f.endswith(".part"):
                    try:
                        os.remove(os.path.join(d, f))
                    except OSError:
                        pass
        print("Rewriting links for offline use...")
        self.rewrite()
        rel = self.url_map.get(self.start)
        if rel:
            with open(os.path.join(self.out, "index.html"), "w") as f:
                f.write('<meta http-equiv="refresh" content="0; url=%s">' % quote(rel))
        print(f"\nDone: {self.files} files ({self.bytes / 1e6:.1f} MB), "
              f"{self.errors} errors, {time.time() - t0:.0f}s")
        if not self.files:
            print("Nothing downloaded. If robots.txt blocks you on your own site, use --ignore-robots.")
        else:
            print(f"Preview: cd \"{self.out}\" && python3 -m http.server 8000   (then open http://localhost:8000)")


def main():
    ap = argparse.ArgumentParser(description="Mirror a website for offline use. No limits unless you set them.")
    ap.add_argument("url")
    ap.add_argument("-o", "--output", help="output folder (default: clone_<host>)")
    ap.add_argument("-w", "--workers", type=int, default=8, help="parallel downloads (default 8)")
    ap.add_argument("--delay", type=float, default=0.2,
                    help="min seconds between requests to one host (default 0.2, 0 = full speed)")
    ap.add_argument("--timeout", type=int, default=30, help="seconds to wait per request")
    ap.add_argument("--max-pages", type=int, default=0, help="stop queuing pages after N (0 = unlimited)")
    ap.add_argument("--max-depth", type=int, default=0, help="link depth from the start page (0 = unlimited)")
    ap.add_argument("--subdomains", action="store_true", help="also crawl pages on subdomains")
    ap.add_argument("--no-external-assets", action="store_true",
                    help="skip CSS/JS/images hosted on other domains")
    ap.add_argument("--ignore-robots", action="store_true", help="skip robots.txt (only for sites you own)")
    c = Cloner(ap.parse_args())
    if not c.host:
        sys.exit("Invalid URL")
    c.run()


if __name__ == "__main__":
    main()
