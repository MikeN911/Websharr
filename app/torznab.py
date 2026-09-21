"""Newznab/Torznab indexer endpoint backed by Webshare search.

Mounted at /torznab/api. Supports t=caps, t=search, t=tvsearch, t=movie.
Only q-based queries are advertised (Webshare search is filename-based, so
imdbid/tvdbid lookups are not possible).

Add this to Sonarr/Radarr as a **Newznab** indexer, not Torznab: the paired
download client is SABnzbd (usenet protocol), and Sonarr only routes a grab
to a usenet client when the release came from a usenet (Newznab) indexer.
The feed emits attributes in both the newznab and torznab namespaces so it
parses correctly either way.
"""

import asyncio
import email.utils
import hashlib
import logging
import re
import unicodedata
import urllib.parse
import xml.etree.ElementTree as ET

import httpx
from fastapi import APIRouter, Request, Response

from .config import config
from .nzb import build_nzb
from .settings import settings
from .tmdb import lookup as tmdb_lookup
from .tmdb import lookup_by_id as tmdb_lookup_by_id
from .webshare import SearchResult, WebshareError

logger = logging.getLogger("websharr.torznab")

router = APIRouter()

TORZNAB_NS = "http://torznab.com/schemas/2015/feed"
NEWZNAB_NS = "http://www.newznab.com/DTD/2010/feeds/attributes/"

CAT_MOVIES = "2000"
CAT_AUDIO = "3000"
CAT_PC = "4000"
CAT_TV = "5000"
CAT_BOOKS = "7000"

VIDEO_EXTENSIONS = (
    ".mkv", ".mp4", ".avi", ".m4v", ".mov", ".wmv", ".ts", ".m2ts", ".webm", ".mpg", ".mpeg",
)
AUDIO_EXTENSIONS = (
    ".mp3", ".flac", ".m4a", ".aac", ".ogg", ".opus", ".wma", ".wav", ".alac",
)
BOOK_EXTENSIONS = (
    ".epub", ".pdf", ".mobi", ".azw", ".azw3", ".cbr", ".cbz", ".djvu",
)
ARCHIVE_EXTENSIONS = (
    ".iso", ".zip", ".rar", ".7z", ".tar", ".gz", ".exe", ".bin",
)
COMPRESSED_EXTENSIONS = (
    ".zip", ".rar", ".7z", ".tar", ".gz", ".tgz", ".bz2", ".tbz2", ".xz",
)
ALL_EXTENSIONS = VIDEO_EXTENSIONS + AUDIO_EXTENSIONS + BOOK_EXTENSIONS + ARCHIVE_EXTENSIONS


def _is_video(name: str) -> bool:
    return name.lower().endswith(VIDEO_EXTENSIONS)


def _is_allowed_file(name: str, category: str = "video") -> bool:
    name_lower = name.lower()
    if category == "video":
        return name_lower.endswith(VIDEO_EXTENSIONS + COMPRESSED_EXTENSIONS)
    if category == "audio":
        return name_lower.endswith(AUDIO_EXTENSIONS + COMPRESSED_EXTENSIONS)
    if category in ("docs", "books"):
        return name_lower.endswith(BOOK_EXTENSIONS + COMPRESSED_EXTENSIONS)
    if category in ("archives", "games"):
        return name_lower.endswith(ARCHIVE_EXTENSIONS)
    return name_lower.endswith(ALL_EXTENSIONS)

# TMDB original_language (ISO 639-1) -> the language name Sonarr/Radarr expect in
# a newznab `language` attribute. Only the codes we can map are tagged; anything
# unknown is left untagged so *arr falls back to parsing the release name.
_LANG_NAMES = {
    "en": "English", "cs": "Czech", "sk": "Slovak", "de": "German", "fr": "French",
    "es": "Spanish", "it": "Italian", "pl": "Polish", "hu": "Hungarian", "nl": "Dutch",
    "pt": "Portuguese", "ru": "Russian", "uk": "Ukrainian", "ja": "Japanese",
    "ko": "Korean", "zh": "Chinese", "cn": "Chinese", "sv": "Swedish", "da": "Danish",
    "no": "Norwegian", "nb": "Norwegian", "fi": "Finnish", "tr": "Turkish", "ro": "Romanian",
    "el": "Greek", "ar": "Arabic", "he": "Hebrew", "hi": "Hindi", "th": "Thai",
    "bg": "Bulgarian", "hr": "Croatian", "sr": "Serbian", "sl": "Slovenian", "ca": "Catalan",
    "fa": "Persian", "vi": "Vietnamese", "id": "Indonesian", "lt": "Lithuanian",
    "lv": "Latvian", "et": "Estonian", "is": "Icelandic",
}


def lang_name(code: str) -> str:
    """*arr language name for a TMDB language code (""->"", unknown code -> "")."""
    return _LANG_NAMES.get((code or "").strip().lower(), "")


# Filename markers of Czech/Slovak audio, as opposed to the original audio with
# subtitles ("titulky"). On Webshare a standalone CZ/SK marker is the normal
# way uploaders identify the audio language, even when "dabing" is omitted.
_DUB_RE = re.compile(r"\bdab(?:ing|ovan\w*|\b)", re.IGNORECASE)
_SK_RE = re.compile(r"\b(?:sk|slovensk\w*|slovak)\b", re.IGNORECASE)
_CZ_RE = re.compile(r"\b(?:cz|cesk\w*|česk\w*|czech)\b", re.IGNORECASE)
_SUBS_RE = re.compile(r"\b(?:titulky|tit|subs?|subtitles)\b", re.IGNORECASE)


def dub_language(name: str) -> str:
    """"Czech"/"Slovak" when the file name signals CZ/SK audio, else ""."""
    name = name or ""
    has_dub = bool(_DUB_RE.search(name))
    has_czech = bool(_CZ_RE.search(name))
    has_slovak = bool(_SK_RE.search(name))
    if not (has_dub or has_czech or has_slovak):
        return ""
    # A language marker followed by an explicit subtitle marker describes the
    # subtitles, not the audio. Explicit "dabing" still wins when both appear.
    if _SUBS_RE.search(name) and not has_dub:
        return ""
    # A dub marked SK (and not CZ) is Slovak; otherwise assume Czech (the default
    # on Webshare, where a bare "Dabing" is Czech).
    if has_slovak and not has_czech:
        return "Slovak"
    return "Czech"


# Audio-track language codes (Webshare file_info) that mean a CZ/SK release.
_AUDIO_CZECH = {"CZE", "CES", "CS", "CZ"}
_AUDIO_SLOVAK = {"SLO", "SLK", "SK"}


def audio_language(codes) -> str:
    """"Czech"/"Slovak" when the file carries such an audio track, else "".

    Only a positive signal: track tags are often missing or wrong, so their
    absence never overrides a marker in the file name.
    """
    codes = {(c or "").strip().upper() for c in codes or ()}
    if codes & _AUDIO_CZECH:
        return "Czech"
    if codes & _AUDIO_SLOVAK:
        return "Slovak"
    return ""


def _xml_response(element: ET.Element, status_code: int = 200) -> Response:
    body = ET.tostring(element, encoding="utf-8", xml_declaration=True)
    return Response(content=body, media_type="application/xml", status_code=status_code)


def _error(code: int, description: str) -> Response:
    el = ET.Element("error", {"code": str(code), "description": description})
    return _xml_response(el)


def _caps() -> Response:
    caps = ET.Element("caps")
    ET.SubElement(caps, "server", {"title": "Websharr", "version": "1.0"})
    ET.SubElement(caps, "limits", {"max": "100", "default": str(config.search_limit)})
    # Advertise id params so Sonarr/Radarr (via Prowlarr) send tvdbid/imdbid/
    # tmdbid — Websharr resolves them to the exact Czech title via TMDB instead
    # of relying on a fuzzy text match.
    searching = ET.SubElement(caps, "searching")
    ET.SubElement(searching, "search", {"available": "yes", "supportedParams": "q"})
    ET.SubElement(searching, "tv-search",
                  {"available": "yes", "supportedParams": "q,season,ep,tvdbid,imdbid"})
    ET.SubElement(searching, "movie-search",
                  {"available": "yes", "supportedParams": "q,imdbid,tmdbid"})
    ET.SubElement(searching, "music-search",
                  {"available": "yes", "supportedParams": "q"})
    ET.SubElement(searching, "book-search",
                  {"available": "yes", "supportedParams": "q"})
    cats = ET.SubElement(caps, "categories")
    movies = ET.SubElement(cats, "category", {"id": CAT_MOVIES, "name": "Movies"})
    ET.SubElement(movies, "subcat", {"id": "2040", "name": "Movies/HD"})
    tv = ET.SubElement(cats, "category", {"id": CAT_TV, "name": "TV"})
    ET.SubElement(tv, "subcat", {"id": "5040", "name": "TV/HD"})
    audio = ET.SubElement(cats, "category", {"id": CAT_AUDIO, "name": "Audio"})
    ET.SubElement(audio, "subcat", {"id": "3010", "name": "Audio/MP3"})
    ET.SubElement(audio, "subcat", {"id": "3040", "name": "Audio/Lossless"})
    ET.SubElement(audio, "subcat", {"id": "3030", "name": "Audio/Audiobook"})
    books = ET.SubElement(cats, "category", {"id": CAT_BOOKS, "name": "Books"})
    ET.SubElement(books, "subcat", {"id": "7020", "name": "Books/EBook"})
    pc = ET.SubElement(cats, "category", {"id": CAT_PC, "name": "PC"})
    ET.SubElement(pc, "subcat", {"id": "4050", "name": "PC/Games"})
    return _xml_response(caps)


_EP_IN_QUERY = re.compile(
    r"^(?P<series>.*?)\s*(?:s(?P<s>\d{1,2})e(?P<e>\d{1,3})|(?P<s2>\d{1,2})x(?P<e2>\d{1,3}))\b",
    re.I,
)


def parse_query(t: str, q: str, season: str | None, ep: str | None):
    """Pull an SxxEyy / 1x05 out of the query text when season/ep weren't
    passed separately — e.g. a user typing "skvrna s01e05" into the box.
    Returns (type, series, season, ep)."""
    q = (q or "").strip()
    if season is None and ep is None:
        m = _EP_IN_QUERY.match(q)
        if m:
            series = (m.group("series") or "").strip()
            if series:
                return "tvsearch", series, (m.group("s") or m.group("s2")), (m.group("e") or m.group("e2"))
    return t, q, season, ep


def build_queries(t: str, q: str, season: str | None, ep: str | None) -> list[str]:
    """Build Webshare search query variants for a Torznab request."""
    q = (q or "").strip()
    if not q:
        return []
    if t == "tvsearch" and season is not None:
        try:
            s = int(season)
        except ValueError:
            return [q]
        if ep is not None:
            try:
                e = int(ep)
            except ValueError:
                return [f"{q} S{s:02d}", f"{q}S{s:02d}"]
            # Several naming conventions live on Webshare: S01E02, 1x02, compact
            # variants like ZRDs03e01, and — common for CZ uploads — a bare
            # episode number ("Series 01 - Title").
            variants = [
                f"{q} S{s:02d}E{e:02d}",
                f"{q} {s}x{e:02d}",
                f"{q}S{s:02d}E{e:02d}",
                f"{q}{s}x{e:02d}",
            ]
            if s == 1:
                # Only for season 1, where a bare "01" is unambiguous enough;
                # for later seasons it would collide with other episodes.
                variants.append(f"{q} {e:02d}")
            return variants
        return [
            f"{q} S{s:02d}",
            f"{q}S{s:02d}",
            f"{q} {s} serie",
            f"{q} {s}. serie",
            f"{q} serie {s}",
            f"{q} {s} sezona",
        ]
    return [q]


def _asciify(text: str) -> str:
    """Transliterate diacritics and drop remaining non-ASCII: "Bez vědomí" ->
    "Bez vedomi". Prowlarr puts the release title in an HTTP header when a
    download is proxied and rejects non-latin-1 chars ("Invalid non-ASCII ...
    in header"); *arr matches diacritic-insensitively, so this is safe."""
    text = unicodedata.normalize("NFKD", text)
    text = "".join(c for c in text if not unicodedata.combining(c) and ord(c) < 128)
    return re.sub(r"\s{2,}", " ", text).strip()


def release_title(query: str, season: str | None, ep: str | None, name: str) -> str:
    """Sonarr/Radarr-parseable release name.

    Webshare filenames often lack SxxEyy (esp. CZ uploads like "Skvrna 01 -
    Pohřeb"), which breaks *arr's import parser. For a tvsearch we prepend the
    requested "<series> SxxEyy" so the folder/release name parses, then keep the
    original stem for quality tokens and human recognition.
    """
    stem = name.rsplit(".", 1)[0] if "." in name else name
    if season is None:
        return _asciify(stem)
    try:
        s = int(season)
    except (TypeError, ValueError):
        return _asciify(stem)
    q = (query or "").strip()
    if ep is not None:
        try:
            prefix = f"{q} S{s:02d}E{int(ep):02d}"
        except (TypeError, ValueError):
            prefix = f"{q} S{s:02d}"
    else:
        prefix = f"{q} S{s:02d}"
    # Strip any SxxEyy/1x02 already in the filename so the release doesn't carry
    # two episode markers (confuses *arr's parser: "unable to determine episode").
    stem = re.sub(r"\b(s\d{1,2}e\d{1,3}|\d{1,2}x\d{1,3})\b", "", stem, flags=re.I)
    stem = re.sub(r"\.{2,}", ".", stem)          # double dots left by the removal
    stem = re.sub(r"\s{2,}", " ", stem).strip(" .-")
    return _asciify(f"{prefix} - {stem}".strip(" -"))


def _is_video(name: str) -> bool:
    return name.lower().endswith(VIDEO_EXTENSIONS)


_RES_RE = re.compile(r"\b(480|540|576|720|1080|2160|4320)p?\b", re.I)


def resolution_class(width: int, height: int) -> int:
    """The standard resolution (360…2160) a video of this size belongs to.

    *arr only parses the labels it knows; a literal "384p" (old DVD-rip AVI) or
    "800p" (2.39:1 crop of a 1080p source) reads as Unknown quality and the
    release is rejected. Width decides for cropped widescreen, height for 4:3,
    whichever puts it higher.
    """
    by_width = 2160 if width >= 3200 else 1080 if width >= 1800 else 720 if width >= 1200 else 0
    by_height = (2160 if height >= 1700 else 1080 if height >= 900 else 720 if height >= 650
                 else 576 if height >= 560 else 540 if height >= 500
                 else 480 if height >= 380 else 360 if height > 0 else 0)
    return max(by_width, by_height)


async def _probe(client, results: list[SearchResult]) -> tuple[dict[str, int], dict[str, str]]:
    """Fetch file_info for results whose *name* leaves something open, and
    return (heights, audio): the video height for names without a resolution
    token — many CZ files ship without one and Sonarr/Radarr reject them as
    'Unknown' quality otherwise — and "Czech"/"Slovak" for names without a
    language marker whose audio track says so (a TV-rip dub named just
    "... 1080p WEB-DL prima+")."""
    need = [r for r in results if not _RES_RE.search(r.name) or not dub_language(r.name)]
    if not need:
        return {}, {}
    sem = asyncio.Semaphore(6)

    async def one(r: SearchResult):
        async with sem:
            try:
                return r, await client.file_info(r.ident)
            except (WebshareError, httpx.HTTPError):
                return r, {}

    heights: dict[str, int] = {}
    audio: dict[str, str] = {}
    for r, info in await asyncio.gather(*(one(r) for r in need)):
        height = resolution_class(int(info.get("width") or 0), int(info.get("height") or 0))
        if height and not _RES_RE.search(r.name):
            heights[r.ident] = height
        lang = audio_language(info.get("audio_languages"))
        if lang and not dub_language(r.name):
            audio[r.ident] = lang
    return heights, audio


_EP_TOKEN = re.compile(r"^(s\d{1,2}e\d{1,3}|s\d{1,2}|\d{1,2}x\d{1,3}|\d{1,4})$")


def normalize_text(text: str) -> str:
    """Lowercase, strip diacritics, split punctuation to spaces."""
    text = unicodedata.normalize("NFKD", (text or "").lower())
    text = "".join(c for c in text if not unicodedata.combining(c))
    return "".join(c if c.isalnum() else " " for c in text)


def _series_tokens(query: str) -> list[str]:
    """Query tokens that name the show/movie — numbers and SxxEyy/1x05
    episode markers dropped, so only the title words remain."""
    return [t for t in normalize_text(query).split() if not _EP_TOKEN.match(t)]


def _as_titles(query) -> list[str]:
    return [query] if isinstance(query, str) else list(query)


_ARTICLES = ("the", "a", "an")


def _title_key(text: str) -> str:
    """Normalized title with a leading article dropped — Sonarr searches
    'The Sleepers' as 'Sleepers', so aliases must match either form."""
    toks = normalize_text(text).split()
    if toks and toks[0] in _ARTICLES:
        toks = toks[1:]
    return " ".join(toks)


def alias_titles(query: str, aliases: list[dict]) -> list[str]:
    """Extra Webshare/CZ titles for a query, from the user's alias map — an
    alias applies when its `from` (a *arr title) appears in the query, ignoring
    a leading article on either side."""
    qk = _title_key(query)
    out = []
    for a in aliases or []:
        fk, to = _title_key(a.get("from", "")), (a.get("to") or "").strip()
        if fk and to and fk in qk:
            out.append(to)
    return out


def _tmdb_kind(t: str, cat: str | None) -> str:
    if t == "movie":
        return "movie"
    if t == "tvsearch":
        return "tv"
    return "movie" if (cat or "").strip().startswith("2") else "tv"  # 2xxx = movies


async def expand_titles(t: str, q: str, cat: str | None, *, tvdbid: str | None = None,
                        imdbid: str | None = None, tmdbid: str | None = None
                        ) -> tuple[list[str], str, str, list[str], int]:
    """Return (search_titles, display_title, original_language, czech_titles, year).

    search_titles: the query, manual-alias titles, the TMDB original title, and
    the TMDB CZ alternative titles (the Czech dub name of an English-origin
    show, e.g. "Kačeří příběhy" for DuckTales) — all searched, and any matching
    file is accepted.
    display_title: the canonical name used as the release-name prefix, so Sonarr
    shows "The Sleepers" instead of whatever alias/query happened to match.
    original_language: the title's language name (from TMDB) used to tag the
    release feed, or "" when unknown; lets *arr apply an original-language policy.
    czech_titles: the subset of search_titles that are Czech dub names — a file
    named after one is a Czech release even without a "dabing" marker, so the
    feed tags it Czech instead of the original language.
    year: the title's first-air/release year from TMDB (0 unknown), used to drop
    files of a same-named other title (see year_conflict).
    """
    # Aliases stay keyed on the *arr text query (interactive search); an ID-only
    # automatic search has no q, so we lean on the TMDB id lookup below instead.
    titles = ([q] if q and q.strip() else []) + alias_titles(q, settings.aliases)
    display = q
    language = ""
    czech_titles: list[str] = []
    year = 0
    if settings.tmdb_token:
        kind = _tmdb_kind(t, cat)
        res = None
        if tmdbid or imdbid or tvdbid:
            res = await tmdb_lookup_by_id(settings.tmdb_token, kind, tmdbid, imdbid, tvdbid)
        if not res:
            res = await tmdb_lookup(settings.tmdb_token, kind, q)
        if res:
            disp, orig, lang, czech, year = res
            seen = {normalize_text(x) for x in titles}
            if disp:
                display = disp  # prefix releases with the canonical title
                # Also search under it — for a CZ-origin show the canonical name
                # *is* the Czech one, and an ID-only search has no other term.
                if normalize_text(disp) not in seen:
                    titles.append(disp)
                    seen.add(normalize_text(disp))
            for extra in (orig, *czech):
                if extra and normalize_text(extra) not in seen:
                    titles.append(extra)
                    seen.add(normalize_text(extra))
            czech_titles = list(czech)
            language = lang_name(lang)
    return titles, display, language, czech_titles, year


def year_conflict(name: str, year: int) -> bool:
    """True when every year token in the file name contradicts the title's year.

    Two different titles can share a Czech name — the 1987 and 2017 DuckTales
    are both "Kačeří příběhy" on Webshare — and such files often disambiguate
    only by a year in the name ("Kaceri pribehy 2017 ..."). ±1 tolerated
    (releases are often stamped a year off); resolution tokens (1080, 2160)
    fall outside the 1900-2099 window.
    """
    if not year:
        return False
    years = [int(t) for t in normalize_text(name).split()
             if t.isdigit() and len(t) == 4 and 1900 <= int(t) <= 2099]
    return bool(years) and all(abs(y - year) > 1 for y in years)


def _match_series_prefix(title_tokens: list[str], name_tokens: list[str]) -> tuple[bool, list[str]]:
    """Check if name_tokens starts with title_tokens.

    Supports both separated tokens ('zrd', 's03e01') and compact tokens
    where the last title token is glued to an episode/season marker (e.g. 'zrds03e01').
    Returns (matches, tail_tokens).
    """
    if not title_tokens:
        return True, name_tokens
    if not name_tokens:
        return False, []

    # 1. Exact tokens prefix match
    if len(name_tokens) >= len(title_tokens) and name_tokens[:len(title_tokens)] == title_tokens:
        return True, name_tokens[len(title_tokens):]

    # 2. Compact match on the last token (e.g. title="zrd", name="zrds03e01" -> first token="zrds03e01")
    if len(title_tokens) > 1:
        if name_tokens[:len(title_tokens) - 1] != title_tokens[:-1]:
            return False, []
        lead_idx = len(title_tokens) - 1
    else:
        lead_idx = 0

    if lead_idx < len(name_tokens):
        cand = name_tokens[lead_idx]
        target = title_tokens[-1]
        if cand.startswith(target):
            rest = cand[len(target):]
            # rest should look like an episode/season marker: s03e01, s03, 3x01, 01, etc.
            if re.match(r"^(s\d{1,2}(?:e\d{1,3})?|\d{1,2}x\d{1,3}|\d{1,2})$", rest, re.I):
                tail = [rest] + name_tokens[lead_idx + 1:]
                return True, tail

    return False, []


def to_torznab_cat(cat: str) -> str:
    """Map human or UI category names to Newznab/Torznab category IDs."""
    c = (cat or "").strip().lower()
    if c in ("tv", "shows", "show", "series", CAT_TV):
        return CAT_TV
    if c in ("movie", "movies", CAT_MOVIES):
        return CAT_MOVIES
    if c in ("music", "audio", CAT_AUDIO):
        return CAT_AUDIO
    if c in ("book", "books", "docs", CAT_BOOKS):
        return CAT_BOOKS
    if c in ("game", "games", "pc", "archives", CAT_PC):
        return CAT_PC
    return ""


def to_ui_cat(cat: str) -> str:
    """Map Torznab category IDs or settings names to canonical UI category keys."""
    c = (cat or "").strip().lower()
    if c in (CAT_TV, "tv", "shows", "show", "series"):
        return "tv"
    if c in (CAT_MOVIES, "movie", "movies"):
        return "movies"
    if c in (CAT_AUDIO, "music", "audio"):
        return "music"
    if c in (CAT_BOOKS, "book", "books", "docs"):
        return "books"
    if c in (CAT_PC, "game", "games", "pc", "archives"):
        return "games"
    return c or "tv"


def find_alias_match(name: str, aliases: list[dict], query: str | None = None) -> dict | None:
    """Find the first alias matching the file name (via regex or title prefix/tokens)."""
    if not aliases:
        return None
    name_clean = name.strip()
    qk = _title_key(query) if query else ""
    for a in aliases:
        rx = (a.get("regex") or "").strip()
        if rx:
            try:
                if re.search(rx, name_clean, re.IGNORECASE):
                    return a
            except re.error:
                pass
        to_title = (a.get("to") or "").strip()
        from_title = (a.get("from") or "").strip()
        if qk:
            fk = _title_key(from_title)
            if fk and (fk in qk or qk in fk):
                if to_title and matches_query([to_title], name_clean):
                    return a
        if to_title and matches_query([to_title], name_clean):
            return a
        if from_title and matches_query([from_title], name_clean):
            return a
    return None


def get_alias_category(name: str, aliases: list[dict], query: str | None = None) -> str | None:
    """Return Torznab category (e.g. '5000', '2000') if file matches an alias with a category."""
    matched = find_alias_match(name, aliases, query)
    if matched and matched.get("category"):
        cat = to_torznab_cat(matched["category"])
        if cat:
            return cat
    return None


def parse_alias_marker(name: str, aliases: list[dict]) -> tuple[int | None, int | None]:
    """Extract (season, episode) from file name using alias regex capture groups if matched."""
    name_clean = name.strip()
    for a in aliases or []:
        rx = (a.get("regex") or "").strip()
        if not rx:
            continue
        try:
            m = re.search(rx, name_clean, re.IGNORECASE)
        except re.error:
            continue
        if m:
            gd = m.groupdict()
            s = gd.get("season")
            e = gd.get("ep") or gd.get("episode")
            if s is not None or e is not None:
                return (
                    int(s) if s and str(s).isdigit() else None,
                    int(e) if e and str(e).isdigit() else None,
                )
            groups = m.groups()
            if len(groups) >= 2:
                try:
                    return int(groups[0]), int(groups[1])
                except (ValueError, TypeError):
                    pass
            elif len(groups) == 1:
                rx_lower = rx.lower()
                if any(w in rx_lower for w in ("season", "serie", "seria", "sezon", r"\bs\b", "s(")):
                    try:
                        return int(groups[0]), None
                    except (ValueError, TypeError):
                        pass
                try:
                    return None, int(groups[0])
                except (ValueError, TypeError):
                    pass
    return None, None


def matches_query(query, name: str) -> bool:
    """True when the file name *starts with* the title words of the query (or of
    any of its alias titles, when a list is passed), or matches an alias regex.

    Webshare's fulltext is loose — a "Skvrna S01E05" search also returns any
    file merely containing "S01E05"/"05" (WWE, football...), and for common-word
    titles unrelated files too. Requiring the name to *begin* with the title
    keeps the right ones; multiple titles let a CZ alias ("Bez vědomí") match a
    query whose *arr title is English ("The Sleepers").
    """
    name_clean = name.strip()
    titles = _as_titles(query)
    aliases = getattr(settings, "aliases", [])

    # 1. Check alias regex matches
    regex_governed_titles = set()
    for title in titles:
        tk = _title_key(title)
        for a in aliases:
            rx = (a.get("regex") or "").strip()
            fk = _title_key(a.get("from", ""))
            to_title = _title_key(a.get("to", ""))
            if (fk and (fk in tk or tk == fk)) or (to_title and tk == to_title):
                if rx:
                    regex_governed_titles.add(to_title or fk)
                    try:
                        if re.search(rx, name_clean, re.IGNORECASE):
                            return True
                    except re.error:
                        pass

    # 2. Check title prefix match (only for titles not restricted by an unmet alias regex)
    ntoks = normalize_text(name).split()
    for title in titles:
        tk = _title_key(title)
        if tk in regex_governed_titles:
            continue
        tokens = _series_tokens(title)
        matched, _ = _match_series_prefix(tokens, ntoks)
        if matched:
            return True
    return False


def _matches_anywhere(query, name: str) -> bool:
    """True when all tokens from any search title appear anywhere in the file name.

    Used for music, books, and archives/games where files are often named
    'Artist - Album' or 'Author - Title' instead of starting with the title.
    """
    ntoks = set(normalize_text(name).split())
    for title in _as_titles(query):
        tokens = [t for t in normalize_text(title).split() if not _EP_TOKEN.match(t)]
        if not tokens:
            return True
        if all(tk in ntoks for tk in tokens):
            return True
    return False


def _detect_category(name: str, default: str = CAT_MOVIES) -> str:
    alias_cat = get_alias_category(name, getattr(settings, "aliases", []))
    if alias_cat:
        return alias_cat
    if re.search(r"[sS]\d{1,2}[eE]\d{1,3}|\b\d{1,2}x\d{2,3}\b", name):
        return CAT_TV
    name_l = name.lower()
    if name_l.endswith(VIDEO_EXTENSIONS):
        return default if default in (CAT_MOVIES, CAT_TV) else CAT_MOVIES
    if name_l.endswith(AUDIO_EXTENSIONS):
        return CAT_AUDIO
    if name_l.endswith(BOOK_EXTENSIONS):
        return CAT_BOOKS
    if name_l.endswith(ARCHIVE_EXTENSIONS):
        return CAT_PC
    return default


def file_marker(query, name: str) -> tuple[int | None, int | None]:
    """(season, episode) implied by the file name, read from an alias regex or the
    first marker after the (matched) show title: SxxEyy, 1x05, or a bare "05" (no season).

    Webshare fulltext is OR-based, so a "Skvrna 05" query returns every Skvrna
    episode — and a "DuckTales S01E02" query returns "DuckTales.S02E02..." too
    (matched on the show name alone). The caller must check both numbers: an
    episode-only match let season-2 files impersonate season 1, and the
    release-name rewrite then hid the real season from *arr entirely.
    """
    # 1. First check if an alias regex matches and extracts season / episode
    as_season, as_ep = parse_alias_marker(name, getattr(settings, "aliases", []))
    if as_season is not None or as_ep is not None:
        return as_season, as_ep

    ntoks = normalize_text(name).split()
    for title in _as_titles(query):
        series = _series_tokens(title)
        matched, tail = _match_series_prefix(series, ntoks)
        if not matched:
            continue  # this title isn't the one the file starts with

        is_special = False
        for i, tk in enumerate(tail):
            if tk in ("special", "specials"):
                is_special = True
                continue
            m = re.match(r"^s(\d{1,2})e(\d{1,3})$", tk) or re.match(r"^(\d{1,2})x(\d{1,3})$", tk)
            if m:
                return int(m.group(1)), int(m.group(2))
            m_s = re.match(r"^s(\d{1,2})$", tk)
            if m_s:
                return int(m_s.group(1)), None
            if tk in ("season", "serie", "seria", "sezona") and i + 1 < len(tail):
                if tail[i + 1].isdigit():
                    return int(tail[i + 1]), None
            if tk.isdigit() and i + 1 < len(tail) and tail[i + 1] in ("season", "serie", "seria", "sezona"):
                return int(tk), None
            if tk.isdigit() and len(tk) <= 2:  # bare episode number (skip years/1080)
                return (0 if is_special else None), int(tk)
        return None, None
    return None, None


def file_episode(query, name: str) -> int | None:
    """Episode number implied by the file name (see file_marker)."""
    return file_marker(query, name)[1]


def relevance(queries: list[str], name: str) -> float:
    """Best fraction of a query's tokens present in the file name."""
    ntoks = set(normalize_text(name).split())
    best = 0.0
    for q in queries:
        qt = normalize_text(q).split()
        if qt:
            best = max(best, sum(1 for t in qt if t in ntoks) / len(qt))
    return best


# Window the synthetic publish dates fall into (see _pub_date).
_PUB_EPOCH = 1640995200  # 2022-01-01 UTC
_PUB_SPAN = 365 * 86400


def _pub_date(ident: str) -> str:
    """A fixed, per-file publish date (RFC 2822).

    Webshare search has no upload date, and *arr needs one. It must not move:
    Sonarr/Radarr recognise a blocklisted usenet release by title + *exact*
    publish date, so "now" meant a failed release was never seen as blocklisted
    and was grabbed again on every search. Derived from the ident so two files
    sharing a release title still differ; years old is harmless (retention is
    the only age check, and age merely breaks ties between equal releases).
    """
    offset = int(hashlib.md5(ident.encode()).hexdigest(), 16) % _PUB_SPAN
    return email.utils.formatdate(_PUB_EPOCH + offset)


def _render_feed(request: Request, results: list[SearchResult], category: str,
                 *, query: str | None = None, season: str | None = None,
                 ep: str | None = None, episodes: dict[str, int] | None = None,
                 heights: dict[str, int] | None = None, audio: dict[str, str] | None = None,
                 language: str = "", czech_titles: list[str] | None = None) -> Response:
    heights = heights or {}
    audio = audio or {}
    episodes = episodes or {}
    ET.register_namespace("torznab", TORZNAB_NS)
    ET.register_namespace("newznab", NEWZNAB_NS)
    rss = ET.Element("rss", {"version": "2.0"})
    channel = ET.SubElement(rss, "channel")
    ET.SubElement(channel, "title").text = "Websharr"
    ET.SubElement(channel, "description").text = "Webshare.cz Newznab bridge"

    base = str(request.base_url).rstrip("/")

    for r in results:
        item = ET.SubElement(channel, "item")
        title = release_title(query, season, episodes.get(r.ident, ep), r.name) \
            if query is not None else \
            (r.name.rsplit(".", 1)[0] if "." in r.name else r.name)
        # Label quality from the real video height when the name lacks one,
        # so *arr doesn't reject the release as "Unknown" quality.
        if not _RES_RE.search(title) and heights.get(r.ident):
            title = f"{title} {heights[r.ident]}p"
        # A dub recognised without a marker in its name — by its audio track, or
        # by being named after the Czech title ("Cerveny trpaslik ...") — gets the
        # marker added, so title-based custom formats ("CZ" in release title)
        # see it too.
        inferred = "" if dub_language(r.name) else audio.get(r.ident) or \
            ("Czech" if czech_titles and matches_query(czech_titles, r.name) else "")
        marker, marker_re = ("SK", _SK_RE) if inferred == "Slovak" else ("CZ", _CZ_RE)
        if inferred and not marker_re.search(title):
            title = f"{title} {marker}"
        ET.SubElement(item, "title").text = title
        ET.SubElement(item, "guid", {"isPermaLink": "false"}).text = f"websharr-{r.ident}"
        # The saved file keeps the raw filename; the folder/title (nzbname) carries
        # the parseable SxxEyy so *arr import works. Pass the title as nzbname so a
        # direct GET of this link (or SAB addurl) names the job correctly.
        link = (
            f"{base}/torznab/nzb/{r.ident}"
            f"?apikey={config.api_key}"
            f"&name={urllib.parse.quote(_asciify(r.name))}&size={r.size}"
            f"&nzbname={urllib.parse.quote(title)}"
        )
        ET.SubElement(item, "link").text = link
        if r.ident and r.ident != "websharr-online":
            ET.SubElement(item, "comments").text = f"https://webshare.cz/#/file/{r.ident}/"
        ET.SubElement(item, "pubDate").text = _pub_date(r.ident)
        ET.SubElement(item, "size").text = str(r.size)
        ET.SubElement(item, "enclosure", {
            "url": link,
            "length": str(r.size),
            "type": "application/x-nzb",
        })
        # A CZ/SK dub overrides the title's original language (a dubbed release
        # is in the dub language, not the original), so *arr's original-language
        # policy grabs the original audio and skips the dub. A file named after
        # the Czech dub title ("Kačeří příběhy ...") is a Czech release even
        # when it carries no "dabing" marker.
        item_lang = dub_language(r.name) or inferred or language
        alias_cat = get_alias_category(r.name, getattr(settings, "aliases", []), query=query)
        if alias_cat:
            item_category = alias_cat
        elif re.search(r"[sS]\d{1,2}[eE]\d{1,3}|\b\d{1,2}x\d{2,3}\b", r.name):
            item_category = CAT_TV
        elif category not in ("", "all"):
            item_category = category
        else:
            item_category = _detect_category(r.name)
        # Emit attrs in both namespaces so the feed parses whether Sonarr/Radarr
        # treats it as Newznab (usenet — the correct choice) or Torznab.
        for ns in (NEWZNAB_NS, TORZNAB_NS):
            ET.SubElement(item, "{%s}attr" % ns, {"name": "category", "value": item_category})
            ET.SubElement(item, "{%s}attr" % ns, {"name": "size", "value": str(r.size)})
            ET.SubElement(item, "{%s}attr" % ns,
                          {"name": "grabs", "value": str(r.positive_votes)})
            if item_lang:
                ET.SubElement(item, "{%s}attr" % ns,
                              {"name": "language", "value": item_lang})

    return _xml_response(rss)


@router.get("/torznab/api")
async def torznab_api(request: Request):
    params = request.query_params
    if params.get("apikey") != config.api_key:
        return _error(100, "Invalid API key")

    t = params.get("t", "caps")
    if t == "caps":
        return _caps()
    if t not in ("search", "tvsearch", "movie", "music", "book"):
        return _error(203, f"Function '{t}' not available")

    cat_param = (params.get("cat", "") or "").strip()
    cat_list = [c.strip() for c in cat_param.split(",") if c.strip()]

    if t == "tvsearch":
        category = CAT_TV
        ws_category = "video"
    elif t == "movie":
        category = CAT_MOVIES
        ws_category = "video"
    elif t == "music":
        category = CAT_AUDIO
        ws_category = "audio"
    elif t == "book":
        category = CAT_BOOKS
        ws_category = "docs"
    else:  # t == "search"
        if any(c.startswith("3") for c in cat_list):
            category = CAT_AUDIO
            ws_category = "audio"
        elif any(c.startswith("7") or c.startswith("8") for c in cat_list):
            category = CAT_BOOKS
            ws_category = "docs"
        elif any(c.startswith("4") for c in cat_list):
            category = CAT_PC
            ws_category = "archives"
        elif any(c.startswith("5") for c in cat_list):
            category = CAT_TV
            ws_category = "video"
        elif any(c.startswith("2") for c in cat_list):
            category = CAT_MOVIES
            ws_category = "video"
        elif cat_list:
            category = cat_list[0]
            ws_category = "all"
        else:
            category = CAT_MOVIES
            ws_category = "all"

    if ws_category == "video":
        t, q, season, ep = parse_query(t, params.get("q", ""), params.get("season"), params.get("ep"))
        # A *arr query may match a Webshare/CZ title (alias map or TMDB lookup);
        # search all and accept files matching any of them. `display` is the nice
        # title used to prefix the release name.
        titles, display, language, czech_titles, year = await expand_titles(
            t, q, params.get("cat"), tvdbid=params.get("tvdbid"),
            imdbid=params.get("imdbid"), tmdbid=params.get("tmdbid"))
        queries = []
        for title in titles:
            for v in build_queries(t, title, season, ep):
                if v not in queries:
                    queries.append(v)
    else:
        q = (params.get("q", "") or "").strip()
        season, ep = None, None
        alias_t = alias_titles(q, getattr(settings, "aliases", []))
        titles = ([q] if q else []) + [x for x in alias_t if x not in ([q] if q else [])]
        display = q
        language = ""
        czech_titles = []
        year = 0
        queries = list(titles)

    if not queries:
        # Webshare has no RSS/"latest" feed, but Sonarr/Radarr reject an indexer
        # whose capability-test query returns zero items ("no results in the
        # configured categories"). Return one deliberately unparseable placeholder
        # in the requested category so the test passes; the decision engine has no
        # title to parse during RSS sync, so it is never grabbed.
        cat = (params.get("cat", "") or "").split(",")[0].strip() or category
        placeholder = SearchResult(
            ident="websharr-online",
            name="Websharr online - no automatic feed, use interactive search",
            size=1,
        )
        return _render_feed(request, [placeholder], cat)

    limit = min(int(params.get("limit", str(config.search_limit)) or config.search_limit), 100)
    offset = int(params.get("offset", "0") or 0)

    want_ep = int(ep) if (t == "tvsearch" and ep and str(ep).isdigit()) else None
    want_season = int(season) if (t == "tvsearch" and season and str(season).isdigit()) else None
    client = request.app.state.webshare
    seen: set[str] = set()
    merged: list[SearchResult] = []
    episodes: dict[str, int] = {}  # season search: each file's own episode number
    for query in queries:
        try:
            results = await client.search(query, category="", limit=limit, offset=offset)
        except (WebshareError, httpx.HTTPError) as exc:
            logger.error("Search '%s' failed: %s", query, exc)
            return _error(900, f"Webshare search failed: {exc}")
        for r in results:
            if r.ident in seen or r.password or not _is_allowed_file(r.name, ws_category):
                continue
            if ws_category == "video":
                if not matches_query(titles, r.name):
                    continue  # drop Webshare's loose non-matching fulltext hits
                if year_conflict(r.name, year):
                    continue  # same-named other title (DuckTales 1987 vs 2017)
                if want_ep is not None or want_season is not None:
                    fs, fe = file_marker(titles, r.name)
                    if want_ep is not None and fe != want_ep:
                        continue  # OR fulltext returns every episode; keep the asked one
                    if want_season is not None and fs is not None and fs != want_season:
                        continue  # an S02E02 file is not the requested S01E02
                    if want_ep is None:
                        # Season search (Sonarr's automatic search when several
                        # episodes of a season are missing).
                        if fs == want_season and fe is None:
                            # Whole season pack (e.g. S01.rar)
                            pass
                        elif fe is not None:
                            # Individual episode in season search
                            if fs is None and want_season != 1:
                                continue
                            episodes[r.ident] = fe
                        else:
                            continue
            else:
                if not (matches_query(titles, r.name) or _matches_anywhere(titles, r.name)):
                    continue
            seen.add(r.ident)
            merged.append(r)

    merged.sort(key=lambda r: (-relevance(queries, r.name), -r.size))
    logger.info("Newznab %s q=%r -> %d results", t, q, len(merged))
    shown = merged[:limit]
    if ws_category == "video":
        heights, audio = await _probe(client, shown)
    else:
        heights, audio = {}, {}
    return _render_feed(request, shown, category, heights=heights, audio=audio,
                        query=display, season=(season if t == "tvsearch" else None), ep=ep,
                        episodes=episodes, language=language, czech_titles=czech_titles)


@router.get("/torznab/nzb/{ident}")
async def torznab_nzb(ident: str, request: Request):
    if request.query_params.get("apikey") != config.api_key:
        return _error(100, "Invalid API key")

    # Filename/size are carried in the link generated by the search feed, so
    # the NZB is self-contained; ident alone is still enough to download.
    name = request.query_params.get("name") or ident
    try:
        size = int(request.query_params.get("size", "0"))
    except ValueError:
        size = 0

    content = build_nzb(ident, name, size)
    # Name the NZB after the parseable release title (nzbname) when present:
    # Sonarr re-uploads it to the SABnzbd client using this filename as the job
    # name, so the download folder carries SxxEyy for import.
    stem = request.query_params.get("nzbname") or \
        (name.rsplit(".", 1)[0] if "." in name else name)
    # Fully transliterate to ASCII — no RFC 5987 filename*: Prowlarr decodes that
    # back to the diacritics and re-emits them raw in its own header, which its
    # HTTP layer rejects ("Invalid non-ASCII in header 0x011B" = ě).
    ascii_name = re.sub(r'[^\x20-\x7e]', "_", _asciify(stem)).replace('"', "_") or "download"
    disposition = f'attachment; filename="{ascii_name}.nzb"'
    return Response(
        content=content,
        media_type="application/x-nzb",
        headers={"Content-Disposition": disposition},
    )
