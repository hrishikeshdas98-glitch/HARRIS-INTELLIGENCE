#!/usr/bin/env python3
"""
Harris County Motivated Seller Lead Scraper  v2
- Correct portal: /applications/websearch/RP.aspx
- Fast timeouts: 15s page load, 8s element — no more 4-min hangs per doc type
- Dual strategy: direct HTTP POST first, Playwright fallback second
- HCAD parcel address lookup
- Never crashes on bad records
"""

import asyncio
import csv
import io
import json
import logging
import os
import re
import sys
import time
import traceback
import zipfile
from datetime import datetime, timedelta
from pathlib import Path
from typing import Optional

import requests
from bs4 import BeautifulSoup

try:
    from playwright.async_api import async_playwright, TimeoutError as PWTimeout
    HAS_PLAYWRIGHT = True
except ImportError:
    HAS_PLAYWRIGHT = False

try:
    from dbfread import DBF
    HAS_DBF = True
except ImportError:
    HAS_DBF = False

# ─────────────────────────────────────────────────────────────────────────────
# CONFIG
# ─────────────────────────────────────────────────────────────────────────────
CLERK_BASE = "https://www.cclerk.hctx.net"
CLERK_RP   = f"{CLERK_BASE}/applications/websearch/RP.aspx"
CLERK_RP_R = f"{CLERK_BASE}/applications/websearch/RP_R.aspx"  # results page

HCAD_PAGES = [
    "https://pdata.hcad.org/download/2025.html",
    "https://pdata.hcad.org/download/2024.html",
    "https://hcad.org/hcad-resources/hcad-appraisal-codes-and-data-download/",
]

CLERK_USERNAME = os.environ.get("CLERK_USERNAME", "")
CLERK_PASSWORD = os.environ.get("CLERK_PASSWORD", "")

LOOK_BACK_DAYS = int(os.environ.get("LOOK_BACK_DAYS", "80"))
MAX_RETRIES    = 3
RETRY_DELAY    = 2

PW_TIMEOUT  = 15_000   # 15 s page load
PW_EL_WAIT  = 8_000    # 8 s per element find

DOC_TYPES = {
    # ── Lis Pendens ───────────────────────────────────────────────────────────
    "L/P":    ("Lis Pendens",                "lis_pendens"),

    # ── Foreclosure ───────────────────────────────────────────────────────────
    "TRSALE": ("Trustee Sale",               "foreclosure"),
    "NOTICE": ("Notice (Foreclosure/Sale)",  "foreclosure"),

    # ── Judgments ─────────────────────────────────────────────────────────────
    "JUDGE":  ("Judgment",                   "judgment"),
    "A/J":    ("Abstract of Judgment",       "judgment"),
    "ORDER":  ("Court Order",                "judgment"),

    # ── Federal / Tax Liens ───────────────────────────────────────────────────
    "T/L":    ("Federal Tax Lien",           "tax_lien"),

    # ── All Liens (HOA, State, Mechanic, Medical, etc.) ──────────────────────
    "LIEN":   ("Lien",                       "lien"),
    "L AFFT": ("Lien Affidavit",             "lien"),
    "CONT":   ("Contract / Mechanic Lien",   "lien"),

    # ── Probate ───────────────────────────────────────────────────────────────
    "PROB":   ("Probate Proceedings",        "probate"),

    # ── Releases ─────────────────────────────────────────────────────────────
    "REL":    ("Release",                    "release"),

    # ── Deeds ─────────────────────────────────────────────────────────────────
    "DEED":   ("Deed",                       "deed"),
    "D/T":    ("Deed of Trust",              "deed_of_trust"),

    # ── Tax Receipt / Bankruptcy ──────────────────────────────────────────────
    "BNKRCY": ("Bankruptcy",                 "bankruptcy"),
    "T/R":    ("Tax Receipt",                "tax_receipt"),
}

CAT_LABELS = {
    "lis_pendens":   "Lis Pendens",
    "foreclosure":   "Pre-Foreclosure / Trustee Sale",
    "judgment":      "Judgment / Abstract",
    "tax_lien":      "Federal Tax Lien",
    "lien":          "Lien",
    "probate":       "Probate / Estate",
    "release":       "Release",
    "deed":          "Deed",
    "deed_of_trust": "Deed of Trust",
    "bankruptcy":    "Bankruptcy",
    "tax_receipt":   "Tax Receipt",
}

# ─────────────────────────────────────────────────────────────────────────────
# LOGGING
# ─────────────────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)],
)
log = logging.getLogger("scraper")

# ─────────────────────────────────────────────────────────────────────────────
# HELPERS
# ─────────────────────────────────────────────────────────────────────────────
def parse_amount(text: str) -> Optional[float]:
    if not text:
        return None
    cleaned = re.sub(r"[^\d.]", "", str(text).replace(",", ""))
    try:
        v = float(cleaned)
        return v if v > 0 else None
    except ValueError:
        return None


def parse_date(text: str) -> str:
    for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y", "%d/%m/%Y", "%m/%d/%y"):
        try:
            return datetime.strptime(text.strip(), fmt).strftime("%Y-%m-%d")
        except Exception:
            continue
    return text.strip()


def name_variants(name: str) -> list:
    name = name.strip().upper()
    variants = {name}
    if "," in name:
        parts = [p.strip() for p in name.split(",", 1)]
        variants.add(f"{parts[1]} {parts[0]}")
        variants.add(f"{parts[0]} {parts[1]}")
    else:
        parts = name.split()
        if len(parts) >= 2:
            variants.add(f"{parts[-1]}, {' '.join(parts[:-1])}")
            variants.add(f"{parts[-1]} {' '.join(parts[:-1])}")
    return list(variants)


def blank_record(doc_code: str, cat: str, label: str) -> dict:
    return {
        "doc_num":      "",
        "doc_type":     doc_code,
        "filed":        "",
        "cat":          cat,
        "cat_label":    CAT_LABELS.get(cat, label),
        "owner":        "",
        "grantee":      "",
        "amount":       None,
        "legal":        "",
        "prop_address": "",
        "prop_city":    "Houston",
        "prop_state":   "TX",
        "prop_zip":     "",
        "mail_address": "",
        "mail_city":    "",
        "mail_state":   "",
        "mail_zip":     "",
        "clerk_url":    "",
        "flags":        [],
        "score":        0,
    }


def score_record(rec: dict) -> tuple:
    flags = []
    score = 30
    cat = rec.get("cat", "")
    doc = rec.get("doc_type", "").upper()

    if cat == "lis_pendens":     flags.append("Lis pendens")
    if cat == "foreclosure":     flags.append("Pre-foreclosure")
    if cat == "judgment":        flags.append("Judgment lien")
    if cat == "tax_lien":        flags.append("Tax lien")
    if cat == "lien":            flags.append("Mechanic lien" if "MECH" in doc or "CONT" in doc else "Lien")
    if cat == "probate":         flags.append("Probate / estate")
    if cat == "bankruptcy":      flags.append("Bankruptcy")

    owner = rec.get("owner", "")
    if owner and re.search(r"\b(LLC|INC|CORP|LTD|LP|TRUST|ASSOC)\b", owner, re.I):
        flags.append("LLC / corp owner")

    try:
        filed = datetime.strptime(rec.get("filed", ""), "%Y-%m-%d")
        if (datetime.now() - filed).days <= 7:
            flags.append("New this week")
            score += 5
    except Exception:
        pass

    score += 10 * len(flags)

    amount = rec.get("amount")
    if amount:
        if amount > 100_000:  score += 15
        elif amount > 50_000: score += 10

    if rec.get("prop_address"):
        score += 5

    return min(score, 100), flags


def parse_table(html: str, doc_code: str, cat: str, label: str) -> list:
    """Extract records from any result table in an HTML page."""
    soup = BeautifulSoup(html, "lxml")
    rows = []
    for tbl in soup.find_all("table"):
        ths = tbl.find_all("th")
        if not ths:
            continue
        hdrs = [th.get_text(strip=True).lower() for th in ths]
        joined = " ".join(hdrs)
        if not any(k in joined for k in ("doc", "filed", "grantor", "instrument", "grantee")):
            continue
        for tr in tbl.find_all("tr")[1:]:
            tds = tr.find_all("td")
            if len(tds) < 3:
                continue
            try:
                link = ""
                for td in tds:
                    a = td.find("a", href=True)
                    if a:
                        href = a["href"]
                        link = href if href.startswith("http") else f"{CLERK_BASE}/{href.lstrip('/')}"
                        break

                def cell(idx):
                    return tds[idx].get_text(strip=True) if idx < len(tds) else ""

                rec = blank_record(doc_code, cat, label)
                rec["doc_num"]   = cell(0)
                rec["filed"]     = parse_date(cell(1))
                rec["owner"]     = cell(2)
                rec["grantee"]   = cell(3)
                rec["legal"]     = cell(4)
                rec["amount"]    = parse_amount(cell(5))
                rec["clerk_url"] = link or f"{CLERK_RP}?DocNum={cell(0)}"
                if rec["doc_num"]:
                    rows.append(rec)
            except Exception:
                continue
    return rows

# ─────────────────────────────────────────────────────────────────────────────
# STRATEGY 1 — Direct HTTP POST  (no browser, fastest)
# ─────────────────────────────────────────────────────────────────────────────
class DirectHTTPScraper:

    def __init__(self, start: datetime, end: datetime):
        self.start   = start
        self.end     = end
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/124.0.0.0 Safari/537.36"
            ),
            "Accept": "text/html,application/xhtml+xml,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.5",
            "Referer": CLERK_RP,
        })
        self._vs  = ""
        self._ev  = ""
        self._vsg = ""

    def _hidden(self, soup, name):
        el = soup.find("input", {"name": name})
        return el["value"] if el and el.get("value") else ""

    def _load_tokens(self) -> bool:
        for attempt in range(MAX_RETRIES):
            try:
                r = self.session.get(CLERK_RP, timeout=20)
                r.raise_for_status()
                soup = BeautifulSoup(r.text, "lxml")
                self._vs  = self._hidden(soup, "__VIEWSTATE")
                self._ev  = self._hidden(soup, "__EVENTVALIDATION")
                self._vsg = self._hidden(soup, "__VIEWSTATEGENERATOR")

                # Debug: print ALL input/select field names on the page
                all_inputs = soup.find_all(["input","select","textarea"])
                field_names = [el.get("name","") for el in all_inputs if el.get("name")]
                log.info(f"Form fields found on RP.aspx: {field_names}")

                if self._vs:
                    log.info("ASP.NET tokens loaded")
                    return True
                log.warning("No __VIEWSTATE on page — portal may redirect to login")
                return False
            except Exception as exc:
                log.warning(f"Token load attempt {attempt+1}: {exc}")
                time.sleep(RETRY_DELAY)
        return False

    def _login(self) -> bool:
        """
        Log in via HTTP POST.
        The portal's 'Log In' link triggers __doPostBack which opens a modal.
        We POST directly to the ASP.NET Login control endpoint.
        """
        if not CLERK_USERNAME or not CLERK_PASSWORD:
            log.warning("No credentials set — skipping login")
            return False

        log.info(f"HTTP: logging in as {CLERK_USERNAME}…")

        # Try each known login endpoint
        login_urls = [
            f"{CLERK_BASE}/applications/websearch/Home.aspx",
            f"{CLERK_BASE}/applications/websearch/eLogin.aspx",
            f"{CLERK_BASE}/applications/websearch/Login.aspx",
        ]

        for login_url in login_urls:
            try:
                r = self.session.get(login_url, timeout=20)
                r.raise_for_status()
                soup = BeautifulSoup(r.text, "lxml")
                vs  = self._hidden(soup, "__VIEWSTATE")
                ev  = self._hidden(soup, "__EVENTVALIDATION")
                vsg = self._hidden(soup, "__VIEWSTATEGENERATOR")

                if not vs:
                    continue  # no form here, try next URL

                # The ASP.NET Login control uses these field names
                payload = {
                    "__VIEWSTATE":          vs,
                    "__VIEWSTATEGENERATOR": vsg,
                    "__EVENTVALIDATION":    ev,
                    "__EVENTTARGET":        "ctl00$cphMain$Login1",
                    "__EVENTARGUMENT":      "",
                    # ASP.NET Login control field names
                    "ctl00$cphMain$Login1$UserName": CLERK_USERNAME,
                    "ctl00$cphMain$Login1$Password": CLERK_PASSWORD,
                    "ctl00$cphMain$Login1$LoginButton": "Log In",
                    # Alternate patterns
                    "ctl00$cphMain$txtUserName": CLERK_USERNAME,
                    "ctl00$cphMain$txtPassword": CLERK_PASSWORD,
                    "ctl00$cphMain$btnLogin":    "Log In",
                    # Simple names
                    "UserName": CLERK_USERNAME,
                    "Password": CLERK_PASSWORD,
                }

                r2 = self.session.post(login_url, data=payload, timeout=20)
                r2.raise_for_status()
                body = r2.text.lower()

                if any(k in body for k in ("log out", "logout", "sign out", "my account", "welcome back")):
                    log.info("HTTP login successful ✅")
                    return True
                elif any(k in body for k in ("invalid", "incorrect", "wrong")):
                    log.error("HTTP login failed — check credentials")
                    return False
                else:
                    log.info(f"HTTP login at {login_url} — state unclear, proceeding")
                    return True  # session cookie may be set regardless

            except Exception as exc:
                log.warning(f"HTTP login attempt at {login_url}: {exc}")
                continue

        log.warning("HTTP: all login URLs failed")
        return False

    def run(self) -> list:
        # Login first, then load search tokens
        self._login()
        if not self._load_tokens():
            return []
        records = []
        for doc_code, (label, cat) in DOC_TYPES.items():
            try:
                recs = self._search(doc_code, label, cat)
                records.extend(recs)
                log.info(f"  HTTP {doc_code}: {len(recs)}")
            except Exception:
                log.error(f"HTTP {doc_code}: {traceback.format_exc()}")
        return records

    def _search(self, doc_code: str, label: str, cat: str) -> list:
        sd = self.start.strftime("%m/%d/%Y")
        ed = self.end.strftime("%m/%d/%Y")

        # EXACT field names from browser Network payload inspection
        payload = {
            "__VIEWSTATE":          self._vs,
            "__VIEWSTATEGENERATOR": self._vsg,
            "__EVENTVALIDATION":    self._ev,
            "__EVENTTARGET":        "",
            "__EVENTARGUMENT":      "",
            "__LASTFOCUS":          "",
            # ── Exact field names confirmed from portal payload ──
            "ctl00$ContentPlaceHolder1$txtFileNo":    "",
            "ctl00$ContentPlaceHolder1$txtFilmCd":    "",
            "ctl00$ContentPlaceHolder1$txtFrom":      sd,
            "ctl00$ContentPlaceHolder1$txtTo":        ed,
            "ctl00$ContentPlaceHolder1$txtOR":        "",   # Grantor
            "ctl00$ContentPlaceHolder1$txtEE":        "",   # Grantee
            "ctl00$ContentPlaceHolder1$txtNameTee":   "",   # Trustee
            "ctl00$ContentPlaceHolder1$txtDesc":      "",   # Description
            "ctl00$ContentPlaceHolder1$txtInstrument": doc_code,  # Instrument Type
            "ctl00$ContentPlaceHolder1$txtVolNo":     "",
            "ctl00$ContentPlaceHolder1$txtPageNo":    "",
            "ctl00$ContentPlaceHolder1$txtSection":   "",
            "ctl00$ContentPlaceHolder1$txtLot":       "",
            "ctl00$ContentPlaceHolder1$txtBlock":     "",
            "ctl00$ContentPlaceHolder1$txtUnit":      "",
            "ctl00$ContentPlaceHolder1$txtAbstract":  "",
            "ctl00$ContentPlaceHolder1$txtOutLot":    "",
            "ctl00$ContentPlaceHolder1$txtTract":     "",
            "ctl00$ContentPlaceHolder1$txtReserve":   "",
            "ctl00$ContentPlaceHolder1$btnSearch":    "Search",
        }
        for attempt in range(MAX_RETRIES):
            try:
                r = self.session.post(CLERK_RP, data=payload, timeout=30)
                r.raise_for_status()
                results = parse_table(r.text, doc_code, cat, label)
                # If 0 results, log snippet to help debug
                if not results:
                    snippet = r.text[:300].replace("\n"," ").strip()
                    log.info(f"  HTTP {doc_code} 0 results — page snippet: {snippet[:200]}")
                return results
            except Exception as exc:
                log.warning(f"  HTTP {doc_code} attempt {attempt+1}: {exc}")
                time.sleep(RETRY_DELAY)
        return []

# ─────────────────────────────────────────────────────────────────────────────
# STRATEGY 2 — Playwright  (browser, used only if HTTP returns nothing)
# ─────────────────────────────────────────────────────────────────────────────
class PlaywrightScraper:

    def __init__(self, start: datetime, end: datetime):
        self.start = start
        self.end   = end

    async def _login(self, page) -> bool:
        """
        Log in via the clerk portal.
        The site uses a JS __doPostBack link to open a login modal —
        no traditional form on the home page.
        Strategy:
          1. Navigate to Home.aspx
          2. Click the 'Log In' link (triggers __doPostBack modal OR redirect)
          3. Wait for username/password fields to appear
          4. Fill and submit
        """
        if not CLERK_USERNAME or not CLERK_PASSWORD:
            log.warning("No credentials set — skipping login")
            return False

        login_url = f"{CLERK_BASE}/applications/websearch/Home.aspx"
        log.info(f"PW: logging in as {CLERK_USERNAME}…")

        try:
            await page.goto(login_url, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
        except Exception as exc:
            log.warning(f"PW login page load: {exc}")
            return False

        # The login link uses __doPostBack — click it via JS to open the modal
        try:
            await page.evaluate("__doPostBack('ctl00$LoginStatus1$ctl02','')")
            await asyncio.sleep(1.5)
        except Exception:
            # Try clicking the visible "Log In" anchor text instead
            try:
                await page.click("a:has-text('Log In')", timeout=5_000)
                await asyncio.sleep(1.5)
            except Exception as exc:
                log.warning(f"PW: could not trigger login modal: {exc}")

        # After modal opens OR page redirects, look for input fields
        # Try filling username in whichever field appears
        filled_user = await self._try_fill(page, [
            "#ctl00_cphMain_Login1_UserName",
            "#ctl00_cphMain_txtUserName",
            "input[id*='UserName']",
            "input[id*='Email']",
            "input[name*='UserName']",
            "input[name*='Email']",
            "input[type='email']",
            "input[type='text']:not([id*='search']):not([id*='Search'])",
        ], CLERK_USERNAME)

        filled_pass = await self._try_fill(page, [
            "#ctl00_cphMain_Login1_Password",
            "#ctl00_cphMain_txtPassword",
            "input[id*='Password']",
            "input[name*='Password']",
            "input[type='password']",
        ], CLERK_PASSWORD)

        if not filled_user or not filled_pass:
            log.warning(f"PW: could not fill login fields (user={filled_user}, pass={filled_pass})")
            # Try navigating directly to a login redirect URL as fallback
            return await self._login_direct_post(page)

        # Submit — the login form uses an ASP.NET Login control button
        clicked = await self._try_click(page, [
            "#ctl00_cphMain_Login1_LoginButton",
            "input[id*='LoginButton']",
            "input[id*='btnLogin']",
            "input[value='Log In']",
            "input[value='Login']",
            "button:has-text('Log In')",
            "button:has-text('Login')",
            "input[type='submit']",
        ])

        if not clicked:
            # Try submitting the form via Enter key
            try:
                await page.keyboard.press("Enter")
            except Exception:
                pass

        try:
            await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
        except Exception:
            pass

        return await self._check_logged_in(page)

    async def _login_direct_post(self, page) -> bool:
        """
        Fallback: navigate directly to the eLogin page which some clerk
        portals expose as a standalone form at /eLogin.aspx or /Login.aspx
        """
        for login_path in [
            "/applications/websearch/eLogin.aspx",
            "/applications/websearch/Login.aspx",
            "/applications/websearch/eComm/Login.aspx",
        ]:
            url = CLERK_BASE + login_path
            try:
                r = await page.goto(url, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
                if r and r.ok:
                    content = await page.content()
                    if "password" in content.lower():
                        log.info(f"Found login form at {url}")
                        # Use exact field labels seen on eLogin.aspx:
                        # "User Name or Email" and "Password" with green "LOG IN" button
                        await self._try_fill(page, [
                            "input[id*='UserName']",
                            "input[id*='Email']",
                            "input[name*='UserName']",
                            "input[placeholder*='User']",
                            "input[type='email']",
                            "input[type='text']",
                        ], CLERK_USERNAME)
                        await self._try_fill(page, [
                            "input[id*='Password']",
                            "input[name*='Password']",
                            "input[type='password']",
                        ], CLERK_PASSWORD)
                        await self._try_click(page, [
                            "input[value='LOG IN']",
                            "input[value='Log In']",
                            "input[value='Login']",
                            "button:has-text('LOG IN')",
                            "button:has-text('Log In')",
                            "input[type='submit']",
                            "button[type='submit']",
                        ])
                        try:
                            await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                        except Exception:
                            pass
                        return await self._check_logged_in(page)
            except Exception:
                continue
        log.warning("PW: all login fallbacks exhausted")
        return False

    async def _check_logged_in(self, page) -> bool:
        body = (await page.content()).lower()
        if any(k in body for k in ("log out", "logout", "sign out", "my account", "welcome back")):
            log.info("PW login successful ✅")
            return True
        elif any(k in body for k in ("invalid", "incorrect", "failed", "wrong password")):
            log.error("PW login failed — check CLERK_USERNAME / CLERK_PASSWORD secrets")
            return False
        else:
            log.info("PW login state unknown — proceeding anyway")
            return True

    async def run(self) -> list:
        records = []
        async with async_playwright() as pw:
            browser = await pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage"]
            )
            ctx  = await browser.new_context(user_agent=(
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/124.0.0.0 Safari/537.36"
            ))
            page = await ctx.new_page()
            page.set_default_timeout(PW_TIMEOUT)

            # Login first
            await self._login(page)

            for doc_code, (label, cat) in DOC_TYPES.items():
                try:
                    recs = await self._search(page, doc_code, label, cat)
                    records.extend(recs)
                    log.info(f"  PW {doc_code}: {len(recs)}")
                except Exception:
                    log.error(f"PW {doc_code}: {traceback.format_exc()}")

            await browser.close()
        return records

    async def _try_fill(self, page, selectors: list, value: str):
        for sel in selectors:
            try:
                el = await page.wait_for_selector(sel, timeout=PW_EL_WAIT)
                if el:
                    await el.fill(value)
                    return
            except Exception:
                continue

    async def _try_select(self, page, selectors: list, value: str):
        for sel in selectors:
            try:
                el = await page.wait_for_selector(sel, timeout=PW_EL_WAIT)
                if el:
                    await page.select_option(sel, value)
                    return
            except Exception:
                continue

    async def _try_click(self, page, selectors: list) -> bool:
        for sel in selectors:
            try:
                el = await page.wait_for_selector(sel, timeout=PW_EL_WAIT)
                if el:
                    await el.click()
                    return True
            except Exception:
                continue
        return False

    async def _search(self, page, doc_code: str, label: str, cat: str) -> list:
        # Navigate — fast fail
        try:
            await page.goto(CLERK_RP, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
        except Exception as exc:
            log.warning(f"  PW nav failed {doc_code}: {exc}")
            return []

        sd = self.start.strftime("%m/%d/%Y")
        ed = self.end.strftime("%m/%d/%Y")

        # Exact IDs confirmed from browser payload (ContentPlaceHolder1 prefix)
        await self._try_fill(page, [
            "#ctl00_ContentPlaceHolder1_txtInstrument",
            "input[name='ctl00$ContentPlaceHolder1$txtInstrument']",
            "input[id*='txtInstrument']",
        ], doc_code)
        await self._try_fill(page, [
            "#ctl00_ContentPlaceHolder1_txtFrom",
            "input[name='ctl00$ContentPlaceHolder1$txtFrom']",
            "input[id*='txtFrom']",
        ], sd)
        await self._try_fill(page, [
            "#ctl00_ContentPlaceHolder1_txtTo",
            "input[name='ctl00$ContentPlaceHolder1$txtTo']",
            "input[id*='txtTo']",
        ], ed)

        clicked = await self._try_click(page, [
            "#ctl00_ContentPlaceHolder1_btnSearch",
            "input[name='ctl00$ContentPlaceHolder1$btnSearch']",
            "input[value='Search']",
            "input[type='submit']",
        ])
        if not clicked:
            return []

        try:
            await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
        except Exception:
            pass  # partial load is OK, parse what we have

        # Collect all pages
        all_rows = []
        for _ in range(50):  # max 50 pages safety
            html = await page.content()
            rows = parse_table(html, doc_code, cat, label)
            all_rows.extend(rows)

            # Next page
            next_found = False
            for sel in ["a:has-text('Next')","a:has-text('>')","input[value='Next']"]:
                try:
                    el = await page.wait_for_selector(sel, timeout=3_000)
                    if el:
                        await el.click()
                        await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                        next_found = True
                        break
                except Exception:
                    continue
            if not next_found:
                break

        return all_rows

# ─────────────────────────────────────────────────────────────────────────────
# FORECLOSURE SCRAPER  (FRCL_R.aspx — dedicated monthly foreclosure listings)
# This page uses year + month selectors, completely separate from RP search.
# ─────────────────────────────────────────────────────────────────────────────
class ForeclosureScraper:
    """
    Scrapes https://www.cclerk.hctx.net/applications/websearch/FRCL_R.aspx
    Selects year and month via __doPostBack, parses the resulting table.
    Can scrape any month/year combination.
    """

    FRCL_URL = f"{CLERK_BASE}/applications/websearch/FRCL_R.aspx"

    # Month name → number mapping as used by the portal dropdown
    MONTH_NAMES = {
        1:"January", 2:"February", 3:"March", 4:"April",
        5:"May", 6:"June", 7:"July", 8:"August",
        9:"September", 10:"October", 11:"November", 12:"December",
    }

    def __init__(self, year: int, month: int):
        self.year  = year
        self.month = month
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/124.0.0.0 Safari/537.36"
            ),
            "Referer": f"{CLERK_BASE}/applications/websearch/FRCL_R.aspx",
        })

    def _hidden(self, soup: BeautifulSoup, name: str) -> str:
        el = soup.find("input", {"name": name})
        return el["value"] if el and el.get("value") else ""

    def _login(self) -> bool:
        """Log in using same credentials as main scraper."""
        if not CLERK_USERNAME or not CLERK_PASSWORD:
            return False
        login_url = f"{CLERK_BASE}/applications/websearch/eLogin.aspx"
        try:
            r = self.session.get(login_url, timeout=20)
            soup = BeautifulSoup(r.text, "lxml")
            vs  = self._hidden(soup, "__VIEWSTATE")
            ev  = self._hidden(soup, "__EVENTVALIDATION")
            vsg = self._hidden(soup, "__VIEWSTATEGENERATOR")
            payload = {
                "__VIEWSTATE": vs, "__EVENTVALIDATION": ev,
                "__VIEWSTATEGENERATOR": vsg,
                "__EVENTTARGET": "", "__EVENTARGUMENT": "",
                "ctl00$cphMain$Login1$UserName": CLERK_USERNAME,
                "ctl00$cphMain$Login1$Password": CLERK_PASSWORD,
                "ctl00$cphMain$Login1$LoginButton": "Log In",
                "UserName": CLERK_USERNAME,
                "Password": CLERK_PASSWORD,
            }
            r2 = self.session.post(login_url, data=payload, timeout=20)
            body = r2.text.lower()
            if any(k in body for k in ("log out","logout","my account","welcome")):
                log.info("ForeclosureScraper: login OK ✅")
                return True
            log.info("ForeclosureScraper: login ambiguous — proceeding")
            return True
        except Exception as exc:
            log.warning(f"ForeclosureScraper login: {exc}")
            return False

    def _load_page(self) -> Optional[BeautifulSoup]:
        """Load the base FRCL_R page and return its soup."""
        for attempt in range(MAX_RETRIES):
            try:
                r = self.session.get(self.FRCL_URL, timeout=20)
                r.raise_for_status()
                return BeautifulSoup(r.text, "lxml")
            except Exception as exc:
                log.warning(f"FRCL load attempt {attempt+1}: {exc}")
                time.sleep(RETRY_DELAY)
        return None

    def _select_year_month(self, soup: BeautifulSoup) -> Optional[BeautifulSoup]:
        """
        The page uses __doPostBack to select year then month.
        We POST the form with the year value, then POST again with month.
        """
        vs  = self._hidden(soup, "__VIEWSTATE")
        ev  = self._hidden(soup, "__EVENTVALIDATION")
        vsg = self._hidden(soup, "__VIEWSTATEGENERATOR")

        # Step 1: Select year
        year_payload = {
            "__VIEWSTATE":          vs,
            "__VIEWSTATEGENERATOR": vsg,
            "__EVENTVALIDATION":    ev,
            "__EVENTTARGET":        "ctl00$cphMain$GridView1",
            "__EVENTARGUMENT":      f"Select${self.year}",
            # Also try direct year field
            "ctl00$cphMain$ddlYear": str(self.year),
            "ctl00$cphMain$ddlMonth": self.MONTH_NAMES.get(self.month, "June"),
            "ctl00$cphMain$btnSearch": "Search",
        }

        try:
            r = self.session.post(self.FRCL_URL, data=year_payload, timeout=30)
            r.raise_for_status()
            soup2 = BeautifulSoup(r.text, "lxml")
            vs2  = self._hidden(soup2, "__VIEWSTATE")
            ev2  = self._hidden(soup2, "__EVENTVALIDATION")
            vsg2 = self._hidden(soup2, "__VIEWSTATEGENERATOR")

            # Step 2: Select month
            month_payload = {
                "__VIEWSTATE":          vs2,
                "__VIEWSTATEGENERATOR": vsg2,
                "__EVENTVALIDATION":    ev2,
                "__EVENTTARGET":        "ctl00$cphMain$GridView1",
                "__EVENTARGUMENT":      f"Select${self.MONTH_NAMES.get(self.month,'June')}",
                "ctl00$cphMain$ddlYear":  str(self.year),
                "ctl00$cphMain$ddlMonth": self.MONTH_NAMES.get(self.month, "June"),
                "ctl00$cphMain$btnSearch": "Search",
            }

            r2 = self.session.post(self.FRCL_URL, data=month_payload, timeout=30)
            r2.raise_for_status()
            return BeautifulSoup(r2.text, "lxml")

        except Exception as exc:
            log.warning(f"FRCL year/month select: {exc}")
            return None

    def _parse_foreclosure_table(self, soup: BeautifulSoup) -> list:
        """Parse the foreclosure listing table."""
        records = []
        tables = soup.find_all("table")

        for tbl in tables:
            rows = tbl.find_all("tr")
            if len(rows) < 2:
                continue
            headers = [th.get_text(strip=True).lower() for th in rows[0].find_all(["th","td"])]
            if not any(k in " ".join(headers) for k in ("grantor","trustee","sale","file","doc","name")):
                continue

            log.info(f"FRCL: found table with {len(rows)-1} data rows, headers: {headers}")

            for tr in rows[1:]:
                tds = tr.find_all("td")
                if len(tds) < 2:
                    continue
                try:
                    # Extract link
                    link = ""
                    for td in tds:
                        a = td.find("a", href=True)
                        if a:
                            href = a["href"]
                            link = href if href.startswith("http") else f"{CLERK_BASE}/{href.lstrip('/')}"
                            break

                    def cell(idx):
                        return tds[idx].get_text(strip=True) if idx < len(tds) else ""

                    # Try to map columns by header name
                    def col(key):
                        for i, h in enumerate(headers):
                            if key in h and i < len(tds):
                                return tds[i].get_text(strip=True)
                        return ""

                    doc_num   = col("doc") or col("file") or col("id") or cell(0)
                    sale_date = parse_date(col("sale") or cell(1))
                    file_date = parse_date(col("file") or col("date") or cell(2))
                    grantor   = col("grantor") or col("name") or col("trustor") or cell(3)
                    trustee   = col("trustee") or col("grantee") or cell(4)
                    legal     = col("legal") or col("description") or col("property") or cell(5)
                    amount    = parse_amount(col("amount") or col("balance") or col("bid") or cell(6))

                    if not doc_num and not grantor:
                        continue

                    rec = blank_record("TRSALE", "foreclosure", "Trustee Sale")
                    rec.update({
                        "doc_num":   doc_num,
                        "doc_type":  "TRSALE",
                        "filed":     file_date or sale_date,
                        "cat":       "foreclosure",
                        "cat_label": "Foreclosure Sale",
                        "owner":     grantor,
                        "grantee":   trustee,
                        "amount":    amount,
                        "legal":     legal,
                        "clerk_url": link or f"{self.FRCL_URL}",
                        # Store sale date separately in legal if different
                    })
                    # Tag sale date into legal for reference
                    if sale_date and sale_date != file_date:
                        rec["legal"] = f"Sale Date: {sale_date} | {legal}".strip(" |")

                    records.append(rec)
                except Exception:
                    continue

        return records

    def run(self) -> list:
        """Full scrape: login → load page → select year/month → parse table."""
        log.info(f"=== Foreclosure Scraper: {self.MONTH_NAMES.get(self.month)} {self.year} ===")

        self._login()

        soup = self._load_page()
        if not soup:
            log.error("FRCL: could not load page")
            return []

        # Try Playwright-style __doPostBack selection via HTTP
        result_soup = self._select_year_month(soup)
        if not result_soup:
            log.warning("FRCL: year/month selection failed, trying to parse base page")
            result_soup = soup

        records = self._parse_foreclosure_table(result_soup)
        log.info(f"FRCL: {len(records)} foreclosure records for {self.MONTH_NAMES.get(self.month)} {self.year}")
        return records


async def scrape_foreclosures_playwright(year: int, month: int) -> list:
    """
    Playwright fallback for the foreclosure page.
    Clicks the year then month in the list UI.
    """
    if not HAS_PLAYWRIGHT:
        return []

    FRCL_URL = f"{CLERK_BASE}/applications/websearch/FRCL_R.aspx"
    month_name = {
        1:"January",2:"February",3:"March",4:"April",
        5:"May",6:"June",7:"July",8:"August",
        9:"September",10:"October",11:"November",12:"December",
    }.get(month, "June")

    records = []
    log.info(f"PW Foreclosure: {month_name} {year}")

    async with async_playwright() as pw:
        browser = await pw.chromium.launch(headless=True, args=["--no-sandbox","--disable-dev-shm-usage"])
        ctx  = await browser.new_context(user_agent=(
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
        ))
        page = await ctx.new_page()
        page.set_default_timeout(PW_TIMEOUT)

        # Login
        try:
            await page.goto(f"{CLERK_BASE}/applications/websearch/eLogin.aspx",
                            wait_until="domcontentloaded", timeout=PW_TIMEOUT)
            await asyncio.sleep(1)
            # Fill credentials
            for sel in ["input[id*='UserName']","input[id*='Email']","input[type='email']","input[type='text']"]:
                try:
                    el = await page.wait_for_selector(sel, timeout=3_000)
                    if el: await el.fill(CLERK_USERNAME); break
                except Exception: continue
            for sel in ["input[id*='Password']","input[type='password']"]:
                try:
                    el = await page.wait_for_selector(sel, timeout=3_000)
                    if el: await el.fill(CLERK_PASSWORD); break
                except Exception: continue
            for sel in ["input[value='LOG IN']","input[value='Log In']","input[type='submit']","button[type='submit']"]:
                try:
                    el = await page.wait_for_selector(sel, timeout=3_000)
                    if el: await el.click(); break
                except Exception: continue
            await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
            log.info("PW FRCL: login done")
        except Exception as exc:
            log.warning(f"PW FRCL login: {exc}")

        # Navigate to foreclosure page
        try:
            await page.goto(FRCL_URL, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
            await asyncio.sleep(1)
        except Exception as exc:
            log.warning(f"PW FRCL nav: {exc}")
            await browser.close()
            return []

        # Click the year
        try:
            year_el = await page.wait_for_selector(f"text={year}", timeout=5_000)
            if year_el:
                await year_el.click()
                await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                await asyncio.sleep(1)
        except Exception as exc:
            log.warning(f"PW FRCL year click: {exc}")

        # Click the month
        try:
            month_el = await page.wait_for_selector(f"text={month_name}", timeout=5_000)
            if month_el:
                await month_el.click()
                await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                await asyncio.sleep(1)
        except Exception as exc:
            log.warning(f"PW FRCL month click: {exc}")

        # Parse whatever is on the page now
        html = await page.content()
        soup = BeautifulSoup(html, "lxml")
        scraper = ForeclosureScraper(year, month)
        records = scraper._parse_foreclosure_table(soup)

        await browser.close()

    log.info(f"PW FRCL: {len(records)} records")
    return records


# ─────────────────────────────────────────────────────────────────────────────
# HCAD PARCEL DB
# ─────────────────────────────────────────────────────────────────────────────
class ParcelDB:

    def __init__(self):
        self.index: dict = {}

    def _find_url(self) -> Optional[str]:
        for page_url in HCAD_PAGES:
            try:
                r = requests.get(page_url, timeout=20)
                soup = BeautifulSoup(r.text, "lxml")
                for a in soup.find_all("a", href=True):
                    href = a["href"]
                    low  = href.lower()
                    if (".zip" in low or ".dbf" in low) and \
                            any(k in low for k in ("real_acct","building","parcel","owner")):
                        full = href if href.startswith("http") else f"https://pdata.hcad.org{href}"
                        log.info(f"HCAD data URL: {full}")
                        return full
            except Exception as exc:
                log.warning(f"HCAD page {page_url}: {exc}")
        return None

    def load(self):
        url = self._find_url()
        if not url:
            log.warning("HCAD bulk URL not found — no address enrichment")
            return

        log.info("Downloading HCAD parcel data…")
        raw = None
        for attempt in range(MAX_RETRIES):
            try:
                r = requests.get(url, timeout=180, stream=True)
                r.raise_for_status()
                raw = r.content
                log.info(f"Downloaded {len(raw)//1_048_576} MB")
                break
            except Exception as exc:
                log.warning(f"HCAD download attempt {attempt+1}: {exc}")
                time.sleep(RETRY_DELAY)

        if not raw:
            return

        rows = []
        try:
            zf = zipfile.ZipFile(io.BytesIO(raw))
            for name in zf.namelist():
                data = zf.read(name)
                low  = name.lower()
                if low.endswith(".dbf") and HAS_DBF:
                    rows.extend(self._read_dbf(data))
                elif low.endswith(".csv"):
                    rows.extend(self._read_csv(data))
        except zipfile.BadZipFile:
            if HAS_DBF and url.lower().endswith(".dbf"):
                rows = self._read_dbf(raw)
            else:
                rows = self._read_csv(raw)

        log.info(f"Indexing {len(rows):,} parcel rows…")
        for row in rows:
            p = self._norm(row)
            if p["owner"]:
                for v in name_variants(p["owner"]):
                    self.index.setdefault(v, p)
        log.info(f"Parcel index: {len(self.index):,} keys")

    def _read_dbf(self, data: bytes) -> list:
        import tempfile
        with tempfile.NamedTemporaryFile(suffix=".dbf", delete=False) as f:
            f.write(data)
            tmp = f.name
        try:
            return [dict(r) for r in DBF(tmp, encoding="latin-1", ignore_missing_memofile=True)]
        finally:
            os.unlink(tmp)

    def _read_csv(self, data: bytes) -> list:
        text = data.decode("latin-1", errors="replace")
        return list(csv.DictReader(io.StringIO(text)))

    def _norm(self, row: dict) -> dict:
        def g(*keys):
            for k in keys:
                for variant in (k, k.upper(), k.lower()):
                    v = row.get(variant)
                    if v and str(v).strip() not in ("", "None"):
                        return str(v).strip()
            return ""
        return {
            "owner":      g("OWNER","OWN1","OWNR","OWNER_NAME","OWNERNAME"),
            "site_addr":  g("SITE_ADDR","SITEADDR","SITE_ADDRESS","STR_ADDR"),
            "site_city":  g("SITE_CITY","SITECITY","SCITY"),
            "site_zip":   g("SITE_ZIP","SITEZIP","SZIP"),
            "mail_addr":  g("ADDR_1","MAILADR1","MAIL_ADDR","MAILINGADDRESS"),
            "mail_city":  g("CITY","MAILCITY","MAIL_CITY","MCITY"),
            "mail_state": g("STATE","MAILSTATE","MAIL_STATE","MSTATE"),
            "mail_zip":   g("ZIP","MAILZIP","MAIL_ZIP","MZIP"),
        }

    def lookup(self, owner: str) -> Optional[dict]:
        for v in name_variants(owner):
            if v in self.index:
                return self.index[v]
        return None

# ─────────────────────────────────────────────────────────────────────────────
# GHL CSV EXPORT
# ─────────────────────────────────────────────────────────────────────────────
def export_ghl_csv(records: list, path: str):
    cols = [
        "First Name","Last Name",
        "Mailing Address","Mailing City","Mailing State","Mailing Zip",
        "Property Address","Property City","Property State","Property Zip",
        "Lead Type","Document Type","Date Filed","Document Number",
        "Amount/Debt Owed","Seller Score","Motivated Seller Flags",
        "Source","Public Records URL",
    ]
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in records:
            parts = (r.get("owner","") or "").replace(","," ").split()
            w.writerow({
                "First Name":            parts[0] if parts else "",
                "Last Name":             " ".join(parts[1:]) if len(parts) > 1 else "",
                "Mailing Address":       r.get("mail_address",""),
                "Mailing City":          r.get("mail_city",""),
                "Mailing State":         r.get("mail_state",""),
                "Mailing Zip":           r.get("mail_zip",""),
                "Property Address":      r.get("prop_address",""),
                "Property City":         r.get("prop_city",""),
                "Property State":        r.get("prop_state",""),
                "Property Zip":          r.get("prop_zip",""),
                "Lead Type":             r.get("cat_label",""),
                "Document Type":         r.get("doc_type",""),
                "Date Filed":            r.get("filed",""),
                "Document Number":       r.get("doc_num",""),
                "Amount/Debt Owed":      r.get("amount","") or "",
                "Seller Score":          r.get("score",0),
                "Motivated Seller Flags":" | ".join(r.get("flags",[])),
                "Source":                "Harris County Clerk",
                "Public Records URL":    r.get("clerk_url",""),
            })
    log.info(f"GHL CSV → {path}")

# ─────────────────────────────────────────────────────────────────────────────
# MAIN
# ─────────────────────────────────────────────────────────────────────────────
async def main():
    end_dt   = datetime.now()
    start_dt = end_dt - timedelta(days=LOOK_BACK_DAYS)
    log.info(f"Date range: {start_dt.date()} → {end_dt.date()}")

    # Foreclosure month/year — default to NEXT month (upcoming sales)
    # Override with env vars FRCL_YEAR and FRCL_MONTH
    now = datetime.now()
    # Default: next month (foreclosure sales are posted ~1 month ahead)
    next_month_dt = (now.replace(day=1) + timedelta(days=32)).replace(day=1)
    frcl_year  = int(os.environ.get("FRCL_YEAR",  next_month_dt.year))
    frcl_month = int(os.environ.get("FRCL_MONTH", next_month_dt.month))
    log.info(f"Foreclosure target: {frcl_year}-{frcl_month:02d}")

    records: list = []

    # ── 1. Fast HTTP scrape (RP.aspx doc types) ───────────────────────────────
    log.info("=== Direct HTTP scrape (RP.aspx) ===")
    try:
        http = DirectHTTPScraper(start_dt, end_dt)
        records = http.run()
        log.info(f"HTTP total: {len(records)}")
    except Exception:
        log.error(traceback.format_exc())

    # ── 2. Playwright fallback for RP.aspx (only if HTTP got nothing) ─────────
    if not records and HAS_PLAYWRIGHT:
        log.info("=== Playwright fallback (RP.aspx) ===")
        try:
            pw = PlaywrightScraper(start_dt, end_dt)
            records = await pw.run()
            log.info(f"Playwright total: {len(records)}")
        except Exception:
            log.error(traceback.format_exc())

    # ── 3. Foreclosure page scrape (FRCL_R.aspx) — always runs ───────────────
    log.info("=== Foreclosure page scrape (FRCL_R.aspx) ===")
    frcl_records: list = []
    try:
        frcl = ForeclosureScraper(frcl_year, frcl_month)
        frcl_records = frcl.run()
    except Exception:
        log.error(traceback.format_exc())

    # Playwright fallback for foreclosures if HTTP got nothing
    if not frcl_records and HAS_PLAYWRIGHT:
        log.info("=== Playwright fallback (FRCL_R.aspx) ===")
        try:
            frcl_records = await scrape_foreclosures_playwright(frcl_year, frcl_month)
        except Exception:
            log.error(traceback.format_exc())

    log.info(f"Foreclosure records: {len(frcl_records)}")
    records.extend(frcl_records)

    # ── Dedup ─────────────────────────────────────────────────────────────────
    seen: set = set()
    unique: list = []
    for r in records:
        key = (r.get("doc_num","") or "").strip()
        if key and key not in seen:
            seen.add(key)
            unique.append(r)
        elif not key:
            # No doc num — dedup by owner+date
            key2 = f"{r.get('owner','')}-{r.get('filed','')}"
            if key2 not in seen:
                seen.add(key2)
                unique.append(r)
    records = unique
    log.info(f"Unique records: {len(records)}")

    # ── HCAD address enrichment ───────────────────────────────────────────────
    log.info("=== HCAD parcel lookup ===")
    parcel = ParcelDB()
    try:
        parcel.load()
    except Exception:
        log.error(traceback.format_exc())

    for r in records:
        try:
            if r.get("owner") and parcel.index:
                p = parcel.lookup(r["owner"])
                if p:
                    r["prop_address"] = p.get("site_addr","")
                    r["prop_city"]    = p.get("site_city","Houston") or "Houston"
                    r["prop_state"]   = "TX"
                    r["prop_zip"]     = p.get("site_zip","")
                    r["mail_address"] = p.get("mail_addr","")
                    r["mail_city"]    = p.get("mail_city","")
                    r["mail_state"]   = p.get("mail_state","TX") or "TX"
                    r["mail_zip"]     = p.get("mail_zip","")
        except Exception:
            continue

    # ── Score — with LP+FC portfolio combo bonus ──────────────────────────────
    lp_owners = {r["owner"] for r in records if r.get("cat") == "lis_pendens" and r.get("owner")}
    fc_owners = {r["owner"] for r in records if r.get("cat") == "foreclosure"  and r.get("owner")}
    combo     = lp_owners & fc_owners

    for r in records:
        try:
            sc, fl = score_record(r)
            if r.get("owner") in combo:
                sc = min(sc + 20, 100)
                if "Pre-foreclosure" not in fl:
                    fl.append("Pre-foreclosure")
            r["score"] = sc
            r["flags"] = fl
        except Exception:
            r["score"] = 30
            r["flags"] = []

    records.sort(key=lambda x: x.get("score", 0), reverse=True)
    with_address = sum(1 for r in records if r.get("prop_address"))

    # ── Save JSON ─────────────────────────────────────────────────────────────
    output = {
        "fetched_at":   datetime.utcnow().isoformat() + "Z",
        "source":       "Harris County Clerk - cclerk.hctx.net",
        "date_range":   {
            "start": start_dt.strftime("%Y-%m-%d"),
            "end":   end_dt.strftime("%Y-%m-%d"),
        },
        "foreclosure_month": f"{frcl_year}-{frcl_month:02d}",
        "total":        len(records),
        "with_address": with_address,
        "records":      records,
    }

    for path in ["dashboard/records.json", "data/records.json"]:
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(output, f, indent=2, default=str)
        log.info(f"Saved → {path}")

    today = datetime.now().strftime("%Y%m%d")
    export_ghl_csv(records, f"data/ghl_export_{today}.csv")

    log.info(f"✅ Done — {len(records)} total leads | {len(frcl_records)} foreclosures | {with_address} with address")


if __name__ == "__main__":
    asyncio.run(main())
