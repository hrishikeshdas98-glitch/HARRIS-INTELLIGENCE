#!/usr/bin/env python3
"""
Harris County Motivated Seller Lead Scraper  v5 — Production
- Single Playwright session: login once, scrape everything
- Correct URLs and field names confirmed from browser inspection
- Foreclosure page (FRCL_R.aspx) scraped separately
- HCAD parcel address enrichment
- GHL CSV export
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
    from playwright.async_api import async_playwright
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
CLERK_BASE  = "https://www.cclerk.hctx.net"
CLERK_LOGIN = f"{CLERK_BASE}/applications/websearch/eLogin.aspx"
CLERK_RP    = f"{CLERK_BASE}/applications/websearch/RP.aspx"
CLERK_FRCL  = f"{CLERK_BASE}/applications/websearch/FRCL_R.aspx"

CLERK_USERNAME = os.environ.get("CLERK_USERNAME", "")
CLERK_PASSWORD = os.environ.get("CLERK_PASSWORD", "")
LOOK_BACK_DAYS = int(os.environ.get("LOOK_BACK_DAYS", "7"))

MAX_RETRIES = 3
RETRY_DELAY = 2
PW_TIMEOUT  = 30_000
PW_ELEM     = 10_000

HCAD_PAGES = [
    "https://pdata.hcad.org/download/2025.html",
    "https://pdata.hcad.org/download/2024.html",
]

# Confirmed instrument codes from:
# https://www.cclerk.hctx.net/applications/websearch/Codes.aspx?DTI=1
DOC_TYPES = {
    "L/P":    ("Lis Pendens",           "lis_pendens"),
    "TRSALE": ("Trustee Sale",          "foreclosure"),
    "NOTICE": ("Notice of Foreclosure", "foreclosure"),
    "JUDGE":  ("Judgment",              "judgment"),
    "A/J":    ("Abstract of Judgment",  "judgment"),
    "T/L":    ("Federal Tax Lien",      "tax_lien"),
    "LIEN":   ("Lien",                  "lien"),
    "L AFFT": ("Lien Affidavit",        "lien"),
    "PROB":   ("Probate",               "probate"),
    "REL":    ("Release",               "release"),
    "DEED":   ("Deed",                  "deed"),
    "D/T":    ("Deed of Trust",         "deed_of_trust"),
    "BNKRCY": ("Bankruptcy",            "bankruptcy"),
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
}

MONTH_NAMES = {
    1:"January", 2:"February", 3:"March",    4:"April",
    5:"May",     6:"June",     7:"July",      8:"August",
    9:"September",10:"October",11:"November",12:"December",
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
def parse_amount(text) -> Optional[float]:
    if not text: return None
    cleaned = re.sub(r"[^\d.]", "", str(text).replace(",", ""))
    try:
        v = float(cleaned)
        return v if v > 0 else None
    except: return None

def parse_date(text) -> str:
    for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y", "%d/%m/%Y", "%m/%d/%y"):
        try: return datetime.strptime(text.strip(), fmt).strftime("%Y-%m-%d")
        except: continue
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

def blank_rec(doc_code, cat, label) -> dict:
    return {
        "doc_num": "", "doc_type": doc_code, "filed": "",
        "cat": cat, "cat_label": CAT_LABELS.get(cat, label),
        "owner": "", "grantee": "", "amount": None, "legal": "",
        "prop_address": "", "prop_city": "Houston",
        "prop_state": "TX", "prop_zip": "",
        "mail_address": "", "mail_city": "",
        "mail_state": "", "mail_zip": "",
        "clerk_url": "", "flags": [], "score": 0,
    }

def score_record(rec: dict) -> tuple:
    flags, score = [], 30
    cat = rec.get("cat", "")
    if cat == "lis_pendens":  flags.append("Lis pendens")
    if cat == "foreclosure":  flags.append("Pre-foreclosure")
    if cat == "judgment":     flags.append("Judgment lien")
    if cat == "tax_lien":     flags.append("Tax lien")
    if cat == "lien":         flags.append("Lien")
    if cat == "probate":      flags.append("Probate / estate")
    if cat == "bankruptcy":   flags.append("Bankruptcy")
    owner = rec.get("owner", "")
    if owner and re.search(r"\b(LLC|INC|CORP|LTD|LP|TRUST|ASSOC)\b", owner, re.I):
        flags.append("LLC / corp owner")
    try:
        if (datetime.now() - datetime.strptime(rec.get("filed",""), "%Y-%m-%d")).days <= 7:
            flags.append("New this week")
            score += 5
    except: pass
    score += 10 * len(flags)
    amt = rec.get("amount")
    if amt:
        score += 15 if amt > 100_000 else (10 if amt > 50_000 else 0)
    if rec.get("prop_address"):
        score += 5
    return min(score, 100), flags

def parse_results_table(html: str, doc_code: str, cat: str, label: str) -> list:
    """Parse results table from HTML page."""
    soup = BeautifulSoup(html, "lxml")
    records = []

    # Log ALL tables found for debugging
    all_tables = soup.find_all("table")
    log.info(f"  parse_results_table: found {len(all_tables)} tables on page")
    for i, tbl in enumerate(all_tables):
        ths = [th.get_text(strip=True) for th in tbl.find_all("th")]
        tds = tbl.find_all("tr")
        log.info(f"    Table {i}: {len(tds)} rows, headers={ths[:8]}")

    for tbl in all_tables:
        ths  = tbl.find_all("th")
        rows = tbl.find_all("tr")

        # Skip tables with fewer than 2 rows (no data)
        if len(rows) < 2:
            continue

        # Skip tiny tables (form labels etc)
        if len(rows) < 3 and not ths:
            continue

        hdrs = [th.get_text(strip=True).lower() for th in ths]
        joined = " ".join(hdrs)

        # Must look like a real results table with data columns
        # Reject form-label tables (File No, Grantor, Grantee as row labels)
        if any(k in joined for k in (
            "file no","file number","instrument","grantor","grantee",
            "filed","date filed","doc number","document number",
            "record date","book","volume"
        )):
            # Make sure it has actual data rows (td cells with real content)
            data_rows = []
            for tr in rows[1:]:
                tds = tr.find_all("td")
                # A real data row has multiple cells with actual text
                cells = [td.get_text(strip=True) for td in tds if td.get_text(strip=True)]
                if len(cells) >= 3:
                    data_rows.append((tds, cells))

            if not data_rows:
                continue

            log.info(f"  Results table matched — headers: {hdrs[:8]}, data rows: {len(data_rows)}")

            # Map header positions
            col = {}
            for i, h in enumerate(hdrs):
                if any(k in h for k in ("file","doc","number","instrument","record")): col.setdefault("doc_num", i)
                if any(k in h for k in ("date","filed","record date")):                col.setdefault("filed", i)
                if any(k in h for k in ("grantor","owner","name")):                    col.setdefault("owner", i)
                if any(k in h for k in ("grantee",)):                                  col.setdefault("grantee", i)
                if any(k in h for k in ("legal","desc","subdivision","property")):     col.setdefault("legal", i)
                if any(k in h for k in ("amount","consideration","price")):            col.setdefault("amount", i)

            for tds, cells in data_rows:
                try:
                    link = ""
                    for td in tds:
                        a = td.find("a", href=True)
                        if a:
                            href = a["href"]
                            link = href if href.startswith("http") else f"{CLERK_BASE}/{href.lstrip('/')}"
                            break

                    def cell(i): return tds[i].get_text(strip=True) if i < len(tds) else ""
                    def mapped(key, fallback_idx):
                        return cell(col[key]) if key in col else cell(fallback_idx)

                    rec = blank_rec(doc_code, cat, label)
                    rec.update({
                        "doc_num":   mapped("doc_num", 0),
                        "filed":     parse_date(mapped("filed", 1)),
                        "owner":     mapped("owner", 2),
                        "grantee":   mapped("grantee", 3),
                        "legal":     mapped("legal", 4),
                        "amount":    parse_amount(mapped("amount", 5)),
                        "clerk_url": link,
                    })
                    if rec["doc_num"] and rec["doc_num"] not in (
                        "File No:", "ID:", "Grantor:", "Grantee:",
                        "Desc:", "Sec:", "Lot:", "Block:", "Unit:"
                    ):
                        records.append(rec)
                except Exception:
                    continue

    return records

# ─────────────────────────────────────────────────────────────────────────────
# MAIN SCRAPER — single Playwright session
# ─────────────────────────────────────────────────────────────────────────────
class HarrisCountyScraper:

    def __init__(self, start, end, frcl_year, frcl_month):
        self.start      = start
        self.end        = end
        self.frcl_year  = frcl_year
        self.frcl_month = frcl_month
        self.records    = []

    async def run(self) -> list:
        async with async_playwright() as pw:
            browser = await pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage"]
            )
            ctx = await browser.new_context(
                user_agent=(
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/124.0.0.0 Safari/537.36"
                ),
                viewport={"width": 1280, "height": 900},
            )
            page = await ctx.new_page()

            # ── Step 1: Login ─────────────────────────────────────────────────
            logged_in = await self._login(page)
            if not logged_in:
                log.error("Login failed — cannot scrape")
                await browser.close()
                return []

            # ── Step 2: Scrape each doc type via RP.aspx ──────────────────────
            log.info("=== Scraping RP.aspx doc types ===")
            for doc_code, (label, cat) in DOC_TYPES.items():
                try:
                    recs = await self._search_rp(page, doc_code, label, cat)
                    self.records.extend(recs)
                    log.info(f"  {doc_code}: {len(recs)} records")
                except Exception:
                    log.error(f"  {doc_code}: {traceback.format_exc()}")

            # ── Step 3: Scrape foreclosure page ───────────────────────────────
            log.info("=== Scraping FRCL_R.aspx foreclosures ===")
            try:
                frcl = await self._scrape_frcl(page)
                self.records.extend(frcl)
                log.info(f"  Foreclosures {MONTH_NAMES[self.frcl_month]} {self.frcl_year}: {len(frcl)}")
            except Exception:
                log.error(f"  Foreclosure: {traceback.format_exc()}")

            await browser.close()
        return self.records

    # ── Login ─────────────────────────────────────────────────────────────────
    async def _login(self, page) -> bool:
        log.info(f"Logging in as {CLERK_USERNAME}…")

        # Try login URLs in order — eLogin.aspx may be under maintenance
        # while RP.aspx is available
        login_urls = [
            f"{CLERK_BASE}/Applications/WebSearch/Registration/Login.aspx",
            f"{CLERK_BASE}/applications/websearch/eLogin.aspx",
            CLERK_RP,  # RP.aspx is confirmed working — try logging in from here
        ]

        for attempt in range(MAX_RETRIES):
            for login_url in login_urls:
                try:
                    await page.goto(login_url, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
                    await asyncio.sleep(2)

                    content = await page.content()
                    lower   = content.lower()

                    # Skip if this URL is also under maintenance
                    if "currently unavailable" in lower or "maintenance" in lower:
                        log.warning(f"  {login_url} is under maintenance, trying next…")
                        continue

                    # Check if there's a login form on this page
                    has_password = await page.query_selector("input[type='password']")
                    has_login_link = await page.query_selector("a:has-text('Log In'), a:has-text('LOGIN')")

                    if has_password:
                        # We have a login form — fill it
                        log.info(f"  Login form found at {login_url}")

                        for sel in ["input[type='text']","input[type='email']",
                                    "input[name*='User']","input[id*='User']",
                                    "input[name*='Email']","input[id*='Email']"]:
                            try:
                                el = await page.query_selector(sel)
                                if el and await el.is_visible():
                                    await el.fill(CLERK_USERNAME)
                                    break
                            except: continue

                        await page.fill("input[type='password']", CLERK_PASSWORD)

                        for sel in ["input[type='submit']","button[type='submit']",
                                    "input[value*='LOG']","input[value*='Log']",
                                    "button:has-text('Log')"]:
                            try:
                                el = await page.query_selector(sel)
                                if el and await el.is_visible():
                                    await el.click()
                                    break
                            except: continue

                        await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                        await asyncio.sleep(2)

                        body = (await page.content()).lower()
                        url  = page.url.lower()

                        if "currently unavailable" in body or "maintenance" in body:
                            log.warning("  Maintenance page after login attempt")
                            continue

                        if any(k in body for k in ("log out","logout","sign out","my account","welcome")):
                            log.info("Login successful ✅")
                            return True

                        if "login" not in url and "registration" not in url:
                            log.info(f"  Login likely OK — now at {page.url}")
                            return True

                    elif has_login_link:
                        # Click the Log In link to get to the form
                        await has_login_link.click()
                        await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                        await asyncio.sleep(1)
                        # Retry this iteration with the new page
                        has_password2 = await page.query_selector("input[type='password']")
                        if has_password2:
                            for sel in ["input[type='text']","input[type='email']",
                                        "input[name*='User']","input[id*='User']"]:
                                try:
                                    el = await page.query_selector(sel)
                                    if el and await el.is_visible():
                                        await el.fill(CLERK_USERNAME)
                                        break
                                except: continue
                            await page.fill("input[type='password']", CLERK_PASSWORD)
                            for sel in ["input[type='submit']","button[type='submit']",
                                        "input[value*='LOG']","input[value*='Log']"]:
                                try:
                                    el = await page.query_selector(sel)
                                    if el and await el.is_visible():
                                        await el.click()
                                        break
                                except: continue
                            await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                            await asyncio.sleep(2)
                            body = (await page.content()).lower()
                            if any(k in body for k in ("log out","logout","my account")):
                                log.info("Login successful ✅")
                                return True
                            if "login" not in page.url.lower():
                                log.info(f"  Login likely OK — now at {page.url}")
                                return True
                    else:
                        # No login form and no login link —
                        # page may already be accessible without login
                        log.info(f"  No login form at {login_url} — may be public access")
                        return True

                except Exception as exc:
                    log.warning(f"  Login attempt {attempt+1} at {login_url}: {exc}")
                    continue

            log.warning(f"  All login URLs tried on attempt {attempt+1}, retrying…")
            await asyncio.sleep(RETRY_DELAY)

        log.error("All login attempts failed")
        return False

    # ── RP.aspx search ────────────────────────────────────────────────────────
    async def _search_rp(self, page, doc_code: str, label: str, cat: str) -> list:
        sd = self.start.strftime("%m/%d/%Y")
        ed = self.end.strftime("%m/%d/%Y")

        # Navigate to form
        try:
            await page.goto(CLERK_RP, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
            await asyncio.sleep(1)
        except Exception as exc:
            log.warning(f"  RP nav failed for {doc_code}: {exc}")
            return []

        # Check portal not down
        content = await page.content()
        if "currently unavailable" in content.lower() and "maintenance" in content.lower():
            log.warning("  Portal unavailable during search")
            return []

        # Fill instrument type — confirmed field name from payload inspection
        try:
            el = await page.query_selector("#ctl00_ContentPlaceHolder1_txtInstrument")
            if not el:
                el = await page.query_selector("input[name='ctl00$ContentPlaceHolder1$txtInstrument']")
            if el:
                await el.fill(doc_code)
            else:
                log.warning(f"  Instrument field not found for {doc_code}")
                return []
        except Exception as exc:
            log.warning(f"  Fill instrument failed: {exc}")
            return []

        # Fill dates — confirmed field names from payload
        try:
            from_el = await page.query_selector("#ctl00_ContentPlaceHolder1_txtFrom")
            to_el   = await page.query_selector("#ctl00_ContentPlaceHolder1_txtTo")
            if from_el: await from_el.fill(sd)
            if to_el:   await to_el.fill(ed)
        except Exception as exc:
            log.warning(f"  Fill dates failed: {exc}")

        # Click Search — confirmed button name from payload
        try:
            btn = await page.query_selector("#ctl00_ContentPlaceHolder1_btnSearch")
            if not btn:
                btn = await page.query_selector("input[value='Search']")
            if btn:
                await btn.click()
            else:
                log.warning(f"  Search button not found for {doc_code}")
                return []
        except Exception as exc:
            log.warning(f"  Search click failed: {exc}")
            return []

        # Wait for results
        try:
            await page.wait_for_url("**/RP_R.aspx**", timeout=PW_TIMEOUT)
        except Exception:
            try:
                await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
            except Exception:
                pass

        await asyncio.sleep(1)

        # Paginate
        all_records = []
        for page_num in range(1, 51):
            html = await page.content()
            rows = parse_results_table(html, doc_code, cat, label)
            all_records.extend(rows)

            # Check for next page link
            try:
                nxt = await page.query_selector(
                    "a:has-text('Next'), input[value='Next'], a[title*='Next']"
                )
                if nxt:
                    await nxt.click()
                    await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                    await asyncio.sleep(0.5)
                else:
                    break
            except Exception:
                break

        return all_records

    # ── FRCL_R.aspx foreclosure page ─────────────────────────────────────────
    async def _scrape_frcl(self, page) -> list:
        try:
            await page.goto(CLERK_FRCL, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
            await asyncio.sleep(2)
        except Exception as exc:
            log.warning(f"  FRCL nav failed: {exc}")
            return []

        content = await page.content()
        if "currently unavailable" in content.lower():
            log.warning("  Portal unavailable for FRCL")
            return []

        log.info(f"  FRCL page loaded: {page.url}")

        # Select year
        try:
            year_sel = await page.query_selector("select[id*='Year'], select[name*='Year']")
            if year_sel:
                await year_sel.select_option(str(self.frcl_year))
                await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                await asyncio.sleep(1)
            else:
                # Try clicking year link
                await page.click(f"text='{self.frcl_year}'", timeout=5_000)
                await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
        except Exception as exc:
            log.warning(f"  FRCL year select: {exc}")

        # Select month
        try:
            month_sel = await page.query_selector("select[id*='Month'], select[name*='Month']")
            if month_sel:
                # Try value as number first, then as name
                try:
                    await month_sel.select_option(str(self.frcl_month))
                except Exception:
                    await month_sel.select_option(label=MONTH_NAMES[self.frcl_month])
                await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                await asyncio.sleep(1)
            else:
                await page.click(f"text='{MONTH_NAMES[self.frcl_month]}'", timeout=5_000)
                await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
        except Exception as exc:
            log.warning(f"  FRCL month select: {exc}")

        # Submit if there's a button
        try:
            btn = await page.query_selector(
                "input[type='submit'], button[type='submit'], "
                "input[value*='Search'], input[value*='View']"
            )
            if btn:
                await btn.click()
                await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
        except Exception:
            pass

        await asyncio.sleep(1)
        html = await page.content()
        return self._parse_frcl(html)

    def _parse_frcl(self, html: str) -> list:
        soup = BeautifulSoup(html, "lxml")
        records = []
        for tbl in soup.find_all("table"):
            rows = tbl.find_all("tr")
            if len(rows) < 2:
                continue
            hdrs = [td.get_text(strip=True).lower() for td in rows[0].find_all(["th","td"])]
            if not any(k in " ".join(hdrs) for k in ("grantor","sale","trustee","file","name","date","doc")):
                continue
            log.info(f"  FRCL table: headers={hdrs}")
            for tr in rows[1:]:
                tds = tr.find_all("td")
                if not tds: continue
                try:
                    link = ""
                    for td in tds:
                        a = td.find("a", href=True)
                        if a:
                            href = a["href"]
                            link = href if href.startswith("http") else f"{CLERK_BASE}/{href.lstrip('/')}"
                            break
                    def cell(i): return tds[i].get_text(strip=True) if i < len(tds) else ""
                    rec = blank_rec("TRSALE", "foreclosure", "Trustee Sale / Foreclosure")
                    rec.update({
                        "doc_num":   cell(0),
                        "filed":     parse_date(cell(1)),
                        "owner":     cell(2),
                        "grantee":   cell(3),
                        "legal":     cell(4),
                        "amount":    parse_amount(cell(5)),
                        "clerk_url": link or CLERK_FRCL,
                        "cat_label": "Foreclosure Sale",
                    })
                    if any([rec["doc_num"], rec["owner"]]):
                        records.append(rec)
                except: continue
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
                        log.info(f"HCAD URL: {full}")
                        return full
            except Exception as exc:
                log.warning(f"HCAD page {page_url}: {exc}")
        return None

    def load(self):
        url = self._find_url()
        if not url:
            log.warning("HCAD URL not found — no address enrichment")
            return
        log.info("Downloading HCAD parcel data…")
        raw = None
        for i in range(MAX_RETRIES):
            try:
                r = requests.get(url, timeout=180, stream=True)
                r.raise_for_status()
                raw = r.content
                log.info(f"Downloaded {len(raw)//1_048_576} MB")
                break
            except Exception as exc:
                log.warning(f"HCAD attempt {i+1}: {exc}")
                time.sleep(RETRY_DELAY)
        if not raw:
            return
        rows = []
        try:
            zf = zipfile.ZipFile(io.BytesIO(raw))
            for name in zf.namelist():
                data = zf.read(name)
                if name.lower().endswith(".dbf") and HAS_DBF:
                    rows.extend(self._read_dbf(data))
                elif name.lower().endswith(".csv"):
                    rows.extend(self._read_csv(data))
        except zipfile.BadZipFile:
            rows = self._read_dbf(raw) if HAS_DBF else self._read_csv(raw)
        log.info(f"Indexing {len(rows):,} rows…")
        for row in rows:
            p = self._norm(row)
            if p["owner"]:
                for v in name_variants(p["owner"]):
                    self.index.setdefault(v, p)
        log.info(f"Parcel index: {len(self.index):,} keys")

    def _read_dbf(self, data: bytes) -> list:
        import tempfile
        with tempfile.NamedTemporaryFile(suffix=".dbf", delete=False) as f:
            f.write(data); tmp = f.name
        try:
            return [dict(r) for r in DBF(tmp, encoding="latin-1", ignore_missing_memofile=True)]
        finally:
            os.unlink(tmp)

    def _read_csv(self, data: bytes) -> list:
        return list(csv.DictReader(io.StringIO(data.decode("latin-1", errors="replace"))))

    def _norm(self, row: dict) -> dict:
        def g(*keys):
            for k in keys:
                for v in (k, k.upper(), k.lower()):
                    val = row.get(v)
                    if val and str(val).strip() not in ("","None"):
                        return str(val).strip()
            return ""
        return {
            "owner":      g("OWNER","OWN1","OWNR","OWNER_NAME"),
            "site_addr":  g("SITE_ADDR","SITEADDR","SITE_ADDRESS"),
            "site_city":  g("SITE_CITY","SITECITY"),
            "site_zip":   g("SITE_ZIP","SITEZIP"),
            "mail_addr":  g("ADDR_1","MAILADR1","MAIL_ADDR"),
            "mail_city":  g("CITY","MAILCITY","MAIL_CITY"),
            "mail_state": g("STATE","MAILSTATE","MAIL_STATE"),
            "mail_zip":   g("ZIP","MAILZIP","MAIL_ZIP"),
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
                "Last Name":             " ".join(parts[1:]) if len(parts)>1 else "",
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

    # Foreclosure target — default next month (sales posted ~1 month ahead)
    next_month = (datetime.now().replace(day=1) + timedelta(days=32)).replace(day=1)
    frcl_year  = int(os.environ.get("FRCL_YEAR","")  or next_month.year)
    frcl_month = int(os.environ.get("FRCL_MONTH","") or next_month.month)
    log.info(f"Foreclosure target: {MONTH_NAMES[frcl_month]} {frcl_year}")

    if not HAS_PLAYWRIGHT:
        log.error("Playwright not installed!")
        return

    # ── Scrape ────────────────────────────────────────────────────────────────
    records: list = []
    try:
        scraper = HarrisCountyScraper(start_dt, end_dt, frcl_year, frcl_month)
        records = await scraper.run()
        log.info(f"Total raw records: {len(records)}")
    except Exception:
        log.error(traceback.format_exc())

    # ── Dedup ─────────────────────────────────────────────────────────────────
    seen, unique = set(), []
    for r in records:
        key = (r.get("doc_num","") or f"{r.get('owner','')}-{r.get('filed','')}").strip()
        if key and key not in seen:
            seen.add(key)
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
        except: continue

    # ── Score with LP+FC combo bonus ──────────────────────────────────────────
    lp_owners = {r["owner"] for r in records if r.get("cat")=="lis_pendens" and r.get("owner")}
    fc_owners = {r["owner"] for r in records if r.get("cat")=="foreclosure"  and r.get("owner")}
    combo     = lp_owners & fc_owners

    for r in records:
        try:
            sc, fl = score_record(r)
            if r.get("owner") in combo:
                sc = min(sc+20, 100)
                if "Pre-foreclosure" not in fl:
                    fl.append("Pre-foreclosure")
            r["score"], r["flags"] = sc, fl
        except:
            r["score"], r["flags"] = 30, []

    records.sort(key=lambda x: x.get("score",0), reverse=True)
    with_address = sum(1 for r in records if r.get("prop_address"))
    frcl_count   = sum(1 for r in records if r.get("cat")=="foreclosure")

    # ── Save JSON ─────────────────────────────────────────────────────────────
    output = {
        "fetched_at":        datetime.utcnow().isoformat() + "Z",
        "source":            "Harris County Clerk - cclerk.hctx.net",
        "date_range":        {
            "start": start_dt.strftime("%Y-%m-%d"),
            "end":   end_dt.strftime("%Y-%m-%d"),
        },
        "foreclosure_month": f"{frcl_year}-{frcl_month:02d}",
        "total":             len(records),
        "with_address":      with_address,
        "records":           records,
    }

    for path in ["dashboard/records.json", "data/records.json"]:
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(output, f, indent=2, default=str)
        log.info(f"Saved → {path}")

    today = datetime.now().strftime("%Y%m%d")
    export_ghl_csv(records, f"data/ghl_export_{today}.csv")

    log.info(
        f"✅ Done — {len(records)} total leads | "
        f"{frcl_count} foreclosures | "
        f"{with_address} with address"
    )

if __name__ == "__main__":
    asyncio.run(main())
