#!/usr/bin/env python3
"""
Harris County Motivated Seller Lead Scraper  v6 — Production
- Fixes owner/grantor column parsing (no more merged cells)
- FRCL scraper uses __doPostBack year+month selection
- Shows auction month, sale date, file date for foreclosures
- Scrapes all months from June 2026 onwards
- Single Playwright session
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

# Confirmed instrument codes
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
    return ""

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
        "sale_date": "",  # auction date for foreclosures
        "auction_month": "",  # e.g. "June 2026"
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
            flags.append("New this week"); score += 5
    except: pass
    score += 10 * len(flags)
    amt = rec.get("amount")
    if amt: score += 15 if amt > 100_000 else (10 if amt > 50_000 else 0)
    if rec.get("prop_address"): score += 5
    return min(score, 100), flags

def parse_rp_table(html: str, doc_code: str, cat: str, label: str) -> list:
    """
    Parse RP_R.aspx results table.
    The table has columns: File No | Date | Grantor | Grantee | Legal Desc | ...
    Each column is a separate <td> — we must NOT merge them.
    """
    soup = BeautifulSoup(html, "lxml")
    records = []

    for tbl in soup.find_all("table"):
        rows = tbl.find_all("tr")
        if len(rows) < 2: continue

        # Get headers from th or first tr
        header_row = rows[0]
        ths = header_row.find_all(["th","td"])
        hdrs = [th.get_text(strip=True) for th in ths]
        hdrs_lower = [h.lower() for h in hdrs]
        joined = " ".join(hdrs_lower)

        # Must be a results table
        if not any(k in joined for k in (
            "file no","file number","grantor","instrument",
            "record","document","filed","date"
        )):
            continue

        # Skip if it looks like the search form (has inputs inside)
        if tbl.find("input") or tbl.find("select"):
            continue

        log.info(f"  RP table: {len(rows)-1} data rows, headers={hdrs}")

        # Map column indices
        col_map = {}
        for i, h in enumerate(hdrs_lower):
            if any(k in h for k in ("file no","file number","rp-","doc","instrument","record no")):
                col_map.setdefault("doc_num", i)
            if any(k in h for k in ("date","filed","recorded")):
                col_map.setdefault("filed", i)
            if "grantor" in h:
                col_map["owner"] = i
            if "grantee" in h:
                col_map["grantee"] = i
            if any(k in h for k in ("legal","desc","subdivision","property")):
                col_map.setdefault("legal", i)
            if any(k in h for k in ("amount","consideration")):
                col_map.setdefault("amount", i)

        for tr in rows[1:]:
            tds = tr.find_all("td")
            if len(tds) < 2: continue
            try:
                link = ""
                for td in tds:
                    a = td.find("a", href=True)
                    if a:
                        href = a["href"]
                        link = href if href.startswith("http") else f"{CLERK_BASE}/{href.lstrip('/')}"
                        break

                def cell(i): return tds[i].get_text(strip=True) if i < len(tds) else ""
                def mcell(key, fallback):
                    return cell(col_map[key]) if key in col_map else cell(fallback)

                doc_num = mcell("doc_num", 0)
                # Skip header-like rows
                if not doc_num or doc_num in hdrs or "file no" in doc_num.lower():
                    continue

                rec = blank_rec(doc_code, cat, label)
                rec.update({
                    "doc_num":   doc_num,
                    "filed":     parse_date(mcell("filed", 1)),
                    "owner":     mcell("owner", 2),
                    "grantee":   mcell("grantee", 3),
                    "legal":     mcell("legal", 4),
                    "amount":    parse_amount(mcell("amount", 5)),
                    "clerk_url": link,
                })
                records.append(rec)
            except: continue

    return records

# ─────────────────────────────────────────────────────────────────────────────
# MAIN SCRAPER
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

            # Login
            logged_in = await self._login(page)
            if not logged_in:
                log.error("Login failed")
                await browser.close()
                return []

            # RP.aspx doc types
            log.info("=== Scraping RP.aspx ===")
            for doc_code, (label, cat) in DOC_TYPES.items():
                try:
                    recs = await self._search_rp(page, doc_code, label, cat)
                    self.records.extend(recs)
                    log.info(f"  {doc_code}: {len(recs)}")
                except Exception:
                    log.error(f"  {doc_code}: {traceback.format_exc()}")

            # FRCL foreclosure page — scrape from frcl_month onwards
            log.info("=== Scraping FRCL_R.aspx foreclosures ===")
            try:
                frcl_recs = await self._scrape_all_frcl_months(page)
                self.records.extend(frcl_recs)
                log.info(f"  Total foreclosure records: {len(frcl_recs)}")
            except Exception:
                log.error(f"  FRCL: {traceback.format_exc()}")

            await browser.close()
        return self.records

    # ── Login ─────────────────────────────────────────────────────────────────
    async def _login(self, page) -> bool:
        log.info(f"Logging in as {CLERK_USERNAME}…")
        login_urls = [
            f"{CLERK_BASE}/Applications/WebSearch/Registration/Login.aspx",
            CLERK_LOGIN,
            CLERK_RP,
        ]
        for attempt in range(MAX_RETRIES):
            for login_url in login_urls:
                try:
                    await page.goto(login_url, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
                    await asyncio.sleep(2)
                    content = (await page.content()).lower()

                    if "currently unavailable" in content or "maintenance" in content:
                        log.warning(f"  {login_url} unavailable")
                        continue

                    has_pw = await page.query_selector("input[type='password']")
                    has_login = await page.query_selector("a:has-text('Log In'), a:has-text('LOGIN')")

                    if has_pw:
                        for sel in ["input[type='text']","input[type='email']",
                                    "input[name*='User']","input[id*='User']"]:
                            try:
                                el = await page.query_selector(sel)
                                if el and await el.is_visible():
                                    await el.fill(CLERK_USERNAME); break
                            except: continue
                        await page.fill("input[type='password']", CLERK_PASSWORD)
                        for sel in ["input[type='submit']","button[type='submit']",
                                    "input[value*='LOG']","input[value*='Log']"]:
                            try:
                                el = await page.query_selector(sel)
                                if el and await el.is_visible():
                                    await el.click(); break
                            except: continue
                        await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                        await asyncio.sleep(2)
                        body = (await page.content()).lower()
                        if any(k in body for k in ("log out","logout","my account","welcome")):
                            log.info("Login successful ✅"); return True
                        if "login" not in page.url.lower() and "registration" not in page.url.lower():
                            log.info(f"  Login OK → {page.url}"); return True
                    elif has_login:
                        await has_login.click()
                        await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                        await asyncio.sleep(1)
                        has_pw2 = await page.query_selector("input[type='password']")
                        if has_pw2:
                            for sel in ["input[type='text']","input[type='email']",
                                        "input[name*='User']","input[id*='User']"]:
                                try:
                                    el = await page.query_selector(sel)
                                    if el and await el.is_visible():
                                        await el.fill(CLERK_USERNAME); break
                                except: continue
                            await page.fill("input[type='password']", CLERK_PASSWORD)
                            for sel in ["input[type='submit']","button[type='submit']",
                                        "input[value*='LOG']","input[value*='Log']"]:
                                try:
                                    el = await page.query_selector(sel)
                                    if el and await el.is_visible():
                                        await el.click(); break
                                except: continue
                            await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                            await asyncio.sleep(2)
                            body = (await page.content()).lower()
                            if any(k in body for k in ("log out","logout","my account")):
                                log.info("Login successful ✅"); return True
                            if "login" not in page.url.lower():
                                log.info(f"  Login OK → {page.url}"); return True
                    else:
                        log.info(f"  No login form at {login_url} — assuming public")
                        return True
                except Exception as exc:
                    log.warning(f"  Login {login_url}: {exc}")
            await asyncio.sleep(RETRY_DELAY)
        log.error("All login attempts failed"); return False

    # ── RP.aspx search ────────────────────────────────────────────────────────
    async def _search_rp(self, page, doc_code, label, cat) -> list:
        sd = self.start.strftime("%m/%d/%Y")
        ed = self.end.strftime("%m/%d/%Y")
        try:
            await page.goto(CLERK_RP, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
            await asyncio.sleep(1)
        except Exception as exc:
            log.warning(f"  RP nav {doc_code}: {exc}"); return []

        content = await page.content()
        if "currently unavailable" in content.lower() and "maintenance" in content.lower():
            return []

        try:
            el = await page.query_selector("#ctl00_ContentPlaceHolder1_txtInstrument")
            if el: await el.fill(doc_code)
            else: return []
            from_el = await page.query_selector("#ctl00_ContentPlaceHolder1_txtFrom")
            to_el   = await page.query_selector("#ctl00_ContentPlaceHolder1_txtTo")
            if from_el: await from_el.fill(sd)
            if to_el:   await to_el.fill(ed)
            btn = await page.query_selector("#ctl00_ContentPlaceHolder1_btnSearch")
            if btn: await btn.click()
            else: return []
        except Exception as exc:
            log.warning(f"  RP form {doc_code}: {exc}"); return []

        try:
            await page.wait_for_url("**/RP_R.aspx**", timeout=PW_TIMEOUT)
        except:
            try: await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
            except: pass
        await asyncio.sleep(1)

        all_records = []
        for _ in range(50):
            html = await page.content()
            rows = parse_rp_table(html, doc_code, cat, label)
            all_records.extend(rows)
            try:
                nxt = await page.query_selector("a:has-text('Next'), input[value='Next']")
                if nxt:
                    await nxt.click()
                    await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                    await asyncio.sleep(0.5)
                else: break
            except: break
        return all_records

    # ── FRCL scraper — all months from frcl_month onwards ────────────────────
    async def _scrape_all_frcl_months(self, page) -> list:
        """
        Scrape FRCL_R.aspx for the target month AND all future months available.
        The page uses __doPostBack links for year and month selection.
        """
        all_records = []

        try:
            await page.goto(CLERK_FRCL, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
            await asyncio.sleep(2)
        except Exception as exc:
            log.warning(f"  FRCL nav: {exc}"); return []

        log.info(f"  FRCL page loaded: {page.url}")

        # Get available months for our target year
        # The page shows year links on left, month links on right
        # First select the year
        year_str = str(self.frcl_year)
        try:
            year_link = await page.query_selector(f"a:has-text('{year_str}')")
            if year_link:
                await year_link.click()
                await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                await asyncio.sleep(1)
                log.info(f"  Selected year {year_str}")
            else:
                log.warning(f"  Year {year_str} link not found")
        except Exception as exc:
            log.warning(f"  Year select: {exc}")

        # Get all month links available on the page
        html = await page.content()
        soup = BeautifulSoup(html, "lxml")

        # Find all month links — they appear as text like "June", "July" etc
        available_months = []
        for month_num, month_name in MONTH_NAMES.items():
            # Look for this month as a clickable link
            link = soup.find("a", string=re.compile(f"^{month_name}$", re.I))
            if link and month_num >= self.frcl_month:
                available_months.append((month_num, month_name))

        log.info(f"  Available months from {MONTH_NAMES[self.frcl_month]}: {[m[1] for m in available_months]}")

        if not available_months:
            # Try clicking the target month directly
            available_months = [(self.frcl_month, MONTH_NAMES[self.frcl_month])]

        # Scrape each month
        for month_num, month_name in available_months:
            log.info(f"  Scraping FRCL: {month_name} {self.frcl_year}…")
            month_recs = await self._scrape_frcl_month(page, month_name, month_num)
            log.info(f"    {month_name} {self.frcl_year}: {len(month_recs)} records")
            all_records.extend(month_recs)

        return all_records

    async def _scrape_frcl_month(self, page, month_name: str, month_num: int) -> list:
        """Select a month on FRCL page and parse all records."""
        # Make sure we're on the FRCL page with the right year selected
        try:
            # Click the month link
            month_link = await page.query_selector(f"a:has-text('{month_name}')")
            if month_link:
                await month_link.click()
                await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                await asyncio.sleep(1.5)
            else:
                log.warning(f"  Month link '{month_name}' not found")
                return []
        except Exception as exc:
            log.warning(f"  Month click {month_name}: {exc}"); return []

        html = await page.content()
        records = self._parse_frcl_table(html, month_name, month_num)
        return records

    def _parse_frcl_table(self, html: str, month_name: str, month_num: int) -> list:
        """
        Parse FRCL results table.
        Columns: Document ID | Sale Date | File Date
        Each row also has a link to the document detail page which has the address.
        """
        soup = BeautifulSoup(html, "lxml")
        records = []
        auction_month = f"{month_name} {self.frcl_year}"

        for tbl in soup.find_all("table"):
            rows = tbl.find_all("tr")
            if len(rows) < 2: continue

            # Get headers
            header_cells = rows[0].find_all(["th","td"])
            hdrs = [c.get_text(strip=True).lower() for c in header_cells]
            joined = " ".join(hdrs)

            # FRCL table has "sale date" and "file date" headers
            if not any(k in joined for k in ("sale","file","document","id","date")):
                continue
            if tbl.find("input") or tbl.find("select"):
                continue

            log.info(f"  FRCL table: {len(rows)-1} rows, headers={hdrs}")

            # Map columns
            col_map = {}
            for i, h in enumerate(hdrs):
                if any(k in h for k in ("document","doc","id","file no","rp-")):
                    col_map.setdefault("doc_num", i)
                if "sale" in h and "date" in h:
                    col_map["sale_date"] = i
                if "file" in h and "date" in h:
                    col_map["file_date"] = i
                if "grantor" in h or "owner" in h or "name" in h:
                    col_map.setdefault("owner", i)
                if "address" in h or "property" in h:
                    col_map.setdefault("address", i)
                if "amount" in h or "balance" in h:
                    col_map.setdefault("amount", i)

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
                    def mcell(key, fallback):
                        return cell(col_map[key]) if key in col_map else cell(fallback)

                    doc_num   = mcell("doc_num", 0)
                    sale_date = parse_date(mcell("sale_date", 1))
                    file_date = parse_date(mcell("file_date", 2))
                    owner     = mcell("owner", 3)
                    address   = mcell("address", 4)
                    amount    = parse_amount(mcell("amount", 5))

                    if not doc_num: continue

                    rec = blank_rec("FRCL", "foreclosure", "Foreclosure Sale")
                    rec.update({
                        "doc_num":       doc_num,
                        "doc_type":      "FRCL",
                        "filed":         file_date or sale_date,
                        "sale_date":     sale_date,
                        "auction_month": auction_month,
                        "cat_label":     f"Foreclosure — {auction_month}",
                        "owner":         owner,
                        "prop_address":  address,
                        "prop_city":     "Houston",
                        "prop_state":    "TX",
                        "amount":        amount,
                        "clerk_url":     link or CLERK_FRCL,
                    })
                    records.append(rec)
                except: continue

        return records

# ─────────────────────────────────────────────────────────────────────────────
# HCAD PARCEL DB
# ─────────────────────────────────────────────────────────────────────────────
class ParcelDB:
    def __init__(self): self.index: dict = {}

    def _find_url(self):
        for page_url in HCAD_PAGES:
            try:
                r = requests.get(page_url, timeout=20)
                soup = BeautifulSoup(r.text, "lxml")
                for a in soup.find_all("a", href=True):
                    href = a["href"]; low = href.lower()
                    if (".zip" in low or ".dbf" in low) and \
                            any(k in low for k in ("real_acct","building","parcel","owner")):
                        full = href if href.startswith("http") else f"https://pdata.hcad.org{href}"
                        log.info(f"HCAD URL: {full}"); return full
            except Exception as e: log.warning(f"HCAD {page_url}: {e}")
        return None

    def load(self):
        url = self._find_url()
        if not url: log.warning("HCAD URL not found"); return
        log.info("Downloading HCAD parcel data…")
        raw = None
        for i in range(MAX_RETRIES):
            try:
                r = requests.get(url, timeout=180, stream=True)
                r.raise_for_status(); raw = r.content
                log.info(f"Downloaded {len(raw)//1_048_576}MB"); break
            except Exception as e: log.warning(f"HCAD {i+1}: {e}"); time.sleep(RETRY_DELAY)
        if not raw: return
        rows = []
        try:
            zf = zipfile.ZipFile(io.BytesIO(raw))
            for name in zf.namelist():
                data = zf.read(name)
                if name.lower().endswith(".dbf") and HAS_DBF: rows.extend(self._read_dbf(data))
                elif name.lower().endswith(".csv"): rows.extend(self._read_csv(data))
        except zipfile.BadZipFile:
            rows = self._read_dbf(raw) if HAS_DBF else self._read_csv(raw)
        log.info(f"Indexing {len(rows):,} rows…")
        for row in rows:
            p = self._norm(row)
            if p["owner"]:
                for v in name_variants(p["owner"]): self.index.setdefault(v, p)
        log.info(f"Parcel index: {len(self.index):,} keys")

    def _read_dbf(self, data):
        import tempfile
        with tempfile.NamedTemporaryFile(suffix=".dbf", delete=False) as f:
            f.write(data); tmp = f.name
        try: return [dict(r) for r in DBF(tmp, encoding="latin-1", ignore_missing_memofile=True)]
        finally: os.unlink(tmp)

    def _read_csv(self, data):
        return list(csv.DictReader(io.StringIO(data.decode("latin-1", errors="replace"))))

    def _norm(self, row):
        def g(*keys):
            for k in keys:
                for v in (k, k.upper(), k.lower()):
                    val = row.get(v)
                    if val and str(val).strip() not in ("","None"): return str(val).strip()
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

    def lookup(self, owner):
        for v in name_variants(owner):
            if v in self.index: return self.index[v]
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
        "Sale Date","Auction Month",
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
                "Sale Date":             r.get("sale_date",""),
                "Auction Month":         r.get("auction_month",""),
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

    next_month = (datetime.now().replace(day=1) + timedelta(days=32)).replace(day=1)
    frcl_year  = int(os.environ.get("FRCL_YEAR","")  or next_month.year)
    frcl_month = int(os.environ.get("FRCL_MONTH","") or next_month.month)
    log.info(f"Foreclosure target: {MONTH_NAMES[frcl_month]} {frcl_year} onwards")

    if not HAS_PLAYWRIGHT:
        log.error("Playwright not installed!"); return

    records: list = []
    try:
        scraper = HarrisCountyScraper(start_dt, end_dt, frcl_year, frcl_month)
        records = await scraper.run()
        log.info(f"Total raw: {len(records)}")
    except Exception:
        log.error(traceback.format_exc())

    # Dedup
    seen, unique = set(), []
    for r in records:
        key = (r.get("doc_num","") or f"{r.get('owner','')}-{r.get('filed','')}").strip()
        if key and key not in seen:
            seen.add(key); unique.append(r)
    records = unique
    log.info(f"Unique: {len(records)}")

    # HCAD address enrichment
    log.info("=== HCAD parcel lookup ===")
    parcel = ParcelDB()
    try: parcel.load()
    except Exception: log.error(traceback.format_exc())

    for r in records:
        try:
            if r.get("owner") and parcel.index:
                p = parcel.lookup(r["owner"])
                if p:
                    if not r.get("prop_address"):
                        r["prop_address"] = p.get("site_addr","")
                    r["prop_city"]    = p.get("site_city","Houston") or "Houston"
                    r["prop_state"]   = "TX"
                    r["prop_zip"]     = p.get("site_zip","")
                    r["mail_address"] = p.get("mail_addr","")
                    r["mail_city"]    = p.get("mail_city","")
                    r["mail_state"]   = p.get("mail_state","TX") or "TX"
                    r["mail_zip"]     = p.get("mail_zip","")
        except: continue

    # Score
    lp_owners = {r["owner"] for r in records if r.get("cat")=="lis_pendens" and r.get("owner")}
    fc_owners = {r["owner"] for r in records if r.get("cat")=="foreclosure"  and r.get("owner")}
    combo     = lp_owners & fc_owners

    for r in records:
        try:
            sc, fl = score_record(r)
            if r.get("owner") in combo:
                sc = min(sc+20, 100)
                if "Pre-foreclosure" not in fl: fl.append("Pre-foreclosure")
            r["score"], r["flags"] = sc, fl
        except: r["score"], r["flags"] = 30, []

    records.sort(key=lambda x: x.get("score",0), reverse=True)
    with_address = sum(1 for r in records if r.get("prop_address"))
    frcl_count   = sum(1 for r in records if r.get("cat")=="foreclosure")

    output = {
        "fetched_at":        datetime.utcnow().isoformat() + "Z",
        "source":            "Harris County Clerk - cclerk.hctx.net",
        "date_range":        {"start": start_dt.strftime("%Y-%m-%d"), "end": end_dt.strftime("%Y-%m-%d")},
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
    log.info(f"✅ Done — {len(records)} total | {frcl_count} foreclosures | {with_address} with address")

if __name__ == "__main__":
    asyncio.run(main())
