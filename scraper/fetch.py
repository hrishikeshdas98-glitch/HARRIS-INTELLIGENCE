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
    Confirmed columns from screenshot:
    [icon] | File Number | File Date | Type/Vol/Page | Names (Grantor+Grantee) | Legal Description | Pgs | Film Code
    Names cell format: "Grantor:NAME\nGrantee:NAME"
    Pagination uses BACK/NEXT buttons.
    """
    soup = BeautifulSoup(html, "lxml")
    records = []

    for tbl in soup.find_all("table"):
        rows = tbl.find_all("tr")
        if len(rows) < 2: continue
        if tbl.find("input", {"type": "text"}) or tbl.find("select"): continue
        if tbl.find("input", {"type": "password"}): continue

        hdrs = [c.get_text(strip=True) for c in rows[0].find_all(["th","td"])]
        hdrs_lower = [h.lower() for h in hdrs]
        joined = " ".join(hdrs_lower)

        # Identify results table
        is_results = (
            "file number" in joined or
            "file date" in joined or
            ("names" in joined and "legal" in joined) or
            any(re.search(r"rp-\d{4}-\d+", r.get_text(), re.I) for r in rows[1:3])
        )
        if not is_results: continue

        log.info(f"  RP table: {len(rows)-1} rows | headers={hdrs}")

        # Map column positions
        col_map = {}
        for i, h in enumerate(hdrs_lower):
            if "file number" in h or "file no" in h: col_map["doc_num"] = i
            if "file date" in h:                      col_map["filed"] = i
            if "type" in h and "vol" in h:            col_map["type_col"] = i
            if "name" in h:                           col_map["names"] = i
            if "legal" in h or "desc" in h:          col_map["legal"] = i

        for tr in rows[1:]:
            tds = tr.find_all("td")
            if len(tds) < 3: continue
            try:
                # Get link
                link = ""
                for td in tds:
                    a = td.find("a", href=True)
                    if a:
                        href = a["href"]
                        link = href if href.startswith("http") else f"{CLERK_BASE}/{href.lstrip('/')}"
                        break

                def cell(i): return tds[i].get_text(strip=True) if i < len(tds) else ""

                # Doc number — find RP-YYYY-NNNNN
                doc_num = ""
                if "doc_num" in col_map:
                    doc_num = cell(col_map["doc_num"])
                if not doc_num:
                    for td in tds:
                        txt = td.get_text(strip=True)
                        if re.match(r"RP-\d{4}-\d+", txt):
                            doc_num = txt; break
                if not doc_num: continue

                filed = parse_date(cell(col_map.get("filed", 1)))

                # Names — "Grantor:FOO BAR\nGrantee:BAZ QUX"
                owner = ""; grantee = ""
                names_idx = col_map.get("names", -1)
                if names_idx >= 0:
                    names_td = tds[names_idx]
                    # Each name is in its own line or span
                    names_text = names_td.get_text("\n", strip=True)
                    g = re.search(r"Grantor:\s*(.+?)(?=\nGrantee:|\nGrantor:|$)", names_text, re.I)
                    ge = re.search(r"Grantee:\s*(.+?)(?=\nGrantee:|\nGrantor:|$)", names_text, re.I)
                    if g:  owner   = g.group(1).strip()
                    if ge: grantee = ge.group(1).strip()
                else:
                    # Scan all tds for Grantor:/Grantee: prefixes
                    for td in tds:
                        for line in td.get_text("\n", strip=True).split("\n"):
                            if line.startswith("Grantor:") and not owner:
                                owner = line.replace("Grantor:","").strip()
                            elif line.startswith("Grantee:") and not grantee:
                                grantee = line.replace("Grantee:","").strip()

                legal = cell(col_map.get("legal", 4))

                rec = blank_rec(doc_code, cat, label)
                rec.update({
                    "doc_num":   doc_num,
                    "filed":     filed,
                    "owner":     owner,
                    "grantee":   grantee,
                    "legal":     legal,
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

            # PDF enrichment — uses same browser session (has login cookies)
            frcl_count = sum(1 for r in self.records if r.get("doc_type") == "FRCL")
            if frcl_count > 0:
                log.info(f"=== PDF enrichment ({frcl_count} FRCL records) ===")
                try:
                    await self._enrich_frcl_pdfs(page)
                except Exception:
                    log.error(f"  PDF enrichment: {traceback.format_exc()}")

            await browser.close()
        return self.records

    # ── PDF enrichment via Playwright (uses existing login session) ───────────
    async def _enrich_frcl_pdfs(self, page) -> None:
        """
        For each FRCL record, navigate to the document viewer page
        and extract: owner name, property address, amount, deed date.
        
        The PDF contains: "Commonly known as: ADDRESS CITY TX ZIP"
        and "GRANTOR/BORROWER executed...Deed of Trust...amount of $XXX"
        """
        frcl_recs = [r for r in self.records 
                     if r.get("doc_type") == "FRCL" and r.get("clerk_url")]
        
        log.info(f"  Enriching {len(frcl_recs)} FRCL PDFs…")
        enriched = 0

        for i, rec in enumerate(frcl_recs):
            try:
                url = rec["clerk_url"]
                
                # Navigate to the document viewer
                await page.goto(url, wait_until="domcontentloaded", timeout=20_000)
                await asyncio.sleep(1.5)
                
                # Debug first record — log everything we see
                if i == 0:
                    log.info(f"  PDF DEBUG url: {page.url}")
                    html = await page.content()
                    soup_d = BeautifulSoup(html, "lxml")
                    # Log all text
                    text_d = " ".join(soup_d.get_text().split())[:1000]
                    log.info(f"  PDF DEBUG page text (first 1000): {text_d}")
                    # Log all iframes
                    iframes = soup_d.find_all("iframe")
                    log.info(f"  PDF DEBUG iframes: {[(f.get('src',''),f.get('id','')) for f in iframes]}")
                    # Log all links
                    links = [(a.get_text(strip=True)[:30], a.get("href","")[:80]) for a in soup_d.find_all("a",href=True)]
                    log.info(f"  PDF DEBUG links: {links[:10]}")
                    # Log any embed/object tags
                    embeds = soup_d.find_all(["embed","object"])
                    log.info(f"  PDF DEBUG embeds: {[(e.name, e.get('src',''),e.get('type','')) for e in embeds]}")
                
                # Get page text content — the viewer renders the PDF text
                content = await page.content()
                soup = BeautifulSoup(content, "lxml")
                text = soup.get_text("\n", strip=True)
                
                # Also try waiting for networkidle and getting text again
                if not text.strip() or len(text) < 100:
                    try:
                        await page.wait_for_load_state("networkidle", timeout=10_000)
                        content = await page.content()
                        soup = BeautifulSoup(content, "lxml")
                        text = soup.get_text("\n", strip=True)
                    except: pass
                
                # Try to find PDF download URL from page
                pdf_url = None
                for a in soup.find_all("a", href=True):
                    href = a["href"]
                    if ".pdf" in href.lower() or "download" in href.lower():
                        pdf_url = href if href.startswith("http") else f"{CLERK_BASE}/{href.lstrip('/')}"
                        break
                # Try download button
                if not pdf_url:
                    try:
                        dl_btn = await page.query_selector("a[download], button:has-text('Download'), a:has-text('Download')")
                        if dl_btn:
                            href = await dl_btn.get_attribute("href") or ""
                            if href:
                                pdf_url = href if href.startswith("http") else f"{CLERK_BASE}/{href.lstrip('/')}"
                    except: pass
                
                if i == 0:
                    log.info(f"  PDF DEBUG text length: {len(text)}, pdf_url found: {pdf_url}")
                
                # Also try to get text from any iframe (PDF viewer)
                iframes = await page.query_selector_all("iframe")
                for iframe in iframes:
                    try:
                        frame = await iframe.content_frame()
                        if frame:
                            frame_html = await frame.content()
                            frame_soup = BeautifulSoup(frame_html, "lxml")
                            text += "\n" + frame_soup.get_text("\n", strip=True)
                    except: continue

                if not text.strip():
                    continue

                # Parse key fields from the PDF text
                data = self._parse_frcl_pdf_text(text)
                
                if data:
                    if data.get("owner"):
                        rec["owner"]        = data["owner"]
                    if data.get("address"):
                        rec["prop_address"] = data["address"]
                        rec["prop_city"]    = data.get("city", "Houston")
                        rec["prop_state"]   = "TX"
                        rec["prop_zip"]     = data.get("zip", "")
                    if data.get("amount"):
                        rec["amount"]       = data["amount"]
                    if data.get("deed_date"):
                        rec["legal"]        = f"Deed dated: {data['deed_date']}"
                    if data.get("lender"):
                        rec["grantee"]      = data["lender"]
                    enriched += 1

                if (i + 1) % 25 == 0:
                    log.info(f"  PDF {i+1}/{len(frcl_recs)} — {enriched} enriched so far")

                await asyncio.sleep(0.2)  # gentle rate limit

            except Exception as exc:
                log.warning(f"  PDF {rec.get('doc_num','?')}: {exc}")
                continue

        log.info(f"  PDF enrichment done: {enriched}/{len(frcl_recs)} records enriched")

    def _parse_frcl_pdf_text(self, text: str) -> Optional[dict]:
        """
        Parse text extracted from FRCL document viewer.
        Key patterns confirmed from actual PDF:
        - "Commonly known as: 18602 WALDEN GLEN CIR HUMBLE, TX 77346"
        - "Kisha Dawnique Jefferson-Brown...as Grantor/Borrower"
        - "original amount of $175,824.00"
        - "Deed of Trust, dated 1/29/2021"
        """
        result = {}
        if not text: return None

        # ── Property Address ─────────────────────────────────────────────────
        # "Commonly known as: ADDRESS CITY TX ZIP"
        m = re.search(
            r"[Cc]ommonly\s+known\s+as[:\s]+([^\n]+(?:TX|TEXAS)\s+\d{5})",
            text, re.I
        )
        if m:
            addr_line = m.group(1).strip().rstrip(",.")
            # Split off city/state/zip
            addr_m = re.match(
                r"(.+?),?\s+([A-Z][A-Z\s]+?),?\s+(?:TX|TEXAS),?\s+(\d{5})",
                addr_line, re.I
            )
            if addr_m:
                result["address"] = addr_m.group(1).strip()
                result["city"]    = addr_m.group(2).strip().title()
                result["zip"]     = addr_m.group(3)
            else:
                result["address"] = addr_line
                result["city"]    = "Houston"
                # Extract zip
                zm = re.search(r"\b(77\d{3})\b", addr_line)
                if zm: result["zip"] = zm.group(1)

        # ── Owner/Grantor ────────────────────────────────────────────────────
        # "NAME...as Grantor/Borrower" or "NAME joined herein...as Grantor"
        patterns = [
            r"([A-Z][A-Za-z\s\-]+?)\s+joined\s+herein",
            r"([A-Z][A-Za-z\s\-,]+?),?\s+as\s+Grantor[/\s]Borrower",
            r"executed\s+and\s+delivered.*?by\s+([A-Z][A-Z\s,]+?),",
            r"WHEREAS,\s+on\s+[\d/]+,\s+([A-Z][A-Za-z\s\-]+?)\s+(?:joined|executed)",
        ]
        for pat in patterns:
            m = re.search(pat, text, re.I)
            if m:
                owner = m.group(1).strip().strip(",")
                # Clean up — remove trailing conjunctions
                owner = re.sub(r'\s+(and|pro|forma|her|his)$', '', owner, flags=re.I)
                if len(owner) > 3:
                    result["owner"] = owner
                    break

        # ── Debt Amount ──────────────────────────────────────────────────────
        for pat in [
            r"original(?:\s+principal)?\s+amount\s+of\s+\$([0-9,]+\.?\d*)",
            r"principal\s+(?:sum|amount)\s+of\s+\$([0-9,]+\.?\d*)",
            r"promissory\s+note.*?\$([0-9,]+\.?\d*)",
        ]:
            m = re.search(pat, text, re.I)
            if m:
                result["amount"] = parse_amount(m.group(1))
                break

        # ── Deed Date ────────────────────────────────────────────────────────
        for pat in [
            r"Deed\s+of\s+Trust[^,]*,?\s+dated\s+([\d/]+|[A-Z][a-z]+\s+\d+,?\s*\d{4})",
            r"executed\s+and\s+delivered.*?on\s+([\d/]+|[A-Z][a-z]+\s+\d+,?\s*\d{4})",
            r"WHEREAS,\s+on\s+([\d/]+)",
        ]:
            m = re.search(pat, text, re.I)
            if m:
                result["deed_date"] = m.group(1).strip()
                break

        # ── Lender ───────────────────────────────────────────────────────────
        for pat in [
            r"([A-Z][A-Z\s,\.]+?(?:BANK|MORTGAGE|LOAN|FINANCIAL|CREDIT)[A-Z\s,\.]*?)\s+is\s+(?:the\s+)?(?:current\s+)?mortgagee",
            r"(?:mortgagee|lender|beneficiary)[:\s]+([A-Z][A-Z\s,\.]+?)[\n\.]",
            r"Mortgage\s+Servicer.*?is\s+([A-Z][A-Z\s,\.]+(?:LLC|INC|CORP|NA|N\.A\.)[A-Z\s,\.]*)",
        ]:
            m = re.search(pat, text, re.I)
            if m:
                lender = m.group(1).strip().strip(",")
                if len(lender) > 3:
                    result["lender"] = lender
                    break

        return result if any(result.values()) else None

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

        # Paginate using NEXT button (confirmed from screenshot)
        all_records = []
        page_num = 1

        while True:
            html = await page.content()
            rows = parse_rp_table(html, doc_code, cat, label)
            all_records.extend(rows)

            # Look for NEXT button
            try:
                nxt = await page.query_selector(
                    "input[value='NEXT'], input[value='Next'], "
                    "button:has-text('NEXT'), button:has-text('Next'), "
                    "a:has-text('NEXT'), a:has-text('Next')"
                )
                if nxt and await nxt.is_visible():
                    await nxt.click()
                    await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                    await asyncio.sleep(0.5)
                    page_num += 1
                else:
                    break
            except Exception:
                break

        return all_records

    # ── FRCL scraper — all months from frcl_month onwards ────────────────────
    async def _scrape_all_frcl_months(self, page) -> list:
        """
        FRCL_R.aspx actual structure (confirmed from screenshot):
        - Year dropdown (select)
        - Month dropdown (select)  
        - SEARCH button
        - Results: Doc ID | Sale Date | File Date | Pgs
        - 486 records for June 2026 across ~49 pages (10 per page)
        """
        all_records = []

        try:
            await page.goto(CLERK_FRCL, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
            await asyncio.sleep(2)
        except Exception as exc:
            log.warning(f"  FRCL nav: {exc}"); return []

        log.info(f"  FRCL loaded: {page.url}")

        # Find all select dropdowns and log them
        selects = await page.query_selector_all("select")
        for sel in selects:
            sid   = await sel.get_attribute("id") or "?"
            sname = await sel.get_attribute("name") or "?"
            opts  = await sel.query_selector_all("option")
            opt_vals = []
            for opt in opts[:15]:
                v = await opt.get_attribute("value") or ""
                t = (await opt.inner_text()).strip()
                opt_vals.append(f"{v}={t}")
            log.info(f"  Select: id={sid} name={sname} options={opt_vals}")

        # Scrape from target month onwards
        months_to_scrape = [
            (m, MONTH_NAMES[m]) for m in range(self.frcl_month, 13)
        ]

        for month_num, month_name in months_to_scrape:
            log.info(f"  Scraping FRCL {month_name} {self.frcl_year}…")
            recs = await self._scrape_frcl_month(page, month_name, month_num)
            log.info(f"    {month_name} {self.frcl_year}: {len(recs)} records")
            if recs:
                all_records.extend(recs)
            elif month_num > self.frcl_month:
                # No records for this future month — stop
                log.info(f"    No records for {month_name}, stopping")
                break

        return all_records

    async def _scrape_frcl_month(self, page, month_name: str, month_num: int) -> list:
        """Select year+month dropdowns, click Search, paginate all results."""
        try:
            await page.goto(CLERK_FRCL, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
            await asyncio.sleep(1.5)
        except Exception as exc:
            log.warning(f"  FRCL nav {month_name}: {exc}"); return []

        year_str = str(self.frcl_year)

        # Use exact IDs confirmed from logs
        try:
            await page.select_option("#ctl00_ContentPlaceHolder1_ddlYear", value=year_str)
            log.info(f"    Year {year_str} selected")
            await asyncio.sleep(0.3)
        except Exception as exc:
            log.warning(f"    Year select: {exc}")

        try:
            await page.select_option("#ctl00_ContentPlaceHolder1_ddlMonth", value=str(month_num))
            log.info(f"    Month {month_name} ({month_num}) selected")
            await asyncio.sleep(0.3)
        except Exception as exc:
            log.warning(f"    Month select: {exc}"); return []

        # Click Search — try multiple selectors
        for sel in ["input[value='Search']","input[value='SEARCH']",
                    "button:has-text('Search')","input[type='submit']"]:
            try:
                el = await page.query_selector(sel)
                if el and await el.is_visible():
                    await el.click()
                    log.info(f"    Clicked: {sel}")
                    break
            except: continue

        await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
        await asyncio.sleep(1.5)

        # Check rows found
        html = await page.content()
        soup = BeautifulSoup(html, "lxml")
        page_text = " ".join(soup.get_text().split())
        rows_match = re.search(r"(\d+)\s+Row", page_text)
        if rows_match:
            log.info(f"    Portal: {rows_match.group(0)}")

        # Log ALL tables to find the results one
        tables = soup.find_all("table")
        log.info(f"    Tables found: {len(tables)}")
        for i, tbl in enumerate(tables):
            rows = tbl.find_all("tr")
            if not rows: continue
            hdrs = [c.get_text(strip=True) for c in rows[0].find_all(["th","td"])]
            sample = [c.get_text(strip=True) for c in rows[1].find_all("td")] if len(rows)>1 else []
            log.info(f"    Table {i}: {len(rows)} rows | headers={hdrs} | sample={sample[:4]}")

        # Paginate
        all_records = []
        page_num = 1

        while True:
            html = await page.content()
            recs = self._parse_frcl_table(html, month_name, month_num)
            all_records.extend(recs)
            log.info(f"    Page {page_num}: {len(recs)} records (total {len(all_records)})")

            # Find pagination — look for page number links in a pager row
            # The page uses number links: 1 2 3 ... 10 ...
            next_page = page_num + 1
            next_found = False

            # Try clicking next page number directly
            try:
                # Look for the next page number as a link
                next_el = await page.query_selector(f"a:text-is('{next_page}')")
                if not next_el:
                    # Try within table cells
                    next_el = await page.query_selector(f"td > a:has-text('{next_page}')")
                if not next_el:
                    # Try span containing the link
                    next_el = await page.query_selector(f"span > a:has-text('{next_page}')")

                if next_el:
                    is_visible = await next_el.is_visible()
                    if is_visible:
                        await next_el.click()
                        await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                        await asyncio.sleep(0.8)
                        page_num += 1
                        next_found = True
                    else:
                        # Page number exists but not visible — may need "..." first
                        dots = await page.query_selector("a:has-text('...')")
                        if dots:
                            await dots.click()
                            await page.wait_for_load_state("networkidle", timeout=15_000)
                            await asyncio.sleep(0.8)
                            # Now try the page number again
                            next_el2 = await page.query_selector(f"a:text-is('{next_page}')")
                            if next_el2 and await next_el2.is_visible():
                                await next_el2.click()
                                await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
                                await asyncio.sleep(0.8)
                                page_num += 1
                                next_found = True
            except Exception as exc:
                log.info(f"    Pagination page {next_page}: {exc}")

            if not next_found:
                log.info(f"    No more pages after {page_num}")
                break

        return all_records

    def _parse_frcl_table(self, html: str, month_name: str, month_num: int) -> list:
        """
        Parse FRCL results.
        Confirmed columns: [icon] | Doc ID (FRCL-YYYY-NNNN) | Sale Date | File Date | Pgs
        """
        soup = BeautifulSoup(html, "lxml")
        records = []
        auction_month = f"{month_name} {self.frcl_year}"

        for tbl in soup.find_all("table"):
            rows = tbl.find_all("tr")
            if len(rows) < 2: continue

            # Skip form/nav tables
            if tbl.find("input", {"type": "text"}) or tbl.find("select"):
                continue
            if tbl.find("input", {"type": "password"}):
                continue

            # Check if any cell in first 3 rows contains an FRCL- doc ID
            # This is the most reliable way to identify the results table
            has_frcl = False
            for tr in rows[:5]:
                for td in tr.find_all(["td","th"]):
                    txt = td.get_text(strip=True)
                    if re.match(r"FRCL-\d{4}-\d+", txt):
                        has_frcl = True
                        break
                    a = td.find("a")
                    if a and re.match(r"FRCL-\d{4}-\d+", a.get_text(strip=True)):
                        has_frcl = True
                        break

            # Also accept tables with "Doc ID" / "Sale Date" headers
            hdrs = [c.get_text(strip=True).lower() for c in rows[0].find_all(["th","td"])]
            has_headers = ("doc" in " ".join(hdrs) and "sale" in " ".join(hdrs))

            if not has_frcl and not has_headers:
                continue

            log.info(f"    FRCL results table: {len(rows)-1} data rows | headers={hdrs}")

            # Find column positions
            col_sale = next((i for i,h in enumerate(hdrs) if "sale" in h), -1)
            col_file = next((i for i,h in enumerate(hdrs) if "file" in h and "date" in h), -1)
            if col_file == -1:
                col_file = next((i for i,h in enumerate(hdrs) if "file" in h), -1)

            for tr in rows:
                tds = tr.find_all("td")
                if not tds: continue

                # Find FRCL doc ID — look for link with FRCL- pattern
                doc_num = ""
                link    = ""
                for td in tds:
                    a = td.find("a", href=True)
                    if a:
                        txt = a.get_text(strip=True)
                        if re.match(r"FRCL-", txt):
                            doc_num = txt
                            href = a["href"]
                            link = href if href.startswith("http") else f"{CLERK_BASE}/{href.lstrip('/')}"
                            break
                    # Also check td text directly
                    txt = td.get_text(strip=True)
                    if re.match(r"FRCL-\d{4}-\d+", txt):
                        doc_num = txt
                        break

                if not doc_num:
                    continue

                def cell(i):
                    return tds[i].get_text(strip=True) if 0 <= i < len(tds) else ""

                # Get dates — use column mapping if available, else try positions 1,2,3
                sale_date = ""
                file_date = ""
                if col_sale >= 0:
                    sale_date = parse_date(cell(col_sale))
                if col_file >= 0:
                    file_date = parse_date(cell(col_file))

                # Fallback: scan all cells for date patterns
                if not sale_date or not file_date:
                    dates_found = []
                    for td in tds:
                        txt = td.get_text(strip=True)
                        d = parse_date(txt)
                        if d: dates_found.append(d)
                    if len(dates_found) >= 2:
                        sale_date = sale_date or dates_found[0]
                        file_date = file_date or dates_found[1]
                    elif len(dates_found) == 1:
                        sale_date = sale_date or dates_found[0]

                rec = blank_rec("FRCL", "foreclosure", "Foreclosure Sale")
                rec.update({
                    "doc_num":       doc_num,
                    "doc_type":      "FRCL",
                    "filed":         file_date,
                    "sale_date":     sale_date,
                    "auction_month": auction_month,
                    "cat_label":     f"Foreclosure — {auction_month}",
                    "clerk_url":     link or CLERK_FRCL,
                })
                records.append(rec)

        return records

# ─────────────────────────────────────────────────────────────────────────────
# FRCL PDF ENRICHER (legacy - kept for reference, replaced by Playwright method)
# ─────────────────────────────────────────────────────────────────────────────
class FRCLPDFEnricher_UNUSED:
    """
    Fetches each FRCL document PDF and extracts:
    - Owner/grantor name
    - Property address
    - Sale date
    - Original deed date
    - Debt amount
    - Mortgagee/lender
    """

    def __init__(self, session: requests.Session):
        self.session = session

    def enrich(self, records: list) -> list:
        """Enrich all FRCL records with PDF data."""
        frcl_recs = [r for r in records if r.get("doc_type") == "FRCL" and r.get("clerk_url")]
        log.info(f"PDF enrichment: {len(frcl_recs)} FRCL records to process")

        enriched = 0
        for i, rec in enumerate(frcl_recs):
            try:
                data = self._fetch_pdf_text(rec["clerk_url"])
                if data:
                    # Update the record in-place
                    if data.get("owner"):     rec["owner"]        = data["owner"]
                    if data.get("address"):   rec["prop_address"] = data["address"]
                    if data.get("city"):      rec["prop_city"]    = data["city"]
                    if data.get("zip"):       rec["prop_zip"]     = data["zip"]
                    if data.get("amount"):    rec["amount"]       = data["amount"]
                    if data.get("deed_date"): rec["legal"]        = f"Deed: {data['deed_date']} | {rec.get('legal','')}"
                    if data.get("lender"):    rec["grantee"]      = data["lender"]
                    enriched += 1
                if (i+1) % 50 == 0:
                    log.info(f"  PDF progress: {i+1}/{len(frcl_recs)} ({enriched} enriched)")
                time.sleep(0.15)  # gentle rate limiting
            except Exception as exc:
                log.warning(f"  PDF {rec.get('doc_num')}: {exc}")
                continue

        log.info(f"PDF enrichment complete: {enriched}/{len(frcl_recs)} records enriched")
        return records

    def _fetch_pdf_text(self, url: str) -> Optional[dict]:
        """
        Fetch the PDF viewer page, get the actual PDF URL, download and extract text.
        The clerk URL opens a viewer page — we need to find the actual PDF link.
        """
        # First try: fetch the viewer page and find the PDF src
        try:
            r = self.session.get(url, timeout=20)
            r.raise_for_status()

            # Look for PDF embed or direct PDF link
            soup = BeautifulSoup(r.text, "lxml")

            pdf_url = None
            # Common patterns for embedded PDF viewers
            for tag in soup.find_all(["iframe", "embed", "object"]):
                src = tag.get("src", "") or tag.get("data", "")
                if ".pdf" in src.lower() or "pdf" in src.lower():
                    pdf_url = src if src.startswith("http") else f"{CLERK_BASE}/{src.lstrip('/')}"
                    break

            # Look for direct PDF links
            if not pdf_url:
                for a in soup.find_all("a", href=True):
                    if ".pdf" in a["href"].lower():
                        pdf_url = a["href"] if a["href"].startswith("http") else f"{CLERK_BASE}/{a['href'].lstrip('/')}"
                        break

            # Some portals serve the PDF directly from the viewer URL with a param
            if not pdf_url:
                # Try appending common PDF export params
                for param in ["?format=pdf", "&format=pdf", "/pdf"]:
                    test_url = url + param
                    try:
                        tr = self.session.head(test_url, timeout=10)
                        if "pdf" in tr.headers.get("content-type", "").lower():
                            pdf_url = test_url
                            break
                    except: continue

            if not pdf_url:
                # If viewer page itself is PDF content
                if "pdf" in r.headers.get("content-type", "").lower():
                    return self._parse_pdf_bytes(r.content)
                return None

            # Download PDF
            pr = self.session.get(pdf_url, timeout=30)
            pr.raise_for_status()
            return self._parse_pdf_bytes(pr.content)

        except Exception as exc:
            log.warning(f"  PDF fetch {url}: {exc}")
            return None

    def _parse_pdf_bytes(self, data: bytes) -> Optional[dict]:
        """Extract text from PDF bytes and parse key fields."""
        try:
            import pypdf
            reader = pypdf.PdfReader(io.BytesIO(data))
            text = "\n".join(page.extract_text() or "" for page in reader.pages)
        except ImportError:
            try:
                import pdfminer.high_level as pdfminer
                text = pdfminer.extract_text(io.BytesIO(data))
            except ImportError:
                log.warning("No PDF library available — install pypdf or pdfminer.six")
                return None
        except Exception as exc:
            log.warning(f"  PDF parse error: {exc}")
            return None

        if not text:
            return None

        return self._extract_fields(text)

    def _extract_fields(self, text: str) -> dict:
        """
        Extract fields from foreclosure notice PDF text.
        Based on actual PDF structure seen in screenshot.
        """
        result = {}

        # ── Sale Date ────────────────────────────────────────────────────────
        # "Date: June 02, 2026" or "Sale Date: 06/02/2026"
        m = re.search(r"Date[:\s]+([A-Z][a-z]+ \d{1,2},?\s*\d{4})", text)
        if m: result["sale_date"] = m.group(1).strip()

        # ── Owner/Grantor ────────────────────────────────────────────────────
        # "with ADRIENNA LUCILLE TORRES, AN UNMARRIED WOMAN, grantor(s)"
        # or "grantor(s) NAME"
        m = re.search(r"with\s+([A-Z][A-Z\s,\.]+?),?\s+(?:AN?\s+)?(?:UNMARRIED|MARRIED|INDIVIDUAL|TRUST|LLC|CORP)", text)
        if m:
            result["owner"] = m.group(1).strip().rstrip(",")
        if not result.get("owner"):
            m = re.search(r"([A-Z][A-Z\s]+?),?\s+grantor\(?s?\)?", text, re.I)
            if m: result["owner"] = m.group(1).strip()

        # ── Debt Amount ──────────────────────────────────────────────────────
        # "principal amount of $199,975.00"
        m = re.search(r"principal amount of \$([0-9,]+\.?\d*)", text, re.I)
        if m:
            result["amount"] = parse_amount(m.group(1))
        if not result.get("amount"):
            m = re.search(r"\$([0-9,]+\.?\d*)", text)
            if m: result["amount"] = parse_amount(m.group(1))

        # ── Original Deed Date ───────────────────────────────────────────────
        # "Deed of Trust...dated June 30, 2017"
        m = re.search(r"Deed of Trust[^.]*dated\s+([A-Z][a-z]+ \d{1,2},?\s*\d{4})", text, re.I)
        if m: result["deed_date"] = m.group(1).strip()

        # ── Lender/Mortgagee ─────────────────────────────────────────────────
        # "U.S. BANK NATIONAL ASSOCIATION is the current mortgagee"
        m = re.search(r"([A-Z][A-Z\s,\.]+?)\s+is the current mortgagee", text, re.I)
        if m: result["lender"] = m.group(1).strip()
        if not result.get("lender"):
            m = re.search(r"Mortgagee[:\s]+([A-Z][A-Z\s,\.]+?)[\n\.]", text, re.I)
            if m: result["lender"] = m.group(1).strip()

        # ── Property Address ─────────────────────────────────────────────────
        # Usually in "Exhibit A" or "Property to Be Sold"
        # Common patterns: street number + street name + city + TX + zip
        addr_patterns = [
            r"(\d{3,5}\s+[A-Z][A-Z\s]+(?:STREET|ST|AVENUE|AVE|DRIVE|DR|ROAD|RD|LANE|LN|BLVD|BOULEVARD|WAY|COURT|CT|PLACE|PL)[.,\s]+(?:HOUSTON|HARRIS)[,\s]*(?:TEXAS|TX)[,\s]*(\d{5}))",
            r"(\d{3,5}\s+[A-Z0-9][A-Z0-9\s#]+),?\s+(HOUSTON|HARRIS COUNTY),?\s+(TEXAS|TX),?\s+(\d{5})",
            r"Property Address[:\s]+(.+?)(?:\n|,\s*Houston|\.|$)",
        ]
        for pat in addr_patterns:
            m = re.search(pat, text, re.I)
            if m:
                result["address"] = m.group(1).strip()
                result["city"]    = "Houston"
                # Try to get zip
                zm = re.search(r"\b(77\d{3})\b", m.group(0))
                if zm: result["zip"] = zm.group(1)
                break

        return result if any(result.values()) else None

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

    # Dedup by doc_num + doc_type combo
    seen, unique = set(), []
    for r in records:
        doc_num  = (r.get("doc_num","") or "").strip()
        doc_type = (r.get("doc_type","") or "").strip()
        owner    = (r.get("owner","") or "").strip()
        filed    = (r.get("filed","") or "").strip()
        # Use doc_num+type if available, else owner+filed
        if doc_num:
            key = f"{doc_num}|{doc_type}"
        else:
            key = f"{owner}|{filed}|{doc_type}"
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
