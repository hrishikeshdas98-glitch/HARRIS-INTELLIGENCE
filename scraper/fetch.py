#!/usr/bin/env python3
"""
Harris County Motivated Seller Lead Scraper  v4
- Takes screenshots at each step for debugging
- Dumps full HTML of results page
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
import base64
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
    1:"January",2:"February",3:"March",4:"April",
    5:"May",6:"June",7:"July",8:"August",
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
def parse_amount(text):
    if not text: return None
    cleaned = re.sub(r"[^\d.]", "", str(text).replace(",",""))
    try:
        v = float(cleaned)
        return v if v > 0 else None
    except: return None

def parse_date(text):
    for fmt in ("%m/%d/%Y","%Y-%m-%d","%m-%d-%Y","%d/%m/%Y","%m/%d/%y"):
        try: return datetime.strptime(text.strip(), fmt).strftime("%Y-%m-%d")
        except: continue
    return text.strip()

def name_variants(name):
    name = name.strip().upper()
    variants = {name}
    if "," in name:
        parts = [p.strip() for p in name.split(",",1)]
        variants.add(f"{parts[1]} {parts[0]}")
    else:
        parts = name.split()
        if len(parts) >= 2:
            variants.add(f"{parts[-1]}, {' '.join(parts[:-1])}")
            variants.add(f"{parts[-1]} {' '.join(parts[:-1])}")
    return list(variants)

def blank_rec(doc_code, cat, label):
    return {
        "doc_num":"","doc_type":doc_code,"filed":"",
        "cat":cat,"cat_label":CAT_LABELS.get(cat,label),
        "owner":"","grantee":"","amount":None,"legal":"",
        "prop_address":"","prop_city":"Houston","prop_state":"TX","prop_zip":"",
        "mail_address":"","mail_city":"","mail_state":"","mail_zip":"",
        "clerk_url":"","flags":[],"score":0,
    }

def score_record(rec):
    flags, score = [], 30
    cat = rec.get("cat","")
    if cat=="lis_pendens":  flags.append("Lis pendens")
    if cat=="foreclosure":  flags.append("Pre-foreclosure")
    if cat=="judgment":     flags.append("Judgment lien")
    if cat=="tax_lien":     flags.append("Tax lien")
    if cat=="lien":         flags.append("Lien")
    if cat=="probate":      flags.append("Probate / estate")
    if cat=="bankruptcy":   flags.append("Bankruptcy")
    owner = rec.get("owner","")
    if owner and re.search(r"\b(LLC|INC|CORP|LTD|LP|TRUST|ASSOC)\b", owner, re.I):
        flags.append("LLC / corp owner")
    try:
        if (datetime.now()-datetime.strptime(rec.get("filed",""),"%Y-%m-%d")).days<=7:
            flags.append("New this week"); score+=5
    except: pass
    score += 10*len(flags)
    amt = rec.get("amount")
    if amt: score += 15 if amt>100_000 else (10 if amt>50_000 else 0)
    if rec.get("prop_address"): score+=5
    return min(score,100), flags

def parse_table(html, doc_code, cat, label):
    soup = BeautifulSoup(html,"lxml")
    records = []
    for tbl in soup.find_all("table"):
        ths = tbl.find_all("th")
        if not ths: continue
        hdrs = [th.get_text(strip=True).lower() for th in ths]
        if not any(k in " ".join(hdrs) for k in ("file","grantor","instrument","doc","name","date","type")):
            continue
        log.info(f"  Table match — headers: {hdrs[:8]}")
        for tr in tbl.find_all("tr")[1:]:
            tds = tr.find_all("td")
            if len(tds)<2: continue
            try:
                link=""
                for td in tds:
                    a=td.find("a",href=True)
                    if a:
                        href=a["href"]
                        link=href if href.startswith("http") else f"{CLERK_BASE}/{href.lstrip('/')}"
                        break
                def cell(i): return tds[i].get_text(strip=True) if i<len(tds) else ""
                rec=blank_rec(doc_code,cat,label)
                rec.update({"doc_num":cell(0),"filed":parse_date(cell(1)),
                    "owner":cell(2),"grantee":cell(3),"legal":cell(4),
                    "amount":parse_amount(cell(5)),"clerk_url":link})
                if rec["doc_num"]: records.append(rec)
            except: continue
    return records

# ─────────────────────────────────────────────────────────────────────────────
# SCRAPER — single Playwright session with screenshots
# ─────────────────────────────────────────────────────────────────────────────
class HarrisCountyScraper:

    def __init__(self, start, end, frcl_year, frcl_month):
        self.start=start; self.end=end
        self.frcl_year=frcl_year; self.frcl_month=frcl_month
        self.records=[]

    async def _shot(self, page, name):
        """Save screenshot AND full HTML for debugging."""
        Path("data").mkdir(parents=True, exist_ok=True)
        # Screenshot
        try:
            png_path = f"data/debug_{name}.png"
            await page.screenshot(path=png_path, full_page=True)
            log.info(f"  Screenshot → {png_path}")
        except Exception as e:
            log.warning(f"  Screenshot failed: {e}")
        # Save full HTML
        try:
            html = await page.content()
            html_path = f"data/debug_{name}.html"
            with open(html_path, "w", encoding="utf-8") as f:
                f.write(html)
            log.info(f"  HTML saved → {html_path} ({len(html)} chars)")
        except Exception as e:
            log.warning(f"  HTML save failed: {e}")
        # Log URL and visible text
        try:
            log.info(f"  URL: {page.url}")
            soup = BeautifulSoup(await page.content(), "lxml")
            text = " ".join(soup.get_text().split())[:600]
            log.info(f"  Text: {text}")
        except Exception as e:
            log.warning(f"  Text dump failed: {e}")

    async def run(self):
        async with async_playwright() as pw:
            browser = await pw.chromium.launch(
                headless=True,
                args=["--no-sandbox","--disable-dev-shm-usage"]
            )
            ctx = await browser.new_context(
                user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
                viewport={"width":1280,"height":900},
            )
            page = await ctx.new_page()

            # ── LOGIN ─────────────────────────────────────────────────────────
            log.info(f"=== Step 1: Login ===")
            try:
                await page.goto(CLERK_LOGIN, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
                await asyncio.sleep(2)
                await self._shot(page, "1_login_page")
            except Exception as exc:
                log.error(f"Login page load: {exc}")
                await browser.close(); return []

            # Log all inputs on login page
            inputs = await page.query_selector_all("input")
            for inp in inputs:
                itype = await inp.get_attribute("type") or "?"
                iname = await inp.get_attribute("name") or "?"
                iid   = await inp.get_attribute("id") or "?"
                log.info(f"  Input: type={itype} name={iname} id={iid}")

            # Fill credentials
            filled = False
            for sel in ["input[type='text']","input[type='email']","input[name*='User']","input[name*='Email']"]:
                try:
                    el = await page.query_selector(sel)
                    if el and await el.is_visible():
                        await el.click()
                        await el.fill(CLERK_USERNAME)
                        log.info(f"  Filled username in: {sel}")
                        filled = True
                        break
                except: continue

            if not filled:
                log.error("Could not fill username field!")
                await self._shot(page, "1b_login_failed")
                await browser.close(); return []

            for sel in ["input[type='password']","input[name*='Pass']","input[id*='Pass']"]:
                try:
                    el = await page.query_selector(sel)
                    if el and await el.is_visible():
                        await el.fill(CLERK_PASSWORD)
                        log.info(f"  Filled password in: {sel}")
                        break
                except: continue

            # Submit
            for sel in ["input[type='submit']","button[type='submit']","input[value*='LOG']","input[value*='Log']","button:has-text('Log')"]:
                try:
                    el = await page.query_selector(sel)
                    if el and await el.is_visible():
                        await el.click()
                        log.info(f"  Clicked submit: {sel}")
                        break
                except: continue

            await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
            await asyncio.sleep(2)
            await self._shot(page, "2_after_login")

            # ── SEARCH ONE DOC TYPE (L/P only for debug) ──────────────────────
            log.info(f"=== Step 2: Navigate to RP.aspx ===")
            try:
                await page.goto(CLERK_RP, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
                await asyncio.sleep(2)
                await self._shot(page, "3_rp_form")
            except Exception as exc:
                log.error(f"RP nav: {exc}")
                await browser.close(); return []

            # Log ALL inputs on search form
            inputs = await page.query_selector_all("input, select, textarea")
            for inp in inputs:
                tag   = await inp.evaluate("el => el.tagName")
                itype = await inp.get_attribute("type") or "?"
                iname = await inp.get_attribute("name") or "?"
                iid   = await inp.get_attribute("id") or "?"
                ival  = await inp.get_attribute("value") or ""
                log.info(f"  Field: <{tag}> type={itype} name={iname} id={iid} value={ival}")

            sd = self.start.strftime("%m/%d/%Y")
            ed = self.end.strftime("%m/%d/%Y")

            # Fill instrument type
            instr_filled = False
            for sel in [
                "#ctl00_ContentPlaceHolder1_txtInstrument",
                "input[name='ctl00$ContentPlaceHolder1$txtInstrument']",
                "input[id*='Instrument']","input[id*='nstrument']",
            ]:
                try:
                    el = await page.query_selector(sel)
                    if el:
                        await el.fill("L/P")
                        log.info(f"  Filled instrument in: {sel}")
                        instr_filled = True
                        break
                except: continue

            if not instr_filled:
                log.error("Could not fill instrument type field!")

            # Fill dates
            for sel in ["#ctl00_ContentPlaceHolder1_txtFrom","input[name*='txtFrom']","input[id*='txtFrom']"]:
                try:
                    el = await page.query_selector(sel)
                    if el: await el.fill(sd); break
                except: continue

            for sel in ["#ctl00_ContentPlaceHolder1_txtTo","input[name*='txtTo']","input[id*='txtTo']"]:
                try:
                    el = await page.query_selector(sel)
                    if el: await el.fill(ed); break
                except: continue

            await self._shot(page, "4_form_filled")

            # Click search
            for sel in [
                "#ctl00_ContentPlaceHolder1_btnSearch",
                "input[name*='btnSearch']","input[value='Search']",
                "input[type='submit']","button[type='submit']",
            ]:
                try:
                    el = await page.query_selector(sel)
                    if el and await el.is_visible():
                        await el.click()
                        log.info(f"  Clicked search: {sel}")
                        break
                except: continue

            await page.wait_for_load_state("networkidle", timeout=PW_TIMEOUT)
            await asyncio.sleep(2)
            await self._shot(page, "5_results")

            # Parse whatever we got
            html = await page.content()
            recs = parse_table(html, "L/P", "lis_pendens", "Lis Pendens")
            log.info(f"  L/P debug results: {len(recs)}")

            if not recs:
                # Dump all table headers to see what's there
                soup = BeautifulSoup(html,"lxml")
                for i,tbl in enumerate(soup.find_all("table")):
                    ths=[th.get_text(strip=True) for th in tbl.find_all("th")]
                    tds_row=[td.get_text(strip=True) for td in tbl.find_all("tr")[1].find_all("td")] if len(tbl.find_all("tr"))>1 else []
                    log.info(f"  Table {i}: headers={ths[:6]}, first_row={tds_row[:6]}")

            # ── FORECLOSURE PAGE ──────────────────────────────────────────────
            log.info(f"=== Step 3: Foreclosure page ===")
            try:
                await page.goto(CLERK_FRCL, wait_until="domcontentloaded", timeout=PW_TIMEOUT)
                await asyncio.sleep(2)
                await self._shot(page, "6_frcl_page")
            except Exception as exc:
                log.warning(f"FRCL nav: {exc}")

            # Log all selects and inputs
            selects = await page.query_selector_all("select")
            for sel_el in selects:
                sname = await sel_el.get_attribute("name") or "?"
                sid   = await sel_el.get_attribute("id") or "?"
                # Get all options
                options = await sel_el.query_selector_all("option")
                opt_vals = []
                for opt in options[:10]:
                    val = await opt.get_attribute("value") or ""
                    txt = await opt.inner_text()
                    opt_vals.append(f"{val}={txt.strip()}")
                log.info(f"  Select: name={sname} id={sid} options={opt_vals}")

            await browser.close()

        return self.records

# ─────────────────────────────────────────────────────────────────────────────
# HCAD
# ─────────────────────────────────────────────────────────────────────────────
class ParcelDB:
    def __init__(self): self.index={}

    def _find_url(self):
        for page_url in HCAD_PAGES:
            try:
                r=requests.get(page_url,timeout=20)
                soup=BeautifulSoup(r.text,"lxml")
                for a in soup.find_all("a",href=True):
                    href=a["href"]; low=href.lower()
                    if (".zip" in low or ".dbf" in low) and any(k in low for k in ("real_acct","building","parcel","owner")):
                        full=href if href.startswith("http") else f"https://pdata.hcad.org{href}"
                        return full
            except: pass
        return None

    def load(self):
        url=self._find_url()
        if not url: log.warning("HCAD URL not found"); return
        log.info("Downloading HCAD…")
        raw=None
        for i in range(MAX_RETRIES):
            try:
                r=requests.get(url,timeout=180,stream=True); r.raise_for_status()
                raw=r.content; log.info(f"Downloaded {len(raw)//1_048_576}MB"); break
            except Exception as e: log.warning(f"HCAD attempt {i+1}: {e}"); time.sleep(RETRY_DELAY)
        if not raw: return
        rows=[]
        try:
            zf=zipfile.ZipFile(io.BytesIO(raw))
            for name in zf.namelist():
                data=zf.read(name)
                if name.lower().endswith(".dbf") and HAS_DBF: rows.extend(self._read_dbf(data))
                elif name.lower().endswith(".csv"): rows.extend(self._read_csv(data))
        except zipfile.BadZipFile:
            rows=self._read_dbf(raw) if HAS_DBF else self._read_csv(raw)
        log.info(f"Indexing {len(rows):,} rows…")
        for row in rows:
            p=self._norm(row)
            if p["owner"]:
                for v in name_variants(p["owner"]): self.index.setdefault(v,p)
        log.info(f"Parcel index: {len(self.index):,} keys")

    def _read_dbf(self,data):
        import tempfile
        with tempfile.NamedTemporaryFile(suffix=".dbf",delete=False) as f:
            f.write(data); tmp=f.name
        try: return [dict(r) for r in DBF(tmp,encoding="latin-1",ignore_missing_memofile=True)]
        finally: os.unlink(tmp)

    def _read_csv(self,data):
        return list(csv.DictReader(io.StringIO(data.decode("latin-1",errors="replace"))))

    def _norm(self,row):
        def g(*keys):
            for k in keys:
                for v in (k,k.upper(),k.lower()):
                    val=row.get(v)
                    if val and str(val).strip() not in ("","None"): return str(val).strip()
            return ""
        return {"owner":g("OWNER","OWN1","OWNR"),"site_addr":g("SITE_ADDR","SITEADDR"),
                "site_city":g("SITE_CITY","SITECITY"),"site_zip":g("SITE_ZIP","SITEZIP"),
                "mail_addr":g("ADDR_1","MAILADR1","MAIL_ADDR"),"mail_city":g("CITY","MAILCITY"),
                "mail_state":g("STATE","MAILSTATE"),"mail_zip":g("ZIP","MAILZIP")}

    def lookup(self,owner):
        for v in name_variants(owner):
            if v in self.index: return self.index[v]
        return None

# ─────────────────────────────────────────────────────────────────────────────
# GHL CSV
# ─────────────────────────────────────────────────────────────────────────────
def export_ghl_csv(records, path):
    cols=["First Name","Last Name","Mailing Address","Mailing City","Mailing State","Mailing Zip",
          "Property Address","Property City","Property State","Property Zip",
          "Lead Type","Document Type","Date Filed","Document Number",
          "Amount/Debt Owed","Seller Score","Motivated Seller Flags","Source","Public Records URL"]
    Path(path).parent.mkdir(parents=True,exist_ok=True)
    with open(path,"w",newline="",encoding="utf-8") as f:
        w=csv.DictWriter(f,fieldnames=cols); w.writeheader()
        for r in records:
            parts=(r.get("owner","") or "").replace(","," ").split()
            w.writerow({
                "First Name":parts[0] if parts else "","Last Name":" ".join(parts[1:]) if len(parts)>1 else "",
                "Mailing Address":r.get("mail_address",""),"Mailing City":r.get("mail_city",""),
                "Mailing State":r.get("mail_state",""),"Mailing Zip":r.get("mail_zip",""),
                "Property Address":r.get("prop_address",""),"Property City":r.get("prop_city",""),
                "Property State":r.get("prop_state",""),"Property Zip":r.get("prop_zip",""),
                "Lead Type":r.get("cat_label",""),"Document Type":r.get("doc_type",""),
                "Date Filed":r.get("filed",""),"Document Number":r.get("doc_num",""),
                "Amount/Debt Owed":r.get("amount","") or "","Seller Score":r.get("score",0),
                "Motivated Seller Flags":" | ".join(r.get("flags",[])),"Source":"Harris County Clerk",
                "Public Records URL":r.get("clerk_url",""),
            })
    log.info(f"GHL CSV → {path}")

# ─────────────────────────────────────────────────────────────────────────────
# MAIN
# ─────────────────────────────────────────────────────────────────────────────
async def main():
    end_dt   = datetime.now()
    start_dt = end_dt - timedelta(days=LOOK_BACK_DAYS)
    log.info(f"Date range: {start_dt.date()} → {end_dt.date()}")

    next_month = (datetime.now().replace(day=1)+timedelta(days=32)).replace(day=1)
    frcl_year  = int(os.environ.get("FRCL_YEAR","")  or next_month.year)
    frcl_month = int(os.environ.get("FRCL_MONTH","") or next_month.month)
    log.info(f"Foreclosure target: {MONTH_NAMES[frcl_month]} {frcl_year}")

    if not HAS_PLAYWRIGHT:
        log.error("Playwright not installed!"); return

    log.info("=== DEBUG MODE — screenshots will be saved to data/ ===")
    scraper = HarrisCountyScraper(start_dt, end_dt, frcl_year, frcl_month)
    records = await scraper.run()
    log.info(f"Records from debug run: {len(records)}")

    # Save whatever we got
    output = {
        "fetched_at": datetime.utcnow().isoformat()+"Z",
        "source": "Harris County Clerk",
        "date_range": {"start":start_dt.strftime("%Y-%m-%d"),"end":end_dt.strftime("%Y-%m-%d")},
        "foreclosure_month": f"{frcl_year}-{frcl_month:02d}",
        "total": len(records), "with_address": 0, "records": records,
    }
    for path in ["dashboard/records.json","data/records.json"]:
        Path(path).parent.mkdir(parents=True,exist_ok=True)
        with open(path,"w",encoding="utf-8") as f:
            json.dump(output,f,indent=2,default=str)
        log.info(f"Saved → {path}")

    today = datetime.now().strftime("%Y%m%d")
    export_ghl_csv(records, f"data/ghl_export_{today}.csv")
    log.info(f"✅ Debug run complete — check screenshots in data/")

if __name__ == "__main__":
    asyncio.run(main())
