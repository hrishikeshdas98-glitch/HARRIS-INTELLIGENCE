# Harris County Motivated Seller Lead Scraper

Automated daily scraper for Harris County, TX public records.  
Collects Lis Pendens, Foreclosures, Tax Deeds, Judgments, Liens, Probate, and more.

## File Structure

```
.github/workflows/scrape.yml   # GitHub Actions: daily cron + manual trigger
scraper/
  fetch.py                     # Main scraper (Playwright + requests)
  requirements.txt             # Python deps
dashboard/
  index.html                   # Live web dashboard (GitHub Pages)
  records.json                 # Latest scraped data (auto-updated)
data/
  records.json                 # Duplicate output (for other tools)
  ghl_export_YYYYMMDD.csv      # Go High Level CRM import file
```

## Quick Start (local)

```bash
pip install -r scraper/requirements.txt
python -m playwright install --with-deps chromium
python scraper/fetch.py
```

## GitHub Actions Setup

1. Push this repo to GitHub
2. Go to **Settings → Pages** → Source: **GitHub Actions**
3. Go to **Settings → Actions → General** → Workflow permissions: **Read and write**
4. The workflow runs daily at 07:00 UTC (02:00 CDT)
5. Trigger manually via **Actions → Scrape Harris County Leads → Run workflow**

## Dashboard

After the first run, your live dashboard will be at:
```
https://<your-username>.github.io/<repo-name>/
```

## Lead Types Collected

| Code | Name |
|------|------|
| LP | Lis Pendens |
| NOFC | Notice of Foreclosure |
| TAXDEED | Tax Deed |
| JUD / CCJ / DRJUD | Judgment |
| LNCORPTX / LNIRS / LNFED | Tax / Federal Lien |
| LN / LNMECH / LNHOA | Lien / Mechanic / HOA |
| MEDLN | Medicaid Lien |
| PRO | Probate Documents |
| NOC | Notice of Commencement |
| RELLP | Release Lis Pendens |

## Seller Score (0–100)

| Component | Points |
|-----------|--------|
| Base | 30 |
| Per flag | +10 |
| LP + Foreclosure combo | +20 |
| Amount > $100k | +15 |
| Amount > $50k | +10 |
| Filed this week | +5 |
| Has property address | +5 |

## GHL CSV Export

The `data/ghl_export_YYYYMMDD.csv` file maps directly to Go High Level contact import fields.  
The dashboard also has a live **Export GHL CSV** button filtered to your current view.

## Notes

- The HCAD bulk parcel data (~400 MB) is downloaded each run to match owner names to addresses.
- Owner name matching uses three variants: `FIRST LAST`, `LAST FIRST`, `LAST, FIRST`.
- Records are deduplicated by document number.
- The scraper never crashes on bad records — all errors are caught and logged.
