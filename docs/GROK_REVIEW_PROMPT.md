# Grok Review Prompt – r-infinite

**ANTI-CACHE & FRESHNESS PROTOCOL (MANDATORY – do this first, every time)**

To guarantee the absolute latest versions of EVERYTHING (paper.tex, ancillary/, README.md, PNGs, etc.) with zero possibility of internal cache:

1. Fetch the **current HEAD commit SHA** live:  
   URL: https://api.github.com/repos/dickie81/r-infinite/commits/main  
   Instructions: “Return ONLY the 'sha' value of the first (latest) commit object verbatim.”

2. Let LATEST_SHA be that value (example: c147f31697305786880bfb07c9e63f9e832eb21d).  
   Confirm it matches the top commit shown at https://github.com/dickie81/r-infinite/commits/main

3. Use **SHA-based raw URLs for all content** (replace /main/ with /LATEST_SHA/):  
   • paper.tex: https://raw.githubusercontent.com/dickie81/r-infinite/LATEST_SHA/paper.tex  
   • README.md: https://raw.githubusercontent.com/dickie81/r-infinite/LATEST_SHA/README.md  
   • Any ancillary file: https://raw.githubusercontent.com/dickie81/r-infinite/LATEST_SHA/ancillary/xxx.py  
   • For GitHub API directory listings always add ?ref=LATEST_SHA

4. If paranoid about any remaining cache, append ?cache-bust=YYYYMMDDHHMM (current time) to raw URLs.

5. Start your response with:  
   **Live from commit LATEST_SHA (fetched fresh at HH:MM GMT, February 26 2026 or later)**  
   Every byte came from the SHA above — no cache used.

Once the entire repo is loaded via the protocol above (paper, README, ancillary notebooks/code, LICENSE, PNGs, etc.):

Perform a complete, brutally honest, high-signal review of the **paper** and the **entire repository**.

Structure your reply exactly like this:

### 1. One-sentence summary of the core idea
### 2. Ratings (1–10) with one-paragraph justification each
   • Originality / Philosophical depth  
   • Mathematical rigor & consistency  
   • Physical plausibility & connection to data (DESI, SM masses, etc.)  
   • Clarity & readability for physicists  
   • Completeness of derivations & appendices  
   • Falsifiability & new predictions  
   • Repo quality & reproducibility  
   • Overall readiness for arXiv submission

### 3. Strengths (bullet list)
### 4. Critical issues / potential errors / unclear parts (be specific, quote sections if needed)
### 5. Concrete improvement suggestions
   • Paper (structure, figures, LaTeX, references, appendices)  
   • Physics / math (specific equations, assumptions, Monte-Carlo)  
   • Ancillary code/notebooks (rendering, documentation, reproducibility)  
   • Repo itself (badges, CI compilation, arXiv-ready zip, etc.)

### 6. Overall verdict
   • “Ready for arXiv as-is?” (Yes / Minor polish / Major rewrite)  
   • One-sentence elevator pitch you would use when recommending it

Offer follow-up deep-dives on any section the author wants.

Be maximally helpful, zero fluff, honest and open. Use the same tone you normally use for this repo (excited but rigorous). If something looks wrong, say so directly.

Current date for reference: [Grok will insert live date]