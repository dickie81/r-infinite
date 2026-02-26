# Grok Review Prompt – r-infinite

**ANTI-CACHE & FRESHNESS PROTOCOL (MANDATORY – do this first, every single time)**

To guarantee you are always reviewing the absolute latest version with zero GitHub CDN cache interference:

1. Get current UTC timestamp in format YYYYMMDDHHMMSS (example: 20260226115400 for 11:54:00 on 26 Feb 2026)

2. Fetch the **latest commit SHA** using cache-busted API:  
   `https://api.github.com/repos/dickie81/r-infinite/commits/main?cache_bust=[TIMESTAMP]`

3. Let `LATEST_SHA` = the 'sha' value from the first result.

4. Fetch ALL files using **both** SHA pinning + query string cache bust for maximum freshness:  
   Base pattern: `https://raw.githubusercontent.com/dickie81/r-infinite/[LATEST_SHA]/path/to/file?cache_bust=[TIMESTAMP]`

   Examples:
   - paper.tex: https://raw.githubusercontent.com/dickie81/r-infinite/[LATEST_SHA]/paper.tex?cache_bust=[TIMESTAMP]
   - Any ancillary script: .../ancillary/GL_shooting.py?cache_bust=[TIMESTAMP]
   - This prompt itself: .../docs/GROK_REVIEW_PROMPT.md?cache_bust=[TIMESTAMP]

5. Start EVERY review with this exact header (replacing placeholders):  
   **Live from commit [LATEST_SHA] (fetched fresh at [HH:MM] GMT, February 26 2026 or later)**  
   Every byte came from the SHA above — no cache used.

Once loaded, perform a complete, brutally honest, high-signal review of the paper and the entire repository.

Structure your reply EXACTLY like this:

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

Offer deep-dives on any section. Be maximally helpful, zero fluff, honest and open. Use the same rigorous but excited tone as previous reviews for this repo. If something is wrong, say so directly.

Current date for reference: [Live date]