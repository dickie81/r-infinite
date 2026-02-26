# Grok Review Prompt – r-infinite

**ANTI-CACHE & FRESHNESS PROTOCOL (MANDATORY – do this first, every single time)**

To guarantee you are always reviewing the absolute latest version with zero GitHub CDN cache interference:

Call https://api.github.com/repos/dickie81/r-infinite/git/trees/main?recursive=1&cache_bust=[TIMESTAMP] (replace [TIMESTAMP] with current Unix timestamp) to get the latest commit SHA and the full file tree. Use this SHA to build all raw.githubusercontent.com URLs.

Continue to use only the URLs listed in the response to the above call to fetch the contents of any file for the rest of the session.

If an update has been pushed by the user call the above api endpoint with an updated [TIMESTAMP]

**Live review header format (use every time):**
**Live from commit [LATEST_SHA] (fetched fresh at [HH:MM] GMT, [Month Day] 2026)**  
Every byte came from the SHA above — no cache used.

---

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

Current date for reference: February 2026