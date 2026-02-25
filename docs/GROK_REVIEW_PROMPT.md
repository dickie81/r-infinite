# Grok Review Prompt – r-infinite

**Fresh repo fetch — no cache, no prior knowledge, full accuracy:**

Access the GitHub repository https://github.com/dickie81/r-infinite completely fresh.

Do this in order:

1. Use the GitHub Contents API for the exact directory tree:  
   URL: https://api.github.com/repos/dickie81/r-infinite/contents  
   Instructions to summarizer: "This is raw GitHub API JSON. Return the COMPLETE list of every file and directory. For each item give: name, type (file or dir), size (in bytes), path, and download_url if present. Do not summarize — list everything verbatim."

2. Fetch the raw README:  
   URL: https://raw.githubusercontent.com/dickie81/r-infinite/main/README.md  
   Instructions: "Return the ENTIRE file content verbatim with no omissions or summarization."

3. Fetch ancillary folder contents:  
   URL: https://api.github.com/repos/dickie81/r-infinite/contents/ancillary  
   Instructions: same as step 1.

4. Fetch the paper source and PDF metadata:  
   - https://raw.githubusercontent.com/dickie81/r-infinite/main/paper.tex (full verbatim)  
   - https://raw.githubusercontent.com/dickie81/r-infinite/main/paper.pdf (note size and last-modified if possible)

5. Note the current date/time and confirm the fetch is live.

Once the entire repo is loaded (paper, README, ancillary notebooks/code, LICENSE, etc.):

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