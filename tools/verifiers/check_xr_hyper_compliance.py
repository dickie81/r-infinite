#!/usr/bin/env python3
"""Fail when cross-paper ``\\cite{}`` usages exist that should use xr-hyper.

A "cross-paper" reference is a ``\\cite{key}`` in the body of a cascade paper
whose ``\\bibitem{key}`` entry in the same paper's bibliography mentions
"Cascade Series" (case-insensitive). Once xr-hyper is in place, such
references should be migrated to ``\\ref{key:label}`` via
``\\externaldocument[key:]{cascade-series-...}``.

The validator:
  1. Parses each ``src/cascade-series-*.tex`` file.
  2. Identifies cite keys whose ``\\bibitem`` entry is a cascade paper.
  3. Reports every body-text ``\\cite{}`` / ``\\nocite{}`` referencing such a
     key (commented-out citations and citations inside ``thebibliography`` are
     skipped).
  4. Exits 1 if any are found, with a per-file breakdown.

Run from the repo root:

    python3 tools/verifiers/check_xr_hyper_compliance.py

Or against an alternative source directory:

    python3 tools/verifiers/check_xr_hyper_compliance.py path/to/src
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SRC_DIR = REPO_ROOT / "src"

CITE_RE = re.compile(r"\\(?:cite|nocite)\{([^}]+)\}")
BIB_BLOCK_RE = re.compile(
    r"\\begin\{thebibliography\}.*?\\end\{thebibliography\}",
    re.DOTALL,
)
BIBITEM_MARKER_RE = re.compile(r"(\\bibitem\{[^}]+\})")
BIBITEM_KEY_RE = re.compile(r"\\bibitem\{([^}]+)\}")
LINE_COMMENT_RE = re.compile(r"(?<!\\)%")

# Distinctive substrings that appear in cascade-paper titles and subtitles.
# Different parts use different bibliography styles: some include "Cascade
# Series" in bibitem entries, others abbreviate to the subtitle. The set below
# is intentionally broad. Extend it when adding a new cascade paper whose
# title doesn't match an existing fragment.
CASCADE_TITLE_FRAGMENTS = (
    "cascade series",
    "from the cascade",
    "scale variance from orthogonality",
    "cosmological constant from the observer",
    "general relativity, four dimensions",
    "quantum gravity without quantising gravity",
    "tower growth",
    "why nothing has structure",
    "the infinite-dimensional unit ball",
)


def cascade_cite_keys(text: str) -> set[str]:
    """Return the cite keys whose ``\\bibitem`` entry names a cascade paper.

    A bibitem is treated as a cascade-paper entry if its body contains any of
    the distinctive title fragments listed in CASCADE_TITLE_FRAGMENTS.
    """
    block_match = BIB_BLOCK_RE.search(text)
    if not block_match:
        return set()
    block = block_match.group(0)
    # Split into [pre, '\bibitem{k1}', body1, '\bibitem{k2}', body2, ...].
    parts = BIBITEM_MARKER_RE.split(block)
    keys: set[str] = set()
    for marker, body in zip(parts[1::2], parts[2::2]):
        key_match = BIBITEM_KEY_RE.match(marker)
        if key_match is None:
            continue
        body_lower = body.lower()
        if any(frag in body_lower for frag in CASCADE_TITLE_FRAGMENTS):
            keys.add(key_match.group(1))
    return keys


def find_violations(path: Path) -> list[tuple[int, list[str], str]]:
    """Return list of (line_no, cascade_keys_in_cite, line_text)."""
    text = path.read_text(encoding="utf-8")
    cascade_keys = cascade_cite_keys(text)
    if not cascade_keys:
        return []

    bib_match = BIB_BLOCK_RE.search(text)
    bib_start = bib_match.start() if bib_match else len(text)

    violations: list[tuple[int, list[str], str]] = []
    char_pos = 0
    for line_no, raw_line in enumerate(text.splitlines(keepends=True), start=1):
        if char_pos >= bib_start:
            break
        # Strip the comment tail of the line, respecting escaped percents.
        comment_match = LINE_COMMENT_RE.search(raw_line)
        scanned = raw_line[: comment_match.start()] if comment_match else raw_line
        for cite_match in CITE_RE.finditer(scanned):
            keys = [k.strip() for k in cite_match.group(1).split(",") if k.strip()]
            cascade_in_cite = [k for k in keys if k in cascade_keys]
            if cascade_in_cite:
                violations.append(
                    (line_no, cascade_in_cite, raw_line.rstrip("\n").strip())
                )
        char_pos += len(raw_line)
    return violations


def display_path(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def main(argv: list[str]) -> int:
    src_dir = SRC_DIR if len(argv) <= 1 else Path(argv[1]).resolve()
    papers = sorted(src_dir.glob("cascade-series-*.tex"))
    if not papers:
        print(f"No cascade-series-*.tex files in {src_dir}", file=sys.stderr)
        return 1

    per_file: list[tuple[Path, list[tuple[int, list[str], str]]]] = []
    for paper in papers:
        per_file.append((paper, find_violations(paper)))

    total = sum(len(v) for _, v in per_file)
    files_with_hits = sum(1 for _, v in per_file if v)

    for paper, violations in per_file:
        rel = display_path(paper)
        if not violations:
            print(f"[OK]   {rel}: 0 cross-paper \\cite usages")
            continue
        print(f"[FAIL] {rel}: {len(violations)} cross-paper \\cite usages")
        for line_no, keys, snippet in violations:
            keys_str = ",".join(keys)
            display = snippet if len(snippet) <= 160 else snippet[:157] + "..."
            print(f"    L{line_no}: \\cite{{{keys_str}}}")
            print(f"        {display}")

    if total:
        print(
            f"\nFAIL: {total} cross-paper \\cite usages across "
            f"{files_with_hits}/{len(papers)} file(s).",
            file=sys.stderr,
        )
        print(
            "These cite keys point at other cascade papers and should be "
            "migrated to xr-hyper:",
            file=sys.stderr,
        )
        print(
            "    \\usepackage{xr-hyper}",
            file=sys.stderr,
        )
        print(
            "    \\externaldocument[<key>:]{cascade-series-<paper>}  "
            "% in the preamble",
            file=sys.stderr,
        )
        print(
            "    \\ref{<key>:<label>}                                "
            "% replaces \\cite{<key>}~Theorem~\\texttt{<label>}",
            file=sys.stderr,
        )
        return 1

    print(f"\nOK: no cross-paper \\cite usages in {len(papers)} file(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
