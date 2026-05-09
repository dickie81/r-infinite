#!/usr/bin/env python3
"""Fail when cross-paper references aren't routed through xr-hyper.

Three violation classes are flagged. A paper passes only when all three
are clean:

Layer A: ``\\cite{paperK}`` to a cascade paper, but the citing paper's
    preamble has no ``\\externaldocument[paperK:]{cascade-series-X}``.
    Bare cross-paper cites are only valid once xr-hyper is wired in for
    that key.

Layer B: ``\\texttt{prefix:label}`` within ~200 characters of a
    ``\\cite{paperK}`` to a cascade paper. These prose-label references
    must be migrated to ``\\ref{paperK:prefix:label}`` (the ``\\cite``
    stays; xr-hyper resolves the target's theorem/section number).

Layer C: ``\\bibitem{paperK}`` for a cascade paper, but the bibitem
    body has no ``\\extlink{\\cascadebase/cascade-series-<X>.pdf}{...}``
    wrap on the title. Each cascade-paper bibliography entry must be a
    clickable cross-PDF link to the target paper. The href target must
    be an *absolute* URL (built via the ``\\cascadebase`` macro) so
    that hyperref emits a ``URI`` PDF action -- the only action type
    browser PDF viewers will follow. Bare relative file targets like
    ``cascade-series-X.pdf`` produce ``GoToR`` / ``Launch`` actions
    that browsers strip for sandboxing, so the click does nothing.

The validator parses each ``src/cascade-series-*.tex`` file:
    1. Extracts the bibliography block and identifies cite keys whose
       ``\\bibitem`` body names a cascade paper (heuristic: the body
       contains one of CASCADE_TITLE_FRAGMENTS).
    2. Extracts the preamble (everything before ``\\begin{document}``)
       and reads ``\\externaldocument[KEY:]{file}`` declarations.
    3. Walks the document body (between the preamble and the
       bibliography), finding ``\\cite{}`` and ``\\nocite{}`` calls.
    4. For each cite-key referencing a cascade paper, emits Layer A,
       Layer B, and/or Layer C violations as appropriate.

LaTeX line comments (``%...``) are stripped per line before scanning.
Cites inside ``\\begin{thebibliography}...\\end{thebibliography}`` are
ignored.

Run from the repo root:

    python3 tools/build/check_xr_hyper_compliance.py

Or against an alternative source directory:

    python3 tools/build/check_xr_hyper_compliance.py path/to/src
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
PREAMBLE_END_RE = re.compile(r"\\begin\{document\}")
EXTERNAL_DOC_RE = re.compile(
    r"\\externaldocument\s*"
    r"(?:\[\s*([A-Za-z0-9_-]+)\s*:?\s*\])?"
    r"\s*\{([^}]+)\}"
)
# Cross-PDF link to a sibling cascade paper, written via the \extlink
# wrapper macro defined in each paper's preamble. \extlink expands to a
# blue-text \href with pdfborder suppressed; the validator treats it as
# the canonical bibitem link form.
HREF_CASCADE_PDF_RE = re.compile(
    r"\\extlink\{\\cascadebase/cascade-series-[A-Za-z0-9_-]+\.pdf\}"
)
# Cascade-style label: a typewritten string with a prefix:suffix shape and a
# prefix that matches the conventions used across the series.
LABEL_PREFIXES = (
    "thm", "lem", "cor", "prop", "def", "rem", "sec",
    "eq", "fig", "tab", "subsec", "ch",
)
TEXTTT_LABEL_RE = re.compile(
    r"\\texttt\{((?:" + "|".join(LABEL_PREFIXES) + r")(?::|\\text\{:\})[A-Za-z0-9_:.\\-]+)\}"
)

# Distinctive substrings that appear in cascade-paper titles and subtitles.
# Different parts use different bibliography styles: some include "Cascade
# Series" in bibitem entries, others abbreviate to the subtitle. The set
# below is intentionally broad. Extend it when adding a new cascade paper
# whose title doesn't match an existing fragment.
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

WINDOW_CHARS = 200


def split_preamble_body_bibliography(text: str) -> tuple[str, str, str]:
    """Return (preamble, body, bibliography). body excludes the bibliography."""
    pre_match = PREAMBLE_END_RE.search(text)
    preamble_end = pre_match.start() if pre_match else 0
    bib_match = BIB_BLOCK_RE.search(text)
    bib_start = bib_match.start() if bib_match else len(text)
    return text[:preamble_end], text[preamble_end:bib_start], text[bib_start:]


def cascade_cite_keys(bibliography: str) -> set[str]:
    """Cite keys whose ``\\bibitem`` entry names a cascade paper."""
    if not bibliography:
        return set()
    parts = BIBITEM_MARKER_RE.split(bibliography)
    keys: set[str] = set()
    for marker, body in zip(parts[1::2], parts[2::2]):
        key_match = BIBITEM_KEY_RE.match(marker)
        if key_match is None:
            continue
        body_lower = body.lower()
        if any(frag in body_lower for frag in CASCADE_TITLE_FRAGMENTS):
            keys.add(key_match.group(1))
    return keys


def xr_hyper_keys(preamble: str) -> set[str]:
    """Set of xr-hyper prefixes declared via ``\\externaldocument[KEY:]``."""
    keys: set[str] = set()
    for m in EXTERNAL_DOC_RE.finditer(preamble):
        prefix = m.group(1)
        if prefix:
            keys.add(prefix)
    return keys


def strip_line_comment(line: str) -> str:
    m = LINE_COMMENT_RE.search(line)
    return line[: m.start()] if m else line


def offset_to_line(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def cascade_bibitems_missing_href(
    bibliography: str, cascade_keys: set[str]
) -> list[tuple[int, str]]:
    """Return [(bib_offset, key)] for cascade-paper bibitems lacking a
    cross-PDF href.

    Each cascade-paper ``\\bibitem{paperK}`` body must contain a
    ``\\extlink{\\cascadebase/cascade-series-<X>.pdf}{...}`` wrap so the bibliography
    entry is a clickable cross-PDF link to the target paper.
    """
    if not bibliography:
        return []
    parts = BIBITEM_MARKER_RE.split(bibliography)
    # parts = [pre, marker_1, body_1, marker_2, body_2, ...]
    violations: list[tuple[int, str]] = []
    cursor = len(parts[0])
    for marker, body in zip(parts[1::2], parts[2::2]):
        marker_start = cursor
        cursor += len(marker) + len(body)
        key_match = BIBITEM_KEY_RE.match(marker)
        if key_match is None:
            continue
        key = key_match.group(1)
        if key not in cascade_keys:
            continue
        if not HREF_CASCADE_PDF_RE.search(body):
            violations.append((marker_start, key))
    return violations


def find_violations(
    path: Path,
) -> tuple[
    list[tuple[int, str, str]],
    list[tuple[int, str, str, str]],
    list[tuple[int, str]],
]:
    """Return (layer_a, layer_b, layer_c) violations.

    Layer A: list of (line_no, missing_xr_key, line_text).
    Layer B: list of (line_no, paper_key, label, snippet).
    Layer C: list of (line_no, paper_key) -- bibitem missing href wrap.
    """
    text = path.read_text(encoding="utf-8")
    preamble, body, bibliography = split_preamble_body_bibliography(text)

    cascade_keys = cascade_cite_keys(bibliography)
    if not cascade_keys:
        return [], [], []
    declared = xr_hyper_keys(preamble)
    # body is text[preamble_end:bib_start]; offset within body maps to line
    # number in the original file by adding the preamble length up front.
    body_offset = len(preamble)

    # Pre-compute a comment-stripped version of body, preserving char
    # positions (replace comment tail with spaces of equal length so offsets
    # into the original text still line up for windowing).
    cleaned_body_chars: list[str] = []
    for raw_line in body.splitlines(keepends=True):
        m = LINE_COMMENT_RE.search(raw_line)
        if m is None:
            cleaned_body_chars.append(raw_line)
        else:
            kept = raw_line[: m.start()]
            tail = raw_line[m.start():]
            # Replace comment characters with spaces, preserving newlines.
            tail_clean = re.sub(r"[^\n]", " ", tail)
            cleaned_body_chars.append(kept + tail_clean)
    cleaned_body = "".join(cleaned_body_chars)

    layer_a: list[tuple[int, str, str]] = []
    layer_b: list[tuple[int, str, str, str]] = []

    cite_matches = list(CITE_RE.finditer(cleaned_body))
    file_lines = text.splitlines()

    def line_and_snippet(offset: int) -> tuple[int, str]:
        line_no = offset_to_line(text, body_offset + offset)
        line_text = file_lines[line_no - 1].strip()
        snippet = line_text if len(line_text) <= 200 else line_text[:197] + "..."
        return line_no, snippet

    # Layer A: every cascade-paper key in every cite must have a declared
    # \externaldocument prefix in the citing paper's preamble.
    for cite_match in cite_matches:
        keys = [k.strip() for k in cite_match.group(1).split(",") if k.strip()]
        cascade_in_cite = [k for k in keys if k in cascade_keys]
        if not cascade_in_cite:
            continue
        line_no, snippet = line_and_snippet(cite_match.start())
        for key in cascade_in_cite:
            if key not in declared:
                layer_a.append((line_no, key, snippet))

    # Layer B: each cascade-style \texttt{prefix:label} is paired with its
    # *nearest* \cite within WINDOW_CHARS. Only that cite is held responsible
    # -- this avoids false positives from a label showing up in two cites'
    # overlapping windows.
    def cite_distance(label_match: re.Match[str], cite_match: re.Match[str]) -> int:
        if cite_match.end() <= label_match.start():
            return label_match.start() - cite_match.end()
        if cite_match.start() >= label_match.end():
            return cite_match.start() - label_match.end()
        return 0  # overlapping is impossible here but keep the branch safe

    for label_match in TEXTTT_LABEL_RE.finditer(cleaned_body):
        nearest: re.Match[str] | None = None
        nearest_dist = WINDOW_CHARS + 1
        for cite_match in cite_matches:
            d = cite_distance(label_match, cite_match)
            if d < nearest_dist:
                nearest_dist = d
                nearest = cite_match
        if nearest is None or nearest_dist > WINDOW_CHARS:
            continue
        keys = [k.strip() for k in nearest.group(1).split(",") if k.strip()]
        cascade_in_cite = [k for k in keys if k in cascade_keys]
        if not cascade_in_cite:
            continue
        label = label_match.group(1)
        line_no, snippet = line_and_snippet(label_match.start())
        for key in cascade_in_cite:
            layer_b.append((line_no, key, label, snippet))

    # Layer C: each cascade-paper bibitem must include a cross-PDF href
    # to the target paper.
    bib_match = BIB_BLOCK_RE.search(text)
    bib_offset = bib_match.start() if bib_match else len(text)
    layer_c: list[tuple[int, str]] = []
    for rel_offset, key in cascade_bibitems_missing_href(
        bibliography, cascade_keys
    ):
        line_no = offset_to_line(text, bib_offset + rel_offset)
        layer_c.append((line_no, key))

    return layer_a, layer_b, layer_c


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

    total_a = 0
    total_b = 0
    total_c = 0
    files_with_hits = 0

    for paper in papers:
        layer_a, layer_b, layer_c = find_violations(paper)
        rel = display_path(paper)
        if not (layer_a or layer_b or layer_c):
            print(f"[OK]   {rel}: no inter-paper references missing xr-hyper")
            continue
        files_with_hits += 1
        total_a += len(layer_a)
        total_b += len(layer_b)
        total_c += len(layer_c)
        print(
            f"[FAIL] {rel}: "
            f"{len(layer_a)} bare cite(s) without \\externaldocument, "
            f"{len(layer_b)} prose label(s) without \\ref, "
            f"{len(layer_c)} bibitem(s) without cross-PDF \\href"
        )
        # Layer A: deduplicate by (line, key) for compactness.
        seen_a: set[tuple[int, str]] = set()
        for line_no, key, snippet in layer_a:
            sig = (line_no, key)
            if sig in seen_a:
                continue
            seen_a.add(sig)
            print(f"    L{line_no}  [A]  \\cite{{{key}}} -- needs in preamble:")
            print(
                f"           \\externaldocument[{key}:]"
                f"{{cascade-series-<paperK>}}"
            )
            print(f"           {snippet}")
        # Layer B: deduplicate by (line, key, label).
        seen_b: set[tuple[int, str, str]] = set()
        for line_no, key, label, snippet in layer_b:
            sig = (line_no, key, label)
            if sig in seen_b:
                continue
            seen_b.add(sig)
            print(
                f"    L{line_no}  [B]  \\texttt{{{label}}} near "
                f"\\cite{{{key}}} -- replace with:"
            )
            print(f"           \\ref{{{key}:{label}}}")
            print(f"           {snippet}")
        # Layer C: deduplicate by (line, key).
        seen_c: set[tuple[int, str]] = set()
        for line_no, key in layer_c:
            sig = (line_no, key)
            if sig in seen_c:
                continue
            seen_c.add(sig)
            print(
                f"    L{line_no}  [C]  \\bibitem{{{key}}} -- "
                f"missing \\extlink{{\\cascadebase/cascade-series-<X>.pdf}}{{...}} wrap"
            )

    if total_a or total_b or total_c:
        print(
            f"\nFAIL: {total_a} Layer-A bare-cite, "
            f"{total_b} Layer-B prose-label, "
            f"{total_c} Layer-C bibitem-no-href violations across "
            f"{files_with_hits}/{len(papers)} file(s).",
            file=sys.stderr,
        )
        print(
            "Layer A: add to the citing paper's preamble (with \\usepackage{xr-hyper}):",
            file=sys.stderr,
        )
        print(
            "    \\externaldocument[paperK:]{cascade-series-<paperK>}",
            file=sys.stderr,
        )
        print(
            "Layer B: replace prose-label references with xr-hyper \\ref:",
            file=sys.stderr,
        )
        print(
            "    Theorem~\\texttt{thm:foo} of \\cite{paperK}  ->  "
            "Theorem~\\ref{paperK:thm:foo} of \\cite{paperK}",
            file=sys.stderr,
        )
        print(
            "Layer C: wrap each cascade-paper bibitem title in \\extlink"
            " (defined in each paper's preamble):",
            file=sys.stderr,
        )
        print(
            "    \\bibitem{paperK} ..., \\extlink{\\cascadebase/cascade-series-<X>.pdf}"
            "{\\textit{Title of paperK}}, ...",
            file=sys.stderr,
        )
        return 1

    print(f"\nOK: no missing xr-hyper coverage across {len(papers)} file(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
