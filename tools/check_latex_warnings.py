#!/usr/bin/env python3
"""Fail CI when cascade LaTeX logs contain regressions.

Scans `src/*.log` for any of:
  * LaTeX errors (lines starting with "!")
  * Overfull hbox / vbox warnings
  * Undefined references, citations, or labels
  * Missing characters
  * Undefined control sequences

Underfull warnings are permitted (cosmetic only, used inside `\\resizebox`).

Exit 0 on clean logs; exit 1 with a per-paper summary otherwise.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

LOG_DIR = Path(__file__).resolve().parents[1] / "src" / "build"

# Patterns that count as a regression.
PATTERNS: dict[str, re.Pattern[str]] = {
    "error": re.compile(r"^! "),
    "overfull": re.compile(r"^Overfull \\[hv]box"),
    "undefined_ref": re.compile(
        r"Reference `[^']+' on page \d+ undefined"
        r"|LaTeX Warning: Reference `[^']+' .* undefined"
    ),
    "undefined_cite": re.compile(r"LaTeX Warning: Citation `[^']+' .* undefined"),
    "missing_char": re.compile(r"Missing character:"),
    "undefined_cs": re.compile(r"Undefined control sequence"),
}


def unwrap_tex_log(text: str, wrap_width: int = 79) -> str:
    """Join lines that TeX hard-wrapped at max_print_line.

    pdflatex wraps log output at $max_print_line (default 79) without any
    continuation marker. A warning like
        LaTeX Warning: Reference `rem:chirality-jacobian-separability' on page 1 undefined
    can split the word "undefined" across two lines, hiding it from
    line-by-line regex scans. We treat any line whose length is at least the
    wrap width as a candidate continuation and merge it with the next line.
    """
    lines = text.split("\n")
    merged: list[str] = []
    for line in lines:
        if merged and len(merged[-1]) >= wrap_width:
            merged[-1] += line
        else:
            merged.append(line)
    return "\n".join(merged)


def scan_log(path: Path) -> dict[str, list[str]]:
    findings: dict[str, list[str]] = {key: [] for key in PATTERNS}
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except FileNotFoundError:
        return findings
    text = unwrap_tex_log(text)
    for line in text.splitlines():
        for key, pattern in PATTERNS.items():
            if pattern.search(line):
                findings[key].append(line.strip())
    return findings


def main() -> int:
    if len(sys.argv) > 1:
        log_dir = Path(sys.argv[1])
    else:
        log_dir = LOG_DIR
    logs = sorted(log_dir.glob("cascade-series-*.log"))
    if not logs:
        print(f"No cascade-series-*.log files found in {log_dir}", file=sys.stderr)
        return 1

    had_regression = False
    for log in logs:
        findings = scan_log(log)
        total = sum(len(v) for v in findings.values())
        status = "OK" if total == 0 else "FAIL"
        counts = " ".join(f"{k}={len(v)}" for k, v in findings.items())
        print(f"[{status}] {log.name}: {counts}")
        if total:
            had_regression = True
            for key, items in findings.items():
                for item in items[:5]:
                    print(f"    {key}: {item}")
                if len(items) > 5:
                    print(f"    {key}: ... ({len(items) - 5} more)")

    if had_regression:
        print("\nLaTeX warning check FAILED. See per-paper detail above.", file=sys.stderr)
        return 1
    print("\nLaTeX warning check passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
