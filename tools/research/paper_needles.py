#!/usr/bin/env python3
"""THE PAPER-NEEDLE PRECHECK (owner-commissioned, A397): the
single shared implementation of paper-needle evaluation, consumed
by BOTH every tower member's own gate AND run_tower's live
precheck, so a member's paper-dependence factors entirely through
its declared needle data and the driver can re-verify it live
without running the member.

THE CONTRACT. A member declares one module-level PURE-LITERAL
constant:

    PAPER_NEEDLES = [
        {"s": "some raw substring", "form": "raw", "min": 1},
        {"s": "`script.py`",        "form": "raw", "min": 2},
        {"s": "whitespace-collapsed text", "form": "ws"},
        {"s": "bold-stripped text",       "form": "plain"},
    ]

- "form": "raw" matches/counts against the paper bytes as read
  (utf-8 text); "ws" against re.sub(r"\\s+", " ", paper); "plain"
  against the ws form with every "**" removed. These are exactly
  the three historical member conventions (the inline `nd in
  paper`, the `normp`, and the `plain` styles).
- "min" (default 1): paper.count(needle) >= min in the stated
  form. A needle asserting absence is {"min": 0, "max": 0}; "max"
  (default None) upper-bounds the count when present.
- The literal must be AST-extractable (no computed entries): the
  driver reads it WITHOUT executing the member.

check(decl, paper) returns (ok, misses): misses lists every
failing entry with its observed count -- both callers print them.

WHY THIS EXISTS (the round-254 manifest precedent, applied to the
paper): with every member's paper consumption factored through
declared data, run_tower re-evaluates all declared needles LIVE
on each invocation and PAPER_SHA can leave the member cache key
-- a paper-prose edit then costs seconds (the precheck) instead
of a 19-member live tower, while a paper edit that breaks any
needle still fails the tower BEFORE any cached PASS is served.
The soundness burden moves to the closure property "the member
touches the paper ONLY through its declared needles", which
run_tower's meta-gate enforces by AST scan (no `in paper` /
`paper.count` expressions outside this module, exactly one
PAPER_NEEDLES literal per member).
"""
import re


def forms(paper):
    """The three normalized views, computed once per caller."""
    ws = re.sub(r"\s+", " ", paper)
    return {"raw": paper, "ws": ws, "plain": ws.replace("**", "")}


def check(decl, paper, pre=None):
    """Evaluate declared needles. Returns (ok, misses); misses
    entries are (needle-dict, observed-count).

    Entry kinds:
    - {"s": needle, "form": F, "min": m, "max": M} -- count
      bounds, as documented above.
    - {"seq": [n1, n2, ...], "form": F} -- a SKELETON CHAIN
      (the lattice_forcing round-187 position gate): every ni
      present and their FIRST occurrences strictly increasing;
      the miss records the offending index positions."""
    fv = pre if pre is not None else forms(paper)
    misses = []
    for d in decl:
        body = fv[d.get("form", "raw")]
        if "seq" in d:
            pos = [body.find(s) for s in d["seq"]]
            okd = all(p >= 0 for p in pos) and \
                all(a < b for a, b in zip(pos, pos[1:]))
            if not okd:
                misses.append((d, pos))
            continue
        n = body.count(d["s"])
        lo = d.get("min", 1)
        hi = d.get("max")
        if n < lo or (hi is not None and n > hi):
            misses.append((d, n))
    return (not misses), misses
