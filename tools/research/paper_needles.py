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
import ast
import re

def var_forms(src):
    """Per-file paper-variable -> form map, derived from the
    ACTUAL read transforms (round-264: a name map alone
    mislabels e.g. quarter_square's raw paper_raw). Recognized
    assignment styles (the codebase's only ones):
      X = open(PAPER...).read()                  -> raw
      X = norm(open(PAPER...).read())            -> ws
      X = norm(open(PAPER...).read()).replace("**", "") -> plain
      X = norm(<rawvar>).replace("**", "")       -> plain
      X = re.sub(r"\s+", " ", <rawvar>)         -> ws
      X = <wsvar>.replace("**", "")              -> plain
    Anything else touching PAPER is left unmapped -- the
    harvester then reports it as complex."""
    out = {}
    for line in src.split("\n"):
        m = re.match(r"(\w+) = open\(PAPER.*\.read\(\)\s*$", line)
        if m:
            out[m.group(1)] = "raw"
            continue
        m = re.match(r'(\w+) = norm\(open\(PAPER.*\)\)\.replace\("\*\*", ""\)', line)
        if m:
            out[m.group(1)] = "plain"
            continue
        m = re.match(r"(\w+) = norm\(open\(PAPER.*\)\)\s*(#.*)?$", line)
        if m:
            out[m.group(1)] = "ws"
            continue
        m = re.match(r'(\w+) = norm\((\w+)\)\.replace\("\*\*", ""\)', line)
        if m and out.get(m.group(2)) == "raw":
            out[m.group(1)] = "plain"
            continue
        m = re.match(r'(\w+) = re\.sub\(r"\\s\+", " ", (\w+)\)', line)
        if m and out.get(m.group(2)) == "raw":
            out[m.group(1)] = "ws"
            continue
        m = re.match(r'(\w+) = (\w+)\.replace\("\*\*", ""\)', line)
        if m and out.get(m.group(2)) == "ws":
            out[m.group(1)] = "plain"
    return out


def harvest(tree, vf):
    """AST-harvest every inline paper-compare from a module tree
    (round-264 F264-1: the mirror meta-gate's extraction side).
    Recognized idioms, matching the codebase's historical forms:
      "needle" in <papervar>            -> (s, form, min 1, None)
      <papervar>.count("needle") >= n   -> (s, form, n, None)
      <papervar>.count("needle") == n   -> (s, form, n, n)
    Returns (reqs, complex_nodes): reqs are requirement tuples
    (s, form, min, max); complex_nodes lists line numbers of any
    OTHER expression touching a paper variable inside a Compare
    (e.g. .find position logic) -- the caller must treat those as
    non-harvestable and demand full conversion."""
    reqs, cplx = [], []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Compare) or len(node.ops) != 1:
            continue
        op = node.ops[0]
        L, R = node.left, node.comparators[0]
        if (isinstance(op, (ast.In, ast.NotIn))
                and isinstance(L, ast.Constant)
                and isinstance(L.value, str)
                and isinstance(R, ast.Name)
                and R.id in vf):
            if isinstance(op, ast.In):
                reqs.append((L.value, vf[R.id], 1, None))
            else:
                cplx.append(node.lineno)
        elif (isinstance(L, ast.Call)
                and isinstance(L.func, ast.Attribute)
                and L.func.attr == "count"
                and isinstance(L.func.value, ast.Name)
                and L.func.value.id in vf
                and len(L.args) == 1
                and isinstance(L.args[0], ast.Constant)
                and isinstance(R, ast.Constant)):
            s = L.args[0].value
            f = vf[L.func.value.id]
            n = R.value
            if isinstance(op, ast.GtE):
                reqs.append((s, f, n, None))
            elif isinstance(op, ast.Eq):
                reqs.append((s, f, n, n))
            else:
                cplx.append(node.lineno)
        else:
            for sub in ast.walk(node):
                if isinstance(sub, ast.Name) and sub.id in vf:
                    cplx.append(node.lineno)
                    break
    return reqs, cplx


def covers(decl, reqs):
    """Does the declared surface entail every harvested inline
    requirement?  A requirement (s, form, lo, hi) is covered by a
    declared entry with the same s and form whose min >= lo and
    (if hi is not None) whose max == hi.  Returns the uncovered
    list."""
    unc = []
    for s, f, lo, hi in reqs:
        ok = False
        for d in decl:
            if "seq" in d:
                continue
            if (d["s"] == s and d.get("form", "raw") == f
                    and d.get("min", 1) >= lo
                    and (hi is None or d.get("max") == hi)):
                ok = True
                break
        if not ok:
            unc.append((s, f, lo, hi))
    return unc


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
        # schema validation (round-264 F264-4): an unknown form
        # or malformed entry is a MISS with a reason, never an
        # uncaught exception inside the precheck
        f = d.get("form", "raw")
        if f not in fv or ("s" not in d and "seq" not in d):
            misses.append((d, "bad-entry"))
            continue
        body = fv[f]
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
