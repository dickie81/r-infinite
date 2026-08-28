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

def _is_paper_read(n):
    """open(PAPER).read() or open(PAPER, encoding="utf-8").read()
    -- EXACTLY (round-267 F267-3: the first version never examined
    the inner open()'s keywords or extra positionals, so an
    encoding swap mapped as a clean read while the member decoded
    different bytes). No extra args, keywords, or call layers
    anywhere in the shape."""
    if not (isinstance(n, ast.Call) and not n.args and not n.keywords
            and isinstance(n.func, ast.Attribute)
            and n.func.attr == "read"
            and isinstance(n.func.value, ast.Call)
            and isinstance(n.func.value.func, ast.Name)
            and n.func.value.func.id == "open"):
        return False
    op = n.func.value
    if (len(op.args) != 1 or not isinstance(op.args[0], ast.Name)
            or op.args[0].id != "PAPER"):
        return False
    if not op.keywords:
        return True
    return (len(op.keywords) == 1
            and op.keywords[0].arg == "encoding"
            and isinstance(op.keywords[0].value, ast.Constant)
            and op.keywords[0].value.value == "utf-8")


def _is_norm(n):
    """norm(X) -- exactly one positional argument. The CALL shape
    only; var_forms additionally verifies the file's norm
    DEFINITION is canonical (round-267 F267-4)."""
    return (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
            and n.func.id == "norm" and len(n.args) == 1
            and not n.keywords)


def shadow_bound(tree, names):
    """True if any RAW-STRING binding form binds one of `names`
    (round-273 F273-1: Python binds names through constructs
    whose target is a plain str, invisible to Name-node walks --
    function/lambda parameters, except-as, match-case captures
    -- and `from m import *` binds opaquely). The canon guards
    (_norm_canonical here; _gate_print_canonical in the driver)
    refuse their sanction whenever one of these binds a guarded
    name: a parameter shadow routed a sanctioned evidence
    f-string into a rogue callee in the round-273 demonstration."""
    names = set(names)
    for n in ast.walk(tree):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.Lambda)):
            a = n.args
            ps = (list(a.posonlyargs) + list(a.args)
                  + list(a.kwonlyargs))
            if a.vararg:
                ps.append(a.vararg)
            if a.kwarg:
                ps.append(a.kwarg)
            if any(p.arg in names for p in ps):
                return True
        elif isinstance(n, ast.ExceptHandler):
            if n.name in names:
                return True
        elif isinstance(n, ast.MatchAs):
            if n.name in names:
                return True
        elif isinstance(n, ast.MatchStar):
            if n.name in names:
                return True
        elif isinstance(n, ast.MatchMapping):
            if n.rest in names:
                return True
        elif isinstance(n, (ast.Import, ast.ImportFrom)):
            if any(x.name == "*" for x in n.names):
                return True
    return False


def _norm_canonical(tree):
    """True iff every FunctionDef named `norm` in the tree is
    EXACTLY the codebase's canonical whitespace collapse,
    `return " ".join(s.split())` (round-267 F267-4: the shape
    rules trusted the NAME norm, so a rogue norm body silently
    mislabeled every downstream form; the definition is now part
    of the matched shape -- a file with a non-canonical or absent
    norm gets no norm-based mappings, and its reads then trip the
    driver's clause (v))."""
    # round-268 F268-3: a canonical def can be SHADOWED at runtime
    # by any other binding of the name (norm = lambda ...,
    # import ... as norm) -- the def then stands as camouflage
    # while the effective transform diverges. Any non-FunctionDef
    # binding of the name refuses all norm-based mappings.
    if shadow_bound(tree, ("norm",)):
        return False
    for n in ast.walk(tree):
        if (isinstance(n, ast.Name) and n.id == "norm"
                and isinstance(n.ctx, (ast.Store, ast.Del))):
            return False
        if isinstance(n, (ast.Import, ast.ImportFrom)):
            for a in n.names:
                if (a.asname or a.name.split(".")[0]) == "norm":
                    return False
        # round-272 F272-2: class and async-def bindings of the
        # name are shadows too -- the FunctionDef-only scan let
        # `class norm` / `async def norm` stand as camouflage
        if (isinstance(n, (ast.AsyncFunctionDef, ast.ClassDef))
                and n.name == "norm"):
            return False
        if (isinstance(n, ast.FunctionDef) and n.name == "norm"
                and any(isinstance(d, ast.expr)
                        for d in n.decorator_list)):
            return False
    found = False
    for n in ast.walk(tree):
        if not (isinstance(n, ast.FunctionDef) and n.name == "norm"):
            continue
        found = True
        body = [b for b in n.body
                if not (isinstance(b, ast.Expr)
                        and isinstance(b.value, ast.Constant)
                        and isinstance(b.value.value, str))]
        if len(n.args.args) != 1 or len(body) != 1:
            return False
        r = body[0]
        arg = n.args.args[0].arg
        if not (isinstance(r, ast.Return)
                and isinstance(r.value, ast.Call)
                and not r.value.keywords
                and len(r.value.args) == 1
                and isinstance(r.value.func, ast.Attribute)
                and r.value.func.attr == "join"
                and isinstance(r.value.func.value, ast.Constant)
                and r.value.func.value.value == " "):
            return False
        c = r.value.args[0]
        if not (isinstance(c, ast.Call) and not c.args
                and not c.keywords
                and isinstance(c.func, ast.Attribute)
                and c.func.attr == "split"
                and isinstance(c.func.value, ast.Name)
                and c.func.value.id == arg):
            return False
    return found


def _is_star_strip(n):
    """X.replace("**", "") -- exactly."""
    return (isinstance(n, ast.Call)
            and isinstance(n.func, ast.Attribute)
            and n.func.attr == "replace" and not n.keywords
            and len(n.args) == 2
            and isinstance(n.args[0], ast.Constant)
            and n.args[0].value == "**"
            and isinstance(n.args[1], ast.Constant)
            and n.args[1].value == "")


def var_forms(src):
    """Per-file paper-variable -> form map, derived from the
    ACTUAL read transforms (round-264: a name map alone
    mislabels e.g. quarter_square's raw paper_raw). Recognized
    assignment shapes (the codebase's only ones):
      X = open(PAPER...).read()                  -> raw
      X = norm(open(PAPER...).read())            -> ws
      X = norm(open(PAPER...).read()).replace("**", "") -> plain
      X = norm(<rawvar>).replace("**", "")       -> plain
      X = re.sub(r"\s+", " ", <rawvar>)         -> ws
      X = <wsvar>.replace("**", "")              -> plain
    Matching is by EXACT AST shape on single-target assignments
    (round-266 F266-2/F266-3: the earlier line-regex ladder was
    fooled by an INFIX mutation inside the greedy open(PAPER...)
    span, and by a phantom mapping line sitting inside a
    docstring -- AST shapes admit neither: string content is
    never scanned, and any extra call layer, argument, or keyword
    anywhere in the shape fails the match, the inner open()'s
    encoding included, F267-3). Assignments anywhere in the tree
    are eligible, walked in line order (round-267: cascade_tower
    reads inside a function); norm-based rules require the file's
    norm DEFINITION to be canonical (F267-4). Anything else
    touching PAPER is left unmapped -- an unmapped variable's
    loads are then flagged by the harvester (inside compares) or
    by the driver's clauses (iii)/(v) (everywhere else)."""
    vf, _nodes = var_form_nodes(ast.parse(src))
    return vf


def var_form_nodes(tree):
    """The node-identity form of var_forms (round-268 F268-1:
    the driver's creation census keyed on target NAMES, so a
    later REBIND of a mapped name -- an arbitrary unrecognized
    transform -- was counted as a creation and its loads
    sanctioned; creation membership must be the recognized
    Assign NODES themselves). Returns (vf, node_ids) where vf is
    the name->form map and node_ids is the set of id(node) for
    exactly the recognized creation Assigns. A name mapped more
    than once (even by two recognized shapes -- the map is
    flow-insensitive, so a second binding would let compares
    before and after it disagree about the form) is DROPPED from
    vf and contributes no recognized nodes; the driver then
    flags every binding and load of it."""
    out, nodes, dup = {}, {}, set()
    norm_ok = _norm_canonical(tree)
    assigns = sorted((n for n in ast.walk(tree)
                      if isinstance(n, ast.Assign)),
                     key=lambda n: n.lineno)
    for node in assigns:
        if (len(node.targets) != 1
                or not isinstance(node.targets[0], ast.Name)):
            continue
        tgt, v = node.targets[0].id, node.value
        form = None
        if _is_paper_read(v):
            form = "raw"
        elif norm_ok and _is_norm(v) and _is_paper_read(v.args[0]):
            form = "ws"
        elif (norm_ok and _is_star_strip(v)
                and _is_norm(v.func.value)
                and _is_paper_read(v.func.value.args[0])):
            form = "plain"
        elif (norm_ok and _is_star_strip(v)
                and _is_norm(v.func.value)
                and isinstance(v.func.value.args[0], ast.Name)
                and out.get(v.func.value.args[0].id) == "raw"):
            form = "plain"
        elif (isinstance(v, ast.Call) and not v.keywords
                and isinstance(v.func, ast.Attribute)
                and v.func.attr == "sub"
                and isinstance(v.func.value, ast.Name)
                and v.func.value.id == "re"
                and len(v.args) == 3
                and isinstance(v.args[0], ast.Constant)
                and v.args[0].value == r"\s+"
                and isinstance(v.args[1], ast.Constant)
                and v.args[1].value == " "
                and isinstance(v.args[2], ast.Name)
                and out.get(v.args[2].id) == "raw"):
            form = "ws"
        elif (_is_star_strip(v)
                and isinstance(v.func.value, ast.Name)
                and out.get(v.func.value.id) == "ws"):
            form = "plain"
        if form is not None:
            if tgt in out:
                dup.add(tgt)
            else:
                out[tgt] = form
                nodes[tgt] = id(node)
    for tgt in dup:
        out.pop(tgt, None)
        nodes.pop(tgt, None)
    return out, set(nodes.values())


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
        if not isinstance(node, ast.Compare):
            continue
        if len(node.ops) != 1:
            # round-265 F265-1: a CHAINED compare touching a paper
            # variable is unclassifiable and must be flagged, not
            # skipped -- the skip made "unharvestable is a hard
            # failure" false for this node shape
            for sub in ast.walk(node):
                if isinstance(sub, ast.Name) and sub.id in vf:
                    cplx.append(node.lineno)
                    break
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


_FORMS = ("raw", "ws", "plain")


def valid(d):
    """The shared schema predicate (round-266 F266-1: check()
    validated entries but covers() then crashed on the same
    malformed decl -- both callers now share this). Well-formed:
    a dict carrying exactly one of a non-empty string "s" or a
    non-empty list-of-non-empty-strings "seq"; a known form;
    non-negative int min; int max >= min when present (bools
    rejected). The non-empty and min<=max clauses also close the
    round-266 F266-5 degenerate always-pass shapes (empty
    needle, negative min, s+seq co-presence)."""
    if not isinstance(d, dict):
        return False
    # key whitelist (round-267 F267-6): 'g' and 'key' are the two
    # load-bearing caller tags; anything else -- e.g. a mistyped
    # 'frm' -- would silently fall back to defaults
    if any(k not in ("s", "seq", "form", "min", "max", "g", "key")
           for k in d):
        return False
    f = d.get("form", "raw")
    sv, sq = d.get("s"), d.get("seq")
    lo, hi = d.get("min", 1), d.get("max")
    if f not in _FORMS:
        return False
    # round-267 F267-5: min 0 with no max can never miss -- the
    # absence pattern must pin max (canonically {"min":0,"max":0})
    if lo == 0 and hi is None:
        return False
    if (sv is None) == (sq is None):
        return False
    if sv is not None and (not isinstance(sv, str) or not sv):
        return False
    if sq is not None and (not isinstance(sq, list) or not sq
                           or any(not isinstance(x, str) or not x
                                  for x in sq)):
        return False
    # round-268 F268-5: min/max on a seq entry are silently
    # ignored by check() -- reject the co-presence so a bound
    # someone believes is enforced cannot ride along dead
    if sq is not None and ("min" in d or "max" in d):
        return False
    if not isinstance(lo, int) or isinstance(lo, bool) or lo < 0:
        return False
    if hi is not None and (not isinstance(hi, int)
                           or isinstance(hi, bool) or hi < lo):
        return False
    return True


def covers(decl, reqs):
    """Does the declared surface entail every harvested inline
    requirement?  A requirement (s, form, lo, hi) is covered by a
    declared entry with the same s and form whose min >= lo and
    (if hi is not None) whose max == hi.  Returns the uncovered
    list.  Malformed entries are skipped (round-266 F266-1: they
    can never cover anything, and check() already reports each of
    them as a bad-entry miss); a non-list decl covers nothing."""
    unc = []
    if not isinstance(decl, list):
        decl = []
    for s, f, lo, hi in reqs:
        ok = False
        for d in decl:
            if not valid(d) or "seq" in d:
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
    # schema validation (round-264 F264-4; completed round-265
    # F265-4; shared with covers() round-266 F266-1): a malformed
    # declaration or entry of ANY shape is a MISS with a reason,
    # never an uncaught exception inside the precheck
    if not isinstance(decl, list):
        return False, [(decl, "bad-decl")]
    misses = []
    for d in decl:
        if not valid(d):
            misses.append((d, "bad-entry"))
            continue
        f = d.get("form", "raw")
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
