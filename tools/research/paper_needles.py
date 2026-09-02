#!/usr/bin/env python3
"""THE PAPER-NEEDLE MODULE (owner-commissioned, A397; restructured
round 275 F275-1, owner's decision: MEMBERS NEVER HOLD PAPER TEXT).

This module is the ONLY code in any tower member's reach that
reads the paper. A member declares one module-level PURE-LITERAL
constant and consumes the paper through exactly two calls:

    PAPER_NEEDLES = [
        {"g": "g8", "s": "some raw substring", "form": "raw", "min": 1},
        {"g": "g8", "s": "whitespace-collapsed text", "form": "ws"},
        {"g": "g9", "s": "bold-stripped text", "form": "plain"},
        {"g": "g9", "form": "plain", "seq": ["first", "then"]},
    ]
    ok, misses = paper_needles.verify(PAPER_NEEDLES, g="g8")
    ok = paper_needles.needle(PAPER_NEEDLES, "bold-stripped text", "plain")
    for d in paper_needles.declared(PAPER_NEEDLES): ...   # read-only copies

- verify(decl, g=None, seq=False) evaluates the declared entries
  (all of them; those tagged g; or the skeleton chains) against
  the paper this module reads itself, returning (ok, misses) --
  misses lists (entry, observed) for every failing entry; no
  paper bytes are returned.
- needle(decl, s, form) evaluates every declared entry with that
  (s, form) -- a bool; an undeclared (s, form) raises KeyError,
  so a member cannot test a needle it did not declare.
- declared(decl) returns DEEP COPIES of the entries for read-only
  inspection (a member may cross-check its own declaration --
  cascade_tower's manifest census -- without holding a handle to
  the objects verify/needle evaluate; the driver forbids every
  other Load of PAPER_NEEDLES, since a loop variable over the
  live list is a mutation handle: round-275 route (d)).
- "form": "raw" matches the paper bytes as read (utf-8 text);
  "ws" the whitespace-collapsed text (re.sub(r"\\s+", " "));
  "plain" the ws form with every "**" removed.
- "min" (default 1) / "max" (default None) bound the count;
  absence is {"min": 0, "max": 0}.
- The literal must be AST-extractable (no computed entries): the
  driver reads it WITHOUT executing the member.

WHY THIS SHAPE (round 275). Rounds 264-274 policed member-side
paper reads with named AST clauses (read shapes, transform
assignments, harvested compares, sanctioned call subtrees,
evidence f-strings, canon gate shapes, binding-form walks) and
found a new plainly-spelled stale-cached-PASS route in every
round: a static walk over a Turing-complete member cannot bound
what a member does with paper text it holds. The closure property
is now STRUCTURAL: no member holds paper text, so there is no
text to launder, mirror, mutate, or route. run_tower's precheck
enforces the shape statically (no paper-naming constant anywhere
in the reach; this module used only through verify/needle/declared
on the declared literal; the literal bound once and never mutated) and
re-evaluates every declaration LIVE on every invocation, so a
paper edit either flips a declared needle -- failing the tower
before any cached PASS is served -- or changes no declared
surface. Computed spellings (getattr/importlib/exec/sys.modules
lookups of this module's internals) remain the disclosed
out-of-scope evasion class (F268-4): drift detection, not a
semantic proof.
"""
import ast
import copy
import os
import re

PAPER_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          "..", "..", "riemann-indistinguishability.md")
_TEXTCACHE = None
_FORMCACHE = None


def _forms_cached():
    global _TEXTCACHE, _FORMCACHE
    if _FORMCACHE is None:
        _TEXTCACHE = open(PAPER_PATH, encoding="utf-8").read()
        _FORMCACHE = forms(_TEXTCACHE)
    return _FORMCACHE


def verify(decl, g=None, seq=False):
    """Evaluate the declared entries (all; or those tagged g; or
    the skeleton chains when seq=True) against the paper this
    module reads. Returns (ok, misses) exactly as check() does;
    no paper text leaves this module."""
    if not isinstance(decl, list):
        return False, [(decl, "bad-decl")]
    sub = decl
    if g is not None:
        sub = [d for d in decl if isinstance(d, dict) and d.get("g") == g]
    if seq:
        sub = [d for d in sub if isinstance(d, dict) and "seq" in d]
    return check(sub, None, pre=_forms_cached())


def needle(decl, s, form):
    """The single-needle gate: every declared entry with this
    (s, form) holds. Undeclared (s, form) raises KeyError -- a
    member cannot consume a needle it did not declare."""
    hits = [d for d in decl if isinstance(d, dict)
            and d.get("s") == s and d.get("form", "raw") == form]
    if not hits:
        raise KeyError((s, form))
    ok, _ = check(hits, None, pre=_forms_cached())
    return ok


def declared(decl):
    """Read-only DEEP COPIES of the declared entries (round 275):
    inspection without a handle to the live declaration."""
    return tuple(copy.deepcopy(d) for d in decl)


_FORMS = ("raw", "ws", "plain")

_TYPEPARAM_NODES = tuple(
    getattr(ast, k) for k in ("TypeVar", "ParamSpec", "TypeVarTuple")
    if hasattr(ast, k)) or (type(None),)

def shadow_bound(tree, names):
    """True if any RAW-STRING binding form binds one of `names`
    (round-273 F273-1: Python binds names through constructs
    whose target is a plain str, invisible to Name-node walks --
    function/lambda parameters, except-as, match-case captures
    -- and `from m import *` binds opaquely). _norm_canonical
    refuses its norm mappings whenever one of these binds norm
    (the driver's gate/print guard that also consumed this was
    retired at round 274 with the evidence-f-string sanction).
    Round-274 F274-3: PEP 695 type-parameter names (3.12+
    TypeVar/ParamSpec/TypeVarTuple, raw-string names) are
    enumerated too when the running grammar has them."""
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
        elif isinstance(n, _TYPEPARAM_NODES):
            if getattr(n, "name", None) in names:
                return True
    return False

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
