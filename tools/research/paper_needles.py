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
surface. (Round-277 F276-1 struck the first version's "internals
reachable only by computed spelling": the sanctioned function
objects' __globals__ and alternate import spellings of this file
reached the text plainly; the driver now requires the three
attributes to be immediately called, forbids any import or
constant naming this module beyond the exact plain import, and
forbids introspection dunder attributes reach-wide.) The
disclosed evasion class is spellings that never write the module
name or the filename as one constant and never touch a dunder:
string arithmetic, getattr with a computed name, exec/eval,
filesystem enumeration, sys.path-fed computed imports (F268-4):
drift detection, not a semantic proof.
"""
import ast
import copy
import json
import os
import re
import subprocess
import sys

# captured at import: the interpreter and this file, for the child.
# The paper's path is NOT a parent-module constant (round 278):
# it is computed only inside the child, so a member enumerating
# loaded modules finds no path to read.
_PY = sys.executable
_SELF = os.path.abspath(__file__)


def _eval_child(payload):
    """Round-278 (F277-1): the paper is read and the entries are
    evaluated in an ISOLATED CHILD PROCESS (-I: no PYTHONPATH, no
    user site, no cwd on sys.path; a scrubbed environment), so no
    paper text ever exists in the member's process -- hooks on
    re/open, trace/profile/audit hooks, and sys.modules/globals/gc
    enumeration in the member find nothing. The child returns
    (ok, misses) as JSON; misses carry the member's own entries
    and observed counts, never text."""
    r = subprocess.run([_PY, "-I", _SELF, "--eval"],
                       input=json.dumps(payload), capture_output=True,
                       text=True, timeout=300,
                       env={"PATH": os.environ.get("PATH", "")})
    if r.returncode != 0:
        raise RuntimeError("paper_needles child failed: "
                           + r.stderr[-500:])
    out = json.loads(r.stdout)
    return bool(out["ok"]), [(d, n) for d, n in out["misses"]]


def _select(decl, g=None, seq=False):
    sub = decl
    if g is not None:
        sub = [d for d in decl if isinstance(d, dict) and d.get("g") == g]
    if seq:
        sub = [d for d in sub if isinstance(d, dict) and "seq" in d]
    return sub


def verify(decl, g=None, seq=False):
    """Evaluate the declared entries (all; or those tagged g; or
    the skeleton chains when seq=True) against the paper, in the
    isolated child. Returns (ok, misses) exactly as check() does;
    no paper text enters the caller's process."""
    if not isinstance(decl, list):
        return False, [(decl, "bad-decl")]
    return _eval_child({"decl": _select(decl, g, seq)})


def needle(decl, s, form):
    """The single-needle gate: every declared entry with this
    (s, form) holds, evaluated in the isolated child. Undeclared
    (s, form) raises KeyError -- a member cannot consume a needle
    it did not declare."""
    hits = [d for d in decl if isinstance(d, dict)
            and d.get("s") == s and d.get("form", "raw") == form]
    if not hits:
        raise KeyError((s, form))
    ok, _ = _eval_child({"decl": hits})
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



def _child_main():
    """--eval: read the declared entries from stdin (JSON), read
    the paper, evaluate, print (ok, misses) as JSON. Runs only in
    the isolated child; the parent never calls check() on text."""
    payload = json.load(sys.stdin)
    paper_path = os.path.join(os.path.dirname(_SELF), "..", "..",
                              "riemann-indistinguishability.md")
    text = open(paper_path, encoding="utf-8").read()
    ok, misses = check(payload["decl"], text)
    json.dump({"ok": ok, "misses": [[d, n] for d, n in misses]},
              sys.stdout)


if __name__ == "__main__" and "--eval" in sys.argv:
    _child_main()
