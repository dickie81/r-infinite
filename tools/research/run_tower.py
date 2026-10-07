#!/usr/bin/env python3
"""The parallel tower driver: execute EVERY tower verifier concurrently
(each in manifest chain mode, so no serial recursion), and pass iff all
pass. This is the full-re-execution battery for certification rounds --
wall time = the longest single verifier instead of the serial sum.
Manifest-vs-disk integrity is checked for all members up front.

RESUME CACHE (round 252, owner-commissioned; key hardened round 253
F253-1; EXECUTABLE-CONTENT keying round 254, owner: "no executable
code changes... this should not invalidate cache" -- the round-245
oneprime decision applied one layer up): each member's PASS is
recorded in checkpoints/tower_results.json under a key binding
  code_sha(member) + code_sha(every file in the member's COMPUTED
  transitive local import closure) + sha256(the paper),
where the closure is the member's full code REACH, iterated to a
TRUE fixed point over BOTH expansions of every reached file: its
import step, and every code file named by a string constant in
its docstring-stripped AST -- bare .py names AND module stems
(spawns built as s + ".py") resolved against every code root
(tools/research and tools/verifiers), AND .tex names resolved
against src/ (round-257 F257-1: needle-gated tex substrates are
verdict inputs, byte-bound like the paper) -- the subprocess/
chain/needle reach the import walk cannot see (rounds 255-257);
imports resolve against the file's own directory AND every code
root (F257-2); code_sha is ckpt_key's docstring-stripped-AST
hash for .py, raw bytes for the tex substrates. Prose edits to members or their
.py substrates do NOT invalidate; any executable change anywhere
in the member's code reach does (the named-.py rule
over-approximates deliberately: over-invalidation, never a stale
PASS); tex substrates, like the paper, are byte-bound -- ANY tex
edit, prose included, rotates every key that reaches it (round-258
F258-1: needle gates match raw tex substrings, so no
prose/executable distinction exists there). The
PAPER left the key at the A397 arc: every member's paper surface
is one declared PAPER_NEEDLES literal, AST-extracted and
re-evaluated LIVE by this driver's needle precheck on every
invocation -- reach-wide (round-264 F264-1: spawned chain
scripts consume the paper too). Since round 275 (F275-1, owner's
decision) MEMBERS NEVER HOLD PAPER TEXT: paper_needles.py is the
only reader in any reach, consumed through verify/needle on the
declared literal, and the closure meta-gate enforces that SHAPE
statically (see the precheck block; drift detection, not a
semantic proof) -- so a paper edit either flips a declared
needle, failing the precheck before any cached PASS is served,
or changes no declared surface. A
paper-prose edit now costs the precheck, not a live tower. The manifest sha is NOT in
the key (round 254): manifest-vs-disk consistency is re-verified
LIVE by this driver's integrity precheck on every invocation, so
binding it would only re-import byte sensitivity. NOT bound:
committed checkpoint DATA files -- their producing CODE is in the
reach (the instruments' own keying binds code, not state bytes,
and the zeros cache is anchor-validated, not content-addressed);
every gate re-runs live on every non-cached run; data-only
corruption of a cached pass's inputs is caught only at the next
key rotation or TOWER_FRESH -- the disclosed, accepted residual.
A member with a cached PASS at the current key is SKIPPED and reported
as "PASS (cached ...)"; the run's summary prints the live-vs-cached
census explicitly (no silent caps). This is the same
certify-against-committed-record philosophy as the manifest chain mode
(the cadence amendment): the cached PASS is the recorded observation of
an identical-input run, not a new execution. TOWER_FRESH=1 forces every
member to run live (reviewers may always force fresh). Run under
tools/research/run_with_checkpoints.sh so the cache is committed and
pushed every 10 minutes -- git is the only restore-proof storage.
Failures are never cached.

ROUND 395 (the owner's residual sweep): the key also binds an
ENVIRONMENT FINGERPRINT (F394-1: the interpreter, the C library, the
CPU, the driver's BLAS thread count, the numeric libraries'
environment switches, and the versions of the third-party
distributions the member's reach imports, closed under their
requirements, with mpmath's and sympy's optional backends -- see
env_fingerprint), so an interpreter or
library change re-runs the affected members live without a manual
TOWER_FRESH; and two prechecks join the run: the render lint of the
markdown paper surfaces (render_lint.py, pinned) and the gate-label
census-numeral scan (A561 O-3). The round-395 sweep adds a third, the
PAPER-READER precheck: every non-member verifier that reads a markdown
paper surface, discovered structurally and run live on every
invocation (round 396 retired its cache) -- see that block. Round 396
adds the REACH precheck after the key computation: no member's reach
may carry an import the walk cannot resolve, and since round 397 the
walk runs its own sabotage case first (F397-B1: `from pkg import
helper` and relative imports); it prints "reach precheck: ..." when
it passes.
"""
import concurrent.futures as cf
import hashlib, json, os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
MAN_PATH = os.path.join(HERE, "tower_manifest.json")
PAPER_PATH = os.path.join(HERE, "..", "..",
                          "riemann-indistinguishability.md")
CACHE_PATH = os.path.join(HERE, "checkpoints",
                          "tower_results.json")
MAN = json.load(open(MAN_PATH, encoding="utf-8"))


def _sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


bad = []
for e in MAN["tower"]:
    p = os.path.join(HERE, e["file"])
    if _sha(p) != e["sha256"]:
        bad.append(e["file"])
for e in MAN.get("keying", []):          # round 283: the keying machinery, pinned
    p = os.path.join(HERE, e["file"])
    if _sha(p) != e["sha256"]:
        bad.append(e["file"])
if bad:
    print(f"MANIFEST STALE for: {bad}", flush=True)
    sys.exit(2)
# round 284 F284-1: the pinned SET is checked by name, not by count
KEYING_PINS = {"ckpt_key.py", "ckpt_migrate.py", "ckpt_key_probes.py",
               "precheck_probes.py", "render_lint.py"}   # the last: round 395
_pinned = {e["file"] for e in MAN.get("keying", [])}
if _pinned != KEYING_PINS or len(MAN.get("keying", [])) != len(KEYING_PINS):   # F285-1: no duplicates
    print(f"MANIFEST keying pins {sorted(_pinned)} != required "
          f"{sorted(KEYING_PINS)} -- refresh it", flush=True)
    sys.exit(2)
print(f"manifest integrity: {len(MAN['tower'])} members verified, "
      f"{len(MAN['keying'])} keying files pinned", flush=True)

import ast as _ast

sys.path.insert(0, HERE)
import paper_needles
import ckpt_key


CODE_ROOTS = (HERE,
              os.path.normpath(os.path.join(HERE, "..",
                                            "verifiers")))
TEXT_ROOTS = (os.path.normpath(os.path.join(HERE, "..", "..",
                                            "src")),)


def _resolve(sc):
    """Resolve a string constant to a HERE-relative substrate
    path. Code: bare .py names AND module stems (round-256
    F256-1 -- spawns built as s + ".py"), searched in every
    code root. TEXT substrates (round-257 F257-1): .tex names
    searched in src/ -- three reach files (one manifest member
    plus two chained verifiers) needle-gate raw
    substrings of the cascade tex papers, so those bytes are
    verdict inputs and must be in the key (bound by raw-byte
    sha via code_sha's non-.py fallback), exactly the
    rationale that byte-binds the main paper. Returns None
    for non-substrate constants."""
    if "/" in sc or " " in sc or not sc:
        return None
    if sc.endswith(".tex"):
        if not sc[:-4].replace("_", "").replace("-", "").isalnum():
            return None
        for r in TEXT_ROOTS:
            pth = os.path.join(r, sc)
            if os.path.exists(pth):
                return os.path.relpath(pth, HERE)
        return None
    cands = [sc] if sc.endswith(".py") else [sc + ".py"]
    for c in cands:
        stem = c[:-3]
        if not stem.replace("_", "").isalnum():
            continue
        for r in CODE_ROOTS:
            pth = os.path.join(r, c)
            if os.path.exists(pth):
                return os.path.relpath(pth, HERE)
    return None


_NAMED_MEMO = {}


def _named_py(rel):
    """Every substrate named by a string constant (bare .py
    name, module stem, or .tex name) in the DOCSTRING-STRIPPED
    AST of the file at HERE-relative path rel -- the
    subprocess/chain/needle reach the import walk cannot see.
    Over-approximates (any mention counts): the safe
    direction. Memoized per file per run. Non-.py reach
    entries (tex substrates) expand to nothing."""
    if not rel.endswith(".py"):
        return set()
    if rel in _NAMED_MEMO:
        return _NAMED_MEMO[rel]
    import ast
    tree = ast.parse(open(os.path.join(HERE, rel), "rb").read())
    for node in ast.walk(tree):
        body = getattr(node, "body", None)
        if (isinstance(body, list) and body
                and isinstance(body[0], ast.Expr)
                and isinstance(body[0].value, ast.Constant)
                and isinstance(body[0].value.value, str)):
            node.body = body[1:]
    out = set()
    for node in ast.walk(tree):
        if (isinstance(node, ast.Constant)
                and isinstance(node.value, str)):
            r = _resolve(node.value)
            if r is not None:
                out.add(r)
    _NAMED_MEMO[rel] = out
    return out


_IMP_MEMO = {}


def _import_targets(path):
    """Per import statement of the file at path: (top-level name or
    None for a relative import, the directories it resolves against,
    the dotted candidates as path-segment lists). Round 397 F397-B1
    (the F269-3 class, its other spelling): `from pkg import helper`
    may name the SUBMODULE pkg/helper.py, so pkg.helper is a candidate
    beside pkg; a relative import resolves against its own package
    directory, `from . import x` included (module None)."""
    import ast
    tree = ast.parse(open(path, "rb").read())
    d = os.path.dirname(path) or HERE
    out = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for a in node.names:
                out.append((a.name.split(".")[0], {d} | set(CODE_ROOTS),
                            [a.name.split(".")]))
        elif isinstance(node, ast.ImportFrom):
            base = node.module.split(".") if node.module else []
            if node.level:
                pkg = d
                for _ in range(node.level - 1):
                    pkg = os.path.dirname(pkg)
                top, roots = None, {pkg}
            else:
                top, roots = base[0], {d} | set(CODE_ROOTS)
            cands = [base] if base else []
            cands += [base + [a.name] for a in node.names if a.name != "*"]
            out.append((top, roots, cands))
    return out


def _local_files(roots, parts):
    """Every module file and package __init__.py on the dotted path
    parts, under each root."""
    found = set()
    for root in roots:
        cands = [os.path.join(root, *parts) + ".py"]
        for i in range(1, len(parts) + 1):
            cands.append(os.path.join(root, *parts[:i], "__init__.py"))
        found.update(pth for pth in cands if os.path.exists(pth))
    return found


def _imports_of(rel):
    """HERE-relative import closure step for the file at rel,
    resolved against the file's OWN directory AND every code
    root (round-257 F257-2: sys.path-inserted cross-root
    imports -- riemann_selection and type_counting import
    verify_selection_rule from tools/verifiers). Non-.py
    entries expand to nothing."""
    if not rel.endswith(".py"):
        return set()
    if rel in _IMP_MEMO:
        return _IMP_MEMO[rel]
    # round-269 F269-3: dotted local imports resolve as path
    # segments -- the old `m + ".py"` probe never existed for
    # `import pkg.helper`, so a package-housed helper escaped
    # BOTH the precheck scan and the cache key (a demonstrated
    # stale-PASS channel against paper AND code edits). Every
    # module file and every package __init__.py on the dotted
    # path joins the reach; round 397 F397-B1 adds the
    # `from pkg import helper` and relative spellings
    # (_import_targets).
    out = {os.path.relpath(pth, HERE)
           for pth in _local_imports(os.path.join(HERE, rel))}
    _IMP_MEMO[rel] = out
    return out


def _local_imports(path):
    """Absolute paths of the local files the imports of path resolve to."""
    out = set()
    for _top, roots, cands in _import_targets(path):
        for parts in cands:
            out |= _local_files(roots, parts)
    return out


def member_reach(name):
    """The member's full code reach, iterated to a TRUE fixed
    point (round-256 F256-2: the previous loop's import-added
    files never received the named-.py scan -- a dead-code
    comprehension): every file reached gains BOTH its import
    step and its named-code step; ckpt_key.py excluded by the
    standing convention."""
    reach = set()
    frontier = {name}
    while frontier:
        f = frontier.pop()
        if f in reach:
            continue
        reach.add(f)
        frontier |= (_imports_of(f) | _named_py(f)) - reach
    reach.discard("ckpt_key.py")
    return reach


# THE PAPER-NEEDLE PRECHECK (the A397 arc; REACH-WIDE per round-264
# F264-1; RESTRUCTURED round 275 F275-1, owner's decision: MEMBERS
# NEVER HOLD PAPER TEXT). paper_needles.py is the only file in any
# member's reach that reads the paper; every member consumes it
# through paper_needles.verify / paper_needles.needle applied to
# its one pure-literal PAPER_NEEDLES declaration. This precheck
# AST-extracts each declaration WITHOUT executing anything and
# evaluates it against the live paper on every invocation, failing
# the run (exit 2) before any cached PASS is served. The closure
# meta-gate enforces the SHAPE on every reach file -- named
# clauses, each a static tripwire:
#   (A) NO PAPER-NAMING CONSTANT: no string constant in the
#       docstring-stripped AST names the paper file (the round-264
#       clause (iv) with its PAPER-assignment exception removed);
#       and (A2, round-277 F276-1) none names the module
#       paper_needles -- so __import__("paper_needles"),
#       sys.modules["paper_needles"], importlib.import_module(...)
#       cannot be spelled with the name;
#   (B) THE MODULE IS USED ONLY THROUGH verify/needle/declared,
#       IMMEDIATELY CALLED: the name paper_needles is bound only
#       by the exact statement `import paper_needles`; every Load
#       of it is the value of an Attribute that is the func of a
#       Call and whose attr is verify, needle, or declared
#       (round-277 F276-1a: `paper_needles.verify.__globals__`
#       reached the cached text through the sanctioned function
#       object -- the attribute may no longer be loaded as a
#       value); no Import/ImportFrom names paper_needles in any
#       dotted path or leaf (F276-1b/c: `from tools.research
#       import paper_needles as pn`, `import tools.research.
#       paper_needles`, `from research import ...` bound the same
#       file under another name); no Attribute anywhere has attr
#       paper_needles (the module object obtained through another
#       reach module's namespace);
#   (F) NO INTROSPECTION SPELLINGS (round-277): no Attribute
#       anywhere whose attr is a dunder name, except __init__ and
#       __name__ (the committed reach's census) -- closes
#       __globals__/__dict__/__code__/__class__/__subclasses__/
#       __builtins__ chains from any object at the spelling;
#   (C) THE DECLARATION IS BOUND ONCE AND NEVER MUTATED: at most
#       one module-level Assign to PAPER_NEEDLES, a pure literal
#       (literal_eval under try/except, F264-4), every entry
#       schema-valid; every OTHER occurrence of the name is a Load
#       standing as the first positional argument of a
#       verify/needle call (round-275 route (d): AugAssign,
#       .append, subscript store, aliasing, comprehension over it
#       all flag);
#   (D) CALL SHAPES: verify(PAPER_NEEDLES) / verify(PAPER_NEEDLES,
#       g=<str>) / verify(PAPER_NEEDLES, seq=True) /
#       needle(PAPER_NEEDLES, <str>, <str>) with the (s, form)
#       pair present in the declaration / declared(PAPER_NEEDLES)
#       (read-only deep copies) -- nothing else;
#   (E) a file calling verify/needle/declared must carry the
#       declaration;
#   (G) NO STORE ON AN IMPORTED MODULE (round-278 F277-1): no
#       Attribute/Subscript Store or Del whose root is an
#       import-bound name, except the exact pairs mp.dps/mp.prec/
#       iv.prec (the mpmath precision contexts -- the reach's 42
#       committed stores, 39+1+2; round-279 pinned the pairs); no Assign
#       binding a bare import-bound module name to another name;
#       and (round-279 F278-1, the round-273 lesson applied here)
#       no Store/Del target whose root is NOT a Name at all
#       ((sys,)[0].executable = x) and no bare Load of an
#       `import`-bound MODULE name anywhere but as an Attribute's
#       value (f(subprocess), for m in [re], (sys,)[0] -- every
#       route that hands the module OBJECT to a binding the root
#       walk cannot see); no string constant "-c" (the spawn-
#       hijack idiom). So re.sub/builtins.open/subprocess.run/
#       sys.executable/os.environ[...] cannot be replaced at the
#       spelling (the child-process evaluator's spawn depends on
#       sys.executable and subprocess; round 277's H1/H2 hooked
#       re.sub and open inside the then in-process reader);
#   (H) NO INTERPRETER HOOK OR NAMESPACE ENUMERATION: no Attribute
#       named settrace/setprofile/addaudithook/_getframe/exc_info/
#       get_objects/get_referrers/get_referents/currentframe/
#       getmodule/getsource/stack/modules/meta_path/path_hooks/
#       displayhook/excepthook; no Call of globals/vars/locals/
#       dir/breakpoint/eval/exec/compile/setattr/delattr; no
#       import of builtins/gc/inspect/ctypes/importlib/runpy/
#       code/codeop/pdb/trace/faulthandler/types/dis/marshal/
#       tracemalloc/threading/_thread/atexit/signal/sitecustomize/
#       usercustomize (the reach's census: zero of each);
#   (I) NO INTROSPECTION DUNDER AS A STRING CONSTANT: none of
#       __globals__/__dict__/__code__/__class__/__subclasses__/
#       __base__/__bases__/__mro__/__builtins__/__closure__/
#       __func__/__self__/__module__/__import__/__loader__/
#       __spec__/__file__/__getattribute__/__getattr__/
#       __reduce__/__wrapped__ appears as a string constant
#       (round-277 F277-3: "never touch a dunder" now means the
#       attribute AND the string).
# With these holding, a member's verdict depends on the paper
# only through declared entries this precheck evaluates LIVE --
# and since round 278 the paper text never exists in a member's
# process at all: paper_needles.verify/needle evaluate in an
# isolated child (-I, scrubbed environment) that returns only
# (ok, misses). What remains for a member is to subvert the child
# (its interpreter path, its spawn, its environment -- clause G)
# or to read the file itself (clauses A/A2), each at the plain
# spelling. Scope, stated honestly (F268-4 carried forward;
# re-sworn round 278): spellings that never write the module
# name or the paper filename as one constant, never touch an
# introspection dunder as attribute or string, and never store
# on an imported module -- string arithmetic, getattr with a
# computed name, exec/eval reached through a computed route (the
# Name calls exec()/eval() are clause H), filesystem
# enumeration, a committed non-.py helper the member names, a
# write into the interpreter's own installation (the -I child
# still imports the installation's sitecustomize; round-279
# F278-3) -- are deliberate evasion outside these tripwires;
# drift detection, not a semantic proof. SCOPE (round 279, the
# owner's decision, recorded in CLAUDE.md): this precheck is a
# drift-detection instrument, not a sandbox; deliberate
# self-subversion of a member's own process is out of scope.
# Rounds 264-274's member-side read/transform/compare/f-string/
# canon-shape/binding-walk clauses are RETIRED with the member
# reads they policed (there is no paper text in a member to
# police).

_paper_bytes = open(PAPER_PATH, encoding="utf-8").read()
_pforms = paper_needles.forms(_paper_bytes)

_PN_ATTRS = ("verify", "needle", "declared")
# the reach's 42 committed stores on imported modules, by exact
# (root, attr) pair (round-279 cosmetic 1: mp.dps 39, mp.prec 1,
# iv.prec 2 -- the product set admitted the unused iv.dps)
_PREC_STORES = frozenset((("mp", "dps"), ("mp", "prec"), ("iv", "prec")))
_HOOK_ATTRS = frozenset((
    "settrace", "setprofile", "addaudithook", "_getframe", "exc_info",
    "get_objects", "get_referrers", "get_referents", "currentframe",
    "getmodule", "getsource", "stack", "modules", "meta_path",
    "path_hooks", "displayhook", "excepthook"))
_HOOK_CALLS = frozenset((
    "globals", "vars", "locals", "dir", "breakpoint", "eval", "exec",
    "compile", "setattr", "delattr"))
_RISKY_MODULES = frozenset((
    "builtins", "gc", "inspect", "ctypes", "importlib", "runpy", "code",
    "codeop", "pdb", "trace", "faulthandler", "types", "dis", "marshal",
    "tracemalloc", "threading", "_thread", "atexit", "signal",
    "sitecustomize", "usercustomize"))
_DUNDER_STRINGS = frozenset((
    "__globals__", "__dict__", "__code__", "__class__", "__subclasses__",
    "__base__", "__bases__", "__mro__", "__builtins__", "__closure__",
    "__func__", "__self__", "__module__", "__import__", "__loader__",
    "__spec__", "__file__", "__getattribute__", "__getattr__",
    "__reduce__", "__wrapped__"))


def _precheck_file(rel):
    """The per-file clauses (A)-(E) plus the live evaluation;
    returns (failures, is-declared-surface)."""
    out = []
    src = open(os.path.join(HERE, rel), "rb").read().decode("utf-8")
    tree = _ast.parse(src)
    # (A) on the docstring-stripped copy (docstrings MAY name the
    # paper; executable constants may not)
    stripped = _ast.parse(src)
    for node in _ast.walk(stripped):
        body = getattr(node, "body", None)
        if (isinstance(body, list) and body
                and isinstance(body[0], _ast.Expr)
                and isinstance(body[0].value, _ast.Constant)
                and isinstance(body[0].value.value, str)):
            node.body = body[1:]
    for node in _ast.walk(stripped):
        if (isinstance(node, _ast.Constant)
                and isinstance(node.value, str)
                and "riemann-indistinguishability" in node.value):
            out.append(f"{rel}: paper-naming constant at line "
                       f"{node.lineno} (clause A)")
        if (isinstance(node, _ast.Constant)
                and isinstance(node.value, str)
                and "paper_needles" in node.value):
            out.append(f"{rel}: module-naming constant at line "
                       f"{node.lineno} (clause A2)")
    # (B) the module name: bindings and loads
    calls = []          # (node, attr) for verify/needle calls
    attr_loads = set()  # id() of Name nodes that are call-func values
    _call_funcs = set()
    for node in _ast.walk(tree):
        if isinstance(node, _ast.Call):
            _call_funcs.add(id(node.func))
    for node in _ast.walk(tree):
        if isinstance(node, _ast.Import):
            for a in node.names:
                if a.name == "paper_needles" and a.asname is None:
                    continue
                if ("paper_needles" in a.name.split(".")
                        or a.asname == "paper_needles"):
                    out.append(f"{rel}: import spelling {a.name!r}"
                               f"{' as ' + a.asname if a.asname else ''}"
                               f" names paper_needles at line "
                               f"{node.lineno} (clause B)")
        if isinstance(node, _ast.ImportFrom):
            segs = (node.module or "").split(".")
            if ("paper_needles" in segs
                    or any(a.name == "paper_needles"
                           or a.asname == "paper_needles"
                           for a in node.names)):
                out.append(f"{rel}: from-import naming paper_needles "
                           f"at line {node.lineno} (clause B)")
        if isinstance(node, _ast.Attribute):
            if node.attr == "paper_needles":
                out.append(f"{rel}: attribute named paper_needles at "
                           f"line {node.lineno} (clause B)")
            if (node.attr.startswith("__") and node.attr.endswith("__")
                    and node.attr not in ("__init__", "__name__")):
                out.append(f"{rel}: introspection attribute "
                           f"{node.attr} at line {node.lineno} "
                           f"(clause F)")
        if (isinstance(node, _ast.Attribute)
                and isinstance(node.value, _ast.Name)
                and node.value.id == "paper_needles"):
            if node.attr not in _PN_ATTRS:
                out.append(f"{rel}: paper_needles.{node.attr} at line "
                           f"{node.lineno} is not verify/needle/"
                           f"declared (clause B)")
            elif id(node) not in _call_funcs:
                out.append(f"{rel}: paper_needles.{node.attr} loaded "
                           f"as a value (not called) at line "
                           f"{node.lineno} (clause B)")
            else:
                attr_loads.add(id(node.value))
        if (isinstance(node, _ast.Call)
                and isinstance(node.func, _ast.Attribute)
                and isinstance(node.func.value, _ast.Name)
                and node.func.value.id == "paper_needles"
                and node.func.attr in _PN_ATTRS):
            calls.append(node)
    for node in _ast.walk(tree):
        if isinstance(node, _ast.Name) and node.id == "paper_needles":
            if isinstance(node.ctx, _ast.Load):
                if id(node) not in attr_loads:
                    out.append(f"{rel}: bare use of the name "
                               f"paper_needles at line {node.lineno} "
                               f"(clause B)")
            else:
                out.append(f"{rel}: the name paper_needles rebound at "
                           f"line {node.lineno} (clause B)")
    # (G) stores on imported modules; module aliases
    _imp_names = set()
    for node in _ast.walk(tree):
        if isinstance(node, _ast.Import):
            for a in node.names:
                _imp_names.add(a.asname or a.name.split(".")[0])
        if isinstance(node, _ast.ImportFrom):
            for a in node.names:
                _imp_names.add(a.asname or a.name)

    def _root(x):
        while isinstance(x, (_ast.Attribute, _ast.Subscript)):
            x = x.value
        return x.id if isinstance(x, _ast.Name) else None

    _mod_names = set()
    for node in _ast.walk(tree):
        if isinstance(node, _ast.Import):
            for a in node.names:
                _mod_names.add(a.asname or a.name.split(".")[0])
    _attr_values = set()
    for node in _ast.walk(tree):
        if isinstance(node, _ast.Attribute):
            _attr_values.add(id(node.value))
    for node in _ast.walk(tree):
        if (isinstance(node, (_ast.Attribute, _ast.Subscript))
                and isinstance(node.ctx, (_ast.Store, _ast.Del))):
            r_ = _root(node)
            if r_ is None:
                out.append(f"{rel}: store target with a non-Name root "
                           f"{_ast.unparse(node)!r} at line "
                           f"{node.lineno} (clause G)")
            elif (r_ in _imp_names
                    and not (isinstance(node, _ast.Attribute)
                             and (r_, node.attr) in _PREC_STORES)):
                out.append(f"{rel}: store on imported module "
                           f"{_ast.unparse(node)!r} at line "
                           f"{node.lineno} (clause G)")
        if (isinstance(node, _ast.Assign)
                and isinstance(node.value, _ast.Name)
                and node.value.id in _imp_names):
            out.append(f"{rel}: import-bound name {node.value.id!r} "
                       f"aliased at line {node.lineno} (clause G)")
        if (isinstance(node, _ast.Name) and isinstance(node.ctx, _ast.Load)
                and node.id in _mod_names
                and id(node) not in _attr_values):
            out.append(f"{rel}: module {node.id!r} loaded as a bare "
                       f"value at line {node.lineno} (clause G)")
    for node in _ast.walk(stripped):
        if (isinstance(node, _ast.Constant) and node.value == "-c"):
            out.append(f"{rel}: '-c' constant at line {node.lineno} "
                       f"(clause G)")
    # (H) interpreter hooks, namespace enumeration, risky imports
    for node in _ast.walk(tree):
        if isinstance(node, _ast.Attribute) and node.attr in _HOOK_ATTRS:
            out.append(f"{rel}: hook/enumeration attribute "
                       f"{node.attr} at line {node.lineno} (clause H)")
        if (isinstance(node, _ast.Call) and isinstance(node.func, _ast.Name)
                and node.func.id in _HOOK_CALLS):
            out.append(f"{rel}: {node.func.id}() at line "
                       f"{node.lineno} (clause H)")
        if isinstance(node, _ast.Import):
            for a in node.names:
                if a.name.split(".")[0] in _RISKY_MODULES:
                    out.append(f"{rel}: import of {a.name} at line "
                               f"{node.lineno} (clause H)")
        if (isinstance(node, _ast.ImportFrom)
                and (node.module or "").split(".")[0] in _RISKY_MODULES):
            out.append(f"{rel}: from-import of {node.module} at line "
                       f"{node.lineno} (clause H)")
    # (I) introspection dunders as string constants
    for node in _ast.walk(stripped):
        if (isinstance(node, _ast.Constant)
                and isinstance(node.value, str)
                and node.value in _DUNDER_STRINGS):
            out.append(f"{rel}: introspection dunder string "
                       f"{node.value} at line {node.lineno} (clause I)")
    if paper_needles.shadow_bound(tree, ("paper_needles",
                                         "PAPER_NEEDLES")):
        out.append(f"{rel}: paper_needles/PAPER_NEEDLES bound through "
                   f"a raw-string binding form (clause B/C)")
    # (C) the declaration
    decl, ndecl, decl_node = None, 0, None
    for node in tree.body:
        if (isinstance(node, _ast.Assign) and len(node.targets) == 1
                and getattr(node.targets[0], "id", "")
                == "PAPER_NEEDLES"):
            ndecl += 1
            decl_node = node
            try:
                decl = _ast.literal_eval(node.value)
            except Exception as ex:
                out.append(f"{rel}: PAPER_NEEDLES is not a pure "
                           f"literal ({ex}) (clause C)")
                return out, True
    if ndecl > 1:
        out.append(f"{rel}: PAPER_NEEDLES literals = {ndecl} (clause C)")
        return out, True
    if decl is not None:
        if not isinstance(decl, list) or not all(
                paper_needles.valid(d) for d in decl):
            out.append(f"{rel}: PAPER_NEEDLES has a schema-invalid "
                       f"entry (clause C)")
            return out, True
    first_args = {id(c.args[0]) for c in calls if c.args}
    for node in _ast.walk(tree):
        if isinstance(node, _ast.Name) and node.id == "PAPER_NEEDLES":
            if node is (decl_node.targets[0] if decl_node else None):
                continue
            if (not isinstance(node.ctx, _ast.Load)
                    or id(node) not in first_args):
                out.append(f"{rel}: PAPER_NEEDLES used outside a "
                           f"verify/needle first argument at line "
                           f"{node.lineno} (clause C)")
    # (D) call shapes; (E) declaration present
    declared_pairs = set()
    if decl:
        declared_pairs = {(d.get("s"), d.get("form", "raw"))
                          for d in decl if "s" in d}
    for c in calls:
        ln = c.lineno
        if decl is None:
            out.append(f"{rel}: verify/needle call at line {ln} "
                       f"without a PAPER_NEEDLES declaration "
                       f"(clause E)")
            continue
        if not (c.args and isinstance(c.args[0], _ast.Name)
                and c.args[0].id == "PAPER_NEEDLES"):
            out.append(f"{rel}: {c.func.attr} first argument is not "
                       f"the bare PAPER_NEEDLES at line {ln} "
                       f"(clause D)")
            continue
        if c.func.attr == "verify":
            if len(c.args) != 1:
                out.append(f"{rel}: verify positional shape at line "
                           f"{ln} (clause D)")
            for k in c.keywords:
                v = k.value
                if k.arg == "g" and isinstance(v, _ast.Constant) \
                        and isinstance(v.value, str):
                    continue
                if k.arg == "seq" and isinstance(v, _ast.Constant) \
                        and v.value is True:
                    continue
                out.append(f"{rel}: verify keyword {k.arg!r} shape at "
                           f"line {ln} (clause D)")
        elif c.func.attr == "declared":
            if len(c.args) != 1 or c.keywords:
                out.append(f"{rel}: declared call shape at line {ln} "
                           f"(clause D)")
        else:  # needle
            if (len(c.args) != 3 or c.keywords
                    or not all(isinstance(a, _ast.Constant)
                               and isinstance(a.value, str)
                               for a in c.args[1:])):
                out.append(f"{rel}: needle call shape at line {ln} "
                           f"(clause D)")
                continue
            pair = (c.args[1].value, c.args[2].value)
            if pair not in declared_pairs:
                out.append(f"{rel}: needle {pair!r} at line {ln} is "
                           f"not declared (clause D)")
    if decl is None:
        return out, False
    # the live evaluation
    ok, miss = paper_needles.check(decl, _paper_bytes, pre=_pforms)
    for d, n in miss:
        out.append(f"{rel}: needle miss ({n}): {d!r}")
    return out, True


_scan = set()
for _e in MAN["tower"]:
    _scan |= {f for f in member_reach(_e["file"])
              if f.endswith(".py")}
_scan.discard("paper_needles.py")   # the one sanctioned reader
_pfail, _nreaders = [], 0
for _rel in sorted(_scan):
    _f, _isreader = _precheck_file(_rel)
    _pfail += _f
    _nreaders += _isreader
if _pfail:
    print("PAPER-NEEDLE PRECHECK FAILURES:", flush=True)
    for f_ in _pfail:
        print(f"  {f_}", flush=True)
    sys.exit(2)
print(f"paper-needle precheck: {len(_scan)} reach files scanned, "
      f"{_nreaders} declared surfaces verified live", flush=True)

# keying-probe precheck (round 282, reviewer's observation): the
# keying module is outside every member's reach by convention, so a
# change to it re-verifies no member live; its sabotage suite runs
# here on every invocation instead, and the tower fails if it does.
_kp = subprocess.run([sys.executable, os.path.join(HERE, "ckpt_key_probes.py")],
                     capture_output=True, text=True)
_kp_line = [l for l in _kp.stdout.splitlines() if l.startswith("ckpt_key probes:")]
print("keying-probe precheck: " + (_kp_line[-1] if _kp_line else "no census line"), flush=True)
# the gate reads the CENSUS, not just the exit code: an emptied or
# thinned suite exiting 0 must still fail (the case count pinned
# EXACTLY -- round 283 O2 -- and 0 unexpected); the suite itself is
# integrity-pinned in the manifest, so a forged census line needs a
# manifest refresh that git review sees (round 283 O1)
KEY_PROBE_CASES = 24
_m = re.match(r"ckpt_key probes: (\d+) cases, (\d+) as expected, (\d+) unexpected",
              _kp_line[-1]) if _kp_line else None
if (_kp.returncode != 0 or _m is None or int(_m.group(1)) != KEY_PROBE_CASES
        or int(_m.group(3)) != 0 or int(_m.group(2)) != int(_m.group(1))):
    print(f"KEYING-PROBE PRECHECK FAILURE (expected exactly {KEY_PROBE_CASES} cases, "
          f"0 unexpected, exit 0; a grown suite must update KEY_PROBE_CASES and "
          f"refresh the manifest):", flush=True)
    print(_kp.stdout[-2000:] + _kp.stderr[-2000:], flush=True)
    sys.exit(2)

# needle-precheck sabotage suite (round 284, reviewer's observation a):
# precheck_probes.py was the one reported-census suite run by no tower
# invocation and pinned nowhere; it is now pinned (manifest) and run here,
# its census pinned exactly like the keying suite's
PRECHECK_PROBE_CASES = 85
_pp = subprocess.run([sys.executable, os.path.join(HERE, "precheck_probes.py")],
                     capture_output=True, text=True)
_pp_line = [l for l in _pp.stdout.splitlines() if l.startswith("precheck probes:")]
print("needle-probe precheck: " + (_pp_line[-1] if _pp_line else "no census line"), flush=True)
_m2 = re.match(r"precheck probes: (\d+) cases, (\d+) as expected, (\d+) unexpected",
               _pp_line[-1]) if _pp_line else None
if (_pp.returncode != 0 or _m2 is None or int(_m2.group(1)) != PRECHECK_PROBE_CASES
        or int(_m2.group(3)) != 0 or int(_m2.group(2)) != int(_m2.group(1))):
    print(f"NEEDLE-PROBE PRECHECK FAILURE (expected exactly {PRECHECK_PROBE_CASES} cases, "
          f"0 unexpected, exit 0; a grown suite must update PRECHECK_PROBE_CASES and "
          f"refresh the manifest):", flush=True)
    print(_pp.stdout[-2000:] + _pp.stderr[-2000:], flush=True)
    sys.exit(2)

# render-lint precheck (round 395, the owner's residual sweep; A562
# O-1, A563 F391-2): the markdown paper surfaces must render as
# written under cmark-gfm (render_lint.py: single-tilde strikes,
# unrendered ~~ or **, intraword emphasis, consumed backslashes,
# variable stars acting as delimiters, stray stars, literal backticks,
# underscore emphasis; since round 396 block structure too, and since
# round 397 any block without a blank line before it, any raw HTML and
# LaTeX quote pairs read as code -- the classes are listed in its
# docstring). The lint carries its own
# sabotage cases; the census line is gated, the probe count pinned
# exactly like the two suites above, and the script is pinned in the
# manifest's keying list
RENDER_PROBE_CASES, RENDER_SURFACES = 23, 2   # 7 -> 10 at the round-395 sweep (L7-L9), 15 at round 396 (L10-L14), 23 at round 397 (L10, L13 widened; L15)
_rl = subprocess.run([sys.executable, os.path.join(HERE, "render_lint.py")],
                     capture_output=True, text=True)
_rl_line = [l for l in _rl.stdout.splitlines() if l.startswith("render lint:")]
print("render-lint precheck: " + (_rl_line[-1] if _rl_line else "no census line"), flush=True)
_m3 = re.match(r"render lint: (\d+) surfaces, (\d+) defects; probes (\d+)/(\d+) as expected",
               _rl_line[-1]) if _rl_line else None
if (_rl.returncode != 0 or _m3 is None or int(_m3.group(1)) != RENDER_SURFACES
        or int(_m3.group(2)) != 0 or int(_m3.group(4)) != RENDER_PROBE_CASES
        or int(_m3.group(3)) != RENDER_PROBE_CASES):
    print(f"RENDER-LINT PRECHECK FAILURE (expected {RENDER_SURFACES} surfaces, "
          f"0 defects, {RENDER_PROBE_CASES}/{RENDER_PROBE_CASES} probes, exit 0):",
          flush=True)
    print(_rl.stdout[:4000] + _rl.stderr[-2000:], flush=True)   # head: the defect list starts there (round 395 B9)
    sys.exit(2)

# gate-label precheck (round 395, A561 O-3): a gate label that spells
# the footer census ("88 cited in place; the range 1i–1bl") goes stale
# at the next landing while its needles advance -- rounds 167 F6, 175
# F2/F5, 213 F3 and A561 O-3 each re-synced labels by hand. No gate
# label in tools/research may carry a census numeral or a Theorem-range
# literal; the needles carry the live values. Scope (round-395 sweep,
# F395-B6/C9): every string constant anywhere in the first argument of
# a call to gate or to a name bound to it by plain, annotated or
# tuple assignment (so f-strings and concatenations are read part by
# part, and joined in source order -- round 397 F397-B4: the round-396
# join followed ast.walk's breadth-first order), a range written with
# any Unicode dash (category Pd) or the minus sign, and a
# floor on the number of labels scanned, so a renamed gate cannot pass
# by scanning nothing (round 396 F396-B8 widened the aliases, dashes and
# joins). Not read: a label passed in a variable. Its own sabotage
# cases run first.
import unicodedata as _ud
_DASHES = "".join(ch for ch in map(chr, range(0x110000))
                  if _ud.category(ch) == "Pd") + "\u2212"
_CENSUS_NUM = re.compile(r"\d+ (?:scripts )?cited in place"
                         r"|1i\s*[" + re.escape(_DASHES) + r"]+\s*1[a-z]{2}")
GATE_LABELS_MIN = 650


def _consts_in_order(node):
    """The string constants under node, in source order."""
    if isinstance(node, _ast.Constant) and isinstance(node.value, str):
        yield node.value
    for c in _ast.iter_child_nodes(node):
        yield from _consts_in_order(c)


def _label_hits(tree):
    """(labels scanned, [lineno of each census-bearing label])."""
    names = {"gate"}
    for node in _ast.walk(tree):
        tgts, val = [], None
        if isinstance(node, _ast.Assign):
            tgts, val = node.targets, node.value
        elif isinstance(node, _ast.AnnAssign) and node.value is not None:
            tgts, val = [node.target], node.value
        if val is None:
            continue
        vals = val.elts if isinstance(val, _ast.Tuple) else [val]
        for t in tgts:
            ts = t.elts if isinstance(t, _ast.Tuple) else [t]
            for tt, vv in zip(ts, vals if len(vals) == len(ts) else vals * len(ts)):
                if (isinstance(tt, _ast.Name) and isinstance(vv, _ast.Name)
                        and vv.id in names):
                    names.add(tt.id)
    n, bad = 0, []
    for node in _ast.walk(tree):
        if (isinstance(node, _ast.Call) and isinstance(node.func, _ast.Name)
                and node.func.id in names and node.args):
            n += 1
            consts = list(_consts_in_order(node.args[0]))
            if any(_CENSUS_NUM.search(c) for c in consts + ["".join(consts)]):
                bad.append(node.lineno)
    return n, bad


_sab = _ast.parse('gate("g1 ok", 1)\n'
                  'gate(f"g2 {k}: 88 cited in place", 1)\n'
                  'gate("g3 the range " + "1i\u22121ca", 1)\n'
                  'G = gate\nG("g4 88 cited in place", 1)\n'
                  'H: object = gate\nH("g5 88 " + "cited in place", 1)\n'
                  'gate("g6 the range " + "1i" + "\ufe581ca", 1)\n'
                  'J, K = gate, print\nJ(f"g7 {k} the range 1i" + "\u2e3a1ca", 1)\n')
if not (_CENSUS_NUM.search("88 cited in place; the range 1i–1bl")
        and _CENSUS_NUM.search("Theorems 1i--1bj")
        and not _CENSUS_NUM.search("the anchored count and range needles")
        and _label_hits(_sab) == (7, [2, 3, 5, 7, 8, 10])):
    print("GATE-LABEL PRECHECK FAILURE: the census-numeral scan missed "
          "its sabotage cases", flush=True)
    sys.exit(2)
_nlab, _lab_bad = 0, []
for _f in sorted(os.listdir(HERE)):
    if not _f.endswith(".py"):
        continue
    _n, _b = _label_hits(_ast.parse(open(os.path.join(HERE, _f), "rb").read()))
    _nlab += _n
    _lab_bad += [f"{_f}:{_ln}" for _ln in _b]
print(f"gate-label precheck: {_nlab} gate labels scanned, "
      f"{len(_lab_bad)} carry a census numeral", flush=True)
if _lab_bad or _nlab < GATE_LABELS_MIN:
    print(f"GATE-LABEL PRECHECK FAILURE: {_lab_bad} "
          f"(scanned {_nlab}, floor {GATE_LABELS_MIN})", flush=True)
    sys.exit(2)

# thread pinning (round 252, measured): 4 workers x full-core
# BLAS oversubscribed the box ~4x -- cascade_heatflow_energy ran
# 105 min in-tower vs 38 s standalone. Each member gets
# cpu_count/workers BLAS threads.
NW = min(4, os.cpu_count() or 4)
THR = str(max(1, (os.cpu_count() or 4)//NW))
# (moved above the fingerprint at round 395: the key binds THR)

# THE ENVIRONMENT FINGERPRINT (round 395, F394-1): a member's verdict
# depends on the interpreter and the numeric libraries as well as on
# its code, so the key binds them too. Per member: the interpreter
# (implementation, full version string, machine), the BLAS thread
# count the driver sets, the mpmath backend switches read from the
# environment, and name==version of every distribution providing a
# third-party module imported anywhere in the member's reach, closed
# under the distributions' non-extra requirements, plus the optional
# backends a library loads without declaring them (mpmath uses gmpy2
# or gmpy when installed; sympy uses python-flint or gmpy2 for its
# ground types -- round-395 sweep, F395-B4), the presence and value of
# the environment switches those libraries and the BLAS read, and the
# CPU (model name and feature flags: OpenBLAS picks its kernel per CPU
# at run time) and the C library (round 396 F396-B10: Python's math
# module calls it). A change in any bound input rotates the key of every
# member whose reach is affected, which then re-runs live -- for the
# bound inputs, over-invalidation and never a stale PASS. NOT bound
# (disclosed): a library rebuilt in place at the same version, a
# system BLAS swapped under an unchanged numpy, edits inside the
# interpreter's own installation, environment variables outside
# _ENV_SWITCHES, and the producers' compute checkpoints (their
# ckpt_key keys bind code only; the members that read them re-run
# live and re-gate the data). After any of those, TOWER_FRESH=1.
import importlib.metadata as _md
import platform as _platform

_STDLIB = set(sys.stdlib_module_names)
_PKG_DISTS = _md.packages_distributions()
_OPTIONAL_BACKENDS = {"mpmath": ("gmpy2", "gmpy"),
                      "sympy": ("python-flint", "gmpy2", "gmpy")}
_ENV_SWITCHES = ("MPMATH_NOGMPY", "MPMATH_NOSAGE", "MPMATH_SAGE",
                 "MPMATH_STRICT", "SAGE_ROOT", "SYMPY_GROUND_TYPES",
                 "SYMPY_USE_CACHE", "OPENBLAS_CORETYPE",
                 "NPY_DISABLE_CPU_FEATURES", "NPY_ENABLE_CPU_FEATURES")


def _cpu_fingerprint():
    """The CPU model name and a hash of its feature flags (Linux
    /proc/cpuinfo; elsewhere platform.processor())."""
    try:
        txt = open("/proc/cpuinfo", encoding="utf-8").read()
    except OSError:
        return "cpu=" + _platform.processor()
    model = re.search(r"^model name\s*:\s*(.*)$", txt, flags=re.M)
    flags = re.search(r"^flags\s*:\s*(.*)$", txt, flags=re.M)
    fl = " ".join(sorted(flags.group(1).split())) if flags else ""
    return (f"cpu={model.group(1).strip() if model else '?'}; flags="
            + hashlib.sha256(fl.encode()).hexdigest()[:16])


_CPU = _cpu_fingerprint()
_TP_MEMO = {}


def _third_party_of(rel):
    """Top-level imported module names of the file at rel that are
    neither stdlib nor local (local = some dotted candidate of the
    statement resolves to a file in the file's own directory or a code
    root, by the same resolution _imports_of uses -- round 397
    F397-B1: a namespace package such as strip_note, which has no
    __init__.py, is local through its module files). Relative imports
    are local by construction."""
    if not rel.endswith(".py"):
        return set()
    if rel in _TP_MEMO:
        return _TP_MEMO[rel]
    _TP_MEMO[rel] = _third_party_in(os.path.join(HERE, rel))
    return _TP_MEMO[rel]


def _third_party_in(path):
    out = set()
    for top, roots, cands in _import_targets(path):
        if top is None or top in _STDLIB or top == "__future__":
            continue
        if any(_local_files(roots, parts) for parts in cands):
            continue
        out.add(top)
    return out


def _dist_version(dist):
    try:
        return _md.version(dist)
    except _md.PackageNotFoundError:
        return "absent"


def env_fingerprint(name):
    tops = set()
    for f in member_reach(name):
        tops |= _third_party_of(f)
    dists, unresolved = set(), set()
    for t in tops:
        ds = _PKG_DISTS.get(t)
        if ds:
            dists.update(ds)
        else:
            unresolved.add(t)
        dists.update(_OPTIONAL_BACKENDS.get(t, ()))
    frontier = list(dists)
    while frontier:                     # close under non-extra requirements
        try:
            reqs = _md.requires(frontier.pop()) or []
        except _md.PackageNotFoundError:
            continue
        for r in reqs:
            if ";" in r and "extra" in r.split(";", 1)[1]:
                continue
            m = re.match(r"\s*([A-Za-z0-9][A-Za-z0-9._-]*)", r)
            if m and m.group(1) not in dists:
                dists.add(m.group(1))
                frontier.append(m.group(1))
    parts = [sys.implementation.name, sys.version, _platform.machine(),
             "libc=" + "-".join(_platform.libc_ver()), _CPU,
             f"blas_threads={THR}"]
    parts += [f"{v}={os.environ[v]!r}" if v in os.environ else f"{v} unset"
              for v in _ENV_SWITCHES]
    parts += sorted(f"{d.lower()}=={_dist_version(d)}" for d in dists)
    parts += sorted(f"unresolved:{t}" for t in unresolved)
    return "\n".join(parts)


def member_key(name):
    h = hashlib.sha256()
    # PAPER_SHA left the key at the A397 needle-precheck arc:
    # every member's declared paper surface is re-verified LIVE
    # by the precheck above on every invocation (the round-254
    # manifest precedent), so binding paper bytes would only
    # re-import prose sensitivity. The needle-gated TEX
    # substrates stay byte-bound in the reach (they are read by
    # members directly, outside the paper precheck's scope).
    # rounds 253-255: the member's full code REACH (imports +
    # named-.py spawn chain, transitive), each file at its
    # EXECUTABLE-CONTENT hash -- prose edits hold the cache
    for f in sorted(member_reach(name)):
        h.update(f.encode())
        # strip_prints=False (round 282): the member reach key keeps
        # the docstring-only hash -- a print edit in the reach
        # re-verifies the member live (cheap), while the producers'
        # compute keys (ckpt_key.code_key) ignore pure prints.
        h.update(ckpt_key.code_sha(
            os.path.join(HERE, f), strip_prints=False).encode())
    # round 395 (F394-1): the environment is an input too
    h.update(env_fingerprint(name).encode())
    return h.hexdigest()[:24]


cache = {}
if os.path.exists(CACHE_PATH):
    try:
        cache = json.load(open(CACHE_PATH, encoding="utf-8"))
    except Exception:
        cache = {}

fresh = os.environ.get("TOWER_FRESH") == "1"
env = dict(os.environ, CASCADE_CHAIN="manifest",
           OMP_NUM_THREADS=THR, OPENBLAS_NUM_THREADS=THR,
           MKL_NUM_THREADS=THR, NUMEXPR_NUM_THREADS=THR)


def run(name):
    t0 = time.time()
    r = subprocess.run([sys.executable, os.path.join(HERE, name)],
                       capture_output=True, text=True, env=env)
    return name, r.returncode, time.time() - t0, r.stdout[-400:]


# THE PAPER-READER PRECHECK (round-395 sweep, F395-A1/A2/B1): the
# round-394 meta-rule found "non-member verifiers that read the paper
# directly" by a grep that saw six of nineteen, and that round's
# render escapes broke three of the thirteen it missed. Discovery is
# structural: every .py file under the code roots (subdirectories
# included) whose docstring-stripped string constants name a markdown
# paper surface is a reader. Members never name the paper (clause A);
# one naming only the formulation would be discovered here and simply
# run twice. EVERY READER RUNS LIVE ON EVERY INVOCATION (round 396,
# F396-B1, MAJOR): a cache key cannot bind what readers actually read
# -- docstring text anchored as source, modules imported through
# sys.path roots outside the reach walk (tools/cascade_constants.py),
# and files read by glob (src/*.tex, PREDICTIONS.md) -- and the 19 run
# in about 15 s in parallel. The discovered count has a floor, so a
# broken discovery cannot pass empty.
READER_SURFACES = ("riemann-indistinguishability.md",
                   "cascade-riemann-formulation.md")
READER_INFRA = {"paper_needles.py", "run_tower.py", "render_lint.py",
                "precheck_probes.py", "refresh_tower_manifest.py"}
READERS_MIN = 19


def discover_readers():
    out = []
    for root in CODE_ROOTS:
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = sorted(d for d in dirnames
                                 if d not in ("__pycache__", "checkpoints"))
            for f in sorted(filenames):
                if not f.endswith(".py") or f in READER_INFRA:
                    continue
                path = os.path.join(dirpath, f)
                tree = _ast.parse(open(path, "rb").read())
                for node in _ast.walk(tree):
                    body = getattr(node, "body", None)
                    if (isinstance(body, list) and body
                            and isinstance(body[0], _ast.Expr)
                            and isinstance(body[0].value, _ast.Constant)
                            and isinstance(body[0].value.value, str)):
                        node.body = body[1:]
                if any(isinstance(n, _ast.Constant)
                       and isinstance(n.value, str)
                       and any(sf in n.value for sf in READER_SURFACES)
                       for n in _ast.walk(tree)):
                    out.append(os.path.relpath(path, HERE))
    return out


def run_reader(name):
    t0 = time.time()
    r = subprocess.run([sys.executable, os.path.join(HERE, name)],
                       capture_output=True, text=True, env=env)
    # the FAIL lines, then the stderr tail (round 397 F397-A6/B3: a
    # crash's traceback went to stderr and was dropped)
    fails = [l for l in r.stdout.splitlines() if "FAIL" in l]
    fails += r.stderr.strip().splitlines()[-6:]
    return name, r.returncode, time.time() - t0, fails, r.stdout[-300:]


readers = discover_readers()
r_fail = []
with cf.ProcessPoolExecutor(max_workers=NW) as ex:
    for name, rc, dt, fails, tail in ex.map(run_reader, readers):
        if rc != 0:
            r_fail.append(name)
            print(f"  READER FAIL {name} (exit {rc}):", flush=True)
            for l in (fails[:18] or [tail]):
                print(f"    {l}", flush=True)
print(f"paper-reader precheck: {len(readers)} readers discovered, "
      f"{len(readers) - len(r_fail)} PASS (all live), "
      f"{len(r_fail)} FAIL", flush=True)
if r_fail or len(readers) < READERS_MIN:
    print(f"PAPER-READER PRECHECK FAILURE: {r_fail} (discovered "
          f"{len(readers)}, floor {READERS_MIN})", flush=True)
    sys.exit(2)

names = [e["file"] for e in MAN["tower"]]
keys = {n: member_key(n) for n in names}
# round 396 (F396-B1, the F269-3 class): an import the reach walk cannot
# resolve is either an uninstalled library (the member would crash) or
# a local module outside the code roots (tools/cascade_constants.py is
# one) -- code the member runs that its key would not bind. No member
# may carry one.
# Round 397 (F397-B1): the reach walk's own sabotage case -- the
# spellings it must resolve, planted in a temporary directory outside
# the repository: `from pkg import helper` (the submodule), a dotted
# import of a namespace package, `from nsp import sib`, and the relative
# `from . import mod`; numpy stays third-party and the namespace
# package stays local.
import tempfile as _tempfile
with _tempfile.TemporaryDirectory() as _td:
    _plant = {"zzpkg/__init__.py": "", "zzpkg/helper.py": "",
              "nsp/mod.py": "", "nsp/sib.py": "from . import mod\n",
              "m.py": "from zzpkg import helper\nimport nsp.mod\n"
                      "from nsp import sib\nimport numpy.linalg\n"}
    for _f, _t in _plant.items():
        os.makedirs(os.path.dirname(os.path.join(_td, _f)), exist_ok=True)
        open(os.path.join(_td, _f), "w").write(_t)
    _got = [sorted(os.path.relpath(p, _td)
                   for p in _local_imports(os.path.join(_td, f)))
            for f in ("m.py", "nsp/sib.py")]
    _tp = _third_party_in(os.path.join(_td, "m.py"))
_want = [["nsp/mod.py", "nsp/sib.py", "zzpkg/__init__.py", "zzpkg/helper.py"],
         ["nsp/mod.py"]]
if _got != _want or _tp != {"numpy"}:
    print(f"REACH PRECHECK FAILURE: the reach walk missed its sabotage "
          f"case (resolved {_got}, third-party {sorted(_tp)})",
          flush=True)
    sys.exit(2)
_unres = {n: [l for l in env_fingerprint(n).split("\n")
              if l.startswith("unresolved:")] for n in names}
_unres = {n: u for n, u in _unres.items() if u}
if _unres:
    print(f"REACH PRECHECK FAILURE: unresolved imports in member reach "
          f"{_unres} (a local module outside the code roots is a "
          f"stale-PASS channel)", flush=True)
    sys.exit(2)
print(f"reach precheck: {len(names)} members, 0 unresolved imports; "
      f"sabotage case resolved ({sum(map(len, _want))} imports)", flush=True)
cached = [] if fresh else \
    [n for n in names if cache.get(keys[n], {}).get("rc") == 0]
live = [n for n in names if n not in cached]
for n in cached:
    c = cache[keys[n]]
    print(f"  PASS {n} (cached {c.get('when', '?')}, "
          f"{c.get('dt', 0)/60:.1f} min live at an identical "
          f"executable-reach key; the paper re-verified by the "
          f"live needle precheck)", flush=True)

fails = []
if live:
    with cf.ProcessPoolExecutor(max_workers=NW) as ex:
        for name, rc, dt, tail in ex.map(run, live):
            print(f"  {'PASS' if rc == 0 else 'FAIL'} {name} "
                  f"(exit {rc}, {dt/60:.1f} min)", flush=True)
            if rc != 0:
                fails.append(name)
                print(tail, flush=True)
            else:
                cache[keys[name]] = {
                    "file": name, "rc": 0, "dt": dt,
                    "when": time.strftime("%Y-%m-%dT%H:%MZ",
                                          time.gmtime())}
                os.makedirs(os.path.dirname(CACHE_PATH),
                            exist_ok=True)
                json.dump(cache, open(CACHE_PATH, "w"),
                          indent=0, sort_keys=True)

print(f"\ncensus: {len(live) - len(fails)} live PASS + "
      f"{len(cached)} cached PASS + {len(fails)} FAIL "
      f"of {len(names)}", flush=True)
print(("TOWER PASS (%d/%d)" % (len(names), len(names)))
      if not fails else f"TOWER FAILURES: {fails}", flush=True)
sys.exit(1 if fails else 0)
