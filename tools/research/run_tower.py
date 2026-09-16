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
               "precheck_probes.py"}
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
    import ast
    tree = ast.parse(open(os.path.join(HERE, rel), "rb").read())
    mods = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            mods.add(node.module)
        elif isinstance(node, ast.Import):
            mods.update(a.name for a in node.names)
    d = os.path.dirname(os.path.join(HERE, rel)) or HERE
    out = set()
    for m in mods:
        # round-269 F269-3: dotted local imports resolve as path
        # segments -- the old `m + ".py"` probe never existed for
        # `import pkg.helper`, so a package-housed helper escaped
        # BOTH the precheck scan and the cache key (a demonstrated
        # stale-PASS channel against paper AND code edits). Every
        # module file and every package __init__.py on the dotted
        # path joins the reach.
        parts = m.split(".")
        for root in {d} | set(CODE_ROOTS):
            cands = [os.path.join(root, *parts) + ".py"]
            for i in range(1, len(parts) + 1):
                cands.append(os.path.join(root, *parts[:i],
                                          "__init__.py"))
            for pth in cands:
                if os.path.exists(pth):
                    out.add(os.path.relpath(pth, HERE))
    _IMP_MEMO[rel] = out
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
    return h.hexdigest()[:24]


cache = {}
if os.path.exists(CACHE_PATH):
    try:
        cache = json.load(open(CACHE_PATH, encoding="utf-8"))
    except Exception:
        cache = {}

fresh = os.environ.get("TOWER_FRESH") == "1"
# thread pinning (round 252, measured): 4 workers x full-core
# BLAS oversubscribed the box ~4x -- cascade_heatflow_energy ran
# 105 min in-tower vs 38 s standalone. Each member gets
# cpu_count/workers BLAS threads.
NW = min(4, os.cpu_count() or 4)
THR = str(max(1, (os.cpu_count() or 4)//NW))
env = dict(os.environ, CASCADE_CHAIN="manifest",
           OMP_NUM_THREADS=THR, OPENBLAS_NUM_THREADS=THR,
           MKL_NUM_THREADS=THR, NUMEXPR_NUM_THREADS=THR)


def run(name):
    t0 = time.time()
    r = subprocess.run([sys.executable, os.path.join(HERE, name)],
                       capture_output=True, text=True, env=env)
    return name, r.returncode, time.time() - t0, r.stdout[-400:]


names = [e["file"] for e in MAN["tower"]]
keys = {n: member_key(n) for n in names}
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
