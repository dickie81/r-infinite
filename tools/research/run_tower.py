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
helper` and relative imports; round 398 F398-B1/B2: `__import__` with
a constant name and fromlist, and a script spawned from a code-root
subdirectory by bare name, relative path or dotted module spec), with
a floor on the committed reach (F398-B6); it prints "reach precheck:
..." when it passes.

ROUND 399 (F399-A1/B1/B2/C1, the static walk's fourth round of missed
spellings): the run is observed. Every live member runs under the
tracer (reach_trace/sitecustomize.py, pinned); the files it read or
spawned are hashed and stored with its PASS, and a cache hit needs the
static key AND every recorded file unchanged. The tracer's own sabotage
case runs first ("dependency precheck: ..."). See THE DYNAMIC
DEPENDENCY RECORD below.
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
               "precheck_probes.py", "render_lint.py",   # render_lint: round 395
               "reach_trace/sitecustomize.py"}          # the tracer: round 399
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


_PY_INDEX = {}


def _py_files(roots):
    """Every .py file under the roots, subdirectories included."""
    key = tuple(roots)
    if key not in _PY_INDEX:
        out = []
        for root in roots:
            for dp, dn, fn in os.walk(root):
                dn[:] = sorted(x for x in dn
                               if x not in ("__pycache__", "checkpoints"))
                out += [os.path.join(dp, f) for f in sorted(fn)
                        if f.endswith(".py")]
        _PY_INDEX[key] = out
    return _PY_INDEX[key]


_SUFFIX_INDEX = {}


def _suffix_index(roots):
    """Every path suffix ("/b.py", "/a/b.py", ...) of every .py file
    under the roots, mapped to the files that end with it."""
    key = tuple(roots)
    if key not in _SUFFIX_INDEX:
        idx = {}
        for f in _py_files(roots):
            parts = f.split(os.sep)
            for i in range(1, len(parts)):
                idx.setdefault(os.sep + os.sep.join(parts[-i:]), set()).add(f)
        _SUFFIX_INDEX[key] = idx
    return _SUFFIX_INDEX[key]


_TOKEN_MEMO = {}


def _resolve_token(tok, roots, text_roots):
    key = (tok, tuple(roots), tuple(text_roots))
    if key in _TOKEN_MEMO:
        return _TOKEN_MEMO[key]
    out = set()
    idx = _suffix_index(roots)
    if tok.endswith(".tex"):
        base = os.path.basename(tok)
        if base[:-4].replace("_", "").replace("-", "").isalnum():
            for r in text_roots:
                pth = os.path.join(r, base)
                if os.path.exists(pth):
                    out = {pth}
                    break
    elif "/" in tok:
        if tok.endswith(".py"):
            tail = os.path.normpath(tok)
            while tail.startswith(".." + os.sep):
                tail = tail[3:]
            out = set(idx.get(os.sep + tail.lstrip(os.sep), ()))
    else:
        stem = tok[:-3] if tok.endswith(".py") else tok
        parts = stem.split(".")
        if all(x.replace("_", "").isalnum() for x in parts):
            if len(parts) == 1 or not tok.endswith(".py"):
                # a module spec (-m, import_module, a bare stem): every
                # package __init__.py on the dotted path, the module, and
                # the package's __init__ and __main__ (round 399
                # F399-B1/C1: -m on a regular package runs its __init__)
                tails = [os.path.join(*parts[:i], "__init__.py")
                         for i in range(1, len(parts) + 1)]
                tails += [os.path.join(*parts) + ".py",
                          os.path.join(*parts, "__main__.py")]
                for t in tails:
                    out |= idx.get(os.sep + t, set())
    _TOKEN_MEMO[key] = out
    return out


def _resolve(sc, roots=None, text_roots=None):
    """Resolve a string constant to the substrate files it may name
    (absolute paths; empty for non-substrate constants). The constant is
    read word by word (round 399 F399-A1/B1: a shell command string
    names its scripts between spaces), each word with surrounding quotes
    dropped. Code: a bare .py name or module stem, searched through
    every code root and its subdirectories (round 398 F398-B2); a
    relative .py path, matched as a path suffix, leading separators and
    "../" dropped (round 399 F399-B1/C1: "/sub/x.py" from an f-string or
    a concatenation); a dotted module spec, with every package
    __init__.py on its path and a package's __main__.py (round 399). TEXT
    substrates (round-257 F257-1): a .tex name, directory part dropped
    (round 399 F399-C1), searched in src/ -- three reach files (one
    manifest member plus two chained verifiers) needle-gate raw
    substrings of the cascade tex papers, so those bytes are verdict
    inputs and must be in the key (bound by raw-byte sha via code_sha's
    non-.py fallback), exactly the rationale that byte-binds the main
    paper."""
    roots = CODE_ROOTS if roots is None else roots
    text_roots = TEXT_ROOTS if text_roots is None else text_roots
    out = set()
    words = sc.split()
    for w in words:
        w = w.strip("'\"")
        # inside a sentence or a command line only a word shaped like a
        # file reference binds (a .py or .tex name, a path, a dotted
        # spec): a prose word that happens to equal a file's stem would
        # pull an unrelated helper into the reach; a constant that is a
        # single word keeps the full stem rule (spawns built as s + ".py")
        if w and (len(words) == 1 or w.endswith((".py", ".tex"))
                  or "/" in w or "." in w.strip(".")):
            out |= _resolve_token(w, roots, text_roots)
    return out


_NAMED_MEMO = {}


def _named_abs(path, roots=None, text_roots=None):
    """Every substrate named by a string constant (bare .py name,
    module stem, relative .py path, dotted module spec, or .tex name)
    in the DOCSTRING-STRIPPED AST of the file at path -- the
    subprocess/chain/needle reach the import walk cannot see.
    Over-approximates (any mention counts): the safe direction.
    Memoized per file and roots per run."""
    roots = CODE_ROOTS if roots is None else roots
    text_roots = TEXT_ROOTS if text_roots is None else text_roots
    key = (path, tuple(roots), tuple(text_roots))
    if key in _NAMED_MEMO:
        return _NAMED_MEMO[key]
    import ast
    tree = ast.parse(open(path, "rb").read())
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
            out |= _resolve(node.value, roots, text_roots)
    _NAMED_MEMO[key] = out
    return out


def _named_py(rel):
    """HERE-relative form of _named_abs for the file at rel; non-.py
    reach entries (tex substrates) expand to nothing."""
    if not rel.endswith(".py"):
        return set()
    return {os.path.relpath(p, HERE)
            for p in _named_abs(os.path.join(HERE, rel))}


_IMP_MEMO = {}


def _import_targets(path, roots=None):
    """Per import statement of the file at path: (top-level name or
    None for a relative import, the directories it resolves against,
    the dotted candidates as path-segment lists). Round 397 F397-B1
    (the F269-3 class, its other spelling): `from pkg import helper`
    may name the SUBMODULE pkg/helper.py, so pkg.helper is a candidate
    beside pkg; a relative import resolves against its own package
    directory, `from . import x` included (module None). Round 398
    (F398-B1): a call to __import__ or importlib.import_module with a
    constant name is an import of that name, its constant fromlist
    entries candidates beside it."""
    import ast
    roots = set(CODE_ROOTS if roots is None else roots)
    tree = ast.parse(open(path, "rb").read())
    d = os.path.dirname(path) or HERE
    out = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            fn = node.func
            fname = (fn.id if isinstance(fn, ast.Name) else
                     fn.attr if isinstance(fn, ast.Attribute) else None)
            kw = {k.arg: k.value for k in node.keywords if k.arg}
            arg = node.args[0] if node.args else kw.get("name")
            pkg_arg = (node.args[1] if len(node.args) > 1 else
                       kw.get("package")) if fname == "import_module" else None
            name = (arg.value if isinstance(arg, ast.Constant)
                    and isinstance(arg.value, str) else None)
            if (name and name.startswith(".") and isinstance(pkg_arg, ast.Constant)
                    and isinstance(pkg_arg.value, str)):
                # round 399 F399-C1: import_module(".x", "pkg") is pkg.x
                lvl = len(name) - len(name.lstrip("."))
                bp = pkg_arg.value.split(".")
                bp = bp[:len(bp) - (lvl - 1)] if lvl > 1 else bp
                name = ".".join(bp + ([name.lstrip(".")]
                                      if name.lstrip(".") else []))
            if (fname in ("__import__", "import_module") and name
                    and all(x.isidentifier() for x in name.split("."))):
                base = name.split(".")
                fl = [k.value for k in node.keywords if k.arg == "fromlist"]
                fl += node.args[3:4]
                names = [e.value for f in fl
                         if isinstance(f, (ast.List, ast.Tuple))
                         for e in f.elts
                         if isinstance(e, ast.Constant)
                         and isinstance(e.value, str) and e.value != "*"]
                out.append((base[0], {d} | roots,
                            [base] + [base + [n] for n in names]))
        if isinstance(node, ast.Import):
            for a in node.names:
                out.append((a.name.split(".")[0], {d} | roots,
                            [a.name.split(".")]))
        elif isinstance(node, ast.ImportFrom):
            base = node.module.split(".") if node.module else []
            if node.level:
                pkg = d
                for _ in range(node.level - 1):
                    pkg = os.path.dirname(pkg)
                top = None
            else:
                top, rr = base[0], {d} | roots
            cands = [base] if base else []
            cands += [base + [a.name] for a in node.names if a.name != "*"]
            out.append((top, rr if not node.level else {pkg}, cands))
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


def _local_imports(path, roots=None):
    """Absolute paths of the local files the imports of path resolve to."""
    out = set()
    for _top, rr, cands in _import_targets(path, roots):
        for parts in cands:
            out |= _local_files(rr, parts)
    return out


def _reach_abs(path, roots, text_roots=None):
    """The fixed-point reach of the file at path over both expansions,
    against the given code roots alone (absolute paths) -- the form the
    reach walk's own sabotage case runs on a temporary tree."""
    reach, frontier = set(), {path}
    while frontier:
        f = frontier.pop()
        if f in reach:
            continue
        reach.add(f)
        if f.endswith(".py"):
            frontier |= (_local_imports(f, roots)
                         | _named_abs(f, roots, text_roots)) - reach
    return reach


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
RENDER_PROBE_CASES, RENDER_SURFACES = 42, 2   # 7 -> 10 at the round-395 sweep (L7-L9), 15 at round 396 (L10-L14), 23 at round 397 (L10, L13 widened; L15), 37 at round 398 (L10, L15 widened; L16, L17), 42 at round 399 (L18-L20 split out or new; L16 cell counts)
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
# part, and joined in source order, by position (round 397 F397-B4:
# the round-396 join followed ast.walk's breadth-first order; round 398
# F398-B7; round 399 F399-B8: field order put a conditional's test
# before its body and a dict display's keys before its values), a range
# written with
# any Unicode dash (category Pd) or the minus sign, and a
# floor on the number of labels scanned, so a renamed gate cannot pass
# by scanning nothing (round 396 F396-B8 widened the aliases, dashes and
# joins). Not read: a label passed in a variable or by keyword, and a
# numeral that is not a string constant (an f-string's {103}, a % or
# .format argument). Its own sabotage cases run first.
import unicodedata as _ud
_DASHES = "".join(ch for ch in map(chr, range(0x110000))
                  if _ud.category(ch) == "Pd") + "\u2212"
_CENSUS_NUM = re.compile(r"\d+ (?:scripts )?cited in place"
                         r"|1i\s*[" + re.escape(_DASHES) + r"]+\s*1[a-z]{2}")
GATE_LABELS_MIN = 650


def _consts_in_order(node):
    """The string constants under node, in source order: sorted by
    position (round 399 F399-B8: field order put a dict display's keys
    before its values), ties -- the parts of an f-string, which share
    its position before Python 3.12 -- kept in field order."""
    found = []

    def walk(n):
        if isinstance(n, _ast.Constant) and isinstance(n.value, str):
            found.append(((getattr(n, "lineno", 0), getattr(n, "col_offset", 0),
                           len(found)), n.value))
        for c in _ast.iter_child_nodes(n):
            walk(c)
    walk(node)
    return [v for _, v in sorted(found)]


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
                  'J, K = gate, print\nJ(f"g7 {k} the range 1i" + "\u2e3a1ca", 1)\n'
                  'gate({"88": " cited", " in": " place"}["88"], 1)\n')
if not (_CENSUS_NUM.search("88 cited in place; the range 1i–1bl")
        and _CENSUS_NUM.search("Theorems 1i--1bj")
        and not _CENSUS_NUM.search("the anchored count and range needles")
        and _label_hits(_sab) == (8, [2, 3, 5, 7, 8, 10, 11])):
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


def _third_party_in(path, roots=None):
    out = set()
    for top, roots, cands in _import_targets(path, roots):
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


# THE DYNAMIC DEPENDENCY RECORD (round 399, F399-A1/B1/B2/C1: the
# F269-3 class in its fourth round -- shell command strings, -m on a
# regular package, path fragments with a prefix, __import__(name=...),
# relative import_module, .tex names with a directory -- each an
# ordinary spelling the static walk missed, three demonstrated as a
# stale cached PASS). The static key cannot enumerate every spelling;
# the run can be observed. Every live member runs with the tracer
# (reach_trace/sitecustomize.py, pinned) first on PYTHONPATH: an audit
# hook records every file the member's Python processes open for
# reading and every command line they spawn. The files under the
# repository that the run read or named, each .py widened by its static
# reach (a child started in isolated mode loads no tracer), are hashed
# and stored with the PASS; a cache hit needs the static key AND every
# recorded file unchanged (a dropped dependency only re-runs a member:
# the safe direction). Excluded: .git, __pycache__, the two markdown
# paper surfaces (the needle precheck evaluates them live), this cache
# and the manifest (integrity-checked above) and the tracer itself. A
# .py read from outside both the repository and the Python installation
# fails the member (external code). An entry with no record (written
# before round 399) is not served; the member runs live once.
import site as _site
import sysconfig as _sysconfig
import tempfile as _tempfile
REPO = os.path.realpath(os.path.join(HERE, "..", ".."))
TRACE_DIR = os.path.realpath(os.path.join(HERE, "reach_trace"))
_DEP_SKIP = {os.path.realpath(x) for x in (
    os.path.join(REPO, "riemann-indistinguishability.md"),
    os.path.join(REPO, "cascade-riemann-formulation.md"),
    CACHE_PATH, MAN_PATH)}
_ENV_DIRS = tuple(sorted({os.path.realpath(x) + os.sep for x in (
    [sys.prefix, sys.base_prefix, sys.exec_prefix]
    + list(_site.getsitepackages()) + [_site.getusersitepackages()]
    + list(_sysconfig.get_paths().values())) if x}))


def _trace_env(trace):
    pp = env.get("PYTHONPATH")
    return dict(env, CASCADE_TRACE=trace,
                PYTHONPATH=TRACE_DIR + (os.pathsep + pp if pp else ""))


def _trace_deps(trace, root):
    """(deps, external) from a trace file: the files under root the run
    read or named on a spawned command line (absolute paths, the
    exclusions applied, each .py widened by its static reach), and the
    .py files it read from outside both root and the Python
    installation."""
    try:
        lines = open(trace, encoding="utf-8",
                     errors="surrogateescape").read().splitlines()
    except OSError:
        lines = []
    deps, external = set(), set()
    for ln in lines:
        kind, _, rest = ln.partition(" ")
        if kind == "R":
            cands = [rest]
        elif kind == "X":
            words = rest.split(" ")
            cands = [os.path.join(words[0], w) for w in words[1:] if w]
        else:
            continue
        for c in cands:
            q = os.path.realpath(c)
            if not os.path.isfile(q):
                continue
            if q.startswith(root + os.sep):
                parts = q[len(root) + 1:].split(os.sep)
                if (parts[0] == ".git" or "__pycache__" in parts
                        or q in _DEP_SKIP
                        or q.startswith(TRACE_DIR + os.sep)):
                    continue
                deps.add(q)
            elif q.endswith(".py") and not q.startswith(_ENV_DIRS):
                external.add(q)
    for q in [d for d in deps if d.endswith(".py")]:
        deps |= {os.path.realpath(x) for x in _reach_abs(q, CODE_ROOTS)
                 if os.path.realpath(x).startswith(root + os.sep)
                 and os.path.isfile(x)}
    return deps, external


_DEP_MEMO = {}


def _dep_hash(path):
    if path not in _DEP_MEMO:
        h = None
        if path.endswith(".py"):
            try:
                h = ckpt_key.code_sha(path, strip_prints=False)
            except Exception:
                h = None
        _DEP_MEMO[path] = h or _sha(path)
    return _DEP_MEMO[path]


def _deps_ok(entry):
    deps = entry.get("deps")
    if deps is None:
        return False
    for rel, h in deps.items():
        q = os.path.join(REPO, rel)
        if not os.path.isfile(q) or _dep_hash(q) != h:
            return False
    return True


def run(name):
    t0 = time.time()
    fd, trace = _tempfile.mkstemp(prefix="tower_trace_", suffix=".txt")
    os.close(fd)
    try:
        r = subprocess.run([sys.executable, os.path.join(HERE, name)],
                           capture_output=True, text=True,
                           env=_trace_env(trace))
        deps, external = _trace_deps(trace, REPO)
    finally:
        os.unlink(trace)
    hashes = {os.path.relpath(q, REPO): _dep_hash(q) for q in sorted(deps)}
    return (name, r.returncode, time.time() - t0, r.stdout[-400:], hashes,
            sorted(external))


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
    # what a failure prints: the FAIL lines (the first 12, the rest
    # counted), the stdout tail when there are none, and the stderr tail
    # in every case (round 397 F397-A6/B3: a crash's traceback went to
    # stderr and was dropped; round 398 F398-B5: stderr then displaced
    # the stdout cause, and a long FAIL list cut the traceback off)
    fails = [l for l in r.stdout.splitlines() if "FAIL" in l]
    show = fails[:12] + ([f"... {len(fails) - 12} more FAIL lines"]
                         if len(fails) > 12 else [])
    if not fails:
        show = ["stdout tail: " + l for l in r.stdout.strip().splitlines()[-4:]]
    show += ["stderr: " + l for l in r.stderr.strip().splitlines()[-6:]]
    return name, r.returncode, time.time() - t0, show


readers = discover_readers()
r_fail = []
with cf.ProcessPoolExecutor(max_workers=NW) as ex:
    for name, rc, dt, show in ex.map(run_reader, readers):
        if rc != 0:
            r_fail.append(name)
            print(f"  READER FAIL {name} (exit {rc}):", flush=True)
            for l in show:
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
# The reach walk's own sabotage case (round 397 F397-B1; widened and
# made hermetic at round 398, F398-B1/B2/B6; widened at round 399,
# F399-B1/B2/B3/C1/C2): the spellings planted below, in a temporary
# directory outside the repository, walked against that directory ALONE
# (code and text roots both) through the full fixed point, and through
# the import half alone. The planted spellings: `from pkg import
# helper`; a dotted import of a namespace package; `from nsp import sib`
# and its relative `from . import mod`; __import__ with a constant name,
# a keyword name, a keyword list fromlist, a positional list fromlist
# and a tuple fromlist; importlib.import_module (attribute form), and
# relative with a constant package; a script named as a bare
# subdirectory file, a relative path, an f-string path led by "/",
# a "../" path and a shell command string; -m on a regular package's
# module and on a package; a .tex named with a directory. numpy and an
# out-of-root module stay third-party; the namespace package stays
# local. A spelling not planted here is not claimed; the dynamic record
# below binds what a live run actually reads.
import tempfile as _tempfile
with _tempfile.TemporaryDirectory() as _td:
    _plant = {"zzpkg/__init__.py": "", "zzpkg/helper.py": "",
              "zzpkg/viaimp.py": "", "zzpkg/viafrom.py": "",
              "zzpkg/viakw.py": "", "zzpkg/viapos.py": "",
              "zzpkg/viatup.py": "", "zzpkg/viaim.py": "",
              "zzpkg/viarel.py": "",
              "nsp/mod.py": "", "nsp/sib.py": "from . import mod\n",
              "sub/check.py": "", "sub/deep.py": "", "sub/dotted.py": "",
              "sub/fslash.py": "", "sub/updir.py": "", "shellrun.py": "",
              "rpkg/__init__.py": "", "rpkg/leaf.py": "",
              "mpkg/__init__.py": "", "mpkg/__main__.py": "",
              "srcx/paper.tex": "",
              "m.py": "from zzpkg import helper\nimport nsp.mod\n"
                      "from nsp import sib\nimport numpy.linalg\n"
                      "__import__('zzpkg.viaimp')\n"
                      "__import__('zzpkg', fromlist=['viafrom'])\n"
                      "__import__(name='zzpkg.viakw')\n"
                      "__import__('zzpkg', None, None, ['viapos'])\n"
                      "__import__('zzpkg', fromlist=('viatup',))\n"
                      "importlib.import_module('zzpkg.viaim')\n"
                      "importlib.import_module('.viarel', 'zzpkg')\n"
                      "__import__('outside_mod')\n"
                      "X = ['sub/check.py', 'deep.py', 'sub.dotted',\n"
                      "     f'{H}/sub/fslash.py', '../sub/updir.py',\n"
                      "     'python3 shellrun.py --flag',\n"
                      "     ['-m', 'rpkg.leaf'], ['-m', 'mpkg'],\n"
                      "     'srcx/paper.tex']\n"}
    for _f, _t in _plant.items():
        os.makedirs(os.path.dirname(os.path.join(_td, _f)), exist_ok=True)
        open(os.path.join(_td, _f), "w").write(_t)
    _tx_roots = (os.path.join(_td, "srcx"),)
    _got = [sorted(os.path.relpath(p, _td)
                   for p in _reach_abs(os.path.join(_td, f), (_td,),
                                       _tx_roots))
            for f in ("m.py", "nsp/sib.py")]
    # the import half alone (the named-file half also binds the
    # dotted and fromlist spellings, so the closure cannot tell which
    # half did)
    _got.append(sorted(os.path.relpath(p, _td) for p in
                       _local_imports(os.path.join(_td, "m.py"), (_td,))))
    _tp = _third_party_in(os.path.join(_td, "m.py"), (_td,))
_want = [sorted(_plant), ["nsp/mod.py", "nsp/sib.py"],
         sorted(["nsp/mod.py", "nsp/sib.py", "zzpkg/__init__.py"]
                + [f"zzpkg/{x}.py" for x in ("helper", "viafrom", "viaimp",
                                              "viakw", "viapos", "viatup",
                                              "viaim", "viarel")])]
if _got != _want or _tp != {"numpy", "outside_mod"}:
    print(f"REACH PRECHECK FAILURE: the reach walk missed its sabotage "
          f"case (reached {_got}, third-party {sorted(_tp)})",
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
# a floor on the committed reach (round 398 F398-B6: a walk broken
# outside the functions the sabotage case calls, the HERE-relative
# wrappers, dropped the union from 109 files to 58 and passed)
REACH_FILES_MIN = 109
_union = set().union(*(member_reach(n) for n in names))
if len(_union) < REACH_FILES_MIN:
    print(f"REACH PRECHECK FAILURE: the members' reach holds {len(_union)} "
          f"files, below the floor {REACH_FILES_MIN}", flush=True)
    sys.exit(2)
print(f"reach precheck: {len(names)} members, {len(_union)} reach files "
      f"(floor {REACH_FILES_MIN}), 0 unresolved imports; sabotage case "
      f"reached {len(_want[0])} planted files", flush=True)
# the tracer's own sabotage case (round 399): a planted script in a
# temporary root reaches each spelling round 399 found, each through a
# file only that spelling touches -- a shell command string, os.system,
# -m on a regular package's module and on a package, an f-string path,
# __import__(name=...) after a sys.path insert, a glob-discovered
# script, a data file, a .tex named with a directory, a child started
# with -E (no tracer: recorded from the spawn line, its own import only
# through the static widening) -- and imports a module from a second
# directory outside the root, which must be classed external
_TPLANT = {"a_shell.py": "", "b_system.py": "", "pkg/__init__.py": "",
           "pkg/mod.py": "", "pkg2/__init__.py": "", "pkg2/__main__.py": "",
           "sub/fsub.py": "", "sub/chain_a.py": "", "out/zz_outside.py": "",
           "data/table.json": "{}", "data/part0.tex": "x",
           "iso.py": "import iso_dep\n", "iso_dep.py": "",
           "m.py": (
               "import glob, os, subprocess, sys\n"
               "H = os.path.dirname(os.path.abspath(__file__))\n"
               "E = sys.executable\n"
               "subprocess.run(f'\"{E}\" a_shell.py', shell=True, cwd=H,"
               " check=True)\n"
               "assert os.system(f'cd \"{H}\" && \"{E}\" b_system.py') == 0\n"
               "subprocess.run([E, '-m', 'pkg.mod'], cwd=H, check=True)\n"
               "subprocess.run([E, '-m', 'pkg2'], cwd=H, check=True)\n"
               "subprocess.run([E, f'{H}/sub/fsub.py'], check=True)\n"
               "sys.path.insert(0, os.path.join(H, 'out'))\n"
               "__import__(name='zz_outside')\n"
               "for f in glob.glob(os.path.join(H, 'sub', 'chain_*.py')):\n"
               "    subprocess.run([E, f], check=True)\n"
               "open(os.path.join(H, 'data', 'table.json')).read()\n"
               "open(H + '/data/part0.tex').read()\n"
               "subprocess.run([E, '-E', os.path.join(H, 'iso.py')], cwd=H,"
               " check=True)\n"
               "sys.path.insert(0, sys.argv[1])\n"
               "import ext_mod\n")}
with _tempfile.TemporaryDirectory() as _tr, \
        _tempfile.TemporaryDirectory() as _tx:
    _tr, _tx = os.path.realpath(_tr), os.path.realpath(_tx)
    for _f, _t in _TPLANT.items():
        os.makedirs(os.path.dirname(os.path.join(_tr, _f)), exist_ok=True)
        open(os.path.join(_tr, _f), "w").write(_t)
    open(os.path.join(_tx, "ext_mod.py"), "w").write("")
    _fd, _trf = _tempfile.mkstemp(prefix="tower_trace_", suffix=".txt")
    os.close(_fd)
    _trr = subprocess.run([sys.executable, os.path.join(_tr, "m.py"), _tx],
                          capture_output=True, text=True, cwd=_tr,
                          env=_trace_env(_trf))
    _tdeps, _text = _trace_deps(_trf, _tr)
    os.unlink(_trf)
    _tgot = {os.path.relpath(q, _tr) for q in _tdeps}
    _textn = {os.path.basename(q) for q in _text}
if (_trr.returncode != 0 or _tgot != set(_TPLANT)
        or _textn != {"ext_mod.py"}):
    print(f"DEPENDENCY PRECHECK FAILURE: the tracer missed its sabotage "
          f"case (rc {_trr.returncode}; missed "
          f"{sorted(set(_TPLANT) - _tgot)}; extra {sorted(_tgot - set(_TPLANT))}; "
          f"external {sorted(_textn)}) {_trr.stderr[-300:]}", flush=True)
    sys.exit(2)
print(f"dependency precheck: the tracer's sabotage case recorded "
      f"{len(_tgot)} planted files and 1 external module", flush=True)

cached = [] if fresh else \
    [n for n in names if cache.get(keys[n], {}).get("rc") == 0
     and _deps_ok(cache[keys[n]])]
live = [n for n in names if n not in cached]
for n in cached:
    c = cache[keys[n]]
    print(f"  PASS {n} (cached {c.get('when', '?')}, "
          f"{c.get('dt', 0)/60:.1f} min live at an identical "
          f"executable-reach key, {len(c['deps'])} recorded dependencies "
          f"unchanged; the paper re-verified by the live needle "
          f"precheck)", flush=True)

fails = []
if live:
    with cf.ProcessPoolExecutor(max_workers=NW) as ex:
        for name, rc, dt, tail, deps, external in ex.map(run, live):
            if rc == 0 and external:
                rc = "external code"
            print(f"  {'PASS' if rc == 0 else 'FAIL'} {name} "
                  f"(exit {rc}, {dt/60:.1f} min, {len(deps)} recorded "
                  f"dependencies)", flush=True)
            if rc != 0:
                fails.append(name)
                print(tail, flush=True)
                if external:
                    print(f"  EXTERNAL CODE read from outside the "
                          f"repository and the Python installation: "
                          f"{external}", flush=True)
            else:
                cache[keys[name]] = {
                    "file": name, "rc": 0, "dt": dt, "deps": deps,
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
