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
PAPER stays byte-hashed deliberately: the needle gates match raw
substrings of the paper, so any paper byte can flip a gate outcome
-- a paper edit owes one live tower. The manifest sha is NOT in
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
import hashlib, json, os, subprocess, sys, time

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
if bad:
    print(f"MANIFEST STALE for: {bad}", flush=True)
    sys.exit(2)
print(f"manifest integrity: {len(MAN['tower'])} members verified",
      flush=True)

PAPER_SHA = _sha(PAPER_PATH)


sys.path.insert(0, HERE)
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
        for root in {d} | set(CODE_ROOTS):
            pth = os.path.join(root, m + ".py")
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


def member_key(name):
    h = hashlib.sha256()
    h.update(PAPER_SHA.encode())
    # rounds 253-255: the member's full code REACH (imports +
    # named-.py spawn chain, transitive), each file at its
    # EXECUTABLE-CONTENT hash -- prose edits hold the cache
    for f in sorted(member_reach(name)):
        h.update(f.encode())
        h.update(ckpt_key.code_sha(
            os.path.join(HERE, f)).encode())
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
          f"executable-reach + paper key)", flush=True)

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
