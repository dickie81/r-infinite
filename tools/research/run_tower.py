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
where code_sha is ckpt_key's docstring-stripped-AST hash -- prose
edits to members or their substrates do NOT invalidate; any
executable change anywhere in the member's code reach does. The
PAPER stays byte-hashed deliberately: the needle gates match raw
substrings of the paper, so any paper byte can flip a gate outcome
-- a paper edit owes one live tower. The manifest sha is NOT in
the key (round 254): manifest-vs-disk consistency is re-verified
LIVE by this driver's integrity precheck on every invocation, so
binding it would only re-import byte sensitivity. NOT bound:
committed checkpoint DATA files -- content-addressed to the
closure's own bytes by the instruments' keying, and every gate
re-runs live on every non-cached run; data-only corruption is the
gates' job, not the cache key's.
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


def member_key(name):
    h = hashlib.sha256()
    h.update(PAPER_SHA.encode())
    # round-253 F253-1 + round-254: the member's computed import
    # closure (which contains the member itself), each file at
    # its EXECUTABLE-CONTENT hash -- prose edits hold the cache
    for f in sorted(ckpt_key.producer_closure((name,), HERE)):
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
          f"{c.get('dt', 0)/60:.1f} min live at identical "
          f"member/manifest/paper hashes)", flush=True)

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
