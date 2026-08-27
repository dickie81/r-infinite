#!/usr/bin/env python3
"""The parallel tower driver: execute EVERY tower verifier concurrently
(each in manifest chain mode, so no serial recursion), and pass iff all
pass. This is the full-re-execution battery for certification rounds --
wall time = the longest single verifier instead of the serial sum.
Manifest-vs-disk integrity is checked for all members up front.

RESUME CACHE (round 252, owner-commissioned after a container restart
threw away a 45-minute partial run): each member's PASS is recorded in
checkpoints/tower_results.json under a key binding the EXACT inputs of
that pass -- sha256(member bytes) + sha256(tower_manifest.json) +
sha256(the paper) -- so any change to the member, the tower set, or the
paper surface invalidates the cache honestly (every tower member's
census/needle gates read the paper, so the paper hash is a true input).
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

MAN_SHA = _sha(MAN_PATH)
PAPER_SHA = _sha(PAPER_PATH)


def member_key(name):
    h = hashlib.sha256()
    h.update(_sha(os.path.join(HERE, name)).encode())
    h.update(MAN_SHA.encode())
    h.update(PAPER_SHA.encode())
    return h.hexdigest()[:24]


cache = {}
if os.path.exists(CACHE_PATH):
    try:
        cache = json.load(open(CACHE_PATH, encoding="utf-8"))
    except Exception:
        cache = {}

fresh = os.environ.get("TOWER_FRESH") == "1"
env = dict(os.environ, CASCADE_CHAIN="manifest")


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
    with cf.ProcessPoolExecutor(
            max_workers=min(4, os.cpu_count() or 4)) as ex:
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
