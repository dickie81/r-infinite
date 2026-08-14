#!/usr/bin/env python3
"""The parallel tower driver: execute EVERY tower verifier concurrently
(each in manifest chain mode, so no serial recursion), and pass iff all
pass. This is the full-re-execution battery for certification rounds --
wall time = the longest single verifier instead of the serial sum.
Manifest-vs-disk integrity is checked for all members up front.
"""
import concurrent.futures as cf
import hashlib, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
MAN = json.load(open(os.path.join(HERE, "tower_manifest.json"),
                     encoding="utf-8"))

bad = []
for e in MAN["tower"]:
    p = os.path.join(HERE, e["file"])
    if hashlib.sha256(open(p, "rb").read()).hexdigest() != e["sha256"]:
        bad.append(e["file"])
if bad:
    print(f"MANIFEST STALE for: {bad}", flush=True)
    sys.exit(2)
print(f"manifest integrity: {len(MAN['tower'])} members verified",
      flush=True)

env = dict(os.environ, CASCADE_CHAIN="manifest")

def run(name):
    t0 = time.time()
    r = subprocess.run([sys.executable, os.path.join(HERE, name)],
                       capture_output=True, text=True, env=env)
    return name, r.returncode, time.time() - t0, r.stdout[-400:]

names = [e["file"] for e in MAN["tower"]]
fails = []
with cf.ProcessPoolExecutor(max_workers=min(4, os.cpu_count() or 4)) as ex:
    for name, rc, dt, tail in ex.map(run, names):
        print(f"  {'PASS' if rc == 0 else 'FAIL'} {name} "
              f"(exit {rc}, {dt/60:.1f} min)", flush=True)
        if rc != 0:
            fails.append(name)
            print(tail, flush=True)
print(("\nTOWER PASS (%d/%d)" % (len(names), len(names))) if not fails
      else f"\nTOWER FAILURES: {fails}", flush=True)
sys.exit(1 if fails else 0)
