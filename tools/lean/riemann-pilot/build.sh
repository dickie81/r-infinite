#!/usr/bin/env bash
# Compile the pilot: every src/*.lean into build/ (olean + ilean). The import graph is read from the
# sources. Files are compiled in parallel (JOBS at a time, default: number of cores), each as soon as
# the pilot files it imports are done. A file is recompiled only if its olean is missing or older than
# its source or than the olean of anything it imports, so after an edit only that file and its
# dependents are rebuilt. FORCE=1 rebuilds everything.
# MATHLIB: a built Mathlib checkout at the commit in MATHLIB_REV (default ./mathlib4).
# SRC: the source directory (default ./src). external/dh/build.sh sets it to compile the
# Davenport–Heilbronn layer into the same build/; a file is then also stale if the olean of a module it
# imports from another layer is newer than its own.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "${MATHLIB:-$HERE/mathlib4}"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$HERE/build"
export LEAN_PATH="$(lake env printenv LEAN_PATH):$HERE/build"
exec python3 - "$HERE" "${JOBS:-$(nproc)}" "${FORCE:-0}" "${SRC:-$HERE/src}" <<'EOF'
import os, re, sys, time, subprocess, threading
here, jobs, force, src = sys.argv[1], int(sys.argv[2]), sys.argv[3] == '1', sys.argv[4]
out = os.path.join(here, 'build')
mods = sorted(f[:-5] for f in os.listdir(src) if f.endswith('.lean'))
deps, ext = {}, {}
for m in mods:
    d, e = set(), set()
    for l in open(os.path.join(src, m + '.lean'), encoding='utf-8'):
        mm = re.match(r'^\s*(?:public\s+)?import\s+(.+)$', l)
        if mm:
            d |= {t for t in mm.group(1).split() if t in mods}
            e |= {t for t in mm.group(1).split() if t not in mods and os.path.exists(os.path.join(out, t + '.olean'))}
    deps[m], ext[m] = d, e
def mtime(p):
    try: return os.path.getmtime(p)
    except OSError: return None
def olean(m): return os.path.join(out, m + '.olean')
def stale(m):
    o = mtime(olean(m))
    return force or o is None or o < mtime(os.path.join(src, m + '.lean')) or \
        any(mtime(olean(d)) > o for d in deps[m] | ext[m])
done, failed, blocked, running = set(), set(), set(), set()
nbuilt, lock, t00 = 0, threading.Condition(), time.time()
def run(m):
    global nbuilt
    t0 = time.time()
    r = subprocess.run(['lean', '-R', src, '-o', olean(m), '-i', os.path.join(out, m + '.ilean'),
                        os.path.join(src, m + '.lean')], capture_output=True, text=True)
    with lock:
        print(f'== {m} ({time.time() - t0:.0f}s)' + ('' if r.returncode == 0 else ' FAILED'))
        sys.stdout.write(r.stdout + r.stderr); sys.stdout.flush()
        running.discard(m)
        if r.returncode == 0: done.add(m); nbuilt += 1
        else:
            failed.add(m)
            if os.path.exists(olean(m)): os.remove(olean(m))
        lock.notify()
with lock:
    while True:
        todo = [m for m in mods if m not in done | failed | blocked | running]
        if not todo and not running: break
        progress = False
        for m in todo:
            if deps[m] & (failed | blocked): blocked.add(m); progress = True
            elif deps[m] <= done and len(running) < jobs:
                progress = True
                if not stale(m): done.add(m); continue
                running.add(m); threading.Thread(target=run, args=(m,)).start()
        if not progress: lock.wait()
print(f'{nbuilt} compiled, {len(done) - nbuilt} up to date, in {time.time() - t00:.0f}s')
if failed:
    print(f'FAILED: {" ".join(sorted(failed))}; not built: {" ".join(sorted(blocked))}')
    sys.exit(1)
EOF
