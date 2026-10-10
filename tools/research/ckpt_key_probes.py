#!/usr/bin/env python3
"""Sabotage probes for the print-insensitive executable-content hash
(ckpt_key.code_sha, round 282) and the migration's refusals
(ckpt_migrate.plan). Every case states what it expects; the suite
prints a census and exits nonzero on any surprise.

Hash cases (H): pairs of sources that MUST hash equal (a pure print
edit, a docstring edit, a comment edit, an added flush=True) and pairs
that MUST hash differently (an arithmetic mangle; a print whose
argument calls a non-whitelisted function; a print that writes to a
file; a print carrying a walrus; a mangle in a string literal used in
arithmetic; a lambda inside a print; an assignment of print's
return value; a higher-order builtin with key=; a starred argument;
a method call outside the attribute whitelist). Also: two pure
prints reordered hold; a generator inside a print calling only
whitelisted names is stripped; a print-free file hashes identically
under both modes; and the legacy hash (strip_prints=False) DOES
rotate on a print edit (it is what run_tower's member reach key
uses).

Migration cases (M): a checkpoint whose stored script_sha256 matches
no historical version is 'unverifiable'; one whose stored key does
not recompute from its own provenance is 'unverifiable'; one whose
dep changed beyond prints is 'blocked' (M5, hermetic: a synthetic
"historical" version of twoprime_recon.py injected into the resolver;
M5r, from a real historical blob when the clone carries the history,
else the truncated history must make the same checkpoint
'unverifiable' -- a refusal either way); and the migration never
rewrites state. The scratch directory is removed at exit.

This file is integrity-PINNED in tower_manifest.json (keying list)
and RUN by run_tower.py as the keying-probe precheck with its case
count pinned exactly (KEY_PROBE_CASES): an edit here must be followed
by refresh_tower_manifest.py, and an added or removed case by updating
that constant, or the tower fails closed (round 285 F285-3).
"""
import hashlib, json, os, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key

BASE = '''"""doc"""
import math
def run(x):
    # a comment
    y = x*2 + 1
    print(f"IVT cell: y {y:.6f} -> {_fdir(y, 5, False)}", flush=True)
    return y
'''
def H(src):
    return ckpt_key.code_sha_src(src.encode(), "x.py", strip_prints=True)
def L(src):
    return ckpt_key.code_sha_src(src.encode(), "x.py", strip_prints=False)

cases = []
def expect(label, cond):
    cases.append((label, bool(cond)))
    print(("PASS " if cond else "FAIL ") + label, flush=True)

base = H(BASE)
expect("H1 pure print text edit holds the hash",
       H(BASE.replace('IVT cell: y', 'IVT cell -- y')) == base)
expect("H2 print rounding-mode edit holds the hash",
       H(BASE.replace('_fdir(y, 5, False)', '_fdir(y, 4, True)')) == base)
expect("H3 docstring + comment edits hold the hash",
       H(BASE.replace('"""doc"""', '"""a different docstring"""').replace('# a comment', '# another')) == base)
expect("H4 dropping flush=True holds the hash",
       H(BASE.replace(', flush=True', '')) == base)
expect("H5 an arithmetic mangle rotates",
       H(BASE.replace('y = x*2 + 1', 'y = x*2 + 2')) != base)
expect("H6 a print calling a non-whitelisted function is NOT stripped (rotates vs the pure print)",
       H(BASE.replace('_fdir(y, 5, False)', 'mutate(y)')) != base)
expect("H7 a print with file= is NOT stripped",
       H(BASE.replace(', flush=True', ', file=sys.stderr')) != base)
expect("H8 a walrus inside a print is NOT stripped",
       H(BASE.replace('{y:.6f}', '{(z := y):.6f}')) != base)
expect("H9 a lambda inside a print is NOT stripped",
       H(BASE.replace('_fdir(y, 5, False)', '(lambda: y)()')) != base)
expect("H10 assigning print's return value is NOT stripped",
       H(BASE.replace('    print(', '    r = print(')) != base)
expect("H11 a method call outside the attribute whitelist is NOT stripped",
       H(BASE.replace('_fdir(y, 5, False)', "state.pop('a')")) != base)
expect("H12 a string literal in arithmetic still rotates",
       H(BASE.replace('y = x*2 + 1', 'y = float("2")*x + 1')) != base)
expect("H16 a whitelisted higher-order builtin with key= inside a print is NOT stripped",
       H(BASE.replace('_fdir(y, 5, False)', 'max(xs, key=mutator)')) != base)
expect("H17 a starred argument inside a print is NOT stripped",
       H(BASE.replace('    print(f"IVT cell', '    print(*items)\n    print(f"IVT cell')) != base)
expect("H18 a generator inside a print calling only whitelisted names is stripped",
       H(BASE.replace('_fdir(y, 5, False)', "', '.join(str(v) for v in xs)")) == base)
expect("H13 the legacy hash rotates on a pure print edit",
       L(BASE.replace('IVT cell: y', 'IVT cell -- y')) != L(BASE))
expect("H14 two pure prints in different orders hold the hash",
       H(BASE.replace('    print(', '    print("a")\n    print(')) == base)
expect("H15 stripping never changes a print-free file's hash vs legacy",
       H(BASE.replace('    print(f"IVT cell: y {y:.6f} -> {_fdir(y, 5, False)}", flush=True)\n', ''))
       == L(BASE.replace('    print(f"IVT cell: y {y:.6f} -> {_fdir(y, 5, False)}", flush=True)\n', '')))

# migration refusals on a synthetic checkpoint in a scratch checkpoint dir
import ckpt_migrate
tmp = tempfile.mkdtemp()
ckpt_migrate.CKDIR = tmp
fake_sha = hashlib.sha256(b"no such version").hexdigest()
params = {"deps": {"oneprime_interval_core.py": fake_sha}, "round": 1}
key = hashlib.sha256(fake_sha.encode() + json.dumps(params, sort_keys=True).encode()).hexdigest()
fn = os.path.join(tmp, f"probe_{key[:12]}.json")
json.dump({"script_sha256": fake_sha, "key": key, "params": params, "state": {"v": 1}}, open(fn, "w"))
st, det, _, _ = ckpt_migrate.plan(os.path.basename(fn))
expect("M1 an unresolvable provenance hash is 'unverifiable'", st == "unverifiable")
# a real historical hash but a stored key that does not recompute
real = ckpt_key.code_sha(os.path.join(HERE, "oneprime_interval_core.py"), strip_prints=False)
params2 = {"deps": {"oneprime_interval_core.py": real}, "round": 1}
badkey = hashlib.sha256(b"tampered").hexdigest()
fn2 = os.path.join(tmp, f"probe2_{badkey[:12]}.json")
json.dump({"script_sha256": real, "key": badkey, "params": params2, "state": {"v": 1}}, open(fn2, "w"))
st, det, _, _ = ckpt_migrate.plan(os.path.basename(fn2))
expect("M2 a stored key that does not recompute from its provenance is 'unverifiable'", st == "unverifiable")
# a genuine self-consistent checkpoint on the current core file: new key == old key iff
# the core file has no pure prints; either way the plan never touches state
goodkey = hashlib.sha256(real.encode() + json.dumps(params2, sort_keys=True).encode()).hexdigest()
fn3 = os.path.join(tmp, f"probe3_{goodkey[:12]}.json")
json.dump({"script_sha256": real, "key": goodkey, "params": params2, "state": {"v": 7}}, open(fn3, "w"))
st, det, newfile, rec = ckpt_migrate.plan(os.path.basename(fn3))
expect("M3 a self-consistent checkpoint is 'migrate' or 'unchanged', never blocked",
       st in ("migrate", "unchanged"))
expect("M4 a migrated record carries the state unchanged and the old key",
       st == "unchanged" or (rec["state"] == {"v": 7} and rec["migrated"]["from_key"] == goodkey))

# M5 (round 282 F282-1; made hermetic round 283 F283-4): a dep that changed
# beyond prints since the checkpoint was produced is 'blocked'. The
# "historical" version is synthetic -- today's twoprime_recon.py with one
# executable statement appended -- injected into the resolver's table under
# its own old hash, so the case needs no git history at all.
def _refusal_case(tag, old_sha):
    params_ = {"deps": {"twoprime_recon.py": old_sha}, "round": 1}
    key_ = hashlib.sha256(old_sha.encode() + json.dumps(params_, sort_keys=True).encode()).hexdigest()
    fn_ = os.path.join(tmp, f"{tag}_{key_[:12]}.json")
    json.dump({"script_sha256": old_sha, "key": key_, "params": params_, "state": {"v": 5}}, open(fn_, "w"))
    return ckpt_migrate.plan(os.path.basename(fn_))[0]

hist = ckpt_migrate._history("twoprime_recon.py")
cur_src = open(os.path.join(HERE, "twoprime_recon.py"), "rb").read()
cur_new = ckpt_key.code_sha_src(cur_src, "x.py", strip_prints=True)
synth = cur_src + b"\nZZ_PROBE_MANGLE = 1\n"
synth_old = ckpt_key.code_sha_src(synth, "x.py", strip_prints=False)
assert ckpt_key.code_sha_src(synth, "x.py", strip_prints=True) != cur_new
hist[synth_old] = ("old", "synthetic", synth)
expect("M5 a dep changed beyond prints since production is 'blocked' (hermetic)",
       _refusal_case("probe5", synth_old) == "blocked")
del hist[synth_old]
# M5r: the same refusal from a REAL historical blob when the clone carries it;
# on a truncated history the hash resolves to nothing and the checkpoint is
# 'unverifiable' -- a refusal either way, never a migration
stale = [h for h, (kind, blob, src) in hist.items()
         if kind == "old" and blob != "synthetic"
         and ckpt_key.code_sha_src(src, "x.py", strip_prints=True) != cur_new]
if stale:
    st5r = _refusal_case("probe5r", stale[0]); want = "blocked"
else:
    fake5r = hashlib.sha256(b"a historical version this clone does not carry").hexdigest()
    st5r = _refusal_case("probe5r", fake5r); want = "unverifiable"
    print("  NOTE: git history of twoprime_recon.py carries no stale blob (shallow clone?); "
          "M5r exercises the truncated-history refusal instead", flush=True)
expect(f"M5r a real (or history-less) stale dep is refused as '{want}'", st5r == want)

import shutil
shutil.rmtree(tmp, ignore_errors=True)
nfail = sum(1 for _, ok in cases if not ok)
print(f"ckpt_key probes: {len(cases)} cases, {len(cases)-nfail} as expected, {nfail} unexpected", flush=True)
print("CKPT_KEY PROBES " + ("PASS" if nfail == 0 else "FAIL"), flush=True)
sys.exit(1 if nfail else 0)
