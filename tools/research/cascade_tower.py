#!/usr/bin/env python3
"""Tower chain-mode support (the cadence amendment, owner-commissioned).

Two chain-gate modes for the certified verifier tower, selected by the
environment variable CASCADE_CHAIN:

  full (default, unset): the historical behavior -- the chain gate
    subprocess-runs the immediate parent verifier, which recursively
    runs its own parent: one run of the newest verifier re-executes
    the whole certified tower serially. Maximal re-verification;
    wall time grows with every landing.

  manifest: certify-against-committed-record -- the chain gate
    (a) sha256-verifies EVERY strict ancestor's committed bytes
    against tools/research/tower_manifest.json (integrity of the
    certified instruments, instant), and (b) verifies the manifest's
    census strings against the paper (so a footer revert still fails
    BOTH the verifier's own census gate and the chain gate -- the
    two-gate detection of the census-propagation sabotage probe is
    preserved without executing anything). Certified LEVELS are not
    re-executed in this mode; their claims rest on the certification
    record plus byte integrity. Full re-execution remains available
    (and scheduled: certification batteries run tools/research/
    run_tower.py, which executes every level in parallel).

The manifest is refreshed by tools/research/refresh_tower_manifest.py in
any commit that touches a tower member or advances the census. A stale
entry for any tower member BELOW THE TOP fails every manifest-mode
chain gate above it (by design); a stale TOP entry has no chain gate
above it and is caught only by run_tower.py's manifest-integrity
precheck (round-215 F3).
"""
import hashlib, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
MANIFEST = os.path.join(HERE, "tower_manifest.json")

# declared paper surface (round-264 F264-1): the two manifest
# census strings are the ONLY paper consumption of chain mode.
# The manifest's values are dynamic and unharvestable, so this
# module declares the CURRENT literals and chain_ok additionally
# asserts man[key] == the declared literal -- a census advance
# must edit this declaration (rotating the module's sha and every
# reach key) or the tower fails.  run_tower's precheck evaluates
# these needles live like any member declaration.
import paper_needles
PAPER_NEEDLES = [
    {"s": "the **86 scripts cited in place** above", "form": "raw",
     "key": "census_count_string"},
    {"s": "extended by Theorems 1i–1bj:", "form": "raw",
     "key": "census_range_string"},
]


def _sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def chain_ok(parent_basename):
    """Return True iff the chain obligation to `parent_basename` is
    met under the active mode. Prints its evidence either way."""
    mode = os.environ.get("CASCADE_CHAIN", "full")
    if mode != "manifest":
        r = subprocess.run([sys.executable, os.path.join(HERE, parent_basename)],
                           capture_output=True, text=True)
        print(f"  chain [full mode]: ran {parent_basename}, "
              f"exit {r.returncode}", flush=True)
        return r.returncode == 0
    man = json.load(open(MANIFEST, encoding="utf-8"))
    tower = man["tower"]
    names = [e["file"] for e in tower]
    if parent_basename not in names:
        print(f"  chain [manifest mode]: {parent_basename} not in manifest",
              flush=True)
        return False
    top = names.index(parent_basename)
    ok = True
    for e in tower[: top + 1]:
        path = os.path.join(HERE, e["file"])
        got = _sha(path) if os.path.exists(path) else "MISSING"
        if got != e["sha256"]:
            print(f"  chain [manifest mode]: HASH MISMATCH {e['file']}",
                  flush=True)
            ok = False
    import paper_needles
    for d in paper_needles.declared(PAPER_NEEDLES):
        if man[d["key"]] != d["s"]:
            print(f"  chain [manifest mode]: manifest {d['key']} "
                  f"{man[d['key']]!r} != declared {d['s']!r}", flush=True)
            ok = False
    ok_n, miss = paper_needles.verify(PAPER_NEEDLES)
    for d, n in miss:
        print(f"  chain [manifest mode]: paper lacks {d['s']!r} "
              f"(count {n})", flush=True)
    ok = ok and ok_n
    if ok:
        print(f"  chain [manifest mode]: {top + 1} ancestor hashes verified; "
              f"census strings verified", flush=True)
    return ok
