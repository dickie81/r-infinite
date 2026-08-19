#!/usr/bin/env python3
"""Regenerate tools/research/tower_manifest.json: the ordered verifier
tower (root -> top), each member's sha256 at the current commit, and
the paper's current census strings. Must be run (and the result
committed) by any commit that touches a tower member or advances the
footer census -- a stale below-top entry fails every manifest-mode chain gate above it; a stale top entry is caught by run_tower's precheck (round-215 F3).
(Relocated from tools/build/ -- the .gitignore `build/` pattern had
silently excluded the original, discovered when restore #11 deleted
the only copy and the round-215 reviewer's battery failed closed on
the stale manifest the missing script should have refreshed.)
"""
import hashlib, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")

TOWER = [
    "cascade_lattice_forcing.py",
    "cascade_primes_side_ball.py",
    "cascade_finite_fill.py",
    "cascade_attraction_margins.py",
    "cascade_li_two_channels.py",
    "cascade_floor_meter.py",
    "cascade_heatflow_energy.py",
    "cascade_saddle_curvature.py",
    "cascade_weil_margin.py",
    "cascade_weil_crossover.py",
    "cascade_prolate_horizon.py",
    "cascade_fluctuation_price.py",
    "cascade_sonin_dirac.py",
]

paper = open(PAPER, encoding="utf-8").read()
mc = re.search(r"the \*\*(\d+) scripts cited in place\*\*", paper)
mr = re.search(r"extended by Theorems (1i–1[a-z]+)", paper)
if not (mc and mr):
    sys.exit("census strings not found in paper")

manifest = {
    "census_count_string": f"the **{mc.group(1)} scripts cited in place** above",
    "census_range_string": f"extended by Theorems {mr.group(1)}:",
    "tower": [
        {"file": f,
         "sha256": hashlib.sha256(
             open(os.path.join(HERE, f), "rb").read()).hexdigest()}
        for f in TOWER
    ],
}
out = os.path.join(HERE, "tower_manifest.json")
json.dump(manifest, open(out, "w", encoding="utf-8"), indent=1)
print(f"manifest written: {len(TOWER)} members; census "
      f"{manifest['census_count_string']!r} / "
      f"{manifest['census_range_string']!r}")
