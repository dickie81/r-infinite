#!/usr/bin/env python3
"""Round 81: J_n (the jump of d ln K_a(0,0)/d delta at log n) from the prime toggle, extrapolated to eps -> 0
by Dl = J eps + B eps^2 + C eps^3 through the three eps > 0 points, against J_pred = 2 Lambda(n) n^{-1/2} E(log n)."""
import sys, json, glob
import numpy as np
from mpmath import mpf
rows = []
for f in sorted(glob.glob(sys.argv[1] + "/*.json")):
    try: o = json.loads(open(f).read())
    except Exception: continue
    e = [x for x in o["eps"] if x["eps"] > 0]
    E0 = float(mpf(o["eps"][0]["E"]))
    A = np.array([[x["eps"], x["eps"]**2, x["eps"]**3] for x in e]); b = np.array([float(mpf(x["Dl"])) for x in e])
    J = np.linalg.solve(A, b)[0]
    rows.append((o["log_n"], o["n"], o["K"], o["w"], E0, J, 2*o["w"]*E0))
print("  n    log n     K    w=Λ/√n    E(log n)      J_meas      2wE      ratio")
for ln, n, K, w, E, J, Jp in sorted(rows):
    print(f"{n:3d}  {ln:.4f}  {K:5d}  {w:.5f}  {E:11.5f}  {J:10.5f}  {Jp:10.5f}  {J/Jp:.5f}")
