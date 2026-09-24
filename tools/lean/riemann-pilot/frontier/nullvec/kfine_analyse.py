#!/usr/bin/env python3
"""Round 81: measured jumps of l' = d ln K_a(0,0)/d delta at delta = log n against J_n = 2 Lambda(n) n^{-1/2} E.
One-sided cubic fits of l on [-hw, 0] and [0, hw]; J = l'(0+) - l'(0-).  Usage: kfine_analyse.py runs/kfine/*.json"""
import sys, json
import numpy as np
from mpmath import mpf
print("  n   log n    w_n=Λ/√n    E=g(a)²/λ₁    J_meas     J_pred=2wE   ratio    l'(0-)   J/l'(0-)")
rows = []
for f in sys.argv[1:]:
    try: o = json.loads(open(f).read())
    except Exception: continue
    x = np.array([s[0] for s in o["scan"]]); y = np.array([float(mpf(s[1])) for s in o["scan"]])
    y0 = y[x == 0][0]
    def slope(mask):
        c = np.polyfit(x[mask], y[mask] - y0, 3)
        return c[2]
    sl, sr = slope(x <= 1e-12), slope(x >= -1e-12)
    J = sr - sl; w = o["Lambda_over_sqrt_n"]; E = float(o["E"])
    rows.append((o["log_n"], o["n"], w, E, J, 2*w*E, sl))
for ln, n, w, E, J, Jp, sl in sorted(rows):
    print(f"{n:3d}  {ln:.4f}  {w:.5f}   {E:12.5f}   {J:9.4f}  {Jp:9.4f}   {J/Jp:.4f}   {sl:8.3f}  {J/sl:.4f}")
