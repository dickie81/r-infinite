#!/usr/bin/env python3
"""Post-hoc control for euler_zeros.py: the same argument-principle count of the zeros of g_X = c1 P_X + c2 with
Re > sigma0, for one cutoff X, on windows (H, H + L] at other heights H.  g_X is almost periodic in t, so every window
of length L is one realisation of its zero statistics; the census window (200, 10000] is one of them (and for t below
X the top primes' phases are not independent, which is the effect under test).
Usage: [SIG0=0.8,0.85] euler_zeros_heights.py X L H1 [H2 ...] out.json   (default SIG0 = 0.7,0.75,0.8,0.85)"""
import sys, json, time, importlib.util, os
spec = importlib.util.spec_from_file_location('ez', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'euler_zeros.py'))
ez = importlib.util.module_from_spec(spec); spec.loader.exec_module(ez)
X = int(sys.argv[1]); L = float(sys.argv[2]); Hs = [float(h) for h in sys.argv[3:-1]]; out = sys.argv[-1]
ez.XS = [X]; ez.KX = [int(ez.np.searchsorted(ez.inert, X, side='right'))]
SIG0 = [float(x) for x in os.environ.get('SIG0', '0.7,0.75,0.8,0.85').split(',')]
rows = []
for H in Hs:
    t0 = time.time(); r = {'H': H, 'L': L, 'X': X}
    for s0 in SIG0:
        res, stats = ez.count(H, H + L, s0)
        r[str(s0)] = res[0]['N']; r['frac_err_' + str(s0)] = res[0]['frac_err']; r['unres_' + str(s0)] = stats['unresolved']
    rows.append(r)
    print(f"H = {H:.0f}: " + ', '.join(f"Re > {s0}: {r[str(s0)]}" for s0 in SIG0) + f"  [{time.time() - t0:.0f}s]", flush=True)
json.dump(rows, open(out, 'w'), indent=1)
