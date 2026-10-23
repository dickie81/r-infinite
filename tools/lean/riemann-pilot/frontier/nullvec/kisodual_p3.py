#!/usr/bin/env python3
"""Round 168, P3: for pure-Eisenstein isodual lattices, are the off-line zeros zeta's zeros
displaced to Re s = 1/2 and d/2 - 1/2? Evaluates |Xi_L| at those points relative to |Xi_L| nearby on the same vertical."""
import sys, subprocess, mpmath as mp
sys.argv = ['x', 'D4', '40']
res = {}
for name in ['D4', 'A2+A2', 'E8', 'Z+Z+Z+Z']:
    sys.argv = ['klatticeslice.py', name, '40']
    g = {}; src = open('klatticeslice.py').read().split("if len(sys.argv) > 3:")[0]
    exec(src, g)
    h = g['h']; Xi = g['Xi']; d = g['d']
    for k in (1, 2, 3):
        gam = mp.zetazero(k).imag
        for sig in (mp.mpf(1)/2, h - mp.mpf(1)/2):
            at = abs(Xi(mp.mpc(sig, gam))); off = abs(Xi(mp.mpc(sig, gam + mp.mpf('0.3'))))
            print(name, 'd=%d' % d, 'gamma_%d' % k, 'Re s=%s' % mp.nstr(sig, 3), 'ratio', mp.nstr(at/off, 3), flush=True)
