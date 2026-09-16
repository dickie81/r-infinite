#!/usr/bin/env python3
"""THE ONE-PRIME ARC, ROUND 7 -- the nfr scan, committed
(round-260 F260-4: the temple docstrings cited "the committed
nfr scan" while the scan lived only in a session run; this file
lands it, unchanged in method, with the recorded output below).

Measures, at even delta = 1.0, the Temple margin / sigma /
polynomial-coefficient tradeoff against the count of nu = 3/2
Gegenbauer modes (poly degree = 2*nfr), on the committed t-space
pipeline at base 0.005. CONDENSED DIGEST of the recorded output (2026-08-28 session;
the numbers reproduce by running this file, whose actual lines
carry per-row rho, separate 'NFR k deg d: max|pt|' lines
printed between each nfr's ell2 0.014 and 0.015 rows (F262-2),
and ell2 = 0.014 rows omitted here -- F261-4 re-swore the earlier 'RECORDED OUTPUT' label;
the trial carries no rigor burden -- the scan chooses a
fixture, it certifies nothing):
    NFR 3 ell2 0.015: -4.307e-07  sigma 1.433e-04  (fails)
    NFR 4 ell2 0.015: +3.203e-07  sigma 9.604e-05  max|pt| 1.085e+02
    NFR 5 ell2 0.015: +3.376e-07  sigma 9.467e-05  max|pt| 8.880e+02
    NFR 6 ell2 0.015: +3.614e-07  sigma 9.277e-05  max|pt| 1.521e+04
    NFR 8 ell2 0.015: +3.855e-07  sigma 9.080e-05  max|pt| 1.262e+06
nfr = 5 chosen: past it the margin gains ~7% then ~3% per
step (the sigma gain ~2% then ~1% per two degrees; nfr 6 -> 8
counted as two steps throughout -- round-262 F262-1 re-swore
the earlier '~5-7%' range, which mixed step conventions) while
the monomial coefficients grow roughly an order of magnitude
per step (1.1e2 -> 8.9e2 -> 1.5e4 -> 1.3e6 across the recorded
rungs), and degree 24 (nfr 12) had destroyed the norm enclosure
outright. The
pure-harmonic saturation (sigma 1.20e-4, base-independent, vs
needed 1.19e-4) is the separate harmonic probe recorded in
Addendum 395; this file carries the nfr ladder only.
"""
import math, sys
sys.path.insert(0, "/home/user/r-infinite/tools/research")
import numpy as np
from scipy.linalg import eigh as scipy_eigh
import oneprime_fractional as opf
from oneprime_push import temple_opt
from oneprime_interval_temple import _geg_monomial

for nfr in (3, 4, 5, 6, 8):
    md, N, M, S, gf4, grids = opf.cell_matrices(
        0.5, "even", base=0.005, nus=(1.5,), nfr=nfr, nrough=13)
    tn, tw, B, TB = grids
    d = 1.0/np.sqrt(np.diag(N))
    Nn = d[:, None]*N*d[None, :]
    ev, U = np.linalg.eigh(Nn)
    keep = ev > 1e-4
    Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T*d[None, :])
    Bw, TBw = Wh @ B, Wh @ TB
    NA = 2*(Bw*tw[None, :]) @ Bw.T
    MA = 2*(Bw*tw[None, :]) @ TBw.T
    SA = 2*(TBw*tw[None, :]) @ TBw.T
    NA, MA, SA = ((NA+NA.T)/2, (MA+MA.T)/2, (SA+SA.T)/2)
    for ell2 in (0.014, 0.015):
        mu, c = temple_opt(NA, MA, SA, ell2)
        nn = float(c @ NA @ c)
        rho = float(c @ MA @ c)/nn
        sig = math.sqrt(max(float(c @ SA @ c)/nn - rho*rho, 0.0))
        if abs(ell2 - 0.015) < 1e-12:
            # fixture-style poly coefficient scale at this nfr
            cf = np.array(Wh.T @ c)
            cf = cf/math.sqrt(float(cf @ N @ cf))
            a = 0.5
            deg = max(fr["n"] for fr in md.frac) + 2
            px = np.zeros(deg + 1)
            for j, fr in enumerate(md.frac):
                g = np.array(_geg_monomial(fr["n"], fr["nu"]))
                mode = np.zeros(fr["n"] + 3)
                mode[:fr["n"] + 1] += g
                mode[2:fr["n"] + 3] -= g
                px[:len(mode)] += float(cf[md.nharm + j])*mode
            pt = px/np.power(a, np.arange(deg + 1))
            print(f"NFR {nfr} deg {deg}: max|pt| {np.max(np.abs(pt)):.3e}")
        print(f"NFR {nfr} ell2 {ell2:g}: {mu:+.3e} rho {rho:+.3e} "
              f"sigma {sig:.3e}", flush=True)
