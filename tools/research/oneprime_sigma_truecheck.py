#!/usr/bin/env python3
"""THE ONE-PRIME ARC, ROUND 7 -- the closed-form sigma^2
cross-check, committed (round-261 F261-2: the even-1.0 theta
comment's decomposition -- measured slop = stored sigma2_hi
minus TRUE sigma^2 -- anchored on a session-run number with no
committed referent; this file lands the computation).

WHAT IT COMPUTES. The even-1.0 frozen trial (rebuilt exactly as
the Stage III fixture builds it: the nfr = 5 span, base 0.003
pipeline, temple_opt at ell2 = 0.015, N-normalized), then the
CLOSED-FORM float values of n, rho, S, sigma^2 -- T phi
evaluated through oneprime_interval_temple's own ClosedT
machinery at 100k graded midpoints (interval midpoints; the
enclosure widths at points are ~1e-7-scale, far below the
quantities read) -- Simpson-free plain Riemann sums on the
graded grid, adequate at the 1e-11 grid-convergence this
records. RECORDED VALUES (2026-08-28 session; reproduced by
running this file -- CONDENSED: the file also prints n and the
per-segment progress):
    closed-form: rho 9.414662e-07  S 8.967757e-09
                 sigma2 8.966871e-09  sigma 9.469356e-05
    pipeline (the nfr scan's fixture row): sigma2 8.962e-09
    temple at ell2 0.015 (float): +3.4364e-07
The theta-comment decomposition this anchors: the theta-0.008
run's stored sigma2_hi 1.871861e-8 (checkpoint
oneprime_ivtemple_215bd4c99544.json, removed at the round-260
sweep as key-misattributed, recoverable at commit 0ecdb7c~1)
minus this TRUE 8.967e-9 = the 9.7e-9 hull-slop excess; the
landed f845eff51e61 state's 9.848648e-9 minus it = 8.8e-10.
The trial carries no rigor burden; this file certifies nothing
-- it is the committed referent for the float decomposition."""
import json, math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import numpy as np
import oneprime_fractional as opf
from oneprime_push import temple_opt
import oneprime_interval_temple as OT
from oneprime_interval_count import V
from oneprime_interval_core import I


def run():
    a = 0.5
    md = opf.Modes(a, "even", nus=(1.5,), nfr=5, nrough=13)
    tn, tw, B, TB, _v = opf.apply_T(md, base=0.003)
    N = 2*(B*tw[None, :]) @ B.T
    M = 2*(B*tw[None, :]) @ TB.T
    S_ = 2*(TB*tw[None, :]) @ TB.T
    N, M, S_ = (N+N.T)/2, (M+M.T)/2, (S_+S_.T)/2
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
    mu, c = temple_opt(NA, MA, SA, 0.015)
    cf = np.array(Wh.T @ c)
    cf = cf/math.sqrt(float(cf @ N @ cf))
    deg = max(fr["n"] for fr in md.frac) + 2
    px = np.zeros(deg + 1)
    for j, fr in enumerate(md.frac):
        g = np.array(OT._geg_monomial(fr["n"], fr["nu"]))
        mode = np.zeros(fr["n"] + 3)
        mode[:fr["n"] + 1] += g
        mode[2:fr["n"] + 3] -= g
        px[:len(mode)] += float(cf[md.nharm + j])*mode
    pt = px/np.power(a, np.arange(deg + 1))
    fx = {"a": a, "parity": "even", "nharm": md.nharm,
          "ws": list(map(float, md.w)),
          "c": list(map(float, cf[:md.nharm])),
          "poly": list(map(float, pt))}
    phifull = cf @ B
    chi_f = float(2*np.sum(tw*np.cosh(tn/2)*phifull))
    tr = OT.trial_from_fixture(fx, fx["c"])
    tabs = OT.build_tables(a, [(tr.ws[i], tr.wI(i))
                               for i in range(len(tr.ws))],
                           tr.deg, 2e-6)
    ct = OT.ClosedT(tr, tabs, I(chi_f - 1e-9, chi_f + 1e-9))
    S = Mv = Nv = 0.0
    for lo, hi, n in ((0.0, 0.4, 40000), (0.4, 0.49, 20000),
                      (0.49, 0.4999, 20000),
                      (0.4999, 0.5 - 1e-9, 20000)):
        x = np.linspace(lo, hi, n + 1)
        mid = 0.5*(x[:-1] + x[1:])
        h = np.diff(x)
        Tm, _ = ct.Tphi_batch(V.point(mid), deriv=False,
                              pole=True)
        tv = 0.5*(Tm.lo + Tm.hi)
        ph = tr.phi_v(V.point(mid))
        pv = 0.5*(ph.lo + ph.hi)
        S += float(np.sum(tv*tv*h))
        Mv += float(np.sum(pv*tv*h))
        Nv += float(np.sum(pv*pv*h))
        print(f"  segment [{lo:g}, {hi:g}] done", flush=True)
    S, Mv, Nv = 2*S, 2*Mv, 2*Nv
    rho = Mv/Nv
    sig2 = S/Nv - rho*rho
    print(f"closed-form: n {Nv:.8f} rho {rho:.6e} S {S:.6e} "
          f"sigma2 {sig2:.6e} sigma {math.sqrt(max(sig2,0)):.6e}",
          flush=True)
    print(f"temple at ell2 0.015 (float): "
          f"{rho - sig2/(0.015 - rho):+.4e}", flush=True)
    return sig2


if __name__ == "__main__":
    run()
    print("sigma truecheck complete", flush=True)
