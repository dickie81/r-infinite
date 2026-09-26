#!/usr/bin/env python3
"""Round 118 construction check: prime-side M (kprimeside.py closed forms) vs the direct zero sum over the 6700 known zeta zeros
plus the smooth tail beyond (density ln(t/2pi)/2pi, sin^2 -> 1/2). Expected agreement ~ tail-model error (~1e-4 relative)."""
import json, math, numpy as np, mpmath as mp
from flint import arb, ctx
import kprimeside as ps
Z = np.array(json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json")))
for xv, K in ((3.0, 6), (7.0, 6)):
    a = math.log(xv)/2; w = np.array([k*math.pi/a for k in range(K)]); sg = np.array([(-1)**k for k in range(K)])
    F = np.array([sg*2*t*math.sin(t*a)/(t*t - w**2) for t in Z]); Mz = F.T @ F
    T0 = Z[-1]; tail = mp.quad(lambda t: 2*mp.log(t/(2*mp.pi))/(2*mp.pi)/t**2, [T0, mp.inf])
    Mz = Mz + np.outer(sg, sg)*float(tail)
    with ctx.workprec(200):
        aa = arb(math.log(xv))/2; ww = [arb(k)*arb.pi()/aa for k in range(K)]; s = [int(v) for v in sg]
        Sv, Sd, Pv, Pd = ps.phi_parts(aa, ww, K, xv, ps.prime_powers(xv))
        val, dd = list(Sv), list(Sd)
        for p in Pv:
            for k in range(K): val[k] += Pv[p][k]; dd[k] += Pd[p][k]
        M = ps.assemble(K, ww, val, dd, s)
        Pk = [s[k]*(aa/2).sinh()/(ww[k]*ww[k] + arb(1)/4) for k in range(K)]
        Mp = np.array([[float((M[j, k] + Pk[j]*Pk[k]).mid()) for k in range(K)] for j in range(K)])
    rel = np.abs(Mp - Mz)/np.abs(Mz).max()
    print(f"x={xv}: max |M_prime - M_zero| / max|M| = {rel.max():.2e};  diag prime {np.round(np.diag(Mp)[:4], 6)}  zero {np.round(np.diag(Mz)[:4], 6)}")
