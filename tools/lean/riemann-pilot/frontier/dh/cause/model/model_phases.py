#!/usr/bin/env python3
"""Random-model prediction of the prime-phase bias at DH zeros right of the line.
At a zero, F = c1 R + c2 = 0 with R the inert random product.  Kac-Rice: zeros are weighted by J = |dF/ds|^2 =
|c1 R D|^2 (D = d log R/ds); delta^2(F) is approximated by 1(|F| < eta)/(pi eta^2).  For the inert primes q in
QS the phase of q^{-it} is U_q = V_q/chi(q); the conditional circular moments m_k(q) = E[U_q^k | zero], k = 1, 2,
are reported with the Rayleigh-type statistic expected for K zeros, Q = 2K(|m1|^2 + |m2|^2).  Split primes enter
neither F nor J, so their conditional moments are 0 in the model.  Usage: model_phases.py [N] [X]
"""
import sys, math, json
import numpy as np
import os
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'model_rate.py')).read().split("def run(")[0].split("t0 = time.time()")[0])  # reuse model_rate.py's setup (primes, tail moments)
N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10_000_000
chi_of = {2: 1j, 3: -1j}   # chi(p) = i for p = 2 mod 5, -i for p = 3 mod 5
QS = [2, 3, 7, 13, 17, 23]
eta = 0.04
res = {}
for sig in [float(s) for s in (sys.argv[3].split(',') if len(sys.argv) > 3 else ['0.6','0.65','0.7','0.8'])]:
    rng = np.random.default_rng(7)
    x = ex**(-sig); lx = np.log(ex)
    S0, S1, S2 = tail_moments(sig) if X > P1 else (0.0, 0.0, 0.0)
    a0 = 2*math.sqrt(S0); b1 = -2*S1/math.sqrt(S0) if S0 > 0 else 0.0
    b2 = 2*math.sqrt(max(S2 - S1*S1/S0, 0.0)) if S0 > 0 else 0.0
    idx = {q: int(np.nonzero(ex == q)[0][0]) for q in QS}
    W = 0.0; acc = {q: np.zeros(2, dtype=complex) for q in QS}; nev = 0
    for _ in range(N // 500_000):
        n = 500_000
        V = np.exp(1j*rng.random((n, ex.size))*2*np.pi)
        Vx = V*x
        logR = np.sum(np.log1p(Vx) - np.log1p(-Vx), axis=1)
        D = np.sum(-2*Vx*lx/(1 - Vx*Vx), axis=1)
        z1 = (rng.standard_normal(n) + 1j*rng.standard_normal(n))/math.sqrt(2)
        z2 = (rng.standard_normal(n) + 1j*rng.standard_normal(n))/math.sqrt(2)
        logR += a0*z1; D += b1*z1 + b2*z2
        R = np.exp(logR); F = c1*R + c2
        sel = np.abs(F) < eta
        J = np.abs(c1*R[sel]*D[sel])**2
        W += J.sum(); nev += int(sel.sum())
        for q in QS:
            U = V[sel, idx[q]]/chi_of[q % 5]
            acc[q][0] += np.sum(J*U); acc[q][1] += np.sum(J*U*U)
    row = {q: [[float((acc[q][0]/W).real), float((acc[q][0]/W).imag)], [float((acc[q][1]/W).real), float((acc[q][1]/W).imag)]] for q in QS}
    res[sig] = {'events': nev, 'moments': row}
    print(f"sigma={sig}: events={nev}  " + "  ".join(f"q={q}: m1={complex(*row[q][0]):.3f} m2={complex(*row[q][1]):.3f}" for q in QS), flush=True)
json.dump({str(k): v for k, v in res.items()}, open(f'model_phases_X{Xarg}.json', 'w'), indent=1)
