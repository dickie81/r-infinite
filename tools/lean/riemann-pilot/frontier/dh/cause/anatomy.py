#!/usr/bin/env python3
"""Anatomy of the four kernel-located off-line zeros of the Davenport-Heilbronn function (P5, exploratory).
At a zero rho, R(rho) = L(rho, chi)/L(rho, chibar) = -eps exactly (eps = e^{2 i theta}, tan theta = kappa).
R is the continuation of prod over inert primes p = +-2 mod 5 of (1 + chi(p) p^-s)/(1 - chi(p) p^-s).
Prints: R(rho) from the Hurwitz values (exact target check); the partial inert products R_P(rho) for growing P
(for Re rho > 1/2 their convergence holds under GRH for L(s, chi5) and is not known unconditionally; the printed
distances show how close they come); and, for the first inert primes, the phase of chi(p) p^{-i gamma}
(the mechanism predicts it near -i, i.e. -pi/2) and the rotation angle of each Euler factor."""
import math, cmath
import numpy as np
from flint import acb, ctx
ctx.prec = 80
kappa = (math.sqrt(10 - 2*math.sqrt(5)) - 2)/(math.sqrt(5) - 1); th = math.atan(kappa); eps = cmath.exp(2j*th)
Z = [(0.8085171824566373856, 85.699348485377592172), (0.6508300806097370824, 114.16334273075698090),
     (0.5743560504508059907, 166.47930591316815588), (0.7242576946268097802, 176.70246124285582505)]
def L(s, conj=False):
    H = [acb.zeta(s, acb(a)/5) for a in range(1, 5)]
    A, B = H[0] - H[3], H[1] - H[2]
    return complex((acb(5)**(-s))*(A + (acb(0, -1) if conj else acb(0, 1))*B))
def primes(n):
    s = np.ones(n+1, bool); s[:2] = False
    for i in range(2, int(n**.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
P = primes(2_000_000); inert = P[(P % 5 == 2) | (P % 5 == 3)]
chi = {2: 1j, 3: -1j}
print(f"target -eps = {(-eps):.6f}  (arg {cmath.phase(-eps):.4f})")
for sig, gam in Z:
    s = acb(sig, gam)
    R = L(s)/L(s, True)
    print(f"\nrho = {sig:.6f} + {gam:.6f} i:  R(rho) = {R:.10f}   |R + eps| = {abs(R + eps):.2e}")
    x = inert.astype(float)**(-sig); ph = np.exp(-1j*gam*np.log(inert.astype(float)))
    V = np.array([chi[p % 5] for p in inert])*ph
    fac = (1 + V*x)/(1 - V*x)
    logs = np.log(fac)
    cum = np.cumsum(logs)
    for Pmax in (10, 100, 1000, 10**4, 10**5, 10**6, 2*10**6):
        k = np.searchsorted(inert, Pmax, side='right')
        RP = np.exp(cum[k-1])
        print(f"   inert primes <= {Pmax:>8}: R_P = {RP:.5f}   |R_P - R| = {abs(RP - R):.3f}")
    print("   p   phase of chi(p) p^{-i gamma} (units of pi)   |factor|   rotation of factor (rad)")
    for i in range(8):
        p = inert[i]
        print(f"   {p:3d}   {cmath.phase(V[i])/math.pi:+.3f}                              {abs(fac[i]):.3f}     {cmath.phase(fac[i]):+.3f}")
