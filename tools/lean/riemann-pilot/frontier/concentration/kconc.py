#!/usr/bin/env python3
"""Round 390: the critical line as the support of a limiting measure (numerics, no Lean).
Gates for the identities the round states (mpmath, 40 digits); every gate fails the run if it fails.
  I1  Γ_ℝ(n)·|S^{n−1}| = 2, n = 1..12, with Γ_ℝ(s) = π^{−s/2}Γ(s/2) and |S^{n−1}| = 2π^{n/2}/Γ(n/2).
  I2  Lerch: ζ'(0, a) = log Γ(a) − ½ log 2π at a = n/2, n = 1..8, hence
      |S^{n−1}| = 2π^{n/2}·exp(ζ'(0) − ζ'(0, n/2)) (ζ(s, a) the Hurwitz zeta of the spectrum a + ℤ_{≥0}).
  I3  ζ(2k) = 2^{2k−1}|B_{2k}|·|B^{4k}|, k = 1..8, with |B^m| = π^{m/2}/Γ(m/2 + 1).
  I4  w = 1 − 1/ρ: |w|² − 1 = (1 − 2β)/(β² + γ²) for ρ = β + iγ, and w(1 − ρ)·w(ρ) = 1."""
import sys
from mpmath import mp, mpf, mpc, gamma, pi, zeta, diff, log, exp, bernoulli, fabs, sqrt
mp.dps = 40
TOL = mpf(10)**-30
fails = 0
def gate(name, err):
    global fails
    ok = err < TOL
    fails += (not ok)
    print(f"{'PASS' if ok else 'FAIL'} {name}: max error {mp.nstr(err, 3)}")
GR = lambda s: pi**(-s/2)*gamma(s/2)
area = lambda n: 2*pi**(mpf(n)/2)/gamma(mpf(n)/2)
vol = lambda m: pi**(mpf(m)/2)/gamma(mpf(m)/2 + 1)
gate("I1 Γ_ℝ(n)|S^{n−1}| = 2", max(fabs(GR(n)*area(n) - 2) for n in range(1, 13)))
hz = lambda a: diff(lambda s: zeta(s, a), 0)
gate("I2 Lerch ζ'(0,a) = log Γ(a) − ½log 2π",
     max(fabs(hz(mpf(n)/2) - (log(gamma(mpf(n)/2)) - log(2*pi)/2)) for n in range(1, 9)))
z0 = diff(zeta, 0)
gate("I2 |S^{n−1}| = 2π^{n/2}exp(ζ'(0) − ζ'(0,n/2))",
     max(fabs(2*pi**(mpf(n)/2)*exp(z0 - hz(mpf(n)/2)) - area(n)) for n in range(1, 9)))
gate("I3 ζ(2k) = 2^{2k−1}|B_2k||B^{4k}|",
     max(fabs(zeta(2*k) - 2**(2*k - 1)*fabs(bernoulli(2*k))*vol(4*k)) for k in range(1, 9)))
err_mod = err_inv = mpf(0)
for b in (mpf('0.1'), mpf('0.3'), mpf('0.5'), mpf('0.7'), mpf('0.9')):
    for g in (mpf('14.134725141734693790457251983562'), mpf(100), mpf(1000)):
        r = mpc(b, g); w = 1 - 1/r
        err_mod = max(err_mod, fabs(abs(w)**2 - 1 - (1 - 2*b)/(b**2 + g**2)))
        err_inv = max(err_inv, abs((1 - 1/(1 - r))*w - 1))
gate("I4 |w|² − 1 = (1 − 2β)/(β² + γ²)", err_mod)
gate("I4 w(1 − ρ)w(ρ) = 1", err_inv)
print("all gates pass" if fails == 0 else f"{fails} gate(s) failed")
sys.exit(1 if fails else 0)
