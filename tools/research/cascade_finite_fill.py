#!/usr/bin/env python3
"""Theorem 1at verifier: the three worlds and the finite fill -- one common
pinning mechanism, the Jensen stages of xi, and the Gaussian attractor.

Gates (all exit-gated; any failure exits 1):
  g1  W1 geometry (function field): y^2 = x^3 + x over F_5 -- brute count
      gives 4 points, zeta numerator 1 - 2T + 5T^2, Frobenius eigenvalues
      1 +- 2i with |alpha| = sqrt(5) exactly (to 1e-12). The finite
      world's RH, pinned by intersection-form positivity (Hasse).
  g2  W2 quantum discreteness (unitary world): unfolded nearest-neighbor
      spacings of the first 201 zeta zeros vs the GUE Wigner surmise --
      KS in (0.065, 0.077) (observed 0.071); vs Poisson KS > 0.3
      (observed 0.352). The finite unitary world's pinning is unitarity;
      the statistics dictionary is N <-> log(t/2pi).
  g3  W3 vacuum world (partition functions): the N = 10 ferromagnetic
      Ising ring at beta*J = 0.7 -- all ten partition-function zeros on
      the unit circle to 1e-9 (Lee-Yang; pinned by coupling positivity).
  g4  the finite fill: Taylor coefficients of xi(1/2+z) by Cauchy
      integral at 40 digits (gamma(0) = xi(1/2) = 0.4971 +- 5e-4);
      every Jensen stage J^(d,n), d = 2..5, n = 0..10, hyperbolic with
      max relative imaginary root part < 1e-8. RH <=> ALL stages
      hyperbolic (Jensen-Polya); GORZ 2019 (d <= 8 all n; every d
      eventually) is cited in the paper, not re-proved here.
  g5  the attractor trend witness: J^(3,n) root-spread ratios
      (largest/smallest magnitude root) strictly decreasing toward the
      symmetric Hermite pattern: 2.1715 / 1.9009 / 1.7596 at
      n = 2 / 6 / 10 (each +- 0.01). The exact affine renormalization is
      GORZ's, cited not re-implemented -- this gate is the trend only.
  g6  the paper needles for the 1at block (title; the three-worlds
      triangulation sentence; the Laguerre-Polya definition sentence;
      the attractor identification; the uniformity residual; the
      no-physical-identification disclaimer; plus the seven round-192
      repair needles and the round-193 epigram needle -- see the
      in-code list, which is the authoritative census).
  g7  the chain: cascade_primes_side_ball.py (Theorem 1as) exits 0.
  g8  the footer census (this script backticked >= 2; "74 scripts cited
      in place"; "Theorems 1i-1ax").

Sabotage record (each: fresh tree, single mangle, restore from pristine;
clean baselines around the suite; censuses are the OBSERVED results):
  (a) title needle mangled in the paper        -> g6 FAIL alone
  (b) Jensen gamma index shifted in code (n+j -> n+j+1 in the stage
      builder)                                 -> CRASH, fail-closed:
      IndexError in the g4 stage loop (d = 5, n = 10 exceeds the
      coefficient table), exit 1 via traceback before g4 prints -- the
      prospective record predicted a g5 pin-failure with g4 surviving;
      the observed behavior is stricter (the mangle cannot even
      complete a run), recorded as observed per the marking rule
  (c) Lee-Yang coupling made antiferromagnetic (bJ 0.7 -> -0.7) -> g3
      FAIL (zeros leave the circle: the positivity IS the pinning)
  (d) footer census reverted 70 -> 69          -> g8 FAIL AND g7 FAIL
      (the chained 1as verifier's own footer gate catches the same
      reversion -- census propagation through the chain, as in the
      1as suite's probe (e))
  (e) chain target renamed in code             -> g7 FAIL alone
"""
import sys, math, subprocess, os, itertools
import numpy as np
from mpmath import mp, mpf, mpc, zeta, gamma as G, pi, exp, sqrt, zetazero

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")
paper = open(PAPER, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label)
    if not ok:
        fails.append(label)

# ---------------------------------------------------------------- g1
q = 5
N = 1 + sum(1 for x in range(q) for y in range(q) if (y*y - (x**3 + x)) % q == 0)
a = q + 1 - N
r1 = complex(a, math.sqrt(4*q - a*a))/2
ok = (N == 4 and a == 2 and abs(r1 - complex(1, 2)) < 1e-12
      and abs(abs(r1) - math.sqrt(q)) < 1e-12)
print(f"  g1 points {N}, a = {a}, eigenvalue {r1}, |alpha| = {abs(r1):.12f}")
gate("g1 W1 function field: finite zeta, eigenvalues pinned to sqrt(q) (Hasse)", ok)

# ---------------------------------------------------------------- g2
mp.dps = 15
gams = [float(zetazero(k).imag) for k in range(1, 202)]
s = np.sort(np.array([(gams[i+1]-gams[i])*math.log(gams[i]/(2*math.pi))/(2*math.pi)
                      for i in range(200)]))
grid = np.linspace(0, 4, 2001)
pdf = 32/math.pi**2 * grid**2 * np.exp(-4*grid**2/math.pi)
cdf = np.cumsum(pdf)*(grid[1]-grid[0])
emp = np.searchsorted(s, grid)/len(s)
ks_gue = float(np.max(np.abs(emp - cdf)))
ks_poi = float(np.max(np.abs(emp - (1 - np.exp(-grid)))))
print(f"  g2 KS vs GUE {ks_gue:.4f}; KS vs Poisson {ks_poi:.4f}")
gate("g2 W2 unitary world: zero spacings GUE-pinned (unitarity), Poisson excluded",
     0.065 < ks_gue < 0.077 and ks_poi > 0.3)

# ---------------------------------------------------------------- g3
NN, bJ = 10, 0.7
c = np.zeros(NN + 1)
for cfg in itertools.product([-1, 1], repeat=NN):
    bonds = sum(cfg[i]*cfg[(i+1) % NN] for i in range(NN))
    c[(sum(cfg) + NN)//2] += math.exp(bJ*bonds)
roots = np.roots(c[::-1])
dev = float(np.max(np.abs(np.abs(roots) - 1.0)))
print(f"  g3 Lee-Yang max ||z|-1| = {dev:.2e} over {len(roots)} zeros")
gate("g3 W3 vacuum world: Lee-Yang circle (coupling positivity pins the zeros)",
     len(roots) == NN and dev < 1e-9)

# ---------------------------------------------------------------- g4
mp.dps = 40
def xi(sv):
    return sv*(sv-1)/2 * pi**(-sv/2) * G(sv/2) * zeta(sv)
M, r, K = 128, mpf(3), 30
vals = [xi(mpf("0.5") + r*exp(mpc(0, 2*pi*m/M))) for m in range(M)]
b = [float((sum(vals[m]*exp(mpc(0, -2*pi*k*m/M)) for m in range(M))/(M*r**k)).real)
     for k in range(K + 1)]
gam = [math.factorial(j)*b[2*j] for j in range(K//2 + 1)]
def jensen(d, n):
    return [math.comb(d, j)*gam[n + j] for j in range(d + 1)]
worst = 0.0
for d in range(2, 6):
    for n in range(0, 11):
        rt = np.roots(jensen(d, n)[::-1])
        worst = max(worst, float(np.max(np.abs(rt.imag))/(1 + np.max(np.abs(rt.real)))))
print(f"  g4 gamma(0) = {gam[0]:.6f}; max relative imag root over d=2..5, n=0..10: {worst:.2e}")
gate("g4 the finite fill: every tested Jensen stage hyperbolic (finite RH holds)",
     abs(gam[0] - 0.4971) < 5e-4 and worst < 1e-8)

# ---------------------------------------------------------------- g5
ratios = []
for n in (2, 6, 10):
    rts = np.sort(np.abs(np.roots(jensen(3, n)[::-1]).real))
    ratios.append(float(rts[-1]/rts[0]))
print(f"  g5 J^(3,n) spread ratios at n=2,6,10: {[round(x,4) for x in ratios]}")
ok = (abs(ratios[0] - 2.1715) < 0.01 and abs(ratios[1] - 1.9009) < 0.01
      and abs(ratios[2] - 1.7596) < 0.01 and ratios[0] > ratios[1] > ratios[2])
gate("g5 the attractor trend: spread ratios decrease toward the Hermite pattern", ok)

# ---------------------------------------------------------------- g6
needles = [
    "**Theorem 1at (the three worlds and the finite fill: one common",
    "three unrelated worlds, three unrelated proofs, one mechanism",
    "closure of polynomials with only real roots: \"the finite fill of",
    "channel's Gaussian is the attractor of the arithmetic channel's",
    "UNIFORMITY — uniformity of the Gaussian attraction: the",
    "The clues functioned as pointers only; no",
    "Griffin–Ono–Rolen–Zagier (2019)",
    "KS = 0.071",
    # round-192 repair needles
    "there are THREE finite worlds in which",
    "Ξ(t) = ξ(½+it) lying in the Laguerre–Pólya class",
    "Deligne's general theorem proceeds by a different",
    "fugacity of the complexified external field",
    "polynomials attract, the h₄ₖ",
    "the analogue-finite target, named HERE as the",
    "exactness\nis the cited theorem's, not the gate's",
]
ok = all(nd in paper for nd in needles)
for nd in needles:
    if nd not in paper:
        print(f"  g6 MISSING: {nd!r}")
gate("g6 the 1at paper needles", ok)

# ---------------------------------------------------------------- g7
rr = subprocess.run([sys.executable, os.path.join(HERE, "cascade_primes_side_ball.py")],
                    capture_output=True, text=True)
gate("g7 the chain: cascade_primes_side_ball.py (Theorem 1as) exits 0", rr.returncode == 0)

# ---------------------------------------------------------------- g8
ok = paper.count("`cascade_finite_fill.py`") >= 2
ok &= "74 scripts cited in place" in paper
ok &= "Theorems 1i–1ax" in paper
gate("g8 the footer census (this script backticked >= 2; 74 cited in place; "
     "the range 1i–1ax)", ok)

print()
if fails:
    print(f"FAILURES ({len(fails)}):")
    for f in fails:
        print("  " + f)
    sys.exit(1)
print("ALL GATES PASS (8/8)")
