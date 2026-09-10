#!/usr/bin/env python3
"""
THE SIGN RULE FROM ARITHMETIC FIRST PRINCIPLES.

Papers' thm:sign-rule (part4b:2127, read directly): sign(dPhi) = +1
for Descent-class observables, -1 for Geometric/Amplitude -- proved
there by three separate mechanisms (Cauchy-Schwarz Gram deficit;
Bott-vs-lapse; Born-overlap chirality), verified 8/8.

CLAIM: all three mechanisms are ONE arithmetic structure -- strict
log-convexity of the Gamma function (the Bohr-Mollerup property, the
DEFINING characterisation of Gamma) = strict Cauchy-Schwarz in the
Tate measure space -- evaluated either OFF or AT its equality
manifold:

  P1 (Descent, +): an interpolation read at adjacent twists sits OFF
     the Cauchy-Schwarz equality manifold; the Gram deficit
     1 - C^2 > 0 STRICTLY, so the correction can only add.
     C^2(d, d+1) = R(2d+2)^2/(R(2d+1) R(2d+3)) < 1 is exactly strict
     midpoint log-convexity of the Beta/Gamma_R system; Cauchy-
     Schwarz on Gaussian-type measures is the classical proof that
     Gamma is log-convex, and by Bohr-Mollerup log-convexity + the
     recursion CHARACTERISES Gamma.  The + sign is a corollary of
     Gamma's defining property.

  P2 (Amplitude, -): a saturated Born overlap sits AT the equality
     manifold (proportional vectors, single-saddle Gaussian): every
     perturbation strictly decreases a normalised overlap (second-
     order, one-signed).  The - sign is Cauchy-Schwarz evaluated at
     its equality case.

  P3 (Geometric, -): a residue-class read restricts the peaked
     weight to a proper coset subset.  [DEMOTED, review 4 (D1): the
     'all 28 shares < 1/pi' bound holds only under the avatar-weight
     pairing 2/Gamma_R(d) (max 0.31322); under the Definition-2.1
     pairing 2/Gamma_R(d+1) it FAILS (max 0.35001 >= 1/pi).  The
     Geometric sign is convention-conditional.  Single-coset shares
     stay < 1/pi under BOTH pairings -- a repair candidate recorded,
     not adopted.]

  P4: the 8/8 audit (papers' table reproduced).
  P5: the boundary -- the population-class assignment of a physical
     observable is instantiation data (parallel to T5 occupancy);
     the magnitude identification alpha(d*)/chi^k is source-
     selection content, inherited, not re-derived here.

THEOREM T7 (arithmetic sign rule; coset clause demoted, review 4):
the sign of a correction is the side of the Cauchy-Schwarz equality
manifold on which the observable's leading formula sits: off-manifold
interpolation reads gain (+); at-manifold saturated overlaps lose
(-).  These two clauses are grounded in strict log-convexity of
Gamma.  The Geometric coset clause is convention-conditional (see P3
note) and no longer claimed as derived.
"""

import itertools
import math

import numpy as np

PI = math.pi
LNPI = math.log(PI)


def R(d):
    return math.exp(math.lgamma((d + 1) / 2.0) - math.lgamma((d + 2) / 2.0))


def lg_R(s):                       # log Gamma_R(s)
    return -s / 2 * LNPI + math.lgamma(s / 2)


def P1():
    print("=" * 74)
    print("P1 (Descent, +): strict log-convexity = strict Cauchy-Schwarz")
    print("=" * 74)
    worst = 1.0
    for d in range(4, 31):
        c2 = R(2 * d + 2) ** 2 / (R(2 * d + 1) * R(2 * d + 3))
        worst = max(worst - 1, c2 - 1) + 1  # track max c2
    rows = [(d, R(2 * d + 2) ** 2 / (R(2 * d + 1) * R(2 * d + 3)))
            for d in (4, 7, 13, 19, 30)]
    for d, c2 in rows:
        print(f"  d = {d:>2}: C^2(d,d+1) = {c2:.6f}   deficit 1-C^2 ="
              f" {1-c2:.6f} > 0")
    allpos = all(R(2 * d + 2) ** 2 < R(2 * d + 1) * R(2 * d + 3)
                 for d in range(1, 216))
    print(f"  strict for ALL d = 1..215: {allpos}")
    print("  identity: this is midpoint log-convexity of the Beta/Gamma_R")
    print("  system; log-convexity + recursion = Bohr-Mollerup, the")
    print("  DEFINING property of Gamma.  Off-manifold => deficit > 0 =>")
    print("  the correction can only ADD: sign +1 for interpolation reads.")


def P2():
    print()
    print("=" * 74)
    print("P2 (Amplitude, -): perturbation at the equality manifold")
    print("=" * 74)
    rng = np.random.default_rng(7)
    x = np.linspace(-8, 8, 4001)
    g = np.exp(-PI * x * x)
    g /= np.linalg.norm(g)
    eps = 1e-3
    worst = 0.0
    for i in range(200):
        pert = rng.standard_normal(len(x))
        pert -= g * (g @ pert)                 # orthogonal perturbation
        pert /= np.linalg.norm(pert)
        v = g + eps * pert
        ov = (g @ v) / np.linalg.norm(v)
        worst = max(worst, ov - 1)
    print(f"  200 random orthogonal perturbations of the saturated overlap:")
    print(f"  max(overlap - 1) = {worst:.2e}  (all <= 0; shift is O(eps^2),")
    print(f"  one-signed: {-eps**2/2:.2e} predicted, second order)")
    print("  => AT the equality manifold every perturbation DECREASES a")
    print("     normalised overlap: sign -1 for saturated Amplitude reads.")


def P3():
    print()
    print("=" * 74)
    print("P3 (Geometric, -): coset restriction of the peaked weight")
    print("=" * 74)
    # tower weight Omega_(d-1) = 2/Gamma_R(d), d = 5..217 (papers' T)
    w = {d: 2 * math.exp(-lg_R(d)) for d in range(5, 218)}
    T = sum(w.values())
    shares = {}
    for r1, r2 in itertools.combinations(range(8), 2):
        s = sum(v for d, v in w.items() if d % 8 in (r1, r2))
        shares[(r1, r2)] = s / T
    mx = max(shares.values())
    mxk = max(shares, key=shares.get)
    bott = sum(v for d, v in w.items() if d % 8 == 5)
    print(f"  tower weight 2/Gamma_R(d), d = 5..217;  1/pi = {1/PI:.5f}")
    print(f"  all 28 two-coset shares: max = {mx:.5f} at residues {mxk}"
          f"   ({'ALL < 1/pi' if mx < 1/PI else '** VIOLATION **'})")
    print(f"  single Dirac coset (d = 5 mod 8): share = {bott/T:.5f}")
    print("  => [DEMOTED, review 4: this bound is pairing-conditional --")
    print("     under the Def-2.1 weight 2/Gamma_R(d+1) the max share is")
    print("     0.35001 >= 1/pi.  The Geometric sign is convention-based.]")


def P4():
    print()
    print("=" * 74)
    print("P4: the 8/8 sign audit (papers' closed family)")
    print("=" * 74)
    rows = [("alpha_s", "Descent", "+"), ("m_tau/m_mu", "Descent", "+"),
            ("m_tau abs", "Descent", "+"), ("ell_A", "Descent", "+"),
            ("sin^2 theta_W", "Descent", "+"),
            ("Omega_m", "Geometric", "-"), ("theta_C", "Amplitude", "-"),
            ("b/s", "Amplitude", "-")]
    for name, cls, sgn in rows:
        pred = "+" if cls == "Descent" else "-"
        ok = "ok" if pred == sgn else "** FAIL **"
        print(f"  {name:<15} {cls:<10} observed {sgn}   predicted {pred}"
              f"   {ok}")
    print("  (theta_23, the ninth closure, is Amplitude '-': also conforms.)")


if __name__ == "__main__":
    P1()
    P2()
    P3()
    P4()
    print()
    print("=" * 74)
    print("P5: boundary -- population-class assignment of a physical")
    print("observable is instantiation data (parallel to T5 occupancy);")
    print("magnitude identification alpha(d*)/chi^k is inherited source-")
    print("selection content.  The SIGN itself is theorem T7: which side")
    print("of the Cauchy-Schwarz equality manifold the read sits on.")
    print("=" * 74)
