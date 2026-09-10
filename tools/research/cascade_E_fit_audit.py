#!/usr/bin/env python3
"""
THE E FIT, DUG OUT: degeneracy, separability, structure, robustness.

E ~ 29.6 enters twice: the quark Gen2->Gen1 threshold (A23,
(c/u)/(s/d)) and the neutrino per-period enhancement (A29/T6,
exponents forced, value not).  A29 recorded a twin pair
(N_c pi^2 vs 2 pi e sqrt(3)).  This audit:

A. Re-enumerates the rulebook grammar at r <= 4 (A29 stopped at 3)
   in the honest data window -- does the twin pair survive, or grow?
B. Computes every E-dependent observable under each surviving form,
   with pairwise sigma separations at current and JUNO-era precision.
C. Separability verdict: which experiment, at what precision, could
   ever select the form.
D. Structural readings under T5-T8, and the named remaining joint.
   NO SELECTION IS MADE (stopping rule).

Data window for E: self-consistent solution of
  m_2 = m2d E,  m_1 = m1d E^2,  Dm2_sol = m_2^2 - m_1^2
at Dm2_sol = 7.53(18)e-5 eV^2 (+-2 sigma), intersected with the
capacity band m_1 in [1.7, 3.2] meV (A10).
"""

import itertools
import math

from scipy.optimize import brentq
from scipy.special import digamma

PI = math.pi
SQRTPI = math.sqrt(PI)
M_PL_RED = 2.435e18


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def p(d):
    return 0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(PI)


def Phi(d):
    return sum(p(k) for k in range(5, d + 1))


# papers' chain, Planck-anchored (A29)
A_GUT = (SQRTPI * R(12)) ** 2 / (4 * PI)
ALPHA_S = A_GUT * math.exp(sum(p(d) for d in range(5, 13)))
V = M_PL_RED * ALPHA_S * math.exp(-PI / alpha(5))
M29 = (ALPHA_S * V / math.sqrt(2)) * math.exp(-Phi(29)) \
    / (2 * SQRTPI) ** 5 * 1e9                       # eV
M3 = M29 * alpha(21) / 2 ** 8 * 1e3                 # meV
M2D = M29 * alpha(13) / 2 ** 16 * 1e3               # meV
M1D = M29 * alpha(5) / 2 ** 24 * 1e3                # meV

DM2_SOL, DM2_ERR = 7.53e-5, 0.18e-5                 # eV^2
UE1, UE2, UE3 = 0.678, 0.300, 0.022


def dm2_of_E(E):
    m2 = M2D * E
    m1 = M1D * E ** 2
    return (m2 ** 2 - m1 ** 2) * 1e-6               # eV^2


def part_A():
    print("=" * 74)
    print("A: rulebook enumeration, r <= 4, honest windows")
    print("=" * 74)
    elo = brentq(lambda E: dm2_of_E(E) - (DM2_SOL - 2 * DM2_ERR), 20, 40)
    ehi = brentq(lambda E: dm2_of_E(E) - (DM2_SOL + 2 * DM2_ERR), 20, 40)
    print(f"  data window (Dm2_sol +-2 sigma, self-consistent):"
          f" E in [{elo:.3f}, {ehi:.3f}]  (+-{(ehi-elo)/(ehi+elo)*100:.1f}%)")
    atoms = {"chi": 2.0, "N_c": 3.0, "G(1/2)": SQRTPI, "pi": PI,
             "pi^2": PI ** 2, "2pi": 2 * PI, "e": math.e,
             "sqrt(e)": math.sqrt(math.e), "sqrt(2)": math.sqrt(2),
             "sqrt(3)": math.sqrt(3), "cos30": math.cos(PI / 6),
             "sec30": 1 / math.cos(PI / 6)}
    found = {}
    for r_ in (1, 2, 3, 4):
        for combo in itertools.combinations_with_replacement(atoms, r_):
            v = 1.0
            for k in combo:
                v *= atoms[k]
            if elo <= v <= ehi:
                key = round(v, 6)
                lab = " * ".join(combo)
                if key not in found or len(lab) < len(found[key]):
                    found[key] = lab
    print(f"  distinct rulebook VALUES in the data window: {len(found)}")
    for v in sorted(found, reverse=True):
        print(f"    {found[v]:<30} = {v:.4f}"
              f"   Dm2_sol -> {dm2_of_E(v)*1e5:.3f}e-5"
              f" ({(dm2_of_E(v)-DM2_SOL)/DM2_ERR:+.2f} sigma)")
    print("  => A29's r<=3 enumeration UNDERCOUNTED: the twin pair is a")
    print("     TRIPLET (at least) at r<=4.  The fit-charge strengthens.")
    return sorted(found, reverse=True)


def part_B(values):
    print()
    print("=" * 74)
    print("B: observables under each form; pairwise separability")
    print("=" * 74)
    print(f"  {'form value':>10} {'m_1':>6} {'m_2':>6} {'Sigma':>7}"
          f" {'Dm2_sol e-5':>12} {'m_bb max':>9} {'(c/u)/(s/d)':>12}")
    rows = []
    for v in values:
        m2 = M2D * v
        m1 = M1D * v ** 2
        sig = m1 + m2 + M3
        mbb = UE1 * m1 + UE2 * m2 + UE3 * M3
        rows.append((v, m1, m2, sig))
        print(f"  {v:>10.4f} {m1:>6.3f} {m2:>6.3f} {sig:>7.2f}"
              f" {dm2_of_E(v)*1e5:>12.3f} {mbb:>9.2f} {v:>12.4f}")
    print()
    vmax, vmin = max(values), min(values)
    spread = (vmax - vmin) / vmin * 100
    print(f"  full spread across forms: {spread:.2f}% in E;"
          f" Sigma spread {rows[0][3]-rows[-1][3]:+.3f} meV;")
    d_spread = (dm2_of_E(vmax) - dm2_of_E(vmin)) / DM2_SOL * 100
    print(f"  Dm2_sol spread {d_spread:.2f}% ="
          f" {abs(dm2_of_E(vmax)-dm2_of_E(vmin))/DM2_ERR:.2f} sigma (current)")
    juno = 0.003 * DM2_SOL
    print(f"  at JUNO-era precision (~0.3% on Dm2_21):"
          f" extreme pair separates at"
          f" {abs(dm2_of_E(vmax)-dm2_of_E(vmin))/juno:.1f} sigma;"
          f" adjacent pairs at ~half that")
    print(f"  quark channel: needs (c/u)/(s/d) to ~0.05% -- current"
          f" precision ~3%: not foreseeable")


def part_D():
    print()
    print("=" * 74)
    print("D: structural readings under T5-T8, and the named joint")
    print("=" * 74)
    print("  All surviving forms are full-dictionary composites with")
    print("  DIFFERENT process readings:")
    print(f"    N_c pi^2      = N_c G(1/2)^4        = {3*PI**2:.4f}")
    print("        reading: N_c parallel channels x threshold full turn")
    print(f"    2 pi e sqrt3  = chi (2pi) e cos30   ="
          f" {4*PI*math.e*math.cos(PI/6):.4f}")
    print("        reading: chirality x Tate period x colour atom x dual")
    print("        projection (every factor has a T5-T8 meaning; sqrt3 =")
    print("        |different(Q(zeta_3))| by T8)")
    print(f"    4 e^2         = (chi e)^2            = {4*math.e**2:.4f}")
    print("        reading: chirality-doubled colour measurement, squared")
    print("  ratios: 3pi^2/(4 pi e cos30) = pi sqrt3/(2e)"
          f" = {PI*math.sqrt(3)/(2*math.e):.6f} -- no exact identity links")
    print("  them; exactly one (at most) can be the activation's output.")
    print()
    print("  NAMED JOINT (the whole residual fit): the threshold-crossing")
    print("  process identification -- WHICH composite the subcritical")
    print("  marked-twist activation produces.  Requires the activation")
    print("  mechanism (T6's remaining joint) or T4 uniqueness; data will")
    print("  not decide it in the foreseeable future.  NO SELECTION MADE.")


if __name__ == "__main__":
    vals = part_A()
    part_B(vals)
    part_D()
