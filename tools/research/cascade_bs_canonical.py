#!/usr/bin/env python3
"""
Resolving the Addendum 12 flag tension: the canonical formulas for
b/s and theta_23, and the amended (weight-graded, incremental) flag
functor that reproduces all nine source assignments mechanically.

Sources read directly (Check 1): part4b:990-1017 (b/s: lead =
(lepton ratio) x e with the UNCORRECTED lepton lead 16.53, closure
-alpha(7)/chi^4); part4b:3918-3938 (theta_23: tan theta_23 =
tan(arccos(N(13)/N(12))) * exp(-sum_{13}^{20} p(d)/2) * closure --
statics plus a HALF-weight exponential).

The two resolutions:

  1. theta_23 -- weight grading.  Its descent exponential is
     half-weight: exp(-Phi/2), an amplitude (Born-rule square root,
     the same machinery as theta_C's exp(-p(13)/2)).  Amend G to read
     FULL-weight (integer-weight) window exponentials only: amplitudes
     occupy the square root of the interval class, echoing the
     archimedean factor's own half-argument structure
     Gamma_R(s) = pi^(-s/2) Gamma(s/2).  Then theta_23: G = F ->
     Amplitude -> d0 = 7, mechanically.
  2. b/s -- incremental occupancy, EMPIRICALLY SELECTED.  Its minimal
     formula over the alphabet extended by closed-observable leads is
     L(m_tau/m_mu) * e  (2 atoms, vs 4 primitives).  Two candidate
     compositional readings differ in whether the sub-lead enters raw
     or closed; the DATA decides (Part A): the raw-lead form matches
     at 0.0 sigma, the closed-lead form misses by ~2 sigma.  So:
     corrections attach once, per observable; sub-leads enter raw; and
     the flags read the INCREMENT -- here the single atom e = exp(1)
     ("one unit of cascade potential across the SU(3) layer"), a
     single-unit exponential exempt from G by the papers' own
     single-layer clause.  b/s: G = F -> Amplitude -> d0 = 7.

Part C re-runs the amended classifier on all nine observables: 9/9.
"""

import math

from scipy.special import digamma

SQRTPI = math.sqrt(math.pi)


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def N(d):
    return SQRTPI * R(d)


def p(d):
    return 0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)


def Phi(a, b):
    return sum(p(d) for d in range(a, b + 1))


def part_A():
    print("=" * 74)
    print("PART A: the data selects the b/s compositional reading")
    print("=" * 74)
    lead = math.exp(Phi(6, 13)) * 2 * SQRTPI          # m_tau/m_mu lead
    closed = lead * math.exp(alpha(14) / 2)           # closed observable
    corr = math.exp(-alpha(7) / 2 ** 4)
    raw_form = lead * math.e * corr
    closed_form = closed * math.e * corr
    obs, sig = 4183.0 / 93.5, (4183.0 / 93.5) * math.hypot(0.007 / 4.183,
                                                           0.8 / 93.5)
    print(f"  m_tau/m_mu lead = {lead:.4f}; closed = {closed:.4f}")
    print(f"  b/s observed (PDG m_b/m_s) = {obs:.2f} +/- {sig:.2f}")
    print(f"  raw-lead form    L(m_tau/m_mu) e exp(-a7/16) = {raw_form:.4f}"
          f"   ({(raw_form-obs)/sig:+.2f} sigma)")
    print(f"  closed-lead form C(m_tau/m_mu) e exp(-a7/16) = {closed_form:.4f}"
          f"   ({(closed_form-obs)/sig:+.2f} sigma)")
    print("  => sub-leads enter RAW; corrections attach once, per")
    print("     observable.  The compositional reading is selected by the")
    print("     measurement, not chosen.")


def part_B():
    print()
    print("=" * 74)
    print("PART B: theta_23's canonical formula is half-weight (amplitude)")
    print("=" * 74)
    t_lead = math.tan(math.acos(N(13) / N(12))) * math.exp(
        -sum(p(d) / 2 for d in range(13, 21)))
    th_lead = math.degrees(math.atan(t_lead))
    th = math.degrees(math.atan(t_lead * math.exp(-alpha(7) / 16)))
    print(f"  lead: tan(arccos(N13/N12)) exp(-sum_13^20 p/2)"
          f" -> theta = {th_lead:.5f} deg")
    print(f"  closed with -alpha(7)/chi^4: {th:.5f} deg"
          f"   (paper: 2.38029; PDG: 2.38 +/- 0.06)")
    print("  the descent factor is exp(-Phi/2): HALF-weight -- an amplitude")
    print("  (Born-rule square root), not a probability-weight descent.")


# ---- Part C: amended classifier ---------------------------------------
# atoms: MPL | static d | expfull a b | exphalf a b | exp1unit | sublead
WINDOW = {12, 13, 14}
FORMULAS = {
    "alpha_s":    [("static", 12), ("expfull", 5, 12)],
    "m_tau/m_mu": [("expfull", 6, 13), ("static", 14)],
    "m_tau abs":  [("MPL",), ("expfull", 5, 19)],
    "ell_A":      [("MPL",), ("static", 4)],
    "sin2thW":    [("static", 13), ("static", 14)],
    "Omega_m":    [("static", 5)],
    "theta_C":    [("static", 12), ("static", 13), ("exphalf", 13, 13)],
    "b/s":        [("sublead", "m_tau/m_mu"), ("exp1unit",)],
    "theta_23":   [("static", 12), ("static", 13), ("exphalf", 13, 20)],
}
PAPER = {"alpha_s": 14, "m_tau/m_mu": 14, "m_tau abs": 19, "ell_A": 19,
         "sin2thW": 5, "Omega_m": 5, "theta_C": 7, "b/s": 7, "theta_23": 7}


def classify(ing):
    """Amended flags: occupancy of the increment (subleads sealed),
    G = FULL-weight multi-layer window exponentials only."""
    own = [t for t in ing if t[0] != "sublead"]
    P = any(t[0] == "MPL" for t in own)
    has_exp = any(t[0] in ("expfull", "exphalf", "exp1unit") for t in own)
    L = not has_exp
    G = any(t[0] == "expfull" and t[2] - t[1] >= 2
            and set(range(t[1], t[2] + 1)) & WINDOW for t in own)
    if P:
        return 19
    if L:
        return 5
    if G:
        return 14
    return 7


def part_C():
    print()
    print("=" * 74)
    print("PART C: amended classifier -- all nine rows")
    print("=" * 74)
    agree = 0
    for name, ing in FORMULAS.items():
        d = classify(ing)
        ok = d == PAPER[name]
        agree += ok
        print(f"  {name:<12} xi-derived d* = {d:>2}   paper = {PAPER[name]:>2}"
              f"   {'ok' if ok else '** TENSION **'}")
    print(f"  agreement: {agree}/9")
    print()
    print("  amendments, both principled and both forced externally:")
    print("  (i) G counts FULL-weight window exponentials; half-weight")
    print("      factors are amplitudes -- the square root of the interval")
    print("      class (echoing Gamma_R's half-argument structure).")
    print("  (ii) flags read the INCREMENT over the maximal closed sub-lead;")
    print("       sub-leads enter raw and corrections attach once -- the")
    print("       reading the b/s measurement itself selects at ~2 sigma.")
    print("  remaining soft spot: the e = exp(1) colour atom's own Adams")
    print("  derivation is open (papers' line 991).")


if __name__ == "__main__":
    part_A()
    part_B()
    part_C()
