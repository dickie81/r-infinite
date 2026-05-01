#!/usr/bin/env python3
"""
Cascade-internal n=4 candidate survey: hunt for 4-fold cascade
structures that could host a novel cascade observable matching
the n=4 chirality-theorem prediction.

CONTEXT
=======
After Candidate (1) (cascade-native 2-loop correction to 1/alpha_em)
and Candidate (2) (d=29 activation for solar splitting) both failed,
Candidate (3) is the most exciting: a CASCADE-INTERNAL observable
with 4-fold structure that has no QFT analog.

The cascade has at least four explicit 4-fold structures:

  (A) Four distinguished source layers (Part IVb prop:source-selection):
      {d_V, d_0, d_{gw}, d_1} = {5, 7, 14, 19}
      Each closed precision observable uses ONE.

  (B) Four Bott-periodic Dirac layers (d mod 8 = 5):
      {5, 13, 21, 29}
      First three are generations; fourth is neutrino source.

  (C) Four Hurwitz division algebras (Part IVa thm:adams):
      R, C, H, O at dimensions 1, 2, 4, 8.

  (D) Four observable types in the source-selection rule:
      Absolute, Observer, Gauge, Amplitude.

A novel cascade observable that uses ALL FOUR layers/structures
simultaneously would naturally exercise the n=4 slot.

WHAT THIS SCRIPT DOES
=====================
For each 4-fold structure (A)-(D), compute natural cascade products
and sums.  Check against:
  - Known cascade gaps (solar splitting, n_s/A_s, Lambda refinements)
  - Notable observed numerical patterns
  - Cascade-internal identities

Report any match (or near-match) at the few-percent level honestly.

WHAT THIS SCRIPT DOES NOT DO
============================
  - Force a match.  If no 4-fold product matches anything observed,
    report the survey as null.
  - Reproduce QFT amplitudes.  By construction we look for
    cascade-internal observables, not QFT analogs.
"""

from __future__ import annotations

import math


# ---------------------------------------------------------------------------
# Cascade primitives
# ---------------------------------------------------------------------------

def R_cascade(d: int) -> float:
    return math.exp(math.lgamma((d + 1) / 2.0) - math.lgamma((d + 2) / 2.0))


def alpha_cascade(d: int) -> float:
    return R_cascade(d) ** 2 / 4.0


def Phi_cascade(d_max: int, d_min: int = 5) -> float:
    """Sum of p(d) = ln(R(d-1)/R(d)) from d=d_min to d=d_max."""
    s = 0.0
    for d in range(d_min, d_max + 1):
        s += math.log(R_cascade(d - 1) / R_cascade(d))
    return s


CHI = 2
GAMMA_HALF = math.sqrt(math.pi)


# Four distinguished source layers
SOURCES = {
    "d_V (volume max)":    5,
    "d_0 (area max)":      7,
    "d_gw (gauge window)": 14,
    "d_1 (phase trans)":   19,
}

# Four Bott Dirac layers
DIRAC_LAYERS_BOTT = [5, 13, 21, 29]

# Four Hurwitz dimensions
HURWITZ_DIMS = [1, 2, 4, 8]


# ---------------------------------------------------------------------------
# Survey 1: Four-source products and sums
# ---------------------------------------------------------------------------

def survey_four_sources():
    print("=" * 76)
    print("SURVEY 1: Four distinguished source layers (cascade-internal 4-fold)")
    print("=" * 76)
    print()

    src_alphas = {name: alpha_cascade(d) for name, d in SOURCES.items()}
    print(f"  {'Source':<30s}  {'d':>3}  {'alpha(d)':>10}")
    for name, d in SOURCES.items():
        print(f"  {name:<30s}  {d:>3}  {alpha_cascade(d):>10.5f}")
    print()

    P = 1.0
    S = 0.0
    P_chi = 1.0   # product of alpha(d)/chi
    P_chi_sq = 1.0   # product of alpha(d)/chi^2
    for d in SOURCES.values():
        P *= alpha_cascade(d)
        S += alpha_cascade(d)
        P_chi *= alpha_cascade(d) / CHI
        P_chi_sq *= alpha_cascade(d) / (CHI ** 2)

    print(f"  Bare four-source product:  P = prod alpha(d^*) = {P:.4e}")
    print(f"  Four-source sum:           S = sum alpha(d^*)  = {S:.4f}")
    print(f"  Product /chi:    prod alpha/chi               = {P_chi:.4e}")
    print(f"  Product /chi^2:  prod alpha/chi^2             = {P_chi_sq:.4e}")
    print(f"  Product * 2*pi^2 (n=4 cascade factor):        = {P * 2*math.pi**2:.4e}")
    print(f"  Product * 4*pi^2 (n=4 with both signs):       = {P * 4*math.pi**2:.4e}")
    print(f"  Product * 6*pi^2 (n=4, 3 generations):        = {P * 6*math.pi**2:.4e}")
    print()

    # Check against known cascade scales / gaps
    print("  Comparisons with known scales:")
    print()

    # Solar mass-squared splitting
    obs_dm2_sol = 7.5e-5   # eV^2
    print(f"    Solar splitting Delta m^2_sol = {obs_dm2_sol:.4e} eV^2")
    print(f"      P * 4*pi^2  = {P*4*math.pi**2:.4e}  (ratio: {P*4*math.pi**2/obs_dm2_sol:.4f})")
    print(f"      P * 2*pi^2  = {P*2*math.pi**2:.4e}  (ratio: {P*2*math.pi**2/obs_dm2_sol:.4f})")
    print(f"      P * pi^2/16 = {P*math.pi**2/16:.4e}  (ratio: {P*math.pi**2/16/obs_dm2_sol:.4f})")
    print()

    # m_29 / m_e ratio
    m_29 = 543.0  # eV
    m_e = 511_000.0  # eV
    ratio_29_e = m_29 / m_e
    print(f"    m_29 / m_e = {ratio_29_e:.4e}")
    print(f"      P * sqrt(2*pi^2) = {P * math.sqrt(2*math.pi**2):.4e}")
    print(f"      sqrt(P)          = {math.sqrt(P):.4e}")
    print()

    # Theta_13 (smallest PMNS angle)
    sin2_theta13 = 0.022   # PDG approx
    print(f"    sin^2(theta_13) (PMNS) = {sin2_theta13:.4f}")
    print(f"      S^2  = {S**2:.4f}")
    print(f"      P^(1/4) = {P**(0.25):.4f}")
    print()


# ---------------------------------------------------------------------------
# Survey 2: Four Bott-periodic Dirac layers
# ---------------------------------------------------------------------------

def survey_four_dirac():
    print("=" * 76)
    print("SURVEY 2: Four Bott-periodic Dirac layers")
    print("=" * 76)
    print()

    print(f"  {'Layer':<6}  {'d':>3}  {'alpha(d)':>10}")
    for d in DIRAC_LAYERS_BOTT:
        print(f"  Dirac  {d:>3}  {alpha_cascade(d):>10.5f}")
    print()

    P = 1.0
    S = 0.0
    for d in DIRAC_LAYERS_BOTT:
        P *= alpha_cascade(d)
        S += alpha_cascade(d)

    print(f"  Four-Dirac-layer product (incl. d=29): {P:.4e}")
    print(f"  Four-Dirac-layer sum  (incl. d=29):    {S:.4f}")
    print()

    # n=4 prediction: sum over 4 Dirac layers of chi*Gamma(1/2)^4
    n4_4layers = 4 * CHI * GAMMA_HALF ** 4   # 8*pi^2 if all four contribute
    n4_3layers = 3 * CHI * GAMMA_HALF ** 4   # 6*pi^2 if only first three
    print(f"  n=4 cascade structural factor (4 layers, incl. d=29):")
    print(f"    4 * chi * Gamma(1/2)^4 = 8*pi^2 = {n4_4layers:.4f}")
    print(f"  vs n=4 (3 layers, generations only):")
    print(f"    3 * chi * Gamma(1/2)^4 = 6*pi^2 = {n4_3layers:.4f}")
    print()
    print("  STRUCTURAL CHOICE: at n=4, do all four Dirac layers contribute, or")
    print("  only the three generation layers?  Per the cascade's structural")
    print("  philosophy (d=29 past d_1=19 phase transition wall), d=29 should")
    print("  NOT contribute to charged-fermion observables at any loop order.")
    print()


# ---------------------------------------------------------------------------
# Survey 3: Four Hurwitz dimensions
# ---------------------------------------------------------------------------

def survey_four_hurwitz():
    print("=" * 76)
    print("SURVEY 3: Four Hurwitz division algebras")
    print("=" * 76)
    print()

    print(f"  {'Algebra':<8}  {'dim':>3}  {'alpha(dim)':>10}  {'R(dim)':>10}")
    for name, d in zip(["R", "C", "H", "O"], HURWITZ_DIMS):
        print(f"  {name:<8}  {d:>3}  {alpha_cascade(d):>10.5f}  {R_cascade(d):>10.5f}")
    print()

    P_alpha = 1.0
    P_R = 1.0
    for d in HURWITZ_DIMS:
        P_alpha *= alpha_cascade(d)
        P_R *= R_cascade(d)

    print(f"  Hurwitz product prod alpha(d):  {P_alpha:.4e}")
    print(f"  Hurwitz product prod R(d):       {P_R:.4f}")
    print()

    # The Hurwitz dim sum is 1+2+4+8 = 15, product is 64
    print(f"  Sum of Hurwitz dims: 1+2+4+8 = {sum(HURWITZ_DIMS)}")
    print(f"  Product of Hurwitz dims: 1*2*4*8 = {math.prod(HURWITZ_DIMS)}")
    print()

    # Check against cascade observables involving these dimensions
    print("  Cascade observables with Hurwitz-dimension dependence:")
    print(f"    alpha(8) (Bott-period coupling): {alpha_cascade(8):.5f}")
    print(f"    alpha(4) (observer dimension):   {alpha_cascade(4):.5f}")
    print(f"    R(4) (observer R):                {R_cascade(4):.5f}")
    print()


# ---------------------------------------------------------------------------
# Survey 4: 4-fold combinations crossed with chirality-theorem n=4
# ---------------------------------------------------------------------------

def survey_chirality_combinations():
    print("=" * 76)
    print("SURVEY 4: chirality-theorem n=4 crossed with 4-fold cascade structures")
    print("=" * 76)
    print()
    print("Structural form: chi*Gamma(1/2)^4 = 2*pi^2 multiplied by a 4-fold")
    print("cascade product or sum.  Test against:")
    print("  - Solar splitting Delta m^2_sol")
    print("  - PMNS angles")
    print("  - Cosmological parameters (n_s, A_s)")
    print()

    twopisq = 2 * math.pi ** 2

    # 4-source product times n=4 factor
    P_src = 1.0
    for d in SOURCES.values():
        P_src *= alpha_cascade(d)

    # 4-source sum times n=4 factor
    S_src = sum(alpha_cascade(d) for d in SOURCES.values())

    candidates = [
        ("alpha(5)*alpha(7)*alpha(14)*alpha(19) * 2*pi^2", P_src * twopisq),
        ("alpha(5)+alpha(7)+alpha(14)+alpha(19) * 2*pi^2", S_src * twopisq),
        ("(alpha(5)*alpha(7)*alpha(14)*alpha(19))^(1/4)", P_src ** 0.25),
        ("sqrt(P_src) * 2*pi", math.sqrt(P_src) * 2 * math.pi),
        ("P_src * pi", P_src * math.pi),
        ("P_src / 2*pi", P_src / (2 * math.pi)),
        ("3 * 2*pi^2 (n=4, 3 gens, no source factor)", 3 * twopisq),
        ("4 * 2*pi^2 (n=4, 4 dirac layers)", 4 * twopisq),
    ]

    obs = [
        ("Solar splitting Delta m^2_sol (eV^2)", 7.5e-5),
        ("Solar mass-mixing M_12 ~ Delta m^2_sol/(2*m_1) (eV)", 7.5e-5/(2*0.0493)),
        ("sin^2 theta_13 (PMNS reactor angle)", 0.022),
        ("sin^2 theta_12 (PMNS solar angle)", 0.31),
        ("sin^2 theta_23 (PMNS atm. angle)", 0.55),
        ("n_s (CMB tilt) - 1 = -0.035", -0.035),
        ("A_s (primordial amp.) ~ 2.1e-9", 2.1e-9),
        ("alpha (fine structure)", 1/137.036),
        ("Higgs quartic lambda (SM)", 0.131),
    ]

    print(f"  {'Cascade candidate':<55s}  {'value':>14s}")
    for name, val in candidates:
        print(f"  {name:<55s}  {val:>14.4e}")
    print()
    print(f"  {'Observable':<55s}  {'value':>14s}")
    for name, val in obs:
        print(f"  {name:<55s}  {val:>14.4e}")
    print()

    # Now check ratios systematically
    print("  Cross-check matrix (candidate / observable, log10):")
    print(f"  {'':>50s}  " + "  ".join(f"{name[:12]:>12s}" for name, _ in obs))
    for cname, cval in candidates:
        row = []
        for oname, oval in obs:
            ratio = cval / oval
            # Color code: |log10(ratio)| < 0.1 means within 25% match
            l = math.log10(abs(ratio))
            row.append(f"{l:>+12.2f}")
        print(f"  {cname[:48]:<50s}  " + "  ".join(row))
    print()
    print("  Look for entries near 0.00 (=match within 25%) for novel matches.")
    print()


# ---------------------------------------------------------------------------
# Survey 5: 4-fold compositional descent
# ---------------------------------------------------------------------------

def survey_compositional_descent():
    print("=" * 76)
    print("SURVEY 5: 4-fold compositional cascade descent")
    print("=" * 76)
    print()
    print("The cascade descent traverses {d=4, 5, ..., 217} in order.")
    print("A 4-fold compositional structure could pick four specific layers")
    print("and form a cascade-native 4-product.  Natural choices:")
    print()
    print("  - Four distinguished sources: {5, 7, 14, 19}")
    print("  - Four Dirac layers (Bott): {5, 13, 21, 29}")
    print("  - Four Hurwitz dims at observer: {1, 2, 4, 8}")
    print("  - Four critical points (Part 0): {5, 7, 19, 217}, but d=217=Planck sink")
    print()

    # Phi values at the four sources
    print("  Phi values at four distinguished source layers:")
    for name, d in SOURCES.items():
        phi = Phi_cascade(d)
        print(f"    Phi({d}) = {phi:.4f}  ({name})")
    print()

    # Sum of Phi values at four sources
    sum_phi_4src = sum(Phi_cascade(d) for d in SOURCES.values())
    print(f"  Sum Phi(d^*) over four sources: {sum_phi_4src:.4f}")
    print(f"  exp(-sum Phi):                  {math.exp(-sum_phi_4src):.4e}")
    print()

    # Phi at four Dirac layers
    print("  Phi values at four Bott Dirac layers:")
    for d in DIRAC_LAYERS_BOTT:
        phi = Phi_cascade(d)
        print(f"    Phi({d}) = {phi:.4f}")
    print()

    sum_phi_4dirac = sum(Phi_cascade(d) for d in DIRAC_LAYERS_BOTT)
    print(f"  Sum Phi(d) over four Dirac layers: {sum_phi_4dirac:.4f}")
    print(f"  exp(-sum Phi):                     {math.exp(-sum_phi_4dirac):.4e}")
    print()

    # Notable comparisons
    print("  Comparisons:")
    print(f"    Cosmological constant Lambda ~ 10^(-120):       1e-120")
    print(f"    exp(-2*Phi(217))    ~ cascade Lambda")
    print(f"    Hubble: H_0 (Mpl units) ~ 10^(-60):              1e-60")
    print(f"    Fermi scale v/M_Pl ~ 10^(-17):                   1e-17")
    print(f"    Electron m_e/M_Pl ~ 10^(-22):                    1e-22")
    print()


# ---------------------------------------------------------------------------
# Synthesis
# ---------------------------------------------------------------------------

def synthesis():
    print("=" * 76)
    print("SYNTHESIS: most promising 4-fold cascade structures")
    print("=" * 76)
    print()
    print("This survey scanned natural 4-fold cascade structures against")
    print("known cascade gaps and notable numerical patterns.  Look for")
    print("entries with near-0 log10 ratios in Survey 4's matrix; those are")
    print("matches within 25%.")
    print()
    print("If no clean match: the n=4 chirality-theorem prediction is")
    print("structurally forced as a formula but does NOT correspond to a")
    print("currently-identified cascade observable, even when paired with")
    print("the cascade's natural 4-fold structures.  This would close")
    print("Candidate (3) negatively, leaving Candidate (1) [QFT-amplitude")
    print("category error, rejected] and Candidate (2) [d=29 activation,")
    print("structurally suppressed] also closed.")
    print()
    print("If a clean match: that's the novel cascade observable.  Pursue")
    print("it as a paper update and structural derivation target.")
    print()


def main():
    print()
    print("CASCADE n=4 CANDIDATE (3): NATIVE 4-FOLD STRUCTURE SURVEY")
    print()
    survey_four_sources()
    survey_four_dirac()
    survey_four_hurwitz()
    survey_chirality_combinations()
    survey_compositional_descent()
    synthesis()


if __name__ == "__main__":
    main()
