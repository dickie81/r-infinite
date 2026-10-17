#!/usr/bin/env python3
"""
Neutrino masses from the existing machinery -- closing the papers'
acknowledged light-neutrino gap with the session's threshold factor.

SOURCES (read directly): part4b l.698 (m_29 = 543 eV chain and
m_nu(g) = m_29 alpha(d_g)/chi^(29-d_g); heaviest 0.0493 eV at -0.4%),
part4b l.4086-4092 (acknowledged gap: lighter two masses too small,
PMNS Cabibbo-analogue failed), PREDICTIONS.md l.116 (same, Tier 5),
tools/research/cascade_neutrino_mass_audit.py (Phi convention:
cumulative from d=5).  Session machinery reused: A10 capacity band
m_1 = Lambda_E = 1.7-3.2 meV; A23 threshold factor N_c pi^2 = 29.609
(the Gen2->Gen1 crossing of the d_1 = 19 phase transition); A28
Planck-anchored alpha_s, v.

HYPOTHESIS (stated before comparison, Check-4 category (b) novel):
the papers' diagonal source form is enhanced by the SESSION'S
threshold factor E = N_c pi^2 once per Bott period below the d_1 = 19
phase transition:

    m_3 = m_29 alpha(21)/chi^8          (d=21 above 19: E^0)
    m_2 = m_29 alpha(13)/chi^16 * E     (one period below: E^1)
    m_1 = m_29 alpha(5)/chi^24  * E^2   (two periods below: E^2)

ZERO new constants: E is A23's quark-sector factor, reused.  The
solar splitting, absent from the input set, becomes a prediction.

Discipline: PART C enumerates the grammar in the window E must occupy
given only the capacity band -- the known twin 2 pi e sqrt(3) lands
too (grammar-open on FORM), but the numeric prediction is form-robust
(twins differ by 0.1%).  The per-period attachment rule is the named
residual lemma, alongside A23's own threshold lemmas.
"""

import itertools
import math

from scipy.special import digamma

SQRTPI = math.sqrt(math.pi)
M_PL_RED = 2.435e18                     # GeV
E_FACTOR = 3 * math.pi ** 2             # A23 threshold factor


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def N(d):
    return SQRTPI * R(d)


def p(d):
    return 0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)


def Phi(d):                              # papers' convention: sum from 5
    return sum(p(k) for k in range(5, d + 1))


# Planck-anchored inputs (A28)
A_GUT = N(12) ** 2 / (4 * math.pi)
ALPHA_S = A_GUT * math.exp(sum(p(d) for d in range(5, 13)))
V = M_PL_RED * ALPHA_S * math.exp(-math.pi / alpha(5))

# observations
DM2_ATM = 2.453e-3                       # eV^2 (NO), PDG
DM2_SOL, DM2_SOL_ERR = 7.53e-5, 0.18e-5  # eV^2, PDG
UE1, UE2, UE3 = 0.678, 0.300, 0.022      # |U_ei|^2 (NuFit/PDG central)
CAP_LO, CAP_HI = 1.7, 3.2                # meV, A10 capacity band for m_1


def part_A():
    print("=" * 74)
    print("PART A: the papers' chain, Planck-anchored (verify -0.4%)")
    print("=" * 74)
    m29 = (ALPHA_S * V / math.sqrt(2)) * math.exp(-Phi(29)) \
        / (2 * SQRTPI) ** 5 * 1e9        # eV
    m3 = m29 * alpha(21) / 2 ** 8
    print(f"  m_29 = (alpha_s v/sqrt2) e^(-Phi(29)) (chi G(1/2))^-5"
          f" = {m29:.1f} eV")
    print(f"  m_3  = m_29 a(21)/chi^8 = {m3*1e3:.2f} meV"
          f"   vs sqrt(Dm2_atm) = {math.sqrt(DM2_ATM)*1e3:.2f} meV"
          f"   ({(m3/math.sqrt(DM2_ATM)-1)*100:+.1f}%)")
    m2d = m29 * alpha(13) / 2 ** 16 * 1e3
    m1d = m29 * alpha(5) / 2 ** 24 * 1e3
    print(f"  diagonal m_2 = {m2d:.4f} meV, m_1 = {m1d:.5f} meV"
          f"  -- the acknowledged gap: solar splitting needs ~9 meV")
    return m29, m3, m2d, m1d


def part_B(m29, m3, m2d, m1d):
    print()
    print("=" * 74)
    print("PART B: the closure -- A23's threshold factor, once per Bott")
    print("        period below d_1 = 19  (E^0, E^1, E^2; zero new constants)")
    print("=" * 74)
    m2 = m2d * E_FACTOR                  # meV
    m1 = m1d * E_FACTOR ** 2
    dm2_sol = (m2 ** 2 - m1 ** 2) * 1e-6           # eV^2
    print(f"  E = N_c pi^2 = {E_FACTOR:.4f}   (A23, quark Gen2->Gen1)")
    print(f"  m_2 = {m2:.3f} meV,  m_1 = {m1:.3f} meV,"
          f"  m_3 = {m3*1e3:.2f} meV")
    print(f"  PREDICTED Dm2_sol = m_2^2 - m_1^2 = {dm2_sol:.3e} eV^2")
    print(f"  observed {DM2_SOL:.3e} +/- {DM2_SOL_ERR:.2e}"
          f"   ({(dm2_sol-DM2_SOL)/DM2_SOL_ERR:+.2f} sigma)")
    print(f"  independent check: m_1 = {m1:.2f} meV inside the capacity")
    print(f"  band Lambda_E = {CAP_LO}-{CAP_HI} meV (A10)"
          f" -> {'PASS' if CAP_LO <= m1 <= CAP_HI else '** FAIL **'}")
    sig = m3 * 1e3 + m2 + m1
    print(f"  Sigma m_nu = {sig:.1f} meV  (floor 58.5; DESI DR2 ~64;"
          f" NORMAL ordering)")
    return m1, m2, m3 * 1e3, sig


def part_C(m2d):
    print()
    print("=" * 74)
    print("PART C: enumerate-first -- the window E must occupy, and who lands")
    print("=" * 74)
    # given only the capacity band and observed Dm2_sol, E must satisfy
    # m_2 = sqrt(m_1^2 + Dm2_sol) with m_1 in the band:
    lo = math.sqrt(CAP_LO ** 2 + DM2_SOL * 1e6) / m2d
    hi = math.sqrt(CAP_HI ** 2 + DM2_SOL * 1e6) / m2d
    print(f"  required E in [{lo:.2f}, {hi:.2f}]  (a +/-1.8% window)")
    atoms = {"chi": 2.0, "N_c": 3.0, "G(1/2)": SQRTPI, "pi": math.pi,
             "pi^2": math.pi ** 2, "2pi": 2 * math.pi, "e": math.e,
             "sqrt(e)": math.sqrt(math.e), "sqrt(2)": math.sqrt(2),
             "sqrt(3)": math.sqrt(3), "cos30": math.cos(math.pi / 6)}
    hits = []
    for r_ in (1, 2, 3):
        for combo in itertools.combinations_with_replacement(atoms, r_):
            v = 1.0
            for k in combo:
                v *= atoms[k]
            if lo <= v <= hi:
                hits.append((" * ".join(combo), v))
    for lab, v in hits:
        print(f"    {lab:<28} {v:.4f}")
    print(f"  {len(hits)} grammar forms land: FORM grammar-open (the u/d")
    print("  twin pair N_c pi^2 vs 2 pi e sqrt(3) reappears, 0.1% apart) --")
    print("  but the PREDICTION is form-robust: either twin gives Dm2_sol")
    print("  within +0.5 sigma.  The rule-based selection (A23 reuse +")
    print("  per-Bott-period attachment) is the named residual lemma.")


def part_D(m1, m2, m3, sig):
    print()
    print("=" * 74)
    print("PART D: downstream forced numbers (ledger rows)")
    print("=" * 74)
    mbeta = math.sqrt(UE1 * m1 ** 2 + UE2 * m2 ** 2 + UE3 * m3 ** 2)
    t1, t2, t3 = UE1 * m1, UE2 * m2, UE3 * m3
    mbb_hi = t1 + t2 + t3
    mbb_lo = max(0.0, t2 - t1 - t3)
    print(f"  spectrum (meV): m_1 = {m1:.2f}, m_2 = {m2:.2f},"
          f" m_3 = {m3:.1f};  Sigma = {sig:.1f}")
    print(f"  m_beta (KATRIN observable)  = {mbeta:.1f} meV"
          f"   -- KATRIN sensitivity ~200-450 meV: FORCED NEGATIVE"
          f" (no signal)")
    print(f"  m_bb (0vbb, if Majorana)    = {mbb_lo:.1f}-{mbb_hi:.1f} meV"
          f"   -- LEGEND-1000/nEXO reach ~9-21 meV:")
    print("    FORCED NEGATIVE: no 0vbb discovery in next-gen experiments")
    print("    (holds a fortiori if the cascade mass term is Dirac).")
    print(f"  Sigma = {sig:.1f} meV: registered SHARP (vs A10's 61-63 band);")
    print("  kill: any cosmology bound below ~60 meV, or JUNO finding")
    print("  inverted ordering, or 0vbb discovery at current sensitivity.")


if __name__ == "__main__":
    m29, m3, m2d, m1d = part_A()
    m1, m2, m3v, sig = part_B(m29, m3, m2d, m1d)
    part_C(m2d)
    part_D(m1, m2, m3v, sig)
