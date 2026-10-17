#!/usr/bin/env python3
"""
Digging past Addendum 9: the sum-rule kill, a cascade-native
normalisation argument, and the energy-bound side of the capacity
postulate confronted with the neutrino sector.

Sources read directly (CLAUDE.md Check 1): part4b.tex lines 4086-4092
(neutrino open question: heaviest mass DERIVED as m_nu = m_29 *
alpha(21)/chi^8 = 0.0493 eV vs observed 0.0495; the two lighter masses
from the same form are admitted inconsistent with the solar splitting;
ordering prediction "nu_e heaviest, nu_tau lightest").

Parts
  A. Sum-rule kill: if ALL SM species' modes count against the horizon
     bits, the bound is oversaturated by ~10^11 -- the saturation
     postulate is only consistent as a single-effective-cutoff (CKN)
     statement, as used in Addenda 7-9.  Recorded as a tested-and-
     killed alternative reading.
  B. Cascade-native normalisation: norm-blindness (the adelic balance
     law sees total arithmetic size, not species -- the same property
     that gave the equivalence principle in Addendum 6) forbids
     g-dependence; the cascade's cell-counting style (S = A/4 in
     Planck cells; discrete states, not momentum phase space) selects
     the bare count m^3 V = S.  Defensible-not-forced: sharpened
     window m* = 17-20 MeV (nats to bits).  Still inside the confined
     interior; the lattice-census target stands.
  C. Energy-bound side: identifying the archimedean saturation scale
     Lambda_E = R^(-1/2) with the LIGHTEST arithmetic mode (lightest
     neutrino) predicts m_1 ~ 1.7-3.2 meV.  With measured splittings:
     NORMAL ordering Sigma m_nu = 61-63 meV (inside the narrow window
     between the oscillation floor 58.5 and cosmology's ~70 meV
     ceiling); INVERTED ordering would give 103-104 meV -- already
     disfavoured.  Near-term falsifiable (DESI/CMB-S4 Sigma; JUNO
     ordering).
  D. The layer-29 check: the papers' own source mass m_29 computed
     from their formula is ~600 eV -- sub-keV, NOT the ~1e9-1e12 GeV
     leptogenesis scale.  The hoped-for independent derivation of the
     census freeze-out epoch (Addendum 6) finds NO anchor at d=29:
     that route is closed.
  E. The fork: the cascade's stated ordering (nu_e heaviest) OPPOSES
     the capacity extension's normal-ordering prediction, and stands
     in tension with measured theta_13 (|U_e3|^2 = 0.022 puts little
     nu_e in the atmospheric-split state).  JUNO adjudicates between
     the papers' own neutrino flank and the capacity reading.
"""

import math

MRED = 2.435e18
RHO = 7.15e-121
R = math.sqrt(3.0 / RHO)
S = math.pi * R * R
V = (4.0 / 3.0) * math.pi * R ** 3
DM2_SOL = 74.2      # meV^2
DM2_ATM = 2517.0    # meV^2


def Rfun(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return Rfun(d) ** 2 / 4.0


def part_A():
    print("=" * 74)
    print("PART A: the all-species sum rule is dead")
    print("=" * 74)
    mt = 172.57 / MRED
    lhs = 12 * mt ** 3            # top quark alone dominates
    rhs = 6 * math.pi ** 2 * S / V
    print(f"  sum_i g_i m_i^3 (top alone) = {lhs:.2e}"
          f"   vs   bound {rhs:.2e}")
    print(f"  oversaturation ~ 10^{math.log10(lhs/rhs):.0f}: the horizon bits")
    print("  cannot count every species' Compton modes.  Saturation is only")
    print("  consistent as a single effective IR cutoff (CKN reading), as")
    print("  used in Addenda 7-9.  Alternative reading tested and killed.")


def part_B():
    print()
    print("=" * 74)
    print("PART B: cascade-native normalisation (defensible, not forced)")
    print("=" * 74)
    m_nats = (S / V) ** (1 / 3)
    m_bits = (S / (V * math.log(2))) ** (1 / 3)
    print(f"  norm-blindness (Addendum 6: the balance law sees total")
    print(f"  arithmetic size, not species) forbids g; cell-counting")
    print(f"  (S = A/4 in Planck cells) selects the bare count m^3 V = S:")
    print(f"    m* = {m_nats*MRED*1e3:.1f} MeV (nats)"
          f" .. {m_bits*MRED*1e3:.1f} MeV (bits)")
    print("  still inside the confined interior; only a nonperturbative")
    print("  census can name the matching QCD quantity.")


def part_C():
    print()
    print("=" * 74)
    print("PART C: the energy-bound side -> the lightest neutrino")
    print("=" * 74)
    m1_lo = R ** -0.5 * MRED * 1e12                 # crude, meV
    m1_hi = (8 * math.pi ** 2 / 6) ** 0.25 * R ** -0.5 * MRED * 1e12
    print(f"  Lambda_E window: {m1_lo:.1f} - {m1_hi:.1f} meV"
          f"  ->  identify with lightest nu mass m_1")
    for m1 in (m1_lo, m1_hi):
        m2 = math.sqrt(m1 ** 2 + DM2_SOL)
        m3 = math.sqrt(m1 ** 2 + DM2_ATM)
        print(f"  NO: m = ({m1:.1f}, {m2:.1f}, {m3:.1f}) meV"
              f"   Sigma = {m1+m2+m3:.1f} meV")
    m3 = m1_lo
    m1 = math.sqrt(m3 ** 2 + DM2_ATM - DM2_SOL)
    m2 = math.sqrt(m3 ** 2 + DM2_ATM)
    print(f"  IO: Sigma = {m1+m2+m3:.1f} meV -> disfavoured by cosmology")
    print("  prediction: NORMAL ordering, Sigma = 61-63 meV -- inside the")
    print("  surviving window [58.5 (oscillation floor), ~70 (cosmology)];")
    print("  falsifiable by DESI/CMB-S4 within years.  A Sigma bound below")
    print("  ~60 meV kills the identification (and nearly kills NO itself).")


def part_D():
    print()
    print("=" * 74)
    print("PART D: the layer-29 leptogenesis anchor is closed")
    print("=" * 74)
    m29 = 0.0493 * 2 ** 8 / alpha(21)     # from part4b: m_nu = m29 a(21)/chi^8
    print(f"  papers' formula (part4b:4086): m_nu = m_29 alpha(21)/chi^8")
    print(f"  alpha(21) = {alpha(21):.5f}  =>  m_29 = {m29:.0f} eV"
          f"  (~{m29/1e3:.2f} keV)")
    print("  the d=29 source is sub-keV -- nowhere near the 1e9-1e12 GeV")
    print("  leptogenesis window.  The hoped-for independent derivation of")
    print("  the census freeze-out epoch (Addendum 6 fossil-bias check)")
    print("  finds no anchor at layer 29: route closed.")


def part_E():
    print()
    print("=" * 74)
    print("PART E: the ordering fork")
    print("=" * 74)
    print("  papers (part4b:4092): 'inverted hierarchy relative to charged")
    print("  leptons: nu_e heaviest ... nu_tau lightest' -- and the lighter")
    print("  masses from their diagonal form (3e-4, 3e-6 eV) are admitted")
    print("  inconsistent with the solar splitting (OQ b).")
    print("  capacity extension (Part C): NORMAL ordering, m_1 ~ 2 meV.")
    print("  tension noted: nu_e-heaviest requires large nu_e content in the")
    print("  atmospheric-split state, vs measured |U_e3|^2 = 0.022.")
    print("  JUNO's ordering determination adjudicates the fork; a combined")
    print("  spectrum (cascade top 49.3 + solar-fixed middle 8.8 + capacity")
    print("  floor ~2 meV) would be complete at Sigma ~ 61 meV.")


if __name__ == "__main__":
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
