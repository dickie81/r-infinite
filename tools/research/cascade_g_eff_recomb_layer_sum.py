#!/usr/bin/env python3
"""
Cascade-native g_eff at recombination via Part VI prop:g_eff template
extended to T_recomb.

CONTEXT
=======
Part VI Proposition prop:g_eff derives g_eff cascade-natively at T_RH:
  g_eff(T_RH) = 28 (boson) + (7/8) * 90 (fermion) = 106.75
matching SM exactly.  This is a flat sum over distinguished cascade layers
(d=5, 12, 13, 14, 21) where every species is relativistic.

At T_recomb, only photons + neutrinos are relativistic.  The cascade
needs an analogous derivation that accounts for:
  (i) which species are relativistic at T_recomb (only gamma + 3 nu)
  (ii) cascade descent factors from each species' home layer to the
       observer at d=4
  (iii) the basin / chirality / sector-dim modifications under cascade
       no-annihilation logic

This verifier explores TWO candidate cascade-native rules and compares
their predictions to Reading 8 (the leading T_CMB closure candidate).

THE TWO CANDIDATE RULES
=======================
RULE A: PER-GENERATION CASCADE DESCENT
  Each neutrino at its home layer (d=5, 13, 21) gets its OWN descent
  factor based on the cascade boundaries it crosses to reach observer
  at d=4.
    nu_tau (d=5):  k=0 boundaries -> factor 1
    nu_mu  (d=13): k=2 boundaries -> factor N_c/chi^2 = 3/4
    nu_e   (d=21): k=4 boundaries -> factor N_c/chi^4 = 3/16
  Photon (d=14): boson, traverses gauge layers transparently -> factor 1
  Total: g_eff = 2 + 1.75 + 1.3125 + 0.3281 = 5.39
  Predicts: T_CMB = 2.35 K, dev -13.7% from observed 2.7255 K

RULE B: UNIFIED NEUTRINO SECTOR
  All 3 neutrino generations are coupled via the cascade path-tensor
  V_12 (x) V_13 (x) V_14 (Part IVa rem:path-tensor).  Cascade radiation
  samples the FULL path-tensor sector, with descent factor set by the
  maximal sector extension at d=21.
    All 3 neutrinos: factor N_c/chi^4 = 3/16 (uniform)
  Photon (d=14): boson transparent -> factor 1
  Total: g_eff = 2 + 5.25 * 3/16 = 2.984
  Predicts: T_CMB = 2.726 K, dev +0.02% (RECOVERS READING 8)

ARGUMENTS FOR EACH RULE
=======================
RULE A (per-generation):
  + Treats each layer independently, mirroring Part VI prop:g_eff at T_RH
    (which sums contributions per layer without cross-coupling)
  + Each species' descent path is geometrically distinct
  - Ignores path-tensor coupling between generations
  - Predicts cosmic neutrino background dominated by nu_tau (at d=5),
    which is testable: measuring CnB anisotropy would distinguish

RULE B (unified sector):
  + Uses cascade path-tensor structure (Part IVa rem:path-tensor) which
    couples generations within the same V_12 (x) V_13 (x) V_14 framework
  + Cascade neutrino sector unified at high-T (all 3 thermalised together
    via SU(2) and U(1) gauge couplings), preserved at low-T
  + Reading 8 closure to +0.02% provides numerical evidence
  + Consistent with SM cosmic neutrino background equality (all 3 species
    at same T_nu)
  - Requires path-tensor "maximal extension" choice (why d=21 not d=29?)
  - More structurally complex than rule A

WHAT'S DIFFERENT AT T_RH vs T_RECOMB
=====================================
At T_RH:
  - All distinguished layers are relativistic AT their home temperatures
  - Each layer contributes its full thermal d.o.f.  No descent factors
    needed because each layer is "live" at its own home.
  - Sum: 106.75

At T_recomb:
  - Most species non-relativistic (decoupled)
  - Photons and neutrinos remain relativistic, BUT at temperatures set
    by the post-Big-Bang cosmological expansion
  - In SM: e+e- annihilation cooled neutrinos relative to photons
  - In cascade no-annihilation: cooling mechanism must be different
  - The DIFFERENCE in T at T_recomb (relative to T_RH per-layer thermal
    state) is what cascade descent factors must capture

CASCADE NO-ANNIHILATION COOLING MECHANISM (CANDIDATE)
======================================================
Without e+e- annihilation, photons and neutrinos can stay coupled longer
(or never decouple in the SM sense).  The cosmological expansion redshifts
both equally.  But the cascade has BASIN STRUCTURE: neutrinos are chirality-
broken (left-handed only in our basin), while photons are chirality-symmetric.

Conjecture: the cascade BASIN FILTER applies at the observer's frame to
relativistic species inheriting from cascade descent paths.  Photons (basin-
symmetric) are unfiltered.  Neutrinos (chirality-broken) are filtered by
1/chi^k where k counts Bott periods crossed in their cascade descent.

For a UNIFIED neutrino sector (Rule B): k=4 from path-tensor maximal
extension d=21.  This gives 1/chi^4.  Combined with sector-dim N_c at
the d=12 gauge layer crossing, total factor is N_c/chi^4 = 3/16.

This is consistent with the cascade's no-semiclassics commitment: it does
NOT use Bogoliubov transformations or thermodynamic decoupling. The
suppression is purely STRUCTURAL (basin filter + sector-dim ratio), not
thermodynamic.

NUMERICAL OUTPUT
================
"""

import math


def main() -> None:
    T_obs = 2.7255
    T_leading = 2.642
    g_eff_SM = 3.383
    N_c = 3
    chi = 2

    print("=" * 76)
    print("Cascade g_eff at recombination: layer-sum analysis")
    print("=" * 76)
    print()

    # Rule A: per-generation
    contributions_A = []
    contributions_A.append(("photon (d=14, boson)", 2, 1.0, 2.0, "boson transparent"))
    contributions_A.append(("nu_tau (d=5)",  2, 1.0, (7/8)*2*1.0, "k=0, no boundary"))
    contributions_A.append(("nu_mu (d=13)",  2, N_c/chi**2, (7/8)*2*N_c/chi**2, "k=2, 1 boundary, sector-dim"))
    contributions_A.append(("nu_e (d=21)",   2, N_c/chi**4, (7/8)*2*N_c/chi**4, "k=4, 2 boundaries, sector-dim"))
    g_A = sum(eff for _, _, _, eff, _ in contributions_A)

    print("RULE A: per-generation cascade descent")
    print(f"  {'species':<26} {'raw':>6} {'factor':>10} {'effective':>10}")
    for spec, raw, fac, eff, _ in contributions_A:
        print(f"  {spec:<26} {raw:>6} {fac:>10.5f} {eff:>10.5f}")
    print(f"  g_eff(A) = {g_A:.4f}")
    T_A = T_leading * (g_eff_SM / g_A) ** 0.25
    print(f"  T_CMB    = {T_A:.4f} K   dev {(T_A/T_obs-1)*100:+.3f}%")
    print()

    # Rule B: unified sector
    g_gamma_B = 2.0
    g_nu_B = (7/8) * 2 * 3 * (N_c / chi**4)
    g_B = g_gamma_B + g_nu_B
    T_B = T_leading * (g_eff_SM / g_B) ** 0.25
    print("RULE B: unified neutrino sector via path-tensor (Reading 8)")
    print(f"  photon (d=14):       {g_gamma_B:.4f} (transparent)")
    print(f"  3 neutrinos unified: (7/8)(2)(3)(N_c/chi^4) = {g_nu_B:.4f}")
    print(f"  g_eff(B) = {g_B:.4f}")
    print(f"  T_CMB    = {T_B:.4f} K   dev {(T_B/T_obs-1)*100:+.3f}%")
    print()

    # Comparison and observed
    print("=" * 76)
    print("Comparison")
    print("=" * 76)
    print(f"  {'Rule':<40} {'g_eff':>8} {'T_CMB (K)':>12} {'dev':>8}")
    print(f"  {'Rule A (per-generation)':<40} {g_A:>8.4f} {T_A:>12.4f} {(T_A/T_obs-1)*100:>+7.2f}%")
    print(f"  {'Rule B (unified sector, Reading 8)':<40} {g_B:>8.4f} {T_B:>12.4f} {(T_B/T_obs-1)*100:>+7.3f}%")
    print(f"  {'Observed':<40} {'-':>8} {T_obs:>12.4f} {0:>+7.2f}%")
    print()

    print("=" * 76)
    print("INTERPRETATION")
    print("=" * 76)
    print("""
The two rules give substantially different predictions.  Reading 8
corresponds to Rule B; Rule A gives a -14% deviation, ruling itself out
against observation.

This means: if Reading 8 is the right cascade closure, the cascade must
commit to the UNIFIED NEUTRINO SECTOR rule.  The structural justification
for this commitment is:

  The cascade path-tensor V_12 (x) V_13 (x) V_14 (Part IVa rem:path-tensor)
  couples all 3 neutrino generations within the same Hilbert-space sector.
  At recombination, the cascade radiation density samples this UNIFIED
  sector via cascade descent through the gauge window {d=12, 13, 14}.
  The descent factor for the unified sector is set by its maximal
  extension at d=21 (the heaviest neutrino home), giving N_c/chi^4.

FALSIFIABILITY:
  Rule A predicts cosmic neutrino background dominated by nu_tau (heavily
  weighted to the d=5 home).  Rule B predicts equal weighting (consistent
  with SM expectation).  CnB measurement (e.g. PTOLEMY) could distinguish.

  More immediately: Reading 8 numerically agrees with observation; Rule A
  disagrees.  This is current evidence for Rule B.

REMAINING STRUCTURAL WORK:
  1. Derive the unified sector rule from cascade primitives (currently a
     plausibility argument, not a theorem).
  2. Justify the "maximal extension d=21" choice over alternatives
     (e.g. d=29 source layer would give different factor).
  3. Derive the boson transparency at gauge layers from cascade
     fermion-gauge coupling structure (Part IVb
     rem:fermion-gauge-coupling-proposal couples fermions; bosons are
     not addressed there).
  4. Cross-check against BBN epoch (T ~ 1 MeV) where the cascade should
     give g_eff ~ 10.75 if same rule applies.

If these structural pieces close, Reading 8 is promoted from candidate
to derivation.  Currently it stands as a candidate with explicit gaps.
""".rstrip())


if __name__ == "__main__":
    main()
