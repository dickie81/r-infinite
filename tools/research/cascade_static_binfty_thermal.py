#!/usr/bin/env python3
"""
Static B^infty + basin-filter-throughout: cascade-native thermodynamics
exploration.

CONTEXT
=======
The cascade's base ontology is B^infty -- infinite-dim unit ball, all
dimensions exist eternally as static structure.  Part VI's truncated-
tower view (time = tower growth) is a particular dynamical reading of
this static structure, classified as Tier 5 by Part VI itself (line
1366: "No result of Part VI is Tier 1 or Tier 2").

Under static B^infty:
  - All cascade layers exist eternally, including d=217
  - Matter exists "pre-Big-Bang" in different character (structural
    existence vs observable thermal occupancy)
  - Basin symmetry chi(S^4)=2 (Part IVb thm:chirality-factorisation,
    Tier 1) operates throughout
  - The "Big Bang" is observational accessibility change, not creation

This raises the question: if basin filter operates LOCALLY throughout
cosmic history (consistent with static B^infty), what does cascade-native
thermodynamics predict at BBN and recombination?

THIS VERIFIER
=============
Computes cascade BBN g_eff under the static-B^infty + basin-filter
reading and compares to:
  - SM expectation g_eff(BBN) ~ 10.75 (consistent with observed Y_p)
  - Cascade Reading 8 at recombination

If the static-B^infty + basin-filter reading FAILS BBN, then it is not
the cascade's correct thermal history -- which means either (a) Reading 8
is also wrong, (b) basin filter is NOT operative locally, or (c) cascade
thermal physics is more complex than uniform basin-filter.

If it PASSES BBN, then it might be a viable cascade-native alternative
to Part VI's "Phase D = SM Boltzmann" reading.
"""

import math


def main() -> None:
    print("=" * 76)
    print("Static B^infty + basin-filter-throughout: BBN cross-check")
    print("=" * 76)
    print()

    T_BBN_MeV = 1.0
    m_e_MeV = 0.511
    N_c = 3
    chi = 2

    # SM baseline at BBN
    # Photons: 2 d.o.f.
    # e+ + e-: 4 d.o.f. (2 helicities x 2 charges) at T > m_e
    # 3 neutrinos: 6 d.o.f. (3 species x 2 helicities, all relativistic)
    g_BBN_SM = 2 + (7/8) * (4 + 6)
    print(f"SM g_eff(BBN) = 2 + (7/8)*(4 e+e- + 6 nu) = {g_BBN_SM}")
    print(f"Observed BBN g_eff = ~10.75 (consistent with Y_p, N_eff = 3.0)")
    print(f"BBN constraint precision: ~5% on g_eff")
    print()

    print("=" * 76)
    print("CASCADE READINGS UNDER STATIC B^infty")
    print("=" * 76)
    print()

    # Reading X1: basin filter operative LOCALLY throughout, but no other modifications
    # e+ in antipodal basin (NOT in our basin's thermal bath at any T)
    # e- in our basin
    # 3 neutrinos: only LEFT-handed in our basin (1 d.o.f./species)
    # No sector-dim N_c factor on either e- or nu
    # Photon basin-symmetric, no filter

    print("Reading X1: basin filter local, no sector-dim, no chirality power")
    print("  Photon: 2 d.o.f. (basin-symmetric)")
    print("  e^-: 2 d.o.f. (e+ in antipodal basin, locally absent)")
    print("  3 nu (left-handed only): 3 d.o.f.")
    g_X1 = 2 + (7/8) * (2 + 3)
    print(f"  g_eff(BBN) = 2 + (7/8)*(2 + 3) = {g_X1:.3f}")
    print(f"  vs SM 10.75: dev {(g_X1/g_BBN_SM-1)*100:+.1f}%")
    print(f"  N_eff equivalent: ({g_X1} - 2 - 7/4) / (7/4) = {(g_X1 - 2 - 7/4)/(7/4):.2f}")
    print(f"  Observed N_eff = 2.99 +/- 0.17 -- INCONSISTENT")
    print()

    # Reading X2: basin filter + sector-dim N_c uniformly applied (Reading 8 extended to BBN)
    print("Reading X2: basin filter local + Reading 8 unified-sector (N_c/chi^4 on all fermions)")
    print("  Photon: 2 d.o.f.")
    print("  e^-: 2 * N_c/chi^4")
    print("  3 nu (left-handed): 3 * N_c/chi^4")
    g_X2 = 2 + (7/8) * (2 + 3) * (N_c / chi**4)
    print(f"  g_eff(BBN) = 2 + (7/8)*(2 + 3)*(N_c/chi^4) = {g_X2:.3f}")
    print(f"  vs SM 10.75: dev {(g_X2/g_BBN_SM-1)*100:+.1f}%")
    print(f"  RULED OUT by BBN")
    print()

    # Reading X3: basin filter + e+ pair production at T > m_e (transient e+ in basin)
    # SM-like at high T (e+ is in our basin transiently from pair production)
    # Cascade-native at low T (e+ has migrated/decoupled to antipodal basin)
    # This is Part VI-like but with basin filter activating at T < m_e
    print("Reading X3: pair production keeps e+ in basin at T > m_e")
    print("           basin filter activates at T < m_e (epoch-dependent)")
    print("  At BBN (T = 1 MeV ~ m_e): e+ still in our basin via thermal pair production")
    print("  All species relativistic and thermal: cascade matches SM")
    print(f"  g_eff(BBN) = {g_BBN_SM} (= SM)")
    print(f"  At recombination (T << m_e): e+ in antipodal basin only")
    print(f"  Reading 8 activates: g_eff(recomb) = 2.984, T_CMB closes to +0.02%")
    print(f"  CONSISTENT WITH BBN, but requires Tier 5 mechanism for the transition")
    print()

    # Reading X4: cascade has different thermal physics altogether
    # Not pure Boltzmann; cascade-native amplitude weighting
    print("Reading X4: cascade has non-Boltzmann thermal physics")
    print("  Speculative; no specific computation possible without further structural work")
    print("  The cascade has not derived its thermal physics rigorously beyond")
    print("  Part V's SM g_eff import and Part VI's prop:g_eff at T_RH.")
    print()

    # Conclusion
    print("=" * 76)
    print("FINDING")
    print("=" * 76)
    print(f"""
Of the four scenarios under static B^infty + basin filter:

  Reading X1 (basin filter local, no Reading 8): g_eff = {g_X1:.2f}
    Off SM by {(g_X1/g_BBN_SM-1)*100:+.0f}%, INCONSISTENT with BBN observations.
    Naive 'left-handed only' basin restriction fails BBN.

  Reading X2 (basin filter + Reading 8 unified): g_eff = {g_X2:.2f}
    Off SM by {(g_X2/g_BBN_SM-1)*100:+.0f}%, dramatically RULED OUT.

  Reading X3 (epoch-dependent activation at T = m_e): g_eff = {g_BBN_SM:.2f} (= SM)
    PASSES BBN, allows Reading 8 at recombination.
    Requires Tier 5 mechanism for basin filter activation transition.

  Reading X4 (cascade non-Boltzmann thermal): undetermined
    Speculative, no rigorous derivation available.

CONCLUSION:
A pure static B^infty + uniform basin filter reading is NOT consistent
with BBN observations.  The cascade either:
  (a) has SM-like thermal physics post-Big-Bang (Part VI Tier 5 reading,
      T_CMB residual stays at -3.07%)
  (b) has an epoch-dependent rule with transition at T ~ m_e (Reading X3,
      Tier 5, allows Reading 8 closure)
  (c) has non-Boltzmann cascade-native thermal physics (X4, speculative)

The user's structural insight (matter pre-217 with different character)
is consistent with B^infty.  But the THERMAL implications -- whether
basin filter operates locally or only globally -- are NOT determined by
B^infty alone.  Local basin filter operating uniformly fails BBN; some
form of epoch-dependence or non-Boltzmann thermal physics is required.

The genuine open question: what is cascade-native thermal physics?
The cascade has theorem-level structural ingredients (B^infty static,
basin symmetry, sector-dim mechanism) but has not derived its thermal
physics rigorously beyond importing SM Boltzmann (Part V T_CMB) and
deriving prop:g_eff at T_RH (Part VI Tier 3).

Reading 8 stands as a Tier 5 candidate; closing it requires deriving
cascade-native post-Big-Bang thermal physics structurally, which is
genuinely open work, not resolvable by purely structural arguments at
the current state of cascade derivation.
""".rstrip())


if __name__ == "__main__":
    main()
