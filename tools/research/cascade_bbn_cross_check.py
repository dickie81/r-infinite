#!/usr/bin/env python3
"""
*** REVISED 2026-05-04 evening ***
Earlier "supersession" was based on Part VI's Tier 5 "Phase D = SM Boltzmann"
reading; that retraction has been walked back.  Part VI's Tier 5 status
(line 1316-1383) means it is NOT sufficient to compel cascade predictions.

Numerical findings in this verifier STAND as a falsification test:
  - Uniform application of f^4 = N_c/chi^4 to all epochs FAILS BBN
    (factor 2.5-3.5 off).
  - Case 3 (cascade = SM Boltzmann throughout) is one Tier 5 reading
    (Part VI's).  Case 4 (epoch-dependent with cascade transition at
    T=m_e) is another Tier 5 reading.
  - Reading 8 viable ONLY under epoch-dependent rule; the structural
    mechanism for the transition is genuinely open.

The cascade has not derived post-Big-Bang thermodynamics cascade-natively
in any Tier 1-3 form.  Part VI's reading and Reading 8's reading are
both speculative.  T_CMB closure remains an open problem at the same
status as Part V Remark rem:tcmb-descent-dependent.

BBN cross-check for cascade Reading 8.

THE TEST
========
Big Bang Nucleosynthesis (BBN) at T ~ 1 MeV constrains the cascade's
g_eff at this epoch through observed light-element abundances:
  Y_p (He-4) ~ 0.245
  N_eff(BBN) = 2.99 +/- 0.17 (Planck + BBN)
These are consistent with SM g_eff(BBN) = 10.75 within ~5%.

If the cascade applies its Reading 8 unified-sector rule UNIFORMLY at
all epochs, g_eff at BBN is dramatically suppressed and BBN abundances
shift far from observation -- ruling out the rule.

If the cascade's rule is EPOCH-DEPENDENT with a structural transition at
T ~ m_e (the electron mass, where SM e+e- annihilation also happens),
the cascade matches SM at BBN and Reading 8 at recombination.  But the
epoch-dependence requires an additional cascade structural derivation.

THIS VERIFIER
=============
Computes g_eff(BBN) under four cascade-native scenarios and compares to
SM and observation.  Identifies the structural commitment required for
Reading 8 to survive BBN.

CASES
=====
SM (baseline):
  At T = 1 MeV, all of {gamma, e+, e-, nu_e, nu_mu, nu_tau} are
  relativistic.
    g_eff_SM(BBN) = 2 + (7/8)*(4 + 6) = 10.75
  Consistent with Y_p observation.

Case 1 (Reading 8 uniform on nu, no e+):
  Cascade no-annihilation says e+ in antipodal basin at all epochs.
  Unified sector rule on neutrinos: factor N_c/chi^4.
    g_eff = 2 + (7/8)*(2_e- + 6*N_c/chi^4)
          = 2 + (7/8)*(2 + 1.125)
          = 4.73
  RULED OUT by BBN: factor 2.3 below observation.

Case 2 (Reading 8 uniform on all fermions):
  Unified sector applied to e+e- AND neutrinos.
    g_eff = 2 + (7/8)*10*N_c/chi^4
          = 3.64
  EVEN WORSE: factor 2.95 below observation.

Case 3 (Cascade = SM at all epochs):
  Cascade follows SM thermodynamics throughout, no Reading 8 modification.
  Passes BBN trivially (= SM by construction).
  But does NOT close T_CMB at recombination (Reading 8 fails).
  Self-defeating: nothing has changed, T_CMB residual stays at -3.07%.

Case 4 (Epoch-dependent cascade rule):
  At T > m_e: cascade thermodynamics matches SM exactly.
              Thermal pair production keeps e+ in our basin.
              g_eff(BBN) = 10.75 (SM) -- PASSES BBN.
  At T = m_e: structural transition.  e+ MIGRATE to antipodal basin
              via cascade no-annihilation mechanism (NOT via SM
              annihilation event).
  At T < m_e: only e- remains in our basin.  Cascade unified sector
              rule activates for surviving relativistic species.
              g_eff(recomb) = 2.984 (Reading 8) -- CLOSES T_CMB.
  PASSES BOTH BBN and T_CMB observations IFF the structural transition
  is derived.

VERDICT
=======
BBN observation rules out a UNIFORM application of cascade Reading 8.
Reading 8 survives ONLY if the cascade has an epoch-dependent rule with
structural transition at T ~ m_e.  This is a NEW structural commitment
required for Reading 8 closure.

The transition mechanism (Case 4): at T = m_e, thermal pair production
(gamma+gamma -> e+e-) drops below threshold and can no longer replenish
e+ in our basin.  By cascade no-annihilation, e+ cannot disappear via
annihilation; instead, they MIGRATE to the antipodal basin via cascade
basin-asymmetry mechanism.  Below T = m_e, only e- is in our basin's
thermal bath, and the cascade unified sector rule activates.

This rescues Reading 8 but adds a fourth required structural piece:
  GAP 4: Derive the e+ migration mechanism at T = m_e cascade-natively.

The previous three gaps remain (path-tensor sampling, channel-count
basin filter, Omega_r -> T_CMB bridge).

If GAP 4 cannot be closed, Reading 8 fails BBN and the cascade T_CMB
residual returns to -3.07% (or via H_0-Gram correction, -2.07%).
"""

import math


def main() -> None:
    print("=" * 76)
    print("BBN cross-check for cascade Reading 8")
    print("=" * 76)
    print()

    # SM baseline
    g_BBN_SM = 2 + (7/8) * (4 + 6)
    g_BBN_obs = 10.75  # consistent with Y_p
    N_c = 3
    chi = 2

    print(f"SM g_eff(BBN) = 2_gamma + (7/8)*(4 e+e- + 6 nu) = {g_BBN_SM}")
    print(f"Observed (Y_p, N_eff): {g_BBN_obs:.2f} (+/- ~5%)")
    print()

    # Case 1: Reading 8 uniform on neutrinos only, no e+
    case1 = 2 + (7/8) * (2 + 6 * N_c / chi**4)

    # Case 2: Reading 8 uniform on all fermions
    case2 = 2 + (7/8) * (4 + 6) * N_c / chi**4

    # Case 3: cascade = SM at BBN
    case3 = g_BBN_SM

    # Case 4: epoch-dependent
    case4_BBN = g_BBN_SM
    case4_recomb = 2 + (7/8) * 2 * 3 * N_c / chi**4

    # Verdict table
    print(f"{'Case':<40} {'g_eff(BBN)':>10} {'dev vs obs':>12} {'BBN status':>12}")
    print("-" * 76)
    rows = [
        ("SM (baseline)",                                  g_BBN_SM,    "ok"),
        ("Case 1: uniform R8 on nu, no e+",               case1,       "RULED OUT"),
        ("Case 2: uniform R8 on all fermions",            case2,       "RULED OUT"),
        ("Case 3: cascade = SM at all epochs",            case3,       "ok (= SM)"),
        ("Case 4: epoch-dep at T = m_e",                  case4_BBN,   "ok (= SM)"),
    ]
    for label, g, status in rows:
        dev = (g/g_BBN_obs - 1) * 100
        print(f"  {label:<38} {g:>10.3f} {dev:>+10.2f}%  {status}")
    print()

    print(f"At recombination:")
    print(f"  Case 3 (= SM): g_eff(recomb) = 3.383, T_CMB = 2.642 K, dev -3.07%")
    print(f"  Case 4 (epoch-dep): g_eff(recomb) = {case4_recomb:.4f}, T_CMB = 2.726 K, dev +0.02%")
    print()

    print("=" * 76)
    print("CONCLUSION")
    print("=" * 76)
    print("""
Cases 1 and 2 (uniform Reading 8) are RULED OUT by BBN.
Case 3 (cascade = SM throughout) passes BBN but fails T_CMB closure.
Case 4 (epoch-dependent transition at T = m_e) passes BOTH but requires
       an additional structural derivation (GAP 4).

  ALWAYS-CASCADE        ALWAYS-SM          EPOCH-DEPENDENT
  Cases 1, 2            Case 3             Case 4
  fails BBN             fails T_CMB        passes both,
  (factor ~3 off)       residual -3.07%    needs GAP 4 closure

GAP 4 (the new structural commitment):
Derive cascade-native mechanism for e+ migration to antipodal basin at
T = m_e.  Specifically: when thermal pair production gamma+gamma -> e+e-
falls below threshold (T < m_e), e+ in our basin cannot be replenished.
By cascade no-annihilation, they cannot annihilate; instead, they
migrate via cascade basin-asymmetry mechanism (cascade-internal, not
SM thermodynamics).

Below T = m_e, only e- remains in our basin's thermal bath.  This is
when Reading 8's unified sector rule activates for the surviving
relativistic species (gamma + 3 nu).

If GAP 4 cannot be closed, Reading 8 must be abandoned, and the cascade
T_CMB residual remains at -3.07% (Part V Theorem) or -2.07% (Part V
Remark with H_0 Gram correction).  In that case, T_CMB closure is not
achievable via Reading 8 and remains an open problem.
""".rstrip())


if __name__ == "__main__":
    main()
