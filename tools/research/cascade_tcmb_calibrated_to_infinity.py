#!/usr/bin/env python3
"""
T_CMB calibrated to infinity: numerical exploration of cascade T_CMB
closure under the refined "cascade extends to d=infty" ontology.

CONTEXT
=======
Part V Theorem (CMB temperature) gives leading prediction
    T_CMB = (90 * Omega_r * M_Pl_red^2 * H_0^2 / (pi^2 * g_eff))^(1/4)
         = 2.642 K
against observed 2.7255 K (COBE/FIRAS) -- residual -3.07%.

Part V Remark notes T_CMB is descent-dependent through H_0 (T_CMB ~ sqrt(H_0)).
Applying the Part 0 first-order Gram correction to H_0 brings T_CMB to ~2.669 K,
residual -2.1%.  The remark explicitly flags closing the last few percent as
"an open problem" requiring either a second-order Gram term or a cascade-intrinsic
g_eff counting rule.

ROADMAP Item 11 (cascade_uv_convergence.py) clarified that d=217 is the deepest
distinguished Gamma-critical LANDMARK, not a fundamental terminus.  The cascade
extends to d=infty with progressively suppressed contributions.  This raises
the question: when an observable is NOT calibrated at a specific landmark,
should its Gram path-sum extend to d=infty rather than truncating at d=217?

The cosmological constant IS calibrated at d=217 (so its Gram path correctly
truncates there).  T_CMB is NOT calibrated at any specific landmark -- it's
derived from a thermodynamic relation involving Omega_r, M_Pl_red, H_0, g_eff.
This raises five candidate readings of "T_CMB calibrated to infinity":

  Reading 1: extend delta_path(5, 217) -> delta_path(5, infty) in the CC chain
             only, propagating through H_0 to T_CMB.  This is structurally wrong
             (CC is calibrated at 217) but tested for completeness.
  Reading 2: T_CMB picks up its OWN Gram correction with delta_path(5, infty)
             applied directly (not through H_0).  Most literal reading of
             "T_CMB calibrated to infinity."
  Reading 3: power-law variants of Reading 2 (T_CMB ~ H_0^(1/2) suggests
             possibly a 3/2 power somewhere; testing exponent values).
  Reading 4: cascade-intrinsic g_eff = N_c = 3 plus Reading 2.
  Reading 5: cascade-intrinsic g_eff = N_c = 3 alone (no Gram extension).

WHAT THIS VERIFIER DOES
=======================
Computes all five readings from cascade primitives and reports the residual
against PDG T_CMB = 2.7255 K.  This is an EXPLORATORY probe of T_CMB closure
under the refined ontology, not a structural derivation.  Any reading that
closes within standing precision is a candidate for promotion to a structural
derivation; any reading that fails to close stays in the open-questions list.

NO CHANGE TO COMMITTED CASCADE PREDICTIONS.  The leading T_CMB = 2.642 K
prediction stands; the Gram-corrected ~2.669 K stands.  This script only
documents the new candidate readings unlocked by ROADMAP Item 11's
"cascade extends to d=infty" clarification.
"""

from __future__ import annotations

import math
import os
import sys
from dataclasses import dataclass

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)
sys.path.insert(0, os.path.join(TOOLS_DIR, "research"))

from cascade_gram_bott_tower import gram_C2, gram_path_sum  # noqa: E402


def delta_path(d_min: int, d_max: int) -> float:
    return gram_path_sum(d_min, d_max)


def delta_path_to_infinity(d_min: int, tol: float = 1e-15, hard_cap: int = 200_000) -> float:
    """Sum 1 - C^2_{d, d+1} from d_min until residual layer < tol."""
    s = 0.0
    for d in range(d_min, hard_cap):
        term = 1.0 - gram_C2(d)
        s += term
        if d > d_min + 100 and term < tol:
            break
    return s


@dataclass
class Reading:
    label: str
    T_CMB: float
    note: str


def main() -> None:
    print("=" * 72)
    print("T_CMB calibrated to infinity")
    print("ROADMAP Item 11 follow-up: numerical exploration only")
    print("=" * 72)

    T_obs = 2.7255  # PDG / COBE-FIRAS
    T_leading = 2.642  # Part V Theorem leading prediction
    T_gram_217 = 2.669  # Part V Remark: H_0 Gram correction propagated to T_CMB
    g_eff_SM = 3.383  # Part V: photons + N_eff = 3.044 neutrinos with (4/11)^(4/3) factor
    N_c = 3  # cascade colour count

    delta_217 = delta_path(5, 217)
    delta_inf = delta_path_to_infinity(5)

    print()
    print(f"  delta_path(5, 217)  = {delta_217:.6f}")
    print(f"  delta_path(5, inf)  = {delta_inf:.6f}")
    print(f"  ratio (inf/217)     = {delta_inf / delta_217:.4f}  (+{(delta_inf/delta_217-1)*100:.2f}% beyond 217)")
    print()
    print(f"  observed T_CMB        = {T_obs:.4f} K (PDG)")
    print(f"  leading cascade T_CMB = {T_leading:.4f} K  (residual {100*(T_leading/T_obs-1):+.2f}%)")
    print(f"  Gram(5,217) on H_0    = {T_gram_217:.4f} K  (residual {100*(T_gram_217/T_obs-1):+.2f}%)")
    print()

    readings = []

    # READING 1: extend delta_path -> infinity in the CC -> H_0 -> T_CMB chain.
    # Structurally wrong (CC is calibrated at 217), included for completeness.
    # T_CMB ~ sqrt(H_0); H_0 picks up factor exp(delta_path) to leading; the
    # *additional* shift from extending Gram from 217 to infty is exp((delta_inf - delta_217)/2).
    extra_from_inf = math.exp(0.5 * (delta_inf - delta_217))
    T1 = T_gram_217 * extra_from_inf
    readings.append(Reading(
        "Reading 1: extend Gram path 217 -> infty in CC chain",
        T1,
        "structurally wrong (CC is at d=217); included for completeness",
    ))

    # READING 2: T_CMB picks up its own Gram correction with delta_path(5, infty)
    # applied DIRECTLY (multiplicative exp(delta_inf), not through sqrt(H_0)).
    # Most literal reading of "T_CMB calibrated to infinity."
    T2 = T_leading * math.exp(delta_inf)
    readings.append(Reading(
        "Reading 2: T_CMB picks up its own delta_path(5, infty) directly",
        T2,
        "most literal reading; substantial closure -3.07% -> -0.94%",
    ))

    # READING 3a: alternative power exponents.  T_CMB ~ rho_r^(1/4); rho_r ~ H_0^2;
    # so T_CMB ~ H_0^(1/2).  If H_0 carries Gram correction exp(delta), T_CMB
    # naturally carries exp(delta/2) -- but Reading 2 used exp(delta) directly.
    # Test other exponents to see what closes.
    for power in (0.5, 1.0, 1.5, 2.0):
        Tp = T_leading * math.exp(power * delta_inf)
        readings.append(Reading(
            f"Reading 3 (power={power}): T_leading * exp({power}*delta_inf)",
            Tp,
            "phenomenological power-law scan",
        ))

    # READING 4: cascade-intrinsic g_eff = N_c = 3 instead of SM g_eff = 3.383.
    # Plus delta_path(5, infty) Gram correction.
    # T_CMB scales as g_eff^(-1/4): T_new/T_old = (g_eff_old / g_eff_new)^(1/4).
    T_geff_only = T_leading * (g_eff_SM / N_c) ** 0.25
    T4 = T_geff_only * math.exp(delta_inf)
    readings.append(Reading(
        "Reading 4: g_eff = N_c = 3 PLUS delta_path(5, infty)",
        T4,
        "cascade-intrinsic g_eff combined with Gram extension",
    ))

    # READING 5: cascade-intrinsic g_eff = N_c = 3 alone (no Gram extension).
    readings.append(Reading(
        "Reading 5: g_eff = N_c = 3 alone (no Gram extension)",
        T_geff_only,
        "purely structural g_eff substitution",
    ))

    # READING 6: cascade-native NO-ANNIHILATION counting.
    # Cascade has CPT-conjugate basins at d=4 (Part IVb thm:chirality-factorisation).
    # e+e- never annihilate in our basin (antimatter is in the antipodal basin,
    # causally disconnected).  The SM (4/11)^(4/3) post-annihilation entropy
    # factor is therefore an SM artifact, not a cascade quantity.
    # Cascade-native counting: photons and neutrinos stay at same T throughout.
    # g_eff_cascade = 2 (photons) + (7/8) * d.o.f./species * N_eff
    N_eff_SM = 3.044
    g_full = 2 + (7/8) * 2 * N_eff_SM  # full Dirac (2 d.o.f. per species)
    T6 = T_leading * (g_eff_SM / g_full) ** 0.25
    readings.append(Reading(
        "Reading 6: cascade no-annihilation, neutrinos full 2 d.o.f.",
        T6,
        "drops (4/11)^(4/3) -- structurally correct but pushes T_CMB MUCH worse",
    ))

    # READING 7: cascade no-annihilation + basin halving (1 d.o.f./species).
    g_half = 2 + (7/8) * 1 * N_eff_SM  # one helicity per species
    T7 = T_leading * (g_eff_SM / g_half) ** 0.25
    readings.append(Reading(
        "Reading 7: cascade no-annihilation + basin halving (1 d.o.f.)",
        T7,
        "antineutrinos in antipodal basin only -- still pushes T_CMB worse",
    ))

    # READING 8: cascade-native no-annihilation + structural T_nu/T_gamma ratio.
    # The required T_nu/T_gamma = (3/16)^(1/4) = (N_c/chi^4)^(1/4) = 0.6585.
    # If the cascade structurally suppresses neutrino temperature by this
    # specific ratio, T_CMB closes within 0.3%.
    # 3/16 = N_c / chi^4 is built from cascade primitives:
    #   N_c = 3 (colour count, Adams' theorem at d=12)
    #   chi^4 = 16 (Euler characteristic of S^4 to the fourth power)
    # The k=4 channel-count corresponds to "2 Bott periods spanned" in the
    # Part IVb correction-family conventions, suggestive of a multi-generation
    # neutrino-photon coupling path traversing both d=13 (Gen 2) and d=21 (Gen 1)
    # boundaries from the photon's d=14 layer.  No derivation yet -- this is
    # numerology with structural hints.
    f4_form = N_c / 16  # = 3/16, leading-order match to ~0.3%
    g_struct = 2 + (7/8) * 2 * 3 * f4_form  # N_eff = 3 (cascade exact)
    T8 = T_leading * (g_eff_SM / g_struct) ** 0.25
    readings.append(Reading(
        "Reading 8: cascade no-annihilation + f^4 = N_c/chi^4 = 3/16",
        T8,
        "structural form (N_c, chi from Part 0/IVa); no derivation yet",
    ))

    # Target g_eff for closure
    target_g = g_eff_SM / (T_obs / T_leading) ** 4
    target_f4 = (target_g - 2) / ((7/8) * 2 * N_eff_SM)
    target_f = target_f4 ** 0.25

    # Print results
    print("-" * 72)
    print("CANDIDATE READINGS")
    print("-" * 72)
    print()
    for r in readings:
        residual_pct = 100.0 * (r.T_CMB / T_obs - 1.0)
        marker = ""
        if abs(residual_pct) < 0.5:
            marker = "  [WITHIN 0.5%]"
        elif abs(residual_pct) < 1.0:
            marker = "  [within 1%]"
        print(f"  {r.label}")
        print(f"    T_CMB = {r.T_CMB:.4f} K   residual {residual_pct:+.3f}%{marker}")
        print(f"    note: {r.note}")
        print()

    # Summary table
    print("-" * 72)
    print("SUMMARY")
    print("-" * 72)
    print()
    # Indexing: readings = [R1, R2, R3-p0.5, R3-p1, R3-p1.5, R3-p2, R4, R5, R6, R7, R8]
    rows = [
        ("Cascade leading (Part V Theorem)",         T_leading),
        ("Cascade Gram on H_0 (delta_path(5,217))",  T_gram_217),
        ("Reading 1: extend delta_path 217->infty",  readings[0].T_CMB),
        ("Reading 2: direct delta_path(5,infty)",    readings[1].T_CMB),
        ("Reading 3c: power=1.5",                    readings[4].T_CMB),
        ("Reading 4: g_eff = N_c + delta_inf",       readings[6].T_CMB),
        ("Reading 5: g_eff = N_c = 3",               readings[7].T_CMB),
        ("Reading 6: cascade no-annihilation 2dof",  readings[8].T_CMB),
        ("Reading 7: cascade no-annihilation 1dof",  readings[9].T_CMB),
        ("Reading 8: f^4 = N_c/chi^4 = 3/16",        readings[10].T_CMB),
        ("Observed (PDG / COBE-FIRAS)",              T_obs),
    ]
    print(f"  {'reading':<48} {'T_CMB (K)':>10}  {'residual':>10}")
    for label, T in rows:
        print(f"  {label:<48} {T:>10.4f}  {100*(T/T_obs-1):>+9.3f}%")

    print()
    print("-" * 72)
    print("TARGET ANALYSIS (cascade-native closure target)")
    print("-" * 72)
    print()
    print(f"  Required g_eff for T_CMB = {T_obs} K exactly: {target_g:.4f}")
    print(f"    -- close to N_c = 3 (Reading 5's coincidence)")
    print(f"  Required T_nu/T_gamma at recomb (cascade-native): f = {target_f:.4f}")
    print(f"    SM (4/11)^(1/3) = {(4/11)**(1/3):.4f}, (4/11)^(4/3) = {(4/11)**(4/3):.4f}")
    print(f"  Required f^4 = {target_f4:.4f}")
    print(f"    Cascade quantities tested:")
    print(f"      N_c/16   = {3/16:.4f}    <-- closest match (off by 0.3%)")
    print(f"      1/N_c^2  = {1/9:.4f}")
    print(f"      1/(2*N_c)= {1/6:.4f}")
    print()
    print()
    print("STRUCTURAL READING: f^4 = N_c / chi^4 = 3/16")
    print("  N_c = 3 (colour count, Adams' theorem at d=12)")
    print("  chi = 2 (Euler characteristic of S^4)")
    print("  k=4 in Part IVb's channel-count convention = 2 Bott periods spanned")
    print()
    print("  Closure precision under cascade-native no-annihilation (Reading 8):")
    print(f"    g_eff = 2 + (7/8)(2)(N_eff=3)(3/16) = {2 + 7/8*2*3*3/16:.4f}")
    print(f"    T_CMB = {T_leading * (g_eff_SM/(2+7/8*2*3*3/16))**0.25:.4f} K")
    print(f"    dev   = {(T_leading*(g_eff_SM/(2+7/8*2*3*3/16))**0.25/T_obs - 1)*100:+.3f}%")
    print()
    print("  IMPORTANT: precision sensitivity to T_leading rounding.")
    print("    T_leading = 2.642 K (Part V published, 4 sig figs):")
    print("      f^4 = 3/16 matches target to -0.27% (robust)")
    print("    Higher-precision forms like N_c*R(12)^2/chi^12 = 0.18804")
    print("      give apparent 0.014% match but are sensitive to T_leading.")
    print("    The robust claim is: f^4 ~ N_c/chi^4 at standing precision.")

    # Interpretation guard rails
    print()
    print("=" * 72)
    print("INTERPRETATION")
    print("=" * 72)
    print("""
This script is EXPLORATORY.  It documents the candidate T_CMB readings unlocked
by ROADMAP Item 11's clarification that the cascade extends to d=infty.  None
of these readings is yet structurally derived from cascade primitives:

 - Reading 1 is structurally WRONG: the CC is calibrated at d=217 and its Gram
   path must not be extended to infty.  Rejected.
 - Reading 2 has the right form (T_CMB applies its own Gram correction at
   d=infty) but lacks a structural argument for why the Gram correction enters
   T_CMB linearly via exp(delta_inf) rather than through sqrt(H_0).  Open.
 - Reading 3 is a phenomenological power-law scan.  Power=3/2 closes to within
   standing cascade precision but has no structural justification.  Rejected
   as numerology absent a derivation.
 - Reading 4 combines a cascade-intrinsic g_eff = N_c = 3 with Gram extension.
   Cascade-internally motivated (N_c is forced by Part IVa) but g_eff = N_c
   ignores photon polarisation and the (4/11)^(4/3) neutrino entropy factor;
   needs structural argument.  Open.
 - Reading 5 is the cleanest single-mechanism candidate NUMERICALLY: replace
   SM g_eff with cascade N_c = 3.  Closes -3.07% to -0.11% (within standing
   cascade precision).
   STRUCTURAL CAVEAT (added after basin/no-annihilation re-examination, see
   addendum below): the cascade-native logic of "no annihilation, basins at
   d=4" pushes g_eff in the OPPOSITE direction (~7, not 3).  Reading 5's
   numerical near-closure is therefore most likely a coincidence rather than
   a structural result.

ADDENDUM: BASIN / NO-ANNIHILATION RE-EXAMINATION
==================================================
The cascade has CPT-conjugate basins at d=4 (Part IVb thm:chirality-factorisation).
e+e- never annihilate in our basin: e+ are in the antipodal basin, causally
disconnected.  This means the SM (4/11)^(4/3) post-annihilation entropy factor
in g_eff = 2 + (7/8)*2*N_eff*(4/11)^(4/3) = 3.383 is structurally an SM
artifact, not a cascade quantity.

Cascade-native counting (no annihilation, photons and neutrinos at same T):
  g_eff_cascade = 2 + (7/8) * d.o.f._per_nu * N_eff
where d.o.f._per_nu = 2 (full Dirac) or 1 (one helicity if antineutrinos in
antipodal basin only).  Both give g_eff in the range 4.6 to 7.3, NOT 3.
This pushes T_CMB to 2.18-2.44 K (residual -10% to -20%).

Cascade neutrino masses (CLAUDE.md): m_3=0.0493, m_2=3e-4, m_1=3e-6 eV.
At recombination (T_gamma = 0.26 eV), all three are relativistic
(m/T < 0.2).  Non-relativistic-transition lever is NOT available.

Source mass m_29 = 543 eV is non-relativistic at recombination but is the
SOURCE, not the propagated physical mass.  Treating it as the radiation-
contributing mass would give g_eff = 2 (only photons), T = 3.01 K (+10.5%).

TARGET ANALYSIS
===============
For T_CMB = 2.7255 K exactly:
  required g_eff = 2.987 (very close to N_c = 3)
  required T_nu/T_gamma at recomb: f = 0.6585  (SM gives 0.7138)
  required f^4 = 0.1880

Striking near-match: N_c / 16 = 3/16 = 0.1875 (off by 0.3%).
Suggestive but no derivation yet.  Other cascade quantities tested (1/N_c^2,
1/(2 N_c), alpha_em^(1/2), etc.) do not match closely.

CONCLUSION: cascade-native logic (no annihilation, basin separation) does
NOT close T_CMB; it makes T_CMB worse.  Reading 5 (g_eff = N_c = 3) is most
likely a numerical coincidence at the -0.11% level.  A genuine cascade-native
closure would require either:
  (a) A cascade-derived T_nu/T_gamma ratio at recomb such that f^4 ~ 0.188
      (the N_c/16 candidate is suggestive but unjustified).
  (b) A cascade-native bridge formula from Omega_r = 1/(4*pi^7) to T_CMB
      that bypasses the SM thermodynamic g_eff entirely.  Part V's Omega_r
      derivation explicitly avoids "photons, thermal equilibrium, or
      particle physics" -- only the bridge to T introduces those concepts.
      A cascade-native bridge would close T_CMB structurally without any
      g_eff parameter.

The original four readings stand as exploratory; the additional finding is
that Reading 5 should be DEMOTED from "cleanest candidate" to "numerical
coincidence pending alternative bridge formula."
""".rstrip())


if __name__ == "__main__":
    main()
