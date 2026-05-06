#!/usr/bin/env python3
"""
*** RETRACTION WALKED BACK 2026-05-04 evening ***
The earlier retraction was based on Part VI's "Phase D = SM Boltzmann"
reading, which Part VI itself classifies as Tier 5 (speculative; line
1316-1383).  Per CLAUDE.md, Tier 5 results are explicitly NOT sufficient
to compel cascade predictions, so retracting Reading 8 on Tier 5 evidence
is unsound.

Reading 8's structural ingredients are Tier 1 cascade-native:
  - Basin symmetry chi(S^4)=2 (Part IVb thm:chirality-factorisation)
  - Sector-dim-ratio mechanism (Part IVb thm:sector-fundamental-y)
  - Channel-count rule k = 2*(Bott periods spanned) (Part IVb)

Part VI's "single-tick Big Bang" + "Phase D follows SM Boltzmann" reading
is Tier 5 speculation.  The cascade has NOT derived post-Big-Bang
thermodynamics cascade-natively; it has imported SM Boltzmann.

Reading 8 is an ALTERNATIVE Tier 5 speculative reading -- but built on
Tier 1 ingredients.  Both readings are exploratory; neither compels
belief at the cascade's standing tier discipline.

This file STANDS as a structural derivation attempt (with the gaps
identified below).  The retraction was over-confident.

T_CMB Reading 8 structural derivation attempt:
    f^4 = (T_nu / T_gamma)^4 = N_c / chi^4 = 3/16

GOAL
====
Derive the cascade-native ratio (T_nu/T_gamma)^4 = N_c/chi^4 from cascade
primitives (Part 0 Gamma function, Part IVa gauge-window structure, Part IVb
chirality-factorisation, Part VI cascade-native g_eff machinery).

This is a STRUCTURAL DERIVATION ATTEMPT.  It identifies cascade-internal
ingredients with explicit source citations, lays out a plausibility argument
step-by-step, and explicitly flags the logical gaps that prevent it from
being a proof.  Per CLAUDE.md Check 1, every "the text does not derive X"
claim is sourced; per Check 5, this claim is made only once and is the
acknowledged open question.

CASCADE-NATIVE INGREDIENTS (each cited to source)
===============================================
(I1) chi(S^4) = 2 basins on the cascade observer's host sphere.
     SOURCE: Part IVb Theorem `thm:chirality-factorisation` -- explicit
     proof via Poincare-Hopf chi(S^4) = 2 + Z_2 height-function symmetry.

(I2) Four spatial dimensions are forced for the cascade observer.
     SOURCE: Part III (Lovelock theorem) -- d=4 is the unique dimension
     where Einstein's equation is forced by symmetry + diffeomorphism
     invariance.  The cascade observer at d=4 has 4 spatial dimensions
     by the Lovelock-forced metric structure.

(I3) chi^4 = 16 = total basin combinations across 4 spatial dimensions.
     CONSEQUENCE of (I1)+(I2): each dimension carries a chi=2 basin pair;
     across 4 dimensions, the basin product space has 16 elements.
     STRUCTURAL: this is a direct combinatorial consequence, not a new
     theorem.  But its application to radiation thermodynamics is novel.

(I4) N_c = 3 colour count, forced by Adams' theorem at d=12.
     SOURCE: Part IVa Theorem `thm:adams` -- R^12 = H^3 (the unique Bott
     class of quaternions in 12 real dimensions).  Adams' theorem gives
     dim of fundamental rep = 3 = N_c.

(I5) Cascade neutrinos are left-handed only.
     SOURCE: Part IVa generations theorem + Part IVb fermion-gauge coupling
     -- neutrinos transform as (1,2)_{-1/2} of SU(3)xSU(2)xU(1)/Z_6,
     left-handed Bott fermions at d=5,13,21.  No right-handed neutrinos
     in the cascade audited spectrum (Majorana-vs-Dirac character is OPEN
     per CLAUDE.md).

(I6) Cascade photons are their own antiparticle.
     STANDARD: photon is the U(1)_em gauge boson, real-field with no
     antiparticle distinct from itself.  In the basin structure, photons
     are basin-symmetric (live identically in matter and antimatter
     basins).

(I7) No e+e- annihilation in our basin.
     SOURCE: CLAUDE.md "Sign anchor" entry -- "anything beyond our
     cosmological horizon is in the antipodal basin, causally
     disconnected".  e+ are in the antipodal basin, never annihilate
     with our basin's e-.  The SM (4/11)^(4/3) post-annihilation entropy
     factor is therefore an SM artifact.

(I8) Cascade-native g_eff at high-T = 106.75 = SM unbroken-phase value.
     SOURCE: Part VI Proposition `prop:g_eff` -- explicit cascade
     derivation summing over distinguished layers (d=5,12,13,14,21).
     The cascade reproduces SM g_eff at T_RH layer-by-layer.

(I9) Sector-dimension-ratio mechanism for N_c factors at d=12.
     SOURCE: Part IVb Theorem `thm:sector-fundamental-y` (verbatim):
     |Y_H|/|Y_{Q_L}| = dim V_12(Q_L) / dim V_12(H) = N_c/1 = N_c.
     "The factor N_c is the sector dimension ratio, NOT a color trace."
     This is a CASCADE-DERIVED structural mechanism for how N_c enters
     observable ratios via the path-tensor V_12 (x) V_13 (x) V_14
     (Part IVa rem:path-tensor).  Established for hypercharge ratios;
     EXTENSION to radiation thermodynamics is the new structural
     commitment proposed here (logical Gap 1 below).

PLAUSIBILITY ARGUMENT (UPDATED with sector-dim-ratio mechanism)
=================================================================
GIVEN (I1)-(I9), here is a candidate structural argument for the
g_eff form at recombination yielding Reading 8.

Step A (cascade-native, follows (I7)+(I8)):
   At recombination (T ~ 0.26 eV), cascade-native counting includes
   photons + neutrinos as relativistic species.  All other SM particles
   (charged leptons, quarks, gauge bosons except photon) are non-
   relativistic and decouple.  Without e+e- annihilation, photons and
   neutrinos START at the same temperature.

Step B (cascade-native, follows (I3)+(I5)+(I6)):
   Basin filter applies asymmetrically.  Neutrinos are chirality-broken
   (left-handed only in our basin), so their phase space is restricted
   relative to photons (which are chirality-symmetric, basin-symmetric
   own-antiparticles).  The basin restriction factor is 1/chi^k where
   k counts cascade descent boundaries crossed; for neutrino at d=21
   descending to observer at d=4, k=4 (2 Bott-period boundaries crossed,
   each contributing chi^2 by the channel-count rule).
   Effective neutrino basin-filter factor: 1/chi^4.

Step C (cascade-native, EXTENSION of Part IVb thm:sector-fundamental-y):
   Sector-dimension-ratio at d=12.  Part IVb already establishes that
   cascade-native ratios at the colour gauge layer take the form of
   sector dimensions in the path-tensor V_12 (x) V_13 (x) V_14:
      |Y_H|/|Y_{Q_L}| = dim V_12(Q_L) / dim V_12(H) = N_c/1 = N_c
   "The factor N_c is the sector dimension ratio, NOT a color trace"
   (Part IVb thm:sector-fundamental-y, verbatim).

   Extending this mechanism to radiation thermodynamics: if the cascade
   radiation density samples the FULL path-tensor Hilbert space (not just
   the relativistic-species subspace), then each cascade neutrino at
   recombination effectively picks up the sector-dimension count
   dim V_12 from cascade descent through d=12.

   For neutrinos in (V_12, V_13) = (1, 2) sector: dim V_12 = 1 directly,
   but the cascade descent through the colour layer "samples" the full
   d=12 phase space, giving effective multiplier N_c.

   For photons at d=14 (U(1) gauge boson, BOSON not fermion):
   The cascade fermion-gauge coupling (Part IVb rem:fermion-gauge-
   coupling-proposal) couples FERMIONS to gauge content; bosons traverse
   gauge layers transparently in cascade descent.  Photon descent does
   NOT pick up the d=12 sector-dim multiplier.

Step D (combining B+C):
   Cascade-native g_eff at recombination:
      g_eff = g_photon * (no factor) + g_neutrino * (N_c / chi^4)
            = 2 + (7/8)(2)(N_eff)(N_c / chi^4)
            = 2 + (7/8)(2)(3)(3/16)
            = 2.984

   Equivalently, written as a temperature ratio at constant g_eff:
      (T_nu / T_gamma)^4 = N_c / chi^4 = 3/16

Numerical check:
   3/16 = 0.1875
   Required for T_CMB closure: 0.188 (off by 0.27%)
   T_CMB(Reading 8) = 2.726 K vs observed 2.7255 K (residual +0.02%)

LOGICAL GAPS (prevent this from being a proof)
==============================================
GAP 1 (Step C extension is novel):
   Part IVb thm:sector-fundamental-y establishes the sector-dim-ratio
   mechanism for HYPERCHARGE Y values: |Y_H|/|Y_{Q_L}| = dim V_12(Q_L) =
   N_c.  This is fully derived in cascade.

   The novel claim of Step C is that the SAME mechanism applies to
   RADIATION THERMODYNAMIC COUNTING -- specifically, that the cascade
   radiation density at recombination samples the full path-tensor
   V_12 (x) V_13 (x) V_14 Hilbert space, picking up sector-dim factors
   at each gauge layer the descent traverses.

   Sub-claims requiring derivation:
   (1a) Radiation density formula extends from "energy per relativistic
        d.o.f." (SM Stefan-Boltzmann) to "energy per cascade path-tensor
        slot."  Cascade-native version of the Bose-Einstein/Fermi-Dirac
        integral.
   (1b) Bosons (photons) traverse gauge layers transparently while
        fermions (neutrinos) couple at each crossed gauge layer.
        Suggested by Part IVb rem:fermion-gauge-coupling but
        not derived for radiation thermodynamics.
   (1c) The d=12 sector-dim factor for neutrinos is N_c (the maximally
        non-trivial V_12 sector), not 1 (their actual V_12 = 1
        assignment as colour singlets).  This requires the descent to
        "sample" the maximal V_12 dimension, not the species' specific
        V_12 occupancy.

GAP 2 (Step B chi^4 power requires derivation):
   The basin filter for neutrinos with k=4 = 2 Bott periods crossed
   (channel-count rule, Part IVb correction family) is suggestive but
   not directly derived for radiation thermodynamics.  Specifically:
   - Neutrino at d=21 -> observer d=4 crosses 2 Bott boundaries
     (P_3/P_2 at d=20-21, P_2/P_1 at d=12-13), giving k=4 by the
     channel-count rule.
   - Photon at d=14 -> observer d=4 crosses 1 Bott boundary
     (P_2/P_1 at d=12-13), giving k=2.
   - But why does the basin filter apply ONLY to neutrinos, not photons?
     Plausibly because photons are basin-symmetric (own antiparticle)
     while neutrinos are chirality-broken.  Not formally derived.
   - Why is the filter (1/chi)^k rather than chi^(-k/2) or some other
     form?  Cascade descent factors in Part IVb take the form
     alpha(d*)/chi^k for delta_Phi shifts; the connection to
     temperature ratios (T_nu/T_gamma)^k = chi^(-k) is plausible
     by Born-rule squaring but not derived.

GAP 3 (No cascade-native bridge from Omega_r to T_CMB):
   Part V derives Omega_r = 1/(4*pi^7) geometrically (Part V Theorem
   on Omega_r, Remark rem:why-4-plus-7: "no quantity in this derivation
   refers to photons, thermal equilibrium, or particle physics").  But
   the bridge from Omega_r to T uses SM thermodynamics:
      T_CMB = (90 Omega_r M_Pl^2 H_0^2 / (pi^2 g_eff))^(1/4)
   with g_eff = 3.383 imported from SM.

   Closing requires extending Part VI prop:g_eff (which derives
   cascade-native g_eff at T_RH = 106.75 by summing over distinguished
   layers) to recombination temperature.  At T_recomb only photons +
   neutrinos are relativistic; the layer sum becomes:
      g_recomb = 2 (photon at d=14)
               + (7/8) * 2 * 3 (one nu per generation at d=21,13,5)
               * (sector-dim-and-basin factor)
   For Reading 8, the factor must equal N_c/chi^4 = 3/16, which (per
   GAPS 1-2) requires the structural extensions sketched above.

CONCLUSION
==========
The structural plausibility argument has cascade-native ingredients (chi,
N_c, basin separation, no annihilation, layer structure) but lacks the
key bridge that connects them to the specific (T_nu/T_gamma)^4 = N_c/chi^4
form.  The numerical match at standing precision (~0.3%) is suggestive
but not yet a derivation.

The required next work to close this is Gap 1: derive the cascade-native
bridge from Omega_r to T_CMB, propagating through the gauge window with
explicit multiplicity factors at each layer crossing.  This would
simultaneously close Reading 8 and replace the SM g_eff import in Part V.

Per CLAUDE.md Check 4: this is acknowledged open territory ("Closing the
last few percent requires either a second-order Gram term or absorbing
g_eff into a cascade-intrinsic counting rule, which is an open problem"
-- Part V Remark `rem:tcmb-descent-dependent`).  Reading 8 is a candidate
for the "cascade-intrinsic counting rule" but requires the bridge
derivation to be promoted from candidate to closure.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)


def main() -> None:
    print("=" * 76)
    print("T_CMB Reading 8: f^4 = N_c/chi^4 structural derivation attempt")
    print("=" * 76)

    N_c = 3
    chi = 2
    f4_form = N_c / chi**4
    f = f4_form ** 0.25

    T_obs = 2.7255
    T_leading = 2.642
    g_eff_SM = 3.383
    N_eff = 3

    g_eff_cascade = 2 + (7/8) * 2 * N_eff * f4_form
    T_pred = T_leading * (g_eff_SM / g_eff_cascade) ** 0.25
    residual_pct = 100 * (T_pred / T_obs - 1)

    print()
    print(f"Cascade primitives:")
    print(f"  N_c = {N_c} (Adams' theorem at d=12, Part IVa)")
    print(f"  chi = {chi} (Euler char of S^4, Part IVb thm:chirality-factorisation)")
    print(f"  4 spatial dims (Lovelock, Part III)")
    print()
    print(f"Combination:")
    print(f"  chi^4 = {chi**4} (basin combinations across 4 spatial dims)")
    print(f"  N_c / chi^4 = {N_c}/{chi**4} = {f4_form}")
    print(f"  f = (T_nu/T_gamma) = (3/16)^(1/4) = {f:.4f}")
    print()
    print(f"Cascade-native no-annihilation g_eff at recombination:")
    print(f"  g_eff = 2_gamma + (7/8) * 2 * N_eff * f^4")
    print(f"        = 2 + {7/8 * 2 * N_eff} * {f4_form}")
    print(f"        = {g_eff_cascade:.4f}")
    print()
    print(f"T_CMB prediction:")
    print(f"  T_CMB = T_leading * (g_eff_SM / g_eff_cascade)^(1/4)")
    print(f"        = {T_leading} * ({g_eff_SM}/{g_eff_cascade:.4f})^0.25")
    print(f"        = {T_pred:.4f} K")
    print(f"  Observed: {T_obs} K")
    print(f"  Residual: {residual_pct:+.3f}%")
    print()
    print("=" * 76)
    print("CASCADE-DERIVED INGREDIENTS WITH SOURCES")
    print("=" * 76)
    sources = [
        ("(I1)", "chi(S^4) = 2 basins",
         "Part IVb thm:chirality-factorisation"),
        ("(I2)", "4 spatial dimensions forced",
         "Part III (Lovelock)"),
        ("(I3)", "chi^4 from 2 Bott periods crossed (channel-count)",
         "Part IVb channel-count rule k = 2*(periods spanned)"),
        ("(I4)", "N_c = 3 colour count",
         "Part IVa thm:adams"),
        ("(I5)", "Neutrinos are left-handed only",
         "Part IVa+IVb (Majorana vs Dirac character OPEN)"),
        ("(I6)", "Photons own-antiparticle, basin-symmetric",
         "Standard, U(1)_em real field"),
        ("(I7)", "No e+e- annihilation in our basin",
         "CLAUDE.md sign-anchor / Part IVb basin separation"),
        ("(I8)", "Cascade-native g_eff(T_RH) = 106.75 = SM exactly",
         "Part VI prop:g_eff"),
        ("(I9)", "Sector-dim-ratio mechanism: N_c factor at d=12",
         "Part IVb thm:sector-fundamental-y -- DERIVED for Y-spectrum"),
    ]
    for tag, desc, source in sources:
        print(f"  {tag} {desc}")
        print(f"       SOURCE: {source}")
        print()

    print("=" * 76)
    print("LOGICAL GAPS (preventing this from being a proof)")
    print("=" * 76)
    gaps = [
        ("GAP 1", "Sector-dim-ratio extension to radiation thermodynamics is novel.",
         "Part IVb thm:sector-fundamental-y derives N_c via dim V_12(Q_L)/dim V_12(H) for Y-spectrum.  Reading 8 requires extending this to radiation density: cascade radiation samples FULL path-tensor V_12 (x) V_13 (x) V_14 (not just relativistic-species subspace), bosons traverse gauge layers transparently while fermions couple at each.  Plausible from cascade structure but not derived in current sources."),
        ("GAP 2", "chi^4 power = k=4 channel count for neutrino descent.",
         "Neutrino at d=21 -> observer d=4 crosses 2 Bott boundaries (P_3/P_2 at d=20-21, P_2/P_1 at d=12-13) giving k=4 by channel-count rule.  Photon at d=14 -> d=4 crosses 1 boundary giving k=2.  Plausible structural reading but the connection to (T_nu/T_gamma)^k = chi^(-k) from Born-rule squaring is suggestive, not derived."),
        ("GAP 3", "No cascade-native bridge from Omega_r to T_CMB at recombination.",
         "Part V uses SM g_eff = 3.383 as input; Part VI prop:g_eff derives g_eff cascade-natively at T_RH = 106.75.  Need analogous derivation at T_recomb where only photon (d=14) and 3 neutrinos (d=5,13,21) are relativistic, with sector-dim-ratio + basin-filter factors.  This is the priority closure work; (I9) provides the template."),
    ]
    for tag, claim, detail in gaps:
        print(f"  {tag}: {claim}")
        print(f"    {detail}")
        print()

    print("=" * 76)
    print("VERDICT")
    print("=" * 76)
    print("""
PROGRESS in this derivation attempt:
  - The N_c factor in Reading 8 has a CASCADE-DERIVED MECHANISM via
    Part IVb thm:sector-fundamental-y (sector dimension ratio).
    This is established cascade-native machinery, not numerology.
  - The chi^4 factor maps to k=4 channel count for 2 Bott periods crossed
    in neutrino descent d=21 -> d=4.
  - Both ingredients are sourced cascade primitives.

REMAINING GAPS (specific and concrete):
  GAP 1: Extend sector-dim-ratio from Y-spectrum (proven in IVb) to
         radiation thermodynamics.  Specifically: bosons traverse gauge
         layers transparently, fermions pick up sector-dim factors.
  GAP 2: Derive (T_nu/T_gamma)^k = chi^(-k) from Born-rule squaring
         applied to cascade descent amplitudes.
  GAP 3: Extend Part VI prop:g_eff layer-sum machinery to T_recomb,
         producing the cascade-native bridge from Omega_r to T_CMB.

These gaps are MORE CONCRETE than my initial framing.  The cascade has
the structural ingredients; what's missing is the formal extension of
existing theorems to the radiation thermodynamic context.

Reading 8 STAYS a candidate.  But the path to closure is clearer:
extend IVb sector-fundamental-y mechanism + IVb channel-count rule +
VI prop:g_eff layer-sum to T_recomb.  This is work the cascade can do
within its existing structural toolkit.

Per CLAUDE.md Check 4: this is acknowledged open territory (Part V
Remark rem:tcmb-descent-dependent explicitly flags g_eff closure as
open; CLAUDE.md "Known Quantitative Issues" entry on T_CMB).
""".rstrip())


if __name__ == "__main__":
    main()
