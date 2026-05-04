#!/usr/bin/env python3
"""
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

PLAUSIBILITY ARGUMENT
=====================
GIVEN (I1)-(I8), here is a candidate structural argument for
(T_nu/T_gamma)^4 = N_c/chi^4 at recombination temperature.

Step A (cascade-native, follows (I7)+(I8)):
   At recombination (T ~ 0.26 eV), cascade-native counting includes
   photons + neutrinos as relativistic species.  All other SM particles
   (charged leptons, quarks, gauge bosons except photon) are non-
   relativistic and decouple.  Without e+e- annihilation, photons and
   neutrinos START at the same temperature.

Step B (cascade-native, follows (I3)+(I5)+(I6)):
   Basin filter applies asymmetrically.  Neutrinos are chirality-broken
   (left-handed only in our basin), so their phase space is restricted
   to 1 of chi^4 = 16 basin combinations across the 4 spatial dimensions.
   Photons are basin-symmetric (chi-invariant), so no basin restriction.
   Effective phase-space ratio: nu/gamma = 1/chi^4.

Step C (cascade-native, follows (I4)):
   Photon-colour coupling at the gauge window.  The cascade radiation
   density flows through the gauge window {d=12, 13, 14}.  Photons live
   at d=14 (U(1) gauge layer); colour SU(3) lives at d=12.  Although
   photons are colour-singlets in the broken phase, the cascade's gauge-
   window crossing structure couples photon thermal density to the
   colour multiplicity at d=12.  Each of N_c = 3 colour states contributes
   to the photon's effective phase space at the gauge window.
   Effective photon phase-space multiplier: N_c.

Step D (combining B+C):
   Net ratio of neutrino-to-photon phase space:
      (phase_nu / phase_gamma) = (1/chi^4) / (N_c) = 1/(N_c * chi^4)
   But the temperature ratio's fourth power is the INVERSE of phase-space
   ratio (since hotter species have more phase space):
      (T_nu / T_gamma)^4 = N_c / chi^4 = 3/16

Numerical check:
   3/16 = 0.1875
   Required for T_CMB closure: 0.188 (off by 0.27%)
   T_CMB(Reading 8) = 2.726 K vs observed 2.7255 K (residual +0.02%)

LOGICAL GAPS (prevent this from being a proof)
==============================================
GAP 1 (Step C is unjustified):
   The claim "photon thermal density at recombination picks up N_c colour
   multiplicity from the d=12 gauge layer" has no cascade-native
   derivation.  It would require:
   (a) A cascade-native bridge formula from Omega_r = 1/(4*pi^7) at
       d=11 to T_CMB at the observer's d=4 layer, that propagates through
       the gauge window {d=12, 13, 14} and picks up multiplicity factors
       at each crossed layer.
   (b) A specific argument for why photons (colour singlets) couple to
       colour multiplicity in the radiation thermodynamic counting.
       Standard QFT says photons don't see colour at all.  The cascade
       might say differently because all matter content lives at the
       same gauge window, but this needs derivation.

GAP 2 (Step B chi^4 power):
   The basin filter for neutrinos is plausibly ~1/chi for ONE chirality
   restriction.  Why chi^4 (one factor per spatial dimension)?
   Each spatial dimension having an independent basin is structural ((I1)
   on S^4 lifted to 4D + Lovelock), but the cascade has not derived that
   these are MULTIPLICATIVE in the radiation thermodynamic counting.
   Possible alternatives: chi^1 (single 4D basin), chi^2 (basin pair on
   each 2-cycle), chi^4 (four independent dimensions).

GAP 3 (No cascade-native bridge from Omega_r to T_CMB):
   Part V derives Omega_r = 1/(4*pi^7) geometrically (Part V Theorem
   on Omega_r, Remark `rem:why-4-plus-7`: "no quantity in this derivation
   refers to photons, thermal equilibrium, or particle physics").  But
   the bridge from Omega_r to T uses SM thermodynamics:
      T_CMB = (90 Omega_r M_Pl^2 H_0^2 / (pi^2 g_eff))^(1/4)
   with g_eff = 3.383 imported from SM.  A cascade-native bridge
   formula would derive g_eff and hence T_CMB structurally.  Without
   it, ANY g_eff substitution (Reading 5's g_eff = N_c, Reading 8's
   g_eff = 2 + (7/8)(2)(3)(3/16) = 2.984) is ad hoc.

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
        ("(I3)", "chi^4 = 16 basin combinations across 4 dims",
         "Combinatorial consequence of (I1)+(I2); novel application"),
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
    ]
    for tag, desc, source in sources:
        print(f"  {tag} {desc}")
        print(f"       SOURCE: {source}")
        print()

    print("=" * 76)
    print("LOGICAL GAPS (preventing this from being a proof)")
    print("=" * 76)
    gaps = [
        ("GAP 1", "Step C (photon picks up N_c multiplicity at gauge window) is unjustified.",
         "Standard QFT: photons don't see colour at all.  Cascade needs to derive WHY the radiation thermodynamic counting at the gauge window gives photons an N_c factor.  Required: cascade-native bridge formula from Omega_r to T_CMB through the gauge window."),
        ("GAP 2", "Step B chi^4 (not chi^1, chi^2) power is unjustified.",
         "Each spatial dimension having an independent chi=2 basin is plausible from S^4 chi=2 + 4D Lovelock, but multiplicativity in radiation thermodynamics is not derived."),
        ("GAP 3", "No cascade-native bridge from Omega_r to T_CMB.",
         "Part V uses SM g_eff = 3.383 as input; closing would require deriving g_eff cascade-natively at recombination temperature, not just at T_RH (where Part VI prop:g_eff already does it)."),
    ]
    for tag, claim, detail in gaps:
        print(f"  {tag}: {claim}")
        print(f"    {detail}")
        print()

    print("=" * 76)
    print("VERDICT")
    print("=" * 76)
    print("""
The structural plausibility argument has cascade-native ingredients but
LACKS THE KEY BRIDGE that would make it a proof.  Reading 8's numerical
match at +0.023% (within standing cascade precision) is suggestive but
not yet derived.

The argument is:
  - PARTIAL STRUCTURE: chi^4 plausibly from basin product across 4 dims;
    N_c plausibly from colour at d=12 -- both cascade-native.
  - MISSING BRIDGE: no cascade-native derivation that the radiation
    thermodynamic counting at recombination is photon * N_c divided by
    neutrino * 1/chi^4.  Standard QFT does not give photons a colour
    multiplicity factor.
  - REQUIRED WORK: derive the cascade-native Omega_r -> T_CMB bridge
    explicitly (Gap 3 = Gap 1 root cause).

Reading 8 STAYS a candidate, not a closure.  Per CLAUDE.md Check 4 this
is acknowledged open territory (Part V Remark rem:tcmb-descent-dependent
explicitly flags g_eff closure as open).
""".rstrip())


if __name__ == "__main__":
    main()
