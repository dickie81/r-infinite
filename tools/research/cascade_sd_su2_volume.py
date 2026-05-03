#!/usr/bin/env python3
"""
The s/d = Omega_3 finding interpreted as SU(2) gauge group volume.

CONTEXT
=======
cascade_quark_hierarchy_full.py identified two NEW structural relations
in the quark mass hierarchy:

  s/d         = Omega_3 = 2*pi^2     (-1.30% match)
  (c/s)/(u/d) = N_c * pi^2           (-0.71% match)

This script proposes a structural mechanism: both relations follow from
cascade descent integrating over the SU(2)_L gauge group manifold.

KEY FACT
========
SU(2) is diffeomorphic to S^3 (the unit quaternions q in H with |q|=1).
With the bi-invariant Killing metric, the volume of SU(2) is

  vol(SU(2)) = 2 * pi^2 = Omega_3.

This is a standard differential-geometry fact.  SU(2) and the observer's
spatial 3-sphere have the SAME structure as a manifold and the SAME
bi-invariant volume.

THE CONJECTURE
==============
The cascade's down-quark Gen 2 -> Gen 1 mass ratio s/d equals the
SU(2)_L gauge group volume:

  s/d = vol(SU(2)) = Omega_3 = 2*pi^2.

The up-down asymmetry per generation step splits cleanly:

  Gen 3 -> 2:  (t/b)/(c/s) = N_c
               (factor N_c from SU(3) color at d=12 layer; no SU(2)
                volume because the descent hasn't yet entered the
                broken-SU(2) regime past d=13).

  Gen 2 -> 1:  (c/s)/(u/d) = N_c * vol(SU(2))/2 = N_c * pi^2
               (factor N_c from SU(3) color, plus HALF the SU(2)
                volume from chirality basin selection per Theorem 4.8).

CASCADE-INTERNAL MECHANISM
===========================
The cascade descent from Gen 2 (d=13, SU(2)_L gauge boson home) to
Gen 1 (d=21, deepest fermion layer) traverses one Bott period (8
layers).  This is the "post-gauge-window" descent region where the
SU(2)_L is broken (Higgs zero on S^12 at d=13).

Down quarks (Q_L doublet under SU(2)_L) integrate over the SU(2)
gauge orbit during this descent.  The integration measure is the
bi-invariant Haar measure on SU(2), with total volume vol(SU(2)) =
2*pi^2 = Omega_3.

Up quarks: the Q_L doublet has the same SU(2) representation, but
u_R^c has a different chirality basin (Theorem 4.8: cascade chirality
factorisation).  At the Gen 2 -> Gen 1 step, the up-quark cascade
descent picks up a chirality basin filter 1/chi = 1/2 relative to
down quarks, contributing vol(SU(2))/2 = pi^2 to the up-down
asymmetry.

WHY GEN 3 -> 2 DOESN'T PICK UP THE SU(2) VOLUME
================================================
Gen 3 (d=5) -> Gen 2 (d=13) descent passes through the gauge window
{12, 13, 14}.  At d=13 (SU(2) home), the descent enters but doesn't
yet "exit" the SU(2)-mediated regime.  The factor N_c for (t/b)/(c/s)
comes from SU(3) color at d=12 (Roadmap #6 hint), not from SU(2)
volume.

The SU(2) volume integration manifests only in the Gen 2 -> Gen 1
step where the descent is fully past the SU(2) home layer (post-
gauge-window region: d=14..21).

WHAT THIS IS / ISN'T
====================
This script presents a STRUCTURAL CONJECTURE, not a full derivation.
The conjecture matches observation within cascade standing precision
(-1.30% for s/d = Omega_3; -0.71% for (c/s)/(u/d) = N_c*pi^2; -0.60%
for c/u = 6*pi^4) and uses cascade-natural primitives (vol(SU(2)) =
Omega_3, N_c, Theorem 4.8 chirality basin).

What's NOT yet derived:
  - The cascade scalar action's Green's function explicitly integrating
    over SU(2) gauge orbit.
  - The chirality basin halving (factor 1/2) forced by Theorem 4.8 on
    the SU(2) ≅ S^3 manifold.
  - The cascade-internal proof that down-quark Gen 2 -> Gen 1 step
    picks up vol(SU(2)) (and not some other gauge volume).

What IS supplied:
  - The empirical match of three structural relations.
  - The structural mechanism: SU(2) volume + chirality basin.
  - The connection to existing cascade theorems (Theorem 4.8, Adams,
    Bott, Lefschetz).

RIGOUR LEVEL: same as Part IVb structural arguments at field-theoretic
precision.  The mechanism is cascade-internally natural; full
derivation requires explicit Green's function computation on the
cascade lattice with SU(2)-symmetric boundary conditions.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)

# Cascade primitives
N_C = 3
OMEGA_3 = 2 * math.pi**2  # observer's S^3 area = SU(2) group volume
B_OVER_S_CAS = 44.7436

# PDG observations (running MS-bar at 2 GeV for light quarks)
m_t_obs = 172.69
m_c_obs = 1.27
m_u_obs = 2.16e-3
m_b_obs = 4.18
m_s_obs = 93.4e-3
m_d_obs = 4.67e-3


def report_su2_volume() -> None:
    print("=" * 78)
    print("STEP 1: SU(2) group volume = Omega_3")
    print("=" * 78)
    print()
    print("  Standard fact: SU(2) is the manifold of unit quaternions, S^3.")
    print("  With the bi-invariant metric, vol(SU(2)) = 2*pi^2 = Omega_3.")
    print()
    print("  This is the SAME 3-sphere area that appears in:")
    print("    - Part I's locked-time 3D projection: Omega_2/Omega_3 = 2/pi.")
    print("    - Part V's baryon fraction: Omega_b = 1/Omega_3.")
    print("    - The observer's spatial slice S^3 = boundary of B^4 at d=4.")
    print()
    print("  vol(SU(2)) = 2*pi^2 = {:.4f}".format(OMEGA_3))
    print()


def report_sd_match() -> None:
    print("=" * 78)
    print("STEP 2: empirical s/d match to vol(SU(2))")
    print("=" * 78)
    print()
    print(f"  Observed s/d (2 GeV):  {m_s_obs/m_d_obs:.4f}")
    print(f"  vol(SU(2)) = Omega_3:  {OMEGA_3:.4f}")
    print(f"  Deviation:             {100*(OMEGA_3 - m_s_obs/m_d_obs)/(m_s_obs/m_d_obs):+.3f}%")
    print()
    print("  Match within cascade standing precision (~1%).")
    print()
    print("  Compare alternative cascade route (Georgi-Jarlskog at GUT):")
    sd_via_GJ = 206.50 / (N_C**2)  # m_mu/m_e / N_c^2
    print(f"    s/d via GJ = (m_mu/m_e)/N_c^2 = {sd_via_GJ:.4f}")
    print(f"    Deviation: {100*(sd_via_GJ - m_s_obs/m_d_obs)/(m_s_obs/m_d_obs):+.3f}%")
    print()
    print("  GJ route is ~10x worse fit than SU(2) volume route.  The")
    print("  cascade's better prediction comes from the SU(2) volume, not")
    print("  from cross-generation lepton ratios.")
    print()


def report_up_down_asymmetry() -> None:
    print("=" * 78)
    print("STEP 3: up-down asymmetry at Gen 2 -> Gen 1 = N_c * vol(SU(2))/2")
    print("=" * 78)
    print()
    asym = (m_c_obs/m_s_obs) / (m_u_obs/m_d_obs)
    print(f"  Observed (c/s)/(u/d):              {asym:.4f}")
    print(f"  N_c * vol(SU(2))/2 = N_c * pi^2:  {N_C*math.pi**2:.4f}")
    print(f"  Deviation:                         {100*(N_C*math.pi**2 - asym)/asym:+.3f}%")
    print()
    print("  The 'half SU(2) volume' interpretation:")
    print()
    print("    SU(2) ≅ S^3 has an antipodal Z_2 symmetry q -> -q.")
    print("    The quotient PSU(2) = SU(2)/Z_2 = SO(3) ≅ RP^3 has half")
    print("    the volume: vol(SO(3)) = pi^2 = vol(SU(2))/2.")
    print()
    print("    Theorem 4.8 (cascade chirality factorisation): on any")
    print("    even-dim sphere, Morse function gives chi=2 chirality basins")
    print("    of equal area.  S^3 is odd-dim, so doesn't natively split.")
    print("    But the SU(2) -> SO(3) covering provides a Z_2 quotient that")
    print("    realises a 'chirality basin selection' on the SU(2) gauge")
    print("    group manifold: pick SU(2) (full group) or PSU(2) (quotient).")
    print()
    print("    Up quarks: pick the quotient (factor 1/2).")
    print("    Down quarks: pick the full group (factor 1).")
    print()
    print("    Why? u_R has Y = +2/3 = 2 * |Y_d_R| (from sector-fundamental")
    print("    rule, Part IVb thm:sector-fundamental-y).  The factor-of-2")
    print("    Y difference may correlate with the SU(2)-vs-PSU(2) choice.")
    print()
    print("    This is structurally suggestive but not yet derived.")
    print()


def report_combined() -> None:
    print("=" * 78)
    print("STEP 4: combined c/u = N_c * vol(SU(2))^2 / 2 = 6*pi^4")
    print("=" * 78)
    print()
    print("  c/u = (c/s)*(s/d)/(u/d)")
    print("      = (s/d) * (c/s)/(u/d)")
    print("      = vol(SU(2)) * N_c * vol(SU(2))/2")
    print("      = N_c * vol(SU(2))^2 / 2")
    print("      = N_c * (2*pi^2)^2 / 2")
    print("      = N_c * 2 * pi^4")
    print("      = 6 * pi^4")
    print()
    print(f"  Observed c/u:           {m_c_obs/m_u_obs:.4f}")
    print(f"  6 * pi^4:               {6*math.pi**4:.4f}")
    print(f"  N_c * vol(SU(2))^2/2:   {N_C * OMEGA_3**2 / 2:.4f}")
    print(f"  Deviation:              {100*(6*math.pi**4 - m_c_obs/m_u_obs)/(m_c_obs/m_u_obs):+.3f}%")
    print()
    print("  Equivalently: c/u = 6*pi^4 = N_c * (Omega_3)^2 / 2.")
    print()
    print("  Geometric reading: the up-quark Gen 2 -> Gen 1 step picks up")
    print("  TWO factors of (SU(2) volume) -- one from the descent itself,")
    print("  one from the chirality basin halving -- combined with the")
    print("  SU(3) color factor N_c.")
    print()


def report_why_gen3_2_doesnt() -> None:
    print("=" * 78)
    print("STEP 5: why Gen 3 -> 2 doesn't pick up SU(2) volume")
    print("=" * 78)
    print()
    print("  Gen 3 (d=5) -> Gen 2 (d=13) descent: 8 layers spanning P_0 + P_1.")
    print("  Crosses gauge window at d=12 (SU(3)), d=13 (SU(2)).")
    print()
    print("  At d=12, the descent enters the SU(3) sector (color factor N_c).")
    print("  At d=13, the descent enters the SU(2) sector but doesn't yet")
    print("    'spread out' over the broken-SU(2) regime -- the descent")
    print("    terminates AT d=13 (Gen 2 fermion home).")
    print()
    print("  The SU(2) volume integration manifests only when the descent")
    print("  PASSES THROUGH the broken-SU(2) regime past d=13.  This happens")
    print("  in the Gen 2 -> 1 step (descent d=13..21, fully past the SU(2)")
    print("  home layer).")
    print()
    print("  Asymmetry summary:")
    print(f"    Gen 3 -> 2:  (t/b)/(c/s) = N_c                    [color only]")
    print(f"    Gen 2 -> 1:  (c/s)/(u/d) = N_c * vol(SU(2))/2     [color + half SU(2)]")
    print()
    print("  The 'kicks in at Gen 2 -> 1' pattern is consistent with the")
    print("  cascade descent's natural progression: SU(3) factor at the")
    print("  gauge-window step (Gen 3 -> 2), SU(2) volume factor at the")
    print("  post-gauge-window step (Gen 2 -> 1).")
    print()


def report_status() -> None:
    print("=" * 78)
    print("STEP 6: status and outlook")
    print("=" * 78)
    print()
    print("  THIS SCRIPT'S CONTRIBUTION:")
    print()
    print("  - Identifies vol(SU(2)) = 2*pi^2 = Omega_3 as the cascade-")
    print("    internal structural origin of s/d = Omega_3.")
    print("  - Interprets the up-down asymmetry growth pi^2 between")
    print("    generation steps as 'half SU(2) volume' = vol(PSU(2)),")
    print("    consistent with cascade chirality basin selection.")
    print("  - Connects three NEW empirical relations (s/d = Omega_3,")
    print("    (c/s)/(u/d) = N_c*pi^2, c/u = 6*pi^4) to existing cascade")
    print("    primitives (gauge group volumes, Theorem 4.8 chirality).")
    print()
    print("  STATUS: structural conjecture matching observation to ~1%.")
    print()
    print("  RIGOUR LEVEL: cascade-internal mechanism articulated with")
    print("  standard cascade primitives.  Full derivation requires:")
    print()
    print("  (1) Explicit cascade scalar action Greens function with")
    print("      SU(2)-symmetric boundary conditions over the descent")
    print("      d=13..21, showing the integration measure equals")
    print("      vol(SU(2))-weighted volume.")
    print()
    print("  (2) Cascade-internal proof that up-quark Q_L^c (with Y=+2/3)")
    print("      picks up vol(PSU(2)) = vol(SU(2))/2 while down-quark")
    print("      Q_L^c (with Y=-1/3) picks up full vol(SU(2)).  Likely")
    print("      through Theorem 4.8 chirality basin selection on the")
    print("      SU(2) -> PSU(2) Z_2 covering.")
    print()
    print("  (3) Connection to the original Roadmap #6 mechanism (Weyl")
    print("      chirality factor at d=12).  The N_c factor at Gen 3 -> 2")
    print("      should also derive from the same cascade-action Greens")
    print("      function, with SU(3)-symmetric boundary conditions.")
    print()
    print("  IMPLICATIONS IF DERIVED:")
    print()
    print("  Closing (1)-(3) cascade-internally would promote 5 of 6 quark")
    print("  masses to Tier 2 (theorem-level) via gauge group volume")
    print("  integration.  This would be a significant unification: gauge")
    print("  group volumes (vol(SU(N)) for N=2, 3) explicitly appear in")
    print("  fermion mass hierarchy at theorem level, bridging the cascade")
    print("  Adams + Bott structural framework with the observed quark")
    print("  mass spectrum.")
    print()


def main() -> int:
    print("=" * 78)
    print("STRUCTURAL CONJECTURE: s/d = vol(SU(2)) = Omega_3")
    print("Roadmap #6 -- structural mechanism for the down-quark Gen 2 -> 1 step")
    print("=" * 78)
    print()
    report_su2_volume()
    report_sd_match()
    report_up_down_asymmetry()
    report_combined()
    report_why_gen3_2_doesnt()
    report_status()
    print("=" * 78)
    print("CONJECTURE: cascade-internal s/d = vol(SU(2)) = 2*pi^2 = Omega_3.")
    print("            Up-down asymmetry at Gen 2 -> 1 picks up additional")
    print("            'half SU(2) volume' = pi^2 from chirality basin")
    print("            selection (Theorem 4.8 applied to SU(2) ≅ S^3 via")
    print("            its Z_2 antipodal covering -> PSU(2) ≅ RP^3).")
    print()
    print("STATUS:     empirical match within cascade standing precision")
    print("            (-1.30%, -0.71%, -0.60% for the three relations).")
    print("            Structural mechanism identified; full derivation open.")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
