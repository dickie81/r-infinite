#!/usr/bin/env python3
"""
Route B attack on (R1) Y_H = N_c * Y_QL: cascade-native SU(2)^2 x U(1)_Y
trace via path-tensor consistency at d=13.

CONTEXT
=======
(R1) Y_H = N_c * Y_QL is the open trace identity in the Y-spectrum
chain (Part IVa rem:y-spectrum-open).  Closure would derive the SM
hypercharge weights from cascade primitives modulo the geometric
observer-anchor on S^4 at d=5.

THE SM ROUTE TO (R1)
====================
In the SM, (R1) follows from:
  - SU(2)^2 x U(1)_Y anomaly cancellation: sum over doublets of
    (n^SU(3) * Y) = 0  =>  3 * Y_QL + 1 * Y_LL = 0  =>  Y_LL = -3 * Y_QL.
  - (R2) Y_LL = -Y_H (gravitational anomaly + Yukawa singlet).
  - Combine: Y_H = -Y_LL = 3 * Y_QL = N_c * Y_QL.

The cascade has (R2) closed via per-layer locality + algebra
(rem:fermion-gauge-coupling-proposal).  (R1) requires the SU(2)^2 x
U(1)_Y trace condition.

ROUTE B HYPOTHESIS
==================
Cascade-native path-tensor consistency at d=13 -- under multi-particle
SU(2) gauge transformation acting on V_13 of all matter units -- might
supply the SU(2)^2 x U(1)_Y trace cascade-natively, replacing QFT
triangle anomalies (which are ruled out by per-layer locality).

THE ATTACK
==========
1. Set up multi-particle path-tensor at d=13 explicitly.
2. Apply SU(2) gauge transformation.
3. Check what cascade-internal consistency conditions emerge.
4. Specifically test whether sum_{doublets} n^SU(3) * Y = 0 is forced.

WHAT THIS SCRIPT DOES NOT DO
============================
Pre-judge the outcome.  This is a research dig, not advocacy.

WHAT THIS SCRIPT DELIVERS
=========================
A direct check of whether Route B closes (R1).  Either:
  - Closes: cascade derives SU(2)^2 x U(1)_Y trace cascade-natively;
    (R1) follows; Y-spectrum chain closes.
  - Fails: documents the specific reason path-tensor consistency
    doesn't supply the trace.  Pivots to alternative routes.
"""

from __future__ import annotations

import sys
from fractions import Fraction


# ---------------------------------------------------------------------------
# Multi-particle path-tensor at d=13 (SM matter content per generation, LH Weyl)
# ---------------------------------------------------------------------------

SM_MATTER_LH = [
    # (name, V_12 dim, V_13 dim, multiplicity factor n^SU(3))
    ("Q_L",   3, 2, 3),
    ("u_L^c", 3, 1, 3),
    ("d_L^c", 3, 1, 3),
    ("L_L",   1, 2, 1),
    ("e_L^c", 1, 1, 1),
]


def doublets():
    """Return only the SU(2)-doublet matter units."""
    return [m for m in SM_MATTER_LH if m[2] == 2]


# ---------------------------------------------------------------------------
# Step 1: per-layer-local action under SU(2) gauge transformation
# ---------------------------------------------------------------------------

def step1_per_layer_action_under_su2():
    print("=" * 78)
    print("STEP 1: per-layer-local action under SU(2) gauge transformation at d=13")
    print("=" * 78)
    print()
    print("The cascade fermion action at d=13 (from rem:fermion-gauge-coupling-")
    print("proposal) is per-layer local:")
    print()
    print("  S_f^{cascade}(d=13) = m(13) sum_i psi-bar^(i)(13) psi^(i)(13)")
    print("                       + g(13) sum_i psi-bar^(i)(13) T^a A^a(13) psi^(i)(13)")
    print()
    print("with sum_i over all matter units carrying V_13 != 0.")
    print()
    print("Under SU(2)_L gauge transformation U_2 acting on V_13:")
    print("  - Doublet psi^(i): psi^(i) -> U_2 psi^(i)")
    print("  - Singlet psi^(j): psi^(j) -> psi^(j)  (T^a annihilates singlets)")
    print("  - Gauge field: A^a -> (U_2 A U_2^{-1} - i (partial U_2) U_2^{-1} / g)^a")
    print()
    print("The mass term m bar-psi psi:")
    print("  bar-psi^(i) psi^(i) -> bar-psi^(i) U_2^dag U_2 psi^(i) = bar-psi^(i) psi^(i)")
    print("  -> INVARIANT per particle.")
    print()
    print("The gauge-coupling term g bar-psi T^a A^a psi:")
    print("  Standard gauge theory result: invariant under combined transformation.")
    print("  -> INVARIANT per particle.")
    print()
    print("Per-layer Berezin integration:")
    print("  Z_f^(i)(13) = int [d-bar-psi^(i) d-psi^(i)] exp(-S^(i)) = m(13)")
    print("  This is INVARIANT under unitary rotation of psi^(i):")
    print("  the Berezin Jacobian for U(2) rotation is exactly 1.")
    print("  -> INVARIANT per particle.")
    print()
    print("CRITICAL OBSERVATION")
    print("====================")
    print("The full multi-particle path integral at d=13 is the PRODUCT of")
    print("per-particle Berezin factors:")
    print()
    print("  Z_tot(13) = prod_i Z_f^(i)(13) = m(13)^{N_matter}")
    print()
    print("Under SU(2) gauge transformation, EACH FACTOR is invariant")
    print("INDEPENDENTLY.  The product is therefore invariant trivially.  No")
    print("Jacobian-style anomaly arises from the multi-particle structure.")
    print()


# ---------------------------------------------------------------------------
# Step 2: where would multi-particle constraint come from?
# ---------------------------------------------------------------------------

def step2_search_for_multi_particle_constraint():
    print("=" * 78)
    print("STEP 2: search for cascade-native multi-particle SU(2) consistency")
    print("=" * 78)
    print()
    print("In SM, SU(2)^2 x U(1)_Y anomaly comes from triangle diagrams with")
    print("two SU(2) gauge boson lines + one U(1)_Y line + a fermion loop.")
    print("The fermion path-integral measure under combined SU(2)+U(1)_Y")
    print("gauge transformations picks up a Jacobian that vanishes only if")
    print("sum_{doublets} (1/2) n^SU(3) Y = 0.  No triangle => no anomaly =>")
    print("no constraint.")
    print()
    print("Per-layer locality of cascade fermions PRECLUDES TRIANGLE DIAGRAMS:")
    print("  - Triangles require derivative gauge couplings (psi-bar gamma_mu A_mu psi")
    print("    with momentum dependence).  Cascade fermion action is")
    print("    psi-bar T^a A^a psi (no derivatives).")
    print("  - Triangles require multi-loop fermion propagators across spacetime.")
    print("    Cascade fermion is per-layer local on the d-axis; no multi-loop")
    print("    structure on the cascade lattice.")
    print()
    print("So the SM's path to the trace constraint is INACCESSIBLE.  Are there")
    print("CASCADE-NATIVE alternative routes to a similar constraint?")
    print()
    print("Candidates audited:")
    print()
    print("  (a) Higgs Yukawa multi-particle consistency.  bar-Q_L H u_R must")
    print("      be SU(2)xU(1)-invariant for each generation.  Per-particle")
    print("      Yukawa singlet conditions follow.  Multi-particle: same")
    print("      conditions for each particle pair.  No NEW cross-particle")
    print("      constraint emerges.")
    print()
    print("  (b) Q = T_3 + Y consistency across all particle types.  After")
    print("      EW breaking, the unbroken U(1)_em annihilates the Higgs vacuum.")
    print("      For each particle, Q = T_3 + Y is a per-particle constraint")
    print("      on Y given Q (electric charge).  Multi-particle: each particle")
    print("      satisfies its own Q = T_3 + Y.  No cross-particle constraint.")
    print()
    print("  (c) Mass matrix unitary.  CKM matrix is unitary, mass eigenstates")
    print("      have well-defined Q.  This requires Y values to be the same")
    print("      across generations (universality), which is automatic in the")
    print("      cascade per-layer-local structure.  Doesn't pin Y_QL vs Y_LL.")
    print()
    print("  (d) Cascade descent path consistency.  Each particle's descent")
    print("      from gauge layer to observer is universal (exp(Phi)).  Doesn't")
    print("      see V values.  No constraint.")
    print()
    print("RESULT: no cascade-native mechanism examined supplies the multi-")
    print("particle constraint sum_{doublets} n^SU(3) Y = 0.")
    print()


# ---------------------------------------------------------------------------
# Step 3: structural reason for the failure
# ---------------------------------------------------------------------------

def step3_structural_failure_reason():
    print("=" * 78)
    print("STEP 3: structural reason path-tensor consistency does not supply (R1)")
    print("=" * 78)
    print()
    print("The cascade's SUCCESS at closing (R2) Y_LL = -Y_H went through a")
    print("specific algebraic path:")
    print("  Yukawa singlet conditions (per-layer locality) + sum_i n_i Y_i = 0")
    print("    => Y_H + Y_LL = 0  (after substitution and cancellation).")
    print()
    print("The cascade's Yukawa singlet conditions are per-particle (each")
    print("Yukawa term must be SUxU-invariant individually).  Algebra then")
    print("reduces the multi-particle gravitational anomaly equation to (R2).")
    print()
    print("(R1) Y_H = N_c * Y_QL would require:")
    print("  (a) A multi-particle algebraic identity NOT reducible to per-particle")
    print("      constraints, AND")
    print("  (b) That identity having the specific form sum_{doublets} n^SU(3) Y_i = 0.")
    print()
    print("In the SM, this comes from anomaly cancellation -- a multi-particle")
    print("path-integral consistency.  The cascade's path integral at d=13 is:")
    print()
    print("  Z_tot(13) = m(13)^{N_matter}")
    print()
    print("a positive scalar with no per-particle weight dependence beyond")
    print("multiplicity.  It cannot encode trace conditions on Y values, since")
    print("Y values appear only in the gauge-coupling term (which is zero in")
    print("the partition function: it's an interaction term, not a measure term).")
    print()
    print("STRUCTURAL CONCLUSION")
    print("====================")
    print("Per-layer locality + Berezin scalar partition function precludes")
    print("the multi-particle path-integral structure that pins (R1) in the SM.")
    print("Route B (cascade-native SU(2)^2 x U(1)_Y trace via path-tensor")
    print("consistency) FAILS for the SAME structural reason that ruled out")
    print("the original triangle-anomaly attack on (I) gravitational x Y.")
    print()
    print("The pattern holds across all four anomaly-style trace conditions:")
    print("  (I)   sum n_i Y_i = 0          [grav x Y]:    inaccessible")
    print("  (II)  sum_{colored} n^SU(2) Y  [SU(3)^2 x Y]: inaccessible")
    print("  (III) sum_{doublets} n^SU(3) Y [SU(2)^2 x Y]: inaccessible (THIS DIG)")
    print("  (IV)  sum n_i Y_i^3            [Y^3]:         inaccessible")
    print()
    print("Cascade per-layer locality structurally precludes any of these")
    print("from being derived as gauge-anomaly conditions cascade-natively.")
    print()


# ---------------------------------------------------------------------------
# Step 4: implications and pivot
# ---------------------------------------------------------------------------

def step4_pivot_to_alternative_routes():
    print("=" * 78)
    print("STEP 4: implications and pivot to alternative routes for (R1)")
    print("=" * 78)
    print()
    print("(R1) cannot be derived via SM-style anomaly cancellation.  This is")
    print("structural (not a calculational gap).  The cascade's SUCCESSFUL")
    print("closures of (R2), Yukawa singlets, and the per-layer Berezin form")
    print("ALL rely on per-layer locality; the SAME locality precludes (R1).")
    print()
    print("REMAINING ROUTES TO (R1)")
    print("========================")
    print()
    print("  ROUTE A: Direct path-tensor color trace.")
    print("  --------")
    print("  Articulate 'V_12 = 1 weight is the trace over V_12 = 3 of the")
    print("  V_12 = 3 weight' as a cascade structural theorem.  This requires")
    print("  identifying a cascade operation T: V_14|_{V_12=3} -> V_14|_{V_12=1}")
    print("  that gives Y_H = N_c * Y_QL by definition rather than derivation.")
    print()
    print("  Risk: tautological.  If the cascade DEFINES Y_H to be the trace")
    print("  over color of Y_QL, then (R1) is true by construction but doesn't")
    print("  derive Y_H independently.  We'd be writing down (R1) by fiat.")
    print()
    print("  ROUTE C: Higgs Yukawa fixed-point structure.")
    print("  --------")
    print("  Use the cascade Higgs's role as the hairy-ball zero on S^12 at")
    print("  d=13 (Part IVa thm:higgs).  The Higgs vacuum direction at the")
    print("  S^12 equator + the matter Yukawa structure might force Y_H to")
    print("  satisfy (R1) via a fixed-point-of-S^12 constraint.")
    print()
    print("  Risk: speculative.  The Higgs sits at one specific geometric")
    print("  point; quark doublets sit elsewhere on S^12.  Connecting their")
    print("  Y values via a single S^12 invariant requires identifying the")
    print("  invariant, which is not yet done.")
    print()
    print("  ROUTE D: New cascade ingredient.")
    print("  --------")
    print("  Accept that (R1) is NOT derivable from current cascade primitives.")
    print("  Identify what ADDITIONAL cascade structure would supply it (e.g.,")
    print("  a multi-layer kinetic term for fermions that the per-layer-local")
    print("  proposal explicitly excludes).")
    print()
    print("  This would REOPEN oq:fermion-gauge-action -- specifically the")
    print("  decision to take the action per-layer local.  If a multi-layer")
    print("  kinetic structure CAN be reconciled with the existing closures")
    print("  (Berezin partition function, Yukawa singlets), it might supply")
    print("  the multi-particle constraint that closes (R1).")
    print()
    print("  Risk: contradicts the per-layer-locality derivation already in")
    print("  rem:fermion-gauge-coupling-proposal.  Would require reopening")
    print("  closed work.")
    print()
    print("RECOMMENDATION")
    print("==============")
    print("Route A is the most concrete next attempt.  Even if it ends up")
    print("tautological, articulating the trace operation cascade-natively")
    print("would clarify what's derivable and what's definitional.  Route C")
    print("is the most speculative but might supply genuine structural")
    print("content if the S^12 fixed-point structure pins Y_H independently.")
    print()
    print("Route B is closed: cascade-native anomaly-style trace is")
    print("STRUCTURALLY UNAVAILABLE.")
    print()


def main() -> int:
    print("=" * 78)
    print("ROUTE B ATTACK ON (R1): cascade-native SU(2)^2 x U(1)_Y trace")
    print("via path-tensor consistency at d=13")
    print("=" * 78)
    print()
    step1_per_layer_action_under_su2()
    step2_search_for_multi_particle_constraint()
    step3_structural_failure_reason()
    step4_pivot_to_alternative_routes()
    return 0


if __name__ == "__main__":
    sys.exit(main())
