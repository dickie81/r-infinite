#!/usr/bin/env python3
"""
Cascade-internal anomaly cancellation: framework for closing the SM
hypercharge Y spectrum at d=14.

CONTEXT
=======
Part IVa rem:fund-or-trivial closes the fundamental representation
DIMENSION at each gauge-window layer:

    d=12 (SU(3)):  V_{12} in {1, 3}   (closed)
    d=13 (SU(2)):  V_{13} in {1, 2}   (closed by rem:single-h-factor)
    d=14 (U(1)):   dim_C = 1          (closed)

The Y VALUES at d=14 are NOT closed by rem:fund-or-trivial.  J's
eigenvalues are +/- i (uniform +/- phase under exp(theta J)), which
cannot reproduce the fractional SM Y spectrum
{-1, -1/2, -1/3, +1/6, +2/3, +1}.

This script lays out the candidate cascade-native route:
cascade-internal anomaly cancellation.  It DOES NOT close the
question -- it sets up the framework as research scaffolding for a
future closure attempt.

THE FOUR ANOMALY CONDITIONS (SM)
================================
For one generation of left-handed Weyl fermions (with right-handed
fields conjugated to left-handed): the SM has four gauge-anomaly
conditions whose simultaneous vanishing forces the Y spectrum up to
overall normalization.  Plus one electric-charge anchor (e.g.
Q_e = -1) pins the normalization.

  (I)   Gravitational x U(1)_Y:  sum_i n_i * Y_i = 0
  (II)  SU(3)^2 x U(1)_Y:        sum_{colored i} n_i^{SU(2)} * Y_i = 0
  (III) SU(2)^2 x U(1)_Y:        sum_{doublet i} n_i^{SU(3)} * Y_i = 0
  (IV)  U(1)_Y^3:                sum_i n_i * Y_i^3 = 0

where n_i = dim(SU(3) rep) * dim(SU(2) rep) of the i-th particle, and
in (II)/(III) we restrict to the relevant colored / doublet subsets.

This script:
  1. Verifies the SM Y spectrum satisfies (I)-(IV) numerically.
  2. Identifies cascade-native candidates for each of (I)-(IV) and
     reports which admit a reading from existing cascade primitives
     and which require new cascade structure.
  3. Tests whether (I)-(IV) plus an electric-charge anchor uniquely
     determine the Y values (algebraically, given the matter content
     from rem:fund-or-trivial + rem:path-tensor).
  4. Reports the OPEN question: which cascade-internal constraints
     play the role of (I)-(IV)?

WHAT THIS SCRIPT DOES NOT DO
============================
  - It does not derive the cascade-native versions of (I)-(IV) from
    cascade structural theorems.  It only PROPOSES candidates.
  - It does not close the Y spectrum cascade-natively.  Closure
    requires identifying actual cascade-internal mechanisms for
    each anomaly condition.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from itertools import product


# ---------------------------------------------------------------------------
# SM matter content per generation (left-handed Weyl convention)
# ---------------------------------------------------------------------------
#
# Each entry: (name, SU(3) rep dim, SU(2) rep dim, Y (as Fraction))
# Right-handed fields are conjugated: Y -> -Y, SU(3) 3 -> 3-bar (same dim).
# Multiplicities n_i = SU(3)_dim * SU(2)_dim.

SM_GENERATION_LH = [
    # Quark doublet Q_L = (u_L, d_L), color triplet, SU(2) doublet, Y = +1/6
    ("Q_L",   3, 2, Fraction(1, 6)),
    # u_L^c (conjugate of u_R), color anti-triplet (still dim 3), singlet, Y = -2/3
    ("u_L^c", 3, 1, Fraction(-2, 3)),
    # d_L^c, color anti-triplet, singlet, Y = +1/3
    ("d_L^c", 3, 1, Fraction(1, 3)),
    # Lepton doublet L_L = (nu_L, e_L), color singlet, doublet, Y = -1/2
    ("L_L",   1, 2, Fraction(-1, 2)),
    # e_L^c, color singlet, singlet, Y = +1
    ("e_L^c", 1, 1, Fraction(1, 1)),
]


def n_i(particle):
    """Multiplicity factor n_i = dim(SU(3)) * dim(SU(2))."""
    _name, n3, n2, _Y = particle
    return n3 * n2


# ---------------------------------------------------------------------------
# Anomaly conditions
# ---------------------------------------------------------------------------

def grav_anomaly(matter):
    """Sum_i n_i Y_i (gravitational x U(1)_Y)."""
    return sum(n_i(p) * p[3] for p in matter)


def su3sq_y_anomaly(matter):
    """Sum_{colored i} n_i^{SU(2)} * Y_i (SU(3)^2 x U(1)_Y).

    For SU(3): trace of T^a T^b over the SU(3) rep is
    tr(T^a T^b) = T(R) delta^{ab}, with T(fund) = 1/2 in the standard
    normalization.  Color triplets and anti-triplets each contribute
    T(R) = 1/2, so the anomaly is:
        sum_{colored i} (1/2) * n_i^{SU(2)} * Y_i = 0
    Drop the overall 1/2: sum_{colored} n^{SU(2)} Y.
    """
    return sum(p[2] * p[3] for p in matter if p[1] == 3)


def su2sq_y_anomaly(matter):
    """Sum_{doublet i} n_i^{SU(3)} * Y_i (SU(2)^2 x U(1)_Y).

    Parallel to (II) but for SU(2): T(fund) = 1/2; doublets contribute
    sum_{doublet} (1/2) n^{SU(3)} Y; drop the 1/2 overall:
        sum_{doublet} n^{SU(3)} Y.
    """
    return sum(p[1] * p[3] for p in matter if p[2] == 2)


def y_cubed_anomaly(matter):
    """Sum_i n_i Y_i^3 (U(1)_Y^3)."""
    return sum(n_i(p) * p[3] ** 3 for p in matter)


# ---------------------------------------------------------------------------
# Verify SM satisfies (I)-(IV)
# ---------------------------------------------------------------------------

def verify_sm_anomalies():
    print("=" * 78)
    print("STEP 1: verify SM Y spectrum satisfies all four anomaly conditions")
    print("=" * 78)
    print()
    print("Per-generation left-handed Weyl content:")
    print()
    for p in SM_GENERATION_LH:
        name, n3, n2, Y = p
        print(f"  {name:8s}  SU(3)={n3}  SU(2)={n2}  Y={Y}  "
              f"n_i={n_i(p)}")
    print()
    g = grav_anomaly(SM_GENERATION_LH)
    su3 = su3sq_y_anomaly(SM_GENERATION_LH)
    su2 = su2sq_y_anomaly(SM_GENERATION_LH)
    y3 = y_cubed_anomaly(SM_GENERATION_LH)
    print(f"  (I)   Gravitational x Y:  sum n_i Y_i        = {g}")
    print(f"  (II)  SU(3)^2 x Y:        sum_{{colored}} n^SU(2) Y_i  = {su3}")
    print(f"  (III) SU(2)^2 x Y:        sum_{{doublet}} n^SU(3) Y_i  = {su2}")
    print(f"  (IV)  Y^3:                sum n_i Y_i^3      = {y3}")
    print()
    all_zero = all(x == 0 for x in (g, su3, su2, y3))
    print(f"  All four vanish: {all_zero}")
    print()


# ---------------------------------------------------------------------------
# Cascade-native candidate readings
# ---------------------------------------------------------------------------

def report_cascade_candidates():
    print("=" * 78)
    print("STEP 2: cascade-native candidate readings of each condition")
    print("=" * 78)
    print()
    print("The cascade has these structural primitives at the gauge layers:")
    print("  - Descent paths (Part IVa thm:forced-paths)")
    print("  - SU(3)/SU(2)/U(1) gauge groups (Adams)")
    print("  - Cascade complex structure J on R^14 (Part II)")
    print("  - Lefschetz obstruction at d=13 (thm:lefschetz)")
    print("  - Hairy-ball obstruction at d=13")
    print("  - Path-tensor structure V_{12} x V_{13} x V_{14} (rem:path-tensor)")
    print("  - Fundamental-or-trivial principle (rem:fund-or-trivial)")
    print()

    candidates = [
        (
            "(I)   Gravitational x Y",
            "Trace of V_{14} eigenvalue distribution over path-tensor "
            "matter content vanishes",
            "DESCENT-INTEGRAL WELL-DEFINEDNESS: the global cascade integral "
            "of a multi-particle matter state at d=14 must be finite; the "
            "leading divergence is proportional to sum n_i Y_i. "
            "STATUS: candidate, not derived from existing primitives. "
            "Need: a cascade theorem stating 'the multi-particle descent "
            "integral at d=14 converges only if the trace of V_{14} weights "
            "over matter content vanishes.'",
        ),
        (
            "(II)  SU(3)^2 x Y",
            "Sum of V_{14} weights over color-fundamental matter vanishes "
            "(restricted to color-charged particles, weighted by SU(2) rep)",
            "SU(3) DESCENT CONSISTENCY: the descent through the d=12 SU(3) "
            "layer requires consistent group action on S^11; multi-particle "
            "states with non-zero color trace would violate the Adams "
            "tangent-field structure.  PARALLEL TO thm:lefschetz BUT FOR "
            "MULTI-PARTICLE STATES.  STATUS: candidate, not derived.  "
            "Need: a cascade theorem stating 'the d=12 layer descent is "
            "consistent only if sum_{colored} n^{SU(2)} Y vanishes.'",
        ),
        (
            "(III) SU(2)^2 x Y",
            "Sum of V_{14} weights over SU(2)-doublet matter vanishes "
            "(weighted by SU(3) rep)",
            "SU(2) LEFSCHETZ CONSISTENCY: the broken SU(2) at d=13 has a "
            "Lefschetz obstruction (no free Lie group action on S^12); "
            "multi-particle states must respect this obstruction.  "
            "STATUS: candidate, partially derivable from thm:lefschetz "
            "(corollary about no free SU(2) action) but not yet derived "
            "for multi-particle Y traces.",
        ),
        (
            "(IV)  Y^3",
            "Third moment of V_{14} weight distribution vanishes",
            "U(1) DESCENT CUBIC CONSISTENCY: the d=14 descent involves the "
            "cubic structure of J^3 (J^2 = -Id, so J^3 = -J), which "
            "constrains higher moments of the U(1) eigenvalue distribution.  "
            "STATUS: candidate, NOT derivable from existing primitives.  "
            "The cascade has not yet identified a cubic structural "
            "constraint at d=14 that produces sum n_i Y_i^3 = 0. "
            "Need: new cascade structure tying U(1)^3 to a cascade quantity.",
        ),
    ]

    for name, summary, body in candidates:
        print(f"  {name}")
        print(f"    Summary: {summary}")
        print(f"    Status: {body}")
        print()


# ---------------------------------------------------------------------------
# Derivation attempt: what blocks closure of (I) from existing primitives?
# ---------------------------------------------------------------------------

def attempt_grav_y_derivation():
    print("=" * 78)
    print("STEP 2.5: focused derivation attempt for (I) gravitational x Y")
    print("=" * 78)
    print()
    print("Goal: derive sum_i n_i Y_i = 0 cascade-natively, where i runs")
    print("over left-handed Weyl fermions per generation and n_i =")
    print("dim(SU(3)) * dim(SU(2)) is the rep multiplicity.")
    print()
    print("Five candidate routes attempted; each fails on existing primitives.")
    print()

    routes = [
        (
            "(a) Descent-integral well-definedness",
            "Apply U(1)_Y by angle theta to a multi-particle cascade state; "
            "require descent integral to converge.",
            "FAILS: thm:forced-paths case (ii) gives the descent attenuation "
            "as exp(Phi(14)), independent of Y. The descent integrand does "
            "NOT see V_{14} eigenvalues. The 'leading divergence proportional "
            "to sum n_i Y_i' assumed in the original sketch does not exist "
            "in the cascade descent structure -- it would require a fermion "
            "action that couples Y to the integrand. Cascade has only the "
            "scalar action S[phi] = sum (2 alpha)^{-1} (Delta phi)^2 "
            "(Part IVb rem:action-uniqueness); fermion action is the "
            "open question oq:fermion-cascade-action.",
        ),
        (
            "(b) Charge conservation",
            "Require sum_i Q_i = 0 over matter content; combined with "
            "Q = T_3 + Y and T_3 traces vanishing within doublets, this "
            "gives sum n_i Y_i = 0.",
            "FAILS as a derivation: 'charge conservation' in QFT is itself "
            "a consequence of U(1) gauge invariance + anomaly cancellation. "
            "Asserting sum Q = 0 cascade-natively is equivalent to asserting "
            "the conclusion. Not a derivation.",
        ),
        (
            "(c) J trace identity",
            "tr(J) = 0 on R^{14} (J is antisymmetric). If the V_{14} weight "
            "structure inherits this, sum n_i Y_i = 0.",
            "FAILS: J's eigenvalues are uniformly +/- i with multiplicity 7 "
            "each. Restricted to any J-invariant subspace, J still has only "
            "+/- i eigenvalues (no fractional Y values). The J trace identity "
            "does not pin Y values to fractions. (rem:u1-vs-projective item "
            "(2) already established this falsification.)",
        ),
        (
            "(d) Bott periodicity to spacetime (d=14 mirrors d=6)",
            "The cascade gauge window at d in {12, 13, 14} sits one Bott "
            "period after spacetime at d in {4, 5, 6}. If d=14 inherits a "
            "trace identity from d=6 by Bott analogy, sum n_i Y_i = 0 "
            "could follow.",
            "FAILS: d=6 is not a distinguished cascade layer (not in "
            "{d_V, d_0, d_1, d_2, d_gw} = {5, 7, 19, 217, 14}). No identity "
            "at d=6 to mirror. The Bott analogy at d=12 (H^3 from d=4) "
            "gave N_c=3 from spacetime's spatial 3D, but there is no "
            "analogous structural carrier at d=6 to source a trace "
            "identity for d=14.",
        ),
        (
            "(e) Path-tensor consistency",
            "rem:path-tensor's verifier (cascade_path_tensor_product.py) "
            "confirms the SM rep content gives 15 Weyl per generation. If "
            "this consistency forces specific Y values, sum n_i Y_i = 0.",
            "FAILS: the verifier explicitly states 'specific representations "
            "are imported from SM observation' (lines 31-35 of the verifier "
            "docstring). The path-tensor structure is consistent with the "
            "SM Y values but does NOT derive them.",
        ),
    ]

    for label, summary, why_fails in routes:
        print(f"  {label}")
        print(f"    Sketch: {summary}")
        print(f"    Why it fails: {why_fails}")
        print()

    print("-" * 78)
    print("STRUCTURAL CONCLUSION")
    print("-" * 78)
    print()
    print("All five routes share a common failure mode: each anomaly")
    print("condition (I)-(IV) requires summing over multi-particle matter")
    print("content with a specific gauge-anomaly weight function (n_i Y_i,")
    print("n^SU(2) Y_i, n^SU(3) Y_i, n_i Y_i^3).  The cascade's existing")
    print("multi-particle structure (path-tensor + descent paths) does NOT")
    print("yet have a notion of 'sum over matter content with gauge-anomaly")
    print("weight' -- such a notion would be supplied by a cascade fermion")
    print("action coupling matter to the U(1)_Y gauge field.")
    print()
    print("The cascade has a SCALAR action (Part IVb rem:action-uniqueness):")
    print("  S[phi] = sum_d (2 alpha(d))^{-1} (Delta phi)^2")
    print("which derives the alpha(d*)/chi^k correction family.  But this")
    print("is for SCALAR observables, not for multi-fermion gauge anomalies.")
    print()
    print("The FERMION cascade action is an existing open question:")
    print("  oq:fermion-cascade-action (Part IVb)")
    print()
    print("STATUS OF Y-SPECTRUM CLOSURE: the four anomaly conditions")
    print("(I)-(IV) are STRUCTURALLY DOWNSTREAM of oq:fermion-cascade-action.")
    print("They cannot be derived from current cascade primitives, because")
    print("the framework that would formulate gauge anomaly cancellation")
    print("(a fermion field action coupling to U(1)_Y) is itself open.")
    print()
    print("THIS NARROWS THE GAP: any attempt at the Y-spectrum closure")
    print("must FIRST address oq:fermion-cascade-action, then derive the")
    print("anomaly conditions (I)-(IV) from that action by standard")
    print("Fujikawa-style or cascade-internal reasoning.  The Y-spectrum")
    print("gap is not 'shallowly open' but 'downstream of a deeper open")
    print("question already on Part IVb's docket.'")
    print()


# ---------------------------------------------------------------------------
# Algebraic test: do (I)-(IV) + electric-charge anchor pin Y values?
# ---------------------------------------------------------------------------

def test_uniqueness_under_anomaly_constraints():
    print("=" * 78)
    print("STEP 3: do (I)-(IV) + Q_e=-1 uniquely determine Y values?")
    print("=" * 78)
    print()
    print("Given the matter content (Q_L: (3,2), u_R: (3,1), d_R: (3,1),")
    print("L_L: (1,2), e_R: (1,1)) -- a cascade-native input from")
    print("rem:fund-or-trivial + rem:path-tensor -- we have 5 unknowns:")
    print("  Y_QL, Y_uR, Y_dR, Y_LL, Y_eR")
    print()
    print("The four anomaly conditions (I)-(IV) and the electric charge")
    print("anchor Q_e = -1 (i.e. Y_eR = -1 in left-handed Weyl convention,")
    print("or equivalently T_3(eR) + Y_eR = -1) give 5 equations in 5")
    print("unknowns.")
    print()
    print("Standard SM derivation (e.g. Pokorski 'Gauge Field Theories'):")
    print("  - (I), (II), (III), (IV) are not all independent.")
    print("  - Modulo the matter content choice, (I) + (III) [+ Q]")
    print("    suffices to pin Y values modulo overall normalization.")
    print("  - The full set of four overdetermines, but consistently.")
    print()
    print("This script's role is to verify the system is well-posed when")
    print("the matter content is fixed (per rem:fund-or-trivial), not to")
    print("close the cascade-native derivation of the constraints.")
    print()

    # Substitute SM Y values back into anomaly conditions to confirm
    # the system as stated has the SM as its unique solution given matter
    # content + 4 anomaly conditions.

    Y = {p[0]: p[3] for p in SM_GENERATION_LH}
    print("With SM Y values substituted:")
    print(f"  Y_QL  = {Y['Q_L']}")
    print(f"  Y_uR^c = {Y['u_L^c']}  (so Y_uR = {-Y['u_L^c']})")
    print(f"  Y_dR^c = {Y['d_L^c']}  (so Y_dR = {-Y['d_L^c']})")
    print(f"  Y_LL  = {Y['L_L']}")
    print(f"  Y_eR^c = {Y['e_L^c']}  (so Y_eR = {-Y['e_L^c']})")
    print()


# ---------------------------------------------------------------------------
# Open question summary
# ---------------------------------------------------------------------------

def open_question_summary():
    print("=" * 78)
    print("STEP 4: the open question, restated precisely")
    print("=" * 78)
    print()
    print("Identify cascade-internal constraints (I'), (II'), (III'), (IV')")
    print("such that:")
    print()
    print("  (a) Each (X') is forced by cascade structure -- descent paths,")
    print("      Lefschetz/hairy-ball obstructions, J-action on C^7, or")
    print("      path-tensor compatibility -- WITHOUT importing QFT triangle")
    print("      diagrams or other semiclassical machinery.")
    print()
    print("  (b) The system {(I'), (II'), (III'), (IV')} together with one")
    print("      electric-charge anchor has the SM Y spectrum as its unique")
    print("      solution, given the matter content fixed by rem:fund-or-trivial")
    print("      and rem:path-tensor.")
    print()
    print("Closing this would upgrade the d=14 entry of rem:fund-or-trivial")
    print("from 'partially closed (dimension forced)' to 'closed (dimension")
    print("and weights forced)'.")
    print()
    print("STATUS: open.  The cascade has not yet identified the cascade-")
    print("native versions of (I)-(IV).  Candidates are recorded above")
    print("(STEP 2); each is a structural conjecture, not a theorem.")
    print()
    print("Until closed, the cascade's claim of zero free parameters is")
    print("precise about predictions but not about per-particle V_{14}")
    print("weight assignment.  See CLAUDE.md 'Known Quantitative Issues',")
    print("matter-rep / hypercharge gap.")
    print()


def main() -> int:
    print("=" * 78)
    print("CASCADE ANOMALY FRAMEWORK: scaffolding for d=14 Y-spectrum closure")
    print("=" * 78)
    print()
    verify_sm_anomalies()
    report_cascade_candidates()
    attempt_grav_y_derivation()
    test_uniqueness_under_anomaly_constraints()
    open_question_summary()
    return 0


if __name__ == "__main__":
    sys.exit(main())
