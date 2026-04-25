#!/usr/bin/env python3
"""
Cascade running coupling as Abelian Wilson holonomy.

CLAIM.  Under Option 2 / Reading G of cascade-path-state-hilbert-derivation1.md,
the cascade's existing running-coupling formula
    alpha_s(M_Z) = alpha_GUT * exp(Phi(12))
(Part IVa Theorem forced-paths, Part IVb strong-coupling theorem)
IS an Abelian Wilson holonomy of an explicit connection 1-form
A(d) = p(d) along the cascade descent path d = 5..12.

The connection is cascade-internal:
    A(d) = p(d) = (1/2) psi((d+1)/2) - (1/2) ln(pi)
where psi is the digamma function (Part IVa Definition cascade-potential).

The Wilson holonomy along path gamma = [d_a, d_b]:
    W_gamma = P-exp(integral_gamma A) = exp(sum_{d=d_a}^{d_b} p(d))
            = exp(Phi(d_b) - Phi(d_a - 1))

For gauge-anchored observables (Part IVa Theorem forced-paths case ii):
    log(Q_obs/Q_bare) = Phi(d_B)
which is the log Wilson holonomy along path d = 5..d_B.

This verifier:
  1. Computes p(d) and Phi(d) from cascade's digamma definition.
  2. Computes the Wilson holonomy on paths d=5..12 (SU(3)), d=5..13 (SU(2)),
     d=5..14 (U(1)).
  3. Reports: the cascade's running coupling formula IS an Abelian Wilson
     line in the multiplicative scaling group (R^+ or C^*).

WHAT THIS DELIVERS.

The cascade's existing perturbative running formula is a Wilson holonomy.
The connection 1-form A(d) = p(d) is cascade-internal, derived from the
slicing recurrence (digamma function = log Gamma' / Gamma reflects the
sphere-area decay rate).

WHAT THIS DOES NOT DELIVER.

Non-Abelian gauge dynamics (gluon self-coupling, confinement, instantons,
non-perturbative effects).  The cascade's Wilson line is in the Abelian
multiplicative group, not in the full SU(3) Lie group.  Adams' theorem
provides the SU(3) ALGEBRA at d=12 (3 vector fields on S^11) but the
cascade's path-Wilson-line at the perturbative level reduces to its
Abelian (trace / character) projection.

The non-Abelian extension would require a cascade-internal construction
of the SU(3) connection at d=12 with explicit Lie-algebra-valued 1-form
and curvature.  This is open under Option 2 and represents the natural
next step beyond perturbative running.
"""
import os
import sys

import numpy as np
from scipy.special import digamma

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def p_cascade(d):
    """Cascade slicing potential: p(d) = (1/2) psi((d+1)/2) - (1/2) ln(pi).

    Part IVa Definition cascade-potential.
    """
    return 0.5 * digamma((d + 1) / 2) - 0.5 * np.log(np.pi)


def Phi_cascade(d):
    """Cumulative cascade potential: Phi(d) = sum_{d'=5}^d p(d')."""
    return sum(p_cascade(dd) for dd in range(5, d + 1))


def wilson_holonomy(path):
    """Abelian Wilson holonomy with connection A(d) = p(d) along path.

    W_gamma = exp(integral_gamma A) = exp(sum_{d in path} p(d))
    """
    return np.exp(sum(p_cascade(d) for d in path))


def main():
    print("=" * 78)
    print("CASCADE RUNNING COUPLING AS ABELIAN WILSON HOLONOMY")
    print("=" * 78)
    print()
    print("Claim: alpha_s(M_Z) = alpha_GUT * exp(Phi(12))")
    print("       IS the Abelian Wilson holonomy of connection A(d) = p(d)")
    print("       along the cascade descent path d = 5..12.")
    print()
    print("Connection 1-form:  A(d) = p(d) = (1/2) psi((d+1)/2) - (1/2) ln(pi)")
    print("Wilson holonomy:    W_gamma = exp(sum_{d in gamma} A(d))")
    print()

    # === Step 1: per-layer potential ===
    print("=" * 78)
    print("Step 1: per-layer cascade potential p(d) for d = 5..14")
    print("=" * 78)
    print()
    print(f"{'d':>4s}  {'p(d) = A(d)':>14s}  {'exp(p(d)) = exp(A(d))':>22s}")
    print("-" * 60)
    for d in range(5, 15):
        p = p_cascade(d)
        print(f"{d:>4d}  {p:>14.10f}  {np.exp(p):>22.10f}")
    print()

    # === Step 2: cumulative potential and Wilson line ===
    print("=" * 78)
    print("Step 2: cumulative Phi(d) and Wilson line exp(Phi(d))")
    print("=" * 78)
    print()
    print(f"{'d_B':>4s}  {'Phi(d_B)':>14s}  {'W = exp(Phi(d_B))':>22s}  {'Gauge group':>14s}")
    print("-" * 70)
    gauge_groups = {12: "SU(3)", 13: "SU(2)", 14: "U(1)"}
    for d_B in range(5, 22):
        Phi = Phi_cascade(d_B)
        W = np.exp(Phi)
        g = gauge_groups.get(d_B, "")
        print(f"{d_B:>4d}  {Phi:>14.10f}  {W:>22.10f}  {g:>14s}")
    print()

    # === Step 3: cascade running coupling formula recovery ===
    print("=" * 78)
    print("Step 3: cascade running coupling = Wilson holonomy")
    print("=" * 78)
    print()

    # alpha_s(M_Z) prediction: cascade gives alpha_s = alpha_GUT * exp(Phi(12))
    # alpha_GUT is the unification coupling (typical SUSY GUT value ~ 1/24-1/25)
    # The cascade's exp(Phi(12)) gives the running factor; multiplied by
    # alpha_GUT to get alpha_s at M_Z.
    Phi_12 = Phi_cascade(12)
    W_12 = np.exp(Phi_12)
    print(f"  Cascade SU(3) descent path: d = 5..12")
    print(f"  Phi(12) = {Phi_12:.10f}")
    print(f"  exp(Phi(12)) = {W_12:.10f}")
    print(f"  This is the Wilson line W_{{[5,12]}} of A = p(d).")
    print()
    print(f"  alpha_s(M_Z) = alpha_GUT * W_{{[5,12]}}")
    print(f"              = alpha_GUT * {W_12:.6f}")
    print()

    # Same for SU(2) and U(1)
    Phi_13 = Phi_cascade(13)
    Phi_14 = Phi_cascade(14)
    W_13 = np.exp(Phi_13)
    W_14 = np.exp(Phi_14)
    print(f"  SU(2) descent path: d = 5..13")
    print(f"  Phi(13) = {Phi_13:.10f}, W_{{[5,13]}} = exp(Phi(13)) = {W_13:.10f}")
    print()
    print(f"  U(1) descent path: d = 5..14")
    print(f"  Phi(14) = {Phi_14:.10f}, W_{{[5,14]}} = exp(Phi(14)) = {W_14:.10f}")
    print()

    # === Step 4: structural interpretation ===
    print("=" * 78)
    print("Step 4: structural interpretation under Option 2")
    print("=" * 78)
    print()
    print("Under Option 2 / Reading G:")
    print()
    print("  (a) The cascade's running coupling formula is an Abelian Wilson")
    print("      holonomy.  The connection 1-form is A(d) = p(d), derived")
    print("      cascade-internally from the digamma function reflecting the")
    print("      sphere-area decay rate.")
    print()
    print("  (b) The Wilson line is in the multiplicative scaling group R^+")
    print("      (or C^* if we keep the cascade's J phase).")
    print()
    print("  (c) The non-Abelian gauge group (SU(3) at d=12, SU(2) at d=13,")
    print("      U(1) at d=14) acts at the GAUGE LAYER itself.  Adams' theorem")
    print("      gives the rank rho(d)-1 of the gauge group.")
    print()
    print("  (d) The full non-Abelian Wilson line W in SU(N) gauge group")
    print("      reduces to the Abelian running upon taking |trace|^2 in the")
    print("      fundamental representation.  Cascade's existing formula is")
    print("      this trace-projected (Abelian) running.")
    print()
    print("WHAT IS DERIVED at this stage:")
    print("  - Cascade's existing alpha_s formula IS a Wilson holonomy with")
    print("    explicit connection A(d) = p(d).")
    print("  - The connection is cascade-internal (from slicing structure).")
    print("  - The path d=5..d_B is forced by gauge layer placement.")
    print()
    print("WHAT IS NOT DERIVED (still open under Option 2):")
    print("  - Full non-Abelian Wilson line in SU(3), SU(2), U(1).")
    print("    Adams gives the gauge ALGEBRA at gauge layers; the path-")
    print("    ordered connection in the algebra is not constructed cascade-")
    print("    internally.")
    print("  - Non-perturbative gauge dynamics (gluon self-coupling,")
    print("    confinement, instantons).  These would require the full")
    print("    non-Abelian Wilson line, not the Abelian reduction.")
    print()
    print("CONCLUSION.  Follow-up 2 partially succeeds: the cascade's existing")
    print("running coupling IS already a Wilson holonomy under Option 2's")
    print("path-state interpretation.  The connection 1-form A(d) = p(d) is")
    print("cascade-internal, and the cascade-potential formula Phi(d) = sum p(d')")
    print("is exactly the log holonomy.")
    print()
    print("This re-interpretation does not produce new predictions but provides")
    print("a gauge-theoretic structural meaning to the cascade's existing")
    print("perturbative running formulae.  The deeper (non-perturbative) gauge")
    print("dynamics is not delivered by this perturbative Abelian projection.")


if __name__ == "__main__":
    main()
