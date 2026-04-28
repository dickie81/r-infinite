#!/usr/bin/env python3
"""
Audit Section 7: Riemannian structure of round S^{d-1} at cascade layers.

IGN entries to investigate:
  7.3  Scalar curvature R_scal = (d-1)(d-2)
  7.4  Lichnerowicz formula slashed{D}^2 = nabla^* nabla + R/4
  7.5  Conformal Killing spinors

Per the audit, 7.4 is noted as "Sphere-Dirac route already tested" --
referencing audit entry 4.6 ($\hat A$-genus = 0 on $S^{2n}$ rules out
Dirac-operator interpretation, USED in Notebook Rem `no-dirac-route`).

So 7.4 is correctly IGN by structural exclusion.  This script focuses on
7.3 (scalar curvature) and 7.5 (Conformal Killing spinors) for any
cascade application.
"""

from __future__ import annotations

import math
import sys

from scipy.special import gammaln  # type: ignore[import-not-found]


def R(d: int) -> float:
    return math.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def alpha(d: int) -> float:
    return R(d) ** 2 / 4


def main() -> int:
    print("=" * 78)
    print("AUDIT SECTION 7: RIEMANNIAN CURVATURE STRUCTURE")
    print("=" * 78)
    print()

    distinguished = [4, 5, 7, 12, 13, 14, 19, 21, 217]

    # ----------------------------------------------------------------
    # 7.3 Scalar curvature R_scal = (d-1)(d-2)
    # ----------------------------------------------------------------
    print("-" * 78)
    print("7.3 SCALAR CURVATURE R_scal = (d-1)(d-2) at distinguished layers")
    print("-" * 78)
    print()
    print(f"{'d':>4}  {'sphere':>8}  {'R_scal':>10}  {'R_scal/(d-1)':>14}  "
          f"{'R_scal*alpha(d)':>16}")
    print("-" * 78)
    for d in distinguished:
        sphere = f"S^{d-1}"
        R_scal = (d - 1) * (d - 2)
        per_d = R_scal / (d - 1) if d > 1 else 0
        prod = R_scal * alpha(d)
        print(f"{d:>4}  {sphere:>8}  {R_scal:>10}  {per_d:>14.4f}  {prod:>16.6f}")
    print()
    print("Observation: R_scal grows as d^2 quadratically, while alpha(d) decays")
    print("as 1/d.  Their product R_scal * alpha(d) -> (d-1)(d-2)/(2(d+1)) ~ d/2.")
    print()
    print("No closed-form cascade match for R_scal; the formula (d-1)(d-2) is the")
    print("trace of the Ricci tensor (d-2)g via R_scal = trace = (d-1)(d-2).")
    print("Audit entry 7.2 (Ricci = (d-2)g) is USED implicitly in Part III §14;")
    print("7.3 is just trace(Ricci), so already implicit.")
    print()
    print("Verdict: 7.3 should move from IGN to USED implicitly via 7.2 (already")
    print("USED).  The scalar curvature is the trace of the Ricci tensor and")
    print("doesn't add new structure beyond what 7.2 already provides.")
    print()

    # ----------------------------------------------------------------
    # 7.4 Lichnerowicz formula
    # ----------------------------------------------------------------
    print("-" * 78)
    print("7.4 LICHNEROWICZ FORMULA slashed{D}^2 = nabla^* nabla + R/4")
    print("-" * 78)
    print()
    print("On S^{d-1}: slashed{D}^2 has spectrum (k + (d-1)/2)^2 for k=0,1,2,...")
    print("Both terms of Lichnerowicz are computable, so the formula is exact.")
    print()
    print("Cascade application requires sphere-Dirac operator, which is RULED OUT")
    print("by audit entry 4.6: hat A-genus on S^{2n} vanishes, so no spinor index")
    print("theorem identity can come from sphere-Dirac.  Notebook Rem 'no-dirac-")
    print("route' (Part IVb) explicitly forbids this route.")
    print()
    print("Verdict: 7.4 IGN by STRUCTURAL EXCLUSION (sphere-Dirac route forbidden")
    print("by 4.6 hat A-genus argument).  Audit should reflect this -- 7.4 is")
    print("not 'just unused', it is excluded.")
    print()

    # ----------------------------------------------------------------
    # 7.5 Conformal Killing spinors
    # ----------------------------------------------------------------
    print("-" * 78)
    print("7.5 CONFORMAL KILLING SPINORS")
    print("-" * 78)
    print()
    print("S^{d-1} admits Killing spinors of both chiralities.  Their existence")
    print("is part of the spin structure on the sphere (audit 5.5).")
    print()
    print("Cascade application: same as 7.4 -- requires sphere-Dirac, which is")
    print("structurally excluded.")
    print()
    print("Verdict: 7.5 IGN by structural exclusion (parallel to 7.4).")
    print()

    # ----------------------------------------------------------------
    # SUMMARY
    # ----------------------------------------------------------------
    print("=" * 78)
    print("SECTION 7 SUMMARY")
    print("=" * 78)
    print()
    print("Three IGN entries resolved:")
    print("  7.3 Scalar curvature (d-1)(d-2): trace of Ricci (USED in 7.2)")
    print("                                   --> reclassify as USED implicitly")
    print("  7.4 Lichnerowicz formula:        sphere-Dirac route excluded by 4.6")
    print("                                   --> IGN (structural exclusion)")
    print("  7.5 Conformal Killing spinors:   sphere-Dirac route excluded by 4.6")
    print("                                   --> IGN (structural exclusion)")
    print()
    print("All three entries resolve cleanly: 7.3 is implicitly used (trace of")
    print("an already-used tensor), 7.4-7.5 are structurally excluded by the")
    print("cascade's no-Dirac-route commitment (4.6 hat A-genus argument).")
    print()
    print("This pattern matches Section 2 (sphere-Laplacian, structurally not")
    print("invoked) and Section 11 (Gamma identities, off-tower or numerical-")
    print("only): each IGN entry has a specific structural reason for non-use.")
    print()
    print("Audit hygiene: the 'IGN' status across sections divides into:")
    print("  (a) USED implicitly via a parent entry (e.g., 7.3 via 7.2)")
    print("  (b) Structurally excluded by an axiom commitment (7.4-7.5 via 4.6)")
    print("  (c) Off-tower / off-cascade-primitive (11.4, 11.5b, 11.8)")
    print("  (d) Operates on a d.o.f. cascade doesn't include (2.7, 2.8)")
    print()
    print("None so far has revealed a missed structural opportunity beyond the")
    print("Legendre duplication Lemma (PR #96).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
