#!/usr/bin/env python3
"""
Audit Section 2: sphere-Laplacian and heat-kernel structure on cascade layers.

Audit IGN entries to investigate:
  2.7  Heat kernel asymptotics on S^{d-1}
  2.8  Laplacian eigenvalues lambda_ell = ell * (ell + d - 2) on S^{d-1}

These give per-layer spectral data not currently invoked by the cascade.
Question: does this spectral data correspond to any cascade quantity?

Cascade primitives at each layer d:
  R(d) = Gamma((d+1)/2)/Gamma((d+2)/2)         -- slicing ratio
  alpha(d) = R(d)^2 / 4                          -- compliance (Part IVb)
  Omega_{d-1} = 2 pi^{d/2} / Gamma(d/2)          -- sphere area
  R_scal(d) = (d-1)(d-2)                         -- scalar curvature of S^{d-1}

Sphere-Laplacian spectral data on S^{d-1}:
  Eigenvalues: lambda_ell = ell * (ell + d - 2),  ell = 0, 1, 2, ...
  Multiplicities: m_ell = (2 ell + d - 2)/(ell + d - 2) * binomial(ell+d-2, ell)
  First non-zero eigenvalue (gap): lambda_1 = d - 1
  Heat kernel: Tr e^{-t Delta} = sum_ell m_ell e^{-t lambda_ell}
"""

from __future__ import annotations

import math
import sys

from scipy.special import gammaln  # type: ignore[import-not-found]


def R(d: int) -> float:
    return math.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def alpha(d: int) -> float:
    return R(d) ** 2 / 4


def omega(d: int) -> float:
    """Surface area of S^{d-1} = 2 pi^{d/2} / Gamma(d/2)."""
    return 2 * math.pi ** (d / 2.0) / math.exp(gammaln(d / 2.0))


def lambda_ell(ell: int, d: int) -> int:
    """Eigenvalue of -Delta on S^{d-1}: ell(ell + d - 2)."""
    return ell * (ell + d - 2)


def mult_ell(ell: int, d: int) -> int:
    """Multiplicity of lambda_ell on S^{d-1}."""
    if ell == 0:
        return 1
    if d == 1:
        return 2 if ell > 0 else 1
    # m_ell = (2 ell + d - 2)/(ell + d - 2) * C(ell + d - 2, ell)
    from math import comb
    return (2 * ell + d - 2) * comb(ell + d - 3, ell - 1) // (ell + d - 2) * 1 \
        if False else \
        ((2 * ell + d - 2) * comb(ell + d - 3, ell - 1)) // ell  # standard form


def main() -> int:
    print("=" * 78)
    print("AUDIT SECTION 2.7-2.8: SPHERE-LAPLACIAN STRUCTURE AT CASCADE LAYERS")
    print("=" * 78)
    print()

    distinguished = [4, 5, 7, 12, 13, 14, 19, 21, 217]

    # -----------------------------------------------------------------
    # Pass 1: tabulate first few eigenvalues at distinguished layers
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 1: Sphere-Laplacian spectrum at distinguished cascade layers")
    print("-" * 78)
    print()
    print(f"{'d':>4}  {'sphere':>10}  {'gap lambda_1':>14}  "
          f"{'lambda_2':>10}  {'lambda_3':>10}  {'lambda_4':>10}")
    print("-" * 78)
    for d in distinguished:
        sphere = f"S^{d-1}"
        gap = lambda_ell(1, d)
        l2 = lambda_ell(2, d)
        l3 = lambda_ell(3, d)
        l4 = lambda_ell(4, d)
        print(f"{d:>4}  {sphere:>10}  {gap:>14}  {l2:>10}  {l3:>10}  {l4:>10}")
    print()
    print("Observation: gap lambda_1 = d - 1 grows linearly with d.")
    print()

    # -----------------------------------------------------------------
    # Pass 2: compare spectral gap to cascade quantities
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 2: Spectral gap vs cascade quantities")
    print("-" * 78)
    print()
    print(f"{'d':>4}  {'gap = d-1':>10}  {'1/alpha(d)':>14}  "
          f"{'gap*alpha':>14}  {'4/R(d)^2':>14}  {'(d-1)*R(d)^2/4':>16}")
    print("-" * 78)
    for d in distinguished:
        gap = d - 1
        a = alpha(d)
        ga = gap * a
        # 1/alpha(d) = 4/R(d)^2
        inv_alpha = 4 / R(d) ** 2
        gap_alpha = (d - 1) * R(d) ** 2 / 4
        print(f"{d:>4}  {gap:>10}  {inv_alpha:>14.4f}  {ga:>14.6f}  "
              f"{inv_alpha:>14.4f}  {gap_alpha:>16.6f}")
    print()
    print("Observation: 1/alpha(d) ~ 2(d+1) approx (since R(d)^2 ~ 2/(d+1)),")
    print("which is roughly 2(gap + 2).  Linear scaling of both, but distinct ratios.")
    print()

    # -----------------------------------------------------------------
    # Pass 3: check (d-1)*alpha(d) -- is it a cascade quantity?
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 3: Test gap * alpha(d) for any closed form")
    print("-" * 78)
    print()
    print(f"{'d':>4}  {'gap*alpha':>14}  {'(d-1)/(d+1)':>14}  {'note':>30}")
    print("-" * 78)
    for d in distinguished:
        ga = (d - 1) * alpha(d)
        ratio = (d - 1) / (d + 1)
        note = ""
        # alpha(d) ~ 1/(2(d+1)) at leading order, so (d-1) * alpha(d) ~ (d-1)/(2(d+1))
        # check this
        approx = (d - 1) / (2 * (d + 1))
        if abs(ga - approx) / max(abs(ga), 1e-30) < 0.1:
            note = "approx (d-1)/(2(d+1))"
        print(f"{d:>4}  {ga:>14.6f}  {ratio:>14.6f}  {note:>30}")
    print()
    print("(d-1) * alpha(d) is approximately (d-1)/(2(d+1)) at leading order,")
    print("with sub-leading corrections from R(d) Stirling expansion.  No exact")
    print("match to any cascade quantity.")
    print()

    # -----------------------------------------------------------------
    # Pass 4: heat kernel asymptotics
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 4: Heat-kernel coefficients at distinguished layers")
    print("-" * 78)
    print()
    print("Tr e^{-t Delta} on S^{d-1} expands as a_0 + a_1 t + a_2 t^2 + ... where")
    print("a_n is an integral of curvature invariants.  For the round S^{d-1} of")
    print("scalar curvature R_scal = (d-1)(d-2):")
    print("  a_0 = Omega_{d-1}                  (volume)")
    print("  a_1 = R_scal / 6 * Omega_{d-1}     (scalar curvature term)")
    print()
    print(f"{'d':>4}  {'sphere':>8}  {'Omega_{d-1}':>14}  {'R_scal':>10}  "
          f"{'a_1':>14}")
    print("-" * 78)
    for d in distinguished:
        sphere = f"S^{d-1}"
        Om = omega(d)
        R_scal = (d - 1) * (d - 2)
        a1 = R_scal * Om / 6
        print(f"{d:>4}  {sphere:>8}  {Om:>14.6e}  {R_scal:>10}  {a1:>14.6e}")
    print()
    print("Heat-kernel coefficients are concrete numbers per layer.  Comparison")
    print("to cascade quantities:")
    print()
    print(f"{'d':>4}  {'a_0 = Omega_{d-1}':>16}  {'1/alpha(d)':>12}  "
          f"{'a_0 * alpha(d)':>14}")
    print("-" * 78)
    for d in distinguished:
        Om = omega(d)
        a = alpha(d)
        prod = Om * a
        print(f"{d:>4}  {Om:>16.6e}  {1/a:>12.4f}  {prod:>14.6e}")
    print()
    print("Omega_{d-1} * alpha(d) decreases super-exponentially in d (as Omega")
    print("itself is super-exponential in d via Gamma).  No clean cascade match.")
    print()

    # -----------------------------------------------------------------
    # CONCLUSION
    # -----------------------------------------------------------------
    print("=" * 78)
    print("CONCLUSION: SPHERE-LAPLACIAN STRUCTURE")
    print("=" * 78)
    print()
    print("Tested whether sphere-Laplacian eigenvalues lambda_ell = ell(ell+d-2)")
    print("or heat-kernel coefficients on S^{d-1} match cascade quantities.")
    print()
    print("Findings:")
    print("  - Spectral gap d-1 has the right scaling (linear in d) but no exact")
    print("    cascade match.  alpha(d) ~ 1/(2(d+1)) is at the same scale but")
    print("    distinct ratio.")
    print("  - Heat-kernel a_0 = Omega_{d-1} is already a cascade primitive (USED).")
    print("    a_1 = R_scal Omega/6 mixes scalar curvature with sphere area; no")
    print("    closed-form match to any cascade quantity.")
    print("  - No structural identity emerges from sphere-Laplacian spectrum at")
    print("    distinguished layers.")
    print()
    print("Why this is consistent with the cascade design:")
    print("  The cascade lives on the INTEGER TOWER {0, 1, ..., 217}, with")
    print("  fields phi(d) defined per layer.  The sphere-Laplacian acts on")
    print("  functions on S^{d-1} -- a CONTINUOUS spatial structure at each")
    print("  layer.  These are orthogonal degrees of freedom.")
    print()
    print("  The cascade's discrete tower Laplacian (Part IVb) is the cascade-")
    print("  intrinsic differential operator.  The continuous sphere Laplacian")
    print("  is a SEPARATE structure that the cascade's scalar action does not")
    print("  invoke -- and inviting it would require additional structure")
    print("  (a tower x sphere PDE).")
    print()
    print("Verdict: 2.7-2.8 are correctly IGN.  The sphere-Laplacian eigenvalues")
    print("are cascade-FORCED but operate on a degree of freedom (spatial fields")
    print("per layer) that the cascade scalar action does not include.  The IGN")
    print("status reflects a structural CHOICE of the cascade (1D tower fields,")
    print("not tower x sphere fields), not a missed opportunity.")
    print()
    print("Audit update: 2.7 and 2.8 should move from 'IGN, not invoked' to")
    print("'IGN, structurally not invoked: cascade scalar action lives on the")
    print("integer tower, not on tower x sphere'.  This is austerity-clean.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
