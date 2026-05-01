#!/usr/bin/env python3
"""
Attempt: derive the cascade Green's function on S^12 to fix the exact
normalization of c_2 = 1/chi in V(theta) = (1/2) cos^2(theta).

CURRENT STATE
=============
After commit d88d459, both (C3) and (C4) of rem:V-cos2-derivation are
upgraded to leading-order structural arguments.  The remaining open
piece: exact normalization of c_2 from the cascade Green's function on
S^12.

THIS SCRIPT
===========
Two attempts at the Green's function:

(A) Standard spherical Laplacian Green's function on S^12.
(B) Cascade-scalar-action embedding of S^12 dynamics.

HONEST PRE-RESULT
=================
Both attempts fail to give a clean cascade-structural derivation of
c_2 = 1/chi at the exact normalization level.  The cascade truly needs
oq:fermion-gauge-action's gauge-coupled action computation for the
exact normalization.  This script documents the failed attempts so the
gap is precisely characterised.

ATTEMPT (A): standard spherical Laplacian
==========================================
Source: pair of antipodal delta-functions on S^12 with strength chi = 2:
  s(theta) = delta(theta) + delta(theta - pi)

L=2 source amplitude:
  s_2 = int s(theta) Y_2(theta) dOmega = Y_2(0) + Y_2(pi) = 2 Y_2(0)
      = 2 * (1 - 1/13) = 24/13

Spherical Laplacian eigenvalue at L=2 on S^12 (n=12):
  lambda_2 = L(L + n - 1) = 2 * 13 = 26

Green's function L=2 response:
  V_L=2(theta) = (s_2 / lambda_2) Y_2(theta) = (24/(13*26)) Y_2(theta)
              = (12/169) Y_2(theta)

V(0) from L=2 only = (12/169) * Y_2(0) = (12/169) * (12/13)
                    = 144/2197 ~= 0.0656

Cascade requires V(0) = 1/2 = 0.5.

Discrepancy: factor 0.0656 / 0.5 = 0.131 ~= 1/7.6.

The standard spherical Laplacian gives V(0) ~ 7.6x SMALLER than cascade.
This means the cascade has a DIFFERENT effective Green's function
normalization on S^12.

ATTEMPT (B): cascade scalar action embedding
============================================
Combine cascade lattice action S = sum_d (1/2alpha(d))(Delta phi)^2 with
spherical kinetic int |nabla_S^12 phi|^2.

In cascade units where cascade kinetic is normalized to 1, the spherical
kinetic coefficient is 1/(alpha(13) * v^2).

L=2 effective mass squared on S^12:
  m_eff^2 = (Laplacian eigenvalue) * (kinetic coefficient)
          = 26 * alpha(13) * v^2  (cascade scalar units)

Compare to required m_H^2 = pi^2 g^2 v^2/16:

  26 * alpha(13) = pi^2 g^2/16  (need to check)

With g^2 = 4 pi alpha(13) (cascade-SM convention):
  26 alpha(13) = pi^2 * 4 pi alpha(13) / 16 = pi^3 alpha(13)/4
  26 = pi^3/4 = 7.75
  FALSE: 26 != 7.75

The naive cascade-scalar embedding does NOT give a consistent
normalisation for the L=2 mode mass.  This confirms the cascade
Higgs sector at d=13 needs the full gauge-coupled action
(oq:fermion-gauge-action), not just the scalar action.

WHAT THIS SCRIPT ACHIEVES
==========================
  1. Quantifies the discrepancy between standard spherical Laplacian
     and cascade requirement (factor ~7.6 in V(0)).
  2. Confirms that the cascade scalar action alone does NOT give
     consistent S^12 dynamics at d=13.
  3. Documents the gap precisely: cascade Higgs Green's function on
     S^12 requires gauge-coupled action computation (oq:fermion-gauge-
     action).

The result is HONEST NEGATIVE for first-principles exact derivation.
The leading-order structural arguments of rem:V-cos2-derivation
(C3 quadrupolar truncation; C4 chirality theorem) remain the cleanest
cascade-internal grounding currently available.
"""

from __future__ import annotations

import math


def Y2_zonal(theta: float, n: int) -> float:
    return math.cos(theta)**2 - 1.0/(n+1)


def main():
    print("=" * 78)
    print("Cascade Green's function on S^12: first-principles attempts")
    print("=" * 78)
    print()

    n = 12  # sphere dimension at d=13
    chi = 2

    # ---- Attempt (A): standard spherical Laplacian ----
    print("ATTEMPT (A): standard spherical Laplacian on S^12")
    print("-" * 78)
    s_2 = 2 * Y2_zonal(0, n)  # source amplitude at L=2
    lambda_2 = 2 * (2 + n - 1)  # = L(L + n - 1) = 2 * 13 = 26
    V_L2_at_0 = (s_2 / lambda_2) * Y2_zonal(0, n)
    print(f"  Source: pair of antipodal delta-functions with strength chi = {chi}")
    print(f"  L=2 source amplitude s_2 = 2 Y_2(0) = 2 * (1 - 1/13) = {s_2:.6f}")
    print(f"  Spherical Laplacian eigenvalue at L=2: lambda_2 = L(L+n-1) = {lambda_2}")
    print()
    print(f"  Green's function response V_L=2(theta) = (s_2 / lambda_2) Y_2(theta)")
    print(f"  V(0) from L=2 only = (s_2/lambda_2) * Y_2(0) = ({s_2:.4f}/{lambda_2}) * {Y2_zonal(0,n):.4f}")
    print(f"                     = {V_L2_at_0:.6f}")
    print()
    print(f"  Cascade requires V(0) = 1/chi = 1/{chi} = {1/chi:.4f}")
    print(f"  Discrepancy: standard Laplacian / cascade = {V_L2_at_0/(1/chi):.4f} ~= 1/{1/(V_L2_at_0/(1/chi)):.2f}")
    print()
    print(f"  CONCLUSION: standard spherical Laplacian gives V(0) ~7.6x SMALLER")
    print(f"  than cascade.  Cascade has different effective normalisation on S^12.")
    print()

    # ---- Attempt (B): cascade-scalar embedding ----
    print("ATTEMPT (B): cascade-scalar embedding (S^12 + lattice combined)")
    print("-" * 78)
    print(f"  Cascade scalar action: S = sum_d (1/2 alpha(d))(Delta phi)^2")
    print(f"  Spherical kinetic on S^12: int |nabla phi|^2 dOmega")
    print()
    print(f"  In cascade units (cascade kinetic = 1), spherical kinetic coefficient")
    print(f"  = 1/(alpha(13) v^2).")
    print(f"  L=2 effective mass^2 = lambda_2 * coefficient = 26 alpha(13) v^2.")
    print()
    print(f"  Required m_H^2 = pi^2 g^2 v^2/16 with g^2 = 4 pi alpha(13):")
    print(f"  26 alpha(13) =? pi^3 alpha(13)/4")
    print(f"  26 =? pi^3/4 = {math.pi**3 / 4:.4f}")
    print(f"  FALSE: 26 != {math.pi**3/4:.4f}")
    print()
    print(f"  CONCLUSION: cascade scalar action alone does NOT give consistent")
    print(f"  S^12 dynamics for the Higgs sector at d=13.  Confirms that")
    print(f"  oq:fermion-gauge-action is needed.")
    print()

    # ---- Status ----
    print("STATUS")
    print("-" * 78)
    print(f"  Both attempts at first-principles cascade Green's function on S^12")
    print(f"  FAIL to give the exact normalisation c_2 = 1/chi.")
    print()
    print(f"  The cascade Higgs sector at d=13 is governed by a Green's function")
    print(f"  that is NOT the standard spherical Laplacian (off by factor 7.6) and")
    print(f"  NOT the naive cascade-scalar-on-sphere embedding (inconsistent).")
    print()
    print(f"  The exact normalisation requires the cascade gauge-coupled action")
    print(f"  computation (downstream of oq:fermion-gauge-action).  Without that,")
    print(f"  the leading-order structural arguments of rem:V-cos2-derivation")
    print(f"  ((C3) quadrupolar truncation; (C4) chirality theorem) remain the")
    print(f"  cleanest cascade-internal grounding.")
    print()
    print(f"  The first-principles dig has reached the boundary of what's tractable")
    print(f"  without the gauge-coupled action.  No further progress is possible")
    print(f"  on the exact Higgs Green's function from purely cascade-scalar")
    print(f"  primitives.")
    print()


if __name__ == "__main__":
    main()
