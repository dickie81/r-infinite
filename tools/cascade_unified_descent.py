#!/usr/bin/env python3
"""
Verify that Part I's three cosmological-constant corrections are all
instances of Part 0's slicing recurrence evaluated at specific cascade
layers.

Part 0's slicing recurrence (Part 0 §3):
    Omega_d = Omega_{d-1} * sqrt(pi) * R(d-1)
    R(d) = Gamma((d+1)/2) / Gamma((d+2)/2)

Backward step:
    Omega_{d-1} / Omega_d = 1 / (sqrt(pi) * R(d-1))

This script shows:
  1. 3D projection factor Omega_2/Omega_3 = 2/pi is one backward slicing
     step at d=3: 1 / (sqrt(pi) * R(2)).
  2. Host frame factor Omega_5/Omega_7 = 3/pi is two backward slicing
     steps (from d=7 through d=6 to d=5): 1 / (pi * R(5) * R(6)).
  3. (Omega_5/Omega_7)^2 = 9/pi^2 is two such host-frame factors, one
     per threshold sphere area passing through.
  4. The full Part I formula rho_Lambda / M_Pl,red^4
     = 18 Omega_19 Omega_217 / pi^3 is the single product.

All three "separate" corrections in Part I §3 are the same operation
(Part 0 slicing recurrence) applied at different cascade layers. This
closes the CLAUDE.md-flagged residual structural task for Part I.
"""

import numpy as np
from scipy.special import gamma as gamma_func


def R(d):
    """Part 0 slicing recurrence coefficient: R(d) = Gamma((d+1)/2)/Gamma((d+2)/2)."""
    return gamma_func((d + 1) / 2) / gamma_func((d + 2) / 2)


def Omega(d):
    """Sphere area of S^d: Omega_d = 2 pi^((d+1)/2) / Gamma((d+1)/2)."""
    return 2 * np.pi ** ((d + 1) / 2) / gamma_func((d + 1) / 2)


def backward_step(d):
    """The slicing recurrence backward step: Omega_{d-1}/Omega_d."""
    return 1 / (np.sqrt(np.pi) * R(d - 1))


if __name__ == "__main__":
    print("=" * 72)
    print("UNIFIED DESCENT: Part I's three corrections as Part 0 slicing steps")
    print("=" * 72)

    # ------------------------------------------------------------------
    # 1. Verify Part 0 slicing recurrence Omega_{d-1}/Omega_d = 1/(sqrt(pi) R(d-1))
    # ------------------------------------------------------------------
    print("\n1. Part 0 slicing recurrence: Omega_{d-1}/Omega_d = 1/(sqrt(pi) R(d-1))")
    print("-" * 72)
    print(f"{'d':>4} {'Omega_d':>12} {'Omega_{d-1}/Omega_d':>22} {'1/(sqrt(pi) R(d-1))':>22}")
    for d in [2, 3, 5, 6, 7, 19]:
        step = Omega(d - 1) / Omega(d)
        recurrence = backward_step(d)
        assert np.isclose(step, recurrence), f"mismatch at d={d}"
        print(f"{d:>4} {Omega(d):>12.6f} {step:>22.8f} {recurrence:>22.8f}")
    print("  All backward steps agree with recurrence. ✓")

    # ------------------------------------------------------------------
    # 2. 3D projection = one backward step at d=3
    # ------------------------------------------------------------------
    print("\n2. 3D projection factor: Omega_2/Omega_3 = 1/(sqrt(pi) R(2))")
    print("-" * 72)
    proj = Omega(2) / Omega(3)
    proj_via_recurrence = backward_step(3)
    proj_closed = 2 / np.pi
    R_2 = R(2)
    R_2_closed = np.sqrt(np.pi) / 2
    print(f"  Omega_2 = 4 pi = {Omega(2):.6f}")
    print(f"  Omega_3 = 2 pi^2 = {Omega(3):.6f}")
    print(f"  Omega_2 / Omega_3 = {proj:.8f}")
    print(f"  2/pi = {proj_closed:.8f}")
    print(f"  R(2) = sqrt(pi)/2 = {R_2:.8f} vs exact {R_2_closed:.8f}")
    print(f"  1/(sqrt(pi) R(2)) = {proj_via_recurrence:.8f}")
    assert np.isclose(proj, proj_closed)
    assert np.isclose(proj, proj_via_recurrence)
    print("  3D projection = one backward slicing step at d=3. ✓")

    # ------------------------------------------------------------------
    # 3. Host frame = two backward steps from d=7 to d=5
    # ------------------------------------------------------------------
    print("\n3. Host frame factor: Omega_5/Omega_7 = 1/(pi R(5) R(6))")
    print("-" * 72)
    host = Omega(5) / Omega(7)
    host_via_recurrence = backward_step(6) * backward_step(7)
    host_closed = 3 / np.pi
    R5R6 = R(5) * R(6)
    print(f"  Omega_5 = pi^3 = {Omega(5):.6f}")
    print(f"  Omega_7 = pi^4/3 = {Omega(7):.6f}")
    print(f"  Omega_5 / Omega_7 = {host:.8f}")
    print(f"  3/pi = {host_closed:.8f}")
    print(f"  R(5) = 16/(15 sqrt(pi)) = {R(5):.8f}")
    print(f"  R(6) = 5 sqrt(pi)/16 = {R(6):.8f}")
    print(f"  R(5) * R(6) = 1/3 = {R5R6:.8f}")
    print(f"  1/(pi R(5) R(6)) = {1 / (np.pi * R5R6):.8f}")
    print(f"  Two-step recurrence 1/(sqrt(pi) R(5)) * 1/(sqrt(pi) R(6)) = {host_via_recurrence:.8f}")
    assert np.isclose(host, host_closed)
    assert np.isclose(host, host_via_recurrence)
    print("  Host frame = two backward slicing steps from d=7 to d=5. ✓")

    # ------------------------------------------------------------------
    # 4. (Omega_5/Omega_7)^2 = 9/pi^2 for the bilinear invariant
    # ------------------------------------------------------------------
    print("\n4. Bilinear host frame: (Omega_5/Omega_7)^2 = 9/pi^2")
    print("-" * 72)
    bilinear_host = host ** 2
    bilinear_host_closed = 9 / np.pi ** 2
    print(f"  (Omega_5/Omega_7)^2 = {bilinear_host:.8f}")
    print(f"  9/pi^2 = {bilinear_host_closed:.8f}")
    assert np.isclose(bilinear_host, bilinear_host_closed)
    print("  Squared because two threshold sphere areas pass through host frame. ✓")

    # ------------------------------------------------------------------
    # 5. Assemble the full formula and compare
    # ------------------------------------------------------------------
    print("\n5. Full formula via unified descent vs Part I Theorem 3.1")
    print("-" * 72)
    # Cascade invariant I_0 from Part 0
    I0 = Omega(19) * Omega(217)
    print(f"  I_0 = Omega_19 * Omega_217 = {I0:.6e}")

    # Part 0 bilinear invariant I (host-frame corrected, used in Paper 0)
    I_bilinear = (Omega(5) / Omega(7)) ** 2 * I0
    print(f"  I = (Omega_5/Omega_7)^2 * I_0 = {I_bilinear:.6e}")
    I_bilinear_closed = 9 * I0 / np.pi ** 2
    print(f"    closed form 9 I_0 / pi^2 = {I_bilinear_closed:.6e}")
    assert np.isclose(I_bilinear, I_bilinear_closed)

    # Part I result
    rho_over_M4 = (Omega(2) / Omega(3)) * (Omega(5) / Omega(7)) ** 2 * I0
    rho_over_M4_closed = 18 * I0 / np.pi ** 3
    print(f"  rho_Lambda/M_Pl,red^4 = (Omega_2/Omega_3) (Omega_5/Omega_7)^2 I_0")
    print(f"                        = {rho_over_M4:.6e}")
    print(f"  closed form 18 I_0 / pi^3 = {rho_over_M4_closed:.6e}")
    assert np.isclose(rho_over_M4, rho_over_M4_closed)

    # Same via slicing steps alone
    rho_via_steps = (
        backward_step(3)
        * (backward_step(6) * backward_step(7)) ** 2
        * Omega(19) * Omega(217)
    )
    print(f"  via slicing steps directly: {rho_via_steps:.6e}")
    assert np.isclose(rho_via_steps, rho_over_M4)
    print("  Same value via slicing recurrence at layers {3, 6, 7} + thresholds {19, 217}. ✓")

    # ------------------------------------------------------------------
    # 6. Match to observation
    # ------------------------------------------------------------------
    print("\n6. Numerical match to observation (Planck 2018)")
    print("-" * 72)
    observed = 7.150e-121
    leading_dev = rho_over_M4 / observed - 1
    print(f"  Predicted (leading):  {rho_over_M4:.4e}")
    print(f"  Observed (Planck):    {observed:.4e}")
    print(f"  Leading deviation:    {leading_dev * 100:+.2f}%")

    # Gram correction
    gram_correction = np.exp(0.02108)
    rho_gram = rho_over_M4 * gram_correction
    gram_dev = rho_gram / observed - 1
    print(f"  Gram-corrected:       {rho_gram:.4e}")
    print(f"  Gram-corrected dev:   {gram_dev * 100:+.3f}%")

    # ------------------------------------------------------------------
    # 7. Summary
    # ------------------------------------------------------------------
    print("\n7. Summary: Unified descent decomposition")
    print("=" * 72)
    print("  rho_Lambda / M_Pl,red^4 = [Part 0 slicing recurrence at layers]")
    print()
    print("  = 1/(sqrt(pi) R(2))                  <-- backward step at d=3    (3D projection)")
    print("  * (1/(sqrt(pi) R(5) sqrt(pi) R(6)))^2 <-- two steps at d=6,7, squared (host frame)")
    print("  * Omega_19                           <-- threshold content at d_1")
    print("  * Omega_217                          <-- threshold content at d_2")
    print()
    print(f"  = (2/pi) * (3/pi)^2 * Omega_19 * Omega_217")
    print(f"  = 18 Omega_19 Omega_217 / pi^3")
    print(f"  = {rho_over_M4:.4e}")
    print()
    print("  ALL three Part I corrections are the SAME operation (Part 0 slicing")
    print("  recurrence) applied at different cascade-distinguished layers.")
    print("  Closes CLAUDE.md residual for Part I.")
