#!/usr/bin/env python3
"""
Cascade v-closure: derive exp(-pi/alpha(5)) from the cascade action

Part IVb Theorem 4.7 writes the electroweak VEV as
    v = M_Pl,red * alpha_GUT * exp(Phi(12->4)) * exp(-pi/alpha(5))

The first three factors are cascade-derived; the fourth was stated as
"an instanton-like suppression" without derivation.  This is item (c) of
Part IVb Remark 4.6's what-remains-open.

This script demonstrates the cascade-native identity

    pi / alpha(5) = Omega_2 / R(5)^2

with both factors Part 0 quantities, and numerically verifies the
complete v-closure chain:

  1. Omega_2 = 4 pi  (observer equatorial 2-sphere, Part 0)
  2. R(5) = 16 / (15 sqrt(pi))  (slicing step at volume maximum)
  3. alpha(5) = R(5)^2 / 4 = 64 / (225 pi)  (cascade gauge coupling)
  4. pi / alpha(5) = 225 pi^2 / 64 = Omega_2 / R(5)^2
  5. exp(-pi/alpha(5)) = 8.53e-16
  6. v = M_Pl,red * alpha_s * exp(-pi/alpha(5)) = 240.8 GeV (observed 246.22)

The proposed cascade-native origin of exp(-pi/alpha(5)):

At d=5 (volume maximum, sphere S^4), the hairy-ball theorem forces every
tangent vector field on S^4 to have zeros summing to chi(S^4) = 2.  The
slicing-direction field at this layer must carry such a defect.  In the
Morse foliation of S^4 by 2-spheres (same mechanism as Part I §3.2's
foliation of S^3), the defect appears as a standard 2D vortex on each
latitude.

A 2D Kosterlitz-Thouless vortex on S^2 with stiffness alpha has action
pi n^2 / alpha per unit winding n.  At d=5 with compliance alpha(5),
the single-winding vortex action is exactly pi/alpha(5), giving the
Boltzmann factor exp(-pi/alpha(5)).

The factor of pi (vs 2pi for a standard Yang-Mills instanton) is the
single-vortex action in the 2-sphere cross-section, not a full 4D YM
instanton: consistent with the cascade's foliation-by-2-spheres
architecture (Part I §3.2, Part IVa §4).

This interpretation is Check 7 clean: 2D vortex action is classical field
theory on a discrete lattice, not semiclassical QFT.  The tunneling
amplitude is read from the action's stationary point directly via the
classical Bogomol'nyi-saturated bound.
"""

import os
import sys

import numpy as np

# Shared cascade primitives.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cascade_constants import R, alpha as alpha_cas, Omega  # noqa: E402


def N(d):
    return np.sqrt(np.pi) * R(d)


if __name__ == "__main__":
    print("=" * 72)
    print("CASCADE v-CLOSURE: exp(-pi/alpha(5)) from the action")
    print("=" * 72)

    # Step 1: analytic form of the exponent
    print("\n1. Analytic form")
    print("-" * 72)
    R5 = R(5)
    alpha5 = alpha_cas(5)
    exponent = np.pi / alpha5
    print(f"  R(5) = Gamma(3)/Gamma(7/2) = 16/(15 sqrt(pi)) = {R5:.10f}")
    print(f"  R(5)^2 = 256/(225 pi) = {R5**2:.10f}")
    print(f"  alpha(5) = R(5)^2/4 = 64/(225 pi) = {alpha5:.10f}")
    print(f"  1/alpha(5) = 225 pi/64 = {1/alpha5:.10f}")
    print(f"  pi/alpha(5) = 225 pi^2/64 = {exponent:.10f}")
    print(f"  exp(-pi/alpha(5)) = {np.exp(-exponent):.4e}")

    # Step 2: cascade-native form
    print("\n2. Cascade-native form:  pi/alpha(5) = Omega_2/R(5)^2")
    print("-" * 72)
    Omega_2 = Omega(2)
    alt = Omega_2 / R5**2
    print(f"  Omega_2 = 4 pi = {Omega_2:.10f}")
    print(f"  R(5)^2  = {R5**2:.10f}")
    print(f"  Omega_2 / R(5)^2 = {alt:.10f}")
    print(f"  pi / alpha(5)    = {exponent:.10f}")
    assert np.isclose(alt, exponent)
    print("  Identity confirmed. Both factors are Part 0 sphere-area / slicing quantities.")

    # Step 3: comparison to standard Yang-Mills instanton
    print("\n3. Comparison: cascade factor = half Yang-Mills instanton")
    print("-" * 72)
    ym = 2 * np.pi / alpha5  # standard YM instanton action S = 8 pi^2 / g^2 = 2 pi/alpha
    cas = np.pi / alpha5
    print(f"  Standard YM:    S = 2 pi/alpha(5) = {ym:.4f}    exp(-S) = {np.exp(-ym):.2e}")
    print(f"  Cascade:        S =   pi/alpha(5) = {cas:.4f}    exp(-S) = {np.exp(-cas):.2e}")
    print(f"  Cascade factor = half of YM.  Interpretation: 2D vortex action on")
    print(f"  the 2-sphere cross-section of S^4 via Morse foliation (not 4D YM).")

    # Step 4: Kosterlitz-Thouless vortex interpretation
    print("\n4. Kosterlitz-Thouless vortex on 2-sphere cross-section of S^4")
    print("-" * 72)
    print(f"  Standard KT result: S_vortex = pi n^2 / alpha  (winding n)")
    print(f"  At alpha(5), single-winding vortex:  pi / alpha(5) = {cas:.4f}")
    print(f"  Matches cascade factor exactly.")
    print(f"  The 2-sphere cross-section comes from Morse foliation of S^4,")
    print(f"  identical mechanism to Part I Sec 3.2's foliation of S^3.")

    # Step 5: Full v-formula verification
    print("\n5. Full v-formula verification")
    print("-" * 72)
    M_Pl_red_GeV = 2.435e18
    alpha_s = 0.1159  # Part IVb leading
    v_predicted = M_Pl_red_GeV * alpha_s * np.exp(-cas)
    v_observed = 246.22
    print(f"  M_Pl,red              = {M_Pl_red_GeV:.4e} GeV")
    print(f"  alpha_s (leading)     = {alpha_s:.4f}")
    print(f"  exp(-pi/alpha(5))     = {np.exp(-cas):.4e}")
    print(f"  v = M_Pl,red * alpha_s * exp(-pi/alpha(5))")
    print(f"    = {v_predicted:.2f} GeV")
    print(f"  Observed v           = {v_observed} GeV")
    print(f"  Deviation            = {100*(v_predicted-v_observed)/v_observed:+.2f}%")

    # Step 6: what this derivation does and doesn't do
    print("\n6. What this derivation does and does not do")
    print("-" * 72)
    print("""
  Does:
    - Write pi/alpha(5) as Omega_2 / R(5)^2, purely cascade-native.
    - Interpret the factor as a 2D vortex action on the Morse-foliation
      2-sphere cross-section of S^4 at the hairy-ball layer d=5.
    - Match the Kosterlitz-Thouless single-vortex action pi n^2/alpha
      at n=1 exactly, not by fitting.
    - Show v = 240.8 GeV (vs observed 246.22, -2.2%) with the full
      cascade-internal chain.

  Does not:
    - Rigorously derive that the cascade's non-perturbative sector at d=5
      saturates the 2D-vortex action.  The Morse-foliation reading gives
      the right number but the mapping between 4D hairy-ball defect and
      2D vortex needs formal justification.
    - Address the -2.2% deviation.  This is descent-dependent (shared
      with alpha_s's leading deviation); the Gram first-order correction
      closes it to sub-1% in the other descent-dependent observables.
    - Explain why the defect action is BPS-saturated (half the full
      index-2 contribution).  Candidate: the chirality-basin decomposition
      of Theorem 4.8 selects one of two basins, halving the effective
      winding.

  Status: item (c) of Part IVb Remark 4.6 partially closed.  The
  cascade-native identity pi/alpha(5) = Omega_2/R(5)^2 is verified;
  the 2D-vortex interpretation is proposed and structurally consistent;
  the BPS/half-winding reading is the remaining interpretive joint.
""")
