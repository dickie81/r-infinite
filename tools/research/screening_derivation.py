#!/usr/bin/env python3
"""
Attempted derivation of the 6 pi screening in 1/alpha_em.

Per Part IVb OQ alpha-em-screening: derive that the photon self-energy at
each Dirac layer contributes exactly N(0) * Gamma(1/2)^2 = 2 pi per
generation.

Existing cascade pieces:
  (1) Cor `2sqrtpi-primitive`: cascade fermion mass obstruction is
      1/(2*sqrt(pi)) = 1/(N(0) * Gamma(1/2)) at each Dirac layer.
      This is the SINGLE-PROPAGATOR-LEG factor.
  (2) Theorem `chirality-factorisation` (Theorem 4.8): a definite-chirality
      propagator traversing a cascade path with n_even even-sphere layers
      makes ONE chirality selection (single source to observer).
  (3) Bott periodicity (Part IVa): N_gen = 3 generations.

Goal: combine these to derive 6 pi screening structurally.

Derivation outline
------------------
A closed fermion loop in QED has the structure:

      photon -> fermion-loop -> photon
                  |     |
                propagator
                  |     |

with TWO propagators going around the loop.  In cascade conventions:

  - Each propagator at a Dirac layer carries a fermion mass obstruction
    factor 1/(2 sqrt(pi)) = 1/(N(0) Gamma(1/2)) per Cor 2sqrtpi-primitive
  - For two propagators in the loop: factor 1/(N(0) Gamma(1/2))^2
                                    = 1/(N(0)^2 Gamma(1/2)^2) = 1/(4 pi)

Chirality structure of a CLOSED loop:
  - Open propagator (source -> observer): ONE chirality selection
    (Theorem 4.8 unitary coherence argument)
  - Closed loop (no source/observer): chirality SUM, contributing
    a factor of chi = N(0) = 2

So the closed loop contribution per Dirac layer:
  (1/(N(0) Gamma(1/2)))^2 * chi
   = (1/(N(0)^2 Gamma(1/2)^2)) * N(0)
   = 1/(N(0) Gamma(1/2)^2)
   = 1/(2 pi)

Inverse contribution to 1/alpha (the screening): N(0) * Gamma(1/2)^2 = 2 pi.

For 3 generations (Bott periodicity from Part IVa): 3 * 2 pi = 6 pi.

This script verifies the numerical identity and lays out the structural
assembly.  Whether this counts as "deriving from the cascade action" or
just "assembling existing cascade pieces" is a calibration question.
"""

from __future__ import annotations

import math
import sys


N_0 = 2  # cascade lapse at d=0 (chirality count, Euler characteristic of S^{2n})
GAMMA_HALF = math.sqrt(math.pi)  # Gamma(1/2) = sqrt(pi)
N_GEN = 3  # Bott periodicity (Part IVa)


def main() -> int:
    print("=" * 78)
    print("DERIVING THE 6 pi SCREENING IN 1/alpha_em")
    print("=" * 78)
    print()

    # ----------------------------------------------------------------
    # Step 1: numerical verification
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Step 1: numerical verification")
    print("-" * 78)
    print()
    print(f"  N(0)              = {N_0}")
    print(f"  Gamma(1/2)        = sqrt(pi) = {GAMMA_HALF:.10f}")
    print(f"  Gamma(1/2)^2      = pi = {GAMMA_HALF**2:.10f}")
    print(f"  N(0) * Gamma(1/2)^2 = 2 pi = {N_0 * GAMMA_HALF**2:.10f}")
    print(f"  N_gen             = {N_GEN} (Bott periodicity, Part IVa)")
    print(f"  Total screening   = N_gen * 2 pi = {N_GEN * N_0 * GAMMA_HALF**2:.10f}")
    print(f"  Target (Part IVb) = 6 pi = {6 * math.pi:.10f}")
    print(f"  Match: {abs(N_GEN * N_0 * GAMMA_HALF**2 - 6 * math.pi) < 1e-12}")
    print()

    # ----------------------------------------------------------------
    # Step 2: structural derivation
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Step 2: structural derivation")
    print("-" * 78)
    print()
    print("Closed fermion loop = TWO propagators going around.")
    print()
    print("Per cascade Cor `2sqrtpi-primitive`, each fermion propagator at")
    print("a Dirac layer carries the obstruction factor")
    print("    1/(2 sqrt(pi)) = 1/(N(0) * Gamma(1/2))")
    print()
    print("Two propagators in the loop:")
    print("    [1/(N(0) Gamma(1/2))]^2 = 1/(N(0)^2 Gamma(1/2)^2) = 1/(4 pi)")
    print()
    print("Chirality structure of a CLOSED loop:")
    print("  - Open path (source -> observer): ONE chirality selection")
    print("    (Theorem 4.8 unitary coherence argument)")
    print("  - Closed loop: chirality SUM (chi = N(0) = 2 basins both")
    print("    contribute, no selection -- the loop returns to itself")
    print("    in both basins independently)")
    print()
    print("Closed-loop chirality factor: chi = N(0) = 2")
    print()
    print("Combining:")
    print("    [1/(N(0) Gamma(1/2))]^2 * chi")
    print("  = [1/(4 pi)] * 2")
    print("  = 1/(2 pi)")
    print()
    print("Inverse contribution to 1/alpha (the screening):")
    print("    Screening per Dirac layer = 2 pi = N(0) * Gamma(1/2)^2")
    print()
    print("Per generation: 3 * 2 pi = 6 pi (factor 3 from N_gen via Bott).")
    print()

    # ----------------------------------------------------------------
    # Step 3: status
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Step 3: status of this derivation")
    print("-" * 78)
    print()
    print("WHAT THIS DERIVES:")
    print("  - The factor 2 pi per generation = N(0) * Gamma(1/2)^2 follows")
    print("    from Cor 2sqrtpi-primitive + Theorem 4.8 chirality-factorisation")
    print("    + standard QED loop topology.")
    print("  - The factor 3 (number of generations) follows from Bott periodicity.")
    print("  - Total 6 pi is therefore CASCADE-INTERNALLY ASSEMBLED.")
    print()
    print("WHAT THIS DOES NOT DERIVE:")
    print("  - The derivation uses standard QED loop structure (two propagators")
    print("    in a closed fermion loop), which is imported from QFT, not derived")
    print("    from the cascade scalar action S = sum (2 alpha)^{-1}(Delta phi)^2.")
    print("  - Part IVb OQ alpha-em-screening asks for derivation 'from the")
    print("    action principle' -- ambiguous between:")
    print("    (a) strictly from S[phi] directly")
    print("    (b) from the cascade's structural framework (action + topology")
    print("        + Bott periodicity)")
    print("  - This script delivers (b), not (a).")
    print()
    print("HONEST READING:")
    print("  The 6 pi screening is now ASSEMBLED from existing cascade structures")
    print("  (fermion obstruction, chirality factorisation, Bott periodicity) plus")
    print("  one imported QFT structure (closed-loop topology).  This is a step")
    print("  toward closing oq:alpha-em-screening but doesn't fully close it -")
    print("  the closed-loop topology is QFT-imported, not cascade-derived.")
    print()
    print("To FULLY close the OQ would require:")
    print("  - Show that the cascade-lattice formulation of QED at the photon")
    print("    layer d=14 produces a fermion-loop diagram with two propagators")
    print("    closed in a cycle (cascade-internal lattice loop topology)")
    print("  - This is genuinely new physics content (cascade lattice gauge")
    print("    theory), not just structural reframing")
    print()
    print("STATUS UPGRADE: oq:alpha-em-screening goes from 'numerical match")
    print("interpreted via 2 pi = N(0) Gamma(1/2)^2' to 'structurally assembled")
    print("from three cascade theorems (Cor 2sqrtpi, Theorem 4.8, Bott from")
    print("Part IVa) + imported closed-loop topology'.  Tier 3 -> Tier 2.5")
    print("(structurally constrained but not fully cascade-internal yet).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
