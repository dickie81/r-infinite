#!/usr/bin/env python3
"""
Chirality-Jacobian separability: the factor 1/chi = 1/2 and the factor
1/sqrt(pi) in the fermion obstruction 1/(2 sqrt(pi)) act independently at
the level of the scalar slicing integral.

Tests the structural split of Part IVb Theorem 2.2 (thm:sp31-decomposition):
    1/(2 sqrt(pi)) = (1/chi) * (1/sqrt(pi))
where the chirality half is derived (Theorem 4.14) and the Jacobian half
is conjectured (Open Question oq:fermion-cascade-action).

Mechanism.  The cascade's scalar slicing integral is
    N(d) = int_{-1}^{1} (1 - x^2)^{(d-1)/2} dx = B(1/2, (d+1)/2) = sqrt(pi) R(d).
Weighting by a chirality projector (1 ± x)/2 gives

    int_{-1}^{1} (1 - x^2)^{(d-1)/2} * (1 ± x)/2 dx = sqrt(pi) R(d) / 2

exactly, at every Dirac layer d in {5, 13, 21, 29}.  The factor of 2 is
removed by the projector; the sqrt(pi) is untouched.  This confirms the
chirality and Jacobian halves of 1/(2 sqrt(pi)) are mechanistically
separable at the slicing-integral level.

Implication.  Any reformulation of Clifford absorption that proposes to
remove sqrt(pi) via a modified slicing measure (e.g. an alpha != 1/2 in
the Beta integrand) is constrained by this separability: the chirality
half already acts within the scalar measure, so the sqrt(pi) absorption
must come from spinor structure (Berezin/Clifford inner product), not
from the axial Jacobian.
"""

import os
import sys

import numpy as np
from scipy.integrate import quad

# Shared cascade primitives.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cascade_constants import R, pi  # noqa: E402

sqrt_pi = np.sqrt(pi)
DIRAC_LAYERS = (5, 13, 21, 29)


def slicing_integral(d, weight):
    """int_{-1}^{1} (1 - x^2)^{(d-1)/2} * weight(x) dx."""
    val, _ = quad(
        lambda x: (1 - x * x) ** ((d - 1) / 2.0) * weight(x),
        -1.0,
        1.0,
    )
    return val


def scalar_lapse(d):
    """N(d) = sqrt(pi) * R(d); the exact value of the scalar integral."""
    return sqrt_pi * R(d)


def fmt_pct(x):
    return f"{x * 100:+.4f}%"


def main():
    print("=" * 78)
    print("CHIRALITY-JACOBIAN SEPARABILITY TEST")
    print("=" * 78)
    print()
    print("Target: verify that weighting the scalar slicing integrand by")
    print("a chirality projector (1 +/- x)/2 produces exactly sqrt(pi) R(d) / 2,")
    print("at every Dirac layer in {5, 13, 21, 29}.")
    print()
    print("If yes: chirality halving is mechanistically independent of the")
    print("sqrt(pi) Jacobian factor, confirming Part IVb Theorem 2.2's split")
    print("1/(2 sqrt(pi)) = (1/chi) * (1/sqrt(pi)).")
    print()

    # Weights under test.
    weights = [
        ("W(x) = 1            [scalar, baseline]",        lambda x: 1.0),
        ("W(x) = (1 + x) / 2  [positive chirality]",      lambda x: 0.5 * (1.0 + x)),
        ("W(x) = (1 - x) / 2  [negative chirality]",      lambda x: 0.5 * (1.0 - x)),
        ("W(x) = sqrt(1-x^2)  [Jacobian modification]",   lambda x: np.sqrt(max(1.0 - x * x, 0.0))),
    ]

    print(f"{'weight':<42s} {'d':>4s} {'integral':>14s} {'target':>14s} {'residue':>12s}")
    print("-" * 90)
    # For (1 ± x)/2 the target is sqrt(pi) R(d) / 2.
    # For the scalar baseline, target is sqrt(pi) R(d).
    # For sqrt(1-x^2) (shown for contrast), no clean closed-form target; we
    # report the residue against sqrt(pi) R(d) / 2 to show it does NOT match.
    max_chirality_residue = 0.0
    for label, w in weights:
        for d in DIRAC_LAYERS:
            integral = slicing_integral(d, w)
            if "chirality" in label:
                tgt = scalar_lapse(d) / 2.0
            elif "scalar" in label:
                tgt = scalar_lapse(d)
            else:
                tgt = scalar_lapse(d) / 2.0
            residue = (integral - tgt) / tgt
            if "chirality" in label:
                max_chirality_residue = max(max_chirality_residue, abs(residue))
            print(
                f"{label:<42s} {d:>4d} {integral:>14.10f} "
                f"{tgt:>14.10f} {fmt_pct(residue):>12s}"
            )
        print()

    print("=" * 78)
    print("Verdict")
    print("=" * 78)
    print()
    if max_chirality_residue < 1e-8:
        print(f"  PASS.  Chirality-weighted integrals match sqrt(pi) R(d) / 2 to")
        print(f"  within {max_chirality_residue:.2e} at every tested Dirac layer.")
        print()
        print("  This verifies that the (1 ± x)/2 projection:")
        print("    - removes the factor of 2 (integral halves),")
        print("    - preserves sqrt(pi) in the result (no Jacobian modification).")
        print()
        print("  Consequence for Part IVb Theorem 2.2 (thm:sp31-decomposition):")
        print("  the two halves of 1/(2 sqrt(pi)) are mechanistically independent.")
        print("  Chirality acts on the integration domain (halving); the Jacobian")
        print("  factor sqrt(pi) = Gamma(1/2) is a property of the measure itself")
        print("  and is not touched by chirality projection.")
        print()
        print("  Consequence for Open Question oq:fermion-cascade-action:")
        print("  a cascade-action derivation of the sqrt(pi) absorption cannot")
        print("  proceed via a modified axial measure (that breaks d-independence;")
        print("  see also tools/model_checks/fermion_dirac_spectral_zeta.py).")
        print("  It must come from spinor structure: Berezin/Clifford inner product,")
        print("  or equivalently the spin-connection coupling in the Dirac operator.")
    else:
        print(f"  FAIL.  Maximum chirality residue {max_chirality_residue:.2e}")
        print(f"  exceeds tolerance 1e-8.  Investigate numerical-precision issues")
        print(f"  or re-examine the algebraic identity int (1-x^2)^k (1+x)/2 dx.")
        raise SystemExit(1)

    # Algebraic sanity check: the parity argument.
    print()
    print("-" * 78)
    print("Algebraic sanity check (parity argument)")
    print("-" * 78)
    print()
    print("  int_{-1}^{1} (1 - x^2)^k * (1 ± x)/2 dx")
    print("    = (1/2) int_{-1}^{1} (1 - x^2)^k dx   [the x term vanishes by parity]")
    print("    = (1/2) int_{-1}^{1} (1 - x^2)^k dx")
    print("    = N(2k+1) / 2")
    print("    = sqrt(pi) R(2k+1) / 2     [Part 0 Theorem 3.1]")
    print()
    print("  Setting 2k + 1 = d:  result is sqrt(pi) R(d) / 2.  No sqrt(pi)")
    print("  absorption occurred; chirality halving is exact and independent.")


if __name__ == "__main__":
    main()
