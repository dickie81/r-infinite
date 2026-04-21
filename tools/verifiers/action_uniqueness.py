#!/usr/bin/env python3
"""
Action uniqueness: does the cascade action's compliance follow from gauge
identification alone?

The candidate action (Part IVb Remark 4.6) is
    S[phi] = sum_d (1/(2 alpha(d))) (Delta phi)^2
with alpha(d) = R(d)^2 / 4 the cascade gauge coupling (Part IVa).

Step 1 (forced by first-order EL): the action must be quadratic,
  nearest-neighbour, and of the form sum (1/(2 beta(d))) (Delta phi)^2
  for some compliance function beta(d).  Any other local quadratic form
  gives an EL equation incompatible with the first-order slicing recurrence.

Step 2 (conditionally forced by gauge identification): if the action
  represents cascade gauge physics, beta(d) must equal alpha(d).

This script verifies Step 2 by comparing seven candidate compliance
functions against Part IVb's Table 1 shifts.  Only beta = alpha matches;
six other natural candidates fail.

The result is a CONDITIONAL uniqueness argument: the action is uniquely
forced GIVEN that its compliance is the cascade's natural gauge coupling
alpha(d) from Paper IVa.  Action uniqueness reduces to the Paper IVa
identification of alpha(d) as the natural coupling, which is itself
motivated by the QFT convention alpha = g^2 / (4 pi).
"""

import os
import sys

import numpy as np

# Shared cascade primitives.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cascade_constants import R, alpha as alpha_cas  # noqa: E402


def marginal_shift(beta_fn, d_star, k, d_min=4, d_max=217):
    """Compute delta Phi = marginal Green's function at d_star / chi^k.

    The marginal Green's function response at source d_star equals beta(d_star).
    Divided by chi^k = 2^k for the chirality filtering (Part IVb Thm 4.8),
    this is the predicted cascade potential shift.
    """
    return beta_fn(d_star) / 2 ** k


# Part IVb Table 1 reported values
PART_IVB_SHIFTS = [
    ("alpha_s, m_tau/m_mu  (source=14, k=1)", 14, 1, 0.01723116),
    ("m_tau abs, ell_A     (source=19, k=1)", 19, 1, 0.01281631),
    ("sin^2 theta_W, Omega_m (source=5, k=3)", 5, 3, 0.01131768),
    ("theta_C              (source=7, k=2)",  7, 2, 0.01663007),
]

CANDIDATES = [
    ("alpha(d) = R(d)^2 / 4 [Part IVa gauge coupling]", alpha_cas),
    ("R(d)                  [slicing coefficient itself]", R),
    ("R(d)^2                [slicing squared, no /4]", lambda d: R(d) ** 2),
    ("R(d) / 2              [sqrt(alpha)]", lambda d: R(d) / 2),
    ("1 / d                 [natural 1/d scaling]", lambda d: 1 / d),
    ("1 / (d + 1)           [telescoping identity]", lambda d: 1 / (d + 1)),
    ("N(d) = sqrt(pi) R(d)  [lapse function itself]", lambda d: np.sqrt(np.pi) * R(d)),
]


if __name__ == "__main__":
    print("=" * 78)
    print("ACTION UNIQUENESS TEST")
    print("Compare 7 candidate compliance functions beta(d) against Part IVb shifts")
    print("=" * 78)

    for name, beta in CANDIDATES:
        print(f"\n  beta(d) = {name}")
        all_match = True
        max_rel_err = 0.0
        for label, d_star, k, target in PART_IVB_SHIFTS:
            predicted = marginal_shift(beta, d_star, k)
            rel_err = abs(predicted - target) / target
            max_rel_err = max(max_rel_err, rel_err)
            mark = "OK" if rel_err < 1e-5 else "MISMATCH"
            if rel_err >= 1e-5:
                all_match = False
            print(
                f"    {label:<42}  {predicted:.6e}  "
                f"(target {target:.6e})  [{mark}]"
            )
        status = "MATCHES Part IVb" if all_match else f"FAILS (max err {max_rel_err*100:.1f}%)"
        print(f"    -> {status}")

    print()
    print("=" * 78)
    print("CONCLUSION")
    print("=" * 78)
    print("""
Among seven natural candidate compliance functions, only
    beta(d) = alpha(d) = R(d)^2 / 4
matches the Part IVb Table 1 shifts to machine precision.  Six other
cascade-natural choices (R, R^2, R/2, 1/d, 1/(d+1), N) fail by factors
of 2 to 100.

This is a CONDITIONAL uniqueness:
  - Action form sum (1/(2 beta(d))) (Delta phi)^2 is forced by first-order EL.
  - Compliance beta(d) = alpha(d) is forced by matching observed shifts.
  - Alpha(d) = R(d)^2 / 4 is Part IVa's cascade gauge coupling, motivated
    by the gauge-theoretic normalisation alpha = g^2 / (4 pi).

Therefore: the action is uniquely determined by
  1. 'First-order EL equation' (forces quadratic nearest-neighbour form)
  2. 'Action represents cascade gauge sector' (forces compliance = alpha(d))

Item 1 is forced by Part 0.  Item 2 is the cascade-internal gauge-physics
identification from Part IVa.  Both are cascade-native.

The residual open question (now narrowed): why does alpha(d) = R(d)^2 / 4
define the cascade's gauge coupling, rather than some other normalisation?
This is answered by Part IVa Section 4.1: the factor of 1/(4 pi) in alpha
is the QFT gauge-theoretic convention; without it, alpha does not have
gauge-coupling meaning.  That identification is structural (it fixes the
scale at which the cascade matches observed gauge couplings), and the
action uniqueness follows.

Remaining truly open: is there a derivation of Paper IVa's identification
alpha(d) = N(d)^2 / (4 pi) that doesn't invoke QFT conventions?  If yes,
the chain closes to the cascade alone.  If no, the identification is a
choice of normalisation — still cascade-internally consistent, but not
uniquely forced in the strongest sense.
""")
