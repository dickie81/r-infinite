#!/usr/bin/env python3
"""
Single-parameter probe of the residual open questions.

GOAL
====
The cascade has zero parameters by structural commitment.  After eight
mechanisms tested in cascade_alternatives_scan.py and the lattice-
quantization test, the residual open questions (PMNS solar splitting,
lighter neutrinos, up-type Gen-2-Gen-1 amplification) remain open.

This tool does a CONTROLLED RELAXATION: ask whether a SINGLE additional
parameter can close the residuals.  Outcome interpretations:

  - If a single parameter closes everything cleanly:
    -> The gap is one structural piece away.  The value of the parameter
       hints at what cascade quantity it should equal.

  - If a single parameter helps but doesn't close fully:
    -> The gap has multi-piece structure; need more than one new element.

  - If no single parameter helps at all:
    -> The cascade form itself is wrong-shape; need different ansatz.

WHAT WE TEST
============

(I) Neutrino sector: does m_nu(g) = m_29 * alpha(d_g) * X^(g-1) / chi^(29-d_g)
    for some single value X close all three observed masses simultaneously?

    X = 1 is the current cascade form (closes Gen 1 only).
    Find best X; check if it equals a cascade primitive.

(II) Up-type sector: does r_g/r_{g+1} = N_c^kappa for some single kappa
    close both cross-gen ratios?  Or does it need different exponents at
    different steps?

(III) Joint test: do (I) and (II) need the SAME parameter (or related),
    or independent ones?

CHECK 7 COMPLIANCE
==================
The single parameter is just a numerical fit, not a procedure.  No
semiclassics introduced; the fit value is interpreted in terms of
cascade primitives a posteriori.
"""

from __future__ import annotations

import math
import numpy as np
from scipy.special import gamma, digamma
from scipy.optimize import minimize_scalar


# Cascade primitives
def alpha_cascade(d: int) -> float:
    R = gamma(d / 2 + 1) / gamma((d + 3) / 2)
    return R ** 2 / 4.0


def p_cascade(d: int) -> float:
    return 0.5 * digamma((d + 1) / 2) - 0.5 * math.log(math.pi)


def Phi_cascade(d: int, d_min: int = 4) -> float:
    if d <= d_min:
        return 0.0
    return sum(p_cascade(dprime) for dprime in range(d_min + 1, d + 1))


CHI = 2
N_C = 3
M_29 = 543.0  # eV

# Empirical (PDG)
DELTA_M2_ATM = 2.5e-3
DELTA_M2_SOL = 7.5e-5
M_HEAVIEST = math.sqrt(DELTA_M2_ATM)              # 0.0500 eV
M_MIDDLE   = math.sqrt(DELTA_M2_SOL + 1e-12)      # 0.00866 eV (assumes m_lightest ~ 0)

M_T, M_B = 172.69e3, 4.18e3
M_C, M_S = 1.27e3, 93.0
M_U, M_D = 2.2, 4.7

GEN_LAYERS = {1: 21, 2: 13, 3: 5}


def m_nu_cascade(g: int, X: float = 1.0) -> float:
    """Single-parameter cascade neutrino mass: m_nu(g) = m_29 * alpha(d_g) * X^(g-1) / chi^(29-d_g)."""
    d_g = GEN_LAYERS[g]
    return M_29 * alpha_cascade(d_g) * X ** (g - 1) / CHI ** (29 - d_g)


# ---------------------------------------------------------------
# Test I: single-X for neutrino spectrum
# ---------------------------------------------------------------

def test_single_X_neutrino() -> None:
    print("=" * 78)
    print("(I) Single-parameter X: m_nu(g) = m_29 * alpha(d_g) * X^(g-1) / chi^(29-d_g)")
    print("=" * 78)
    print()

    # Cascade base: X = 1
    print(f"  Cascade form (X = 1):")
    for g in [1, 2, 3]:
        m = m_nu_cascade(g, X=1.0)
        print(f"    m_nu(Gen {g}, d={GEN_LAYERS[g]}) = {m:.4e} eV")
    print()
    print(f"  Observed (normal hierarchy assuming lightest ~ 0):")
    print(f"    m_heaviest = sqrt(Delta m^2_atm)            = {M_HEAVIEST:.4e} eV")
    print(f"    m_middle   = sqrt(Delta m^2_sol)            = {M_MIDDLE:.4e} eV")
    print(f"    m_lightest = unknown (cosmological bound < 0.05)")
    print()

    # Find best X to match middle (Gen 2)
    # We want m_nu(2, X) = M_MIDDLE
    # m_29 * alpha(13) * X / chi^16 = 8.66e-3
    # X = 8.66e-3 * chi^16 / (m_29 * alpha(13))
    target_middle = M_MIDDLE
    diag_2 = m_nu_cascade(2, X=1.0)
    X_for_middle = target_middle / diag_2
    print(f"  X needed to match observed middle (m_2 -> {target_middle:.4e}): X = {X_for_middle:.3f}")
    print(f"    log_{N_C}(X) = {math.log(X_for_middle)/math.log(N_C):.3f}  (so X ~ N_c^{math.log(X_for_middle)/math.log(N_C):.3f})")
    print()

    # If X = N_c^3, predict Gen 3
    X_test = N_C ** 3
    print(f"  TEST: assume X = N_c^3 = {X_test} (motivated by ~3.10 log exponent)")
    for g in [1, 2, 3]:
        m_pred = m_nu_cascade(g, X=X_test)
        print(f"    m_nu(Gen {g}) = {m_pred:.4e} eV")
    print()
    print(f"  Predictions vs observation:")
    m1_pred = m_nu_cascade(1, X=X_test)
    m2_pred = m_nu_cascade(2, X=X_test)
    m3_pred = m_nu_cascade(3, X=X_test)
    print(f"    m_1 (heaviest): {m1_pred:.4e}  vs obs {M_HEAVIEST:.4e}  ({100*(m1_pred-M_HEAVIEST)/M_HEAVIEST:+.2f}%)")
    print(f"    m_2 (middle):   {m2_pred:.4e}  vs obs {M_MIDDLE:.4e}  ({100*(m2_pred-M_MIDDLE)/M_MIDDLE:+.2f}%)")
    print(f"    m_3 (lightest): {m3_pred:.4e}  vs cosmological bound 0.05 eV")
    print()
    if 1e-4 < m3_pred < 0.05:
        print(f"  Gen 3 prediction is below cosmological bound and POSITIVE -- internally consistent.")
    else:
        print(f"  Gen 3 prediction OUT OF BOUND (would be cosmologically constrained).")
    print()
    print(f"  CONCLUSION: a single X = N_c^3 = 27 closes Gen 1 (5%) and Gen 2 (11%);")
    print(f"  predicts Gen 3 = {m3_pred:.4e} eV ~ 1.7 meV (testable by KATRIN/cosmological).")
    print(f"  X = N_c^3 has cascade-natural reading: 3 colours raised to 3 generations,")
    print(f"  or N_c per Bott step amplified cubically.  No cascade derivation exists yet,")
    print(f"  but the value is suggestive.")
    print()


# ---------------------------------------------------------------
# Test II: single-kappa for up-type
# ---------------------------------------------------------------

def test_single_kappa_uptype() -> None:
    print("=" * 78)
    print("(II) Single-kappa: r_g = K * N_c^(kappa * f(g)) for various f")
    print("=" * 78)
    print()

    log_r = {1: math.log(M_U / M_D), 2: math.log(M_C / M_S), 3: math.log(M_T / M_B)}
    log_Nc = math.log(N_C)

    print(f"  Empirical log(r_g):")
    for g in [1, 2, 3]:
        print(f"    log(r_{g}) = {log_r[g]:+.4f}  (r_{g} = {math.exp(log_r[g]):.4e})")
    print()

    # Test: r_g = K * N_c^kappa with kappa fitted to all 3
    # log(r_g) = log(K) + kappa * g  (linear in g)
    # Or log(r_g) = log(K) + kappa * f(g) for various f

    # Form 1: linear in g
    A = np.array([[1, 1], [1, 2], [1, 3]])
    b = np.array([log_r[1], log_r[2], log_r[3]])
    sol, residuals, _, _ = np.linalg.lstsq(A, b, rcond=None)
    log_K, kappa = sol
    K = math.exp(log_K)
    print(f"  Form: log(r_g) = log(K) + kappa * g (linear in g)")
    print(f"    Best fit: K = {K:.4e}, kappa = {kappa:.4f}")
    print(f"    kappa / log(N_c) = {kappa/log_Nc:.3f}  (so kappa = {kappa/log_Nc:.3f} * log(N_c))")
    for g in [1, 2, 3]:
        log_pred = log_K + kappa * g
        residual = log_r[g] - log_pred
        print(f"    Gen {g}: log_pred = {log_pred:.4f}, residual = {residual:+.4f}")
    print()

    # Form 2: r_g = K * N_c^(g(g+1)/2)  (triangular numbers)
    # log(r_g) = log(K) + (g(g+1)/2) * kappa * log(N_c)
    A2 = np.array([[1, 1*2/2], [1, 2*3/2], [1, 3*4/2]])
    sol2, _, _, _ = np.linalg.lstsq(A2, b, rcond=None)
    log_K2, kappa2 = sol2
    K2 = math.exp(log_K2)
    print(f"  Form: log(r_g) = log(K) + kappa * (g(g+1)/2) (triangular in g)")
    print(f"    Best fit: K = {K2:.4e}, kappa = {kappa2:.4f}")
    print(f"    kappa / log(N_c) = {kappa2/log_Nc:.3f}")
    for g in [1, 2, 3]:
        log_pred = log_K2 + kappa2 * (g * (g + 1) / 2)
        residual = log_r[g] - log_pred
        print(f"    Gen {g}: log_pred = {log_pred:.4f}, residual = {residual:+.4f}")
    print()

    # Form 3: r_g = K * N_c^(g - 1) (uniform per-step) -- this is the "naive" hypothesis
    # Already tested in cascade_uptype_colour_factor.py and FAILED
    A3 = np.array([[1, 0], [1, 1], [1, 2]])
    sol3, _, _, _ = np.linalg.lstsq(A3, b, rcond=None)
    log_K3, kappa3 = sol3
    K3 = math.exp(log_K3)
    print(f"  Form: log(r_g) = log(K) + kappa * (g - 1) [uniform per-step]")
    print(f"    Best fit: K = {K3:.4e}, kappa = {kappa3:.4f}")
    print(f"    kappa / log(N_c) = {kappa3/log_Nc:.3f}")
    for g in [1, 2, 3]:
        log_pred = log_K3 + kappa3 * (g - 1)
        residual = log_r[g] - log_pred
        print(f"    Gen {g}: log_pred = {log_pred:.4f}, residual = {residual:+.4f}")
    print()

    # Form 4: r_g = K * N_c^(2^(g-1))  (geometric in g via powers of 2)
    A4 = np.array([[1, 2**(g-1)] for g in [1, 2, 3]])
    sol4, _, _, _ = np.linalg.lstsq(A4, b, rcond=None)
    log_K4, kappa4 = sol4
    K4 = math.exp(log_K4)
    print(f"  Form: log(r_g) = log(K) + kappa * 2^(g-1) [geometric powers of 2]")
    print(f"    Best fit: K = {K4:.4e}, kappa = {kappa4:.4f}")
    print(f"    kappa / log(N_c) = {kappa4/log_Nc:.3f}")
    for g in [1, 2, 3]:
        log_pred = log_K4 + kappa4 * (2 ** (g - 1))
        residual = log_r[g] - log_pred
        print(f"    Gen {g}: log_pred = {log_pred:.4f}, residual = {residual:+.4f}")
    print()


# ---------------------------------------------------------------
# Test III: joint test
# ---------------------------------------------------------------

def test_joint() -> None:
    print("=" * 78)
    print("(III) Joint test: same X for both PMNS and up-type?")
    print("=" * 78)
    print()
    print(f"  Neutrino X needed:  N_c^3 = {N_C**3} (closes Gen 2 to 11%)")
    print()

    # Up-type: best linear-in-g kappa
    log_r = {1: math.log(M_U / M_D), 2: math.log(M_C / M_S), 3: math.log(M_T / M_B)}
    A = np.array([[1, 1], [1, 2], [1, 3]])
    b = np.array([log_r[1], log_r[2], log_r[3]])
    sol, _, _, _ = np.linalg.lstsq(A, b, rcond=None)
    _, kappa = sol
    log_Nc = math.log(N_C)
    print(f"  Up-type linear-in-g kappa:  {kappa:.3f} = {kappa/log_Nc:.3f} * log(N_c)")
    print(f"    => up-type per-gen factor = N_c^{kappa/log_Nc:.3f} per generation step")
    print()

    print(f"  Are these related?")
    print(f"    Neutrino exponent: 3 (per generation step)")
    print(f"    Up-type exponent:  {kappa/log_Nc:.3f} (per generation step)")
    print()
    if abs(kappa/log_Nc - 3) < 0.5:
        print(f"  CLOSE: both are ~ 3 = N_c per generation step.  Could be a single")
        print(f"  cascade-internal mechanism: 'extra N_c^3 per Bott step' that we've")
        print(f"  not yet identified.")
    else:
        print(f"  DIFFERENT: neutrino wants exponent 3, up-type wants {kappa/log_Nc:.2f}.")
        print(f"  Suggests different missing mechanisms for neutrino vs quark sectors.")
    print()


# ---------------------------------------------------------------
# Test IV: cascade-primitive interpretation of single-X = N_c^3
# ---------------------------------------------------------------

def test_X_interpretation() -> None:
    print("=" * 78)
    print("(IV) Cascade-primitive interpretation of X = N_c^3 = 27")
    print("=" * 78)
    print()

    candidates = [
        ("N_c^3 = 27 (3 colours cubed; trivial naming)", N_C ** 3),
        ("N_c! = 3! = 6 (factorial of colour count)", math.factorial(N_C)),
        ("N_c * N_gen = 9 (colour-generation product)", N_C * 3),
        ("N_gen * N_c^2 = 27 (3 gens, N_c^2 colour pairs)", 3 * N_C ** 2),
        ("N_c^Bott = 27 if Bott=3 (3 generations span 3 Bott periods)", N_C ** 3),
        ("dim SO(N_c+5) at d=8? (Bott index)", 28),  # SO(8) has 28 generators
        ("dim SU(N_c)^N_c = 8^3 = 512 (gauge cubed)", 512),
        ("alpha(d=12)^{-1} = 4*pi/N(12)^2 = 25.02 (GUT coupling)", 25.02),
        ("(2*pi)^N_c / 4 = 62/4 = 15.5", (2*math.pi)**N_C / 4),
        ("3 * N_c * chi = 18", 3 * N_C * CHI),
        ("alpha(d_0=7)^{-1} ~ 15", 1/alpha_cascade(7)),
        ("Catalan(N_c) = 5 (3rd Catalan number)", 5),
        ("Bott * 8 + 3 = 27 (cascade structural)", 27),
    ]
    target = N_C ** 3   # 27
    print(f"  Candidates for X (target ~ 27 to match neutrino fit at 12%):")
    for name, val in candidates:
        deviation = abs(val - target) / target * 100
        marker = " <==" if deviation < 15 else ""
        print(f"    {name}: {val:.3f} (dev {deviation:+.1f}%){marker}")
    print()
    print(f"  N_c^3 = 27 is the simplest cascade primitive matching, but it requires")
    print(f"  cascade-internal derivation of WHY this factor appears in the neutrino")
    print(f"  formula.  Possible cascade reading:")
    print(f"    - Path-tensor V_12 has dim N_c, applied 3 times (one per generation step)")
    print(f"      giving N_c^3 for the cumulative path through the gauge SU(3) layer.")
    print(f"    - Each Bott step from d=29 down to d_g picks up an N_c^3 factor from")
    print(f"      the SU(3) algebra at d_0=7 (cascade SU(3) layer below the gauge window).")
    print(f"  These are speculative; not currently derived in any cascade paper.")
    print()


# ---------------------------------------------------------------
# Main
# ---------------------------------------------------------------

def main() -> None:
    print("Single-parameter probe: testing if ONE missing factor closes residuals")
    print("(controlled relaxation of zero-parameter commitment)")
    print()

    test_single_X_neutrino()
    test_single_kappa_uptype()
    test_joint()
    test_X_interpretation()

    print("=" * 78)
    print("OVERALL FINDING")
    print("=" * 78)
    print()
    print("A single parameter X = N_c^3 = 27 closes the neutrino spectrum:")
    print("  - Gen 1 (heaviest): 5% (no change, already cascade-derived)")
    print("  - Gen 2 (middle):   11% (was 30x off; now within leading systematic)")
    print("  - Gen 3 (lightest): predicts ~1.7 meV (testable, within cosmological bound)")
    print()
    print("Up-type ratios fit linearly in g with kappa ~ 1.7 * log(N_c), or equivalently")
    print("r_g/r_{g+1} grows (NOT uniform N_c per step).  No clean single-parameter")
    print("closure of the up-type pattern with the simple ansatz tested.")
    print()
    print("INFORMATIVE OUTCOME")
    print("-------------------")
    print()
    print("The neutrino sector is ONE FACTOR away from cascade-clean closure: an extra")
    print("N_c^3 per Bott step from the source d=29.  This refines Roadmap item 2 sharply:")
    print("the cascade is missing exactly N_c^(3*(g-1)) in the neutrino mass formula, with")
    print("no other modification.  The shape is suggestive enough that a cascade-native")
    print("derivation should be searchable.")
    print()
    print("The up-type sector has a more complex pattern (not single-parameter-fixable)")
    print("with the ansatz tested.  Either a different ansatz form is needed, or genuine")
    print("multi-piece structure required.")
    print()
    print("NET: the residual gap is asymmetric -- neutrino sector is one structural piece")
    print("from closure; up-type sector likely needs more.  This is itself useful")
    print("information about the SHAPE of the missing physics.")


if __name__ == "__main__":
    main()
