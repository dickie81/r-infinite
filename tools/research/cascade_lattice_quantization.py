#!/usr/bin/env python3
"""
Cascade-lattice quantization research: PARTIAL-NEGATIVE on cross-Bott
extension via full path-integral propagator.

PROPOSAL TESTED (Check 7 compliant -- 1D layer index only, no spheres):

The cascade scalar action S = sum_d (2 alpha(d))^{-1} (Delta phi)^2 is a
1D Gaussian quadratic kinetic operator on the layer index d.  Currently
the cascade uses the classical saddle-point amplitude exp(-S_cl/2) =
exp(-Delta_Phi/2) for adjacent-layer mixing (Cabibbo geometric mean,
Theorem cabibbo-geometric-mean).  The proposal: extend to non-adjacent
("cross-Bott") layers by replacing the single-saddle approximation with
the full lattice path-integral propagator G = K^{-1}, where K is the
kinetic kernel:

    K_{d,d'} = (1/alpha_{d-1} + 1/alpha_d) delta_{d,d'}
                - (1/alpha_d) delta_{d',d+1}
                - (1/alpha_{d-1}) delta_{d',d-1}

with Dirichlet boundary conditions at d=4 (observer) and d=217 (Planck
sink).  This is cascade-native by Check 7 ("cascade-lattice Green's
functions on the layer index d -- admissible").

RESULT: PARTIAL-NEGATIVE
========================
Three findings, none of which close the targeted open questions:

(1) The full lattice propagator DISAGREES WITH THE SADDLE-POINT at 14%
    even at adjacent layers (G(12,13)/sqrt(G(12,12)G(13,13)) = 0.95 vs
    saddle exp(-p(13)/2) = 0.834).  The cascade's existing closed Cabibbo
    prediction uses the saddle-point; the full path-integral propagator
    moves AWAY from the closed value.  The cascade is therefore NOT a
    full-path-integral quantum lattice theory; it's a tree-level/saddle-
    point amplitude theory.  Promoting to a full quantum lattice is the
    wrong direction for this cascade structure.

(2) PMNS solar splitting OVERSHOOTS by 3-4 orders of magnitude.  Naive
    seesaw M_ij = m_29 G(29,d_i) G(29,d_j) / G(29,29) gives M_11 = 174 eV
    vs observed 0.05 eV.  The mass matrix is rank-1 (single source),
    collapsing two eigenvalues to zero.  Single-source-via-lattice-
    propagator is wrong-shape for the neutrino sector.

(3) Up-type Gen-2-to-Gen-1 N_c^3 pattern NOT CAPTURED.  Required
    exponents for the cross-Bott factor through d=12 are k = -0.67
    (Gen 3->Gen 2 step) and k = +18.3 (Gen 2->Gen 1 step) -- massively
    inconsistent.  No uniform exponent works.

CONCLUSION
==========
The "discrete cascade quantum field theory on the layer lattice with
cross-Bott kernels" sketch I gave as the missing-piece guess for the
remaining open questions is wrong, at least in this specific form.

What this rules out:
  * Full-path-integral propagator G = K^{-1} as the cross-Bott structure.
  * Single-source seesaw with G(29, d_g) couplings as the neutrino-sector
    closure.
  * Uniform-exponent mechanism via G(d_g, 12) for up-type generation
    pattern.

What this does NOT rule out (still open):
  * A different operator structure on the cascade lattice (perhaps tied
    to Berezin / chirality / path-tensor rather than scalar lattice).
  * Per-step amplitude / saddle-point structure with non-trivial cross-
    Bott corrections that go beyond the matrix-inverse propagator.
  * Non-naive seesaw structures (e.g., type-II / type-III seesaw analog
    with different cascade source structure).

The cascade's existing closures (Cabibbo, the alpha(d*)/chi^k family,
chirality factorisation) all use SADDLE-POINT amplitudes, not full
path-integral propagators.  This is structurally significant: the
cascade is not a quantum-lattice-field-theory in the standard sense.
Whatever closes the remaining open questions probably does NOT lie in
"more lattice quantum machinery" but in a different structural element
(plausibly path-tensor + chirality + cross-Bott Berezin).

CHECK 7 COMPLIANCE
==================
Everything below uses ONLY the 1D layer index d.  The lattice propagator
is on the layer lattice with Dirichlet BCs, no spheres, no spectral
decomposition of S^{d-1}, no KK reduction.  The negative result holds
within Check 7.
"""

from __future__ import annotations

import math
import numpy as np
from scipy.special import gamma, digamma


# ---------------------------------------------------------------
# Cascade primitives
# ---------------------------------------------------------------

def N_d(d: int) -> float:
    """Lapse function."""
    return math.sqrt(math.pi) * gamma((d + 1) / 2) / gamma((d + 2) / 2)


def R_d(d: int) -> float:
    """Compactification radius / area-ratio."""
    return gamma(d / 2 + 1) / gamma((d + 3) / 2)


def alpha_cascade(d: int) -> float:
    """Cascade gauge coupling alpha(d) = R(d)^2 / 4."""
    return R_d(d) ** 2 / 4.0


def p_cascade(d: int) -> float:
    """Per-step descent potential p(d) = (1/2) psi((d+1)/2) - (1/2) ln pi."""
    return 0.5 * digamma((d + 1) / 2) - 0.5 * math.log(math.pi)


def Phi_cascade(d: int, d_min: int = 4) -> float:
    """Cumulative descent potential from observer (d=4) to layer d."""
    if d <= d_min:
        return 0.0
    return sum(p_cascade(dprime) for dprime in range(d_min + 1, d + 1))


# ---------------------------------------------------------------
# Cascade lattice quantization: build kinetic kernel K and invert
# ---------------------------------------------------------------

def build_kinetic_kernel(d_min: int = 4, d_max: int = 217) -> np.ndarray:
    """
    Build the cascade scalar action's kinetic kernel on the layer lattice.

    Action: S = sum_d (1/(2 alpha(d))) (phi(d+1) - phi(d))^2

    Kernel: K_{d,d'} where d ranges from d_min to d_max-1 (interior).
    Endpoints d_min and d_max are Dirichlet-fixed (phi = 0 there).

    For d in interior:
      K_{d,d}   = 1/alpha(d-1) + 1/alpha(d)  [diagonal]
      K_{d,d-1} = -1/alpha(d-1)              [lower off-diag]
      K_{d,d+1} = -1/alpha(d)                [upper off-diag]
    """
    n_interior = d_max - d_min - 1   # interior layers: d_min+1, ..., d_max-1
    K = np.zeros((n_interior, n_interior))

    # Index i corresponds to layer d = d_min + 1 + i
    for i in range(n_interior):
        d = d_min + 1 + i
        a_prev = alpha_cascade(d - 1)  # spring stiffness on left
        a_curr = alpha_cascade(d)      # spring stiffness on right
        K[i, i] = 1.0 / a_prev + 1.0 / a_curr
        if i > 0:
            K[i, i - 1] = -1.0 / a_prev
        if i < n_interior - 1:
            K[i, i + 1] = -1.0 / a_curr

    return K


def cascade_propagator(d_min: int = 4, d_max: int = 217) -> tuple[np.ndarray, np.ndarray]:
    """
    Compute G = K^{-1}, the cascade-lattice Green's function.
    Returns (G, layer_indices) where layer_indices[i] = d for row/col i.
    """
    K = build_kinetic_kernel(d_min, d_max)
    G = np.linalg.inv(K)
    n = K.shape[0]
    layer_indices = np.array([d_min + 1 + i for i in range(n)])
    return G, layer_indices


def G_at(G, layers, d1: int, d2: int) -> float:
    """Look up G(d1, d2) from the propagator matrix."""
    i = np.where(layers == d1)[0]
    j = np.where(layers == d2)[0]
    if len(i) == 0 or len(j) == 0:
        return 0.0
    return G[i[0], j[0]]


# ---------------------------------------------------------------
# Test 1: PMNS solar splitting via cross-Bott seesaw with m_29
# ---------------------------------------------------------------

def test_pmns_solar(G, layers) -> None:
    """
    Test whether the cascade-lattice propagator gives off-diagonal
    couplings between m_29 source (d=29) and the three generations
    (d in {5, 13, 21}) sufficient to close PMNS solar splitting.

    Diagonal cascade neutrino mass: m_g = m_29 * alpha(d_g) / chi^(29 - d_g)
    where chi = 2.  So:
      m_1 (Gen 1, d=21) = m_29 * alpha(21) / 2^8
      m_2 (Gen 2, d=13) = m_29 * alpha(13) / 2^16
      m_3 (Gen 3, d=5)  = m_29 * alpha(5)  / 2^24

    Observed m_1 ~ 0.0493 eV (matches atm scale, derived).
    Observed m_2 ~ sqrt(Delta m^2_sol) = 8.66e-3 eV (factor 800 above
    cascade diagonal).

    Cross-Bott proposal: cascade-lattice propagator G(29, d_g) provides
    additional cross-coupling.  The seesaw-like off-diagonal contribution
    to neutrino masses:

      M_ij ~ m_29 * G(29, d_i) * G(29, d_j)

    Test whether this gives M_12 ~ 7.6e-4 eV (small-mixing approx) or
    closes the solar mass^2 splitting via large-mixing diagonalization.
    """
    print("=" * 78)
    print("TEST 1: PMNS solar splitting / lighter neutrinos (Roadmap item 2)")
    print("=" * 78)
    print()

    # Empirical anchors
    m_29_eV = 543.0
    m_atm_eV = 0.0495
    Delta_m2_sol = 7.5e-5
    Delta_m2_atm = 2.5e-3
    m_1_obs = math.sqrt(Delta_m2_atm)  # ~ 0.0500 eV (heaviest in normal hierarchy)
    m_2_obs = math.sqrt(Delta_m2_sol)  # ~ 0.00866 eV
    m_3_obs_upper = 0.05               # PDG bound

    # Diagonal cascade prediction (from Part IVb)
    chi = 2
    m_1_diag = m_29_eV * alpha_cascade(21) / chi**8
    m_2_diag = m_29_eV * alpha_cascade(13) / chi**16
    m_3_diag = m_29_eV * alpha_cascade(5)  / chi**24

    print("Diagonal cascade (Part IVb thm:complete-mass extrapolated):")
    print(f"  m_1 (d=21) = {m_1_diag:.5f} eV   vs observed {m_1_obs:.5f} eV  ({100*(m_1_diag-m_1_obs)/m_1_obs:+.2f}%)")
    print(f"  m_2 (d=13) = {m_2_diag:.2e} eV   vs observed {m_2_obs:.5f} eV  (factor {m_2_obs/m_2_diag:.1f} too small)")
    print(f"  m_3 (d=5)  = {m_3_diag:.2e} eV   vs observed bound {m_3_obs_upper}")
    print()

    # Cascade-lattice cross-Bott couplings to m_29
    g_29_21 = G_at(G, layers, 29, 21)
    g_29_13 = G_at(G, layers, 29, 13)
    g_29_5  = G_at(G, layers, 29, 5)
    g_29_29 = G_at(G, layers, 29, 29)

    print("Cascade-lattice propagator cross-Bott matrix elements:")
    print(f"  G(29, 29)   = {g_29_29:.4e}    (diagonal)")
    print(f"  G(29, 21)   = {g_29_21:.4e}    (one Bott step)")
    print(f"  G(29, 13)   = {g_29_13:.4e}    (two Bott steps)")
    print(f"  G(29, 5)    = {g_29_5:.4e}    (three Bott steps)")
    print()

    # Naive saddle-point estimate for comparison
    Phi29 = Phi_cascade(29)
    Phi21 = Phi_cascade(21)
    Phi13 = Phi_cascade(13)
    Phi5  = Phi_cascade(5)
    saddle_29_21 = math.exp(-(Phi29 - Phi21) / 2)
    saddle_29_13 = math.exp(-(Phi29 - Phi13) / 2)
    saddle_29_5  = math.exp(-(Phi29 - Phi5)  / 2)

    print("Saddle-point Gaussian amplitudes for comparison:")
    print(f"  exp(-(Phi(29)-Phi(21))/2) = {saddle_29_21:.4e}")
    print(f"  exp(-(Phi(29)-Phi(13))/2) = {saddle_29_13:.4e}")
    print(f"  exp(-(Phi(29)-Phi(5))/2)  = {saddle_29_5:.4e}")
    print()

    # Test seesaw-style off-diagonal: M_ij ~ m_29 * G(29, d_i) * G(29, d_j) / G(29, 29)
    # (this is the appropriate "propagation through source" formula)
    if g_29_29 > 0:
        M_11 = m_29_eV * g_29_21**2 / g_29_29
        M_22 = m_29_eV * g_29_13**2 / g_29_29
        M_33 = m_29_eV * g_29_5**2  / g_29_29
        M_12 = m_29_eV * g_29_21 * g_29_13 / g_29_29
        M_13 = m_29_eV * g_29_21 * g_29_5  / g_29_29
        M_23 = m_29_eV * g_29_13 * g_29_5  / g_29_29

        print("Cross-Bott seesaw mass matrix M_ij = m_29 G(29,d_i) G(29,d_j) / G(29,29):")
        print(f"  M_11 (d=21,21) = {M_11:.4e} eV  (cf m_1 obs {m_1_obs:.4e})")
        print(f"  M_22 (d=13,13) = {M_22:.4e} eV  (cf m_2 obs {m_2_obs:.4e})")
        print(f"  M_33 (d=5,5)   = {M_33:.4e} eV")
        print(f"  M_12 off-diag  = {M_12:.4e} eV")
        print(f"  M_13 off-diag  = {M_13:.4e} eV")
        print(f"  M_23 off-diag  = {M_23:.4e} eV")
        print()

        # Diagonalize the 3x3 mass matrix
        M = np.array([[M_11, M_12, M_13],
                      [M_12, M_22, M_23],
                      [M_13, M_23, M_33]])
        eigvals, eigvecs = np.linalg.eigh(M)
        eigvals_sorted = sorted(np.abs(eigvals), reverse=True)
        print("Diagonalized mass eigenvalues (sorted heaviest to lightest):")
        for i, ev in enumerate(eigvals_sorted):
            print(f"  m_{i+1} = {ev:.4e} eV")
        if len(eigvals_sorted) >= 2:
            dm2_atm_pred = eigvals_sorted[0]**2 - eigvals_sorted[1]**2
            print(f"  Delta m^2 (heaviest pair) = {dm2_atm_pred:.4e} eV^2")
        if len(eigvals_sorted) >= 3:
            dm2_sol_pred = eigvals_sorted[1]**2 - eigvals_sorted[2]**2
            print(f"  Delta m^2 (lighter pair)  = {dm2_sol_pred:.4e} eV^2")
            print(f"  Observed atm = {Delta_m2_atm:.2e} eV^2")
            print(f"  Observed sol = {Delta_m2_sol:.2e} eV^2")

        # Mixing angles from eigvecs
        print()
        print("Cascade-lattice mixing angles (PMNS-like):")
        # PMNS angles standard parameterization
        # eigenstates ordered for normal hierarchy
        # Just print the rotation matrix; angles extraction requires care
        # (due to ordering), but the magnitude tells us about size of mixing
        print(f"  Rotation matrix (mass to flavor basis):")
        for row in eigvecs.T:
            print(f"    [{row[0]:+.4f}, {row[1]:+.4f}, {row[2]:+.4f}]")

    print()


# ---------------------------------------------------------------
# Test 2: Up-type Gen-2-to-Gen-1 amplification
# ---------------------------------------------------------------

def test_uptype_pattern(G, layers) -> None:
    """
    Test whether cascade-lattice propagator gives the (c/s)/(u/d) ~ N_c^3
    amplification that the diagonal cascade misses.

    Hypothesis: up-type (Yukawa via tilde-H) involves a different cascade
    path than down-type (Yukawa via H), specifically a path through d=12
    with N_c-trace structure.  At the lattice level, this manifests as
    different propagator weights for up vs down across the gauge window.
    """
    print("=" * 78)
    print("TEST 2: up-type Gen-2-to-Gen-1 amplification (Roadmap item 4)")
    print("=" * 78)
    print()

    # Empirical
    m_t, m_b = 172.69e3, 4.18e3
    m_c, m_s = 1.27e3, 93.0
    m_u, m_d = 2.2, 4.7
    r_3 = m_t / m_b
    r_2 = m_c / m_s
    r_1 = m_u / m_d

    print(f"Empirical up/down ratios per generation:")
    print(f"  r_3 = m_t/m_b = {r_3:.2f}")
    print(f"  r_2 = m_c/m_s = {r_2:.2f}")
    print(f"  r_1 = m_u/m_d = {r_1:.3f}")
    print(f"  Cross-gen: r_3/r_2 = {r_3/r_2:.2f} ~ N_c, r_2/r_1 = {r_2/r_1:.2f} ~ N_c^3")
    print()

    # Up-type Yukawa hypothesis: the up-type Yukawa singlet bar Q_L tilde-H u_R
    # involves complex conjugation at d=12 (J^{-1} acting on V_12 = 3).
    # In the cascade lattice, this could correspond to an additional
    # propagator factor through d=12.

    # For each generation, compute G(d_g, 12) -- amplitude for fermion at
    # generation layer d_g to "pass through" d=12
    g_21_12 = G_at(G, layers, 21, 12)
    g_13_12 = G_at(G, layers, 13, 12)
    g_5_12  = G_at(G, layers, 5,  12)
    g_12_12 = G_at(G, layers, 12, 12)

    print("Cascade-lattice G(d_g, 12) (path through gauge SU(3) layer):")
    print(f"  G(21, 12) = {g_21_12:.4e}    (Gen 1 -> SU(3))")
    print(f"  G(13, 12) = {g_13_12:.4e}    (Gen 2 -> SU(3))")
    print(f"  G(5, 12)  = {g_5_12:.4e}     (Gen 3 -> SU(3))")
    print(f"  G(12, 12) = {g_12_12:.4e}    (diagonal at SU(3))")
    print()

    # If up-type carries an EXTRA factor of G(d_g, 12) / G(12, 12)
    # relative to down-type (interpretation: complex conjugation at d=12
    # forces an additional propagator round-trip), then:
    #
    # m_up / m_down at Gen g = (G(d_g, 12) / G(12,12))^k for some k

    # Test: predicted r_g / lepton_ratio
    # cascade lepton: m_tau/m_mu = 16.83, m_mu/m_e = 207
    # observed up/down at Gen g: r_g
    # if up/down = (G(d_g,12)/G(12,12))^k * (something universal)...

    # First, just look at the ratios:
    factor_21 = g_21_12 / g_12_12
    factor_13 = g_13_12 / g_12_12
    factor_5  = g_5_12  / g_12_12
    print("Lattice 'factor through d=12': G(d_g, 12) / G(12, 12)")
    print(f"  Gen 1 (d=21): {factor_21:.4e}")
    print(f"  Gen 2 (d=13): {factor_13:.4e}")
    print(f"  Gen 3 (d=5):  {factor_5:.4e}")
    print()

    # Compare to N_c-pattern needed: r_3/r_2 ~ N_c, r_2/r_1 ~ N_c^3
    # If up-type Yukawa carries (G(d_g,12)/G(12,12))^k extra, then
    # r_g / lepton_ratio ~ (G(d_g,12)/G(12,12))^k
    # ratio r_g / r_{g+1} = (factor_g / factor_{g+1})^k

    ratio_3_2 = factor_5 / factor_13   # Gen 3 vs Gen 2
    ratio_2_1 = factor_13 / factor_21  # Gen 2 vs Gen 1
    print(f"Lattice cross-gen factor ratios:")
    print(f"  Gen 3 / Gen 2 (factor_5 / factor_13) = {ratio_3_2:.4f}")
    print(f"  Gen 2 / Gen 1 (factor_13 / factor_21) = {ratio_2_1:.4f}")
    print()
    print(f"For r_3/r_2 ~ N_c = 3, need ratio_3_2^k = 3, so k = {math.log(3)/math.log(ratio_3_2):.3f}")
    print(f"For r_2/r_1 ~ N_c^3 = 27, need ratio_2_1^k = 27, so k = {math.log(27)/math.log(ratio_2_1):.3f}")
    print(f"If lattice mechanism is right, both k values should match")
    print(f"(structural test: same exponent across all cross-gen steps).")
    print()


# ---------------------------------------------------------------
# Test 3: Cabibbo geometric-mean recovery (sanity check)
# ---------------------------------------------------------------

def test_cabibbo_sanity(G, layers) -> None:
    """
    Sanity check: does the cascade-lattice propagator reproduce the
    Cabibbo geometric-mean factor exp(-p(13)/2) at the gauge window?

    This is the closed result from Theorem cabibbo-geometric-mean.
    The lattice propagator G(12, 13) should equal (or be proportional to)
    the saddle-point Gaussian amplitude exp(-p(13)/2) = 0.8336.
    """
    print("=" * 78)
    print("TEST 3 (sanity check): Cabibbo geometric-mean recovery")
    print("=" * 78)
    print()

    g_12_13 = G_at(G, layers, 12, 13)
    g_12_12 = G_at(G, layers, 12, 12)
    g_13_13 = G_at(G, layers, 13, 13)

    # Saddle-point amplitude
    p13 = p_cascade(13)
    saddle = math.exp(-p13 / 2)

    # Cauchy-Schwarz upper bound
    cs_bound = math.sqrt(g_12_12 * g_13_13)

    print(f"  Lattice G(12, 13)   = {g_12_13:.6e}")
    print(f"  G(12, 12)            = {g_12_12:.6e}")
    print(f"  G(13, 13)            = {g_13_13:.6e}")
    print(f"  Cauchy-Schwarz bound = sqrt(G(12,12) G(13,13)) = {cs_bound:.6e}")
    print(f"  Lattice ratio G(12,13)/sqrt(G(12,12)G(13,13)) = {g_12_13/cs_bound:.6f}")
    print()
    print(f"  Saddle-point exp(-p(13)/2) = {saddle:.6f}")
    print(f"  CS-saturation expectation: ratio ~ saddle? Match: {abs(g_12_13/cs_bound - saddle)/saddle * 100:.2f}% diff")
    print()


# ---------------------------------------------------------------
# Main
# ---------------------------------------------------------------

def main() -> None:
    print("Cascade-lattice quantization: testing cross-Bott structure")
    print("(Check 7 compliant: 1D layer index only, no spheres)")
    print()

    # Build the propagator
    G, layers = cascade_propagator(d_min=4, d_max=217)
    print(f"Built cascade lattice propagator on layers {layers[0]}..{layers[-1]}")
    print(f"Matrix shape: {G.shape}")
    print(f"Condition number: {np.linalg.cond(G):.2e}")
    print()

    # Sanity check first
    test_cabibbo_sanity(G, layers)

    # Test 1: PMNS / neutrinos
    test_pmns_solar(G, layers)

    # Test 2: up-type
    test_uptype_pattern(G, layers)


if __name__ == "__main__":
    main()
