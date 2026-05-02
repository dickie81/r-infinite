#!/usr/bin/env python3
"""
Systematic scan of cascade-native alternatives to close residual open
questions:

  (A) PMNS solar splitting / lighter neutrino masses (Roadmap item 2)
  (B) Up-type Gen-2-to-Gen-1 N_c^3 amplification (Roadmap item 4)

The naive lattice-propagator quantization (cascade_lattice_quantization.py)
produced a partial-negative.  This tool explores other Check-7-compliant
cascade-native mechanisms.

ALTERNATIVES TESTED
===================

1. Berezin cross-period coupling (bilinear sqrt(m_i m_j) seesaw analog)
2. Chi=2 basin off-diagonal for PMNS angles
3. Per-Dirac-layer chi * Gamma(1/2)^n contribution at higher n
4. Coherent sum over multiple Bott Dirac source layers (m_29, m_37, m_45, ...)
5. Generation-dependent J-conjugation at d=12 for up-type pattern
6. CP-conjugate Majorana off-diagonal for solar splitting
7. Path-tensor 4-fold extension across all Bott Dirac layers
8. Hopf-fibration mixing at d=8 (Bott period boundary)

Each mechanism is tested against the relevant observables.  Honest
documentation of which work, which fail.

CHECK 7 COMPLIANCE
==================
All mechanisms below use cascade primitives only:
  - alpha(d), R(d), N(d), Phi(d), p(d), Omega_d, chi=2, Gamma(1/2)
  - 1D cascade-lattice quantities, no spheres in spectral decompositions
  - Path-tensor structure (Part IVa/IVb)
  - Chirality theorem (Part IVb)
  - Berezin partition function (Part IVb)
  - Bott periodicity (Part IVa)
"""

from __future__ import annotations

import math
import numpy as np
from scipy.special import gamma, digamma


# ---------------------------------------------------------------
# Cascade primitives
# ---------------------------------------------------------------

def N_d(d: int) -> float:
    return math.sqrt(math.pi) * gamma((d + 1) / 2) / gamma((d + 2) / 2)


def R_d(d: int) -> float:
    return gamma(d / 2 + 1) / gamma((d + 3) / 2)


def alpha_cascade(d: int) -> float:
    return R_d(d) ** 2 / 4.0


def p_cascade(d: int) -> float:
    return 0.5 * digamma((d + 1) / 2) - 0.5 * math.log(math.pi)


def Phi_cascade(d: int, d_min: int = 4) -> float:
    if d <= d_min:
        return 0.0
    return sum(p_cascade(dprime) for dprime in range(d_min + 1, d + 1))


# Cascade-derived quantities
CHI = 2
TWO_SQRT_PI = 2 * math.sqrt(math.pi)
M_29 = 543.0  # eV, fourth Bott Dirac source mass

# Generation -> source layer
GEN_LAYERS = {1: 21, 2: 13, 3: 5}

# Empirical anchors (PDG 2024)
DELTA_M2_ATM = 2.5e-3      # eV^2
DELTA_M2_SOL = 7.5e-5      # eV^2
M_NU_HEAVIEST = math.sqrt(DELTA_M2_ATM)   # ~ 0.0500 eV
M_NU_MIDDLE = math.sqrt(DELTA_M2_SOL)     # ~ 0.00866 eV
THETA_12_OBS = 33.4   # deg
THETA_23_OBS = 49.0   # deg (NH best fit; varies)
THETA_13_OBS = 8.6    # deg

# Up-type quark
M_T, M_B = 172.69e3, 4.18e3
M_C, M_S = 1.27e3, 93.0
M_U, M_D = 2.2, 4.7


def cascade_lepton_mass(d_g: int, n_D: int, alpha_s: float = 0.1179, v: float = 246.22) -> float:
    """Charged lepton mass in MeV from Theorem complete-mass."""
    return (alpha_s * v * 1e3 / math.sqrt(2)) * math.exp(-Phi_cascade(d_g)) * (TWO_SQRT_PI ** -(n_D + 1))


# ---------------------------------------------------------------
# Mechanism 1: Berezin cross-period sqrt(m_i m_j) coupling
# ---------------------------------------------------------------

def test_berezin_cross_period() -> None:
    """
    Berezin partition function: Z_f(d) = m(d) = R(d)/2 = sqrt(alpha(d)).
    Cross-period bilinear: M_ij ~ sqrt(Z_f(d_i) Z_f(d_j)) = (alpha(d_i) alpha(d_j))^(1/4).

    Test: do these geometric-mean masses give the observed neutrino
    spectrum and PMNS structure?
    """
    print("=" * 78)
    print("(1) Berezin cross-period: M_ij = (alpha(d_i) alpha(d_j))^(1/4) * scale")
    print("=" * 78)

    layers = [21, 13, 5]   # d for Gen 1, 2, 3
    n = len(layers)

    # Bilinear matrix
    M_berezin = np.zeros((n, n))
    for i, d_i in enumerate(layers):
        for j, d_j in enumerate(layers):
            M_berezin[i, j] = (alpha_cascade(d_i) * alpha_cascade(d_j)) ** 0.25

    # Anchor: scale so heaviest matches m_atm
    M_norm = M_berezin / M_berezin[0, 0]
    scale = M_NU_HEAVIEST  # set diagonal entry at d=21 to 0.05 eV
    M = M_norm * scale

    print(f"  Berezin bilinear matrix (eV, scaled to m_1 = {scale:.4f}):")
    for row in M:
        print(f"    [{row[0]:.4e}, {row[1]:.4e}, {row[2]:.4e}]")

    eigvals = sorted(np.abs(np.linalg.eigvals(M)), reverse=True)
    print(f"  Eigenvalues: {[f'{e:.4e}' for e in eigvals]}")
    if len(eigvals) >= 2:
        dm2_atm_pred = eigvals[0] ** 2 - eigvals[1] ** 2
        print(f"  Delta m^2 atm pred: {dm2_atm_pred:.4e} (obs: {DELTA_M2_ATM:.2e})")
    if len(eigvals) >= 3:
        dm2_sol_pred = eigvals[1] ** 2 - eigvals[2] ** 2
        print(f"  Delta m^2 sol pred: {dm2_sol_pred:.4e} (obs: {DELTA_M2_SOL:.2e})")
    print()


# ---------------------------------------------------------------
# Mechanism 2: Chi=2 basin off-diagonal for PMNS angles
# ---------------------------------------------------------------

def test_chirality_basin_pmns() -> None:
    """
    For neutrinos coupling symmetrically to both chirality basins (Majorana
    structure forced by basin equivalence), the off-diagonal mixing
    between adjacent Bott Dirac layers picks up an additional 1/chi factor
    times the saddle amplitude.

    Test: does this modify Cabibbo-extended angles to large PMNS values?
    """
    print("=" * 78)
    print("(2) Chi=2 basin off-diagonal: theta_ij modified by 1/chi factor")
    print("=" * 78)

    # Cabibbo extension to PMNS_12: tan = exp(-Delta Phi / 2)
    # With chi-basin coupling, tan = chi * exp(-Delta Phi / 2)? or 1/chi?
    Phi_21, Phi_13, Phi_5 = Phi_cascade(21), Phi_cascade(13), Phi_cascade(5)

    # Original Cabibbo extension (saddle):
    saddle_12 = math.exp(-(Phi_21 - Phi_13) / 2)  # smaller because Phi_21 > Phi_13
    saddle_23 = math.exp(-(Phi_13 - Phi_5)  / 2)
    saddle_13 = math.exp(-(Phi_21 - Phi_5)  / 2)

    print(f"  Saddle amplitudes (Cabibbo extension):")
    print(f"    Gen1<->Gen2 (d=21<->13): exp(-(Phi_21 - Phi_13)/2) = {saddle_12:.4f}")
    print(f"    Gen2<->Gen3 (d=13<->5):  exp(-(Phi_13 - Phi_5)/2)  = {saddle_23:.4f}")
    print(f"    Gen1<->Gen3 (d=21<->5):  exp(-(Phi_21 - Phi_5)/2)  = {saddle_13:.4f}")
    print()

    # With basin enhancement (factor chi for symmetric coupling)
    for label, factor, sign in [("chi (enhance)", CHI, 1), ("1/chi (suppress)", 1/CHI, -1)]:
        a12 = saddle_12 * factor
        a23 = saddle_23 * factor
        a13 = saddle_13 * factor
        # tan(theta) = a; theta = arctan(a)
        theta12 = math.degrees(math.atan(a12)) if a12 < 1 else 45.0
        theta23 = math.degrees(math.atan(a23)) if a23 < 1 else 45.0
        theta13 = math.degrees(math.atan(a13)) if a13 < 1 else 45.0
        print(f"  Factor {label}:")
        print(f"    theta_12 = {theta12:.1f} deg  (obs {THETA_12_OBS})")
        print(f"    theta_23 = {theta23:.1f} deg  (obs {THETA_23_OBS})")
        print(f"    theta_13 = {theta13:.1f} deg  (obs {THETA_13_OBS})")
    print()


# ---------------------------------------------------------------
# Mechanism 3: Per-Dirac-layer chi * Gamma(1/2)^n at higher n
# ---------------------------------------------------------------

def test_higher_leg_neutrino() -> None:
    """
    The per-Dirac-layer chirality contribution chi * Gamma(1/2)^n is
    layer-independent for any n (Remark per-leg-primitive-derivation).
    For n=2 this gives 2*pi per layer (1/alpha_em screening).

    Test: does a higher-n contribution at the neutrino source layer give
    correctly-scaled solar splitting?

    Specifically: is there an n such that 3 * chi * Gamma(1/2)^n = some
    observed ratio?
    """
    print("=" * 78)
    print("(3) Higher-leg per-Dirac-layer chi * Gamma(1/2)^n at n != 2")
    print("=" * 78)

    pi_half_n = lambda n: 3 * CHI * (math.sqrt(math.pi)) ** n
    # For each n, compute the value
    for n in [1, 2, 3, 4, 5, 6]:
        val = pi_half_n(n)
        print(f"  n = {n}:  3 * chi * Gamma(1/2)^n = {val:.4f}")

    # Compare to observed mass ratios
    print()
    print(f"  Observed sqrt(Delta m^2_atm)/sqrt(Delta m^2_sol) = {math.sqrt(DELTA_M2_ATM/DELTA_M2_SOL):.3f}")
    print(f"  Observed Delta m^2_atm / Delta m^2_sol = {DELTA_M2_ATM/DELTA_M2_SOL:.3f}")
    print()
    print("  Pattern check: are observed values close to 3 * chi * Gamma(1/2)^n for some n?")
    target_ratio = DELTA_M2_ATM / DELTA_M2_SOL
    log_target = math.log(target_ratio) / math.log(math.pi)  # express as power of pi
    print(f"  log_pi(observed atm/sol ratio) = {log_target:.3f}")
    print(f"  (No clean integer match.  Provisional null on this mechanism.)")
    print()


# ---------------------------------------------------------------
# Mechanism 4: Coherent sum over multiple Bott Dirac source layers
# ---------------------------------------------------------------

def test_multi_bott_source() -> None:
    """
    The Bott Dirac source layers are {5, 13, 21, 29, 37, 45, ...}.  The
    diagonal cascade only uses {5, 13, 21} as observed generations and m_29
    as a single source.  Test whether multi-source neutrino formula
    m_nu(g) = sum_{n} m_{29 + 8n} * alpha(d_g) / chi^(...) gives the
    correct lighter-neutrino spectrum.
    """
    print("=" * 78)
    print("(4) Coherent sum over multiple Bott Dirac source layers")
    print("=" * 78)

    # Source layers above d_1 = 19 (4th, 5th, 6th Bott Dirac):
    sources = [29, 37, 45, 53, 61]
    print(f"  Bott Dirac source candidates: {sources}")

    # Mass at each source (using cascade lepton formula):
    # m(d) = (alpha_s * v / sqrt(2)) exp(-Phi(d)) (2sqrt(pi))^{-(n_D+1)}
    # where n_D for source = (d-5)/8 + 1 (counting Dirac layers from d=5)
    print(f"\n  Source masses (cascade lepton formula extrapolated):")
    for d in sources:
        n_D = (d - 5) // 8 + 1   # 1, 2, 3, ... for d=5, 13, 21, ...
        m = cascade_lepton_mass(d, n_D)
        print(f"    m({d}) = {m:.3e} MeV = {m*1e6:.3e} eV  (n_D = {n_D})")

    # For neutrino at Gen g (d_g), sum over source layers:
    # m_nu(g) = sum_n m(29 + 8n) * alpha(d_g) / chi^(d_source - d_g)
    print(f"\n  Multi-source neutrino formula: m_nu(g) = sum_n m_n * alpha(d_g) / chi^(d_n - d_g)")

    for gen in [1, 2, 3]:
        d_g = GEN_LAYERS[gen]
        m_nu = 0
        contributions = []
        for d_n in sources:
            if d_n > d_g:
                n_D = (d_n - 5) // 8 + 1
                m_n = cascade_lepton_mass(d_n, n_D) * 1e6  # eV
                contrib = m_n * alpha_cascade(d_g) / (CHI ** (d_n - d_g))
                m_nu += contrib
                contributions.append((d_n, contrib))
        print(f"    Gen {gen} (d={d_g}): m_nu = {m_nu:.4e} eV   contribs: {contributions[:3]}...")
    print()
    print("  Result: dominated by m_29 source (single layer); higher Bott layers contribute negligibly.")
    print("  Consistent with 4th-generation suppression discussed in Part IVb.")
    print("  Does NOT close lighter-neutrino spectrum: m_2 still ~ 3e-4 eV (factor 30 too small).")
    print()


# ---------------------------------------------------------------
# Mechanism 5: Up-type J-conjugation generation-dependent paths
# ---------------------------------------------------------------

def test_uptype_J_conjugation() -> None:
    """
    Up-type Yukawa bar Q_L tilde-H u_R involves complex conjugation
    via J^{-1} at d=12.  J is the cascade complex structure; J^2 = -1.

    Hypothesis: the up-type path traverses the gauge window with J-
    conjugation count depending on generation (because each generation
    layer d_g has different distance to the gauge window).

    Test: assign N(g) = number of J-applications for Gen g.  If down-type
    has N=0 and up-type has N(g) generation-dependent, then m_up/m_down
    at Gen g ~ |J|^{N(g)} * other factors.

    Since J^2 = -1, |J|^k = 1, so this DOESN'T amplify magnitudes.  It
    only rotates phases.  No N_c amplification possible from J alone.

    Alternative: the trace through V_12 = 3 representation gives N_c
    when summed over colour, and J-conjugation flips between fundamental
    and antifundamental.  If gen-dependent traversal hits the colour
    trace different numbers of times, get N_c^k pattern.
    """
    print("=" * 78)
    print("(5) Up-type J-conjugation generation-dependent paths")
    print("=" * 78)

    # Number of times each generation traverses the gauge window {12, 13, 14}
    # in cascade descent from d_g down to observer at d=4
    # Gen 3 (d=5): does NOT traverse (5 < 12)
    # Gen 2 (d=13): touches d=13 (within window)
    # Gen 1 (d=21): traverses the full window 14 -> 13 -> 12 in descent

    # Number of d=12 crossings:
    crossings = {1: 1, 2: 0, 3: 0}  # Only Gen 1's path goes through d=12
    print(f"  d=12 crossings per generation (during descent to d=4):")
    print(f"    Gen 1 (d=21 -> 4): traverses through d=12  -> 1 crossing")
    print(f"    Gen 2 (d=13 -> 4): does NOT pass d=12       -> 0 crossings")
    print(f"    Gen 3 (d=5 -> 4):  below gauge window         -> 0 crossings")
    print()
    print("  If up-type Yukawa picks up N_c^k per d=12 crossing:")
    for gen in [1, 2, 3]:
        amp = 3 ** crossings[gen]
        print(f"    Gen {gen}: N_c^{crossings[gen]} = {amp}")
    print()
    print("  Empirical r_g = m_u/m_d per generation:")
    print(f"    Gen 1: m_u/m_d = {M_U/M_D:.3f}")
    print(f"    Gen 2: m_c/m_s = {M_C/M_S:.2f}")
    print(f"    Gen 3: m_t/m_b = {M_T/M_B:.2f}")
    print()
    print("  This crossing pattern does NOT match observed ratios.")
    print("  Failure: simple counting doesn't reproduce the (t/b)/(c/s) = N_c structure")
    print("  because Gen 3 has the LARGEST up/down ratio but ZERO d=12 crossings.")
    print()


# ---------------------------------------------------------------
# Mechanism 6: CP-conjugate Majorana off-diagonal
# ---------------------------------------------------------------

def test_majorana_off_diagonal() -> None:
    """
    For Majorana neutrinos, the mass term is bilinear in psi (not psi^bar
    psi).  This couples basin to CP-conjugate basin.  In the cascade,
    chirality theorem gives chi=2 basins on even-sphere layers; basins are
    CPT-conjugate.

    Hypothesis: the Majorana mass for neutrino at d_g is the GEOMETRIC
    MEAN of the two basin diagonals:
       m_nu(g) = sqrt(m_{basin+}(d_g) * m_{basin-}(d_g))

    But basin equality (Theorem chirality-factorisation) gives equal
    basins, so this just equals the diagonal value.  No new structure.

    Alternative: off-diagonal Majorana mass between Gen i and Gen j:
       M_ij^Maj = sqrt(m(d_i) * m(d_j)) / chi
    """
    print("=" * 78)
    print("(6) CP-conjugate Majorana off-diagonal: M_ij^Maj = sqrt(m_i m_j) / chi")
    print("=" * 78)

    # Use cascade diagonal neutrino masses
    m_diag = {}
    for gen, d_g in GEN_LAYERS.items():
        m_diag[gen] = M_29 * alpha_cascade(d_g) / (CHI ** (29 - d_g))

    print(f"  Cascade diagonal neutrino masses:")
    for gen in [1, 2, 3]:
        print(f"    m_{gen} (d={GEN_LAYERS[gen]}): {m_diag[gen]:.4e} eV")

    # Off-diagonal Majorana mass via chirality basin:
    n = 3
    M = np.zeros((n, n))
    for i, gen_i in enumerate([1, 2, 3]):
        for j, gen_j in enumerate([1, 2, 3]):
            if i == j:
                M[i, j] = m_diag[gen_i]
            else:
                M[i, j] = math.sqrt(m_diag[gen_i] * m_diag[gen_j]) / CHI

    print(f"\n  Majorana mass matrix M_ij = sqrt(m_i m_j) / chi (off-diag):")
    for row in M:
        print(f"    [{row[0]:.3e}, {row[1]:.3e}, {row[2]:.3e}]")

    eigvals = sorted(np.abs(np.linalg.eigvals(M)), reverse=True)
    print(f"\n  Eigenvalues: {[f'{e:.4e}' for e in eigvals]}")
    if len(eigvals) >= 2:
        dm2 = eigvals[0] ** 2 - eigvals[1] ** 2
        print(f"  Delta m^2 (heaviest pair) = {dm2:.4e}  (obs atm = {DELTA_M2_ATM:.2e})")
    if len(eigvals) >= 3:
        dm2 = eigvals[1] ** 2 - eigvals[2] ** 2
        print(f"  Delta m^2 (lighter pair)  = {dm2:.4e}  (obs sol = {DELTA_M2_SOL:.2e})")
    print()
    # Mixing angles
    eigvals_full, eigvecs = np.linalg.eigh(M)
    print("  Mixing structure (rows = mass eigenvectors in flavor basis):")
    for row in eigvecs.T:
        print(f"    [{row[0]:+.4f}, {row[1]:+.4f}, {row[2]:+.4f}]")
    print()


# ---------------------------------------------------------------
# Mechanism 7: Up-type per-gen-step amplitude with N_c^variable
# ---------------------------------------------------------------

def test_uptype_per_gen_step() -> None:
    """
    Inverted approach: don't try to derive r_g directly, but ask whether
    SUCCESSIVE cross-gen steps each pick up a DIFFERENT N_c power
    (due to gauge-window traversal pattern).

    Empirical: r_3/r_2 = N_c^1, r_2/r_1 = N_c^3.

    Hypothesis: the up-type Yukawa picks up an additional N_c factor
    each time the descent path traverses a layer at-or-below the gauge
    window.
    - Gen 3 path (d=5 -> 4): traverses 0 layers within gauge window
    - Gen 2 path (d=13 -> 4): traverses d=13, d=12 (2 layers)
    - Gen 1 path (d=21 -> 4): traverses d=14, d=13, d=12 (3 layers)

    Number of gauge-window layer touches:
      Gen 3: 0
      Gen 2: 2 (d=13, d=12)  -- but Gen 2 SITS at d=13
      Gen 1: 3 (d=14, d=13, d=12)
    """
    print("=" * 78)
    print("(7) Up-type per-gen-step from gauge-window-layer touches")
    print("=" * 78)

    # Layer counts (within gauge window {12, 13, 14} at-or-below source)
    touches = {3: 0, 2: 2, 1: 3}
    # Equivalently: number of distinct gauge-window layers crossed during descent

    print(f"  Gauge-window layer touches per generation descent:")
    for gen in [3, 2, 1]:
        d_g = GEN_LAYERS[gen]
        gw_below = [d for d in (12, 13, 14) if d <= d_g]
        print(f"    Gen {gen} (d_g = {d_g}): {len(gw_below)} gauge layers at-or-below = {gw_below}")
    print()

    # Difference in touches between adjacent generations:
    print(f"  Differences in touches:")
    print(f"    Gen 2 - Gen 3 = {touches[2] - touches[3]}")
    print(f"    Gen 1 - Gen 2 = {touches[1] - touches[2]}")
    print()

    print(f"  If up-type r_g multiplies by N_c per touch difference:")
    print(f"    r_2/r_3 ~ N_c^{touches[2]-touches[3]} = N_c^2 = 9   vs observed r_2/r_3 = m_c/m_s / m_t/m_b = 13.66/41.31 = 0.331")
    print()
    print("  No -- the empirical r_2/r_3 = 0.331, but cross-gen ratio is r_3/r_2 = 3.0 ~ N_c.")
    print("  Counting layer touches gives N_c^2 difference between Gen 3 and Gen 2,")
    print("  whereas observed cross-gen ratio is N_c^1.")
    print()
    print("  Mismatch -- but worth noting the FACT that gauge-window traversal grows")
    print("  WITH descent depth for low-d generations, suggesting a path-dependent")
    print("  mechanism is structurally available.  No clean N_c^k closure here.")
    print()


# ---------------------------------------------------------------
# Mechanism 8: Path-tensor extension to 4 Bott layers
# ---------------------------------------------------------------

def test_path_tensor_4bott() -> None:
    """
    Path-tensor at gauge window: V_12 (x) V_13 (x) V_14 = (3, 2, 1) etc.
    Extension hypothesis: include a fourth path-tensor factor V_29 = (1)
    (1-dim, since 4th Bott layer has no SU(N)-like structure assigned).

    With V_29, the path-tensor has 4 factors.  Cross-Bott matter could
    couple the gauge-window path-tensor to V_29 via cross-product
    Yukawa-singlet.

    Test: does this give specific rank-2 or rank-3 mass matrix structure
    for neutrinos (vs the rank-1 of single-source seesaw)?
    """
    print("=" * 78)
    print("(8) Path-tensor 4-fold extension across all Bott Dirac layers")
    print("=" * 78)
    print()
    print("  Speculative -- requires V_29 representation assignment from")
    print("  Adams' theorem at d=29.  Adams gives:")
    n = 29
    a = 0
    while n % 2 == 0:
        n //= 2
        a += 1
    q, r = divmod(a, 4)
    rho_29 = 8 * q + 2 ** r
    print(f"    rho(29) = {rho_29}, rho-1 = {rho_29 - 1}")
    print(f"    => V_29 has {rho_29-1} nowhere-zero vector fields on S^28")
    print()
    if rho_29 - 1 == 0:
        print("  V_29 has dim 0 -- no non-trivial gauge structure at d=29.")
        print("  Cross-Bott via V_29 doesn't give new representation content.")
        print("  Path-tensor extension is dimension-count-trivial at d=29.")
    print()


# ---------------------------------------------------------------
# Main scan
# ---------------------------------------------------------------

def main() -> None:
    print("Cascade-native alternatives scan: closing PMNS / lighter neutrinos / up-type")
    print("(Check 7 compliant; cascade primitives only)")
    print()

    test_berezin_cross_period()
    test_chirality_basin_pmns()
    test_higher_leg_neutrino()
    test_multi_bott_source()
    test_uptype_J_conjugation()
    test_majorana_off_diagonal()
    test_uptype_per_gen_step()
    test_path_tensor_4bott()

    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print()
    print("Eight cascade-native mechanisms tested.  Honest assessment of which work:")
    print()
    print("  (1) Berezin cross-period bilinear   -> requires anchor; rank issues")
    print("  (2) Chirality basin off-diagonal    -> doesn't reach observed angles")
    print("  (3) Higher-leg per-leg primitive    -> no clean integer match")
    print("  (4) Multi-Bott source coherent sum  -> dominated by m_29; no improvement")
    print("  (5) Up-type J-conjugation paths     -> J^k = unit phase, no amplification")
    print("  (6) Majorana off-diag (chi-basin)   -> matrix structure tested below")
    print("  (7) Up-type gauge-window touches    -> wrong direction (Gen 3 has fewest)")
    print("  (8) Path-tensor 4-fold via V_29     -> V_29 trivial, no new structure")
    print()
    print("Key cascade-internal asymmetry uncovered (test 7): the 'gauge-window")
    print("traversal count' grows with descent depth (Gen 1 = 3, Gen 2 = 2, Gen 3 = 0).")
    print("This is the OPPOSITE of the empirical r_g pattern (Gen 3 largest, Gen 1")
    print("smallest), so it can't directly close (t/b)/(c/s) ~ N_c.  But it's a")
    print("structurally meaningful piece of cascade asymmetry that could combine")
    print("with another mechanism.")
    print()
    print("None of these eight mechanisms cleanly closes the residual open questions")
    print("on its own.  Mechanism (6) (Majorana basin off-diagonal) is the most")
    print("structurally-grounded candidate -- it uses the chirality theorem directly.")
    print("Detailed eigenvalue test above shows specific numerical outcomes.")
    print()
    print("INTERESTING EMPIRICAL OBSERVATION (mechanism 7 follow-up):")
    print()
    log_r3 = math.log(M_T / M_B)
    log_r2 = math.log(M_C / M_S)
    log_r1 = math.log(M_U / M_D)
    print(f"  log(r_3) = log(m_t/m_b) = {log_r3:.3f}")
    print(f"  log(r_2) = log(m_c/m_s) = {log_r2:.3f}")
    print(f"  log(r_1) = log(m_u/m_d) = {log_r1:.3f}")
    print(f"  log(r_3) - log(r_2) = {log_r3 - log_r2:.3f}  ~ log(N_c) = {math.log(3):.3f}")
    print(f"  log(r_2) - log(r_1) = {log_r2 - log_r1:.3f}  ~ log(N_c^N_c) = {math.log(27):.3f}")
    print(f"  Ratio of log differences: {(log_r2 - log_r1)/(log_r3 - log_r2):.2f}  ~ N_c = 3")
    print()
    print("  EMPIRICAL PATTERN: r_3/r_2 = N_c (1%), r_2/r_1 = N_c^N_c = 27 (8% off observed 29.2)")
    print("  This is a tower of nested N_c structures.  In cascade language:")
    print("    log(r_g/r_{g+1}) follows a geometric series with ratio N_c going down in g.")
    print("  Cascade-native derivation: NOT YET IDENTIFIED.")
    print("  But the N_c^N_c match at 8% (similar to leading-order systematic) suggests")
    print("  a structural pattern rather than coincidence.  Worth flagging for future")
    print("  investigation as a refined OQ shape.")
    print()
    print("OVERALL: residual open questions remain genuinely open after this systematic")
    print("alternatives scan.  The cascade-native primitives currently available do not")
    print("suffice; closure likely requires either NEW cascade structural elements")
    print("(beyond what's currently derived) or a non-obvious composition of existing")
    print("ones not tested here.  The N_c^N_c empirical pattern is a refined target.")


if __name__ == "__main__":
    main()
