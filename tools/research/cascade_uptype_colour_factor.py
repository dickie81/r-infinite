#!/usr/bin/env python3
"""
Roadmap item 4: up-type quark colour factor (t/b)/(c/s) ~ N_c.

CONTEXT
=======
Part IVb Roadmap item 4 (currently open):

  "Complete the quark mass spectrum.  The ratio (t/b)/(c/s) = 3.04 ~ N_c
   suggests an additional colour factor from the Weyl chirality
   decomposition at d=12.  Computing this from the cascade's own spinor
   structure at S^11 would complete the quark sector."

The cascade has the following relevant structure already derived:

(1) Lepton mass formula (Theorem complete-mass, Part IVb):
    m_l(d_g) = (alpha_s v / sqrt(2)) exp(-Phi(d_g)) (2 sqrt(pi))^(-(n_D+1))

(2) Georgi-Jarlskog down-type pattern (Part IVb thm:gj):
    m_b/m_tau = N_c       (Gen 3, d=5,  outside gauge window)
    m_s/m_mu  = 1/N_c     (Gen 2, d=13, inside gauge window)
    m_d/m_e   = N_c       (Gen 1, d=21, outside gauge window)

(3) Cascade hypercharge spectrum (Part IVb thm:sector-fundamental-y):
    |Y_Q_L|  = 1/(2 N_c) = 1/6        [sector-fundamental of (3,2)]
    |Y_d_R|  = 1/N_c     = 1/3        [sector-fundamental of (3,1) at k=1]
    |Y_u_R|  = 2/N_c     = 2/3        [k=2 lattice point of (3,1) via Yukawa singlet]
    |Y_L_L|  = 1/2                    [sector-fundamental of (1,2)]
    |Y_e_R|  = 1                      [sector-fundamental of (1,1)]
    |Y_H|    = 1/2                    [sector-fundamental of (1,2)]

(4) d=12 structural primitives:
    - Spinor type: COMPLEX WEYL (Bott mirror of d=4)
    - Adams: rho(12) - 1 = 3 = N_c
    - Path-tensor V_12 = 3 for color-charged matter (CLAUDE.md `rem:fund-or-trivial`)
    - Complex structure J at d=12 with J^2 = -1
    - Weyl-chirality decomposition of psi at d=12: psi = psi_+ + psi_-

(5) The SM Yukawa structure couples down-type via H, up-type via
    H-tilde = i sigma_2 H^*.  The conjugation H -> H* is the action of
    J^{-1} = -J at d=12.

THE QUESTION
============
Observed: (m_t/m_b)/(m_c/m_s) = 3.04 ~ N_c.

Can a cascade-native mechanism derive this?  Test six candidate
mechanisms.  Per CLAUDE.md Check 7, semiclassical procedures are
inadmissible -- so candidates here are restricted to cascade-internal
ingredients.

EMPIRICAL RATIOS (low energy, PDG 2024)
---------------------------------------
   m_t = 172.69 GeV,  m_b = 4.18 GeV
   m_c = 1.27 GeV,    m_s = 93 MeV
   m_u = 2.2 MeV,     m_d = 4.7 MeV

   r_3 = m_t/m_b = 41.31  (Gen 3 up/down)
   r_2 = m_c/m_s = 13.66  (Gen 2 up/down)
   r_3/r_2 = 3.024 ~ N_c (1.5%)

CASCADE LEPTON RATIOS (Theorem complete-mass, closed)
-----------------------------------------------------
   m_tau/m_mu = exp(Phi(13) - Phi(5)) * (2 sqrt(pi)) = 16.83
   m_mu/m_e   = exp(Phi(21) - Phi(13)) * (2 sqrt(pi)) = 207
"""

from __future__ import annotations

import math
from fractions import Fraction


# --- Cascade primitives ---

def gamma(x: float) -> float:
    return math.gamma(x)


def N_d(d: int) -> float:
    return math.sqrt(math.pi) * gamma((d + 1) / 2) / gamma((d + 2) / 2)


def R_d(d: int) -> float:
    return gamma(d / 2 + 1) / gamma((d + 3) / 2)


def Phi_cascade(d: int) -> float:
    """Cascade potential from observer at d=4 down to d=d_g (sum of -ln N(d'))."""
    if d <= 4:
        return 0.0
    return sum(-math.log(N_d(dprime)) for dprime in range(5, d + 1))


def alpha_cascade(d: int) -> float:
    return R_d(d) ** 2 / 4.0


# --- Constants ---

N_C = 3
CHI = 2  # Euler characteristic of even spheres
TWO_SQRT_PI = 2 * math.sqrt(math.pi)

# PDG 2024 values (low-energy, MS-bar where appropriate)
M_T_OBS = 172.69e3   # MeV
M_B_OBS = 4.18e3
M_C_OBS = 1.27e3
M_S_OBS = 93.0
M_U_OBS = 2.2
M_D_OBS = 4.7
M_TAU_OBS = 1776.86
M_MU_OBS = 105.66
M_E_OBS = 0.511

GENERATIONS = {3: 5, 2: 13, 1: 21}  # gen -> d_g
N_D_COUNT = {3: 1, 2: 2, 1: 3}      # gen -> n_D in mass formula


def cascade_lepton_ratio(g_top: int, g_bot: int) -> float:
    """m_l(g_top) / m_l(g_bot) from Theorem complete-mass."""
    d_top = GENERATIONS[g_top]
    d_bot = GENERATIONS[g_bot]
    nD_top = N_D_COUNT[g_top]
    nD_bot = N_D_COUNT[g_bot]
    return (math.exp(-Phi_cascade(d_top) + Phi_cascade(d_bot))
            * TWO_SQRT_PI ** ((nD_bot + 1) - (nD_top + 1)))


def main() -> None:
    print("=" * 78)
    print("Roadmap item 4: up-type quark colour factor (t/b)/(c/s) ~ N_c")
    print("=" * 78)
    print()

    # ---------------------------------------------------------------
    # Step 0: empirical observation
    # ---------------------------------------------------------------
    r3 = M_T_OBS / M_B_OBS
    r2 = M_C_OBS / M_S_OBS
    r1 = M_U_OBS / M_D_OBS
    print("STEP 0: empirical up/down quark ratios per generation")
    print("-" * 78)
    print(f"  r_3 = m_t/m_b   = {r3:.3f}     (Gen 3 up/down)")
    print(f"  r_2 = m_c/m_s   = {r2:.3f}     (Gen 2 up/down)")
    print(f"  r_1 = m_u/m_d   = {r1:.3f}     (Gen 1 up/down)")
    print()
    print(f"  r_3 / r_2 = {r3/r2:.3f}  vs  N_c = {N_C}    (deviation {abs(r3/r2-N_C)/N_C*100:.2f}%)")
    print(f"  r_2 / r_1 = {r2/r1:.3f}  vs  N_c = {N_C}    (deviation {abs(r2/r1-N_C)/N_C*100:.2f}%)")
    print()
    print(f"  Per-generation up/down ratios r_g themselves are NOT N_c:")
    print(f"  {r3:.1f}, {r2:.1f}, {r1:.2f} -- they grow but not uniformly per step.")
    print()

    # ---------------------------------------------------------------
    # Step 1: cascade lepton ratios as baseline
    # ---------------------------------------------------------------
    print("STEP 1: cascade lepton ratios (Theorem complete-mass, closed)")
    print("-" * 78)
    tau_mu = cascade_lepton_ratio(3, 2)
    mu_e = cascade_lepton_ratio(2, 1)
    print(f"  cascade m_tau/m_mu = exp(Phi(13)-Phi(5)) * 2sqrt(pi) = {tau_mu:.3f}")
    print(f"  cascade m_mu/m_e   = exp(Phi(21)-Phi(13)) * 2sqrt(pi) = {mu_e:.3f}")
    print(f"  observed m_tau/m_mu = {M_TAU_OBS/M_MU_OBS:.3f}")
    print(f"  observed m_mu/m_e   = {M_MU_OBS/M_E_OBS:.3f}")
    print()

    # ---------------------------------------------------------------
    # Step 2: cascade Georgi-Jarlskog down-type prediction
    # ---------------------------------------------------------------
    print("STEP 2: cascade Georgi-Jarlskog down-type prediction (closed)")
    print("-" * 78)
    gj_factor = {3: N_C, 2: 1.0/N_C, 1: N_C}
    bs_pred = (gj_factor[3] * tau_mu * (1.0/gj_factor[2]))  # m_b/m_s
    bs_obs = M_B_OBS / M_S_OBS
    print(f"  cascade m_b/m_s = N_c * (m_tau/m_mu) * N_c = {bs_pred:.2f}  (GUT scale)")
    print(f"  observed m_b/m_s (low energy) = {bs_obs:.2f}")
    print(f"  Note: GUT-to-low-energy running shrinks down-type ratio by ~factor 3.3.")
    print()

    # ---------------------------------------------------------------
    # Step 3: candidate mechanisms for up-type extra N_c per gen
    # ---------------------------------------------------------------
    print("STEP 3: cascade-native candidate mechanisms for up-type extra N_c")
    print("-" * 78)
    print()

    # --- Mechanism A: hypercharge amplitude ratio |Y_u|/|Y_d| = 2 ---
    Y_uR = Fraction(2, 3)
    Y_dR = Fraction(1, 3)
    print(f"  (A) Hypercharge amplitude: |Y_u_R|/|Y_d_R| = {Y_uR}/{Y_dR} = {float(Y_uR/Y_dR):.3f}")
    print(f"      Predicts uniform up/down ratio = 2.  Observed: r_3={r3:.1f}, r_2={r2:.1f}, r_1={r1:.2f}")
    print(f"      VERDICT: FAILS.  Per-gen up/down ratios are NOT 2 (or any constant).")
    print()

    # --- Mechanism B: hypercharge squared (gauge coupling amplitude) ---
    print(f"  (B) Hypercharge squared: (|Y_u|/|Y_d|)^2 = {float((Y_uR/Y_dR)**2):.3f}")
    print(f"      Predicts uniform up/down ratio = 4.  Same per-gen ratio mismatch.")
    print(f"      VERDICT: FAILS.")
    print()

    # --- Mechanism C: direct N_c trace at d=12 (uniform) ---
    print(f"  (C) Uniform N_c trace at d=12: m_u/m_d = N_c = {N_C} (every generation)")
    print(f"      Predicts r_3 = r_2 = r_1 = {N_C}.  Empirical: 41.3, 13.7, 0.47.")
    print(f"      Predicts (t/b)/(c/s) = 1, NOT N_c.  Doesn't match observation.")
    print(f"      VERDICT: FAILS.")
    print()

    # --- Mechanism D: Weyl chirality x N_c at d=12 ---
    weyl_x_nc = CHI * N_C
    print(f"  (D) Weyl chirality x N_c: chi * N_c = {CHI} * {N_C} = {weyl_x_nc}")
    print(f"      Same uniform structure as (C); same failure mode.")
    print(f"      VERDICT: FAILS.")
    print()

    # --- Mechanism E: Generation-dependent (outside-window only) ---
    print(f"  (E) Outside-window-only N_c factor for up-type:")
    print(f"      Gen 3 (d=5 outside): up gets N_c = 3 extra  -> r_3_pred = N_c * down_factor_3")
    print(f"      Gen 2 (d=13 inside): up gets 1 extra        -> r_2_pred = down_factor_2")
    print(f"      Gen 1 (d=21 outside): up gets N_c = 3 extra -> r_1_pred = N_c * down_factor_1")
    print()
    print(f"      Predicts r_3 = {N_C}, r_2 = 1, r_1 = {N_C}.")
    print(f"      Empirical: r_3 = {r3:.1f}, r_2 = {r2:.1f}, r_1 = {r1:.2f}.")
    print(f"      Predicts (t/b)/(c/s) = N_c/1 = {N_C} = N_c.")
    print(f"      Predicts (c/s)/(u/d) = 1/N_c = {1.0/N_C:.3f}.  Empirical: {r2/r1:.2f}.")
    print(f"      VERDICT: gives correct (t/b)/(c/s) = N_c BUT predicts r_2 = 1 vs observed 13.7.")
    print(f"      Per-gen up/down magnitudes wrong; only the cross-gen ratio is right.")
    print()

    # --- Mechanism F: per-step N_c amplification, Weyl chirality at d=12 ---
    print(f"  (F) Per-generation-step N_c amplification (Weyl chirality at d=12):")
    print(f"      Hypothesis: each generation step (Gen g+1 -> Gen g) crosses the gauge")
    print(f"      window once, picking up an additional N_c factor for up-type only.")
    print(f"      Mechanism: complex Weyl at d=12 has two halves; up uses J-conjugated half")
    print(f"      via H-tilde, picking up an extra colour-trace factor of N_c per traversal.")
    print()
    print(f"      Predicts: r_3 / r_2 = N_c, r_2 / r_1 = N_c (both cross-gen ratios = N_c).")
    print(f"      Empirical: r_3/r_2 = {r3/r2:.2f}, r_2/r_1 = {r2/r1:.2f}.")
    print(f"      Top step matches at 1.5%; bottom step is N_c^~3, not N_c.")
    print()
    print(f"      VERDICT: works for (t/b)/(c/s) but FAILS for (c/s)/(u/d).")
    print()

    # ---------------------------------------------------------------
    # Step 4: structural test of the (F) mechanism
    # ---------------------------------------------------------------
    print("STEP 4: testing mechanism (F) more carefully")
    print("-" * 78)
    K_2 = r2 / N_C
    K_3 = r3 / (N_C ** 2)
    K_1 = r1
    print(f"  If r_g = K * N_c^(g-1) with g=1,2,3:")
    print(f"    K from r_3 = {r3:.2f} -> K = {K_3:.3f}")
    print(f"    K from r_2 = {r2:.2f} -> K = {K_2:.3f}")
    print(f"    K from r_1 = {r1:.2f} -> K = {K_1:.3f}")
    print(f"  Residual K_3/K_2 = {K_3/K_2:.3f}, K_2/K_1 = {K_2/K_1:.3f}")
    print(f"  -> K is NOT constant: pure r_g ~ N_c^(g-1) form fails on Gen 1.")
    print()
    print(f"  Alternative: r_g = K * N_c^x_g with non-uniform x_g.")
    print(f"  Solving: log(r_g)/log(N_c) gives x_g + log(K)/log(N_c).")
    print(f"    log(r_3)/log(N_c) = {math.log(r3)/math.log(N_C):.3f}")
    print(f"    log(r_2)/log(N_c) = {math.log(r2)/math.log(N_C):.3f}")
    print(f"    log(r_1)/log(N_c) = {math.log(r1)/math.log(N_C):.3f}")
    print(f"  Differences (Delta_x):")
    print(f"    x_3 - x_2 = {(math.log(r3)-math.log(r2))/math.log(N_C):.3f} ~ 1.0  (cross-gen N_c factor)")
    print(f"    x_2 - x_1 = {(math.log(r2)-math.log(r1))/math.log(N_C):.3f} ~ 1.95 ~ 2 (NOT N_c)")
    print()
    print(f"  CRITICAL FINDING: Gen 2 -> Gen 1 step is N_c^~3, not N_c^1.")
    print(f"  The cross-gen ratio (t/b)/(c/s) = N_c is a TWO-OUT-OF-THREE pattern;")
    print(f"  (c/s)/(u/d) is closer to N_c^3 than N_c.  The 'Weyl chirality at d=12'")
    print(f"  hypothesis would predict uniform N_c per step, which is NOT what we see.")
    print()

    # ---------------------------------------------------------------
    # Step 5: status assessment
    # ---------------------------------------------------------------
    print("STEP 5: status assessment")
    print("-" * 78)
    print()
    print("  Roadmap item 4 was framed as: 'additional colour factor of N_c from Weyl")
    print("  chirality at d=12 would complete the up-type spectrum'.  Numerical test:")
    print()
    print("  - Cross-gen (t/b)/(c/s) = N_c at 1.5%: STRUCTURALLY CONSISTENT with one")
    print("    extra N_c per generation-step crossing.")
    print("  - Cross-gen (c/s)/(u/d) ~ 29 ~ N_c^3: NOT consistent with the same mechanism.")
    print("  - The 'uniform N_c per step' Weyl-chirality hypothesis is therefore")
    print("    NOT borne out across both cross-gen pairs.")
    print()
    print("  Two possibilities:")
    print()
    print("  (a) The pattern (t/b)/(c/s) = N_c is a Gen-3-vs-Gen-2-specific structural")
    print("      feature (NOT a universal per-gen-step N_c rule), perhaps tied to the")
    print("      cascade's gauge-window position: Gen 2 sits AT the SU(2) layer d=13")
    print("      (inside the window), while Gen 3 at d=5 is OUTSIDE.  The N_c factor")
    print("      is the path-traversal of the gauge window between Gen 3 and Gen 2.")
    print()
    print("      For Gen 2 -> Gen 1, both d=13 and d=21 are at-or-outside the window,")
    print("      so no extra N_c factor; instead some other (different) cascade")
    print("      mechanism gives the observed N_c^~3 amplification.")
    print()
    print("  (b) The cascade does not predict the up-type spectrum cleanly; the")
    print("      observed (t/b)/(c/s) ~ N_c is a lower-precision approximation than")
    print("      the closed lepton/down-type predictions, and a clean Weyl-chirality-")
    print("      at-d=12 derivation is not available with current cascade ingredients.")
    print()
    print("  Per CLAUDE.md Check 7, semiclassical procedures (Coleman-Weinberg potentials")
    print("  on cascade spheres, Bogoliubov mixing, KK reduction) are out of bounds.")
    print("  A cascade-native closure must derive the up-type structure from existing")
    print("  ingredients: chirality theorem (chi=2 basins), Adams (N_c=3), path-tensor,")
    print("  hypercharge spectrum (Y_u=2/3 vs Y_d=1/3).")
    print()
    print("  STATUS: Roadmap item 4 partially clarified but not closed.")
    print("  The 'Weyl chirality at d=12 -> extra N_c per generation-step' hypothesis is")
    print("  consistent with (t/b)/(c/s) = N_c at 1.5% but inconsistent with the")
    print("  Gen-2-to-Gen-1 step where (c/s)/(u/d) ~ N_c^3 is observed.  A clean cascade-")
    print("  internal mechanism that distinguishes the Gen-3-vs-Gen-2 step from the")
    print("  Gen-2-vs-Gen-1 step is required.")
    print()


if __name__ == "__main__":
    main()
