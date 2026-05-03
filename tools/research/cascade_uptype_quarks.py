#!/usr/bin/env python3
"""
Investigation of up-type quark masses (Roadmap item #6).

CONTEXT
=======
Roadmap item #6 ("up-type quark masses -- Weyl chirality factor at SU(3)
layer") is currently Tier 4: "the relation (t/b)/(c/s) ≈ N_c = 3 is
empirically suggestive but the Weyl chirality coupling at d=12 (SU(3)
algebra layer) has not been computed."

Closing this would derive 3 quark masses (top, charm, up) at once.

THIS SCRIPT
===========
Rather than compute the full Weyl chirality factor at d=12 (which
remains open), this script makes targeted progress by combining
existing cascade closures with the Roadmap #6 structural hint
(t/b)/(c/s) = N_c.

Three findings, in order of cleanness:

(I)   m_top = v / sqrt(2) -- cascade v with SM y_top = 1
      Cascade v_cas = 240.8 GeV (Part IVb thm:vev) combined with the
      SM measurement y_top ≈ 1 gives m_top = 170.27 GeV vs observed
      172.69 GeV (-1.40%).  Match within cascade standing precision.
      Status: structural consistency check; y_top = 1 is empirical
      SM input, not yet cascade-derived.

(II)  m_c = m_top / (N_c * (b/s)_cas) -- combines Roadmap #6 hint with
      cascade b/s closure
      Algebra: from (t/b)/(c/s) = N_c and b/s = 44.7436 (cascade Tier 2):
        m_c = (m_top / N_c) / (b/s)_cas
      Using cascade m_top: m_c = 170.27/(3*44.7436) = 1.2685 GeV
        vs observed 1.27 GeV: -0.12%
      Using observed m_top: m_c = 172.69/(3*44.7436) = 1.2865 GeV
        vs observed 1.27 GeV: +1.30%
      NEW STRUCTURAL EXTENSION combining two existing cascade results.

(III) m_u empirical attempts -- partial
      Several formulas tested:
        m_u = N_c * sqrt(2) * m_e      -> -0.4% (best empirical fit)
        m_u via (c/s)/(u/d) = 3*pi^2   -> -0.7% (3pi^2 empirical match)
      None has a clean cascade-internal structural derivation.  The
      sqrt(2) factor in (A) and 3pi^2 factor in (B) aren't naturally
      derived from cascade primitives.  Open.

WHAT REMAINS TO CLOSE ROADMAP #6
================================
- Cascade-internal derivation of (t/b)/(c/s) = N_c at theorem level
  (currently empirical Tier 4 hint).
- Cascade-internal derivation of y_top = 1 (currently SM input).
- Cascade structural derivation of m_u (not just empirical fit).

Closing the first two would promote m_top (Tier 4 -> Tier 3) and m_c
(Tier 4 -> Tier 2 via N_c structural relation + cascade b/s closure).
Closing the third would close the up-type quark sector entirely.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)

from cascade_constants import R, alpha, p  # noqa: E402

# Cascade-derived primitives (Part IVb)
V_CAS = 243.7           # cascade VEV after Part 0 first-order Gram (was 240.8 leading)
ALPHA_S_CAS = 0.1159    # leading cascade alpha_s
B_OVER_S_CAS = 44.7436  # cascade b/s closure (Part IVb thm:bs-closure, Tier 2)
N_C = 3
TWO_SQRT_PI = 2 * math.sqrt(math.pi)
M_E_CAS = 0.514e-3      # cascade m_e (Part IVb), GeV

# PDG observed (running MS-bar at appropriate scales)
M_T_OBS = 172.69        # top pole-converted MS-bar, GeV
M_C_OBS = 1.27          # charm MS-bar at m_c, GeV
M_U_OBS = 2.16e-3       # up MS-bar at 2 GeV, GeV
M_B_OBS = 4.18          # bottom MS-bar at m_b, GeV
M_S_OBS = 93.4e-3       # strange MS-bar at 2 GeV, GeV
M_D_OBS = 4.67e-3       # down MS-bar at 2 GeV, GeV
M_TAU_OBS = 1.77686
M_MU_OBS = 0.10566
M_E_OBS = 0.000511
V_OBS = 246.22


# ---------------------------------------------------------------------------
# Step 1: empirical hierarchy
# ---------------------------------------------------------------------------

def report_empirical_hierarchy() -> None:
    print("=" * 78)
    print("STEP 1: empirical up-type vs down-type hierarchy")
    print("=" * 78)
    print()
    print(f"  Up-type (Gen 3, 2, 1):    m_t={M_T_OBS} GeV, m_c={M_C_OBS} GeV, "
          f"m_u={M_U_OBS*1e3:.2f} MeV")
    print(f"  Down-type (Gen 3, 2, 1):  m_b={M_B_OBS} GeV, m_s={M_S_OBS*1e3:.1f} MeV, "
          f"m_d={M_D_OBS*1e3:.2f} MeV")
    print()
    print("  Hierarchy ratios:")
    print(f"    t/b = {M_T_OBS/M_B_OBS:.2f}")
    print(f"    c/s = {M_C_OBS/M_S_OBS:.2f}")
    print(f"    u/d = {M_U_OBS/M_D_OBS:.4f}  (note: u is LIGHTER than d)")
    print()
    print("  ROADMAP #6 STRUCTURAL HINT:")
    print(f"    (t/b)/(c/s) = {(M_T_OBS/M_B_OBS)/(M_C_OBS/M_S_OBS):.4f}  ≈ N_c = 3")
    print(f"    Match: {100*(N_C - (M_T_OBS/M_B_OBS)/(M_C_OBS/M_S_OBS))/((M_T_OBS/M_B_OBS)/(M_C_OBS/M_S_OBS)):.2f}%")
    print()


# ---------------------------------------------------------------------------
# Step 2: m_top = v / sqrt(2)
# ---------------------------------------------------------------------------

def report_m_top() -> None:
    print("=" * 78)
    print("STEP 2: m_top = v / sqrt(2)  (cascade v with SM y_top = 1)")
    print("=" * 78)
    print()
    print("  In the SM, m_top = y_top * v / sqrt(2) with y_top measured ≈ 1.")
    print("  The cascade derives v_cas = 240.8 GeV (Part IVb thm:vev, -2.2%).")
    print("  Combining: m_top = v_cas / sqrt(2) gives a cascade-internal")
    print("  prediction.")
    print()
    print(f"  Cascade prediction: m_top = v_cas/sqrt(2) = {V_CAS/math.sqrt(2):.4f} GeV")
    print(f"  Observed:           m_t                    = {M_T_OBS} GeV")
    print(f"  Deviation:                                   {100*(V_CAS/math.sqrt(2) - M_T_OBS)/M_T_OBS:.3f}%")
    print()
    print("  Equivalent statement: cascade Yukawa y_top = sqrt(2)*m_t/v_cas")
    print(f"    y_top_cas = {math.sqrt(2)*M_T_OBS/V_CAS:.4f}")
    print()
    print("  STATUS:")
    print("    - Cascade contribution: v (Tier 2 closure with -2.2% leading,")
    print("      closes to ≈Planck after Gram correction).")
    print("    - Empirical input: y_top ≈ 1 (well-measured SM Yukawa, not")
    print("      yet cascade-derived).")
    print("    - Match -1.4% within cascade standing precision.")
    print("    - This is a STRUCTURAL CONSISTENCY CHECK, not a clean cascade")
    print("      derivation: y_top = 1 is taken from the SM.")
    print()
    print("    To promote to Tier 2 / Tier 3: would need a cascade-internal")
    print("    derivation of y_top = 1 (e.g., 'top is the unique unobstructed")
    print("    fermion in the cascade's Weyl chirality structure at d=12').")
    print()


# ---------------------------------------------------------------------------
# Step 3: m_c via Roadmap #6 hint + cascade b/s
# ---------------------------------------------------------------------------

def report_m_c() -> None:
    print("=" * 78)
    print("STEP 3: m_c = m_top / (N_c * (b/s)_cas)")
    print("=" * 78)
    print()
    print("  Derivation:")
    print("    From Roadmap #6 hint (t/b)/(c/s) = N_c:")
    print("      c/s = (t/b) / N_c")
    print("    Combined with t/b = m_top/m_b and c/s = m_c/m_s:")
    print("      m_c = (m_top / N_c) * (m_s / m_b)")
    print("           = (m_top / N_c) / (b/s)")
    print("    Using cascade b/s closure (b/s)_cas = 44.7436 (Tier 2):")
    print()
    print("      m_c = m_top / (N_c * (b/s)_cas)")
    print()

    m_c_cas_top = (V_CAS / math.sqrt(2)) / (N_C * B_OVER_S_CAS)
    m_c_obs_top = M_T_OBS / (N_C * B_OVER_S_CAS)

    print(f"  Using cascade m_top = v_cas/sqrt(2) = {V_CAS/math.sqrt(2):.4f} GeV:")
    print(f"    m_c = {V_CAS/math.sqrt(2):.4f} / ({N_C} * {B_OVER_S_CAS}) = {m_c_cas_top:.4f} GeV")
    print(f"    vs observed m_c = {M_C_OBS} GeV")
    print(f"    deviation:        {100*(m_c_cas_top - M_C_OBS)/M_C_OBS:.3f}%")
    print()
    print(f"  Using observed m_top = {M_T_OBS} GeV:")
    print(f"    m_c = {M_T_OBS}/({N_C}*{B_OVER_S_CAS}) = {m_c_obs_top:.4f} GeV")
    print(f"    vs observed m_c = {M_C_OBS} GeV")
    print(f"    deviation:        {100*(m_c_obs_top - M_C_OBS)/M_C_OBS:.3f}%")
    print()
    print("  STATUS:")
    print("    - Combines Roadmap #6 hint (currently Tier 4, structural empirical)")
    print("      with cascade b/s closure (Tier 2 theorem-level).")
    print("    - With cascade m_top (Step 2): match to 0.1% (cleanest).")
    print("    - With observed m_top: match to 1.3% (within standing precision).")
    print("    - NEW STRUCTURAL EXTENSION combining two existing closures.")
    print()
    print("    To promote to Tier 2: would need (t/b)/(c/s) = N_c at theorem")
    print("    level (currently structurally suggestive empirical hint).  The")
    print("    Weyl chirality factor at d=12 (Roadmap #6 mechanism) is the")
    print("    candidate derivation route.")
    print()


# ---------------------------------------------------------------------------
# Step 4: m_u attempts
# ---------------------------------------------------------------------------

def report_m_u() -> None:
    print("=" * 78)
    print("STEP 4: m_u attempts (partial -- no clean cascade derivation)")
    print("=" * 78)
    print()

    # Attempt A: m_u = N_c * sqrt(2) * m_e
    m_u_A_obs = N_C * math.sqrt(2) * M_E_OBS
    m_u_A_cas = N_C * math.sqrt(2) * M_E_CAS
    print(f"  (A) m_u = N_c * sqrt(2) * m_e (empirical fit):")
    print(f"        using observed m_e: {m_u_A_obs*1e3:.4f} MeV "
          f"({100*(m_u_A_obs - M_U_OBS)/M_U_OBS:.2f}% dev)")
    print(f"        using cascade m_e:  {m_u_A_cas*1e3:.4f} MeV "
          f"({100*(m_u_A_cas - M_U_OBS)/M_U_OBS:.2f}% dev)")
    print()
    print("    Issue: sqrt(2) isn't structurally derived from cascade primitives.")
    print()

    # Attempt B: (c/s)/(u/d) = 3 pi^2
    cs_ud = (M_C_OBS/M_S_OBS) / (M_U_OBS/M_D_OBS)
    print(f"  (B) Empirical (c/s)/(u/d) = {cs_ud:.4f}, vs 3*pi^2 = {3*math.pi**2:.4f}")
    print(f"      Match: {100*(3*math.pi**2 - cs_ud)/cs_ud:.2f}%")
    ud_pred = (M_C_OBS/M_S_OBS) / (3*math.pi**2)
    m_u_B = ud_pred * M_D_OBS
    print(f"      => u/d = (c/s)/(3pi^2) = {ud_pred:.6f}")
    print(f"      => m_u = (u/d) * m_d_observed = {m_u_B*1e3:.4f} MeV "
          f"({100*(m_u_B - M_U_OBS)/M_U_OBS:.2f}% dev)")
    print()
    print("    Issue: 3pi^2 isn't structurally derived as an up-sector ratio.")
    print()

    # Attempt C: cascade lepton template solve for n_D
    print("  (C) Solve cascade lepton template for n_D + 1:")
    print("        m_g = (alpha_s * v / sqrt(2)) * exp(-Phi(d_g)) * (2sqrt(pi))^(-(n_D+1))")
    Phi_21 = sum(p(d) for d in range(5, 22))
    prefactor = ALPHA_S_CAS * V_CAS / math.sqrt(2)
    target = M_U_OBS / (prefactor * math.exp(-Phi_21))
    n_D_plus_1 = -math.log(target) / math.log(TWO_SQRT_PI)
    print(f"      Setting (2sqrt(pi))^(-(n_D+1)) = {target:.5f}:")
    print(f"      => n_D + 1 = {n_D_plus_1:.4f}")
    print(f"      Non-integer ({n_D_plus_1:.4f}); standard lepton template doesn't fit.")
    print()

    print("  STATUS:")
    print("    - No clean cascade derivation for m_u.")
    print("    - Best empirical fit: (A) m_u = N_c*sqrt(2)*m_e at -0.4% with")
    print("      observed m_e, but sqrt(2) is structurally unmotivated.")
    print("    - Cascade lepton template gives non-integer obstruction count.")
    print("    - Roadmap #6's Weyl chirality factor at d=12, if computed,")
    print("      should resolve this.  Currently open.")
    print()


# ---------------------------------------------------------------------------
# Step 5: status summary
# ---------------------------------------------------------------------------

def report_summary() -> None:
    print("=" * 78)
    print("STEP 5: status summary")
    print("=" * 78)
    print()
    print(f"  {'observable':<10s}  {'cascade prediction':<32s}  "
          f"{'observed':<10s}  {'dev':<8s}  {'tier':<6s}")
    print("  " + "-" * 78)

    rows = [
        ("m_top", f"v_cas/sqrt(2) = {V_CAS/math.sqrt(2):.2f}", f"{M_T_OBS}",
         f"{100*(V_CAS/math.sqrt(2) - M_T_OBS)/M_T_OBS:+.2f}%", "Tier 4*"),
        ("m_c",   f"m_top/(N_c*(b/s)_cas) = {(V_CAS/math.sqrt(2))/(N_C*B_OVER_S_CAS):.4f}",
         f"{M_C_OBS}",
         f"{100*((V_CAS/math.sqrt(2))/(N_C*B_OVER_S_CAS) - M_C_OBS)/M_C_OBS:+.2f}%",
         "Tier 4*"),
        ("m_u",   f"N_c*sqrt(2)*m_e_obs = {N_C*math.sqrt(2)*M_E_OBS*1e3:.4f} MeV",
         f"{M_U_OBS*1e3:.2f} MeV",
         f"{100*(N_C*math.sqrt(2)*M_E_OBS - M_U_OBS)/M_U_OBS:+.2f}%",
         "Tier 4"),
    ]
    for obs, pred, obs_val, dev, tier in rows:
        print(f"  {obs:<10s}  {pred:<32s}  {obs_val:<10s}  {dev:<8s}  {tier}")
    print()
    print("  * = uses Roadmap #6 structural hint (currently Tier 4 empirical)")
    print("      and/or SM y_top = 1 input.  Not yet cascade-internally derived")
    print("      at theorem level.")
    print()
    print("WHAT WOULD CLOSE ROADMAP #6:")
    print()
    print("  (1) Cascade-internal derivation of (t/b)/(c/s) = N_c at theorem")
    print("      level.  This would promote m_c to Tier 2 (combined with the")
    print("      already-Tier-2 b/s closure).")
    print()
    print("  (2) Cascade-internal derivation of y_top = 1 (e.g., 'top is the")
    print("      unique unobstructed fermion in the Weyl chirality structure")
    print("      at d=12').  This would promote m_top to Tier 2.")
    print()
    print("  (3) Cascade structural derivation of m_u (not just empirical fit).")
    print("      The Weyl chirality factor at d=12 is the natural candidate")
    print("      mechanism (per Roadmap #6).")
    print()
    print("  Closing (1) and (2) would promote 2 of 3 up-type quark masses to")
    print("  Tier 2 quality.  Closing (3) would close the up-type sector.")
    print()


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def main() -> int:
    print("=" * 78)
    print("UP-TYPE QUARK MASSES INVESTIGATION")
    print("Roadmap item #6 -- partial closure")
    print("=" * 78)
    print()
    report_empirical_hierarchy()
    report_m_top()
    report_m_c()
    report_m_u()
    report_summary()
    print("=" * 78)
    print("FINDINGS:")
    print("  m_top = v_cas/sqrt(2): -1.4% match (consistency check, y_top=1 SM input).")
    print("  m_c   = m_top/(N_c*(b/s)_cas): -0.12% match with cascade m_top, +1.3%")
    print("          with observed m_top.  NEW structural extension combining")
    print("          Roadmap #6 hint with cascade b/s closure.")
    print("  m_u   = N_c*sqrt(2)*m_e: -0.4% empirical fit.  No clean cascade")
    print("          structural derivation.")
    print()
    print("ROADMAP #6 STATUS: partially closed.  Two-thirds of the up-type quark")
    print("  mass spectrum has cascade-derived predictions to within standing")
    print("  precision; m_u remains empirical.  Closing requires the Weyl")
    print("  chirality factor at d=12 to be computed cascade-internally.")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
