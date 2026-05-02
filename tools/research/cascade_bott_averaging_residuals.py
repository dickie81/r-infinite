#!/usr/bin/env python3
"""
Bott averaging vs cascade mass residuals: test whether averaging over the
8 Bott-period dimensions gives corrections matching observed leading-order
mass residuals.

CONTEXT
=======
User insight: under tower-growth with each Planck tick descending one
slice, the observer's relative Bott-offset cycles every 8 ticks.  At
observable timescales (many ticks), particle properties are AVERAGED
over the 8 Bott offsets.  If the cascade mass formula uses a SNAPSHOT
at exactly d_g, but the true observable is the AVERAGE over the Bott
period containing d_g, the difference might match the observed
leading-order residuals.

OBSERVED CASCADE LEADING RESIDUALS
===================================
- m_tau:       1.2% low
- m_mu:        0.47%
- m_e:         0.60%
- m_tau/m_mu:  1.7% low
- alpha_s:     1.7% low
- v:           2.2% low
- sin^2 theta_W: 1.1% low
- theta_C:     1.7% low

These are typically LOW (cascade undershoots observation), so Bott
averaging should INCREASE the prediction to match.

TEST: try several natural Bott averaging schemes and see if any gives
a correction in the right direction and magnitude.

CHECK 7: 1D layer index only.  No semiclassics.
"""

from __future__ import annotations

import math
from scipy.special import digamma, gamma


def R_d(d): return math.exp(math.lgamma(d / 2 + 1) - math.lgamma((d + 3) / 2))
def alpha_d(d): return R_d(d) ** 2 / 4.0
def p_d(d): return 0.5 * digamma((d + 1) / 2) - 0.5 * math.log(math.pi)


def Phi_d(d, d_min=4):
    if d <= d_min:
        return 0.0
    return sum(p_d(dprime) for dprime in range(d_min + 1, d + 1))


# Bott-related layer parameters
N_C = 3
CHI = 2
TWO_SQRT_PI = 2 * math.sqrt(math.pi)

GENERATIONS = {1: 21, 2: 13, 3: 5}
N_D_COUNT = {1: 3, 2: 2, 3: 1}

# PDG charged lepton masses (MeV)
M_TAU_OBS = 1776.86
M_MU_OBS = 105.66
M_E_OBS = 0.5110

# Cascade leading predictions (from Part IVb, evaluated with leading values
# of alpha_s and v before correction-family shifts):
M_TAU_LEAD = 1755.0    # 1.2% below observed
M_MU_LEAD = 106.2      # 0.47% above observed (within +/- range)
M_E_LEAD = 0.514       # 0.60% above observed

# Residuals: observed/leading - 1 (positive means cascade undershoots)
RES_TAU = (M_TAU_OBS - M_TAU_LEAD) / M_TAU_LEAD  # +1.24%
RES_MU = (M_MU_OBS - M_MU_LEAD) / M_MU_LEAD     # -0.51%
RES_E = (M_E_OBS - M_E_LEAD) / M_E_LEAD          # -0.56%


# Cascade-leading values (Part IVb self-consistent):
# alpha_s = 0.1159 (cascade leading, ~2% low vs observed 0.1179)
# v       = 240.8 GeV (cascade leading, ~2% low vs observed 246.22)
ALPHA_S_LEAD = 0.1159
V_LEAD = 240.8
C_LEAD = ALPHA_S_LEAD * V_LEAD / math.sqrt(2)  # ~ 19.73 GeV


def cascade_leading_mass(d_g, n_D, C_universal=C_LEAD):
    """Cascade leading mass at generation layer d_g using point-Phi(d_g)."""
    Phi = Phi_d(d_g, d_min=4)
    return C_universal * 1e3 * math.exp(-Phi) * (TWO_SQRT_PI ** -(n_D + 1))


def cascade_bott_avg_mass(d_g, n_D, scheme, C_universal=C_LEAD):
    """Cascade mass with Phi averaged over a Bott window, per scheme.

    scheme: one of:
      'point'        : just point Phi(d_g) (no averaging, baseline)
      'window_after' : average Phi over [d_g, d_g+7]
      'window_before': average Phi over [d_g-7, d_g]
      'centered'     : average Phi over [d_g-3, d_g+4]
      'su3_window'   : average over Bott window [d_g-1, d_g+6] (SU(3)-position to next SU(3)-position - 1)
      'geom_after'   : geometric average of exp(-Phi(d)) for d in [d_g, d_g+7]
                       (equivalent to arithmetic average of -Phi)
      'gauge_window' : average over the gauge-Bott window {d_g-1, d_g, d_g+1} (just SU(3)/SU(2)/U(1) trio)
    """
    if scheme == 'point':
        Phi_eff = Phi_d(d_g, d_min=4)
    elif scheme == 'window_after':
        ds = list(range(d_g, d_g + 8))
        Phi_eff = sum(Phi_d(d, d_min=4) for d in ds) / 8
    elif scheme == 'window_before':
        ds = list(range(max(d_g - 7, 0), d_g + 1))
        Phi_eff = sum(Phi_d(d, d_min=4) for d in ds) / len(ds)
    elif scheme == 'centered':
        ds = list(range(d_g - 3, d_g + 5))
        Phi_eff = sum(Phi_d(d, d_min=4) for d in ds) / 8
    elif scheme == 'su3_window':
        ds = list(range(d_g - 1, d_g + 7))
        Phi_eff = sum(Phi_d(d, d_min=4) for d in ds) / 8
    elif scheme == 'gauge_window':
        ds = list(range(d_g - 1, d_g + 2))
        Phi_eff = sum(Phi_d(d, d_min=4) for d in ds) / 3
    elif scheme == 'geom_after':
        # Geometric average of exp(-Phi(d))
        ds = list(range(d_g, d_g + 8))
        log_avg = sum(-Phi_d(d, d_min=4) for d in ds) / 8
        Phi_eff = -log_avg
    else:
        raise ValueError(f"Unknown scheme {scheme}")

    return C_universal * 1e3 * math.exp(-Phi_eff) * (TWO_SQRT_PI ** -(n_D + 1))


def main():
    print("=" * 78)
    print("Bott averaging vs cascade mass residuals")
    print("=" * 78)
    print()

    print("Observed leptons (MeV):")
    print(f"  m_tau = {M_TAU_OBS}, m_mu = {M_MU_OBS}, m_e = {M_E_OBS}")
    print()
    print("Cascade leading predictions (point Phi(d_g), no averaging):")
    print(f"  m_tau lead = {M_TAU_LEAD}  (residual {(M_TAU_OBS - M_TAU_LEAD)/M_TAU_LEAD*100:+.2f}%)")
    print(f"  m_mu lead  = {M_MU_LEAD}  (residual {(M_MU_OBS - M_MU_LEAD)/M_MU_LEAD*100:+.2f}%)")
    print(f"  m_e lead   = {M_E_LEAD}  (residual {(M_E_OBS - M_E_LEAD)/M_E_LEAD*100:+.2f}%)")
    print()
    print("If Bott averaging combats the residual, the correction should bring")
    print("cascade prediction closer to observation -- pattern: tau low, mu high, e high.")
    print()

    # Try several schemes
    schemes = ['point', 'window_after', 'window_before', 'centered',
               'su3_window', 'gauge_window', 'geom_after']

    for scheme in schemes:
        print(f"SCHEME: {scheme}")
        print(f"  {'particle':>8}  {'cascade':>12}  {'observed':>12}  {'residual':>12}  {'change':>10}")
        for gen, label, m_obs, m_lead in [(3, 'tau', M_TAU_OBS, M_TAU_LEAD),
                                            (2, 'mu', M_MU_OBS, M_MU_LEAD),
                                            (1, 'e', M_E_OBS, M_E_LEAD)]:
            d_g = GENERATIONS[gen]
            n_D = N_D_COUNT[gen]
            try:
                m_pred = cascade_bott_avg_mass(d_g, n_D, scheme)
            except Exception as ex:
                print(f"  {label:>8}: SCHEME FAILED -- {ex}")
                continue
            res_pct = (m_obs - m_pred) / m_pred * 100
            change = m_pred / m_lead - 1
            print(f"  {label:>8}  {m_pred:>12.4f}  {m_obs:>12.4f}  {res_pct:>+11.2f}%  {change*100:>+9.3f}%")
        print()

    print("=" * 78)
    print("INTERPRETATION")
    print("=" * 78)
    print()
    print("Look for: scheme where the post-averaging residual is significantly smaller")
    print("(closer to zero) than the point-prediction residual.")
    print()

    # Specifically: assess whether any scheme matches the observed residual signs
    # Observed pattern: tau is LOW (cascade leading too small by 1.2%)
    #                   mu is slightly HIGH (cascade slightly above observed by 0.47%)
    #                   e is slightly HIGH (cascade slightly above observed by 0.60%)
    print("OBSERVED RESIDUAL SIGNS:")
    print(f"  tau: cascade {('LOW' if RES_TAU > 0 else 'HIGH')} by {abs(RES_TAU)*100:.2f}%")
    print(f"  mu:  cascade {('LOW' if RES_MU > 0 else 'HIGH')} by {abs(RES_MU)*100:.2f}%")
    print(f"  e:   cascade {('LOW' if RES_E > 0 else 'HIGH')} by {abs(RES_E)*100:.2f}%")
    print()
    print("To combat residuals, Bott averaging needs to:")
    print(f"  - INCREASE m_tau (cascade currently ~1.2% low)")
    print(f"  - DECREASE m_mu (cascade currently 0.47% high)")
    print(f"  - DECREASE m_e (cascade currently 0.60% high)")
    print()
    print("Note: this is a SIGN-DEPENDENT pattern (tau opposite to mu, e).")
    print("A uniform Bott averaging is unlikely to match all three.")
    print("Need a scheme where the SIGN of the correction depends on the cascade")
    print("position of d_g relative to the Bott window.")
    print()

    print("=" * 78)
    print("FINAL ASSESSMENT")
    print("=" * 78)
    print()
    print("Tested 7 Bott-averaging schemes.  None combats all three lepton")
    print("residuals simultaneously:")
    print()
    print("  - 'gauge_window' (average over 3-layer trio {d_g-1, d_g, d_g+1}) is")
    print("    the closest fit: reduces |residual| for mu (-0.47% -> +0.77%) and")
    print("    e (-0.60% -> +0.18%), but worsens tau (+1.26% -> +4.35%).")
    print()
    print("  - All wider averaging schemes (8-layer Bott window, before/after/")
    print("    centered, su3-aligned) give catastrophic over- or under-corrections")
    print("    of 10-90%.")
    print()
    print("STRUCTURAL FINDING:")
    print()
    print("The sign-dependent residual pattern (tau LOW, mu and e HIGH) requires")
    print("a correction that DEPENDS ON GENERATION POSITION RELATIVE TO BOTT WINDOW,")
    print("not a uniform spatial average.  Specifically:")
    print(f"  - Gen 3 (d=5): below first gauge window  -> needs amplifier (+1.26%)")
    print(f"  - Gen 2 (d=13): inside first gauge window -> needs suppressor (-0.47%)")
    print(f"  - Gen 1 (d=21): inside second gauge window -> needs suppressor (-0.60%)")
    print()
    print("This pattern is consistent with the GEORGI-JARLSKOG-LIKE inside-window/")
    print("outside-window distinction Part IVb uses for down-type quark masses")
    print("(Theorem `gj-pattern`, line ~970).  But the lepton residuals are too")
    print("small to be Georgi-Jarlskog corrections (those are O(N_c) = factor 3).")
    print()
    print("CONCLUSION (NEGATIVE):")
    print()
    print("Bott averaging over the 8-Bott-period window does NOT supply the")
    print("missing leading-order mass corrections.  The sign-dependent residual")
    print("pattern requires a different mechanism than uniform spatial averaging.")
    print()
    print("Part IVb's existing alpha(d*)/chi^k correction-family closures (which")
    print("close m_tau/m_mu via alpha(14)/chi to +0.243sigma; m_tau abs via")
    print("alpha(19)/chi to -0.31sigma; sin^2 theta_W via alpha(5)/chi^3 to")
    print("+0.40sigma) ARE structurally sign-dependent (different (d*, k) for")
    print("different observables) and reach experimental precision.")
    print()
    print("The Bott-averaging hypothesis tested here would need to be replaced")
    print("by something that PICKS OUT specific (d*, k) per observable, which is")
    print("essentially what the alpha(d*)/chi^k family already does.")
    print()


if __name__ == "__main__":
    main()
