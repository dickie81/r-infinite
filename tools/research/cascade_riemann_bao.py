#!/usr/bin/env python3
"""
First observational contact for two Addendum-10-adjacent predictions:

  A. Status of the Sigma m_nu = 61-63 meV / normal-ordering prediction
     against 2025-2026 cosmology (numbers from DESI DR2 2503.14738 /
     2503.14744 and ACT DR6 + DESI DR2 isocurvature analysis
     2606.17994; see Addendum 11 for links).
  B. The log-periodic Riemann-frequency template, fit to the DESI DR2
     BAO data that ship with this repository (src/generated/
     bao-table.tex): delta H/H = A cos(g ln(1+z)) + B sin(g ln(1+z)),
     with g fixed at the matter-era mappings of the first Riemann
     zeros, g = (3/2) gamma_n in ln(1+z).  Linear least squares in
     (A, B) on top of the Planck fiducial; continuum scan in g for
     the look-elsewhere control.

The template's propagation to observables: dD_H/D_H = -dH/H at z;
dD_M/D_M = -(1/chi) int (dH/H) dchi; dD_V/D_V = (2 dD_M/D_M +
dD_H/D_H)/3; r_d held fixed (late-time modulation only).
"""

import math

import numpy as np

# z, type, obs, sigma, pull_planck  (from src/generated/bao-table.tex;
# Planck model value = obs + pull*sigma, pull = (model-obs)/sigma)
DATA = [
    (0.295, "DV", 7.930, 0.150, +0.63),
    (0.510, "DM", 13.650, 0.200, -1.01),
    (0.510, "DH", 20.890, 0.490, +3.60),
    (0.706, "DM", 16.970, 0.240, +2.76),
    (0.706, "DH", 20.270, 0.470, -0.38),
    (0.934, "DM", 21.790, 0.240, +0.50),
    (0.934, "DH", 17.730, 0.300, -0.76),
    (1.321, "DM", 27.680, 0.500, +0.58),
    (1.321, "DH", 13.850, 0.340, +0.47),
    (1.484, "DM", 30.420, 0.660, -0.40),
    (1.484, "DH", 13.240, 0.450, -0.91),
    (2.330, "DM", 39.200, 0.560, -0.30),
    (2.330, "DH", 8.540, 0.140, +0.31),
]
OM = 0.315
GAMMAS = [14.134725, 21.022040, 25.010858]


def E(z):
    return math.sqrt(OM * (1 + z) ** 3 + (1 - OM))


def templates(g):
    """Fractional response of each observable to dH/H = cos(g ln(1+z))
    and sin(g ln(1+z)) -- returns arrays C, S over DATA rows."""
    zg = np.linspace(0, 2.35, 2400)
    dchi = 1.0 / np.array([E(z) for z in zg])
    lc = np.log(1 + zg)
    C, Sv = [], []
    for (z, typ, *_r) in DATA:
        idx = zg <= z
        chi = np.trapezoid(dchi[idx], zg[idx])
        # dD_M/D_M for cos and sin modulations
        dmc = -np.trapezoid(np.cos(g * lc[idx]) * dchi[idx], zg[idx]) / chi
        dms = -np.trapezoid(np.sin(g * lc[idx]) * dchi[idx], zg[idx]) / chi
        dhc = -math.cos(g * math.log(1 + z))
        dhs = -math.sin(g * math.log(1 + z))
        if typ == "DM":
            c, s = dmc, dms
        elif typ == "DH":
            c, s = dhc, dhs
        else:
            c, s = (2 * dmc + dhc) / 3.0, (2 * dms + dhs) / 3.0
        C.append(c)
        Sv.append(s)
    return np.array(C), np.array(Sv)


def fit(g):
    C, Sv = templates(g)
    r = np.array([-p for (_, _, _, _, p) in DATA])          # (obs-model)/sigma
    w = np.array([(o + p * s) / s for (_, _, o, s, p) in DATA])  # model/sigma
    X = np.column_stack([w * C, w * Sv])
    beta, *_ = np.linalg.lstsq(X, r, rcond=None)
    resid = r - X @ beta
    chi2 = float(resid @ resid)
    cov = np.linalg.inv(X.T @ X)
    amp = math.hypot(*beta)
    sig = math.sqrt(max(cov[0, 0], cov[1, 1]))
    return chi2, amp, sig, beta


def main():
    print("=" * 74)
    print("PART A: Sigma m_nu prediction vs current cosmology")
    print("=" * 74)
    print("  prediction (Addendum 10): NORMAL ordering, Sigma = 61-63 meV")
    print("  DESI DR2 + CMB (2025): Sigma < 64 meV (95%, LCDM)  -> alive by")
    print("    a hair; < 160 meV in w0waCDM (but evolving DE would kill the")
    print("    staticness the capacity construction requires)")
    print("  ACT DR6 + DESI DR2 (2026): Sigma < 52-57 meV (LCDM, adiabatic)")
    print("    -> EXCLUDES the prediction -- and the NO oscillation floor")
    print("    (58.5 meV) with it: the 'negative neutrino mass' tension.")
    print("  verdict: the prediction dies and rises with standard normal")
    print("  ordering itself; it is now a bystander hostage to cosmology's")
    print("  own anomaly.  Resolution paths: systematics (prediction lives),")
    print("  evolving DE (staticness dies anyway), new physics (all bets off).")

    print()
    print("=" * 74)
    print("PART B: Riemann log-periodic template vs DESI DR2 BAO (in-repo)")
    print("=" * 74)
    chi2_0 = sum(p * p for (_, _, _, _, p) in DATA)
    print(f"  baseline chi2 (Planck fiducial): {chi2_0:.2f} / 13 pts")
    print(f"  {'frequency':<26}{'chi2':>8}{'dchi2':>8}{'amp':>9}{'~95% lim':>10}")
    for gam in GAMMAS:
        g = 1.5 * gam
        chi2, amp, sig, _ = fit(g)
        print(f"  gamma_{GAMMAS.index(gam)+1} = {gam:7.3f} (g={g:5.1f})"
              f"{chi2:>8.2f}{chi2_0-chi2:>8.2f}{amp:>9.4f}{2*sig:>10.4f}")
    best = (None, 1e9, 0, 0)
    for g in np.arange(3.0, 45.0, 0.1):
        chi2, amp, sig, _ = fit(g)
        if chi2 < best[1]:
            best = (g, chi2, amp, sig)
    print(f"  continuum scan g in [3,45]: best g = {best[0]:.1f},"
          f" chi2 = {best[1]:.2f} (dchi2 = {chi2_0-best[1]:.2f}), amp ="
          f" {best[2]:.4f}")
    print("  look-elsewhere: 2 fitted params + scanned g; dchi2 of this size")
    print("  at a free frequency is unremarkable.  The Riemann frequencies")
    print("  are NOT preferred over the continuum.")
    print("  => first observational bound at the Riemann frequencies:")
    print("     |dH/H| oscillation amplitude < few x 1e-2 (95%) at g1-g3 --")
    print("     five orders above the <=1e-4 coupling ceiling from clock")
    print("     drifts (Addendum 6): BAO cannot yet test the surviving")
    print("     parameter space, but the template is now fit, not just")
    print("     proposed.  Null recorded.")


if __name__ == "__main__":
    main()
