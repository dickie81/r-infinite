#!/usr/bin/env python3
"""Fold hardening, part 1: decompose alpha = 0.681 into its two
constituents, each measured independently:

  (a) the index-sampling conversion: D_index (increments sampled AT
      the zeros) vs D_fixed (increments of S(t) at fixed t-shifts).
      Measured for zeta AND for the CUE eigenphase ensembles (where
      the fixed-shift statistic is Sigma^2-adjacent), and for the
      Gaussian surrogates themselves (self-consistency).
  (b) the finite-height suppression of the bare diagonal sum:
      D_fixed(zeta, measured) vs the bare prime sum -- the true
      Berry-resummation-class factor, cleanly separated from (a).

S(t) for zeta on a fine grid: S(t) = N(t) - Nbar(t), N(t) = #{gamma
<= t}, over the window heights 130..500 (matching fold_D's index
window). For CUE: the eigenphase counting function on its own circle.
"""
import numpy as np, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fold_D import (Nbar, zeros380, D_emp, D_zeta_analytic,
                    D_cue_analytic, D_zeta_sat, TWO_PI)


def D_fixed_from_points(points, tlo, thi, mean_density_fn, amax_sp, ng=8000):
    """E[(S(t+a)-S(t))^2] on a fine grid; a in mean-spacing units."""
    tg = np.linspace(tlo, thi, ng)
    Nt = np.searchsorted(points, tg)
    S = Nt - mean_density_fn(tg)
    sp = (thi - tlo)/np.mean(np.diff(np.sort(
        points[(points > tlo) & (points < thi)])))/ng  # grid pts per spacing^-1
    # mean spacing in t at window center:
    pts = points[(points > tlo) & (points < thi)]
    msp = np.mean(np.diff(np.sort(pts)))
    out = []
    for a_sp in amax_sp:
        da = int(round(a_sp*msp/(tg[1] - tg[0])))
        d = S[da:] - S[:-da]
        out.append(np.mean(d*d))
    return np.array(out)


if __name__ == "__main__":
    lags_sp = [1, 2, 4, 8, 16, 24, 32, 48]
    Z = zeros380()
    # ---- zeta: fixed-shift D over the window
    Dzf = D_fixed_from_points(Z, 130.0, 500.0, Nbar, lags_sp)
    # zeta index-shift (fold_D's statistic, same window)
    dz = Nbar(Z) - np.arange(1, len(Z) + 1) + 0.5
    Dzi = D_emp(dz[40:340], 48)
    bare = D_zeta_analytic(np.array(lags_sp, float), 320.0)
    bare_smear = np.mean([D_zeta_analytic(np.array(lags_sp, float), T)
                          for T in np.linspace(130, 500, 15)], axis=0)
    print(" a(sp)  D_fixed(zeta)  D_index(zeta)  bare-diagonal(smeared)")
    for i, a in enumerate(lags_sp):
        print(f"  {a:3d}     {Dzf[i]:.3f}          "
              f"{Dzi[a-1]:.3f}          {bare_smear[i]:.3f}")
    print(f"\n plateaus (16..48): fixed {np.mean(Dzf[4:]):.3f}; "
          f"index {np.mean([Dzi[15], Dzi[23], Dzi[31], Dzi[47]]):.3f}; "
          f"bare {np.mean(bare_smear[4:]):.3f}")
    print(f" (b) finite-height suppression = fixed/bare = "
          f"{np.mean(Dzf[4:])/np.mean(bare_smear[4:]):.3f}")
    print(f" (a) index-sampling conversion = index/fixed = "
          f"{np.mean([Dzi[15], Dzi[23], Dzi[31], Dzi[47]])/np.mean(Dzf[4:]):.3f}")
    print(f" product (= alpha decomposed) vs alpha 0.681: "
          f"{np.mean([Dzi[15], Dzi[23], Dzi[31], Dzi[47]])/np.mean(bare_smear[4:]):.3f}")

    # ---- CUE: same decomposition on eigenphases
    from scipy.stats import unitary_group
    Dci_all, Dcf_all = [], []
    for s in (11, 23, 47, 61, 83, 101, 131, 151, 173, 199):
        U = unitary_group(dim=380, seed=s).rvs()
        ph = np.sort(np.angle(np.linalg.eigvals(U)))
        u = (ph - ph[0])*380/TWO_PI
        Dci_all.append(D_emp(u - np.arange(len(u)), 48))
        Dcf_all.append(D_fixed_from_points(
            u, 10.0, 370.0, lambda t: t, lags_sp, ng=6000))
    Dci = np.mean(Dci_all, axis=0)
    Dcf = np.mean(Dcf_all, axis=0)
    sig2 = D_cue_analytic(np.array(lags_sp, float))
    print("\n a(sp)  D_fixed(CUE)  D_index(CUE)  Sigma^2 form")
    for i, a in enumerate(lags_sp):
        print(f"  {a:3d}     {Dcf[i]:.3f}         {Dci[a-1]:.3f}         "
              f"{sig2[i]:.3f}")
    print(f" CUE: fixed vs Sigma^2 at 16..48: "
          f"{np.mean(Dcf[4:]):.3f} vs {np.mean(sig2[4:]):.3f}; "
          f"index/fixed = {np.mean([Dci[15], Dci[23], Dci[31], Dci[47]])/np.mean(Dcf[4:]):.3f}")
