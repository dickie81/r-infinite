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
                    D_cue_analytic, TWO_PI)


def D_fixed_from_points(points, tlo, thi, mean_density_fn, amax_sp, ng=8000):
    """E[(S(t+a)-S(t))^2] on a fine grid; a in mean-spacing units."""
    tg = np.linspace(tlo, thi, ng)
    Nt = np.searchsorted(points, tg)
    S = Nt - mean_density_fn(tg)
    pts = points[(points > tlo) & (points < thi)]
    msp = np.mean(np.diff(np.sort(pts)))
    out = []
    for a_sp in amax_sp:
        da = int(round(a_sp*msp/(tg[1] - tg[0])))
        d = S[da:] - S[:-da]
        out.append(np.mean(d*d))
    return np.array(out)


def decomposition(verbose=True):
    """Measure the alpha decomposition. Returns a dict:
    zeta fixed/index plateaus, bare-diagonal plateau, CUE fixed/index
    at lags [1,2,4,8,16,24,32,48], and the Sigma^2 form."""
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
    if verbose:
        print(" a(sp)  D_fixed(zeta)  D_index(zeta)  bare-diagonal(smeared)")
        for i, a in enumerate(lags_sp):
            print(f"  {a:3d}     {Dzf[i]:.3f}          "
                  f"{Dzi[a-1]:.3f}          {bare_smear[i]:.3f}")
    if verbose: print(f"\n plateaus (16..48): fixed {np.mean(Dzf[4:]):.3f}; "
          f"index {np.mean([Dzi[15], Dzi[23], Dzi[31], Dzi[47]]):.3f}; "
          f"bare {np.mean(bare_smear[4:]):.3f}")
    if verbose: print(f" (b) finite-height suppression = fixed/bare = "
          f"{np.mean(Dzf[4:])/np.mean(bare_smear[4:]):.3f}")
    if verbose: print(f" (a) index-sampling conversion = index/fixed = "
          f"{np.mean([Dzi[15], Dzi[23], Dzi[31], Dzi[47]])/np.mean(Dzf[4:]):.3f}")
    if verbose: print(f" product (= alpha decomposed) vs alpha 0.681: "
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
    if verbose: print("\n a(sp)  D_fixed(CUE)  D_index(CUE)  Sigma^2 form")
    if verbose:
        for i, a in enumerate(lags_sp):
            print(f"  {a:3d}     {Dcf[i]:.3f}         {Dci[a-1]:.3f}         "
                  f"{sig2[i]:.3f}")
    if verbose: print(f" CUE: fixed vs Sigma^2 at 16..48: "
          f"{np.mean(Dcf[4:]):.3f} vs {np.mean(sig2[4:]):.3f}; "
          f"index/fixed = {np.mean([Dci[15], Dci[23], Dci[31], Dci[47]])/np.mean(Dcf[4:]):.3f}")
    return {"lags": lags_sp,
            "zeta_fixed": [float(v) for v in Dzf],
            "zeta_index_at_lags": [float(Dzi[a-1]) for a in lags_sp],
            "bare_smeared": [float(v) for v in bare_smear],
            "cue_fixed": [float(v) for v in Dcf],
            "cue_index_at_lags": [float(Dci[a-1]) for a in lags_sp],
            "sigma2": [float(v) for v in sig2],
            "surrogate_sawtooth": surrogate_sawtooth(lags_sp)}


def surrogate_sawtooth(lags_sp, nreal=40):
    """The self-consistency branch (round-224 F7: the docstring
    promised this measurement; now computed): Gaussian surrogate
    fields with a climbing D, positions by inv_Nbar, sawtooth =
    D_fixed - D_index, expected 1/6 at every lag."""
    from fold_D import inv_Nbar
    from fold_surrogate import surrogate_field
    rng = np.random.default_rng(7)
    prof = D_cue_analytic(np.arange(1, 1025).astype(float)) - 1.0/6
    NZ = 380
    vals = []
    for _ in range(nreal):
        d = surrogate_field(prof, rng)
        g = np.array([inv_Nbar(k - 0.5 + d[k-1], g0=20.0 + 2.3*k)
                      for k in range(1, NZ + 1)])
        g = np.sort(g)
        Di = D_emp(Nbar(g) - np.arange(1, NZ + 1) + 0.5, 48)
        Df = D_fixed_from_points(g, float(g[30]), float(g[-30]),
                                 Nbar, lags_sp, ng=6000)
        vals.append([float(Df[i] - Di[a-1])
                     for i, a in enumerate(lags_sp)])
    return [float(v) for v in np.mean(vals, axis=0)]


if __name__ == "__main__":
    decomposition()
