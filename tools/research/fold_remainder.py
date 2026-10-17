#!/usr/bin/env python3
"""Remainder attack, instrument 1: is the ~25% non-Gaussian premium
significant, and what cumulant structure carries it?

(A) The significance test. The certified excess (+0.710) is ONE
correlated draw: the same 380 zeros at all ten points. The 1be
surrogate excess (+0.95) is an ensemble mean over independent
per-point draws. Honest comparison: SHARED-FIELD surrogates -- one
Gaussian field per draw, evaluated at all ten points exactly as the
real zeros are (unconditioned, like the real zeta side of 1bc;
the CUE comparator stays the conditioned ensemble mean, the
certified construction) -- giving a distribution of correlated
ten-point mean excesses. Report the real +0.710's percentile in it.

(B) The cumulant census. Skewness and excess kurtosis of the real
zeta displacement field delta_n (window zeros 40..340) and of its
increments at lags 1/4/16, vs CUE eigenphase sets and the Gaussian
surrogate baseline (expected 0/0).
"""
import numpy as np, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fold_D import Nbar, inv_Nbar, D_cue_analytic, TWO_PI, zeros380
from fold_surrogate import Sect, surrogate_field, GRIDS, NZ

MERTENS = 0.2614972128476428
SIXTH = 1.0/6.0


def profiles():
    lags = np.arange(1, 1025).astype(float)
    X0 = 320.0/TWO_PI
    Vsat = (math.log(math.log(X0)) + MERTENS + 1)/math.pi**2
    Dz = np.minimum(D_cue_analytic(lags), Vsat) - SIXTH
    Dc = D_cue_analytic(lags) - SIXTH
    return Dz, Dc


def calib(prof, rng, n=80):
    from fold_D import D_emp
    r = np.mean([D_emp(surrogate_field(prof, rng), 48)
                 for _ in range(n)], axis=0)/prof[:48]
    return 1.0/math.sqrt(float(np.mean(r)))


def positions(field):
    return np.array([inv_Nbar(k - 0.5 + field[k-1], g0=20.0 + 2.3*k)
                     for k in range(1, NZ + 1)])


def significance(ndraw=32, verbose=True):
    """The shared-field twin test. Returns dict: real_mean (the
    correlated ten-point real-zeta excess over the surrogate-CUE
    comparator), draws (ndraw shared-field surrogate mean excesses),
    percentile, z."""
    Z = zeros380()
    comb = np.array([inv_Nbar(float(k)) for k in range(1, NZ + 1)])
    Dz_prof, Dc_prof = profiles()
    crng = np.random.default_rng(99)
    sz = calib(Dz_prof, crng)
    sc = calib(Dc_prof, crng)
    print(f"calib: zeta {sz:.4f}, cue {sc:.4f}", flush=True)
    sects = {c: Sect(c) for c in GRIDS}
    pts = [(c, t0) for c, taus in GRIDS.items() for t0 in taus]

    def band_count(zeros, c, t0):
        W = c/2.0
        return int(np.sum((zeros > t0 - W) & (zeros < t0 + W)))

    # conditioned CUE ensemble means per point (the certified comparator)
    cue_mean = {}
    m_comb = {}
    for c, t0 in pts:
        S = sects[c]
        m_comb[(c, t0)] = S.margin(comb, float(t0))
        target = band_count(comb, c, t0)
        rng = np.random.default_rng(9000 + int(t0) + 1)
        Rs, tried = [], 0
        while len(Rs) < 16 and tried < 4000:
            tried += 1
            d = sc*surrogate_field(Dc_prof, rng)
            g = positions(d)
            if band_count(g, c, t0) != target:
                continue
            m = S.margin(g, float(t0))
            if m > 1e-14:
                Rs.append(math.log10(m/m_comb[(c, t0)]))
        cue_mean[(c, t0)] = float(np.mean(Rs))
    print("cue means done", flush=True)

    # the real zeta's correlated draw
    real_ex = []
    for c, t0 in pts:
        S = sects[c]
        mz = S.margin(Z, float(t0))
        real_ex.append(math.log10(mz/m_comb[(c, t0)]) - cue_mean[(c, t0)])
    real_mean = float(np.mean(real_ex))
    if verbose:
        print(f"REAL zeta correlated draw: mean excess {real_mean:+.3f} "
              f"(per-point {[f'{v:+.2f}' for v in real_ex]})", flush=True)

    # shared-field surrogate draws (unconditioned, like the real side)
    NDRAW = ndraw
    rng = np.random.default_rng(4242)
    draws = []
    for i in range(NDRAW):
        d = sz*surrogate_field(Dz_prof, rng)
        g = positions(d)
        ex = []
        for c, t0 in pts:
            S = sects[c]
            m = S.margin(g, float(t0))
            if m <= 1e-14:
                ex.append(None)
                continue
            ex.append(math.log10(m/m_comb[(c, t0)]) - cue_mean[(c, t0)])
        ex = [e for e in ex if e is not None]
        draws.append(float(np.mean(ex)))
        if verbose:
            print(f"  draw {i:2d}: mean excess {draws[-1]:+.3f}", flush=True)
    draws = np.array(draws)
    pct = float(np.mean(draws <= real_mean))
    if verbose: print(f"\n(A) shared-field surrogate mean-excess distribution: "
          f"mean {np.mean(draws):+.3f}, sd {np.std(draws):.3f}, "
          f"range [{draws.min():+.3f}, {draws.max():+.3f}]", flush=True)
    if verbose: print(f"    REAL {real_mean:+.3f} sits at percentile {100*pct:.1f} "
          f"({np.sum(draws <= real_mean)}/{NDRAW} draws below); "
          f"z = {(real_mean - np.mean(draws))/np.std(draws):+.2f}", flush=True)
    return {"real_mean": real_mean, "real_per_point": [float(v) for v in real_ex],
            "draws": [float(v) for v in draws], "percentile": pct,
            "z": float((real_mean - np.mean(draws))/np.std(draws))}


def cumulant_census(verbose=True):
    """(B): skew/excess-kurtosis of the displacement fields (window
    zeros 40..340) and their increments, for zeta / CUE / the
    Gaussian surrogate baseline. Returns {name: [skew, exkurt]}."""
    from scipy.stats import skew, kurtosis, unitary_group
    Z = zeros380()
    Dz_prof, _ = profiles()
    crng = np.random.default_rng(99)
    sz = calib(Dz_prof, crng)
    rng = np.random.default_rng(4242)
    dz = (Nbar(Z) - np.arange(1, NZ + 1) + 0.5)[40:340]
    rows = [("zeta", dz)]
    cu = []
    for s in (11, 23, 47, 61):
        U = unitary_group(dim=380, seed=s).rvs()
        ph = np.sort(np.angle(np.linalg.eigvals(U)))
        u = (ph - ph[0])*380/TWO_PI
        cu.append((u - np.arange(len(u)))[40:340])
    rows.append(("cue", np.concatenate(cu)))
    g = np.concatenate([sz*surrogate_field(Dz_prof, rng)[40:340]
                        for _ in range(8)])
    rows.append(("surr", g))
    out = {}
    if verbose:
        print("\n(B) cumulants:  field      skew   ex-kurt   (increments "
              "lag 1 / 4 / 16: skew, ex-kurt)", flush=True)
    for name, v in rows:
        out[name] = [float(skew(v)), float(kurtosis(v))]
        if verbose:
            incs = []
            for l in (1, 4, 16):
                d = v[l:] - v[:-l]
                incs.append(f"{skew(d):+.2f},{kurtosis(d):+.2f}")
            print(f"    {name:5s}  {skew(v):+.3f}  {kurtosis(v):+.3f}   "
                  f"[{' | '.join(incs)}]", flush=True)
    return out


if __name__ == "__main__":
    significance()
    cumulant_census()
