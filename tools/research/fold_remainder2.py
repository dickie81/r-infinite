#!/usr/bin/env python3
"""Remainder attack, instrument 2: the CUE-side twin test. At the ten
certified points, compare conditioned ensembles of (i) REAL CUE
eigenphase sets, constructed exactly as certified 1bc's comparator
(dim-380 unitary_group, eigenphases unfolded to the Riemann density
by the uniform circle map, count-conditioned, deterministic seeds)
and (ii) the 1be Gaussian D-matched CUE surrogates. If real minus
surrogate ~ +0.20, the 1be 'non-Gaussian remainder' attribution
inverts: the premium belongs to the comparator side (real
determinantal CUE vs its Gaussian twin), not to zeta.
"""
import numpy as np, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fold_D import inv_Nbar, D_cue_analytic, TWO_PI
from fold_surrogate import Sect, surrogate_field, GRIDS, NZ
from scipy.stats import unitary_group

SIXTH = 1.0/6.0


def cue_real_set(seed):
    """Certified 1bc's cue_set verbatim (cascade_fluctuation_price.py:
    236-242): uniform-density unfolding, mean-anchored."""
    rng = np.random.default_rng(seed)
    U = unitary_group.rvs(NZ, random_state=rng)
    th = np.sort(np.angle(np.linalg.eigvals(U)))
    t = (th + math.pi)/TWO_PI*NZ
    t = t - t.mean() + (NZ + 1)/2
    return np.array([inv_Nbar(max(float(x), 0.6)) for x in np.sort(t)])


def cue_twin_gap(verbose=True):
    """Returns dict: per-point real-CUE minus surrogate-CUE R gaps,
    mean, sem, npos."""
    comb = np.array([inv_Nbar(float(k)) for k in range(1, NZ + 1)])
    lags = np.arange(1, 1025).astype(float)
    Dc_prof = D_cue_analytic(lags) - SIXTH
    crng = np.random.default_rng(99)
    from fold_D import D_emp
    r = np.mean([D_emp(surrogate_field(Dc_prof, crng), 48)
                 for _ in range(80)], axis=0)/Dc_prof[:48]
    sc = 1.0/math.sqrt(float(np.mean(r)))
    sects = {c: Sect(c) for c in GRIDS}
    pts = [(c, t0) for c, taus in GRIDS.items() for t0 in taus]

    def band_count(zeros, c, t0):
        W = c/2.0
        return int(np.sum((zeros > t0 - W) & (zeros < t0 + W)))

    gaps = []
    for c, t0 in pts:
        S = sects[c]
        mc = S.margin(comb, float(t0))
        target = band_count(comb, c, t0)
        # real CUE, conditioned
        Rr, seed, got = [], 0, 0
        while got < 16 and seed < 4000:
            g = cue_real_set(31000 + int(t0)*7 + seed)
            seed += 1
            if band_count(g, c, t0) != target:
                continue
            m = S.margin(g, float(t0))
            if m > 1e-14:
                Rr.append(math.log10(m/mc)); got += 1
        # surrogate CUE, conditioned (the 1be construction)
        rng = np.random.default_rng(9000 + int(t0) + 1)
        Rs, tried = [], 0
        while len(Rs) < 16 and tried < 4000:
            tried += 1
            d = sc*surrogate_field(Dc_prof, rng)
            g = np.array([inv_Nbar(k - 0.5 + d[k-1], g0=20.0 + 2.3*k)
                          for k in range(1, NZ + 1)])
            if band_count(g, c, t0) != target:
                continue
            m = S.margin(g, float(t0))
            if m > 1e-14:
                Rs.append(math.log10(m/mc))
        gap = float(np.mean(Rr) - np.mean(Rs))
        gaps.append(gap)
        if verbose:
            print(f"  c={c:4.0f} t0={t0:3d}: R_realCUE {np.mean(Rr):+.3f} "
                  f"R_surrCUE {np.mean(Rs):+.3f}  gap {gap:+.3f}", flush=True)
    mean = float(np.mean(gaps))
    sem = float(np.std(gaps)/math.sqrt(len(gaps)))
    if verbose:
        print(f"\nCUE twin gap (real - surrogate): mean "
              f"{mean:+.3f} +- {sem:.3f}", flush=True)
    return {"gaps": gaps, "mean": mean, "sem": sem,
            "npos": int(sum(g > 0 for g in gaps))}


if __name__ == "__main__":
    cue_twin_gap()
