#!/usr/bin/env python3
"""The saturation attack (commissioned after the 1bg landing):
derive the saturation constant m_sat ~ 0.253-0.255 (the c = 120
plateau; c = 60 scattered 0.21-0.50 with steps).

THE SCAFFOLD (derived before measurement; this run tests it):
  (T1) THE HORIZON HEIGHT IN CLOSED FORM: the count crossing
       nb = N_sh reads (2c/A) ln(tau0/2pi)/(2pi) = 2c/pi, i.e.
       ln(tau0/2pi) = 2A: tau* = 2pi e^(2A) = 2pi e^4 = 343.06,
       INDEPENDENT of c -- and e^(2A) is also the prime cutoff
       (DELTA = 2A): the same u-support width sets which primes
       the section hears and where its dodging dies (the Nyquist
       condition in two costumes).
  (T2) THE TIGHT MEAN BY POISSON SUMMATION: for a perfect lattice
       of ordinates at spacing delta_s < pi, every aliasing term
       vanishes (the autocorrelation support is |u| <= 2A), so
       the sampling frame is TIGHT: Q = ln(tau0/2pi) * Identity
       in G-normalized units -- margin = mean, no dodging.
  (T3) THE REDUCTION: measured m_sat = 0.253 is ~16x below the
       tight value ln(420/2pi) = 4.20 -- the saturation constant
       is a FLUCTUATION functional: m_sat = L * F(spacing process)
       with L = ln(tau0/2pi), F a universal functional of the
       normalized spacing statistics at Nyquist ratio r = L/(2A).

Experiments:
  E1 tight-mean check: Q(top prolate) vs ln(tau0/2pi) at four
     saturated tau0 (verifies T2 and the normalization algebra).
  E2 the surrogate ladder at (120, 420): m_sat for point processes
     of IDENTICAL local density -- perfect lattice (predict ~ L,
     tight), jittered lattices (sigma/delta = 0.05..0.4), CUE
     eigenangle spacings (Mezzadri sampling), Poisson -- vs the
     measured zeta value. If zeta sits on the CUE value, the
     constant is pure level-repulsion statistics (a computable
     random-matrix functional); the lattice-vs-zeta split
     separates rigidity from repulsion.
  E3 gap alignment: the saturated minimizer's spectral profile
     |f_w(s)|^2 vs the zero positions -- does its mass sit in the
     largest gaps of the band (gap-hiding)?
  E4 the fine scan: m_sat(tau0) at step 5 over 350-520 (c = 120)
     with the band's max-gap statistic -- plateau structure, the
     ~460-480 step, and the m_sat vs max-gap correlation.

Check 7: sampling theory, Poisson summation, random-matrix
surrogates -- classical analysis (CUE surrogates follow the
certified 1bc/1be comparator pattern). Check 8: no hypothesis
input. Keying per A355: DEPS = this file + floor_probe.py + the
four substrates; params carry every stage input; the CUE seeds
are explicit params.

RESULT (all probes + the E2b coverage-fixed rerun complete):

DERIVED EXACTLY, VERIFIED:
  (1) THE HORIZON HEIGHT: tau* = 2pi e^(2A) = 343.06, c-independent
      (T1 algebra; the ladders saturate there at both c) -- and
      e^(2A) is the prime cutoff: one u-support width sets both.
  (2) THE TIGHT MEAN: Q(top prolate) = ln(tau0/2pi) to 0.3-0.6% at
      all four saturated points (T2, Poisson summation -- every
      aliasing term vanishes above tau* since the autocorrelation
      support is |u| <= 2A). The finite-band lattice margin
      converges to it (3.530 at half=200, 3.786 at 300, L = 4.202).

THE "CONSTANT" DEFLATES -- m_sat IS NOT UNIVERSAL:
  (3) E3/E4: the saturated minimizer LOCKS ONTO ONE spectral
      feature (a soft wide-gap neighborhood at gamma ~ 416.8) for
      every center from tau0 = 360 to ~465 -- the 0.253 plateau is
      that single feature's dodge value, ridden as the band slides
      100+ units; at ~475 the feature exits the reachable band and
      the margin steps to the next feature's value (0.37-0.42).
      Ensemble across the scan: range 0.183-0.417, median 0.254;
      corr(log m, band max-gap) = -0.805. The minimizer is
      gap-seeking but optimizes a gap NEIGHBORHOOD, not the argmax
      gap (dist to argmax ~ 45 at three of four points). The
      c = 60 scatter/steps = a narrower band changing features
      more often; the apparent c-independence = both bands riding
      the same feature. m_sat ~ 1/4 IS A COINCIDENCE of one
      feature -- the quarter reading is dead.
  (4) THE DISORDER LADDER (E2/E2b, same density throughout):
      lattice 3.53-3.79 >> jitter 0.05/0.15/0.30: 3.00/1.33/0.09
      >> zeta 0.253 vs CUE (full coverage, N=320) 0.064 +- 0.038
      (range 0.010-0.119; all ten realizations below zeta) >>
      Poisson 0.000. The saturated margin is a RIGIDITY METER.
      Zeta's ~0.6-decade elevation above CUE is the certified 1bc
      stiffness excess (+0.71 decades at the deep points, Theorem
      1bc/1be) measured in the saturated regime -- consistent with
      certified 1be's attribution (counting + the prime
      pair-correlation budget; CUE's determinantal premium makes
      CUE the better dodger, g14/g15). Caveat: the surrogates use
      constant density (zeta's ln-growth varies ~+-12% across the
      +-200 band; second-order for concentrated sections, but a
      density-modulated surrogate is the clean follow-up).

NET: the saturation "constant" is m_sat = L x F(local spacing
landscape) with L = ln(tau0/2pi) derived and F a feature-local
extreme statistic, not a universal number; what IS universal is
the ordering and the scale of the rigidity gap to CUE, which the
certified fold arc already derived from the prime budget. No
quarter, no new constant to derive -- the commission closes by
deflation into certified results plus two new exact theorems
(tau* and the tight mean).
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
from fold_D import zeros380
from fold_surrogate import A
from witness_twosided import TwoSided


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS6 = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "witness_offline.py",
    "witness_twosided.py", "floor_probe.py", "floor_probe6.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

C0, T0 = 120.0, 420.0
SAT_T0 = [380.0, 420.0, 460.0, 500.0]


def zform_pts(S, gams, t0):
    g = np.asarray(gams, dtype=float)
    s = np.concatenate([(g - t0)*A, (-g - t0)*A])
    Vb = np.asarray(S.vhat(s.astype(complex)))
    if Vb.shape[0] != len(s):
        Vb = Vb.T
    Q = Vb.conj().T @ Vb
    return (Q + Q.conj().T)/2


def margin(S, gams, t0):
    ev = scipy_eigh(zform_pts(S, gams, t0), S.G, eigvals_only=True)
    return float(ev[0])


def local_density(t0):
    return math.log(t0/(2*math.pi))/(2*math.pi)   # zeros per unit gamma


def cue_points(rng, t0, half, dens, N=320):
    """CUE eigenangle spacings rescaled to the target density,
    unfolded, laid down over [t0-half, t0+half] (Mezzadri QR).
    N must satisfy (N-1)/dens > 2*half + slack, or the surrogate
    under-covers the band and grants edge dodges (the first run's
    N = 256 gave ~+-190 < +-200: cue 0.096 was edge-biased low)."""
    Zm = (rng.standard_normal((N, N)) +
          1j*rng.standard_normal((N, N)))/math.sqrt(2)
    Qm, Rm = np.linalg.qr(Zm)
    Qm = Qm * (np.diagonal(Rm)/np.abs(np.diagonal(Rm)))
    ang = np.sort(np.angle(np.linalg.eigvals(Qm)))
    sp = np.diff(ang)*N/(2*math.pi)               # unit-mean spacings
    pos = np.cumsum(sp)/dens
    pos = pos - pos.mean() + t0
    return pos[(pos > t0 - half) & (pos < t0 + half)]


def surrogate_ladder(S, Z, t0, nreal=10, seed=11):
    dens = local_density(t0)
    half = 200.0                                   # generous band
    zeta_band = Z[(Z > t0 - half) & (Z < t0 + half)]
    out = {"L": math.log(t0/(2*math.pi)),
           "zeta": margin(S, Z, t0),
           "zeta_band": margin(S, zeta_band, t0)}
    lat = t0 + (np.arange(-int(half*dens), int(half*dens) + 1)
                )/dens
    out["lattice"] = margin(S, lat, t0)
    rng = np.random.default_rng(seed)
    for sig in (0.05, 0.15, 0.30):
        vals = [margin(S, lat + rng.standard_normal(len(lat))
                       * sig/dens, t0) for _ in range(nreal)]
        out[f"jit{sig}"] = [float(np.mean(vals)), float(np.std(vals))]
    vals = [margin(S, cue_points(rng, t0, half, dens), t0)
            for _ in range(nreal)]
    out["cue"] = [float(np.mean(vals)), float(np.std(vals))]
    vals = []
    for _ in range(nreal):
        npts = rng.poisson(2*half*dens)
        vals.append(margin(S, t0 + (rng.random(npts) - 0.5)*2*half,
                           t0))
    out["poisson"] = [float(np.mean(vals)), float(np.std(vals))]
    return out


def tight_mean(S, Z, t0):
    Q = zform_pts(S, Z, t0)
    n = S.n
    w = np.eye(n)[:, 0]/math.sqrt(S.G[0, 0])
    return float(np.real(np.conj(w) @ Q @ w))


def gap_alignment(S, Z, t0):
    Q = zform_pts(S, Z, t0)
    ev, V = scipy_eigh(Q, S.G)
    w = V[:, 0]
    sgrid = np.linspace(-1.2*S.c, 1.2*S.c, 2401)
    Vc = np.asarray(S.vhat(sgrid.astype(complex)))
    if Vc.shape[0] != len(sgrid):
        Vc = Vc.T
    prof = np.abs(Vc @ w)**2
    speak = float(sgrid[int(np.argmax(prof))])
    gpeak = t0 + speak/A
    zb = Z[(Z > t0 - S.c/A) & (Z < t0 + S.c/A)]
    gaps = np.diff(zb)
    k = int(np.argmax(gaps))
    gap_mid = float(0.5*(zb[k] + zb[k+1]))
    return {"gamma_peak": gpeak, "max_gap": float(gaps[k]),
            "max_gap_mid": gap_mid,
            "dist": abs(gpeak - gap_mid),
            "mean_gap": float(gaps.mean())}


def fine_scan(S, Z, lo=350.0, hi=520.0, step=5.0):
    rows = []
    t0 = lo
    while t0 <= hi + 1e-9:
        m = margin(S, Z, t0)
        zb = Z[(Z > t0 - S.c/A) & (Z < t0 + S.c/A)]
        gmax = float(np.diff(zb).max())
        rows.append({"t0": t0, "m": m, "gmax": gmax})
        t0 += step
    return rows


def run():
    Z = zeros380()
    S = TwoSided(C0)
    # E1
    params = {"deps": DEPS6, "sat_t0": SAT_T0, "c": C0}
    st = ckpt_key.load("sat_tight", KEYFILE, params)
    if st is None:
        st = [{"t0": t0, "Qtop": tight_mean(S, Z, t0),
               "L": math.log(t0/(2*math.pi))} for t0 in SAT_T0]
        ckpt_key.save("sat_tight", KEYFILE, params, st)
    for r in st:
        print(f"  E1 t0={r['t0']:.0f}: Q(top) {r['Qtop']:.3f} vs "
              f"L = ln(t0/2pi) {r['L']:.3f} (ratio "
              f"{r['Qtop']/r['L']:.3f})", flush=True)
    # E2
    params = {"deps": DEPS6, "c": C0, "t0": T0, "nreal": 10,
              "seed": 11, "half": 200.0}
    sur = ckpt_key.load("sat_surrogates", KEYFILE, params)
    if sur is None:
        sur = surrogate_ladder(S, Z, T0)
        ckpt_key.save("sat_surrogates", KEYFILE, params, sur)
    L = sur["L"]
    print(f"  E2 (120,420) L={L:.3f}: zeta {sur['zeta']:.3f} "
          f"(band-only {sur['zeta_band']:.3f}) lattice "
          f"{sur['lattice']:.3f}", flush=True)
    for k in ("jit0.05", "jit0.15", "jit0.3", "jit0.30"):
        if k in sur:
            print(f"     {k}: {sur[k][0]:.3f} +- {sur[k][1]:.3f}",
                  flush=True)
    print(f"     cue: {sur['cue'][0]:.3f} +- {sur['cue'][1]:.3f}   "
          f"poisson: {sur['poisson'][0]:.3f} +- {sur['poisson'][1]:.3f}",
          flush=True)
    # E3
    params = {"deps": DEPS6, "c": C0, "t0s": SAT_T0}
    ga = ckpt_key.load("sat_gaps", KEYFILE, params)
    if ga is None:
        ga = [dict(t0=t0, **gap_alignment(S, Z, t0))
              for t0 in SAT_T0]
        ckpt_key.save("sat_gaps", KEYFILE, params, ga)
    for r in ga:
        print(f"  E3 t0={r['t0']:.0f}: minimizer peak gamma "
              f"{r['gamma_peak']:.2f}, largest band gap "
              f"{r['max_gap']:.2f} (mean {r['mean_gap']:.2f}) at "
              f"{r['max_gap_mid']:.2f}, dist {r['dist']:.2f}",
              flush=True)
    # E4
    params = {"deps": DEPS6, "c": C0, "lo": 350.0, "hi": 520.0,
              "step": 5.0}
    fs = ckpt_key.load("sat_scan", KEYFILE, params)
    if fs is None:
        fs = fine_scan(S, Z)
        ckpt_key.save("sat_scan", KEYFILE, params, fs)
    ms = np.array([r["m"] for r in fs])
    gs = np.array([r["gmax"] for r in fs])
    cc = float(np.corrcoef(np.log(ms), gs)[0, 1])
    print(f"  E4 scan 350-520 step 5: m range [{ms.min():.3f}, "
          f"{ms.max():.3f}] median {np.median(ms):.3f}; "
          f"corr(log m, max-gap) {cc:+.3f}", flush=True)
    for r in fs:
        print(f"     t0 {r['t0']:.0f}: m {r['m']:.3f} gmax "
              f"{r['gmax']:.2f}", flush=True)


def run2():
    """E2b: the coverage-fixed surrogate rerun (N = 320, full-band
    CUE) plus the lattice at half = 300 (edge-effect quantifier)."""
    Z = zeros380()
    S = TwoSided(C0)
    params = {"deps": DEPS6, "c": C0, "t0": T0, "nreal": 10,
              "seed": 23, "half": 200.0, "N": 320, "lat_half": 300.0}
    st = ckpt_key.load("sat_surrogates2", KEYFILE, params)
    if st is None:
        dens = local_density(T0)
        rng = np.random.default_rng(23)
        vals = [margin(S, cue_points(rng, T0, 200.0, dens, N=320),
                       T0) for _ in range(10)]
        lat3 = T0 + (np.arange(-int(300.0*dens),
                               int(300.0*dens) + 1))/dens
        st = {"cue_fixed": [float(np.mean(vals)), float(np.std(vals)),
                            float(np.min(vals)), float(np.max(vals))],
              "lattice300": margin(S, lat3, T0)}
        ckpt_key.save("sat_surrogates2", KEYFILE, params, st)
    print(f"  E2b cue (full coverage, N=320): {st['cue_fixed'][0]:.3f} "
          f"+- {st['cue_fixed'][1]:.3f} (range {st['cue_fixed'][2]:.3f}"
          f"..{st['cue_fixed'][3]:.3f});  lattice half=300: "
          f"{st['lattice300']:.3f}", flush=True)


if __name__ == "__main__":
    run()
    run2()
    print("saturation probes complete", flush=True)
