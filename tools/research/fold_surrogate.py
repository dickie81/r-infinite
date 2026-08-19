#!/usr/bin/env python3
"""Fold attack, instrument 2: the transfer. Gaussian surrogate zero
sets whose displacement fields carry EXACTLY the two second-order
profiles (zeta's prime-budget saturation; CUE's RMT log-climb),
count-conditioned as in 1bc's headline, pushed through the 1bc
section margin at the ten conditioned points. If the surrogate
difference reproduces +0.710 +- 0.086, the stiffness excess is
DERIVED from the second-order rigidity profiles alone (the
saturation being the primes' budget); any shortfall quantifies the
non-Gaussian / higher-order remainder.

Surrogates: stationary Gaussian delta_n on n = 1..380 by circulant
embedding of C(l) = sigma^2 - D(l)/2 (negative circulant modes
clipped); positions gamma_n = inv_Nbar(n - 1/2 + delta_n).
D-profiles: the measured/analytic hybrid pinned by fold_D.py --
  zeta: alpha * D_prime_sum(l; T0=320), alpha = plateau match
  CUE:  Sigma^2 form minus the statistic-conversion constant c0,
        both from fold_D's empirics.
Conditioning: accept iff the in-band count at the point equals the
comb's (the 1bc protocol), deterministic seed ladder, 16 accepted
per point per ensemble.

RESULT LADDER (superseded history, round-224 F1/F2: the runs below
carried empirical floors 0.12/0.18 that overrode the derived zeta
bracket, and a grid differing from certified 1bc's at four of ten
points; the as-stated configuration's pins live in
cascade_prime_budget_fold.py g7/g8):
  hybrid profiles (alpha-scaled):                    +0.812 +- 0.096
  floored profiles, landing grid, seeds 7000/9000:   +0.841 / +0.922
The parameter-free profile FORMS and the exact constants (sawtooth
1/6; bracket ln ln X + Mertens + 1, measured 2.630/pi^2 vs the
formula's 2.630/pi^2 at T0 = 320) stand; the reviewer's sensitivity
runs showed the qualitative result robust across all four
configurations (forty point-evaluations, all positive).
"""
import numpy as np, math, os, sys
from numpy.polynomial import legendre as L
from scipy.special import spherical_jn
from scipy.linalg import eigh as scipy_eigh
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fold_D import (Nbar, inv_Nbar, D_zeta_analytic, D_cue_analytic,
                    TWO_PI)

A = 2.0
NZ = 380


def make_basis(c, n, KL):
    k = np.arange(KL)
    alpha = (k + 1)/np.sqrt((2*k + 1)*(2*k + 3))
    Tx = np.zeros((KL, KL))
    for i in range(KL - 1):
        Tx[i, i+1] = Tx[i+1, i] = alpha[i]
    Lm = -np.diag(k*(k + 1.0)) - c*c*(Tx @ Tx)
    ev, V = scipy_eigh(Lm)
    return V[:, np.argsort(-ev)[:n]].T


def psi_hat_batch(coefs, s):
    KL = coefs.shape[1]
    ks = np.arange(KL)
    J = np.empty((KL, len(s)))
    absl = np.abs(s)
    for k in ks:
        J[k] = spherical_jn(int(k), absl)
    sign = np.where(s[None, :] >= 0, 1.0, (-1.0)**(ks[:, None]))
    ph = (1j**ks)*np.sqrt(ks + 0.5)
    return (coefs.astype(complex)*ph[None, :]) @ (2*sign*J)


class Sect:
    def __init__(self, c):
        self.c = c
        self.n = int(2*c/math.pi) + 4
        KL = int(1.4*c) + 60
        self.P = make_basis(c, self.n, KL)
        xg, wg = np.polynomial.legendre.leggauss(800)
        PX = np.zeros((self.n, len(xg)))
        for m in range(self.n):
            PX[m] = L.legval(xg, self.P[m]*np.sqrt(np.arange(KL) + 0.5))
        self.G = A*np.einsum('ni,i,mi->nm', PX, wg, PX)

    def margin(self, zeros, tau0):
        s = np.concatenate([(zeros - tau0)*A, (-zeros - tau0)*A])
        V = psi_hat_batch(self.P, s)*A
        Q = V @ V.conj().T
        Q = (Q + Q.conj().T)/2
        return scipy_eigh(Q, self.G, eigvals_only=True)[0]


def surrogate_field(Dprof, rng, n=NZ, grid=2048):
    """Stationary Gaussian field with structure function Dprof
    (length >= grid//2) via circulant embedding of C = s2 - D/2."""
    s2 = Dprof[-1]/2.0
    C = np.empty(grid)
    C[0] = s2
    half = grid//2
    for l in range(1, half + 1):
        C[l] = s2 - Dprof[min(l, len(Dprof)) - 1]/2.0
    C[half+1:] = C[1:half][::-1]
    lam = np.fft.rfft(C).real
    lam = np.clip(lam, 0, None)
    z = rng.standard_normal(len(lam)) + 1j*rng.standard_normal(len(lam))
    f = np.fft.irfft(np.sqrt(lam*grid/2)*z, n=grid)
    return f[:n]


# round-224 F2: the landing's grid differed from certified 1bc's at
# four of ten points; this is 1bc's CGRID verbatim.
GRIDS = {60.0: [200, 240, 280, 300],
         120.0: [260, 300, 340, 360, 400, 450]}
NACC = 16


def run_fold(seed_base=9000, nacc=NACC, verbose=True):
    """The parameter-free fold at one deterministic seed ladder.
    Returns (per-point excess dict keyed "c:t0", mean, sem,
    calibration dict, profile summary dict)."""
    comb = np.array([inv_Nbar(float(k)) for k in range(1, NZ + 1)])
    lags = np.arange(1, 1025).astype(float)
    # PARAMETER-FREE profiles (fold_harden.py's decomposition):
    # the index/fixed conversion is the sawtooth constant 1/6 exactly
    # (S falls linearly by 1 between zeros: 2 x uniform var 1/12);
    # CUE fixed-shift D = Sigma^2 itself; zeta's saturation bracket =
    # ln ln X + Mertens + 1 (Mertens' theorem for the resolved primes
    # + the GUE short-time resummation tail), X = T0/2pi at the
    # window center. Zero fitted parameters.
    SIXTH = 1.0/6.0
    MERTENS = 0.2614972128476428
    X0 = 320.0/TWO_PI
    Vsat = (math.log(math.log(X0)) + MERTENS + 1)/math.pi**2
    # round-224 F1: the landing carried empirical floors (0.12/0.18)
    # here that silently overrode the derived bracket -- min(Sigma^2,
    # Vsat) - 1/6 = 0.0998 < 0.12 at EVERY lag, so the transfer ran on
    # the floor, not the formula. Floors removed: the profiles below
    # are exactly the stated parameter-free forms. (The zeta profile
    # is then the constant Vsat - 1/6 at every integer lag at this
    # window -- Sigma^2(1) = 0.346 already exceeds the bracket 0.266
    # -- i.e. a white-noise displacement field at the derived
    # variance; the CUE circulant's negative modes are clipped,
    # disclosed.)
    Dz_prof = np.minimum(D_cue_analytic(lags), Vsat) - SIXTH
    Dc_prof = D_cue_analytic(lags) - SIXTH
    if verbose: print(f"parameter-free: zeta sat bracket {Vsat*math.pi**2:.3f}/pi^2 "
          f"-> plateau {Vsat - SIXTH:.3f}; CUE(24) {Dc_prof[23]:.3f}",
          flush=True)
    if verbose: print(f"profiles: zeta plateau {Dz_prof[500]:.3f}; "
          f"CUE at 24/380: {Dc_prof[23]:.3f}/{Dc_prof[379]:.3f}", flush=True)
    # per-profile calibration: scale each field so the realized D
    # hits the target (round-224 C2: the x1.30 note described the
    # old hybrid profile; the current zeta field needs no clipping
    # and calibrates at 1.001)
    from fold_D import D_emp
    scale = {}
    crng = np.random.default_rng(99)
    for name, prof in (("zeta", Dz_prof), ("cue", Dc_prof)):
        r = np.mean([D_emp(surrogate_field(prof, crng), 48)
                     for _ in range(80)], axis=0)/prof[:48]
        scale[name] = 1.0/math.sqrt(float(np.mean(r)))
        if verbose:
            print(f"  calibration [{name}]: realized/target {np.mean(r):.3f} "
                  f"-> field scale {scale[name]:.4f}", flush=True)

    if verbose: print("building sections...", flush=True)
    sects = {c: Sect(c) for c in GRIDS}

    def band_count(zeros, c, t0):
        W = c/A
        return int(np.sum((zeros > t0 - W) & (zeros < t0 + W)))

    results = {}
    for c, taus in GRIDS.items():
        S = sects[c]
        for t0 in taus:
            target = band_count(comb, c, t0)
            m_comb = S.margin(comb, float(t0))
            out = {}
            for name, prof in (("zeta", Dz_prof), ("cue", Dc_prof)):
                rng = np.random.default_rng(seed_base + int(t0) + (0 if name == "zeta" else 1))
                Rs, tried = [], 0
                while len(Rs) < nacc and tried < 4000:
                    tried += 1
                    d = scale[name]*surrogate_field(prof, rng)
                    g = np.array([inv_Nbar(k - 0.5 + d[k-1], g0=comb[k-1])
                                  for k in range(1, NZ + 1)])
                    if band_count(g, c, t0) != target:
                        continue
                    m = S.margin(g, float(t0))
                    if m <= 1e-14 or m_comb <= 1e-14:
                        continue
                    Rs.append(math.log10(m/m_comb))
                out[name] = (np.mean(Rs), np.std(Rs), len(Rs), tried)
            dz, dc = out["zeta"], out["cue"]
            ex = dz[0] - dc[0]
            results[f"{c:g}:{t0}"] = ex
            if verbose:
                print(f"  c={c:4.0f} t0={t0:3d}: R_surrzeta {dz[0]:+.3f}"
                      f"(n={dz[2]}/{dz[3]}) R_surrcue {dc[0]:+.3f}"
                      f"(n={dc[2]}/{dc[3]}) excess {ex:+.3f}", flush=True)
    vals = np.array(list(results.values()))
    mean = float(np.mean(vals))
    sem = float(np.std(vals)/math.sqrt(len(vals)))
    prof = {"Vsat_bracket": Vsat*math.pi**2, "zeta_plateau": float(Dz_prof[500]),
            "cue_24": float(Dc_prof[23])}
    if verbose:
        print(f"\n FOLD RESULT: surrogate excess mean {mean:+.3f} "
              f"+- {sem:.3f} over {len(vals)} "
              f"points (1bc measured +0.710 +- 0.086)", flush=True)
    return results, mean, sem, {k: float(v) for k, v in scale.items()}, prof


if __name__ == "__main__":
    run_fold(seed_base=9000)
