#!/usr/bin/env python3
"""THE TWO-PRIME WINDOW, STAGE 0 -- float64 feasibility
reconnaissance on [log 3, log 4) (the research front queued
behind the A397 chain; opened on the owner's "Start on the
two-prime window").

THE OBJECT. The semi-local Weil form at the real place plus the
primes 2 AND 3. For test support length delta = 2a in
[log 3, log 4) the prime powers inside the autocorrelation window
(-delta, delta) are exactly log 2 and log 3 (log 4 = 2 log 2
enters only at delta > log 4; log 5 > log 4), so on that window
the two-prime form IS Weil's full quadratic functional --
identically, as the one-prime form is below log 3 (Theorem 1bj
(i)). Kernel:
    W_23(r) = Re psi(1/4 + ir/2) - log pi
              - C_2 cos(r log 2) - C_3 cos(r log 3),
    C_p = 2 Lambda(p) p^{-1/2} = 2 log p / sqrt p
(C_2 = sqrt 2 log 2, the certified one-prime coefficient; C_3 =
2 log 3 / sqrt 3 = 1.2685...). In t-space the prime part is the
pair of shifts
    T_prime b(t) = - sum_p (C_p/2) [b(t + log p) + b(t - log p)],
and everything else -- T_arch, the rank-one pole +/- 2 chi <chi,b>,
the trial families, the GL-panel quadratures, the whitening, the
Temple ladder -- is the committed one-prime t-space pipeline
(oneprime_fractional.py, adjudicated against the certified
instrument at the cos-24 anchor), imported and generalised here
by a PRIMES list. The second kink of the t-grid sits at
log 3 - a (the first at log 2 - a, both inside (0, a) on the
window).

WHAT STAGE 0 MEASURES (float64, NOT a certificate):
  * per cell (parity, delta): the section's own lambda_1 and
    lambda_2 on the union span (harmonics + rough + fractional
    Gegenbauer edges), the Temple value at the own-lambda_2 rung
    and the half rung, rho, sigma, the new-mode weight. A NEGATIVE
    section lambda_1 is a float64 counterexample candidate to
    positivity at that delta (the Rayleigh quotient of the full
    form is bounded above by the section's); a positive Temple
    value is the feasibility signal for a certificate.
  * the continuity check across log 3: the one-prime form at
    delta = 1.09 (its own window) against the two-prime form at
    delta = 1.10.
  * the wrong-form diagnostic: the ONE-prime form evaluated at
    delta in (log 3, log 4) -- Connes-Consani's numerical
    observation was that positivity is LOST past a prime's
    threshold and RESTORED by adding that prime's functional; the
    diagnostic shows which of the two happens here.
  * the kernel's negative set on [0, 260]: where W_23 < 0
    against W_2 (the Birman-Schwinger counting support of a later
    Stage II).

CELLS. delta in {1.10, 1.12, 1.13, 1.15, 1.20, 1.25, 1.30, 1.35, 1.38} for
even and odd (log 3 = 1.0986, log 4 = 1.3863).

CHECKS. 7: classical (the explicit formula's semi-local form,
Kato-Temple, GL quadrature). 8: no hypothesis input; Riemann-side
pure mathematics.

Keying law: every producing file in every key (executable
content). Not a tower member; a research probe whose numbers are
recorded as float64 reconnaissance only.
"""
import hashlib, math, os, sys, time

import numpy as np
from scipy.linalg import eigh as scipy_eigh
from scipy.special import digamma

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
import oneprime_fractional as OF
from oneprime_fractional import Modes, gl_panels, LG4PI, psign
from oneprime_push import temple_opt


def _sha(name):
    return ckpt_key.code_sha(os.path.join(HERE, name))


DEPS2 = {f: _sha(f) for f in ("oneprime_fractional.py",
                              "oneprime_push.py",
                              "oneprime_certificate.py",
                              "oneprime_bridge.py")}
KEYFILE = os.path.join(HERE, "twoprime_recon.py")

LOG3 = math.log(3.0)
LOG4 = math.log(4.0)


def Cp(p):
    """2 Lambda(p) / sqrt p for a prime p (k = 1 power)."""
    return 2.0*math.log(p)/math.sqrt(p)


PRIMES_ONE = (2,)
PRIMES_TWO = (2, 3)
CELLS = (1.10, 1.12, 1.13, 1.15, 1.20, 1.25, 1.30, 1.35, 1.38)


def W_kernel(r, primes):
    r = np.asarray(r, dtype=float)
    out = digamma(0.25 + 0.5j*r).real - math.log(math.pi)
    for p in primes:
        out = out - Cp(p)*np.cos(r*math.log(p))
    return out


def apply_T(md, primes, base=0.012):
    """oneprime_fractional.apply_T generalised: the prime part is
    the sum of shifts over `primes`; the t-grid kinks at
    log p - a for each prime inside (0, a)."""
    a, parity = md.a, md.parity
    kinks = tuple(sorted({min(max(math.log(p) - a, 0.0), a)
                          for p in primes}))
    tn, tw = gl_panels(0.0, a, sing=kinks + (a,), base=base)
    B = md.t_eval(tn)
    TB = -LG4PI*B.copy()
    f = np.cos if parity == "even" else np.sin
    for k, t in enumerate(tn):
        bt = B[:, k]
        acc = np.zeros(md.n)
        for lo, hi, sing in (((0.0, a - t, (a - t,))),
                             ((a - t, a + t, (a - t, a + t)))):
            u, wu = gl_panels(lo, hi, sing=sing, base=base)
            if len(u) == 0:
                continue
            A = (np.exp(u/2) - 1)/np.sinh(u)
            both_in = (t + u <= a) & (t - u >= -a)
            Bp = md.t_eval(t + u)
            Bm = md.t_eval(t - u)
            Dfull = (Bp + Bm)/2 - bt[:, None]
            Dh = -2*f(md.w[:, None]*t)*np.sin(
                md.w[:, None]*u[None, :]/2)**2
            D = np.where(both_in[None, :],
                         np.vstack([Dh, Dfull[md.nharm:]]),
                         Dfull)
            acc += bt*np.sum(A*wu)
            acc += (D*(np.exp(u/2)/np.sinh(u)*wu)[None, :]).sum(1)
        TB[:, k] -= acc
        TB[:, k] += bt*math.log(1.0/math.tanh((a + t)/2))
    for p in primes:
        lp = math.log(p)
        TB += -(Cp(p)/2)*(md.t_eval(tn + lp) + md.t_eval(tn - lp))
    chi = (np.cosh(tn/2) if parity == "even" else np.sinh(tn/2))
    v = 2*(B*(tw*chi)[None, :]).sum(1)
    TB += psign(parity)*2*np.outer(v, chi)
    return tn, tw, B, TB, v


def cell(a, parity, primes, base=0.012):
    md = Modes(a, parity)
    gf4 = max(max(fr["gF4"]) for fr in md.frac)
    assert gf4 < 1e-8, f"gF4 FAIL {parity} a={a}: {gf4:.1e}"
    tn, tw, B, TB, v = apply_T(md, primes, base=base)
    N = 2*(B*tw[None, :]) @ B.T
    # whiten the VALUE matrices (the committed pipeline's lesson:
    # Grams over one discrete measure keep S >= M N^-1 M exactly)
    d = 1.0/np.sqrt(np.diag(N))
    ev, U = np.linalg.eigh(d[:, None]*N*d[None, :])
    keep = ev > 1e-4
    Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T*d[None, :])
    Bw, TBw = Wh @ B, Wh @ TB
    NA = 2*(Bw*tw[None, :]) @ Bw.T
    MA = 2*(Bw*tw[None, :]) @ TBw.T
    SA = 2*(TBw*tw[None, :]) @ TBw.T
    NA, MA, SA = (NA + NA.T)/2, (MA + MA.T)/2, (SA + SA.T)/2
    lams = scipy_eigh(MA, NA, eigvals_only=True)
    l1, l2 = float(lams[0]), float(lams[1])
    res = SA - MA @ np.linalg.solve(NA, MA)
    minres = float(np.linalg.eigvalsh((res + res.T)/2)[0])
    out = {"dim": int(NA.shape[0]), "gF4": gf4, "lambda1": l1,
           "lambda2": l2, "minres": minres, "nharm": md.nharm}
    for tag, ell2 in (("own", l2), ("half", 0.5*l2)):
        try:
            mu, c = temple_opt(NA, MA, SA, ell2)
        except np.linalg.LinAlgError:
            # a form negative enough that ell2 N - M is not positive
            # definite (the wrong-form diagnostic past its window):
            # Temple is undefined there; lambda_1 is the verdict
            mu, c = float("nan"), None
        if c is not None:
            nn = float(c @ NA @ c)
            rho = float(c @ MA @ c)/nn
            sig = math.sqrt(max(float(c @ SA @ c)/nn - rho*rho, 0.0))
            craw = Wh.T @ c
            nold = md.nharm if parity == "odd" else OF.NHALF
            fw = float(np.sum(craw[nold:]**2)/np.sum(craw**2))
        else:
            rho = sig = fw = float("nan")
        out[tag] = {"ell2": ell2, "temple": mu, "rho": rho,
                    "sigma": sig, "new_weight": fw}
    return out


def kernel_negative_set(primes, rmax=260.0, h=0.002):
    rs = np.arange(0.0, rmax, h)
    w = W_kernel(rs, primes)
    neg = w < 0
    idx = np.flatnonzero(np.diff(neg.astype(int)))
    edges = list(rs[idx + 1])
    if neg[0]:
        edges = [0.0] + edges
    if neg[-1]:
        edges = edges + [rmax]
    pieces = [(float(edges[i]), float(edges[i + 1]))
              for i in range(0, len(edges) - 1, 2)]
    return {"pieces": pieces, "total_len": float(sum(b - a for a, b in pieces)),
            "min": float(w.min()), "argmin": float(rs[int(w.argmin())])}


def run():
    params = {"deps": DEPS2, "cells": CELLS, "primes": PRIMES_TWO,
              "nus": OF.NUS, "nfr": OF.NFR, "nrough": OF.NROUGH}
    st = ckpt_key.load("twoprime_recon", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is not None:
        return st
    st = {"kernel": {"one": kernel_negative_set(PRIMES_ONE),
                     "two": kernel_negative_set(PRIMES_TWO)}}
    for tag, K in st["kernel"].items():
        print(f"KERNEL {tag}-prime: negative pieces {len(K['pieces'])} "
              f"total length {K['total_len']:.3f} min {K['min']:+.4f} "
              f"at r = {K['argmin']:.3f}; first pieces "
              f"{[(round(x, 3), round(y, 3)) for x, y in K['pieces'][:4]]}",
              flush=True)
    # continuity anchor: the one-prime form at its own window top
    t0 = time.time()
    for parity in ("even", "odd"):
        r = cell(1.09/2, parity, PRIMES_ONE)
        st[f"anchor:{parity}:1.09"] = r
        print(f"ANCHOR one-prime {parity} delta 1.09: lambda1 "
              f"{r['lambda1']:+.3e} lambda2 {r['lambda2']:+.3e} Temple(own) "
              f"{r['own']['temple']:+.3e} sigma {r['own']['sigma']:.3e} "
              f"[{time.time() - t0:.0f}s]", flush=True)
    for delta in CELLS:
        for parity in ("even", "odd"):
            for tag, primes in (("two", PRIMES_TWO), ("one", PRIMES_ONE)):
                r = cell(delta/2, parity, primes)
                st[f"{tag}:{parity}:{delta:g}"] = r
                print(f"{tag.upper():>4}-prime {parity:4s} delta {delta:g}: "
                      f"lambda1 {r['lambda1']:+.3e} lambda2 {r['lambda2']:+.3e} "
                      f"Temple(own) {r['own']['temple']:+.3e} (rho "
                      f"{r['own']['rho']:+.3e} sig {r['own']['sigma']:.3e} "
                      f"nw {r['own']['new_weight']:.3f}) half "
                      f"{r['half']['temple']:+.3e} mr {r['minres']:+.1e} "
                      f"[{time.time() - t0:.0f}s]", flush=True)
                ckpt_key.save("twoprime_recon_partial", KEYFILE, params,
                              st, kfun=ckpt_key.code_key)
    ckpt_key.save("twoprime_recon", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    return st


STAB_CELLS = ((1.30, "even"), (1.30, "odd"), (1.35, "even"),
              (1.35, "odd"), (1.38, "even"), (1.38, "odd"))
STAB_BASES = (0.012, 0.008, 0.005)


def stability():
    """The window-top adjudication (Stage 0b): the base-0.012 run
    read the odd section's lambda_1 at -1.45e-9 (1.35) and
    -3.1e-9 (1.38) -- a sign the FULL form cannot have below
    log 4 unless RH is false, so the reading must be measured
    against the pipeline's quadrature floor before any statement.
    The six window-top cells at GL-panel bases 0.012 / 0.008 /
    0.005: a lambda_1 that moves with the base is quadrature; the
    record's precedent (the even-1.0 Temple value, -9.4e-7 ->
    -2.7e-7 at base 0.008) sets the expected scale."""
    params = {"deps": DEPS2, "cells": STAB_CELLS, "bases": STAB_BASES,
              "primes": PRIMES_TWO, "nus": OF.NUS, "nfr": OF.NFR,
              "nrough": OF.NROUGH}
    st = ckpt_key.load("twoprime_stab", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is not None:
        return st
    st = {}
    t0 = time.time()
    for delta, parity in STAB_CELLS:
        for base in STAB_BASES:
            r = cell(delta/2, parity, PRIMES_TWO, base=base)
            st[f"{parity}:{delta:g}:{base:g}"] = r
            print(f"STAB two-prime {parity:4s} delta {delta:g} base {base:g}: "
                  f"lambda1 {r['lambda1']:+.3e} lambda2 {r['lambda2']:+.3e} "
                  f"Temple(own) {r['own']['temple']:+.3e} sigma "
                  f"{r['own']['sigma']:.3e} mr {r['minres']:+.1e} "
                  f"[{time.time() - t0:.0f}s]", flush=True)
            ckpt_key.save("twoprime_stab_partial", KEYFILE, params, st,
                          kfun=ckpt_key.code_key)
    ckpt_key.save("twoprime_stab", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    return st


if __name__ == "__main__":
    if os.environ.get("TP_STABILITY") == "1":
        stability()
        print("two-prime window stage-0b stability complete", flush=True)
    else:
        run()
        print("two-prime window stage-0 reconnaissance complete", flush=True)
