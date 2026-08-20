#!/usr/bin/env python3
"""The partition attack (commissioned after the Reflection Identity,
15f9509): dissect the window-partition law -- the measured
    odd(Q_Z,380) ~= -odd(PRIME)          (residual 2e-3)
against the exact windowed explicit formula, under which the FULL
zero form carries +odd(PRIME) (as built, Q_full = ARCH + POLE +
PRIME with the prime matrix's sign), so the zero tail must carry
+2 odd(PRIME) and the window FLIPS the sign of the odd
fluctuation integral. Four experiments:

  (E1) WINDOW SWEEP (existing 380 ordinates): the projection
       coefficient beta(T) = <odd Q_Z(T), odd PRIME>_F /
       ||odd PRIME||_F^2 for window |gamma| <= T, T = 350..653.
       Plateau at -1 => a robust local duality; drift => the -1 at
       653 is window-tuned.
  (E2) PER-PRIME DECOMPOSITION: least-squares fit odd(Q_Z) ~=
       sum_n beta_n odd(PRIME_n) over the prime powers n <= e^4
       individually -- does the windowed zero configuration hear
       EACH prime with coefficient -1 (the per-prime duality), or
       only the aggregate?
  (E3) RESIDUAL ANATOMY: R = odd(Q_Z) + odd(PRIME) has norm 0.043
       while ||odd ARCH|| = 1.23 -- the density-slope (archimedean)
       odd part is ABSENT from the windowed identity, so the tail
       absorbs it too. Measure corr(R, odd ARCH), corr(R, odd
       POLE), and the unexplained remainder.
  (E4) TAIL TRAJECTORY: extend the ordinate list to gamma ~ 1000
       (mpmath zetazero, chunked resumable checkpoints) and track
       beta(T) for T = 700..1000: direction and rate of the
       predicted march from -1 toward +1 (equivalently the tail's
       accumulating +2), and the tail-only projection
       <odd(TailForm(653,T)), odd PRIME> / ||odd PRIME||^2 -> +2?

Check 7: unconditional explicit formula + finite linear algebra;
the S(t) route invoked only as interpretation. Check 8: no
hypothesis input. Keying per A355: DEPS carries this file,
floor_probe.py, and the four substrate modules; params carry the
stage inputs (point, window list, chunk indices).

RESULT: appended after the run by the analysis pass.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from fold_D import zeros380
from fold_surrogate import A
from witness_twosided import (TwoSided, vonmangoldt, DELTA,
                              TGX, TGW, NS_PR, LAMV)


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS4 = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "witness_offline.py",
    "witness_twosided.py", "floor_probe.py", "floor_probe4.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

PTS4 = [(60.0, 200.0), (120.0, 300.0)]
SWEEP_T = [350.0, 400.0, 450.0, 500.0, 550.0, 600.0, 653.7]
EXT_TO = 660          # zetazero index cap (gamma(660) ~ 1015)
EXT_CHUNK = 40
EXT_T = [700.0, 750.0, 800.0, 850.0, 900.0, 950.0, 1000.0]


def odd(M, n):
    P = np.diag([(-1.0)**k for k in range(n)])
    return (M - P @ M @ P)/2


def zform(S, gams, t0):
    """Zero form for an explicit ordinate list (with mirrors)."""
    if len(gams) == 0:
        return np.zeros((S.n, S.n), dtype=complex)
    g = np.asarray(gams)
    s = np.concatenate([(g - t0)*A, (-g - t0)*A])
    Vb = np.asarray(S.vhat(s.astype(complex)))
    if Vb.shape[0] != len(s):
        Vb = Vb.T
    Q = Vb.conj().T @ Vb
    return (Q + Q.conj().T)/2


def prime_mats_per_n(S, tau0):
    """The prime matrix split per prime power n (the code's
    prime_mat loop, one matrix per n)."""
    from numpy.polynomial import legendre as L
    out = {}
    for n_ in NS_PR:
        u = np.log(n_)
        if u >= DELTA:
            continue
        lo, hi = -1.0, 1.0 - u/A
        xm = (hi + lo)/2 + (hi - lo)/2*TGX
        wm = (hi - lo)/2*TGW*A
        B1 = S.psi_x(xm)
        B2 = S.psi_x(xm + u/A)
        Am = np.einsum('ni,i,mi->nm', B1, wm, B2)
        phz = np.exp(1j*tau0*u)
        PR = -LAMV[n_]/np.sqrt(n_)*(phz*Am + np.conj(phz)*Am.T)
        out[int(n_)] = PR
    return out


def frob(Mv):
    return float(np.linalg.norm(Mv))


def proj(Ma, Mb):
    """<Ma, Mb>_F / ||Mb||_F^2 (real part)."""
    return float(np.real(np.sum(np.conj(Mb)*Ma)) /
                 max(np.sum(np.abs(Mb)**2), 1e-300))


def ext_zeros():
    """Ordinates 381..EXT_TO via mpmath, chunked + resumable."""
    from mpmath import mp, zetazero
    mp.dps = 15
    gams = []
    for lo in range(381, EXT_TO + 1, EXT_CHUNK):
        hi = min(lo + EXT_CHUNK - 1, EXT_TO)
        # keying note (A355 disclosure): these chunks are pure
        # mathematical constants fully determined by (lo, hi, dps,
        # fn) -- the file sha is deliberately NOT in the key, so a
        # docstring/RESULT edit does not spuriously recompute ~10
        # minutes of mpmath; any change to what is computed must
        # change these params.
        params = {"fn": "mpmath.zetazero.imag",
                  "lo": lo, "hi": hi, "dps": 15}
        name = f"zext_{lo}_{hi}"
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            st = [float(zetazero(k).imag) for k in range(lo, hi + 1)]
            ckpt_key.save(name, KEYFILE, params, st)
            print(f"  zext {lo}-{hi}: gamma {st[0]:.2f}..{st[-1]:.2f}",
                  flush=True)
        gams.extend(st)
    return np.array(gams)


def run():
    Z = zeros380()
    sects = {}
    def sect(c):
        if c not in sects:
            sects[c] = TwoSided(c)
        return sects[c]

    for c, t0 in PTS4:
        S = sect(c)
        n = S.n
        S.weil_margin(t0)
        oPR = odd(S.PRIME, n)
        oAR = odd(S.ARCH, n)
        oPO = odd(S.QW - S.ARCH - S.PRIME, n)
        nPR = frob(oPR)
        print(f"\n== ({c:.0f},{t0:.0f})  ||oddPRIME|| {nPR:.3f} "
              f"||oddARCH|| {frob(oAR):.3f} ||oddPOLE|| "
              f"{frob(oPO):.4f}", flush=True)

        # E1: window sweep on the existing list
        for T in SWEEP_T:
            sub = Z[Z <= T]
            oQ = odd(zform(S, sub, t0), n)
            b = proj(oQ, oPR)
            r = frob(oQ + oPR)/nPR
            print(f"  E1 T={T:6.1f} nz={len(sub):3d}: beta {b:+.4f} "
                  f"resid {r:.4f}", flush=True)

        # E2: per-prime fit at the full window
        oQ = odd(zform(S, Z, t0), n)
        mats = prime_mats_per_n(S, t0)
        keys = sorted(mats)
        omats = [odd(mats[k], n) for k in keys]
        Gm = np.array([[np.real(np.sum(np.conj(a)*b)) for b in omats]
                       for a in omats])
        rhs = np.array([np.real(np.sum(np.conj(a)*oQ)) for a in omats])
        beta = np.linalg.lstsq(Gm, rhs, rcond=None)[0]
        print("  E2 per-n beta (n: beta, ||odd PR_n||):", flush=True)
        for k, b in zip(keys, beta):
            print(f"     n={k:3d}: {b:+.3f}  ({frob(odd(mats[k],n)):7.3f})",
                  flush=True)

        # E3: residual anatomy
        R = oQ + oPR
        cAR = proj(R, oAR)
        R2 = R - cAR*oAR
        cPO = proj(R2, oPO) if frob(oPO) > 0 else 0.0
        R3 = R2 - cPO*oPO
        print(f"  E3 ||R|| {frob(R):.4f}; proj onto oddARCH {cAR:+.4f} "
              f"(residual after {frob(R2):.4f}); onto oddPOLE "
              f"{cPO:+.3f} (after {frob(R3):.4f})", flush=True)

    # E4: extended tail trajectory
    ZE = ext_zeros()
    print(f"\n  extended ordinates: {len(ZE)} up to {ZE[-1]:.1f}",
          flush=True)
    for c, t0 in PTS4:
        S = sect(c)
        n = S.n
        oPR = odd(S.PRIME, n)
        n2 = float(np.sum(np.abs(oPR)**2))
        print(f"== E4 ({c:.0f},{t0:.0f}):", flush=True)
        base = odd(zform(S, Z, t0), n)
        for T in EXT_T:
            sub = ZE[ZE <= T]
            oQ = base + odd(zform(S, sub, t0), n)
            b = proj(oQ, oPR)
            btail = proj(oQ - base, oPR)
            print(f"  T={T:6.1f} (+{len(sub):3d} zeros): beta(win) "
                  f"{b:+.4f} beta(tail 653->T) {btail:+.4f}",
                  flush=True)


if __name__ == "__main__":
    run()
    print("partition probes complete", flush=True)
