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

RESULT (probes complete; the E5 gauge experiment settles the arc).
NOTE FIRST: this file's header premise -- "the FULL zero form
carries +odd(PRIME) ... so the zero tail must carry +2 odd(PRIME)"
-- was REFUTED by its own E4: there is no tail bookkeeping at all.
The header is retained as the record of the hypothesis under test.

  E1 (window sweep): beta(T) plateaus at -0.998/-1.000 from
      T = 350-400 upward -- the identity locks once the window
      covers band + leakage reach ((120,300) at T = 350 clips the
      reach: -0.926); NOT window-tuned.
  E2 (per-prime): beta_n = -1 within 1-3% for every prime power
      with non-tiny odd norm at (120,300) (all 24 powers; the bulk
      within 1%); same at (60,200) for ||odd PRIME_n|| >~ 1.5
      (small-norm entries fit-noisy). The windowed zero
      configuration reconstructs EACH prime's operator
      contribution individually.
  E3 (residual anatomy): R projects onto odd(ARCH) at
      -0.9998/-0.9958 and onto the pole at ~ +-0.9: the statement
      is odd(Q_Z) = -odd(ARCH + POLE + PRIME)_code + eps with
      ||eps|| = 0.02-0.03 out of ~21 -- the full arithmetic trio
      at -1, closure 1.5e-3.
  E4 (tail): 280 further ordinates (653 -> 1013; 269 of them
      below the T = 1000 trajectory cap -- round-234 F2) contribute
      0.0000 to the odd projection; beta(win) unmoved to four
      decimals. The far zeros are invisible to the section.
  E5 (the gauge experiment; gauge_check() below): rebuilding ARCH
      in the true gauge (complex vhat on the same r-grid) gives
      ||ARCH_true - conj(ARCH_code)|| = 0.0000 exactly, and
      ARCH_true + POLE + conj(PRIME_code) matches Q_Z,380
      DIRECTLY at 0.0020/0.0037 Frobenius (the code-orientation
      build matches conj(Q_Z) at 0.047/0.055 instead).

VERDICT -- the Reflection Identity DEFLATES: the certified
1bb-lineage arithmetic machinery builds the CONJUGATE of the
explicit-formula operator (a phase-gauge convention: real
psi_hat_batch + the e^{+i tau0 u} prime orientation), so
Q_W_code ~= conj(Q_Z) is the plain windowed explicit formula seen
through that convention. Every certified scalar -- margins,
eigenvalues, pins -- is conjugation-blind and UNAFFECTED; the g4
proximity explanation stands in cleaner form (isospectrality =
the formula's operator-level closure + the measured defect).
What stands as the arc's real content: THE WINDOWED EXPLICIT
FORMULA HOLDS OPERATOR-WISE ON CONCENTRATED SECTIONS at 0.2-0.4%
Frobenius -- tail-free (E4), window-local (E1), per-prime
resolved at beta_n = -1 (E2), odd-sector closure 1.5e-3 (E3).
Open: the defect's anatomy (0.2-0.7%, rising with tau0 --
quadrature/Rwin/list-finiteness split unmeasured). Convention
flag for future operator-level (phase-sensitive) work on the 1bb
lineage: as-built arithmetic = conj(formula operator).
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


def gauge_check():
    """E5: rebuild ARCH in the true gauge (complex vhat over the
    code's own r-grid) and test which orientation satisfies the
    explicit formula directly. Recorded output at 87f30b1+:
      (60,200):  ARCH_true+POLE+PRIME_code vs QZ 0.7891 / vs
                 conj(QZ) 0.0470;  ...+conj(PRIME_code) vs QZ
                 0.0020 / vs conj(QZ) 0.7896;
                 ||ARCH_true - conj(ARCH_code)|| = 0.0000
      (120,300): 0.5870/0.0554; 0.0037/0.5896; 0.0000"""
    from scipy.special import digamma as scipy_digamma
    Z = zeros380()
    for c, t0 in PTS4:
        S = TwoSided(c)
        QZ = zform(S, Z, t0)
        S.weil_margin(t0)
        Rwin, NR = 800.0, 120001
        r = np.linspace(t0 - Rwin, t0 + Rwin, NR)
        Vc = np.asarray(S.vhat(((r - t0)*A).astype(complex)))
        if Vc.shape[0] != NR:
            Vc = Vc.T
        ker = np.real(scipy_digamma(0.25 + 0.5j*r)) - np.log(np.pi)
        dr = r[1] - r[0]
        AT = (Vc.conj().T * ker[None, :]) @ Vc * dr/(2*np.pi)
        AT = (AT + AT.conj().T)/2
        POLE = S.QW - S.ARCH - S.PRIME
        for tag, PR in (("PRIME_code", S.PRIME),
                        ("conj(PRIME_code)", np.conj(S.PRIME))):
            QWt = AT + POLE + PR
            QWt = (QWt + QWt.conj().T)/2
            nq = np.linalg.norm(QWt)
            print(f"  ({c:.0f},{t0:.0f}) ARCH_true+POLE+{tag}: vs QZ "
                  f"{np.linalg.norm(QWt - QZ)/nq:.4f}  vs conj(QZ) "
                  f"{np.linalg.norm(QWt - np.conj(QZ))/nq:.4f}",
                  flush=True)
        print(f"  ({c:.0f},{t0:.0f}) ||ARCH_true - conj(ARCH_code)|| = "
              f"{np.linalg.norm(AT - np.conj(S.ARCH)):.6f}", flush=True)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "gauge":
        gauge_check()
    else:
        run()
    print("partition probes complete", flush=True)
