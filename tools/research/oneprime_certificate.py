#!/usr/bin/env python3
"""THE ONE-PRIME ARC, STAGE B1 -- the diagonal-kernel
representation and the certificate feasibility survey.

Commission: "B1 pls" (the staged plan in oneprime_notes.py; Stage A
landed in oneprime_bridge.py).

THE REPRESENTATION (the opening structural result). The prime term
of the semi-local Weil form is DIAGONAL IN FREQUENCY: CC's
<f|V(n)f> = n^{-1/2}[(f* star f)(n) + (f* star f)(n^-1)] is the
autocorrelation of f at +-log n, i.e. (1/2pi) int |ghat(t)|^2
2 cos(t log n) dt. The archimedean term is diagonal by
construction (kernel 2 theta'), and the pole term is rank one per
parity sector. Hence on the one-prime window delta in
[log 2, log 3) the whole form collapses to

  Q(g) = (1/2pi) int |ghat(t)|^2 W(t) dt  +-  2 <chi, G>^2,
  W(t)  = 2 theta'(t) - sqrt(2) log 2 * cos(t log 2),
  chi   = cosh(t/2) (even sector, + sign) /
          sinh(t/2) (odd sector, - sign),

with ONE delta-independent kernel W across the whole window (only
the support class [-a, a], a = delta/2, grows; below log 2 the
cosine term self-annihilates against the autocorrelation's
support, so the representation is valid for all delta < log 3).
The certificate problem is therefore PURE KERNEL-SIGN GEOMETRY vs
PALEY-WIENER CONCENTRATION: can |ghat|^2 (type a <= 0.549, unit
L^2) hide enough mass in W's negative dips to beat the positive
region plus the pole? No zeros ledger enters -- if the class
infimum can be lower-bounded positively by explicit analysis, the
result is an UNCONDITIONAL Weil-positivity theorem for the window,
strictly beyond CC's L <= log 2 (their Selecta Theorem 1). The
verified-zeros chain of the original B1 plan survives as the
fallback route if the direct analysis cannot close.

PRIOR-ART DUTY (Stage-0 amendment). CC's ref [14] for the
numerical positivity at lambda = sqrt(2) is Yoshida 1992 ("On
Hermitian forms attached to zeta functions") -- numerics, at
L = log 2 exactly, consistent with the Stage-0 verdict. Bombieri's
"Remarks on Weil's quadratic functional in the theory of prime
numbers" (Rend. Lincei 2000) works variationally on the same
functional and MUST be read before any unconditional-theorem claim
for the window is made; until that check, every positivity number
here is a measurement, not a claimed theorem.

THE INSTRUMENT.
  S1  the representation gate: the diagonal prime
      -(1/2pi) int sqrt(2) log 2 cos(r log 2) q_i q_j dr (r-grid)
      against the certified t-overlap PRIME (t-grid), both
      parities, three deltas -- two independent quadratures of the
      same operator.
  S2  the kernel chart: W's sign geometry on [0, 60] at dr 1e-3 --
      the negative dips (intervals, depths), all crossings, the
      near-zero squeak at the second cosine peak t = 4pi/log 2 ~
      18.13, and the floor past the last crossing (positivity of W
      beyond it checked to r = 200, with the asymptotic
      W >= log(t/2pi) - sqrt(2) log 2 taking over).
  S3  the feasibility survey per (delta, parity) across the
      window: cos-basis (certified NBASE = 24) section lambda_1,
      lambda_2 and extremal; a SMOOTH trial basis (cos^4 window x
      harmonics, C^3 at the support edges, grid-orthonormalized,
      n = 16) whose extremal phi has small Temple residual; the
      residual sigma = ||T phi - rho phi|| computed on a wide
      r-grid (Rmax 1500); the Kato-Temple FEASIBILITY value
      lambda_T = rho - sigma^2/(ell_2 - rho) with ell_2 = the
      cos-24 section lambda_2 (a stand-in, NOT a rigorous lower
      bound for the true second eigenvalue -- the survey measures
      whether the route can close, it does not certify); and the
      extremal's budget decomposition (pole share, dip-mass vs
      positive-mass of |ghat|^2 against W).

CHECKS. 7: classical throughout (explicit formula, Fourier
analysis, Kato-Temple spectral bounds); no semiclassics. 8: no
hypothesis input; pure analytic number theory.

Keying law: every producing file in every key.
"""
import hashlib, math, os, sys

import numpy as np
from scipy.special import psi as scipy_digamma
from scipy.linalg import eigh as scipy_eigh

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from oneprime_bridge import (NBASE, LOG2, LOG3, build_Q64,
                             fhat_matrix64, overlap_matrix,
                             basis_eval, freqs)

def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPSC = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                              "height_uniformity.py",
                              "oneprime_bridge.py",
                              "oneprime_certificate.py")}
KEYFILE = os.path.join(HERE, "oneprime_certificate.py")

C2 = math.sqrt(2.0)*math.log(2.0)          # 2 Lambda(2)/sqrt(2)

def hplus(r):
    return np.real(scipy_digamma(0.25 + 0.5j*r)) - np.log(np.pi)

def Wker(r):
    return hplus(r) - C2*np.cos(r*math.log(2.0))

def tgrid(a, npts=4001):
    tg = np.linspace(-a, a, npts)
    return tg, tg[1] - tg[0]

def trapzw(npts, h):
    w = np.full(npts, h)
    w[0] = w[-1] = h/2
    return w

def smooth_basis(a, parity, nsm=16, p=4, npts=4001):
    """cos^p(pi t/(2a)) window times harmonics, grid-orthonormalized
    via symmetric whitening (C^{p-1} at the support edges -> ghat
    decay r^-(p+1))."""
    tg, dt = tgrid(a, npts)
    win = np.cos(np.pi*tg/(2*a))**p
    ks = (np.arange(nsm) if parity == "even"
          else np.arange(1, nsm + 1))
    raw = (win[None, :]*np.cos(ks[:, None]*np.pi*tg[None, :]/a)
           if parity == "even"
           else win[None, :]*np.sin(ks[:, None]*np.pi*tg[None, :]/a))
    wq = trapzw(npts, dt)
    Gm = (raw*wq[None, :]) @ raw.T
    ev, U = np.linalg.eigh(Gm)
    keep = ev > 1e-12*ev[-1]
    B = (U[:, keep]/np.sqrt(ev[keep])[None, :]).T @ raw
    return tg, dt, B

def qhat_rows(B, tg, dt, r, parity, chunk=10001):
    """q_k(r) = int G_k(t) {cos,sin}(rt) dt, chunked over r."""
    wq = trapzw(len(tg), dt)
    Bw = B*wq[None, :]
    out = np.empty((B.shape[0], len(r)))
    f = np.cos if parity == "even" else np.sin
    for i in range(0, len(r), chunk):
        rr = r[i:i + chunk]
        out[:, i:i + chunk] = Bw @ f(np.outer(tg, rr))
    return out

def chi_vec(B, tg, dt, parity):
    wq = trapzw(len(tg), dt)
    chi = np.cosh(tg/2) if parity == "even" else np.sinh(tg/2)
    return (B*wq[None, :]) @ chi

def psign(parity):
    return 1.0 if parity == "even" else -1.0

def residual(phi, tg, dt, parity, rw, Ww, chunk=10001):
    """One-pass wide-grid application of T to the trial phi:
    returns (rho, sigma, pos_mass, neg_mass, pole), all in
    ||phi||^2-normalized units."""
    wq = trapzw(len(tg), dt)
    f = np.cos if parity == "even" else np.sin
    drw = rw[1] - rw[0]
    Tphi = np.zeros(len(tg))
    posm = negm = 0.0
    for i in range(0, len(rw), chunk):
        rr = rw[i:i + chunk]
        C = f(np.outer(tg, rr))
        qc = (phi*wq) @ C
        Wc = Ww[i:i + chunk]
        Tphi += C @ (Wc*qc)
        q2 = qc*qc
        posm += float(np.sum(q2[Wc > 0]*Wc[Wc > 0]))
        negm += float(np.sum(q2[Wc < 0]*Wc[Wc < 0]))
    Tphi *= drw/(2*np.pi)
    chi = np.cosh(tg/2) if parity == "even" else np.sinh(tg/2)
    pv = float((phi*wq) @ chi)
    Tphi += psign(parity)*2*pv*chi
    nrm = float((phi*wq) @ phi)
    rho = float((phi*wq) @ Tphi)/nrm
    Tn2 = float((Tphi*wq) @ Tphi)/nrm
    sig = math.sqrt(max(Tn2 - rho*rho, 0.0))
    return (rho, sig, posm*drw/(2*np.pi)/nrm,
            negm*drw/(2*np.pi)/nrm, psign(parity)*2*pv*pv/nrm)


def run():
    params = {"deps": DEPSC, "nbase": NBASE}
    st = ckpt_key.load("oneprime_cert", KEYFILE, params)
    if st is not None:
        return st
    st = {}

    # ------------------------------------- S1 the representation gate
    r6 = np.linspace(-600.0, 600.0, 120001)
    dr6 = r6[1] - r6[0]
    cosr = np.cos(r6*math.log(2.0))
    s1 = {}
    for parity in ("even", "odd"):
        for delta in (0.7, 0.9, 1.05):
            a = delta/2
            F = fhat_matrix64(a, r6, parity)
            Pdiag = -(C2/(2*np.pi))*(F*cosr[None, :]) @ F.T * dr6
            _, _, Ac, _, PR = build_Q64(delta, parity=parity)
            # at delta = 0.7, log 2 sits 0.0069 from the support
            # edge: ||PRIME|| is itself near zero (a ~39-point
            # overlap window on the t-grid), so PRIME-relative
            # deviation is an artifact of the tiny denominator; the
            # gated quantity is deviation on the FORM's scale
            # (ARCH-relative), with the PRIME-relative figure
            # printed alongside
            dP = float(np.linalg.norm(Pdiag - PR)/np.linalg.norm(PR))
            dA = float(np.linalg.norm(Pdiag - PR)/np.linalg.norm(Ac))
            s1[f"{parity}:{delta:g}"] = {"rel_prime": dP,
                                         "rel_arch": dA}
            print(f"S1 {parity} delta {delta:g}: dev rel PRIME "
                  f"{dP:.2e}, rel ARCH {dA:.2e}", flush=True)
    assert max(x["rel_arch"] for x in s1.values()) < 1e-5, "S1 FAIL"
    st["S1"] = s1

    # ------------------------------------------- S2 the kernel chart
    rf = np.arange(0.0, 60.0, 1e-3)
    Wf = Wker(rf)
    sgn = np.sign(Wf)
    cross = rf[1:][sgn[1:] != sgn[:-1]]
    neg = Wf < 0
    dips = []
    i = 0
    while i < len(rf):
        if neg[i]:
            j = i
            while j < len(rf) and neg[j]:
                j += 1
            seg = Wf[i:j]
            dips.append({"lo": float(rf[i]), "hi": float(rf[j-1]),
                         "depth": float(seg.min()),
                         "argmin": float(rf[i + int(seg.argmin())])})
            i = j
        else:
            i += 1
    tsq = 4*math.pi/math.log(2.0)
    wsq = float(Wker(np.array([tsq]))[0])
    rchk = np.arange(cross[-1] + 1e-3, 200.0, 1e-3)
    floor_chk = float(Wker(rchk).min())
    print(f"S2 kernel chart: crossings {[f'{c:.4f}' for c in cross]}",
          flush=True)
    for d in dips:
        print(f"S2 dip [{d['lo']:.4f}, {d['hi']:.4f}] depth "
              f"{d['depth']:.4f} at {d['argmin']:.4f}", flush=True)
    print(f"S2 squeak at 4pi/log2 = {tsq:.4f}: W = {wsq:.6f}; min W "
          f"on (last crossing, 200] = {floor_chk:.6f}", flush=True)
    assert floor_chk > 0, "S2 FAIL: negative kernel past last crossing"
    st["S2"] = {"crossings": [float(c) for c in cross], "dips": dips,
                "squeak_t": tsq, "squeak_W": wsq,
                "floor_min_to_200": floor_chk}

    # -------------------------- S3 the feasibility survey
    rw = np.linspace(-1500.0, 1500.0, 300001)
    drw = rw[1] - rw[0]
    Ww = Wker(rw)
    s3 = {}
    for delta in (0.6931, 0.75, 0.8, 0.9, 1.0, 1.05, 1.09):
        a = delta/2
        for parity in ("even", "odd"):
            # certified cos-basis section: lambda_1, lambda_2
            Q, G, _, _, _ = build_Q64(delta, parity=parity)
            evc = scipy_eigh(Q, G, eigvals_only=True)
            l1c, l2c = float(evc[0]), float(evc[1])

            # smooth trial section (frequency route, Rmax 600)
            tg, dt, B = smooth_basis(a, parity)
            qs = qhat_rows(B, tg, dt, r6, parity)
            W6 = Wker(r6)
            M = (qs*W6[None, :]) @ qs.T * dr6/(2*np.pi)
            cv = chi_vec(B, tg, dt, parity)
            M = M + psign(parity)*2*np.outer(cv, cv)
            M = (M + M.T)/2
            evs, Vs = scipy_eigh(M)
            l1s = float(evs[0])
            phi = Vs[:, 0] @ B            # extremal on the t-grid

            # the residual on the wide grid (one-pass helper)
            rho, sig, posm, negm, pol = residual(phi, tg, dt, parity,
                                                 rw, Ww)
            # Kato-Temple feasibility with ell_2 = cos-24 lambda_2
            lT = (rho - sig*sig/(l2c - rho)
                  if l2c > rho else float("-inf"))
            sneed = math.sqrt(max(rho*(l2c - rho), 0.0))

            s3[f"{parity}:{delta:g}"] = {
                "l1_cos24": l1c, "l2_cos24": l2c, "l1_smooth16": l1s,
                "rho": rho, "sigma": sig, "sigma_needed": sneed,
                "temple_feas": lT, "pos_mass": posm,
                "neg_mass": negm, "pole": pol}
            print(f"S3 {parity} delta {delta:g}: l1(cos24) {l1c:+.3e} "
                  f"l2(cos24) {l2c:+.3e} | l1(smooth16) {l1s:+.3e} "
                  f"rho {rho:+.3e} sigma {sig:.3e} (needed "
                  f"{sneed:.3e}) -> Temple-feas {lT:+.3e} | budget "
                  f"pos {posm:+.3e} neg {negm:+.3e} pole {pol:+.3e}",
                  flush=True)

    st["S3"] = s3

    # -------- S4 trial-convergence scan: does sigma shrink under
    # richer/smoother trials, or stagnate (which would indicate
    # edge-singular true eigenfunctions needing adapted bases)?
    s4 = {}
    for delta, parity in ((0.6931, "even"), (0.9, "even"),
                          (1.09, "odd")):
        a = delta/2
        Q, G, _, _, _ = build_Q64(delta, parity=parity)
        evc = scipy_eigh(Q, G, eigvals_only=True)
        l2c = float(evc[1])
        for (p, nsm) in ((2, 16), (4, 16), (4, 32), (6, 32)):
            tg, dt, B = smooth_basis(a, parity, nsm=nsm, p=p)
            qs = qhat_rows(B, tg, dt, r6, parity)
            W6 = Wker(r6)
            M = (qs*W6[None, :]) @ qs.T * dr6/(2*np.pi)
            cv = chi_vec(B, tg, dt, parity)
            M = M + psign(parity)*2*np.outer(cv, cv)
            M = (M + M.T)/2
            evs, Vs = scipy_eigh(M)
            phi = Vs[:, 0] @ B
            rho, sig, _, _, _ = residual(phi, tg, dt, parity, rw, Ww)
            lT = (rho - sig*sig/(l2c - rho)
                  if l2c > rho else float("-inf"))
            sneed = math.sqrt(max(rho*(l2c - rho), 0.0))
            s4[f"{parity}:{delta:g}:p{p}:n{nsm}"] = {
                "rho": rho, "sigma": sig, "sigma_needed": sneed,
                "temple_feas": lT}
            print(f"S4 {parity} delta {delta:g} p={p} nsm={nsm}: rho "
                  f"{rho:+.3e} sigma {sig:.3e} (needed {sneed:.3e}) "
                  f"-> Temple-feas {lT:+.3e}", flush=True)
    st["S4"] = s4

    # -------- S5 the edge-behavior chase: S4 found sigma SHRINKS as
    # the window roughens (p = 2 beat p = 4 beat p = 6, first
    # closure at delta = log 2) -- the true eigenfunction has weak
    # edge vanishing. So: (a) the certified cos-24 extremal itself
    # as trial (linear edge vanishing AND the best rho), (b) p = 1
    # and richer p = 2 smooth trials.
    s5 = {}
    for delta, parity in ((0.6931, "even"), (0.75, "even"),
                          (0.8, "even"), (0.9, "even"),
                          (1.09, "odd")):
        a = delta/2
        Q, G, _, _, _ = build_Q64(delta, parity=parity)
        evc, Vc = scipy_eigh(Q, G)
        l2c = float(evc[1])
        trials = {}
        tgc, dtc = tgrid(a)
        trials["cos24"] = Vc[:, 0] @ basis_eval(a, parity, tgc)
        for (p, nsm) in ((1, 32), (2, 32), (2, 48)):
            tg, dt, B = smooth_basis(a, parity, nsm=nsm, p=p)
            qs = qhat_rows(B, tg, dt, r6, parity)
            W6 = Wker(r6)
            M = (qs*W6[None, :]) @ qs.T * dr6/(2*np.pi)
            cv = chi_vec(B, tg, dt, parity)
            M = M + psign(parity)*2*np.outer(cv, cv)
            M = (M + M.T)/2
            _, Vs = scipy_eigh(M)
            trials[f"p{p}n{nsm}"] = Vs[:, 0] @ B
        for name, phi in trials.items():
            rho, sig, _, _, _ = residual(phi, tgc, dtc, parity,
                                         rw, Ww)
            lT = (rho - sig*sig/(l2c - rho)
                  if l2c > rho else float("-inf"))
            sneed = math.sqrt(max(rho*(l2c - rho), 0.0))
            s5[f"{parity}:{delta:g}:{name}"] = {
                "rho": rho, "sigma": sig, "sigma_needed": sneed,
                "temple_feas": lT}
            print(f"S5 {parity} delta {delta:g} {name}: rho "
                  f"{rho:+.3e} sigma {sig:.3e} (needed {sneed:.3e}) "
                  f"-> Temple-feas {lT:+.3e}", flush=True)
    st["S5"] = s5

    ckpt_key.save("oneprime_cert", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    run()
    print("one-prime certificate survey (Stage B1 opening) complete",
          flush=True)
