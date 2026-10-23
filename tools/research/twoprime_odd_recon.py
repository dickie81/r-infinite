#!/usr/bin/env python3
"""THE TWO-PRIME WINDOW, STAGE 1/2 RECONNAISSANCE for the odd
delta = 1.10 cell (a = 0.55): the float64 choice of the count row
(nu, beta) and the entire-trial Temple feasibility, before the
interval instruments are built (A418 (iv): a certificate here
states lambda_1(log 3) >= Temple > 0 in the odd sector by
nesting).

(1) THE COUNT ROW. The certified count instrument's construction
in float64 with the two-prime kernel W_23: on the support
{W_23 < nu + beta} of [0, rmax] a Simpson frame r_i, weights
c_i = (2/pi) w_i qt(r_i), qt = (nu + beta - W_23)_+, and the
odd-projected Gram G_ij = [sin((r_i - r_j)a)/(r_i - r_j) -
sin((r_i + r_j)a)/(r_i + r_j)]/2; A = C^{1/2} G C^{1/2}; the row
certifies #{PWP_odd < nu} <= 1 when mu_2(A) + EOP < beta. Scanned
over nu in [0.02, 0.15] and beta in {1.0, 1.2, 1.3, 1.5}; the
tail lemma of the certified instrument needs h_+(rmax) - C_2 -
C_3 > nu + beta, which at rmax = 260 caps nu + beta below ~1.47
(h_+(260) = 3.72): rmax = 600 (h_+ = 4.56, cap ~2.3) is recorded
for the interval instrument.
(2) THE TRIAL. The interval Temple instrument evaluates ENTIRE
trials only (harmonics + polynomials); Stage 0's union span
carried fractional-edge modes (weight 0.60). Here: the pure
harmonic odd basis (24 integer + 24 half-integer sines) at base
0.003 via the two-prime t-space operator, the two-stage odd
route in float -- pole-free Temple at ell2 = nu* -> nu1, then the
full form at ell2 = nu1 -- and, if the harmonics fall short, the
nu = 3/2 Gegenbauer polynomial modes (odd n) added.

CHECKS 7/8 clean. Float64 reconnaissance; not a certificate.
Keying law: every producing file in every key.
"""
import math, os, sys, time

import numpy as np
from scipy.linalg import eigh as scipy_eigh
from scipy.special import digamma

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
import oneprime_fractional as opf
import twoprime_recon as TR
from oneprime_push import temple_opt


def _sha(name):
    return ckpt_key.code_sha(os.path.join(HERE, name))


DEPSR = {f: _sha(f) for f in ("twoprime_recon.py", "oneprime_fractional.py",
                              "oneprime_push.py")}
KEYFILE = os.path.join(HERE, "twoprime_odd_recon.py")

A = 0.55
LOG2, LOG3 = math.log(2.0), math.log(3.0)
C2, C3 = TR.Cp(2), TR.Cp(3)
HSIMP = 0.02


def W23(r):
    return TR.W_kernel(r, (2, 3))


def hplus(r):
    return digamma(0.25 + 0.5j*r).real - math.log(math.pi)


def support_nodes(nu, beta, rmax):
    rs = np.arange(0.0, rmax, 0.002)
    pos = W23(rs) < nu + beta
    assert not pos[-1], "support reaches rmax"
    idx = np.flatnonzero(np.diff(pos.astype(int)))
    edges = rs[idx + 1]
    if pos[0]:
        edges = np.concatenate([[0.0], edges])
    pieces = edges.reshape(-1, 2)
    nodes, wts = [], []
    for lo, hi in pieces:
        if hi - lo < 2*HSIMP:
            continue
        n = int(math.ceil((hi - lo)/HSIMP)); n += n % 2
        x = np.linspace(lo, hi, n + 1); h = (hi - lo)/n
        w = np.full(n + 1, 2.0); w[1::2] = 4.0; w[0] = w[-1] = 1.0
        nodes.append(x); wts.append(w*(h/3.0))
    return np.concatenate(nodes), np.concatenate(wts), pieces


def count_mu(a, nu, beta, rmax=600.0):
    rs, wq, pieces = support_nodes(nu, beta, rmax)
    qt = np.clip(nu + beta - W23(rs), 0.0, None)
    c = (2.0/math.pi)*wq*qt
    keep = c > 0
    rs, c = rs[keep], c[keep]
    d = rs[:, None] - rs[None, :]; s = rs[:, None] + rs[None, :]
    with np.errstate(divide="ignore", invalid="ignore"):
        sd = np.where(np.abs(d) < 1e-12, a, np.sin(d*a)/d)
        ss = np.where(np.abs(s) < 1e-12, a, np.sin(s*a)/s)
    G = 0.5*(sd - ss)          # odd projection
    sq = np.sqrt(c)
    Am = sq[:, None]*G*sq[None, :]
    ev = np.linalg.eigvalsh((Am + Am.T)/2)[::-1]
    return float(ev[0]), float(ev[1]), len(rs), float(sum(h - l for l, h in pieces))


def fixture(a, parity, nus=(), nfr=0, base=0.003):
    md = opf.Modes(a, parity, nus=nus, nfr=nfr, nrough=0)
    tn, tw, B, TB, v = TR.apply_T(md, (2, 3), base=base)
    N = 2*(B*tw[None, :]) @ B.T
    M = 2*(B*tw[None, :]) @ TB.T
    S = 2*(TB*tw[None, :]) @ TB.T
    N, M, S = (N + N.T)/2, (M + M.T)/2, (S + S.T)/2
    d = 1.0/np.sqrt(np.diag(N))
    ev, U = np.linalg.eigh(d[:, None]*N*d[None, :])
    keep = ev > 1e-4
    Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T*d[None, :])
    chi = np.sinh(tn/2)
    Bw, TBw = Wh @ B, Wh @ TB
    NA = 2*(Bw*tw[None, :]) @ Bw.T
    MA = 2*(Bw*tw[None, :]) @ TBw.T
    SA = 2*(TBw*tw[None, :]) @ TBw.T
    vfull = 2*(Bw*(tw*chi)[None, :]).sum(1)
    TBfree = TBw - opf.psign(parity)*2*np.outer(vfull, chi)
    MF = 2*(Bw*tw[None, :]) @ TBfree.T
    SF = 2*(TBfree*tw[None, :]) @ TBfree.T
    sym = lambda X: (X + X.T)/2
    return md, sym(NA), sym(MA), sym(SA), sym(MF), sym(SF)


def fixture_nh(a, parity, nh, base=0.003):
    """fixture() with the harmonic count nh set on the LOCAL Modes
    object (w, nharm, n) -- never by storing on the imported module
    (the tower precheck's clause G)."""
    md = opf.Modes(a, parity, nus=(), nfr=0, nrough=0)
    if parity == "even":
        w = list((np.arange(nh) + 0.5)*np.pi/a)
    else:
        w = sorted(list((np.arange(nh) + 1.0)*np.pi/a)
                   + list((np.arange(nh) + 0.5)*np.pi/a))
    md.w = np.array(w); md.nharm = len(md.w); md.n = md.nharm + len(md.frac)
    tn, tw, B, TB, v = TR.apply_T(md, (2, 3), base=base)
    N = 2*(B*tw[None, :]) @ B.T
    M = 2*(B*tw[None, :]) @ TB.T
    S = 2*(TB*tw[None, :]) @ TB.T
    N, M, S = (N + N.T)/2, (M + M.T)/2, (S + S.T)/2
    d = 1.0/np.sqrt(np.diag(N))
    ev, U = np.linalg.eigh(d[:, None]*N*d[None, :])
    keep = ev > 1e-4
    Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T*d[None, :])
    Bw, TBw = Wh @ B, Wh @ TB
    NA = 2*(Bw*tw[None, :]) @ Bw.T
    MA = 2*(Bw*tw[None, :]) @ TBw.T
    SA = 2*(TBw*tw[None, :]) @ TBw.T
    sym = lambda X: (X + X.T)/2
    return md, sym(NA), sym(MA), sym(SA)


def two_stage(NA, MA, SA, MF, SF, nustar):
    """Float two-stage odd route: pole-free Temple at ell2 = nustar
    -> nu1; full Temple at ell2 = nu1 (the fixture builder's 0.9
    safety on nu1 mirrored)."""
    lF = scipy_eigh(MF, NA, eigvals_only=True)
    muF, cF = temple_opt(NA, MF, SF, nustar)
    if cF is None:
        return {"stage1": None}
    nnF = float(cF @ NA @ cF); rhoF = float(cF @ MF @ cF)/nnF
    sigF = math.sqrt(max(float(cF @ SF @ cF)/nnF - rhoF**2, 0.0))
    nu1 = (rhoF - sigF*sigF/(nustar - rhoF))*0.9
    lT = scipy_eigh(MA, NA, eigvals_only=True)
    out = {"stage1": {"temple": muF, "rhoF": rhoF, "sigF": sigF, "nu1": nu1,
                      "l1F": float(lF[0]), "l2F": float(lF[1])},
           "l1T": float(lT[0]), "l2T": float(lT[1])}
    if nu1 <= 0:
        return out
    mu, c = temple_opt(NA, MA, SA, nu1)
    if c is None:
        out["stage2"] = None
        return out
    nn = float(c @ NA @ c); rho = float(c @ MA @ c)/nn
    sig = math.sqrt(max(float(c @ SA @ c)/nn - rho**2, 0.0))
    out["stage2"] = {"temple": mu, "rho": rho, "sigma": sig, "ell2": nu1,
                     "needed_sigma": math.sqrt(max(rho*(nu1 - rho), 0.0))}
    return out


def run():
    params = {"deps": DEPSR, "a": A, "hsimp": HSIMP}
    st = ckpt_key.load("twoprime_odd_recon", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is not None:
        return st
    st = {}
    print(f"tail lemma: h+(260) - C2 - C3 = {hplus(260.0) - C2 - C3:.3f}; "
          f"h+(600) - C2 - C3 = {hplus(600.0) - C2 - C3:.3f}", flush=True)
    # (1) the count scan
    t0 = time.time()
    scan = {}
    for beta in (1.0, 1.2, 1.3, 1.5):
        best = None
        for nu in [round(x, 3) for x in np.arange(0.02, 0.151, 0.01)]:
            m1, m2, m, L = count_mu(A, nu, beta)
            scan[f"{nu:g}:{beta:g}"] = {"mu1": m1, "mu2": m2, "margin": beta - m2,
                                        "m": m, "support_len": L}
            if m2 < beta:
                best = (nu, beta - m2)
        print(f"COUNT beta {beta:g}: odd-projected count <= 1 up to nu = "
              f"{best[0] if best else None} (margin {best[1] if best else float('nan'):.3e}); "
              f"m {m} support {L:.1f} [{time.time() - t0:.0f}s]", flush=True)
        st[f"best:{beta:g}"] = best
    st["scan"] = scan
    # (2) the entire-trial Temple, pure harmonics
    for tag, kw in (("harm", dict(nus=(), nfr=0)),
                    ("harm+poly", dict(nus=(1.5,), nfr=5))):
        md, NA, MA, SA, MF, SF = fixture(A, "odd", **kw)
        for beta in (1.2, 1.5):
            b = st[f"best:{beta:g}"]
            if b is None:
                continue
            r = two_stage(NA, MA, SA, MF, SF, b[0])
            st[f"temple:{tag}:{beta:g}"] = r
            s1, s2 = r.get("stage1"), r.get("stage2")
            print(f"TEMPLE {tag} (dim {NA.shape[0]}) nu* {b[0]:g} (beta {beta:g}): "
                  f"section l1 {r.get('l1T', float('nan')):+.3e} l2 {r.get('l2T', float('nan')):+.3e}; "
                  f"stage1 nu1 {s1['nu1'] if s1 else float('nan'):+.4e} "
                  f"(rhoF {s1['rhoF'] if s1 else float('nan'):+.4e} sigF {s1['sigF'] if s1 else float('nan'):.2e}); "
                  f"stage2 Temple {s2['temple'] if s2 else float('nan'):+.3e} "
                  f"(rho {s2['rho'] if s2 else float('nan'):+.3e} sigma {s2['sigma'] if s2 else float('nan'):.2e} "
                  f"needed {s2['needed_sigma'] if s2 else float('nan'):.2e}) [{time.time() - t0:.0f}s]",
                  flush=True)
    ckpt_key.save("twoprime_odd_recon", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    return st


if __name__ == "__main__" and not any(os.environ.get(k) == "1" for k in ("TP_POLE", "TP_LEVER", "TP_LEVER2")):
    run()
    print("two-prime odd-1.10 reconnaissance complete", flush=True)


# ---- the POLE-INCLUSIVE odd count (the odd analogue of Stage II-b)
def pole_col(a, rs):
    """<f_i, g>_full for the frame f_i = sqrt(c_i/2) sin(r_i t) and
    the pole vector g = sqrt 2 sinh(t/2), full inner product
    2 int_0^a: = sqrt(c_i) * 2 int_0^a sin(r t) sinh(t/2) dt, with
    int_0^a sin(rt) e^{kt} dt = (e^{ka}(k sin(ra) - r cos(ra)) + r)
    / (k^2 + r^2)."""
    def J(k):
        return (np.exp(k*a)*(k*np.sin(rs*a) - rs*np.cos(rs*a)) + rs)/(k*k + rs*rs)
    return 2.0*0.5*(J(0.5) - J(-0.5))


def count_mu_pole(a, nu, beta, rmax=600.0):
    rs, wq, pieces = support_nodes(nu, beta, rmax)
    qt = np.clip(nu + beta - W23(rs), 0.0, None)
    c = (2.0/math.pi)*wq*qt
    keep = c > 0
    rs, c = rs[keep], c[keep]
    d = rs[:, None] - rs[None, :]; s = rs[:, None] + rs[None, :]
    with np.errstate(divide="ignore", invalid="ignore"):
        sd = np.where(np.abs(d) < 1e-12, a, np.sin(d*a)/d)
        ss = np.where(np.abs(s) < 1e-12, a, np.sin(s*a)/s)
    G = 0.5*(sd - ss)
    sq = np.sqrt(c)
    Am = sq[:, None]*G*sq[None, :]
    b = sq*pole_col(a, rs)
    gg = 2.0*(math.sinh(a) - a)          # <g,g>_full = 4 int_0^a sinh^2(t/2)
    Ab = np.zeros((len(rs) + 1, len(rs) + 1))
    Ab[:-1, :-1] = (Am + Am.T)/2; Ab[:-1, -1] = b; Ab[-1, :-1] = b; Ab[-1, -1] = gg
    ev = np.linalg.eigvalsh(Ab)[::-1]
    evf = np.linalg.eigvalsh((Am + Am.T)/2)[::-1]
    return float(ev[0]), float(ev[1]), float(evf[1]), gg


def pole_scan():
    print(f"pole strength <g,g> = {2.0*(math.sinh(A) - A):.4f}", flush=True)
    st = ckpt_key.load("twoprime_odd_recon", KEYFILE,
                       {"deps": DEPSR, "a": A, "hsimp": HSIMP}, kfun=ckpt_key.code_key)
    for beta in (1.0, 1.2, 1.3, 1.5):
        best = None
        for nu in [round(x, 3) for x in np.arange(0.02, 0.121, 0.01)]:
            m1, m2, m2free, gg = count_mu_pole(A, nu, beta)
            flag = "<=1" if m2 < beta else "2+"
            if m2 < beta: best = (nu, beta - m2)
            print(f"  POLE-COUNT nu {nu:g} beta {beta:g}: mu2(bordered) {m2:.5f} "
                  f"(pole-free {m2free:.5f}) margin {beta - m2:+.3e} {flag}", flush=True)
        print(f"POLE-COUNT beta {beta:g}: odd pole-inclusive count <= 1 up to nu = "
              f"{best[0] if best else None} (margin {best[1] if best else float('nan'):.3e})", flush=True)
    # single-stage Temple on the harmonic trial at candidate ell2
    md, NA, MA, SA, MF, SF = fixture(A, "odd")
    for ell2 in (0.03, 0.04, 0.05, 0.06, 0.07):
        mu, c = temple_opt(NA, MA, SA, ell2)
        nn = float(c @ NA @ c); rho = float(c @ MA @ c)/nn
        sig = math.sqrt(max(float(c @ SA @ c)/nn - rho**2, 0.0))
        print(f"TEMPLE harm single-stage ell2 {ell2:g}: {mu:+.3e} (rho {rho:+.3e} "
              f"sigma {sig:.2e} needed {math.sqrt(max(rho*(ell2 - rho), 0)):.2e})", flush=True)


if __name__ == "__main__" and os.environ.get("TP_POLE") == "1":
    pole_scan()


def lever_scan():
    print(f"tail lemma at rmax 1500: h+(1500) - C2 - C3 = {hplus(1500.0) - C2 - C3:.3f}", flush=True)
    for beta in (2.0, 2.5, 3.0):
        for nu in (0.03, 0.035, 0.04, 0.045, 0.05):
            m1, m2, m2free, gg = count_mu_pole(A, nu, beta, rmax=1500.0)
            print(f"  POLE-COUNT nu {nu:g} beta {beta:g} rmax 1500: mu2(bordered) {m2:.5f} "
                  f"(pole-free {m2free:.5f}) margin {beta - m2:+.3e} {'<=1' if m2 < beta else '2+'}", flush=True)
    for nh in (24, 32, 40, 48):
        md, NA, MA, SA = fixture_nh(A, "odd", nh)
        for ell2 in (0.03, 0.035, 0.04):
            mu, c = temple_opt(NA, MA, SA, ell2)
            nn = float(c @ NA @ c); rho = float(c @ MA @ c)/nn
            sig = math.sqrt(max(float(c @ SA @ c)/nn - rho**2, 0.0))
            print(f"TEMPLE harm NHALF {nh} (dim {NA.shape[0]}) ell2 {ell2:g}: {mu:+.3e} (rho {rho:+.3e} "
                  f"sigma {sig:.2e} needed {math.sqrt(max(rho*(ell2 - rho), 0)):.2e})", flush=True)


if __name__ == "__main__" and os.environ.get("TP_LEVER") == "1":
    lever_scan()


def lever_scan2():
    for beta, rmax in ((2.0, 600.0), (2.5, 1000.0)):
        for nu in (0.035, 0.04, 0.045):
            m1, m2, m2free, gg = count_mu_pole(A, nu, beta, rmax=rmax)
            print(f"  POLE-COUNT nu {nu:g} beta {beta:g} rmax {rmax:g}: mu2(bordered) {m2:.5f} "
                  f"(pole-free {m2free:.5f}) margin {beta - m2:+.3e} {'<=1' if m2 < beta else '2+'}", flush=True)
    for nh in (24, 32, 40):
        md, NA, MA, SA = fixture_nh(A, "odd", nh)
        for ell2 in (0.035, 0.04):
            mu, c = temple_opt(NA, MA, SA, ell2)
            nn = float(c @ NA @ c); rho = float(c @ MA @ c)/nn
            sig = math.sqrt(max(float(c @ SA @ c)/nn - rho**2, 0.0))
            print(f"TEMPLE harm NHALF {nh} (dim {NA.shape[0]}) ell2 {ell2:g}: {mu:+.3e} (rho {rho:+.3e} "
                  f"sigma {sig:.2e} needed {math.sqrt(max(rho*(ell2 - rho), 0)):.2e})", flush=True)


if __name__ == "__main__" and os.environ.get("TP_LEVER2") == "1":
    lever_scan2()
