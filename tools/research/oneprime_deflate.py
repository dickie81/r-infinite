#!/usr/bin/env python3
"""THE ONE-PRIME ARC, STAGE B1, ROUND 7 -- the deflation
reconnaissance: pole-inclusive Birman-Schwinger counting at the
even-1.0 frontier (float64 measurement; no certificate claimed).

Commission: "Attack the deflation route pls" (the owner's choice
at the round-259 convergence: the even-1.0 closure).

THE GAP THIS ATTACKS. The certified even ell_2 chain runs
    #{PWP_even < nu} <= 1  =>  lambda_2(PWP_even) >= nu
    =>  lambda_2(T_even) >= nu     (pole +2 chi chi* PSD rank-one,
                                    Weyl/interlacing)
and at delta = 1.0 the pole-free count flips to 2 at nu ~ 0.013
(A375) while the Temple side needs ell_2 ~ 0.018 (A374's needed
sigma = 1.300e-4 back-derives ell_2 = section lambda_2 ~ 0.018).
The interlacing step DISCARDS the pole's lift of the second mode:
lambda_2(T_even) can sit above lambda_2(PWP_even), up at the
section value. This file measures whether counting T_even
DIRECTLY -- the pole kept inside the counting operator -- moves
the certifiable nu* from 0.013 to the ~0.017-0.018 the Temple
side needs.

THE POLE-INCLUSIVE REDUCTION (the round-243 chain, one term
richer; conventions carried through Plancherel, then VALIDATED
against the recorded rows -- gD1 -- and the t-space section
spectra -- gD3/gD4).  For even f on [-a, a] with
<f, T_even f> < nu <f, f>, T_even = W_op + 2 chi (x) chi,
chi = cosh(t/2), inner products on [-a, a]:
with g = f|_[0,a], fhat(r) = 2<g, phi_r>, phi_r(x) = cos(r x),
<g, .> the HALF-LINE inner product,
    <f, W_op f> = (4/pi) int_0^oo W(r) <g, phi_r>^2 dr,
    <f, f> = 2||g||^2,          <chi, f> = 2 <chi, g>,
so qt(r) = (nu + beta - W(r))_+ >= nu + beta - W(r) gives
    (4/pi) int qt <g, phi_r>^2 dr
        >= (nu + beta) 2||g||^2 - <f, W_op f>
        >  2 beta ||g||^2 + 2 <chi, f>^2 / 2 ... assembled:
    <g, (T_count - 4 chi (x) chi) g> > beta ||g||^2,
    T_count = (2/pi) int_0^oo qt(r) phi_r (x) phi_r dr.
Hence  #{T_even < nu} <= #{eig(T_count - 4 chi chi*) >= beta},
and the certificate shape for the interval instrument is
    mu_2(T_count - 4 chi chi*) + EOP < beta
        =>  lambda_2(T_even) >= nu,
whose finite-frame form is an INERTIA test on the bordered
signed Gram (n_+(G S G - (beta - EOP) G) <= 1, S =
diag(1,...,1,-1), border vector 2 chi) -- Stage II's existing
verified-eigensolve machinery on one more symmetric matrix.
This file measures the float64 flip curves only.

METHOD (this file, all float64).
  (1) COUNTING SPECTRA in a truncated orthogonal cosine basis
      e_k(x) = cos(k pi x / a) on [0, a] (exact Gram: diag(a,
      a/2, a/2, ...)): T_count's matrix is
      (2/pi) P diag(w_i qt(r_i)) P^T with P_{k,i} = <e_k,
      phi_{r_i}> in closed form and Simpson weights w_i on the
      qt > 0 support; the pole column <e_k, chi> in closed form.
      Basis compression only LOWERS mu_2 (Cauchy), so the flip
      nu* it reports is biased UP: the convergence pair
      (KBASIS, KBASIS2) must agree (gD2) before any number is
      read.  mu_2 flip scans in nu at beta in {1.5, 2.0, 2.5},
      pole-free and pole-inclusive.
  (2) SECTION SPECTRA from the committed t-space pipeline
      (oneprime_fractional.cell_matrices, the A374 top
      configuration): lambda_{1,2,3} of the whitened section of
      T_even and of the pole-projected M - 2 v v^T (v = <chi,
      b_i> in the pipeline's own doubled convention) -- the
      recorded story to reproduce: l1_polefree in [-2.0, -1.3]
      (A374), lambda_2(polefree) ~ 0.013 (A375's flip),
      lambda_2(T_even section) ~ 0.018 (A374's needed sigma).
  (3) TEMPLE FEASIBILITY at ell_2 = nu*_pole: temple_opt on the
      A374 top span AND on the ENTIRE span (nus = (1.5,) --
      s = 1 edge factors are polynomials; Stage III's interval
      machinery certifies entire trials only), margins tabled
      against the candidate ell_2 ladder.

GATES (each an assert; a failure means the conventions are
wrong and every downstream number is void):
  gD1  builder validation against the certified rows' recorded
       float story: pole-free beta - mu_2 at even:0.95
       (nu 0.02, beta 1.5) in [1e-3, 2e-2] (recorded float
       clearance >= 3.5e-3, certified margin 3.641e-3); at
       even:1.0 (nu 0.01, beta 2.0) in [5e-5, 2e-3] (the
       recorded 2.5e-4 knife-edge, certified 2.058e-4).
  gD2  basis convergence: |mu_2(K) - mu_2(K2)| < 1e-4 at every
       scanned point read into a verdict.
  gD3  section reproduction: l1_polefree in [-2.2, -1.1];
       lambda_2(polefree) in [0.010, 0.016]; lambda_2(T_even)
       in [0.015, 0.022].
  gD4  count-vs-section consistency: nu*_pole (the pole-
       inclusive flip) <= lambda_2(T_even section) + 1e-3 (the
       count lower-bounds what the Ritz section upper-bounds).
  gD5  the pipeline's own gF1/gF4 at every cell_matrices call.

CHECKS. 7: classical only (Birman-Schwinger counting, Cauchy
interlacing, Weyl, Plancherel, Simpson). 8: no hypothesis input
anywhere -- the target nu* is set by the recorded Temple
needed-sigma, a property of the form itself.

Keying law: every producing file in every key (executable
content, round 245); the closure COMPUTED, never hand-listed
(the F250-1 lesson).
"""
import math, os, sys

import numpy as np
from scipy.linalg import eigh as scipy_eigh
from scipy.special import digamma

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
import oneprime_fractional as opf
from oneprime_push import temple_opt

KEYFILE = os.path.join(HERE, "oneprime_deflate.py")
DEPSD = {f: ckpt_key.code_sha(os.path.join(HERE, f))
         for f in sorted(ckpt_key.producer_closure(
             {"oneprime_deflate.py"}, HERE))}

LOG2 = math.log(2.0)
SQ2L2 = math.sqrt(2.0)*LOG2
LOGPI = math.log(math.pi)

KBASIS = 320
KBASIS2 = 480
HSIMP = 0.02
RMAX = 700.0
BETAS = (1.5, 2.0, 2.5, 3.0)


def W(r):
    """W(r) = Re psi(1/4 + i r/2) - log pi - sqrt2 log2 cos(r log2)
    (float64; the certified Stage-I enclosure is the rigorous
    counterpart)."""
    r = np.asarray(r, dtype=float)
    return (digamma(0.25 + 0.5j*r).real - LOGPI
            - SQ2L2*np.cos(r*LOG2))


def support_nodes(nu, beta):
    """Simpson nodes/weights on the qt > 0 support pieces of
    [0, RMAX] (float recon: pieces located on a 0.005 scan, each
    bridged to a Simpson grid at pitch <= HSIMP; the certified
    instrument brackets the crossings rigorously instead)."""
    rs = np.arange(0.0, RMAX, 0.005)
    pos = W(rs) < nu + beta
    assert not pos[-1], "support reaches RMAX -- enlarge"
    # contiguous positive runs -> [lo, hi] pieces
    idx = np.flatnonzero(np.diff(pos.astype(int)))
    edges = rs[idx + 1]
    if pos[0]:
        edges = np.concatenate([[0.0], edges])
    pieces = edges.reshape(-1, 2)
    nodes, wts = [], []
    for lo, hi in pieces:
        if hi - lo < 2*HSIMP:
            continue
        n = int(math.ceil((hi - lo)/HSIMP))
        n += n % 2          # Simpson: even panel count
        x = np.linspace(lo, hi, n + 1)
        h = (hi - lo)/n
        w = np.full(n + 1, 2.0)
        w[1::2] = 4.0
        w[0] = w[-1] = 1.0
        nodes.append(x)
        wts.append(w*(h/3.0))
    return np.concatenate(nodes), np.concatenate(wts)


def _p_matrix(a, ks, rs):
    """P_{k,i} = <cos(k pi x/a), cos(r_i x)>_[0,a], closed form:
    [sin((w-r)a)/(w-r) + sin((w+r)a)/(w+r)]/2, w = k pi/a (the
    same identity as Stage II's frame Gram)."""
    w = ks[:, None]*math.pi/a
    r = rs[None, :]
    def sc(x):
        return np.where(np.abs(x) < 1e-12, a,
                        np.sin(np.where(np.abs(x) < 1e-12, 1.0, x)
                               * a)
                        / np.where(np.abs(x) < 1e-12, 1.0, x))
    return 0.5*(sc(w - r) + sc(w + r))


def _chi_col(a, ks):
    """<cos(k pi x/a), cosh(x/2)>_[0,a] closed form."""
    w = ks*math.pi/a
    return ((0.5*np.cos(w*a)*math.sinh(a/2)
             + w*np.sin(w*a)*math.cosh(a/2))/(w*w + 0.25))


def count_mu(a, nu, beta, kb, pole):
    """(mu_1, mu_2) of T_count (- 4 chi chi* if pole) in the
    kb-mode cosine compression."""
    rs, wq = support_nodes(nu, beta)
    qt = np.clip(nu + beta - W(rs), 0.0, None)
    ks = np.arange(kb)
    P = _p_matrix(a, ks, rs)
    T = (2.0/math.pi)*(P*(wq*qt)[None, :]) @ P.T
    if pole:
        c = _chi_col(a, ks)
        T = T - 4.0*np.outer(c, c)
    # orthogonal basis: Gram diag(a, a/2, ..., a/2)
    d = np.full(kb, math.sqrt(2.0/a))
    d[0] = math.sqrt(1.0/a)
    K = d[:, None]*T*d[None, :]
    ev = np.linalg.eigvalsh((K + K.T)/2)
    return float(ev[-1]), float(ev[-2])


def flip_scan(a, beta, pole, nus):
    """max nu in `nus` with mu_2 < beta (count <= 1), with the
    gD2 convergence check at each read point."""
    best = None
    curve = {}
    for nu in nus:
        m1, m2 = count_mu(a, nu, beta, KBASIS, pole)
        m1b, m2b = count_mu(a, nu, beta, KBASIS2, pole)
        assert abs(m2 - m2b) < 1e-4, \
            f"gD2 FAIL nu {nu:g} beta {beta:g}: {m2:.6f} vs {m2b:.6f}"
        curve[f"{nu:g}"] = {"mu1": m1b, "mu2": m2b,
                            "margin": beta - m2b}
        if m2b < beta:
            best = nu
    return best, curve


def run():
    params = {"deps": DEPSD, "kb": (KBASIS, KBASIS2),
              "h": HSIMP, "betas": BETAS}
    st = ckpt_key.load("oneprime_deflate", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is not None:
        return st
    st = {}

    # ---- gD1: builder validation against the certified rows
    _, m2a = count_mu(0.475, 0.02, 1.5, KBASIS2, pole=False)
    gap_a = 1.5 - m2a
    _, m2b = count_mu(0.5, 0.01, 2.0, KBASIS2, pole=False)
    gap_b = 2.0 - m2b
    print(f"gD1: even:0.95 polefree mu2 gap {gap_a:+.4e} "
          f"(recorded float >= 3.5e-3, certified 3.641e-3)",
          flush=True)
    print(f"gD1: even:1.0  polefree mu2 gap {gap_b:+.4e} "
          f"(recorded knife-edge 2.5e-4, certified 2.058e-4)",
          flush=True)
    assert 1e-3 < gap_a < 2e-2, f"gD1 FAIL 0.95: {gap_a:.3e}"
    assert 5e-5 < gap_b < 2e-3, f"gD1 FAIL 1.0: {gap_b:.3e}"
    st["gD1"] = {"gap095": gap_a, "gap100": gap_b}

    # ---- (1) the flip scans at a = 0.5
    nus = [round(x, 4) for x in np.arange(0.008, 0.0261, 0.0005)]
    st["flips"] = {}
    for beta in BETAS:
        nf_free, curve_f = flip_scan(0.5, beta, False, nus)
        nf_pole, curve_p = flip_scan(0.5, beta, True, nus)
        st["flips"][f"{beta:g}"] = {
            "polefree_max_nu": nf_free, "pole_max_nu": nf_pole,
            "polefree": curve_f, "pole": curve_p}
        print(f"FLIP beta {beta:g}: pole-free count<=1 up to nu "
              f"= {nf_free}, POLE-INCLUSIVE up to nu = {nf_pole}",
              flush=True)

    # ---- (2) section spectra from the t-space pipeline
    sect = {}
    for base in (0.008, 0.005):
        md, N, M, S, gf4, grids = opf.cell_matrices(
            0.5, "even", base=base, nus=(0.6, 0.75, 1.0, 1.25),
            nfr=12, nrough=13)
        assert gf4 < 1e-8, f"gD5/gF4 FAIL: {gf4:.1e}"
        tn, tw, B, TB = grids
        chi = np.cosh(tn/2)
        v = 2*(B*(tw*chi)[None, :]).sum(1)
        d = 1.0/np.sqrt(np.diag(N))
        Nn = d[:, None]*N*d[None, :]
        ev, U = np.linalg.eigh(Nn)
        keep = ev > 1e-4
        Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T
              * d[None, :])
        Bw = Wh @ B
        TBw = Wh @ TB
        NA = 2*(Bw*tw[None, :]) @ Bw.T
        MA = 2*(Bw*tw[None, :]) @ TBw.T
        NA, MA = (NA + NA.T)/2, (MA + MA.T)/2
        vw = Wh @ v
        MP = MA - 2.0*np.outer(vw, vw)
        lam = scipy_eigh(MA, NA, eigvals_only=True)
        lamp = scipy_eigh(MP, NA, eigvals_only=True)
        sect[f"{base:g}"] = {
            "l123_T": [float(x) for x in lam[:3]],
            "l123_polefree": [float(x) for x in lamp[:3]]}
        print(f"SECTION base {base:g}: T_even l1..3 "
              f"{lam[0]:+.4e} {lam[1]:+.4e} {lam[2]:+.4e} | "
              f"polefree {lamp[0]:+.4e} {lamp[1]:+.4e} "
              f"{lamp[2]:+.4e}", flush=True)
    st["sections"] = sect
    l2T = sect["0.005"]["l123_T"][1]
    l1pf = sect["0.005"]["l123_polefree"][0]
    l2pf = sect["0.005"]["l123_polefree"][1]
    assert -2.2 < l1pf < -1.1, f"gD3 FAIL l1pf {l1pf:.3e}"
    assert 0.010 < l2pf < 0.016, f"gD3 FAIL l2pf {l2pf:.3e}"
    assert 0.015 < l2T < 0.022, f"gD3 FAIL l2T {l2T:.3e}"
    nustar = st["flips"]["2"]["pole_max_nu"]
    assert nustar is None or nustar <= l2T + 1e-3, \
        f"gD4 FAIL: nu*_pole {nustar} vs section l2 {l2T:.4e}"

    # ---- (3) Temple feasibility at the candidate ell_2 ladder
    ladder = [0.012, 0.013, 0.014, 0.015, 0.016, 0.017, 0.018]
    if nustar is not None and round(nustar, 4) not in ladder:
        ladder.append(round(nustar, 4))
    st["temple"] = {}
    for tag, kw in (("top", dict(nus=(0.6, 0.75, 1.0, 1.25),
                                 nfr=12, nrough=13)),
                    ("entire", dict(nus=(1.5,), nfr=12,
                                    nrough=13))):
        md, N, M, S, gf4, grids = opf.cell_matrices(
            0.5, "even", base=0.005, **kw)
        assert gf4 < 1e-8, f"gD5/gF4 FAIL {tag}: {gf4:.1e}"
        tn, tw, B, TB = grids
        d = 1.0/np.sqrt(np.diag(N))
        Nn = d[:, None]*N*d[None, :]
        ev, U = np.linalg.eigh(Nn)
        keep = ev > 1e-4
        Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T
              * d[None, :])
        Bw = Wh @ B
        TBw = Wh @ TB
        NA = 2*(Bw*tw[None, :]) @ Bw.T
        MA = 2*(Bw*tw[None, :]) @ TBw.T
        SA = 2*(TBw*tw[None, :]) @ TBw.T
        NA, MA, SA = ((NA + NA.T)/2, (MA + MA.T)/2,
                      (SA + SA.T)/2)
        l2A = float(scipy_eigh(MA, NA, eigvals_only=True)[1])
        rows = {}
        for ell2 in ladder:
            mu, c = temple_opt(NA, MA, SA, min(ell2, l2A))
            if c is None:
                rows[f"{ell2:g}"] = None
                continue
            nn = float(c @ NA @ c)
            rho = float(c @ MA @ c)/nn
            sig = math.sqrt(max(float(c @ SA @ c)/nn - rho*rho,
                                0.0))
            need = math.sqrt(max(rho*(min(ell2, l2A) - rho), 0.0))
            rows[f"{ell2:g}"] = {"temple": mu, "rho": rho,
                                 "sigma": sig, "needed": need}
            print(f"TEMPLE {tag} ell2 {ell2:g}: {mu:+.3e} rho "
                  f"{rho:+.3e} sigma {sig:.3e} (needed "
                  f"{need:.3e})", flush=True)
        st["temple"][tag] = {"dim": NA.shape[0], "l2A": l2A,
                             "rows": rows}
        print(f"TEMPLE {tag}: dim {NA.shape[0]} section l2 "
              f"{l2A:.4e}", flush=True)

    ckpt_key.save("oneprime_deflate", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    return st


if __name__ == "__main__":
    run()
    print("deflation reconnaissance complete", flush=True)
