#!/usr/bin/env python3
"""THE ONE-PRIME ARC, ROUND 7 -- THE INTERVAL PASS, STAGE II-b:
the certified POLE-INCLUSIVE count at the even-1.0 frontier.

Commission: "Attack the deflation route pls" (the owner's choice
at the round-259 convergence).  The float reconnaissance
(oneprime_deflate.py, committed checkpoint) measured: keeping the
even pole INSIDE the counting operator moves the certifiable
ell_2 at delta = 1.0 from the pole-free interlacing floor
lambda_2(PWP_even) ~ 0.0119 up toward lambda_2(T_even) ~ 0.0180
-- the level the Temple side needs.  This instrument certifies
that count rigorously.

THE REDUCTION (the round-243 parity-projected Birman-Schwinger
chain, one term richer; every convention validated against the
recorded rows by oneprime_deflate gD1 at 4 digits).  For even f
on [-a, a] with <f, T_even f> < nu <f, f>, where T_even = W_op +
2 chi (x) chi, chi(t) = cosh(t/2), inner products on [-a, a]:
put g = f|_[0,a] (so <f,f> = 2||g||^2, <chi,f> = 2<chi,g>, and
fhat(r) = 2<g, phi_r> with phi_r(x) = cos(r x), half-line inner
products).  From <f, W_op f> = (4/pi) int_0^oo W(r) <g,phi_r>^2
dr and qt(r) = (nu + beta - W(r))_+ >= nu + beta - W(r),
Plancherel ((4/pi) int <g,phi_r>^2 dr = 2||g||^2) gives on the
d-dimensional negative spectral subspace of T_even - nu:
    <g, (T_count - 4 chi (x) chi) g> > beta ||g||^2,
    T_count = (2/pi) int_0^oo qt(r) phi_r (x) phi_r dr,
(the restriction f -> g is injective and dimension-preserving),
hence  #{T_even < nu} <= #{eig(T_count - 4 chi chi*) > beta}.

THE CERTIFICATE (all classical; no eigenvector enclosures).
With T_H the Simpson frame discretization (Stage II's pieces,
weights, EOP -- the chi chi* term is EXACT, so EOP is unchanged)
and beta' = beta - EOP - 1e-9:
  (1) WEYL.  ||T_count - T_H||_op <= EOP gives
      #{eig(T_count - 4 chi chi*) > beta}
          <= #{eig(T_H - 4 chi chi*) > beta'}.
  (2) HAYNSWORTH INERTIA ADDITIVITY (1968).  For the bordered
      self-adjoint form on L^2(0,a) (+) R
          M = [[T_H - beta', v], [v*, 1]],   v = 2 chi,
      the two Schur reductions (T_H - beta' boundedly invertible
      -- certified below; the (2,2) block = 1 > 0) give
          n_+(T_H - beta') + n_+(g(beta'))
              = n_+(M) = 1 + n_+(T_H - beta' - v v*),
      with the secular value g(beta') = 1 - v*(T_H - beta')^{-1}v.
      So  g(beta') < 0  and  #{eig(T_H) > beta'} <= 2  force
          #{eig(T_H - 4 chi chi*) > beta'} <= 1.
  (3) WOODBURY.  T_H = Psi Psi* with Psi = Phi C^{1/2} (Phi the
      frame map, C = diag(c_i) >= 0, A = Psi*Psi = C^{1/2} G
      C^{1/2} -- Stage II's certified matrix), and for
      beta' not in spec(A) u {0}:
          (Psi Psi* - beta')^{-1}
              = -(1/beta')[I + Psi (beta' - A)^{-1} Psi*],
          v*(T_H - beta')^{-1} v
              = -(1/beta')[||v||^2 + hv^T (beta' - A)^{-1} hv],
      hv = Psi* v = 2 C^{1/2} h, h_i = <phi_{r_i}, chi> =
      [cos(r a) sinh(a/2)/2 + r sin(r a) cosh(a/2)]/(r^2 + 1/4)
      (closed form), ||v||^2 = 4(a/2 + sinh(a)/2).  The
      resolvent quadratic form is enclosed by a VERIFIED LINEAR
      SOLVE: float x ~ (beta' - A_mid)^{-1} hv_mid, interval
      residual r = hv - (beta' - A) x, and
          |hv^T (beta'-A)^{-1} hv - hv^T x| <= ||hv|| ||r||/gap,
      gap = dist(beta', spec(A)) from the veigs enclosures --
      no eigenvectors anywhere.
  (4) The chain:  #{T_even < nu} <= 1, i.e.
          lambda_2(T_even) >= nu,
      the ell_2 premise the Stage III even-1.0 cell consumes.
      (The certificate needs mu_2(T_H) > beta' NOWHERE; if the
      count regime were K <= 1 the plain Weyl route suffices --
      gP5 records K = 2 as the operating regime.)

DEGENERACY NOTE (why Haynsworth and not a secular ROOT count):
g(beta') < 0 alone, argued through root-locations of the secular
function, needs case analysis when <chi, psi_k> = 0; the inertia
identity has no cases -- it needs only the invertibility of
T_H - beta', which gP5 certifies with an explicit gap.  (When
every coupling to the above-beta' modes vanishes, g(beta') >= 1
> 0 and the certificate simply does not fire -- the safe
direction.)

GATES:
  gP1  veigs self-test (Stage II's gII2 pattern, seed 7).
  gP2  shared-machinery drift guard (re-sworn round 260,
       F260-3: the previous description claimed "this file's
       frame + Gram" -- false; the gate calls Stage II's own
       certify_cell): the IMPORTED certify_cell at the
       certified pole-free even:1.0 row (nu 0.01, beta 2.0)
       reproduces the committed oneprime_ivcount checkpoint's
       mu1/mu2 enclosures within the sum of enclosure radii
       plus 1e-9 -- a drift guard on the machinery this file
       imports (frames, W enclosures, veigs). What pins THIS
       file's own bordered path instead: gP3/gP3b (float
       wiring vs the committed reconnaissance + the Woodbury
       cross-check), gP4 (H-refinement), gP5 (the regime
       gates), and the recon's gD4 count-vs-section
       consistency.
  gP3  float wiring vs the committed reconnaissance: the
       bordered operator's float mu_2 (dense eigh of the signed
       Gram in the A-basis) must sit within 2e-4 of the
       reconnaissance's cosine-compression mu_2 at each row
       (two independent discretizations of the same operator);
       and float g(beta') must be negative at each certified
       row.
  gP4  refinement honesty: at the primary row, H -> H/sqrt(2)
       moves the certified g(beta') and the mu enclosures by
       less than the claimed EOP sum (the gII4 pattern).
  gP5  the operating regime and the Haynsworth premise: the
       veigs enclosures place beta' STRICTLY inside the
       (mu_3, mu_2) gap with explicit margins (invertibility of
       T_H - beta' with quantified gap; K = 2).
  gP6  the certificate: rigorous g(beta').hi < 0 with margin
       recorded per row; support strictly inside rmax (the
       truncation-unsafe direction guarded).

CHECKS. 7: classical only -- Birman-Schwinger, Plancherel, Weyl,
Haynsworth inertia additivity, Woodbury, verified linear solve
with residual/gap bounds, IEEE-754 directed rounding. 8: no
hypothesis input; the row targets come from the recorded Temple
needed-sigma, a property of the form itself.

Keying law: every producing file in every key (executable
content, round 245); the closure COMPUTED (F250-1).
"""
import math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key


def _fdir(x, sf, up):
    """Print x to sf significant figures rounded in the SAFE direction
    (round-281 F281-1 at the pole prints): up=False for a lower bound
    (toward -inf), up=True for an upper bound (toward +inf); exact binary
    value (F281-2)."""
    from decimal import Decimal, localcontext, ROUND_CEILING, ROUND_FLOOR
    if x is None or x != x:
        return "nan"
    with localcontext() as c:
        c.rounding = ROUND_CEILING if up else ROUND_FLOOR
        c.prec = sf
        return format(+Decimal(float(x)), "e")
from oneprime_interval_core import (I, PI, isinh, icosh, _u, _d)
from oneprime_interval_count import (
    V, vsin, vup, vdn, W_batch, support_pieces, eop_bound,
    frame_nodes, veigs, gamma_n, certify_cell)

KEYFILE = os.path.join(HERE, "oneprime_interval_pole.py")
DEPSP = {f: ckpt_key.code_sha(os.path.join(HERE, f))
         for f in sorted(ckpt_key.producer_closure(
             {"oneprime_interval_pole.py"}, HERE))}

# the certificate rows (float margins from the committed
# reconnaissance: (0.014, 2.0) count +1.58e-3, (0.015, 2.5)
# count +1.81e-3; both supports end well inside the Stage-I
# validated range r <= 260)
ROWS = [(0.5, 0.014, 2.0), (0.5, 0.015, 2.5)]
HFRAME = 0.02
RMAX = 260.0


def _frame_gram(parity_sign, a, rs, clo, chi_w):
    """Interval Gram of the scaled frame u_i = sqrt(c_i)
    phi_{r_i} -- the certify_cell construction, mirrored
    directed-step for directed-step (round-248 F248-1f)."""
    m = len(rs)
    ri = rs[:, None]
    rj = rs[None, :]
    dm = ri - rj
    sm = ri + rj

    def sinc_block(marr):
        flat = marr.ravel()
        small = np.abs(flat) < 1e-8
        arg = V.point(flat)*V.scalar(I(a), len(flat))
        s = vsin(arg)
        out_lo = np.empty_like(flat)
        out_hi = np.empty_like(flat)
        nz = ~small
        num = V(s.lo[nz], s.hi[nz])
        den = V.point(flat[nz])
        p1 = num.lo/den.lo
        p2 = num.lo/den.hi
        p3 = num.hi/den.lo
        p4 = num.hi/den.hi
        out_lo[nz] = vdn(np.minimum(np.minimum(p1, p2),
                                    np.minimum(p3, p4)))
        out_hi[nz] = vup(np.maximum(np.maximum(p1, p2),
                                    np.maximum(p3, p4)))
        da2 = (flat[small]*a)**2
        out_lo[small] = vdn(a*(1 - vup(da2/6)) - 1e-300)
        out_hi[small] = vup(np.full(int(small.sum()), a))
        return (out_lo.reshape(marr.shape),
                out_hi.reshape(marr.shape))

    d_lo, d_hi = sinc_block(dm)
    s_lo, s_hi = sinc_block(sm)
    assert parity_sign > 0          # even sector only (this file)
    Glo = vdn(0.5*(d_lo + s_lo))
    Ghi = vup(0.5*(d_hi + s_hi))
    sq_lo = vdn(np.sqrt(np.maximum(clo, 0.0)))
    sq_hi = vup(np.sqrt(chi_w))
    SL = vdn(sq_lo[:, None]*sq_lo[None, :])
    SH = vup(sq_hi[:, None]*sq_hi[None, :])
    Alo = vdn(np.minimum(np.minimum(SL*Glo, SL*Ghi),
                         np.minimum(SH*Glo, SH*Ghi)))
    Ahi = vup(np.maximum(np.maximum(SL*Glo, SL*Ghi),
                         np.maximum(SH*Glo, SH*Ghi)))
    return (Alo, Ahi), (sq_lo, sq_hi)


def _chi_column(a, rs):
    """Interval h_i = <phi_{r_i}, cosh(x/2)>_[0,a] =
    [cos(r a) sinh(a/2)/2 + r sin(r a) cosh(a/2)]/(r^2 + 1/4)."""
    n = len(rs)
    aI = I(a)
    sh = isinh(aI*I(0.5))
    ch = icosh(aI*I(0.5))
    ra = V.point(rs)*V.scalar(aI, n)
    from oneprime_interval_count import vcos
    cra = vcos(ra)
    sra = vsin(ra)
    t1 = cra*V.scalar(sh*I(0.5), n)
    t2 = sra*V.point(rs)*V.scalar(ch, n)
    num = t1 + t2
    den = V.point(rs)*V.point(rs) + V.scalar(I(0.25), n)
    # den > 0 always: directed 4-way divide
    p1 = num.lo/den.lo
    p2 = num.lo/den.hi
    p3 = num.hi/den.lo
    p4 = num.hi/den.hi
    lo = vdn(np.minimum(np.minimum(p1, p2), np.minimum(p3, p4)))
    hi = vup(np.maximum(np.maximum(p1, p2), np.maximum(p3, p4)))
    return lo, hi


def _idot(xlo, xhi, ylo, yhi):
    """Interval dot product, fsum-exact with one directed step."""
    p1 = xlo*ylo
    p2 = xlo*yhi
    p3 = xhi*ylo
    p4 = xhi*yhi
    lo = np.minimum(np.minimum(p1, p2), np.minimum(p3, p4))
    hi = np.maximum(np.maximum(p1, p2), np.maximum(p3, p4))
    return (_d(math.fsum(vdn(lo))), _u(math.fsum(vup(hi))))


def certify_pole_row(a, nu, beta, H=HFRAME, rmax=RMAX):
    """The full rigorous pole-inclusive chain for one row."""
    pieces, brackets = support_pieces(nu, beta, rmax)
    assert pieces and pieces[-1][1] < rmax - 1.0, \
        "gP6 FAIL: support not strictly inside rmax"
    eop = eop_bound(nu, beta, a, pieces, brackets, H)
    rs, wq = frame_nodes(pieces, H)
    wv = W_batch(rs)
    qt = (V.scalar(I(nu) + I(beta), len(rs)) - wv).pos()
    wqV = V.point(wq)
    twopi_inv = V.scalar((I(2.0)/PI), len(rs))
    cV = (twopi_inv*wqV*qt)
    keep = cV.hi > 0
    rs, clo, chiw = rs[keep], cV.lo[keep], cV.hi[keep]
    m = len(rs)
    (Alo, Ahi), (sq_lo, sq_hi) = _frame_gram(+1.0, a, rs, clo,
                                             chiw)
    d, rho = veigs((Alo, Ahi))
    bprime = _d(_d(beta - eop) - 1e-9)
    # gP5: beta' strictly inside the (mu_3, mu_2) gap
    gap_lo = _d(bprime - _u(d[2] + rho))
    gap_hi = _d(_d(d[1] - rho) - bprime)
    assert gap_lo > 1e-4 and gap_hi > 1e-4, \
        f"gP5 FAIL: gaps {gap_lo:.2e}/{gap_hi:.2e}"
    # resolvent gap to spec(A) (kernel-adjacent d's included)
    gap = min(abs(bprime - float(di)) for di in d)
    gap = _d(gap - rho)
    assert gap > 1e-4, f"gP5 FAIL: resolvent gap {gap:.2e}"

    # the border in the A-coordinate: hv = 2 C^{1/2} h
    h_lo, h_hi = _chi_column(a, rs)
    hv_lo = vdn(np.minimum(np.minimum(2*sq_lo*h_lo,
                                      2*sq_lo*h_hi),
                           np.minimum(2*sq_hi*h_lo,
                                      2*sq_hi*h_hi)))
    hv_hi = vup(np.maximum(np.maximum(2*sq_lo*h_lo,
                                      2*sq_lo*h_hi),
                           np.maximum(2*sq_hi*h_lo,
                                      2*sq_hi*h_hi)))
    hv_mid = 0.5*(hv_lo + hv_hi)
    hv_rad = vup(np.maximum(hv_hi - hv_mid, hv_mid - hv_lo))
    Amid = 0.5*(Alo + Ahi)
    Arad = vup(np.maximum(Ahi - Amid, Amid - Alo))

    # verified solve (beta' - A) x = hv
    x = np.linalg.solve(bprime*np.eye(m) - Amid, hv_mid)
    # residual r = hv - (beta' - A) x, enclosed midpoint-radius:
    # mid part with fl-error inflation, radius from Arad, hv_rad
    Ax = Amid @ x
    flerr = _u(gamma_n(m)*float(np.max(np.abs(Amid) @ np.abs(x)
                                       + 1e-300)))
    r_mid = hv_mid - (bprime*x - Ax)
    r_rad = (Arad @ np.abs(x)) + hv_rad + flerr \
        + 4*np.spacing(np.abs(r_mid) + 1e-300)
    r_norm = _u(math.sqrt(math.fsum(vup((np.abs(r_mid)
                                         + r_rad)**2))))
    hv_norm = _u(math.sqrt(math.fsum(vup(np.maximum(
        np.abs(hv_lo), np.abs(hv_hi))**2))))
    corr = _u(hv_norm*r_norm/gap)
    q_lo, q_hi = _idot(hv_lo, hv_hi, vdn(x - 1e-300),
                       vup(x + 1e-300))
    Q = I(_d(q_lo - corr), _u(q_hi + corr))

    # ||v||^2 = 4 (a/2 + sinh(a)/2)
    vn2 = (I(a) + isinh(I(a)))*I(2.0)
    # g(beta') = 1 + (1/beta')(||v||^2 + Q)
    g = I(1.0) + (vn2 + Q)/I(bprime)
    gmargin = _d(-g.hi)

    return {"m": int(m), "eop": eop, "rho": rho,
            "mu": [[_d(float(di) - rho), _u(float(di) + rho)]
                   for di in d[:3]],
            "bprime": bprime, "gap": gap, "gap_lo": gap_lo,
            "gap_hi": gap_hi, "corr": corr,
            "g": [g.lo, g.hi], "gmargin": gmargin,
            "nu": nu, "beta": beta, "npieces": len(pieces),
            "certified": bool(gmargin > 0),
            "rs_first_last": [float(rs[0]), float(rs[-1])],
            "hv_norm": hv_norm, "r_norm": r_norm}


def _float_bordered_mu2(a, nu, beta, H=HFRAME, rmax=RMAX):
    """Float wiring check: mu_2 of T_H - 4 chi chi* via the
    dense signed bordered Gram (midpoints), for gP3."""
    pieces, _ = support_pieces(nu, beta, rmax)
    rs, wq = frame_nodes(pieces, H)
    wv = W_batch(rs)
    qtm = np.clip(nu + beta - 0.5*(wv.lo + wv.hi), 0.0, None)
    c = (2.0/math.pi)*wq*qtm
    keep = c > 0
    rs, c = rs[keep], c[keep]
    def sc(x):
        return np.where(np.abs(x) < 1e-12, a,
                        np.sin(np.where(np.abs(x) < 1e-12, 1.0,
                                        x)*a)
                        / np.where(np.abs(x) < 1e-12, 1.0, x))
    dm = rs[:, None] - rs[None, :]
    sm = rs[:, None] + rs[None, :]
    G = 0.5*(sc(dm) + sc(sm))
    sq = np.sqrt(c)
    A = sq[:, None]*G*sq[None, :]
    h = ((0.5*np.cos(rs*a)*math.sinh(a/2)
          + rs*np.sin(rs*a)*math.cosh(a/2))/(rs*rs + 0.25))
    hv = 2*sq*h
    gam = 4*(a/2 + math.sinh(a)/2)
    Gb = np.zeros((len(rs) + 1, len(rs) + 1))
    Gb[:-1, :-1] = A
    Gb[:-1, -1] = hv
    Gb[-1, :-1] = hv
    Gb[-1, -1] = gam
    S = np.ones(len(rs) + 1)
    S[-1] = -1.0
    ev, U = np.linalg.eigh(Gb)
    keep2 = ev > 1e-12*ev.max()
    R = (U[:, keep2]*np.sqrt(ev[keep2])[None, :]).T
    K = (R*S[None, :]) @ R.T
    w = np.linalg.eigvalsh((K + K.T)/2)
    return float(w[-1]), float(w[-2])


def run():
    import json
    params = {"deps": DEPSP, "H": HFRAME, "rows": ROWS,
              "rmax": RMAX, "round": 7}
    st = ckpt_key.load("oneprime_ivpole", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is not None:
        return st
    st = {}

    # gP1: verified eigensolver self-test
    rng = np.random.default_rng(7)
    Qr, _ = np.linalg.qr(rng.standard_normal((40, 40)))
    lam = np.arange(1.0, 41.0)
    Atest = Qr @ np.diag(lam) @ Qr.T
    Atest = 0.5*(Atest + Atest.T)
    dtest, rtest = veigs((Atest, Atest))
    assert rtest < 1e-8, f"gP1 FAIL rho {rtest}"
    for lv in lam:
        assert np.min(np.abs(dtest - lv)) <= rtest, "gP1 FAIL"
    print(f"gP1 PASS: verified eigensolve rho {rtest:.2e}",
          flush=True)

    # gP2: frame cross-anchor against the committed certified row
    import glob
    cand = sorted(glob.glob(os.path.join(
        HERE, "checkpoints", "oneprime_ivcount_*.json")))
    cand = [p for p in cand if "partial" not in p]
    assert cand, "gP2 FAIL: no committed ivcount checkpoint"
    ivc = json.load(open(cand[0]))["state"]["even:1"]
    mine = certify_cell("even", 0.5, 0.01, 2.0)
    for k in ("mu1", "mu2"):
        tol = ivc["rho"] + mine["rho"] + ivc["eop"] \
            + mine["eop"] + 1e-9
        mid_a = 0.5*(ivc[k][0] + ivc[k][1])
        mid_b = 0.5*(mine[k][0] + mine[k][1])
        assert abs(mid_a - mid_b) < tol, \
            f"gP2 FAIL {k}: {mid_a} vs {mid_b}"
    print("gP2 PASS: certified even:1 row reproduced "
          f"(mu2 mid {0.5*(mine['mu2'][0] + mine['mu2'][1]):.6f})",
          flush=True)

    # gP3: float wiring vs the committed reconnaissance
    dc = sorted(glob.glob(os.path.join(
        HERE, "checkpoints", "oneprime_deflate_*.json")))
    assert dc, "gP3 FAIL: no committed reconnaissance checkpoint"
    rec = json.load(open(dc[0]))["state"]["flips"]
    for a, nu, beta in ROWS:
        _, mu2f = _float_bordered_mu2(a, nu, beta)
        rrow = rec[f"{beta:g}"]["pole"][f"{nu:g}"]
        assert abs(mu2f - rrow["mu2"]) < 2e-4, \
            f"gP3 FAIL {nu}/{beta}: {mu2f} vs {rrow['mu2']}"
        print(f"gP3: row ({nu:g}, {beta:g}) float bordered mu2 "
              f"{mu2f:.6f} vs recon {rrow['mu2']:.6f}", flush=True)
    # gP3b: the Woodbury identity checked in float against a
    # direct x-space discretization of v*(T_H - beta')^{-1}v
    # (an independent route to the same resolvent quadratic
    # form: sign errors in the reduction die here)
    a, nu, beta = ROWS[-1]
    pieces, _ = support_pieces(nu, beta, RMAX)
    rsf, wqf = frame_nodes(pieces, HFRAME)
    wvf = W_batch(rsf)
    qtf = np.clip(nu + beta - 0.5*(wvf.lo + wvf.hi), 0.0, None)
    cf = (2.0/math.pi)*wqf*qtf
    keepf = cf > 0
    rsf, cf = rsf[keepf], cf[keepf]
    bp = beta - 1e-6
    # direct route: solve (T_H - bp) f = v on a midpoint x-grid;
    # T_H acts as sum_i c_i cos(r_i x) <cos(r_i .), f>
    nx = 1200
    xg = (np.arange(nx) + 0.5)*(a/nx)
    wx = a/nx
    Phi = np.cos(rsf[:, None]*xg[None, :])
    vv = 2*np.cosh(xg/2)
    Tmat = (Phi.T*cf[None, :]) @ (Phi*wx)
    fsol = np.linalg.solve(Tmat - bp*np.eye(nx), vv)
    direct = float((vv*fsol).sum()*wx)
    sqf = np.sqrt(cf)
    hf = ((0.5*np.cos(rsf*a)*math.sinh(a/2)
           + rsf*np.sin(rsf*a)*math.cosh(a/2))/(rsf*rsf + 0.25))
    hvf = 2*sqf*hf
    dmf = rsf[:, None] - rsf[None, :]
    smf = rsf[:, None] + rsf[None, :]
    def scf(xa):
        return np.where(np.abs(xa) < 1e-12, a,
                        np.sin(np.where(np.abs(xa) < 1e-12, 1.0,
                                        xa)*a)
                        / np.where(np.abs(xa) < 1e-12, 1.0, xa))
    Af = (sqf[:, None]*(0.5*(scf(dmf) + scf(smf)))*sqf[None, :])
    xw = np.linalg.solve(bp*np.eye(len(rsf)) - Af, hvf)
    vn2f = 4*(a/2 + math.sinh(a)/2)
    wood = -(1.0/bp)*(vn2f + float(hvf @ xw))
    assert abs(direct - wood) < 5e-4*max(1.0, abs(wood)), \
        f"gP3b FAIL: direct {direct:.6e} vs Woodbury {wood:.6e}"
    print(f"gP3b PASS: v*(T_H-b')^-1 v direct {direct:+.6e} vs "
          f"Woodbury {wood:+.6e}", flush=True)
    print("gP3 PASS: bordered float mu2 matches the committed "
          "reconnaissance at every row", flush=True)

    # the certificates
    for a, nu, beta in ROWS:
        res = certify_pole_row(a, nu, beta)
        st[f"even:{nu:g}:{beta:g}"] = res
        tag = (f"[COUNT <= 1 CERTIFIED at nu {nu:g}]"
               if res["certified"] else "[NOT certified]")
        print(f"IVP even:1.0 row (nu {nu:g}, beta {beta:g}): "
              f"m {res['m']} EOP {_fdir(res['eop'], 3, True)} rho "
              f"{res['rho']:.2e} mu2 [{_fdir(res['mu'][1][0], 7, False)}, "
              f"{_fdir(res['mu'][1][1], 7, True)}] mu3 "
              f"[{_fdir(res['mu'][2][0], 7, False)}, {_fdir(res['mu'][2][1], 7, True)}] "
              f"gaps {_fdir(res['gap_lo'], 3, False)}/{_fdir(res['gap_hi'], 3, False)} "
              f"g(beta') [{_fdir(res['g'][0], 7, False)}, "
              f"{_fdir(res['g'][1], 7, True)}] margin {_fdir(res['gmargin'], 4, False)} "
              f"{tag}", flush=True)
        assert res["certified"], \
            f"gP6 FAIL ({nu}, {beta}): g margin {res['gmargin']}"

    # gP4: refinement honesty at the primary row -- two checks:
    # the mu_2 enclosure moves within the claimed EOPs + radii
    # (the gII4 pattern: the sharp frame check), and the g value
    # moves within the resolvent perturbation bound
    #   |dg| <= ||v||^2 (eop + eop' + |dbeta'|)/(gap gap')
    #           + corr + corr'
    # (first-resolvent-identity + |g'| <= ||v||^2/gap^2 over the
    # beta' shift; classical).
    a, nu, beta = ROWS[-1]
    ref = certify_pole_row(a, nu, beta, H=HFRAME/math.sqrt(2.0))
    base = st[f"even:{nu:g}:{beta:g}"]
    mshift = abs(0.5*(ref["mu"][1][0] + ref["mu"][1][1])
                 - 0.5*(base["mu"][1][0] + base["mu"][1][1]))
    mbudget = base["eop"] + ref["eop"] + base["rho"] \
        + ref["rho"] + 1e-10
    assert mshift <= mbudget, \
        f"gP4 FAIL mu2 shift {mshift:.3e} budget {mbudget:.3e}"
    gshift = abs(0.5*(ref["g"][0] + ref["g"][1])
                 - 0.5*(base["g"][0] + base["g"][1]))
    vn2f = 4*(a/2 + math.sinh(a)/2)
    gbudget = vn2f*(base["eop"] + ref["eop"]
                    + abs(base["bprime"] - ref["bprime"])) \
        / (base["gap"]*ref["gap"]) \
        + base["corr"] + ref["corr"] + 1e-9
    assert gshift <= gbudget, \
        f"gP4 FAIL g shift {gshift:.3e} budget {gbudget:.3e}"
    print(f"gP4 PASS: H-refinement mu2 shift {mshift:.2e} "
          f"(budget {mbudget:.2e}), g shift {gshift:.2e} "
          f"(budget {gbudget:.2e})", flush=True)
    st["__gP4__"] = {"mshift": mshift, "gshift": gshift,
                     "eop_ref": ref["eop"], "g_ref": ref["g"]}

    nustar = max(nu for (a, nu, beta) in ROWS
                 if st[f"even:{nu:g}:{beta:g}"]["certified"])
    st["__nustar__"] = nustar
    print(f"STAGE II-b VERDICT: lambda_2(T_even) >= {nustar:g} "
          f"CERTIFIED at delta = 1.0 (pole-inclusive count; "
          f"the pole-free chain certified 0.01)", flush=True)
    ckpt_key.save("oneprime_ivpole", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    return st


if __name__ == "__main__":
    run()
    print("interval pole-inclusive count (Stage II-b) complete",
          flush=True)
