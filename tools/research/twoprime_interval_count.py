#!/usr/bin/env python3
"""THE TWO-PRIME WINDOW, STAGE 1 -- the certified POLE-INCLUSIVE
Birman-Schwinger count for the odd sector of the two-prime form
at delta = 1.10 (a = 0.55): the ell_2 premise of the first
two-prime certificate (A417/A418 (iv)).

THE OBJECT. The semi-local Weil form at the real place plus the
primes 2 and 3 -- on [log 3, log 4) Weil's full functional --
with kernel
    W_23(r) = Re psi(1/4 + ir/2) - log pi - C_2 cos(r log 2)
              - C_3 cos(r log 3),   C_p = 2 log p / sqrt p,
in the odd sector, where the pole is the NEGATIVE rank-one
-2 |chi><chi|, chi(t) = sinh(t/2).

THE COUNT, POLE KEPT INSIDE. For beta > 0,
    T_odd - nu = max(W_23 - nu, beta)(D) - [qt(D) + 2|chi><chi|],
    qt = (nu + beta - W_23)_+  (compactly supported on [0, rmax]
    by the tail lemma),
so with B >= beta and K = qt(D) + 2|chi><chi| >= 0 (both terms
PSD), Weyl monotonicity gives #{T_odd < nu} <= #{eig K > beta}.
K's nonzero spectrum is that of the frame Gram of
    f_i = sqrt(c_i/2) sin(r_i t)  (Simpson nodes r_i on the
                                   support pieces, c_i = (2/pi)
                                   w_i qt(r_i)),
    g   = sqrt 2 sinh(t/2)
in the full inner product 2 int_0^a: the odd-projected sine Gram
A_ij = sqrt(c_i c_j) [sin((r_i - r_j)a)/(r_i - r_j) - sin((r_i +
r_j)a)/(r_i + r_j)]/2 (the one-prime instrument's closed form)
BORDERED by the pole column b_i = sqrt(c_i) [J(1/2) - J(-1/2)]
(r_i), J(k) = (e^{ka}(k sin(ra) - r cos(ra)) + r)/(k^2 + r^2)
-- i.e. sqrt(c_i) * 2 int_0^a sin(r_i t) sinh(t/2) dt -- and the
corner <g, g> = 2 (sinh a - a).  Because the odd pole enters K
with a POSITIVE sign, the bordered matrix is a genuine Gram and
the verified eigenvalue enclosure (the one-prime instrument's
veigs) applies directly -- no Woodbury secular certificate, no
count-regime gate (those were the even sector's device, where the
pole enters K negatively; Theorem 1bj(iii)). The discretisation
error ||K - K_H|| is the one-prime EOP bound (Simpson four-
derivative term with the two-prime majorants + per-bracket hull
terms); the pole column is exact (closed form, interval).
    CERTIFICATE:  mu_2(K_H) + EOP < beta  =>  #{T_odd < nu} <= 1
                                             =>  lambda_2(T_odd) >= nu.
This is the direct premise the Temple certificate needs
(oneprime_interval_temple's odd two-stage route, whose
interlacing capped ell_2 at the pole-free lambda_1 ~ 0.015 here,
is bypassed: the float reconnaissance showed the harmonic trial
needs ell_2 >~ 0.035 at this cell).

WHAT CHANGES AGAINST THE ONE-PRIME INSTRUMENT (every other line
is the committed round-6 chain, imported or copied verbatim):
  * W_batch/W_enclose: - C_3 cos(r log 3) (C3I = 2 LOG3 / SQRT3,
    interval constants at 80 bits);
  * majorants: |W'| <= [psi'/2 + C_2 log 2] + C_3 log 3, and
    C_3 log^k 3 added to M2, M3, M4 (the cosine's derivatives);
  * the tail lemma: for r >= rmax, W_23(r) >= h_+(rmax) - C_2 -
    C_3 (h_+ increasing), asserted > nu + beta -- which forces
    rmax = 600 here (h_+(600) - C_2 - C_3 = 2.31 > 2.05; at 260
    the cap 1.47 would exclude beta >= 1.5);
  * qmax: -min W_23 <= -psi(1/4) + ln pi + C_2 + C_3 = 7.621 <
    7.64 (the one-prime 6.36 plus C_3 = 1.2686);
  * the bordered Gram (above).

GATES (asserted in run()):
  gII2   the verified eigensolver self-test (one-prime gate,
         re-run here);
  gII5   the pole column: the interval closed form contains the
         float64 scipy quadrature value at 12 nodes;
  gII6   the kernel: W23_batch contains the float64 two-prime
         kernel (scipy digamma) at 200 points on [0, rmax];
  gII3   the certificate margin > 0 for the row;
  gII1'  wiring vs the float reconnaissance (twoprime_odd_recon):
         the float bordered mu_2 lies inside the enclosure
         widened by EOP + 1e-2.

CHECKS. 7: classical (Birman-Schwinger, Weyl, Simpson, IEEE-754
interval arithmetic). 8: no hypothesis input; Riemann-side pure
mathematics.  Keying law: every producing file in every key
(executable content; the computed transitive closure).
"""
import json, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from oneprime_interval_core import (
    I, PI, TWO_PI, LOG2, LOGPI, SQRT2, C2I, iexp, ilog, icos, isin,
    isinh, _u, _d, _const, dW_majorant, d2W_majorant, W_enclose)
from oneprime_interval_count import (
    V, vup, vdn, vsin, vcos, W_batch as W2_batch, M3_majorant,
    M4_majorant, veigs, frame_nodes)

LOG3 = _const(lambda iv: iv.log(3))
SQRT3 = _const(lambda iv: iv.sqrt(3))
C3I = I(2.0)*LOG3/SQRT3          # 2 log 3 / sqrt 3 = 1.26857...

# THE ROW (set from the float reconnaissance; recorded in A419)
A_CELL = 0.55                    # delta = 1.10
ROW = {"nu": 0.05, "beta": 2.0}  # the lever scan (A419): margin ~9e-3 float
RMAX = 600.0                     # tail lemma: h+(600) - C2 - C3 = 2.31 > 2.05
H_FRAME = 0.02



def _fdir(x, sf, up):
    """Print x to sf significant figures rounded in the SAFE direction
    (round-280 F280-2 at the instrument prints): up=False for a lower
    bound (toward -inf), up=True for an upper bound (toward +inf)."""
    from decimal import Decimal, localcontext, ROUND_CEILING, ROUND_FLOOR
    if x is None or x != x:
        return "nan"
    with localcontext() as c:
        c.rounding = ROUND_CEILING if up else ROUND_FLOOR
        c.prec = sf
        return format(+Decimal(repr(float(x))), "e")

def W23_batch(r):
    r = np.asarray(r, np.float64)
    n = len(r)
    cosarg = V.point(r)*V.scalar(LOG3, n)
    return W2_batch(r) - V.scalar(C3I, n)*vcos(cosarg)


def W23_enclose(r):
    return W_enclose(r) - C3I*icos(I(r)*LOG3)


def M1_23(rmax):
    return _u(dW_majorant(rmax) + (C3I*LOG3).hi)

def M2_23(rmax):
    return _u(d2W_majorant(rmax) + (C3I*LOG3*LOG3).hi)

def M3_23():
    return _u(M3_majorant() + (C3I*LOG3*LOG3*LOG3).hi)

def M4_23():
    return _u(M4_majorant() + (C3I*LOG3*LOG3*LOG3*LOG3).hi)


def support_pieces(nu, beta, rmax=RMAX, scan_h=2e-3, ref_h=2e-5):
    """oneprime_interval_count.support_pieces with the two-prime
    kernel, majorant, and tail lemma (see the module docstring)."""
    c = nu + beta
    m1 = M1_23(rmax)

    def classify(grid):
        mids = 0.5*(grid[:-1] + grid[1:])
        half = (grid[1] - grid[0])/2
        wmid = W23_batch(mids)
        cell_lo = vdn(wmid.lo - _u(m1*half*1.0000001))
        cell_hi = vup(wmid.hi + _u(m1*half*1.0000001))
        inn = cell_hi < c
        out = cell_lo > c
        return mids, cell_lo, inn, out

    grid = np.arange(0.0, rmax + scan_h, scan_h)
    grid[-1] = min(grid[-1], rmax + scan_h)
    mids, cell_lo, inn, out = classify(grid)
    strad = ~(inn | out)
    # tail lemma: h+(rmax) - C2 - C3 > c (h+ increasing on r >= 0)
    wr = W_enclose(rmax)
    hplus_lo = (wr + C2I*icos(I(rmax)*LOG2)).lo
    assert _d(_d(hplus_lo - C2I.hi) - C3I.hi) > c, \
        f"tail lemma fails: h+({rmax}) - C2 - C3 <= {c}"
    pieces = []
    brackets = []
    i = 0
    ncell = len(mids)
    while i < ncell:
        if inn[i]:
            j = i
            while j + 1 < ncell and inn[j + 1]:
                j += 1
            pieces.append((grid[i], grid[j + 1]))
            i = j + 1
        elif strad[i]:
            j = i
            while j + 1 < ncell and strad[j + 1]:
                j += 1
            lo_r, hi_r = grid[i], grid[j + 1]
            ng = max(4, int(math.ceil((hi_r - lo_r)/ref_h)))
            g2 = np.linspace(lo_r, hi_r, ng + 1)
            m2_, cl2, in2, out2 = classify(g2)
            k = 0
            while k < ng:
                if in2[k]:
                    l = k
                    while l + 1 < ng and in2[l + 1]:
                        l += 1
                    pieces.append((g2[k], g2[l + 1]))
                    k = l + 1
                elif not out2[k]:
                    l = k
                    while l + 1 < ng and not out2[l + 1] \
                            and not in2[l + 1]:
                        l += 1
                    qmx = _u(max(0.0,
                                 float((c - cl2[k:l + 1]).max())))
                    brackets.append((g2[k], g2[l + 1], qmx))
                    k = l + 1
                else:
                    k += 1
            i = j + 1
        else:
            i += 1
    return pieces, brackets


def eop_bound(nu, beta, a, pieces, brackets, H, rmax=RMAX):
    """The one-prime EOP bound with the two-prime majorants and
    qmax: -min W_23 <= -psi(1/4) + ln pi + C2 + C3 < 7.64."""
    m1 = M1_23(rmax)
    m2 = M2_23(rmax)
    m3 = M3_23()
    m4 = M4_23()
    qmax = _u(nu + beta + 7.64)
    ta = 2*a
    g4 = a*(m4 + 4*ta*m3 + 6*ta*ta*m2 + 8*ta**3*m1
            + 2*ta**4*qmax)
    tot_len = sum(p[1] - p[0] for p in pieces)
    simpson = tot_len*(H**4)*g4/180.0
    br = sum((b[1] - b[0])*b[2] for b in brackets)*a
    return _u((2/math.pi)*(simpson + br)*(1 + 1e-9))


def pole_column_I(a, rs):
    """Interval enclosures of 2 int_0^a sin(r t) sinh(t/2) dt =
    J(1/2) - J(-1/2) per node (closed form; scalar interval
    transcendentals)."""
    aI = I(a)
    ep = iexp(aI*I(0.5))
    em = iexp(aI*I(-0.5))
    out_lo = np.empty(len(rs))
    out_hi = np.empty(len(rs))
    for i, r in enumerate(rs):
        rI = I(float(r))
        s = isin(rI*aI)
        cc = icos(rI*aI)
        r2 = rI*rI
        jp = (ep*(I(0.5)*s - rI*cc) + rI)/(I(0.25) + r2)
        jm = (em*(I(-0.5)*s - rI*cc) + rI)/(I(0.25) + r2)
        v = jp - jm
        out_lo[i], out_hi[i] = v.lo, v.hi
    return V(out_lo, out_hi)


def certify_row(a, nu, beta, H=H_FRAME, rmax=RMAX):
    pieces, brackets = support_pieces(nu, beta, rmax)
    eop = eop_bound(nu, beta, a, pieces, brackets, H, rmax)
    rs, wq = frame_nodes(pieces, H)
    wv = W23_batch(rs)
    qt = (V.scalar(I(nu) + I(beta), len(rs)) - wv).pos()
    wqV = V.point(wq)
    twopi_inv = V.scalar((I(2.0)/PI), len(rs))
    cV = (twopi_inv*wqV*qt)
    keep = cV.hi > 0
    rs, clo, chi = rs[keep], cV.lo[keep], cV.hi[keep]
    m = len(rs)
    ri = rs[:, None]
    rj = rs[None, :]
    dm = ri - rj
    sm = ri + rj
    aI = I(a)

    def sinc_block(marr):
        flat = marr.ravel()
        small = np.abs(flat) < 1e-8
        arg = V.point(flat)*V.scalar(aI, len(flat))
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
        out_hi[small] = vup(np.full(small.sum(), a))
        return (out_lo.reshape(marr.shape),
                out_hi.reshape(marr.shape))
    d_lo, d_hi = sinc_block(dm)
    s_lo, s_hi = sinc_block(sm)
    # odd projection: G = (sinc(d) - sinc(s))/2
    Glo = vdn(0.5*(d_lo - s_hi))
    Ghi = vup(0.5*(d_hi - s_lo))
    sq_lo = vdn(np.sqrt(np.maximum(clo, 0.0)))
    sq_hi = vup(np.sqrt(chi))
    SL = vdn(sq_lo[:, None]*sq_lo[None, :])
    SH = vup(sq_hi[:, None]*sq_hi[None, :])
    Alo = vdn(np.minimum(np.minimum(SL*Glo, SL*Ghi),
                         np.minimum(SH*Glo, SH*Ghi)))
    Ahi = vup(np.maximum(np.maximum(SL*Glo, SL*Ghi),
                         np.maximum(SH*Glo, SH*Ghi)))
    # the pole column and corner (genuine Gram: PSD rank-one added)
    col = pole_column_I(a, rs)
    blo = vdn(np.minimum(np.minimum(sq_lo*col.lo, sq_lo*col.hi),
                         np.minimum(sq_hi*col.lo, sq_hi*col.hi)))
    bhi = vup(np.maximum(np.maximum(sq_lo*col.lo, sq_lo*col.hi),
                         np.maximum(sq_hi*col.lo, sq_hi*col.hi)))
    gg = I(2.0)*(isinh(aI) - aI)
    Blo = np.zeros((m + 1, m + 1))
    Bhi = np.zeros((m + 1, m + 1))
    Blo[:m, :m], Bhi[:m, :m] = Alo, Ahi
    Blo[:m, m] = Blo[m, :m] = blo
    Bhi[:m, m] = Bhi[m, :m] = bhi
    Blo[m, m], Bhi[m, m] = gg.lo, gg.hi
    d, rho = veigs((Blo, Bhi))
    dfree, rhofree = veigs((Alo, Ahi))
    mu1 = I(_d(d[0] - rho), _u(d[0] + rho))
    mu2 = I(_d(d[1] - rho), _u(d[1] + rho))
    mu2_full_hi = _u(mu2.hi + eop)
    margin = _d(beta - mu2_full_hi)
    return {"m": int(m), "eop": eop, "rho": rho,
            "mu1": [mu1.lo, mu1.hi], "mu2": [mu2.lo, mu2.hi],
            "mu2_polefree": [_d(dfree[1] - rhofree),
                             _u(dfree[1] + rhofree)],
            "mu2_full_hi": mu2_full_hi, "beta": beta, "nu": nu,
            "a": a, "rmax": rmax, "H": H, "margin": margin,
            "npieces": len(pieces), "nbrackets": len(brackets),
            "support_len": float(sum(p[1] - p[0] for p in pieces)),
            "gg": [gg.lo, gg.hi],
            "certified": bool(margin > 0)}


def _sha(name):
    return ckpt_key.code_sha(os.path.join(HERE, name))


DEPS2C = {f: _sha(f) for f in sorted(ckpt_key.producer_closure(
    ("twoprime_interval_count.py",), HERE))}
KEYFILE = os.path.join(HERE, "twoprime_interval_count.py")


def run():
    from scipy.special import digamma
    from scipy.integrate import quad
    params = {"deps": DEPS2C, "H": H_FRAME, "row": ROW, "a": A_CELL,
              "rmax": RMAX, "round": 1}
    st = ckpt_key.load("twoprime_ivcount", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is not None:
        return st
    # gII2: verified eigensolver self-test (the one-prime gate)
    rng = np.random.default_rng(6)
    Qr, _ = np.linalg.qr(rng.standard_normal((40, 40)))
    lam = np.arange(1.0, 41.0)
    Atest = Qr @ np.diag(lam) @ Qr.T
    Atest = 0.5*(Atest + Atest.T)
    dtest, rtest = veigs((Atest, Atest))
    assert rtest < 1e-8, f"gII2 FAIL rho {rtest}"
    for lv in lam:
        assert np.min(np.abs(dtest - lv)) <= rtest, "gII2 FAIL"
    print(f"gII2 PASS: verified eigensolve rho {rtest:.2e}", flush=True)
    # gII5: the pole column closed form contains the quadrature value
    a = A_CELL
    rtest_nodes = np.array([0.0, 0.37, 1.1, 2.9, 7.3, 15.8, 41.0, 99.5,
                            250.2, 640.0, 1100.3, 1499.0])
    col = pole_column_I(a, rtest_nodes)
    for i, r in enumerate(rtest_nodes):
        q, _e = quad(lambda t: math.sin(r*t)*math.sinh(t/2), 0.0, a,
                     limit=400)
        assert col.lo[i] - 1e-9 <= 2*q <= col.hi[i] + 1e-9, \
            f"gII5 FAIL r={r}: [{col.lo[i]}, {col.hi[i]}] vs {2*q}"
    print("gII5 PASS: pole column closed form contains quadrature "
          "at 12 nodes", flush=True)
    # gII6: the two-prime kernel enclosure contains scipy's value
    rr = np.linspace(0.0, RMAX, 200)
    wv = W23_batch(rr)
    wf = (digamma(0.25 + 0.5j*rr).real - math.log(math.pi)
          - float(C2I.lo)*np.cos(rr*math.log(2))
          - float(C3I.lo)*np.cos(rr*math.log(3)))
    assert np.all(wv.lo - 1e-9 <= wf) and np.all(wf <= wv.hi + 1e-9), \
        "gII6 FAIL: W23 enclosure misses the float kernel"
    print(f"gII6 PASS: W23 enclosure contains the float kernel at 200 "
          f"points (max width {float(np.max(wv.hi - wv.lo)):.2e})", flush=True)
    res = certify_row(a, ROW["nu"], ROW["beta"])
    print(f"IVC2 odd:1.1 nu {ROW['nu']:g} beta {ROW['beta']:g}: m {res['m']} "
          f"support {res['support_len']:.1f} pieces {res['npieces']} "
          f"brackets {res['nbrackets']}; mu2 [{res['mu2'][0]:.6f}, "
          f"{res['mu2'][1]:.6f}] (pole-free [{res['mu2_polefree'][0]:.6f}, "
          f"{res['mu2_polefree'][1]:.6f}]) EOP {res['eop']:.2e} rho "
          f"{res['rho']:.2e} -> mu2+EOP {res['mu2_full_hi']:.6f} < beta "
          f"{ROW['beta']:g}: margin {_fdir(res['margin'], 4, False)} "
          f"[{'COUNT <= 1 CERTIFIED: lambda_2(T_odd) >= nu' if res['certified'] else 'FAIL'}]",
          flush=True)
    assert res["certified"], f"gII3 FAIL: margin {res['margin']:.3e}"
    # gII1': wiring vs the float reconnaissance
    try:
        import twoprime_odd_recon as TOR
        m1f, m2f, _m2free, _gg = TOR.count_mu_pole(a, ROW["nu"], ROW["beta"],
                                                    rmax=RMAX)
        lo = res["mu2"][0] - res["eop"] - 1e-2
        hi = res["mu2"][1] + res["eop"] + 1e-2
        assert lo <= m2f <= hi, f"gII1' FAIL: float mu2 {m2f} vs [{lo}, {hi}]"
        print(f"gII1' PASS: float bordered mu2 {m2f:.6f} inside the enclosure",
              flush=True)
        res["float_mu2"] = m2f
    except ImportError:
        print("gII1' skipped: twoprime_odd_recon absent", flush=True)
    st = {"odd:1.1": res}
    ckpt_key.save("twoprime_ivcount", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    return st


if __name__ == "__main__":
    run()
    print("two-prime interval count (Stage 1) complete", flush=True)
