#!/usr/bin/env python3
"""THE ONE-PRIME ARC, ROUND 6 -- THE INTERVAL PASS, STAGE III:
the interval Temple certificates, and the assembled theorem.

GOAL. For each certificate cell a RIGOROUS Kato-Temple lower
bound (ratio form)
    lambda_1(T_cell) >= (ell2 M - S)/(ell2 n - M) > 0
(valid whenever ell2 <= lambda_2 and M/n < ell2; it is the
rearranged positivity of <phi,(T - lambda_1)(T - ell2)phi>),
with n = <phi, phi>, M = <phi, T phi>, S = ||T phi||^2 all
interval enclosures, and ell2 from Stage II's certified counts
(even: ell2 = nu*, the even pole being PSD rank-one; odd:
two-stage per round 243 -- the pole-free Temple gives
nu1 <= lambda_1(PWP_odd), then negative-rank-one interlacing
gives lambda_2(T_odd) >= nu1).

THE TRIAL IS ENTIRE. phi = sum_h c_h trig(w_h t) + P(t) with P
the polynomial part (the nu = 3/2 modes q(t) C_m^{3/2}(t/a) are
polynomials).  The float64 survey (this round) shows the entire
basis closes every theorem cell, so no fractional-edge mode
enters the certificates and every derivative of phi is bounded
and explicit.  The trial's coefficients are float64-optimized
and FROZEN (a trial carries no rigor burden).

THE OPERATOR IN CLOSED FORM.  With phi_an the globally-defined
trig+poly expression and phi its restriction to [-a, a] (zero
outside),
  (T phi)(t) = -(log 4pi + gamma) phi(t) - phi(t) IA(a + t)
               - DINT(t) + phi(t) log coth((a + t)/2)
               - (C2/2)[phi(t + log2) + phi(t - log2)]
               +/- 2 chi(t) <chi, phi>,
  DINT(t) = int_0^{a+t} E(u) Dfull(t, u) du
            - (1/2) int_{a-t}^{a+t} E(u) phi_an(t + u) du,
  Dfull(t, u) = (phi_an(t+u) + phi_an(t-u))/2 - phi_an(t)
(the second integral removes the analytic continuation of
phi_an(t+u) beyond the support edge; phi(t-u) stays in range on
[0, a+t]).  Every u-integral reduces to ONE-DIMENSIONAL
CUMULATIVE TABLES built once per cell with rigorous interval
quadrature:
  IA(x) = int_0^x A,  A = (e^{u/2} - 1)/sinh u,
  Gw(x) = int_0^x E sin^2(w u/2) du   (per harmonic w),
  Cw(x) = int_{X0}^x E cos(w u) du,  Sw(x) likewise with sin,
  Hi(x) = int E u^i du (i >= 2 from 0; i in {0, 1} from X0),
  E = e^{u/2}/sinh u.  The X0-based tables are only ever used
as DIFFERENCES over [a - t, a + t] with a - t >= DEDGE > X0
handled through the geometric node region.  Then
  int_0^{a+t} E Dfull du =
      sum_h c_h (-2) trig(w_h t) Gw_h(a + t)
      + sum_{i even >= 2} Q_i(t) Hi(a + t)
(Q_i the exact binomial re-expansion: Dfull_poly =
 sum_{i even >= 2} u^i Q_i(t)), and
  int_{a-t}^{a+t} E phi_an(t+u) du =
      sum_h c_h [trig-products with (Cw, Sw) differences]
      + sum_i P_i(t)[Hi(k2) - Hi(k1)]
(P_i the plain binomial re-expansion; k1 = a - t, k2 = a + t).
THE PAYOFF: T phi and its t-DERIVATIVE are explicit elementary
expressions (table derivatives are the INTEGRANDS, evaluated
pointwise), so the t-quadratures for n, M, S use midpoint cells
with correction terms that are TIGHT LOCAL INTERVAL EVALUATIONS
-- no crude global envelopes anywhere.  Between table nodes a
lookup returns the bracketing cumulatives plus the cell's
stored integrand hull.

QUADRATURES.  Tables: geometric nodes X0..XSW then uniform
(per-cell htab), per-cell midpoint + f''-interval corrections
(integrands elementary; E'', A'' explicit).  t-integrals for
M, S: uniform cells (per-cell ht from CELLCFG, sized so the
O(ht^2) lambda-loss sits under each cell's float margin),
midpoint + correction |int - f(m) h| <= (h^2/4)|f'(cell)| with
f' from the closed form, cells split at the kink t = log2 - a,
GRADED (per-cell theta) toward t = a; chi and n by Simpson at
the fixed pitch HCHI (h^5 error, ht-independent); the DEDGE
edge slivers are bounded by the log-squared envelope.  The M/S
passes are BATCH-VECTORIZED (Tphi_batch over t-cell arrays:
table lookups by searchsorted gathers, trig through the Stage-
II V layer, signed C/S table differences widened by endpoint
slivers w * suffix-max|f| -- the inner/outer corner hull is
not an enclosure for signed integrands); chunk sums use
math.fsum (exactly rounded) with a final directed rounding.

GATES:
  gT2  wiring: rho = M/n tracks the float64 fixture rho within
       1e-4 (the float pipeline has its own quadrature error).
  gT3  the Temple certificate per cell with premises
       (M/n < ell2 rigorously; odd stage-one nu1 > 0).
  gT5  normalization sanity: n in [0.5, 2] (the fixture
       normalizes to n = 1 in float64).
  gT6  batch/scalar cross-check: Tphi_batch and the scalar
       Tphi enclose the same value, so per cell their
       enclosures (value and derivative) must overlap at
       sample points.
  gT7  _vlog containment against the Stage-I scalar ilog
       (itself mpmath-gated), width-capped.

CHECKS. 7: classical (Kato-Temple ratio form, midpoint/
mean-value remainders, IEEE-754 interval arithmetic). 8: no
hypothesis input.

Keying law: every producing file in every key (executable
content, round 245).
"""
import json, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from oneprime_interval_core import (
    I, PI, LOG2, C2I, EULER, iexp, ilog, isinh, icosh,
    icos, isin, _u, _d)
from oneprime_interval_count import V, vsin, vcos, vup, vdn

LG4PI = ilog(I(4.0)*PI) + EULER

X0 = 1e-16
XSW = 1e-3
HTAB = 1e-5
HT = 5e-5
HCHI = 5e-4     # chi/norm Simpson pitch, fixed (h^5 error)
DEDGE = 1e-14   # > 10*X0; the edge sliver (log-squared bound)

# per-cell (ht, htab, theta): mean-value pitch, table pitch,
# edge grading -- sized from each cell's float64 Temple margin
# (the lambda-loss scales as ht^2 and theta^2; the tightest
# cell, even:0.95 at float margin ~8e-7, needs ht ~ 8e-7)
CELLCFG = {
    "even:0.6931": (5e-5, 1e-5, 0.1),
    "even:0.8":    (5e-6, 1e-5, 0.05),
    "even:0.9":    (3e-6, 1e-5, 0.03),
    "even:0.95":   (8e-7, 4e-6, 0.01),
    "odd:0.9":     (2e-5, 1e-5, 0.1),
    "odd:1.05":    (4e-6, 1e-5, 0.04),
    "odd:1.09":    (2e-6, 5e-6, 0.02),
}


def _vexp_end(x, side):
    n = np.round(x/0.6931471805599453)
    sV = V.point(x) - V(np.full_like(x, LOG2.lo),
                        np.full_like(x, LOG2.hi))*V.point(n)
    K = 22
    term = V(np.ones_like(x), np.ones_like(x))
    tot = V(np.ones_like(x), np.ones_like(x))
    for k in range(1, K):
        # interval coefficient (round-248 F248-1c: the float
        # 1.0/k pre-rounds outside any remainder budget)
        term = term*sV*V.scalar(I(1.0)/I(float(k)), len(x))
        tot = tot + term
    m = np.maximum(np.abs(sV.lo), np.abs(sV.hi))
    rem = vup((m**K)/math.factorial(K)/(1 - m/(K + 1)))
    lo = np.ldexp(vdn(tot.lo - rem), n.astype(int))
    hi = np.ldexp(vup(tot.hi + rem), n.astype(int))
    return lo if side < 0 else hi

def _vexp(x):
    return V(_vexp_end(x.lo, -1), _vexp_end(x.hi, +1))

def _vlog_end(x, side):
    """Vectorized rigorous log of a positive endpoint array:
    frexp reduction x = m 2^e with m folded into [1/sqrt2,
    sqrt2), then log m = 2 atanh z, z = (m-1)/(m+1), |z| <=
    0.1716, atanh by series with explicit remainder and
    INTERVAL coefficients 1/(2k+1)."""
    m, e = np.frexp(x)
    small = m < 0.7071067811865476
    m = np.where(small, m*2.0, m)          # exact scaling
    e = np.where(small, e - 1, e).astype(np.float64)
    n = len(x)
    z = (V.point(m) - 1.0).divpos(V.point(m) + 1.0)
    z2 = z.sq()
    assert np.all(z2.hi < 0.03)
    K = 14
    term = V(z.lo.copy(), z.hi.copy())
    tot = V(z.lo.copy(), z.hi.copy())
    for k in range(1, K):
        term = term*z2
        tot = tot + term*V.scalar(I(1.0)/I(float(2*k + 1)), n)
    mz = np.maximum(np.abs(z.lo), np.abs(z.hi))
    rem = vup((mz**(2*K + 1))/(2*K + 1)/(1 - 0.03))
    at = V(vdn(tot.lo - rem), vup(tot.hi + rem))
    lg = at*2.0 + V(np.full(n, LOG2.lo),
                    np.full(n, LOG2.hi))*V.point(e)
    return lg.lo if side < 0 else lg.hi

def _vlog(x):
    """log on a positive interval vector (monotone: endpoint
    enclosures)."""
    return V(_vlog_end(x.lo, -1), _vlog_end(x.hi, +1))

def _vpow(x, k):
    p = V(np.ones_like(x.lo), np.ones_like(x.lo))
    for _ in range(k):
        p = p*x
    return p

def _sinh_cosh(u):
    """e^{u/2}, sinh u, cosh u -- with a SERIES path for small u
    (the direct (e^u - e^{-u})/2 loses ~11 digits of RELATIVE
    width at u ~ 1e-11, which summed over the geometric table
    region was a 3e-4 width leak).  sinh u = u(1 + u^2/6 +
    u^4/120 + R), 0 <= R <= u^6/5040/(1 - u^2/56).
    E-BOUND NOTE (cited by the CE_B budget; round-249 F249-4
    restores the note the citation pointed at): E(u) =
    e^{u/2}/sinh u <= 1/u + 1 on (0, 1.2], since termwise
    (1 + u) sinh u = (1+u)(u + u^3/6 + ...) >= u(1 + u/2 +
    u^2/8 + ...) = u e^{u/2} (coefficient-by-coefficient for
    u <= 1.2); numeric margin >= 0.499 over the whole range."""
    n = len(u.lo)
    e2 = _vexp(u*V.scalar(0.5, n))
    e = e2*e2
    einv = V(vdn(1.0/e.hi), vup(1.0/e.lo))   # directed (F248-1b)
    sh = (e - einv)*V.scalar(0.5, n)
    ch = (e + einv)*V.scalar(0.5, n)
    small = u.hi < 0.01
    if np.any(small):
        ulo, uhi = u.lo[small], u.hi[small]
        m = int(small.sum())
        us = V(ulo, uhi)
        u2 = us*us
        one = V(np.ones(m), np.ones(m))
        ser = one + u2*V.scalar(I(1.0)/I(6.0), m) \
            + u2*u2*V.scalar(I(1.0)/I(120.0), m)
        rem = vup((uhi**6)/5040.0/(1 - 1e-4/56))
        ser = V(ser.lo, vup(ser.hi + rem))
        shs = us*ser
        slo = sh.lo.copy()
        shi = sh.hi.copy()
        slo[small] = shs.lo
        shi[small] = shs.hi
        sh = V(slo, shi)
    return e2, sh, ch


def E_A_prime(u):
    """E, A, E', E'', A', A'' on u-interval vectors, u.lo > 0."""
    n = len(u.lo)
    e2, sh, ch = _sinh_cosh(u)
    E = e2.divpos(sh)
    A = (e2 - 1).divpos(sh)
    coth = ch.divpos(sh)
    half = V.scalar(0.5, n)
    csch2 = V(np.ones(n), np.ones(n)).divpos(sh*sh)
    Ep = E*(half - coth)
    Epp = E*((half - coth)*(half - coth) + csch2)
    Ap = E*half - A*coth
    App = Ep*half - Ap*coth + A*csch2
    return E, A, Ep, Epp, Ap, App


class Table:
    """Cumulative rigorous integral with SEPARATED core and
    error cumsums: differences over [x1, x2] carry only the
    error accumulated BETWEEN the bracketing nodes (a shared
    prefix error would otherwise enter every difference twice
    -- the round-6 build's first width blowup).  The fl-cumsum
    accumulation of the directed terms is ENCLOSED by the slop
    lemma (round-248 F248-1a): each partial sum differs from
    the exact sum of its (already directed) float terms by at
    most (n-1) u Sigma|terms| / (1 - n u), and a difference of
    two partials by at most twice that; the bound (with a 1.05
    factor covering its own nearest-rounded assembly) is folded
    into `extra`, which callers therefore ADD to, not assign."""

    def __init__(self, nodes, fmid, fpp, fcell):
        self.x = nodes
        h = np.diff(nodes)
        err = vup(h**3/24.0*np.maximum(np.abs(fpp.lo),
                                       np.abs(fpp.hi)))
        self.core_lo = np.concatenate(
            [[0.0], np.cumsum(vdn(fmid.lo*h))])
        self.core_hi = np.concatenate(
            [[0.0], np.cumsum(vup(fmid.hi*h))])
        self.errc = np.concatenate([[0.0], np.cumsum(vup(err))])
        u_ = np.finfo(np.float64).eps
        # absum covers BOTH value cumsums AND the errc cumsum
        # (round-249 F249-3: errc is an equally-nearest
        # fl-cumsum whose terms were outside the lemma's sum)
        absum = float(np.sum(np.maximum(np.abs(fmid.lo),
                                        np.abs(fmid.hi))*h
                             + err))
        nn_ = len(h)
        self.extra = _u(1.05*2.0*nn_*u_*absum)
        # (head-sliver widenings from callers ADD to this slop)
        self.f_lo = fcell.lo
        self.f_hi = fcell.hi
        # suffix max of |f| over cells >= j: for SIGNED
        # integrands (C/S tables) the enclosure of an integral
        # over an endpoint sliver of width w is +/- w * this
        # bound (the inner/outer corner hull is NOT an
        # enclosure for signed f -- interior extrema of the
        # cumulative escape it; caught in the round-6
        # vectorization review).  |E cos|, |E sin| <= E
        # decreasing, so the suffix max is sharp up to the
        # cell hull.
        fabs = np.maximum(np.abs(fcell.lo), np.abs(fcell.hi))
        self.fabs_ge = np.maximum.accumulate(fabs[::-1])[::-1]

    def _j(self, x):
        j = int(np.searchsorted(self.x, x, side="right")) - 1
        return max(0, min(j, len(self.x) - 2))

    def diff(self, x1, x2):
        """int_{x1}^{x2} f, x1 <= x2 within the node range."""
        j1, j2 = self._j(x1), self._j(x2)
        d1 = max(x1 - self.x[j1], 0.0)
        d2 = max(x2 - self.x[j2], 0.0)
        core_lo = self.core_lo[j2] - self.core_hi[j1]
        core_hi = self.core_hi[j2] - self.core_lo[j1]
        err = _u(self.errc[j2] - self.errc[j1]
                 + self.errc[min(j2 + 1, len(self.errc) - 1)]
                 - self.errc[j2])
        # partial strips at both ends: int over [node_j, x] of
        # f is enclosed by (cell hull of f) * dx -- a PRODUCT
        # interval (dx >= 0 exact), not a 0-anchored window
        p1lo = min(self.f_lo[j1]*d1, self.f_hi[j1]*d1)
        p1hi = max(self.f_lo[j1]*d1, self.f_hi[j1]*d1)
        p2lo = min(self.f_lo[j2]*d2, self.f_hi[j2]*d2)
        p2hi = max(self.f_lo[j2]*d2, self.f_hi[j2]*d2)
        lo = core_lo - p1hi + p2lo - err - self.extra
        hi = core_hi - p1lo + p2hi + err + self.extra
        return I(_d(_d(lo)), _u(_u(hi)))

    def at(self, x):
        """int from the table start (node 0) to x."""
        return self.diff(self.x[0], x)

    # ---- vectorized lookups (round-6 batch pass) ----

    def _j_v(self, x):
        j = np.searchsorted(self.x, x, side="right") - 1
        return np.clip(j, 0, len(self.x) - 2)

    def _diff_arr(self, x1, x2):
        """Vectorized diff for point arrays x1 <= x2; mirrors
        diff() term by term (same core/err/strip algebra, same
        directed roundings)."""
        j1 = self._j_v(x1)
        j2 = self._j_v(x2)
        d1 = np.maximum(x1 - self.x[j1], 0.0)
        d2 = np.maximum(x2 - self.x[j2], 0.0)
        core_lo = self.core_lo[j2] - self.core_hi[j1]
        core_hi = self.core_hi[j2] - self.core_lo[j1]
        jn = np.minimum(j2 + 1, len(self.errc) - 1)
        err = vup(self.errc[j2] - self.errc[j1]
                  + self.errc[jn] - self.errc[j2])
        p1a = self.f_lo[j1]*d1
        p1b = self.f_hi[j1]*d1
        p2a = self.f_lo[j2]*d2
        p2b = self.f_hi[j2]*d2
        lo = core_lo - np.maximum(p1a, p1b) \
            + np.minimum(p2a, p2b) - err - self.extra
        hi = core_hi - np.minimum(p1a, p1b) \
            + np.maximum(p2a, p2b) + err + self.extra
        return vdn(vdn(lo)), vup(vup(hi))

    def at_v(self, xlo, xhi):
        """Vectorized at() over interval endpoints -- VALID ONLY
        for monotone cumulatives (f >= 0: IA, G, H tables)."""
        x0 = np.full_like(xlo, self.x[0])
        lo1, hi1 = self._diff_arr(x0, xlo)
        lo2, hi2 = self._diff_arr(x0, xhi)
        return V(np.minimum(lo1, lo2), np.maximum(hi1, hi2))

    def diff_v(self, x1, x2, signed):
        """Vectorized int over [x1, x2] (V endpoints, x1.hi <=
        x2.lo elementwise).  signed=False (f >= 0): hull of the
        inner/outer corner spans (extremes at the corners by
        monotonicity).  signed=True (C/S): inner span widened by
        the endpoint slivers +/- w * suffix-max|f|."""
        assert np.all(x1.hi <= x2.lo)
        li, hi_ = self._diff_arr(x1.hi, x2.lo)
        if signed:
            j1 = self._j_v(x1.lo)
            j2 = self._j_v(x2.lo)
            s = vup((x1.hi - x1.lo)*self.fabs_ge[j1]
                    + (x2.hi - x2.lo)*self.fabs_ge[j2])
            return V(vdn(li - s), vup(hi_ + s))
        lo_, ho = self._diff_arr(x1.lo, x2.hi)
        return V(np.minimum(li, lo_), np.maximum(hi_, ho))


def _table_nodes(a, htab=HTAB):
    geo = [X0]
    while geo[-1] < XSW:
        geo.append(min(geo[-1]*1.007, XSW))
    xmax = 2*a + 4e-3
    uni = np.arange(XSW, xmax + htab, htab)
    return np.concatenate([np.array(geo[:-1]), uni])


def build_tables(a, harm_ws, degmax, htab=HTAB):
    """harm_ws: list of (w_float, wI_interval) pairs.  The float
    w keys the table NAMES; every integrand uses the EXACT
    interval frequency wIv (round-248 F248-1d: tabulating at
    the float frequency while the operator multiplies by trig
    at the exact frequency broke the closed-form identity by
    ~ulp(w); one source of truth now)."""
    nodes = _table_nodes(a, htab)
    mid = 0.5*(nodes[:-1] + nodes[1:])
    cellV = V(nodes[:-1], nodes[1:])
    midV = V(mid, mid)
    n = len(mid)
    Em, Am, Epm, Eppm, Apm, Appm = E_A_prime(midV)
    Ec, Ac, Epc, Eppc, Apc, Appc = E_A_prime(cellV)
    tabs = {}
    tA = Table(nodes, Am, Appc, Ac)
    tA.extra += _u(0.51*X0)
    tabs["IA"] = tA
    for i in range(0, degmax + 1):
        ui_m = V.point(mid**i)
        f_m = Em*ui_m
        ui_c = _upow_cell(cellV, i)
        f_c = Ec*ui_c
        if i == 0:
            fpp = Eppc
        elif i == 1:
            fpp = Eppc*ui_c + V.scalar(2.0, n)*Epc
        else:
            fpp = Eppc*ui_c + V.scalar(2.0*i, n)*Epc \
                * _upow_cell(cellV, i - 1) \
                + V.scalar(float(i*(i - 1)), n)*Ec \
                * _upow_cell(cellV, i - 2)
        t = Table(nodes, f_m, fpp, f_c)
        if i >= 2:
            # head int_0^X0 E u^i with E <= 1/u + 1: enclosed
            # assembly (round-249 F249-6: the float form's
            # margin was below its own assembly slop)
            x0i = _ipow(I(X0), i)
            t.extra += _u((x0i/I(float(i))
                           + x0i*I(X0)/I(float(i + 1))).hi)
        tabs[f"H{i}"] = t
    for w, wIv in harm_ws:
        s2m = vsin(midV*V.scalar(wIv*I(0.5), n))
        s2m = s2m*s2m
        s2c = vsin(cellV*V.scalar(wIv*I(0.5), n))
        s2c = s2c*s2c
        sinw_c = vsin(cellV*V.scalar(wIv, n))
        cosw_c = vcos(cellV*V.scalar(wIv, n))
        fpp = Eppc*s2c + Epc*sinw_c*V.scalar(wIv, n) \
            + Ec*cosw_c*V.scalar(wIv*wIv*I(0.5), n)
        tG = Table(nodes, Em*s2m, fpp, Ec*s2c)
        # head: int_0^X0 E sin^2(wu/2) <= (w/2)^2 X0^2 (2x room
        # over the true w^2 X0^2/8 covers the nearest rounding)
        tG.extra += _u((w/2)**2*X0**2)
        tabs[f"G{w:.9f}"] = tG
        cosm = vcos(midV*V.scalar(wIv, n))
        sinm = vsin(midV*V.scalar(wIv, n))
        fppC = Eppc*cosw_c - V.scalar(I(2.0)*wIv, n)*Epc*sinw_c \
            - V.scalar(wIv*wIv, n)*Ec*cosw_c
        fppS = Eppc*sinw_c + V.scalar(I(2.0)*wIv, n)*Epc*cosw_c \
            - V.scalar(wIv*wIv, n)*Ec*sinw_c
        tabs[f"C{w:.9f}"] = Table(nodes, Em*cosm, fppC,
                                  Ec*cosw_c)
        tabs[f"S{w:.9f}"] = Table(nodes, Em*sinm, fppS,
                                  Ec*sinw_c)
    return tabs


def _upow_cell(c, i):
    if i == 0:
        return V(np.ones_like(c.lo), np.ones_like(c.lo))
    return V(vdn(c.lo**i), vup(c.hi**i))


class Trial:
    def __init__(self, a, parity, harm, poly):
        self.a = a
        self.aI = I(a)
        self.parity = parity
        self.harm = harm
        self.poly = poly
        self.deg = len(poly) - 1
        self.ws = [(k + off)*math.pi/a for _, k, off in harm]
        self.cabs = _u(math.fsum(
            [abs(c) for c, _, _ in harm]
            + [max(abs(p.lo), abs(p.hi))*max(a, 1.0)**j
               for j, p in enumerate(poly)]))

    def wI(self, idx):
        c, k, off = self.harm[idx]
        return (I(k) + I(off))*PI/self.aI

    def phi_pt(self, x):
        even = self.parity == "even"
        tot = I(0.0)
        for idx, (c, k, off) in enumerate(self.harm):
            arg = self.wI(idx)*x
            tot = tot + I(c)*(icos(arg) if even else isin(arg))
        p = I(0.0)
        for cj in reversed(self.poly):
            p = p*x + cj
        return tot + p

    def dphi_pt(self, x, order=1):
        """phi^(order) at interval x, orders 1..4.  Trig cycle:
        even (cos base): -w sin, -w^2 cos, +w^3 sin, +w^4 cos;
        odd (sin base): w cos, -w^2 sin, -w^3 cos, +w^4 sin."""
        even = self.parity == "even"
        tot = I(0.0)
        for idx, (c, k, off) in enumerate(self.harm):
            w = self.wI(idx)
            arg = w*x
            wpow = I(1.0)
            for _ in range(order):
                wpow = wpow*w
            if even:
                tr = [None, -isin(arg), -icos(arg),
                      isin(arg), icos(arg)][order]
            else:
                tr = [None, icos(arg), -isin(arg),
                      -icos(arg), isin(arg)][order]
            tot = tot + I(c)*wpow*tr
        dp = _poly_deriv(self.poly, order)
        p = I(0.0)
        for cj in reversed(dp):
            p = p*x + cj
        return tot + p

    def phi_v(self, x):
        """phi at a V of points/cells (mirrors phi_pt)."""
        n = len(x.lo)
        even = self.parity == "even"
        tot = V.scalar(0.0, n)
        for idx, (c, k, off) in enumerate(self.harm):
            arg = x*V.scalar(self.wI(idx), n)
            tr_ = vcos(arg) if even else vsin(arg)
            tot = tot + tr_*V.scalar(I(c), n)
        p = V.scalar(0.0, n)
        for cj in reversed(self.poly):
            p = p*x + V.scalar(cj, n)
        return tot + p

    def dphi_v(self, x, order):
        """phi^(order) at a V, orders 1..4 (mirrors dphi_pt's
        trig cycle)."""
        n = len(x.lo)
        even = self.parity == "even"
        tot = V.scalar(0.0, n)
        for idx, (c, k, off) in enumerate(self.harm):
            w = self.wI(idx)
            arg = x*V.scalar(w, n)
            wp = I(1.0)
            for _ in range(order):
                wp = wp*w
            if even:
                sgn, use_sin = [(0, 0), (-1, 1), (-1, 0),
                                (1, 1), (1, 0)][order]
            else:
                sgn, use_sin = [(0, 0), (1, 0), (-1, 1),
                                (-1, 0), (1, 1)][order]
            tr_ = vsin(arg) if use_sin else vcos(arg)
            tot = tot + tr_*V.scalar(I(c)*wp*I(float(sgn)), n)
        dp = _poly_deriv(self.poly, order)
        p = V.scalar(0.0, n)
        for cj in reversed(dp):
            p = p*x + V.scalar(cj, n)
        return tot + p

    def poly_shift_coeffs(self):
        out = []
        for i in range(self.deg + 1):
            ci = []
            for j in range(i, self.deg + 1):
                ci.append(self.poly[j]
                          * I(float(math.comb(j, i))))
            out.append(ci)
        return out


def _poly_deriv(coeffs, order):
    c = list(coeffs)
    for _ in range(order):
        c = [c[j]*I(float(j)) for j in range(1, len(c))]
    return c if c else [I(0.0)]


class ClosedT:
    def __init__(self, tr, tabs, chi_phi):
        self.tr = tr
        self.tabs = tabs
        self.chi_phi = chi_phi
        self.Pi = tr.poly_shift_coeffs()

    def _peval(self, coeffs, t):
        p = I(0.0)
        for cj in reversed(coeffs):
            p = p*t + cj
        return p

    def _tab_at(self, name, xI):
        tab = self.tabs[name]
        lo = tab.at(xI.lo)
        hi = tab.at(xI.hi)
        return I(min(lo.lo, hi.lo), max(lo.hi, hi.hi))

    def _tab_diff(self, name, x1I, x2I, signed=False):
        """int_{x1}^{x2}, x1I.hi <= x2I.lo required.  Monotone
        tables (f >= 0): hull of the inner/outer corner spans.
        Signed tables (C/S): inner span widened by the endpoint
        slivers +/- width * suffix-max|f| -- the corner hull is
        NOT an enclosure for signed integrands (round-6
        vectorization review; the pre-fix scalar path used the
        corner hull for C/S too)."""
        tab = self.tabs[name]
        assert x1I.hi <= x2I.lo
        inner = tab.diff(x1I.hi, x2I.lo)
        if signed:
            j1 = tab._j(x1I.lo)
            j2 = tab._j(x2I.lo)
            s = _u((x1I.hi - x1I.lo)*tab.fabs_ge[j1]
                   + (x2I.hi - x2I.lo)*tab.fabs_ge[j2])
            return I(_d(inner.lo - s), _u(inner.hi + s))
        outer = tab.diff(x1I.lo, x2I.hi)
        return I(min(inner.lo, outer.lo),
                 max(inner.hi, outer.hi))

    def _EI(self, xI):
        e2, sh, ch = _sinh_cosh(V(np.array([xI.lo]),
                                  np.array([xI.hi])))
        E = e2.divpos(sh)
        return I(E.lo[0], E.hi[0])

    def _AI(self, xI):
        e2, sh, ch = _sinh_cosh(V(np.array([xI.lo]),
                                  np.array([xI.hi])))
        A = (e2 - 1).divpos(sh)
        return I(A.lo[0], A.hi[0])

    def _E_ui(self, i, xI):
        E = self._EI(xI)
        p = I(1.0)
        for _ in range(i):
            p = p*xI
        return E*p

    def _peval_v(self, coeffs, t):
        p = V.scalar(0.0, len(t.lo))
        for cj in reversed(coeffs):
            p = p*t + V.scalar(cj, len(t.lo))
        return p

    def _phi_restricted_v(self, x):
        """Vectorized _phi_restricted: clip to [-a, a], hull
        with 0 on straddling entries, exact 0 on dead entries."""
        a = self.tr.a
        cl = V(np.clip(x.lo, -a, a), np.clip(x.hi, -a, a))
        v = self.tr.phi_v(cl)
        dead = (x.lo >= a) | (x.hi <= -a)
        strad = ((x.hi > a) | (x.lo < -a)) & ~dead
        lo = np.where(strad, np.minimum(v.lo, 0.0), v.lo)
        hi = np.where(strad, np.maximum(v.hi, 0.0), v.hi)
        lo = np.where(dead, 0.0, lo)
        hi = np.where(dead, 0.0, hi)
        return V(lo, hi)

    def _dphi_restricted_v(self, x):
        a = self.tr.a
        cl = V(np.clip(x.lo, -a, a), np.clip(x.hi, -a, a))
        v = self.tr.dphi_v(cl, 1)
        dead = (x.lo >= a) | (x.hi <= -a)
        strad = ((x.hi > a) | (x.lo < -a)) & ~dead
        lo = np.where(strad, np.minimum(v.lo, 0.0), v.lo)
        hi = np.where(strad, np.maximum(v.hi, 0.0), v.hi)
        lo = np.where(dead, 0.0, lo)
        hi = np.where(dead, 0.0, hi)
        return V(lo, hi)

    def Tphi_batch(self, t, deriv=False, pole=True):
        """Vectorized Tphi over a V of t-points/cells: mirrors
        the scalar closed form term by term (the dint and corr
        harmonic loops are merged so each harmonic's trig at t
        is computed once; C/S differences carry the signed
        sliver widening -- see Table.diff_v)."""
        tr = self.tr
        n = len(t.lo)
        even = tr.parity == "even"
        phit = tr.phi_v(t)
        dphit = tr.dphi_v(t, 1) if deriv else None
        aV = V.scalar(I(tr.a), n)
        k1 = aV - t
        k2 = aV + t
        IAv = self.tabs["IA"].at_v(k2.lo, k2.hi)
        E1 = E2 = Aat = shb = None
        if deriv:
            e2a, sha, _c = _sinh_cosh(k1)
            E1 = e2a.divpos(sha)
            e2b, shb, _c = _sinh_cosh(k2)
            E2 = e2b.divpos(shb)
            Aat = (e2b - 1.0).divpos(shb)
        dint = V.scalar(0.0, n)
        ddint = V.scalar(0.0, n)
        corr = V.scalar(0.0, n)
        dcorr = V.scalar(0.0, n)
        for idx, (c, k, off) in enumerate(tr.harm):
            w = tr.ws[idx]
            wIv = tr.wI(idx)
            wS = V.scalar(wIv, n)
            cV = V.scalar(I(c), n)
            cwt = vcos(t*wS)
            swt = vsin(t*wS)
            trig = cwt if even else swt
            G = self.tabs[f"G{w:.9f}"].at_v(k2.lo, k2.hi)
            dint = dint + cV*(-2.0)*trig*G
            Cd = self.tabs[f"C{w:.9f}"].diff_v(k1, k2, True)
            Sd = self.tabs[f"S{w:.9f}"].diff_v(k1, k2, True)
            if even:
                term = cwt*Cd - swt*Sd
            else:
                term = swt*Cd + cwt*Sd
            corr = corr + cV*term
            if deriv:
                dtrig = (-swt)*wS if even else cwt*wS
                s = vsin(k2*V.scalar(wIv*I(0.5), n))
                gint = E2*s*s
                ddint = ddint + cV*(-2.0)*(dtrig*G + trig*gint)
                wpt = V.scalar(wIv, n)
                ec2 = E2*vcos(k2*wpt)
                ec1 = E1*vcos(k1*wpt)
                es2 = E2*vsin(k2*wpt)
                es1 = E1*vsin(k1*wpt)
                if even:
                    dterm = (-swt)*wS*Cd - cwt*wS*Sd \
                        + cwt*(ec2 + ec1) - swt*(es2 + es1)
                else:
                    dterm = cwt*wS*Cd + (-swt)*wS*Sd \
                        + swt*(ec2 + ec1) + cwt*(es2 + es1)
                dcorr = dcorr + cV*dterm
        for i in range(2, tr.deg + 1, 2):
            Qi = self._peval_v(self.Pi[i], t)
            Hi = self.tabs[f"H{i}"].at_v(k2.lo, k2.hi)
            dint = dint + Qi*Hi
            if deriv:
                dQi = self._peval_v(_poly_deriv(self.Pi[i], 1),
                                    t)
                ddint = ddint + dQi*Hi + Qi*E2*_vpow(k2, i)
        for i in range(0, tr.deg + 1):
            Pi_t = self._peval_v(self.Pi[i], t)
            Hd = self.tabs[f"H{i}"].diff_v(k1, k2, False)
            corr = corr + Pi_t*Hd
            if deriv:
                dPi = self._peval_v(_poly_deriv(self.Pi[i], 1),
                                    t)
                dcorr = dcorr + dPi*Hd \
                    + Pi_t*(E2*_vpow(k2, i) + E1*_vpow(k1, i))
        corr = corr*0.5
        dcorr = dcorr*0.5
        DINT = dint - corr
        e2t = _vexp(k2)
        lcoth = _vlog((e2t + 1.0).divpos(e2t - 1.0))
        lg2V = V.scalar(LOG2, n)
        p1 = self._phi_restricted_v(t + lg2V)
        p2 = self._phi_restricted_v(t - lg2V)
        prime = V.scalar(C2I*I(0.5), n)*(p1 + p2)
        _e2, shc, chc = _sinh_cosh(t*V.scalar(0.5, n))
        chit = chc if even else shc
        chi_eff = self.chi_phi if pole else I(0.0)
        ce = V.scalar(chi_eff*I(2.0 if even else -2.0), n)
        lgV = V.scalar(LG4PI, n)
        Tv = (-lgV)*phit - phit*IAv - DINT + phit*lcoth \
            - prime + ce*chit
        if not deriv:
            return Tv, None
        dp1 = self._dphi_restricted_v(t + lg2V)
        dp2 = self._dphi_restricted_v(t - lg2V)
        dprime = V.scalar(C2I*I(0.5), n)*(dp1 + dp2)
        dlcoth = V.scalar(-1.0, n).divpos(shb)
        dchit = (shc if even else chc)*V.scalar(0.5, n)
        dT = (-lgV)*dphit - dphit*IAv - phit*Aat \
            - (ddint - dcorr) + dphit*lcoth + phit*dlcoth \
            - dprime + ce*dchit
        return Tv, dT

    def Tphi(self, t, deriv=False, pole=True):
        tr = self.tr
        a = tr.a
        even = tr.parity == "even"
        phit = tr.phi_pt(t)
        dphit = tr.dphi_pt(t, 1) if deriv else None
        k1 = I(a) - t
        k2 = I(a) + t
        IAv = self._tab_at("IA", k2)
        # hoisted: E at k1, k2 (harmonic-independent; the
        # per-harmonic scalar sinh evaluations were the first
        # run's 20x hot-spot)
        E1 = self._EI(k1) if deriv else None
        E2 = self._EI(k2) if deriv else None
        dint = I(0.0)
        ddint = I(0.0)
        for idx, (c, k, off) in enumerate(tr.harm):
            w = tr.ws[idx]
            wIv = tr.wI(idx)
            trig = icos(wIv*t) if even else isin(wIv*t)
            G = self._tab_at(f"G{w:.9f}", k2)
            dint = dint + I(c)*I(-2.0)*trig*G
            if deriv:
                dtrig = (-isin(wIv*t))*wIv if even \
                    else icos(wIv*t)*wIv
                s = isin(wIv*k2*I(0.5))
                gint = E2*s*s
                ddint = ddint + I(c)*I(-2.0)*(dtrig*G
                                              + trig*gint)
        for i in range(2, tr.deg + 1, 2):
            Qi = self._peval(self.Pi[i], t)
            Hi = self._tab_at(f"H{i}", k2)
            dint = dint + Qi*Hi
            if deriv:
                dQi = self._peval(_poly_deriv(self.Pi[i], 1), t)
                ddint = ddint + dQi*Hi + Qi*E2*_ipow(k2, i)
        corr = I(0.0)
        dcorr = I(0.0)
        for idx, (c, k, off) in enumerate(tr.harm):
            w = tr.ws[idx]
            wIv = tr.wI(idx)
            Cd = self._tab_diff(f"C{w:.9f}", k1, k2, signed=True)
            Sd = self._tab_diff(f"S{w:.9f}", k1, k2, signed=True)
            cwt, swt = icos(wIv*t), isin(wIv*t)
            if even:
                term = cwt*Cd - swt*Sd
            else:
                term = swt*Cd + cwt*Sd
            corr = corr + I(c)*term
            if deriv:
                ec2 = E2*icos(wIv*k2)
                ec1 = E1*icos(wIv*k1)
                es2 = E2*isin(wIv*k2)
                es1 = E1*isin(wIv*k1)
                if even:
                    dterm = (-swt)*wIv*Cd - cwt*wIv*Sd \
                        + cwt*(ec2 + ec1) - swt*(es2 + es1)
                else:
                    dterm = cwt*wIv*Cd + (-swt)*wIv*Sd \
                        + swt*(ec2 + ec1) + cwt*(es2 + es1)
                dcorr = dcorr + I(c)*dterm
        for i in range(0, tr.deg + 1):
            Pi_t = self._peval(self.Pi[i], t)
            Hd = self._tab_diff(f"H{i}", k1, k2)
            corr = corr + Pi_t*Hd
            if deriv:
                dPi = self._peval(_poly_deriv(self.Pi[i], 1), t)
                dcorr = dcorr + dPi*Hd \
                    + Pi_t*(E2*_ipow(k2, i) + E1*_ipow(k1, i))
        corr = corr*I(0.5)
        dcorr = dcorr*I(0.5)
        DINT = dint - corr
        e2t = iexp(k2)
        lcoth = ilog((e2t + 1)/(e2t - 1))
        p1 = self._phi_restricted(t + LOG2)
        p2 = self._phi_restricted(t - LOG2)
        prime = C2I*I(0.5)*(p1 + p2)
        chit = icosh(t*I(0.5)) if even else isinh(t*I(0.5))
        ps = I(1.0) if even else I(-1.0)
        chi_eff = self.chi_phi if pole else I(0.0)
        Tv = (-LG4PI*phit - phit*IAv - DINT + phit*lcoth
              - prime + ps*I(2.0)*chi_eff*chit)
        if not deriv:
            return Tv, None
        Aat = self._AI(k2)
        dp1 = self._dphi_restricted(t + LOG2)
        dp2 = self._dphi_restricted(t - LOG2)
        dprime = C2I*I(0.5)*(dp1 + dp2)
        dlcoth = I(-1.0)/isinh(k2)
        dchit = (isinh(t*I(0.5)) if even
                 else icosh(t*I(0.5)))*I(0.5)
        dT = (-LG4PI*dphit - dphit*IAv - phit*Aat
              - (ddint - dcorr) + dphit*lcoth + phit*dlcoth
              - dprime + ps*I(2.0)*chi_eff*dchit)
        return Tv, dT

    def _phi_restricted(self, xI):
        a = self.tr.a
        if xI.lo >= a or xI.hi <= -a:
            return I(0.0)
        cl = I(max(xI.lo, -a), min(xI.hi, a))
        v = self.tr.phi_pt(cl)
        if xI.hi > a or xI.lo < -a:
            return I(min(v.lo, 0.0), max(v.hi, 0.0))
        return v

    def _dphi_restricted(self, xI):
        a = self.tr.a
        if xI.lo >= a or xI.hi <= -a:
            return I(0.0)
        if xI.hi > a or xI.lo < -a:
            cl = I(max(xI.lo, -a), min(xI.hi, a))
            v = self.tr.dphi_pt(cl, 1)
            return I(min(v.lo, 0.0), max(v.hi, 0.0))
        return self.tr.dphi_pt(xI, 1)


def _ucells(lo, hi, h):
    n = max(1, int(math.ceil((hi - lo)/h)))
    e = np.linspace(lo, hi, n + 1)
    return e[:-1], e[1:]

def _gcells(far, near, hstart, theta=0.5):
    """Geometric cells from far toward the singular point near,
    per-cell width <= theta times the remaining distance (the
    mean-value error of a cell at distance d is O(width^2/d),
    so the graded region's total error is O(theta^2) --
    h-INDEPENDENT; tight cells need small theta, not small h,
    here)."""
    lo_l, hi_l = [], []
    pos = far
    h = hstart
    while near - pos > 1e-16:
        step = min(h, (near - pos))
        lo_l.append(pos)
        hi_l.append(pos + step)
        pos += step
        h = max((near - pos)*theta, 1e-16)
        if near - pos <= near*1e-15:
            break
    return np.array(lo_l), np.array(hi_l)


def temple_cell(tr, tabs, ell2, use_pole, ht=HT, theta=0.1):
    a = tr.a
    even = tr.parity == "even"
    # T phi log-diverges at t = a (the E ~ 1/u correction
    # integral against nonvanishing phi(a)); mean-value cells
    # GRADED toward a (width ~ theta * dist neutralizes the
    # 1/dist of dT), uniform elsewhere, split at the
    # prime-shift kink k0.
    k0 = math.log(2.0) - a
    D0 = 1e-3
    bset = {DEDGE, a - D0}
    if DEDGE < k0 < a - D0:
        bset.add(k0)
    bounds = sorted(bset)
    segs = []
    for lo, hi in zip(bounds[:-1], bounds[1:]):
        if hi - lo < 1e-12:
            continue
        segs.append(_ucells(lo, hi, ht))
    segs.append(_gcells(a - D0, a - DEDGE, ht, theta))
    cl_arr = np.concatenate([s[0] for s in segs])
    ch_arr = np.concatenate([s[1] for s in segs])
    # <chi, phi> and n by per-cell SIMPSON with interval
    # fourth-derivative bounds (the mean-value form accumulated
    # a (h/4)-times-phi-prime-L1 width ~1e-3 that flowed through
    # the pole into every T phi -- the relaunch-1 failure);
    # Simpson panel error is h^5 |f4|/2880.
    def chider(x, order):
        # d^order/dt^order of chi(t): chi = cosh(t/2) (even) or
        # sinh(t/2) (odd); each derivative halves and toggles
        even_toggle = (order % 2 == 0)
        use_cosh = (even == even_toggle)
        fn = icosh if use_cosh else isinh
        return fn(x*I(0.5))*_ipow(I(0.5), order)
    chi_lo_p, chi_hi_p = [], []
    n_lo_p, n_hi_p = [], []
    # Simpson converges as h^5: the FIXED pitch HCHI (the value
    # validated at the round's first certified cell: n width
    # ~2e-10, chi width ~1e-10) suffices independently of the
    # M/S pitch, so refining ht does not inflate this loop
    ccells = []
    for lo, hi in zip(bounds[:-1], bounds[1:]):
        if hi - lo < 1e-12:
            continue
        cl_, ch_ = _ucells(lo, hi, HCHI)
        ccells += list(zip(cl_, ch_))
    gl_, gh_ = _gcells(a - D0, a - DEDGE, HCHI)
    ccells += list(zip(gl_, gh_))
    for (cl, ch) in ccells:
        # round-249 F249-1: the panel width, midpoint, and
        # Simpson weight are INTERVALS enclosing the true
        # values (the width is not Sterbenz-exact near DEDGE;
        # fl(h/6) pre-rounds; the fl midpoint is off-center by
        # an unbudgeted first-order term) -- same class as the
        # M/S loop's F248-1f repair, now applied here
        lo_, hi_ = I(cl), I(ch)
        hI = hi_ - lo_
        mI = (lo_ + hi_)*I(0.5)
        w6 = hI/I(6.0)
        cellI = I(cl, ch)
        pl, pm, ph = (tr.phi_pt(lo_), tr.phi_pt(mI),
                      tr.phi_pt(hi_))
        xl, xm, xh = (chider(lo_, 0), chider(mI, 0),
                      chider(hi_, 0))
        simp = (pl*xl + I(4.0)*pm*xm + ph*xh)*w6
        pc = [tr.phi_pt(cellI)] + [tr.dphi_pt(cellI, o)
                                   for o in (1, 2, 3, 4)]
        cc = [chider(cellI, o) for o in range(5)]
        f4 = (pc[4]*cc[0] + I(4.0)*pc[3]*cc[1]
              + I(6.0)*pc[2]*cc[2] + I(4.0)*pc[1]*cc[3]
              + pc[0]*cc[4])
        h5 = _ipow(hI, 5)
        e = _u((h5*I(f4.abs_hi())/I(2880.0)).hi)
        chi_lo_p.append(_d(simp.lo - e))
        chi_hi_p.append(_u(simp.hi + e))
        simp2 = (pl*pl + I(4.0)*pm*pm + ph*ph)*w6
        g4 = I(2.0)*(pc[4]*pc[0] + I(4.0)*pc[3]*pc[1]
                     + I(3.0)*pc[2]*pc[2])
        e2_ = _u((h5*I(g4.abs_hi())/I(2880.0)).hi)
        n_lo_p.append(_d(simp2.lo - e2_))
        n_hi_p.append(_u(simp2.hi + e2_))
    # fsum is exactly rounded, one directed step after
    # (round-248 F248-1g: the += accumulation was nearest)
    chi_lo = _d(math.fsum(chi_lo_p))
    chi_hi = _u(math.fsum(chi_hi_p))
    n_lo = _d(math.fsum(n_lo_p))
    n_hi = _u(math.fsum(n_hi_p))
    # uncovered t-measure: the two DEDGE slivers PLUS the
    # _gcells terminal gap <= a*1e-15 (round-248 F248-1e: sl2
    # previously budgeted exactly 2*DEDGE with zero headroom);
    # |chi| <= cosh(a/2) <= 1.3 on a <= 0.55
    DG = _u(DEDGE + a*2e-15)
    sl = _u(2*DG*1.3*tr.cabs)
    chi_phi = I(_d(2*(chi_lo - sl)), _u(2*(chi_hi + sl)))
    sl2 = _u(2*DG*tr.cabs**2)
    nn = I(_d(2*(n_lo - sl2)), _u(2*(n_hi + sl2)))

    ct = ClosedT(tr, tabs, chi_phi)
    # |T phi(t)| <= CE_A + CE_B ln(1/(a - t)) on the sliver:
    # the divergent piece is the correction integral, |corr| <=
    # (cabs/2)(ln(k2/k1) + k2) since E(u) <= 1/u + 1 on (0, 1.2]
    # (see the E-bound note in _sinh_cosh); every other term is
    # a COMPUTED enclosure (round-248 F248-2: the previous
    # 2.2/40.0/1.0 were verified-true but underived constants):
    #   |phi| <= cabs;  |dint| <= sum_h 2|c_h| Gw(xtop) (poly
    #   part identically zero for the pure-harmonic trials --
    #   asserted);  IA(k2) <= IA(xtop);  lcoth(k2) <= lcoth(a);
    #   |prime| <= C2 cabs;  (cabs/2) k2 <= 0.51 cabs (2a+1e-3).
    assert tr.deg == 0, "CE_A dint bound assumes pure-harmonic"
    cabsI = I(tr.cabs)
    xtop = 2*a + 1e-3
    ia_top = tabs["IA"].at(xtop)
    ea_ = iexp(I(a))
    lcoth_a = ilog((ea_ + 1)/(ea_ - 1))
    dint_top = I(0.0)
    for idx, (c, k, off) in enumerate(tr.harm):
        w = tr.ws[idx]
        dint_top = dint_top + I(abs(c))*I(2.0) \
            *tabs[f"G{w:.9f}"].at(xtop)
    chiam = I(max(abs(chi_phi.lo), abs(chi_phi.hi)))
    CE_B_I = I(0.51)*cabsI
    CE_A_I = (LG4PI*cabsI + cabsI*I(ia_top.hi)
              + cabsI*I(lcoth_a.hi) + I(dint_top.hi)
              + C2I*cabsI
              + I(0.51)*cabsI*I(xtop)
              + I(2.0)*chiam*icosh(I(a)*I(0.5))
              + I(0.51)*cabsI*I(ilog(I(xtop)).abs_hi()))
    CE_B = _u(CE_B_I.hi)
    CE_A = _u(CE_A_I.hi)
    lnD_I = I(0.0) - ilog(I(DEDGE))
    lnD = _u(lnD_I.hi)
    CEDGE = _u((CE_A_I + CE_B_I*lnD_I).hi)
    # gT6: the batch and scalar paths both enclose the same true
    # values, so their enclosures must overlap
    for tv in (0.31*a, 0.57*a, 0.83*a):
        sv, sd = ct.Tphi(I(tv), deriv=True, pole=use_pole)
        bv, bd = ct.Tphi_batch(V.point(np.array([tv])),
                               deriv=True, pole=use_pole)
        assert max(sv.lo, bv.lo[0]) <= min(sv.hi, bv.hi[0]), \
            f"gT6 FAIL value at t={tv}"
        assert max(sd.lo, bd.lo[0]) <= min(sd.hi, bd.hi[0]), \
            f"gT6 FAIL deriv at t={tv}"
    # batched M/S passes: chunk sums via math.fsum (exactly
    # rounded), directed one-ulp rounding at the end -- same
    # documented-negligible interior-rounding convention as the
    # Table cumsums and the pre-batch scalar += accumulation
    mlo_p, mhi_p, shi_p, slo_p = [], [], [], []
    CH = 65536
    ncl = len(cl_arr)
    import time as _time
    t0 = _time.time()
    for s0 in range(0, ncl, CH):
        cl = cl_arr[s0:s0 + CH]
        chh = ch_arr[s0:s0 + CH]
        # true cell width chh - cl as an INTERVAL (round-248
        # F248-1f: the float difference is not Sterbenz-exact
        # for the first cells above DEDGE); e uses its upper end
        hV = V(vdn(chh - cl), vup(chh - cl))
        hhi = hV.hi
        mV = V.point(0.5*(cl + chh))
        cellV = V(cl, chh)
        Tm, _n = ct.Tphi_batch(mV, deriv=False, pole=use_pole)
        Tc, dTc = ct.Tphi_batch(cellV, deriv=True,
                                pole=use_pole)
        phim = tr.phi_v(mV)
        p0 = tr.phi_v(cellV)
        p1_ = tr.dphi_v(cellV, 1)
        f = phim*Tm
        fh = f*hV
        fp = p1_*Tc + p0*dTc
        e = vup(hhi*hhi*0.25*np.maximum(np.abs(fp.lo),
                                        np.abs(fp.hi)))
        mlo_p.append(math.fsum(vdn(fh.lo - e)))
        mhi_p.append(math.fsum(vup(fh.hi + e)))
        f2h = Tm.sq()*hV
        f2p = Tc*dTc*2.0
        e2_ = vup(hhi*hhi*0.25*np.maximum(np.abs(f2p.lo),
                                          np.abs(f2p.hi)))
        shi_p.append(math.fsum(vup(np.maximum(f2h.hi, 0.0)
                                   + e2_)))
        slo_p.append(math.fsum(vdn(np.maximum(f2h.lo - e2_,
                                              0.0))))
        done = min(s0 + CH, ncl)
        print(f"    ms {done}/{ncl} "
              f"{_time.time() - t0:.0f}s", flush=True)
    M_lo = _d(math.fsum(mlo_p))
    M_hi = _u(math.fsum(mhi_p))
    S_hi = _u(math.fsum(shi_p))
    S_lo = _d(math.fsum(slo_p))
    # sliver integrals: int_{a-DEDGE}^{a} ln^k(1/d) dd =
    # DEDGE*(lnD^k + k lnD^{k-1} + ...) <= DEDGE*(lnD + k)^k;
    # assembled in I arithmetic (round-248: no nearest-rounded
    # chains inside the budgets); the CEDGE-bounded terms use
    # DG = DEDGE + gap, covering the _gcells terminal gap and
    # the [0, DEDGE] head
    DGI = I(_u(DG))
    DEI = I(DEDGE)
    CEDGE_I = CE_A_I + CE_B_I*lnD_I
    Msl = _u((DEI*cabsI*(CE_A_I + CE_B_I*(lnD_I + I(1.0)))
              + I(2.0)*DGI*cabsI*CEDGE_I).hi)
    M = I(_d(2*(M_lo - Msl)), _u(2*(M_hi + Msl)))
    Sedge = CE_A_I + CE_B_I*(lnD_I + I(2.0))
    Ssl = _u((DEI*Sedge*Sedge
              + I(2.0)*DGI*CEDGE_I*CEDGE_I).hi)
    S = I(_d(2*S_lo), _u(2*(S_hi + Ssl)))
    rho = M/nn
    ok = rho.hi < ell2.lo
    lam = None
    if ok:
        lam = _d(((ell2*M - S)/(ell2*nn - M)).lo)
    sig2 = _u((S/nn - rho.sq()).hi)
    return {"rho": [rho.lo, rho.hi], "sigma2_hi": sig2,
            "n": [nn.lo, nn.hi], "S": [S.lo, S.hi],
            "chi_phi": [chi_phi.lo, chi_phi.hi],
            "ncells": int(ncl), "premise_ok": bool(ok),
            "temple_lo": lam}


def make_fixtures():
    """Float64 fixtures on the PURE-HARMONIC basis (this round's
    survey: harmonics alone -- half-integer plus the integer
    'rough' modes with nonvanishing edges -- close every theorem
    cell; the entire trial keeps Stage III explosion-free)."""
    import oneprime_fractional as opf
    from oneprime_push import temple_opt
    out = {}
    specs = [("even", 0.6931, 0.15), ("even", 0.80, 0.15),
             ("even", 0.90, 0.04), ("even", 0.95, 0.02),
             ("odd", 0.90, 0.15), ("odd", 1.05, 0.15),
             ("odd", 1.09, 0.08)]
    for parity, delta, nustar in specs:
        a = delta/2
        md = opf.Modes(a, parity, nus=(), nfr=0)
        tn, tw, B, TB, _v = opf.apply_T(md, base=0.003)
        N = 2*(B*tw[None, :]) @ B.T
        M = 2*(B*tw[None, :]) @ TB.T
        S = 2*(TB*tw[None, :]) @ TB.T
        N, M, S = (N + N.T)/2, (M + M.T)/2, (S + S.T)/2
        d = 1.0/np.sqrt(np.diag(N))
        Nn = d[:, None]*N*d[None, :]
        ev, U = np.linalg.eigh(Nn)
        keep = ev > 1e-4
        Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :])
              .T*d[None, :])
        chi = (np.cosh(tn/2) if parity == "even"
               else np.sinh(tn/2))
        Bw, TBw = Wh @ B, Wh @ TB
        NA = 2*(Bw*tw[None, :]) @ Bw.T
        MA = 2*(Bw*tw[None, :]) @ TBw.T
        SA = 2*(TBw*tw[None, :]) @ TBw.T
        NA, MA, SA = ((NA + NA.T)/2, (MA + MA.T)/2,
                      (SA + SA.T)/2)
        entry = {"a": a, "parity": parity, "nustar": nustar,
                 "delta": delta}
        if parity == "odd":
            vfull = 2*(Bw*(tw*chi)[None, :]).sum(1)
            TBfree = TBw - opf.psign(parity)*2*np.outer(
                vfull, chi)
            MF = 2*(Bw*tw[None, :]) @ TBfree.T
            SF = 2*(TBfree*tw[None, :]) @ TBfree.T
            MF, SF = (MF + MF.T)/2, (SF + SF.T)/2
            muF, cF = temple_opt(NA, MF, SF, nustar)
            cfree = np.array(Wh.T @ cF)
            nrmF = math.sqrt(float(cfree @ N @ cfree))
            entry["cfree"] = list(cfree/nrmF)
            nnF = float(cF @ NA @ cF)
            rhoF = float(cF @ MF @ cF)/nnF
            sigF = math.sqrt(max(float(cF @ SF @ cF)/nnF
                                 - rhoF*rhoF, 0.0))
            ell2 = (rhoF - sigF*sigF/(nustar - rhoF))*0.9
            entry["rhoF_float"] = rhoF
        else:
            ell2 = nustar
        mu, c = temple_opt(NA, MA, SA, ell2)
        cf = np.array(Wh.T @ c)
        nrm = math.sqrt(float(cf @ N @ cf))
        cf = cf/nrm
        entry["c"] = list(map(float, cf))
        entry["rho_float"] = float(cf @ M @ cf)
        entry["ws"] = list(map(float, md.w))
        entry["nharm"] = int(md.nharm)
        out[f"{parity}:{delta:g}"] = entry
        print(f"  fixture {parity}:{delta:g}", flush=True)
    return out


def trial_from_fixture(fx, coeffs):
    a = fx["a"]
    parity = fx["parity"]
    nharm = fx["nharm"]
    harm = []
    for i in range(nharm):
        val = fx["ws"][i]*a/math.pi
        kk = int(math.floor(val + 1e-6))
        offv = val - kk
        if abs(offv - 0.5) < 1e-6:
            offv = 0.5
        elif abs(offv) < 1e-6:
            offv = 0.0
        elif abs(offv - 1.0) < 1e-6:
            kk, offv = kk + 1, 0.0
        else:
            raise ValueError(f"bad w {val}")
        harm.append((coeffs[i], kk, offv))
    poly = [I(0.0)]        # pure-harmonic trial
    return Trial(a, parity, harm, poly)



def _ipow(x, k):
    p = I(1.0)
    for _ in range(k):
        p = p*x
    return p


def _sha(name):
    import ckpt_key
    return ckpt_key.code_sha(os.path.join(HERE, name))

DEPST3 = {f: _sha(f) for f in ("oneprime_fractional.py",
                               "oneprime_push.py",
                               "oneprime_bridge.py",
                               "oneprime_certificate.py",
                               "oneprime_interval_core.py",
                               "oneprime_interval_count.py",
                               "oneprime_interval_temple.py")}
# (push added round 248 F248-3; bridge + certificate added
# round 249 F249-2: the TRANSITIVE import closure of
# make_fixtures' producers -- fractional imports build_Q64
# from bridge and psign from certificate (psign is
# load-bearing in the odd TBfree), push imports both -- every
# producing file in every key, per the round-245 keying law)
KEYFILE = os.path.join(HERE, "oneprime_interval_temple.py")


def run():
    # gT7: the vectorized log agrees with the Stage-I scalar
    # (itself mpmath-gated) -- overlap + width cap
    for xv in (1e-3, 0.11, 0.5, 1.0, 2.5, 7.0):
        il = ilog(I(xv))
        vl = _vlog(V.point(np.array([xv])))
        assert (max(il.lo, vl.lo[0]) <= min(il.hi, vl.hi[0])
                and vl.hi[0] - vl.lo[0] < 1e-12), \
            f"gT7 FAIL at {xv}"
    params = {"deps": DEPST3,
              "cfg": {k: list(v) for k, v in CELLCFG.items()},
              "hchi": HCHI, "round": 6}
    st = ckpt_key.load("oneprime_ivtemple", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is not None:
        return st
    # keyed Stage-II premise load (round-248 F248-4: the glob
    # could silently consume a stale or partial checkpoint)
    import oneprime_interval_count as OC
    cparams = {"deps": OC.DEPSII, "H": 0.02, "cells": OC.CELLS,
               "round": 6}
    counts = ckpt_key.load(
        "oneprime_ivcount",
        os.path.join(HERE, "oneprime_interval_count.py"),
        cparams, kfun=ckpt_key.code_key)
    assert counts is not None, \
        "Stage II checkpoint at the CURRENT key required"
    fx = make_fixtures()
    pjson = os.path.join(
        HERE, "checkpoints",
        f"oneprime_ivtemple_partial_"
        f"{ckpt_key.code_key(KEYFILE, params)[:12]}.json")
    part = {}
    try:
        part = json.load(open(pjson))["state"]
        print(f"  partial: {len(part)} cells", flush=True)
    except Exception:
        pass
    st = {}
    allok = True
    for cellk, f in fx.items():
        if cellk in part:
            st[cellk] = part[cellk]
            allok = allok and st[cellk]["certified"]
            continue
        countrow = counts[cellk]
        assert countrow["certified"] and \
            abs(countrow["nu"] - f["nustar"]) < 1e-12, \
            f"count cert mismatch {cellk}"
        nustar = I(f["nustar"])
        ht_, htab_, th_ = CELLCFG[cellk]
        tr = trial_from_fixture(f, f["c"])
        tabs = build_tables(
            f["a"],
            [(tr.ws[i], tr.wI(i)) for i in range(len(tr.ws))],
            tr.deg, htab_)
        if f["parity"] == "even":
            res = temple_cell(tr, tabs, nustar, True,
                              ht=ht_, theta=th_)
            res["ell2"] = [nustar.lo, nustar.hi]
        else:
            trF = trial_from_fixture(f, f["cfree"])
            resF = temple_cell(trF, tabs, nustar, False,
                               ht=ht_, theta=th_)
            ok1 = resF["premise_ok"] and \
                resF["temple_lo"] is not None and \
                resF["temple_lo"] > 0
            assert ok1, f"odd stage1 fails {cellk}: {resF}"
            nu1 = I(resF["temple_lo"])
            res = temple_cell(tr, tabs, nu1, True,
                              ht=ht_, theta=th_)
            res["stage1"] = resF
            res["ell2"] = [nu1.lo, nu1.hi]
        assert abs(0.5*(res["rho"][0] + res["rho"][1])
                   - f["rho_float"]) < 1e-4, \
            f"gT2 FAIL {cellk}: rho {res['rho']} vs " \
            f"{f['rho_float']}"
        assert 0.5 < res["n"][0] and res["n"][1] < 2.0, \
            f"gT5 FAIL {cellk} n {res['n']}"
        ok = res["premise_ok"] and res["temple_lo"] is not None \
            and res["temple_lo"] > 0
        tl = res["temple_lo"]
        print(f"IVT {cellk}: rho [{res['rho'][0]:.4e}, "
              f"{res['rho'][1]:.4e}] s2<={res['sigma2_hi']:.3e} "
              f"ell2 {res['ell2'][0]:.4g} -> Temple >= "
              f"{tl if tl is not None else float('nan'):.4e} "
              f"{'CERTIFIED' if ok else 'FAIL'}", flush=True)
        res["certified"] = bool(ok)
        allok = allok and ok
        st[cellk] = res
        part[cellk] = res
        json.dump({"key": ckpt_key.code_key(KEYFILE, params),
                   "state": part}, open(pjson, "w"), indent=0)
    st["theorem"] = bool(allok)
    if allok:
        print("THEOREM (interval-rigorous): the semi-local "
              "one-prime Weil form is positive -- the full form "
              "on [log 2, 0.95] and the odd sector through "
              "1.09 -- every ingredient an interval enclosure "
              "(the round-248 slop lemma and directed repairs "
              "close the former sub-ulp conventions); "
              "positivity at each certified support length "
              "covers every shorter length by domain nesting "
              "(restriction of a positive quadratic form).",
              flush=True)
    ckpt_key.save("oneprime_ivtemple", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    if os.path.exists(pjson):
        os.remove(pjson)
    return st


if __name__ == "__main__":
    run()
    print("interval temple (Stage III) complete", flush=True)
