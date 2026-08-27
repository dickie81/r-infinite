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
(HTAB), per-cell midpoint + f''-interval corrections
(integrands elementary; E'', A'' explicit).  t-integrals:
uniform cells (HT), midpoint + correction |int - f(m) h| <=
(h^2/4)|f'(cell)| with f' from the closed form (mean-value
form; first derivatives only), cells split at the kink
t = log2 - a; the DEDGE edge slivers are bounded crudely.

GATES:
  gT2  wiring: rho = M/n tracks the float64 fixture rho within
       1e-4 (the float pipeline has its own quadrature error).
  gT3  the Temple certificate per cell with premises
       (M/n < ell2 rigorously; odd stage-one nu1 > 0).
  gT5  normalization sanity: n in [0.5, 2] (the fixture
       normalizes to n = 1 in float64).

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

X0 = 1e-11
XSW = 1e-3
HTAB = 1e-5
HT = 5e-5
DEDGE = 1e-9    # > 10*X0: k1 = a - t stays in table range


def _vexp_end(x, side):
    n = np.round(x/0.6931471805599453)
    sV = V.point(x) - V(np.full_like(x, LOG2.lo),
                        np.full_like(x, LOG2.hi))*V.point(n)
    K = 22
    term = V(np.ones_like(x), np.ones_like(x))
    tot = V(np.ones_like(x), np.ones_like(x))
    for k in range(1, K):
        term = term*sV*V.scalar(1.0/k, len(x))
        tot = tot + term
    m = np.maximum(np.abs(sV.lo), np.abs(sV.hi))
    rem = vup((m**K)/math.factorial(K)/(1 - m/(K + 1)))
    lo = np.ldexp(vdn(tot.lo - rem), n.astype(int))
    hi = np.ldexp(vup(tot.hi + rem), n.astype(int))
    return lo if side < 0 else hi

def _vexp(x):
    return V(_vexp_end(x.lo, -1), _vexp_end(x.hi, +1))

def _sinh_cosh(u):
    """e^{u/2}, sinh u, cosh u -- with a SERIES path for small u
    (the direct (e^u - e^{-u})/2 loses ~11 digits of RELATIVE
    width at u ~ 1e-11, which summed over the geometric table
    region was a 3e-4 width leak).  sinh u = u(1 + u^2/6 +
    u^4/120 + R), 0 <= R <= u^6/5040/(1 - u^2/56)."""
    n = len(u.lo)
    e2 = _vexp(u*V.scalar(0.5, n))
    e = e2*e2
    einv = V(1.0/e.hi, 1.0/e.lo)
    sh = (e - einv)*V.scalar(0.5, n)
    ch = (e + einv)*V.scalar(0.5, n)
    small = u.hi < 0.01
    if np.any(small):
        ulo, uhi = u.lo[small], u.hi[small]
        m = int(small.sum())
        us = V(ulo, uhi)
        u2 = us*us
        one = V(np.ones(m), np.ones(m))
        ser = one + u2*V.scalar(1.0/6, m) \
            + u2*u2*V.scalar(1.0/120, m)
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
    -- the round-6 build's first width blowup).  Core cumsums
    are kept as directed lo/hi partial sums (their own rounding
    accumulation is genuinely prefix-shared and stays; it is
    ~n*eps*scale ~ 1e-10, negligible)."""

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
        self.f_lo = fcell.lo
        self.f_hi = fcell.hi
        self.extra = 0.0     # sliver widening (both directions)

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


def _table_nodes(a):
    geo = [X0]
    while geo[-1] < XSW:
        geo.append(min(geo[-1]*1.007, XSW))
    xmax = 2*a + 4e-3
    uni = np.arange(XSW, xmax + HTAB, HTAB)
    return np.concatenate([np.array(geo[:-1]), uni])


def build_tables(a, ws, degmax):
    nodes = _table_nodes(a)
    mid = 0.5*(nodes[:-1] + nodes[1:])
    cellV = V(nodes[:-1], nodes[1:])
    midV = V(mid, mid)
    n = len(mid)
    Em, Am, Epm, Eppm, Apm, Appm = E_A_prime(midV)
    Ec, Ac, Epc, Eppc, Apc, Appc = E_A_prime(cellV)
    tabs = {}
    tA = Table(nodes, Am, Appc, Ac)
    tA.extra = _u(0.51*X0)
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
            t.extra = _u(X0**i/i + X0**(i + 1)/(i + 1))
        tabs[f"H{i}"] = t
    for w in ws:
        wI = I(w)
        s2m = vsin(midV*V.scalar(wI/2, n))
        s2m = s2m*s2m
        s2c = vsin(cellV*V.scalar(wI/2, n))
        s2c = s2c*s2c
        sinw_c = vsin(cellV*V.scalar(wI, n))
        cosw_c = vcos(cellV*V.scalar(wI, n))
        fpp = Eppc*s2c + Epc*sinw_c*V.scalar(wI, n) \
            + Ec*cosw_c*V.scalar(wI*wI/2, n)
        tG = Table(nodes, Em*s2m, fpp, Ec*s2c)
        tG.extra = _u((w/2)**2*X0**2)
        tabs[f"G{w:.9f}"] = tG
        cosm = vcos(midV*V.scalar(wI, n))
        sinm = vsin(midV*V.scalar(wI, n))
        fppC = Eppc*cosw_c - V.scalar(2*w, n)*Epc*sinw_c \
            - V.scalar(w*w, n)*Ec*cosw_c
        fppS = Eppc*sinw_c + V.scalar(2*w, n)*Epc*cosw_c \
            - V.scalar(w*w, n)*Ec*sinw_c
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
        self.cabs = _u(sum(abs(c) for c, _, _ in harm)
                       + sum(max(abs(p.lo), abs(p.hi))
                             * max(a, 1.0)**j
                             for j, p in enumerate(poly)))

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
        even = self.parity == "even"
        tot = I(0.0)
        for idx, (c, k, off) in enumerate(self.harm):
            w = self.wI(idx)
            arg = w*x
            wpow = w if order == 1 else w*w
            if order == 1:
                tr = (-isin(arg)) if even else icos(arg)
            else:
                tr = (-icos(arg)) if even else (-isin(arg))
            tot = tot + I(c)*wpow*tr
        dp = _poly_deriv(self.poly, order)
        p = I(0.0)
        for cj in reversed(dp):
            p = p*x + cj
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

    def _tab_diff(self, name, x1I, x2I):
        """int_{x1}^{x2} with between-nodes error only; interval
        endpoints handled by min/max spans."""
        tab = self.tabs[name]
        if x1I.hi <= x2I.lo:
            inner = tab.diff(x1I.hi, x2I.lo)
            outer = tab.diff(x1I.lo, x2I.hi)
            return I(min(inner.lo, outer.lo),
                     max(inner.hi, outer.hi))
        return tab.diff(min(x1I.lo, x2I.lo),
                        max(x1I.hi, x2I.hi)).hull(I(0.0)) \
            if False else I(-1e30, 1e30)

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

    def Tphi(self, t, deriv=False, pole=True):
        tr = self.tr
        a = tr.a
        even = tr.parity == "even"
        phit = tr.phi_pt(t)
        dphit = tr.dphi_pt(t, 1) if deriv else None
        k1 = I(a) - t
        k2 = I(a) + t
        IAv = self._tab_at("IA", k2)
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
                s = isin(I(w)*k2*I(0.5))
                gint = self._EI(k2)*s*s
                ddint = ddint + I(c)*I(-2.0)*(dtrig*G
                                              + trig*gint)
        for i in range(2, tr.deg + 1, 2):
            Qi = self._peval(self.Pi[i], t)
            Hi = self._tab_at(f"H{i}", k2)
            dint = dint + Qi*Hi
            if deriv:
                dQi = self._peval(_poly_deriv(self.Pi[i], 1), t)
                ddint = ddint + dQi*Hi + Qi*self._E_ui(i, k2)
        corr = I(0.0)
        dcorr = I(0.0)
        for idx, (c, k, off) in enumerate(tr.harm):
            w = tr.ws[idx]
            wIv = tr.wI(idx)
            Cd = self._tab_diff(f"C{w:.9f}", k1, k2)
            Sd = self._tab_diff(f"S{w:.9f}", k1, k2)
            cwt, swt = icos(wIv*t), isin(wIv*t)
            if even:
                term = cwt*Cd - swt*Sd
            else:
                term = swt*Cd + cwt*Sd
            corr = corr + I(c)*term
            if deriv:
                ec2 = self._EI(k2)*icos(I(w)*k2)
                ec1 = self._EI(k1)*icos(I(w)*k1)
                es2 = self._EI(k2)*isin(I(w)*k2)
                es1 = self._EI(k1)*isin(I(w)*k1)
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
                    + Pi_t*(self._E_ui(i, k2)
                            + self._E_ui(i, k1))
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


def temple_cell(tr, tabs, ell2, use_pole):
    a = tr.a
    even = tr.parity == "even"
    k0 = math.log(2.0) - a
    bset = {DEDGE, a - DEDGE}
    if DEDGE < k0 < a - DEDGE:
        bset.add(k0)
    bounds = sorted(bset)
    cells = []
    for lo, hi in zip(bounds[:-1], bounds[1:]):
        if hi - lo < 1e-12:
            continue
        cl, ch = _ucells(lo, hi, HT)
        cells += list(zip(cl, ch))
    chi_lo = chi_hi = 0.0
    n_lo = n_hi = 0.0
    for (cl, ch) in cells:
        h = ch - cl
        m = I(0.5*(cl + ch))
        cellI = I(cl, ch)
        phim = tr.phi_pt(m)
        chim = icosh(m*I(0.5)) if even else isinh(m*I(0.5))
        f = phim*chim
        p0 = tr.phi_pt(cellI)
        p1_ = tr.dphi_pt(cellI, 1)
        c0 = icosh(cellI*I(0.5)) if even \
            else isinh(cellI*I(0.5))
        c1 = (isinh(cellI*I(0.5)) if even
              else icosh(cellI*I(0.5)))*I(0.5)
        fp = p1_*c0 + p0*c1
        e = _u(h*h*0.25*fp.abs_hi())
        chi_lo += _d(f.lo*h - e)
        chi_hi += _u(f.hi*h + e)
        f2 = phim*phim
        f2p = I(2.0)*p0*p1_
        e2_ = _u(h*h*0.25*f2p.abs_hi())
        n_lo += _d(f2.lo*h - e2_)
        n_hi += _u(f2.hi*h + e2_)
    sl = _u(2*DEDGE*1.3*tr.cabs)
    chi_phi = I(_d(2*(chi_lo - sl)), _u(2*(chi_hi + sl)))
    sl2 = _u(2*DEDGE*tr.cabs**2)
    nn = I(_d(2*(n_lo - sl2)), _u(2*(n_hi + sl2)))

    ct = ClosedT(tr, tabs, chi_phi)
    CEDGE = _u((float(LG4PI.hi) + 2.2 + 40.0 + 1.0
                + float(C2I.hi))*tr.cabs
               + 2*max(abs(chi_phi.lo), abs(chi_phi.hi))
               * float(icosh(I(a/2)).hi))
    M_lo = M_hi = 0.0
    S_hi = 0.0
    S_lo = 0.0
    for (cl, ch) in cells:
        h = ch - cl
        m = I(0.5*(cl + ch))
        cellI = I(cl, ch)
        Tm, _ = ct.Tphi(m, deriv=False, pole=use_pole)
        Tc, dTc = ct.Tphi(cellI, deriv=True, pole=use_pole)
        phim = tr.phi_pt(m)
        p0 = tr.phi_pt(cellI)
        p1_ = tr.dphi_pt(cellI, 1)
        f = phim*Tm
        fp = p1_*Tc + p0*dTc
        e = _u(h*h*0.25*fp.abs_hi())
        M_lo += _d(f.lo*h - e)
        M_hi += _u(f.hi*h + e)
        f2 = Tm*Tm
        f2p = I(2.0)*Tc*dTc
        e2_ = _u(h*h*0.25*f2p.abs_hi())
        S_hi += _u(max(f2.hi, 0.0)*h + e2_)
        S_lo += _d(max(f2.lo*h - e2_, 0.0))
    Msl = _u(2*DEDGE*tr.cabs*CEDGE)
    M = I(_d(2*(M_lo - Msl)), _u(2*(M_hi + Msl)))
    Ssl = _u(2*DEDGE*CEDGE*CEDGE)
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
            "ncells": len(cells), "premise_ok": bool(ok),
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


def _geg_coeffs(n, nu):
    c0 = [I(1.0)]
    if n == 0:
        return c0
    c1 = [I(0.0), I(2*nu)]
    if n == 1:
        return c1
    for k in range(1, n):
        nxt = [I(0.0)]*(k + 2)
        for j, cj in enumerate(c1):
            nxt[j + 1] = nxt[j + 1] + cj*I(2*(k + nu))
        for j, cj in enumerate(c0):
            nxt[j] = nxt[j] - cj*I(k + 2*nu - 1)
        nxt = [x*I(1.0/(k + 1)) for x in nxt]
        c0, c1 = c1, nxt
    return c1

def _ipow(x, k):
    p = I(1.0)
    for _ in range(k):
        p = p*x
    return p


def _sha(name):
    import ckpt_key
    return ckpt_key.code_sha(os.path.join(HERE, name))

DEPST3 = {f: _sha(f) for f in ("oneprime_fractional.py",
                               "oneprime_interval_core.py",
                               "oneprime_interval_count.py",
                               "oneprime_interval_temple.py")}
KEYFILE = os.path.join(HERE, "oneprime_interval_temple.py")


def run():
    import glob
    params = {"deps": DEPST3, "htab": HTAB, "ht": HT,
              "round": 6}
    st = ckpt_key.load("oneprime_ivtemple", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is not None:
        return st
    ivc = sorted(glob.glob(os.path.join(
        HERE, "checkpoints", "oneprime_ivcount_*.json")))
    assert ivc, "Stage II checkpoint required"
    counts = json.load(open(ivc[0]))["state"]
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
        tr = trial_from_fixture(f, f["c"])
        tabs = build_tables(f["a"], tr.ws, tr.deg)
        if f["parity"] == "even":
            res = temple_cell(tr, tabs, nustar, True)
            res["ell2"] = [nustar.lo, nustar.hi]
        else:
            trF = trial_from_fixture(f, f["cfree"])
            resF = temple_cell(trF, tabs, nustar, False)
            ok1 = resF["premise_ok"] and \
                resF["temple_lo"] is not None and \
                resF["temple_lo"] > 0
            assert ok1, f"odd stage1 fails {cellk}: {resF}"
            nu1 = I(resF["temple_lo"])
            res = temple_cell(tr, tabs, nu1, True)
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
              "1.09 -- every ingredient an interval enclosure.",
              flush=True)
    ckpt_key.save("oneprime_ivtemple", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    if os.path.exists(pjson):
        os.remove(pjson)
    return st


if __name__ == "__main__":
    run()
    print("interval temple (Stage III) complete", flush=True)
