#!/usr/bin/env python3
"""THE TWO-PRIME WINDOW, STAGE 2 -- the interval Kato-Temple
certificate for the odd sector of the two-prime form at delta =
1.10 (a = 0.55): the first two-prime certificate, and by domain
nesting the rigorous odd-sector answer to A418's structural
question at the log 3 threshold.

THE OBJECT. Weil's full quadratic functional on test functions of
support length delta in [log 3, log 4) equals the semi-local form
at the real place plus the primes 2 and 3 (A417). Its closed-form
t-space operator is the one-prime instrument's (oneprime_interval_
temple.py, Theorem 1bj) with the prime part
    - (C2/2)[phi(t + log 2) + phi(t - log 2)]
    - (C3/2)[phi(t + log 3) + phi(t - log 3)],   C3 = 2 log 3/sqrt 3,
and everything else identical: T_arch by the one-dimensional
cumulative tables (IA, Gw, Cw, Sw, Hi), the rank-one odd pole
-2 chi <chi, phi> with chi = sinh(t/2), the entire trial (pure
harmonics here), the graded mean-value quadratures for n, M, S.

THE CERTIFICATE. Kato-Temple in ratio form,
    lambda_1(T_odd) >= (ell2 M - S)/(ell2 n - M) > 0,
valid for rho = M/n < ell2 <= lambda_2(T_odd), with the premise
ell2 = nu* from the CERTIFIED POLE-INCLUSIVE COUNT
(twoprime_interval_count.py, loaded at its current
executable-content key): #{T_odd < nu*} <= 1 with the pole kept
inside the counting operator, so lambda_2(T_odd) >= nu* directly
-- the odd analogue of Theorem 1bj's even-1.0 device (there the
interlacing route lost the premise; here the two-stage route's
interlacing capped ell2 at the pole-free lambda_1 ~ 0.015, below
the ~0.035 the harmonic trial needs).  Single stage: no pole-free
Temple, no interlacing.

WHAT CHANGES AGAINST THE ONE-PRIME INSTRUMENT (this file is
GENERATED from it by exact substitutions -- the generator's
assertion list is the complete diff; everything else is the
committed round-6/7 code, imported or copied verbatim):
  ClosedT23.Tphi_batch / Tphi: the prime part is the two-shift
    sum above (value and t-derivative);
  temple_cell23: the t-cells are split at BOTH kinks, log 2 - a
    and log 3 - a; the sliver envelope's prime term is
    (C2 + C3) cabs (harmonic branch) / (C2 + C3) M0 (polynomial
    branch);
  the run: one odd cell, delta = 1.10, ell2 = nu* from the
    two-prime count checkpoint; the fixture from the two-prime
    t-space operator (twoprime_recon.apply_T, base 0.003, pure
    harmonics with NHALF from the reconnaissance).

GATES: gT7 (vlog vs scalar), gT2 (rho tracks the float fixture
within 1e-4), gT5 (n in [0.5, 2]), gT6 (batch/scalar overlap),
gT3 (premise rho < ell2 and Temple > 0), plus gT9: the count
premise row is certified and its nu equals the fixture's nu*.

CHECKS. 7: classical. 8: no hypothesis input. Keying law: every
producing file in every key (computed transitive closure).
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
from oneprime_interval_temple import (
    LG4PI, X0, XSW, HTAB, HT, HCHI, DEDGE, Table, _table_nodes,
    build_tables, Trial, _poly_deriv, _ucells, _gcells, _ipow,
    _sinh_cosh, _vexp, _vlog, _vpow, _upow_cell, E_A_prime,
    trial_from_fixture, ClosedT)
from twoprime_interval_count import LOG3, C3I, ROW, A_CELL

# the cell configuration (ht, htab, theta): the odd:1.09 one-prime
# cell used (2e-6, 5e-6, 0.02) at float margin 1.8e-5; this cell's
# float margin is ~4e-6 at ell2 = 0.04, so the mean-value pitch
# and the edge grading are tightened
CELLCFG23 = {"odd:1.1": (1.5e-6, 5e-6, 0.015)}
NHALF_FIX = 24


class ClosedT23:
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
        lg3V = V.scalar(LOG3, n)
        p1 = self._phi_restricted_v(t + lg2V)
        p2 = self._phi_restricted_v(t - lg2V)
        p3 = self._phi_restricted_v(t + lg3V)
        p4 = self._phi_restricted_v(t - lg3V)
        prime = V.scalar(C2I*I(0.5), n)*(p1 + p2) \
            + V.scalar(C3I*I(0.5), n)*(p3 + p4)
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
        dp3 = self._dphi_restricted_v(t + lg3V)
        dp4 = self._dphi_restricted_v(t - lg3V)
        dprime = V.scalar(C2I*I(0.5), n)*(dp1 + dp2) \
            + V.scalar(C3I*I(0.5), n)*(dp3 + dp4)
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
        p3 = self._phi_restricted(t + LOG3)
        p4 = self._phi_restricted(t - LOG3)
        prime = C2I*I(0.5)*(p1 + p2) + C3I*I(0.5)*(p3 + p4)
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
        dp3 = self._dphi_restricted(t + LOG3)
        dp4 = self._dphi_restricted(t - LOG3)
        dprime = C2I*I(0.5)*(dp1 + dp2) + C3I*I(0.5)*(dp3 + dp4)
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


def temple_cell23(tr, tabs, ell2, use_pole, ht=HT, theta=0.1):
    a = tr.a
    even = tr.parity == "even"
    # T phi log-diverges at t = a (the E ~ 1/u correction
    # integral against nonvanishing phi(a)); mean-value cells
    # GRADED toward a (width ~ theta * dist neutralizes the
    # 1/dist of dT), uniform elsewhere, split at the
    # prime-shift kink k0.
    k0 = math.log(2.0) - a
    k1_ = math.log(3.0) - a          # the second prime-shift kink
    D0 = 1e-3
    bset = {DEDGE, a - D0}
    if DEDGE < k0 < a - D0:
        bset.add(k0)
    if DEDGE < k1_ < a - D0:
        bset.add(k1_)
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

    ct = ClosedT23(tr, tabs, chi_phi)
    # |T phi(t)| <= CE_A + CE_B ln(1/(a - t)) on the sliver:
    # the divergent piece is the correction integral, |corr| <=
    # (cabs/2)(ln(k2/k1) + k2) since E(u) <= 1/u + 1 on (0, 1.2]
    # (see the E-bound note in _sinh_cosh); every other term is
    # a COMPUTED enclosure (round-248 F248-2: the previous
    # 2.2/40.0/1.0 were verified-true but underived constants):
    #   |phi| <= cabs;  |dint| <= sum_h 2|c_h| Gw(xtop)
    #   + sum_{i even >= 2} Qabs_i Hi(xtop) (round 7: the poly
    #   part's Dfull term sum u^i Q_i(t) bounded coefficientwise
    #   on |t| <= a -- Qabs_i = sum_k |Pi[i][k]| a^k, the SAME
    #   Pi = poly_shift_coeffs the DINT computation uses, and
    #   the same i-range; identically zero when deg = 0, so the
    #   rounds <= 6 cells are unchanged);
    #   IA(k2) <= IA(xtop);  lcoth(k2) <= lcoth(a);
    #   |prime| <= (C2 + C3) cabs;  (cabs/2) k2 <= 0.51 cabs (2a+1e-3).
    cabsI = I(tr.cabs)
    xtop = 2*a + 1e-3
    ia_top = tabs["IA"].at(xtop)
    ea_ = iexp(I(a))
    lcoth_a = ilog((ea_ + 1)/(ea_ - 1))
    chiam = I(max(abs(chi_phi.lo), abs(chi_phi.hi)))
    if tr.deg == 0:
        # the rounds-<=6 derivation, byte-identical for the
        # pure-harmonic cells (their certified values must not
        # move):  |dint| <= sum_h 2|c_h| Gw(xtop)
        dint_top = I(0.0)
        for idx, (c, k, off) in enumerate(tr.harm):
            w = tr.ws[idx]
            dint_top = dint_top + I(abs(c))*I(2.0) \
                *tabs[f"G{w:.9f}"].at(xtop)
        cab_s = cabsI
        CE_B_I = I(0.51)*cabsI
        CE_A_I = (LG4PI*cabsI + cabsI*I(ia_top.hi)
                  + cabsI*I(lcoth_a.hi) + I(dint_top.hi)
                  + (C2I + C3I)*cabsI
                  + I(0.51)*cabsI*I(xtop)
                  + I(2.0)*chiam*icosh(I(a)*I(0.5))
                  + I(0.51)*cabsI*I(ilog(I(xtop)).abs_hi()))
    else:
        # ROUND 7 -- the SUPPORT-ONLY sliver envelope (any
        # entire trial, polynomial part included).  The
        # coefficient-sum route dies for polynomials: their
        # analytic continuation past the support edge is huge
        # (the measured Sigma_i |P_i(a)| Hi(xtop) = 7.4e3 put
        # Ssl at ~1e-4 -- the failed first runs).  Instead, on
        # [k1, k2] the +u branch of Dfull cancels the
        # correction integrand EXACTLY:
        #   DINT(t) = int_0^{k1} E Dfull du
        #           + int_{k1}^{k2} E [phi_an(t-u)/2 - phi(t)] du
        # (algebra: Dfull - phi_an(t+u)/2 = phi_an(t-u)/2
        # - phi(t); ranges: t + u <= a for u <= k1 = a - t, and
        # t - u in [-a, 2t - a] subset [-a, a] for u <= k2 --
        # every argument IN SUPPORT).  With M0 = sup_supp|phi|
        # (rigorous subdivided enclosure), M2 = sup_supp|phi''|
        # (coefficient sums -- enters only times k1^2 <=
        # DEDGE^2, via |Dfull| <= u^2 M2 / 2 and E <= 1/u + 1
        # on (0, 1.2]: int_0^{k1} E u^2 M2/2 <= 0.3 M2 k1^2 at
        # k1 <= 1e-3), and |phi(t-u)/2 - phi(t)| <= 1.5 M0:
        #   |DINT| <= 0.3 M2 k1^2
        #           + 1.5 M0 (ln(k2/k1) + k2).
        # The remaining terms as before with M0 in place of the
        # coefficient sum (t and t +- log2 stay in support).
        nsub = 8192
        edges = np.linspace(0.0, a, nsub + 1)
        pc_ = tr.phi_v(V(edges[:-1], edges[1:]))
        m0f = float(np.max(np.maximum(np.abs(pc_.lo),
                                      np.abs(pc_.hi))))
        m0I = I(_u(m0f))
        m2I = I(0.0)
        for idx, (c, k, off) in enumerate(tr.harm):
            m2I = m2I + I(abs(c))*tr.wI(idx)*tr.wI(idx)
        d2p = _poly_deriv(tr.poly, 2)
        for j, cj in enumerate(d2p):
            m2I = m2I + I(cj.abs_hi())*_ipow(I(a), j)
        cab_s = m0I
        CE_B_I = I(1.5)*m0I
        CE_A_I = (LG4PI*m0I + m0I*I(ia_top.hi)
                  + m0I*I(lcoth_a.hi)
                  + (C2I + C3I)*m0I
                  + I(1.5)*m0I*I(xtop)
                  + I(2.0)*chiam*icosh(I(a)*I(0.5))
                  + I(1.5)*m0I*I(ilog(I(xtop)).abs_hi())
                  + I(0.3)*m2I*I(DEDGE)*I(DEDGE))
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
    Msl = _u((DEI*cab_s*(CE_A_I + CE_B_I*(lnD_I + I(1.0)))
              + I(2.0)*DGI*cab_s*CEDGE_I).hi)
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
    # ell2 recorded in EVERY result (round-252, reviewer-3 F3:
    # the stage-1 record previously lacked it, so the odd
    # nu*-to-stage-1 premise link was not re-checkable from the
    # stored state)
    return {"rho": [rho.lo, rho.hi], "sigma2_hi": sig2,
            "n": [nn.lo, nn.hi], "S": [S.lo, S.hi],
            "chi_phi": [chi_phi.lo, chi_phi.hi],
            "ncells": int(ncl), "premise_ok": bool(ok),
            "temple_lo": lam,
            "ell2": [ell2.lo, ell2.hi],
            "ce": [CE_A, CE_B, CEDGE, Msl, Ssl]}


def make_fixture(a, nustar, nhalf=NHALF_FIX):
    """The frozen float64 trial for the odd cell: pure harmonics
    on the two-prime t-space operator at base 0.003; the Temple
    optimum at ell2 = nustar (single stage)."""
    import oneprime_fractional as opf
    import twoprime_recon as TR
    from oneprime_push import temple_opt
    from scipy.linalg import eigh as scipy_eigh
    # the harmonic count is the module default (NHALF_FIX = 24 =
    # opf.NHALF); a different count would be set on the LOCAL
    # Modes object (w, nharm, n), never by storing on the imported
    # module (the tower precheck's clause G)
    assert nhalf == opf.NHALF, "fixture harmonic count is the module default"
    md = opf.Modes(a, "odd", nus=(), nfr=0, nrough=0)
    tn, tw, B, TB, _v = TR.apply_T(md, (2, 3), base=0.003)
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
    NA, MA, SA = (NA + NA.T)/2, (MA + MA.T)/2, (SA + SA.T)/2
    mu, c = temple_opt(NA, MA, SA, nustar)
    assert c is not None, "float Temple has no admissible direction"
    cf = np.array(Wh.T @ c)
    cf = cf/math.sqrt(float(cf @ N @ cf))
    fx = {"a": a, "parity": "odd", "nustar": nustar, "delta": 2*a,
          "c": list(map(float, cf[:md.nharm])),
          "rho_float": float(cf @ M @ cf), "temple_float": float(mu),
          "ws": list(map(float, md.w)), "nharm": int(md.nharm),
          "sigma_float": math.sqrt(max(float(cf @ S @ cf) - float(cf @ M @ cf)**2, 0.0)),
          "l12": [float(x) for x in scipy_eigh(MA, NA, eigvals_only=True)[:2]]}
    return fx


def _sha(name):
    return ckpt_key.code_sha(os.path.join(HERE, name))


DEPS2T = {f: _sha(f) for f in sorted(ckpt_key.producer_closure(
    ("twoprime_interval_temple.py",), HERE))}
KEYFILE = os.path.join(HERE, "twoprime_interval_temple.py")


def run():
    import twoprime_interval_count as TC
    for xv in (1e-3, 0.11, 0.5, 1.0, 2.5, 7.0):
        il = ilog(I(xv))
        vl = _vlog(V.point(np.array([xv])))
        assert (max(il.lo, vl.lo[0]) <= min(il.hi, vl.hi[0])
                and vl.hi[0] - vl.lo[0] < 1e-12), f"gT7 FAIL at {xv}"
    params = {"deps": DEPS2T, "cfg": {k: list(v) for k, v in CELLCFG23.items()},
              "hchi": HCHI, "nhalf": NHALF_FIX, "row": ROW, "round": 1}
    st = ckpt_key.load("twoprime_ivtemple", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is not None:
        return st
    cparams = {"deps": TC.DEPS2C, "H": TC.H_FRAME, "row": TC.ROW,
               "a": TC.A_CELL, "rmax": TC.RMAX, "round": 1}
    counts = ckpt_key.load("twoprime_ivcount",
                           os.path.join(HERE, "twoprime_interval_count.py"),
                           cparams, kfun=ckpt_key.code_key)
    assert counts is not None, "Stage 1 checkpoint at the CURRENT key required"
    crow = counts["odd:1.1"]
    assert crow["certified"] and abs(crow["nu"] - ROW["nu"]) < 1e-12 \
        and abs(crow["a"] - A_CELL) < 1e-12, f"gT9 FAIL: count row {crow}"
    print(f"gT9 PASS: count row certified at nu {crow['nu']:g} "
          f"(margin {crow['margin']:.3e})", flush=True)
    fx = make_fixture(A_CELL, ROW["nu"])
    print(f"  fixture odd:1.1: float Temple {fx['temple_float']:+.3e} rho "
          f"{fx['rho_float']:+.4e} sigma {fx['sigma_float']:.3e} section l1/l2 "
          f"{fx['l12'][0]:+.3e}/{fx['l12'][1]:+.3e} nharm {fx['nharm']}", flush=True)
    ht_, htab_, th_ = CELLCFG23["odd:1.1"]
    tr = trial_from_fixture(fx, fx["c"])
    tabs = build_tables(fx["a"], [(tr.ws[i], tr.wI(i)) for i in range(len(tr.ws))],
                        tr.deg, htab_)
    res = temple_cell23(tr, tabs, I(fx["nustar"]), True, ht=ht_, theta=th_)
    assert abs(0.5*(res["rho"][0] + res["rho"][1]) - fx["rho_float"]) < 1e-4, \
        f"gT2 FAIL: rho {res['rho']} vs {fx['rho_float']}"
    assert 0.5 < res["n"][0] and res["n"][1] < 2.0, f"gT5 FAIL n {res['n']}"
    ok = res["premise_ok"] and res["temple_lo"] is not None and res["temple_lo"] > 0
    tl = res["temple_lo"]
    print(f"IVT2 odd:1.1: rho [{res['rho'][0]:.4e}, {res['rho'][1]:.4e}] "
          f"s2<={res['sigma2_hi']:.3e} ell2 {res['ell2'][0]:.4g} -> Temple >= "
          f"{tl if tl is not None else float('nan'):.4e} "
          f"{'CERTIFIED' if ok else 'FAIL'}", flush=True)
    res["certified"] = bool(ok)
    res["fixture"] = fx
    st = {"odd:1.1": res, "theorem": bool(ok)}
    if ok:
        print(f"THEOREM (interval-rigorous): the semi-local two-prime Weil "
              f"form -- Weil's full functional on [log 3, log 4) -- is "
              f"positive in the odd sector at support length 1.10, "
              f"lambda_1 >= {tl:.4e}, every ingredient an interval enclosure; "
              f"by domain nesting the odd-sector margin at the log 3 "
              f"threshold, and on the whole one-prime window, is >= {tl:.4e}.",
              flush=True)
    ckpt_key.save("twoprime_ivtemple", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    return st


if __name__ == "__main__":
    run()
    print("two-prime interval temple (Stage 2) complete", flush=True)
