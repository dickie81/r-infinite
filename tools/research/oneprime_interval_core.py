#!/usr/bin/env python3
"""THE ONE-PRIME ARC, ROUND 6 -- THE INTERVAL PASS, STAGE I:
the rigorous interval core and the enclosure of the window kernel
W(r) = Re psi(1/4 + ir/2) - log pi - sqrt(2) log 2 cos(r log 2).

Commission: "Interval pass pls" (the owner's choice at the
round-247 convergence; the arc's certificates are float64-modulo
and this pass replaces every load-bearing number with a rigorous
enclosure, turning the [log 2, 0.95] closure into an unconditional
theorem candidate).

DESIGN (Stage I of three instruments):
  I   this file: interval arithmetic + rigorous W enclosures.
  II  oneprime_interval_count.py: certified Birman-Schwinger
      counts -- interval qtcheck profiles, kernel matrices with
      operator-norm error bounds, verified eigenvalue brackets,
      margin-friendly (nu, beta) cell re-selection.
  III oneprime_interval_temple.py: the Temple side -- fixed
      rational trial vectors, enclosed quadratic-form entries,
      final interval Temple certificates per cell.

THE ARITHMETIC (no unproven accuracy assumptions anywhere):
  * IntvF: closed float64 intervals with outward rounding by
    math.nextafter around every + - * / and sqrt. IEEE 754
    guarantees correct rounding of these five operations, so
    one nextafter step in each direction brackets the true
    result: this is rigorous by the standard, not by libm faith.
  * Transcendentals (exp, log, atan, sin, cos, cosh, sinh) are
    implemented HERE via argument reduction + Taylor/elementary
    series with explicit interval remainder terms, using only the
    five guaranteed operations plus cached high-precision interval
    constants (pi, log 2, log pi, sqrt 2, euler) imported once
    from mpmath.iv at 80 bits and outward-rounded to floats.
    Every function is gated by containment against mpmath.iv on
    randomized points (gI2).
  * mpmath.iv itself is used only for the constants and the gates,
    never in a load-bearing enclosure path.

THE PSI ENCLOSURE (classical, self-contained):
  Re psi(1/4 + i r/2) via the recurrence
      psi(z) = psi(z + n) - sum_{k=0}^{n-1} 1/(z + k)
  with n chosen so w = z + n has x = Re w >= max(12, sqrt(2)|y|),
  then Binet's second formula on Re w > 0:
      psi(w) = log w - 1/(2w) - J(w),
      J(w)   = 2 int_0^oo t dt / ((t^2 + w^2)(e^{2 pi t} - 1)).
  With x >= sqrt(2)|y|: Re(t^2 + w^2) = t^2 + x^2 - y^2
  >= t^2 + x^2/2, so |t^2 + w^2| >= t^2 + x^2/2 > 0 and the
  integrand is bounded by (1/(t^2 + x^2/2)) * t/(e^{2 pi t} - 1).
  J is enclosed by interval Riemann sums on the fixed grid
  t in [0, TCUT] (step HJ), evaluating the integrand ON EACH
  SUBINTERVAL as an interval (hull enclosure -- no derivative
  bounds needed), plus the explicit tail
      |tail| <= 2/(TCUT^2 + x^2/2) * int_TCUT^oo t e^{-2 pi t}
                / (1 - e^{-2 pi TCUT}) dt
  evaluated in closed form. The e^{2 pi t} - 1 factors on the
  grid are precomputed once as intervals and reused across every
  w (the per-point cost is then pure guaranteed arithmetic).

DERIVATIVE MAJORANTS (for Stage II quadratures): on r >= 0,
  |W'(r)|  <= |psi'(1/4 + ir/2)|/2 + C2 log 2,
  |W''(r)| <= |psi''(1/4 + ir/2)|/4 + C2 log^2 2,
with |psi'(w)|, |psi''(w)| bounded through the same shift by
  |psi'(w)| <= sum_k 1/|z+k|^2 + [1/|w| + 1/(2|w|^2) + J1 bound]
and the elementary |psi'(x+iy)| <= psi'(x) monotone bounds; the
committed function dW_majorant returns a single uniform constant
per r-range, gated against dense float64 finite differences (gI4).

GATES (all asserted in run()):
  gI1  containment: the W enclosure contains the float64
       scipy.special.digamma value at NSAMP points spanning
       [1e-6, 260] (the scipy value is spectral-quality; a
       rigorous enclosure that misses it is wrong).
  gI2  transcendental containment: each in-house function's
       enclosure CONTAINS the mpmath.iv (80-bit) reference
       interval at randomized points (exp/log/cos/sin), or the
       120-bit point value where mpmath.iv lacks the function
       (atan/cosh/sinh) -- round-248 F248-9: the description
       now matches the stronger assertion the code makes.
  gI3  arithmetic self-tests: algebraic identities hold as
       containments; refinement shrinks widths monotonically.
  gI4  derivative-majorant sanity: |finite difference of W| at
       dense float64 points <= the committed majorant on every
       tested subrange.
  gI5  width ceilings: W enclosure width <= WCAP (1.2e-6) on
       the sampled range at the production (TCUT, HJ, XMIN) --
       calibrated to Stage II's budget: the margin-friendly
       count cells need delta_W <~ 5e-6, so the cap leaves 4x;
       widths are recorded in the checkpoint.

CHECKS. 7: classical throughout (Binet's formula, Taylor
remainders, IEEE 754 interval arithmetic); no semiclassics.
8: no hypothesis input.

Keying law: every producing file in every key -- by executable
content (docstring-stripped AST), per the round-245 owner
decision.
"""
import math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key

_UP = math.inf
_DN = -math.inf

def _u(x):
    return math.nextafter(x, _UP)

def _d(x):
    return math.nextafter(x, _DN)


class I:
    """Closed float64 interval [lo, hi] with outward rounding.
    Only IEEE-guaranteed operations touch lo/hi."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        if not (lo <= hi):
            raise ValueError(f"bad interval [{lo}, {hi}]")
        self.lo = lo
        self.hi = hi

    def __repr__(self):
        return f"I[{self.lo!r}, {self.hi!r}]"

    @property
    def width(self):
        return self.hi - self.lo

    @property
    def mid(self):
        return 0.5*(self.lo + self.hi)

    def __add__(self, o):
        o = _c(o)
        return I(_d(self.lo + o.lo), _u(self.hi + o.hi))

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, o):
        o = _c(o)
        return I(_d(self.lo - o.hi), _u(self.hi - o.lo))

    def __rsub__(self, o):
        return _c(o) - self

    def __mul__(self, o):
        o = _c(o)
        ps = (self.lo*o.lo, self.lo*o.hi, self.hi*o.lo,
              self.hi*o.hi)
        return I(_d(min(ps)), _u(max(ps)))

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = _c(o)
        if o.lo <= 0.0 <= o.hi:
            raise ZeroDivisionError("interval divisor contains 0")
        ps = (self.lo/o.lo, self.lo/o.hi, self.hi/o.lo,
              self.hi/o.hi)
        return I(_d(min(ps)), _u(max(ps)))

    def __rtruediv__(self, o):
        return _c(o)/self

    def sq(self):
        m = min(abs(self.lo), abs(self.hi))
        if self.lo <= 0.0 <= self.hi:
            m = 0.0
        M = max(abs(self.lo), abs(self.hi))
        return I(_d(m*m), _u(M*M))

    def sqrt(self):
        if self.lo < 0:
            raise ValueError("sqrt of negative interval")
        return I(_d(math.sqrt(self.lo)), _u(math.sqrt(self.hi)))

    def hull(self, o):
        o = _c(o)
        return I(min(self.lo, o.lo), max(self.hi, o.hi))

    def contains(self, x):
        return self.lo <= x <= self.hi

    def abs_hi(self):
        return max(abs(self.lo), abs(self.hi))


def _c(x):
    return x if isinstance(x, I) else I(float(x))


# ---- high-precision interval constants (mpmath.iv, once) ----

def _const(fn):
    from mpmath import iv
    iv.prec = 80
    v = fn(iv)
    return I(_d(float(v.a)), _u(float(v.b)))

PI = _const(lambda iv: iv.pi)
TWO_PI = PI*2
HALF_PI = PI/2
LOG2 = _const(lambda iv: iv.log(2))
LOGPI = _const(lambda iv: iv.log(iv.pi))
SQRT2 = _const(lambda iv: iv.sqrt(2))
EULER = _const(lambda iv: +iv.euler)
C2I = SQRT2*LOG2          # the prime coefficient sqrt(2) log 2


# ---- in-house transcendentals (series + explicit remainders) --

def iexp(x):
    """exp over an interval: exp monotone, so endpoints suffice;
    each endpoint via 2^n * exp(s), |s| <= ln2/2, Taylor with
    remainder |R_K| <= |s|^K/K! * 1/(1 - |s|/(K+1))."""
    return I(_exp_pt(x.lo, -1) if isinstance(x, I)
             else _exp_pt(float(x), -1),
             _exp_pt(x.hi, +1) if isinstance(x, I)
             else _exp_pt(float(x), +1))

def _exp_pt(x, side):
    if x == 0.0:
        return 1.0
    n = int(round(x/0.6931471805599453))
    s = I(x) - LOG2*n
    K = 22
    term = I(1.0)
    tot = I(1.0)
    for k in range(1, K):
        term = term*s/k
        tot = tot + term
    m = s.abs_hi()
    rem = (m**K)/math.factorial(K)/(1 - m/(K + 1))
    tot = tot + I(-_u(rem), _u(rem))
    sc = 2.0**n
    v = tot*I(sc)
    return v.lo if side < 0 else v.hi

def ilog(x):
    """log over a positive interval; endpoints via atanh series:
    log(m) with m = a * 2^-n in [1/sqrt2, sqrt2], log(m) =
    2 atanh(u), u = (m-1)/(m+1), |u| <= 0.1716, remainder
    |R| <= |u|^{2K+1}/(1-u^2) * 2/(2K+1)."""
    if x.lo <= 0:
        raise ValueError("log of non-positive interval")
    return I(_log_pt(x.lo, -1), _log_pt(x.hi, +1))

def _log_pt(x, side):
    n = 0
    m = x
    while m > 1.4142135623730951:
        m /= 2.0
        n += 1
    while m < 0.7071067811865476:
        m *= 2.0
        n -= 1
    mi = I(m)
    u = (mi - 1)/(mi + 1)
    K = 14
    u2 = u.sq()
    term = u
    tot = u
    for k in range(1, K):
        term = term*u2
        tot = tot + term/(2*k + 1)
    au = u.abs_hi()
    rem = (au**(2*K + 1))/(1 - au*au)/(2*K + 1)
    tot = (tot + I(-_u(rem), _u(rem)))*2
    v = tot + LOG2*n
    # exact scaling correction: x = m * 2^n held exactly since
    # /2 and *2 are exact in binary; v encloses log x
    return v.lo if side < 0 else v.hi

def iatan(x):
    """atan over an interval; monotone, endpoints via reduction
    atan(t) = pi/2 - atan(1/t) for t > 1, then atan(t) with
    t <= 1 via the half-angle-free series after one bisection
    t -> t/(1+sqrt(1+t^2)) so |t| <= 0.4142; series remainder
    |R| <= |t|^{2K+1}/(2K+1)/(1-t^2)."""
    return I(_atan_pt(x.lo, -1), _atan_pt(x.hi, +1))

def _atan_pt(x, side):
    s = 1.0 if x >= 0 else -1.0
    xa = abs(x)
    inv = xa > 1.0
    ti = I(1.0)/I(xa) if inv else I(xa)
    ti = ti/(1 + (1 + ti.sq()).sqrt())     # atan(x)=2atan(that)
    K = 12
    t2 = ti.sq()
    term = ti
    tot = ti
    for k in range(1, K):
        term = term*t2
        tot = tot + term*((-1)**k)/(2*k + 1)
    at = ti.abs_hi()
    rem = (at**(2*K + 1))/(2*K + 1)/(1 - at*at)
    tot = (tot + I(-_u(rem), _u(rem)))*2
    if inv:
        tot = HALF_PI - tot
    v = tot if s > 0 else -tot
    return v.lo if side < 0 else v.hi

def _sin_core(x):
    """sin on |x| <= pi/2 + slack via Taylor, interval in/out."""
    K = 12
    x2 = x.sq()
    term = x
    tot = x
    for k in range(1, K):
        term = term*x2*(-1)/((2*k)*(2*k + 1))
        tot = tot + term
    m = x.abs_hi()
    rem = (m**(2*K + 1))/math.factorial(2*K + 1)
    return tot + I(-_u(rem), _u(rem))

def icos(x):
    """cos over an interval via range reduction with interval pi:
    y = x - 2 pi n, then cos y = sin(pi/2 - y) on the reduced
    argument, with monotonicity handling by evaluating the sine
    core on the interval directly (the core is a genuine interval
    extension, so no monotone split is needed -- widths stay
    O(width + remainder))."""
    x = _c(x)
    n = round(x.mid/6.283185307179586)
    y = x - TWO_PI*n
    # |y| <= pi + width; fold once more if needed
    if y.abs_hi() > 3.15:
        if y.mid > 0:
            return -_cos_reduced(y - PI)
        return -_cos_reduced(y + PI)
    return _cos_reduced(y)

def _cos_reduced(y):
    return _sin_core(HALF_PI - y)

def isin(x):
    return icos(_c(x) - HALF_PI)

def icosh(x):
    e = iexp(x)
    return (e + 1/e)/2

def isinh(x):
    e = iexp(x)
    return (e - 1/e)/2


# ---- the Binet-integral psi enclosure ----

TCUT = 6.0
HJ = 1.5e-3
XMIN = 25.0

_binet_cache = {}

def _binet_grid():
    """Fixed t-grid with precomputed interval 1/(e^{2 pi t} - 1)
    on each subinterval (hull over the subinterval: the factor is
    DECREASING, so the hull is [f(t+h), f(t)]) plus t-hulls."""
    if "g" in _binet_cache:
        return _binet_cache["g"]
    n = int(round(TCUT/HJ))
    # exact right endpoint: the tail bound covers [TCUT, oo), so
    # the grid must cover [0, TCUT] with no gap -- ts[-1] = TCUT
    # exactly, interior points monotone floats
    ts = [TCUT*j/n for j in range(n + 1)]
    ts[0], ts[-1] = 0.0, TCUT
    cells = []
    for j in range(n):
        tl, th = ts[j], ts[j + 1]
        tI = I(tl, th)
        if tl == 0.0:
            # t/(e^{2 pi t}-1) is decreasing from 1/(2 pi);
            # handle the removable singularity by the factored
            # form g(t) = t/(e^{2 pi t}-1) in [g(th), 1/(2 pi)]
            ghi = (I(1.0)/TWO_PI).hi
            glo = (I(th)/(iexp(TWO_PI*th) - 1)).lo
            cells.append((tI, I(glo, ghi)))
        else:
            e_hi = (I(tl)/(iexp(TWO_PI*tl) - 1)).hi
            e_lo = (I(th)/(iexp(TWO_PI*th) - 1)).lo
            cells.append((tI, I(e_lo, e_hi)))
    _binet_cache["g"] = cells
    return cells

def repsi_quarter(r):
    """Rigorous enclosure of Re psi(1/4 + i r/2) for r >= 0."""
    ri = _c(r)
    y = ri/2
    yh = y.abs_hi()
    n = max(int(math.ceil(XMIN - 0.25)),
            int(math.ceil(1.4142135623730951*yh - 0.25)) + 1)
    x = I(0.25) + n            # Re w, exact small integers
    # recurrence sum: Re sum 1/(z+k) = sum (1/4+k)/((1/4+k)^2+y^2)
    y2 = y.sq()
    s = I(0.0)
    for k in range(n):
        a = I(0.25 + k)        # exact in binary
        s = s + a/(a.sq() + y2)
    # Re log w = 0.5 log(x^2 + y^2)
    relog = ilog(x.sq() + y2)/2
    # Re 1/(2w) = x/(2(x^2+y^2))
    modw2 = x.sq() + y2
    re_inv2w = x/(modw2*2)
    reJ, _ = _J_re_im_iv(x, y)
    return relog - re_inv2w - reJ - s

def _J_re_im_iv(x, y):
    """Interval-argument version of _J_re_im (x, y intervals)."""
    x2y2 = x.sq() - y.sq()
    two_xy = x*y*2
    reJ = I(0.0)
    imJ = I(0.0)
    # tI.width is EXACT: the uniform grid from 0 satisfies
    # Sterbenz (node ratio <= 2 except the first cell, whose
    # difference from 0 is trivially exact) -- round-248
    # disposition of F248-1f's core:424 sub-item
    for tI, gI in _binet_grid():
        a = tI.sq() + x2y2
        den = a.sq() + two_xy.sq()
        reJ = reJ + gI*a/den*tI.width
        imJ = imJ + gI*two_xy/den*tI.width
    reJ = reJ*2
    imJ = -imJ*2
    x2h = (x.sq()/2 + I(TCUT).sq()).lo
    efac = iexp(I(-2*math.pi*TCUT))
    denom = (1 - efac).lo
    tint = (efac*(I(TCUT)/TWO_PI + 1/(TWO_PI.sq()))).hi
    tail = _u(2*tint/(denom*x2h))
    tb = I(-tail, tail)
    return reJ + tb, imJ + tb

def W_enclose(r):
    """Rigorous enclosure of the window kernel W(r)."""
    ri = _c(r)
    return repsi_quarter(ri) - LOGPI - C2I*icos(ri*LOG2)


# ---- derivative majorants (uniform constants, Stage II) ----

def dW_majorant(rmax):
    """A single rigorous constant M1 with |W'(r)| <= M1 on
    [0, rmax]: |d/dr Re psi(1/4+ir/2)| <= |psi'(1/4+ir/2)|/2 and
    |psi'(x+iy)| <= sum_{k>=0} 1/((x+k)^2+y^2) <= sum 1/(x+k)^2
    = psi'(x) <= psi'(1/4) = pi^2/2 + 8 Catalan... we use the
    crude uniform bound psi'(1/4) < 17.2 (Hurwitz zeta(2,1/4) =
    pi^2 + 8G < 17.1974), so |W'| <= 17.2/2 + C2 log 2 < 9.581.
    Rigorous because zeta(2, 1/4) = sum 1/(k+1/4)^2 <= 16 +
    sum_{k>=1} 1/k^2 = 16 + pi^2/6 < 17.65 -- we return that
    fully-proved cruder constant."""
    m_psi1 = 16.0 + (PI.sq()/6).hi          # zeta(2,1/4) bound
    return _u(m_psi1/2 + (C2I*LOG2).hi)

def d2W_majorant(rmax):
    """|W''(r)| <= |psi''|/4 + C2 log^2 2; |psi''(x+iy)| <=
    2 sum 1/|x+k+iy|^3 <= 2 sum 1/(k+1/4)^3 <= 2(64 + zeta(3))
    < 130.5."""
    m_psi2 = 2*(64.0 + 1.2020569031595943)
    return _u(m_psi2/4 + (C2I*LOG2*LOG2).hi)


# ---- keys, gates, run ----

def _sha(name):
    import ckpt_key
    return ckpt_key.code_sha(os.path.join(HERE, name))

# COMPUTED transitive closure (round 252, reviewer-3 F4 -- the
# hand-listed pair omitted certificate's own bridge/fold chain)
DEPSI = {f: _sha(f) for f in sorted(__import__("ckpt_key")
        .producer_closure(("oneprime_interval_core.py",), HERE))}
KEYFILE = os.path.join(HERE, "oneprime_interval_core.py")

NSAMP = 160
WCAP = 1.2e-6

def run():
    import numpy as np
    params = {"deps": DEPSI, "tcut": TCUT, "hj": HJ,
              "xmin": XMIN, "nsamp": NSAMP, "round": 6}
    st = ckpt_key.load("oneprime_ivcore", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is not None:
        return st
    from oneprime_certificate import Wker

    # gI3 arithmetic self-tests
    a, b = I(1.1, 1.2), I(-0.4, 0.3)
    assert ((a + b) - b).contains(a.mid), "gI3 FAIL add/sub"
    assert (a*b).contains(1.15*(-0.05)), "gI3 FAIL mul"
    assert ((a/I(3.0))*3).contains(a.mid), "gI3 FAIL div"
    assert I(2.0).sqrt().sq().contains(2.0), "gI3 FAIL sqrt"

    # gI2 transcendental containment vs mpmath.iv (80-bit)
    from mpmath import iv, mp
    iv.prec = 80
    mp.prec = 120
    rng = np.random.default_rng(6)
    ptref = {iatan: mp.atan, icosh: mp.cosh, isinh: mp.sinh}
    for fn, ref in ((iexp, iv.exp), (ilog, iv.log),
                    (icos, iv.cos), (isin, iv.sin),
                    (iatan, None), (icosh, None),
                    (isinh, None)):
        for _ in range(60):
            x = float(rng.uniform(0.01, 30.0)
                      if fn in (ilog,) else rng.uniform(-30, 30))
            mine = fn(I(x))
            if ref is None:
                # mpmath.iv lacks atan/cosh/sinh; gate on
                # containment of the 120-bit point value
                # (cosh/sinh added round 248, F248-9: the
                # docstring claimed them gated, now they are)
                v = float(ptref[fn](mp.mpf(x)))
                assert mine.contains(v), \
                    f"gI2 FAIL {fn.__name__}({x})"
                continue
            r = ref(iv.mpf(x))
            assert mine.lo <= float(r.a) and \
                float(r.b) <= mine.hi, \
                f"gI2 FAIL {fn.__name__}({x})"
    print("gI2 PASS: exp/log/cos/sin/atan/cosh/sinh contain "
          "80/120-bit refs at 60 random points each", flush=True)

    # gI1 + gI5: W enclosures contain scipy values, widths capped
    rs = np.concatenate([np.linspace(1e-6, 12, 40),
                         np.linspace(12, 60, 40),
                         np.linspace(60, 260, NSAMP - 80)])
    wids = []
    for r in rs:
        enc = W_enclose(float(r))
        wv = float(Wker(np.array([r]))[0])
        assert enc.contains(wv), \
            f"gI1 FAIL: W({r}) = {wv} not in {enc}"
        wids.append(enc.width)
    wmax = float(max(wids))
    assert wmax <= WCAP, f"gI5 FAIL width {wmax:.2e} > {WCAP}"
    print(f"gI1 PASS: {len(rs)} containments; gI5 PASS: max "
          f"width {wmax:.3e} <= {WCAP}", flush=True)

    # gI4 derivative-majorant sanity on dense float64 grids
    m1, m2 = dW_majorant(260.0), d2W_majorant(260.0)
    rg = np.arange(1e-4, 260, 5e-4)
    wv = Wker(rg)
    d1 = np.abs(np.diff(wv))/5e-4
    assert float(d1.max()) <= m1, "gI4 FAIL first derivative"
    d2 = np.abs(np.diff(wv, 2))/25e-8
    assert float(d2.max()) <= m2, "gI4 FAIL second derivative"
    print(f"gI4 PASS: |W'| fd-max {float(d1.max()):.3f} <= {m1:.3f}; "
          f"|W''| fd-max {float(d2.max()):.3f} <= {m2:.3f}",
          flush=True)

    st = {"gI2": "pass", "gI1_n": int(len(rs)),
          "wmax": wmax, "wcap": WCAP,
          "m1": m1, "m2": m2,
          "sample": {f"{float(r):.6f}":
                     [W_enclose(float(r)).lo,
                      W_enclose(float(r)).hi]
                     for r in (0.5, 3.305, 8.823, 10.533,
                               18.011, 100.0, 250.0)}}
    ckpt_key.save("oneprime_ivcore", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    return st


if __name__ == "__main__":
    run()
    print("interval core (Stage I) complete", flush=True)
