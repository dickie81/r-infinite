"""A certificate for the loss of the sieve route to Linnik's exponent below 7/3 (README round 578; SEVEN-THIRDS.md
section 44; sieve_route_probe.py).

sieve_route_probe.py estimates the loss of section 44's decomposition and bounds it from above in double precision,
without directed rounding.  This file proves upper bounds.  Every decision in a bound is exact, every floating-point
operation on a bound is rounded outward, Buchstab's omega is enclosed, and the windows are proved.  Its rule for
decomposition is sharper than the probe's (below), and it certifies the exponents 2.28 (hux) and 2.25 (cons) as well as
section 44's 2.29 and 2.27.

What is certified.  For (hux, 2.28), (cons, 2.25), (hux, 2.29) and (cons, 2.27) with n = 600 cells a side, and for
(hux, 2.32) with n = 50: a number below 1 that is at least the loss of section 44's decomposition (the probe's
docstring states it), run with a window (u1', u2') proved to lie inside the window of section 44's Type II lemma.
The loss is an integral of Buchstab's omega over regions of [v, 1/2]^2 and [v, 1/2]^4.  The bound is a sum over the
cells of a grid of side h: h^2 (or h^4) times an upper bound for the integrand on the cell.  The gates check
arithmetic and implementation, not analysis.  Section 44 gives the argument (the Type II lemma, Harman's fundamental
theorem, the separation of variables, the inputs (H1) and (H2)) at paper level, unrefereed.

How.
  Exact decisions.  Every coordinate is an integer multiple of 1/DEN, DEN = 2^40: the window ends u1' = U1/DEN and
    u2' = U2/DEN, v = u2' - u1', R = 1 - u2', and the corners of the cells (side H/DEN).  Each test of the region, of
    evaluability (a subset sum of exponents, or its range over a cell, inside U = (u1', u2') u (1 - u2', 1 - u1')) and
    of the conditions for decomposition compares integers.  Run on (u1', u2'), section 44's decomposition is valid:
    (u1', u2') lies inside the Type II window and u2' L > 1, and v and R are taken from (u1', u2').
  The rule for decomposition.  A term of depth 2 that is not evaluable can be decomposed when alpha1 + alpha2 <= R,
    and then each of its terms of depth 3 that is not evaluable needs alpha1 + alpha2 + alpha3 <= R.  The complement
    window is (R, 1 - u1'), so a sum in (R, 1 - u1') makes its term evaluable.  So on a cell where the sum stays below
    1 - u1', every point that is not evaluable meets the condition.  A cell of (alpha1, alpha2) is decomposed when
    A + B < 1 - u1' and A + B + C < 1 - u1' for every alpha3 cell that may be non-evaluable (capitals are upper
    corners); otherwise it is dropped.  The probe's rule (round 576) asks for the sums to be at most R on the whole
    cell.  For (alpha1, alpha2) in a region of positive area the non-evaluable alpha3 reach exactly R - alpha1 - alpha2,
    so that rule refuses the alpha3 cell across that value at every grid size, and its bound does not tend to the loss
    as the cells shrink (printed below for hux at 2.29).
  Outward rounding.  After each floating-point operation on an upper (lower) bound comes one step of numpy.nextafter
    up (down).  IEEE 754 addition, multiplication and division in round-to-nearest are correctly rounded, so the step
    makes a strict bound.  A sum of n nonnegative terms computed in any order is at least (1 - 2(n - 1) 2^-53) times
    the exact sum when n 2^-53 <= 1/4.  So each sum is multiplied by 1 + 4n 2^-53, rounded up (function inflate).
    The final total is a math.fsum of the cells' bounds, treated the same way.
  Omega.  lo_i <= omega(t) <= hi_i for t in [i d, (i + 1) d), d = 2^-16, 1 <= t < 16; omega is 0 below 1.  On [1, 2),
    omega(t) = 1/t.  Above 2, F(t) = t omega(t) has F(2) = 1 and F'(t) = omega(t - 1).  So on an interval
    F(t_i) <= F(t) <= F(t_i) + d hi_{i - 1/d}, the bounds for F(t_i) advance by d lo_{i - 1/d} and d hi_{i - 1/d},
    lo_i = F_lo(t_i)/t_{i+1} and hi_i = (F_hi(t_i) + d hi_{i - 1/d})/t_i, all rounded outward.  The supremum of omega
    on an interval of arguments is at most the largest hi_i over the table intervals that meet it (a sparse table),
    and the infimum is at least the least lo_i (or 0 if the interval reaches below 1).
  Windows.  On each piece of a curve, A(beta)(1 - beta) is decreasing: its derivative is -3/(2 - beta)^2 for Ingham's
    3/(2 - beta), -6/(3 beta - 1)^2 for Huxley's 3/(3 beta - 1), and -7/3 for the constant 7/3.  So on [b0, b1] the
    numerator of lower(beta) is at most A(b0)(1 - b0)/2 + 1/2 - L(1 - b1).  u1' is the largest value of lower at the
    pieces' right ends, divided by L, plus 2^-30, rounded up to a multiple of 1/DEN.  Branch and bound in exact
    rational arithmetic proves lower(beta) <= u1' L on (1/2, 11/12].  At beta = 1/2 the bin's bound holds for every
    length when L > 2.  A is monotone on each piece, so its maximum Amax (12/5 for hux, 7/3 for cons) is at the
    pieces' ends.  u2' is min((L - Amax/2)/L, 1/2) minus 2^-30, rounded down.

Checks (references: the closed forms of omega on [1, 4) at 40 digits; above 4, sieve_route_probe.py's trapezoid table
at step 2.5e-5, whose error is far below 1e-8; the probe's midpoint estimate).
  (C0) The rounding.  For 20000 random pairs (x, y) of floats with signs and exponents in [-40, 40] and each of
       +, *, /: dn(x o y) <= x o y <= up(x o y) in exact rational arithmetic.  For 200 random arrays of 1000
       nonnegative floats, inflate of the numpy sum is at least the exact sum.
  (C1) The windows, for every certified (curve, L): the branch and bound closes, A <= Amax at the pieces' ends,
       u2' <= (L - Amax/2)/L, u2' <= 1/2, u1' < u2', u2' L > 1 and L > 2.
  (C2) The omega enclosure: lo <= hi on [1, 16); width below 1e-4; the closed form at 1500 random points of [1, 4)
       lies in [lo, hi]; the table at 3000 random points of [4, 16) lies within 1e-8 of [lo, hi].
  (C3) Exact replay (hux, 2.29, n = 150).  For 1500 random candidate cells of depth 2 and 1500 random counted cells of
       depth 4: the floating arguments of omega bracket the exact rational ones; the omega bound is at least the
       largest hi over the exact index range; the prefactor is at least the exact 1/(a b^2) (or 1/(a b c d^2)) at the
       lower corner; the cell bound is at least the exact product.
  (C4) The decisions at points (hux, 2.29, n = 200).  (i) 20000 random points of the depth-2 region lie in counted
       cells.  (ii) In every decomposed cell, at three corners moved inward by one unit and at one random point, where
       the point is in the region and not evaluable: alpha1 + alpha2 <= R, and alpha1 + alpha2 + alpha3 <= R for
       every non-evaluable alpha3 of a grid of step DEN // 10^4 units.  (iii) At that random point, a random point of
       its depth-4 region that is not evaluable lies in a counted depth-4 cell.  (iv) An independent implementation of
       the sharp rule passes every decomposed cell.  (v) At 1500 random points of random candidate cells and 750 of
       random counted depth-4 cells, the cell bound is at least h^2 (or h^4) times the integrand at the point.
  (C5) The certificates: hux 2.28, cons 2.25, hux 2.29 and cons 2.27 at n = 600 below 1; hux 2.32 at n = 50 below 1;
       and hux 2.30 at n = 150 at least the probe's midpoint estimate at (200, 100).
  (C6) Decomposition costs from below (hux, 2.29, n = 200).  For 600 random decomposed cells that lie inside the
       depth-2 region (surely in the region and surely not evaluable), the certified cost is at least a lower bound
       computed independently.  The lower bound sums, over the depth-4 cells that lie inside the depth-4 region with
       their alpha3 cell inside the depth-3 region, h^4 times the infimum of the integrand: omega from the lower
       enclosure, the prefactor at the upper corner, rounded inward.  The lower bound must be positive for at least
       100 of the sampled cells.
Printed, not gated: the size of the coarse certificate (hux 2.32, n = 50); hux at 2.29 with n = 150, 300 and 600 under
the probe's rule and under the sharp rule, against the midpoint estimate at (400, 200), with the number and area of the
cells that the sharp rule may decompose and the probe's rule refuses; hux at 2.27 and cons at 2.24 with n = 600, both
above 1; the probe's midpoint estimates at (400, 200) for hux at 2.275 and cons at 2.245.
Sabotage cases, each of which must fail its gate: (k0) no outward rounding (C0); (k1) u1' from the pieces' right ends
without the last one, 11/12 (C1); (k2) omega's upper bound without the growth of F within an interval (C2); (k3) the
prefactors rounded to nearest (C3); (k4) the conditions for decomposition tested at the lower corner (C4); (k5) a
depth-2 cell dropped when its centre is evaluable (C4); (k6) the condition on alpha3 left out (C4); (k7) the
prefactors taken at the upper corner (C4); (k8) decomposition costs set to 0 (C6); (k9) sums neither inflated nor
rounded (C0).  The rounding of the cell computations is below what the point tests (C4) can see; C0 and C3 test it
against exact arithmetic.

Scope.  The certificate bounds the integral that defines the loss of this decomposition; it does not check that the
integral is the loss (section 44's analysis).  The bounds depend on the grid, and n is a choice.
"""
import itertools
import math
import os
import sys
import time
from fractions import Fraction as Fr

import mpmath
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieve_route_probe as probe  # noqa: E402

DEN = 1 << 40
NW = 1 << 16
UMAX = 16
EPS53 = 2.0 ** -53
MARGIN = Fr(1, 1 << 30)
CASES = (("hux", Fr(228, 100), 600), ("cons", Fr(225, 100), 600), ("hux", Fr(229, 100), 600),
         ("cons", Fr(227, 100), 600), ("hux", Fr(232, 100), 50))
SABOTAGE = {"k0": "C0", "k1": "C1", "k2": "C2", "k3": "C3", "k4": "C4", "k5": "C4", "k6": "C4", "k7": "C4",
            "k8": "C6", "k9": "C0"}


# ------------------------------------------------------------------------------------------------------- rounding

def up(x, mut=None):
    return x if mut == "k0" else np.nextafter(x, np.inf)


def dn(x, mut=None):
    return x if mut == "k0" else np.nextafter(x, -np.inf)


def inflate(s, n, mut=None):
    """At least the exact sum of n nonnegative floats whose computed sum, in any order, is s."""
    if mut == "k9":
        return s
    return up(s * up(1.0 + 4.0 * n * EPS53, mut), mut)


def deflate(s, n, mut=None):
    """At most the exact sum of n nonnegative floats whose computed sum, in any order, is s."""
    return dn(s * dn(1.0 - 4.0 * n * EPS53, mut), mut)


# ---------------------------------------------------------------------------------------------------------- omega

def omega_enclosure(mut=None):
    """Arrays lo, hi with lo[i] <= omega(t) <= hi[i] for t in [i d, (i + 1) d), d = 2^-16, 1 <= t < UMAX."""
    n = UMAX * NW
    lo, hi = np.zeros(n), np.zeros(n)
    d = 1.0 / NW
    i = np.arange(NW, 2 * NW)
    lo[NW:2 * NW] = dn(1.0 / ((i + 1) * d), mut)
    hi[NW:2 * NW] = up(1.0 / (i * d), mut)
    lo_l, hi_l = lo.tolist(), hi.tolist()
    nx = (lambda x, y: x) if mut == "k0" else math.nextafter
    inf = math.inf
    flo = fhi = 1.0
    for k in range(2 * NW, n):
        a, b = lo_l[k - NW], hi_l[k - NW]
        t0, t1 = k * d, (k + 1) * d
        lo_l[k] = nx(flo / t1, -inf)
        top = nx(fhi + d * b, inf)
        hi_l[k] = nx((fhi if mut == "k2" else top) / t0, inf)
        flo = nx(flo + d * a, -inf)
        fhi = top
    return np.array(lo_l), np.array(hi_l)


def _sparse(arr, f):
    st, k = [arr], 1
    while (1 << k) <= len(arr):
        prev, span = st[-1], 1 << (k - 1)
        st.append(f(prev[:-span], prev[span:]))
        k += 1
    return st


def _query(st, f, l, r):
    k = np.floor(np.log2(r - l + 1)).astype(np.int64)
    out = np.empty(l.shape)
    for lev in np.unique(k):
        m = k == lev
        out[m] = f(st[lev][l[m]], st[lev][r[m] - (1 << lev) + 1])
    return out


class OmegaBounds:
    """Bounds for the supremum and infimum of omega on intervals of arguments, from the enclosure."""

    def __init__(self, mut=None):
        self.lo, self.hi = omega_enclosure(mut)
        self.st_hi = _sparse(self.hi, np.maximum)
        self.st_lo = _sparse(self.lo, np.minimum)

    @staticmethod
    def _range(lo_arg, hi_arg):
        if np.any(hi_arg >= UMAX):
            raise ValueError("omega argument beyond the table")
        l = np.floor(np.maximum(lo_arg, 1.0) * NW).astype(np.int64)
        return l, np.maximum(np.floor(hi_arg * NW).astype(np.int64), l)

    def sup(self, lo_arg, hi_arg):
        lo_arg, hi_arg = np.asarray(lo_arg, dtype=float), np.asarray(hi_arg, dtype=float)
        zero = hi_arg < 1.0
        l, r = self._range(lo_arg, np.where(zero, 1.0, hi_arg))
        return np.where(zero, 0.0, _query(self.st_hi, np.maximum, l, r))

    def inf(self, lo_arg, hi_arg):
        lo_arg, hi_arg = np.asarray(lo_arg, dtype=float), np.asarray(hi_arg, dtype=float)
        zero = lo_arg < 1.0
        l, r = self._range(np.where(zero, 1.0, lo_arg), np.where(zero, 1.0, hi_arg))
        return np.where(zero, 0.0, _query(self.st_lo, np.minimum, l, r))


def omega_ref(u, fine):
    """omega at the rational point u: closed forms at 40 digits on [1, 4), the probe's fine table above 4."""
    mpmath.mp.dps = 40
    x = mpmath.mpf(u.numerator) / u.denominator
    if x < 1:
        return mpmath.mpf(0)
    if x < 2:
        return 1 / x
    if x < 3:
        return (1 + mpmath.log(x - 1)) / x
    if x < 4:
        return (1 + mpmath.log(x - 1) + mpmath.quad(lambda s: mpmath.log(s - 1) / s, [2, x - 1])) / x
    us, tab = fine
    return mpmath.mpf(float(np.interp(float(x), us, tab)))


# -------------------------------------------------------------------------------------------------------- windows

PIECES = {"hux": ((Fr(1, 2), Fr(3, 4), "ing"), (Fr(3, 4), Fr(11, 12), "hux")),
          "cons": ((Fr(1, 2), Fr(5, 7), "ing"), (Fr(5, 7), Fr(16, 21), "c73"), (Fr(16, 21), Fr(11, 12), "hux"))}
AMAX = {"hux": Fr(12, 5), "cons": Fr(7, 3)}


def A_of(kind, b):
    if kind == "ing":
        return 3 / (2 - b)
    if kind == "hux":
        return 3 / (3 * b - 1)
    return Fr(7, 3)


def lower_exact(kind, b, L):
    return (A_of(kind, b) * (1 - b) / 2 + Fr(1, 2) - L * (1 - b)) / (b - Fr(1, 2))


def window_ends(L, curve, mut=None):
    ends = [(b1, kind) for _, b1, kind in PIECES[curve]]
    if mut == "k1":
        ends = ends[:-1]
    m1 = max(lower_exact(kind, b, L) for b, kind in ends) / L
    U1 = math.ceil((m1 + MARGIN) * DEN)
    U2 = math.floor((min((L - AMAX[curve] / 2) / L, Fr(1, 2)) - MARGIN) * DEN)
    return U1, U2


def certify_window(L, curve, U1, U2):
    T = Fr(U1, DEN) * L
    boxes, ok = 0, T > 0 and L > 2
    for b0, b1, kind in PIECES[curve]:
        ok &= max(A_of(kind, b0), A_of(kind, b1)) <= AMAX[curve]
        stack = [(b0, b1)]
        while stack and ok:
            x0, x1 = stack.pop()
            boxes += 1
            nhi = A_of(kind, x0) * (1 - x0) / 2 + Fr(1, 2) - L * (1 - x1)
            if nhi <= 0 or (x0 > Fr(1, 2) and nhi / (x0 - Fr(1, 2)) <= T):
                continue
            if x1 - x0 < Fr(1, 1 << 80):
                ok = False
                break
            mid = (x0 + x1) / 2
            stack += [(x0, mid), (mid, x1)]
    u2 = Fr(U2, DEN)
    ok = ok and u2 <= (L - AMAX[curve] / 2) / L and u2 <= Fr(1, 2) and U1 < U2 and u2 * L > 1
    return ok, boxes


# ------------------------------------------------------------------------------ the decomposition on the integer grid

def inside(lo, hi, U1, U2):
    return ((lo > U1) & (hi < U2)) | ((lo > DEN - U2) & (hi < DEN - U1))


def surely_evaluable(los, his, U1, U2):
    out = np.zeros(np.broadcast(*los, *his).shape, dtype=bool)
    for r in range(1, len(los) + 1):
        for S in itertools.combinations(range(len(los)), r):
            out |= inside(sum(los[i] for i in S), sum(his[i] for i in S), U1, U2)
    return out


def surely_unevaluable(los, his, U1, U2):
    out = np.ones(np.broadcast(*los, *his).shape, dtype=bool)
    for r in range(1, len(los) + 1):
        for S in itertools.combinations(range(len(los)), r):
            lo, hi = sum(los[i] for i in S), sum(his[i] for i in S)
            out &= ((hi <= U1) | (lo >= U2)) & ((hi <= DEN - U2) | (lo >= DEN - U1))
    return out


def point_evaluable(alphas, U1, U2):
    return surely_evaluable(alphas, alphas, U1, U2)


class Cert:
    """Section 44's decomposition on the grid of n cells a side from v, with the proved window of (L, curve)."""

    def __init__(self, L, curve, n, om, mut=None, rule="sharp"):
        self.L, self.curve, self.n, self.om, self.mut, self.rule = L, curve, n, om, mut, rule
        self.U1, self.U2 = window_ends(L, curve, mut)
        self.V, self.R = self.U2 - self.U1, DEN - self.U2
        self.H = -(-(DEN // 2 - self.V) // n)
        self.e = self.V + self.H * np.arange(n, dtype=np.int64)
        self.h = self.H / DEN
        self.h2 = up(self.h * self.h, mut)
        self.h4 = up(self.h2 * self.h2, mut)

    def pref2(self, a, b):
        if self.mut == "k7":
            a, b = a + self.H, b + self.H
        af, bf = a / DEN, b / DEN
        if self.mut == "k3":
            return 1.0 / (af * bf * bf)
        return up(1.0 / dn(dn(af * bf, self.mut) * bf, self.mut), self.mut)

    def pref4(self, a, b, c, d):
        if self.mut == "k7":
            a, b, c, d = a + self.H, b + self.H, c + self.H, d + self.H
        af, bf, cf, df = a / DEN, b / DEN, c / DEN, d / DEN
        if self.mut == "k3":
            return 1.0 / (af * bf * cf * df * df)
        m = self.mut
        return up(1.0 / dn(dn(dn(dn(af * bf, m) * cf, m) * df, m) * df, m), m)

    def args2(self, a, b):
        H = self.H
        return dn((DEN - a - b - 2 * H) / (b + H), self.mut), up((DEN - a - b) / b, self.mut)

    def args4(self, a, b, c, d):
        H = self.H
        return dn((DEN - a - b - c - d - 4 * H) / (d + H), self.mut), up((DEN - a - b - c - d) / d, self.mut)

    def bound2(self, a, b):
        om = self.om.sup(*self.args2(a, b))
        return up(up(self.h2 * om, self.mut) * self.pref2(a, b), self.mut)

    def bound4(self, a, b, c, d):
        om = self.om.sup(*self.args4(a, b, c, d))
        return up(up(self.h4 * om, self.mut) * self.pref4(a, b, c, d), self.mut)

    def candidates(self):
        """The depth-2 cells that may meet the region and may be non-evaluable."""
        e, H, U1, U2 = self.e, self.H, self.U1, self.U2
        a, b = e[:, None], e[None, :]
        A, B = a + H, b + H
        if self.mut == "k5":
            maybe_ne = ~point_evaluable([a + H // 2, b + H // 2], U1, U2)
        else:
            maybe_ne = ~surely_evaluable([a, b], [A, B], U1, U2)
        return (b < A) & (2 * a < DEN) & (a + 2 * b <= DEN) & ~((a > U1) & (A < U2)) & maybe_ne

    def inner(self, i, j):
        """None when decomposition is not allowed on the whole cell (i, j); otherwise the indices of the alpha3 cells
        that may be non-evaluable, and the matrix over (those, every alpha4 cell) of the depth-4 cells that may meet
        the region and may be non-evaluable.  The sharp rule: the cell's sum alpha1 + alpha2, and the sum
        alpha1 + alpha2 + alpha3 over every alpha3 cell that may be non-evaluable, stay below 1 - u1'.  A
        non-evaluable point then has these sums at most R = 1 - u2', because (R, 1 - u1') is the complement window.
        The rule "whole" is round 576's: the same sums at most R on the whole cell."""
        e, H, U1, U2, R, mut = self.e, self.H, self.U1, self.U2, self.R, self.mut
        lim = R + 1 if self.rule == "whole" else DEN - U1
        a, b = int(e[i]), int(e[j])
        A, B = a + H, b + H
        if (a + b if mut == "k4" else A + B) >= lim:
            return None
        kk = np.nonzero((e < B) & (a + b + 2 * e <= DEN))[0]
        c = e[kk]
        ne3 = ~surely_evaluable([a, b, c], [A, B, c + H], U1, U2) if c.size else np.zeros(0, bool)
        if not ne3.any():
            return kk[ne3], np.zeros((0, self.n), dtype=bool)
        top = (a + b + c[ne3]) if mut == "k4" else (A + B + c[ne3] + H)
        if mut != "k6" and np.any(top >= lim):
            return None
        c3, d = c[ne3][:, None], e[None, :]
        ok = (d < c3 + H) & (a + b + c3 + 2 * d <= DEN) & ~surely_evaluable([a, b, c3, d], [A, B, c3 + H, d + H], U1, U2)
        return kk[ne3], ok

    def ref_cost(self, i, j):
        """The certified cost of decomposing cell (i, j), or None when not allowed."""
        cells = self.inner(i, j)
        if cells is None:
            return None
        if self.mut == "k8":
            return 0.0
        k3, ok = cells
        rows, cols = np.nonzero(ok)
        if not rows.size:
            return 0.0
        f = self.bound4(int(self.e[i]), int(self.e[j]), self.e[k3][rows], self.e[cols])
        return float(inflate(float(f.sum()), int(f.size), self.mut))

    def outer(self, record=False):
        cand = self.candidates()
        ii, jj = np.nonzero(cand)
        drop = self.bound2(self.e[ii], self.e[jj])
        use_ref, allowed = np.zeros_like(cand), np.zeros_like(cand)
        bests = []
        for t, (i, j) in enumerate(zip(ii, jj)):
            best = float(drop[t])
            ref = self.ref_cost(i, j)
            allowed[i, j] = ref is not None
            if ref is not None and ref < best:
                best = ref
                use_ref[i, j] = True
            bests.append(best)
        total = float(inflate(math.fsum(bests), len(bests), self.mut))
        return (total, {"cand": cand, "use_ref": use_ref, "allowed": allowed}) if record else total


# ---------------------------------------------------------------------------------------------------------- gates

def c0(mut=None, cases=20000, seed=5780):
    rng = np.random.default_rng(seed)
    x = rng.uniform(0.5, 1.0, cases) * 2.0 ** rng.integers(-40, 41, cases) * rng.choice([-1.0, 1.0], cases)
    y = rng.uniform(0.5, 1.0, cases) * 2.0 ** rng.integers(-40, 41, cases) * rng.choice([-1.0, 1.0], cases)
    bad = 0
    for f, g in ((np.add, lambda p, q: p + q), (np.multiply, lambda p, q: p * q), (np.divide, lambda p, q: p / q)):
        r = f(x, y)
        for xi, yi, l, h in zip(x.tolist(), y.tolist(), dn(r, mut).tolist(), up(r, mut).tolist()):
            ex = g(Fr(xi), Fr(yi))
            bad += not (Fr(l) <= ex <= Fr(h))
    sums = 0
    for _ in range(200):
        arr = rng.uniform(0, 1, 1000) * 2.0 ** rng.integers(-20, 21, 1000)
        sums += Fr(float(inflate(float(np.sum(arr)), arr.size, mut))) < sum(Fr(v) for v in arr.tolist())
    return bad == 0 and sums == 0, {"ops": 3 * cases, "bad": bad, "arrays": 200, "sums_low": sums}


def c1(mut=None):
    rows, ok = [], True
    for curve, L, _ in CASES:
        U1, U2 = window_ends(L, curve, mut)
        good, boxes = certify_window(L, curve, U1, U2)
        ok &= good
        rows.append((curve, float(L), U1 / DEN, U2 / DEN, boxes, good))
    return ok, rows


def c2(om, fine, seed=5782, n_low=1500, n_high=3000):
    rng = np.random.default_rng(seed)
    lo, hi = om.lo[NW:], om.hi[NW:]
    order, width = int(np.sum(lo > hi)), float(np.max(hi - lo))
    tol = mpmath.mpf("1e-8")
    miss_low = miss_high = 0
    for start, stop, count in ((1, 4, n_low), (4, UMAX, n_high)):
        for _ in range(count):
            u = Fr(int(rng.integers(start << 30, stop << 30)), 1 << 30)
            k = math.floor(u * NW)
            r = omega_ref(u, fine)
            if start == 1:
                miss_low += not (mpmath.mpf(om.lo[k]) <= r <= mpmath.mpf(om.hi[k]))
            else:
                miss_high += not (mpmath.mpf(om.lo[k]) - tol <= r <= mpmath.mpf(om.hi[k]) + tol)
    ok = order == 0 and width < 1e-4 and miss_low == 0 and miss_high == 0
    return ok, {"order": order, "width": width, "miss_low": miss_low, "n_low": n_low, "miss_high": miss_high,
                "n_high": n_high}


def _exact_sup(om, lo_ex, hi_ex):
    if hi_ex < 1:
        return Fr(0)
    l, r = math.floor(max(lo_ex, Fr(1)) * NW), math.floor(hi_ex * NW)
    return Fr(float(np.max(om.hi[l:r + 1])))


def c3(om, mut=None, samples=1500, seed=5783):
    rng = np.random.default_rng(seed)
    c = Cert(Fr(229, 100), "hux", 150, om, mut)
    H, hx = c.H, Fr(c.H, DEN)
    ii, jj = np.nonzero(c.candidates())
    bad = dict.fromkeys(("args2", "om2", "pref2", "bound2", "args4", "om4", "pref4", "bound4"), 0)

    def replay(tag, cs, lo_ex, hi_ex, pref_ex, hpow, args_f, pref_f, bound_f):
        lo_f, hi_f = args_f(*cs)
        bad["args" + tag] += not (Fr(float(lo_f[0])) <= lo_ex and Fr(float(hi_f[0])) >= hi_ex)
        om_ex = _exact_sup(om, lo_ex, hi_ex)
        bad["om" + tag] += Fr(float(om.sup(lo_f, hi_f)[0])) < om_ex
        bad["pref" + tag] += Fr(float(pref_f(*cs)[0])) < pref_ex
        bad["bound" + tag] += Fr(float(bound_f(*cs)[0])) < hpow * om_ex * pref_ex

    for t in rng.choice(len(ii), samples):
        a, b = int(c.e[ii[t]]), int(c.e[jj[t]])
        replay("2", [np.array([a]), np.array([b])], Fr(DEN - a - b - 2 * H, b + H), Fr(DEN - a - b, b),
               Fr(DEN ** 3, a * b * b), hx ** 2, c.args2, c.pref2, c.bound2)
    _, rec = c.outer(record=True)
    refined = np.argwhere(rec["use_ref"])
    done = 0
    while done < samples:
        i, j = refined[rng.integers(len(refined))]
        k3, ok = c.inner(i, j)
        rows, cols = np.nonzero(ok)
        if not rows.size:
            continue
        s = rng.integers(rows.size)
        a, b, cc, d = int(c.e[i]), int(c.e[j]), int(c.e[k3[rows[s]]]), int(c.e[cols[s]])
        replay("4", [np.array([v]) for v in (a, b, cc, d)], Fr(DEN - a - b - cc - d - 4 * H, d + H),
               Fr(DEN - a - b - cc - d, d), Fr(DEN ** 5, a * b * cc * d * d), hx ** 4, c.args4, c.pref4, c.bound4)
        done += 1
    return sum(bad.values()) == 0, {"samples": samples, **bad}


def rule_audit(c, use_ref):
    """An independent implementation of the sharp whole-cell rule; returns the number of decomposed cells breaking it."""
    H, e = c.H, [int(x) for x in c.e]
    top = DEN - c.U1
    wins = ((c.U1, c.U2), (DEN - c.U2, DEN - c.U1))
    bad = 0
    for i, j in np.argwhere(use_ref):
        a, b = e[i], e[j]
        if not a + b + 2 * H < top:
            bad += 1
            continue
        for cc in e:
            if not (cc < b + H and a + b + 2 * cc <= DEN):
                continue
            lows, sure = (a, b, cc), False
            for mask in range(1, 8):
                s = sum(lows[k] for k in range(3) if mask >> k & 1)
                w = H * bin(mask).count("1")
                if any(w0 < s and s + w < w1 for w0, w1 in wins):
                    sure = True
                    break
            if not sure and not a + b + cc + 3 * H < top:
                bad += 1
                break
    return bad


def c4(om, fine, mut=None, draws=20000, pts=1500, seed=5784):
    rng = np.random.default_rng(seed)
    c = Cert(Fr(229, 100), "hux", 200, om, mut)
    _, rec = c.outer(record=True)
    cand, use_ref = rec["cand"], rec["use_ref"]
    V, H, U1, U2, R, n, e = c.V, c.H, c.U1, c.U2, c.R, c.n, c.e
    idx = lambda x: np.clip((np.asarray(x) - V) // H, 0, n - 1)
    x1, x2 = rng.integers(V, DEN // 2, draws), rng.integers(V, DEN // 2, draws)
    reg = (x2 < x1) & (x1 + 2 * x2 <= DEN) & ~((x1 > U1) & (x1 < U2)) & ~point_evaluable([x1, x2], U1, U2)
    miss1 = int(np.sum(reg & ~cand[idx(x1), idx(x2)]))
    miss2 = miss3 = tested2 = tested3 = 0
    for i, j in np.argwhere(use_ref):
        lo1, lo2 = int(e[i]), int(e[j])
        cells = c.inner(i, j)
        corners = ((lo1 + H - 1, lo2 + H - 1), (lo1 + H - 1, lo2 + 1), (lo1 + 1, lo2 + H - 1),
                   (lo1 + int(rng.integers(0, H)), lo2 + int(rng.integers(0, H))))
        for t, (p1, p2) in enumerate(corners):
            if not (p2 < p1 and p1 + 2 * p2 <= DEN) or (U1 < p1 < U2) or point_evaluable([p1, p2], U1, U2):
                continue
            grid = np.arange(V, min(p2, (DEN - p1 - p2) // 2 + 1), DEN // 10 ** 4, dtype=np.int64)
            ne = grid[~point_evaluable([p1, p2, grid], U1, U2)] if grid.size else grid
            tested2 += 1
            miss2 += p1 + p2 > R or bool(ne.size and p1 + p2 + int(ne.max()) > R)
            if t < 3 or not ne.size or cells is None:
                continue
            p3 = int(rng.choice(ne))
            hi4 = min(p3, (DEN - p1 - p2 - p3) // 2 + 1)
            if hi4 <= V:
                continue
            p4 = int(rng.integers(V, hi4))
            if point_evaluable([p1, p2, p3, p4], U1, U2):
                continue
            tested3 += 1
            k3, ok = cells
            k, l = int(idx(p3)), int(idx(p4))
            row = int(np.searchsorted(k3, k))
            miss3 += row >= len(k3) or k3[row] != k or not ok[row, l]
    audit = rule_audit(c, use_ref)
    mpmath.mp.dps = 40
    hx = mpmath.mpf(H) / DEN
    ii, jj = np.nonzero(cand)
    low2 = pos2 = 0
    for t in rng.choice(len(ii), pts):
        a, b = int(e[ii[t]]), int(e[jj[t]])
        p1, p2 = a + int(rng.integers(0, H)), b + int(rng.integers(0, H))
        val = omega_ref(Fr(DEN - p1 - p2, p2), fine) * mpmath.mpf(DEN) ** 3 / (mpmath.mpf(p1) * p2 * p2)
        if val > 0:
            pos2 += 1
            low2 += mpmath.mpf(float(c.bound2(np.array([a]), np.array([b]))[0])) < hx ** 2 * val
    refined = np.argwhere(use_ref)
    low4 = pos4 = tries = 0
    while pos4 < pts // 2 and tries < 20 * pts:
        tries += 1
        i, j = refined[rng.integers(len(refined))]
        k3, ok = c.inner(i, j)
        rows, cols = np.nonzero(ok)
        if not rows.size:
            continue
        s = rng.integers(rows.size)
        cs = [int(e[i]), int(e[j]), int(e[k3[rows[s]]]), int(e[cols[s]])]
        p = [v + int(rng.integers(0, H)) for v in cs]
        val = omega_ref(Fr(DEN - sum(p), p[3]), fine) * mpmath.mpf(DEN) ** 5 / (
            mpmath.mpf(p[0]) * p[1] * p[2] * p[3] * p[3])
        if val > 0:
            pos4 += 1
            low4 += mpmath.mpf(float(c.bound4(*[np.array([v]) for v in cs])[0])) < hx ** 4 * val
    ok = (miss1 == 0 and miss2 == 0 and miss3 == 0 and audit == 0 and low2 == 0 and low4 == 0
          and int(reg.sum()) > 1000 and tested2 > 1000 and tested3 > 100 and pos2 > pts // 2 and pos4 >= pts // 2)
    return ok, {"region": int(reg.sum()), "miss_region": miss1, "decomp_tests": tested2, "miss_decomp": miss2,
                "depth4_points": tested3, "miss_depth4": miss3, "audited": int(use_ref.sum()), "audit_breaks": audit,
                "points2": pos2, "low2": low2, "points4": pos4, "low4": low4}


def c5(om, mid, mut=None, full=True):
    rec = {"mid": float(mid), "hux230_n150": Cert(Fr(230, 100), "hux", 150, om, mut).outer()}
    ok = rec["hux230_n150"] >= mid
    for curve, L, n in CASES if full else CASES[-1:]:
        key = f"{curve}{int(L * 100)}_n{n}"
        rec[key] = Cert(L, curve, n, om, mut).outer()
        ok &= rec[key] < 1
    return ok, rec


def c6(om, mut=None, cells=600, seed=5786):
    rng = np.random.default_rng(seed)
    c = Cert(Fr(229, 100), "hux", 200, om, mut)
    _, rec = c.outer(record=True)
    e, H, U1, U2 = c.e, c.H, c.U1, c.U2
    hl = dn(c.h * c.h)
    h4lo = dn(hl * hl)
    ij = np.argwhere(rec["use_ref"])
    a, b = e[ij[:, 0]], e[ij[:, 1]]
    A, B = a + H, b + H
    interior = ((B <= a) & (2 * A <= DEN) & (A + 2 * B <= DEN) & ((A <= U1) | (a >= U2))
                & surely_unevaluable([a, b], [A, B], U1, U2))
    pool = ij[interior]
    low = positive = 0
    for t in rng.choice(len(pool), min(cells, len(pool)), replace=False):
        i, j = pool[t]
        a, b = int(e[i]), int(e[j])
        A, B = a + H, b + H
        cc = e[(e + H <= b) & (A + B + 2 * (e + H) <= DEN)]
        cc = cc[surely_unevaluable([a, b, cc], [A, B, cc + H], U1, U2)] if cc.size else cc
        lower = 0.0
        if cc.size:
            c3, d = cc[:, None], e[None, :]
            C3, D = c3 + H, d + H
            inner = (D <= c3) & (A + B + C3 + 2 * D <= DEN) & surely_unevaluable([a, b, c3, d], [A, B, C3, D], U1, U2)
            rows, cols = np.nonzero(inner)
            if rows.size:
                C, Dd = cc[rows] + H, e[cols] + H
                lo_arg = dn((DEN - A - B - C - Dd) / Dd)
                hi_arg = up((DEN - a - b - cc[rows] - e[cols]) / e[cols])
                om_inf = om.inf(lo_arg, hi_arg)
                p = up(up(up(up((A / DEN) * (B / DEN)) * (C / DEN)) * (Dd / DEN)) * (Dd / DEN))
                f = dn(dn(h4lo * om_inf) * dn(1.0 / p))
                lower = float(deflate(float(f.sum()), int(f.size)))
        positive += lower > 0
        low += c.ref_cost(i, j) < lower
    ok = low == 0 and positive >= 100
    return ok, {"cells": int(min(cells, len(pool))), "interior_pool": int(len(pool)), "lower_positive": positive,
                "below_lower": low}


def run(fine, mid, mut=None, full=False):
    om = OmegaBounds(mut)
    gates = {"C0": lambda: c0(mut), "C1": lambda: c1(mut), "C2": lambda: c2(om, fine), "C3": lambda: c3(om, mut),
             "C4": lambda: c4(om, fine, mut), "C5": lambda: c5(om, mid, mut, full), "C6": lambda: c6(om, mut)}
    return {k: f() for k, f in gates.items()}


def main():
    t0 = time.time()
    fine = probe.omega_table(2.5e-5)
    mid = probe.midpoint(2.30, "hux", 200, 100, probe.Omega())
    res = run(fine, mid, full=True)
    for k, (ok, rec) in res.items():
        print(f"{k}: {'pass' if ok else 'FAIL'} {rec}", flush=True)
    om = OmegaBounds()
    c = Cert(Fr(232, 100), "hux", 50, om)
    tot, rec = c.outer(record=True)
    terms = sum(int(c.inner(i, j)[1].sum()) for i, j in np.argwhere(rec["use_ref"]))
    print(f"  coarse certificate hux 2.32, n = 50: bound {tot:.6f}; {int(rec['cand'].sum())} depth-2 cells, "
          f"{int(rec['use_ref'].sum())} decomposed, {terms} depth-4 cells", flush=True)
    rows, gaps = [], []
    for n in (150, 300, 600):
        cw, cs = Cert(Fr(229, 100), "hux", n, om, rule="whole"), Cert(Fr(229, 100), "hux", n, om)
        (tw, rw), (ts, rs) = cw.outer(record=True), cs.outer(record=True)
        extra = int(np.sum(rs["allowed"] & ~rw["allowed"]))
        rows.append(f"n = {n}: {tw:.4f} (round 576's rule), {ts:.4f} (sharp)")
        gaps.append(f"n = {n}: {extra} cells, area {extra * cs.h ** 2:.5f}")
    print(f"  hux 2.29 by grid: {'; '.join(rows)}; midpoint at (400,200) "
          f"{probe.midpoint(2.29, 'hux', 400, 200, probe.Omega()):.4f}", flush=True)
    print(f"  cells the sharp rule may decompose and round 576's rule refuses (hux 2.29): {'; '.join(gaps)}", flush=True)
    print(f"  above 1 at n = 600: hux 2.27 {Cert(Fr(227, 100), 'hux', 600, om).outer():.4f}, cons 2.24 "
          f"{Cert(Fr(224, 100), 'cons', 600, om).outer():.4f}", flush=True)
    pom = probe.Omega()
    mids = [(cv, L, probe.midpoint(L, cv, 400, 200, pom)) for cv, L in (("hux", 2.275), ("cons", 2.245))]
    print(f"  midpoint estimates at (400,200) near the thresholds: "
          f"{', '.join(f'{cv} {L} {m:.4f}' for cv, L, m in mids)}", flush=True)
    caught = {}
    for m, gate in SABOTAGE.items():
        r = run(fine, mid, m)
        caught[m] = not r[gate][0]
        print(f"  sabotage {m}: gate {gate} {'fails (caught)' if caught[m] else 'passes (MISSED)'}; failing gates "
              f"{[k for k, v in r.items() if not v[0]]}", flush=True)
    ok = all(v[0] for v in res.values())
    print(f"gates {'pass' if ok else 'FAIL'}; sabotage {sum(caught.values())}/{len(caught)} caught; "
          f"{time.time() - t0:.0f}s", flush=True)
    return 0 if ok and all(caught.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
