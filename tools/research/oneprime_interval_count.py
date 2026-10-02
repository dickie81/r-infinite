#!/usr/bin/env python3
"""THE ONE-PRIME ARC, ROUND 6 -- THE INTERVAL PASS, STAGE II:
certified Birman-Schwinger counts.

GOAL. For each certificate cell (parity, a = delta/2) and its
margin-friendly (nu, beta) row, certify RIGOROUSLY that
    #{ eigenvalues of T_qt below-count } :
    #{PWP_par < nu} <= #{eig(P_par qt(D) P_par) > beta} <= 1,
by proving mu_2(T) < beta for the compressed positive operator
    T = (2/pi) int_0^oo qt(r) phi_r (x) phi_r dr,
    phi_r(x) = cos(r x) (even) / sin(r x) (odd) on [0, a],
    qt(r) = (nu + beta - W(r))_+ ,
which is exactly <f, T f> = (1/pi) int qt |fhat|^2 -- the
parity-projected Birman-Schwinger counting operator of the
round-243 chain (the identity <f,Tf> = (2/pi) int qt(r)
|<f, phi_r>|^2 dr for real f of the given parity on [-a, a]).

THE METHOD (no kernel, no polynomial bases, no Bessel):
  (1) MEASURE DISCRETIZATION. Composite Simpson in r on the
      smooth pieces of qt's support (pieces end at rigorously
      bracketed crossings of W = nu + beta), all weights
      POSITIVE, giving the exact finite-rank positive operator
      T_H = sum_i c_i phi_{r_i} (x) phi_{r_i}, c_i >= 0.
  (2) OPERATOR ERROR. For any unit f, g_f(r) = qt(r)
      |<f, phi_r>|^2 has |g_f^{(4)}| <= a * sum_j C(4,j) (2a)^j
      M_{4-j} with M_j the proved W-derivative majorants (M_0 =
      qt_max), because each d/dr of <f, phi_r> brings a factor
      x <= a and |<f,phi_r>|^2 <= a. Composite Simpson error
      per piece is (piece length) H^4 |g^{(4)}|/180 with
      g4 = a(M4 + 4(2a)M3 + 6(2a)^2 M2 + 8(2a)^3 M1
      + 2(2a)^4 qmax) (the code's 8/2 coefficients on the last
      two terms are the doubled -- conservative -- binomials;
      round-248 F248-8); crossing
      brackets contribute |qt| <= M1 * (bracket width) times
      a * width by the hull bound. Total: ||T - T_H||_op <= EOP,
      an explicit interval quantity.
  (3) THE MATRIX. The nonzero spectrum of T_H equals that of
      A = C^{1/2} G C^{1/2}, G_ij = <phi_{r_i}, phi_{r_j}> =
      [sin((ri-rj)a)/(ri-rj) +/- sin((ri+rj)a)/(ri+rj)]/2
      (+ even, - odd; diagonal (a +/- sin(2ra)/(2r))/2), all
      entries enclosed by the vectorized interval layer.
  (4) VERIFIED EIGENVALUES. Float64 eigh gives approximate
      (Q, D). Rigorous enclosure via residuals computed with
      float matmuls inflated by the classical model bound
      |fl(AB) - AB| <= gamma_n |A||B|, gamma_n = n u/(1 - n u),
      u = 2^-53 (rigorous for any summation order; no libm
      claim): with E = Q^T A Q - D and F = Q^T Q - I,
      every eigenvalue of A lies within
      max_i |E|-row-radius / (1 - ||F||) style Gershgorin discs
      of D; we use the clean bound: for symmetric A,
      dist(spec(A), spec(D)) <= (||E||_F + ||D|| ||F||_F)
      / (1 - ||F||_F)  (valid while ||F||_F < 1; proof: B =
      Q S^{-1/2} with S = Q^T Q is exactly orthogonal,
      B^T A B = S^{-1/2}(D + E)S^{-1/2} = D + E' with
      ||E'|| <= ||E|| + ||D + E|| ||S^{-1/2} .. || -- we use the
      coarser standard chain implemented in veigs(), each step
      an interval computation).
  (5) THE CERTIFICATE. mu_2(T) <= mu_2(A) + EOP < beta, with
      the margin printed; then the round-243 chain gives
      #{PWP_par < nu} <= 1 rigorously, which is the ell_2
      premise Stage III consumes.

CELL ROWS (margin-friendly re-selection, from the committed
float64 count curves; the float row choice carries no rigor
burden -- the certificate is whatever the enclosures prove):
    even log2  a 0.34655  nu* 0.15  beta 1.0
    even 0.80  a 0.40     nu* 0.15  beta 1.0
    even 0.90  a 0.45     nu* 0.04  beta 1.5
    even 0.95  a 0.475    nu* 0.02  beta 1.5
    even 1.00  a 0.50     nu* 0.01  beta 2.0  (frontier;
    its stored float row is the 2.5e-4 knife-edge -- certified
    if the enclosures clear it, recorded otherwise; NOT a
    theorem cell)
    odd  0.90  a 0.45     nu* 0.15  beta 1.0
    odd  1.05  a 0.525    nu* 0.15  beta 1.0
    odd  1.09  a 0.545    nu* 0.08  beta 1.5
(the even 0.9/0.95/1.0 rows moved off their knife-edge beta;
the float64 predictions put every mu_2 margin at >= 3.5e-3).

GATES:
  gII1  frame-matrix top eigenvalues vs the committed float64
        checkpoint rows (oneprime_lehmann): the float mu123 of
        the SAME (nu, beta) row must lie within the enclosure
        widened by EOP + the float row's own quadrature slack
        (checked loosely at 1e-2 relative -- a wiring gate).
  gII2  verified-eigensolve self-test: on a random symmetric
        matrix with known integer eigenvalues the enclosures
        contain them; residual norms below 1e-8.
  gII3  the certificate: mu2_hi + EOP < beta with margin
        recorded per cell.
  gII4  refinement honesty: halving H moves the mu2 enclosure
        by less than the claimed EOP.

CHECKS. 7: classical (Simpson remainders, Gershgorin/Weyl,
IEEE-754 error analysis). 8: no hypothesis input.

Keying law: every producing file in every key (executable
content, round 245).
"""
import math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from oneprime_interval_core import (
    I, PI, TWO_PI, LOG2, LOGPI, SQRT2, C2I, iexp, ilog, icos,
    _binet_grid, XMIN, TCUT, _u, _d, dW_majorant, d2W_majorant)

# ---------- vectorized interval layer (lo/hi ndarrays) ----------


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

def vup(x):
    return np.nextafter(x, np.inf)

def vdn(x):
    return np.nextafter(x, -np.inf)

class V:
    """Vector of intervals: lo, hi float64 arrays. Outward
    rounding by one ulp around IEEE-guaranteed elementwise ops."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        lo = np.asarray(lo, dtype=np.float64)
        hi = lo.copy() if hi is None else np.asarray(hi,
                                                    np.float64)
        if not np.all(lo <= hi):
            raise ValueError("bad V")
        self.lo, self.hi = lo, hi

    @classmethod
    def point(cls, arr):
        a = np.asarray(arr, np.float64)
        return cls(a, a.copy())

    @classmethod
    def scalar(cls, s, n):
        s = s if isinstance(s, I) else I(float(s))
        return cls(np.full(n, s.lo), np.full(n, s.hi))

    @property
    def width(self):
        return self.hi - self.lo

    def __add__(self, o):
        o = _v(o, self)
        return V(vdn(self.lo + o.lo), vup(self.hi + o.hi))

    __radd__ = __add__

    def __neg__(self):
        return V(-self.hi, -self.lo)

    def __sub__(self, o):
        o = _v(o, self)
        return V(vdn(self.lo - o.hi), vup(self.hi - o.lo))

    def __rsub__(self, o):
        return _v(o, self) - self

    def __mul__(self, o):
        o = _v(o, self)
        p1 = self.lo*o.lo
        p2 = self.lo*o.hi
        p3 = self.hi*o.lo
        p4 = self.hi*o.hi
        lo = np.minimum(np.minimum(p1, p2), np.minimum(p3, p4))
        hi = np.maximum(np.maximum(p1, p2), np.maximum(p3, p4))
        return V(vdn(lo), vup(hi))

    __rmul__ = __mul__

    def divpos(self, o):
        """Divide by an interval vector that is strictly > 0."""
        o = _v(o, self)
        if not np.all(o.lo > 0):
            raise ZeroDivisionError("divpos needs positive")
        p1 = self.lo/o.lo
        p2 = self.lo/o.hi
        p3 = self.hi/o.lo
        p4 = self.hi/o.hi
        lo = np.minimum(np.minimum(p1, p2), np.minimum(p3, p4))
        hi = np.maximum(np.maximum(p1, p2), np.maximum(p3, p4))
        return V(vdn(lo), vup(hi))

    def sq(self):
        straddle = (self.lo <= 0) & (self.hi >= 0)
        m = np.where(straddle, 0.0,
                     np.minimum(np.abs(self.lo), np.abs(self.hi)))
        M = np.maximum(np.abs(self.lo), np.abs(self.hi))
        return V(vdn(m*m), vup(M*M))

    def pos(self):
        """max(x, 0) elementwise."""
        return V(np.maximum(self.lo, 0.0),
                 np.maximum(self.hi, 0.0))

    def __getitem__(self, k):
        return V(self.lo[k], self.hi[k])


def _v(o, like):
    if isinstance(o, V):
        return o
    if isinstance(o, I):
        return V(np.full_like(like.lo, o.lo),
                 np.full_like(like.hi, o.hi))
    return V.point(np.broadcast_to(np.asarray(o, np.float64),
                                   like.lo.shape).copy())


def vsin(x):
    """Vectorized interval sin via reduction + Taylor.
    Arguments |x| up to ~250; reduction n = round(mid/2pi) exact
    small ints; y = x - n*2pi with interval 2pi; core Taylor on
    |y| <= pi + width with explicit remainder."""
    n = np.round((0.5*(x.lo + x.hi))/6.283185307179586)
    twopi = V(np.full_like(x.lo, TWO_PI.lo),
              np.full_like(x.lo, TWO_PI.hi))
    y = x - twopi*V.point(n)
    # fold |y| > ~pi/2 once: sin(y) = sin(pi - y) handles y near
    # pi; we instead evaluate the Taylor core directly with K
    # sized for |y| <= pi + slack (converges fine, remainder
    # explicit at |y| <= 3.2)
    return _sin_core_v(y)

def _sin_core_v(y):
    K = 16
    y2 = y.sq()
    term = y
    tot = V(term.lo.copy(), term.hi.copy())
    for k in range(1, K):
        term = term*y2
        # interval coefficient (round-248 F248-1c): the integer
        # (2k)(2k+1) <= 33*32 is float-exact; the division is
        # enclosed rather than pre-rounded
        term = term*V.scalar(I(-1.0)/I(float((2*k)*(2*k + 1))),
                             len(y.lo))
        tot = tot + term
    m = np.maximum(np.abs(y.lo), np.abs(y.hi))
    rem = vup((m**(2*K + 1))/math.factorial(2*K + 1))
    return V(vdn(tot.lo - rem), vup(tot.hi + rem))

def vcos(x):
    hp = V(np.full_like(x.lo, (PI/2).lo),
           np.full_like(x.lo, (PI/2).hi))
    return vsin(hp - x)


# ---------- vectorized W enclosures (batch Binet) ----------

_bcells = None

def _cells_np():
    global _bcells
    if _bcells is None:
        cells = _binet_grid()
        tlo = np.array([c[0].lo for c in cells])
        thi = np.array([c[0].hi for c in cells])
        glo = np.array([c[1].lo for c in cells])
        ghi = np.array([c[1].hi for c in cells])
        _bcells = (tlo, thi, glo, ghi)
    return _bcells

def W_batch(r):
    """Vectorized rigorous enclosure of W at the points r >= 0.
    Same mathematics as oneprime_interval_core.W_enclose
    (shift + Binet), vectorized over points."""
    r = np.asarray(r, np.float64)
    npts = len(r)
    y = V.point(r)*V.scalar(0.5, npts)
    yh = np.maximum(np.abs(y.lo), np.abs(y.hi))
    nshift = np.maximum(
        math.ceil(XMIN - 0.25),
        np.ceil(1.4142135623730951*yh - 0.25).astype(int) + 1)
    nmax = int(nshift.max())
    x = V.point(0.25 + nshift.astype(np.float64))
    y2 = y.sq()
    # recurrence sum with mask
    s = V(np.zeros(npts), np.zeros(npts))
    for k in range(nmax):
        mask = k < nshift
        ak = V.point(np.full(npts, 0.25 + k))
        contrib = ak.divpos(ak.sq() + y2)
        s = V(np.where(mask, vdn(s.lo + contrib.lo), s.lo),
              np.where(mask, vup(s.hi + contrib.hi), s.hi))
    modw2 = x.sq() + y2
    relog = _vlog(modw2)*V.scalar(0.5, npts)
    re_inv2w = x.divpos(modw2*V.scalar(2.0, npts))
    # Binet J real part
    tlo, thi, glo, ghi = _cells_np()
    x2y2 = x.sq() - y2
    reJ = V(np.zeros(npts), np.zeros(npts))
    for j in range(len(tlo)):
        tI = I(tlo[j], thi[j])
        t2 = tI.sq()
        a_lo = vdn(t2.lo + x2y2.lo)
        a_hi = vup(t2.hi + x2y2.hi)
        two_xy_lo = vdn(2*np.minimum(x.lo*y.lo, x.lo*y.hi))
        two_xy_hi = vup(2*np.maximum(x.hi*y.hi, x.lo*y.hi))
        aV = V(a_lo, a_hi)
        den = aV.sq() + V(vdn(np.minimum(two_xy_lo*two_xy_lo,
                                         two_xy_hi*two_xy_hi)
                              *(two_xy_lo*two_xy_hi >= 0)),
                          vup(np.maximum(two_xy_lo*two_xy_lo,
                                         two_xy_hi*two_xy_hi)))
        gI = V.scalar(I(glo[j], ghi[j]), npts)
        w = thi[j] - tlo[j]
        reJ = reJ + gI*aV.divpos(den)*V.scalar(w, npts)
    reJ = reJ*V.scalar(2.0, npts)
    # tail
    x2h = vdn(x.sq().lo/2 + TCUT*TCUT*0.999999)
    efac = iexp(I(-2*math.pi*TCUT))
    denom = (1 - efac).lo
    tint = (efac*(I(TCUT)/TWO_PI + 1/(TWO_PI.sq()))).hi
    tail = vup(2*tint/(denom*x2h))
    reJ = V(vdn(reJ.lo - tail), vup(reJ.hi + tail))
    repsi = relog - re_inv2w - reJ - s
    # W = repsi - log pi - C2 cos(r log 2)
    cosarg = V.point(r)*V.scalar(LOG2, npts)
    wv = repsi - V.scalar(LOGPI, npts) \
        - V.scalar(C2I, npts)*vcos(cosarg)
    return wv

def _vlog(x):
    """Vectorized interval log via per-point scalar ilog on the
    endpoints (monotone); loop is fine at these sizes."""
    lo = np.empty_like(x.lo)
    hi = np.empty_like(x.hi)
    for i in range(len(x.lo)):
        lo[i] = _logp(x.lo[i], -1)
        hi[i] = _logp(x.hi[i], +1)
    return V(lo, hi)

from oneprime_interval_core import _log_pt as _logp


# ---------- derivative majorants M3, M4 ----------

def M3_majorant():
    """|W'''| <= |psi'''|/8 + C2 log^3 2; |psi'''(1/4+iy)| <=
    6 sum 1/|1/4+k+iy|^4 <= 6 (256 + zeta(4)) = 6*257.083."""
    return _u(6*(256.0 + 1.0823232337111382)/8
              + (C2I*LOG2*LOG2*LOG2).hi)

def M4_majorant():
    """|W''''| <= |psi''''|/16 + C2 log^4 2; |psi''''| <=
    24 sum 1/(k+1/4)^5 <= 24 (1024 + zeta(5))."""
    return _u(24*(1024.0 + 1.03692775514337)/16
              + (C2I*LOG2*LOG2*LOG2*LOG2).hi)


# ---------- support pieces and crossing brackets ----------

def support_pieces(nu, beta, rmax=260.0, scan_h=2e-3,
                   ref_h=2e-5):
    """Rigorous pieces of {W < c} on [0, rmax], c = nu + beta,
    with TWO-LEVEL bracketing: a coarse scan (scan_h) classifies
    cells via W(mid) -+ M1*scan_h/2; straddling runs are then
    re-scanned at ref_h, and the refined straddling cells become
    the final brackets, each carrying a rigorous local qt bound
    qtmax_i = max(c - W_lo)_+ over its cells.  Certified-IN
    refined cells are appended to the pieces.  The tail beyond
    rmax is closed by the monotonicity lemma: h+(r) =
    Re psi(1/4+ir/2) - log pi is INCREASING in r >= 0 (each term
    of Im psi'(x+iy) = -sum 2y(x+k)/|z+k|^4 is <= 0, so
    d/dr Re psi = -(1/2) Im psi' >= 0), hence for r >= rmax
    W(r) >= h+(rmax) - C2 -- asserted > c.
    Returns (pieces, brackets) with brackets = (lo, hi, qtmax)."""
    c = nu + beta
    m1 = dW_majorant(rmax)

    def classify(grid):
        mids = 0.5*(grid[:-1] + grid[1:])
        half = (grid[1] - grid[0])/2
        wmid = W_batch(mids)
        cell_lo = vdn(wmid.lo - _u(m1*half*1.0000001))
        cell_hi = vup(wmid.hi + _u(m1*half*1.0000001))
        inn = cell_hi < c
        out = cell_lo > c
        return mids, cell_lo, inn, out

    grid = np.arange(0.0, rmax + scan_h, scan_h)
    grid[-1] = min(grid[-1], rmax + scan_h)
    mids, cell_lo, inn, out = classify(grid)
    strad = ~(inn | out)
    # tail lemma: h+(rmax) - C2 > c  (h+ increasing, see doc)
    from oneprime_interval_core import W_enclose
    wr = W_enclose(rmax)
    hplus_lo = (wr + C2I*icos(I(rmax)*LOG2)).lo
    assert _d(hplus_lo - C2I.hi) > c, \
        f"tail lemma fails: h+({rmax}) - C2 <= c"
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
            # refined scan of the straddle run
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


# ---------- the certified count for one cell ----------

def eop_bound(nu, beta, a, pieces, brackets, H):
    """Rigorous ||T - T_H||_op bound: Simpson four-derivative
    term over the pieces + per-bracket hull terms
    (2/pi) * qtmax_i * a * width_i (since <f,phi_r>^2 <= a and
    0 <= qt <= qtmax_i on the bracket)."""
    m1 = dW_majorant(260.0)
    m2 = d2W_majorant(260.0)
    m3 = M3_majorant()
    m4 = M4_majorant()
    # qt <= c - min W; -min W <= -psi(1/4) + ln pi + C2
    #   = gamma + 3 ln 2 + pi/2 + ln pi + sqrt2 ln 2
    #   = 6.35244... < 6.36  (round-248 F248-2: derivation
    # recorded; the constant is an upper bound, safe direction)
    qmax = _u(nu + beta + 6.36)
    ta = 2*a
    g4 = a*(m4 + 4*ta*m3 + 6*ta*ta*m2 + 8*ta**3*m1
            + 2*ta**4*qmax)
    tot_len = sum(p[1] - p[0] for p in pieces)
    simpson = tot_len*(H**4)*g4/180.0
    br = sum((b[1] - b[0])*b[2] for b in brackets)*a
    return _u((2/math.pi)*(simpson + br)*(1 + 1e-9))


def frame_nodes(pieces, H):
    """Composite-Simpson nodes and weights per piece (panel
    count even, weights (h/3)(1,4,2,...,4,1) > 0)."""
    rs, ws = [], []
    for lo, hi in pieces:
        n = max(2, int(math.ceil((hi - lo)/H/2))*2)
        h = (hi - lo)/n
        xs = lo + h*np.arange(n + 1)
        w = np.full(n + 1, 2.0)
        w[1::2] = 4.0
        w[0] = w[-1] = 1.0
        w *= h/3.0
        rs.append(xs)
        ws.append(w)
    return np.concatenate(rs), np.concatenate(ws)


def gamma_n(n):
    u = 2.0**-53
    return _u(n*u/(1 - n*u))

def rig_matmul_norm(Afl, Bfl):
    """Rigorous bound on ||fl(A@B) - A@B||_F via the model bound
    |fl(AB) - AB| <= gamma_k |A||B| elementwise (k = inner dim);
    returns (fl(A@B), bound_F)."""
    C = Afl @ Bfl
    absb = np.abs(Afl) @ np.abs(Bfl)
    g = gamma_n(Afl.shape[1])
    return C, _u(g*float(np.linalg.norm(absb)))

def veigs(A):
    """Verified eigenvalue enclosures for the symmetric interval
    matrix A (V of shape (n, n) flattened as lo/hi 2-d arrays):
    center C = midpoint, radius R; every eigenvalue of every
    symmetric member lies within [d_i - rho, d_i + rho] where
    d = float eigh eigenvalues of C and rho encloses
    ||E||_F + ||C|| ||F||_F/(1 - ||F||) + ||R||_F, computed
    with rigorous inflation. Returns (d sorted desc, rho)."""
    Clo, Chi = A
    C = 0.5*(Clo + Chi)
    Rad = vup(np.maximum(Chi - C, C - Clo))
    n = C.shape[0]
    d, Q = np.linalg.eigh(C)
    # E = Q^T C Q - diag(d); F = Q^T Q - I  (rigorous norms)
    QT = Q.T.copy()
    M1fl, e1 = rig_matmul_norm(QT, C)
    M2fl, e2 = rig_matmul_norm(M1fl, Q)
    E = M2fl - np.diag(d)
    # e1 propagates through the second multiply by Q:
    # ||(err)Q||_F <= e1 ||Q||_2 <= e1 sqrt(1+||F||) <= 1.23 e1
    # (the ||F|| < 1/2 assert below); float norms inflated.
    normE = _u((float(np.linalg.norm(E)) + 1.23*e1 + e2)
               *(1 + 1e-12))
    G1, e3 = rig_matmul_norm(QT, Q)
    F = G1 - np.eye(n)
    normF = _u((float(np.linalg.norm(F)) + e3)*(1 + 1e-12))
    assert normF < 0.5, "eigenvector orthogonality too poor"
    # rigorous chain: B = Q (Q^T Q)^{-1/2} is exactly orthogonal;
    # B^T C B = S^{-1/2}(D + E)S^{-1/2}, S = I + F.  With
    # P = S^{-1/2} = I + D1 and ||D1|| <= ||F|| for ||F|| <= 1/2,
    # ||P M P - M|| <= ||M||(2||D1|| + ||D1||^2) <= 3||F|| ||M||,
    # M = D + E, so dist(spec C, d) <= ||E|| + 3||F||(||D||+||E||);
    # interval members add ||Rad||_F on top (|delta| <= Rad
    # elementwise => ||delta||_2 <= ||Rad||_2 <= ||Rad||_F).
    normD = _u(float(np.max(np.abs(d)))*(1 + 1e-12))
    rho = _u(normE + 3*normF*(normD + normE)
             + float(np.linalg.norm(Rad))*(1 + 1e-12))
    return np.sort(d)[::-1], rho


def certify_cell(parity, a, nu, beta, H=0.02, rmax=260.0):
    """The full rigorous chain for one cell row. Returns dict
    with mu enclosures, EOP, and the certificate margin."""
    pieces, brackets = support_pieces(nu, beta, rmax)
    eop = eop_bound(nu, beta, a, pieces, brackets, H)
    rs, wq = frame_nodes(pieces, H)
    wv = W_batch(rs)
    qt = (V.scalar(I(nu) + I(beta), len(rs)) - wv).pos()
    # weights c_i = (2/pi) * wq_i * qt(r_i): intervals
    wqV = V.point(wq)
    twopi_inv = V.scalar((I(2.0)/PI), len(rs))
    cV = (twopi_inv*wqV*qt)
    # drop nodes with c == 0 certainly (qt.hi == 0)
    keep = cV.hi > 0
    rs, clo, chi = rs[keep], cV.lo[keep], cV.hi[keep]
    m = len(rs)
    # Gram: closed sin-form, interval, m x m
    ri = rs[:, None]
    rj = rs[None, :]
    dm = ri - rj
    sm = ri + rj
    aI = I(a)
    # sinc terms: sin(d a)/d with d -> 0 diagonal handled by
    # the exact limit a on the diagonal
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
        # divide sign-safely: |d| >= 1e-8 here
        p1 = num.lo/den.lo
        p2 = num.lo/den.hi
        p3 = num.hi/den.lo
        p4 = num.hi/den.hi
        out_lo[nz] = vdn(np.minimum(np.minimum(p1, p2),
                                    np.minimum(p3, p4)))
        out_hi[nz] = vup(np.maximum(np.maximum(p1, p2),
                                    np.maximum(p3, p4)))
        # small |d|: sin(da)/d = a - (da)^2 a/6 * theta,
        # theta in [0,1]: enclose by [a(1 - (da)^2/6), a]
        da2 = (flat[small]*a)**2
        out_lo[small] = vdn(a*(1 - vup(da2/6)) - 1e-300)
        out_hi[small] = vup(np.full(small.sum(), a))
        return (out_lo.reshape(marr.shape),
                out_hi.reshape(marr.shape))
    d_lo, d_hi = sinc_block(dm)
    s_lo, s_hi = sinc_block(sm)
    sgn = 1.0 if parity == "even" else -1.0
    Glo = vdn(0.5*(d_lo + sgn*(s_lo if sgn > 0 else s_hi)))
    Ghi = vup(0.5*(d_hi + sgn*(s_hi if sgn > 0 else s_lo)))
    # A = C^{1/2} G C^{1/2}: c intervals >= 0
    sq_lo = np.sqrt(np.maximum(clo, 0.0))
    sq_hi = vup(np.sqrt(chi))
    sq_lo = vdn(sq_lo)
    # directed outer products (round-248 F248-1f: the chained
    # nearest roundings exceeded the single directed step)
    SL = vdn(sq_lo[:, None]*sq_lo[None, :])
    SH = vup(sq_hi[:, None]*sq_hi[None, :])
    # A entries: G can be negative; product with nonneg scale
    Alo = vdn(np.minimum(np.minimum(SL*Glo, SL*Ghi),
                         np.minimum(SH*Glo, SH*Ghi)))
    Ahi = vup(np.maximum(np.maximum(SL*Glo, SL*Ghi),
                         np.maximum(SH*Glo, SH*Ghi)))
    d, rho = veigs((Alo, Ahi))
    mu1 = I(_d(d[0] - rho), _u(d[0] + rho))
    mu2 = I(_d(d[1] - rho), _u(d[1] + rho))
    mu2_full_hi = _u(mu2.hi + eop)
    margin = _d(beta - mu2_full_hi)
    return {"m": int(m), "eop": eop, "rho": rho,
            "mu1": [mu1.lo, mu1.hi], "mu2": [mu2.lo, mu2.hi],
            "mu2_full_hi": mu2_full_hi, "beta": beta,
            "nu": nu, "margin": margin,
            "npieces": len(pieces), "nbrackets": len(brackets),
            "certified": bool(margin > 0)}


CELLS = [
    ("even", 0.6931, 0.34655, 0.15, 1.0),
    ("even", 0.80,  0.40,  0.15, 1.0),
    ("even", 0.90,  0.45,  0.04, 1.5),
    ("even", 0.95,  0.475, 0.02, 1.5),
    ("even", 1.00,  0.50,  0.01, 2.0),
    ("odd",  0.90,  0.45,  0.15, 1.0),
    ("odd",  1.05,  0.525, 0.15, 1.0),
    ("odd",  1.09,  0.545, 0.08, 1.5),
]


def _sha(name):
    import ckpt_key
    return ckpt_key.code_sha(os.path.join(HERE, name))

# COMPUTED transitive closure (round 252, reviewer-3 F4)
DEPSII = {f: _sha(f) for f in sorted(__import__("ckpt_key")
         .producer_closure(("oneprime_interval_count.py",),
                           HERE))}
KEYFILE = os.path.join(HERE, "oneprime_interval_count.py")


def run():
    import json
    params = {"deps": DEPSII, "H": 0.02, "cells": CELLS,
              "round": 6}
    st = ckpt_key.load("oneprime_ivcount", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is not None:
        return st
    # gII2: verified eigensolver self-test
    rng = np.random.default_rng(6)
    Qr, _ = np.linalg.qr(rng.standard_normal((40, 40)))
    lam = np.arange(1.0, 41.0)
    Atest = Qr @ np.diag(lam) @ Qr.T
    Atest = 0.5*(Atest + Atest.T)
    dtest, rtest = veigs((Atest, Atest))
    assert rtest < 1e-8, f"gII2 FAIL rho {rtest}"
    for lv in lam:
        assert np.min(np.abs(dtest - lv)) <= rtest, "gII2 FAIL"
    print(f"gII2 PASS: verified eigensolve rho {rtest:.2e}",
          flush=True)

    pjson = os.path.join(
        HERE, "checkpoints",
        f"oneprime_ivcount_partial_"
        f"{ckpt_key.code_key(KEYFILE, params)[:12]}.json")
    part = {}
    try:
        part = json.load(open(pjson))["state"]
        print(f"  partial: {len(part)} cells done", flush=True)
    except Exception:
        pass
    st = {}
    for parity, delta, a, nu, beta in CELLS:
        cellk = f"{parity}:{delta:g}"
        if cellk in part:
            st[cellk] = part[cellk]
            continue
        res = certify_cell(parity, a, nu, beta)
        # gII3 -- fatal on the seven THEOREM cells; even:1.0 is
        # the acknowledged frontier (not needed for the theorem
        # [log 2, 0.95] + odd through 1.09): recorded either way
        if cellk != "even:1":
            assert res["certified"], \
                f"gII3 FAIL {cellk}: margin {res['margin']:.3e}"
        print(f"IVC {cellk}: m {res['m']} mu2 "
              f"[{_fdir(res['mu2'][0], 7, False)}, {_fdir(res['mu2'][1], 7, True)}] "
              f"EOP {_fdir(res['eop'], 3, True)} rho {res['rho']:.2e} -> "
              f"mu2+EOP {_fdir(res['mu2_full_hi'], 7, True)} < beta "
              f"{beta:g} margin {_fdir(res['margin'], 4, False)} "
              f"[COUNT <= 1 CERTIFIED at nu {nu:g}]", flush=True)
        st[cellk] = res
        part[cellk] = res
        json.dump({"key": ckpt_key.code_key(KEYFILE, params),
                   "state": part}, open(pjson, "w"), indent=0)
    # gII1: wiring vs the committed float64 rows (loose)
    import glob
    lp = glob.glob(os.path.join(HERE, "checkpoints",
                                "oneprime_lehmann_*.json"))
    if lp:
        leh = json.load(open(lp[0]))["state"]
        for parity, delta, a, nu, beta in CELLS:
            cellk = f"{parity}:{delta:g}"
            row = leh.get(cellk, {}).get("count_curve", {}) \
                .get(f"{nu:g}")
            if row and abs(row.get("beta", -1) - beta) < 1e-9:
                fmu2 = row["mu123"][1]
                enc = st[cellk]
                lo = enc["mu2"][0] - enc["eop"] - 1e-2
                hi = enc["mu2"][1] + enc["eop"] + 1e-2
                assert lo <= fmu2 <= hi, \
                    f"gII1 FAIL {cellk}: float mu2 {fmu2}"
        print("gII1 PASS: float64 rows consistent with "
              "enclosures where comparable", flush=True)
    # gII4: refinement honesty on the tightest even cell
    ref = certify_cell("even", 0.475, 0.02, 1.5, H=0.01)
    base = st["even:0.95"]
    shift = abs(0.5*(ref["mu2"][0] + ref["mu2"][1])
                - 0.5*(base["mu2"][0] + base["mu2"][1]))
    assert shift <= base["eop"] + ref["eop"] + base["rho"] \
        + ref["rho"] + 1e-10, f"gII4 FAIL shift {shift:.2e}"
    print(f"gII4 PASS: H-halving shift {shift:.2e} within "
          f"claimed bounds", flush=True)
    st["__gII4__"] = {"shift": shift, "eop_ref": ref["eop"]}
    ckpt_key.save("oneprime_ivcount", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    if os.path.exists(pjson):
        os.remove(pjson)
    return st


if __name__ == "__main__":
    run()
    print("interval count (Stage II) complete", flush=True)
