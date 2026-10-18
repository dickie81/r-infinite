"""The critical block at sigma = 5/7 and a sixth-moment socket for prime moduli (README round 541).

Part I is exact arithmetic in the model of `seven_thirds.py`.  Part II is a numerical probe.

Chen-Gupta-Li's zero detector (their Section 12) has mollifier X = (qT)^eps and smoothing
Y = (qT)^{1/2}, so its class-I blocks have length N <= (qT)^{1/2}, and each block is raised to a
power N^k inside a window where a large-values estimate applies.  For the mean value theorem at
Ingham's level t_I(s) = 3(1-s)/(2-s), the window is [1/(2-s), 3/(2(2-s))], with ratio exactly 3/2.

Checks.
  (K) The critical block.  On a rational grid of s in [7/10, 4/5], with 5/7 included:
      (K1) the window is exactly [1/(2-s), 3/(2(2-s))];
      (K2) nu_c(s) = 1/(2(2-s)) has 2 nu_c at its left end and 3 nu_c at its right end;
      (K3) no power k nu_c lies strictly inside it;
      (K4) every other block exponent nu in (0, 1/2] on a rational grid has a power strictly inside.
      At s = 5/7, nu_c = 7/18, the point of the barrier set B = {7/18, 7/9} u [7/6, oo) of
      `seven_thirds.py` that lies in (0, 1/2].
  (X) The sixth-moment socket.  Hypothesis SIX(delta): for the detector's blocks (light mollifier)
      of length N = Q^nu with 1/3 <= nu <= 1/2,
          sum over chi != chi_0 of |D_N(chi)|^6  <=  Q^{o(1)} (Q N^3 + Q^{-delta} N^6).
      In the model this adds, for detectors with x = 0 only, the exponents nu with
      max(1 + 3 nu (1 - 2s), 6 nu (1 - s) - delta) <= t.  SIX(0) is the mean value theorem for D^3
      and changes nothing.  The best exponent the model certifies, maximised over the grid of
      `seven_thirds.py` (with 5/7 and 7/10 added), is computed by bisection for several delta:
      (X1) delta = 0 gives 7/3, attained at s = 5/7 (no certificate for 7/3 - 1/10^4 there);
      (X2) every delta > 0 tested gives an exponent below 7/3, recorded in the output;
      (X3) the exponent decreases as delta increases;
      (X4) the floor: at s = 7/10 the model certifies 20/9 with delta = 1/6 and nothing below
           20/9 - 1/10^4 even with delta = 1/2.  There t = 2/3, the window is [5/6, 10/9] (ratio 4/3),
           and the block 5/18 has 3(5/18) at its left end and 4(5/18) at its right end, with
           (5/18) * 3 < 1 < (5/18) * 4: the next doubly-critical block, whose eighth moment wraps.
  (Y) The socket on the stack's own families (README round 542): the mean value theorem and Huxley's
      estimate (rounds 524-527), with no part of Chen-Gupta-Li's Proposition 3.1, plus SIX(delta):
      (Y1) at s = 3/4 the model's exponent is 12/5 - 8 delta/5 for delta in {0, 1/40, 1/24, 1/20}
           (to the bisection's tolerance 10^-5), so 12/5 at delta = 0 (round 527) and 7/3 at 1/24;
      (Y2) over the grid with 3/4 added, delta = 1/24 - 1/1000 gives a maximum above 7/3 and
           delta = 1/24 + 1/1000 one below 7/3, both at s = 3/4;
      (Y3) the floor: at s = 3/4 the model certifies 16/7 with delta = 1/14 and nothing below
           16/7 - 1/10^4 even with delta = 1/2; there t = 4/7, the window is [6/7, 8/7], and the
           block 2/7 has 3(2/7) and 4(2/7) at its two ends, with 3(2/7) < 1 < 4(2/7).
  (Z) Moment hypotheses on the stack's families (README round 543).  Suppose the 2k-th moment of L(1/2 + it, chi)
      over the characters mod q, at one point per character, is at most Q^{1+o(1)}.  In the model it counts the
      integral class at mollifier exponent 0 with smoothing Q^y, y = (1 - t)/(2k(s - 1/2)), and every block of
      length at least Q^y; the other blocks go by powers into the windows of the mean value theorem and Huxley's
      estimate.  (Z1) For k = 2, 3, 4 the model certifies 2 + 2/(2k + 1) at s = 3/4 and nothing below it by 10^-4;
      (Z2) the maximum over the grid with 3/4 added is that number (within 2 * 10^-5), at s = 3/4.  For k = 2 it is
      12/5, the stack's exponent from the fourth moment it has (round 527); for k = 3 it is 16/7.
  (U) A sixth moment with a loss (README round 544).  Keep the proved fourth moment and suppose the sixth moment is at
      most Q^{1+theta+o(1)}, one point per character.  The integral class and the blocks of length at least Q^y go
      through the critical line, y = min(nu4, nu6), nu4 = (1 - t)/(4h), nu6 = (1 + theta - t)/(6h), h = s - 1/2; the
      other blocks go by powers into the windows of the mean value theorem and Huxley's estimate, as in (Z).
      (U1) Exact identities, for every s, theta and A on a rational grid.  Let [lo, hi] be the mean value theorem's
           window, hi = t/(2(1 - s)).  Below Ingham's level (A < 3/(2 - s)) hi/3 < lo/2, and the blocks in
           (hi/3, lo/2) have no power in [lo, hi] (checked at the midpoint).  The reach (1 + theta - t)/(2kh) of a
           2k-th moment with loss theta is at most hi/3 iff A (3 - k/2 + (k - 3)s) >= 3(1 + theta), for k = 2, 3, 4;
           so nu6 <= hi/3 iff A >= 2 + 2 theta, for every s, and nu4 <= hi/3 iff A >= 3/(2 - s) (Ingham).  For s > 2/3
           Huxley's window, halved, reaches hi/3 iff A >= 3/(3s - 1) (Huxley).  At s = 5/7 and A = 7/3: nu4 = 7/18,
           the integral class detects |L(1/2 + it, chi)| >= Q^{1/12}, the fourth moment counts it by Q^{2/3} = Q^t and
           the sixth by Q^{1/2 + theta}, and nu6 - nu4 = 7(theta - 1/6)/9.
      (U2) For each theta tested, the maximum over the grid of (Z), with 3/4 and sigma_0(theta) added, is
           max(16/7, min(2 + 2 theta, 12/5)) (within 2 * 10^-5), and it is below 7/3 exactly for the theta below 1/6.
      (U3) For 1/7 < theta < 1/5 the model certifies 2 + 2 theta, and nothing below it by 10^-4, at both ends of
           [sigma_0, sigma_H]: sigma_0(theta) = (1 + 4 theta)/(2 + 2 theta), where Ingham's 3/(2 - s) equals
           2 + 2 theta, and sigma_H(theta) = (5 + 2 theta)/(6 + 6 theta), where Huxley's 3/(3s - 1) does.  At
           sigma_0 - 1/100 and sigma_H + 1/100 it certifies 2 + 2 theta - 10^-4.  sigma_0(1/6) = 5/7.
  (V) Large central values in a band of heights (README round 545).  The fourth moment counts the characters with
      |L(1/2 + it, chi)| >= Q^a, one point per character, by Q^{1-4a}.  Suppose that count is Q^{1-4a-delta} for a in
      a band [a_lo, a_hi] only.  As in (U), the integral class and every block whose height a = nu h has count at most
      Q^t go through the critical line; the other blocks go by powers.
      (V1) With all four families of `seven_thirds.py` (Chen-Gupta-Li's Proposition 3.1 included) and the band
           1/12 -+ 1/100, the maximum over V_GRID is 7/3, at s = 5/7, for delta = 0, and below 7/3 - 10^-3 for
           delta = 1/1000, 1/100 and 1/50, decreasing in delta.
      (V2) With the stack's families only and the band [1/24, 1/8], delta = 34/1000 gives a maximum of at least 7/3
           and delta = 35/1000 one below 7/3 (over X_GRID with 3/4 added).
      The sixth moment with loss theta gives the count Q^{1+theta-6a} = Q^{1-4a-(2a-theta)}, a saving 1/6 - theta at
      a = 1/12; a uniform bound |L(1/2 + it, chi)| <= Q^c makes the count vanish for a > c.
  (W) The common target H* (README round 550).  (X) uses SIX(delta) only through its large-values consequence: the
      blocks nu with max(1 + 3 nu (1 - 2s), 6 nu (1 - s) - delta) <= t are counted.  H*(delta, w) is that consequence
      for the blocks within w of nu_c(s) = 1/(2(2 - s)) only.
      (W1) With delta = 1/100 and w = 1/1000 the maximum over X_GRID is below 7/3 (recorded in the output).
      (W2) At s = 5/7 and delta = 1/100: w = 1/100 certifies what the unrestricted socket does, and w = 1/1000 still
           certifies an exponent below 7/3 - 1/200.
      (W3) The band hypothesis gives H*: at nu = nu_c(s) the block is large at height a(s) = nu_c(s)(s - 1/2) on the
           critical line, and the band's count 1 - 4a(s) equals the socket's 6 nu_c(s)(1 - s), for s on (K)'s grid;
           a(5/7) = 1/12.  The square 2 nu_c(s) is the window's left end, where Chen-Gupta-Li's third term sits.
  (M) The sixth moment of smooth character sums S_N(chi) = sum_n phi(n/N) chi(n), phi = sin^2(pi(x - 1))
      on [1, 2], at N = round(q^{7/18}) for primes q from 10^4 to 10^7.  For each q:
      (M1) Parseval: sum over chi of |S_N|^2 = (q - 1) sum phi(n/N)^2;
      (M2) no wrap-around in the fourth moment (4N^2 < q): sum |S_N|^4 = (q - 1) D_2, with D_2 the
           weighted count of integer solutions of x1 x2 = y1 y2;
      (M3) the sixth moment from the FFT equals (q - 1) sum over c of R_3(c)^2, with R_3(c) the
           weighted count of x1 x2 x3 = c (mod q), computed directly and independently;
      and the record: rho = sum_{chi != chi_0} |S_N|^6 / ((q - 1) D_3), with D_3 the weighted count
      of integer solutions of x1 x2 x3 = y1 y2 y3 (the diagonal, which is the sixth moment of a
      Steinhaus random multiplicative function), and the scale W^6 / ((q - 1) D_3), W = S_N(chi_0),
      which is the size of the term that the divisor bound leaves and SIX(delta) removes.

Scope.  Part I checks arithmetic in a model; the hypothesis SIX(delta) is not proved here, and for
delta > 0 it is a power saving in the off-diagonal (wrap-around) count of x1 x2 x3 = y1 y2 y3 (mod q)
with N^3 = q^{7/6} > q, which this round does not find in the literature.  Part II measures one
polynomial at t = 0 for a handful of primes; it is not evidence about the worst case over all
coefficient sequences, and it cannot see factors of q^{1/6} <= 15 at these sizes.  The script runs
eleven mutations and requires each to fail at least one check.
"""
from fractions import Fraction as F
import sys
import time

import numpy as np

import seven_thirds as st

S57 = F(5, 7)
K_GRID = [F(7, 10) + F(1, 10) * F(i, 40) for i in range(41)] + [S57]


def window(s):
    t = 3 * (1 - s) / (2 - s)
    lo = (1 - t) / (2 * s - 1)          # 1 + L(1 - 2s) <= t
    hi = t / (2 * (1 - s))              # 2L(1 - s) <= t
    return t, lo, hi


def strictly_inside_power(nu, lo, hi):
    k = 1
    while k * nu <= hi:
        if lo < k * nu < hi:
            return True
        k += 1
    return False


def check_K(mut=None):
    fails = []
    for s in K_GRID:
        t, lo, hi = window(s)
        if not (lo == 1 / (2 - s) and hi == F(3, 2) / (2 - s) and hi / lo == F(3, 2)):
            fails.append(f"K1 at s = {s}")
        nu_c = 1 / (2 * (2 - s))
        if mut == "critical block one tenth off":
            nu_c = nu_c * F(11, 10)
        if not (2 * nu_c == lo and 3 * nu_c == hi):
            fails.append(f"K2 at s = {s}")
        if strictly_inside_power(nu_c, lo, hi):
            fails.append(f"K3 at s = {s}")
        for i in range(1, 400):
            nu = F(1, 2) * F(i, 400)
            if nu != nu_c and not strictly_inside_power(nu, lo, hi):
                fails.append(f"K4 at s = {s}, nu = {nu}")
                break
    if 1 / (2 * (2 - S57)) != F(7, 18) or F(7, 18) not in st.B_PTS:
        fails.append("K at 5/7: nu_c is not 7/18")
    return fails


def six_piece(s, t, delta):
    """nu in [1/3, 1/2] with max(1 + 3nu(1 - 2s), 6nu(1 - s) - delta) <= t, or None."""
    a = max(F(1, 3), (1 - t) / (3 * (2 * s - 1)))
    b = min(F(1, 2), (t + delta) / (6 * (1 - s)))
    return (a, b) if a <= b else None


def covered_extra(G, extra, lo, hi):
    pieces = list(extra)
    for a, b in G:
        k = 1
        while b / k >= lo:
            pieces.append((a / k, b / k))
            k += 1
    pieces.sort()
    reach = lo
    for a, b in pieces:
        if a > reach:
            break
        if b >= reach:
            reach = b
        if reach >= hi:
            return True
    return reach >= hi


def certify_six(s, A, delta, methods=st.METHODS):
    t = A * (1 - s)
    G = [iv for m in methods if (iv := st.good_interval(m, s, t)) is not None]
    if st.certify(s, A, methods=methods) is not None:
        return "base"
    six = six_piece(s, t, delta)
    if six is None or delta <= 0:
        return None
    f0 = st.tiny_floor(G)
    if f0 <= 0:
        return None
    for lo, hi, y0, y1, tag in st.detectors(s, t):
        if lo != 0:
            continue
        y = y0
        if y <= f0 or covered_extra(G, [six], f0, y):
            return tag + "+SIX"
    return None


def best_exponent(s, delta, lo=F(2), hi=F(7, 3) + F(1, 100), tol=F(1, 10**4), methods=st.METHODS):
    if certify_six(s, hi, delta, methods) is None:
        return None
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if certify_six(s, mid, delta, methods) is not None:
            hi = mid
        else:
            lo = mid
    return hi


X_GRID = sorted(set(st.GRID + [S57, F(7, 10)]))
DELTAS = [F(0), F(1, 100), F(1, 50), F(1, 20), F(1, 12), F(1, 6)]


def check_X(deltas=DELTAS, mut=None):
    fails, table = [], []
    for d in deltas:
        worst, arg = F(0), None
        for s in X_GRID:
            a = best_exponent(s, d)
            if a is None:
                fails.append(f"X no certificate at s = {s}, delta = {d}")
                break
            if a > worst:
                worst, arg = a, s
        table.append((d, worst, arg))
    d0 = [w for d, w, a in table if d == 0]
    if d0:
        w0, a0 = d0[0], [a for d, w, a in table if d == 0][0]
        if not (F(7, 3) - F(1, 10**4) < w0 <= F(7, 3) + F(1, 10**4) and a0 == S57):
            fails.append(f"X1 delta = 0 gives {float(w0)} at s = {a0}")
        if certify_six(S57, F(7, 3) - F(1, 10**4), F(0)) is not None:
            fails.append("X1 delta = 0 certifies below 7/3 at 5/7")
    for d, w, a in table:
        if d > 0 and not w < F(7, 3) - F(1, 10**3):
            fails.append(f"X2 delta = {d} gives {float(w)}")
    ws = [w for d, w, a in table]
    if mut == "socket delta enters with the wrong sign":
        ws = ws[::-1]
    if any(w2 > w1 for w1, w2 in zip(ws, ws[1:])):
        fails.append("X3 the exponent does not decrease with delta")
    # (X4) the floor 20/9 at s = 7/10, and its doubly-critical block 5/18 (eighth moment past Q)
    s7, A7 = F(7, 10), F(20, 9)
    t7 = A7 * (1 - s7)
    lo7, hi7 = (1 - t7) / (2 * s7 - 1), t7 / (2 * (1 - s7))
    if not (certify_six(s7, A7, F(1, 6)) is not None
            and certify_six(s7, A7 - F(1, 10**4), F(1, 2)) is None
            and (t7, lo7, hi7) == (F(2, 3), F(5, 6), F(10, 9))
            and 3 * F(5, 18) == lo7 and 4 * F(5, 18) == hi7 and 4 * F(5, 18) > 1 > 3 * F(5, 18)):
        fails.append("X4 the floor at s = 7/10")
    return fails, table


STACK = ("MVT", "HUX")              # the large-values families landed in Lean, rounds 524-527


def check_Y(mut=None):
    """(Y) The socket on the stack's own families, without Chen-Gupta-Li's Proposition 3.1."""
    methods = ("MVT",) if mut == "Huxley dropped from the stack's families" else STACK
    fails, rows = [], []
    s34 = F(3, 4)
    tol = F(1, 10**5)
    # (Y1) at s = 3/4 the exponent is 12/5 - 8 delta/5 (to the tolerance), 12/5 at delta = 0
    for d in (F(0), F(1, 40), F(1, 24), F(1, 20)):
        a = best_exponent(s34, d, hi=F(3), tol=tol, methods=methods)
        if a is None or not (F(12, 5) - F(8, 5) * d <= a <= F(12, 5) - F(8, 5) * d + 2 * tol):
            fails.append(f"Y1 at delta = {d}: {None if a is None else float(a)}")
    # (Y2) over the grid with 3/4: delta = 1/24 -+ 1/1000 straddles 7/3, the maximum at s = 3/4
    grid = sorted(set(X_GRID + [s34]))
    for d, below in ((F(1, 24) - F(1, 1000), False), (F(1, 24) + F(1, 1000), True)):
        worst, arg = F(0), None
        for s in grid:
            a = best_exponent(s, d, hi=F(3), tol=tol, methods=methods)
            if a is None:
                worst, arg = F(3), s
                break
            if a > worst:
                worst, arg = a, s
        rows.append((d, worst, arg))
        if (worst < F(7, 3)) != below or arg != s34:
            fails.append(f"Y2 at delta = {d}: {float(worst)} at s = {arg}")
    # (Y3) the floor 16/7 at s = 3/4 and its doubly-critical block 2/7
    t = F(16, 7) * (1 - s34)
    lo, hi = (1 - t) / (2 * s34 - 1), t / (2 * (1 - s34))
    if not (certify_six(s34, F(16, 7), F(1, 14), methods) is not None
            and certify_six(s34, F(16, 7) - F(1, 10**4), F(1, 2), methods) is None
            and (t, lo, hi) == (F(4, 7), F(6, 7), F(8, 7))
            and 3 * F(2, 7) == lo and 4 * F(2, 7) == hi and 4 * F(2, 7) > 1 > 3 * F(2, 7)):
        fails.append("Y3 the floor at s = 3/4")
    return fails, rows


def certify_moment(s, A, k, methods=STACK):
    """Class II by a 2k-th moment of L on the critical line at mollifier exponent 0, which also counts the blocks of
    length Q^nu >= Q^{(1 - t)/(2k(s - 1/2))}; the other blocks by powers in the windows of `methods`."""
    t = A * (1 - s)
    if t >= 1:
        return "trivial"
    G = [iv for m in methods if (iv := st.good_interval(m, s, t)) is not None]
    y = (1 - t) / (2 * k * (s - F(1, 2)))
    f0 = st.tiny_floor(G)
    if f0 <= 0:
        return None
    return "L%d" % (2 * k) if covered_extra(G, [(y, F(10))], f0, y) else None


def best_moment(s, k, methods=STACK, tol=F(1, 10**5)):
    lo, hi = F(2), F(3)
    if certify_moment(s, hi, k, methods) is None:
        return None
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if certify_moment(s, mid, k, methods) is not None:
            hi = mid
        else:
            lo = mid
    return hi


def check_Z(mut=None):
    """(Z) Moment hypotheses on the stack's families: the 2k-th moment gives 2 + 2/(2k + 1), at s = 3/4."""
    fails, rows = [], []
    grid = sorted(set(X_GRID + [F(3, 4)]))
    for k in (2, 3, 4):
        Ak = 2 + F(2, 2 * k + 1)
        kk = k - 1 if mut == "the sixth moment read as the fourth" and k == 3 else k
        if not (certify_moment(F(3, 4), Ak, kk) is not None and certify_moment(F(3, 4), Ak - F(1, 10**4), kk) is None):
            fails.append(f"Z1 2k = {2 * k} at s = 3/4")
        worst, arg = F(0), None
        for s in grid:
            a = best_moment(s, kk)
            if a is not None and a > worst:
                worst, arg = a, s
        rows.append((2 * k, worst, arg))
        if not (Ak <= worst <= Ak + F(2, 10**5) and arg == F(3, 4)):
            fails.append(f"Z2 2k = {2 * k}: maximum {float(worst)} at s = {arg}")
    return fails, rows


def certify_loss(s, A, theta, methods=STACK, mut=None):
    """The proved fourth moment beside a sixth moment at most Q^{1 + theta + o(1)}: the integral class and the blocks of
    length Q^nu >= Q^{min(nu4, nu6)} through the critical line; the other blocks by powers in the windows of `methods`."""
    t = A * (1 - s)
    if t >= 1:
        return "trivial"
    G = [iv for m in methods if (iv := st.good_interval(m, s, t)) is not None]
    h = s - F(1, 2)
    loss = 2 * theta if mut == "the loss counted twice" else theta
    nu4, nu6 = (1 - t) / (4 * h), (1 + loss - t) / (6 * h)
    y = min(nu4, nu6)
    f0 = st.tiny_floor(G)
    if f0 <= 0:
        return None
    return ("L6" if nu6 < nu4 else "L4") if covered_extra(G, [(y, F(10))], f0, y) else None


def best_loss(s, theta, tol=F(1, 10**5), mut=None):
    lo, hi = F(2), F(3)
    if certify_loss(s, hi, theta, mut=mut) is None:
        return None
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if certify_loss(s, mid, theta, mut=mut) is not None:
            hi = mid
        else:
            lo = mid
    return hi


def loss_exponent(theta):
    """The closed form of (U2): the sixth moment caps the Ingham-Huxley envelope at 2 + 2 theta, above the floor 16/7."""
    return max(F(16, 7), min(2 + 2 * theta, F(12, 5)))


def loss_point(theta):
    """sigma_0(theta), where Ingham's 3/(2 - s) equals 2 + 2 theta."""
    return (1 + 4 * theta) / (2 + 2 * theta)


def loss_point_hux(theta):
    """sigma_H(theta), where Huxley's 3/(3s - 1) equals 2 + 2 theta."""
    return (5 + 2 * theta) / (6 + 6 * theta)


THETAS = [F(0), F(1, 12), F(1, 7), F(3, 20), F(4, 25), F(1, 6) - F(1, 100), F(1, 6), F(9, 50), F(1, 5), F(1, 4),
          F(1, 3)]


def check_U(mut=None):
    """(U) A sixth moment with a loss theta beside the proved fourth moment, on the stack's families."""
    fails, rows = [], []
    # (U1) the identities behind the closed form, and the arithmetic at the critical point
    for s in sorted(set(K_GRID + [F(5, 8), F(3, 4), F(7, 8)])):
        h = s - F(1, 2)
        for th in THETAS:
            for A in (2 + 2 * th - F(1, 1000), 2 + 2 * th, 2 + 2 * th + F(1, 1000),
                      3 / (2 - s) - F(1, 1000), 3 / (2 - s), 3 / (3 * s - 1) - F(1, 1000), 3 / (3 * s - 1)):
                t = A * (1 - s)
                lo, hi = (1 - t) / (2 * s - 1), t / (2 * (1 - s))
                top = hi / 2 if mut == "the gap's top read as hi/2" else hi / 3
                nu4, nu6 = (1 - t) / (4 * h), (1 + th - t) / (6 * h)
                ok = (nu6 <= top) == (A >= 2 + 2 * th) and (nu4 <= top) == (A >= 3 / (2 - s))
                for k in (2, 3, 4):
                    ok = ok and ((1 + th - t) / (2 * k * h) <= top) == (A * (3 - F(k, 2) + (k - 3) * s) >= 3 * (1 + th))
                if A < 3 / (2 - s):
                    mid = (hi / 3 + lo / 2) / 2
                    ok = ok and hi / 3 < lo / 2 and not any(lo <= k * mid <= hi for k in range(1, 8))
                if s > F(2, 3):
                    lo_h = (1 - t) / (6 * s - 4)
                    ok = ok and (lo_h / 2 <= top) == (A >= 3 / (3 * s - 1))
                if not ok:
                    fails.append(f"U1 at s = {s}, theta = {th}, A = {A}")
                    break
    s, A = S57, F(7, 3)
    t, h = A * (1 - s), s - F(1, 2)
    nu4 = (1 - t) / (4 * h)
    if not (t == F(2, 3) and nu4 == F(7, 18) == 1 / (2 * (2 - s)) and nu4 * h == F(1, 12) and 1 - 4 * nu4 * h == t):
        fails.append("U1 the fourth moment at the critical point")
    for th in THETAS:
        nu6 = (1 + th - t) / (6 * h)
        if (1 + th - 6 * nu4 * h < t) != (th < F(1, 6)) or nu6 - nu4 != F(7, 9) * (th - F(1, 6)):
            fails.append(f"U1 the sixth moment at the critical point, theta = {th}")
    # (U2) the closed form over the grid, and the threshold 1/6
    for th in THETAS:
        grid = sorted(set(X_GRID + [F(3, 4)] + ([loss_point(th)] if loss_point(th) > F(1, 2) else [])))
        worst, arg = F(0), None
        for s in grid:
            a = best_loss(s, th, mut=mut)
            if a is not None and a > worst:
                worst, arg = a, s
        rows.append((th, worst, arg))
        E = loss_exponent(th)
        if not (E <= worst <= E + F(2, 10**5)) or (worst < F(7, 3)) != (th < F(1, 6)):
            fails.append(f"U2 theta = {th}: maximum {float(worst)} at s = {arg}, closed form {float(E)}")
    # (U3) the two ends of the interval [sigma_0(theta), sigma_H(theta)] on which the cap 2 + 2 theta binds
    for th in THETAS:
        if F(1, 7) < th < F(1, 5):
            s0, sH, A0 = loss_point(th), loss_point_hux(th), 2 + 2 * th
            if not (3 / (2 - s0) == A0 == 3 / (3 * sH - 1)
                    and all(certify_loss(s, A0, th, mut=mut) is not None
                            and certify_loss(s, A0 - F(1, 10**4), th, mut=mut) is None for s in (s0, sH))
                    and all(certify_loss(s, A0 - F(1, 10**4), th, mut=mut) is not None
                            for s in (s0 - F(1, 100), sH + F(1, 100)))):
                fails.append(f"U3 at theta = {th}, [sigma_0, sigma_H] = [{s0}, {sH}]")
    if loss_point(F(1, 6)) != S57:
        fails.append("U3 sigma_0(1/6) is not 5/7")
    return fails, rows


def certify_band(s, A, delta, a_lo, a_hi, methods=STACK, mut=None):
    """The fourth moment's count Q^{1-4a} of the characters with |L(1/2 + it, chi)| >= Q^a, lowered to
    Q^{1-4a-delta} for a_lo <= a <= a_hi: the integral class and the blocks whose height a = nu h has count at most
    Q^t through the critical line; the other blocks by powers in the windows of `methods`."""
    t = A * (1 - s)
    if t >= 1:
        return "trivial"
    if st.certify(s, A, methods=methods) is not None:
        return "base"
    G = [iv for m in methods if (iv := st.good_interval(m, s, t)) is not None]
    h = s - F(1, 2)
    f0 = st.tiny_floor(G)
    if f0 <= 0:
        return None
    d = -delta if mut == "the band's saving enters with the wrong sign" else delta
    nu4 = (1 - t) / (4 * h)
    lo_b, hi_b = max((1 - t - d) / (4 * h), a_lo / h), a_hi / h
    band = [(lo_b, hi_b)] if lo_b <= hi_b else []
    for y in [nu4] + [lo_b] * len(band):
        if covered_extra(G, [(nu4, F(10))] + band, f0, y):
            return "band"
    return None


def best_band(s, delta, a_lo, a_hi, methods=STACK, tol=F(1, 10**5), mut=None):
    lo, hi = F(2), F(3)
    if certify_band(s, hi, delta, a_lo, a_hi, methods, mut) is None:
        return None
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if certify_band(s, mid, delta, a_lo, a_hi, methods, mut) is not None:
            hi = mid
        else:
            lo = mid
    return hi


V_GRID = sorted(set(X_GRID + [F(3, 4)] + [S57 + F(i, 2000) for i in range(-20, 21)]))
BAND = (F(1, 12) - F(1, 100), F(1, 12) + F(1, 100))
BAND_STACK = (F(1, 24), F(1, 8))


def certify_hstar(s, A, delta, w, methods=st.METHODS, mut=None):
    """(X)'s certificate with the SIX piece cut to the blocks within w of nu_c(s)."""
    t = A * (1 - s)
    G = [iv for m in methods if (iv := st.good_interval(m, s, t)) is not None]
    if st.certify(s, A, methods=methods) is not None:
        return "base"
    six = six_piece(s, t, delta)
    if six is None or delta <= 0:
        return None
    nc = 1 / (2 * (2 - s))
    if mut == "the H* window centred one tenth off":
        nc = nc * F(11, 10)
    a, b = max(six[0], nc - w), min(six[1], nc + w)
    if a > b:
        return None
    f0 = st.tiny_floor(G)
    if f0 <= 0:
        return None
    for lo, hi, y0, y1, tag in st.detectors(s, t):
        if lo != 0:
            continue
        if y0 <= f0 or covered_extra(G, [(a, b)], f0, y0):
            return tag + "+H*"
    return None


def best_hstar(s, delta, w, tol=F(1, 10**5), mut=None):
    lo, hi = F(2), F(7, 3) + F(1, 100)
    if certify_hstar(s, hi, delta, w, mut=mut) is None:
        return None
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if certify_hstar(s, mid, delta, w, mut=mut) is not None:
            hi = mid
        else:
            lo = mid
    return hi


def check_W(mut=None):
    """(W) The large-values consequence of SIX(delta), near the critical block only."""
    fails, rows = [], []
    tol, d = F(1, 10**5), F(1, 100)
    if mut is None:
        worst, arg = F(0), None
        for s in X_GRID:
            a = best_hstar(s, d, F(1, 1000), tol=tol)
            if a is None:
                worst, arg = F(3), s
                break
            if a > worst:
                worst, arg = a, s
        rows.append((d, F(1, 1000), worst, arg))
        if not worst < F(7, 3):
            fails.append(f"W1: {float(worst)} at s = {arg}")
    full = best_exponent(S57, d, tol=tol)
    for w, bound in ((F(1, 100), None), (F(1, 1000), F(7, 3) - F(1, 200))):
        a = best_hstar(S57, d, w, tol=tol, mut=mut)
        rows.append((d, w, a, S57))
        if a is None or (bound is None and abs(a - full) > 2 * tol) or (bound is not None and not a < bound):
            fails.append(f"W2 at w = {w}: {a} (unrestricted {full})")
    for s in K_GRID:
        nc = 1 / (2 * (2 - s))
        a = nc * (s - F(1, 2))
        if 1 - 4 * a != 6 * nc * (1 - s) or 2 * nc != window(s)[1]:
            fails.append(f"W3 at s = {s}")
    if F(7, 18) * (S57 - F(1, 2)) != F(1, 12):
        fails.append("W3: the height at 5/7")
    return fails, rows


def check_V(mut=None):
    """(V) A power saving in the count of large central values, in a band of heights only."""
    fails, rows = [], []
    tol = F(1, 10**5)
    band = (F(1, 10) - F(1, 100), F(1, 10) + F(1, 100)) if mut == "the band centred at 1/10" else BAND
    ws = []
    for d in (F(0), F(1, 1000), F(1, 100), F(1, 50)):
        worst, arg = F(0), None
        for s in V_GRID:
            a = best_band(s, d, *band, methods=st.METHODS, tol=tol, mut=mut)
            if a is None:
                worst, arg = F(3), s
                break
            if a > worst:
                worst, arg = a, s
        rows.append(("all four families", d, worst, arg))
        ws.append(worst)
        if d == 0 and not (F(7, 3) <= worst <= F(7, 3) + 2 * tol and arg == S57):
            fails.append(f"V1 delta = 0: {float(worst)} at s = {arg}")
        if d > 0 and not worst < F(7, 3) - F(1, 1000):
            fails.append(f"V1 delta = {d}: {float(worst)} at s = {arg}")
    if any(w2 >= w1 for w1, w2 in zip(ws, ws[1:])):
        fails.append("V1 the maximum does not decrease with delta")
    for d, below in ((F(34, 1000), False), (F(35, 1000), True)):
        worst, arg = F(0), None
        for s in sorted(set(X_GRID + [F(3, 4)])):
            a = best_band(s, d, *BAND_STACK, methods=STACK, tol=tol, mut=mut)
            if a is None:
                worst, arg = F(3), s
                break
            if a > worst:
                worst, arg = a, s
        rows.append(("stack's families", d, worst, arg))
        if (worst < F(7, 3)) != below:
            fails.append(f"V2 delta = {d}: {float(worst)} at s = {arg}")
    return fails, rows


# ---------------------------------------------------------------- Part II: the sixth moment

def primes_near(xs):
    from sympy import nextprime
    return [int(nextprime(int(x))) for x in xs]


def phi(x):
    return np.where((x >= 1) & (x <= 2), np.sin(np.pi * (x - 1)) ** 2, 0.0)


def discrete_logs(q, nmax):
    """ind(n) for 1 <= n <= nmax w.r.t. a primitive root, from the logs of the primes."""
    from sympy import primitive_root, primerange, factorint
    from sympy.ntheory.residue_ntheory import discrete_log
    g = int(primitive_root(q))
    lp = {p: int(discrete_log(q, p, g)) for p in primerange(2, nmax + 1)}
    ind = np.zeros(nmax + 1, dtype=np.int64)
    for n in range(2, nmax + 1):
        ind[n] = sum(e * lp[p] for p, e in factorint(n).items()) % (q - 1)
    return g, ind


def moments(q, N, mut=None):
    n = np.arange(N, 2 * N + 1)
    w = phi(n / N)
    keep = w > 0
    n, w = n[keep], w[keep]
    g, ind = discrete_logs(q, int(n.max()))
    A = np.zeros(q - 1)
    np.add.at(A, ind[n], w)
    S = np.fft.fft(A)
    a2 = np.abs(S) ** 2
    W = float(w.sum())
    out = {"q": q, "N": N, "W": W}
    out["M2"] = float(a2.sum())
    out["M4"] = float((a2 ** 2).sum())
    out["M6"] = float((a2 ** 3).sum())
    out["S0"] = float(S[0].real)
    # integer convolutions: r2 on [0, 4N^2]
    L2 = int(n.max()) ** 2
    r2 = np.zeros(L2 + 1)
    for x, wx in zip(n, w):
        r2[x * n] += wx * w
    out["D2"] = float((r2 ** 2).sum())
    # D3 = sum over (x3, y3) of phi phi sum_t r2(b t) r2(a t), a = x3/g, b = y3/g
    from math import gcd
    D3 = 0.0
    for x3, w3 in zip(n, w):
        for y3, v3 in zip(n, w):
            gg = gcd(int(x3), int(y3))
            a, b = int(x3) // gg, int(y3) // gg
            T = L2 // max(a, b)
            D3 += w3 * v3 * float(np.dot(r2[b:b * T + 1:b], r2[a:a * T + 1:a]))
    out["D3"] = D3
    # residue classes: R3(c) = sum of w(x1)w(x2)w(x3) over x1 x2 x3 = c (mod q)
    ms = np.nonzero(r2)[0]
    rv = r2[ms]
    R3 = np.zeros(q)
    step = max(1, int(2e7 // max(len(ms), 1)))
    for i in range(0, len(n), step):
        xs, ws = n[i:i + step], w[i:i + step]
        idx = (np.outer(xs, ms) % q).ravel()
        R3 += np.bincount(idx, weights=np.outer(ws, rv).ravel(), minlength=q)
    if mut == "drop one residue class":
        R3[1] = 0.0
    out["R3sq"] = float((R3 ** 2).sum())
    return out


def check_M(qs, mut=None):
    fails, rows = [], []
    for q in qs:
        N = int(round(q ** (7 / 18)))
        t0 = time.time()
        o = moments(q, N, mut)
        n = np.arange(N, 2 * N + 1)
        sw2 = float((phi(n / N) ** 2).sum())
        rel = lambda a, b: abs(a - b) / max(abs(b), 1e-300)
        if rel(o["M2"], (q - 1) * sw2) > 1e-9:
            fails.append(f"M1 at q = {q}")
        if rel(o["M4"], (q - 1) * o["D2"]) > 1e-8:
            fails.append(f"M2 at q = {q}: {o['M4']} vs {(q - 1) * o['D2']}")
        if rel(o["M6"], (q - 1) * o["R3sq"]) > 1e-8:
            fails.append(f"M3 at q = {q}: {o['M6']} vs {(q - 1) * o['R3sq']}")
        nonprin = o["M6"] - o["S0"] ** 6
        rho = nonprin / ((q - 1) * o["D3"])
        scale = o["W"] ** 6 / ((q - 1) * o["D3"])
        rows.append((q, N, rho, scale, time.time() - t0))
    return fails, rows


QS_GATE = [10007, 100003, 1000003]
QS_EXTRA = [30011, 300007, 3000017, 10000019]


def main(mut=None, qs=QS_GATE, verbose=False):
    res = {}
    res["K"] = check_K(mut)
    xf, table = check_X(mut=mut) if mut in (None, "socket delta enters with the wrong sign") else ([], [])
    res["X"] = xf
    yf, yrows = check_Y(mut) if mut in (None, "Huxley dropped from the stack's families") else ([], [])
    res["Y"] = yf
    zf, zrows = check_Z(mut) if mut in (None, "the sixth moment read as the fourth") else ([], [])
    res["Z"] = zf
    uf, urows = check_U(mut) if mut in (None, "the loss counted twice", "the gap's top read as hi/2") else ([], [])
    res["U"] = uf
    vf, vrows = check_V(mut) if mut in (None, "the band's saving enters with the wrong sign",
                                        "the band centred at 1/10") else ([], [])
    res["V"] = vf
    wf, wrows = check_W(mut) if mut in (None, "the H* window centred one tenth off") else ([], [])
    res["W"] = wf
    mf, rows = check_M(qs if mut in (None, "drop one residue class") else [], mut)
    res["M"] = mf
    if verbose:
        for d, w, a in table:
            print(f"    delta = {str(d):>5}: model exponent {float(w):.4f} (max over the grid, at s = {a})")
        for d, w, a in yrows:
            print(f"    stack only, delta = {float(d):.5f}: model exponent {float(w):.5f} (max over the grid, at s = {a})")
        for k2, w, a in zrows:
            print(f"    moment 2k = {k2}: model exponent {float(w):.5f} (max over the grid, at s = {a})")
        for th, w, a in urows:
            print(f"    sixth moment with loss theta = {str(th):>7}: model exponent {float(w):.5f} (max over the grid, at s = {a})")
        for fam, d, w, a in vrows:
            print(f"    band saving delta = {float(d):.3f}, {fam}: model exponent {float(w):.5f} (max over the grid, at s = {a})")
        for d, w, v, a in wrows:
            print(f"    H* with delta = {float(d):.3f}, window {float(w):.4f}: model exponent {float(v):.5f} (at s = {a})")
        for q, N, rho, scale, dt in rows:
            print(f"    q = {q:>9}, N = {N:>4}: rho = {rho:.4f}, W^6/((q-1)D3) = {scale:.3f}  [{dt:.1f}s]")
    return res


MUTATIONS = ["critical block one tenth off", "socket delta enters with the wrong sign",
             "drop one residue class", "fourth moment with N^2 > q", "Huxley dropped from the stack's families",
             "the sixth moment read as the fourth", "the loss counted twice", "the gap's top read as hi/2",
             "the band's saving enters with the wrong sign", "the band centred at 1/10",
             "the H* window centred one tenth off"]


def mutation_fourth_wrap():
    """At N = q^{1/2} the products x1 x2 wrap modulo q and the identity M2 must fail."""
    q = 10007
    N = int(q ** 0.5)
    o = moments(q, N)
    return [] if abs(o["M4"] - (q - 1) * o["D2"]) / o["M4"] < 1e-8 else ["M2 fails with wrap"]


if __name__ == "__main__":
    qs = QS_GATE + (QS_EXTRA if "--extra" in sys.argv else [])
    res = main(qs=qs, verbose=True)
    nfail = 0
    for key in "KXYZUVWM":
        print(f"({key}) {'pass' if not res[key] else 'FAIL'}")
        for f in res[key]:
            print("    ", f)
        nfail += len(res[key])
    caught = 0
    for name in MUTATIONS:
        if name == "fourth moment with N^2 > q":
            r = {"M": mutation_fourth_wrap()}
        else:
            r = main(name, qs=[10007])
        n = sum(len(v) for v in r.values())
        print(f"mutation '{name}': {n} failing checks, {'caught' if n else 'NOT CAUGHT'}")
        caught += 1 if n else 0
    print(f"{len(MUTATIONS)} mutations, {caught} caught")
    raise SystemExit(1 if nfail or caught < len(MUTATIONS) else 0)
