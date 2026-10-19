"""A sieve route to Linnik's exponent below 7/3 (README round 576; SEVEN-THIRDS.md section 44).

Setting.  q prime, a prime to q, x = q^L.  A is the set of n in [x, 2x] with n = a (mod q), weighted smoothly; B is
the integers of [x, 2x] prime to q with weight 1/phi(q).  A prime factor p of n is recorded by alpha = log p / log x.
The aim is S(A, (2x)^(1/2)) > 0, a prime p = a (mod q) in [x, 2x], by Harman's sieve.

Inputs.
  (H1) L(s, chi) != 0 for Re s > 11/12, every chi (the stack's Eis.LFunction_ne_zero_of_re_gt, kernel-checked).
  (H2) sum_{chi mod q} N(sigma, T, chi) <= (qT)^(A(sigma)(1 - sigma) + o(1)), uniformly in T >= 2, with
       hux:  A = 3/(2 - sigma) for sigma <= 3/4 and 3/(3 sigma - 1) above.  These are (1.4) and (1.5) of Chen, Gupta
             and Li (arXiv:2507.08296v2), from the qT mean value theorem and from Halasz-Montgomery-Huxley (Huxley,
             Acta Arith. 26 (1975)); the maximum is Huxley's 12/5, at 3/4.
       cons: A = 3/(2 - sigma) for sigma <= 5/7 and min(7/3, 3/(3 sigma - 1)) above: hux with Chen-Gupta-Li's 7/3.

The Type II window (paper level, section 44).  For chi in the bin beta*(chi) = beta, where beta*(chi) is the largest
real part of a zero near the height in question, a product B(chi) of smoothly weighted prime sums of total length X
is at most X^(beta + eps) (zero-free region, Mellin inversion), and a polynomial W(chi) of length P with arbitrary
coefficients has sum_chi |W|^2 <= (q + P)||w||^2.  By Cauchy-Schwarz over the bin, which has at most
q^(A(beta)(1 - beta)) characters,

    sum_{bin} |W B| <= q^(A(1 - beta)/2) ((q + P) P)^(1/2) X^beta,

which is o(x) for every beta in [1/2, 11/12] exactly when m = log P / log q satisfies

    m > lower(beta) = (A(1 - beta)/2 + 1/2 - L(1 - beta)) / (beta - 1/2)  (for P < q),
    m < upper(beta) = L - A(beta)/2                                       (for P > q).

So W of length x^u with u in (u1, u2) = (max lower / L, min upper / L) is a Type II factor: the window.  The checks
use the window over every beta in [1/2, 11/12].  Section 44 also states the window over the critical beta
(A(beta) >= L) only, with an argument for the other bins; that variant is printed, not gated.

The decomposition.  U = (u1, u2) u (1 - u2, 1 - u1), v = u2 - u1, R = 1 - u2.  A term with prime factors of exponents
alpha_i is evaluable when some subset sum of the alpha_i lies in U (the other factor, the rest of n, is then the
complement).  Type I information holds up to x^(1 - 1/L) (counting in a progression), which covers x^(R + eps) since
u2 L > 1, so S(A_r, x^v) is evaluable for every product of primes r <= x^R (Harman's fundamental theorem, with the
fundamental lemma below x^eps).  Buchstab's identity gives

    S(A, (2x)^(1/2)) = S(A, x^v) - sum_{v <= alpha1 < 1/2} S(A_p1, p1),
    S(A_p1, p1) = S(A_p1, x^v) - sum_{v <= alpha2 < alpha1} S(A_p1p2, p2)   (alpha1 outside (u1, u2)).

The terms S(A_p1p2, p2) enter with sign +.  One that is not evaluable is either dropped, at the cost of its share
omega((1 - alpha1 - alpha2)/alpha2)/(alpha1 alpha2^2), or decomposed when alpha1 + alpha2 <= R:

    S(A_p1p2, p2) = S(A_p1p2, x^v) - sum_{v <= alpha3 < alpha2} S(A_p1p2p3, p3).

Its terms of depth 3 enter with sign -, so each must be evaluable or decomposed in the same way (which needs
alpha1 + alpha2 + alpha3 <= R); the terms of depth 4 enter with sign + and are dropped when not evaluable.  The loss
is the sum over the dropped terms of their shares; a loss below 1 gives S(A, (2x)^(1/2)) >> x/(q log x).  Each
(alpha1, alpha2) takes the cheaper of the two options.  omega is Buchstab's function: omega(u) = 1/u on [1, 2],
(u omega(u))' = omega(u - 1), and the term of a remaining factor below the last prime has no share.

Two computations of the loss.
  midpoint: midpoint sums on grids (n2 cells in alpha1 and alpha2, n3 in alpha3 and in alpha4); an estimate.
  outer:    an upper bound.  Cells of side h = (1/2 - v)/n in each of the four variables; a cell counts when it can
            meet the region (interval arithmetic for every subset sum and every inequality), with the integrand at
            its supremum on the cell (prefactor at the lower corner, omega at its range maximum plus a Lipschitz
            allowance); decomposition is used for a cell of (alpha1, alpha2) only when its conditions hold on the
            whole cell; the window is shrunk by MARGIN on each side.

Checks.
  (S1) The window over every beta, for (hux, 2.29), (hux, 2.30), (cons, 2.25), (cons, 2.27): u2 = (L - Amax/2)/L to
       1e-9 (Amax = 12/5 or 7/3); u1 equals the largest of lower at the breakpoints (3/4, 11/12 for hux; 5/7, 16/21,
       11/12 for cons), divided by L, to 1e-7 against a grid of 2 * 10^6 points; u1 < u2 and u2 L > 1.
  (S2) omega: 1/u on [1, 2]; within 1e-7 of (1 + log(u - 1))/u on [2, 3]; within 1e-7 of a table of step H/4 on
       [3, 15]; and Buchstab's identity in shares, omega(1/v)/v - int_v^(1/2) omega((1 - a)/a)/a^2 da = 1, to 1e-4
       at v = 0.08, 0.1, 0.2.
  (S3) midpoint losses at (n2, n3) = (200, 100): hux at 2.30 in [0.60, 0.70] and cons at 2.25 in [0.80, 0.90]; and
       hux at 2.30 moves by less than 0.03 at (400, 200).
  (S4) outer bounds at n = 600: hux at L = 2.29 and cons at L = 2.27 are below 1; the outer bound for hux at 2.30 with
       n = 150 is at least the midpoint estimate of (S3); and at 20000 random points of random cells (side
       (1/2 - 0.08)/150), each of the two cell bounds is at least its integrand wherever the integrand is positive
       (more than half the depth-2 points and a tenth of the depth-4 points must be such).
  Printed, not gated: midpoint losses at other L for both curves (hux at 2.29 among them), the window over the critical
  beta only and its losses, and the outer bound for hux at 2.30 with n = 600.
Mutations, each of which must fail a gate (run on S1-S3 and S4's last two checks): (m1) the large sieve's (q + P) read
as q for P > q, which removes the upper end of the window (fails S1); (m2) the terms of depth 3 dropped as if they
had sign + (fails S3); (m3) omega(u) = 1/u for every u >= 1 (fails S2); (m4) the complement window (1 - u2, 1 - u1)
left out of U (fails S3); (m5) the cell bounds with the integrand at the upper corner of each cell (fails S4).

Scope.  The gates check arithmetic: the windows, omega, and the two loss computations for the decomposition above.
They do not check the analysis (the Type II lemma, Harman's fundamental theorem, the separation of variables, the
inputs (H1) and (H2)); section 44 gives that argument at paper level, unrefereed.  The outer bound is an upper bound
for the integral as computed in double precision; it is not interval arithmetic.
"""
import itertools
import sys
import time

import numpy as np

H = 1e-4
UMAX = 40.0
MARGIN = 1e-5
NBETA = 2_000_001
MUTS = ("m1", "m2", "m3", "m4", "m5")


def omega_table(h=H, mut=None):
    n = int(round(UMAX / h)) + 1
    us = np.arange(n) * h
    om = np.zeros(n)
    i1, i2 = int(round(1 / h)), int(round(2 / h))
    om[i1:i2 + 1] = 1 / us[i1:i2 + 1]
    if mut == "m3":
        om[i2 + 1:] = 1 / us[i2 + 1:]
        return us, om
    for i in range(i2 + 1, n):
        j = i - i1
        om[i] = (us[i - 1] * om[i - 1] + h * 0.5 * (om[j] + om[j - 1])) / us[i]
    return us, om


class Omega:
    """Buchstab's omega from a table, with range maxima from a sparse table."""

    def __init__(self, mut=None):
        self.us, self.om = omega_table(mut=mut)
        self.n = len(self.om)
        self.st = [self.om]
        k = 1
        while (1 << k) <= self.n:
            prev, span = self.st[-1], 1 << (k - 1)
            self.st.append(np.maximum(prev[:-span], prev[span:]))
            k += 1

    def __call__(self, u):
        u = np.asarray(u, dtype=float)
        return np.where(u < 1, 0.0, np.interp(np.minimum(u, UMAX), self.us, self.om))

    def sup(self, lo, hi):
        """At least the supremum of omega on [lo, hi] (omega = 0 below 1)."""
        lo = np.maximum(np.asarray(lo, dtype=float), 1.0)
        hi = np.minimum(np.asarray(hi, dtype=float), UMAX)
        empty = hi < lo
        l = np.clip(np.floor(lo / H).astype(np.int64), 0, self.n - 1)
        r = np.maximum(np.clip(np.ceil(hi / H).astype(np.int64), 0, self.n - 1), l)
        k = np.floor(np.log2(r - l + 1)).astype(np.int64)
        out = np.empty(l.shape)
        for lev in np.unique(k):
            m = k == lev
            out[m] = np.maximum(self.st[lev][l[m]], self.st[lev][r[m] - (1 << lev) + 1])
        return np.where(empty, 0.0, out + H + 1e-6)


def A_hux(b):
    b = np.asarray(b, dtype=float)
    return np.where(b <= 3 / 4, 3 / (2 - b), 3 / (3 * b - 1))


def A_cons(b):
    b = np.asarray(b, dtype=float)
    return np.where(b <= 5 / 7, 3 / (2 - b), np.minimum(7 / 3, 3 / (3 * b - 1)))


CURVES = {"hux": (A_hux, 12 / 5, (3 / 4, 11 / 12)), "cons": (A_cons, 7 / 3, (5 / 7, 16 / 21, 11 / 12))}


def lower(b, A, L):
    return (A * (1 - b) / 2 + 0.5 - L * (1 - b)) / (b - 0.5)


def window(L, curve, mut=None, crit_only=False):
    Afun = CURVES[curve][0]
    b = np.linspace(0.5, 11 / 12, NBETA)[1:]
    A = Afun(b)
    keep = A >= L if crit_only else np.ones_like(b, dtype=bool)
    low = lower(b, A, L)[keep]
    up = np.full(keep.sum(), np.inf) if mut == "m1" else (L - A / 2)[keep]
    return float(low.max()) / L, min(float(up.min()) / L, 0.5)


def inside(lo, hi, u1, u2, mut=None):
    first = (lo > u1) & (hi < u2)
    return first if mut == "m4" else first | ((lo > 1 - u2) & (hi < 1 - u1))


def evaluable(alphas, u1, u2, mut=None):
    out = np.zeros(np.broadcast(*alphas).shape, dtype=bool)
    for r in range(1, len(alphas) + 1):
        for S in itertools.combinations(range(len(alphas)), r):
            s = sum(alphas[i] for i in S)
            out |= inside(s, s, u1, u2, mut)
    return out


def surely_evaluable(los, his, u1, u2, mut=None):
    out = np.zeros(np.broadcast(*los, *his).shape, dtype=bool)
    for r in range(1, len(los) + 1):
        for S in itertools.combinations(range(len(los)), r):
            out |= inside(sum(los[i] for i in S), sum(his[i] for i in S), u1, u2, mut)
    return out


def drop_cell(a, b, h, om, mut=None):
    """At least the supremum of omega((1 - a1 - a2)/a2)/(a1 a2^2) on [a, a + h] x [b, b + h]."""
    A, B = a + h, b + h
    if mut == "m5":
        return om((1 - A - B) / B) / (A * B * B)
    return om.sup((1 - A - B) / B, (1 - a - b) / b) / (a * b * b)


def depth4_cell(a, b, c, d, h, om, mut=None):
    """At least the supremum of omega((1 - a1 - a2 - a3 - a4)/a4)/(a1 a2 a3 a4^2) on the cell of side h at (a, b, c, d)."""
    A, B, C, D = a + h, b + h, c + h, d + h
    if mut == "m5":
        return om((1 - A - B - C - D) / D) / (A * B * C * D * D)
    return om.sup((1 - A - B - C - D) / D, (1 - a - b - c - d) / d) / (a * b * c * d * d)


def midpoint(L, curve, n2, n3, om, mut=None, crit_only=False):
    u1, u2 = window(L, curve, mut, crit_only)
    v, R = u2 - u1, 1 - u2
    h2 = (0.5 - v) / n2
    a = v + h2 * (np.arange(n2) + 0.5)
    A1, A2 = np.meshgrid(a, a, indexing="ij")
    valid = (A2 < A1) & (1 - A1 - A2 >= A2) & ~((A1 > u1) & (A1 < u2))
    ne2 = valid & ~evaluable([A1, A2], u1, u2, mut)
    share2 = om((1 - A1 - A2) / A2) / (A1 * A2 ** 2)
    t = (np.arange(n3) + 0.5) / n3
    total = 0.0
    for i, j in np.argwhere(ne2):
        x1, x2 = a[i], a[j]
        cost = share2[i, j] * h2 * h2
        tot = x1 + x2
        best = cost
        if tot <= R:
            a3 = v + (x2 - v) * t
            a3 = a3[1 - tot - a3 >= a3]
            bad3 = a3[~evaluable([x1, x2, a3], u1, u2, mut)] if a3.size else a3
            if bad3.size == 0 or mut == "m2":
                best = 0.0
            elif np.all(tot + bad3 <= R):
                X3 = bad3[:, None]
                X4 = v + (X3 - v) * t[None, :]
                ne4 = (1 - tot - X3 - X4 >= X4) & ~evaluable([x1, x2, X3, X4], u1, u2, mut)
                f4 = om((1 - tot - X3 - X4) / X4) / (x1 * x2 * X3 * X4 ** 2)
                c4 = float((f4 * ne4 * (X3 - v) / n3).sum() * (x2 - v) / n3)
                best = min(cost, c4 * h2 * h2)
        total += best
    return total


def outer(L, curve, n, om, mut=None):
    u1, u2 = window(L, curve, mut)
    u1, u2 = u1 + MARGIN, u2 - MARGIN
    v, R = u2 - u1, 1 - u2
    h = (0.5 - v) / n
    e = v + h * np.arange(n)
    a, b = e[:, None], e[None, :]
    A, B = a + h, b + h
    cand = (b < A) & (a + 2 * b <= 1) & ~((a > u1) & (A < u2)) & ~surely_evaluable([a, b], [A, B], u1, u2, mut)
    drop = np.where(cand, h * h * drop_cell(a, b, h, om, mut), 0.0)
    total = 0.0
    for i, j in np.argwhere(cand):
        ai, bj = e[i], e[j]
        Ai, Bj = ai + h, bj + h
        best = drop[i, j]
        if Ai + Bj <= R:
            c = e[(e < Bj) & (ai + bj + 2 * e <= 1)]
            ne3 = ~surely_evaluable([ai, bj, c], [Ai, Bj, c + h], u1, u2, mut) if c.size else np.zeros(0, bool)
            if not ne3.any():
                best = 0.0
            elif np.all(Ai + Bj + c[ne3] + h <= R):
                c3 = c[ne3][:, None]
                C3 = c3 + h
                d = e[None, :]
                D = d + h
                ok = (d < C3) & (ai + bj + c3 + 2 * d <= 1) & ~surely_evaluable([ai, bj, c3, d], [Ai, Bj, C3, D], u1, u2, mut)
                f = depth4_cell(ai, bj, c3, d, h, om, mut)
                best = min(best, float(np.where(ok, f, 0.0).sum()) * h ** 4)
        total += best
    return total


def s1(mut=None):
    rows, ok = [], True
    for curve, L in (("hux", 2.29), ("hux", 2.30), ("cons", 2.25), ("cons", 2.27)):
        Afun, amax, brk = CURVES[curve]
        u1, u2 = window(L, curve, mut)
        u1x = max(float(lower(np.array(bb), Afun(bb), L)) for bb in brk) / L
        u2x = (L - amax / 2) / L
        good = abs(u1 - u1x) < 1e-7 and abs(u2 - u2x) < 1e-9 and u1 < u2 and u2 * L > 1
        ok &= good
        rows.append((curve, L, u1, u2, u1x, u2x))
    return ok, rows


def s2(om, mut=None):
    us, tab = omega_table(mut=mut)
    m12 = (us >= 1) & (us <= 2)
    e12 = float(np.max(np.abs(tab[m12] - 1 / us[m12])))
    m23 = (us > 2) & (us <= 3)
    e23 = float(np.max(np.abs(tab[m23] - (1 + np.log(us[m23] - 1)) / us[m23])))
    us4, tab4 = omega_table(H / 4, mut=mut)
    m3 = (us >= 3) & (us <= 15)
    e3 = float(np.max(np.abs(tab[m3] - np.interp(us[m3], us4, tab4))))
    ids = []
    for v in (0.08, 0.1, 0.2):
        x = np.linspace(v, 0.5, 400001)
        f = om((1 - x) / x) / x ** 2
        ids.append(float(om(1 / v)) / v - float(np.trapezoid(f, x)))
    ok = e12 < 1e-12 and e23 < 1e-7 and e3 < 1e-7 and all(abs(t - 1) < 1e-4 for t in ids)
    return ok, {"e12": e12, "e23": e23, "e3": e3, "ids": ids}


def s3(om, mut=None, full=True):
    hux = midpoint(2.30, "hux", 200, 100, om, mut)
    cons = midpoint(2.25, "cons", 200, 100, om, mut)
    ok = 0.60 <= hux <= 0.70 and 0.80 <= cons <= 0.90
    rec = {"hux": hux, "cons": cons}
    if full:
        rec["hux_fine"] = midpoint(2.30, "hux", 400, 200, om, mut)
        ok &= abs(rec["hux_fine"] - hux) < 0.03
    return ok, rec


def cell_check(om, mut=None, n=150, draws=20000, seed=576):
    """The cell bounds against the integrands at random points of random cells (v = 0.08, side (1/2 - v)/n)."""
    rng = np.random.default_rng(seed)
    v = 0.08
    h = (0.5 - v) / n
    a, b = (v + h * rng.integers(0, n, draws) for _ in range(2))
    x1, x2 = a + h * rng.random(draws), b + h * rng.random(draws)
    val2 = om((1 - x1 - x2) / x2) / (x1 * x2 ** 2)
    pos2 = val2 > 0
    rat2 = float(np.min(drop_cell(a, b, h, om, mut)[pos2] / val2[pos2]))
    corners = [v + h * rng.integers(0, n // 2, draws) for _ in range(4)]
    pts = [c + h * rng.random(draws) for c in corners]
    val4 = om((1 - sum(pts)) / pts[3]) / (pts[0] * pts[1] * pts[2] * pts[3] ** 2)
    pos4 = val4 > 0
    rat4 = float(np.min(depth4_cell(*corners, h, om, mut)[pos4] / val4[pos4]))
    return rat2 >= 1 and rat4 >= 1 and pos2.sum() > draws // 2 and pos4.sum() > draws // 10, (rat2, rat4, int(pos2.sum()), int(pos4.sum()))


def s4(om, rec3, mut=None, full=True):
    ok_cells, gaps = cell_check(om, mut)
    rec = {"sanity": outer(2.30, "hux", 150, om, mut), "gaps": gaps}
    ok = ok_cells and rec["sanity"] >= rec3["hux"]
    if full:
        rec["hux229"] = outer(2.29, "hux", 600, om, mut)
        rec["cons227"] = outer(2.27, "cons", 600, om, mut)
        ok &= rec["hux229"] < 1 and rec["cons227"] < 1
    return ok, rec


def run(mut=None, full=False):
    om = Omega(mut)
    g1, r1 = s1(mut)
    g2, r2 = s2(om, mut)
    g3, r3 = s3(om, mut, full)
    g4, r4 = s4(om, r3, mut, full)
    return (g1, g2, g3, g4), (r1, r2, r3, r4), om


def main():
    t0 = time.time()
    gates, (r1, r2, r3, r4), om = run(full=True)
    for curve, L, u1, u2, u1x, u2x in r1:
        print(f"S1: {curve} L = {L}: window ({u1:.6f}, {u2:.6f}); breakpoint values ({u1x:.6f}, {u2x:.6f}); "
              f"u2 L = {u2 * L:.4f}", flush=True)
    print(f"S2: omega errors {r2['e12']:.1e} on [1,2], {r2['e23']:.1e} on [2,3], {r2['e3']:.1e} against step H/4 on "
          f"[3,15]; Buchstab identity {', '.join(f'{t:.6f}' for t in r2['ids'])}", flush=True)
    print(f"S3: midpoint losses at (200,100): hux 2.30 {r3['hux']:.4f}, cons 2.25 {r3['cons']:.4f}; hux 2.30 at "
          f"(400,200) {r3['hux_fine']:.4f}", flush=True)
    print(f"S4: outer bounds at n = 600: hux 2.29 {r4['hux229']:.4f}, cons 2.27 {r4['cons227']:.4f}; hux 2.30 at "
          f"n = 150 {r4['sanity']:.4f} >= {r3['hux']:.4f}; least ratio of cell bound to integrand at random points "
          f"{r4['gaps'][0]:.4f} (depth 2, {r4['gaps'][2]} points) and {r4['gaps'][1]:.4f} (depth 4, {r4['gaps'][3]} points)",
          flush=True)
    for curve, Ls in (("hux", (2.26, 2.28, 2.29, 2.32)), ("cons", (2.24, 2.26, 2.27))):
        vals = ", ".join(f"{L}: {midpoint(L, curve, 400, 200, om):.4f}" for L in Ls)
        print(f"  midpoint at (400,200), {curve}: {vals}", flush=True)
    for curve, L in (("hux", 2.28), ("hux", 2.30), ("cons", 2.24), ("cons", 2.25)):
        u1, u2 = window(L, curve, crit_only=True)
        print(f"  critical beta only, {curve} L = {L}: window ({u1:.4f}, {u2:.4f}), midpoint loss at (400,200) "
              f"{midpoint(L, curve, 400, 200, om, crit_only=True):.4f}", flush=True)
    print(f"  outer bound, hux 2.30, n = 600: {outer(2.30, 'hux', 600, om):.4f}", flush=True)
    ok = all(gates)
    caught = {}
    for m in MUTS:
        caught[m] = not all(run(m)[0])
    print(f"gates {'pass' if ok else 'FAIL'} ({', '.join(f'S{i + 1} ' + ('pass' if g else 'FAIL') for i, g in enumerate(gates))}); "
          f"mutations: {', '.join(f'{m} ' + ('caught' if c else 'MISSED') for m, c in caught.items())}; "
          f"{time.time() - t0:.0f}s", flush=True)
    return 0 if ok and all(caught.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
