"""Exact-arithmetic checks for SEVEN-THIRDS.md (README round 528): where Chen-Gupta-Li's 7/3 sits
for prime moduli, and what the stack's inputs do there.

The model.  Exponents are powers of Q = qT with q prime and T = q^{o(1)} (the Linnik deduction of
round 520 uses T = O(log q)).  A Dirichlet polynomial of length N = Q^l is large at V = N^s on a set
W of characters; a large-values estimate is a bound |W| <= Q^{F(l, s) + o(1)}.  The families are:
    MVT  max(2l(1-s), 1 + l(1-2s))                       mean value theorem, CGL (1.2)
    HUX  max(2l(1-s), 1 + l(4-6s))                       Huxley, CGL (1.3); the stack's round 526
    HM   2l(1-s) once l > l_HM(s)                         Halasz-Montgomery, off-diagonal on Re s = a:
         l_HM(s) = min(1, 1/(2(2s-1)), (5/12)/(2s-1-1/12))   a -> 0 (Polya-Vinogradov), a = 1/12
                                                          (the half-plane: mu(1/12) = 5/12); round 525
    P31  max(2l(1-s), 1/2 + l(3-4s), c + l(2-4s)), c = 4/3, for 7/10 <= s <= 4/5 and l >= 2/3:
         CGL Proposition 3.1, which is their bound for prime q with T = q^{o(1)}
A zero detector has a mollifier of length Q^x and smoothing Q^y.  Its class-I zeros give large values
of blocks of length Q^nu, x <= nu <= y, raised to powers (and multiplied across detectors).  Its
class-II zeros number at most Q^{c2}, with c2 from one of
    FM(j)   x <= 1/j:  c2 = 1 - p_j y (s - 1/2),  p_j = 4j/(j+2)   (Holder: L^4 and M^{2j}, X^j <= Q)
    FMx     x >= 0:    c2 = 1 + 2x - 4y(s - 1/2)                  (pointwise |M_X| <= X^{1/2}, p = 4)
    FMg(j)  x >= 1/j:  c2 = p_j (1/4 + x/2 - y(s - 1/2))         (Holder with X^j > Q)
    HPE(a)  0 < a < s: class II is empty once y(s - a) > mu(a) + x(1 - a)  (the half-plane's pointwise
            bound on Re s = a; mu(a) = 1/2 - a for a <= 1/12, (11/12 - a)/2 for 1/12 <= a <= 11/12)
    MOM(k, a)  1/2 <= a < s:  c2 = 1 + (2k-4) mu(a) + 2k(x(1-a) - y(s-a))  (2k-th moment by Holder)

Checks.
  (T) The triple point at s = 5/7, t = (7/3)(1 - 5/7) = 2/3: F_MVT(7/9) = F_P31(7/9) = 2/3, the
      density term is 2/3 at 7/6, FM(1) at x = 1 needs y = 7/6 and FMx at x = 0 needs y = 7/18,
      with 7/9 = 2(7/18) and 7/6 = 3(7/18).
  (B) The barrier at s = 5/7.  Let B = {7/18, 7/9} u [7/6, oo).  (B1) Every finite sum of elements
      of B is 7/18, 7/9 or at least 7/6, and every family above has F >= 2/3 there.  (B2) For every
      detector above with c2 <= 2/3, the interval [x, y] meets B (exactly, over the finitely many
      breakpoints of each affine piece; MOM on a rational grid of (k, a); HPE at the two lines that
      minimize its bound, with a grid check that no other line does better).  So a zero whose blocks
      lie in B for every detector is counted by no product of blocks below Q^{2/3}, and within this
      family no argument gives a density exponent below 7/3 at s = 5/7.
  (S) The socket.  With c = 4/3 - kappa in P31, for kappa in {1/100, 1/50, 1/39}: the crossing
      s0 = (5 - 6 kappa)/(7 - 3 kappa) has 3/(2 - s0) = 3c/(1 + s0) = 7/3 - kappa and lies in
      [7/10, 4/5]; one detector certifies 7/3 - kappa at s0; and on a rational grid of s in
      [1/2, 11/12] some detector certifies an exponent at most 7/3 - kappa.  At kappa = 1/20 the
      crossing leaves [7/10, 4/5].
  (C) Calibration: on a rational grid of s in [1/2, 11/12] (with 5/7, 3/4 and 23/29), one detector
      certifies 36/13 with MVT alone (round 524), 87/35 with MVT and HM (round 525), 12/5 with MVT
      and HUX (round 527), and 7/3 with all four families.  With (B), 7/3 is the least exponent this
      family certifies at s = 5/7.
  (P) The exponents compared at CGL's critical case (|W| = q^{2/3}, N = q^{7/9}): their term
      q^2 |W|^{3/2} = q^3; the Gauss-sum form with |F| <= M^{11/12} pointwise (the half-plane) is
      q^{31/9}; with |F| = M^{1/2} on average it is q^{19/6}.

Scope.  This checks arithmetic in a model, not the analysis.  The model's families are the ones the
stack has (rounds 520-527) plus CGL Proposition 3.1; (B) is a statement about this family only.  To
show the checks can fail, the script runs six mutations and requires each to fail at least one check.
"""
from fractions import Fraction as F
from math import ceil

S57 = F(5, 7)
B_PTS = (F(7, 18), F(7, 9))
B_TAIL = F(7, 6)


def mu(a):
    if a <= F(1, 12):
        return F(1, 2) - a
    if a <= F(11, 12):
        return (F(11, 12) - a) / 2
    return F(0)


def terms(m, s, c=F(4, 3)):
    """(lo, [(c_i, d_i)]) with F = max_i c_i + d_i l on l >= lo, or None where the method gives nothing."""
    dens = (F(0), 2 * (1 - s))
    if m == "MVT":
        return F(0), [dens, (F(1), 1 - 2 * s)]
    if m == "HUX":
        return F(0), [dens, (F(1), 4 - 6 * s)]
    if m == "HM":
        cands = [F(1)]
        if 2 * s - 1 > 0:
            cands.append(F(1) / (2 * (2 * s - 1)))
        if 2 * s - 1 - F(1, 12) > 0:
            cands.append(F(5, 12) / (2 * s - 1 - F(1, 12)))
        return min(cands), [dens]           # strict: l > lo
    if m == "P31":
        if not (F(7, 10) <= s <= F(4, 5)):
            return None
        return F(2, 3), [dens, (F(1, 2), 3 - 4 * s), (c, 2 - 4 * s)]
    raise ValueError(m)


METHODS = ("MVT", "HUX", "HM", "P31")


def F_at(m, s, l, c=F(4, 3)):
    tm = terms(m, s, c)
    if tm is None:
        return None
    lo, ts = tm
    if l < lo or (m == "HM" and l == lo):
        return None
    return max(ci + di * l for ci, di in ts)


def good_interval(m, s, t, c=F(4, 3)):
    """{l : F_m(l) <= t} as (a, b), closed except HM's open left end, or None."""
    tm = terms(m, s, c)
    if tm is None:
        return None
    a, ts = tm
    b = None
    for ci, di in ts:
        if di > 0:
            v = (t - ci) / di
            b = v if b is None else min(b, v)
        elif di < 0:
            a = max(a, (t - ci) / di)
        elif ci > t:
            return None
    if b is None or a > b:
        return None
    if m == "HM":
        a += F(1, 10**9)            # HM's good set is open at its left end
    return a, b


def covered(G, lo, hi):
    """Every nu in [lo, hi] (0 < lo) has k >= 1 with k*nu in the union G of intervals."""
    pieces = []
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


def tiny_floor(G):
    """nu0 > 0 with (0, nu0] covered by the copies of one nondegenerate interval of G."""
    best = F(0)
    for a, b in G:
        if b > a > 0:
            k0 = max(1, ceil(1 / (b / a - 1)))
            best = max(best, b / k0)
    return best


def detectors(s, t, js=range(1, 13), x_grid=None):
    """(x_lo, x_hi, y0, y1, tag): y_min(x) = y0 + y1*x on x in [x_lo, x_hi] (x_hi None = unbounded)."""
    h = s - F(1, 2)
    for j in js:
        p = F(4 * j, j + 2)
        yield F(0), F(1, j), (1 - t) / (p * h), F(0), f"FM({j})"
        yield F(1, j), None, (F(1, 4) - t / p) / h, F(1, 2) / h, f"FMg({j})"
    yield F(0), None, (1 - t) / (4 * h), F(2) / (4 * h), "FMx"
    for a in (F(1, 10**9), F(1, 12)):
        if a < s:
            yield F(0), None, mu(a) / (s - a), (1 - a) / (s - a), f"HPE({a})"


def mom_detectors(s, t):
    for k in range(2, 13):
        for i in range(0, 60):
            a = F(1, 2) + (s - F(1, 2)) * F(i, 60)
            m_k = 1 + (2 * k - 4) * mu(a)
            yield F(0), None, (m_k - t) / (2 * k * (s - a)), (1 - a) / (s - a), f"MOM({k},{a})"


def meets_B(x, y):
    if y < x:
        return False
    if any(x <= b <= y for b in B_PTS):
        return True
    return y >= B_TAIL


def avoid_points(d, Bpts=B_PTS, tail=B_TAIL):
    """x in the detector's domain with [x, y_min(x)] missing B, from exact breakpoints."""
    lo, hi, y0, y1, tag = d
    y = lambda x: y0 + y1 * x
    brk = {lo}
    if hi is not None:
        brk.add(hi)
    for v in list(Bpts) + [tail]:
        brk.add(v)
        if y1 != 0:
            brk.add((v - y0) / y1)
    if y1 != 1:
        brk.add(y0 / (1 - y1))
    brk = sorted(b for b in brk if b >= lo and (hi is None or b <= hi))
    pts = list(brk) + [(u + v) / 2 for u, v in zip(brk, brk[1:])]
    pts.append(brk[-1] + 1 if hi is None else brk[-1])
    return [x for x in pts if x >= lo and (hi is None or x <= hi) and not meets_B(x, y(x))]


def check_T():
    t = F(2, 3)
    ok = [
        F_at("MVT", S57, F(7, 9)) == t,
        F_at("P31", S57, F(7, 9)) == t,
        2 * F(7, 6) * (1 - S57) == t,
        (1 - t) / (F(4, 3) * (S57 - F(1, 2))) == F(7, 6),
        (1 - t) / (4 * (S57 - F(1, 2))) == F(7, 18),
        F(7, 9) == 2 * F(7, 18) and F(7, 6) == 3 * F(7, 18),
    ]
    return ok


def check_B(c=F(4, 3), extra=()):
    t = F(2, 3)
    fails = []
    # (B1) sums of elements of B: k*7/18 for k = 1, 2 lie in B_PTS, k >= 3 or any tail element >= 7/6
    assert all(k * F(7, 18) in B_PTS or k * F(7, 18) >= B_TAIL for k in range(1, 50))
    for m in METHODS:
        for l in B_PTS:
            v = F_at(m, S57, l, c)
            if v is not None and v < t:
                fails.append(f"B1 {m} at {l}: {v}")
        tm = terms(m, S57, c)
        if tm is not None and (F(0), 2 * (1 - S57)) not in tm[1]:
            fails.append(f"B1 {m} lacks the density term")
        if tm is not None:
            v = F_at(m, S57, max(B_TAIL, tm[0] + F(1, 10**6)), c)
            if v is not None and v < t:
                fails.append(f"B1 {m} at the tail: {v}")
    for m, fn in extra:
        for l in list(B_PTS) + [B_TAIL]:
            v = fn(l)
            if v is not None and v < t:
                fails.append(f"B1 {m} at {l}: {v}")
    # (B2) detectors
    dets = list(detectors(S57, t)) + list(mom_detectors(S57, t))
    for d in dets:
        bad = avoid_points(d)
        if bad:
            fails.append(f"B2 {d[4]} avoids B at x = {bad[0]}")
    # HPE: no line a in (0, 5/7) beats min over a -> 0+ and a = 1/12, on a grid of a and x
    for i in range(1, 200):
        a = S57 * F(i, 200)
        for x in (F(0), F(1, 4), F(7, 18), F(1, 2), F(7, 9), F(1)):
            ya = (mu(a) + x * (1 - a)) / (S57 - a)
            ybest = min((mu(F(1, 10**9)) + x) / S57, (mu(F(1, 12)) + x * F(11, 12)) / (S57 - F(1, 12)))
            if ya < ybest - F(1, 10**6):
                fails.append(f"B2 HPE line {a} beats the endpoints at x = {x}")
    return fails


def certify(s, A, c=F(4, 3), methods=METHODS):
    """Some single detector certifies the exponent A at s (exact)."""
    t = A * (1 - s)
    G = [iv for m in methods if (iv := good_interval(m, s, t, c)) is not None]
    f0 = tiny_floor(G)
    for lo, hi, y0, y1, tag in detectors(s, t):
        xs = [lo] if hi is None else [lo, hi]
        for x in xs:
            y = y0 + y1 * x
            if y <= x:
                return tag
            x2 = x if x > 0 else f0
            if x2 <= 0:
                continue
            if x2 >= y or covered(G, x2, y):
                return tag
    return None


def check_S(kappas=(F(1, 100), F(1, 50), F(1, 39))):
    fails = []
    for kap in kappas:
        c = F(4, 3) - kap
        s0 = (5 - 6 * kap) / (7 - 3 * kap)
        A = F(7, 3) - kap
        if not (3 / (2 - s0) == A and 3 * c / (1 + s0) == A and F(7, 10) <= s0 <= F(4, 5)):
            fails.append(f"S crossing at kappa = {kap}")
        if certify(s0, A, c) is None:
            fails.append(f"S no detector at the crossing, kappa = {kap}")
        for i in range(1, 101):
            s = F(1, 2) + (F(11, 12) - F(1, 2)) * F(i, 100)
            if certify(s, A, c) is None:
                fails.append(f"S no detector at s = {s}, kappa = {kap}")
                break
    k5 = F(1, 20)
    if (5 - 6 * k5) / (7 - 3 * k5) >= F(7, 10):
        fails.append("S kappa = 1/20 crossing stays in [7/10, 4/5]")
    return fails


GRID = [F(1, 2) + (F(11, 12) - F(1, 2)) * F(i, 100) for i in range(1, 101)]
CALIBRATION = [  # (methods, A, round): the exponents the stack has landed, and Chen-Gupta-Li's 7/3
    (("MVT",), F(36, 13), "524"),
    (("MVT", "HM"), F(87, 35), "525"),
    (("MVT", "HUX"), F(12, 5), "527"),
    (METHODS, F(7, 3), "CGL"),
]


def check_C(cal=CALIBRATION):
    fails = []
    for methods, A, tag in cal:
        for s in GRID + [F(5, 7), F(3, 4), F(23, 29)]:
            if certify(s, A, methods=methods) is None:
                fails.append(f"C {tag}: no detector certifies {A} at s = {s}")
                break
    return fails


def check_P():
    W, N, M = F(2, 3), F(7, 9), F(2, 9)
    return [2 + F(3, 2) * W == 3,
            3 * W + F(5, 4) + N / 4 == F(31, 9),
            3 * W + F(3, 2) * N == F(19, 6),
            # the Gauss-sum form: (N/q)^3 q^{3/2} |W|^3 |F|^3 with |F| = M^{11/12} or M^{1/2}
            3 * (N - 1) + F(3, 2) + 3 * W + 3 * F(11, 12) * M == F(31, 9),
            3 * (N - 1) + F(3, 2) + 3 * W + 3 * F(1, 2) * M == F(19, 6)]


def main(mut=None):
    out = {}
    out["T"] = [] if all(check_T()) else ["T"]
    if mut == "c below 4/3 in P31":
        out["B"] = check_B(c=F(4, 3) - F(1, 100))
    elif mut == "MVT without the density term":
        out["B"] = check_B(extra=[("MVT'", lambda l: 1 + l * (1 - 2 * S57))])
    elif mut == "a better half-plane, mu(1/12) = 5/24":
        global mu
        mu0 = mu
        mu = lambda a: mu0(a) / 2
        out["B"] = check_B()
        mu = mu0
    elif mut == "class II at p = 4 with X = Q^(1/2) free":
        out["B"] = check_B()
        d = (F(1, 2), None, (1 - F(2, 3)) / (4 * (S57 - F(1, 2))), F(0), "fake")
        if avoid_points(d):
            out["B"].append("B2 fake detector avoids B")
    else:
        out["B"] = check_B()
    if mut == "socket with kappa = 1/20 in place of 1/39":
        out["S"] = check_S(kappas=(F(1, 100), F(1, 50), F(1, 20)))
    elif mut is None:
        out["S"] = check_S()
    else:
        out["S"] = []
    out["P"] = [] if all(check_P()) else ["P"]
    if mut == "calibration at 12/5 - 1/100 for MVT and HUX":
        out["C"] = check_C(cal=[(("MVT", "HUX"), F(12, 5) - F(1, 100), "527-")])
    elif mut is None:
        out["C"] = check_C()
    else:
        out["C"] = []
    return out


MUTATIONS = ["c below 4/3 in P31", "MVT without the density term", "a better half-plane, mu(1/12) = 5/24",
             "class II at p = 4 with X = Q^(1/2) free", "socket with kappa = 1/20 in place of 1/39",
             "calibration at 12/5 - 1/100 for MVT and HUX"]

if __name__ == "__main__":
    res = main()
    nfail = 0
    for key in "TBSPC":
        print(f"({key}) {'pass' if not res[key] else 'FAIL'}")
        for f in res[key]:
            print("    ", f)
        nfail += len(res[key])
    uncaught = 0
    for name in MUTATIONS:
        r = main(name)
        n = sum(len(v) for v in r.values())
        print(f"mutation '{name}': {n} failing checks, {'caught' if n else 'NOT CAUGHT'}")
        uncaught += 0 if n else 1
    print(f"{len(MUTATIONS)} mutations, {len(MUTATIONS) - uncaught} caught")
    raise SystemExit(1 if nfail or uncaught else 0)
