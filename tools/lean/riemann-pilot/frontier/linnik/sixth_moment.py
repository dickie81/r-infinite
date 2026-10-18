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
four mutations and requires each to fail at least one check.
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


def certify_six(s, A, delta):
    t = A * (1 - s)
    G = [iv for m in st.METHODS if (iv := st.good_interval(m, s, t)) is not None]
    if st.certify(s, A) is not None:
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


def best_exponent(s, delta, lo=F(2), hi=F(7, 3) + F(1, 100), tol=F(1, 10**4)):
    if certify_six(s, hi, delta) is None:
        return None
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if certify_six(s, mid, delta) is not None:
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
    mf, rows = check_M(qs if mut in (None, "drop one residue class") else [], mut)
    res["M"] = mf
    if verbose:
        for d, w, a in table:
            print(f"    delta = {str(d):>5}: model exponent {float(w):.4f} (max over the grid, at s = {a})")
        for q, N, rho, scale, dt in rows:
            print(f"    q = {q:>9}, N = {N:>4}: rho = {rho:.4f}, W^6/((q-1)D3) = {scale:.3f}  [{dt:.1f}s]")
    return res


MUTATIONS = ["critical block one tenth off", "socket delta enters with the wrong sign",
             "drop one residue class", "fourth moment with N^2 > q"]


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
    for key in "KXM":
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
