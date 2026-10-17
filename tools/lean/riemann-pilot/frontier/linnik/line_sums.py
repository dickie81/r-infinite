"""A numerical probe of the line sums in SEVEN-THIRDS.md section 6 (README round 529).

For a set W of characters mod a prime q, R(b) = sum_{chi in W} chi(b) on F_q^*, and for a line
b1 m1 + b2 m2 + m3 = 0 (all m_i nonzero)
    L(m) = sum_{(b1, b2) on the line, b1 b2 != 0} R(b1) R(b2/b1) conj(R(b2)).
Chen-Gupta-Li's first term of S_3 is the bound |L(m)| <= q |W|^{3/2} on the lines with |m_i| <= M,
M = q/N.  The probe takes |W| = q^{2/3}, N = q^{7/9} (their critical case) at q = 10007 and 10009.

  (P1) The lines with m1 + m2 + m3 = 0 pass through (b1, b2) = (1, 1), where R(1)^3 = |W|^3, which is
       q|W|^{3/2} when |W| = q^{2/3}.  Gate: the 12 largest |L| (diagonal triple removed) are such
       lines, and each is within 1% of |W|^3.
  (P2) Generic lines: the points where b1, b2 or b2/b1 equals 1 removed, and the diagonal triple
       removed.  For random W the median |L| is within a factor 2 of sqrt(q)|W|^{3/2} (the
       random-phase size), a factor sqrt(q) below the per-line bound.  For W an interval of exponents
       (consecutive powers of a generator) or a progression of exponents with difference
       floor((q - 1)/|W|), some lines come within a factor 2 of q|W|^{3/2}.
  (P3) W a random subset of a subgroup of X(q) of order h | q - 1, h from |W| to q - 1: the mean |L|
       over generic lines divided by sqrt(q)|W|^{1/2}E(W)^{1/2}, E(W) = sum_b |R(b)|^4/(q - 1), stays
       in [0.05, 0.5] while E(W)/|W|^2 ranges from about 23 to about 390.
Mutation: R replaced by random complex values of the same mean square (not the transform of a set),
for which (P1) must fail.

Scope.  This is a numerical probe at one size of q, for these families of W.  It proves nothing about
large-values sets, and the families are not large-values sets of polynomials supported on [N, 2N].
"""
import numpy as np


def prim_root(q):
    f, n, p = [], q - 1, 2
    while p * p <= n:
        if n % p == 0:
            f.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        f.append(n)
    return next(g for g in range(2, q) if all(pow(g, (q - 1) // r, q) != 1 for r in f))


def dlog_table(q):
    g, dl, x = prim_root(q), np.zeros(q, dtype=np.int64), 1
    for j in range(q - 1):
        dl[x] = j
        x = x * g % q
    return dl


def R_of(K, q):
    ind = np.zeros(q - 1)
    ind[K] = 1.0
    return np.fft.fft(ind)


def sums(R, dl, q, M, W, generic):
    b2, out = np.arange(1, q, dtype=np.int64), []
    for m1 in range(-M, M + 1):
        for m2 in range(-M, M + 1):
            for m3 in range(-M, M + 1):
                if 0 in (m1, m2, m3):
                    continue
                b1 = (-(m2 * b2 + m3) * pow(m1 % q, q - 2, q)) % q
                ok = b1 != 0
                if generic:
                    ok &= (b1 != 1) & (b2 != 1) & (b1 != b2)
                l1, l2 = dl[b1[ok]], dl[b2[ok]]
                t = R[l1] * R[(l2 - l1) % (q - 1)] * np.conj(R[l2]) - W
                out.append(((m1, m2, m3), t.sum()))
    return out


def sizes(q):
    return round(q / round(q ** (7 / 9))), round(q ** (2 / 3))


def p1(R=None, q=10007, seed=1):
    M, Wn = sizes(q)
    dl, rng = dlog_table(q), np.random.default_rng(seed)
    K = rng.choice(q - 1, Wn, replace=False)
    if R is None:
        R = R_of(K, q)
    res = sums(R, dl, q, M, Wn, generic=False)
    top = sorted(res, key=lambda r: -abs(r[1]))[:12]
    ok = all(sum(m) == 0 and abs(abs(v) / Wn ** 3 - 1) < 0.01 for m, v in top)
    print(f"(P1) q={q} M={M} |W|={Wn}: top 12 lines {'all' if ok else 'NOT all'} with m1+m2+m3=0 "
          f"and |L| = |W|^3 within 1%; e.g. m={top[0][0]}, |L|/|W|^3={abs(top[0][1]) / Wn ** 3:.4f}")
    return ok


def p2(q=10007, seed=1):
    M, Wn = sizes(q)
    dl, rng = dlog_table(q), np.random.default_rng(seed)
    kinds = {"random": rng.choice(q - 1, Wn, replace=False), "interval": np.arange(Wn),
             "progression": np.arange(0, q - 1, (q - 1) // Wn)[:Wn]}
    ok = True
    for name, K in kinds.items():
        L = np.array([v for _, v in sums(R_of(K, q), dl, q, M, Wn, generic=True)])
        rp = np.sqrt(q) * Wn ** 1.5
        med, mx = np.median(np.abs(L)) / rp, np.abs(L).max() / (q * Wn ** 1.5)
        print(f"(P2) {name:8s}: median |L|/(sqrt(q)|W|^1.5) = {med:.3f}, max |L|/(q|W|^1.5) = {mx:.3f}")
        if name == "random":
            ok &= 0.5 <= med <= 2
        else:
            ok &= mx >= 0.5
    return ok


def p3(q=10009, seed=7):
    M, Wn = sizes(q)
    dl, rng = dlog_table(q), np.random.default_rng(seed)
    ok = True
    for h in [h for h in range(Wn, q) if (q - 1) % h == 0]:
        K = rng.choice(h, Wn, replace=False) * ((q - 1) // h)
        R = R_of(K, q)
        E = (np.abs(R) ** 4).sum() / (q - 1)
        L = np.array([v for _, v in sums(R, dl, q, M, Wn, generic=True)])
        r = np.mean(np.abs(L)) / (np.sqrt(q) * Wn ** 0.5 * E ** 0.5)
        print(f"(P3) h={h:6d}: E/|W|^2 = {E / Wn ** 2:7.2f}, mean|L|/(sqrt(q)|W|^.5 E^.5) = {r:.3f}")
        ok &= 0.05 <= r <= 0.5
    return ok


if __name__ == "__main__":
    oks = [p1(), p2(), p3()]
    q = 10007
    M, Wn = sizes(q)
    rng = np.random.default_rng(3)
    fake = (rng.normal(size=q - 1) + 1j * rng.normal(size=q - 1)) * np.sqrt(Wn / 2)
    caught = not p1(R=fake)
    print(f"gates {'pass' if all(oks) else 'FAIL'}; mutation (R not from a set) {'caught' if caught else 'NOT CAUGHT'}")
    raise SystemExit(0 if all(oks) and caught else 1)
