"""The concentrated sets are smooth numbers at a Farey point (README round 534; SEVEN-THIRDS.md section 14).

For the (G1) sets W of gram_probe.py, with top singular vector b_n = sqrt(w(n)) V(ind n) on [N, 2N] and the 24 values
beta != 1 with the largest |R(beta)| of structure_probe.py (S1), at q = 10007, 100003 and 1000003:

  (P1) Write each beta as m/m' with structure_probe.rep.  The gcd d of the 24 differences m - m' is greater than 1,
       q/d lies in [N, 2N], and q/d is the point q/d' (d' a positive integer) nearest to the centre 3N/2 of the weight.
  (P2) Put r = d n - q, so that n = r/d (mod q), r = -q (mod d) and |r| < q/2 for n in [N, 2N].  Let y be the least
       prime such that at least 90% of sum |b_n|^2 lies on the n whose r is y-smooth (no prime factor above y).  Then
       y = 11, 17 and 29 at the three q, and at most 7% of the n in [N, 2N] have y-smooth r.  On the main support (the
       PR largest |b_n|, PR the participation ratio) the b_n have one phase, to within 10^-6 pi.
  (P3) Let psi_j(a) = e(j ind_d(a)/phi(d)) be the characters of the cyclic group (Z/d)^*, and for k in W let lambda(k)
       be the j that maximises |sum_{h <= M, (h, d) = 1} chi_k(h) psi_j(h)|.  Then chi_k(-1) = psi_lambda(k)(-1) for
       every k in W, each class lambda = j has between 0.9 and 1.1 times |W|/phi(d) members, and at least 99.9% of the
       additive quadruples k1 + k2 = k3 + k4 (mod L) of W have lambda1 + lambda2 = lambda3 + lambda4 (mod phi(d)).
       For a random W of the same size, labelled by the same rule, the share is at most 60%.
  (P4) The primes the labels do not see agree with them: for every prime p with M < p <= y and p not dividing d, the
       mean over W of Re chi_k(p) psi_lambda(k)(p) is at least 0.12, while for the random W of (P3), with its own
       labels, its absolute value is at most 0.08.
  (P5) The explicit set: b' = sqrt(w) times the indicator of the n in [N, 2N] with y-smooth r, and W' the R exponents
       k != 0 with the largest |A* b'|.  The concentration of W' (power iteration on G restricted to W') is at least
       0.95 times that of W.
  (P6) With k the number of primes p <= y not dividing d, (E(W)/|W|^3)^{1/k} lies between 0.70 and 0.77 at the
       three q, and gamma = log(E(W)/|W|^3)/log c, with c the concentration of W, is below 3.
Mutation: the labels of (P3) permuted at random over W, for which the 99.9% gate of (P3) must fail.

Scope.  A numerical probe at three values of q, for the sets one search method finds.  It describes those sets and one
explicit family; it bounds nothing over other sets of size q^{2/3}.  (P6) records a regularity at three q.
"""
from functools import reduce
from math import gcd

import numpy as np

from gram_probe import QS, Gram
from line_sums import dlog_table, prim_root
from structure_probe import s1, rep


def lpf(x):
    """The largest prime factor of |x| (1 for |x| = 1)."""
    x, p, big = abs(int(x)), 2, 1
    while p * p <= x:
        while x % p == 0:
            x //= p
            big = p
        p += 1
    return max(big, x) if x > 1 else big


def labels(S, K, d, dl):
    units = [a for a in range(1, d) if gcd(a, d) == 1]
    ph = len(units)
    gd = next(g for g in units if len({pow(g, e, d) for e in range(ph)}) == ph)
    indd = {pow(gd, e, d): e for e in range(ph)}
    hs = np.array([h for h in range(1, int(S.M) + 1) if gcd(h, d) == 1])
    psi = np.exp(2j * np.pi * np.outer(np.arange(ph), [indd[h % d] for h in hs]) / ph)
    chi = np.exp(2j * np.pi * np.outer(K, dl[hs]) / S.L)
    sgn = np.array([round(np.exp(2j * np.pi * j * indd[d - 1] / ph).real) for j in range(ph)])
    return np.abs(chi @ psi.T).argmax(1), ph, sgn, indd


def align(S, K, lab, ph, indd, d, p, dl):
    """The mean over K of Re chi_k(p) psi_lab(k)(p)."""
    return np.exp(2j * np.pi * (K * dl[p] / S.L + lab * indd[p % d] / ph)).real.mean()


def lab_share(S, K, lab, ph):
    """The share of the additive quadruples of K whose labels add, by Fourier analysis on Z/ph."""
    E = []
    for t in range(ph):
        f = np.zeros(S.L, complex)
        f[K] = np.exp(2j * np.pi * t * lab / ph)
        E.append((np.abs(np.fft.fft(f)) ** 4).sum() / S.L)
    return sum(E) / (ph * E[0])


def conc(S, K, v, iters=60):
    m = np.zeros(S.L, bool)
    m[K] = True
    v = np.where(m, v, 0)
    v /= np.linalg.norm(v)
    for _ in range(iters):
        v = np.where(m, S.G(v), 0)
        v /= np.linalg.norm(v)
    return S.rayleigh(v) / S.L


def main():
    ok, caught = True, True
    rng = np.random.default_rng(29)
    for q in QS:
        dl = dlog_table(q)
        S = Gram(q, dl=dl)
        v, K = S.alternate()
        c = S.rayleigh(v) / S.L
        _, bs, _, _ = s1(S, K, prim_root(q))
        d = reduce(gcd, [abs(m - mp) for m, mp in (rep(b, q) for b in bs)])
        near = min(range(1, q), key=lambda e: abs(q / e - 1.5 * S.N)) if d > 1 else None
        print(f"(P1) q={q} N={S.N} M={S.M:.2f}: gcd d = {d}, q/d = {q / d:.0f}, 3N/2 = {1.5 * S.N:.0f}, "
              f"nearest q/d' at d' = {near}")
        ok &= d > 1 and S.N <= q / d <= 2 * S.N and near == d
        n = np.arange(S.N, 2 * S.N + 1)
        r = d * n - q
        ok &= int(np.abs(r).max()) < q / 2
        P = np.array([lpf(x) if x else q for x in r])
        b = np.sqrt(S.w) * (S.L * np.fft.ifft(v))[S.idx]
        p = np.abs(b) ** 2
        p /= p.sum()
        y = next((y_ for y_ in range(2, 98) if lpf(y_) == y_ and p[P <= y_].sum() >= 0.9), None)
        if y is None:
            print("(P2)   no prime y <= 97 carries 90% of the mass")
            ok = False
            continue
        share = np.mean(P <= y)
        main_ = np.argsort(-p)[:int(1 / (p ** 2).sum())]
        ph0 = np.angle(b[main_])
        spread = np.abs(np.angle(np.exp(1j * (ph0 - ph0[0])))).max() / np.pi
        print(f"(P2)   y = {y}: mass on y-smooth r = {p[P <= y].sum():.3f}, share of n = {share:.4f}; phase spread "
              f"on the main support ({len(main_)} points) = {spread:.1e} pi")
        print("       heaviest points: r = " + ", ".join(str(int(x)) for x in r[np.argsort(-p)[:8]]))
        ok &= share <= 0.07 and spread <= 1e-6
        lab, ph, sgn, indd = labels(S, K, d, dl)
        parity = np.all(np.where(K % 2 == 0, 1, -1) == sgn[lab])
        cnt = np.bincount(lab, minlength=ph)
        sh = lab_share(S, K, lab, ph)
        Kr = rng.choice(np.arange(1, S.L), S.R, replace=False)
        labr = labels(S, Kr, d, dl)[0]
        shr = lab_share(S, Kr, labr, ph)
        shm = lab_share(S, K, rng.permutation(lab), ph)
        print(f"(P3)   parity agrees on all of W: {parity}; class sizes {cnt.tolist()} (|W|/phi(d) = {S.R / ph:.0f}); "
              f"labelled share {sh:.6f}; random W {shr:.3f}; permuted labels {shm:.3f}")
        ok &= bool(parity) and cnt.min() >= 0.9 * S.R / ph and cnt.max() <= 1.1 * S.R / ph
        ok &= sh >= 0.999 and shr <= 0.6
        caught &= shm < 0.999
        ps = [p_ for p_ in range(int(S.M) + 1, y + 1) if lpf(p_) == p_ and d % p_]
        al = [align(S, K, lab, ph, indd, d, p_, dl) for p_ in ps]
        alr = [align(S, Kr, labr, ph, indd, d, p_, dl) for p_ in ps]
        print("(P4)   unseen primes, mean Re chi(p) psi_lambda(p) on W (random W): "
              + ", ".join(f"{p_}: {a:+.2f} ({ar:+.2f})" for p_, a, ar in zip(ps, al, alr)))
        ok &= len(ps) > 0 and min(al) >= 0.12 and max(np.abs(alr)) <= 0.08
        arr = np.zeros(S.L, complex)
        arr[S.idx] = np.sqrt(S.w) * (P <= y)
        vx, Kx = S.top(np.fft.fft(arr))
        cx = conc(S, Kx, vx)
        print(f"(P5)   explicit set ({int((P <= y).sum())} points): c = {cx:.4f} against c(W) = {c:.4f} "
              f"(ratio {cx / c:.3f}); overlap {len(np.intersect1d(Kx, K)) / S.R:.2f}")
        ok &= cx >= 0.95 * c
        k = sum(1 for p_ in range(2, y + 1) if lpf(p_) == p_ and d % p_)
        er = S.energy(K) / S.R ** 3
        gam = np.log(er) / np.log(c)
        print(f"(P6)   k = {k}: E(W)/|W|^3 = {er:.4f}, per prime {er ** (1 / k):.3f}; c = {c:.4f}, per prime "
              f"{c ** (1 / k):.3f}; gamma = {gam:.3f}")
        ok &= 0.70 <= er ** (1 / k) <= 0.77 and gam < 3
    print(f"gates {'pass' if ok else 'FAIL'}; "
          f"mutation (permuted labels in (P3)) {'caught' if caught else 'NOT CAUGHT'}")
    return 0 if ok and caught else 1


if __name__ == "__main__":
    raise SystemExit(main())
