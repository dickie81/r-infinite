"""The structure of the concentrated sets of gram_probe.py (README round 533; SEVEN-THIRDS.md section 13).

For a set W of exponents, R(b) = sum_{k in W} e(k ind(b)/L) = sum_{chi in W} chi(b) on F_q^*.  The height of b is the
smallest max(|m|, |m'|) over m = b m' (mod q), m' != 0, found by Gauss reduction of the lattice {(m, m') : m = b m'
mod q}; a random b has height near sqrt(q).  The singular vector of a (G1) set is b_n = sqrt(w(n)) V(ind n) on
[N, 2N], and its main support S is its PR largest points by |b_n|, PR the participation ratio of gram_probe.py (G6).

  (S1) For the (G1) sets at q = 10007, 100003 and 1000003, the 24 values of b != 1 with the largest |R(b)| all have
       |R(b)| >= 0.4|W|, |arg R(b)| <= 0.01 pi and height at most 4M.  For 300 random b the median height is at
       least 0.4 sqrt(q).
  (S2) Write each of those 24 b as m/m' with the representation found.  If b is negative or lies outside [1/2, 2],
       then b n = n' with n, n' in [N, 2N] needs m n - m' n' = kq with k != 0 (a wrap modulo q).  At least 20 of the
       24 are of that kind.
  (S3) The main support S is closed under each of the 12 b with the largest |R(b)| to at least 25% (the fraction of
       n in S with b n mod q in S); for 200 random b the median closure is at most 0.02.
  (S4) The interval itself carries no such structure: for the same 24 b, the median of the fraction of n in [N, 2N]
       with b n mod q in [N, 2N] is within a factor 1.5 of the median over 300 random b.
  (S5) Control: for a random W of the same size the largest |R(b)|, b != 1, is below 0.2|W|.
Mutation: a random W in place of the (G1) set in (S1), which must fail.

Scope.  A numerical probe at three values of q, for the sets one search method finds.  It describes those sets; it
proves nothing about other sets of size q^{2/3}.
"""
import numpy as np

from gram_probe import QS, Gram
from line_sums import dlog_table, prim_root


def rep(b, q):
    """A shortest nonzero (m, m') with m = b m' (mod q), in the max norm up to the reduced basis."""
    u, v = (q, 0), (b % q, 1)
    n2 = lambda x: x[0] * x[0] + x[1] * x[1]
    if n2(u) < n2(v):
        u, v = v, u
    while n2(v):
        k = round((u[0] * v[0] + u[1] * v[1]) / n2(v))
        u = (u[0] - k * v[0], u[1] - k * v[1])
        if n2(u) >= n2(v):
            break
        u, v = v, u
    cands = [c for c in (v, u, (u[0] + v[0], u[1] + v[1]), (u[0] - v[0], u[1] - v[1])) if c[1] != 0]
    return min(cands, key=lambda c: max(abs(c[0]), abs(c[1])))


def height(b, q):
    m, mp = rep(b, q)
    return max(abs(m), abs(mp))


def R_of(S, K):
    ind = np.zeros(S.L)
    ind[K] = 1
    return np.fft.ifft(ind) * S.L


def s1(S, K, g, top=24):
    R = R_of(S, K)
    a = np.abs(R)
    a[0] = 0
    idx = np.argsort(-a)[:top]
    bs = [pow(g, int(j), S.q) for j in idx]
    hs = [height(b, S.q) for b in bs]
    ok = a[idx].min() >= 0.4 * S.R and max(abs(np.angle(R[idx]))) <= 0.01 * np.pi and max(hs) <= 4 * S.M
    return ok, bs, a[idx], hs


def main():
    ok = True
    rng = np.random.default_rng(23)
    for q in QS:
        S = Gram(q, dl=dlog_table(q))
        g = prim_root(q)
        v, K = S.alternate()
        good, bs, vals, hs = s1(S, K, g)
        rh = [height(int(b), q) for b in rng.integers(2, q - 1, 300)]
        print(f"(S1) q={q} M={S.M:.1f}: top-24 |R(b)|/|W| in [{vals.min() / S.R:.3f}, {vals.max() / S.R:.3f}], "
              f"heights <= {max(hs)} (4M = {4 * S.M:.0f}); random-b median height {np.median(rh):.0f} "
              f"(sqrt q = {q ** .5:.0f})")
        print("       " + ", ".join(f"{m}/{mp}" for m, mp in (rep(b, q) for b in bs[:12:2])))
        ok &= good and np.median(rh) >= 0.4 * q ** .5
        reps = [rep(b, q) for b in bs]
        wrap = sum(m * mp < 0 or not (0.5 <= m / mp <= 2) for m, mp in reps)
        print(f"(S2)   {wrap} of the 24 are negative or outside [1/2, 2]")
        ok &= wrap >= 20
        b = np.sqrt(S.w) * (S.L * np.fft.ifft(v))[S.idx]
        a2 = np.abs(b) ** 2
        pr = int(a2.sum() ** 2 / (a2 ** 2).sum())
        n = np.arange(S.N, 2 * S.N + 1)
        supp = n[np.argsort(-np.abs(b))[:pr]]
        st = set(int(x) for x in supp)
        clos = lambda beta: np.mean([((beta * int(x)) % q) in st for x in supp])
        tc = [clos(beta) for beta in bs[:12]]
        rc = [clos(int(beta)) for beta in rng.integers(2, q - 1, 200)]
        print(f"(S3)   closure of the main support ({pr} points) under the top 12 b: min {min(tc):.2f}; "
              f"random b median {np.median(rc):.3f}")
        ok &= min(tc) >= 0.25 and np.median(rc) <= 0.02
        ov = lambda beta: np.mean(((beta * n) % q >= S.N) & ((beta * n) % q <= 2 * S.N))
        to = np.median([ov(beta) for beta in bs])
        ro = np.median([ov(int(beta)) for beta in rng.integers(2, q - 1, 300)])
        print(f"(S4)   overlap of b[N, 2N] with [N, 2N]: top-24 median {to:.3f}, random median {ro:.3f}")
        ok &= ro / 1.5 <= to <= 1.5 * ro
        Kr = rng.choice(np.arange(1, S.L), S.R, replace=False)
        ar = np.abs(R_of(S, Kr))
        ar[0] = 0
        print(f"(S5)   random W: largest |R(b)|/|W| = {ar.max() / S.R:.3f}")
        ok &= ar.max() < 0.2 * S.R
    S = Gram(QS[0], dl=dlog_table(QS[0]))
    caught = not s1(S, np.random.default_rng(3).choice(np.arange(1, S.L), S.R, replace=False), prim_root(QS[0]))[0]
    print(f"gates {'pass' if ok else 'FAIL'}; mutation (random W in (S1)) {'caught' if caught else 'NOT CAUGHT'}")
    return 0 if ok and caught else 1


if __name__ == "__main__":
    raise SystemExit(main())
