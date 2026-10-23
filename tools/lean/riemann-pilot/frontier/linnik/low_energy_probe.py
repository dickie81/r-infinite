"""Large-values sets at the critical point have near-minimal energy (README round 535; SEVEN-THIRDS.md section 15).

  (L1) Exact exponent arithmetic.  At sigma = 5/7, N = q^{7/9}, |W| = q^{2/3} and T = q^{o(1)}, the three terms of
       Chen-Gupta-Li's Proposition 10.2, |W|N^{4-4sigma}, |W|^{21/8}(qT)^{1/4}N^{1-2sigma} and |W|^3 N^{1-2sigma}, are
       q^{14/9}, q^{5/3} and q^{5/3}, and the minimum |W|^4/q of E(W) is q^{5/3}.  Their energy term
       qN|W|^{1/2}E(W)^{1/2} at E(W) = q^{5/3} is q^{3-1/18}, and their first term (qT)^2|W|^{3/2} is q^3.
  (L2) The concentrated sets of gram_probe.py (G1) have kappa = E(W)/(|W|^4/L) above 4 at q = 10007, 100003 and
       1000003, rising with q.  (Proposition 10.2 allows kappa up to q^eps at the critical point.)
  (L3) The small lines, exactly.  Let R0 = R off b = 1 and R0(1) = 0, so the points where an argument is 1 are left
       out.  For the box of lines m = (m1, m2, m3), |m1|, |m3| <= M, 1 <= m2 <= M, with B_m(x) = (m1 x + m3)/m2, put
       X(x) = sum_m R0(B_m(x)/x) conj R0(B_m(x)) and LS = sum_x R0(x) X(x), the sum of the line sums of section 6 over
       the box.  By Cauchy-Schwarz |LS| <= ||R0|| ||X||, and ||X||^2 = sum_{m,m'} C(m, m') with the four-point
       correlations C(m, m') = sum_x R0(B_m/x) conj R0(B_m) conj R0(B_m'/x) R0(B_m').  Put theta = ||X||^2/(|box|^2 q
       |W|^2), which is 1 at full coherence, and cs = |LS|/(||R0|| ||X||).  At q = 10007 and 100003, for the (G1) set,
       the best set of energy_frontier.py with kappa <= 1.25 and a random set of the same size:
       - cs >= 0.5 for each set: Cauchy-Schwarz loses at most a factor 2 here;
       - theta >= 0.1 for the (G1) set, theta <= 0.03 for the kappa <= 1.25 set, and theta <= 10/|box| for the random
         set;
       - theta of the kappa <= 1.25 set falls by at least a factor 2 from q = 10007 to 100003.
Mutation: the (G1) set in place of the kappa <= 1.25 set in (L3), for which the bound theta <= 0.03 must fail.

Scope.  (L1) is arithmetic on the cited bound.  (L2) and (L3) are measurements of the sets two search methods find,
at the listed q; they bound nothing over all sets of size q^{2/3}.
"""
from fractions import Fraction as Fr

import numpy as np

from energy_frontier import frontier
from gram_probe import QS, Gram
from line_sums import dlog_table


def l1():
    s, n, w = Fr(5, 7), Fr(7, 9), Fr(2, 3)
    terms = (w + n * (4 - 4 * s), w * Fr(21, 8) + Fr(1, 4) + n * (1 - 2 * s), 3 * w + n * (1 - 2 * s))
    emin = 4 * w - 1
    eterm = 1 + n + w / 2 + emin / 2
    first = 2 + Fr(3, 2) * w
    print(f"(L1) Proposition 10.2 terms: q^{terms[0]}, q^{terms[1]}, q^{terms[2]}; |W|^4/q = q^{emin}; "
          f"energy term q^{eterm}; first term q^{first}")
    return terms == (Fr(14, 9), Fr(5, 3), Fr(5, 3)) and emin == Fr(5, 3) and eterm == 3 - Fr(1, 18) and first == 3


class Lines:
    def __init__(self, S, dl):
        q, self.S, self.dl = S.q, S, dl
        g = int(np.argmax(dl == 1))
        pw = np.zeros(q - 1, dtype=np.int64)
        acc = 1
        for j in range(q - 1):
            pw[j] = acc
            acc = acc * g % q
        self.inv = np.zeros(q, dtype=np.int64)
        self.inv[1:] = pw[(-dl[1:]) % (q - 1)]
        M = int(S.M)
        self.box = [(a, b, c) for a in range(-M, M + 1) for b in range(1, M + 1) for c in range(-M, M + 1)]
        self.x = np.arange(1, q, dtype=np.int64)

    def stats(self, K):
        q, x, inv, dl = self.S.q, self.x, self.inv, self.dl
        ind = np.zeros(self.S.L)
        ind[K] = 1
        Rexp = np.fft.ifft(ind) * self.S.L
        R0 = np.zeros(q, complex)
        R0[1:] = Rexp[dl[1:]]
        R0[1] = 0
        xinv, X = inv[x], np.zeros(q - 1, complex)
        for m1, m2, m3 in self.box:
            B = (m1 * x + m3) % q * inv[m2] % q
            X += R0[B * xinv % q] * np.conj(R0[B])
        Rx = R0[x]
        nX2 = (np.abs(X) ** 2).sum()
        theta = nX2 / (len(self.box) ** 2 * q * self.S.R ** 2)
        return theta, abs((Rx * X).sum()) / np.sqrt((np.abs(Rx) ** 2).sum() * nX2)


def main():
    ok = l1()
    caught = True
    rng = np.random.default_rng(37)
    kap_g1, theta_fr = [], []
    for q in QS:
        dl = dlog_table(q)
        S = Gram(q, dl=dl)
        v, K = S.alternate()
        kap = S.energy(K) / (S.R ** 4 / S.L)
        kap_g1.append(kap)
        print(f"(L2) q={q}: kappa of the (G1) set = {kap:.2f}")
        if q == QS[-1]:
            continue
        best, _ = frontier(S, steps=150)
        sets = {"G1": K, "kappa<=1.25": best[1.25][1],
                "random": rng.choice(np.arange(1, S.L), S.R, replace=False)}
        lines = Lines(S, dl)
        th = {}
        for name, KK in sets.items():
            theta, csr = lines.stats(KK)
            th[name] = theta
            print(f"(L3)   {name:12s}: theta = {theta:.4f}, cs = {csr:.3f} (|box| = {len(lines.box)})")
            ok &= csr >= 0.5
        ok &= th["G1"] >= 0.1 and th["kappa<=1.25"] <= 0.03 and th["random"] <= 10 / len(lines.box)
        caught &= not (th["G1"] <= 0.03)
        theta_fr.append(th["kappa<=1.25"])
    ok &= min(kap_g1) > 4 and kap_g1[0] < kap_g1[1] < kap_g1[2]
    ok &= len(theta_fr) == 2 and theta_fr[1] <= theta_fr[0] / 2
    print(f"gates {'pass' if ok else 'FAIL'}; "
          f"mutation (the (G1) set in place of the kappa <= 1.25 set) {'caught' if caught else 'NOT CAUGHT'}")
    return 0 if ok and caught else 1


if __name__ == "__main__":
    raise SystemExit(main())
