"""Energy-constrained concentration at the critical case (README round 532; SEVEN-THIRDS.md section 12).

Uses gram_probe.Gram: weight sin^2 on [N, 2N], |W| = R = q^{2/3}, N = q^{7/9}, L = q - 1.  kappa = E(W)/(R^4/L) is at
least 1 for every W, by Cauchy-Schwarz: E(W) = sum_s r(s)^2 >= (sum_s r(s))^2/L = R^4/L, with r(s) the number of
(k1, k2) in W^2 with k1 + k2 = s.  The swap dynamic starts at the (G1) set of gram_probe.py and runs T steps with an
energy penalty mu_t = mu_max t/T.  At each step the score is |u|^2/max|u|^2 - mu_t marg/max(marg), with u = G v and
marg(k) the cross-correlation of 1_W with r (the increase in E(W) from adding k, up to O(1)).  At most 3% of W is
exchanged per step: the lowest-scoring members against the highest-scoring non-members, while the latter score
higher.  For each threshold on kappa the set with the largest concentration c (as in gram_probe.py) is kept.

  (F1) At q = 10007, 100003 and 1000003 the dynamic reaches kappa <= 1.25.
  (F2) The best c with kappa <= 1.25 falls with q and is below 0.25 at q = 1000003.  The best c with kappa <= 2 also
       falls with q.
  (F3) For the best sets with kappa <= 1.25 and with kappa <= 2: tr E^3 exceeds the mean over random W of size R
       (Gram.random_mean_tr3), and is at most half the energy term qN R^{1/2} E(W)^{1/2} of Chen-Gupta-Li's (2.3).
       The ratio of tr E^3 to that energy term falls with q, for both thresholds.  tr E^3 comes from the eigenvalues of
       E at q = 10007 and 100003, and from 24 Rademacher probes at q = 1000003.
Mutation: mu_max = 0 (no energy penalty), at q = 10007, for which (F1) must fail.

Scope.  A numerical probe at three values of q with one weight shape and one search method.  The dynamic finds
local maxima, so nothing here bounds the largest concentration at a given energy over all W of size R.
"""
import numpy as np

from gram_probe import QS, Gram
from line_sums import dlog_table

THR = (1.25, 2.0)


def frontier(S, steps=200, mu_max=4.0, swap=0.03):
    v, K = S.alternate()
    inW = np.zeros(S.L, bool)
    inW[K] = True
    best = {t: (0.0, None, None) for t in THR}
    nsw = max(1, int(swap * S.R))
    min_kappa = np.inf
    for t in range(steps):
        u = S.G(v)
        c = np.vdot(v, u).real / S.L
        ind = inW.astype(float)
        A = np.fft.fft(ind)
        E = (np.abs(A) ** 4).sum() / S.L
        kap = E / (S.R ** 4 / S.L)
        min_kappa = min(min_kappa, kap)
        for th in THR:
            if kap <= th and c > best[th][0]:
                best[th] = (c, K.copy(), kap)
        r = np.fft.ifft(A * A).real
        marg = np.fft.ifft(np.fft.fft(r) * np.conj(A)).real
        a = np.abs(u) ** 2
        a[0] = 0
        marg[0] = 0
        sc = a / a.max() - (mu_max * t / steps) * marg / marg.max()
        sc[0] = -np.inf
        weak = K[np.argsort(sc[K])[:nsw]]
        out = np.where(~inW)[0]
        strong = out[np.argsort(-sc[out])[:nsw]]
        k = 0
        while k < nsw and sc[strong[k]] > sc[weak[k]]:
            k += 1
        if k:
            inW[weak[:k]] = False
            inW[strong[:k]] = True
            K = np.where(inW)[0]
        v = np.where(inW, u, 0)
        v /= np.linalg.norm(v)
    return best, min_kappa


def main():
    ok, cs, ratios = True, {t: [] for t in THR}, {t: [] for t in THR}
    for q in QS:
        S = Gram(q, dl=dlog_table(q))
        best, kmin = frontier(S)
        mean = S.random_mean_tr3()
        print(f"(F1) q={q} R={S.R} N={S.N}: smallest kappa reached = {kmin:.3f}")
        ok &= kmin <= 1.25
        for th in THR:
            c, K, kap = best[th]
            if K is None:
                ok = False
                print(f"(F2)   kappa <= {th}: not reached")
                continue
            t3 = S.tr3(K)[0]
            eterm = q * S.N * np.sqrt(S.R * kap * S.R ** 4 / S.L)
            cs[th].append(c)
            ratios[th].append(t3 / eterm)
            print(f"(F2)   kappa <= {th}: best c = {c:.4f} at kappa = {kap:.3f}")
            print(f"(F3)     tr E^3/q^3 = {t3 / q ** 3:.4f}, random mean/q^3 = {mean / q ** 3:.4f}, "
                  f"energy term/q^3 = {eterm / q ** 3:.3f}, ratio = {t3 / eterm:.3f}")
            ok &= mean < t3 <= eterm / 2
    for th in THR:
        ok &= len(cs[th]) == 3 and cs[th][0] > cs[th][1] > cs[th][2]
        ok &= len(ratios[th]) == 3 and ratios[th][0] > ratios[th][1] > ratios[th][2]
    ok &= len(cs[1.25]) == 3 and cs[1.25][2] < 0.25
    S = Gram(QS[0], dl=dlog_table(QS[0]))
    kmin0 = frontier(S, mu_max=0.0)[1]
    caught = not (kmin0 <= 1.25)
    print(f"mutation (mu_max = 0) at q={QS[0]}: smallest kappa = {kmin0:.3f}")
    print(f"gates {'pass' if ok else 'FAIL'}; mutation {'caught' if caught else 'NOT CAUGHT'}")
    return 0 if ok and caught else 1


if __name__ == "__main__":
    raise SystemExit(main())
