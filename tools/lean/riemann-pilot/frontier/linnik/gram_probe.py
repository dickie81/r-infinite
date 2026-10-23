"""A large-q probe of the Gram matrix at the critical case (README round 531; SEVEN-THIRDS.md section 11).

Exponent coordinates: L = q - 1, g a primitive root, chi_k(g^j) = e(kj/L).  Weight w(n) = sin^2(pi(n - N)/N) on
[N, 2N] (dyadic, as Chen-Gupta-Li's smoothing is), f[ind n] = w(n), and Kt(d) = sum_n w(n) e(d ind(n)/L) is the
Gram entry of the difference chi_d.  For v supported on a set W of exponents, G v is fft(f * L ifft(v)) restricted
to W; its diagonal is diag = sum w, about N/2, and E = G - diag I.  With one point per character at t = 0, tr E^3
is the S_3 of section 6.  The critical case: |W| = R = q^{2/3}, N = q^{7/9}, M = q/N.  The dual sum of section 6 has
|F(chi_d)| = |Kt(d)| sqrt(q)/N for d != 0; delta(d) = 1 - log|F|/log M, so |F| = M^{1 - delta}.  The additive
energy of W in Z/L is E(W) = #{k1 + k2 = k3 + k4}; a random W has E(W) about R^4/L at these sizes.

  (G1) Alternating projections from the bump (v = fft(f); then v <- fft(f * L ifft(v)), W <- the R largest |v| with
       k = 0 excluded, v <- v 1_W), 40 steps, at q = 10007, 100003 and 1000003.  The concentration
       c = (v^* G v/|v|^2)/L is at most 1, and about 1 in the critical case.  At each q, 0.25 < c < 0.7 and
       c > 5 diag/L.
  (G2) With the weight sin^2 on [N, 2N] no character has |F| > M^{0.7}: min delta > 0.3 at the three q, so the major
       part of SEVEN-THIRDS.md section 10 (delta < 3/32) is empty there.  Controls: the same profile placed
       symmetrically about 0 (at n and q - n for 1 <= n <= N) gives min delta < 0.1, and the sharp cutoff (w = 1 on
       [N, 2N], round 530's P4) gives min delta < 0.2, at the three q.
  (G3) The off-diagonal part of v^* G v for the (G1) sets, split by the delta of the difference
       (v^* G v = sum_d Kt(d) A(d), A the autocorrelation of v): at least 0.85 of it lies on delta < 3/4, and between
       0.2 and 0.7 of it on delta < 1/2.
  (G4) The (G1) sets have E(W) between R^{8/3} and 4 R^{8/3}; at the critical case the energy term
       qN R^{1/2} E(W)^{1/2} of Chen-Gupta-Li's (2.3) is q^3 exactly when E(W) = R^{8/3}.  Their tr E^3 is at most half
       of that energy term.  tr E^3 is computed from the eigenvalues of E at q = 10007 and 100003, where also
       lambda(E)^3 <= tr E^3 + diag tr E^2 (every eigenvalue of E is at least -diag), and by 24 Rademacher probes at
       q = 1000003.
  (G5) The same search with W confined to a random pool of 2R exponents: E(W) at most 1.2 R^4/L, and tr E^3 at most
       twice its mean over random W of size R, p_3 (L - 3)(L^2 sum w^3 - 3 diag L sum w^2 + 2 diag^3) with
       p_3 = R(R - 1)(R - 2)/((L - 1)(L - 2)(L - 3)), which is (5/16)R^3 N up to lower order.
  (G6) The top singular vector of each (G1) set, b_n = sqrt(w(n)) V(ind n) on [N, 2N] with V = L ifft(v), is sparse:
       its participation ratio (sum |b|^2)^2/sum |b|^4 lies between L/R = q^{1/3} and 3L/R, against N = q^{7/9}
       points.  As a 1-bounded polynomial it is far from a large-values set: its transform D = G v has
       |D(chi)| < N^{0.6} max|b_n| for every chi != 1.
Mutation: the weight placed symmetrically about 0, for which (G2) must fail.

Scope.  A numerical probe at three values of q, with one smooth weight shape and one search method.  (G2)'s
controls show that the weight's shape and position matter.  Alternating projections find local maxima, so nothing
here bounds the largest concentration, or the largest tr E^3, over all W of size R.  A random pool makes W
random-like, so (G5) does not test structured sets of low energy.
"""
import numpy as np

from line_sums import dlog_table

QS = (10007, 100003, 1000003)


class Gram:
    def __init__(self, q, kind="sin2", dl=None):
        self.q, self.L = q, q - 1
        self.N, self.R = round(q ** (7 / 9)), round(q ** (2 / 3))
        self.M = q / self.N
        dl = dlog_table(q) if dl is None else dl
        if kind == "symmetric":
            m = np.arange(1, self.N + 1)
            wm = np.cos(np.pi * m / (2 * self.N)) ** 2
            n, w = np.concatenate([m, q - m]), np.concatenate([wm, wm])
        else:
            n = np.arange(self.N, 2 * self.N + 1)
            w = np.ones(len(n)) if kind == "sharp" else np.sin(np.pi * (n - self.N) / self.N) ** 2
        self.w = w
        self.f = np.zeros(self.L)
        np.add.at(self.f, dl[n], w)
        self.idx = dl[n]
        self.Kt = np.conj(np.fft.fft(self.f))
        self.diag = self.Kt[0].real
        F = np.abs(self.Kt) * np.sqrt(q) / self.N
        F[0] = 1.0
        with np.errstate(divide="ignore"):
            self.delta = 1 - np.log(F) / np.log(self.M)
        self.delta[0] = np.inf

    def G(self, v):
        return np.fft.fft(self.f * (self.L * np.fft.ifft(v)))

    def top(self, u, pool=None):
        a = np.abs(u) if pool is None else np.where(pool, np.abs(u), -1.0)
        a[0] = -1
        K = np.argpartition(-a, self.R)[:self.R]
        out = np.zeros(self.L, complex)
        out[K] = u[K]
        return out / np.linalg.norm(out), K

    def alternate(self, steps=40, pool=None):
        v, K = self.top(np.fft.fft(self.f), pool)
        for _ in range(steps):
            v, K = self.top(self.G(v), pool)
        return v, K

    def rayleigh(self, v):
        return np.vdot(v, self.G(v)).real / np.vdot(v, v).real

    def split(self, v):
        A = np.fft.ifft(np.abs(np.fft.fft(v)) ** 2)
        c = (self.Kt * A).real
        c[0] = 0
        return {cut: c[self.delta < cut].sum() / c.sum() for cut in (1 / 2, 3 / 4)}

    def energy(self, K):
        ind = np.zeros(self.L)
        ind[K] = 1
        return (np.abs(np.fft.fft(ind)) ** 4).sum() / self.L

    def tr3(self, K, probes=24, seed=5):
        """tr E^3 and, from the eigenvalues when R is small, lambda(E) and tr E^2."""
        if self.R < 3000:
            Ks = np.sort(K)
            E = self.Kt[(Ks[:, None] - Ks[None, :]) % self.L]
            np.fill_diagonal(E, 0)
            mu = np.linalg.eigvalsh(E)
            return (mu ** 3).sum(), mu.max(), (mu ** 2).sum()
        m = np.zeros(self.L, bool)
        m[K] = True
        rng, est = np.random.default_rng(seed), []
        for _ in range(probes):
            z = np.zeros(self.L)
            z[K] = rng.choice([-1.0, 1.0], self.R)
            y = z
            for _ in range(3):
                y = np.where(m, self.G(y), 0) - self.diag * y
            est.append(np.vdot(z, y).real)
        self.tr3_stderr = float(np.std(est) / np.sqrt(probes))
        return float(np.mean(est)), None, None

    def random_mean_tr3(self):
        L, R, d = self.L, self.R, self.diag
        p3 = R * (R - 1) * (R - 2) / ((L - 1) * (L - 2) * (L - 3))
        return p3 * (L - 3) * (L ** 2 * (self.w ** 3).sum() - 3 * d * L * (self.w ** 2).sum() + 2 * d ** 3)


def g2(kind, dls):
    out = [Gram(q, kind, dls[q]).delta.min() for q in QS]
    print(f"(G2) weight {kind:9s}: min delta = " + ", ".join(f"{d:.3f}" for d in out) + f" at q = {QS}")
    return out


def main():
    dls = {q: dlog_table(q) for q in QS}
    ok = True
    rng = np.random.default_rng(21)
    for q in QS:
        S = Gram(q, dl=dls[q])
        R4L = S.R ** 4 / S.L
        v, K = S.alternate()
        lam = S.rayleigh(v)
        c = lam / S.L
        sh = S.split(v)
        EW = S.energy(K)
        eterm = q * S.N * np.sqrt(S.R * EW)
        t3, lmax, t2 = S.tr3(K)
        print(f"(G1) q={q} N={S.N} R={S.R} M={S.M:.2f}: c = {c:.4f} (diag/L = {S.diag / S.L:.4f}), "
              f"lambda/diag = {lam / S.diag:.2f}")
        print(f"(G3)   off-diagonal share on delta < 1/2: {sh[1 / 2]:.3f}, on delta < 3/4: {sh[3 / 4]:.3f}")
        err = "" if lmax is not None else f" +- {S.tr3_stderr / q ** 3:.4f} (probes)"
        print(f"(G4)   E(W)/R^(8/3) = {EW / S.R ** (8 / 3):.2f}, E(W)/(R^4/L) = {EW / R4L:.2f}; "
              f"tr E^3/q^3 = {t3 / q ** 3:.4f}{err}; energy term/q^3 = {eterm / q ** 3:.3f}")
        ok &= 0.25 < c < 0.7 and c > 5 * S.diag / S.L and sh[3 / 4] >= 0.85 and 0.2 <= sh[1 / 2] <= 0.7
        b = np.sqrt(S.w) * (S.L * np.fft.ifft(v))[S.idx]
        a = np.abs(b) ** 2
        pr = a.sum() ** 2 / (a ** 2).sum()
        D = np.abs(S.G(v))
        D[0] = 0
        lv = np.log(D.max() / np.abs(b).max()) / np.log(S.N)
        print(f"(G6)   participation ratio of b = {pr:.0f}, L/R = {S.L / S.R:.0f}, N = {S.N}; "
              f"max |D| = N^{lv:.3f} max|b_n|")
        ok &= S.R ** (8 / 3) <= EW <= 4 * S.R ** (8 / 3) and t3 <= eterm / 2
        ok &= S.L / S.R <= pr <= 3 * S.L / S.R and lv < 0.6
        if lmax is not None:
            ok &= lmax ** 3 <= t3 + S.diag * t2
        pool = np.zeros(S.L, bool)
        pool[rng.choice(np.arange(1, S.L), 2 * S.R, replace=False)] = True
        vp, Kp = S.alternate(pool=pool)
        EWp = S.energy(Kp)
        t3p = S.tr3(Kp)[0]
        mean = S.random_mean_tr3()
        print(f"(G5)   pool of 2R: c = {S.rayleigh(vp) / S.L:.4f}, E(W)/(R^4/L) = {EWp / R4L:.2f}, "
              f"tr E^3/q^3 = {t3p / q ** 3:.4f}, random mean/q^3 = {mean / q ** 3:.4f}")
        ok &= EWp <= 1.2 * R4L and t3p <= 2 * mean
    ok &= min(g2("sin2", dls)) > 0.3 and max(g2("symmetric", dls)) < 0.1 and max(g2("sharp", dls)) < 0.2
    caught = not (min(g2("symmetric", dls)) > 0.3)
    print(f"gates {'pass' if ok else 'FAIL'}; "
          f"mutation (symmetric weight in (G2)) {'caught' if caught else 'NOT CAUGHT'}")
    return 0 if ok and caught else 1


if __name__ == "__main__":
    raise SystemExit(main())
