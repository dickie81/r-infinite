"""The Gauss-sum transfer and the excess-energy lemma (README round 555; SEVEN-THIRDS.md section 23).

Notation of gram_probe.py: q prime, L = q - 1, g a primitive root, chi_k(g^j) = e(kj/L), weight w = sin^2 on [N, 2N],
N = q^{7/9}, |W| = R = q^{2/3}.  E_W = [K(chi chi'^bar)] off the diagonal, K(psi) = sum_n w(n) psi(n).  tau(psi) is
the Gauss sum sum_y psi(y) e(y/q), T_W = [tau(chi chi'^bar)] (diagonal tau(chi_0) = -1) and T'_W = T_W + I.

The transfer.  Write w(y) = sum_xi c_xi e(xi y/q) on F_q.  For psi != chi_0, K(psi) = tau(psi) sum_{xi != 0} c_xi
psi^bar(xi), so E_W = sum_{xi != 0} c_xi D_xi^* T'_W D_xi with D_xi = diag(chi(xi)), and
||E_W|| <= C ||T'_W||, C = sum_{xi != 0} |c_xi|.  T_W/L is the compression of multiplication by e(y/q) to span(W),
so ||T'_W|| <= L + 1 for every W, and T'_W does not depend on N or w.

The excess-energy lemma.  Let b be supported on the integers [N0, 2N0), with (2N0)^2 < q, and let W be a set of
characters with |S_b(chi)| >= V0 on W, S_b(chi) = sum_n b_n chi(n).  Put R(x) = sum_{chi in W} chi(x) and
kappa = L E(W)/|W|^4 = 1 + sum_{x != 1} |R(x)|^4/|W|^4.  Then
    |W| (V0^2 - ||b||^2) <= sum_{n != n'} b_n conj(b_n') R(n/n') <= |W| (kappa - 1)^{1/4} ||rho||_{4/3},
with rho(x) = sum_{n != n', n/n' = x} |b_n b_n'|, by Hoelder with exponents 4 and 4/3.  Since no ratio wraps,
||rho||_{4/3}^4 <= ||rho||_1^2 ||rho||_2^2 <= ||b||_1^4 ||b||_inf^4 E_Z, with E_Z = #{n1 n2 = n3 n4} in the block.
By Cauchy-Schwarz instead, sum_{n != n'} |R(n/n')|^2 >= |W|^2 (V0^2 - ||b||^2)^2/||b||^4.

  (T1) The transfer at q = 10007, 100003 and 1000003, for five sets of size R: the best sets of energy_frontier.py
       with kappa <= 1.25 and kappa <= 2, the concentrated set of gram_probe.py (G1), and two random sets.
       |tau| = sqrt(q) for chi != chi_0, D T_W is Hermitian (D = diag((-1)^k)), and ||E_W|| <= C ||T'_W|| (relative
       tolerance 1e-9).  Norms are top eigenvalues by Lanczos on FFT matrix-vector products; at q = 10007 they agree
       with dense eigenvalues to 1e-8.  Measured: ||E_W||/(C ||T'_W||) >= 0.5 for the frontier and (G1) sets and
       <= 0.35 for the random sets, at every q.
  (T2) Subgroup annihilators.  For W = H^perp, the characters trivial on a subgroup H, span(W) is the functions
       constant on the cosets of H, so ||T_W||/L = max_{c != 0} |sum_{h in H} e(ch/q)|/|H|, exactly.  Checked to 1e-9
       at (q, |H|) = (10009, 24) and (100003, 42), where |W| = 417 and 2381, together with (T1)'s inequality.
  (T3) Random calibration.  For random W of size R, ||T'_W||/L lies within 5% of 2 sqrt(alpha(1 - alpha)),
       alpha = R/L, the norm of the compression of a unitary with uniformly distributed spectrum by a free
       projection of trace alpha.  Two random sets at each q of (T1).
  (T4) The lemma, at q = 10007, 100003 and 1000003, with N0 = round(q^{7/18}), b = 1 on [N0, 2N0), and W the R
       characters (k != 0) with the largest |S_b|, V0 the least of these.  Gates: V0^2 > ||b||^2, and
       kappa - 1 >= ((V0^2 - ||b||^2)/||rho||_{4/3})^4 >= (V0^2 - ||b||^2)^4/(N0^4 E_Z), and the Cauchy-Schwarz form.
       Recorded: sigma = log V0/log N0, kappa - 1 against the bound and against the least value
       (L - R)^2/((L - 1) R^2) that any W of size R has.
  (T5) The same sets, measured.  kappa - 1 increases with q and exceeds 5 times the least value at every q, and at
       least half of kappa - 1 comes from the x = s/t with |s|, t <= 10.  These sets sit near sigma = 0.67.  At the
       critical point the ratios n/n' of height at most (V0^2 - N0)/(4 N0), about N0^{3/7}/4, carry at most half of
       sum_{n != n'} R(n/n'), since they number at most 2 H N0 and |R| <= |W|; with Proposition 10.2's
       kappa <= q^{o(1)}, Hoelder over them raises that height to q^{1/3 - o(1)}.  So these measurements are of
       another regime.
Mutations, each of which must fail a gate: (m1) C replaced by max |c_xi| in (T1); (m2) 2 sqrt(alpha(1 - alpha))
replaced by sqrt(alpha(1 - alpha)) in (T3); (m3) (T2)'s maximum over c replaced by the value at c = 1;
(m4) ||rho||_{4/3} replaced by ||rho||_2 in (T4)'s first bound (Hoelder with exponents that are not conjugate);
(m5) ||b||^4 replaced by ||b||^2 in (T4)'s Cauchy-Schwarz form; (m6) (T5)'s small ratios restricted to x = -1.

Scope.  The transfer and the lemma are proved above; the probe checks them and their conventions numerically.  The
sets come from one search method each, at three values of q.  At these q the sets of (T4) sit near sigma = 0.62, far
below the critical point (sigma = 5/7 with |W| = q^{2/3}), where the lemma gives kappa - 1 >= q^{-1/9}/(C log q).
(T3) compares with a free-probability value; it is a calibration, not a theorem about these sets.
"""
import sys

import numpy as np
from scipy.sparse.linalg import LinearOperator, eigsh

from energy_frontier import frontier
from gram_probe import QS, Gram
from line_sums import dlog_table, prim_root

H_CASES = ((10009, 24), (100003, 42))


def gauss_sums(q):
    """tau(chi_k) for every k in Z/L, as L ifft of e(g^j/q)."""
    L, g = q - 1, prim_root(q)
    pw = np.ones(L, dtype=np.int64)
    for j in range(1, L):
        pw[j] = pw[j - 1] * g % q
    return L * np.fft.ifft(np.exp(2j * np.pi * pw / q)), pw


def weight_coeffs(S):
    """C = sum_{xi != 0} |c_xi| and max_{xi != 0} |c_xi| for w(y) = sum_xi c_xi e(xi y/q)."""
    wq = np.zeros(S.q)
    wq[np.arange(S.N, 2 * S.N + 1)] = S.w
    c = np.abs(np.fft.fft(wq) / S.q)[1:]
    return c.sum(), c.max()


def lanczos_norm(matvec, n):
    op = LinearOperator((n, n), matvec=matvec, dtype=complex)
    return abs(eigsh(op, k=1, which="LM", tol=1e-12, maxiter=20000)[0][0])


def norms(S, ftau, K):
    """||E_W|| and ||T'_W|| by Lanczos; E and D T' are Hermitian."""
    L, Ks = S.L, np.sort(K)
    sgn = np.where(Ks % 2 == 0, 1.0, -1.0)
    fKt = np.fft.fft(S.Kt)

    def lift(x):
        z = np.zeros(L, complex)
        z[Ks] = x
        return np.fft.fft(z)

    def mv_E(x):
        x = np.asarray(x).ravel()
        return np.fft.ifft(fKt * lift(x))[Ks] - S.diag * x

    def mv_T(x):
        x = np.asarray(x).ravel()
        return sgn * (np.fft.ifft(ftau * lift(x))[Ks] + x)

    return lanczos_norm(mv_E, len(Ks)), lanczos_norm(mv_T, len(Ks))


def dense_norms(S, tau, K):
    Ks = np.sort(K)
    D = (Ks[:, None] - Ks[None, :]) % S.L
    E = S.Kt[D].copy()
    np.fill_diagonal(E, 0)
    T = tau[D].copy()
    sgn = np.where(Ks % 2 == 0, 1.0, -1.0)
    Th = sgn[:, None] * (T + np.eye(len(Ks)))
    herm = np.abs(Th - Th.conj().T).max() / np.abs(Th).max()
    return np.abs(np.linalg.eigvalsh(E)).max(), np.abs(np.linalg.eigvalsh((Th + Th.conj().T) / 2)).max(), herm


def measure_t1():
    """Norms for (T1) and (T3); each entry is (q, name, ||E||, ||T'||, C, max|c|, L, alpha, dense_ok, tau_ok)."""
    rows = []
    rng = np.random.default_rng(55)
    for q in QS:
        S = Gram(q, dl=dlog_table(q))
        tau, _ = gauss_sums(q)
        ftau = np.fft.fft(tau)
        C, cmax = weight_coeffs(S)
        tau_ok = bool(np.allclose(np.abs(tau[1:]), np.sqrt(q), rtol=1e-9) and abs(tau[0] + 1) < 1e-6)
        best, _ = frontier(S, steps=150)
        _, K1 = S.alternate()
        sets = {"k<=1.25": best[1.25][1], "k<=2": best[2.0][1], "G1": K1,
                "random1": rng.choice(np.arange(1, S.L), S.R, replace=False),
                "random2": rng.choice(np.arange(1, S.L), S.R, replace=False)}
        alpha = S.R / S.L
        print(f"(T1) q={q} N={S.N} R={S.R} C={C:.4f} max|c|={cmax:.4f}; 2 sqrt(alpha(1-alpha)) = "
              f"{2 * np.sqrt(alpha * (1 - alpha)):.4f}; |tau| = sqrt(q): {tau_ok}", flush=True)
        for name, K in sets.items():
            if K is None:
                rows.append((q, name, None, None, C, cmax, S.L, alpha, False, tau_ok))
                print(f"  {name}: not reached", flush=True)
                continue
            nE, nT = norms(S, ftau, K)
            dense_ok = True
            if q == QS[0]:
                dE, dT, herm = dense_norms(S, tau, K)
                dense_ok = bool(abs(dE - nE) <= 1e-8 * dE and abs(dT - nT) <= 1e-8 * dT and herm < 1e-9)
            rows.append((q, name, nE, nT, C, cmax, S.L, alpha, dense_ok, tau_ok))
            print(f"  {name:8s} ||E||/L = {nE / S.L:.4f}  ||T'||/L = {nT / S.L:.4f}  "
                  f"||E||/(C||T'||) = {nE / (C * nT):.4f}  ||T'||/(2 sqrt(alpha(1-alpha)) L) = "
                  f"{nT / S.L / (2 * np.sqrt(alpha * (1 - alpha))):.4f}" + ("  (dense agrees)" if q == QS[0] and
                                                                           dense_ok else ""), flush=True)
    return rows


def gate_t1(rows, mut=None):
    ok = True
    for q, name, nE, nT, C, cmax, L, alpha, dense_ok, tau_ok in rows:
        if nE is None:
            return False
        ok &= tau_ok and dense_ok and nE <= (cmax if mut == "m1" else C) * nT * (1 + 1e-9)
        pred = (1 if mut == "m2" else 2) * np.sqrt(alpha * (1 - alpha))
        if name.startswith("random"):
            ok &= nE / (C * nT) <= 0.35 and abs(nT / L / pred - 1) <= 0.05
        else:
            ok &= nE / (C * nT) >= 0.5
    return bool(ok)


def measure_t2():
    """Each entry is (q, h, ||T_W||/L dense, max_c, value at c = 1, ||E||, ||T'||, C, L)."""
    rows = []
    for q, h in H_CASES:
        S = Gram(q, dl=dlog_table(q))
        tau, pw = gauss_sums(q)
        L = q - 1
        K = np.arange(0, L, h)                       # chi_k is trivial on H = <g^{L/h}> iff h | k
        H = pw[np.arange(0, L, L // h)]
        sums = np.array([abs(np.exp(2j * np.pi * (c * H % q) / q).sum()) for c in range(1, q)]) / h
        nE, nT = norms(S, np.fft.fft(tau), K)
        Ks = np.sort(K)
        T = tau[(Ks[:, None] - Ks[None, :]) % L]
        Th = np.where(Ks % 2 == 0, 1.0, -1.0)[:, None] * T
        nT0 = np.abs(np.linalg.eigvalsh((Th + Th.conj().T) / 2)).max()
        C, _ = weight_coeffs(S)
        rows.append((q, h, nT0 / L, sums.max(), sums[0], nE, nT, C, L))
        print(f"(T2) q={q} |H|={h} |W|={len(K)}: ||T_W||/L = {nT0 / L:.10f}, max_c |sum_H e(ch/q)|/|H| = "
              f"{sums.max():.10f} (at c = 1: {sums[0]:.4f}); ||E||/L = {nE / L:.4f}, ||T'||/L = {nT / L:.4f}",
              flush=True)
    return rows


def gate_t2(rows, mut=None):
    ok = True
    for q, h, t, smax, s1, nE, nT, C, L in rows:
        ok &= abs(t - (s1 if mut == "m3" else smax)) <= 1e-9 and nE <= C * nT * (1 + 1e-9)
    return bool(ok)


def measure_t4():
    """Each entry is (q, N0, R, L, V0^2, ||b||^2, kappa - 1, ||rho||_4/3, ||rho||_2, E_Z, l2 sum, share of kappa - 1
    from |s|, t <= 10, share from x = -1)."""
    rows = []
    for q in QS:
        L, R = q - 1, round(q ** (2 / 3))
        N0 = round(q ** (7 / 18))
        dl = dlog_table(q)
        n = np.arange(N0, 2 * N0)
        f = np.zeros(L)
        f[dl[n]] = 1.0
        Sb = np.abs(L * np.fft.ifft(f))
        Sb[0] = -1
        K = np.argpartition(-Sb, R)[:R]
        V0sq = Sb[K].min() ** 2
        ind = np.zeros(L)
        ind[K] = 1.0
        Rx = L * np.fft.ifft(ind)                     # R(g^j) = sum_{k in W} e(kj/L)
        R4 = np.abs(Rx) ** 4
        kap1 = (R4.sum() - R4[0]) / R ** 4
        ratios, prods = {}, {}
        for a in n.tolist():
            for c in n.tolist():
                prods[a * c] = prods.get(a * c, 0) + 1
                if a != c:
                    x = a * pow(c, -1, q) % q
                    ratios[x] = ratios.get(x, 0) + 1
        rho = np.array(list(ratios.values()), float)
        rho43 = (rho ** (4 / 3)).sum() ** 0.75
        rho2 = np.sqrt((rho ** 2).sum())
        EZ = sum(v * v for v in prods.values())
        l2 = sum(abs(Rx[dl[x]]) ** 2 * m for x, m in ratios.items())
        small = {(sg * a * pow(c, -1, q)) % q for a in range(1, 11) for c in range(1, 11) for sg in (1, -1)} - {1}
        sh10 = sum(R4[dl[x]] for x in small) / (R4.sum() - R4[0])
        shm1 = R4[dl[q - 1]] / (R4.sum() - R4[0])
        rows.append((q, N0, R, L, V0sq, float(len(n)), kap1, rho43, rho2, EZ, l2, sh10, shm1))
    return rows


def gate_t4(rows, mut=None):
    ok = True
    for q, N0, R, L, V0sq, nb2, kap1, rho43, rho2, EZ, l2, sh10, shm1 in rows:
        gap = V0sq - nb2
        B1 = (gap / (rho2 if mut == "m4" else rho43)) ** 4
        B2 = gap ** 4 / (N0 ** 4 * EZ)
        cs = R ** 2 * gap ** 2 / (nb2 if mut == "m5" else nb2 ** 2)
        ok &= (2 * N0) ** 2 < q and gap > 0 and kap1 >= B1 * (1 - 1e-9) and B1 >= B2 * (1 - 1e-9)
        ok &= rho43 ** 4 <= N0 ** 4 * EZ * (1 + 1e-9) and l2 >= cs * (1 - 1e-9)
        if mut is None:
            floor = (L - R) ** 2 / ((L - 1) * R ** 2)
            sig = np.log(np.sqrt(V0sq)) / np.log(N0)
            print(f"(T4) q={q} N0={N0} R={R}: V0 = N0^{sig:.3f}, V0^2 - ||b||^2 = {gap:.1f}, "
                  f"||rho||_4/3 = {rho43:.1f}, E_Z = {EZ}; kappa - 1 = {kap1:.4f} >= {B1:.3e} >= {B2:.3e}; "
                  f"least possible = {floor:.4f}; l2 form {l2:.4e} >= {cs:.4e}; ||rho||_2 = {rho2:.1f}")
    return bool(ok)


def gate_t5(rows, mut=None):
    k1s = [r[6] for r in rows]
    ok = all(a < b for a, b in zip(k1s, k1s[1:]))
    for q, N0, R, L, V0sq, nb2, kap1, rho43, rho2, EZ, l2, sh10, shm1 in rows:
        floor = (L - R) ** 2 / ((L - 1) * R ** 2)
        ok &= kap1 > 5 * floor and (shm1 if mut == "m6" else sh10) >= 0.5
        if mut is None:
            print(f"(T5) q={q}: kappa - 1 = {kap1:.4f} = {kap1 / floor:.1f} x least; share from |s|, t <= 10: "
                  f"{sh10:.3f}; from x = -1: {shm1:.4f}")
    return bool(ok)


def main(argv):
    r1, r2, r4 = measure_t1(), measure_t2(), measure_t4()
    ok = gate_t1(r1) and gate_t2(r2) and gate_t4(r4) and gate_t5(r4)
    caught = {"m1": not gate_t1(r1, "m1"), "m2": not gate_t1(r1, "m2"), "m3": not gate_t2(r2, "m3"),
              "m4": not gate_t4(r4, "m4"), "m5": not gate_t4(r4, "m5"), "m6": not gate_t5(r4, "m6")}
    print(f"gates {'pass' if ok else 'FAIL'}; mutations: "
          + ", ".join(f"{k} {'caught' if v else 'NOT CAUGHT'}" for k, v in caught.items()))
    return 0 if ok and all(caught.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
