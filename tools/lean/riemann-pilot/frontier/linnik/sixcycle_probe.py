"""The six-cycle of the Gauss-sum matrix as a bilinear form (README round 558; SEVEN-THIRDS.md section 26).

Notation of transfer_probe.py: q prime, L = q - 1, g a primitive root, chi_k(g^j) = e(kj/L), W = {chi_k : k in K},
R(x) = sum_{chi in W} chi(x), T = T_W = [tau(chi chi'^bar)]_{chi, chi' in W} (diagonal tau(chi_0) = -1), so
that T'_W = T + I, and D = diag(chi(-1)).  Since conj(tau(psi)) = psi(-1) tau(psi^bar), T^* = D T D, so T D is
Hermitian and tr((T T^*)^3) = tr((T D)^6) = ||(T D)^3||_F^2.  Expanding the three Gauss sums and summing over the
middle characters,
    (T D)^3_{chi1, chi4} = chi4(-1) (tau(chi1 chi4^bar) S(chi1, chi4) + [chi1 = chi4] Z(chi1)),
    S(chi1, chi4) = sum_{x + y + z = 1, xyz != 0} chi1(x) chi4^bar(z) R(-y/x) R(-z/y),
    Z(chi) = L sum_{u != 0, -1} chi^bar(u) R(1 + u) R(u/(1 + u)),
the last from the triples with sum 0.  So
    tr((T T^*)^3) = q sum_{chi1 != chi4} |S(chi1, chi4)|^2 + sum_{chi in W} |Z(chi) - S(chi, chi)|^2.
S is the two-dimensional multiplicative Fourier transform of G(x, z) = R(-y/x) R(-z/y), with y = 1 - x - z and
G = 0 where y = 0.  The map (x, z) -> (a, b) = (-y/x, -z/y) is injective, since y = 1/(1 - b - 1/a), and
sum_x |R(x)|^2 = L |W|.  So orthogonality over all pairs of characters gives
    sum_{chi1, chi4 in W} |S|^2 <= sum_{all chi1, chi4} |S|^2 = L^2 sum |G|^2 <= L^4 |W|^2.
Orthogonality in u and Cauchy-Schwarz give
    sum_{chi in W} |Z(chi)|^2 <= L^3 sum_u |R(1 + u) R(u/(1 + u))|^2 <= L^3 sum_x |R(x)|^4 = kappa L^3 |W|^4,
with kappa = L E(W)/|W|^4.

  (S1) The entrywise identity for (T D)^3, the trace identity, and T^* = D T D, to relative tolerance 1e-9.
  (S2) Orthogonality over all pairs (relative tolerance 1e-9), sum |G|^2 <= L^2 |W|^2, and the restricted sum
       sum_{chi1, chi4 in W} |S|^2 <= L^4 |W|^2.
  (S3) sum_{chi in W} |Z|^2 <= L^3 sum_u |R(1 + u) R(u/(1 + u))|^2 <= L^3 sum_x |R(x)|^4.
  (S4) Random calibration.  For the random sets at q >= 499, tr((T T^*)^3) lies within 6% of the free value
       (5 - 6 alpha + 2 alpha^2) L^3 |W|^4, alpha = |W|/L.  Here T/L is the compression of multiplication by e(y/q),
       a unitary with uniformly distributed spectrum, to span(W); for free projections p, p' of trace alpha the
       moment-cumulant formula gives tau((p p')^3) = alpha^4 (1 + 3(1 - alpha) + (1 - alpha)(1 - 2 alpha)), and
       tr((T T^*)^3) = L^7 tau((p p')^3) in that model.  As alpha -> 0 the value tends to the tree part 5 L^3 |W|^4.
  Sets: at q = 101, 499, 1009 and 2003, two random sets of round(q^{2/3}) nontrivial characters and the
  round(q^{2/3}) nontrivial characters with the largest |sum_{N0 <= n < 2 N0} chi(n)|, N0 = round(q^{7/18}) (as in
  transfer_probe.py (T4)); and the annihilators of the subgroups of order 8 mod 1009 and 13 mod 2003.
  Printed, not gated: ||T||/L; the trace over the free value, for every set; the diagonal part's share of the trace;
  the off-diagonal part over its large-sieve bound q L^4 |W|^2; sum |G|^2/(L^2 |W|^2); and kappa.  Since
  sum_{all} |S|^2 = L^2 sum |G|^2, the off-diagonal part q sum_{chi1 != chi4} |S|^2 over L^3 |W|^4 equals the share
  of sum |S|^2 on the off-diagonal of W x W, divided by the uniform share (|W|/L)^2, times
  (q/L) sum |G|^2/(L^2 |W|^2).
Mutations, each of which must fail a gate: (m1) S with R(y/x) R(z/y) (the signs dropped); (m2) the trace identity
with q replaced by 1; (m3) Z without its factor L; (m4) orthogonality with L in place of L^2; (m5) the bound on
sum |G|^2 with L |W|^2 in place of L^2 |W|^2; (m6) (S3) with L^2 in place of L^3; (m7) (S4)'s free value read as
its limit 5.

Scope.  The identities and bounds are proved above; the probe checks them and their conventions numerically at four
small q.  (S4) compares with a free-probability value; it is a calibration, not a theorem about these sets, and the
printed measurements are calibrations at these sizes, not statements about large-values sets.
"""
import sys

import numpy as np

from line_sums import dlog_table, prim_root

QS6 = (101, 499, 1009, 2003)
H6 = ((1009, 8), (2003, 13))
MUTS = ("m1", "m2", "m3", "m4", "m5", "m6", "m7")


def field(q):
    L, g = q - 1, prim_root(q)
    pw = np.ones(L, dtype=np.int64)
    for j in range(1, L):
        pw[j] = pw[j - 1] * g % q
    tau = L * np.fft.ifft(np.exp(2j * np.pi * pw / q))      # tau(chi_k) = sum_j e(kj/L) e(g^j/q)
    return L, pw, dlog_table(q), tau


def g_table(q, L, pw, dl, Rx, signs=True):
    """G(g^i, g^l) = R(-y/x) R(-z/y), y = 1 - x - z, and 0 where y = 0; with signs=False, R(y/x) R(z/y)."""
    X, Zs = pw[:, None], pw[None, :]
    Y = (1 - X - Zs) % q
    ok = Y != 0
    Ys = np.where(ok, Y, 1)
    inv_x = pw[(-np.arange(L)) % L][:, None]
    inv_y = pw[(-dl[Ys]) % L]
    a = (q - Ys if signs else Ys) * inv_x % q
    b = (q - Zs if signs else Zs) * inv_y % q
    return np.where(ok, Rx[dl[a]] * Rx[dl[b]], 0)


def measure(q, name, K, field_data):
    """The quantities of (S1)-(S4) for W = {chi_k : k in K}."""
    L, pw, dl, tau = field_data
    K = np.sort(np.asarray(K))
    W = len(K)
    ind = np.zeros(L)
    ind[K] = 1.0
    Rx = L * np.fft.ifft(ind)                                # R(g^j) = sum_{k in K} e(kj/L)
    out = {"q": q, "L": L, "W": W, "name": name}
    for signs in (True, False):
        G = g_table(q, L, pw, dl, Rx, signs)
        S = L * np.fft.ifft(np.fft.fft(G, axis=1), axis=0)   # S[a, b] = sum_{i,l} G e(ai/L) e(-bl/L)
        out["S" if signs else "S_m1"] = S[np.ix_(K, K)]
        if signs:
            out["sumG2"] = float((np.abs(G) ** 2).sum())
            out["sumS2_all"] = float((np.abs(S) ** 2).sum())
    up1 = (pw + 1) % q
    okz = up1 != 0
    up1s = np.where(okz, up1, 1)
    h = np.where(okz, Rx[dl[up1s]] * Rx[dl[pw * pw[(-dl[up1s]) % L] % q]], 0)
    out["Z0"] = np.fft.fft(h)[K]                             # Z without its factor L
    out["sumh2"] = float((np.abs(h) ** 2).sum())
    out["sumR2"] = float((np.abs(Rx) ** 2).sum())
    out["sumR4"] = float((np.abs(Rx) ** 4).sum())
    T = tau[(K[:, None] - K[None, :]) % L]
    sgn = np.where(K % 2 == 0, 1.0, -1.0)                    # chi_k(-1) = (-1)^k
    TD = T * sgn[None, :]
    out["herm"] = float(np.abs(T.conj().T - sgn[:, None] * T * sgn[None, :]).max() / np.abs(T).max())
    TD3 = TD @ TD @ TD
    out["TD3"] = TD3
    M = T @ T.conj().T
    out["trace"] = float(np.trace(M @ M @ M).real)
    out["frob"] = float((np.abs(TD3) ** 2).sum())
    out["normT"] = float(np.linalg.norm(T, 2))
    out["sgn"], out["T"] = sgn, T
    return out


def gate(m, mut=None):
    q, L, W = m["q"], m["L"], m["W"]
    S = m["S_m1"] if mut == "m1" else m["S"]
    Z = m["Z0"] * (1 if mut == "m3" else L)
    rhs = m["sgn"][None, :] * (m["T"] * S + np.diag(Z))
    ok = np.abs(m["TD3"] - rhs).max() <= 1e-9 * np.abs(m["TD3"]).max()
    off = (np.abs(S) ** 2).sum() - (np.abs(np.diag(S)) ** 2).sum()
    tr_rhs = (1 if mut == "m2" else q) * off + (np.abs(Z - np.diag(S)) ** 2).sum()
    ok &= abs(m["trace"] - tr_rhs) <= 1e-9 * m["trace"] and abs(m["frob"] - m["trace"]) <= 1e-9 * m["trace"]
    ok &= m["herm"] <= 1e-9
    ok &= abs(m["sumS2_all"] - (L if mut == "m4" else L ** 2) * m["sumG2"]) <= 1e-9 * m["sumS2_all"]
    ok &= abs(m["sumR2"] - L * W) <= 1e-9 * L * W
    ok &= m["sumG2"] <= (L if mut == "m5" else L ** 2) * W ** 2 * (1 + 1e-9)
    ok &= (np.abs(S) ** 2).sum() <= L ** 4 * W ** 2 * (1 + 1e-9)
    ok &= (np.abs(Z) ** 2).sum() <= (L ** 2 if mut == "m6" else L ** 3) * m["sumh2"] * (1 + 1e-9)
    ok &= m["sumh2"] <= m["sumR4"] * (1 + 1e-9)
    if m["name"].startswith("random") and q >= 499:
        ok &= abs(m["trace"] / (free_value(W / L, mut) * L ** 3 * W ** 4) - 1) <= 0.06
    return bool(ok)


def free_value(alpha, mut=None):
    """tr((T T^*)^3)/(L^3 |W|^4) for a uniform-spectrum unitary compressed by a free projection of trace alpha."""
    return 5.0 if mut == "m7" else 1 + 3 * (1 - alpha) + (1 - alpha) * (1 - 2 * alpha)


def sets():
    rng = np.random.default_rng(558)
    for q in QS6:
        fd = field(q)
        L, _, dl, _ = fd
        R, N0 = round(q ** (2 / 3)), round(q ** (7 / 18))
        f = np.zeros(L)
        f[dl[np.arange(N0, 2 * N0)]] = 1.0
        Sb = np.abs(L * np.fft.ifft(f))
        Sb[0] = -1
        yield q, "random1", rng.choice(np.arange(1, L), R, replace=False), fd
        yield q, "random2", rng.choice(np.arange(1, L), R, replace=False), fd
        yield q, "interval", np.argpartition(-Sb, R)[:R], fd
        for qh, h in H6:
            if qh == q:
                yield q, f"H^perp |H|={h}", np.arange(0, L, h), fd


def main(argv):
    rows = []
    for q, name, K, fd in sets():
        m = measure(q, name, K, fd)
        L, W = m["L"], m["W"]
        S2 = np.abs(m["S"]) ** 2
        off = q * (S2.sum() - np.diag(S2).sum())
        diag = m["trace"] - off
        kappa = m["sumR4"] / W ** 4
        print(f"q={q} {name:14s} |W|={W:4d} ||T||/L={m['normT'] / L:.4f} "
              f"trace/free={m['trace'] / (free_value(W / L) * L ** 3 * W ** 4):.4f} diag/trace={diag / m['trace']:.4f} "
              f"off/(q L^4 |W|^2)={off / (q * L ** 4 * W ** 2):.3e} "
              f"sum|G|^2/(L^2 |W|^2)={m['sumG2'] / (L * W) ** 2:.4f} "
              f"kappa={kappa:.4f} "
              f"gates {'pass' if gate(m) else 'FAIL'}", flush=True)
        rows.append(m)
    ok = all(gate(m) for m in rows)
    caught = {mu: not all(gate(m, mu) for m in rows) for mu in MUTS}
    print(f"gates {'pass' if ok else 'FAIL'}; mutations: "
          + ", ".join(f"{k} {'caught' if v else 'NOT CAUGHT'}" for k, v in caught.items()))
    return 0 if ok and all(caught.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
