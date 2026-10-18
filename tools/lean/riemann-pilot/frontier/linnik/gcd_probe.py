"""The gcd dichotomy for the critical block (README round 559; SEVEN-THIRDS.md section 27).

Notation of transfer_probe.py: q prime, L = q - 1, g a primitive root, chi_k(g^j) = e(kj/L).  The block is
I = [N0, 2 N0) (integers), D_J(chi) = sum_{m in J} chi(m), and I/f = {m : f m in I}, an interval of length about
N0/f.  Grouping the pairs (n, n') in I^2 by their gcd g and writing n = g a, n' = g b with (a, b) = 1,
    |D_I(chi)|^2 = sum_g C_g(chi),   C_g(chi) = sum_{a, b in I/g, (a, b) = 1} chi(a) chi^bar(b)
                                            = sum_e mu(e) |D_{I/(g e)}(chi)|^2.
So the part from the pairs with gcd > G is
    P_{>G}(chi) = sum_{n, n' in I, (n, n') > G} chi(n) chi^bar(n') = sum_{f > G} c_f |D_{I/f}(chi)|^2,
    c_f = sum_{g | f, g > G} mu(f/g),   |c_f| <= d(f),
and every scale N0/f in it is below N0/G.  For any set W of characters, Hoelder with exponents 3/2 and 3 and the
mean value theorem for the cube D_{I/f}^3 (length M_f < 8 (N0/f)^3, coefficients a_m = #{m = h1 h2 h3})
    sum_{chi in W} |P_{>G}| <= sum_{f > G} |c_f| |W|^{2/3} (sum_chi |D_{I/f}|^6)^{1/3},
    sum_chi |D_{I/f}|^6 <= (L + M_f) sum_m a_m^2.
At the critical point (|W| = q^{2/3}, N0 = q^{7/18}, V0 = N0^{5/7}) the right side is
q^{o(1)} |W|^{2/3} (q^{1/3} N0 + N0^2/G), a share q^{o(1)} (q^{-1/18} + 1/G) of |W| V0^2.  The rest,
P_{<=G}(chi) = sum over the pairs with gcd <= G, has the fourth moment
    sum_chi |P_{<=G}(chi)|^2 = L sum_{(a, b) = 1} #{g <= G : g a, g b in I}^2,
since n1 n2' = n1' n2 has no wrap ((2 N0)^2 < q); that is about N0^2 log G, against N0^2 log N0 for |D_I|^4.

  (P1) The identity P_{>G} = sum_{f > G} c_f |D_{I/f}|^2, against the direct sum over the pairs with gcd > G,
       for every chi, to relative tolerance 1e-9, at G = 1, 2, 4 and 8.
  (P2) The fourth-moment identity for P_{<=G}, exactly (an integer count), at the same G.
  (P3) For W the |W| characters with the largest |D_I| (|W| = round(q^{2/3})): the Hoelder bound above, with the
       sixth moments computed, and the mean value bound for each cube.
  Sizes: q = 10007 and 100003, N0 = round(q^{7/18}).
  Printed, not gated: the share sum_{W} |P_{>G}| / sum_{W} |D_I|^2, the bound's share, and
  sum |P_{<=G}|^2 / sum |D_I|^4.
Mutations, each of which must fail a gate: (m1) c_f read as mu(f) (the sum over g dropped); (m2) the pairs grouped
by gcd >= G in place of gcd > G; (m3) Hoelder with |W|^{1/2} in place of |W|^{2/3}; (m4) the mean value bound
without its term M_f.

Scope.  The identity and the bounds are proved above; the probe checks them and their conventions at two small q,
where N0 is 36 and 88.  It says nothing about the critical exponent itself.
"""
import sys
from math import gcd

import numpy as np

from line_sums import dlog_table

QS = (10007, 100003)
GS = (1, 2, 4, 8)
MUTS = ("m1", "m2", "m3", "m4")


def mobius_upto(n):
    mu = np.ones(n + 1, dtype=np.int64)
    is_p = np.ones(n + 1, dtype=bool)
    is_p[:2] = False
    for p in range(2, n + 1):
        if is_p[p]:
            is_p[2 * p::p] = False
            mu[p::p] *= -1
            mu[p * p::p * p] = 0
    mu[0] = 0
    return mu


def interval_sums(q, dl, lo, hi):
    """D_J(chi_k) for every k, J = [lo, hi) as integers."""
    L = q - 1
    f = np.zeros(L)
    if hi > lo:
        np.add.at(f, dl[np.arange(lo, hi)], 1.0)
    return L * np.fft.ifft(f)


def c_coeffs(F, G, mu, mut=None):
    """c_f = sum_{g | f, g > G} mu(f/g) for 1 <= f <= F (m1: mu(f); m2: g >= G)."""
    c = np.zeros(F + 1, dtype=np.int64)
    for g in range(1, F + 1):
        if g > G or (mut == "m2" and g == G):
            c[g::g] += mu[1:F // g + 1]
    if mut == "m1":
        c = np.where(np.arange(F + 1) > G, mu[:F + 1], 0)
    return c


def measure(q):
    L, dl = q - 1, dlog_table(q)
    N0 = round(q ** (7 / 18))
    lo, hi = N0, 2 * N0
    F = hi - 1
    mu = mobius_upto(F)
    DI = interval_sums(q, dl, lo, hi)
    sub = {f: interval_sums(q, dl, -(-lo // f), -(-hi // f)) for f in range(1, F + 1)}
    six, mvt = {}, {}
    for f in range(1, F + 1):
        a, b = -(-lo // f), -(-hi // f)
        six[f] = float((np.abs(sub[f]) ** 6).sum())
        if b > a:
            h = np.arange(a, b)
            prods = np.multiply.outer(np.multiply.outer(h, h), h).ravel()
            _, cnt = np.unique(prods, return_counts=True)
            mvt[f] = (float(prods.max() - prods.min() + 1), float((cnt.astype(np.int64) ** 2).sum()))
        else:
            mvt[f] = (0.0, 0.0)
    n = np.arange(lo, hi)
    pairs = [(x, y, gcd(int(x), int(y))) for x in n for y in n]
    R = round(q ** (2 / 3))
    W = np.argsort(-np.abs(DI))[:R]
    out = {"q": q, "L": L, "N0": N0, "DI": DI, "W": W, "rows": {}}
    for G in GS:
        rows = {}
        for mut in (None, "m1", "m2"):
            c = c_coeffs(F, G, mu, mut)
            P_id = sum(c[f] * np.abs(sub[f]) ** 2 for f in range(1, F + 1) if c[f] != 0)
            rows[mut] = (P_id, c)
        r = np.zeros(L)
        for x, y, d in pairs:
            if d > G:
                r[dl[x * pow(int(y), -1, q) % q]] += 1.0
        P_dir = L * np.fft.ifft(r)
        r2 = np.zeros(L)
        for x, y, d in pairs:
            if d <= G:
                r2[dl[x * pow(int(y), -1, q) % q]] += 1.0
        P_le = L * np.fft.ifft(r2)
        count = 0
        for a0 in range(1, hi):
            for b0 in range(1, hi):
                if gcd(a0, b0) == 1:
                    k = sum(1 for g0 in range(1, G + 1) if lo <= g0 * a0 < hi and lo <= g0 * b0 < hi)
                    count += k * k
        out["rows"][G] = {"id": rows, "dir": P_dir, "le": P_le, "count": count}
    out["six"], out["mvt"], out["F"] = six, mvt, F
    return out


def gate(m, mut=None):
    q, L, W = m["q"], m["L"], m["W"]
    ok = True
    for G, row in m["rows"].items():
        P_id, c = row["id"][mut if mut in ("m1", "m2") else None]
        P_dir = row["dir"]
        ok &= np.abs(P_id - P_dir).max() <= 1e-9 * max(1.0, np.abs(P_dir).max())
        ok &= abs((np.abs(row["le"]) ** 2).sum() - L * row["count"]) <= 1e-9 * L * row["count"]
        lhs = np.abs(P_dir[W]).sum()
        expo = 0.5 if mut == "m3" else 2 / 3
        rhs = sum(abs(c[f]) * len(W) ** expo * m["six"][f] ** (1 / 3) for f in range(1, m["F"] + 1) if c[f] != 0)
        ok &= lhs <= rhs * (1 + 1e-9)
    for f, (M, E) in m["mvt"].items():
        ok &= m["six"][f] <= (L + (0 if mut == "m4" else M)) * E * (1 + 1e-9)
    return bool(ok)


def main(argv):
    rows = []
    for q in QS:
        m = measure(q)
        W, DI = m["W"], m["DI"]
        tot = (np.abs(DI[W]) ** 2).sum()
        full4 = (np.abs(DI) ** 4).sum()
        for G, row in m["rows"].items():
            c = row["id"][None][1]
            share = np.abs(row["dir"][W]).sum() / tot
            bound = sum(abs(c[f]) * len(W) ** (2 / 3) * m["six"][f] ** (1 / 3)
                        for f in range(1, m["F"] + 1) if c[f] != 0) / tot
            print(f"q={q} N0={m['N0']} |W|={len(W)} G={G}: share of gcd > G on W = {share:.4f}, bound's share = "
                  f"{bound:.3f}; sum |P_<=G|^2 / sum |D_I|^4 = {(np.abs(row['le']) ** 2).sum() / full4:.4f}",
                  flush=True)
        rows.append(m)
    ok = all(gate(m) for m in rows)
    caught = {mu: not all(gate(m, mu) for m in rows) for mu in MUTS}
    print(f"gates {'pass' if ok else 'FAIL'}; mutations: "
          + ", ".join(f"{k} {'caught' if v else 'NOT CAUGHT'}" for k, v in caught.items()))
    return 0 if ok and all(caught.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
