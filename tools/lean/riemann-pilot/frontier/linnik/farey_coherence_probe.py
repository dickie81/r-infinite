"""Where the coherence of the small-line sums lives (README round 563; SEVEN-THIRDS.md section 31).

Notation of low_energy_probe.py.  q prime, |W| = round(q^{2/3}), N = round(q^{7/9}), M = q/N, R(y) = sum_{chi in W}
chi(y) and R0 = R with R0(1) = 0.  The box holds the lines m = (m1, m2, m3) with |m1|, |m3| <= M and 1 <= m2 <= M;
only the generic lines (m1 != 0 and m3 != 0) are used, since a line with a zero coordinate collapses to
(q - 1)|R(c)|^2 (README round 539).  B_m(x) = (m1 x + m3)/m2 and Y_m(x) = R0(B_m(x)/x) conj R0(B_m(x)).

The common component.  In R(B/x) conj R(B) = sum_{chi, chi'} chi(B/x) conj chi'(B) the terms chi = chi' sum to
R(1/x) = conj R(x) on every line.  They are the triples of section 6 that are not distinct, and they make every pair
of lines correlate by about q|W|.  So put Y'_m(x) = Y_m(x) - conj R(x) (with R(1) = |W|), X'(x) = sum_m Y'_m(x) and
theta' = ||X'||^2/(|box|^2 q |W|^2).  The centring is exact on average: sum_{u in F_q^*} R(u/x) conj R(u) =
(q - 1) conj R(x) by orthogonality.  The height of x is the least max(|a|, b) with x = a/b mod q.

  (F1) The orthogonality identity behind the centring, at five points x, to relative tolerance 1e-9.
  (F2) Random sets of size |W|: theta' <= 3/|box|, three times the level of the diagonal m = m', and the points of
       height <= 30 carry less than a quarter of ||X'||^2, at q = 10007 and 100003.
  (F3) The sets of energy_frontier.py with kappa <= 1.25: the points of height <= 30 carry more than half of
       ||X'||^2 at both q, though they are 11% and 1.1% of F_q^*.
  (F4) theta' of the kappa <= 1.25 set falls by at least a factor 2 from q = 10007 to 100003.
  (F5) At q = 10007, the full matrix C(m, m') = sum_x Y'_m(x) conj Y'_m'(x): the pairs of lines with the same ratio
       m1 : m3, m2 : m3 or m1 : m2 (the lines a diagonal scaling (b1, b2) -> (beta1 b1, beta2 b2) relates) carry less
       than a tenth of sum C for the kappa <= 1.25 set, although its twelve largest generic entries are of that kind.
  Printed, not gated: theta' and the shares by height for the (G1) set of gram_probe.py, and the mean |R| at heights
  <= 10 and elsewhere.
Mutations, each of which must fail a gate: (m1) the common component kept (no centring); (m2) the centring with the
wrong sign; (m3) the random set in place of the kappa <= 1.25 set in (F3).

Scope.  These are measurements, at two values of q, of sets that two search methods find (alternating projections
and the energy-penalised exchange of energy_frontier.py); they bound nothing over all sets of size q^{2/3}.  At these q,
M is 7 and 12, so "small height" and "the box" are not well separated.
"""
import sys

import numpy as np

from energy_frontier import frontier
from gram_probe import QS, Gram
from line_sums import dlog_table
from low_energy_probe import Lines

HCUT = 30
MUTS = ("m1", "m2", "m3")


def r_of(S, dl, K):
    ind = np.zeros(S.L)
    ind[K] = 1
    Rexp = np.fft.ifft(ind) * S.L
    R = np.zeros(S.q, complex)
    R[1:] = Rexp[dl[1:]]
    return R


def heights(q, H):
    ht = np.full(q, H + 1, dtype=np.int64)
    for b in range(1, H + 1):
        binv = pow(b, -1, q)
        for a in range(-H, H + 1):
            if a:
                x = a * binv % q
                ht[x] = min(ht[x], max(abs(a), b))
    return ht


def xprime(lines, R, box, sign):
    q, x, inv = lines.S.q, lines.x, lines.inv
    R0 = R.copy()
    R0[1] = 0
    xinv = inv[x]
    cR = np.conj(R[x])
    X = np.zeros(q - 1, complex)
    Y = []
    for m1, m2, m3 in box:
        B = (m1 * x + m3) % q * inv[m2] % q
        y = R0[B * xinv % q] * np.conj(R0[B]) - sign * cR
        X += y
        Y.append(y.astype(np.complex64))
    return X, Y


def measure(q, pairs):
    dl = dlog_table(q)
    S = Gram(q, dl=dl)
    lines = Lines(S, dl)
    box = [m for m in lines.box if m[0] != 0 and m[2] != 0]
    v, K = S.alternate()
    best, _ = frontier(S, steps=150)
    rng = np.random.default_rng(37)
    sets = {"G1": K, "kappa<=1.25": best[1.25][1], "random": rng.choice(np.arange(1, S.L), S.R, replace=False)}
    ht = heights(q, int(2 * np.sqrt(q)))[lines.x]
    out = {"q": q, "box": len(box), "R": S.R, "frac_small": float((ht <= HCUT).mean()), "sets": {}}
    for name, KK in sets.items():
        R = r_of(S, dl, KK)
        if name == "kappa<=1.25":
            pts = (2, 3, 5, 7, 11)
            idt = []
            for x0 in pts:
                u = np.arange(1, q)
                lhs = (R[u * pow(x0, -1, q) % q] * np.conj(R[u])).sum()
                idt.append(abs(lhs - (q - 1) * np.conj(R[x0])) <= 1e-9 * (q - 1) * S.R)
            out["identity"] = all(idt)
        rec = {}
        for sign, tag in ((1, None), (0, "m1"), (-1, "m2")):
            X, Y = xprime(lines, R, box, sign)
            a2 = np.abs(X) ** 2
            rec[tag] = (a2.sum() / (len(box) ** 2 * q * S.R ** 2), a2[ht <= HCUT].sum() / a2.sum())
            if tag is None and pairs:
                Ym = np.array(Y)
                C = (Ym @ Ym.conj().T).real.astype(np.float64)
                A = np.array(box)
                r13 = A[:, None, 0] * A[None, :, 2] == A[:, None, 2] * A[None, :, 0]
                r23 = A[:, None, 1] * A[None, :, 2] == A[:, None, 2] * A[None, :, 1]
                r12 = A[:, None, 0] * A[None, :, 1] == A[:, None, 1] * A[None, :, 0]
                off = ~np.eye(len(box), dtype=bool)
                rel = (r13 | r23 | r12) & off
                prim = np.array([tuple(np.array(m) // np.gcd.reduce(np.abs(m))) for m in box])
                dup = (prim[:, None, :] == prim[None, :, :]).all(axis=2) & off
                gen = off & ~dup
                rec["scaling_share"] = (C * (rel & ~dup)).sum() / C.sum()
                iu = np.triu_indices(len(box), 1)
                g = gen[iu]
                top = np.argsort(-np.abs(C[iu][g]))[:12]
                rec["top_scaling"] = bool(rel[iu][g][top].all())
            if tag is None:
                absR = np.abs(R[lines.x])
                rec["meanR"] = (absR[(ht <= 10) & (lines.x > 1)].mean() / S.R,
                                absR[(ht > 10)].mean() / S.R)
        out["sets"][name] = rec
    return out


def gate(ms, mut=None):
    ok = True
    th = []
    for m in ms:
        tag = mut if mut in ("m1", "m2") else None
        rnd = m["sets"]["random"][tag]
        ok &= m.get("identity", True)
        ok &= rnd[0] <= 3 / m["box"] and rnd[1] < 0.25
        low = m["sets"]["random" if mut == "m3" else "kappa<=1.25"][tag]
        ok &= low[1] > 0.5
        th.append(m["sets"]["kappa<=1.25"][tag][0])
        if "scaling_share" in m["sets"]["kappa<=1.25"]:
            s = m["sets"]["kappa<=1.25"]
            ok &= s["scaling_share"] < 0.1 and s["top_scaling"]
    ok &= len(th) == 2 and th[1] <= th[0] / 2
    return bool(ok)


def main():
    ms = []
    for i, q in enumerate(QS[:2]):
        m = measure(q, pairs=(i == 0))
        ms.append(m)
        print(f"q={q} |W|={m['R']} generic lines={m['box']} share of F_q^* at height <= {HCUT}: {m['frac_small']:.3f}"
              f"; orthogonality identity {'holds' if m.get('identity') else 'FAILS'}", flush=True)
        for name, rec in m["sets"].items():
            th, sh = rec[None]
            extra = (f"; scaling-class share {rec['scaling_share']:+.3f}, top twelve generic pairs scaling-related: "
                     f"{rec['top_scaling']}") if "scaling_share" in rec else ""
            print(f"  {name:12s} theta' = {th:.5f} (3/|box| = {3 / m['box']:.5f}), share at height <= {HCUT}: {sh:.3f}"
                  f"; uncentred theta = {rec['m1'][0]:.5f}; mean |R|/|W| at height <= 10: {rec['meanR'][0]:.3f}, "
                  f"elsewhere {rec['meanR'][1]:.3f}{extra}", flush=True)
    ok = gate(ms)
    caught = {mu: not gate(ms, mu) for mu in MUTS}
    print(f"gates {'pass' if ok else 'FAIL'}; mutations: "
          + ", ".join(f"{k} {'caught' if v else 'NOT CAUGHT'}" for k, v in caught.items()))
    return 0 if ok and all(caught.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
