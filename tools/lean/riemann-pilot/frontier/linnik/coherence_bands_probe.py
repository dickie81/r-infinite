"""Where the coherence sits against round 570's proven range, split in psi (README round 573; SEVEN-THIRDS.md section 41).

Notation of farey_coherence_probe.py and IDEAS.md B33.  q prime, |W| = round(q^{2/3}), M = q/round(q^{7/9}), the
generic lines m = (m1, m2, m3) (m1 != 0, m3 != 0) of the box, B_m(x) = (m1 x + m3)/m2, w = 1_W - |W|/L on the
characters, c_x(psi) = sum_chi w(chi) w(conj(psi) chi) conj(chi)(x) and T_psi(x) = sum_m psi(B_m(x)) with psi(0) = 0.
B33's expansion is X'(x) + e(x) = sum_{psi != 1} c_x(psi) T_psi(x), with e(x) = |box| conj R(x) - c_x(1)(|box| - Z(x)),
c_x(1) = (1 - 2|W|/L) conj R(x) plus |W|^2/L at x = 1, and Z(x) the number of lines with B_m(x) = 0.  At each x the
square |X'(x) + e(x)|^2 splits into the diagonal sum_{psi != 1} |c_x(psi) T_psi(x)|^2 (round 571's D) and the rest, the
off-diagonal O.  Both are summed over x and divided by |box|^2 q |W|^2, as theta' is.  Round 570 proves the
incoherence on the points of height below q^{1/6} (when kappa <= q^{o(1)}); this probe asks where the measured
coherence sits relative to that range.

  (P1) The expansion, computed by FFT over the characters, equals X'(x) + e(x) computed from R at x = 1, 2, 3, 5, 7 and
       q - 1, for both sets at both q, to relative tolerance 1e-9 (in units of |box| |W|).  At the same points, the
       diagonal equals the mean over u in F_q^* of |Y~_u(x)|^2, where Y~_u(x) = sum_m R0(u B_m(x)/x) conj R0(u B_m(x))
       - c_x(1)(|box| - Z(x)) and Y~_1(x) = X'(x) + e(x) (Parseval over psi), to relative tolerance 1e-9.  So the
       off-diagonal at x is the excess of the shift u = 1 over the mean of its multiplicative translates.
  (P2) The sets of energy_frontier.py with kappa <= 1.25, at q = 10007 and 20011: the off-diagonal carries at least
       three quarters of ||X' + e||^2; the points of height at most q^{1/6} carry at most a third of it; and the points
       of height above q^{1/6} and at most 4M carry at least half.
  (P3) Random sets of size |W| at both q: |O| is at most 5% of ||X' + e||^2.
  Printed, not gated: ||X' + e||^2 and the diagonal by height band.
Mutations, each of which must fail a gate: (m1) the trivial character kept in the expansion (fails P1); (m2) the random
set in place of the kappa <= 1.25 set in (P2); (m3) the cut q^{1/4} in place of q^{1/6} in (P2).

Scope.  These are measurements, at two values of q, of the sets that energy_frontier.py's search finds; they bound
nothing over all sets of size q^{2/3}.  At these q the cut q^{1/6} is 4.6 and 5.2 and 4M is 31.0 and 36.1, so the
bands are a few integers wide.
"""
import sys

import numpy as np

from energy_frontier import frontier
from farey_coherence_probe import heights, r_of, xprime
from gram_probe import Gram
from line_sums import dlog_table
from low_energy_probe import Lines

QS = (10007, 20011)
PTS = (1, 2, 3, 5, 7)
MUTS = ("m1", "m2", "m3")
BANDS = (2, 4, 8, 16)


def measure(q):
    dl = dlog_table(q)
    S = Gram(q, dl=dl)
    lines = Lines(S, dl)
    inv = lines.inv
    boxl = [m for m in lines.box if m[0] != 0 and m[2] != 0]
    box = np.array(boxl, dtype=np.int64)
    nb, L, W, M = len(box), S.L, S.R, S.M
    best, _ = frontier(S, steps=150)
    rng = np.random.default_rng(37)
    sets = {"kappa<=1.25": best[1.25][1], "random": rng.choice(np.arange(1, L), W, replace=False)}
    H4 = int(4 * M)
    ht = heights(q, H4 + 2)
    norm = nb ** 2 * q * W ** 2
    xs = list(lines.x)
    pw = np.zeros(L, dtype=np.int64)
    pw[dl[1:]] = np.arange(1, q)
    out = {"q": q, "M": M, "H4": H4, "ht": ht, "sets": {}}
    for name, KK in sets.items():
        R = r_of(S, dl, KK)
        R0 = R.copy()
        R0[1] = 0
        X, _ = xprime(lines, R, boxl, 1)
        ind = np.zeros(L)
        ind[KK] = 1
        w = ind - W / L
        fw = np.fft.fft(w)
        tot = np.zeros(q)
        dia = np.zeros(q)
        err = {None: 0.0, "m1": 0.0, "shift": 0.0}
        for x in range(1, q):
            B = (box[:, 0] * x + box[:, 2]) % q * inv[box[:, 1]] % q
            hist = np.zeros(L)
            np.add.at(hist, dl[B[B != 0]], 1)
            T = np.fft.ifft(hist) * L
            ph = np.exp(-2j * np.pi * np.arange(L) * dl[x] / L)
            cw = np.fft.ifft(np.fft.fft(w * ph) * np.conj(fw))
            prod = cw[1:] * T[1:]
            s = prod.sum()
            tot[x] = abs(s) ** 2
            dia[x] = (np.abs(prod) ** 2).sum()
            if x in PTS or x == q - 1:
                cR = np.conj(R[x])
                Z = int((B == 0).sum())
                c1 = (1 - 2 * W / L) * cR + (W * W / L if x == 1 else 0)
                rhs = X[xs.index(x)] + nb * cR - c1 * (nb - Z)
                for tag, val in ((None, s), ("m1", s + cw[0] * T[0])):
                    err[tag] = max(err[tag], abs(val - rhs) / (nb * W))
                F = R0[pw * inv[x] % q] * np.conj(R0[pw])
                Yt = np.fft.ifft(np.fft.fft(F) * np.conj(np.fft.fft(hist))) - c1 * (nb - Z)
                err["shift"] = max(err["shift"], abs(Yt[0] - rhs) / (nb * W),
                                   abs((np.abs(Yt) ** 2).mean() - dia[x]) / (nb * W) ** 2)
        out["sets"][name] = {"tot": tot / norm, "dia": dia / norm, "err": err}
    return out


def shares(m, name, cut):
    rec, ht = m["sets"][name], m["ht"]
    tot, dia = rec["tot"], rec["dia"]
    T = tot.sum()
    low = ht <= cut
    mid = (ht > cut) & (ht <= m["H4"])
    return {"T": T, "off": (T - dia.sum()) / T, "low": tot[low].sum() / T, "mid": tot[mid].sum() / T}


def gate(ms, mut=None):
    ok = True
    for m in ms:
        q = m["q"]
        for name in ("kappa<=1.25", "random"):
            ok &= m["sets"][name]["err"]["m1" if mut == "m1" else None] <= 1e-9
            ok &= m["sets"][name]["err"]["shift"] <= 1e-9
        cut = int(q ** 0.25) if mut == "m3" else int(q ** (1 / 6))
        k = shares(m, "random" if mut == "m2" else "kappa<=1.25", cut)
        ok &= k["off"] >= 0.75 and k["low"] <= 1 / 3 and k["mid"] >= 0.5
        r = shares(m, "random", cut)
        ok &= abs(r["off"]) <= 0.05
    return bool(ok)


def main():
    ms = []
    for q in QS:
        m = measure(q)
        ms.append(m)
        cut = int(q ** (1 / 6))
        print(f"q={q} |W|={round(q ** (2 / 3))} M={m['M']:.2f} cut floor(q^(1/6))={cut} floor(4M)={m['H4']}", flush=True)
        edges = [e for e in BANDS if e < m["H4"]] + [m["H4"], q]
        for name, rec in m["sets"].items():
            k = shares(m, name, cut)
            lo, cells = 0, []
            for e in edges:
                sel = (m["ht"] > lo) & (m["ht"] <= e)
                cells.append(f"({lo},{e if e < q else 'inf'}]: {rec['tot'][sel].sum():.5f}/{rec['dia'][sel].sum():.5f}")
                lo = e
            print(f"  {name:12s} ||X'+e||^2 = {k['T']:.5f}, off-diagonal share {k['off']:+.3f}, share at height <= q^(1/6) "
                  f"{k['low']:.3f}, in (q^(1/6), 4M] {k['mid']:.3f}; identity errors {rec['err'][None]:.1e}, "
                  f"{rec['err']['shift']:.1e}", flush=True)
            print("    total/diagonal by height: " + "  ".join(cells), flush=True)
    ok = gate(ms)
    caught = {mu: not gate(ms, mu) for mu in MUTS}
    print(f"gates {'pass' if ok else 'FAIL'}; mutations: "
          + ", ".join(f"{k} {'caught' if v else 'NOT CAUGHT'}" for k, v in caught.items()))
    return 0 if ok and all(caught.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
