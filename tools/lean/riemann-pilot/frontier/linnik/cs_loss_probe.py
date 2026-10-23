"""How far the coherence exceeds round 571's diagonal, by height band (README round 574; SEVEN-THIRDS.md section 42).

Notation of coherence_bands_probe.py.  At each x, with a_psi = c_x(psi) T_psi(x) for psi != 1, the coherence is
|sum_psi a_psi|^2 = |X'(x) + e(x)|^2, the diagonal (round 571) is sum_psi |a_psi|^2, and B33's Cauchy-Schwarz bound is
(sum_psi |c_x(psi)|^2)(sum_psi |T_psi(x)|^2).  For each set and each band of heights (at most q^{1/6}; above q^{1/6}
and at most 4M; above 4M) this prints the summed ratios coherence/diagonal (the enhancement) and Cauchy-Schwarz/
coherence (B33's loss), for the kappa <= 1.25 set of energy_frontier.py and a random set of the same size.

Printed, not gated.  The q are taken from the command line (round 574 ran 10007 20011 40009).  The search's sets vary
in strength with q, so the printed numbers show no monotone trend, and they bound nothing over all sets of size q^{2/3}.
Since the diagonal carries at most q^{-1/9+o(1)} of theta' when kappa <= q^{o(1)} (round 571), core 1 follows whenever
the global enhancement is at most q^{1/9-2 delta} up to logarithms; that sufficient condition is an inequality, not a
gate of this script.
"""
import sys

import numpy as np

from energy_frontier import frontier
from farey_coherence_probe import heights
from gram_probe import Gram
from line_sums import dlog_table
from low_energy_probe import Lines


def run(q):
    dl = dlog_table(q)
    S = Gram(q, dl=dl)
    lines = Lines(S, dl)
    inv = lines.inv
    box = np.array([m for m in lines.box if m[0] != 0 and m[2] != 0], dtype=np.int64)
    L, W, M = S.L, S.R, S.M
    best, _ = frontier(S, steps=150)
    rng = np.random.default_rng(37)
    sets = {"kappa<=1.25": best[1.25][1], "random": rng.choice(np.arange(1, L), W, replace=False)}
    H4 = int(4 * M)
    ht = heights(q, H4 + 2)
    cut = int(q ** (1 / 6))
    bands = (("height <= q^(1/6)", ht <= cut), ("(q^(1/6), 4M]", (ht > cut) & (ht <= H4)), ("above 4M", ht > H4))
    for name, KK in sets.items():
        ind = np.zeros(L)
        ind[KK] = 1
        w = ind - W / L
        fw = np.fft.fft(w)
        tot = np.zeros(q)
        dia = np.zeros(q)
        csb = np.zeros(q)
        for x in range(1, q):
            B = (box[:, 0] * x + box[:, 2]) % q * inv[box[:, 1]] % q
            hist = np.zeros(L)
            np.add.at(hist, dl[B[B != 0]], 1)
            T = np.fft.ifft(hist) * L
            ph = np.exp(-2j * np.pi * np.arange(L) * dl[x] / L)
            cw = np.fft.ifft(np.fft.fft(w * ph) * np.conj(fw))
            prod = cw[1:] * T[1:]
            tot[x] = abs(prod.sum()) ** 2
            dia[x] = (np.abs(prod) ** 2).sum()
            csb[x] = (np.abs(cw[1:]) ** 2).sum() * (np.abs(T[1:]) ** 2).sum()
        cells = [f"{lab}: enhancement {tot[sel].sum() / dia[sel].sum():6.1f}, CS loss {csb[sel].sum() / tot[sel].sum():8.1f}"
                 for lab, sel in bands]
        print(f"q={q} L={L} {name:12s} global enhancement {tot.sum() / dia.sum():6.1f} | " + " | ".join(cells),
              flush=True)


if __name__ == "__main__":
    for q in map(int, sys.argv[1:]):
        run(q)
