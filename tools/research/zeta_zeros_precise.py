#!/usr/bin/env python3
"""Data producer: the first 800 nontrivial zeros of zeta to 100 decimal digits (mpmath.zetazero at 105 dps),
written to checkpoints/zeta_zeros_800_100dps.json as decimal strings (Theorem 1bu's substrate: the zero-side
sums ghat_1(gamma)^2 at the cells reach e^{-383}, far below what the double-precision list zeta_zeros_6700.json
can resolve -- a zero known to 1e-15 leaves ghat(gamma)^2 ~ 1e-30, and 40 digits leave 1e-80 against e^{-383} = 1e-166 at delta = 3.5). The list ends at gamma_800 = 1183.71.
About six minutes. Usage: zeta_zeros_precise.py"""
import os, json, time
import mpmath as mp
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "checkpoints")
N = 800

if __name__ == "__main__":
    mp.mp.dps = 105
    t0 = time.time(); out = []
    for n in range(1, N + 1):
        out.append(mp.nstr(mp.zetazero(n).imag, 100))
    os.makedirs(OUT, exist_ok=True)
    json.dump(out, open(os.path.join(OUT, f"zeta_zeros_{N}_100dps.json"), "w"))
    print(f"{N} zeros at 100 digits in {time.time() - t0:.0f}s; last {out[-1]}")
