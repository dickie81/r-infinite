"""refine_k2_probe.py: the certificate's total with the evaluable two-prime parts of the dropped depth-2 terms kept, in
exact integers on the grid of `route_limits.replay` (SIEVE-ROUTE.md §28; round 704). A replay of a refined
certificate, not a certificate: the refinement's soundness is not proved in Lean.

A dropped depth-2 term `S(A_{p₁p₂}, p₂)` counts `n = p₁p₂m` with every prime of `m` at least `p₂`, and splits exactly by
the factorization of `m`. Its part with `m = q₁q₂`, `p₂ ≤ q₁ ≤ q₂`, has the `B`-density `dα₁dα₂dβ/(α₁α₂βγ)`, with
`α₁, α₂, β, γ = 1 − α₁ − α₂ − β` the exponents of `p₁, p₂, q₁, q₂`; where some subset sum of `{α₁, α₂, β, γ}` lies in
`U = (u₁, u₂) ∪ (1 − u₂, 1 − u₁)` it is a Type II sum in that grouping (§6), which the refinement keeps. For a candidate
cell `(i, j)` lying wholly in the term's region (`e_j + H ≤ e_i`, `2(e_i + H) ≤ DEN`), the kept share is at least
  `sub = Σ_k ⌊K·H³·DEN/((e_i + H)(e_j + H)(e_k + H)·γ_hi)⌋`
over the cells `k` of `β` with `e_k ≥ e_j + H` (so `β ≥ α₂`), `2(e_k + H) + e_i + e_j + 2H ≤ DEN` (so `β ≤ γ`) and
`surely` evaluable at `[cell i, cell j, cell k, (γ_lo, γ_hi)]`, `γ_hi = DEN − e_i − e_j − e_k`, `γ_lo = γ_hi − 3H`. The
cell's cost `b2` becomes `b2 − sub` (truncated at `0`), and a decomposed cell costs `min(ref, b2 − sub)`. Depth-4 costs
are not refined. Everything else is `route_limits.replay`'s.

Gate: where `route_limits.jsonl` has the row of the curve, `L` and `n`, the unrefined total equals the row's total; and
the refined total is at most the unrefined one. Exits 1 otherwise.

Usage: refine_k2_probe.py CURVE L N [N ...]. The window is the row's when `route_limits.jsonl` has one for the curve and
`L`, else `route_limits.window`'s sampled scan (its corners not checked). Prints each total over `K` and the depth-4
tests of the decomposed cells, before and after.
"""
import json
import os
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl  # noqa: E402

DEN, K, TOPK = rl.DEN, rl.K, rl.TOPK
tsub, cdiv, subset_sums = rl.tsub, rl.cdiv, rl.subset_sums


def replay2(U1, U2, n):
    """`route_limits.replay`'s total, the refined total, and the depth-4 tests of the decomposed cells of each."""
    V = U2 - U1
    H = (tsub(DEN // 2, V) + n - 1) // n
    lim = tsub(DEN, U1)

    def e(k):
        return V + H * k

    def inside(lo, hi):
        return (U1 < lo and hi < U2) or (tsub(DEN, U2) < lo and hi < tsub(DEN, U1))

    def surely(xs):
        return any(inside(*s) for s in subset_sums(xs))

    def invK(s, t, m):
        return K if DEN <= s + 2 * t + (m + 1) * H else cdiv(K * (t + H), DEN - s - t - m * H)

    def omK(s, t, m):
        if DEN < s + 2 * t:
            return 0
        if s + 3 * t + (m + 2) * H <= DEN:
            return TOPK
        if DEN < s + 3 * t:
            return invK(s, t, m)
        return max(invK(s, t, m), TOPK)

    def cell(k):
        return (e(k), e(k) + H)

    def sub2(i, j):
        ei, ej = e(i), e(j)
        if not (ej + H <= ei and 2 * (ei + H) <= DEN):
            return 0
        tot = 0
        k = 0
        while True:
            ek = e(k)
            if 2 * (ek + H) + ei + ej + 2 * H > DEN:
                break
            if ek >= ej + H:
                g_hi = DEN - ei - ej - ek
                if surely([cell(i), cell(j), cell(k), (g_hi - 3 * H, g_hi)]):
                    tot += K * H ** 3 * DEN // ((ei + H) * (ej + H) * (ek + H) * g_hi)
            k += 1
        return tot

    total = total2 = t4 = t4r = 0
    for i in range(n):
        for j in range(n):
            ei, ej = e(i), e(j)
            if not (ej < ei + H and 2 * ei < DEN and ei + 2 * ej <= DEN and not (U1 < ei and ei + H < U2)
                    and not surely([cell(i), cell(j)])):
                continue
            b2 = cdiv(H * H * DEN * omK(ei, ej, 2), ei * ej * ej)
            b2r = tsub(b2, sub2(i, j))
            ks = [k for k in range(n) if e(k) < ej + H and ei + ej + 2 * e(k) <= DEN
                  and not surely([cell(i), cell(j), cell(k)])]
            if not (ei + H + (ej + H) < lim and all(ei + H + (ej + H) + (e(k) + H) < lim for k in ks)):
                total += b2
                total2 += b2r
                continue
            ref = tests = 0
            for k in ks:
                ek = e(k)
                for l in range(k + 1):
                    el = e(l)
                    if ei + ej + ek + 2 * el <= DEN:
                        tests += 1
                        if not surely([cell(i), cell(j), cell(k), cell(l)]):
                            ref += cdiv(H ** 4 * DEN * omK(ei + ej + ek, el, 4), ei * ej * ek * el * el)
            total += min(ref, b2)
            t4 += tests if ref <= b2 else 0
            total2 += min(ref, b2r)
            t4r += tests if ref <= b2r else 0
    return total, total2, t4, t4r


def main():
    curve, L, ns = sys.argv[1], Fr(sys.argv[2]), [int(x) for x in sys.argv[3:]]
    rows = [r for r in rl.rows_of(os.path.join(HERE, 'route_limits.jsonl')) if r['curve'] == curve and Fr(r['L']) == L]
    if rows:
        U1, U2 = rows[0]['U1'], rows[0]['U2']
        src = f"route_limits.jsonl's window [{rows[0]['W1']}, {rows[0]['W2']}]"
    else:
        w1, w2 = rl.window(rl.parse(curve), L)
        U1, U2 = -(-int(Fr(str(w1)) * DEN) // 1), int(Fr(str(w2)) * DEN)
        src = f"the sampled window [{w1}, {w2}] (corners not checked)"
    print(f"refine_k2_probe: {curve}, L = {L}, {src}; replays of a refined certificate, not certificates", flush=True)
    bad = 0
    for n in ns:
        t0 = time.time()
        tot, tot2, t4, t4r = replay2(U1, U2, n)
        row = [r for r in rows if r['n'] == n and r['U1'] == U1 and r['U2'] == U2]
        check = ''
        if row:
            same = row[0]['total'] == tot
            check = f"; equals route_limits.jsonl's total: {same}"
            bad += not same
        if tot2 > tot:
            bad += 1
            check += '; FAIL: refined above unrefined'
        print(f"  n = {n}: total/K {tot / K:.5f}, refined {tot2 / K:.5f}; depth-4 tests of the decomposed cells {t4}, "
              f"refined {t4r}; {time.time() - t0:.0f} s{check}", flush=True)
    print("REFINE_K2", "PASS" if bad == 0 else f"FAIL ({bad})")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
