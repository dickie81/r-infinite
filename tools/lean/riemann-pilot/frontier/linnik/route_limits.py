"""route_limits.py: where the sieve route's certificate ends (SIEVE-ROUTE.md §23, rounds 626–629): the certificates,
the window corners and `quadfit` in exact arithmetic, `fit` and the window's sampled scan in floating point. (Round 628:
retracted, false when written: the first line read "…, in exact arithmetic"; review of round 627, finding 1. Round
629: `quadfit` named; review of round 628, finding 4.)

The route of SIEVE-ROUTE.md §§19–22 proves Linnik's theorem with exponent `L` from three checks on a window
`[w₁, w₂]` (`m = w·L`): the window condition `WindowOKHM g L m₁ m₂ (1/1000) (1/1000)`, which the window files prove
by `norm_num` at the corners of each piece; the grid's and route's conditions `GridOK`, `Fits` and `RouteOK` (by
`decide` and `norm_num`, as in `Linnik225C.lean`); and the certificate's `total < K` on the grid
(`external/pnt/SieveCertDefs.lean`), which the kernel checks by `decide +kernel` (`SieveMain.linnik_route_lt`).
This script computes the three for a curve, an exponent and a grid size `n`, without Lean:

* `window`: the Halász–Montgomery window by round 621's sampled scan (`β` at each piece's ends and 400 interior
  points, `m` in steps of `1/20000` over `[0.30L, 0.52L]`, `w ∈ {0, 4·10⁻⁶}`, the margin `1/25000`), the longest
  passing run of `m`, its ends `m/L` rounded to five decimals;
* `corners`: every corner inequality of the window files in exact rationals (round 623's check): each piece below
  `5/6` by orthogonality (T1) at `β ∈ {lo, hi}`, `w ∈ {0, 4·10⁻⁶}` and the window's ends and `1`; the top piece
  `[5/6, 11/12]` by `windowPieceHM_const_split`'s three families. If a corner at an end fails, that end moves inward
  by `10⁻⁵` until none fails; the row records the ends used. (Round 629: `corners` also takes a window with
  `m₁ ≥ 1`, which `WindowOKHM` allows: there the inequalities for `m ≥ 1`, at `m₁` and `m₂`, and at `m₁ = 1` those
  for `m ≤ 1` at `m = 1` too; review of round 628, finding 2. Round 630: retracted, false when written: "there only
  the inequalities for `m ≥ 1`"; review of round 629, finding 4; marked as a retraction in round 632, review of round
  625, F7.);
* `replay`: `SieveCertDefs.lean`'s `total` on the grid `U1 = ⌈w₁·DEN⌉`, `U2 = ⌊w₂·DEN⌋`, `n`, in exact integers
  (`cdiv`, `omK`, `bound2`, `bound4`, `cand`, `allowed`, `refcost`, `dec`, `cost` as there; natural subtraction
  truncated at `0`, division by `0` giving `0`), and `GridOK`, `Fits` and `RouteOK` as `decide` would evaluate them.

A row with `total < K`, no failed corner and every grid and route condition true (`accepted`) is a certificate that
`SieveMain.linnik_route_lt` takes, with the curve's counts (`counts_U`; `counts_7c` under `CGLDensity`), which do not
depend on `L`: what remains is the kernel's run of `norm_num` at the corners and `decide +kernel` on the total, which
this script does not make. Lean's kernel has accepted each part of rounds 623 and 625 that it has run, with bounds
about `0.1%` above the parts from earlier replays of the same definitions, whose totals this script reproduces:
`math.ceil(part * 1.001)` in double precision for round 623's, `⌈1.001 × part⌉` exactly for round 625's. (Round 627:
it read "with bounds `⌈1.001 × part⌉`", false for round 623's; review of round 626, F2.)

Curves, parsed from the Lean sources: `gU` (`SieveTypeIIU232.lean`, with no hypothesis) and `g7c`
(`SieveTypeIIU226C.lean`, under `LinnikCGL.CGLDensity`).

Usage:
  route_limits.py run OUT.jsonl CURVE L N [N ...]   window, corners and replay at each N; rows already in OUT reused
  route_limits.py fit OUT.jsonl                     per (curve, L) with three or more N: loss(N) ≈ a + c/N
  route_limits.py floor CURVE [LO HI A ...]         the exact floor L* (with decimals rounded down and up); the least
                                                    L = k/10⁴ with a sampled window; with LO HI A, the pieces inside
                                                    [LO, HI] take the exponent A
  route_limits.py holdout OUT.jsonl CURVE L N       the fits without the row at N, evaluated at N, against that row
  route_limits.py quadfit OUT.jsonl                 per (curve, L) with four or more N: loss(N) ≈ a + c/N + d/N², exact
  route_limits.py windows CURVE L                   all the windows [W1, W2]/10⁵ whose exact corners pass, with
                                                    m₁ < 1 < m₂ and with m₁ ≥ 1 (round 629: it searched W₁ and W₂
                                                    within 40 of 10⁵/L, for m₁ < 1 only)
  route_limits.py parts NAME W1 W2 DW N             each committed part file `external/pnt/NAME{k}.lean` of the grid
                                                    [W1/DW, W2/DW] with N cells: its parts' depth-4 tests and work
  route_limits.py corners CURVE L W1 W2 D           the exact corners of the one window [W1/D, W2/D] at L, against L*

`fit` is an extrapolation, not a certificate: `a` (all grids, least squares) and `a₂` (the two largest grids) estimate
the loss as `N → ∞`, and `c/(1 − a)` is the `N` at which the fitted line crosses `1`. `L` is given as a decimal or a
fraction (`9/4`) and stored as a fraction.

`floor`'s exact floor: `Fits` gives `DEN < L·U2 < L·w₂·DEN`, so `m₂ > 1`, where `WindowOKHM` has only its orthogonality
branch; at `m = m₂` that branch is `(L − m₂)(1 − β − w) ≥ g(β)/2 + 1/25000`, so every window that `Fits` and
`WindowOKHM` accept has `L > L* = 1 + sup (g(β)/2 + 1/25000)/(1 − β − 4·10⁻⁶)` over `1/2 ≤ β ≤ 11/12`. On each piece
the quotient grows with `β`, so its supremum there is its value at the piece's right end (Lean's `if σ < hi` gives `hi`
itself to the next piece). (Round 627; review of round 626, F4. Round 628: it read "max" and "`β ≤ 11/12`"; review of
round 627, out-of-scope observation O-2.)
"""
import json, os, re, sys, time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
PNT = os.path.join(HERE, '..', '..', 'external', 'pnt')
CURVES = {'gU': ('SieveTypeIIU232.lean', 'gU'), 'g7c': ('SieveTypeIIU226C.lean', 'g7c')}
DELTA = EPS = Fr(1, 1000)
MARGIN = Fr(1, 25000)
WS = (Fr(0), Fr(4, 10 ** 6))


def parse(curve):
    """The pieces `(lo, hi, A)` of the curve on `[1/2, 11/12]`: `A = None` for the count `1`, else `A·(1 − σ)`."""
    fn, name = CURVES[curve]
    t = open(os.path.join(PNT, fn), encoding='utf-8').read()
    i = t.index(f'def {name} (σ : ℝ) : ℝ :=')
    body = t[i:t.index('\n\n', i)]
    pieces, lo = [], Fr(1, 2)
    for m in re.finditer(r'if σ < (\d+) / (\d+) then (?:(1)|\((\d+) / (\d+)\) \* \(1 - σ\)) else', body):
        hi = Fr(int(m.group(1)), int(m.group(2)))
        A = None if m.group(3) else Fr(int(m.group(4)), int(m.group(5)))
        pieces.append((lo, hi, A))
        lo = hi
    last = re.findall(r'else\s*\n\s*\((\d+) / (\d+)\) \* \(1 - σ\)\s*$', body)
    assert lo == Fr(5, 6) and last == [('101', '50')], (curve, lo, last)
    pieces.append((lo, Fr(11, 12), Fr(101, 50)))
    return pieces


def window(pieces, L):
    """Round 621's sampled scan of the window (floats); `None` if no `m` passes."""
    import numpy as np
    bs, gs = [], []
    for lo, hi, A in pieces:
        b = np.linspace(float(lo), float(hi), 402)
        bs.append(b)
        gs.append(np.ones_like(b) if A is None else float(A) * (1 - b))
    b, g = np.concatenate(bs), np.concatenate(gs)
    L = float(L)
    marg, d, e = float(MARGIN), float(DELTA), float(EPS)
    ms = np.arange(0.30 * L, 0.52 * L, 1 / 20000)
    ok = np.ones(len(ms), dtype=bool)
    for k, m in enumerate(ms):
        for w in (0.0, 4e-6):
            base = (L - m) * (b + w) + g / 2
            E = base + ((1 + m) / 2 if m <= 1 else m)
            if m <= 1:
                B = 5 / 12 + m / 12 + d * (1 - m) + 2 * e
                E = np.minimum(E, base + m / 2 + np.maximum(m, g + B) / 2)
            if (E > L - marg).any():
                ok[k] = False
                break
    runs, start = [], None
    for i, o in enumerate(list(ok) + [False]):
        if o and start is None:
            start = i
        if not o and start is not None:
            runs.append((start, i - 1))
            start = None
    if not runs:
        return None
    a, z = max(runs, key=lambda r: r[1] - r[0])
    return round(ms[a] / L, 5), round(ms[z] / L, 5)


def corners(pieces, L, W1, W2, D=100000):
    """Every corner inequality of the window `[W1/D, W2/D]`, exact: on each piece and at its ends, the inequality for
    `m ≤ 1` at the ends of `[m₁, 1]` when `m₁ ≤ 1`, and the one for `m ≥ 1` at the ends of `[max(m₁, 1), m₂]` (`Fits`
    gives `m₂ > 1`; round 629: `m₁ ≥ 1` allowed). Returns (failures as (end, tag), least slack, its tag)."""
    m1, m2 = Fr(W1, D) * L, Fr(W2, D) * L
    assert m1 < m2 and 1 < m2, (float(m1), float(m2))
    lo_ms, hi_ms = ((m1, Fr(1)) if m1 <= 1 else ()), (max(m1, Fr(1)), m2)
    E = L - MARGIN
    fails, worst = [], [None, None]

    def chk(tag, m, val):
        s = E - val
        if worst[0] is None or s < worst[0]:
            worst[0], worst[1] = s, tag
        if s < 0:
            fails.append(('lo' if m == m1 else 'hi' if m == m2 else 'one', tag))

    for lo, hi, A in pieces[:-1]:
        p, a = (Fr(1), Fr(0)) if A is None else (A, A)
        for b in (lo, hi):
            for w in WS:
                for m in lo_ms:
                    chk(('T1', str(lo), str(hi), str(b), str(m), str(w)), m,
                        (L - m) * (b + w) + (p - a * b) / 2 + (1 + m) / 2)
                for m in hi_ms:
                    chk(('T1', str(lo), str(hi), str(b), str(m), str(w)), m, (L - m) * (b + w) + (p - a * b) / 2 + m)
    lo, hi, A = pieces[-1]
    for b in (lo, hi):
        for w in WS:
            for m in lo_ms:
                base = (L - m) * (b + w) + (A - A * b) / 2 + m / 2
                chk(('HM1', str(b), str(m), str(w)), m, base + m / 2)
                chk(('HM2', str(b), str(m), str(w)), m,
                    base + ((A - A * b) + (Fr(5, 12) + m / 12 + DELTA * (1 - m) + 2 * EPS)) / 2)
            for m in hi_ms:
                chk(('HM3', str(b), str(m), str(w)), m, (L - m) * (b + w) + (A - A * b) / 2 + m)
    return fails, worst[0], worst[1]


def encl(x, k=7):
    """`x > 0` between its decimals of `k` places rounded down and up (round 629: a bound is displayed by the decimal on
    its safe side; review of round 628, finding 1)."""
    s, lo, hi = 10 ** k, (x * 10 ** k).__floor__(), (x * 10 ** k).__ceil__()
    return f'{lo // s}.{lo % s:0{k}d}', f'{hi // s}.{hi % s:0{k}d}'


def floor_q(pieces):
    """`L* − 1`, the supremum of the quotient over the pieces' right ends (the module docstring), and its arguments."""
    qv = {phi: ((Fr(1) if A is None else A * (1 - phi)) / 2 + MARGIN) / (1 - phi - WS[1]) for _, phi, A in pieces}
    q = max(qv.values())
    return q, [b for b, v in qv.items() if v == q]


DEN, K = 2 ** 40, 2 ** 60
TOPK = (K * 5672 + 9999) // 10000


def tsub(a, b):
    return a - b if a > b else 0


def cdiv(a, b):
    return 0 if b == 0 else (a + b - 1) // b


def subset_sums(xs):
    if not xs:
        return [(0, 0)]
    rest = subset_sums(xs[1:])
    p = xs[0]
    return rest + [(s[0] + p[0], s[1] + p[1]) for s in rest]


def replay(U1, U2, n, per_row=False):
    """`SieveCertDefs.lean`'s `total` and the grid's conditions; counts of candidates, decompositions and tests; with
    `per_row`, also each row's tests, candidates and decomposed cells of depth 4."""
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

    total = 0
    cnt = dict(cands=0, allowed=0, dec=0, tested4=0, d4_dec=0)
    per = [dict(tests=0, cands=0, d4_dec=0) for _ in range(n)]
    for i in range(n):
        for j in range(n):
            ei, ej = e(i), e(j)
            if not (ej < ei + H and 2 * ei < DEN and ei + 2 * ej <= DEN and not (U1 < ei and ei + H < U2)
                    and not surely([cell(i), cell(j)])):
                continue
            cnt['cands'] += 1
            per[i]['cands'] += 1
            b2 = cdiv(H * H * DEN * omK(ei, ej, 2), ei * ej * ej)
            ks = [k for k in range(n) if e(k) < ej + H and ei + ej + 2 * e(k) <= DEN
                  and not surely([cell(i), cell(j), cell(k)])]
            if not (ei + H + (ej + H) < lim and all(ei + H + (ej + H) + (e(k) + H) < lim for k in ks)):
                total += b2
                continue
            cnt['allowed'] += 1
            ref = d4 = 0
            for k in ks:
                ek = e(k)
                for l in range(k + 1):
                    el = e(l)
                    if ei + ej + ek + 2 * el <= DEN:
                        cnt['tested4'] += 1
                        per[i]['tests'] += 1
                        if not surely([cell(i), cell(j), cell(k), cell(l)]):
                            d4 += 1
                            ref += cdiv(H ** 4 * DEN * omK(ei + ej + ek, el, 4), ei * ej * ek * el * el)
            if ref <= b2:
                cnt['dec'] += 1
                cnt['d4_dec'] += d4
                per[i]['d4_dec'] += d4
                total += ref
            else:
                total += b2
    gridok = dict(H_pos=0 < H, U1_lt_U2=U1 < U2, two_U2_lt=2 * U2 < DEN, two_e_lt=2 * e(n - 1) < DEN,
                  four_H_le_V=4 * H <= V, DEN_lt_top=DEN < 2 * (V + n * H))
    return (total, cnt, gridok, per) if per_row else (total, cnt, gridok)


def frac(s):
    return Fr(s)


def rows_of(out):
    return [json.loads(l) for l in open(out, encoding='utf-8')] if os.path.exists(out) else []


def cmd_run(out, curve, Ls, ns):
    L = frac(Ls)
    have = {(r['curve'], r['L'], r['n']) for r in rows_of(out)}
    pieces = parse(curve)
    w = None
    for n in ns:
        if (curve, str(L), n) in have:
            print(f'{curve} L={L} n={n}: reused', flush=True)
            continue
        if w is None:
            w = window(pieces, L)
            if w is None:
                print(f'{curve} L={L}: no window', flush=True)
                return
            W1, W2 = round(w[0] * 100000), round(w[1] * 100000)
            moves = 0
            while True:
                fails, slack, tag = corners(pieces, L, W1, W2)
                if not fails:
                    break
                ends = {f[0] for f in fails}
                assert 'one' not in ends, fails[:3]
                W1 += 'lo' in ends
                W2 -= 'hi' in ends
                moves += 1
                assert moves <= 50, (W1, W2)
        U1, U2 = (W1 * DEN + 99999) // 100000, W2 * DEN // 100000
        fits = dict(lo=W1 * DEN < 100000 * U1, hi=100000 * U2 < W2 * DEN, top=L.denominator * DEN < L.numerator * U2)
        route = dict(two_lt_L=2 < L, L_le=L <= Fr(5, 2), w=0 < W1 < W2 < 100000)
        t0 = time.time()
        total, cnt, gridok = replay(U1, U2, n)
        row = dict(curve=curve, L=str(L), n=n, W1=W1, W2=W2, scan=list(w), corner_moves=moves,
                   least_slack=float(slack), least_slack_at=list(tag), U1=U1, U2=U2, total=total,
                   total_over_K=total / K, lt_K=total < K, counts=cnt, gridok=gridok, fits=fits, route=route,
                   accepted=total < K and all(gridok.values()) and all(fits.values()) and all(route.values()),
                   secs=round(time.time() - t0))
        with open(out, 'a', encoding='utf-8') as f:
            f.write(json.dumps(row) + '\n')
        print(f'{curve} L={L} n={n} window [{W1}, {W2}]/1e5 (moves {moves}, slack {float(slack):.2e}): '
              f'total/K {total / K:.5f} accepted {row["accepted"]} tests {cnt["tested4"]} ({row["secs"]}s)',
              flush=True)


def fits(rows):
    """Per (curve, L) with three or more grids: `a`, the least-squares line in `1/N` through every grid, and `a₂`, the
    line through the two largest grids, each an estimate of the loss as `N → ∞`; and per curve and estimate, the `L`
    at which it crosses `1`, linear in `L` between the two computed exponents around the crossing."""
    by = {}
    for r in rows:
        by.setdefault((r['curve'], Fr(r['L'])), {})[r['n']] = r['total_over_K']
    out, cross = [], []
    for (curve, L), pts in sorted(by.items()):
        ns = sorted(pts)
        d = dict(curve=curve, L=L, pts=[(n, pts[n]) for n in ns])
        if len(ns) >= 3:
            xs, ys = [1 / n for n in ns], [pts[n] for n in ns]
            mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
            c = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
            a = my - c * mx
            c2 = (ys[-2] - ys[-1]) / (xs[-2] - xs[-1])
            d.update(a=a, c=c, resid=max(abs(y - a - c * x) for x, y in zip(xs, ys)), a2=ys[-1] - c2 * xs[-1], c2=c2)
        out.append(d)
    for curve in sorted({d['curve'] for d in out}):
        al = [d for d in out if d['curve'] == curve and 'a' in d]
        for k in ('a', 'a2'):
            for d0, d1 in zip(al, al[1:]):
                v0, v1 = d0[k], d1[k]
                if (v0 - 1) * (v1 - 1) <= 0 and v0 != v1:
                    cross.append(dict(curve=curve, est=k, L0=d0['L'], L1=d1['L'],
                                      L=d0['L'] + (d1['L'] - d0['L']) * Fr(1 - v0) / Fr(v1 - v0)))
    return out, cross


def cmd_fit(out):
    """Print `fits`: neither estimate is a certificate, and their spread is no error bound (see `quadfit`). (Round 628:
    retracted, false when written: "their spread shows how far the model `a + c/N` is from exact"; review of round
    627, finding 1.)"""
    res, cross = fits(rows_of(out))
    for d in res:
        line = ', '.join(f'{n}: {v:.5f}' for n, v in d['pts'])
        if 'a' not in d:
            print(f"{d['curve']} L={float(d['L']):.4f}: {line} (fewer than three grids, no fit)")
            continue
        n1 = d['c'] / (1 - d['a']) if d['a'] < 1 else float('inf')
        n12 = d['c2'] / (1 - d['a2']) if d['a2'] < 1 else float('inf')
        print(f"{d['curve']} L={float(d['L']):.4f}: {line}; a = {d['a']:.4f} (c = {d['c']:.1f}, max residual "
              f"{d['resid']:.4f}), a₂ = {d['a2']:.4f} (c₂ = {d['c2']:.1f}); a + c/N = 1 at N = {n1:.0f}, "
              f"a₂ + c₂/N = 1 at N = {n12:.0f}")
    for x in cross:
        print(f"{x['curve']}: {'a' if x['est'] == 'a' else 'a₂'}(L) crosses 1 between L = {float(x['L0']):.4f} and "
              f"{float(x['L1']):.4f}, at about {float(x['L']):.4f} (linear in L)")


def cmd_floor(curve, over=()):
    """The exact floor `L*` (the module docstring's argument), and the least `L = k/10⁴` in `[2.10, 2.30]` at which the
    sampled window is nonempty (bisection on `k`, the window growing with `L`), with that window's exact corners. With
    `over`, triples `(LO, HI, A)`: every piece inside `[LO, HI]` first takes the exponent `A` (a curve that is not
    committed, to measure what a lower density exponent there would move)."""
    pieces = parse(curve)
    for lo_, hi_, A_ in over:
        pieces = [(lo, hi, A_ if lo_ <= lo and hi <= hi_ else A) for lo, hi, A in pieces]
    amax = max(A for _, _, A in pieces if A is not None)
    at = [f'[{plo}, {phi}]' for plo, phi, A in pieces if A == amax]
    q, arg = floor_q(pieces)
    name = curve + ''.join(f' with A = {A_} on [{lo_}, {hi_}]' for lo_, hi_, A_ in over)
    # round 632: one label for all the arguments, 'attained' when 11/12 was among them; review of round 625, O1
    kind = lambda b: 'attained' if b == pieces[-1][1] else 'a left limit'  # only the top piece's end is in the window
    print(f'{name}: the exact floor L* = 1 + sup (g/2 + 1/25000)/(1 - b - 4e-6) = {1 + q}, between '
          f'{" and ".join(encl(1 + q))}, at b = {", ".join(f"{b} ({kind(b)})" for b in arg)}; A_max = {amax} on '
          f'{", ".join(at)}, 1 + A_max/2 = {1 + amax / 2}, between {" and ".join(encl(1 + amax / 2))}', flush=True)
    lo, hi = 21000, 23000
    assert window(pieces, Fr(lo, 10000)) is None and window(pieces, Fr(hi, 10000)) is not None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if window(pieces, Fr(mid, 10000)) is None:
            lo = mid
        else:
            hi = mid
    L = Fr(hi, 10000)
    w = window(pieces, L)
    W1, W2 = round(w[0] * 100000), round(w[1] * 100000)
    m1, m2 = Fr(W1, 100000) * L, Fr(W2, 100000) * L
    head = f'  the sampled window is empty at L = {lo / 10000} and nonempty at {hi / 10000}: [{W1}, {W2}]/1e5'
    if m1 < m2 and 1 < m2:
        fails, slack, _ = corners(pieces, L, W1, W2)
        print(f'{head}, its exact corners {"pass" if not fails else "FAIL"} (least slack {float(slack):.2e})')
    else:  # round 630: it asked m1 < 1 < m2; review of round 629, out-of-scope observation O1
        print(f'{head}, with m1 = {float(m1):.7f}, m2 = {float(m2):.7f}: not m1 < m2 with m2 > 1 (Fits needs m2 > 1)')


def cmd_holdout(out, curve, Ls, n):
    """The fits at (curve, L) without the row at `n`, evaluated at `n`, against that row: an out-of-sample test."""
    L = frac(Ls)
    rows = rows_of(out)
    keep = [r for r in rows if not (r['curve'] == curve and Fr(r['L']) == L and r['n'] == n)]
    assert len(keep) == len(rows) - 1, 'no such row'
    d = [d for d in fits(keep)[0] if d['curve'] == curve and d['L'] == L][0]
    if 'a' not in d:
        sys.exit(f'{curve} L={L}: fewer than three grids remain without n={n}; no fit')
    act = [r['total_over_K'] for r in rows if r['curve'] == curve and Fr(r['L']) == L and r['n'] == n][0]
    print(f"{curve} L={L} without n={n} (grids {[m for m, _ in d['pts']]}): a + c/n = {d['a'] + d['c'] / n:.5f}, "
          f"a₂ + c₂/n = {d['a2'] + d['c2'] / n:.5f}; the replay at n = {n}: {act:.5f}")


def cmd_quadfit(out):
    """Per (curve, L) with four or more grids: the least-squares fit of `total/K` by `a + c/N + d/N²`, in exact
    rationals (`total` and `K` are integers), against `fits`'s `a` and `a₂`: the spread of `a` and `a₂` is no error
    bound when the intercept falls outside it."""
    rows = rows_of(out)
    by = {}
    for r in rows:
        by.setdefault((r['curve'], Fr(r['L'])), {})[r['n']] = Fr(r['total'], K)
    lin = {(d['curve'], d['L']): d for d in fits(rows)[0] if 'a' in d}
    for (curve, L), pts in sorted(by.items()):
        if len(pts) < 4:
            continue
        X = [[Fr(1), Fr(1, n), Fr(1, n * n)] for n in sorted(pts)]
        y = [pts[n] for n in sorted(pts)]
        A = [[sum(X[k][i] * X[k][j] for k in range(len(X))) for j in range(3)] for i in range(3)]
        b = [sum(X[k][i] * y[k] for k in range(len(X))) for i in range(3)]
        for i in range(3):  # Gauss–Jordan on the normal equations, exact
            piv = A[i][i]
            A[i] = [v / piv for v in A[i]]
            b[i] = b[i] / piv
            for j in range(3):
                if j != i and A[j][i] != 0:
                    f = A[j][i]
                    A[j] = [vj - f * vi for vj, vi in zip(A[j], A[i])]
                    b[j] = b[j] - f * b[i]
        d = lin[(curve, L)]
        lo, hi = sorted((d['a'], d['a2']))
        print(f"{curve} L={float(L):.4f} (grids {sorted(pts)}): a + c/N + d/N² intercept {float(b[0]):.5f}; "
              f"a = {d['a']:.5f}, a₂ = {d['a2']:.5f}; inside [a, a₂]: {lo <= float(b[0]) <= hi}")


def cmd_windows(curve, Ls):
    """All the windows `[W1, W2]/10⁵` whose exact corners pass (`corners`), `Fits` asking `m₂ > 1`. Each corner
    inequality is affine in `m` and is also checked at `m = 1` when the window contains it, so with `c` the largest `W`
    with `W·L < 10⁵` and `d` the least with `W·L > 10⁵`: the windows with `m₁ < 1 < m₂` that pass are those with `W1`
    in an interval ending at `c` and `W2` in one starting at `d` (none if `[c, d]` fails), and the windows with
    `m₁ ≥ 1` that pass are the pairs `W1 < W2` from `e = ⌈10⁵/L⌉` up to the largest `W2` for which `[e, W2]` passes (for
    `m ≥ 1` each inequality bounds `m` above). The intervals' ends are found by bisection with `corners`. (Round 629:
    it searched `W1` and `W2` within 40 of `10⁵/L`, for `m₁ < 1` only; review of round 628, findings 2 and 4.)"""
    L = frac(Ls)
    pieces = parse(curve)
    e = (100000 / L).__ceil__()
    c, d = e - 1, (e + 1 if e * L == 100000 else e)
    ok = lambda W1, W2: not corners(pieces, L, W1, W2)[0]

    def last(good, lo, hi):  # the last x in [lo, hi] with good(x), good holding on an initial run from lo
        while lo < hi:
            mid = (lo + hi + 1) // 2
            lo, hi = (mid, hi) if good(mid) else (lo, mid - 1)
        return lo

    nA, A = 0, ''
    if ok(c, d):
        a = c - last(lambda t: ok(c - t, d), 0, c - 1)
        b = last(lambda W2: ok(c, W2), d, 99999)
        nA, A = (c - a + 1) * (b - d + 1), f'W1 in [{a}, {c}], W2 in [{d}, {b}]'
    nB, B = 0, ''
    if ok(e, e + 1):
        top = last(lambda W2: ok(e, W2), e + 1, 99999)
        nB, B = (top - e + 1) * (top - e) // 2, f'{e} <= W1 < W2 <= {top}'
    lst = []
    if nA + nB <= 20:
        if nA:
            lst += [(x, y) for x in range(a, c + 1) for y in range(d, b + 1)]
        if nB:
            lst += [(x, y) for x in range(e, top + 1) for y in range(x + 1, top + 1)]
        assert all(ok(x, y) for x, y in lst)
    print(f'{curve} L={L} = {float(L):.7f}: {nA} windows with m1 < 1 < m2 pass their exact corners'
          + (f' ({A})' if nA else '') + f', and {nB} with m1 >= 1' + (f' ({B})' if nB else '')
          + (f": {', '.join(f'[{x}, {y}]' for x, y in lst)}" if lst else ''))


def cmd_parts(name, W1, W2, DW, n):
    """Each committed part file `external/pnt/{name}{k}.lean`, k = 1, 2, …, of the grid `[W1/DW, W2/DW]` with `n`
    cells: per file, the part with the most depth-4 tests (its tests and work) and the part with the most work (its
    work and tests), work being candidate cells plus decomposed cells of depth 4 (`replay`'s per-row counts)."""
    U1, U2 = (W1 * DEN + DW - 1) // DW, W2 * DEN // DW
    _, _, _, per = replay(U1, U2, n, per_row=True)
    k = 1
    while os.path.exists(os.path.join(PNT, f'{name}{k}.lean')):
        src = open(os.path.join(PNT, f'{name}{k}.lean'), encoding='utf-8').read()
        rg = [(int(a), int(b)) for a, b in re.findall(r'theorem \S+ : rows (\d+) (\d+) ≤', src)]
        T = [sum(per[i]['tests'] for i in range(a, b)) for a, b in rg]
        Wk = [sum(per[i]['cands'] + per[i]['d4_dec'] for i in range(a, b)) for a, b in rg]
        it, iw = max(range(len(rg)), key=lambda x: T[x]), max(range(len(rg)), key=lambda x: Wk[x])
        print(f'{name}{k}: {len(rg)} parts; most tests: rows {rg[it][0]}–{rg[it][1] - 1}, {T[it]} tests, '
              f'work {Wk[it]}; most work: rows {rg[iw][0]}–{rg[iw][1] - 1}, work {Wk[iw]}, {T[iw]} tests')
        k += 1


def cmd_corners(curve, Ls, W1, W2, D):
    """The exact corners (`corners`) of the one window `[W1/D, W2/D]` at `L`, with `m₁`, `m₂` and `L − L*` (round 628:
    windows between `L*` and its decimals rounded up)."""
    L = frac(Ls)
    pieces = parse(curve)
    q, _ = floor_q(pieces)
    m1, m2 = Fr(W1, D) * L, Fr(W2, D) * L
    fails, slack, _ = corners(pieces, L, W1, W2, D)
    print(f'{curve} L={L} = {float(L):.10f} (L* = {1 + q}, between {" and ".join(encl(1 + q))}; L - L* = '
          f'{float(L - 1 - q):.3e}): window [{W1}, {W2}]/{D}, m1 = {float(m1):.10f}, m2 = {float(m2):.10f}: its exact '
          f'corners {"pass" if not fails else "FAIL"} (least slack {float(slack):.3e})')


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'run':
        cmd_run(a[1], a[2], a[3], [int(x) for x in a[4:]])
    elif a[0] == 'fit':
        cmd_fit(a[1])
    elif a[0] == 'floor':
        cmd_floor(a[1], [tuple(frac(x) for x in a[k:k + 3]) for k in range(2, len(a), 3)])
    elif a[0] == 'holdout':
        cmd_holdout(a[1], a[2], a[3], int(a[4]))
    elif a[0] == 'quadfit':
        cmd_quadfit(a[1])
    elif a[0] == 'windows':
        cmd_windows(a[1], a[2])
    elif a[0] == 'parts':
        cmd_parts(a[1], int(a[2]), int(a[3]), int(a[4]), int(a[5]))
    elif a[0] == 'corners':
        cmd_corners(a[1], a[2], int(a[3]), int(a[4]), int(a[5]))
    else:
        sys.exit(__doc__)
