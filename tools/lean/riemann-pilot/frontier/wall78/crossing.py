"""The slice's crossing cost and the low side, from the release's proofs (README round 500).

Source: The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex in github.com/openai/math (family 003; the tree
read here is commit adc7f1241). Line numbers below are that file's.

The row-norm exponent. The proof of Lemma probe-row-norm (lines 8124-8332) bounds each dyad by the energy of Lemma
reflected-energy (line 7747, eqs. old-eq:4.4, old-eq:4.6 and old-eq:4.7):
    E = O/2 + max(H, v + l_b) - S0 - B0 + z_a - u - l_b - 2e/3 - (T - y)_+/2,
    T = 2H + 2A0 + 2z_a - N_* - N0 - 3B0,   y = v + 3l_b + e <= T (a retained dyad),   u = min(v, z_a, (v + z_a)/3),
with N_* = 1 + ell' (line 8187, theta_N = 0) and the proof's constraints H <= M' - O (line 8223), 2A0 <= O and
z_a <= ell' (line 8240), S0 + N0 + B0 <= A0 (disjoint parts of the active primes, lines 7708-7715), all lengths >= 0,
the epsilons dropped. Its bound is the maximum of E over the dyads: the largest of six linear programs, one for each
piece of max(H, v + l_b) and of -u. In any geometry (M' = M - 2d, ell' = ell - d, eq. old-eq:5.2) that maximum is
    M' + max(0, M' + ell' - 1, (1 + 3 ell' - 2M')/4)       when M' >= (1 - ell')/2 (otherwise no dual dyad is retained).
[Scope, 2026-10-22 (frontier/rank/FIVE-SIXTHS.md section 9.4, O2): gate X1 samples ell' <= 0.3 only.  The formula
holds wherever M' >= 2 ell' (gate S7 of frontier/rank/slotsplit.py), which every low side satisfies; at (M', ell') =
(0.6181, 0.9935) the maximum exceeds it by 0.178, through a branch with v + l_b > H.]
The middle term is the first branch (u = z_a), where v + l_b exceeds H. There the whole excess is the column term NB of
the factor K + NB in Lemma hybrid-energy (line 7510, eq. old-eq:4.6b; K = Z^H, N = Z^v, B = Z^{l_b}). The last term is
the second branch (line 8306). Since M' + ell' - 1 = M + ell - 1 - 3d, the first branch charges (M + ell - 1 - 3d)_+:
nothing inside the slice, and (M + ell - 1)_+ at tuple size d = 0. Proposition probe-low (line 8564) takes half of the
row exponent by Cauchy-Schwarz, and its tuple sum adds -d (eq. old-eq:5.5); every piece then falls with d, so the low
side is taken at d = 0, where crossing the slice costs (M + ell - 1)_+/2: c = 1 on the first branch, nothing on the
second.

Round 496's model (exponent_lp.py, used by offslice.py) adds c mu/2 to all six low rows, the row-loss rows included.
Charged on the first branch only, as derived here, it changes nothing under Sang's range, where the loss vanishes across
the slice; with round 498's rows alone the break-even with the Gram term moves from 1/30 to 1/18.

The low side as a lever. A lower low side alone moves round 498's limits 13/15 and 31/36, on the slice and with the rows
near a = 1/2 unchanged; so does a lower C0 wall for 31/36. Every number here is a statement about this exponent system,
not a theorem.

Gates (exit status 1 if any fails):
  X1  the maximum of E over the dyads at 400 random (M', ell'): no retained dyad exactly when M' < (1 - ell')/2, and
      otherwise the formula above within 1e-9; without the kernel term the maximum is larger, without the retention
      condition unbounded
  X2  on the slice M + ell = 1 the formula is M' + (5 ell + d - 1)_+/4, Sang's L_ell(d), for ell in [1/6, 1/5] and
      d in [0, ell]; at ell = 1/6 it is the lemma's exponent M' + ((d - 1/6)/4)_+ (exact arithmetic on a grid)
  X3  in exact arithmetic: the first-branch dyad (O = 0, H = M', z_a = ell', v = T, the rest 0) gives
      M' + (M' + ell' - 1); the second-branch dyad (H = (1 - ell')/2, O = M' - H, z_a = ell', T = 0, the rest 0) gives
      M' + (1 + 3 ell' - 2M')/4; and the release's identity v + z_a - u = max(v, z_a, 2(v + z_a)/3) holds
  X4  at the first-branch dyad, E is the sum of the exponents of Lemma hybrid-energy's factors K + NB and
      B{N + L + (NL)^{2/3}}, the coefficient factor (line 7931) and the kernel term, and log(K + NB) - log K is the
      whole excess M' + ell' - 1 (exact)
  X5  the low side's tuple exponent l_x/2 + G(d)/2 + X(d)/2 - d, with the Gram pieces G(d) = max(0, theta b,
      2b - l_y + d) and the excess X(d) of the formula, is largest at d = 0 at 2000 random geometries
  X6  the crossing cost on the first branch only: (i) the obstruction under the rows every configuration keeps is
      round 499's table; (ii) with round 498's rows alone the break-evens are 1/18 with the Gram term (round 496's
      model: 1/30) and 2/15 without it; (iii) round 496's break-even in the release's system stays in (0.15, 0.16);
      (iv) the fifteen configurations across the slice at c = 1 and c = 0 keep round 499's values within 2e-6
  X7  the low side lowered by s: (i) round 498's obstruction gives 13/15 - 4s/5 and 31/36 - 5s/6; (ii) under the kept
      rows on the slice, 13/15 - 4s/5 and 31/36 - 2s/3 for s <= 1/24, both 5/6 at s = 1/24; (iii) the C0 wall lowered
      by t instead gives 31/36 - t/6 and leaves 13/15; (iv) on the slice Lindelof + all readings at s = 1/100 gives
      0.8587858, below 31/36, with the same walls, and Sang's inputs at s = 1/200 and s = 10 give 0.8745077, with the
      high side's bins among the walls and the low side not
"""
import sys
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog
from concurrent.futures import ProcessPoolExecutor
import offslice as O
import levers as LV
import exponent_lp as EX

HIGHS = O.HIGHS
# dyad data w = (O, H, A0, N0, S0, B0, z_a, v, l_b, e)
TY = np.array([0, 2, 2, -1, 0, -3, 2, -1, -3, -1], float)          # (T - y) + N_*
BASE = np.array([0.5, 0, 0, 0, -1, -1, 1, 0, -1, -2 / 3])            # O/2 + z_a - S0 - B0 - l_b - 2e/3
UNIT = np.eye(10)
P1 = (UNIT[1], UNIT[7] + UNIT[8])                                     # max(H, v + l_b)
P2 = (-UNIT[7], -UNIT[6], -(UNIT[7] + UNIT[6]) / 3)                   # -u = max(-v, -z_a, -(v + z_a)/3)


def emax(Mp, lp, retention=True, kernel=True):
    """the maximum of E over the dyads; -inf if no dyad is retained, inf if unbounded."""
    A = [[1, 1, 0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 1, 1, 1, 0, 0, 0, 0]]
    b = [Mp, 0.0, 0.0]
    if retention:
        A.append(list(-TY)); b.append(-(1 + lp))
    best = -np.inf
    for p1 in P1:
        for p2 in P2:
            c = BASE + p1 + p2 - (TY / 2 if kernel else 0)
            r = linprog(-c, A_ub=A, b_ub=b, bounds=[(0, None)] * 6 + [(0, lp)] + [(0, None)] * 3, method='highs',
                        options=HIGHS)
            if r.status == 3:
                return np.inf
            if r.status == 0:
                best = max(best, -r.fun + ((1 + lp) / 2 if kernel else 0.0))
    return best


def formula(Mp, lp):
    return Mp + max(0, Mp + lp - 1, (1 + 3 * lp - 2 * Mp) / 4)


def energy(w, lp):
    """old-eq:4.6 at one dyad, in exact arithmetic when w holds Fractions."""
    o, h, a0, n0, s0, b0, za, v, lb, e = w
    T = 2 * h + 2 * a0 + 2 * za - (1 + lp) - n0 - 3 * b0
    y = v + 3 * lb + e
    u = min(v, za, (v + za) / 3)
    return o / 2 + max(h, v + lb) - s0 - b0 + za - u - lb - e * Fr(2, 3) - max(T - y, 0) / 2, T, y


def low_rows_first(theta, cost):
    """round 496's six low rows with the crossing cost on the first branch only (not on the row-loss rows)."""
    return [(n, r[:4] + [0.0 if 'row loss' in n else r[4]], c) for n, r, c in O.low_rows(theta, cost)]


def obstruction(gram, cost, mode, kept=True, soft=False, first_only=True, s=0.0, t=0.0, slice_eq=False):
    """min over the geometry of max(low side - s, C0 wall - t); offslice.obstruction when first_only is False and
    s = t = 0."""
    rows = (low_rows_first if first_only else O.low_rows)(1 / 6 if gram == 'paper' else 0.0, cost)
    A, b = [r for _, r, _ in rows], [c + s for _, _, c in rows]
    A += [[-5 / 6, -1 / 2, 1 / 3, -1, 0], [1, 1, 1, 0, -1], [1, -1, 0, 0, 0]]
    b += [-4 / 3 + t, 1.0, 0.0]
    if not soft:
        A.append([-2, 1, 1, 0, 0] if gram == 'none' else [-11 / 6, 5 / 6, 1, 0, 0]); b.append(0.0)
    if slice_eq:
        A.append([-1, -1, -1, 0, 0]); b.append(-1.0)
    for r, c in (O.KEPT if kept else []):
        A.append(r); b.append(c)
    res = linprog([0, 0, 0, 1, 0], A_ub=A, b_ub=b, bounds=[(0, 1)] * 3 + [(0, 2), (0, 2.0 if mode == 'cross' else 0.0)],
                  method='highs', options=HIGHS)
    return res.fun


def breakeven(gram, kept, soft, base, first_only):
    from scipy.optimize import brentq
    f = lambda c: obstruction(gram, c, 'cross', kept, soft, first_only) - base + 1e-10
    return brentq(f, 0.0, 1.0, xtol=1e-12) if f(0.0) < 0 else None


def obstruction498(gram, s):
    """levers.obstruction (round 498: B(ell) + max(t, C0) over b >= 0, the absorption without the Gram term) with the
    low side lowered by s."""
    Bl, C0 = (11 / 12, 0.0, -1 / 4), (-1 / 4, 1 / 6, 5 / 4)
    tb = -1 / 12 if gram == 'none' else 0.0
    rows = [(Bl[0] - s, tb, Bl[2]), (Bl[0] + C0[0], C0[1], Bl[2] + C0[2])]
    A = [[cb, cl, -1.0] for c, cb, cl in rows]
    rhs = [-c for c, cb, cl in rows]
    if gram == 'none':
        A.append([3.0, 3.0, 0.0]); rhs.append(1.0)
    return linprog([0, 0, 1], A_ub=A, b_ub=rhs, bounds=[(0, None), (None, None), (None, None)], method='highs').fun


class Variant(O.OffSlice):
    """offslice's program with the crossing cost on the first branch only, and the low side lowered by s."""

    def __init__(self, kappa, s=0.0, first_only=True, **kw):
        self.s, self.first_only = s, first_only
        super().__init__(kappa, **kw)

    def fixed_rows(self):
        out = []
        for n, r, b in super().fixed_rows():
            if n.startswith('low:'):
                r = r[:4] + [0.0 if (self.first_only and 'row loss' in n) else r[4]]
                b = b + self.s
            out.append((n, r, b))
        return out


def run_variant(args):
    """offslice.run for the Variant program."""
    cfg, mode, cost, s, first_only = args
    kappa, fp = 3 / 4, []
    for _ in range(O.STAGES):
        if kappa < 13 / 18:
            break
        o = Variant(kappa, s=s, first_only=first_only, mode=mode, cost=cost, **cfg)
        sol = o.solve()
        if sol is None:
            break
        fp.append((kappa, sol, o))
        if abs(2 * sol['v'][3] - 1 - kappa) < 1e-10:
            break
        kappa = 2 * sol['v'][3] - 1
    least = min(sol['v'][3] for _, sol, _ in fp)
    i = max(j for j in range(len(fp)) if fp[j][1]['v'][3] <= least + 1e-7)
    kap, sol, o = fp[i]
    return sol['v'][3], kap, i, len(fp), o.walls(sol), max(x['small'] for _, x, _ in fp)


class ModelFirst(EX.Model):
    """exponent_lp.Model with the crossing cost on the first branch only."""

    def low_rows(self, mu_cost):
        A, b = EX.Model.low_rows(self, mu_cost)
        A = A.copy()
        A[[1, 3, 5], 4] = 0.0          # rows (piece, row loss) for the three Gram pieces
        return A, b


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    rng = np.random.default_rng(500)
    dev, nfeas, ninf, bad = 0.0, 0, 0, 0
    for _ in range(400):
        Mp, lp = rng.uniform(0.3, 1.2), rng.uniform(0, 0.3)
        e = emax(Mp, lp)
        if e == -np.inf:
            ninf += 1
            bad += Mp >= (1 - lp) / 2 - 1e-12
        else:
            nfeas += 1
            bad += Mp < (1 - lp) / 2 - 1e-12
            dev = max(dev, abs(e - formula(Mp, lp)))
    nok = emax(0.8, 0.17, kernel=False)
    noret = emax(0.8, 0.17, retention=False)
    gate('X1', dev < 1e-9 and bad == 0 and nfeas > 300 and nok > formula(0.8, 0.17) + 0.1 and noret == np.inf,
         f'max of E over the dyads = M\' + max(0, M\' + ell\' - 1, (1 + 3 ell\' - 2M\')/4) at {nfeas} random '
         f'geometries '
         f'(max deviation {dev:.1e}); no retained dyad at the other {ninf}, each with M\' < (1 - ell\')/2; sabotage: '
         f'without the kernel term {nok:.4f} > {formula(0.8, 0.17):.4f}, without retention {noret}')

    ok, n = True, 0
    for ell in (Fr(1, 6), Fr(7, 40), Fr(9, 50), Fr(1, 5)):
        for k in range(11):
            d = ell * k / 10
            M = 1 - ell
            Mp, lp = M - 2 * d, ell - d
            f = Mp + max(0, Mp + lp - 1, (1 + 3 * lp - 2 * Mp) / 4)
            ok &= f == Mp + max(Fr(0), 5 * ell + d - 1) / 4
            if ell == Fr(1, 6):
                ok &= f == Mp + max(0, (d - Fr(1, 6)) / 4)
            n += 1
    gate('X2', ok, f'on the slice the formula is M\' + (5 ell + d - 1)_+/4 (Sang\'s L_ell(d)) at {n} grid points, '
                   f'ell in '
                   f'[1/6, 1/5], d in [0, ell]; at ell = 1/6 the lemma\'s M\' + ((d - 1/6)/4)_+ (exact)')

    ok, msgs = True, []
    for Mp, lp in ((Fr(17, 20), Fr(1, 6)), (Fr(9, 10), Fr(3, 20)), (Fr(21, 20), Fr(1, 5)), (Fr(3, 5), Fr(1, 5))):
        z = Fr(0)
        T1 = 2 * Mp + lp - 1
        e1, T, y = energy((z, Mp, z, z, z, z, lp, T1, z, z), lp)
        first = T1 >= 2 * lp
        if first:
            ok &= T == y and e1 == Mp + max(0, Mp + lp - 1)
        h2 = (1 - lp) / 2
        e2, T, y = energy((Mp - h2, h2, z, z, z, z, lp, z, z, z), lp)
        ok &= T == 0 and e2 == Mp + (1 + 3 * lp - 2 * Mp) / 4
        ok &= max(e1 if first else -1, e2, Mp) == Mp + max(0, Mp + lp - 1, (1 + 3 * lp - 2 * Mp) / 4)
        msgs.append(f'({Mp}, {lp}): {e1 if first else "-"} / {e2}')
    for _ in range(500):
        v, za = Fr(int(rng.integers(0, 60)), 40), Fr(int(rng.integers(0, 60)), 40)
        ok &= v + za - min(v, za, (v + za) / 3) == max(v, za, 2 * (v + za) / 3)
    gate('X3', ok, 'first-branch / second-branch dyads at (M\', ell\'): ' + ', '.join(msgs) +
         '; and v + z_a - u = max(v, z_a, 2(v + z_a)/3) at 500 random points (exact)')

    ok = True
    for Mp, lp in ((Fr(17, 20), Fr(1, 6)), (Fr(9, 10), Fr(3, 20)), (Fr(21, 20), Fr(1, 5))):
        z = Fr(0)
        o, h, a0, n0, s0, b0, za, lb, e = z, Mp, z, z, z, z, lp, z, z
        v = 2 * Mp + lp - 1
        E, T, y = energy((o, h, a0, n0, s0, b0, za, v, lb, e), lp)
        sieve = max(h, v + lb)                                   # K + NB
        cubic = lb + max(v, za, 2 * (v + za) / 3)                # B{N + L + (NL)^{2/3}}
        coef = -v - 2 * lb - e * Fr(2, 3) - s0 - b0              # line 7931
        kern = -max(T - y, 0) / 2
        ok &= E == o / 2 + sieve + cubic + coef + kern and E - Mp == sieve - h == max(0, Mp + lp - 1)
    gate('X4', ok, 'at the first-branch dyad E = O/2 + log(K + NB) + log B{N + L + (NL)^(2/3)} + coefficient + kernel, '
                   'and the excess E - M\' is log(K + NB) - log K = (M\' + ell\' - 1)_+ (exact, three geometries)')

    worst = -np.inf
    for _ in range(2000):
        lx, ly, ell = rng.uniform(0.2, 0.5), rng.uniform(0.3, 0.5), rng.uniform(0.1, 0.25)
        th = (1 / 6, 0.0)[int(rng.integers(0, 2))]
        M, b = lx + ly, ly - lx
        dmax = min(ell, (2 * M + ell - 1) / 5)
        if dmax <= 0:
            continue
        d = np.linspace(0, dmax, 201)
        G = np.maximum.reduce([0 * d, th * b + 0 * d, 2 * b - ly + d])
        X = np.maximum.reduce([0 * d, M + ell - 1 - 3 * d, (1 + 3 * ell - 2 * M + d) / 4])
        f = lx / 2 + G / 2 + X / 2 - d
        worst = max(worst, (f[1:] - f[0]).max())
    gate('X5', worst < 0, f'the low side\'s tuple exponent is largest at d = 0 at 2000 random geometries '
                          f'(largest f(d) - f(0) for d > 0: {worst:.2e})')

    tab = {}
    for gram, soft, base in (('paper', False, 13 / 15), ('none', False, 31 / 36), ('none', True, 31 / 36)):
        tab[(gram, soft)] = (obstruction(gram, 1.0, 'inside', True, soft), obstruction(gram, 1.0, 'cross', True, soft),
                             obstruction(gram, 0.0, 'cross', True, soft), breakeven(gram, True, soft, base, True))
    pa, nh, ns = tab[('paper', False)], tab[('none', False)], tab[('none', True)]
    ok1 = (all(abs(x - 13 / 15) < 1e-9 for x in pa[:3]) and pa[3] is None
           and abs(nh[0] - 31 / 36) < 1e-9 and abs(nh[1] - 31 / 36) < 1e-9 and abs(nh[2] - 103 / 120) < 1e-9
           and abs(nh[3] - 2 / 15) < 1e-6 and abs(ns[0] - 31 / 36) < 1e-9 and abs(ns[1] - 31 / 36) < 1e-9
           and abs(ns[2] - 103 / 120) < 1e-9 and abs(ns[3] - 1 / 7) < 1e-6)
    be = [breakeven(g, False, False, base, fo) for g, base in (('paper', 13 / 15), ('none', 31 / 36))
          for fo in (True, False)]
    ok2 = (abs(be[0] - 1 / 18) < 1e-6 and abs(be[1] - 1 / 30) < 1e-6 and abs(be[2] - 2 / 15) < 1e-6
           and abs(be[3] - 2 / 15) < 1e-6)
    liu_v1 = (1507 - 2 * np.sqrt(921)) / 1653
    off = ModelFirst(kappa=0.75, slice_eq=False)
    lo_c, _ = EX.solve(off, mu_cost=0.15)
    hi_c, _ = EX.solve(off, mu_cost=0.16)
    ok3 = lo_c.x[4] > 1e-3 and lo_c.x[3] < liu_v1 - 1e-6 and hi_c.x[4] < 1e-9
    names = [nm for nm, _, _ in LV.CONFIGS]
    jobs = [(cfg, 'cross', c, 0.0, True) for c in (1.0, 0.0) for _, cfg, _ in LV.CONFIGS]
    with ProcessPoolExecutor(max_workers=4) as ex:
        res = list(ex.map(run_variant, jobs))
    want = [O.CROSS1[nm][0] if nm in O.CROSS1 else rec[0] for nm, _, rec in LV.CONFIGS] + \
           [O.CROSS0[nm][0] for nm in names]
    dev4 = max(abs(r[0] - w) for r, w in zip(res, want))
    gate('X6', ok1 and ok2 and ok3 and dev4 < 2e-6,
         f'crossing cost on the first branch only: kept rows {pa[0]:.10f} / {pa[1]:.10f} / {pa[2]:.10f} / none, '
         f'{nh[0]:.10f} / {nh[1]:.10f} / {nh[2]:.10f} / {nh[3]:.8f}, soft {ns[3]:.8f} (round 499\'s table); '
         f'round 498\'s rows alone: break-even {be[0]:.8f} (1/18; round 496\'s model {be[1]:.8f}, 1/30) and '
         f'{be[2]:.8f} (2/15; model {be[3]:.8f}); release\'s system: cost 0.15 crosses (mu = {lo_c.x[4]:.3f}), 0.16 '
         f'does not (mu = {hi_c.x[4]:.1e}); the fifteen configurations at c = 1 and c = 0 within {dev4:.1e} of '
         f'round 499\'s values')

    r498 = [(obstruction498('paper', s), obstruction498('none', s)) for s in (1 / 200, 1 / 100, 1 / 50)]
    ok1 = all(abs(p - (13 / 15 - 4 * s / 5)) < 1e-9 and abs(q - (31 / 36 - 5 * s / 6)) < 1e-9
              for (p, q), s in zip(r498, (1 / 200, 1 / 100, 1 / 50)))
    on_slice = lambda gram, **kw: obstruction(gram, 1.0, 'inside', slice_eq=True, **kw)
    kept = [(s, on_slice('paper', s=s), on_slice('none', s=s)) for s in (1 / 200, 1 / 100, 1 / 50, 1 / 24)]
    ok2 = all(abs(p - (13 / 15 - 4 * s / 5)) < 1e-9 and abs(q - (31 / 36 - 2 * s / 3)) < 1e-9 for s, p, q in kept)
    ok2 &= abs(kept[-1][1] - 5 / 6) < 1e-9 and abs(kept[-1][2] - 5 / 6) < 1e-9
    c0 = [(t, on_slice('paper', t=t), on_slice('none', t=t)) for t in (1 / 200, 1 / 100, 1 / 50)]
    ok3 = all(abs(p - 13 / 15) < 1e-9 and abs(q - (31 / 36 - t / 6)) < 1e-9 for t, p, q in c0)
    cf = {nm: cfg for nm, cfg, _ in LV.CONFIGS}
    rec = {nm: r for nm, _, r in LV.CONFIGS}
    jobs = [(cf['Lindelof + all readings'], 'slice', 1.0, 1 / 100, True),
            (cf["Sang's inputs"], 'slice', 1.0, 1 / 200, True), (cf["Sang's inputs"], 'slice', 1.0, 10.0, True)]
    with ProcessPoolExecutor(max_workers=3) as ex:
        lin, sa1, sa2 = list(ex.map(run_variant, jobs))
    ok4 = (abs(lin[0] - 0.8587858) < 2e-6 and lin[0] < 31 / 36 and lin[4] == rec['Lindelof + all readings'][5]
           and abs(sa1[0] - 0.8745077) < 2e-6 and abs(sa2[0] - 0.8745077) < 2e-6
           and all('E' in r[4] and 'low side' not in r[4] for r in (sa1, sa2)))
    sang0 = rec["Sang's inputs"][0]
    gate('X7', ok1 and ok2 and ok3 and ok4,
         f'low side lowered by s: round 498\'s obstruction ' +
         ', '.join(f'{p:.8f} / {q:.8f}' for p, q in r498) + ' at s = 1/200, 1/100, 1/50 (13/15 - 4s/5, 31/36 - 5s/6); '
         'kept rows on the slice ' + ', '.join(f'{p:.8f} / {q:.8f}' for _, p, q in kept) +
         ' at s = 1/200, 1/100, 1/50, 1/24 (13/15 - 4s/5, 31/36 - 2s/3; 5/6 at 1/24); C0 wall lowered by t: ' +
         ', '.join(f'{p:.8f} / {q:.8f}' for _, p, q in c0) + ' (13/15, 31/36 - t/6); Lindelof + all readings at '
         's = 1/100: '
         f'{lin[0]:.7f} < 31/36, walls {", ".join(lin[4])}; Sang\'s inputs at s = 1/200 and 10: {sa1[0]:.7f}, '
         f'{sa2[0]:.7f} (s = 0: {sang0:.7f}), walls {", ".join(sa1[4])} and {", ".join(sa2[4])}')

    print(f'{fails} gate(s) failed' if fails else 'all gates pass')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
