"""How far the high side's inputs move to reach 0.87, with the low side pinned (README round 506).

Rounds 503-505 pinned the release's low side at Sang's short windows: on his slice it is 11/12 - ell/4 whatever b is,
and the exceptional Gram term behind that is a main term (on Xu-Sang's reading) for every ray group T the release
allows and every xi that keeps the principal residue. At Sang's principal edge 0.87 the low side therefore needs
ell >= 14/75, while his high side admits ell <= 0.16091 there; round 503's need(0.87) = 0.0064390 is the low-side
saving that closes the gap. This script prices the other side: how far two of the high side's inputs must move for
the high side to admit the longer window, with the low side as the release has it.

The two inputs are the model's (levers.py, offslice.py), both hypothetical:
  k   the reflected numerator over a bin bounded through a 2k-th moment: the bin exponent carries h w (1 - R) with
      w = 1 - 1/(2k). Sang's fourth moment is k = 2 (w = 3/4); k = 10^9 stands for Lindelof on average (w = 1).
  t   Sang's row count R_kappa(delta, x) moved toward the density-hypothesis count 1 - delta by the fraction t (the
      floor bin keeps R = 1, as in levers.py's dh).
need is round 503's: the low side's least excess over B = 0.87 among the geometries the high side admits at s0 = 0.87,
on Sang's slice, under round 501's reading (Sang's ell >= 1/6 and 6 kappa ell > 3/4 read as the low side's range),
at kappa = 2B - 1 = 0.74. The floor bin is on the release's contour unless 'rotated floor' (levers.py's rot: Sang's
rotated line with vartheta = 0). Every number here is a statement about this exponent system, not a theorem.

Gates (exit status 1 if any fails):
  H1  Sang's inputs (k = 2, t = 0): need = 0.0064390 (2e-6, round 503), with the bins E, the supply ell/h > 21/100,
      the low side's exceptional row and the principal edge among the walls
  H2  the moment exponent: need falls strictly from k = 2 through K_STAR - 0.01 with the bins E binding, and from
      K_STAR + 0.01 to Lindelof on average it is FLOOR_NEED (1e-6), where the bins are slack and the floor bin and
      Sang's low-rows condition bind
  H3  the row counts: the same with t, threshold T_STAR; the density-hypothesis counts (t = 1) give FLOOR_NEED
  H4  the floor: with the floor bin on Sang's rotated line, need is ROT_NEED < 0 at k = 3 and at t = 1, so 0.87 is
      reached with the release's low side; at k = 2 it is unchanged. need crosses 0 at K0_ROT and T0_ROT (brackets
      +-0.01)
  H5  kappa, over round 503's grid 0.74, ..., 1 (lowbudget's KGRID): for k = 2 need rises strictly with kappa, so it is
      least at 0.74; for k = 3, with either floor, it does not depend on kappa (1e-9)
  H6  the binding bin at Sang's inputs, (delta, x) = BIND, with R_kappa there against 1 - delta
"""
import sys
import numpy as np
from scipy.optimize import linprog
from concurrent.futures import ProcessPoolExecutor
import offslice as O
import highfloor as HF
import levers as LV
import rotated_contour as RC
from lowbudget import KGRID

B0, KAPPA = 0.87, 0.74
SANG_NEED = 0.0064390        # round 503, gate B4
FLOOR_NEED = 0.0001351
ROT_NEED = -0.0004730
K_STAR, T_STAR = 2.758963, 0.602413   # where the bins stop binding (bisection, 20 steps, need within 2e-7 of the floor)
K0_ROT, T0_ROT = 2.789202, 0.598513   # with the rotated floor, where need crosses 0 (bisection, 20 steps)
BIND = (0.5131666666666667, 0.5)   # the grid bin (delta, x) where E is largest at Sang's inputs


class Mixed(HF.Reading):
    """highfloor.Reading with Sang's row count moved toward 1 - delta by the fraction t."""

    def __init__(self, kappa, t=0.0, **kw):
        self.t = t
        super().__init__(kappa, **kw)

    def count(self, d, x):
        return (1 - self.t) * RC.Rk(d, x, self.kappa) + self.t * (1 - d + 0 * x)


def reading(k=2.0, t=0.0, rot=False, kappa=KAPPA):
    return Mixed(kappa, t=t, read=True, s=0.0, mode='slice', k=k, rot=rot)


def need(o, B=B0):
    """round 503's need(B) for the reading o: least low-side excess where the high side admits s0 = B."""
    rows, rhs, names = [], [], []
    for n, r, b in o.fixed_rows():
        low = n.startswith('low:')
        rows.append([r[0], r[1], r[2], -1.0 if low else 0.0])
        rhs.append(b if low else b - r[3] * B)
        names.append(n)
    A0, b0 = np.array(rows), np.array(rhs)
    idx = np.arange(0, o.C.shape[1], 7)
    for _ in range(500):
        Cb = o.C[:, idx]
        A = np.vstack([A0, np.column_stack([Cb[1], Cb[2], Cb[3], np.zeros(idx.size)])])
        res = linprog([0, 0, 0, 1], A_ub=A, b_ub=np.concatenate([b0, B - Cb[0]]),
                      bounds=[(0, 1)] * 3 + [(None, None)], method='highs', options=O.HIGHS)
        if res.status != 0:
            raise RuntimeError(res.message)
        w = res.x
        E = o.C[0] + o.C[1] * w[0] + o.C[2] * w[1] + o.C[3] * w[2] - B
        new = np.setdiff1d(np.flatnonzero(E > 1e-10), idx)
        if new.size == 0:
            act = {names[i] for i in range(len(names)) if A0[i] @ w > b0[i] - 1e-7 and not names[i].startswith('slice')}
            act |= {'E'} if E.max() > -1e-7 else set()
            j = int(np.argmax(E))
            nx = RC.XL.shape[1]
            return dict(need=w[3] - B, lx=w[0], ly=w[1], ell=w[2], b=w[1] - w[0], walls=act, emax=E.max(),
                        small=o.small_max(np.array([w[0], w[1], w[2], B, 0.0])),
                        bin=(float(RC.DL[j // nx, 0]), float(RC.XL[0, j % nx])))
        idx = np.union1d(idx, new[np.argsort(E[new])[-25:]])
    raise RuntimeError('no convergence')


def job(a):
    return a, need(reading(**a))


FLOOR_WALLS = {'floor bin', 'low rows', 'low:P^(1/6)', 'principal edge'}


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    ks = [2.0, 2.25, 2.5, K_STAR - 0.01, K_STAR + 0.01, 3.0, 6.0, float(LV.LINDELOF)]
    ts = [0.0, 0.25, 0.5, T_STAR - 0.01, T_STAR + 0.01, 1.0]
    jobs = ([dict(k=k) for k in ks] + [dict(t=t) for t in ts]
            + [dict(k=3.0, rot=True), dict(t=1.0, rot=True), dict(k=2.0, rot=True)]
            + [dict(k=K0_ROT - 0.01, rot=True), dict(k=K0_ROT + 0.01, rot=True),
               dict(t=T0_ROT - 0.01, rot=True), dict(t=T0_ROT + 0.01, rot=True)]
            + [dict(k=k, rot=r, kappa=kap) for k, r in ((2.0, False), (3.0, False), (3.0, True)) for kap in KGRID])
    with ProcessPoolExecutor(max_workers=4) as ex:
        res = list(ex.map(job, jobs))
    get = lambda **a: next(r for j, r in res if j == a)

    s = get(k=2.0)
    ok = abs(s['need'] - SANG_NEED) < 2e-6 and {'E', 'ell/h>21/100', 'low:P^(1/6)', 'principal edge'} <= s['walls']
    gate('H1', ok, f'Sang\'s inputs: need(0.87) = {s["need"]:.7f} at ell {s["ell"]:.5f}, b {s["b"]:.5f}; walls '
                   + ', '.join(sorted(s['walls'])))

    def scan(name, key, vals, star):
        rs = [get(**{key: v}) for v in vals]
        above = [r for v, r in zip(vals, rs) if v <= star - 0.01]
        below = [r for v, r in zip(vals, rs) if v >= star + 0.01]
        ok = all(x['need'] > y['need'] + 1e-6 for x, y in zip(above, above[1:]))
        ok &= all('E' in r['walls'] and r['need'] > FLOOR_NEED + 1e-6 for r in above)
        ok &= all(abs(r['need'] - FLOOR_NEED) < 1e-6 and r['walls'] == FLOOR_WALLS and r['emax'] < -1e-7
                  for r in below)
        ok &= all(r['small'] < 0 for r in rs)
        gate(name, ok, f'{key} = ' + ', '.join(f'{v:g}: {r["need"]:+.7f}' for v, r in zip(vals, rs))
             + f'; the bins stop binding at {key} = {star}')

    scan('H2', 'k', ks, K_STAR)
    scan('H3', 't', ts, T_STAR)

    r3, r1, r2 = get(k=3.0, rot=True), get(t=1.0, rot=True), get(k=2.0, rot=True)
    ok = abs(r3['need'] - ROT_NEED) < 1e-6 and abs(r1['need'] - ROT_NEED) < 1e-6 and ROT_NEED < 0
    ok &= abs(r2['need'] - SANG_NEED) < 2e-6
    kb = (get(k=K0_ROT - 0.01, rot=True)['need'], get(k=K0_ROT + 0.01, rot=True)['need'])
    tb = (get(t=T0_ROT - 0.01, rot=True)['need'], get(t=T0_ROT + 0.01, rot=True)['need'])
    ok &= kb[0] > 0 > kb[1] and tb[0] > 0 > tb[1]
    gate('H4', ok, f'rotated floor: need {r3["need"]:+.7f} at k = 3, {r1["need"]:+.7f} at t = 1, {r2["need"]:+.7f} at '
                   f'k = 2; need crosses 0 between k = {K0_ROT - 0.01:.3f} and {K0_ROT + 0.01:.3f} '
                   f'({kb[0]:+.1e}, {kb[1]:+.1e}) and between t = {T0_ROT - 0.01:.3f} and {T0_ROT + 0.01:.3f}')

    ok, lines = True, []
    for k, r in ((2.0, False), (3.0, False), (3.0, True)):
        vals = [get(k=k, rot=r, kappa=kap)['need'] for kap in KGRID]
        if k == 2.0:
            ok &= all(x < y for x, y in zip(vals, vals[1:]))
        else:
            ok &= max(vals) - min(vals) < 1e-9
        lines.append(f'k = {k:g}{" rotated" if r else ""}: ' + ', '.join(f'{v:+.7f}' for v in vals))
    gate('H5', ok, 'need over kappa = ' + ', '.join(f'{x:g}' for x in KGRID) + ': ' + '; '.join(lines))

    d, x = s['bin']
    Rs, Rdh = RC.Rk(d, x, KAPPA), 1 - d
    ok = abs(d - BIND[0]) < 1e-9 and abs(x - BIND[1]) < 1e-9 and s['emax'] > -1e-7
    gate('H6', ok, f'binding bin at Sang\'s inputs: delta = {d:.4f}, x = {x:.3f}; R_kappa = {Rs:.5f} against '
                   f'1 - delta = {Rdh:.5f}')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
