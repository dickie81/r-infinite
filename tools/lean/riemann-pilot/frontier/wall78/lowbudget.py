"""The release's low estimate at short prime windows, step by step, and what it must give (README round 503).

The release's Proposition prop:probe-low bounds each rescaled tuple's separated probe, eq. low-separated, by
Cauchy-Schwarz in the row sum: Q^{-1/2} [(Q/Y') P_a^{1/6}]^{1/2} [Z^{M'}]^{1/2} = (X')^{1/2} P_a^{1/12}. Its steps, as
exponents of Z at tuple size d = 0 (Q = Z^M, Y' = Z^{l_y}, P_a = Y'^2/Q = Z^b):
  the separation's normalization Q^{-1/2}                                  -M/2
  the Gram bound (Proposition prop:probe-gram), half of
      its diagonal k = 0, Q/Y'                                              (M - l_y)/2
      its exceptional frequencies, P_a^{1/6} (theta = 1/6; 0 when removed)  theta b/2
      its other frequencies, P_a^2/Y'                                       (2b - l_y)/2
  the completed-row norm (Lemma lem:probe-row-norm), half of its bound,
      the row count Z^{M'} times round 500's row loss                       (M + loss)/2
with the Gram terms entering through their maximum, and the tuple sum f(d) = -d. The high side's normalization
C(s) = s - 5/6 + l_x/3 + ell/6 (Definition def:stage-high-data) turns the probe's exponent L into the low side
s0 = L + 5/6 - l_x/3 - ell/6.

The model is lowerend.py's and highfloor.py's (offslice.py on Sang's slice under round 501's reading, with the levers
of levers.py). need(B) is the low side's excess over a boundary B where the high side admits it: the least, over the
geometries the high side admits at s0 = B with kappa = 2B - 1 (or a given kappa), of the low side minus B. Every number
here is a statement about this exponent system, not a theorem.

Gates (exit status 1 if any fails):
  B1  the steps above, summed and turned into s0, equal the model's low side (offslice.low_rows) at 2000 random
      geometries with M + ell <= 1, with the exceptional term and without it (1e-12)
  B2  in exact arithmetic on Sang's slice l_x = (1-b-ell)/2, l_y = (1+b-ell)/2, at every point of a rational grid with
      ell <= 1/5 and the third term absorbed (b <= (1-ell)/(3-2 theta)): the low side is 11/12 - ell/4 + (theta-1/6)b/2,
      so with the exceptional term it does not depend on b; of its slope -1/4 in ell, -1/12 comes through l_x and -1/6
      through C(s); it reaches a boundary B at ell = 4(11/12 - B): 1/6 at 7/8 and 14/75 at 87/100
  B3  need(B) for Sang's inputs reproduces lowerend.py's curve: at each recorded boundary it is the saving s that gave
      it (1e-6), it vanishes at his 0.8748866 (1e-6), and at 0.87 it is s* (1e-5), with ell = 0.16091, the walls E,
      the supply and the principal edge, and need rising with kappa from 2B - 1 = 0.74 to 1
  B4  need(0.87), least over kappa in {0.74, 0.75, 0.76, 0.77, 0.78, 0.8, 0.85, 0.9, 1} (2e-6): Sang's inputs
      0.0064390; the exceptional term removed 0.0022930, at the same ell, smaller by b/12 (1e-9) with
      b = 137 ell/21 - 1, where the supply ell/h > 21/100 binds (1e-6); Sang's 21/100 read as his row count's 1/5
      (levers.py's tech) 0.0063442; both -0.0040493 at kappa = 0.77, with b = 7 ell - 1 (1e-6). Only the last is
      at most 0
  B5  kappa above 3/4: the least boundary over kappa in {0.75, 0.76, ..., 1} of each of the fifteen configurations
      under round 501's reading, within 2e-6 of its record. Two fall below their bootstrap values: Sang's inputs +
      Gram removed + all readings to 0.8678790 and Lindelof + all readings + Gram removed to 0.8612731, both at
      kappa = 0.77; the other thirteen are least at kappa = 3/4. With ell >= 1/6 kept, only Lindelof + all readings +
      Gram removed falls, to 0.8613056. Each least is licensed: kappa >= 2B - 1
"""
import sys
import random
from fractions import Fraction as Fr
from concurrent.futures import ProcessPoolExecutor
import numpy as np
from scipy.optimize import linprog
import offslice as O
import levers as LV
import lowerend as LE
import highfloor as HF


def steps(lx, ly, ell, theta):
    """the release's low estimate, step by step, as the low side s0 (tuple size 0, M + ell <= 1)."""
    M, b, zero = lx + ly, ly - lx, lx * 0
    norm = -M / 2
    diag = (M - ly) / 2
    gram = max(zero, theta * b, 2 * b - ly) / 2
    rows = (M + max(zero, M + ell - 1, (1 + 3 * ell - 2 * M) / 4)) / 2
    L = norm + diag + gram + rows
    return L + Fr(5, 6) - lx / 3 - ell / 6 if isinstance(lx, Fr) else L + 5 / 6 - lx / 3 - ell / 6


def model_low(lx, ly, ell, theta):
    return max(r[0] * lx + r[1] * ly + r[2] * ell - b for _, r, b in O.low_rows(theta, 1.0))


def need(cfg, B, kappa=None):
    """the low side's least excess over B where the high side admits s0 = B (on the slice, round 501's reading)."""
    k = 2 * B - 1 if kappa is None else kappa
    o = HF.Reading(k, read=True, s=0.0, mode='slice', **cfg)
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
            small = o.small_max(np.array([w[0], w[1], w[2], B, 0.0]))
            return dict(need=w[3] - B, lx=w[0], ly=w[1], ell=w[2], b=w[1] - w[0], walls=act, small=small, kappa=k)
        idx = np.union1d(idx, new[np.argsort(E[new])[-25:]])
    raise RuntimeError('no convergence')


def need_job(args):
    return need(*args)


def boundary_at(args):
    cfg, k, read = args
    sol = LE.Reading(k, read=read, s=0.0, mode='slice', **cfg).solve()
    return np.inf if sol is None else sol['v'][3]


KGRID = (0.74, 0.75, 0.76, 0.77, 0.78, 0.8, 0.85, 0.9, 1.0)
BUDGET = {'Sang': (0.0064390, 0.74), 'Gram removed': (0.0022930, 0.74), 'tech': (0.0063442, 0.75),
          'Gram removed + tech': (-0.0040493, 0.77)}
LEAST_READ = {"Sang's inputs + Gram removed + all readings": (0.8678790, 0.77),
              "Lindelof + all readings + Gram removed": (0.8612731, 0.77)}
LEAST_KEPT = {"Lindelof + all readings + Gram removed": (0.8613056, 0.77)}
ELL_087 = 0.16091


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    rng, dev, n = random.Random(503), 0.0, 0
    while n < 2000:
        lx, ly, ell = rng.uniform(0, 0.6), rng.uniform(0, 0.7), rng.uniform(0, 0.3)
        if lx + ly + ell > 1:
            continue
        for theta in (1 / 6, 0.0):
            dev = max(dev, abs(steps(lx, ly, ell, theta) - model_low(lx, ly, ell, theta)))
        n += 1
    gate('B1', dev < 1e-12, f'normalization, Gram diagonal, Gram terms and row norm, through C(s), equal the model\'s '
                            f'low side at {n} geometries with M + ell <= 1, theta = 1/6 and 0: largest gap {dev:.1e}')

    ok, npts = True, 0
    for theta in (Fr(1, 6), Fr(0)):
        for li in range(1, 21):
            ell = Fr(li, 100)
            for bi in range(0, 41):
                b = Fr(bi, 100)
                if b > (1 - ell) / (3 - 2 * theta):
                    continue
                lx, ly = (1 - b - ell) / 2, (1 + b - ell) / 2
                v = steps(lx, ly, ell, theta)
                ok &= isinstance(v, Fr) and v == Fr(11, 12) - ell / 4 + (theta - Fr(1, 6)) * b / 2
                npts += 1
    # the slope in ell at fixed b: through l_x = (1-b-ell)/2 the low side moves by (1/6)(-1/2) = -1/12; through
    # C(s)'s ell/6 by -1/6
    split = (Fr(1, 6) * Fr(-1, 2), Fr(-1, 6))
    ok &= sum(split) == Fr(-1, 4)
    th = (4 * (Fr(11, 12) - Fr(7, 8)), 4 * (Fr(11, 12) - Fr(87, 100)))
    ok &= th == (Fr(1, 6), Fr(14, 75))
    gate('B2', ok, f'on Sang\'s slice at {npts} rational points: low side = 11/12 - ell/4 + (theta - 1/6) b/2; slope '
                   f'in ell {split[0]} (through l_x) + {split[1]} (through C(s)) = -1/4; reaches 7/8 at ell = {th[0]} '
                   f'and 87/100 at ell = {th[1]}')

    cfgs = dict((nm, c) for nm, c, _ in LV.CONFIGS)
    sang = cfgs["Sang's inputs"]
    curve = [need(sang, B) for s, B in sorted(LE.CURVE.items())]
    dev_c = max(abs(r['need'] - s) for r, s in zip(curve, sorted(LE.CURVE)))
    at_own = need(sang, 0.8748866)
    r87 = need(sang, 0.87)
    rising = [need(sang, 0.87, k)['need'] for k in (0.74, 0.75, 0.77, 0.8, 0.9, 1.0)]
    ok = (dev_c < 1e-6 and abs(at_own['need']) < 1e-6 and abs(r87['need'] - LE.S_STAR) < 1e-5
          and abs(r87['ell'] - ELL_087) < 1e-5 and {'E', 'ell/h>21/100', 'principal edge'} <= r87['walls']
          and all(x < y for x, y in zip(rising, rising[1:])) and r87['small'] < 0)
    gate('B3', ok, f'Sang\'s inputs: need at the curve\'s boundaries equals its savings within {dev_c:.1e}; '
                   f'need(0.8748866) = {at_own["need"]:.1e}; need(0.87) = {r87["need"]:.7f} at ell {r87["ell"]:.5f}, '
                   f'b {r87["b"]:.5f}, walls {", ".join(sorted(r87["walls"]))}; rising in kappa: '
                   + ', '.join(f'{x:.7f}' for x in rising))

    variants = {'Sang': dict(k=2), 'Gram removed': dict(k=2, gram='none'), 'tech': dict(k=2, tech=True),
                'Gram removed + tech': dict(k=2, gram='none', tech=True)}
    jobs = [(cfg, 0.87, k) for cfg in variants.values() for k in KGRID]
    with ProcessPoolExecutor(max_workers=4) as ex:
        res = list(ex.map(need_job, jobs))
    best = {}
    for i, nm in enumerate(variants):
        row = res[i * len(KGRID):(i + 1) * len(KGRID)]
        best[nm] = min(row, key=lambda r: r['need'])
    s, g, t, gt = best['Sang'], best['Gram removed'], best['tech'], best['Gram removed + tech']
    ok = all(abs(best[nm]['need'] - BUDGET[nm][0]) < 2e-6 and abs(best[nm]['kappa'] - BUDGET[nm][1]) < 1e-9
             for nm in variants)
    ok &= abs(s['ell'] - g['ell']) < 1e-9 and abs(s['need'] - g['need'] - g['b'] / 12) < 1e-9
    ok &= abs(g['b'] - (137 * g['ell'] / 21 - 1)) < 1e-6 and abs(gt['b'] - (7 * gt['ell'] - 1)) < 1e-6
    ok &= [nm for nm in variants if best[nm]['need'] <= 0] == ['Gram removed + tech']
    gate('B4', ok, 'need(0.87), least over kappa: ' + '; '.join(
        f'{nm} {best[nm]["need"]:+.7f} (kappa {best[nm]["kappa"]}, ell {best[nm]["ell"]:.5f}, b {best[nm]["b"]:.5f})'
        for nm in variants) + f'; the exceptional term is worth b/12 = {g["b"] / 12:.7f} at Sang\'s geometry')

    ks = np.round(np.arange(0.75, 1.0000001, 0.01), 6)
    jobs = [(cfg, k, rd) for rd in (True, False) for _, cfg, _ in LV.CONFIGS for k in ks]
    with ProcessPoolExecutor(max_workers=4) as ex:
        vals = np.array(list(ex.map(boundary_at, jobs))).reshape(2, len(LV.CONFIGS), len(ks))
    ok, lines = True, []
    for j, (tab, recs) in enumerate(((LEAST_READ, LE.READ_LOW), (LEAST_KEPT, None))):
        for i, (nm, cfg, rec) in enumerate(LV.CONFIGS):
            row = vals[j, i]
            m = int(np.argmin(row))
            boot = recs[nm] if recs else rec[0]
            ok &= ks[m] >= 2 * row[m] - 1
            if nm in tab:
                ok &= abs(row[m] - tab[nm][0]) < 2e-6 and abs(ks[m] - tab[nm][1]) < 1e-9 and row[m] < boot - 1e-4
                lines.append(f'{nm}{"" if recs else " (ell >= 1/6 kept)"} {boot:.7f} -> {row[m]:.7f} at kappa {ks[m]}')
            else:
                ok &= m == 0 and row[0] >= boot - 1e-6
    gate('B5', ok, 'least over kappa in [3/4, 1]: ' + '; '.join(lines) + '; every other configuration least at 3/4, '
                   'no lower than its bootstrap value; every least licensed (kappa >= 2B - 1)')

    print(f'{fails} gate(s) failed' if fails else 'all gates pass')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
