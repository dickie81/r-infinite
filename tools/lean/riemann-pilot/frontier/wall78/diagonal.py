"""The second transform's diagonal and a third plain factor (README round 508).

Sang's numerator average, his Proposition prop:numerator, bounds each block of the reflected numerator through the
release's plain fourth moment, its Lemma lem:plain, by Hoelder. His approximate functional equation cuts both sums at
sqrt(Q), so its longest blocks have length U^{1/2}: m = 1/2 in units where the moment's width M is 1, the units of his
capacity 2m + 6 kappa z <= 1. The release proves lem:plain by an induction on M. For two plain factors and no prime
slots it reflects each factor longer than M/2 once, to length at most M - n + xi, which gives its padded zero-slot core
A* = n_1* + n_2* <= M + delta (eq. old-eq:2.1h). The diagonal of its second transform (eq. old-eq:2.12) and its
centred exceptional terms (eq. old-eq:2.19) each leave the excess A - M, so the induction closes for A <= M, with delta
more in the core. Reflection takes the plain sum at X to the conjugate sum at C_k/X, with C_k <= C_A Z^M, so for a row
whose conductor is of size Z^M a block of length M/2 is its own reflection, and k copies of a longest block have
A = kM/2 for every choice of reflections: 3M/2 for a sixth moment (gate D2).

If that excess were the method's only loss beyond A = M, k plain factors at block m would give U^{max(1, km)}, and
Hoelder over a class of U^R rows the block exponent R (1 - 1/(2k)) + max(1, km)/(2k) - vartheta m (the rotation's
saving on a block of length U^m is U^{vartheta m}). No prime slot fits at m = 1/2 (km >= 1 for k >= 2). There the
exponent exceeds Sang's (3R+1)/4 - vartheta/2 by R (k-2)/(4k) for k >= 2 and by (1-R)(2-k)/(4k) for k <= 2, at every
vartheta (gate D1). So within the method no order of moment, and no choice of orders bin by bin, bounds the longest
blocks below Sang's fourth moment. The excess is what the trivial bound U^{1/4} on the k - 2 extra factors costs.

What a third factor would have to give (gate D3, exchange.py's frame at 0.87, round 506): a sixth moment at A = 3M/2
that loses only U^eta over the width, U^{1 + eta}, with Lindelof on average at A <= M under round 507's capacity, a loss
linear in A - M in between, and the fourth moment kept at the floor bin, where every order gives U at R = 1. All of this
is hypothetical; the sources read prove no such moment. Two strategies are computed for one order in every bin:
vartheta = 0 without Sang's amplifier rows ('Loss', capacity.py's amp_rows=False), and Sang's vartheta capped at
eta/(k-2) bin by bin with his rows ('LossRot'); below the cap the longest blocks bind. Each gives a sufficient eta.
Orders mixed bin by bin can only raise the thresholds, and are not computed. The method's eta is k/2 - 1. Every number
here is a statement about this exponent system, not a theorem.

Gates (exit status 1 if any fails):
  D1  exact, on rational grids (k from 1 to 12 in steps of 1/4, R in [0, 1], vartheta in [0, 1/10]): the block exponent
      at m = 1/2 exceeds Sang's (3R+1)/4 - vartheta/2 by R (k-2)/(4k) (k >= 2) or (1-R)(2-k)/(4k) (k <= 2), so never
      falls below it, with equality iff k = 2, or R = 0 with k >= 2, or R = 1 with k <= 2; k m >= 1 there for k >= 2;
      on [1/k, 1/2] the exponent is nondecreasing in m (k >= 2), so the longest block binds; with a moment U^{1+eta}
      at m = 1/2 in place of U^{k/2} the exponent is below Sang's iff eta < (1-R)(k/2 - 1), and the method's
      k/2 - 1 is never below that; the bound sup|S|^{2k-4} times the fourth moment gives eta = (2k-4) alpha for
      |S| <= U^alpha, and alpha = 1/4, the trivial bound, gives k/2 - 1. At k = 2 the exponent is Sang's
      eq. numerator-balance value
  D2  exact: two factors (lengths on a grid in [0, 2M], xi on a grid) reflected as the release reflects them have
      n_i* <= M/2 + xi and A* <= M + 2 xi; for k = 3, ..., 6 factors of length M/2, every one of the 2^k choices of
      reflections leaves A* = kM/2; for every cut x of the approximate functional equation (a grid in [0, 1]) the
      longest block has length max(x, 1-x) >= 1/2, and the block at 1/2 is its own reflection
  D3  the model (exchange.py's frame at 0.87): at eta = 0 both classes reproduce capacity.Cap with vartheta = 0
      (1e-14), and eta moves K by exactly eta/(2k) in 'Loss'; the method's eta = k/2 - 1 under 'LossRot' moves every
      bin of Sang's model (k = 2, his vartheta) by exactly R (k-2)/(4k) in K and nothing else (1e-14), and at k = 3, 4
      no geometry then admits 0.87 (the program is infeasible), while Sang's needs SANG_NEED. For k = 3 and 4, with
      'Loss' and 'LossRot': the bins stop binding at ETA_FLOOR and, with the rotated floor, need(0.87) changes sign at
      ETA_CROSS, each bracketed by +-0.001: below ETA_FLOOR need is FLOOR_NEED with the bins slack and exchange.py's
      floor walls, above it the bins bind and need exceeds FLOOR_NEED; need is negative below ETA_CROSS and positive,
      with the bins binding, above it. 'LossRot' raises each threshold
"""
import sys
from fractions import Fraction as Fr
from itertools import product
import numpy as np
from concurrent.futures import ProcessPoolExecutor
import capacity as CP
import exchange as X
import rotated_contour as RC

XS, XL, DL = RC.XS, RC.XL, RC.DL
# eta where the bins stop binding (FLOOR) and where need(0.87) changes sign with the rotated floor (CROSS), for
# (k, strategy); bisection, 22 steps (--bisect)
ETA_FLOOR = {(3, 'Loss'): 0.021122, (3, 'LossRot'): 0.024889, (4, 'Loss'): 0.111240, (4, 'LossRot'): 0.116413}
ETA_CROSS = {(3, 'Loss'): 0.017225, (3, 'LossRot'): 0.020243, (4, 'Loss'): 0.104843, (4, 'LossRot'): 0.109834}
BR = 0.001


class Loss(CP.Cap):
    """capacity.Cap with vartheta = 0 and the longest blocks' moment U^{1 + eta}: K = 5/6 - w (1-R) + eta/(2k)."""

    def __init__(self, kappa, eta=0.0, **kw):
        self.eta = eta
        super().__init__(kappa, theta='zero', amp_rows=False, **kw)

    def th_bins(self, d, x):
        return 0 * d * x

    def th_small(self, ell, h):
        return 0 * self.DS

    def coeffs(self, d, x, R, reflection_cost=True):
        th = self.th_bins(d, x)
        K = 5 / 6 - self.w * (1 - R) + self.eta / (2 * self.k) + th / 2
        z = 0 * d * x
        return 1 / 2 + d / 2 + K + z, -K + z, -(1 / 2 + th) + z, -1 / 2 + x * d + K + z

    def small_max(self, v):
        lx, ly, ell, s0 = v[:4]
        h = 1 - lx + ell
        th = self.th_small(ell, h)
        return (1 / 2 + self.DS / 2 - ly * (1 / 2 + th) - s0 - ell / 2 + XS * self.DS * ell
                + h * (5 / 6 - self.w * (1 - self.Rs) + self.eta / (2 * self.k) + th / 2)).max()


class LossRot(Loss):
    """Loss with Sang's vartheta capped at eta/(k-2) bin by bin, where the longest blocks' saving vartheta/2 meets the
    short blocks' vartheta/k; below the cap the longest blocks bind, with share 1/2. Sang's amplifier rows kept."""

    def __init__(self, kappa, eta=0.0, **kw):
        self.eta = eta
        CP.Cap.__init__(self, kappa, theta='max', **kw)

    def cap(self):
        return self.eta / (self.k - 2)

    def th_bins(self, d, x):
        return np.minimum(np.minimum(np.minimum(self.lam * self.tau * x * d, d / 2), 1 / 10), self.cap())

    def th_small(self, ell, h):
        return np.minimum(XS * self.DS * min(ell / h, self.tau), self.cap())


CLASSES = {'Loss': Loss, 'LossRot': LossRot}


def model(k, eta, strat='Loss', rot=False):
    return CLASSES[strat](X.KAPPA, eta=eta, t=0.0, read=True, s=0.0, mode='slice', k=float(k), rot=rot)


def need(k, eta, strat='Loss', rot=False):
    try:
        return X.need(model(k, eta, strat, rot))
    except RuntimeError:
        return dict(need=float('inf'), emax=float('inf'), walls={'infeasible'})


def job(a):
    return a, need(*a)


def floor_slack(r):
    return abs(r['need'] - X.FLOOR_NEED) < 2e-7 and r['emax'] < -1e-7


def d1():
    ks = [Fr(i, 4) for i in range(4, 49)]
    Rs = [Fr(i, 40) for i in range(41)]
    ths = [Fr(i, 100) for i in range(11)]
    etas = [Fr(i, 80) for i in range(81)]
    ok, n = True, 0
    for k, R, th in product(ks, Rs, ths):
        F = lambda m: R * (1 - 1 / (2 * k)) + max(Fr(1), k * m) / (2 * k) - th * m
        S = (3 * R + 1) / 4 - th / 2
        gap = F(Fr(1, 2)) - S
        ok &= gap == (R * (k - 2) / (4 * k) if k >= 2 else (1 - R) * (2 - k) / (4 * k))
        ok &= gap >= 0 and (gap == 0) == (k == 2 or (R == 0 and k >= 2) or (R == 1 and k <= 2))
        if k >= 2:
            ok &= k * Fr(1, 2) >= 1
            ms = [1 / k + (Fr(1, 2) - 1 / k) * Fr(i, 20) for i in range(21)]
            ok &= all(F(a) <= F(b) for a, b in zip(ms, ms[1:]))
        if k > 2:
            for eta in etas:
                Fe = R * (1 - 1 / (2 * k)) + (1 + eta) / (2 * k) - th / 2
                ok &= (Fe < S) == (eta < (1 - R) * (k / 2 - 1))
            ok &= k / 2 - 1 >= (1 - R) * (k / 2 - 1)
            ok &= (2 * k - 4) * Fr(1, 4) == k / 2 - 1
        n += 1
    R, q, v, m = Fr(3, 5), Fr(1, 4), Fr(1, 7), Fr(1, 5)
    ok &= -q * v * m - q * v * (1 - 2 * m) / 2 == -q * v / 2
    ok &= R * (1 - Fr(1, 4)) + Fr(1, 4) == (3 * R + 1) / 4
    return ok, n


def d2():
    ok, n = True, 0
    for M in (Fr(1, 2), Fr(1), Fr(7, 5), Fr(3)):
        for xi in (Fr(0), Fr(1, 1000), Fr(1, 50)):
            lens = [M * Fr(i, 40) for i in range(81)]
            for n1, n2 in product(lens, lens):
                st = [n if n <= M / 2 else M - n + xi for n in (n1, n2)]
                ok &= all(s <= M / 2 + xi for s in st) and sum(st) <= M + 2 * xi
                n += 1
        for k in range(3, 7):
            ns = [M / 2] * k
            for refl in product((False, True), repeat=k):
                A = sum(M - x if r else x for x, r in zip(ns, refl))
                ok &= A == k * M / 2 and A > M
            ok &= sum(min(x, M - x) for x in ns) == k * M / 2
    for i in range(101):
        x = Fr(i, 100)
        ok &= max(x, 1 - x) >= Fr(1, 2)
    ok &= min(Fr(1, 2), 1 - Fr(1, 2)) == Fr(1, 2)
    return ok, n


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    ok, n = d1()
    gate('D1', ok, f'{n} exact (k, R, vartheta): at m = 1/2 the block exponent exceeds Sang\'s (3R+1)/4 - vartheta/2 '
                   f'by R (k-2)/(4k) (k >= 2) or (1-R)(2-k)/(4k) (k <= 2), zero only at k = 2, R = 0 or R = 1 as stated; '
                   f'no slot at m = 1/2; the longest block binds; a loss eta beats Sang iff eta < (1-R)(k/2-1), and the '
                   f'method\'s k/2 - 1 never does; sup|S|^(2k-4) at the trivial U^(1/4) gives the same k/2 - 1')

    ok, n = d2()
    gate('D2', ok, f'{n} exact two-factor reflections: n_i* <= M/2 + xi, A* <= M + 2 xi (eq. old-eq:2.1h); k = 3..6 '
                   f'factors of length M/2: A* = kM/2 for all 2^k reflection choices; every cut of the approximate '
                   f'functional equation has a block of length 1/2, its own reflection')

    dev = 0.0
    for k in (3, 4):
        z = CP.cap(k=float(k), theta='zero')
        for strat in ('Loss', 'LossRot'):
            dev = max(dev, np.abs(model(k, 0.0, strat).C - z.C).max())
        a, e = model(k, 0.0), model(k, 0.05)
        sh = 0.05 / (2 * k)
        dev = max(dev, np.abs(e.C[0] - a.C[0] - sh).max(), np.abs(e.C[1] - a.C[1] + sh).max(),
                  np.abs(e.C[2] - a.C[2]).max(), np.abs(e.C[3] - a.C[3] - sh).max())
    dm = 0.0
    sang = X.reading(k=2.0)
    Rg = sang.count(DL, XL).ravel()
    for k in (3, 4):
        mth = model(k, k / 2 - 1, 'LossRot')
        sh = Rg * (k - 2) / (4 * k)
        dm = max(dm, np.abs(mth.C[0] - sang.C[0] - sh).max(), np.abs(mth.C[1] - sang.C[1] + sh).max(),
                 np.abs(mth.C[2] - sang.C[2]).max(), np.abs(mth.C[3] - sang.C[3] - sh).max())

    keys = [(k, s) for k in (3, 4) for s in ('Loss', 'LossRot')]
    jobs = [(k, k / 2 - 1, 'LossRot', False) for k in (3, 4)]
    for k, s in keys:
        f, c = ETA_FLOOR[(k, s)], ETA_CROSS[(k, s)]
        jobs += [(k, f - BR, s, False), (k, f + BR, s, False), (k, c - BR, s, True), (k, c + BR, s, True)]
    with ProcessPoolExecutor(max_workers=4) as ex:
        res = dict(ex.map(job, jobs))
    meth = [res[(k, k / 2 - 1, 'LossRot', False)] for k in (3, 4)]
    ok = dev < 1e-14 and dm < 1e-14 and all(r['walls'] == {'infeasible'} for r in meth)
    lines = []
    for k, s in keys:
        f, c = ETA_FLOOR[(k, s)], ETA_CROSS[(k, s)]
        lo, hi = res[(k, f - BR, s, False)], res[(k, f + BR, s, False)]
        clo, chi = res[(k, c - BR, s, True)], res[(k, c + BR, s, True)]
        ok &= floor_slack(lo) and lo['walls'] == X.FLOOR_WALLS
        ok &= not floor_slack(hi) and 'E' in hi['walls'] and hi['need'] > X.FLOOR_NEED + 1e-7
        ok &= clo['need'] < 0 < chi['need'] and 'E' in chi['walls']
        lines.append(f'k = {k} {s}: bins slack below eta = {f} ({lo["need"]:+.7f}), binding above '
                     f'({hi["need"]:+.7f}); rotated floor crosses 0 at eta = {c} ({clo["need"]:+.1e}, {chi["need"]:+.1e})')
    for k in (3, 4):
        ok &= ETA_FLOOR[(k, 'LossRot')] > ETA_FLOOR[(k, 'Loss')] and ETA_CROSS[(k, 'LossRot')] > ETA_CROSS[(k, 'Loss')]
    gate('D3', ok, f'eta = 0 reproduces capacity.Cap with vartheta = 0 and eta moves K by eta/(2k) (max deviation '
                   f'{dev:.0e}); the method\'s eta = k/2 - 1 moves Sang\'s bins by R (k-2)/(4k) (max deviation {dm:.0e}) '
                   f'and no geometry admits 0.87 at k = 3, 4 (Sang\'s needs {X.SANG_NEED}); ' + '; '.join(lines))
    print(f'{fails} gate(s) failed' if fails else 'all gates pass')
    return 1 if fails else 0


def bis(f, lo, hi, steps=22):
    for _ in range(steps):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if f(m) else (lo, m)
    return lo, hi


def bisect_job(spec):
    k, s, kind = spec
    top = 0.05 if k == 3 else 0.3
    if kind == 'floor':
        return spec, bis(lambda e: floor_slack(need(k, e, s)), 0.0, top)
    return spec, bis(lambda e: need(k, e, s, True)['need'] < 0, 0.0, top)


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--bisect':
        specs = [(k, s, kind) for k in (3, 4) for s in ('Loss', 'LossRot') for kind in ('floor', 'cross')]
        with ProcessPoolExecutor(max_workers=4) as ex:
            for spec, (lo, hi) in ex.map(bisect_job, specs):
                print(spec, f'eta in [{lo:.6f}, {hi:.6f}]', flush=True)
        sys.exit(0)
    sys.exit(main())
