"""The amplifier's share of vartheta beyond the fourth moment, and what it moves (README round 507).

Sang's numerator average, his Proposition prop:numerator, comes from the release's plain fourth moment (its Lemma
lem:plain) by Hoelder, with prime amplification fitted into the moment's capacity. The release proves the moment for
two plain factors, with the capacity n_1 + n_2 + 6 kappa z <= M (its eq. old-eq:3.9); in Sang's units 2m + 6 kappa z <= 1.
His balance, eq. numerator-balance, then gives the bin average U^{(3R+1)/4 - vartheta/2}. Round 497's lever replaced the
fourth moment by a 2k-th and kept the saving vartheta/2 for every k, "a modelling assumption". With k plain factors and a
capacity of the same form, k m + 6 kappa z <= 1 (hypothetical: no such moment is proved), the same balance gives
U^{R + (1-R)/(2k) - vartheta/k} (gate C1).

In each bin's exponent vartheta then enters with the coefficient h (1 - 1/k) - l_y, the same for every bin: the reflection
cost U^vartheta = Z^{h vartheta}, less the amplifier's share h vartheta/k, less the row line's l_y vartheta. At a given
geometry the best vartheta is therefore Sang's in every bin or 0 in every bin, and the feasible set is the union of the
two cases (one linear program each). On Sang's slice the coefficient is (ell (4 - 3/k) - (1+b)/k)/2: positive for every
k >= 5/2 wherever the row count's supply ell/h > 1/5 holds (round 502), and at k = 2 negative exactly where Sang's
h/2 < l_y holds (gate C2). Every configuration keeps h/2 < l_y, so the model's bin exponent (share 1/2, Sang's vartheta)
is at most the capacity-consistent one with either vartheta; the model's feasible set contains the capacity-consistent
one, and a recorded value that the capacity-consistent lever reproduces is its value there too (gate C4).

The model is exchange.py's (round 506), levers.py's (round 498) and rotated_contour.py's (round 497); the
capacity-consistent lever changes only the amplifier's share in the numerator's exponent (gate C2). Every number here is
a statement about this exponent system, not a theorem.

Gates (exit status 1 if any fails):
  C1  exact, on random rationals (k = 2, 3, 4, 6; 400 each): with z_p = v (1 - k m)_+ the supply and the capacity
      hold, every block m <= 1/k has the exponent R + (1-R)/(2k) - vartheta/k and no block exceeds it; Sang's option 2
      (vartheta = q/(6 kappa), split at m0 = (1 - 6 kappa L)/k) has the same exponent on [m0, 1/k], and the absolute
      count at m0 exceeds it by (R - (6 kappa - 2q) L)/(2k), Sang's "/4" at k = 2, so his short gate does not depend
      on k. At k = 2 the balance is Sang's eq. numerator-balance
  C2  the coefficients. With the share 1/2 the classes here reproduce exchange.py's and levers.py's arrays at k = 2
      and 3 (1e-14). With the share 1/k they differ by vartheta (1/2 - 1/k) in the numerator's exponent and nothing
      else, which moves every bin by h vartheta (1/2 - 1/k) (1e-14). The functions install() puts in place give the
      share-1/k arrays with vartheta = 0 for k != 2 (1e-14). Exact on Sang's slice over a rational grid:
      h (1 - 1/k) - l_y = (ell (4 - 3/k) - (1+b)/k)/2; ell/h > 1/5 is ell > (1+b)/7; for k in {5/2, 3, 4, 6} the
      coefficient is positive wherever ell > (1+b)/7; at k = 2 it is negative exactly where ell < (1+b)/5, which is
      h/2 < l_y. Each of levers.py's fifteen configurations keeps the row h/2 < l_y, on the slice (levers.py) and off
      it (highfloor.py's reading, with l_y < 1/2 dropped)
  C3  at 0.87 (round 506's frame), with the share 1/k: need(0.87) at k = 2 equals the model's 0.0064390; at k = 9/4,
      0.0043686 with Sang's vartheta, below vartheta = 0's 0.0044666; at k = 5/2, 0.0020839 with vartheta = 0, below
      Sang's 0.0028442; at k = 3, 0.0006734 with Sang's vartheta (the bins binding) and FLOOR_NEED with vartheta = 0
      (floor bin, low rows), ROT_NEED with the rotated floor. With vartheta = 0 the bins stop binding at K_ZERO, and with
      the rotated floor need changes sign at K0_ZERO; with Sang's vartheta at K_MAX and K0_MAX (each bracketed by
      +-0.01). Dropping the rows that serve only the amplifier (the short gate, and Sang's 21/100 for the row count's
      1/5) leaves the vartheta = 0 brackets unchanged (1e-9). Round 506's K_STAR and K0_ROT lie below K_ZERO and K0_ZERO
  C4  the recorded values: each committed script that uses a moment other than the fourth is rerun with install() in
      place (vartheta = 0 and the share 1/k for k != 2). Every gate of rotated_contour.py, levers.py, offslice.py,
      crossing.py, lowerend.py, highfloor.py and lowbudget.py (rounds 497-503) passes except offslice.py's I1, which
      checks the model's own formula, share 1/2 included, against exponent_lp.py. exchange.py (round 506) fails exactly
      H2 and H4, its moment thresholds, and H5, where at kappa = 1 the rotated floor's need at k = 3 is -0.0004728 against
      -0.0004730
"""
import os
import re
import subprocess
import sys
import random
import importlib
from fractions import Fraction as Fr
import numpy as np
from concurrent.futures import ProcessPoolExecutor
import exchange as X
import highfloor as HF
import levers as LV
import offslice as O
import rotated_contour as RC

XS, XL, DL, DS = RC.XS, RC.XL, RC.DL, RC.DS
K_ZERO, K_MAX = 2.810390, 3.191170          # where the bins stop binding (bisection, 20 steps): vartheta = 0, Sang's
K0_ZERO, K0_MAX = 2.841055, 3.247524        # with the rotated floor, where need crosses 0 (bisection, 20 steps)
NEED = {(2.25, 'max'): 0.0043686, (2.25, 'zero'): 0.0044666, (2.5, 'max'): 0.0028442, (2.5, 'zero'): 0.0020839,
        (3.0, 'max'): 0.0006734}
RERUN = ['exchange', 'levers', 'rotated_contour', 'offslice', 'crossing', 'lowerend', 'highfloor', 'lowbudget']
EXPECT_FAIL = {'exchange': {'H2', 'H4', 'H5'}, 'offslice': {'I1'}}


class Cap(X.Mixed):
    """exchange.Mixed with the amplifier's share of vartheta 1/2 ('model') or 1/k ('cap'), vartheta Sang's or 0, and
    optionally without the rows that serve only the amplifier."""

    def __init__(self, kappa, share='cap', theta='max', amp_rows=True, **kw):
        self.share, self.theta, self.amp_rows = share, theta, amp_rows
        super().__init__(kappa, **kw)

    def sh(self):
        return 0.5 if self.share == 'model' else 1 / self.k

    def coeffs(self, d, x, R, reflection_cost=True):
        th = np.minimum(np.minimum(self.lam * self.tau * x * d, d / 2), 1 / 10) * (self.theta == 'max')
        K = 5 / 6 - self.w * (1 - R) + th * (1 - self.sh())
        z = 0 * d * x
        return 1 / 2 + d / 2 + K + z, -K + z, -(1 / 2 + th) + z, -1 / 2 + x * d + K + z

    def small_max(self, v):
        lx, ly, ell, s0 = v[:4]
        h = 1 - lx + ell
        th = XS * self.DS * min(ell / h, self.tau) * (self.theta == 'max')
        return (1 / 2 + self.DS / 2 - ly * (1 / 2 + th) - s0 - ell / 2 + XS * self.DS * ell
                + h * (5 / 6 - self.w * (1 - self.Rs) + th * (1 - self.sh()))).max()

    def fixed_rows(self):
        rows = super().fixed_rows()
        if self.amp_rows:
            return rows
        out = []
        for n, r, b in rows:
            if n == 'short gate':
                continue
            if n == 'ell/h>21/100':
                n, r, b = 'ell/h>1/5', [-1 / 5, 0, -4 / 5, 0, 0], -1 / 5 - 1e-9
            out.append((n, r, b))
        return out


class CapLever(LV.Lever):
    """levers.Lever with the same switches. On Sang's slice vartheta's coefficient h (1 - s) - l_y is
    -(1+b) s/2 + ell (4 - 3s)/2, s the share."""

    def __init__(self, kappa, share='cap', theta='max', **cfg):
        self.share, self.theta = share, theta
        super().__init__(kappa, **cfg)

    def sh(self):
        return 0.5 if self.share == 'model' else 1 / self.k

    def coeffs(self, d, x):
        w, R = 1 - 1 / (2 * self.k), self.count(d, x)
        th = np.minimum(np.minimum(self.lam * self.tau * x * d, d / 2), 1 / 10) * (self.theta == 'max')
        s = self.sh()
        return (-1 / 4 + d / 2 - th * s / 2 - w * (1 - R) / 2 + 0 * x, 1 / 6 - th * s / 2 - w * (1 - R) / 2 + 0 * x,
                5 / 4 + x * d + th * (4 - 3 * s) / 2 - 3 * w * (1 - R) / 2 + 0 * x)


# The capacity-consistent lever as replacements for the committed classes' methods: for k != 2, vartheta = 0 (gate C2
# checks them against Cap and CapLever); for k = 2 the committed methods unchanged.
_sys_init, _sys_parts = RC.System.__init__, RC.System.parts
_lev_coeffs, _lev_parts = LV.Lever.coeffs, LV.Lever.parts
_off_coeffs, _off_small = O.OffSlice.coeffs, O.OffSlice.small_max


def sys_init(self, kappa, k=2, tau=None, mode='sang', gram='paper'):
    _sys_init(self, kappa, k=k, tau=tau, mode=mode, gram=gram)
    if k != 2:
        w, R = 1 - 1 / (2 * k), RC.Rk(DL, XL, kappa)
        self.e0 = (-1 / 4 + DL / 2 - w * (1 - R) / 2).ravel()
        self.eb = (1 / 6 - w * (1 - R) / 2).ravel()
        self.el = (5 / 4 + XL * DL - 3 * w * (1 - R) / 2).ravel()


def small_slice(self, b, ell, ds):
    lx, ly, h = RC.geometry(b, ell)
    return (-1 / 4 + b / 6 + 5 * ell / 4 + ds / 2 + XS * ds * ell - h * (1 - 1 / (2 * self.k)) * (1 - self.Rs)).max()


def sys_parts(self, b, ell):
    out = _sys_parts(self, b, ell)
    if self.k == 2 or self.mode == 'sang':
        return out
    return [(small_slice(self, b, ell, DS), 'small delta')] + [p for p in out if p[1] != 'small delta']


def lev_coeffs(self, d, x):
    if self.k == 2:
        return _lev_coeffs(self, d, x)
    w, R = 1 - 1 / (2 * self.k), self.count(d, x)
    return (-1 / 4 + d / 2 - w * (1 - R) / 2 + 0 * x, 1 / 6 - w * (1 - R) / 2 + 0 * x,
            5 / 4 + x * d - 3 * w * (1 - R) / 2 + 0 * x)


def lev_parts(self, b, ell):
    out = _lev_parts(self, b, ell)
    if self.k == 2:
        return out
    return [(small_slice(self, b, ell, self.DS), 'small delta')] + [p for p in out if p[1] != 'small delta']


def off_coeffs(self, d, x, R, reflection_cost=True):
    if self.k == 2:
        return _off_coeffs(self, d, x, R, reflection_cost)
    K = 5 / 6 - self.w * (1 - R)
    z = 0 * d * x
    return 1 / 2 + d / 2 + K + z, -K + z, -1 / 2 + z, -1 / 2 + x * d + K + z


def off_small(self, v):
    if self.k == 2:
        return _off_small(self, v)
    lx, ly, ell, s0 = v[:4]
    h = 1 - lx + ell
    return (1 / 2 + self.DS / 2 - ly / 2 - s0 - ell / 2 + XS * self.DS * ell
            + h * (5 / 6 - self.w * (1 - self.Rs))).max()


def install():
    RC.System.__init__, RC.System.parts = sys_init, sys_parts
    LV.Lever.coeffs, LV.Lever.parts = lev_coeffs, lev_parts
    O.OffSlice.coeffs, O.OffSlice.small_max = off_coeffs, off_small


def cap(k=2.0, rot=False, share='cap', theta='max', amp_rows=True, kappa=X.KAPPA):
    return Cap(kappa, share=share, theta=theta, amp_rows=amp_rows, t=0.0, read=True, s=0.0, mode='slice', k=k, rot=rot)


def need_job(a):
    return a, X.need(cap(**a))


def c1(trials=400, seed=507):
    rng, oks = random.Random(seed), []
    for k in (2, 3, 4, 6):
        for _ in range(trials):
            R = Fr(rng.randint(1, 999), 1000)
            kap = Fr(13, 18) + Fr(rng.randint(0, 1000), 1000) * Fr(5, 18)
            L = Fr(rng.randint(1, 500), 1000)
            q = Fr(rng.randint(1, 1000), 1000) * Fr(5, 12)
            v = min(L, 1 / (6 * kap)) * Fr(rng.randint(0, 1000), 1000)
            th = q * v
            top = R + (1 - R) / (2 * k) - th / k
            z = lambda m: v * max(Fr(0), 1 - k * m)
            F = lambda m: R + (1 - R) / (2 * k) - th * m - q * z(m) / k
            ms = [Fr(i, 120) for i in range(121)]
            ok = all(z(m) <= L and (k * m + 6 * kap * z(m) <= 1 if m <= Fr(1, k) else z(m) == 0) for m in ms)
            ok &= all(F(m) == top for m in ms if m <= Fr(1, k)) and all(F(m) <= top for m in ms)
            if L < 1 / (6 * kap):
                th2 = q / (6 * kap)
                top2 = R + (1 - R) / (2 * k) - th2 / k
                m0 = (1 - 6 * kap * L) / k
                F2 = lambda m: R + (1 - R) / (2 * k) - th2 * m - q * ((1 - k * m) / (6 * kap)) / k
                ok &= all(F2(m) == top2 and (1 - k * m) / (6 * kap) <= L for m in ms if m0 <= m <= Fr(1, k))
                ok &= (R + (Fr(1, 2) - th2) * m0) - top2 == (R - (6 * kap - 2 * q) * L) / (2 * k)
            oks.append(ok)
    R, q, v, m = Fr(3, 5), Fr(1, 4), Fr(1, 7), Fr(1, 5)
    sang = (3 * R + 1) / 4 == R + (1 - R) / 4 and -q * v * m - q * v * (1 - 2 * m) / 2 == -q * v / 2
    return all(oks) and sang, len(oks)


def rerun(mod):
    """run a committed script's gates with install() in place; return (rc, passed names, failed names)."""
    p = subprocess.run([sys.executable, os.path.abspath(__file__), '--rerun', mod], capture_output=True, text=True,
                       cwd=os.path.dirname(os.path.abspath(__file__)))
    lines = [re.match(r'^(\w+) (PASS|FAIL)\b', s) for s in p.stdout.splitlines()]
    passed = [m.group(1) for m in lines if m and m.group(2) == 'PASS']
    failed = [m.group(1) for m in lines if m and m.group(2) == 'FAIL']
    return p.returncode, passed, failed


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    ok, n = c1()
    gate('C1', ok, f'{n} exact instances (k = 2, 3, 4, 6): with k plain factors the balanced blocks give '
                   f'R + (1-R)/(2k) - vartheta/k and no block exceeds it; option 2 keeps the short gate, '
                   f'(R - (6 kappa - 2q) L)/(2k) <= 0, for every k; at k = 2 this is Sang\'s eq. numerator-balance')

    dev_m = dev_s = dev_i = 0.0
    for k in (2.0, 3.0):
        a, b = cap(k=k, share='model'), X.reading(k=k)
        dev_m = max(dev_m, np.abs(a.C - b.C).max())
        la, lb = CapLever(3 / 4, share='model', k=k), LV.Lever(3 / 4, k=k)
        dev_m = max(dev_m, *(np.abs(getattr(la, e) - getattr(lb, e)).max() for e in ('e0', 'eb', 'el')))
    for k in (3.0, 4.0, float(LV.LINDELOF)):
        a, b = cap(k=k, share='cap'), cap(k=k, share='model')
        th = np.minimum(np.minimum(a.lam * a.tau * XL * DL, DL / 2), 1 / 10).ravel()
        dK = th * (1 / 2 - 1 / k)
        dev_s = max(dev_s, np.abs(a.C[0] - b.C[0] - dK).max(), np.abs(a.C[1] - b.C[1] + dK).max(),
                    np.abs(a.C[2] - b.C[2]).max(), np.abs(a.C[3] - b.C[3] - dK).max())
        z = cap(k=k, theta='zero')
        o = X.reading(k=k)
        dev_i = max(dev_i, max(np.abs(np.ravel(p) - q).max()
                               for p, q in zip(off_coeffs(o, DL, XL, o.count(DL, XL)), z.C)))
        lz, lo = CapLever(3 / 4, theta='zero', k=k), LV.Lever(3 / 4, k=k)
        dev_i = max(dev_i, max(np.abs(np.ravel(p) - getattr(lz, e)).max()
                               for p, e in zip(lev_coeffs(lo, DL, XL), ('e0', 'eb', 'el'))))
    ok_e = True
    for kk in (Fr(2), Fr(5, 2), Fr(3), Fr(4), Fr(6)):
        for bi in range(0, 21):
            for li in range(1, 41):
                b, ell = Fr(bi, 100), Fr(li, 200)
                h, ly = (1 + b + 3 * ell) / 2, (1 + b - ell) / 2
                c = h * (1 - 1 / kk) - ly
                ok_e &= c == (ell * (4 - 3 / kk) - (1 + b) / kk) / 2
                ok_e &= (ell / h > Fr(1, 5)) == (ell > (1 + b) / 7)
                if kk >= Fr(5, 2) and ell > (1 + b) / 7:
                    ok_e &= c > 0
                if kk == 2:
                    ok_e &= (c < 0) == (ell < (1 + b) / 5) == (h / 2 < ly)
    kept = all('h/2<ly' in {r[0] for r in LV.Lever(3 / 4, **cfg).hard_rows()}
               and 'h/2<ly' in {n for n, _, _ in HF.Reading(3 / 4, drop_ly=True, read=True, s=0.0, mode='inside',
                                                            **cfg).fixed_rows()}
               for _, cfg, _ in LV.CONFIGS)
    ok = dev_m < 1e-14 and dev_s < 1e-14 and dev_i < 1e-14 and ok_e and kept
    gate('C2', ok, f'share 1/2 reproduces exchange.py\'s and levers.py\'s arrays (max deviation {dev_m:.0e}); share 1/k '
                   f'moves the numerator\'s exponent by vartheta (1/2 - 1/k) only (max deviation {dev_s:.0e}); '
                   f'install()\'s functions equal vartheta = 0 with share 1/k (max deviation {dev_i:.0e}); on Sang\'s '
                   f'slice the coefficient is (ell (4 - 3/k) - (1+b)/k)/2, positive for k >= 5/2 where ell > (1+b)/7, '
                   f'negative at k = 2 exactly where h/2 < l_y; the row h/2 < l_y in all fifteen configurations, '
                   f'on the slice and off it with l_y < 1/2 dropped')

    br = [(K_ZERO - 0.01, 'zero', False), (K_ZERO + 0.01, 'zero', False), (K_MAX - 0.01, 'max', False),
          (K_MAX + 0.01, 'max', False), (K0_ZERO - 0.01, 'zero', True), (K0_ZERO + 0.01, 'zero', True),
          (K0_MAX - 0.01, 'max', True), (K0_MAX + 0.01, 'max', True)]
    jobs = ([dict(k=2.0, share=s) for s in ('model', 'cap')]
            + [dict(k=k, theta=t) for k, t in NEED] + [dict(k=3.0, theta='zero'), dict(k=3.0, theta='zero', rot=True)]
            + [dict(k=k, theta=t, rot=r) for k, t, r in br]
            + [dict(k=k, theta=t, rot=r, amp_rows=False) for k, t, r in br if t == 'zero'])
    with ProcessPoolExecutor(max_workers=4) as ex:
        res = list(ex.map(need_job, jobs))
    get = lambda **a: next(r for j, r in res if j == a)
    m2, c2 = get(k=2.0, share='model'), get(k=2.0, share='cap')
    z3, r3 = get(k=3.0, theta='zero'), get(k=3.0, theta='zero', rot=True)
    ok = abs(m2['need'] - X.SANG_NEED) < 2e-6 and abs(c2['need'] - m2['need']) < 1e-12
    ok &= all(abs(get(k=k, theta=t)['need'] - v) < 2e-6 for (k, t), v in NEED.items())
    ok &= get(k=2.25, theta='max')['need'] < get(k=2.25, theta='zero')['need']
    ok &= get(k=2.5, theta='zero')['need'] < get(k=2.5, theta='max')['need']
    ok &= 'E' in get(k=3.0, theta='max')['walls']
    ok &= abs(z3['need'] - X.FLOOR_NEED) < 1e-6 and z3['walls'] == X.FLOOR_WALLS and z3['emax'] < -1e-7
    ok &= abs(r3['need'] - X.ROT_NEED) < 1e-6
    fl = lambda r: abs(r['need'] - X.FLOOR_NEED) < 2e-7 and r['emax'] < -1e-7
    n = [get(k=k, theta=t, rot=r) for k, t, r in br]
    ok &= not fl(n[0]) and fl(n[1]) and not fl(n[2]) and fl(n[3])
    ok &= n[4]['need'] > 0 > n[5]['need'] and n[6]['need'] > 0 > n[7]['need']
    ok &= all(abs(get(k=k, theta=t, rot=r, amp_rows=False)['need'] - get(k=k, theta=t, rot=r)['need']) < 1e-9
              for k, t, r in br if t == 'zero')
    ok &= X.K_STAR < K_ZERO < K_MAX and X.K0_ROT < K0_ZERO < K0_MAX
    gate('C3', ok, f'need(0.87) with the share 1/k: k = 2 {c2["need"]:+.7f} (the model\'s); k = 9/4 '
                   f'{get(k=2.25, theta="max")["need"]:+.7f} (Sang\'s vartheta) and {get(k=2.25, theta="zero")["need"]:+.7f} '
                   f'(0); k = 5/2 {get(k=2.5, theta="max")["need"]:+.7f} and {get(k=2.5, theta="zero")["need"]:+.7f}; k = 3 '
                   f'{get(k=3.0, theta="max")["need"]:+.7f} (bins binding) and {z3["need"]:+.7f}, {r3["need"]:+.7f} with the '
                   f'rotated floor. The bins stop binding at k = {K_ZERO} (2k = {2 * K_ZERO:.3f}) with vartheta = 0 and '
                   f'{K_MAX} (2k = {2 * K_MAX:.3f}) with Sang\'s; need crosses 0 with the rotated floor at k = {K0_ZERO} '
                   f'(2k = {2 * K0_ZERO:.3f}) and {K0_MAX}; the amplifier\'s rows do not move the vartheta = 0 brackets. '
                   f'Round 506: {X.K_STAR} and {X.K0_ROT}')

    ok, lines = True, []
    for mod in RERUN:
        rc, passed, failed = rerun(mod)
        want = EXPECT_FAIL.get(mod, set())
        ok &= set(failed) == want and len(failed) == len(want) and rc == (1 if want else 0) and len(passed) > 0
        lines.append(f'{mod} {len(passed)} pass' + (f', fail {", ".join(failed)}' if failed else ''))
    gate('C4', ok, 'with the share 1/k and vartheta = 0 for k != 2: ' + '; '.join(lines))
    print(f'{fails} gate(s) failed' if fails else 'all gates pass')
    return 1 if fails else 0


if __name__ == '__main__':
    if len(sys.argv) > 2 and sys.argv[1] == '--rerun':
        install()
        sys.exit(importlib.import_module(sys.argv[2]).main())
    sys.exit(main())
