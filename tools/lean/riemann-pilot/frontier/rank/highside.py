"""The high side's first rung (FIVE-SIXTHS.md, section 11).

Sections 7-9 leave the release-level boundary at 0.8748866, with the bins delta >= 1/8 ('E') binding at every sigma
(slotsplit.py's S3).  This script asks what those bins need, in the release-level configuration: section 8's program
(slotsplit.Five2X across the slice) at crossing cost c = 1, with Sang's rotation, round 498's readings, Xu-Sang's
counts R_kappa and fourth moment (k = 2), the trilinear sigma = 2/3, and the rows l <= 1/5, l >= 1/6 and l_y < 1/2
dropped as in S6; every boundary is bootstrapped from kappa = 3/4 (slotsplit.boot).  A bin is a class of Poisson rows
with detector parameter delta = 2a - 1 and amplitude ratio x = q/delta (Xu-Sang's notation); its endpoint is
E = C0 + C1 l_x + C2 l_y + C3 l - s0 (offslice.OffSlice.coeffs), with the count entering through
K = 5/6 - w (1 - R) + vartheta/2, w = 1 - 1/(2k).  A saving U^s = Z^{s h} on a bin, h = 1 - l_x + l, lowers E by
s h.  Every number is a statement about the pilot's model of the release's exponent system, not a theorem about
L-functions.

Gates (exit status 1 if any fails):
  H1  what binds: the release-level boundary is 0.8748866 (2e-6), with walls E, the low side and the slice; at its
      optimum the bins within 1e-7 of their endpoint all lie at x = 1/2 with delta in [0.4688, 0.4702] (1e-4), and the
      tight low rows are the Gram bound's exceptional term ('low:P^(1/6)') and the slice.
  H2  relief on the bins delta >= 1/8: a saving U^s on the bins delta in [0.44, 0.50] only gives 0.8748474 at s = 0.01
      and at s = 0.05 alike (1e-6); on every bin delta >= 1/8, 0.8730362 at s = 0.01 and 0.8711404 at s = 0.02
      (1e-6), a slope (0.8748866 - B)/s between 0.18 and 0.19 at both; 0.8667866 at s = 0.045 with the floor bin among
      the walls and E not; density-hypothesis counts R = 1 - delta on the bins delta >= 1/8 only, and round 498's
      counts = 'dh' (the small bins too), give 0.8667866 as well (1e-6).
  H3  stronger moments: the 2k-th moment's weight w = 1 - 1/(2k) at k = 5/2, 3, 4 gives 0.8712795, 0.8692279,
      0.8674539 with E among the walls, and at k = 6 0.8667866 with the floor bin and not E (1e-6).
  H4  the next rung: with density-hypothesis counts and a saving U^{0.001} on the floor bin and the small bins
      (slotsplit.Five2's eta_L), 13/15 (2e-7) at (l_x, l_y, l) = (2/5, 2/5, 1/5) (1e-4), with E and Sang's rotation
      condition h/2 < l_y among the walls; with U^{0.0005}, 0.8667067 with the floor bin among the walls (1e-6); with
      sigma = 1/2 and U^{0.001}, 13/15 again.
  H5  where the counts come from: Xu-Sang's R_kappa = 1 - delta + (alpha - delta) delta P/(2 J) recomputed with the long
      witness's slope alpha' in place of alpha = 5/6 (the slope of the release's e(r) = max(1, (1 + 5r)/6)), the long
      branch taken as (alpha' - delta)_+: alpha' = 5/6 reproduces the model's count (1e-15) and 0.8748866 (2e-6);
      alpha' = 3/4 gives 0.8741816, alpha' = 1/2 gives 0.8714461 with E among the walls, alpha' = 1/8 gives 0.8667866
      with the floor bin among the walls, the count then being 1 - delta exactly on every bin delta >= 1/8 (1e-6).  The
      plain moment's capacity constant 6 (m1 + m2 + 6 kappa z <= 1, so c = 1/(3 kappa)) replaced by 2 gives 0.8733798.
      And the algebra: on every bin, R_kappa - (1 - delta) is half the parallel combination ab/(a + b) of the long
      branch a = alpha - delta and the short branch b = delta P_kappa/D_kappa (1e-12).
  H6  T3's pointwise route, in exact arithmetic: at S6's first-branch dyad (M', l') = (2t, t), t = 5572/10000 (O = 0,
      H = M', z_a = l', v = T = 2M' + l' - 1, the rest 0), crossing.energy is M' + (M' + l' - 1), the column term's
      excess 3t - 1; replacing the hybrid factors (K + NB) B (N + L + (NL)^{2/3}) by K L N B, square-root
      cancellation in each (k, P) pair's sum, changes the energy to E - max(H, v + l_b) + u + H = M' + l', an excess
      t; the ratio t/(3t - 1) = 0.8297 (1e-4) is the route's effective crossing cost, against the break-even
      c in (0.16, 0.165) of S6.

Usage: python3 highside.py     (a few seconds; imports slotsplit.py and fivesixths.py, and ../wall78)
"""
import os
import sys
from fractions import Fraction as Fr
from concurrent.futures import ProcessPoolExecutor

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'wall78'))
import slotsplit as SS     # noqa: E402
import fivesixths as F     # noqa: E402
import crossing as X       # noqa: E402

O = F.O
DL, XL = O.DL, O.XL
ALPHA = 5 / 6
FAILS = []


def gate(name, ok, msg):
    print(f'{name}: {"PASS" if ok else "FAIL"}  {msg}', flush=True)
    if not ok:
        FAILS.append(name)


def rk(d, x, kappa, alpha=ALPHA, cap=6.0):
    """Xu-Sang's eq. row-functions with the long witness's slope alpha and the plain moment's capacity constant cap
    (m1 + m2 + cap kappa z <= 1, so c = 2/(cap kappa)); the long branch is (alpha - delta)_+."""
    c = 2 / (cap * kappa)
    D = 3 - (1 + 2 * c) * x
    P = (2 - 2 * c * x) * (1 - x)
    a = np.maximum(alpha - d, 0.0)
    return 1 - d + a * d * P / (2 * (a * D + d * P))


class Window(SS.Five2X):
    """a saving U^SAVE (or density-hypothesis counts, MODE = 'dh') on the bins with delta in WIN only."""
    WIN, SAVE, MODE = (1 / 8, 5 / 6), 0.0, 'save'

    def __init__(self, kappa, **kw):
        super().__init__(kappa, **kw)
        m = ((DL >= self.WIN[0] - 1e-12) & (DL <= self.WIN[1] + 1e-12) & (XL >= -1)).ravel()
        if self.MODE == 'dh':
            Cn = np.stack([c.ravel() for c in self.coeffs(DL, XL, 1 - DL + 0 * XL)])
            self.C[:, m] = Cn[:, m]
        s = self.SAVE
        self.C[0, m] -= s
        self.C[1, m] += s
        self.C[3, m] -= s


class W44(Window):
    WIN, SAVE = (0.44, 0.50), 0.01


class W44b(Window):
    WIN, SAVE = (0.44, 0.50), 0.05


class WE1(Window):
    SAVE = 0.01


class WE2(Window):
    SAVE = 0.02


class WE45(Window):
    SAVE = 0.045


class WDH(Window):
    MODE = 'dh'


class Alpha(SS.Five2X):
    """Xu-Sang's count with the long witness's slope ALPHA and the plain capacity constant CAP."""
    ALPHA, CAP = ALPHA, 6.0

    def count(self, d, x):
        return (1 - d + 0 * x) if self.counts == 'dh' else rk(d, x, self.kappa, self.ALPHA, self.CAP)


class A56(Alpha):
    ALPHA = 5 / 6


class A34(Alpha):
    ALPHA = 3 / 4


class A12(Alpha):
    ALPHA = 1 / 2


class A18(Alpha):
    ALPHA = 1 / 8


class Cap2(Alpha):
    CAP = 2.0


def job(a):
    key, cfg, kw, klass = a
    return key, SS.boot((cfg, kw, klass))


def main():
    c1 = SS.cross_cfg(1.0)
    base = dict(sigma=2 / 3, drop=SS.D3)
    dh = dict(c1, counts='dh')
    jobs = [('base', c1, base, SS.Five2X), ('W44', c1, base, W44), ('W44b', c1, base, W44b),
            ('WE1', c1, base, WE1), ('WE2', c1, base, WE2), ('WE45', c1, base, WE45), ('WDH', c1, base, WDH),
            ('dh', dh, base, SS.Five2X),
            ('k2.5', dict(c1, k=2.5), base, SS.Five2X), ('k3', dict(c1, k=3), base, SS.Five2X),
            ('k4', dict(c1, k=4), base, SS.Five2X), ('k6', dict(c1, k=6), base, SS.Five2X),
            ('L1', dh, dict(base, eta_L=0.001), SS.Five2X), ('L05', dh, dict(base, eta_L=0.0005), SS.Five2X),
            ('L1s', dh, dict(base, sigma=0.5, eta_L=0.001), SS.Five2X),
            ('A56', c1, base, A56), ('A34', c1, base, A34), ('A12', c1, base, A12), ('A18', c1, base, A18),
            ('Cap2', c1, base, Cap2)]
    with ProcessPoolExecutor(4) as ex:
        res = dict(ex.map(job, jobs))
    for key, *_ in jobs:
        r = res[key]
        print(f'    {key:5s} B = {r[0]:.7f} kappa {r[1]:.5f} walls {r[2]} (l_x, l_y, l) = '
              f'({r[3][0]:.4f}, {r[3][1]:.4f}, {r[3][2]:.4f})')
    B = {k: r[0] for k, r in res.items()}
    W = {k: r[2] for k, r in res.items()}
    near = lambda k, want, tol=1e-6: abs(B[k] - want) < tol
    # H1: what binds
    B0, kap, _, _ = res['base']
    prog = SS.Five2X(kap, **c1, **base)
    sol = prog.solve()
    v = sol['v']
    E = prog.C[0] + prog.C[1] * v[0] + prog.C[2] * v[1] + prog.C[3] * v[2] - v[3]
    nx = XL.shape[1]
    act = np.flatnonzero(E > -1e-7)
    d_act, x_act = DL[act // nx, 0], XL[0, act % nx]
    tight = sorted(n for n, r, b in sol['fixed'] if b - np.dot(r, v) < 1e-7)
    gate('H1', abs(B0 - 0.8748866) < 2e-6 and set(W['base']) == {'E', 'low side', 'slice'} and act.size > 0
         and np.all(np.abs(x_act - 0.5) < 1e-12) and abs(d_act.min() - 0.4688) < 1e-4 and abs(d_act.max() - 0.4702) < 1e-4
         and tight == ['low:P^(1/6)', 'slice'],
         f'boundary {B0:.7f}, walls {W["base"]}; {act.size} bins within 1e-7 of their endpoint, at x = '
         f'{x_act.min():.4f}..{x_act.max():.4f}, delta in [{d_act.min():.4f}, {d_act.max():.4f}]; tight rows {tight}')
    # H2: relief on the bins
    slope = [(B0 - B['WE1']) / 0.01, (B0 - B['WE2']) / 0.02]
    gate('H2', near('W44', 0.8748474) and near('W44b', 0.8748474) and near('WE1', 0.8730362)
         and near('WE2', 0.8711404) and all(0.18 <= s <= 0.19 for s in slope)
         and near('WE45', 0.8667866) and 'floor bin' in W['WE45'] and 'E' not in W['WE45']
         and near('WDH', 0.8667866) and near('dh', 0.8667866),
         f'window [0.44, 0.50]: {B["W44"]:.7f} at s = 0.01, {B["W44b"]:.7f} at s = 0.05; every bin: '
         f'{B["WE1"]:.7f} at 0.01, {B["WE2"]:.7f} at 0.02 (slopes {slope[0]:.4f}, {slope[1]:.4f}), {B["WE45"]:.7f} at '
         f'0.045 (walls {W["WE45"]}); DH counts on the bins {B["WDH"]:.7f}, counts = dh {B["dh"]:.7f}')
    # H3: stronger moments
    ks = (('k2.5', 0.8712795), ('k3', 0.8692279), ('k4', 0.8674539))
    gate('H3', all(near(k, want) and 'E' in W[k] for k, want in ks) and near('k6', 0.8667866)
         and 'floor bin' in W['k6'] and 'E' not in W['k6'],
         ', '.join(f'k = {k[1:]}: {B[k]:.7f} ({"E" if "E" in W[k] else "no E"})' for k, _ in ks)
         + f', k = 6: {B["k6"]:.7f} (walls {W["k6"]})')
    # H4: the next rung
    pt = res['L1'][3]
    gate('H4', abs(B['L1'] - 13 / 15) < 2e-7 and max(abs(pt[0] - 0.4), abs(pt[1] - 0.4), abs(pt[2] - 0.2)) < 1e-4
         and 'E' in W['L1'] and 'h/2<ly' in W['L1'] and near('L05', 0.8667067) and 'floor bin' in W['L05']
         and abs(B['L1s'] - 13 / 15) < 2e-7,
         f'DH counts and U^0.001 on the floor and small bins: {B["L1"]:.9f} (13/15 = {13 / 15:.9f}) at '
         f'({pt[0]:.4f}, {pt[1]:.4f}, {pt[2]:.4f}), walls {W["L1"]}; U^0.0005: {B["L05"]:.7f} (walls {W["L05"]}); '
         f'sigma = 1/2: {B["L1s"]:.9f}')
    # H5: where the counts come from
    kk = res['A56'][1]
    dev56 = float(np.max(np.abs(rk(DL, XL, kk) - O.Rk(DL, XL, kk))))
    dev18 = float(np.max(np.abs(rk(DL, XL, kk, alpha=1 / 8) - (1 - DL + 0 * XL))))
    c = 1 / (3 * kk)
    Dk = 3 - (1 + 2 * c) * XL
    Pk = (2 - 2 * c * XL) * (1 - XL)
    a, b = ALPHA - DL, DL * Pk / Dk
    par = float(np.max(np.abs((O.Rk(DL, XL, kk) - (1 - DL)) - a * b / (2 * (a + b)))))
    gate('H5', dev56 < 1e-15 and near('A56', 0.8748866, 2e-6) and near('A34', 0.8741816) and near('A12', 0.8714461)
         and 'E' in W['A12'] and near('A18', 0.8667866) and 'floor bin' in W['A18'] and dev18 < 1e-6
         and near('Cap2', 0.8733798) and par < 1e-12,
         f'slope 5/6 reproduces the count (deviation {dev56:.1e}) and {B["A56"]:.7f}; 3/4: {B["A34"]:.7f}; 1/2: '
         f'{B["A12"]:.7f} (walls {W["A12"]}); 1/8: {B["A18"]:.7f} (walls {W["A18"]}), count minus (1 - delta) '
         f'{dev18:.1e}; plain capacity constant 2: {B["Cap2"]:.7f}; R - (1 - delta) = ab/(2(a + b)) within {par:.1e}')
    # H6: T3's pointwise route, exact
    t = Fr(5572, 10000)
    Mp, lp = 2 * t, t
    T = 2 * Mp + lp - 1
    w = (Fr(0), Mp, Fr(0), Fr(0), Fr(0), Fr(0), lp, T, Fr(0), Fr(0))
    En, Tn, y = X.energy(w, lp)
    o, h, a0, n0, s0, b0, za, vv, lb, e = w
    u = min(vv, za, (vv + za) / 3)
    Epw = En - max(h, vv + lb) + u + h
    ratio = (Epw - Mp) / (En - Mp)
    gate('H6', Tn == T and y == T and En == Mp + (Mp + lp - 1) and Epw == Mp + lp and ratio == t / (3 * t - 1)
         and abs(float(ratio) - 0.8297) < 1e-4,
         f'at (M\', l\') = (2t, t), t = {t}: release {En} = M\' + {En - Mp} (3t - 1), pointwise {Epw} = M\' + '
         f'{Epw - Mp} (t); effective crossing cost t/(3t - 1) = {float(ratio):.4f}')
    if FAILS:
        print('FAILED:', ', '.join(FAILS))
        sys.exit(1)
    print('all gates pass')


if __name__ == '__main__':
    main()
