"""The high side's first rung (FIVE-SIXTHS.md, sections 11 and 13).

Sections 7-9 leave the release-level boundary at 0.8748866, with the bins delta >= 1/8 ('E') binding at every sigma
(slotsplit.py's S3).  This script asks what those bins need, in the release-level configuration: section 8's program
(slotsplit.Five2X across the slice, which enforces the small bins delta < 1/8 since section 15) at crossing cost c = 1,
with Sang's rotation, round 498's readings, the third Gram term soft (round 499's S3, slotsplit.cross_cfg's soft_third:
Xu-Sang's l_y - l > 11b/6 dropped and the third term carried in the low side's maximum), Xu-Sang's counts R_kappa and
fourth moment (k = 2), the trilinear sigma = 2/3, and the rows l <= 1/5, l >= 1/6 and l_y < 1/2 dropped as in S6; every
boundary is bootstrapped from kappa = 3/4 (slotsplit.boot).  A bin is a class of Poisson rows with detector parameter
delta = 2a - 1 and amplitude ratio x = q/delta (Xu-Sang's notation); its endpoint is
E = C0 + C1 l_x + C2 l_y + C3 l - s0 (offslice.OffSlice.coeffs), with the count entering through
K = 5/6 - w (1 - R) + vartheta/2, w = 1 - 1/(2k).  A saving U^s = Z^{s h} on a bin, h = 1 - l_x + l, lowers E by s h.
Every number is a statement about the pilot's model of the release's exponent system, not a theorem about L-functions.

Gates (exit status 1 if any fails):
  H1  what binds: the release-level boundary is 0.8748866 (2e-6), with walls E, the low side and the slice; at its
      optimum the bins within 1e-7 of their endpoint all lie at x = 1/2 with delta in [0.4688, 0.4702] (1e-4), and the
      tight low rows are the Gram bound's exceptional term ('low:P^(1/6)') and the slice.
  H2  relief on the bins delta >= 1/8: a saving U^s on the bins delta in [0.44, 0.50] only gives 0.8748474 at s = 0.01
      and at s = 0.05 alike (1e-6), its binding bins then lying just outside the window (within 1e-3 below 0.44 and
      above 0.50, at x = 1/2); on every bin delta >= 1/8, 0.8730362 at s = 0.01 and 0.8711703 at s = 0.02 (1e-6), a
      slope (0.8748866 - B)/s between 0.18 and 0.19 at both; 0.8693956 at s = 0.045 and at s = 0.1, with the small bins
      delta < 1/8 among the walls and neither E nor the floor bin, and density-hypothesis counts R = 1 - delta on the
      bins delta >= 1/8 only give 0.8693956 as well (1e-6); round 498's counts = 'dh', the small bins included, give
      0.8667866 (1e-6), with the floor bin among the walls and not the small bins.  With every bin delta >= 1/8 removed
      and the short gate, which their counts set, dropped (NoBins), the program gives 0.8693956 as well (1e-6), with
      the small bins among the walls, and its value is nondecreasing in kappa at 9 points from its fixed point, 2B - 1,
      to 3/4.  The counts and savings on those bins enter only their rows and the short gate, so at every kappa any
      relief confined to them gives at least NoBins's value.  If that value is nondecreasing on the whole interval,
      such relief, bootstrapped from 3/4, has no stage below 0.8693956 while its values stay below 7/8: a sampled
      check, not a proof.
  H3  stronger moments, with the amplifier's share as README round 507 has it beyond the fourth moment.  Its two
      capacity-consistent levers are vartheta = 0 in every bin (lam = 0 on the bins delta >= 1/8, and ThetaZero on the
      small bins) and Sang's vartheta at the share vartheta/k (ShareK, on the bins and the small bins; the floor bin
      has vartheta = 0).  The 2k-th moment's weight w = 1 - 1/(2k) at k = 5/2, 3 and 4 gives, with vartheta = 0,
      0.8715666, 0.8693505 and 0.8674755 with E among the walls; at k = 5 and 5.25, 0.8668677 and 0.8668015 with the
      small bins among the walls and not E; at k = 6, 0.8667866 with the floor bin and not E (1e-6).  At each of those
      six k the share vartheta/k gives more, so vartheta = 0 is the better lever there.  The model's share vartheta/2
      at every k gives 0.8712795, 0.8692279 and 0.8674539 at k = 5/2, 3 and 4 (1e-6), below the capacity-consistent
      values by less than 4e-4.
  H4  beyond the first rung, with density-hypothesis counts and Sang's rotation kept.  (i) A saving on the floor bin
      and the small bins only (slotsplit.Five2's eta_L): U^{0.001} gives 13/15 (2e-7) at (l_x, l_y, l) =
      (2/5, 2/5, 1/5) (1e-4), with E and the rotation's condition h/2 < l_y among the walls; U^{0.0005} gives 0.8667067
      with the floor bin among the walls (1e-6); with sigma = 1/2 and U^{0.001}, 13/15 again.  (ii) A saving U^eta on
      every bin, the floor bin and the small bins included: at sigma = 2/3, 0.8657615 at eta = 0.01 and 0.8548781 at
      eta = 0.1 (1e-6), each with the floor bin and h/2 < l_y among the walls and E not, and 41/48 (2e-7) at eta = 0.3,
      at (1/4, 1/2, 1/4) (1e-4), with h/2 < l_y, the low side and l_x > l among the walls; at sigma = 1, 13/15 (2e-7)
      at eta = 0.1 with the row loss among the walls.  With the numerator unrotated (vartheta = 0 and h/2 < l_y
      dropped, section 3's reading), sigma = 2/3 and eta = 0.3 give 28/33 (2e-7).  (iii) In exact arithmetic: under
      h/2 <= l_y, l <= l_x, b >= 0 and M + l <= 1 the low side is at least 5/6 + (1 + l_x - 3l)/24 >= 41/48, with
      equality at (1/4, 1/2, 1/4); fivesixths.low is 41/48 there and obeys both bounds at 4000 random rational points of
      that region.  (iv) That point violates Xu-Sang's l_y - l > 11b/6, which the soft third drops: with it kept
      (soft_third = False) eta = 0.3 gives 253/294 (2e-7) at (16/49, 22/49, 11/49) (1e-4), with h/2 < l_y, the slice and
      l_y - l > 11b/6 among the walls; the low side's own linear program with that row is 253/294 (1e-9), and
      fivesixths.low is 253/294 at that point.
  H5  where the counts come from: Xu-Sang's R_kappa = 1 - delta + (alpha - delta) delta P/(2 J) recomputed with the long
      witness's slope alpha' in place of alpha = 5/6 (the slope of the release's e(r) = max(1, (1 + 5r)/6)), the long
      branch taken as (alpha' - delta)_+: alpha' = 5/6 reproduces the model's count (1e-15) and 0.8748866 (2e-6);
      alpha' = 3/4 gives 0.8741816, alpha' = 1/2 gives 0.8714461 with E among the walls, alpha' = 1/8 gives 0.8677780
      with the small bins among the walls and not the floor bin (1e-6), the count then being 1 - delta exactly on every
      bin delta >= 1/8 (1e-6), and above it on the small bins, where the long branch 1/8 - delta is positive;
      alpha' = 3/200 gives 0.8667974 with the small bins among the walls, and alpha' = 1/80 gives 0.8667866 with the
      floor bin among the walls and not the small bins (1e-6).  The
      plain moment's capacity constant 6 (m1 + m2 + 6 kappa z <= 1, so c = 1/(3 kappa)) replaced by 2 gives 0.8733798
      from the closed form, with c > 6/13, outside the range of Xu-Sang's balance, and with the plain selection z_P at
      the balance above the prime supply l/h of that optimum on between 10% and 16% of the bins; the supply can only
      raise the count, so 0.8733798 is a lower bound for that variant's boundary (with the constant 6, z_P stays below
      the supply 1/5 that Xu-Sang's count assumes, so that variant amplifies no less).  And the algebra: at every bin
      of the grid delta >= 1/8, at the bootstrap's kappa, R_kappa - (1 - delta) is half the parallel combination
      ab/(a + b) of the long branch a = alpha - delta and the short branch b = delta P_kappa/D_kappa (1e-12).
  H6  T3's pointwise route.  In exact arithmetic: at S6's first-branch dyad (M', l') = (2t, t), t = 5572/10000 (O = 0,
      H = M', z_a = l', v = T = 2M' + l' - 1, the rest 0), crossing.energy is M' + (M' + l' - 1), the column term's
      excess 3t - 1; replacing the hybrid factors (K + NB) B (N + L + (NL)^{2/3}) by K L N B, square-root
      cancellation in each (k, P) pair's sum, changes the energy to E - max(H, v + l_b) + u + H = M' + l', an excess
      t, the ratio t/(3t - 1) = 0.8297 (1e-4); at the first-branch dyad (8/5, 1/10) the same ratio is 1/7, so it is a
      property of the dyad, not a crossing cost.  In the program: the low side charging l/2 (the pointwise excess at
      the tuple's own first-branch dyad) in place of c mu/2 gives 0.9487180 (1e-6), above 0.8748866, so the cheaper of
      the two charges, min(mu, l)/2, leaves the boundary at 0.8748866.
  H7  where the counts would have to improve: density-hypothesis counts on a window of delta only give 0.8748866 on
      [4/7, 5/6] and on [1/8, 0.45] (2e-6), 0.8746407 on [0.40, 0.55], 0.8735094 on [0.30, 0.65], 0.8712876 on
      [0.20, 0.75] (1e-6), and on [1/8, 0.70] between 0.8714881 and 0.8714946 (1e-6), with the small bins among the
      walls: the lower value enforces them as a relaxation, the upper on the region l >= tau h, where that relaxation is
      exact (WinW3A); H9 checks the argument that the exact boundary lies between them.  Each is above the first rung
      by more than 1e-3; in the three windows around 0.47 the binding bins lie just outside the window (within 1e-3, at
      x = 1/2), and a saving U^{0.05} on [0.40, 0.55] gives the same value as density-hypothesis counts there.
  H8  the T1-T3 trade-off (FIVE-SIXTHS.md, section 14), with T2 strong: density-hypothesis counts and a saving U^{0.2}
      on every bin.  Unrotated (vartheta = 0 in every bin, h/2 < l_y dropped, the small rows' z-line z0 = 1/6 + 1/100 as
      in fivesixths' runs without rotation), the program matches B(sigma, c) = 5/6 + (2 sigma - 1)_+
      min(1/(6(4 sigma + 1)), c/(12c + 5 - 4 sigma)) within 1e-6 at the 20 points sigma in {1/2, 0.6, 2/3, 3/4, 1}, c in
      {0.01, 0.1, 0.3, 1}, with no bin among the walls (neither E nor the floor bin nor the small bins), so the value is
      the low side's.  In exact arithmetic that law is the low side's least value at 20 rational (sigma, c), sigma in
      {3/5, 2/3, 3/4, 1}, c in {1/100, 1/10, 3/10, 1, 3}: with u = M - 2l the low side less 5/6 is at least
      u/12 + max(0, c(3l + u - 1)/2, (1 - (5 - 4 sigma) l - 2u)/8), with equality at b = 0; a vertex (u, l) attains the
      law, and a convex combination of the last two terms whose coefficients of u and l are nonnegative bounds the
      expression below by it (the two cases split at c = (5 - 4 sigma)/(24 sigma - 6)).  On the diagonal
      l_x = l_y = l = t the crossing charge c(3t - 1)/2 and the row loss's charge (1 - (5 - 4 sigma) t)/8 meet at
      t = (1 + 4c)/(12c + 5 - 4 sigma), with common value c(2 sigma - 1)/(12c + 5 - 4 sigma), at 12 rational (sigma, c).
      With Sang's rotation kept the program gives 5/6 + c/4 within 1e-6 at sigma in {0.55, 2/3, 3/4}, c in {0.01, 0.06},
      at (1/2, 1/2, 1/2) (1e-4), with the third Gram term soft and hard alike (Xu-Sang's l_y - l > 11b/6 among the walls
      exactly in the runs that keep it).  In exact arithmetic, under h/2 <= l_y, l <= l_x and b >= 0 the low side with a
      crossing is at least 5/6 + min(c/4, 1/48) at 4000 random rational points (sigma in {1/2, 2/3, 3/4, 1}, c in
      {1/100, 1/20, 1/12, 1/5, 1}), with equality for sigma <= 3/4 at (1/2, 1/2, 1/2) when c <= 1/12 and at
      (1/4, 1/2, 1/4) when c >= 1/12, the third Gram term soft.  Also exact: at (1/2, 1/2, 1/2), where l_y - l = 11b/6
      = 0, the low side is 5/6 + max(c/4, (4 sigma - 3)/16), equal to the bound at sigma = 3/4 + c for c <= 1/12; and
      (16/49, 22/49, 11/49), on the slice with h/2 = l_y and l_y - l = 11b/6, gives
      5/6 + 4/147 + max(0, (44 sigma - 38)/196)/2.  By linear programming over the rotated low side with a crossing, at
      sigma in {1/2, 2/3, 3/4, 0.8, 0.9, 1} and c in {0.01, 1/12, 0.1, 0.2, 1}: with the third term soft the least
      value equals that bound (1e-9) exactly where sigma <= 3/4 + c (c <= 1/12) or sigma <= 3/4 (c > 1/12), and lies
      above it by more than 1e-6 elsewhere; with Xu-Sang's l_y - l > 11b/6 kept it equals 5/6 + min(c/4, 4/147)
      exactly where sigma <= 3/4 + c (c < 16/147) or sigma <= 19/22 (c >= 16/147), and lies above it by more than 1e-6
      elsewhere; at sigma = 1 the soft value lies above the bound by more than 6e-3 at each c.

  H9  the small bins delta < 1/8 at every reported optimum.  slotsplit.Five2X enforces them as cutting planes
      (FIVE-SIXTHS.md section 15): exactly where vartheta = 0 there (ThetaZero), and as a relaxation, vartheta at its
      largest value x delta tau, while h/2 < l_y is kept; ShareK's are not enforced.  At every optimum but WW3's the
      exact small_max is at most 1e-9, and at ShareK's it is negative.  At WW3's it is positive and below 1e-5, and
      WW3A, on l >= tau h, gives a value above WW3's by less than 1e-5 with the small bins holding (1e-9).  The two
      bound WW3's exact boundary: at kappa = 3/4, the first stage of every bootstrap here, WW3's relaxation is exact
      (1e-9) and equals WW3A's least value (1e-9), so the exact boundary is at most WW3A's.  The relaxation's value
      is nondecreasing in kappa at 9 points from its own fixed point, 2B - 1, to 3/4, the interval its bootstrap moves
      in.  If it is nondecreasing on that whole interval, the exact program's bootstrap, which starts at 3/4 and lies
      above the relaxation at every kappa, has no stage below the relaxation's boundary while its values stay below
      7/8: a sampled check, not a proof.

Usage: python3 highside.py     (a few seconds; imports slotsplit.py and fivesixths.py, and ../wall78)
"""
import os
import random
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


class WE10(Window):
    SAVE = 0.1


class WDH(Window):
    MODE = 'dh'


class WinHi(Window):
    WIN, MODE = (4 / 7, 5 / 6), 'dh'


class WinLo(Window):
    WIN, MODE = (1 / 8, 0.45), 'dh'


class WinMid(Window):
    WIN, MODE = (0.40, 0.55), 'dh'


class WinW1(Window):
    WIN, MODE = (0.30, 0.65), 'dh'


class WinW2(Window):
    WIN, MODE = (0.20, 0.75), 'dh'


class WinW3(Window):
    WIN, MODE = (1 / 8, 0.70), 'dh'


class WinS(Window):
    WIN, SAVE = (0.40, 0.55), 0.05


class WinW3A(WinW3):
    """WinW3 on the region l >= tau h, where vartheta in the small bins is at its largest value exactly, so the
    enforced small bins are exact there.  Its least stage is its first, at kappa = 3/4, where WinW3's relaxation is
    exact too; that stage is the exact program's first, so its value bounds WinW3's exact boundary above (H7, H9)."""

    def fixed_rows(self):
        return super().fixed_rows() + [('l/h>=tau', [-self.tau, 0.0, -(1 - self.tau), 0.0, 0.0], -self.tau)]


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


class A015(Alpha):
    ALPHA = 3 / 200


class A0125(Alpha):
    ALPHA = 1 / 80


class NoBins(Window):
    """every bin delta >= 1/8 removed (its row made slack) and the short gate, which their counts set, dropped: what
    any relief confined to those bins can at most do (H2)."""

    def __init__(self, kappa, **kw):
        super().__init__(kappa, **kw)
        self.C[0, :] = -10.0
        self.C[1:, :] = 0.0

    def fixed_rows(self):
        return [r for r in super().fixed_rows() if r[0] != 'short gate']


class ThetaZero(SS.Five2X):
    """vartheta = 0 in the small bins too (with lam = 0 the bins delta >= 1/8 already have vartheta = 0)."""

    def small_max(self, v):
        lx, ly, ell, s0 = v[:4]
        h = 1 - lx + ell
        base = (1 / 2 + self.DS / 2 - ly / 2 - s0 - ell / 2 + O.XS * self.DS * ell
                + h * (5 / 6 - self.w * (1 - self.Rs))).max()
        return base - self.eta_L * h

    def small_rows(self):
        """the small bins exactly: vartheta = 0 makes them linear."""
        return SS.small_rows(self, 0 * self.DS * O.XS, 1 / 2)


class ShareK(SS.Five2X):
    """Sang's vartheta with the amplifier's share vartheta/k (README round 507) on the bins and the small bins: the
    reflection cost less the share, vartheta (1 - 1/k), in place of the model's vartheta/2."""

    def coeffs(self, d, x, R, reflection_cost=True):
        c0, c1, c2, c3 = super().coeffs(d, x, R, reflection_cost)
        th = np.minimum(np.minimum(self.lam * self.tau * x * d, d / 2), 1 / 10)
        dk = th * ((1 - 1 / self.k) - 1 / 2) if reflection_cost else 0 * th
        return c0 + dk, c1 - dk, c2, c3 + dk

    def small_max(self, v):
        lx, ly, ell, s0 = v[:4]
        h = 1 - lx + ell
        th = O.XS * self.DS * min(ell / h, self.tau)
        base = (1 / 2 + self.DS / 2 - ly * (1 / 2 + th) - s0 - ell / 2 + O.XS * self.DS * ell
                + h * (5 / 6 - self.w * (1 - self.Rs) + th * (1 - 1 / self.k))).max()
        return base - self.eta_L * h

    def small_rows(self):
        """none: vartheta enters with the coefficient h (1 - 1/k) - l_y, whose sign h/2 < l_y does not fix."""
        return None


class ChargeEll(SS.Five2X):
    """the low side's first-branch rows charge l/2, the pointwise route's excess, in place of c mu/2."""

    def fixed_rows(self):
        out = []
        for n, r, b in super().fixed_rows():
            r = list(r)
            if n.startswith('low:') and 'row loss' not in n:
                r[2] += 1 / 2
                r[4] = 0.0
            out.append((n, r, b))
        return out


def job(a):
    key, cfg, kw, klass = a
    return key, SS.boot((cfg, kw, klass))


def per_kappa(klass, cfg, kw, b0, n=9):
    """the program's value and exact small bins at n points from its bootstrap's fixed point 2 b0 - 1 to 3/4, and
    whether the value is nondecreasing in kappa there (H2, H9)."""
    out = []
    for kap in np.linspace(2 * b0 - 1, 3 / 4, n):
        sol = klass(kap, **cfg, **kw).solve()
        out.append((float(sol['v'][3]), float(sol['small'])))
    return out, all(b[0] >= a[0] - 1e-12 for a, b in zip(out, out[1:]))


def rotation_floor(n=4000, seed=20261022):
    """H4 (iii): fivesixths.low against 5/6 + (1 + l_x - 3l)/24 and 41/48 under h/2 <= l_y, l <= l_x, b >= 0 and
    M + l <= 1, at n random rational points."""
    rng = random.Random(seed)
    lo = Fr(41, 48)
    ok, least, m = True, None, 0
    while m < n:
        lx, ly, ell = (Fr(rng.randint(0, 1000), 1000) for _ in range(3))
        if not (ell <= lx <= ly and 2 * ly >= 1 - lx + ell and lx + ly + ell <= 1):
            continue
        m += 1
        v = F.low(lx, ly, ell)
        ok = ok and v >= Fr(5, 6) + (1 + lx - 3 * ell) / 24 >= lo
        least = v if least is None else min(least, v)
    return ok, least, F.low(Fr(1, 4), Fr(1, 2), Fr(1, 4))


def hard_third():
    """H4 (iv): the low side's least value over (l_x, l_y, l, s0) under h/2 <= l_y, l <= l_x, b >= 0, M + l <= 1 and
    Xu-Sang's l_y - l >= 11b/6: rows s0 >= 5/6 + (l_x - l)/6 + each Gram piece / 2."""
    A, b = [], []
    for g0, g1 in ((0, 0), (-1 / 12, 1 / 12), (-1, 1 / 2)):          # max(0, b/6, 2b - l_y)/2 over (l_x, l_y)
        A.append([1 / 6 + g0, g1, -1 / 6, -1]); b.append(-5 / 6)
    A += [[-1, -2, 1, 0], [-1, 0, 1, 0], [1, -1, 0, 0], [1, 1, 1, 0], [-11 / 6, 5 / 6, 1, 0]]
    b += [-1.0, 0.0, 0.0, 1.0, 0.0]
    r = F.linprog([0, 0, 0, 1], A_ub=A, b_ub=b, bounds=[(0, 1)] * 3 + [(0, 2)], method='highs', options=F.HIGHS)
    return r.fun, r.x


def law_certificates():
    """H8, exact: with u = M - 2l >= 0 and the Gram excess >= 0 (zero at b = 0), the low side less 5/6 is at least
    u/12 + z, z >= max(0, c(3l + u - 1)/2, (1 - (5 - 4 sigma) l - 2u)/8).  At each (sigma, c) a primal vertex attains
    the law and a convex combination (alpha, beta) of the last two rows bounds u/12 + z below by it."""
    ok, n = True, 0
    for sg in (Fr(3, 5), Fr(2, 3), Fr(3, 4), Fr(1)):
        for cc in (Fr(1, 100), Fr(1, 10), Fr(3, 10), Fr(1), Fr(3)):
            D, c0 = 12 * cc + 5 - 4 * sg, (5 - 4 * sg) / (24 * sg - 6)
            law = (2 * sg - 1) * min(1 / (6 * (4 * sg + 1)), cc / D)
            if cc <= c0:
                u, ell, al, be = Fr(0), (1 + 4 * cc) / D, (5 - 4 * sg) / D, 12 * cc / D
            else:
                u, ell = (4 * sg - 2) / (1 + 4 * sg), 1 / (1 + 4 * sg)
                al, be = (5 - 4 * sg) / (6 * cc * (1 + 4 * sg)), 2 / (1 + 4 * sg)
            f = u / 12 + max(Fr(0), cc * (3 * ell + u - 1) / 2, (1 - (5 - 4 * sg) * ell - 2 * u) / 8)
            cu, cl = 1 / Fr(12) + al * cc / 2 - be / 4, 3 * al * cc / 2 - be * (5 - 4 * sg) / 8
            ok = (ok and u >= 0 and ell >= 0 and f == law and al >= 0 and be >= 0 and al + be <= 1 and cu >= 0
                  and cl >= 0 and -al * cc / 2 + be / 8 == law)
            n += 1
    return ok, n


def rotated_cross(n=4000, seed=20261023):
    """H8, rotated: the low side with a crossing, s0 = 5/6 + (l_x - l)/6 + max(0, b/6, 2b - l_y)/2 + max(c mu, L)/2,
    mu = (M + l - 1)_+, against 5/6 + min(c/4, 1/48) under h/2 <= l_y, l <= l_x and b >= 0, at n random rational
    points; and equality, for sigma <= 3/4, at (1/2, 1/2, 1/2) when c <= 1/12 and at (1/4, 1/2, 1/4) when c >= 1/12.
    The points that attain the least values, in exact arithmetic: s0(1/2, 1/2, 1/2) = 5/6 + max(c/4, (4 sigma - 3)/16),
    so the bound holds with equality there at sigma = 3/4 + c for c <= 1/12; and (16/49, 22/49, 11/49), on the slice,
    with h/2 = l_y and l_y - l = 11b/6, has s0 = 5/6 + 4/147 + max(0, (44 sigma - 38)/196)/2."""
    rng = random.Random(seed)
    sgs, cs = (Fr(1, 2), Fr(2, 3), Fr(3, 4), Fr(1)), (Fr(1, 100), Fr(1, 20), Fr(1, 12), Fr(1, 5), Fr(1))

    def s0(lx, ly, ell, sg, cc):
        b, M = ly - lx, lx + ly
        return (Fr(5, 6) + (lx - ell) / 6 + max(Fr(0), b / 6, 2 * b - ly) / 2
                + max(cc * max(Fr(0), M + ell - 1), (1 + (4 * sg - 1) * ell - 2 * M) / 4) / 2)
    floor = lambda cc: Fr(5, 6) + min(cc / 4, Fr(1, 48))
    ok, m, gap = True, 0, None
    while m < n:
        lx, ly, ell = (Fr(rng.randint(0, 1000), 1000) for _ in range(3))
        if not (ell <= lx <= ly and 2 * ly >= 1 - lx + ell):
            continue
        sg, cc = rng.choice(sgs), rng.choice(cs)
        g = s0(lx, ly, ell, sg, cc) - floor(cc)
        ok, m = ok and isinstance(g, Fr) and g >= 0, m + 1
        gap = g if gap is None else min(gap, g)
    q, h = Fr(1, 4), Fr(1, 2)
    at = all(s0(*((h, h, h) if cc <= Fr(1, 12) else (q, h, q)), sg, cc) == floor(cc) for sg in sgs[:3] for cc in cs)
    at = at and all(s0(h, h, h, sg, cc) == Fr(5, 6) + max(cc / 4, (4 * sg - 3) / 16) for sg in sgs for cc in cs)
    at = at and all(s0(h, h, h, Fr(3, 4) + cc, cc) == floor(cc) for cc in cs if cc <= Fr(1, 12))
    p = (Fr(16, 49), Fr(22, 49), Fr(11, 49))
    at = at and 2 * p[1] == 1 - p[0] + p[2] and p[0] + p[1] + p[2] == 1 and 6 * (p[1] - p[2]) == 11 * (p[1] - p[0])
    at = at and all(s0(*p, sg, cc) == Fr(5, 6) + Fr(4, 147) + max(Fr(0), (44 * sg - 38) / 196) / 2
                    for sg in sgs + (Fr(19, 22),) for cc in cs)
    return ok, gap, at


def rotated_lp(sg, cc, hard):
    """H8: the least rotated low side with a crossing, by linear programming over (l_x, l_y, l, s0, mu): rows s0 >= the
    first branch's pieces + c mu/2 and the second branch's + L/2, mu >= M + l - 1, l <= l_x, b >= 0, h/2 <= l_y, and
    Xu-Sang's l_y - l >= 11b/6 when hard."""
    A, b = [], []
    for g0, g1 in ((0, 0), (-1 / 12, 1 / 12), (-1, 1 / 2)):          # max(0, b/6, 2b - l_y)/2 over (l_x, l_y)
        A.append([1 / 6 + g0, g1, -1 / 6, -1, cc / 2]); b.append(-5 / 6)
        A.append([1 / 6 + g0 - 1 / 4, g1 - 1 / 4, -1 / 6 + (4 * sg - 1) / 8, -1, 0]); b.append(-5 / 6 - 1 / 8)
    A += [[1, 1, 1, 0, -1], [-1, 0, 1, 0, 0], [1, -1, 0, 0, 0], [-1, -2, 1, 0, 0]]
    b += [1.0, 0.0, 0.0, -1.0]
    if hard:
        A.append([-11 / 6, 5 / 6, 1, 0, 0]); b.append(0.0)
    r = F.linprog([0, 0, 0, 1, 0], A_ub=A, b_ub=b, bounds=[(0, 1)] * 3 + [(0, 2), (0, 2)], method='highs',
                  options=F.HIGHS)
    return r.fun


def main():
    c1 = SS.cross_cfg(1.0)
    base = dict(sigma=2 / 3, drop=SS.D3)
    dh = dict(c1, counts='dh')
    norot = dict(sigma=2 / 3, drop=SS.D3 + ('h/2<ly',), eta=0.3, eta_L=0.3)
    jobs = [('base', c1, base, SS.Five2X), ('W44', c1, base, W44), ('W44b', c1, base, W44b),
            ('WE1', c1, base, WE1), ('WE2', c1, base, WE2), ('WE45', c1, base, WE45), ('WE10', c1, base, WE10),
            ('WDH', c1, base, WDH), ('dh', dh, base, SS.Five2X),
            ('k2.5', dict(c1, k=2.5), base, SS.Five2X), ('k3', dict(c1, k=3), base, SS.Five2X),
            ('k4', dict(c1, k=4), base, SS.Five2X)]
    jobs += [(f'k{k}z', dict(c1, k=k, lam=0.0), base, ThetaZero) for k in (2.5, 3, 4, 5, 5.25, 6)]
    jobs += [(f'k{k}s', dict(c1, k=k), base, ShareK) for k in (2.5, 3, 4, 5, 5.25, 6)]
    jobs += [('L1', dh, dict(base, eta_L=0.001), SS.Five2X), ('L05', dh, dict(base, eta_L=0.0005), SS.Five2X),
             ('L1s', dh, dict(base, sigma=0.5, eta_L=0.001), SS.Five2X),
             ('U01', dh, dict(base, eta=0.01, eta_L=0.01), SS.Five2X),
             ('U1', dh, dict(base, eta=0.1, eta_L=0.1), SS.Five2X),
             ('U3', dh, dict(base, eta=0.3, eta_L=0.3), SS.Five2X),
             ('U1s1', dh, dict(base, sigma=1.0, eta=0.1, eta_L=0.1), SS.Five2X),
             ('U3n', dict(dh, lam=0.0), norot, ThetaZero),
             ('U3h', dict(dh, soft_third=False), dict(base, eta=0.3, eta_L=0.3), SS.Five2X),
             ('A56', c1, base, A56), ('A34', c1, base, A34), ('A12', c1, base, A12), ('A18', c1, base, A18),
             ('Cap2', c1, base, Cap2), ('ell2', c1, base, ChargeEll),
             ('WHi', c1, base, WinHi), ('WLo', c1, base, WinLo), ('WMid', c1, base, WinMid), ('WW1', c1, base, WinW1),
             ('WW2', c1, base, WinW2), ('WW3', c1, base, WinW3), ('WS', c1, base, WinS),
             ('WW3A', c1, base, WinW3A), ('A015', c1, base, A015), ('A0125', c1, base, A0125),
             ('NoBins', c1, base, NoBins)]
    z0 = 1 / 6 + 1 / 100
    for sg in (0.5, 0.6, 2 / 3, 0.75, 1.0):
        for cc in (0.01, 0.1, 0.3, 1.0):
            jobs.append((('T13', sg, cc), dict(SS.cross_cfg(cc), counts='dh', lam=0.0),
                         dict(sigma=sg, drop=SS.D3 + ('h/2<ly',), eta=0.2, eta_L=0.2, z0=z0), ThetaZero))
    for sg in (0.55, 2 / 3, 0.75):
        for cc in (0.01, 0.06):
            for third in (True, False):
                jobs.append((('T13r', sg, cc, third), dict(SS.cross_cfg(cc), counts='dh', soft_third=third),
                             dict(sigma=sg, drop=SS.D3, eta=0.2, eta_L=0.2), SS.Five2X))
    with ProcessPoolExecutor(4) as ex:
        res = dict(ex.map(job, jobs))
    for key, *_ in jobs:
        r = res[key]
        print(f'    {str(key):6s} B = {r[0]:.7f} kappa {r[1]:.5f} walls {r[2]} (l_x, l_y, l) = '
              f'({r[3][0]:.4f}, {r[3][1]:.4f}, {r[3][2]:.4f})')
    B = {k: r[0] for k, r in res.items()}
    W = {k: r[2] for k, r in res.items()}
    S = {k: r[4] for k, r in res.items()}
    near = lambda k, want, tol=1e-6: abs(B[k] - want) < tol
    klass = {key: kl for key, _, _, kl in jobs}
    kwargs = {key: (cfg, kw) for key, cfg, kw, _ in jobs}
    nx = XL.shape[1]

    def binding(key):
        """the bins within 1e-7 of their endpoint at the optimum of job key, at its bootstrapped kappa."""
        cfg, kw = kwargs[key]
        prog = klass[key](res[key][1], **cfg, **kw)
        sol = prog.solve()
        v = sol['v']
        E = prog.C[0] + prog.C[1] * v[0] + prog.C[2] * v[1] + prog.C[3] * v[2] - v[3]
        act = np.flatnonzero(E > -1e-7)
        return np.unique(DL[act // nx, 0]), np.unique(XL[0, act % nx]), sol

    def outside(key, lo, hi):
        dd, xx, _ = binding(key)
        return (dd.size == 2 and np.all(np.abs(xx - 0.5) < 1e-12) and 0 < lo - dd[0] < 1e-3 and 0 < dd[1] - hi < 1e-3,
                dd)

    # H1: what binds
    B0 = res['base'][0]
    d_act, x_act, sol = binding('base')
    v = sol['v']
    prog = SS.Five2X(res['base'][1], **c1, **base)
    E = prog.C[0] + prog.C[1] * v[0] + prog.C[2] * v[1] + prog.C[3] * v[2] - v[3]
    act = np.flatnonzero(E > -1e-7)
    tight = sorted(n for n, r, b in sol['fixed'] if b - np.dot(r, v) < 1e-7)
    gate('H1', abs(B0 - 0.8748866) < 2e-6 and set(W['base']) == {'E', 'low side', 'slice'} and act.size > 0
         and np.all(np.abs(XL[0, act % nx] - 0.5) < 1e-12) and abs(d_act.min() - 0.4688) < 1e-4
         and abs(d_act.max() - 0.4702) < 1e-4 and tight == ['low:P^(1/6)', 'slice'],
         f'boundary {B0:.7f}, walls {W["base"]}; {act.size} bins within 1e-7 of their endpoint, at x = '
         f'{x_act.min():.4f}..{x_act.max():.4f}, delta in [{d_act.min():.4f}, {d_act.max():.4f}]; tight rows {tight}')
    # H2: relief on the bins
    slope = [(B0 - B['WE1']) / 0.01, (B0 - B['WE2']) / 0.02]
    ok44, d44 = outside('W44', 0.44, 0.50)
    _, nb_mono = per_kappa(NoBins, c1, base, B['NoBins'])
    gate('H2', near('W44', 0.8748474) and near('W44b', 0.8748474) and ok44 and near('WE1', 0.8730362)
         and near('WE2', 0.8711703) and all(0.18 <= s <= 0.19 for s in slope)
         and all(near(k, 0.8693956) and 'small delta' in W[k] and 'floor bin' not in W[k] and 'E' not in W[k]
                 for k in ('WE45', 'WE10', 'WDH'))
         and near('dh', 0.8667866) and 'floor bin' in W['dh'] and 'small delta' not in W['dh']
         and near('NoBins', 0.8693956) and 'small delta' in W['NoBins'] and nb_mono,
         f'window [0.44, 0.50]: {B["W44"]:.7f} at s = 0.01, {B["W44b"]:.7f} at s = 0.05, binding bins at delta '
         f'{", ".join(f"{t:.5f}" for t in d44)}; every bin: {B["WE1"]:.7f} at 0.01, {B["WE2"]:.7f} at 0.02 (slopes '
         f'{slope[0]:.4f}, {slope[1]:.4f}), {B["WE45"]:.7f} at 0.045 and {B["WE10"]:.7f} at 0.1 (walls {W["WE45"]}); '
         f'DH counts on the bins {B["WDH"]:.7f}, counts = dh {B["dh"]:.7f} (walls {W["dh"]}); without the bins '
         f'delta >= 1/8 and the short gate {B["NoBins"]:.7f} (walls {W["NoBins"]}), nondecreasing in kappa at 9 '
         f'points from {2 * B["NoBins"] - 1:.6f} to 3/4: {nb_mono}')
    # H3: stronger moments
    kz = (('k2.5z', 0.8715666), ('k3z', 0.8693505), ('k4z', 0.8674755))
    kh = (('k2.5', 'k2.5z', 0.8712795), ('k3', 'k3z', 0.8692279), ('k4', 'k4z', 0.8674539))
    better = {k: B[f'k{k}s'] - B[f'k{k}z'] for k in (2.5, 3, 4, 5, 5.25, 6)}
    gate('H3', all(near(k, want) and 'E' in W[k] for k, want in kz)
         and all(near(k, want) and 'small delta' in W[k] and 'E' not in W[k]
                 for k, want in (('k5z', 0.8668677), ('k5.25z', 0.8668015)))
         and near('k6z', 0.8667866) and 'floor bin' in W['k6z'] and 'E' not in W['k6z']
         and all(near(a, want) and 0 < B[z] - B[a] < 4e-4 for a, z, want in kh) and min(better.values()) > 1e-5,
         'vartheta = 0: ' + ', '.join(f'k = {k[1:-1]}: {B[k]:.7f} ({"E" if "E" in W[k] else "no E"})' for k, _ in kz)
         + f', k = 5: {B["k5z"]:.7f}, k = 5.25: {B["k5.25z"]:.7f} (walls {W["k5.25z"]}), k = 6: {B["k6z"]:.7f} '
         f'(walls {W["k6z"]}); share vartheta/2: '
         + ', '.join(f'k = {a[1:]}: {B[a]:.7f} (below by {B[z] - B[a]:.1e})' for a, z, _ in kh)
         + '; share vartheta/k: ' + ', '.join(f'k = {k}: {B[f"k{k}s"]:.7f}' for k in better))
    # H4: beyond the first rung
    pt, pt3, pth = res['L1'][3], res['U3'][3], res['U3h'][3]
    rf_ok, rf_least, rf_vertex = rotation_floor()
    ht_val, _ = hard_third()
    ht_low = F.low(Fr(16, 49), Fr(22, 49), Fr(11, 49))
    gate('H4', abs(B['L1'] - 13 / 15) < 2e-7 and max(abs(pt[0] - 0.4), abs(pt[1] - 0.4), abs(pt[2] - 0.2)) < 1e-4
         and 'E' in W['L1'] and 'h/2<ly' in W['L1'] and near('L05', 0.8667067) and 'floor bin' in W['L05']
         and abs(B['L1s'] - 13 / 15) < 2e-7
         and all(near(k, want) and 'floor bin' in W[k] and 'h/2<ly' in W[k] and 'E' not in W[k]
                 for k, want in (('U01', 0.8657615), ('U1', 0.8548781)))
         and abs(B['U3'] - 41 / 48) < 2e-7 and max(abs(pt3[0] - 0.25), abs(pt3[1] - 0.5), abs(pt3[2] - 0.25)) < 1e-4
         and {'h/2<ly', 'low side', 'lx>ell'} <= set(W['U3'])
         and abs(B['U1s1'] - 13 / 15) < 2e-7 and 'row loss' in W['U1s1'] and abs(B['U3n'] - 28 / 33) < 2e-7
         and rf_ok and rf_vertex == Fr(41, 48)
         and abs(B['U3h'] - 253 / 294) < 2e-7 and max(abs(pth[0] - 16 / 49), abs(pth[1] - 22 / 49),
                                                       abs(pth[2] - 11 / 49)) < 1e-4
         and {'h/2<ly', 'slice', 'ly-ell>11b/6'} <= set(W['U3h']) and 'ly-ell>11b/6' not in W['U3']
         and abs(ht_val - 253 / 294) < 1e-9 and ht_low == Fr(253, 294),
         f'(i) floor and small bins only: U^0.001 {B["L1"]:.9f} (13/15 = {13 / 15:.9f}) at ({pt[0]:.4f}, {pt[1]:.4f}, '
         f'{pt[2]:.4f}), walls {W["L1"]}; U^0.0005 {B["L05"]:.7f}; sigma = 1/2: {B["L1s"]:.9f}; (ii) every bin, '
         f'sigma = 2/3: {B["U01"]:.7f} at 0.01, {B["U1"]:.7f} at 0.1 (walls {W["U1"]}), {B["U3"]:.9f} at 0.3 '
         f'(41/48 = {41 / 48:.9f}) at ({pt3[0]:.4f}, {pt3[1]:.4f}, {pt3[2]:.4f}), walls {W["U3"]}; sigma = 1: '
         f'{B["U1s1"]:.9f} (walls {W["U1s1"]}); unrotated: {B["U3n"]:.9f} (28/33 = {28 / 33:.9f}); (iii) low side '
         f'{rf_vertex} at (1/4, 1/2, 1/4), least {float(rf_least):.6f} at 4000 points, both bounds hold: {rf_ok}; '
         f'(iv) third term hard: {B["U3h"]:.9f} (253/294 = {253 / 294:.9f}) at ({pth[0]:.4f}, {pth[1]:.4f}, '
         f'{pth[2]:.4f}), walls {W["U3h"]}; linear program {ht_val:.10f}; fivesixths.low {ht_low} at '
         f'(16/49, 22/49, 11/49)')
    # H5: where the counts come from
    kk = res['A56'][1]
    dev56 = float(np.max(np.abs(rk(DL, XL, kk) - O.Rk(DL, XL, kk))))
    dev18 = float(np.max(np.abs(rk(DL, XL, kk, alpha=1 / 8) - (1 - DL + 0 * XL))))
    c = 1 / (3 * kk)
    Dk = 3 - (1 + 2 * c) * XL
    Pk = (2 - 2 * c * XL) * (1 - XL)
    a, b = ALPHA - DL, DL * Pk / Dk
    par = float(np.max(np.abs((O.Rk(DL, XL, kk) - (1 - DL)) - a * b / (2 * (a + b)))))
    def plain_selection(cap, kap):
        """the plain selection z_P = (1 - 2m)/(cap kappa) at Xu-Sang's balance t*, r*(t*), m = t* - r*."""
        cc = 2 / (cap * kap)
        Dc, Pc = 3 - (1 + 2 * cc) * XL, (2 - 2 * cc * XL) * (1 - XL)
        ac, bc = np.maximum(ALPHA - DL, 0.0), DL * Pc / Dc
        tc = 1 + bc / (2 * (ac + bc))
        rc = ((2 - 2 * cc * XL) * tc + (cc - 1) * XL) / Dc
        return cc, (1 - 2 * (tc - rc)) / (cap * kap)

    c2, zP = plain_selection(2.0, res['Cap2'][1])
    _, zP6 = plain_selection(6.0, res['A56'][1])
    lx2, _, ell2 = res['Cap2'][3][:3]
    supply = ell2 / (1 - lx2 + ell2)
    over = float(np.mean(zP > supply))
    gate('H5', dev56 < 1e-15 and near('A56', 0.8748866, 2e-6) and near('A34', 0.8741816) and near('A12', 0.8714461)
         and 'E' in W['A12'] and near('A18', 0.8677780) and 'small delta' in W['A18'] and 'floor bin' not in W['A18']
         and near('A015', 0.8667974) and 'small delta' in W['A015'] and near('A0125', 0.8667866)
         and 'floor bin' in W['A0125'] and 'small delta' not in W['A0125'] and dev18 < 1e-6
         and near('Cap2', 0.8733798) and c2 > 6 / 13 and 0.10 < over < 0.16 and zP6.max() < 1 / 5 and par < 1e-12,
         f'slope 5/6 reproduces the count (deviation {dev56:.1e}) and {B["A56"]:.7f}; 3/4: {B["A34"]:.7f}; 1/2: '
         f'{B["A12"]:.7f} (walls {W["A12"]}); 1/8: {B["A18"]:.7f} (walls {W["A18"]}); 3/200: {B["A015"]:.7f}; 1/80: '
         f'{B["A0125"]:.7f} (walls {W["A0125"]}); count minus (1 - delta) '
         f'{dev18:.1e}; plain capacity constant 2: {B["Cap2"]:.7f}, with c = {c2:.4f} (6/13 = {6 / 13:.4f}) and z_P '
         f'up to {zP.max():.4f} above the supply {supply:.4f} on {100 * over:.1f}% of the bins (constant 6: z_P up to '
         f'{zP6.max():.4f}); R - (1 - delta) = ab/(2(a + b)) within {par:.1e}')
    # H6: T3's pointwise route
    out6 = []
    for Mp, lp in ((2 * Fr(5572, 10000), Fr(5572, 10000)), (Fr(8, 5), Fr(1, 10))):
        T = 2 * Mp + lp - 1
        w = (Fr(0), Mp, Fr(0), Fr(0), Fr(0), Fr(0), lp, T, Fr(0), Fr(0))
        En, Tn, y = X.energy(w, lp)
        o, h, a0, n0, s0, b0, za, vv, lb, e = w
        u = min(vv, za, (vv + za) / 3)
        Epw = En - max(h, vv + lb) + u + h
        out6.append((Mp, lp, T, En, Tn, y, Epw, (Epw - Mp) / (En - Mp)))
    (Mp, lp, T, En, Tn, y, Epw, ratio), (_, _, _, En2, _, _, Epw2, ratio2) = out6
    t = lp
    gate('H6', Tn == T and y == T and En == Mp + (Mp + lp - 1) and Epw == Mp + lp and ratio == t / (3 * t - 1)
         and abs(float(ratio) - 0.8297) < 1e-4 and ratio2 == Fr(1, 7) and near('ell2', 0.9487180) and B['ell2'] > B0,
         f'at (M\', l\') = (2t, t), t = {t}: release {En} = M\' + {En - Mp} (3t - 1), pointwise {Epw} = M\' + '
         f'{Epw - Mp} (t), ratio t/(3t - 1) = {float(ratio):.4f}; at (8/5, 1/10) the ratio is {ratio2}; the low side '
         f'charging l/2: {B["ell2"]:.7f} (walls {W["ell2"]})')
    # H7: density-hypothesis counts on windows of delta only
    edge = [(k, kl.WIN, outside(k, *kl.WIN)) for k, kl in (('WMid', WinMid), ('WW1', WinW1), ('WW2', WinW2))]
    gate('H7', near('WHi', B0, 2e-6) and near('WLo', B0, 2e-6) and near('WMid', 0.8746407) and near('WW1', 0.8735094)
         and near('WW2', 0.8712876) and near('WW3', 0.8714881) and near('WW3A', 0.8714946)
         and 'small delta' in W['WW3'] and all(e[2][0] for e in edge)
         and abs(B['WS'] - B['WMid']) < 1e-6 and all(B[k] > 0.8667866 + 1e-3 for k in ('WMid', 'WW1', 'WW2', 'WW3')),
         f'DH counts on delta in [4/7, 5/6]: {B["WHi"]:.7f}, [1/8, 0.45]: {B["WLo"]:.7f}; [0.40, 0.55]: '
         f'{B["WMid"]:.7f}, [0.30, 0.65]: {B["WW1"]:.7f}, [0.20, 0.75]: {B["WW2"]:.7f}, [1/8, 0.70]: between '
         f'{B["WW3"]:.7f} and {B["WW3A"]:.7f} (walls {W["WW3"]}); '
         f'binding bins ' + '; '.join(f'{wn}: delta {", ".join(f"{t:.5f}" for t in e[1])}' for _, wn, e in edge)
         + f'; U^0.05 on [0.40, 0.55]: {B["WS"]:.7f}')
    # H8: the T1-T3 trade-off with T2 strong
    law = lambda sg, cc: 5 / 6 + max(0.0, 2 * sg - 1) * min(1 / (6 * (4 * sg + 1)), cc / (12 * cc + 5 - 4 * sg))
    t13 = [k for k in res if isinstance(k, tuple) and k[0] == 'T13']
    t13r = [k for k in res if isinstance(k, tuple) and k[0] == 'T13r']
    dev8 = max(abs(B[k] - law(k[1], k[2])) for k in t13)
    dev8r = max(abs(B[k] - (5 / 6 + k[2] / 4)) for k in t13r)
    diag = all(max(abs(v - 0.5) for v in res[k][3][:3]) < 1e-4 for k in t13r)
    hard = all(('ly-ell>11b/6' in W[k]) == (not k[3]) for k in t13r)
    slack = not any({'E', 'floor bin', 'small delta'} & set(W[k]) for k in t13 + t13r)
    cert, ncert = law_certificates()
    rc_ok, rc_gap, rc_at = rotated_cross()
    rl_ok, rl_gap, rl_n = True, [], 0
    for sg in (1 / 2, 2 / 3, 3 / 4, 0.8, 0.9, 1.0):
        for cc in (0.01, 1 / 12, 0.1, 0.2, 1.0):
            lp_soft, lp_hard = rotated_lp(sg, cc, False), rotated_lp(sg, cc, True)
            bound, bound_h = 5 / 6 + min(cc / 4, 1 / 48), 5 / 6 + min(cc / 4, 4 / 147)
            eq_s = sg <= 3 / 4 + (cc if cc <= 1 / 12 + 1e-12 else 0) + 1e-12
            eq_h = sg <= (3 / 4 + cc if cc < 16 / 147 else 19 / 22) + 1e-12
            for val, bd, eq in ((lp_soft, bound, eq_s), (lp_hard, bound_h, eq_h)):
                rl_ok = rl_ok and (abs(val - bd) < 1e-9 if eq else val - bd > 1e-6) and lp_hard >= lp_soft - 1e-9
            if sg == 1.0:
                rl_gap.append(lp_soft - bound)
            rl_n += 1
    rl_ok = rl_ok and min(rl_gap) > 6e-3 and rl_n == 30
    exact = True
    for sg in (Fr(3, 5), Fr(2, 3), Fr(3, 4), Fr(1)):
        for cc in (Fr(1, 100), Fr(1, 10), Fr(3, 10)):
            tt = (1 + 4 * cc) / (12 * cc + 5 - 4 * sg)
            cross, loss = cc * (3 * tt - 1) / 2, (1 - (5 - 4 * sg) * tt) / 8
            exact = exact and cross == loss == cc * (2 * sg - 1) / (12 * cc + 5 - 4 * sg) and 3 * tt > 1
    gate('H8', len(t13) == 20 and len(t13r) == 12 and dev8 < 1e-6 and dev8r < 1e-6 and diag and hard and slack
         and exact and cert and ncert == 20 and rc_ok and rc_at and rl_ok,
         f'unrotated, DH counts, U^0.2 on every bin: the program matches 5/6 + (2 sigma - 1)_+ min(1/(6(4 sigma + 1)), '
         f'c/(12c + 5 - 4 sigma)) within {dev8:.1e} at {len(t13)} points (sigma in 1/2..1, c in 0.01..1); with the '
         f'rotation, 5/6 + c/4 within {dev8r:.1e} at {len(t13r)} runs (third term soft and hard), at (1/2, 1/2, 1/2): '
         f'{diag}, hard third among the walls exactly when kept: {hard}; no bin among the walls: {slack}; on the '
         f'diagonal the two branches meet exactly: {exact}; primal vertex and dual certificate at {ncert} rational '
         f'(sigma, c): {cert}; rotated, 5/6 + min(c/4, 1/48) at 4000 points: {rc_ok} (least gap {float(rc_gap):.2e}), '
         f'attained at (1/2, 1/2, 1/2) or (1/4, 1/2, 1/4), and the values at (1/2, 1/2, 1/2) and '
         f'(16/49, 22/49, 11/49): {rc_at}; least rotated low side by linear programming at '
         f'{rl_n} (sigma, c): equal to the bound exactly where sigma <= 3/4 + c (c <= 1/12) or sigma <= 3/4 (c > 1/12) '
         f'with the third term soft, and to 5/6 + min(c/4, 4/147) where sigma <= 3/4 + c (c < 16/147) or '
         f'sigma <= 19/22 (c >= 16/147) with it hard, above elsewhere (by at least {min(rl_gap):.4f} at sigma = 1): '
         f'{rl_ok}')
    # H9: the small bins at every reported optimum
    viol = sorted(str(k) for k in S if S[k] > 1e-9 and k != 'WW3')
    ww3k, mono = per_kappa(WinW3, c1, base, B['WW3'])
    start = ww3k[-1][1] <= 1e-9 and abs(ww3k[-1][0] - B['WW3A']) < 1e-9
    gate('H9', not viol and 0 < S['WW3'] < 1e-5 and S['WW3A'] <= 1e-9 and 0 < B['WW3A'] - B['WW3'] < 1e-5
         and all(S[f'k{k}s'] < 0 for k in (2.5, 3, 4, 5, 5.25, 6)) and mono and start,
         f'{len(S)} optima; largest small-bin endpoint {max(v for k, v in S.items() if k != "WW3"):.1e} outside WW3; '
         f'WW3 (relaxation) {S["WW3"]:.1e}, WW3A {S["WW3A"]:.1e}; ShareK (not enforced): largest '
         f'{max(S[f"k{k}s"] for k in (2.5, 3, 4, 5, 5.25, 6)):.1e}; violations: {viol}; WW3\'s relaxation at kappa '
         f'= 3/4 exact ({ww3k[-1][1]:.1e}) and equal to WW3A: {start}; nondecreasing in kappa at 9 points from '
         f'{2 * B["WW3"] - 1:.6f} to 3/4: {mono}')
    if FAILS:
        print('FAILED:', ', '.join(FAILS))
        sys.exit(1)
    print('all gates pass')


if __name__ == '__main__':
    main()
