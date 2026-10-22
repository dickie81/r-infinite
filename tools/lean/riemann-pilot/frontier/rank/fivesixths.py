"""The release's exponent system at 5/6 (FIVE-SIXTHS.md).

The question is what a zero-free half-plane Re s > 5/6 would need from the release's method (README rounds 496-508
model it in frontier/wall78).  Every number here is a statement about that exponent system, not a theorem about
L-functions.

Notation (README round 496): the probe's lengths (l_x, l_y, ell), M = l_x + l_y, b = l_y - l_x, h = 1 - l_x + ell,
crossing mu = (M + ell - 1)_+.  The release's low side, as the boundary it gives (README round 503):
    s0 = 5/6 + l_x/6 - ell/6 + max(0, theta b, 2b - l_y)/2 + L/2 + c mu/2,
theta = 1/6 (the Gram bound's exceptional term, a main term for the release's A_m: rounds 504-505), L the completed
rows' norm loss.  The Gram bound needs P_a = Y'^2/Q >= 1, that is b >= 0; the compensated probe rescales X by every
slot product, so its geometry needs l_x > ell (Xu-Sang's eq. low-geometry, "We will require l_x > ell").

The second branch's slot sum (FIVE-SIXTHS.md, section 2).  At the dyad where round 500's second branch is attained the
dual is trivial (v = l_b = e = 0) and every slot is active, so the completed row of each row k is a fixed multiple of
the slot sum sum_P a(P)/sqrt(q_P); Lemma lem:hybrid-energy bounds it by Cauchy-Schwarz, Z^{z_a}.  sigma is the exponent
of that slot sum's square per unit of active slot length: sigma = 1 is the release's bound, sigma = 2/3 the size of
the cubic large sieve's (NL)^{2/3} term at N = 1, which is also the size of Patterson's main term.  The second
branch then charges (1 + (4 sigma - 1) ell' - 2 M')/4 in place of (1 + 3 ell' - 2 M')/4.  [Corrected in
FIVE-SIXTHS.md section 7: sigma is the parameter of that second branch, not the trivial dual's exponent, since a
bound at the trivial dual alone does not move the dyads' maximum.  slotsplit.py's gate S5 gives the hybrid bounds
that realize sigma = 5/8 (every column's slot sum at square-root size), 2/3 (the L term dropped) and 1/2 (a
square-root sieve N + (NL)^{1/2}); its gates S1-S2 give sigma = 3/4 from the release's own pair phase.]

Gates (exit status 1 if any fails):
  F1  the floor (exact arithmetic): at 4000 random rational geometries with b >= 0, l_x >= ell, L >= 0 and mu >= 0,
      s0 - 5/6 = (M - 2 ell)/12 + (max(0, b/6, 2b - l_y) - b/6)/2 + L/2 + mu/2 >= (l_x - ell)/6 >= 0, with equality
      iff l_x = l_y = ell and L = mu = 0; and the vertex (1/3, 1/3, 1/3) gives exactly 5/6.  The identity agrees
      with lowbudget.steps (round 503) wherever both are defined.
  F2  the low side's least value over the geometry, for the second-branch slot exponent sigma (linear programs over
      (l_x, l_y, ell, mu), first-branch crossing cost c = 1, b >= 0, l_x >= ell, M' >= (1 - ell)/2 for a retained dyad):
      5/6 + max(0, (2 sigma - 1)/(6 (4 sigma + 1))) at sigma in {0, 1/4, 1/2, 2/3, 3/4, 1} (1e-9): 13/15 at sigma = 1,
      28/33 at sigma = 2/3, 5/6 for sigma <= 1/2.  Dropping l_x >= ell, sigma = 0 goes below 5/6.
  F3  the dyads of round 500's row-norm exponent (crossing.emax's program, 300 random (M', ell') with ell' <= 0.36 and
      M' >= (1 - ell')/2): with the cubic sieve's L term (u = v) dropped the maximum is
      M' + max(0, M' + ell' - 1, (1 + 5 ell'/3 - 2 M')/4) (1e-9); with it, crossing.formula.  At (M', ell') =
      (2/3, 1/3) the release's maximum M' + 1/6 is attained at a dyad with v = l_b = e = 0 and z_a = ell', where
      E = O/2 + H + z_a exactly; with the powerful part O forced to 0 it is M' + 1/9, at a dyad with v = 0 again
  F4  the exponent system (offslice.OffSlice with round 500's first-branch crossing, Xu-Sang's admissibility and
      round 498's readings), with sigma, a uniform row-sum saving U^eta = Z^{eta h} in every bin (the floor bin and
      the small bins included), no numerator rotation (vartheta = 0 in the bins delta >= 1/8, and with it Xu-Sang's
      h < 2 l_y, imposed for the rotation only; the small bins keep Sang's vartheta, since offslice's small_max does
      not read lam), the third Gram term carried in the low side's max, and the small rows' z-line z0.  The small
      bins delta < 1/8, which the program does not enforce, are slack (exact small_max < 0) at every optimum of F4
      and F5:
        (i)   sigma = 1, eta = 0 with the rotation reproduces round 498's 'everything' (0.8613056) and 'Lindelof + all
              readings' (0.8667866) to 2e-6
        (ii)  sigma = 2/3, eta = 0.13, DH counts and Lindelof: 28/33 (1e-6)
        (iii) sigma = 1/2, eta = 0.18, z0 = 1/6 + 1/100, with Sang's counts and fourth moment and with DH counts and
              Lindelof: 5/6 (2e-7), at (l_x, l_y, ell) within 1e-3 of (1/3, 1/3, 1/3)
        (iv)  the same with z0 = 17/50 (Sang's): 0.835 (1e-6), the small rows binding
        (v)   the same with eta = 0.16 < 1/6: above 5/6 by more than 1e-3
        (vi)  sigma = 1 with eta = 0.3: 13/15 (1e-6)
  F5  the row saving the vertex needs: at (1/3, 1/3, 1/3), h = 1 and the C0 wall 4/3 - 5 l_x/6 - l_y/2 + ell/3 = 1
      (exact), so eta >= 1/6; in the program (sigma = 1/2, z0 = 1/6 + 1/100) DH counts with Lindelof reach 5/6 at
      eta = 0.168 and not at 0.166, Sang's counts and fourth moment at 0.178 and not at 0.175
  F6  two readings at the vertex, in exact arithmetic.  (i) The small rows' line: the release's proof of Lemma
      lem:compensated-absolute-local-bounds on x_r = beta_* + e, w_r = 1/2 needs the selected-prime exponents
      -x_r, -6 z_r, 4 - 5x_r - 6 z_r, 1 - w_r - 6 z_r (off u) and -1/2, 3/2 - 2x_r, 2 - 3x_r, 3 - 5x_r, R and V
      (on u) to be nonpositive, and the first Euler region's good-prime terms 4 - 6x_r - 6z_r, 1 - x_r - w_r - 6z_r
      below -1; at x_r = 5/6 and z_r = 1/6 + 1/100 every one holds, and z_r stays right of zeta_F(6z)'s pole at
      1/6 (with z_r = 1/6 - 1/100 that fails).  (ii) The tuple sum: with the second branch at sigma = 1/2, the
      rescaled tuple's exponent -d + L_sigma(d)/2 is <= 0 for d in [0, ell] at the vertex, so the low side is
      taken at d = 0 there, as round 500 found for the release's loss
  N1  Patterson's bias (FIVE-SIXTHS.md, section 2): over the 7796 split primary primes of norm <= 8*10^4 (the pilot's
      periods data; the 31 inert primes of norm q^2 <= 8*10^4, where gamma_2 = 1 and alpha = -1, are excluded since
      the fourth review round), |sum gamma_2(pi) alpha(pi)^k| is at least 8 sqrt(n) for k = 0 and at most
      2.5 sqrt(n) for k = -3, ..., 3, k != 0; and gamma_2^3 = mu alpha at every prime (1e-9).  The untwisted sum over
      norms <= X grows from X = 2*10^4 to 8*10^4 with log-slope between 0.7 and 5/6 (that of X^{5/6}/log X there is
      0.74, that of sqrt(n) 0.45).  The release's trivial-dual slot coefficient is gamma_2(q) alpha(q)^{-2} times
      finite-order factors, the case k = -2.

Usage: python3 fivesixths.py [periods_w_FILE]   (N1 needs the prime data; it is skipped, and reported, without it)
"""
import math
import os
import sys
from fractions import Fraction as Fr
from concurrent.futures import ProcessPoolExecutor

import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
WALL = os.path.join(HERE, '..', 'wall78')
sys.path.insert(0, HERE)
sys.path.insert(0, WALL)
import crossing as X        # noqa: E402
import offslice as O        # noqa: E402
import levers as LV         # noqa: E402
import lowbudget as LB      # noqa: E402

HIGHS = {'primal_feasibility_tolerance': 1e-10, 'dual_feasibility_tolerance': 1e-10}
FAILS = []


def gate(name, ok, msg):
    print(f'{name}: {"PASS" if ok else "FAIL"}  {msg}', flush=True)
    if not ok:
        FAILS.append(name)


# ---------------------------------------------------------------- F1, F2: the low side
def low(lx, ly, ell, L=0, mu=0, theta=Fr(1, 6), c=1):
    b = ly - lx
    zero = 0 * lx
    return Fr(5, 6) + lx / 6 - ell / 6 + max(zero, theta * b, 2 * b - ly) / 2 + Fr(L) / 2 + c * Fr(mu) / 2


def floor_terms(lx, ly, ell, L=0, mu=0):
    b, M = ly - lx, lx + ly
    return (M - 2 * ell) / 12 + (max(0 * b, b / 6, 2 * b - ly) - b / 6) / 2 + Fr(L) / 2 + Fr(mu) / 2


def low_min(sigma, lx_ge_ell=True):
    """least low side over (l_x, l_y, ell, mu, s0): rows s0 >= each of the low side's pieces (the three Gram pieces,
    each with no row loss and with the second branch at exponent sigma; the crossing cost on the first branch only),
    b >= 0, M + ell <= 1 + mu, M' >= (1 - ell)/2."""
    A, b = [], []
    for g0, g1 in ((0, 0), (-1 / 12, 1 / 12), (-1, 1 / 2)):           # max(0, b/6, 2b - l_y)/2 over (l_x, l_y)
        A.append([1 / 6 + g0, g1, -1 / 6, 1 / 2, -1]); b.append(-5 / 6)   # + mu/2 (first branch)
        A.append([1 / 6 + g0 - 1 / 4, g1 - 1 / 4, -1 / 6 + (4 * sigma - 1) / 8, 0, -1]); b.append(-5 / 6 - 1 / 8)
    A += [[1, -1, 0, 0, 0], [1, 1, 1, -1, 0], [-1, -1, -1 / 2, 0, 0]]
    b += [0.0, 1.0, -1 / 2]
    if lx_ge_ell:
        A.append([-1, 0, 1, 0, 0]); b.append(0.0)
    r = linprog([0, 0, 0, 0, 1], A_ub=A, b_ub=b, bounds=[(0, 1)] * 3 + [(0, 1), (0, 2)], method='highs',
                options=HIGHS)
    return r.fun, r.x


def low_min_formula(sigma):
    return 5 / 6 + max(0.0, (2 * sigma - 1) / (6 * (4 * sigma + 1)))


# ---------------------------------------------------------------- F3: the dyads
TY, BASE, UNIT, P1 = X.TY, X.BASE, X.UNIT, X.P1
FULL = (-UNIT[7], -UNIT[6], -(UNIT[7] + UNIT[6]) / 3)    # -u pieces: L term (u = v), N term, (NL)^{2/3} term
NOL = FULL[1:]


def emax(Mp, lp, pieces=FULL, omax=None):
    A = [[1, 1, 0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 1, 1, 1, 0, 0, 0, 0], list(-TY)]
    b = [Mp, 0.0, 0.0, -(1 + lp)]
    if omax is not None:
        A.append(list(UNIT[0])); b.append(omax)
    best, arg = -np.inf, None
    for p1 in P1:
        for p in pieces:
            c = BASE + p1 + p - TY / 2
            r = linprog(-c, A_ub=A, b_ub=b, bounds=[(0, None)] * 6 + [(0, lp)] + [(0, None)] * 3, method='highs',
                        options=HIGHS)
            if r.status == 0 and -r.fun + (1 + lp) / 2 > best:
                best, arg = -r.fun + (1 + lp) / 2, r.x
    return best, arg


def gauss_formula(Mp, lp):
    return Mp + max(0, Mp + lp - 1, (1 + 5 * lp / 3 - 2 * Mp) / 4)


# ---------------------------------------------------------------- F4, F5: the exponent system
class Five(O.OffSlice):
    """offslice's program with the second branch at slot exponent sigma (row loss (1 + (4 sigma - 1) ell - 2M)/4), the
    crossing cost on the first branch only (round 500), a uniform row-sum saving U^eta = Z^{eta h} in every bin
    (the bins delta >= 1/8, the small bins and the floor bin), the small rows' z-line z0, and dropped rows."""

    def __init__(self, kappa, sigma=1.0, eta=0.0, z0=None, drop=(), **kw):
        self.sigma, self.eta, self.z0, self.drop = sigma, eta, z0, set(drop)
        super().__init__(kappa, **kw)
        self.C = self.C.copy()
        self.C[0] -= eta
        self.C[1] += eta
        self.C[3] -= eta

    def small_max(self, v):
        return super().small_max(v) - self.eta * (1 - v[0] + v[2])

    def floor_rows(self):
        return [(n, [r[0] + self.eta, r[1], r[2] - self.eta, r[3], r[4]], b + self.eta)
                for n, r, b in super().floor_rows()]

    def fixed_rows(self):
        out = []
        for n, r, b in super().fixed_rows():
            r = list(r)
            if n.startswith('low:') and 'row loss' in n:
                r[2] += (4 * self.sigma - 1) / 8 - 3 / 8
                r[4] = 0.0
            if n in self.drop:
                continue
            if n == 'low rows' and self.z0 is not None:
                c = self.z0 - 1 / 6
                r = [-c, -1 / 2, c, 0, 0]
                b = (-c if self.margin else -1 / 20 - 2 * O.DMIN - c) - 1e-9
            out.append((n, r, b))
        return out


KAPPAS = (13 / 18, 0.7226111, 3 / 4)
L9 = LV.LINDELOF
NOROT = ('h/2<ly', 'ell<=1/5', 'ell>=1/6')
CFG = {
    'everything': (dict(k=L9, gram='none', lam=100.0, counts='dh', **LV.READ), {}),
    'Lindelof + all readings': (dict(k=L9, **LV.READ), {}),
    'Sang, no rotation': (dict(k=2, lam=0.0, soft_third=True, **LV.READ), {}),
    'DH + Lindelof, no rotation': (dict(k=L9, lam=0.0, counts='dh', soft_third=True, **LV.READ), {}),
}


def solve(args):
    name, kw = args
    cfg = CFG[name][0]
    best = None
    for kap in KAPPAS:
        prog = Five(kap, **cfg, **kw)
        sol = prog.solve()
        if sol is not None and (best is None or sol['v'][3] < best[0] - 1e-12):
            best = (sol['v'][3], kap, tuple(sol['v'][:3]), prog.walls(sol), float(sol['small']))
    return args, best


# ---------------------------------------------------------------- N1: Patterson's bias
def bias(path):
    from composite import Field, load_primes, SplitPrime
    F = Field('w')
    pr = [P for P in load_primes(F, path, 80000) if isinstance(P, SplitPrime)]
    z = np.array([complex(P.el[0] - 0.5 * P.el[1], math.sqrt(3) / 2 * P.el[1]) for P in pr])
    al = z / np.abs(z)
    g2 = np.array([P.G[2] for P in pr])
    cube = np.max(np.abs(g2 ** 3 + al))             # gamma_2^3 = mu alpha = -alpha at primes
    sums = {k: abs(np.sum(g2 * al ** k)) for k in range(-3, 4)}
    nm = np.array([P.norm for P in pr])
    slope = math.log(sums[0] / abs(np.sum(g2[nm <= 20000]))) / math.log(4)    # untwisted, 2*10^4 to 8*10^4
    return len(pr), cube, sums, slope


def main():
    rng = np.random.default_rng(20261022)
    # F1
    bad, eq_bad, lb_bad, n_lb = 0, 0, 0, 0
    for _ in range(4000):
        ell = Fr(int(rng.integers(0, 400)), 1000)
        lx = ell + Fr(int(rng.integers(0, 400)), 1000)
        ly = lx + Fr(int(rng.integers(0, 400)), 1000)
        L, mu = Fr(int(rng.integers(0, 50)), 1000), Fr(int(rng.integers(0, 50)), 1000)
        s = low(lx, ly, ell, L, mu)
        if s - Fr(5, 6) != floor_terms(lx, ly, ell, L, mu) or s - Fr(5, 6) < (lx - ell) / 6:
            bad += 1
        if (s == Fr(5, 6)) != (lx == ly == ell and L == 0 and mu == 0):
            eq_bad += 1
        M = lx + ly
        if M + ell <= 1 and M >= (1 - ell) / 2:
            n_lb += 1
            Lr = max(Fr(0), (1 + 3 * ell - 2 * M) / 4)
            if LB.steps(lx, ly, ell, Fr(1, 6)) != low(lx, ly, ell, Lr):
                lb_bad += 1
    v = Fr(1, 3)
    gate('F1', bad == 0 and eq_bad == 0 and lb_bad == 0 and n_lb > 300 and low(v, v, v) == Fr(5, 6),
         f'4000 geometries: identity and floor failures {bad}, equality-case failures {eq_bad}; lowbudget.steps '
         f'disagrees at {lb_bad} of {n_lb}; low(1/3, 1/3, 1/3) = {low(v, v, v)}')
    # F2
    rows, worst = [], 0.0
    for sg in (0.0, 0.25, 0.5, 2 / 3, 0.75, 1.0):
        val, _ = low_min(sg)
        worst = max(worst, abs(val - low_min_formula(sg)))
        rows.append(f'{sg:.3f}: {val:.9f}')
    v1, v23, v12 = low_min(1.0)[0], low_min(2 / 3)[0], low_min(0.5)[0]
    below, _ = low_min(0.0, lx_ge_ell=False)
    gate('F2', worst < 1e-9 and abs(v1 - 13 / 15) < 1e-9 and abs(v23 - 28 / 33) < 1e-9 and abs(v12 - 5 / 6) < 1e-9
         and below < 5 / 6 - 1e-3,
         f'least low side by sigma {"; ".join(rows)}; max deviation from the closed form {worst:.1e}; '
         f'without l_x >= ell at sigma = 0: {below:.6f}')
    # F3
    pts = [(rng.uniform(0, 1.3), rng.uniform(0, 0.36)) for _ in range(700)]
    pts = [(m, l) for m, l in pts if m >= (1 - l) / 2 + 1e-3][:300]
    dev_full = max(abs(emax(m, l)[0] - X.formula(m, l)) for m, l in pts)
    dev_gs = max(abs(emax(m, l, NOL)[0] - gauss_formula(m, l)) for m, l in pts)
    e, w = emax(2 / 3, 1 / 3)
    O_, H_, za = w[0], w[1], w[6]
    triv = max(abs(w[7]), abs(w[8]), abs(w[9])) < 1e-9 and abs(za - 1 / 3) < 1e-9
    exact = abs(e - (O_ / 2 + H_ + za)) < 1e-9
    e0, w0 = emax(2 / 3, 1 / 3, omax=0.0)
    gate('F3', dev_full < 1e-9 and dev_gs < 1e-9 and abs(e - 2 / 3 - 1 / 6) < 1e-9 and triv and exact
         and abs(e0 - 2 / 3 - 1 / 9) < 1e-9 and abs(w0[7]) < 1e-9,
         f'{len(pts)} dyad programs: release vs crossing.formula {dev_full:.1e}, L term dropped vs '
         f'M\' + max(0, M\'+l\'-1, (1+5l\'/3-2M\')/4) {dev_gs:.1e}; at (2/3, 1/3) E_max - M\' = {e - 2/3:.6f} at '
         f'O = {O_:.4f}, H = {H_:.4f}, z_a = {za:.4f}, v = l_b = e = 0: {triv}, E = O/2 + H + z_a: {exact}; with '
         f'O = 0, {e0 - 2/3:.6f} at v = {w0[7]:.1e}, l_b = {w0[8]:.4f}')
    # F4, F5
    z0s = 1 / 6 + 1 / 100
    jobs = [('everything', dict()), ('Lindelof + all readings', dict()),
            ('DH + Lindelof, no rotation', dict(sigma=2 / 3, eta=0.13, drop=NOROT)),
            ('Sang, no rotation', dict(sigma=0.5, eta=0.18, z0=z0s, drop=NOROT)),
            ('DH + Lindelof, no rotation', dict(sigma=0.5, eta=0.18, z0=z0s, drop=NOROT)),
            ('Sang, no rotation', dict(sigma=0.5, eta=0.18, z0=17 / 50, drop=NOROT)),
            ('DH + Lindelof, no rotation', dict(sigma=0.5, eta=0.16, z0=z0s, drop=NOROT)),
            ('DH + Lindelof, no rotation', dict(sigma=1.0, eta=0.3, z0=z0s, drop=NOROT)),
            ('DH + Lindelof, no rotation', dict(sigma=0.5, eta=0.168, z0=z0s, drop=NOROT)),
            ('DH + Lindelof, no rotation', dict(sigma=0.5, eta=0.166, z0=z0s, drop=NOROT)),
            ('Sang, no rotation', dict(sigma=0.5, eta=0.178, z0=z0s, drop=NOROT)),
            ('Sang, no rotation', dict(sigma=0.5, eta=0.175, z0=z0s, drop=NOROT))]
    with ProcessPoolExecutor(4) as ex:
        res = list(ex.map(solve, jobs))
    B = [r[1][0] for r in res]
    geo = [r[1][2] for r in res]
    for (nm, kw), r in res:
        print(f'    {nm:28s} {str({k: (round(v, 4) if isinstance(v, float) else v) for k, v in kw.items() if k != "drop"}):46s}'
              f' B = {r[0]:.7f} kappa {r[1]:.4f} (l_x, l_y, ell) = ({r[2][0]:.4f}, {r[2][1]:.4f}, {r[2][2]:.4f})'
              f' walls {r[3]}')
    near = lambda g: max(abs(t - 1 / 3) for t in g) < 1e-3
    small4 = max(r[1][4] for r in res)
    ok4 = (small4 < 0 and abs(B[0] - 0.8613056) < 2e-6 and abs(B[1] - 0.8667866) < 2e-6 and abs(B[2] - 28 / 33) < 1e-6
           and abs(B[3] - 5 / 6) < 2e-7 and abs(B[4] - 5 / 6) < 2e-7 and near(geo[3]) and near(geo[4])
           and abs(B[5] - 0.835) < 1e-6 and B[6] > 5 / 6 + 1e-3 and abs(B[7] - 13 / 15) < 1e-6)
    gate('F4', ok4, f'(i) {B[0]:.7f}, {B[1]:.7f}; (ii) {B[2]:.7f} (28/33 = {28/33:.7f}); (iii) {B[3]:.9f}, '
         f'{B[4]:.9f}; (iv) {B[5]:.7f}; (v) {B[6]:.7f}; (vi) {B[7]:.7f}; small bins at every optimum of F4 and F5: '
         f'largest endpoint {small4:.1e}')
    v3 = Fr(1, 3)
    c0 = Fr(4, 3) - 5 * v3 / 6 - v3 / 2 + v3 / 3
    ok5 = (c0 == 1 and 1 - v3 + v3 == 1 and abs(B[8] - 5 / 6) < 2e-7 and B[9] > 5 / 6 + 1e-6
           and abs(B[10] - 5 / 6) < 2e-7 and B[11] > 5 / 6 + 1e-6)
    gate('F5', ok5, f'C0 wall at the vertex {c0}, h = 1; DH + Lindelof at eta 0.168 {B[8]:.9f}, 0.166 {B[9]:.7f}; '
         f'Sang at eta 0.178 {B[10]:.9f}, 0.175 {B[11]:.7f}')
    # F6
    def line_ok(x, w, z):
        off = [-x, -6 * z, 4 - 5 * x - 6 * z, 1 - w - 6 * z]
        on = [Fr(-1, 2), Fr(3, 2) - 2 * x, 2 - 3 * x, 3 - 5 * x, 4 - 5 * x - 6 * z, 4 - 6 * x - 6 * z, -6 * z]
        region = [4 - 6 * x - 6 * z, 1 - x - w - 6 * z]
        return (all(t < 0 for t in off) and all(t <= 0 for t in on) and all(t < -1 for t in region)
                and z > Fr(1, 6))
    x5, w5 = Fr(5, 6), Fr(1, 2)
    ok_line = line_ok(x5, w5, Fr(1, 6) + Fr(1, 100)) and not line_ok(x5, w5, Fr(1, 6) - Fr(1, 100))
    sg, M3, l3 = Fr(1, 2), Fr(2, 3), Fr(1, 3)
    tup = [-d + max(Fr(0), (1 + (4 * sg - 1) * (l3 - d) - 2 * (M3 - 2 * d)) / 4) / 2
           for d in (Fr(k, 300) * l3 for k in range(301))]
    gate('F6', ok_line and max(tup) == 0 and tup[0] == 0,
         f'small rows\' line at x_r = 5/6, w_r = 1/2: z_r = 1/6 + 1/100 admissible {line_ok(x5, w5, Fr(1, 6) + Fr(1, 100))}, '
         f'1/6 - 1/100 {line_ok(x5, w5, Fr(1, 6) - Fr(1, 100))}; tuple exponent at the vertex: max over d {max(tup)}, '
         f'at d = ell {tup[-1]}')
    # N1
    path = sys.argv[1] if len(sys.argv) > 1 else None
    if path and os.path.exists(path):
        n, cube, sums, slope = bias(path)
        rt = math.sqrt(n)
        others = max(sums[k] for k in sums if k != 0)
        gate('N1', n == 7796 and cube < 1e-9 and sums[0] >= 8 * rt and others <= 2.5 * rt and 0.7 <= slope <= 5 / 6,
             f'{n} primes, sqrt(n) = {rt:.1f}; max |gamma_2^3 + alpha| {cube:.1e}; |sum gamma_2 alpha^k|: '
             + ', '.join(f'k={k:+d} {sums[k]:.1f}' for k in sorted(sums))
             + f'; log-slope of the untwisted sum from 2*10^4 to 8*10^4 {slope:.4f}')
    else:
        print('N1: SKIPPED  (no prime data given; pass periods_w_8e4.txt, see FIVE-SIXTHS.md section 6)')
    if FAILS:
        print('FAILED:', ', '.join(FAILS))
        sys.exit(1)
    print('all gates pass')


if __name__ == '__main__':
    main()
