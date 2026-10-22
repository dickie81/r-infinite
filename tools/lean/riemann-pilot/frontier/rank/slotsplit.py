"""The slot product split in two, the ladder of inputs, and the vertex's bins (FIVE-SIXTHS.md, section 7).

The slot-split bound.  Lemma lem:hybrid-energy bounds the inner slot sums of its proof by Heath-Brown's cubic large
sieve over the columns j (norm ~ N) against the active slot products P (norm ~ L = Z^{z_a}), N + L + (NL)^{2/3}, and
treats the tuple coefficient a(P) as a general bounded function: the release's proof of Lemma lem:reflected-energy
says "The function \\(a\\) need not retain product form at this norm step."  Before that step the coefficient is a
product over the active slots of one-prime factors times the mark-mark phases, and for two active marks
(j_p = j_q = 0) the release's eq. reflection-pair-phase gives (q/p)_3^{j_p + j_q + 2} = (q/p)_3^2.  The release's K is
even and its slots have equal lengths l/K.  Split the active slots into two halves, P = AB, of norms L_A, L_B.  For a
fixed column j the inner sum is a bilinear form sum_{A,B} x_j(A) y_j(B) conj((B/A)_3), and the cubic large sieve in
(A, B) bounds its square by (L_A + L_B + (L_A L_B)^{2/3}) |x|^2 |y|^2, which is about L^{2/3} for balanced halves.
Summed over the ~N columns this gives N L^{2/3}, so the factor becomes min{N + L + (NL)^{2/3}, N L^{2/3}}: in the
release's notation u = min{v, z_a, (v + z_a)/3} becomes max{u, z_a/3} (up to O(l/K), which K absorbs).

Gates (exit status 1 if any fails):
  S1  round 500's dyad program (crossing.py) with u replaced by max(u, z_a/3): (a) without the new row it is
      crossing.formula (1e-9) at 300 random (M', l') with l' <= 0.36, M' >= (1 - l')/2; (b) with it, at the same kind
      of points, it is at most M' + max(0, M' + l' - 1, (1 + 2 l' - 2M')/4) (1e-9), with equality (1e-9) wherever
      M' >= 1/2 - l'/3 + 1/100; (c) at (2/3, 1/3) the excess is 1/12 (the release's 1/6), attained at a dyad with
      v = z_a/3 = 1/9, z_a = 1/3, l_b = e = 0.  The second branch (1 + 2l' - 2M')/4 is FIVE-SIXTHS.md's
      (1 + (4 sigma - 1) l' - 2M')/4 at sigma = 3/4.
  S2  the low side 5/6 - l/6 + min over l_x of (l_x/6 + max(0, b/6, 2b - l_y)/2) + X/2, X the excess of S1's program
      at d = 0, minimized over a grid of (M, l) with M >= 2l, M >= (1 - l)/2 and M + l <= 1: 41/48 at (3/4, 1/4)
      (1e-9), and 13/15 without the new row; fivesixths.low_min(3/4) is 41/48 too; at (3/4, 1/4) the tuple exponent
      -d + X(M - 2d, l - d)/2 is <= 0 for d in [0, l] (1e-9), so the low side is taken at d = 0.
  S3  the system with Sang's inputs and the readings (fivesixths.Five, bootstrapped from kappa = 3/4): (i) with
      Sang's rotation and no row saving the boundary is 0.8748866 (2e-6) at sigma = 1, 3/4 and 1/2, with the bins
      'E' among the walls and no row loss; (ii) with a uniform row saving U^{1/10}, no rotation and the small rows'
      line 1/6 + 1/100, sigma = 3/4 gives 41/48 and sigma = 1 gives 13/15 (1e-6).
  S4  the vertex's bins: (i) in exact arithmetic, at (1/3, 1/3, 1/3) with density-hypothesis counts R = 1 - delta,
      Lindelof (w = 1) and no rotation, the bin endpoint at x = 1/2 is 1 - delta/3 - s0 for 24 rational delta in
      [1/8, 5/6], so s0 = 5/6 needs a saving at least 1/6 - delta/3 on every bin with delta < 1/2; (ii) in the
      program (sigma = 1/2, small rows' line 1/6 + 1/100, no rotation), DH counts with Lindelof and a saving U^{3/10}
      on the floor bin and the small bins alone give 31/36 with 'E' among the walls, and with U^{1/5} on every bin
      give 5/6 (2e-7).
  S5  the dictionary between hybrid bounds and FIVE-SIXTHS.md's sigma (the parameter of the second branch
      (1 + (4 sigma - 1) l' - 2M')/4, which section 2 of that note misdescribed as the trivial dual's exponent):
      with the factor replaced by min(release, N L^{1/2}) (every column's slot sum at square-root size), by
      N + (NL)^{2/3} (the L term dropped) and by N + (NL)^{1/2} (a square-root sieve), the dyad program never exceeds
      the second branch with sigma = 5/8, 2/3 and 1/2 (1e-9 at S1's points), equals it at the low side's optimum,
      and the least low side, by fivesixths.low_min and by the exact program on S2's grid, is 71/84, 28/33 and 5/6.
      So sigma = 1/2, the floor 5/6, needs the square-root sieve for the slot coefficients; square-root slot sums
      at every column give 71/84, and the slot-split bound gives 41/48.

Every number here is a statement about the pilot's model of the release's exponent system (frontier/wall78 and
fivesixths.py), not a theorem about L-functions.

Usage: python3 slotsplit.py     (about 40 s)
"""
import os
import sys
from fractions import Fraction as Fr
from concurrent.futures import ProcessPoolExecutor

import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'wall78'))
import fivesixths as F      # noqa: E402
import crossing as X        # noqa: E402
import levers as LV         # noqa: E402

HIGHS = F.HIGHS
TY, BASE, UNIT, P1, P2 = X.TY, X.BASE, X.UNIT, X.P1, X.P2
FAILS = []


def gate(name, ok, msg):
    print(f'{name}: {"PASS" if ok else "FAIL"}  {msg}', flush=True)
    if not ok:
        FAILS.append(name)


# ---------------------------------------------------------------- S1: the dyads
def emax_F(Mp, lp, a=1.0, b=2 / 3, sc=None):
    """the maximum of the release's E over the dyads when the hybrid factor N + L + (NL)^{2/3} is replaced by
    max(N, L^a, (NL)^b), optionally capped by a per-column bound N L^{sc}: -u = max(v, a z_a, b(v + z_a)) - v - z_a,
    then min(-u, (sc - 1) z_a).  a = 1, b = 2/3, sc = None is the release (crossing.emax)."""
    pieces = (-UNIT[6], (a - 1) * UNIT[6] - UNIT[7], (b - 1) * (UNIT[6] + UNIT[7]))
    A = [[1, 1, 0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 1, 1, 1, 0, 0, 0, 0], list(-TY)]
    b0 = [Mp, 0.0, 0.0, -(1 + lp)]
    best, arg = -np.inf, None
    for p1 in P1:
        for p2 in pieces:
            c = np.concatenate([BASE + p1 - TY / 2, [1.0]])
            AA = [r + [0.0] for r in A] + [list(-p2) + [1.0]]
            bb = list(b0) + [0.0]
            if sc is not None:
                AA.append([0, 0, 0, 0, 0, 0, 1 - sc, 0, 0, 0, 1.0]); bb.append(0.0)
            r = linprog(-c, A_ub=AA, b_ub=bb, bounds=[(0, None)] * 6 + [(0, lp)] + [(0, None)] * 3 + [(None, None)],
                        method='highs', options=HIGHS)
            if r.status == 0 and -r.fun + (1 + lp) / 2 > best:
                best, arg = -r.fun + (1 + lp) / 2, r.x
    return best, arg


SPLIT = dict(sc=2 / 3)          # the slot-split bound: per column L^{2/3}
DICTIONARY = (   # (name, hybrid bound, second-branch coefficient of l', optimum (M, ell), least low side)
    ('every column at square-root size', dict(sc=1 / 2), 3 / 2, (5 / 7, 2 / 7), 71 / 84),
    ('L term dropped', dict(a=0.0), 5 / 3, (8 / 11, 3 / 11), 28 / 33),
    ('square-root sieve N + (NL)^(1/2)', dict(a=0.0, b=0.5), 1.0, (2 / 3, 1 / 3), 5 / 6),
)


def emax_split(Mp, lp, split=True):
    return emax_F(Mp, lp, **(SPLIT if split else {}))


def split_formula(Mp, lp):
    return Mp + max(0, Mp + lp - 1, (1 + 2 * lp - 2 * Mp) / 4)


# ---------------------------------------------------------------- S2: the low side
def gram_min(M, ell, n=201):
    """min over l_x in [ell, M/2] of l_x/6 + max(0, b/6, 2b - l_y)/2 (piecewise linear: grid with the kinks)."""
    xs = set(np.linspace(ell, M / 2, n))
    for t in (M / 2, M / 3, (2 * M) / 5, ell):          # b = 0; b/6 = 2b - l_y (l_x = M(11/23)... ) checked by grid
        if ell <= t <= M / 2:
            xs.add(t)
    best = np.inf
    for lx in xs:
        ly = M - lx
        b = ly - lx
        best = min(best, lx / 6 + max(0.0, b / 6, 2 * b - ly) / 2)
    return best


def low_side(M, ell, **kw):
    Xs = emax_F(M, ell, **kw)[0] - M
    return 5 / 6 - ell / 6 + gram_min(M, ell) + Xs / 2


def low_grid(extra=(), **kw):
    best = (np.inf, None, None)
    pts = [(M, ell) for M in np.linspace(0.5, 1.0, 21) for ell in np.linspace(0.15, 0.4, 21)]
    pts += [(0.75, 0.25), (0.8, 0.2)] + list(extra)
    for M, ell in pts:
        if M < 2 * ell - 1e-12 or M < (1 - ell) / 2 or M + ell > 1 + 1e-12:
            continue
        s = low_side(M, ell, **kw)
        if s < best[0]:
            best = (s, M, ell)
    return best


# ---------------------------------------------------------------- S3, S4: the system
class Five2(F.Five):
    """fivesixths.Five with the row saving split: eta_L on the floor bin and the small bins, eta (eta_E) on the bins
    delta >= 1/8."""

    def __init__(self, kappa, eta_L=None, **kw):
        super().__init__(kappa, **kw)
        self.eta_L = self.eta if eta_L is None else eta_L

    def small_max(self, v):
        return F.O.OffSlice.small_max(self, v) - self.eta_L * (1 - v[0] + v[2])

    def floor_rows(self):
        e = self.eta_L
        return [(n, [r[0] + e, r[1], r[2] - e, r[3], r[4]], b + e) for n, r, b in F.O.OffSlice.floor_rows(self)]


def boot(job):
    cfg, kw = job
    kappa, fp = 3 / 4, []
    for _ in range(40):
        if kappa < 13 / 18 - 1e-12:
            break
        prog = Five2(kappa, **cfg, **kw)
        sol = prog.solve()
        if sol is None:
            break
        fp.append((float(sol['v'][3]), kappa, prog.walls(sol)))
        if abs(2 * sol['v'][3] - 1 - kappa) < 1e-10:
            break
        kappa = 2 * sol['v'][3] - 1
    return min(fp, key=lambda t: t[0]) if fp else None


def main():
    rng = np.random.default_rng(20261022)
    # S1
    pts = []
    while len(pts) < 300:
        m, l = rng.uniform(0, 1.3), rng.uniform(0, 0.36)
        if m >= (1 - l) / 2 + 1e-3:
            pts.append((m, l))
    dev_rel = max(abs(emax_split(m, l, split=False)[0] - X.formula(m, l)) for m, l in pts)
    over, dev_eq, n_eq = 0.0, 0.0, 0
    for m, l in pts:
        e = emax_split(m, l)[0]
        over = max(over, e - split_formula(m, l))
        if m >= 0.5 - l / 3 + 0.01:
            dev_eq = max(dev_eq, abs(e - split_formula(m, l))); n_eq += 1
    e, w = emax_split(2 / 3, 1 / 3)
    at = abs(w[7] - 1 / 9) < 1e-9 and abs(w[6] - 1 / 3) < 1e-9 and abs(w[8]) < 1e-9 and abs(w[9]) < 1e-9
    gate('S1', dev_rel < 1e-9 and over < 1e-9 and dev_eq < 1e-9 and n_eq > 150 and abs(e - 2 / 3 - 1 / 12) < 1e-9
         and at,
         f'{len(pts)} dyad programs: without the split vs crossing.formula {dev_rel:.1e}; with it, above '
         f'M\' + max(0, M\'+l\'-1, (1+2l\'-2M\')/4) by at most {over:.1e}, equal within {dev_eq:.1e} at the {n_eq} '
         f'points with M\' >= 1/2 - l\'/3 + 1/100; at (2/3, 1/3) excess {e - 2 / 3:.6f} at v = {w[7]:.4f}, '
         f'z_a = {w[6]:.4f}, l_b = {w[8]:.1e}, e = {w[9]:.1e}')
    # S2
    s_split, Ms, ls = low_grid(**SPLIT)
    s_rel, Mr, lr = low_grid()
    lm = F.low_min(0.75)[0]
    tup = max(-d + (emax_split(0.75 - 2 * d, 0.25 - d)[0] - (0.75 - 2 * d)) / 2
              for d in np.linspace(0, 0.25, 26) if 0.75 - 2 * d >= (1 - (0.25 - d)) / 2)
    gate('S2', abs(s_split - 41 / 48) < 1e-9 and abs(Ms - 0.75) < 1e-9 and abs(ls - 0.25) < 1e-9
         and abs(s_rel - 13 / 15) < 1e-9 and abs(lm - 41 / 48) < 1e-9 and tup <= 1e-9,
         f'least low side with the split {s_split:.9f} at (M, l) = ({Ms:.3f}, {ls:.3f}) (41/48 = {41/48:.9f}); '
         f'without it {s_rel:.9f} (13/15) at ({Mr:.3f}, {lr:.3f}); low_min(3/4) = {lm:.9f}; tuple exponent max over '
         f'd {tup:.1e}')
    # S3, S4
    R, z0 = LV.READ, 1 / 6 + 1 / 100
    D2, NOROT = ('ell<=1/5', 'ell>=1/6'), ('h/2<ly', 'ell<=1/5', 'ell>=1/6')
    sang = dict(k=2, soft_third=True, **R)
    sang0 = dict(k=2, lam=0.0, soft_third=True, **R)
    dhl0 = dict(k=LV.LINDELOF, counts='dh', lam=0.0, soft_third=True, **R)
    jobs = [(sang, dict(sigma=1.0, drop=D2)), (sang, dict(sigma=0.75, drop=D2)), (sang, dict(sigma=0.5, drop=D2)),
            (sang0, dict(sigma=0.75, eta=0.1, z0=z0, drop=NOROT)), (sang0, dict(sigma=1.0, eta=0.1, z0=z0, drop=NOROT)),
            (dhl0, dict(sigma=0.5, eta=0.0, eta_L=0.3, z0=z0, drop=NOROT)),
            (dhl0, dict(sigma=0.5, eta=0.2, z0=z0, drop=NOROT))]
    with ProcessPoolExecutor(4) as ex:
        res = list(ex.map(boot, jobs))
    for (cfg, kw), r in zip(jobs, res):
        print(f'    {str({k: v for k, v in kw.items() if k != "drop"}):60s} B = {r[0]:.7f} kappa {r[1]:.5f} walls {r[2]}')
    ok3 = (all(abs(r[0] - 0.8748866) < 2e-6 and 'E' in r[2] and 'row loss' not in r[2] for r in res[:3])
           and abs(res[3][0] - 41 / 48) < 1e-6 and abs(res[4][0] - 13 / 15) < 1e-6)
    gate('S3', ok3, f'(i) eta = 0: sigma 1 {res[0][0]:.7f}, 3/4 {res[1][0]:.7f}, 1/2 {res[2][0]:.7f}; (ii) U^(1/10): '
         f'sigma 3/4 {res[3][0]:.7f} (41/48 = {41/48:.7f}), sigma 1 {res[4][0]:.7f} (13/15 = {13/15:.7f})')
    v3, bad = Fr(1, 3), 0
    for i in range(24):
        d = Fr(1, 8) + Fr(i, 23) * (Fr(5, 6) - Fr(1, 8))
        K = Fr(5, 6) - (1 - (1 - d))          # w = 1, R = 1 - delta, vartheta = 0
        E = (Fr(1, 2) + d / 2 + K) - K * v3 - Fr(1, 2) * v3 + (-Fr(1, 2) + Fr(1, 2) * d + K) * v3
        if E != 1 - d / 3:
            bad += 1
    gate('S4', bad == 0 and abs(res[5][0] - 31 / 36) < 1e-6 and 'E' in res[5][2] and abs(res[6][0] - 5 / 6) < 2e-7,
         f'(i) endpoint 1 - delta/3 - s0 at the vertex: {24 - bad} of 24 bins exact; (ii) savings on the low bins '
         f'only {res[5][0]:.7f} (31/36 = {31/36:.7f}), walls {res[5][2]}; on every bin {res[6][0]:.9f}')
    # S5: the dictionary between hybrid bounds and the second branch
    rows, ok5 = [], True
    for name, kw, coef, opt, value in DICTIONARY:
        sg = (coef + 1) / 4
        over = max(emax_F(m, l, **kw)[0] - (m + max(0, m + l - 1, (1 + coef * l - 2 * m) / 4)) for m, l in pts)
        M0, l0 = opt
        at = abs(emax_F(M0, l0, **kw)[0] - M0 - max(0, M0 + l0 - 1, (1 + coef * l0 - 2 * M0) / 4))
        lm = F.low_min(sg)[0]
        g = low_grid(extra=[opt], **kw)
        ok = (over < 1e-9 and at < 1e-9 and abs(lm - value) < 1e-9 and abs(F.low_min_formula(sg) - value) < 1e-9
              and abs(g[0] - value) < 1e-9)
        ok5 = ok5 and ok
        rows.append(f'{name}: sigma {sg:.4f}, formula exceeded by {over:.1e}, exact at the optimum {at:.1e}, '
                    f'least low side {lm:.9f} (LP) {g[0]:.9f} (exact program on the grid)')
    gate('S5', ok5, '; '.join(rows))
    if FAILS:
        print('FAILED:', ', '.join(FAILS))
        sys.exit(1)
    print('all gates pass')


if __name__ == '__main__':
    main()
