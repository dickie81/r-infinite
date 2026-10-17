"""Round 498's levers off Sang's slice (README round 499).

Geometry. The release's Definition def:stage-high-data has lengths (l_x, l_y, ell), with h = 1 - l_x + ell,
M = l_x + l_y and b = l_y - l_x; Sang's slice is M + ell = 1 (round 496). Variables v = (l_x, l_y, ell, s0, mu): s0 is
the boundary and mu >= 0 the amount by which M + ell may exceed 1.

High side, relative to s0: the release's bin exponent at d = h (eq. stage-high-exponent, round 496's high side) with the
numerator rotated as in round 497. Moving w from 1 - a to 1/2 - vartheta costs l_y (delta/2 - vartheta), and the bin's
numerator U^{R + delta/2} becomes U^{R + (1-R)/(2k) - vartheta/2} times the reflection cost U^vartheta:
    E = 1/2 + delta/2 - l_y (1/2 + vartheta) - s0 - ell/2 + x delta ell + h (5/6 - w (1 - R) + vartheta/2),
w = 1 - 1/(2k). This holds for the bins delta >= 1/8 (vartheta as in levers.py), the small bins (vartheta = x delta
min(ell/h, 1/(6 kappa))) and the floor bin (R = 1, vartheta = 0; on the release's contour it is delta_f (h - l_y)/2
higher). Gate I1 checks it against exponent_lp.py's release exponent plus the rotation, off the slice.
Low side: round 496's model of the release's Proposition prop:probe-low (exponent_lp.py's six low rows, gate I2):
    s0 >= 5/6 + l_x/6 - ell/6 + max(0, theta b, 2b - l_y)/2 + max(0, 1 + 3 ell - 2M)/8 + c mu/2.
These are the three terms of the Gram bound (Proposition prop:probe-gram, with P_a = Y'^2/Q = Z^b) at tuple size d = 0,
theta = 1/6 with the exceptional term and 0 without it, and the row-norm loss. Round 496 reads the loss for M + ell <= 1
from the release's proof of Lemma lem:probe-row-norm; crossing the slice by mu costs c mu/2, and round 496 reads c = 1
from that proof's first branch.
Admissibility: round 498's hard rows in general geometry (Sang's conditions with b = l_y - l_x and h = 1 - l_x + ell),
including his range 1/6 <= ell <= 1/5, his condition l_y - ell > 11b/6 that makes the third Gram term the smaller
(round 497's absorption 2b - l_y + ell <= 0 without the Gram term; soft_third drops both, and the term then enters
through the low side's max), the short gate and the principal edge. The levers, the bootstrap and its least stage are
levers.py's.
Solving: every constraint is linear in v except the small bins. The program without them is solved by cutting planes
over the 1501 x 201 bins delta >= 1/8, with the floor bin's two rows; the small bins are then checked at the optimum. A
relaxation whose optimum satisfies the dropped constraints is optimal.
Every boundary here is a statement about this exponent system, not a theorem.

Modes: 'slice' (M + ell = 1), 'inside' (M + ell <= 1), 'cross' (M + ell <= 1 + mu at cost c mu/2).

Gates (exit status 1 if any fails):
  I1  the high side equals exponent_lp.py's release exponent plus round 497's rotation at 2000 random geometries off the
      slice and random bins (1e-12); dropping the reflection cost U^vartheta breaks it
  I2  the six low rows equal exponent_lp.py's (round 496), with and without the Gram term, at c = 0 and c = 1
  G1  on the slice: each configuration's boundary within 2e-6 of levers.py's recorded value, kappa within 1e-6, the same
      attaining stage, stage count and status, and the same walls off the principal edge
  G2  inside the slice: each boundary within 1e-8 of the slice's; off the principal edge the optimum is on the slice
      (M + ell within 1e-7 of 1)
  G3  across the slice at c = 1: each boundary within 2e-6 of its recorded value, with its walls; 13 of the 15 equal
      the slice's within 1e-8
  G4  across the slice at c = 0: each boundary within 2e-6 of its recorded value
  C2  at each configuration's attaining stage off the principal edge: the break-even cost c* = 2 p_slice / p_low from
      the duals of the inside program, recorded within 1e-3; solving at 0.95 c* crosses and lowers the boundary, and
      at 1.05 c* it does not (where p_low = 0, solving at c = 100 crosses)
  W2  the small bins are slack (max endpoint < 0) at every stage of G1-G4
  O2  the obstruction over the geometry. At delta = 0 every configuration's bin row is the C0 wall's,
      s0 >= 4/3 - 5 l_x/6 - l_y/2 + ell/3 (1e-15), and the floor bin's rows at x = 0 lie delta_f/2 above it rotated and
      delta_f (1 + h - l_y)/2 above it on the release's contour (2000 random geometries, 1e-12); so E_max exceeds the C0
      wall. Then min of max(low side, C0 wall), with b >= 0, the third-term condition and the rows every configuration
      keeps (1/6 <= ell <= 1/5, l_x > ell, h/2 < l_y, l_y < 1/2, ell/h > 1/5 and the low
      rows' limit). With the Gram term it is 13/15 inside the slice and across it at c = 1 and at c = 0; without it,
      31/36 inside and at c = 1 and 103/120 at c = 0, with break-even cost 2/15 (1/7 with the third term soft); all
      within 1e-9 (break-evens 1e-6). With round 498's rows alone (b >= 0 and the third-term condition) the
      break-evens are 1/30 and 2/15. Every configuration's boundary at c = 1 lies above its limit
  O3  with the Gram term the low side alone, under ell <= 1/5 and no other row, is at least 13/15 over the whole
      geometry at c = 0, inside the slice and across it (1e-9); dropping ell <= 1/5 or the row-norm loss breaks it
  K1  2 (31/36) - 1 = 13/18 in exact fractions: below 31/36 the bootstrap leaves Sang's range 13/18 <= kappa <= 1
  S3  with the third Gram term soft in place of Sang's two conditions, every boundary of G1-G3 moves by less than 1e-9
"""
import sys
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog, brentq
from concurrent.futures import ProcessPoolExecutor
import rotated_contour as RC
import levers as LV
import exponent_lp as EX
from rotated_contour import Rk

DL, XL, XS = RC.DL, RC.XL, RC.XS
Z0, DMIN = RC.Z0, RC.DMIN
HIGHS = {'primal_feasibility_tolerance': 1e-10, 'dual_feasibility_tolerance': 1e-10}
STAGES = 40


def low_rows(theta, cost):
    """the six low-side pieces as (name, row over v, rhs), row . v <= rhs."""
    out = []
    for gn, g in (('1', (0, 0)), ('P^(1/6)', (-theta / 2, theta / 2)), ('P^2/Y', (-1, 1 / 2))):
        for rn, r, rc in (('', (0, 0, 0), 0.0), ('+row loss', (-1 / 4, -1 / 4, 3 / 8), 1 / 8)):
            out.append(('low:' + gn + rn, [1 / 6 + g[0] + r[0], g[1] + r[1], -1 / 6 + r[2], -1.0, cost / 2],
                        -5 / 6 - rc))
    return out


def floor_rows(d, rot, rot_extra=0.0):
    """the floor bin (R = 1, vartheta = 0) at x = 0 and x = 1/2, on Sang's rotated line or the release's contour."""
    e, out = rot_extra * d / 2, []
    for x in (0.0, 0.5):
        if rot:
            c = (1 / 2 + d / 2 + 5 / 6 + e, -5 / 6 - e, -1 / 2 - e, -1 / 2 + x * d + 5 / 6 + e)
        else:
            c = ((1 + d) / 2 + 5 / 6 + d / 2, -(5 / 6 + d / 2), -(1 + d) / 2, -1 / 2 + x * d + 5 / 6 + d / 2)
        out.append(('floor bin', [c[1], c[2], c[3], -1.0, 0.0], -c[0]))
    return out


class OffSlice:
    def __init__(self, kappa, k=2, gram='paper', floor=1 / 50, rot=False, edge=LV.EDGE_SANG, tech=False, margin=False,
                 lam=1.0, counts='sang', rot_extra=0.0, mode='inside', cost=1.0, soft_third=False):
        self.kappa, self.k, self.gram, self.floor, self.rot, self.edge = kappa, k, gram, floor, rot, edge
        self.tech, self.margin, self.lam, self.counts, self.rot_extra = tech, margin, lam, counts, rot_extra
        self.mode, self.cost, self.soft_third = mode, cost, soft_third
        self.tau, self.w = 1 / (6 * kappa), 1 - 1 / (2 * k)
        R = self.count(DL, XL)
        self.gate_need = (R / (6 * kappa - 2 * XL * DL)).max() if lam == 1 else -1.0
        self.C = np.stack([c.ravel() for c in self.coeffs(DL, XL, R)])
        self.DS = np.linspace(floor, 1 / 8, 401)[:-1, None]
        self.Rs = self.count(self.DS, XS)

    def count(self, d, x):
        return (1 - d + 0 * x) if self.counts == 'dh' else Rk(d, x, self.kappa)

    def coeffs(self, d, x, R, reflection_cost=True):
        """E = C0 + C1 l_x + C2 l_y + C3 ell - s0 on the bins delta >= 1/8."""
        th = np.minimum(np.minimum(self.lam * self.tau * x * d, d / 2), 1 / 10)
        K = 5 / 6 - self.w * (1 - R) + (th / 2 if reflection_cost else -th / 2)
        z = 0 * d * x
        return 1 / 2 + d / 2 + K + z, -K + z, -(1 / 2 + th) + z, -1 / 2 + x * d + K + z

    def floor_rows(self):
        return floor_rows(self.floor, self.rot, self.rot_extra)

    def small_max(self, v):
        lx, ly, ell, s0 = v[:4]
        h = 1 - lx + ell
        th = XS * self.DS * min(ell / h, self.tau)
        return (1 / 2 + self.DS / 2 - ly * (1 / 2 + th) - s0 - ell / 2 + XS * self.DS * ell
                + h * (5 / 6 - self.w * (1 - self.Rs) + th / 2)).max()

    def fixed_rows(self):
        rows = low_rows(1 / 6 if self.gram == 'paper' else 0.0, self.cost)
        add = lambda n, r, b: rows.append((n, [float(t) for t in r], float(b)))
        add('slice', [1, 1, 1, 0, -1], 1.0)
        if self.mode == 'slice':
            add('slice=', [-1, -1, -1, 0, 0], -1.0)
        add('b>0', [1, -1, 0, 0, 0], -1e-7)
        add('ell<=1/5', [0, 0, 1, 0, 0], 1 / 5)
        add('ell>=1/6', [0, 0, -1, 0, 0], -1 / 6)
        add('lx>ell', [-1, 0, 1, 0, 0], -1e-9)
        if self.soft_third:
            pass
        elif self.gram == 'paper':
            add('ly-ell>11b/6', [-11 / 6, 5 / 6, 1, 0, 0], -1e-9)
        else:
            add('Pa^2/Y<=1', [-2, 1, 1, 0, 0], 0.0)
        if not self.tech:
            add('6k.ell>3/4', [0, 0, -6 * self.kappa, 0, 0], -3 / 4 - 1e-9)
            add('ell/h>21/100', [-0.21, 0, -0.79, 0, 0], -0.21 - 1e-9)
        else:
            add('ell/h>1/5', [-1 / 5, 0, -4 / 5, 0, 0], -1 / 5 - 1e-9)
        add('h/2<ly', [-1 / 2, -1, 1 / 2, 0, 0], -1 / 2 - 1e-9)
        add('ly<1/2', [0, 1, 0, 0, 0], 1 / 2 - 1e-9)
        s = Z0 - 1 / 6
        add('low rows', [-s, -1 / 2, s, 0, 0], (-s if self.margin else -1 / 20 - 2 * DMIN - s) - 1e-9)
        if self.lam == 1:
            g = min(self.gate_need, self.tau)
            add('short gate', [-g, 0, g - 1, 0, 0], -g - 1e-9)
        add('principal edge', [0, 0, 0, -1, 0], -self.edge)
        return rows + self.floor_rows()

    def solve(self, tol=1e-10):
        fixed = self.fixed_rows()
        A0 = np.array([r for _, r, _ in fixed]); b0 = np.array([b for _, _, b in fixed])
        nd, nx = DL.shape[0], XL.shape[1]
        ii, jj = np.meshgrid(np.arange(0, nd, 30), np.arange(0, nx, 25), indexing='ij')
        idx = np.unique(np.concatenate([(ii * nx + jj).ravel(), np.arange(0, nd, 10) * nx + nx - 1]))
        bounds = [(0, 1), (0, 1), (0, 1), (0.5, 1), (0, 0.5 if self.mode == 'cross' else 0.0)]
        for _ in range(500):
            Cb = self.C[:, idx]
            A = np.vstack([A0, np.column_stack([Cb[1], Cb[2], Cb[3], -np.ones(idx.size), np.zeros(idx.size)])])
            res = linprog([0, 0, 0, 1, 0], A_ub=A, b_ub=np.concatenate([b0, -Cb[0]]), bounds=bounds, method='highs',
                          options=HIGHS)
            if res.status == 2:
                return None
            if res.status != 0:
                raise RuntimeError(res.message)
            v = res.x
            E = self.C[0] + self.C[1] * v[0] + self.C[2] * v[1] + self.C[3] * v[2] - v[3]
            new = np.setdiff1d(np.flatnonzero(E > tol), idx)
            if new.size == 0:
                return dict(v=v, res=res, fixed=fixed, emax=E.max(), small=self.small_max(v))
            idx = np.union1d(idx, new[np.argsort(E[new])[-25:]])
        raise RuntimeError('no convergence')

    def walls(self, sol, tol=1e-6):
        v, out = sol['v'], set()
        if sol['emax'] > -tol:
            out.add('E')
        if sol['small'] > -tol:
            out.add('small delta')
        for n, r, b in sol['fixed']:
            if n == 'slice=' or (n == 'slice' and self.mode == 'slice') or np.dot(r, v) <= b - tol:
                continue
            if n.startswith('low:'):
                out.add('low side' if self.gram == 'paper' else 'Gram saving')
                out |= {'row loss'} if 'row loss' in n else set()
                out |= {'third Gram term'} if 'P^2/Y' in n else set()
            else:
                out.add(n)
        if v[4] > 1e-9:
            out.add('crossing')
        return tuple(sorted(out))

    def prices(self, sol):
        """shadow prices of the slice and of the low side: -d s0/d rhs (the marginals are <= 0)."""
        m, names = sol['res'].ineqlin.marginals, [n for n, _, _ in sol['fixed']]
        return -m[names.index('slice')], -sum(m[i] for i, n in enumerate(names) if n.startswith('low:'))


def run(args):
    cfg, mode, cost = args[:3]
    soft = len(args) > 3 and args[3]
    kappa, fp = 3 / 4, []
    for _ in range(STAGES):
        if kappa < 13 / 18:
            break
        o = OffSlice(kappa, mode=mode, cost=cost, soft_third=soft, **cfg)
        sol = o.solve()
        if sol is None:
            break
        fp.append((kappa, sol, o))
        if abs(2 * sol['v'][3] - 1 - kappa) < 1e-10:
            break
        kappa = 2 * sol['v'][3] - 1
    if not fp:
        return None
    least = min(s['v'][3] for _, s, _ in fp)
    i = max(j for j in range(len(fp)) if fp[j][1]['v'][3] <= least + 1e-7)
    kap, sol, o = fp[i]
    gap = abs(2 * fp[-1][1]['v'][3] - 1 - fp[-1][0])
    return dict(B=sol['v'][3], kappa=kap, v=sol['v'], stage=i, stages=len(fp),
                status='fixed point' if gap < 1e-9 else ('stopped' if len(fp) < STAGES else 'stage cap'),
                walls=o.walls(sol), small=max(s['small'] for _, s, _ in fp), M_ell=sol['v'][:3].sum())


def breakeven(args):
    """at a configuration's attaining stage: c* = 2 p_slice / p_low, and the boundary at 0.95 c* and 1.05 c*."""
    cfg, kappa = args
    base = OffSlice(kappa, mode='inside', **cfg).solve()
    ps, pl = OffSlice(kappa, mode='inside', **cfg).prices(base)
    B0 = base['v'][3]
    if pl < 1e-9:
        hi = OffSlice(kappa, mode='cross', cost=100.0, **cfg).solve()
        return B0, ps, pl, np.inf, None, hi['v'][3], hi['v'][4]
    cs = 2 * ps / pl
    lo = OffSlice(kappa, mode='cross', cost=0.95 * cs, **cfg).solve()
    hi = OffSlice(kappa, mode='cross', cost=1.05 * cs, **cfg).solve()
    return B0, ps, pl, cs, (lo['v'][3], lo['v'][4]), hi['v'][3], hi['v'][4]


S_LOW = Z0 - 1 / 6
KEPT = [([0, 0, -1, 0, 0], -1 / 6), ([0, 0, 1, 0, 0], 1 / 5), ([-1, 0, 1, 0, 0], 0.0),
        ([-1 / 2, -1, 1 / 2, 0, 0], -1 / 2), ([0, 1, 0, 0, 0], 1 / 2), ([-1 / 5, 0, -4 / 5, 0, 0], -1 / 5),
        ([-S_LOW, -1 / 2, S_LOW, 0, 0], -S_LOW)]
# the rows no reading drops, in their weakest forms: 1/6 <= ell <= 1/5, l_x > ell, h/2 < l_y, l_y < 1/2, ell/h > 1/5,
# and the low rows' limit h(z_0 - 1/6) - l_y/2 < 0


def obstruction(gram, cost, mode, kept=True, soft=False):
    """min over the geometry of max(low side, C0 wall): b >= 0, Sang's condition on the third Gram term (without the
    Gram term, round 497's absorption) unless soft, and the rows every configuration keeps if kept."""
    rows = low_rows(1 / 6 if gram == 'paper' else 0.0, cost)
    A, b = [r for _, r, _ in rows], [c for _, _, c in rows]
    A += [[-5 / 6, -1 / 2, 1 / 3, -1, 0], [1, 1, 1, 0, -1], [1, -1, 0, 0, 0]]  # C0 wall, M + ell <= 1 + mu, b >= 0
    b += [-4 / 3, 1.0, 0.0]
    if not soft:
        A.append([-2, 1, 1, 0, 0] if gram == 'none' else [-11 / 6, 5 / 6, 1, 0, 0]); b.append(0.0)
    for r, c in (KEPT if kept else []):
        A.append(r); b.append(c)
    res = linprog([0, 0, 0, 1, 0], A_ub=A, b_ub=b, bounds=[(0, 1)] * 3 + [(0, 2), (0, 2.0 if mode == 'cross' else 0.0)],
                  method='highs', options=HIGHS)
    return res.fun


def breakeven_limit(gram, kept, soft, base):
    """the cost below which crossing lowers the limit base; None if it does not at c = 0."""
    f = lambda c: obstruction(gram, c, 'cross', kept, soft) - base + 1e-10
    return brentq(f, 0.0, 1.0, xtol=1e-12) if f(0.0) < 0 else None


FP = 'fixed point'
CROSS1 = {   # name: (B, kappa, stage, stages, status, walls) across the slice at c = 1, where it differs from the slice
    "Sang's inputs + Gram removed":
        (0.8709157, 0.7418314, 4, 5, FP, ('6k.ell>3/4', 'E', 'Gram saving', 'crossing', 'ell/h>21/100', 'slice')),
    "Sang's inputs + Gram removed + all readings":
        (0.8694484, 0.7500000, 0, 12, FP, ('E', 'Gram saving', 'crossing', 'ell>=1/6', 'short gate', 'slice')),
}
CROSS0 = {   # name: (B, status) across the slice at c = 0
    "Sang's inputs": (0.8713556, FP), "Sang's inputs + all readings": (0.8713556, FP),
    "Sang's inputs + Gram removed": (0.8700000, FP), "Sang's inputs + Gram removed + all readings": (0.8621496, FP),
    "Sang's inputs + amplifier x2": (0.8709486, FP), "Sang's inputs + amplifier to the caps": (0.8709293, FP),
    "Sang's inputs + DH counts": (0.8700000, FP), "Sang's inputs + DH counts + all readings": (0.8667333, FP),
    "Lindelof on average": (0.8700000, FP), "Lindelof + rotated floor": (0.8700000, FP),
    "Lindelof + floor 1/1000": (0.8700000, FP), "Lindelof + Gram removed": (0.8700000, FP),
    "Lindelof + all readings": (0.8667333, FP), "Lindelof + all readings + Gram removed": (0.8584333, 'stopped'),
    "everything": (0.8584333, 'stopped'),
}
BREAKEVEN = {   # name: c* at the attaining stage, off the principal edge
    "Sang's inputs": 0.1625, "Sang's inputs + all readings": 0.1625, "Sang's inputs + Gram removed": np.inf,
    "Sang's inputs + Gram removed + all readings": np.inf, "Sang's inputs + amplifier x2": 0.1603,
    "Sang's inputs + amplifier to the caps": 0.1896, "Sang's inputs + DH counts": 0.1623,
    "Sang's inputs + DH counts + all readings": 0.1665, "Lindelof on average": 0.1623,
    "Lindelof + all readings": 0.1665,
    "Lindelof + all readings + Gram removed": 0.3824, "everything": 0.5000,
}


def fmt(r):
    if r is None:
        return 'infeasible'
    v = r['v']
    return (f'B = {r["B"]:.7f}  kappa {r["kappa"]:.7f}  stage {r["stage"]} of {r["stages"]}, {r["status"]}  '
            f'(l_x, l_y, ell) = ({v[0]:.5f}, {v[1]:.5f}, {v[2]:.5f}), M + ell = {r["M_ell"]:.6f}, mu = {v[4]:.4f}  '
            f'walls: {", ".join(r["walls"])}')


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    rng = np.random.default_rng(499)
    dev = dev_s = 0.0
    for _ in range(2000):
        kap, k = rng.uniform(13 / 18, 3 / 4), int(rng.integers(2, 5))
        lx, ly, ell = rng.uniform(0.25, 0.45), rng.uniform(0.35, 0.5), rng.uniform(1 / 6, 1 / 5)
        s0, mu = rng.uniform(0.85, 0.9), 0.0
        d, x = rng.uniform(1 / 8, 3 / 4), rng.uniform(0, 0.5)
        m = EX.Model(kappa=kap, slice_eq=False)
        R = float(m.R(np.array([d]), np.array([x]))[0])
        v = np.array([lx, ly, ell, s0, mu])
        o = OffSlice(kap, k=k)
        th = min(o.tau * x * d, d / 2, 1 / 10)
        h = 1 - lx + ell
        rot = (float(m.E(v, np.array([d]), np.array([x]))[0]) + ly * (d / 2 - th)
               + h * ((1 - R) / (2 * k) - th / 2 + th - d / 2))
        for rc, acc in ((True, 'dev'), (False, 'dev_s')):
            c = o.coeffs(np.array([d]), np.array([x]), np.array([R]), reflection_cost=rc)
            mine = float(c[0][0] + c[1][0] * lx + c[2][0] * ly + c[3][0] * ell - s0)
            if rc:
                dev = max(dev, abs(mine - rot))
            else:
                dev_s = max(dev_s, abs(mine - rot))
    gate('I1', dev < 1e-12 and dev_s > 1e-3,
         f'high side = release exponent (exponent_lp.py) + rotation at 2000 points off the slice: max deviation '
         f'{dev:.1e}; sabotage, reflection cost dropped: {dev_s:.3f}')

    ok, worst = True, 0.0
    for th in (1 / 6, 0.0):
        for cost in (0.0, 1.0):
            A, b = EX.Model(theta=th, slice_eq=False).low_rows(cost)
            mine = low_rows(th, cost)
            worst = max(worst, np.abs(A[:6] - np.array([r for _, r, _ in mine])).max(),
                        np.abs(b[:6] - np.array([c for _, _, c in mine])).max())
    gate('I2', worst < 1e-15, f"the six low rows equal exponent_lp.py's, theta in (1/6, 0), c in (0, 1): "
                              f"max deviation {worst:.0e}")

    names = [nm for nm, _, _ in LV.CONFIGS]
    jobs = [(cfg, mode, cost) for mode, cost in (('slice', 1.0), ('inside', 1.0), ('cross', 1.0), ('cross', 0.0))
            for _, cfg, _ in LV.CONFIGS]
    with ProcessPoolExecutor(max_workers=4) as ex:
        res = list(ex.map(run, jobs))
    n = len(names)
    sl, ins, c1, c0 = res[:n], res[n:2 * n], res[2 * n:3 * n], res[3 * n:]

    for (nm, cfg, rec), r in zip(LV.CONFIGS, sl):
        B, kap, i, stages, status, walls = rec
        edge = abs(B - cfg.get('edge', LV.EDGE_SANG)) < 1e-6
        ok = (r is not None and abs(r['B'] - B) < 2e-6 and abs(r['kappa'] - kap) < 1e-6 and r['stage'] == i
              and r['stages'] == stages and r['status'] == status and (edge or r['walls'] == walls))
        gate('G1', ok, f'{nm:44s} {fmt(r)}  (levers.py: {B:.7f}, {", ".join(walls)})')

    for (nm, cfg, rec), r, s in zip(LV.CONFIGS, ins, sl):
        edge = abs(rec[0] - cfg.get('edge', LV.EDGE_SANG)) < 1e-6
        ok = r is not None and abs(r['B'] - s['B']) < 1e-8 and (edge or abs(r['M_ell'] - 1) < 1e-7)
        gate('G2', ok, f'{nm:44s} {fmt(r)}')

    for (nm, cfg, rec), r, s in zip(LV.CONFIGS, c1, sl):
        if nm in CROSS1:
            B, kap, i, stages, status, walls = CROSS1[nm]
            ok = (r is not None and abs(r['B'] - B) < 2e-6 and abs(r['kappa'] - kap) < 1e-6 and r['stage'] == i
                  and r['stages'] == stages and r['status'] == status and r['walls'] == walls)
        else:
            ok = r is not None and abs(r['B'] - s['B']) < 1e-8
        gate('G3', ok, f'{nm:44s} {fmt(r)}')

    for nm, r in zip(names, c0):
        B, status = CROSS0[nm]
        gate('G4', r is not None and abs(r['B'] - B) < 2e-6 and r['status'] == status, f'{nm:44s} {fmt(r)}')

    smax = max(r['small'] for r in sl + ins + c1 + c0)
    gate('W2', smax < 0, f'small bins: largest endpoint over every stage of G1-G4 {smax:.1e}')

    todo = [(nm, cfg, r['kappa']) for (nm, cfg, rec), r in zip(LV.CONFIGS, sl) if nm in BREAKEVEN]
    with ProcessPoolExecutor(max_workers=4) as ex:
        be = list(ex.map(breakeven, [(cfg, kap) for _, cfg, kap in todo]))
    for (nm, cfg, kap), (B0, ps, pl, cs, lo, hiB, hi_mu) in zip(todo, be):
        want = BREAKEVEN[nm]
        if np.isinf(want):
            ok = np.isinf(cs) and hi_mu > 1e-6 and hiB < B0 - 1e-6
            msg = f'p_slice {ps:.4f}, p_low {pl:.1e}: crosses at any cost; at c = 100: B = {hiB:.7f} (inside {B0:.7f})'
        else:
            ok = (abs(cs - want) < 1e-3 and lo[1] > 1e-6 and lo[0] < B0 - 1e-9 and hi_mu < 1e-9
                  and abs(hiB - B0) < 1e-9)
            msg = (f'p_slice {ps:.4f}, p_low {pl:.4f}, c* = {cs:.4f}; at 0.95 c*: B = {lo[0]:.7f}, mu = {lo[1]:.4f}; '
                   f'at 1.05 c*: B = {hiB:.7f} (inside {B0:.7f})')
        gate('C2', ok, f'{nm:44s} kappa {kap:.7f}: {msg}')

    cdev = fdev = 0.0
    wall = np.array([4 / 3, -5 / 6, -1 / 2, 1 / 3])
    for nm, cfg, _ in LV.CONFIGS:
        for kap in (13 / 18, 3 / 4):
            o = OffSlice(kap, **cfg)
            c = np.array([t.ravel() for t in o.coeffs(0 * XL, XL, o.count(0 * XL, XL))])
            cdev = max(cdev, np.abs(c - wall[:, None]).max())
    for lx, ly, ell, d in zip(rng.uniform(0.25, 0.45, 2000), rng.uniform(0.35, 0.5, 2000),
                              rng.uniform(1 / 6, 1 / 5, 2000), rng.uniform(1e-4, 1 / 50, 2000)):
        w0 = wall[0] + wall[1] * lx + wall[2] * ly + wall[3] * ell
        h = 1 - lx + ell
        for rot, extra in ((True, d / 2), (False, d / 2 + d * (h - ly) / 2)):
            n_, r, b_ = floor_rows(d, rot)[0]
            fdev = max(fdev, abs((-b_ + r[0] * lx + r[1] * ly + r[2] * ell) - (w0 + extra)))
    O = {}
    for gram, soft, base in (('paper', False, 13 / 15), ('none', False, 31 / 36), ('none', True, 31 / 36)):
        O[(gram, soft)] = (obstruction(gram, 1.0, 'inside', True, soft), obstruction(gram, 1.0, 'cross', True, soft),
                           obstruction(gram, 0.0, 'cross', True, soft), breakeven_limit(gram, True, soft, base))
    be_min = (breakeven_limit('paper', False, False, 13 / 15), breakeven_limit('none', False, False, 31 / 36))
    above = all(r['B'] > O[('paper' if cfg.get('gram', 'paper') == 'paper' else 'none', False)][1]
                for (nm, cfg, _), r in zip(LV.CONFIGS, c1))
    pa, nh, ns = O[('paper', False)], O[('none', False)], O[('none', True)]
    ok = (cdev < 1e-15 and fdev < 1e-12 and all(abs(t - 13 / 15) < 1e-9 for t in pa[:3]) and pa[3] is None
          and abs(nh[0] - 31 / 36) < 1e-9 and abs(nh[1] - 31 / 36) < 1e-9 and abs(nh[2] - 103 / 120) < 1e-9
          and abs(nh[3] - 2 / 15) < 1e-6
          and abs(ns[0] - 31 / 36) < 1e-9 and abs(ns[1] - 31 / 36) < 1e-9 and abs(ns[2] - 103 / 120) < 1e-9
          and abs(ns[3] - 1 / 7) < 1e-6
          and abs(be_min[0] - 1 / 30) < 1e-6 and abs(be_min[1] - 2 / 15) < 1e-6 and above)
    gate('O2', ok, f'delta = 0 rows = the C0 wall (max deviation {cdev:.0e}), floor bin above it (max deviation '
                   f'{fdev:.0e}); with the rows every configuration keeps (inside / across at c = 1 / at c = 0 / '
                   f'break-even): Gram '
                   f'term {pa[0]:.10f} / {pa[1]:.10f} / {pa[2]:.10f} / none; without it {nh[0]:.10f} / {nh[1]:.10f} / '
                   f'{nh[2]:.10f} / {nh[3]:.8f} (31/36, 103/120, 2/15); third Gram term soft {ns[0]:.10f} / '
                   f"{ns[1]:.10f} / {ns[2]:.10f} / {ns[3]:.8f} (1/7). With round 498's rows alone (b >= 0 and the "
                   f'third-term condition): break-even {be_min[0]:.8f} (1/30) and {be_min[1]:.8f} (2/15). Every '
                   f'configuration at c = 1 above its limit')

    def low_only(cap=True, loss=True):
        rows = [r for r in low_rows(1 / 6, 0.0) if loss or 'row loss' not in r[0]]
        A, b = [r for _, r, _ in rows] + [[1, 1, 1, 0, -1]], [c for _, _, c in rows] + [1.0]
        if cap:
            A.append([0, 0, 1, 0, 0]); b.append(1 / 5)
        return linprog([0, 0, 0, 1, 0], A_ub=A, b_ub=b, bounds=[(0, 1)] * 3 + [(0, 2), (0, 2)], method='highs',
                       options=HIGHS).fun
    lo3 = (low_only(), low_only(cap=False), low_only(loss=False))
    gate('O3', abs(lo3[0] - 13 / 15) < 1e-9 and lo3[1] < 13 / 15 - 1e-3 and lo3[2] < 13 / 15 - 1e-3,
         f'the low side alone with the Gram term, under ell <= 1/5 only, inside the slice and across it at c = 0: '
         f'min {lo3[0]:.10f} (13/15); sabotage, ell <= 1/5 dropped: {lo3[1]:.6f}; row-norm loss dropped: {lo3[2]:.6f}')

    gate('K1', 2 * Fr(31, 36) - 1 == Fr(13, 18),
         f"2 (31/36) - 1 = {2 * Fr(31, 36) - 1}: below 31/36 the bootstrap's kappa = 2B - 1 leaves Sang's range "
         f"13/18 <= kappa <= 1")

    jobs = [(cfg, mode, cost, True) for mode, cost in (('slice', 1.0), ('inside', 1.0), ('cross', 1.0))
            for _, cfg, _ in LV.CONFIGS]
    with ProcessPoolExecutor(max_workers=4) as ex:
        soft = list(ex.map(run, jobs))
    dsoft = max(abs(a['B'] - b['B']) for a, b in zip(soft, sl + ins + c1))
    gate('S3', dsoft < 1e-9, f"the third Gram term soft in place of Sang's two conditions: every boundary of G1-G3 "
                             f"moves by at most {dsoft:.1e}")

    print(f'{fails} gate(s) failed' if fails else 'all gates pass')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
