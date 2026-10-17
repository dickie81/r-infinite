"""More levers on the rotated 7/8 comparison, and a correction to round 497's R5 (README round 498).

Builds on rotated_contour.py (round 497): Sang's slice l_x = (1-b-ell)/2, l_y = (1+b-ell)/2, h = (1+b+3 ell)/2,
his rotated contour and exact mode.

The boundary. Sang records the high side "relative to the low bound C_b(B(ell))" (his eq. full-exponent contains
a - B(ell)), and his Lemma closure compares the low bound Z^{C_b(B(ell)) + Delta/4} and the high side's remainder
Z^{C_b(beta_*) - rho} with the principal term, "Since C_b has slope one". So a zero at beta_* is excluded once
C_b(beta_*) exceeds both the low side's exponent and the high side's. With E_max(b, ell) the largest high-side
endpoint relative to B(ell) (the bins delta >= 1/8, the small bins and the floor bin), the boundary is
    max(edge, B(ell) + max(t_min(b), E_max(b, ell))),   B(ell) = 11/12 - ell/4,
with t_min = 0 when the low side carries the Gram bound's exceptional term (his eq. signal-low,
C_b(B(ell)) = l_x/2 + b/12), t_min = -b/12 when it does not, and edge the principal row's condition (Sang's H_eta is
holomorphic on Re s > 87/100). With the term this is Sang's reading wherever the walls rise faster than ell/4 (gate L1
records his value); without it, the high side's slack buys as much of the saving b/12 as it can carry. It is
minimised over b and ell; the short gate and his other admissibility conditions stay hard.

The bootstrap is his, kappa_{n+1} = 2 B_n - 1 from kappa_0 = 3/4, while kappa >= 13/18, until |2B - 1 - kappa| < 1e-10,
a stage with no admissible point, or 40 stages. Each stage's B_n is a boundary (its kappa is licensed by B_{n-1}), so
the bootstrap's boundary is the least of them, reported at the last stage within 1e-7 of it. Where B falls as kappa
rises (his 6 kappa ell > 3/4 or the short gate binding) that is the first stage, kappa = 3/4, not the iteration's fixed
point; his admissibility caps kappa at 3/4, and the script keeps the cap.

Correction. Round 497's R5 took the boundary B(ell) - b/12 with every endpoint <= 0 relative to B(ell), and applied
87/100 to B(ell): the high side was never asked to carry the saving. Gate C1 reproduces its two values on that legacy
path (with round 497's own bootstrap, the last stage) and records the corrected ones.

Exact mode, as in round 497, with one change: Sang's C_0 < -1/250 is the delta = 0 end of his coarse small-delta
scalar ("\\max\\{C_0,C_0+A_{\\rm sm}/8\\}<-1/250"), which exact mode replaces by E_small from the floor up; it is
dropped here (the legacy path keeps it).

Levers. Readings of the release and of Sang (none re-derived):
  floor   the detector floor a_0 = 1/2 + delta_f/2. The release fixes 51/100 (delta_f = 1/50) and, in every use read
          (lines 4054, 4163-4166, 4285-4349, 4372-4382, 4505, 4675, 5187-5212, 5353, 5442-5445, 5571, 5838,
          5924-5932, 6822-6827, 8736), only through strict inequalities with positive margins.
  rot     the floor bin on Sang's rotated line with vartheta = 0. His Proposition prop:numerator (a class of nonunit
          physical rows, #B << U^{R+eps}) with R = 1 and no prime gain gives U^{(3R+1)/4} = U. He keeps "the original
          pointwise contour" there.
  edge    the principal row's region. Sang's Lemma principal-remainder assumes beta_* > B(ell) > 87/100, imposed here
          on the boundary itself. The release's local exponents (lines 4150-4176; the closest good-prime terms
          Q^{1-x_r-w_r-6z_r} and Q^{4-6x_r-6z_r}) converge for p not dividing u while sigma > 401/600 at z_r = 33/200,
          w_r = 19/20 (gate A1).
  tech    Sang's 6 kappa ell > 3/4 is dropped: its one use is the slope bound "above by 2" (line 1314), which holds
          from ell >= 1/6 and kappa >= 13/18 (gate A1). His ell/(h+zeta) > 21/100 serves the uniform short gate (line
          1233), which exact mode checks directly; it is weakened to the supply his Proposition prop:row-count assumes,
          "\\mathscr L=\\ell/d>1/5" (line 807).
  margin  his low-rows condition h(z_0 - 1/6) - l_y/2 + 2 d_min < -1/20 "gives a saving of 1/20"; only a fixed
          positive saving is used, and d_min enters his choices only as a fixed positive scale (the slot mesh and
          tau <= d_min/100), so its limit h(z_0 - 1/6) - l_y/2 < 0 is taken.
Hypothetical inputs:
  k       a 2k-th moment over the bin (round 497; 10**9 stands for Lindelof on average).
  gram    the Gram bound's exceptional term removed (t_min = -b/12 above), with round 497's absorption 3b <= 1 - 3 ell.
  amp     amplification vartheta = min(lam x delta/(6 kappa), delta/2, 1/10) on delta >= 1/8, the caps from Sang's
          raised lines "0\\le\\vartheta\\le\\min\\{a-1/2,1/10\\}"; for lam > 1 no short gate is imposed.
  dh      density-hypothesis counts R = 1 - delta above the floor (the floor bin keeps R = 1).
Every boundary here is a statement about this exponent system, not a theorem. Values are optima over the script's
grids (ell on 69 points refined locally, the bins on 1501 x 201 points for delta >= 1/8 and 400 x 201 below).

Gates (exit status 1 if any fails):
  L1  each configuration's boundary within 2e-6 of its recorded value, with its recorded walls, kappa within 1e-6, the
      stage that attains it, the number of stages, and the bootstrap's status
  C1  correction: the legacy path reproduces round 497's R5 values 0.8673682 and 0.8639728 within 2e-6, and each
      corrected value exceeds it by more than 1e-4
  S1  sabotage: the rotated floor with the release's term ell delta added back reproduces the unrotated floor's
      boundary within 2e-6, and differs from the rotated floor's by more than 1e-5
  O1  obstruction: at delta = 0 every count is R = 1 and vartheta = 0, so every bin's endpoint coefficients are C0's,
      C0 = -1/4 + b/6 + 5 ell/4 (every configuration at kappa = 13/18 and 3/4, 1e-15), and C0 is Sang's eq.
      full-exponent at a = 1/2, d = h, q = vartheta = 0, R = 1; the floor bin's endpoint at x = 0 is C0 + delta_f/2
      rotated and C0 + delta_f (1/2 + ell) on the release's contour (2000 random points each, 1e-12). So E_max > C0,
      and every boundary exceeds the infimum over b >= 0 of B(ell) + max(t_min(b), C0): 13/15 with the Gram term,
      31/36 without it (with the absorption). Both infima by linear programming within 1e-9 of the fractions, and
      every configuration's boundary above its limit
  A1  two readings' arithmetic in exact fractions: at w = 19/20, z = 33/200 the good-prime exponents 1 - x - w - 6z and
      4 - 6x - 6z are Sang's -181/100 and -221/100 at x = 87/100, and both are < -1 for x > 401/600; without
      6 kappa ell > 3/4, his two slopes stay below 2 (kappa >= 13/18, ell >= 1/6, q <= 5/12, l_y < 1/2)
  W1  at Sang's optimum the high side's endpoint on delta >= 1/8 peaks at x = 1/2 and 0.46 < delta < 0.48
"""
import sys
from fractions import Fraction as Fr
import numpy as np
from concurrent.futures import ProcessPoolExecutor
from scipy.optimize import minimize_scalar, linprog
import rotated_contour as RC
from rotated_contour import Rk, geometry, System

DL, XL, XS = RC.DL, RC.XL, RC.XS
EDGE_SANG, EDGE_READ = 87 / 100, 401 / 600
LINDELOF = 10 ** 9
STAGES = 40


class Lever(System):
    def __init__(self, kappa, k=2, gram='paper', floor=1 / 50, rot=False, edge=EDGE_SANG, tech=False, margin=False,
                 lam=1.0, counts='sang', legacy=False, rot_extra=0.0):
        self.kappa, self.k, self.mode, self.gram = kappa, k, 'exact', gram
        self.floor, self.rot, self.edge, self.tech, self.margin = floor, rot, edge, tech, margin
        self.lam, self.counts, self.legacy, self.rot_extra = lam, counts, legacy, rot_extra
        self.tau = 1 / (6 * kappa)
        R = self.count(DL, XL)
        self.gate_need = (R / (6 * kappa - 2 * XL * DL)).max() if lam == 1 else -1.0
        self.e0, self.eb, self.el = (c.ravel() for c in self.coeffs(DL, XL))
        self.DS = np.linspace(floor, 1 / 8, 401)[:-1, None]
        self.Rs = self.count(self.DS, XS)

    def count(self, d, x):
        return (1 - d + 0 * x) if self.counts == 'dh' else Rk(d, x, self.kappa)

    def coeffs(self, d, x):
        """the endpoint E = e0 + eb b + el ell of the bins delta >= 1/8, relative to B(ell)."""
        w, R = 1 - 1 / (2 * self.k), self.count(d, x)
        th = np.minimum(np.minimum(self.lam * self.tau * x * d, d / 2), 1 / 10)
        return (-1 / 4 + d / 2 - th / 4 - w * (1 - R) / 2 + 0 * x, 1 / 6 - th / 4 - w * (1 - R) / 2 + 0 * x,
                5 / 4 + x * d + 5 * th / 4 - 3 * w * (1 - R) / 2 + 0 * x)

    def hard_rows(self):
        """Sang's linear admissibility conditions that are not boundary-relative, as (name, ab, al, rhs)."""
        drop = {'B>87/100', 'C0<-1/250'}
        if self.tech:
            drop |= {'6k.ell>3/4', 'ell/h>21/100'}
        if self.margin:
            drop |= {'low rows'}
        rows = [r for r in System.side(self) if r[0] not in drop]
        if self.tech:
            rows.append(('ell/h>1/5', 1, -7, -1 - 1e-9))                  # prop:row-count's supply: 7 ell - b > 1
        if self.margin:
            s = RC.Z0 - 1 / 6
            rows.append(('low rows', s / 2 - 1 / 4, 3 * s / 2 + 1 / 4, -s / 2 + 1 / 4 - 1e-9))   # h s - l_y/2 < 0
        return rows

    def floor_endpoint(self, b, ell, x):
        """the floor bin (R = 1) relative to B(ell): on Sang's rotated line with vartheta = 0, or the release's."""
        lx, ly, h = geometry(b, ell)
        d, C0 = self.floor, -1 / 4 + b / 6 + 5 * ell / 4
        if self.rot:
            return C0 + d / 2 + x * d * ell + self.rot_extra * d * ell
        return (1 + d) / 2 * (1 - ly) - (11 / 12 - ell / 4) - ell / 2 + x * d * ell + h * (1 + d / 2 - 1 / 6)

    def parts(self, b, ell):
        lx, ly, h = geometry(b, ell)
        C0 = -1 / 4 + b / 6 + 5 * ell / 4
        w = 1 - 1 / (2 * self.k)
        ts = min(ell / h, 1 / (6 * self.kappa))
        Es = (C0 + self.DS / 2 + XS * self.DS * (ell + 2 * ts * (h / 4 - ly / 2)) - h * w * (1 - self.Rs)).max()
        Ef = self.floor_endpoint(b, ell, np.array([0.0, 0.5])).max()
        return [(Es, 'small delta'), (Ef, 'floor bin')]

    def endpoints(self, b, ell):
        """the high side's endpoints relative to B(ell): the bins delta >= 1/8, the small bins, the floor bin."""
        out = [((self.e0 + self.eb * b + self.el * ell).max(), 'E')] + self.parts(b, ell)
        if self.legacy:
            out.append((-1 / 4 + b / 6 + 5 * ell / 4 + 1 / 250, 'C0<-1/250'))
        return out

    def b_range(self, ell):
        lo, hi = 0.0, np.inf
        for n, ab, al, rhs in self.hard_rows():
            r = rhs - al * ell
            if abs(ab) < 1e-15:
                if r < 0:
                    return None
            elif ab > 0:
                hi = min(hi, r / ab)
            else:
                lo = max(lo, r / ab)
        if self.lam == 1:                                   # short gate: ell/h >= min(gate_need, 1/(6 kappa))
            g = min(self.gate_need, 1 / (6 * self.kappa))
            hi = min(hi, 2 * ell / g - 1 - 3 * ell - 1e-9)
        return (lo, hi) if lo <= hi else None

    def tmin(self, b):
        return -b / 12 if self.gram == 'none' else 0.0

    def t_of(self, ell):
        rng = self.b_range(ell)
        if rng is None:
            return None
        lo, hi = rng
        emax = lambda b: max(v for v, _ in self.endpoints(b, ell))
        if self.legacy:                      # round 497's R5: every endpoint <= 0, then the largest such b
            r = minimize_scalar(emax, bounds=(lo, hi), method='bounded', options={'xatol': 1e-12})
            if r.fun > -1e-9:
                return None
            if emax(hi) <= -1e-9:
                return -hi / 12, hi
            a, c = r.x, hi
            for _ in range(60):
                m = (a + c) / 2
                a, c = (m, c) if emax(m) <= -1e-9 else (a, m)
            return -a / 12, a
        f = lambda b: max(self.tmin(b), emax(b))
        r = minimize_scalar(f, bounds=(lo, hi), method='bounded', options={'xatol': 1e-12})
        return min((f(r.x), r.x), (f(lo), lo), (f(hi), hi))

    def bound(self, ell):
        tb = self.t_of(ell)
        if tb is None:
            return None
        t, b = tb
        Bl = 11 / 12 - ell / 4
        if self.legacy:                      # round 497 applied 87/100 to B(ell)
            return (Bl + t, b) if Bl >= self.edge else None
        return max(self.edge, Bl + t), b

    def best(self):
        start = (1 / 6 if self.tech else max(1 / 6, 1 / (8 * self.kappa))) + 1e-7
        ells = np.unique(np.concatenate([[start], np.linspace(1 / 6, 1 / 5, 69)]))
        ells = ells[ells >= start]
        vals = [(r[0], e) for e in ells for r in [self.bound(e)] if r is not None]
        if not vals:
            return None
        B0, e0 = min(vals)
        g = lambda e: (self.bound(e) or (1.0, None))[0]
        r = minimize_scalar(g, bounds=(max(start, e0 - 1.1e-3), min(1 / 5, e0 + 1.1e-3)), method='bounded',
                            options={'xatol': 1e-11})
        e = r.x if r.fun < B0 else e0
        B, b = self.bound(e)
        return B, e, b

    def walls(self, ell, b, B, tol=1e-6):
        """the conditions within tol of binding at the optimum."""
        out = set()
        if abs(B - self.edge) < tol:
            out.add('principal edge')
        t = B - (11 / 12 - ell / 4)
        out |= {n for v, n in self.endpoints(b, ell) if v > t - tol}
        if self.tmin(b) > t - tol:
            out.add('low side' if self.gram == 'paper' else 'Gram saving')
        out |= {n for n, ab, al, rhs in self.hard_rows() if ab * b + al * ell > rhs - tol}
        if self.lam == 1:
            g = min(self.gate_need, 1 / (6 * self.kappa))
            if b > 2 * ell / g - 1 - 3 * ell - tol:
                out.add('short gate')
        return tuple(sorted(out))


def fixed_point(cfg, stages=STAGES):
    kappa, out = 3 / 4, []
    for _ in range(stages):
        if kappa < 13 / 18:
            break
        r = Lever(kappa, **cfg).best()
        if r is None:
            break
        out.append((kappa, r))
        if abs(2 * r[0] - 1 - kappa) < 1e-10:
            break
        kappa = 2 * r[0] - 1
    return out


def run(cfg):
    """the bootstrap's boundary: the least stage's (the last within 1e-7 of it; round 497's legacy path: the last
    stage), with its walls."""
    fp = fixed_point(cfg)
    if not fp:
        return None
    least = min(r[0] for _, r in fp)
    i = len(fp) - 1 if cfg.get('legacy') else max(j for j in range(len(fp)) if fp[j][1][0] <= least + 1e-7)
    kap, (B, ell, b) = fp[i]
    gap = abs(2 * fp[-1][1][0] - 1 - fp[-1][0])
    status = 'fixed point' if gap < 1e-9 else ('stopped' if len(fp) < STAGES else 'stage cap')
    return B, kap, ell, b, len(fp), gap, status, Lever(kap, **cfg).walls(ell, b, B), i


READ = dict(floor=1 / 1000, rot=True, edge=EDGE_READ, tech=True, margin=True)
FP = 'fixed point'
CONFIGS = [   # (name, configuration, recorded (B, kappa, attaining stage, stages, status, walls))
    ("Sang's inputs", dict(k=2),
     (0.8748866, 0.7497733, 3, 4, FP, ('E', 'low side'))),
    ("Sang's inputs + all readings", dict(k=2, **READ),
     (0.8748866, 0.7497733, 3, 4, FP, ('E', 'low side'))),
    ("Sang's inputs + Gram removed", dict(k=2, gram='none'),
     (0.8745078, 0.7500000, 0, 17, FP, ('6k.ell>3/4', 'E', 'ell>=1/6'))),
    ("Sang's inputs + Gram removed + all readings", dict(k=2, gram='none', **READ),
     (0.8745012, 0.7490024, 4, 5, FP, ('E', 'ell>=1/6'))),
    ("Sang's inputs + amplifier x2", dict(k=2, lam=2.0),
     (0.8741924, 0.7483849, 3, 4, FP, ('E', 'low side'))),
    ("Sang's inputs + amplifier to the caps", dict(k=2, lam=100.0),
     (0.8741773, 0.7483545, 3, 4, FP, ('E', 'ell/h>21/100', 'low side'))),
    ("Sang's inputs + DH counts", dict(k=2, counts='dh'),
     (0.8701164, 0.7402328, 1, 2, FP, ('floor bin', 'low rows', 'low side'))),
    ("Sang's inputs + DH counts + all readings", dict(k=2, counts='dh', **READ),
     (0.8667866, 0.7335732, 1, 2, FP, ('b>0', 'floor bin', 'low side'))),
    ("Lindelof on average", dict(k=LINDELOF),
     (0.8701164, 0.7402328, 1, 2, FP, ('floor bin', 'low rows', 'low side'))),
    ("Lindelof + rotated floor", dict(k=LINDELOF, rot=True),
     (0.8700000, 0.7400000, 1, 2, FP, ('low rows', 'principal edge'))),
    ("Lindelof + floor 1/1000", dict(k=LINDELOF, floor=1 / 1000),
     (0.8700000, 0.7400000, 1, 2, FP, ('low rows', 'principal edge'))),
    ("Lindelof + Gram removed", dict(k=LINDELOF, gram='none'),
     (0.8700000, 0.7400000, 1, 2, FP, ('6k.ell>3/4', 'principal edge'))),
    ("Lindelof + all readings", dict(k=LINDELOF, **READ),
     (0.8667866, 0.7335732, 1, 2, FP, ('b>0', 'floor bin', 'low side'))),
    ("Lindelof + all readings + Gram removed", dict(k=LINDELOF, gram='none', **READ),
     (0.8618569, 0.7500000, 0, 9, FP, ('Gram saving', 'floor bin', 'short gate'))),
    ("everything", dict(k=LINDELOF, gram='none', lam=100.0, counts='dh', **READ),
     (0.8613056, 0.7226111, 1, 2, FP, ('Gram saving', 'ell>=1/6', 'floor bin'))),
]
LEGACY = [("round 497 R5, Sang's inputs, legacy path", dict(k=2, gram='none', legacy=True), 0.8673682),
          ("round 497 R5, Lindelof, legacy path", dict(k=LINDELOF, gram='none', legacy=True), 0.8639728)]
CORRECTED = ["Sang's inputs + Gram removed", "Lindelof + Gram removed"]
SABOTAGE = ("Lindelof + rotated floor, release term added back", dict(k=LINDELOF, rot=True, rot_extra=1.0))


def fmt(r):
    if r is None:
        return 'infeasible'
    return (f'B = {r[0]:.7f}  kappa {r[1]:.7f}  ell {r[2]:.5f}  b {r[3]:.5f}  stage {r[8]} of {r[4]}, {r[6]} '
            f'(|2B - 1 - kappa| = {r[5]:.0e})  walls: {", ".join(r[7])}')


def full_exponent(b, ell, a, d, theta, q, R):
    """Sang's eq. full-exponent: a - B(ell) - l_y(1/2 + vartheta) + h(z_0 - 1/6) - ell/2 + ell q
    + d(K + vartheta/2 - z_0), K = (3R + 1)/4."""
    lx, ly, h = geometry(b, ell)
    K = (3 * R + 1) / 4
    return (a - (11 / 12 - ell / 4) - ly * (1 / 2 + theta) + h * (RC.Z0 - 1 / 6) - ell / 2 + ell * q
            + d * (K + theta / 2 - RC.Z0))


def obstruction(gram):
    """inf over b >= 0 (and the absorption 3b + 3 ell <= 1 without the Gram term) of B(ell) + max(t_min(b), C0)."""
    Bl, C0 = (11 / 12, 0.0, -1 / 4), (-1 / 4, 1 / 6, 5 / 4)          # (constant, b, ell)
    tb = -1 / 12 if gram == 'none' else 0.0
    rows = [(Bl[0], tb, Bl[2]), (Bl[0] + C0[0], C0[1], Bl[2] + C0[2])]   # t >= c + cb b + cl ell
    A = [[cb, cl, -1.0] for c, cb, cl in rows]
    rhs = [-c for c, cb, cl in rows]
    if gram == 'none':
        A.append([3.0, 3.0, 0.0])
        rhs.append(1.0)
    res = linprog([0, 0, 1], A_ub=A, b_ub=rhs, bounds=[(0, None), (None, None), (None, None)], method='highs')
    return res.fun, res.x


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    jobs = [c for _, c, _ in CONFIGS] + [c for _, c, _ in LEGACY] + [SABOTAGE[1]]
    with ProcessPoolExecutor(max_workers=4) as ex:
        res = list(ex.map(run, jobs))
    n = len(CONFIGS)
    got = {nm: r for (nm, _, _), r in zip(CONFIGS, res[:n])}

    for (nm, cfg, rec), r in zip(CONFIGS, res[:n]):
        ok = r is not None and rec is not None
        if ok:
            B, kap, i, stages, status, walls = rec
            ok = (abs(r[0] - B) < 2e-6 and abs(r[1] - kap) < 1e-6 and r[8] == i and r[4] == stages and r[6] == status
                  and r[7] == walls)
        gate('L1', ok, f'{nm:44s} {fmt(r)}' + ('' if rec is None else f'  (recorded {rec[0]:.7f})'))

    for (nm, cfg, want), r, corr in zip(LEGACY, res[n:n + 2], CORRECTED):
        c = got[corr]
        ok = r is not None and abs(r[0] - want) < 2e-6 and c is not None and c[0] - want > 1e-4
        gate('C1', ok, f'{nm}: {fmt(r)} (round 497: {want:.7f}); corrected ("{corr}"): '
                       + ('infeasible' if c is None else f'{c[0]:.7f}'))

    rs, plain, rot = res[-1], got['Lindelof on average'], got['Lindelof + rotated floor']
    ok = rs is not None and abs(rs[0] - plain[0]) < 2e-6 and abs(rs[0] - rot[0]) > 1e-5
    gate('S1', ok, f'sabotage, the release term ell delta added back to the rotated floor: {fmt(rs)}; '
                   f'unrotated floor {plain[0]:.7f}, rotated floor {rot[0]:.7f}')

    dev = 0.0
    for nm, cfg, _ in CONFIGS:
        for kap in (13 / 18, 3 / 4):
            e0, eb, el = Lever(kap, **cfg).coeffs(0 * XL, XL)
            dev = max(dev, abs(e0 + 1 / 4).max(), abs(eb - 1 / 6).max(), abs(el - 5 / 4).max())
    rng = np.random.default_rng(498)
    fdev = 0.0
    for b, ell, d in zip(rng.uniform(0, 0.2, 2000), rng.uniform(1 / 6, 1 / 5, 2000), rng.uniform(1e-4, 1 / 50, 2000)):
        C0 = -1 / 4 + b / 6 + 5 * ell / 4
        fdev = max(fdev, abs(full_exponent(b, ell, 1 / 2, geometry(b, ell)[2], 0.0, 0.0, 1.0) - C0),
                   abs(Lever(3 / 4, floor=d, rot=True).floor_endpoint(b, ell, 0.0) - (C0 + d / 2)),
                   abs(Lever(3 / 4, floor=d).floor_endpoint(b, ell, 0.0) - (C0 + d * (1 / 2 + ell))))
    lim = {g: obstruction(g) for g in ('paper', 'none')}
    gaps = [r[0] - lim[cfg.get('gram', 'paper')][0] if r else -1.0 for (nm, cfg, _), r in zip(CONFIGS, res[:n])]
    gate('O1', dev < 1e-15 and fdev < 1e-12 and abs(lim['paper'][0] - 13 / 15) < 1e-9
         and abs(lim['none'][0] - 31 / 36) < 1e-9 and min(gaps) > 0,
         f"delta = 0 coefficients = C0's (max deviation {dev:.0e}); full-exponent at delta = 0, d = h and floor bin at "
         f'x = 0 (max deviation {fdev:.0e}); '
         f'limits {lim["paper"][0]:.10f} (13/15, at b, ell = {lim["paper"][1][0]:.4f}, {lim["paper"][1][1]:.4f}) and '
         f'{lim["none"][0]:.10f} (31/36, at {lim["none"][1][0]:.4f}, {lim["none"][1][1]:.4f}); every configuration '
         f'above its limit (least margin {min(gaps):.2e})')

    x, w, z = Fr(87, 100), Fr(19, 20), Fr(33, 200)
    t1, t2 = 1 - x - w - 6 * z, 4 - 6 * x - 6 * z
    xe = (5 - 6 * z) / 6
    k_lo, l_lo, q, ly, z0 = Fr(13, 18), Fr(1, 6), Fr(5, 12), Fr(1, 2), Fr(17, 50)
    slope1 = 1 - z0 + q / (12 * k_lo)                               # K - z0 + q/(12 kappa), K <= 1
    slope2 = 1 - z0 + q * Fr(1, 5) * ly / (6 * k_lo * l_lo) ** 2    # K - z0 + q ell l_y/d^2, d >= 6 kappa ell
    gate('A1', t1 == Fr(-181, 100) and t2 == Fr(-221, 100) and xe == Fr(401, 600)
         and 1 - xe - w - 6 * z < -1 and 4 - 6 * xe - 6 * z == -1 and slope1 < 2 and slope2 < 2,
         f'at x = 87/100: {t1}, {t2}; 4 - 6x - 6z = -1 at x = {xe}, where 1 - x - w - 6z = {1 - xe - w - 6 * z}; '
         f'slopes without 6 kappa ell > 3/4: {slope1} = {float(slope1):.4f}, {slope2} = {float(slope2):.4f}')

    s = got["Sang's inputs"]
    lv = Lever(s[1], k=2)
    E = (lv.e0 + lv.eb * s[3] + lv.el * s[2]).reshape(DL.shape[0], XL.shape[1])
    i, j = np.unravel_index(np.argmax(E), E.shape)
    gate('W1', 0.46 < DL[i, 0] < 0.48 and XL[0, j] == 0.5,
         f"Sang's optimum: E peaks at delta = {DL[i, 0]:.4f}, x = {XL[0, j]} (a = {(1 + DL[i, 0]) / 2:.4f}), "
         f'value {E.max():.1e}')

    print(f'{fails} gate(s) failed' if fails else 'all gates pass')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
