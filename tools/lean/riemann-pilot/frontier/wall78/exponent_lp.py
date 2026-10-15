"""The release's 7/8 exponent comparison as a linear program (README round 496).

Source: The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex in github.com/openai/math
(family 003; the tree read here is commit adc7f1241, unchanged at 1581d4cbd). Line numbers below are
that file's.

Variables: the geometry (l_x, l_y, ell) of Definition stage-high-data (line 5583) and the boundary s0.
Every constraint is linear in them for fixed (delta, x), so the best boundary is a linear program.

High side. Lemma bin-contour-accounting (line 6022), eq. stage-high-exponent (line 6092):
    E = a - s0 + h(z0 - 1/6) - a l_y - ell/2 + g + d(R + delta/2 - z0),   h = 1 - l_x + ell,
taken at the longest rows d = h (where z0 cancels), with g = q ell = x delta ell (lines 15811, 15824),
a = (1 + delta)/2, and E <= 0 required for every bin delta in (1/50, kappa], x in [0, 1/2].
Row counts R: Proposition detector-counts (line 15185), max{R_short(t), L(t)} balanced over t:
    R* = 1 - delta + (alpha - delta) delta P_x / (2 J),   J = (alpha - delta) D_x + delta P_x,
    P_x = (1 - 2 x cM)(2 - 4 x cP),   D_x = 3 - 2 x cM - 4 x cP,
with alpha = 5/6, cM = 1/2 (z_M(r) = (1 - r)/2) and cP = 1/(6 kappa) (z_P(m) = (1 - 2m)/(6 kappa),
eq. plain-zero-loss-capacity, line 15177), which at kappa = 3/4 gives the paper's D_x = 3 - 17x/9, P_x = (2 - 8x/9)(1 - x).
The floor bin a = 51/100 has the trivial count R = 1 (line 4381: "The bin a=51/100 will be bounded by
the trivial row count.").
Not modelled (the endpoint model): the intermediate range, small and large rows, the frequency
extension, and the prime supply against the capacities; so every boundary computed here is a lower
bound for what the release's machinery gives with the stated inputs, not a theorem.

Low side. Proposition probe-low (line 8564): |I| << Z^{l_x/2 + b/12}, b = l_y - l_x, from the Gram
bound (Q/Y')(1 + P_a^{1/6} + P_a^2/Y') (Proposition probe-gram, line 8340) and the row norm.
Against C(s0) = s0 - 5/6 + l_x/3 + ell/6 this is s0 >= 5/6 + l_x/6 - ell/6 + (Gram exponent)/2 + (row loss)/2.
Row loss: the second branch of Lemma probe-row-norm's proof (line 8306), M' + (1 + 3 ell' - 2M')/4,
with M' = M - 2d, ell' = ell - d, i.e. (1 + 3 ell - 2M + d)_+/4, worst at d = 0 after the -d of
eq. old-eq:5.5 (line 8632). On the slice M + ell = 1 this is (5 ell + d - 1)_+/4, the L_ell(d) of Sang
(arXiv 2610.15291, Proposition prop:low, 1/6 <= ell <= 1/5). Off the slice it is a reading of the same
proof, which uses M' + ell' - 1 = -3d (line 8246) only through T_d <= H - 3d (so it holds for M + ell <= 1);
the other lemmas of the low estimate were not re-read for general geometry.

Gates (each can fail; exit status 1 if any does):
  W1  slice optimum at kappa = 3/4 equals Liu v1, (1507 - 2 sqrt 921)/1653, within 1e-9
  W2  slice optimum with kappa = 2 s0 - 1 iterated equals Liu v2's B_new (cubic 1188x^3 - 2160x^2 + 171x
      + 190, root in (0.38858, 0.38859)) within 1e-9, and ell agrees with Liu's ell_new within 1e-6
  W3  the release's own geometry (b, ell) = (1/8, 1/6) is feasible at s0 = 7/8 with slack in
      [49/440640, 3e-4] (Lemma balanced-endpoint, line 15994, proves -E* >= 49/440640)
  W4  off the slice (M + ell <= 1 only) the optimum is on the slice, and the slice's shadow price is 1/16;
      crossing the slice by mu at a low-side cost c mu/2 (c = 1 is the first branch of the row-norm
      proof as read) pays only for c below a break-even in (0.15, 0.16); the low side carries a
      shadow price in (0.79, 0.83) of the boundary, the high bins the rest
  W5  levers: each recorded boundary within 5e-5
  W6  caps: DH counts with a row saving give 13/15; without the Gram exceptional term, with DH counts
      and row saving U^{1/2}, 38/45; both within 1e-6. W6b: these are the low side's own minima over
      the geometry (the low rows alone, no high side), 13/15 and 38/45
  W7  de Faveri's Corollary 1.5 at n = 6 is weaker than R* at the binding bin
  S1  sabotage: with cP = 1/4 in place of 1/(6 kappa) the optimum moves off Liu v1 by more than 1e-6
"""
import sys
import numpy as np
from scipy.optimize import linprog

ALPHA, CM = 5 / 6, 0.5
FLOOR = 1 / 50


def r_star(d, x, cP, alpha=ALPHA, cM=CM):
    P = (1 - 2 * x * cM) * (2 - 4 * x * cP)
    D = 3 - 2 * x * cM - 4 * x * cP
    am = np.maximum(alpha - d, 0.0)
    with np.errstate(invalid='ignore', divide='ignore'):
        extra = np.where(am > 0, am * d * P / (2 * (am * D + d * P)), 0.0)
    return 1 - d + extra


class Model:
    """Inputs of one scenario. counts: 'paper' or 'dh'; eta: uniform row saving U^eta (R <= 1 - eta);
    theta: Gram exceptional exponent (paper 1/6); cg: multiplier of the amplitude cost g."""

    def __init__(self, counts='paper', alpha=ALPHA, cM=CM, cP=None, dR=0.0, eta=0.0, theta=1 / 6,
                 cg=1.0, slice_eq=True, kappa=0.75):
        self.counts, self.alpha, self.cM, self.cP_fixed = counts, alpha, cM, cP
        self.dR, self.eta, self.theta, self.cg, self.slice_eq, self.kappa = dR, eta, theta, cg, slice_eq, kappa

    def cP(self):
        return self.cP_fixed if self.cP_fixed is not None else 1 / (6 * self.kappa)

    def R(self, d, x):
        d, x = np.asarray(d, float), np.asarray(x, float)
        if self.counts == 'dh':
            r = 1 - d + 0 * x
        else:
            r = np.maximum(r_star(d, x, self.cP(), self.alpha, self.cM) - self.dR, 1 - d)
        r = np.where(d == FLOOR, 1.0, r)          # the floor bin, exactly a = 51/100
        return np.minimum(r, 1 - self.eta)

    def E(self, v, d, x):
        lx, ly, ell, s0 = v[:4]
        r = self.R(d, x); a = (1 + d) / 2
        return a * (1 - ly) - s0 - ell / 2 + self.cg * x * d * ell + (1 - lx + ell) * (r + d / 2 - 1 / 6)

    def high_rows(self, d, x):
        """E(delta, x) <= 0 as rows over v = (l_x, l_y, ell, s0, mu)."""
        r = self.R(d, x); a = (1 + d) / 2; K = r + d / 2 - 1 / 6
        z = np.zeros_like(K)
        A = np.column_stack([-K, -a, -0.5 + self.cg * x * d + K, -np.ones_like(K), z])
        return A, -(a + K)

    def low_rows(self, mu_cost):
        rows, rhs = [], []
        G = [np.zeros(5), np.array([-self.theta / 2, self.theta / 2, 0, 0, 0]), np.array([-1.0, 0.5, 0, 0, 0])]
        Rl = [(np.zeros(5), 0.0), (np.array([-2 / 8, -2 / 8, 3 / 8, 0, 0]), 1 / 8)]
        for g in G:
            for rl, rc in Rl:
                rows.append(np.array([1 / 6, 0, -1 / 6, -1, mu_cost / 2]) + g + rl); rhs.append(-5 / 6 - rc)
        # b >= 0, l_x > ell, supply ell/h > 7/37, M + ell <= 1 + mu
        rows += [[1, -1, 0, 0, 0], [-1, 0, 1, 0, 0], [-7, 0, -30, 0, 0], [1, 1, 1, 0, -1]]
        rhs += [0, -1e-3, -7 - 1e-6, 1]
        if self.slice_eq:
            rows.append([-1, -1, -1, 0, 0]); rhs.append(-1)
        return np.array(rows, float), np.array(rhs, float)

    def emax(self, v, nd=2001, nx=51, top=8):
        """max of E over the bins: the floor bin exactly, then a grid above it, refined at its top points
        by coordinate ascent with bounded scalar maximisation (E is smooth above the floor)."""
        from scipy.optimize import minimize_scalar
        xs = np.linspace(0, 0.5, nx)
        best = [(float(self.E(v, FLOOR, xx)), FLOOR, float(xx)) for xx in (0.0, 0.5)]   # linear in x
        d = np.linspace(FLOOR, self.kappa, nd)[1:, None]
        G = self.E(v, d, xs[None, :])
        lo = FLOOR + 1e-13
        for f in np.argsort(G.ravel())[-top:]:
            i, j = np.unravel_index(f, G.shape)
            dd, xx = float(d[i, 0]), float(xs[j])
            for _ in range(4):
                dd = minimize_scalar(lambda t: -float(self.E(v, t, xx)), bounds=(max(lo, dd - 2e-3), min(self.kappa, dd + 2e-3)),
                                     method='bounded', options={'xatol': 1e-13}).x
                xx = minimize_scalar(lambda t: -float(self.E(v, dd, t)), bounds=(0.0, 0.5),
                                     method='bounded', options={'xatol': 1e-13}).x
                xx = 0.5 if self.E(v, dd, 0.5) >= self.E(v, dd, xx) else (0.0 if self.E(v, dd, 0.0) >= self.E(v, dd, xx) else xx)
            best.append((float(self.E(v, dd, xx)), dd, xx))
        best.sort(reverse=True)
        return best


HIGHS = {'primal_feasibility_tolerance': 1e-10, 'dual_feasibility_tolerance': 1e-10}


def solve(m, mu_cost=None, tol=5e-11):
    """Cutting planes: a coarse grid of bins, then the refined worst bins of each solution as new cuts."""
    d0, x0 = np.meshgrid(np.linspace(FLOOR, m.kappa, 120), np.linspace(0, 0.5, 11), indexing='ij')
    pts_d, pts_x = list(d0.ravel()), list(x0.ravel())
    mu_free = mu_cost is not None
    Lr, Lb = m.low_rows(mu_cost if mu_free else 0.0)
    bounds = [(0, 1), (0, 1), (0, 1), (0.5, 1), (0, 0.5 if mu_free else 0)]
    for it in range(300):
        A, B = m.high_rows(np.array(pts_d), np.array(pts_x))
        res = linprog(c=[0, 0, 0, 1, 0], A_ub=np.vstack([A, Lr]), b_ub=np.concatenate([B, Lb]),
                      bounds=bounds, method='highs', options=HIGHS)
        if res.status != 0:
            raise RuntimeError(res.message)
        worst = m.emax(res.x)
        if worst[0][0] <= tol:
            return res, it
        for e, dd, xx in worst:
            if e > tol:
                pts_d.append(dd); pts_x.append(xx)
    raise RuntimeError(f'no convergence: max E = {worst[0][0]:.2e}')


def slice_price(m):
    """Shadow price of M + ell <= 1 (d s0 / d mu) at the optimum, from the LP duals."""
    res, _ = solve(m)
    return res, res.ineqlin.marginals[-1 - (1 if m.slice_eq else 0)]


def liu_v2():
    from mpmath import mp, mpf, sqrt, cos, acos, pi
    mp.dps = 30
    xi = mpf(20) / 33 + sqrt(1391) / 33 * cos(acos(mpf(28470) / mpf(1391) ** 1.5) / 3 - 2 * pi / 3)
    return float((18 * xi + 7) / (18 * xi + 9)), float((5 - 6 * xi) / (9 + 18 * xi)), float(xi)


def de_faveri_delta(n, s):
    """de Faveri, arXiv 2610.04045, Corollary 1.5: delta_n(sigma)."""
    if s <= 0.5 + 1 / n:
        return (2 * s - 1) / ((1 - 2 * s) * n + 4)
    if s <= 1 - 1 / (2 * n):
        return (2 * s - 1) * ((2 * s - 1) * n ** 2 - (6 * s - 2) * n + 3) / ((2 * s - 1) * (3 - 2 * s) * n ** 2 - 4 * s * n + 2)
    return (8 * s ** 2 - 10 * s + 3) / (1 - 4 * (1 - s) ** 2 * n)


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    liu_v1 = (1507 - 2 * np.sqrt(921)) / 1653
    res, it = solve(Model(kappa=0.75))
    s0_v1 = res.x[3]
    gate('W1', abs(s0_v1 - liu_v1) < 1e-9, f'kappa = 3/4: s0 = {s0_v1:.12f}, Liu v1 = {liu_v1:.12f} ({it} cuts)')

    kappa = 0.75
    for _ in range(4):
        res, it = solve(Model(kappa=kappa)); kappa = 2 * res.x[3] - 1
    B2, ell2, xi2 = liu_v2()
    gate('W2', abs(res.x[3] - B2) < 1e-9 and abs(res.x[2] - ell2) < 1e-6,
         f'kappa iterated: s0 = {res.x[3]:.12f} (Liu v2 {B2:.12f}); ell = {res.x[2]:.8f} (Liu {ell2:.8f}); '
         f'Liu xi = {xi2:.6f} is the binding bin delta')

    m = Model(kappa=0.75)
    lx, ly, ell = (1 - 1 / 8 - 1 / 6) / 2, (1 + 1 / 8 - 1 / 6) / 2, 1 / 6
    slack = -m.emax(np.array([lx, ly, ell, 7 / 8]), nd=20001, nx=201)[0][0]
    gate('W3', 49 / 440640 <= slack <= 3e-4, f'release geometry at s0 = 7/8: slack {slack:.3e} (>= 49/440640 = {49/440640:.3e})')

    off = Model(kappa=0.75, slice_eq=False)
    res, price = slice_price(off)
    M_ell = res.x[0] + res.x[1] + res.x[2]
    gate('W4', abs(M_ell - 1) < 1e-6 and abs(res.x[3] - liu_v1) < 1e-9 and abs(abs(price) - 1 / 16) < 2e-3,
         f'off-slice optimum s0 = {res.x[3]:.10f} at M + ell = {M_ell:.8f}; slice shadow price {price:.5f}')
    n_low = len(off.low_rows(0.0)[0])
    duals = res.ineqlin.marginals
    low_price = -duals[len(duals) - n_low:][:6].sum()          # the six low-side pieces
    high_price = -duals[:len(duals) - n_low].sum()
    gate('W4d', 0.79 < low_price < 0.83 and abs(low_price + high_price - 1) < 1e-6,
         f'shadow prices on s0: low side {low_price:.4f}, high bins {high_price:.4f} (sum 1)')
    res_c, _ = solve(off, mu_cost=1.0)
    gate('W4b', abs(res_c.x[3] - liu_v1) < 1e-9 and res_c.x[4] < 1e-9,
         f'crossing the slice at row-norm cost mu (first branch): s0 = {res_c.x[3]:.10f}, mu = {res_c.x[4]:.2e}')
    lo_c, _ = solve(off, mu_cost=0.15)
    hi_c, _ = solve(off, mu_cost=0.16)
    gate('W4c', lo_c.x[4] > 1e-3 and lo_c.x[3] < liu_v1 - 1e-6 and hi_c.x[4] < 1e-9,
         f'break-even cost in (0.15, 0.16) per unit mu (bisection: 0.15391): cost 0.15 crosses '
         f'(mu = {lo_c.x[4]:.3f}, s0 = {lo_c.x[3]:.6f}); cost 0.16 does not (mu = {hi_c.x[4]:.1e})')

    levers = [
        ('DH counts', Model(counts='dh', slice_eq=False), 0.86979),
        ('uniform R - 0.03', Model(dR=0.03, slice_eq=False), 0.87091),
        ('alpha = 2/3', Model(alpha=2 / 3, slice_eq=False), 0.87392),
        ('no amplitude cost g', Model(cg=0.0, slice_eq=False), 0.87255),
        ('Gram exceptional P_a^(1/12)', Model(theta=1 / 12, slice_eq=False), 0.86961),
        ('Gram exceptional removed', Model(theta=0.0, slice_eq=False), 0.86395),
        ('row saving U^(1/4) alone', Model(eta=0.25, slice_eq=False), liu_v1),
        ('row saving U^(1/2) alone', Model(eta=0.5, slice_eq=False), 0.87082),
    ]
    for name, mm, want in levers:
        r, _ = solve(mm)
        gate('W5', abs(r.x[3] - want) < 5e-5, f'{name:30s} s0 = {r.x[3]:.5f} (recorded {want:.5f})')

    r, _ = solve(Model(counts='dh', eta=0.1, slice_eq=False))
    gate('W6', abs(r.x[3] - 13 / 15) < 1e-6, f'DH counts + row saving U^(1/10): s0 = {r.x[3]:.8f} (13/15 = {13/15:.8f})')
    r, _ = solve(Model(counts='dh', eta=0.5, theta=0.0, slice_eq=False))
    gate('W6', abs(r.x[3] - 38 / 45) < 1e-6, f'DH + row saving U^(1/2) + no Gram exceptional: s0 = {r.x[3]:.8f} (38/45 = {38/45:.8f})')
    for th, want, nm in [(1 / 6, 13 / 15, '13/15'), (0.0, 38 / 45, '38/45')]:
        Lr, Lb = Model(theta=th, slice_eq=False).low_rows(0.0)
        lo = linprog(c=[0, 0, 0, 1, 0], A_ub=Lr, b_ub=Lb, bounds=[(0, 1), (0, 1), (0, 1), (0.5, 1), (0, 0)],
                     method='highs', options=HIGHS)
        gate('W6b', abs(lo.x[3] - want) < 1e-9,
             f'low side alone, minimised over the geometry (Gram exponent {th:.4f}): {lo.x[3]:.10f} = {nm}, '
             f'at ell = {lo.x[2]:.4f}, M = {lo.x[0] + lo.x[1]:.4f}')

    delta = xi2; sig = (1 + delta) / 2
    r_df = 1 - de_faveri_delta(6, sig)
    r_paper = r_star(np.array([delta]), np.array([0.0, 0.5]), 2 / 9)
    gate('W7', r_df > r_paper.max() > r_paper.min() > 1 - delta,
         f'binding bin delta = {delta:.4f}: de Faveri n = 6 count {r_df:.4f} > R* in [{r_paper.min():.4f}, {r_paper.max():.4f}] > DH {1 - delta:.4f}')

    r, _ = solve(Model(cP=1 / 4, kappa=0.75))
    gate('S1', abs(r.x[3] - liu_v1) > 1e-6, f'sabotage cP = 1/4: s0 = {r.x[3]:.10f} differs from Liu v1 by {abs(r.x[3] - liu_v1):.2e}')

    print(f'{fails} gate(s) failed' if fails else 'all gates pass')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
