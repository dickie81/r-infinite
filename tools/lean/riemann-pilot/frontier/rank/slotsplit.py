"""The slot product split, the trilinear bound, the ladder of inputs, the vertex's bins and the crossing cost
(FIVE-SIXTHS.md, sections 7, 8 and 9).

The slot-split bound (section 7.3).  Lemma lem:hybrid-energy bounds the inner slot sums of its proof by Heath-Brown's
cubic large sieve over the columns j (norm ~ N) against the active slot products P (norm ~ L = Z^{z_a}),
N + L + (NL)^{2/3}, and treats the tuple coefficient a(P) as a general bounded function: the release's proof of Lemma
lem:reflected-energy says "The function \\(a\\) need not retain product form at this norm step."  Before that step the
coefficient is a product over the active slots of one-prime factors times the mark-mark phases, and for two active
marks (j_p = j_q = 0) the release's eq. reflection-pair-phase gives (q/p)_3^{j_p + j_q + 2} = (q/p)_3^2.  The
release's K is even and its slots have equal lengths l/K.  Split the active slots into two halves, P = AB, of norms
L_A, L_B.  For a fixed column j the inner sum is a bilinear form sum_{A,B} x_j(A) y_j(B) conj((B/A)_3), and the cubic
large sieve in (A, B) bounds its square by (L_A + L_B + (L_A L_B)^{2/3}) |x|^2 |y|^2, which is about L^{2/3} for
balanced halves.  Summed over the ~N columns this gives N L^{2/3}, so the factor becomes min{N + L + (NL)^{2/3},
N L^{2/3}}: in the release's notation u = min{v, z_a, (v + z_a)/3} becomes max{u, z_a/3} (up to O(l/K), which K
absorbs).

The trilinear bound (section 9).  In column j the half B carries its column factor chi_B(j)^{-2} = conj((j/B)_3) (the
release's line 1906: (x/p)_3 = chi_p(x)^2) and the cross pair phase conj((B/A)_3); by cubic reciprocity their product
is conj((B/jA)_3), and its modulus jA is squarefree, since the character vanishes unless (j, A) = 1.  Cauchy-Schwarz in
A, then Heath-Brown's sieve with the rows m = jA (multiplicity at most d(m)) against the columns B, bounds the sum over
the columns by N L_A + L_B + (NL)^{2/3}; halves with L_A about (L/N)^{1/2} give N + (NL)^{2/3} up to Z^{O(l/K)}.  That
is the L term dropped: sigma = 2/3 and the least low side 28/33 (S5's row (b)).

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
      -d + X(M - 2d, l - d)/2 is <= 0 for d in [0, l] (1e-9), so the low side is taken at d = 0.  At (M, l) =
      (3/4, 1/4) the low side is the same for every l_x in [1/4, 3/8]; Xu-Sang's l_y - l > 11b/6 holds there for
      l_x > 21/64 (checked here at l_x = 3/8).
  S3  the system with Sang's inputs and the readings (fivesixths.Five, bootstrapped from kappa = 3/4): (i) with
      Sang's rotation and no row saving the boundary is 0.8748866 (2e-6) at sigma = 1, 3/4, 2/3 and 1/2, with the bins
      'E' among the walls and no row loss; (ii) with a uniform row saving U^{1/10}, no rotation and the small rows'
      line 1/6 + 1/100, sigma = 3/4 gives 41/48, sigma = 2/3 gives 0.8537843 with the bins 'E' among the walls
      (the high side binds before 28/33), and sigma = 1 gives 13/15 (1e-6).
  S4  the vertex's bins: (i) in exact arithmetic, at (1/3, 1/3, 1/3) with density-hypothesis counts R = 1 - delta,
      Lindelof (w = 1) and no rotation, the bin endpoint at x = 1/2 is 1 - delta/3 - s0 for 24 rational delta in
      [1/8, 5/6], so s0 = 5/6 needs a saving at least 1/6 - delta/3 on every bin with delta < 1/2; the model's own
      coefficients (fivesixths.Five with those counts) give the same endpoint at every bin with delta >= 1/8 (1e-8);
      (ii) in the program (sigma = 1/2, small rows' line 1/6 + 1/100, no rotation), DH counts with Lindelof and a
      saving U^{3/10} on the floor bin and the small bins alone give 31/36 with 'E' among the walls, and with U^{1/5}
      on every bin give 5/6 (2e-7).
  S5  the dictionary between hybrid bounds and FIVE-SIXTHS.md's sigma (the parameter of the second branch
      (1 + (4 sigma - 1) l' - 2M')/4, which section 2 of that note misdescribed as the trivial dual's exponent).  The
      factor is replaced by (a) min(release, N L^{1/2}): every column's squared slot sum << L^{1/2}, that is slot
      sums << L^{3/4} before the 1/sqrt(q_P) normalization, not square-root cancellation; (b) N + (NL)^{2/3}: the L
      term dropped, the trilinear bound; (c) N + N^{3/4} L^{1/2}; (d) N + (NL)^{1/2}; (e) N alone: square-root
      cancellation in every column.  At S1's points the dyad program never exceeds the second branch with sigma =
      5/8, 2/3, 1/2, 1/2 and 1/2 (1e-9); it equals it at the low side's optimum; and the least low side, by
      fivesixths.low_min and by the exact program on S2's grid, is 71/84, 28/33, 5/6, 5/6 and 5/6.  The release's
      row is F2-F3 of fivesixths.py and the slot split's is S1-S2.
  S6  the crossing cost (FIVE-SIXTHS.md section 8).  Round 500's first branch charges c mu/2 on the low side with
      c = 1, the column term NB of the factor K + NB in Lemma lem:hybrid-energy.  Across the slice (mode 'cross', the
      program's cap on mu raised from 1/2 to 2, round 502's reading dropping l_y < 1/2, round 498's readings), with
      sigma = 2/3 and no row saving, the bootstrapped boundary is 5/6 at c = 0 (2e-7), and 0.8486654, 0.8615362,
      0.8725510, 0.8744704, 0.8748866 and the release's 0.8748866 at c = 0.05, 0.1, 0.15, 0.16, 0.165 and 1 (1e-6,
      2e-6 at c >= 0.165); sigma = 3/4 gives the same at c = 0 and 0.15.  On the ray l_x = l_y = l = t at
      kappa = 3/4 and c = 0: 0.8786610 at t = 1/2 and above 5/6 + 10^-3 at t = 0.55, both with the bins 'E' among the
      walls, and 5/6 at t = 0.56 (2e-7).  With sigma = 1, c = 0 reaches 5/6 at (1, 1, 1), the corner of the model's
      length box, with mu = 2, the cap; with the cap at 1.9 it gives 0.8350000.  Without round 498's readings, c = 0
      gives 0.8700000 with the principal edge among the walls.  Far across the slice the geometries are admissible
      only in the model (Xu-Sang's admissibility rows and the pilot's high side); the release's lemmas were not
      re-derived there.
  S7  the crossing cost's zero is target T3: with the quadratic sieve's factor K + NB replaced by K, round 500's dyad
      program has no first branch, and its maximum is M' + max(0, (1 + 3l' - 2M')/4) (1e-9) at 300 random (M', l')
      in [0.3, 2] x [0, 1], and at most M' + max(0, (1 + 2l' - 2M')/4) with the split; with the column term, on the
      ray (M', l') = (2t, t), the maximum's excess is the first branch 3t - 1 for t = 0.4, 0.5, 0.5572, 0.75 (1e-9).
      So S6's c = 0 is exactly the column term removed, with no further branch in the dyads.  With the column term,
      the program equals crossing.formula (1e-9) at 300 random (M', l') in that box with M' >= 2l', the region every
      low side uses (l_x >= l and b >= 0 give M' - 2l' = M - 2l >= 0 at every tuple size), and exceeds it by more than
      0.1 at (0.6181, 0.9935), so crossing.py's "In any geometry" holds where its gate X1 samples (l' <= 0.3), not
      at every l'.
  S8  the trilinear bound's ingredients, computed directly in Z[w] (cubic residue symbols by Euler's criterion,
      primary means = 1 mod 3): (i) at 2000 random triples of split primes of norm below 4000, cubic reciprocity
      holds, and the B-half's character in column j, conj((j/B)_3) conj((B/A)_3), equals conj((B/jA)_3) at every
      triple and conj((B/jA^2)_3) (FIVE-SIXTHS.md's struck attack note) at fewer than 45 percent; (ii) the slot
      coefficient is a composite Gauss sum: at 25 random pairs of split primes of norm below 400, gamma_2(pq)
      = (q/p)_3 (p/q)_3 gamma_2(p) gamma_2(q) (1e-12), gamma_2(c) = N(c)^{-1/2} sum_{v mod c} (v/c)_3 e(v/c) summed
      directly, and the factor (q/p)_3 (p/q)_3 = chi_p(q)^2 chi_q(p)^2 is the release's pair phase for two marks; with
      its conjugate the identity fails (error above 0.5); (iii) min over a in [0, 1] of max(v + a z, (1 - a) z,
      2(v + z)/3) equals max(v, 2(v + z)/3) on a grid of (v, z) in [0, 2]^2 (1e-12), and a split restricted to
      a in {0, 1/m, ..., 1} exceeds it by at most z/m (the slots' granularity).

Every number here is a statement about the pilot's model of the release's exponent system (frontier/wall78 and
fivesixths.py), not a theorem about L-functions.

Usage: python3 slotsplit.py     (about 70 s)
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
def emax_F(Mp, lp, a=1.0, b=2 / 3, sc=None, colterm=True, terms=None):
    """the maximum of the release's E over the dyads when the hybrid factor N + L + (NL)^{2/3} is replaced by
    max(N, L^a, (NL)^b), optionally capped by a per-column bound N L^{sc}: -u = max(v, a z_a, b(v + z_a)) - v - z_a,
    then min(-u, (sc - 1) z_a).  a = 1, b = 2/3, sc = None is the release (crossing.emax).  colterm=False replaces
    the quadratic sieve's factor K + NB by K (target T3, section 8).  terms, if given, replaces max(N, L^a, (NL)^b)
    by the maximum of N^cv L^cz over its pairs (cv, cz)."""
    if terms is None:
        terms = ((1, 0), (0, a), (b, b))
    pieces = tuple((cz - 1) * UNIT[6] + (cv - 1) * UNIT[7] for cv, cz in terms)
    A = [[1, 1, 0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 1, 1, 1, 0, 0, 0, 0], list(-TY)]
    b0 = [Mp, 0.0, 0.0, -(1 + lp)]
    best, arg = -np.inf, None
    for p1 in (P1 if colterm else P1[:1]):
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
TRILINEAR = dict(a=0.0)         # the trilinear bound N + (NL)^{2/3} (section 9)
CROSS_COSTS = (0.0, 0.05, 0.1, 0.15, 0.16, 0.165, 1.0)
CROSS_VALUES = ((5 / 6, 2e-7), (0.8486654, 1e-6), (0.8615362, 1e-6), (0.8725510, 1e-6), (0.8744704, 1e-6),
                (0.8748866, 2e-6), (0.8748866, 2e-6))
DICTIONARY = (   # (name, hybrid bound, second-branch coefficient of l', optimum (M, ell), least low side)
    ('(a) squared slot sums << L^(1/2) in every column', dict(sc=1 / 2), 3 / 2, (5 / 7, 2 / 7), 71 / 84),
    ('(b) L term dropped (trilinear)', TRILINEAR, 5 / 3, (8 / 11, 3 / 11), 28 / 33),
    ('(c) N + N^(3/4) L^(1/2)', dict(terms=((1, 0), (3 / 4, 1 / 2))), 1.0, (2 / 3, 1 / 3), 5 / 6),
    ('(d) square-root sieve N + (NL)^(1/2)', dict(a=0.0, b=0.5), 1.0, (2 / 3, 1 / 3), 5 / 6),
    ('(e) N alone', dict(terms=((1, 0),)), 1.0, (2 / 3, 1 / 3), 5 / 6),
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


class Five2X(Five2):
    """Five2 across the slice with the program's cap on mu raised from 1/2 to MU_MAX (section 8)."""
    MU_MAX = 2.0

    def solve(self, tol=1e-10):
        fixed = self.fixed_rows()
        A0 = np.array([r for _, r, _ in fixed]); b0 = np.array([b for _, _, b in fixed])
        DL, XL = F.O.DL, F.O.XL
        nd, nx = DL.shape[0], XL.shape[1]
        ii, jj = np.meshgrid(np.arange(0, nd, 30), np.arange(0, nx, 25), indexing='ij')
        idx = np.unique(np.concatenate([(ii * nx + jj).ravel(), np.arange(0, nd, 10) * nx + nx - 1]))
        bounds = [(0, 1), (0, 1), (0, 1), (0.5, 1), (0, self.MU_MAX if self.mode == 'cross' else 0.0)]
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


class Five2XFix(Five2X):
    """Five2X with l_x, l_y and l pinned (FIX = (l_x, l_y, l)) and MU_MAX settable: the ray and the corner (S6)."""
    FIX = None

    def fixed_rows(self):
        rows = super().fixed_rows()
        if self.FIX is not None:
            for i, t in enumerate(self.FIX):
                e = [0.0] * 5
                e[i] = 1.0
                rows = rows + [(f'fix{i}', e, t), (f'fix{i}-', [-x for x in e], -t)]
        return rows


def ray_point(job):
    t, sigma = job
    cls = type('Ray', (Five2XFix,), {'FIX': (t + 1e-8, t + 2e-7, t)})   # strict l_x > l and b > 0, just off the ray
    prog = cls(3 / 4, **cross_cfg(0.0), sigma=sigma, drop=D3)
    sol = prog.solve()
    return (None, None) if sol is None else (float(sol['v'][3]), prog.walls(sol))


def cross_cfg(c, readings=True):
    return dict(k=2, soft_third=True, mode='cross', cost=c, **(LV.READ if readings else {}))


D3 = ('ell<=1/5', 'ell>=1/6', 'ly<1/2')


# ---------------------------------------------------------------- S8: the trilinear bound's ingredients in Z[w]
W3 = np.exp(2j * np.pi * np.arange(3) / 3)
UNITS = ((1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1))     # 1, w, w^2, -1, -w, -w^2


def zmul(x, y):
    """(a + b w)(c + d w) with w^2 = -1 - w."""
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0] - x[1] * y[1])


def split_primes(bound):
    """the primary (= 1 mod 3) generators of the split primes of norm p < bound, p = 1 mod 3."""
    out = []
    for p in range(7, bound):
        if p % 3 != 1 or any(p % d == 0 for d in range(2, int(p ** 0.5) + 1)):
            continue
        for b in range(1, int((4 * p / 3) ** 0.5) + 2):
            s2 = 4 * p - 3 * b * b
            s = int(round(s2 ** 0.5)) if s2 >= 0 else -1
            if s >= 0 and s * s == s2 and (b + s) % 2 == 0:
                for u in UNITS:
                    x = zmul(((b + s) // 2, b), u)
                    if x[0] % 3 == 1 and x[1] % 3 == 0:
                        out.append((p, x))
                        break
                break
    return out


def csym(P, x):
    """(x/pi)_3 as the exponent k of w^k (None if pi | x), by Euler's criterion in Z[w]/pi = F_p, where w = -a/b."""
    p, (a, b) = P
    r = (-a * pow(b, -1, p)) % p
    t = (x[0] + x[1] * r) % p
    if t == 0:
        return None
    t = pow(t, (p - 1) // 3, p)
    return next(k for k in range(3) if pow(r, k, p) == t)


def gauss2(mods):
    """gamma_2(c) = N(c)^{-1/2} sum_{v mod c} (v/c)_3 e(v/c) for c the product of the given primes (distinct norms),
    e(z) = exp(2 pi i Tr(z/sqrt(-3))); for rational v and c = a + b w, Tr(v/(c sqrt(-3))) = -b v/N(c), and the rational
    v in [0, N(c)) represent Z[w]/c."""
    c, n = (1, 0), 1
    for P in mods:
        c, n = zmul(c, P[1]), n * P[0]
    v = np.arange(n)
    chi = np.ones(n, dtype=complex)
    for P in mods:
        tab = np.zeros(P[0], dtype=complex)
        tab[1:] = [W3[csym(P, (u, 0))] for u in range(1, P[0])]
        chi *= tab[v % P[0]]
    return complex(np.sum(chi * np.exp(-2j * np.pi * ((c[1] * v) % n) / n))) / n ** 0.5


class Five2XCap(Five2X):
    """Five2X with the program's cap on mu at 1.9 (S6: the sigma = 1 corner)."""
    MU_MAX = 1.9


def boot(job):
    cfg, kw = job[:2]
    klass = job[2] if len(job) > 2 else Five2
    kappa, fp = 3 / 4, []
    for _ in range(40):
        if kappa < 13 / 18 - 1e-12:
            break
        prog = klass(kappa, **cfg, **kw)
        sol = prog.solve()
        if sol is None:
            break
        fp.append((float(sol['v'][3]), kappa, prog.walls(sol), tuple(float(t) for t in sol['v'][:5])))
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
    flat = [lx / 6 + max(0.0, (0.75 - 2 * lx) / 6, 2 * (0.75 - 2 * lx) - (0.75 - lx)) / 2
            for lx in np.linspace(0.25, 0.375, 11)]
    xs = lambda lx: (0.75 - lx) - 0.25 > 11 * (0.75 - 2 * lx) / 6        # Xu-Sang's l_y - l > 11b/6
    gate('S2', abs(s_split - 41 / 48) < 1e-9 and abs(Ms - 0.75) < 1e-9 and abs(ls - 0.25) < 1e-9
         and abs(s_rel - 13 / 15) < 1e-9 and abs(lm - 41 / 48) < 1e-9 and tup <= 1e-9
         and max(flat) - min(flat) < 1e-12 and xs(0.375) and not xs(0.25) and not xs(21 / 64) and xs(21 / 64 + 1e-9),
         f'least low side with the split {s_split:.9f} at (M, l) = ({Ms:.3f}, {ls:.3f}) (41/48 = {41/48:.9f}); '
         f'without it {s_rel:.9f} (13/15) at ({Mr:.3f}, {lr:.3f}); low_min(3/4) = {lm:.9f}; tuple exponent max over '
         f'd {tup:.1e}; the Gram part is {flat[0]:.6f} for every l_x in [1/4, 3/8] (spread {max(flat) - min(flat):.1e}), '
         f'and l_y - l > 11b/6 holds exactly for l_x > 21/64 there')
    # S3, S4, S6: the bootstrapped systems
    R, z0 = LV.READ, 1 / 6 + 1 / 100
    D2, NOROT = ('ell<=1/5', 'ell>=1/6'), ('h/2<ly', 'ell<=1/5', 'ell>=1/6')
    sang = dict(k=2, soft_third=True, **R)
    sang0 = dict(k=2, lam=0.0, soft_third=True, **R)
    dhl0 = dict(k=LV.LINDELOF, counts='dh', lam=0.0, soft_third=True, **R)
    jobs = {'i1': (sang, dict(sigma=1.0, drop=D2)), 'i34': (sang, dict(sigma=0.75, drop=D2)),
            'i23': (sang, dict(sigma=2 / 3, drop=D2)), 'i12': (sang, dict(sigma=0.5, drop=D2)),
            'ii34': (sang0, dict(sigma=0.75, eta=0.1, z0=z0, drop=NOROT)),
            'ii23': (sang0, dict(sigma=2 / 3, eta=0.1, z0=z0, drop=NOROT)),
            'ii1': (sang0, dict(sigma=1.0, eta=0.1, z0=z0, drop=NOROT)),
            's4low': (dhl0, dict(sigma=0.5, eta=0.0, eta_L=0.3, z0=z0, drop=NOROT)),
            's4all': (dhl0, dict(sigma=0.5, eta=0.2, z0=z0, drop=NOROT)),
            'one': (cross_cfg(0.0), dict(sigma=1.0, drop=D3), Five2X),
            'one19': (cross_cfg(0.0), dict(sigma=1.0, drop=D3), Five2XCap),
            'noread': (cross_cfg(0.0, readings=False), dict(sigma=2 / 3, drop=D3), Five2X),
            'c34_0': (cross_cfg(0.0), dict(sigma=0.75, drop=D3), Five2X),
            'c34_15': (cross_cfg(0.15), dict(sigma=0.75, drop=D3), Five2X)}
    for c in CROSS_COSTS:
        jobs[('c', c)] = (cross_cfg(c), dict(sigma=2 / 3, drop=D3), Five2X)
    RAY = (0.5, 0.55, 0.56)
    with ProcessPoolExecutor(4) as ex:
        res = dict(zip(jobs, ex.map(boot, jobs.values())))
        ray = dict(zip(RAY, ex.map(ray_point, [(t, 2 / 3) for t in RAY])))
    for key, (cfg, kw, *_) in jobs.items():
        r = res[key]
        print(f'    {str(key):10s} {str({k: v for k, v in kw.items() if k != "drop"}):52s} B = {r[0]:.7f} '
              f'kappa {r[1]:.5f} walls {r[2]}')
    ok3 = (all(abs(res[k][0] - 0.8748866) < 2e-6 and 'E' in res[k][2] and 'row loss' not in res[k][2]
               for k in ('i1', 'i34', 'i23', 'i12'))
           and abs(res['ii34'][0] - 41 / 48) < 1e-6 and abs(res['ii23'][0] - 0.8537843) < 1e-6 and 'E' in res['ii23'][2]
           and abs(res['ii1'][0] - 13 / 15) < 1e-6)
    gate('S3', ok3, f'(i) eta = 0: sigma 1 {res["i1"][0]:.7f}, 3/4 {res["i34"][0]:.7f}, 2/3 {res["i23"][0]:.7f}, '
         f'1/2 {res["i12"][0]:.7f}; (ii) U^(1/10): sigma 3/4 {res["ii34"][0]:.7f} (41/48 = {41/48:.7f}), 2/3 '
         f'{res["ii23"][0]:.7f} (walls {res["ii23"][2]}), 1 {res["ii1"][0]:.7f} (13/15 = {13/15:.7f})')
    v3, bad = Fr(1, 3), 0
    for i in range(24):
        d = Fr(1, 8) + Fr(i, 23) * (Fr(5, 6) - Fr(1, 8))
        K = Fr(5, 6) - (1 - (1 - d))          # w = 1, R = 1 - delta, vartheta = 0
        E = (Fr(1, 2) + d / 2 + K) - K * v3 - Fr(1, 2) * v3 + (-Fr(1, 2) + Fr(1, 2) * d + K) * v3
        if E != 1 - d / 3:
            bad += 1
    prog = F.Five(0.75, k=LV.LINDELOF, counts='dh', lam=0.0, soft_third=True, sigma=0.5, **R)
    C, DL, XL = prog.C, F.O.DL, F.O.XL
    nx = XL.shape[1]
    bins = [i for i in range(DL.shape[0]) if DL[i, 0] >= 1 / 8 - 1e-12]
    dev4 = max(abs(C[0][i * nx + nx - 1] + (C[1][i * nx + nx - 1] + C[2][i * nx + nx - 1] + C[3][i * nx + nx - 1]) / 3
                   - (1 - DL[i, 0] / 3)) for i in bins)
    gate('S4', bad == 0 and abs(XL[0, -1] - 0.5) < 1e-12 and len(bins) > 1000 and dev4 < 1e-8
         and abs(res['s4low'][0] - 31 / 36) < 1e-6 and 'E' in res['s4low'][2] and abs(res['s4all'][0] - 5 / 6) < 2e-7,
         f'(i) endpoint 1 - delta/3 - s0 at the vertex: {24 - bad} of 24 bins exact, and the model\'s coefficients at '
         f'x = 1/2 agree at its {len(bins)} bins with delta >= 1/8 within {dev4:.1e}; (ii) savings on the low bins '
         f'only {res["s4low"][0]:.7f} (31/36 = {31/36:.7f}), walls {res["s4low"][2]}; on every bin '
         f'{res["s4all"][0]:.9f}')
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
    # S6: the crossing cost
    rc = [res[('c', c)] for c in CROSS_COSTS]
    ok6 = all(abs(r[0] - want) < tol for r, (want, tol) in zip(rc, CROSS_VALUES))
    t = rc[0][3]
    one, one19, noread = res['one'], res['one19'], res['noread']
    ok6 = (ok6 and max(abs(t[0] - t[2]), abs(t[1] - t[2])) < 1e-6 and t[2] >= 0.557
           and abs(res['c34_0'][0] - rc[0][0]) < 1e-7 and abs(res['c34_15'][0] - rc[3][0]) < 1e-7
           and abs(one[0] - 5 / 6) < 2e-7 and min(one[3][:3]) > 1 - 1e-6 and one[3][4] > 2 - 1e-6
           and abs(one19[0] - 0.835) < 1e-6 and abs(noread[0] - 0.87) < 1e-6 and 'principal edge' in noread[2]
           and abs(ray[0.5][0] - 0.8786610) < 1e-6 and 'E' in ray[0.5][1]
           and ray[0.55][0] > 5 / 6 + 1e-3 and 'E' in ray[0.55][1]
           and abs(ray[0.56][0] - 5 / 6) < 2e-7 and 'E' not in ray[0.56][1])
    gate('S6', ok6, 'sigma 2/3, no row saving, l_y < 1/2 dropped, mu <= 2: ' + ', '.join(
        f'c = {c}: {r[0]:.7f}' for c, r in zip(CROSS_COSTS, rc))
         + f'; sigma 3/4 at c = 0, 0.15: {res["c34_0"][0]:.7f}, {res["c34_15"][0]:.7f}; at c = 0 the optimum has '
         f'l_x = l_y = ell = {t[2]:.4f}, M + ell = {t[0] + t[1] + t[2]:.4f}; on the ray at kappa = 3/4: '
         + ', '.join(f't = {s}: {ray[s][0]:.7f}' + (' (E)' if 'E' in ray[s][1] else '') for s in RAY)
         + f'; sigma = 1 at c = 0: {one[0]:.9f} at (l_x, l_y, ell) = ({one[3][0]:.4f}, {one[3][1]:.4f}, '
         f'{one[3][2]:.4f}), mu = {one[3][4]:.4f}; with mu <= 1.9: {one19[0]:.7f}; without round 498\'s readings: '
         f'{noread[0]:.7f}, walls {noread[2]}')
    # S7: the crossing cost's zero is target T3
    rng7 = np.random.default_rng(7)
    dev_r, over_s, n7 = 0.0, -np.inf, 0
    while n7 < 300:
        m, l = rng7.uniform(0.3, 2.0), rng7.uniform(0.0, 1.0)
        if m < (1 - l) / 2 + 1e-3:
            continue
        dev_r = max(dev_r, abs(emax_F(m, l, colterm=False)[0] - m - max(0, (1 + 3 * l - 2 * m) / 4)))
        over_s = max(over_s, emax_F(m, l, sc=2 / 3, colterm=False)[0] - m - max(0, (1 + 2 * l - 2 * m) / 4))
        n7 += 1
    ray7 = [(t, emax_F(2 * t, t)[0] - 2 * t, 3 * t - 1) for t in (0.4, 0.5, 0.5572, 0.75)]
    dev_f, nf = 0.0, 0
    while nf < 300:
        m, l = rng7.uniform(0.3, 2.0), rng7.uniform(0.0, 1.0)
        if m < 2 * l or m < (1 - l) / 2 + 1e-3:
            continue
        dev_f = max(dev_f, abs(emax_F(m, l)[0] - X.formula(m, l)))
        nf += 1
    big = emax_F(0.6181, 0.9935)[0] - X.formula(0.6181, 0.9935)
    gate('S7', dev_r < 1e-9 and over_s < 1e-9 and all(abs(e - f) < 1e-9 for _, e, f in ray7) and dev_f < 1e-9
         and big > 0.1,
         f'without the column term (K + NB -> K), at {n7} random (M\', l\') in [0.3, 2] x [0, 1]: the release\'s '
         f'maximum is M\' + max(0, (1 + 3l\' - 2M\')/4) within {dev_r:.1e}, and with the split it is at most '
         f'M\' + max(0, (1 + 2l\' - 2M\')/4) (excess {over_s:.1e}); with the column term, on the ray (2t, t) the '
         f'excess is the first branch 3t - 1: ' + ', '.join(f't = {t}: {e:.4f}' for t, e, _ in ray7)
         + f'; with it, crossing.formula holds within {dev_f:.1e} at {nf} random points with M\' >= 2l\', and is '
         f'exceeded by {big:.4f} at (0.6181, 0.9935)')
    # S8: the trilinear bound's ingredients
    rng8 = np.random.default_rng(8)
    ps = split_primes(4000)
    rec = ident = jsq = 0
    NT = 2000
    for _ in range(NT):
        i, j, k = rng8.choice(len(ps), 3, replace=False)
        A, B, J = ps[i], ps[j], ps[k]
        rec += csym(A, B[1]) == csym(B, A[1])
        col_pair = (-csym(B, J[1]) - csym(A, B[1])) % 3                # conj((j/B)_3) conj((B/A)_3)
        ident += col_pair == (-(csym(J, B[1]) + csym(A, B[1]))) % 3    # conj((B/j)_3 (B/A)_3) = conj((B/jA)_3)
        jsq += col_pair == (-(csym(J, B[1]) + 2 * csym(A, B[1]))) % 3  # conj((B/jA^2)_3)
    small = split_primes(400)
    err, err_conj = 0.0, np.inf
    for _ in range(25):
        i, j = rng8.choice(len(small), 2, replace=False)
        P, Q = small[i], small[j]
        g_pq, g_p, g_q = gauss2([P, Q]), gauss2([P]), gauss2([Q])
        phase = W3[csym(P, Q[1])] * W3[csym(Q, P[1])]                  # (q/p)_3 (p/q)_3 = chi_p(q)^2 chi_q(p)^2
        err = max(err, abs(g_pq - phase * g_p * g_q))
        if abs(phase - 1) > 1e-9:
            err_conj = min(err_conj, abs(g_pq - np.conj(phase) * g_p * g_q))
    dev_split, gran = 0.0, -np.inf
    for v in np.linspace(0, 2, 41):
        for z in np.linspace(0, 2, 41):
            f = lambda a: max(v + a * z, (1 - a) * z, 2 * (v + z) / 3)
            cand = list(np.linspace(0, 1, 1001)) + ([min(1.0, max(0.0, (z - v) / (2 * z)))] if z > 0 else [])
            target = max(v, 2 * (v + z) / 3)
            dev_split = max(dev_split, abs(min(f(a) for a in cand) - target))
            gran = max(gran, min(f(k / 8) for k in range(9)) - target - z / 8)
    gate('S8', rec == NT and ident == NT and jsq < 0.45 * NT and err < 1e-12 and err_conj > 0.5
         and dev_split < 1e-12 and gran <= 1e-12,
         f'(i) {NT} triples of split primes of norm < 4000: reciprocity {rec}, the B-half\'s character equals '
         f'conj((B/jA)_3) at {ident} and conj((B/jA^2)_3) at {jsq}; (ii) gamma_2(pq) = (q/p)_3 (p/q)_3 '
         f'gamma_2(p) gamma_2(q) within {err:.1e} at 25 pairs of norm < 400, with the conjugate phase off by at least '
         f'{err_conj:.2f}; (iii) the split\'s minimum is max(v, 2(v + z)/3) within {dev_split:.1e}, and eighths of '
         f'the slots cost at most z/8 (excess over it {gran:.1e})')
    if FAILS:
        print('FAILED:', ', '.join(FAILS))
        sys.exit(1)
    print('all gates pass')


if __name__ == '__main__':
    main()
