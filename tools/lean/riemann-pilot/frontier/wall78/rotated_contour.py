"""The 7/8 comparison in the rotated numerator coordinate (README round 497).

The release (openai/math, The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex) moves each row bin's
contour to "Re s=a+16e, Re w=1-a-6e, Re z=z_0" (line 5828). Sang (arXiv 2610.15291, sec. 6) rotates the numerator
line to "Re s=a+16e, Re w=1/2-vartheta, Re z=z_0" and averages the reflected numerator over the bin,
U^{(3R+1)/4 - vartheta/2} (his Proposition prop:numerator, from the plain fourth moment and Hoelder).

Rotated endpoint, derived here from the release's bin exponent at d = h (Lemma bin-contour-accounting): moving w from
1 - a to 1/2 - vartheta costs l_y (delta/2 - vartheta) through Y^{w-1}, and replaces the bin's numerator U^{R + delta/2}
by U^{R + (1-R)/(2k) - vartheta/2 + vartheta} (moment order 2k, reflection cost U^vartheta). With vartheta = tau x delta:
    E = C0 + delta/2 + x delta {ell + 2 tau (h/4 - l_y/2)} - h (1 - 1/(2k)) (1 - R_kappa),   C0 = -1/4 + b/6 + 5 ell/4,
on Sang's slice l_x = (1-b-ell)/2, l_y = (1+b-ell)/2, h = (1+b+3 ell)/2, boundary B(ell) = 11/12 - ell/4.
At k = 2, tau = 1/(6 kappa) this is Sang's eq. endpoint. Sang's admissibility (his sec. 6 items 1-4) is implemented as
stated; "exact" mode replaces his coarse small-delta scalar ("the coarse bound ... gives E_small <= C0 + A_sm delta")
by E_small with the full count, his case split ell/h < 1/(6 kappa) by tau_small = min(ell/h, 1/(6 kappa)), and his
floor scalar ("endpoint C0+(1/2+3 ell/2)/50 and slope less than 2") by the floor bin's exact endpoint on the
release's contour (a = 51/100, R = 1). In both modes the full-capacity amplification on delta >= 1/8 is used either
under Sang's option 1 (ell/h >= 1/(6 kappa)) or under his short gate "R<=(6kappa-2q)L" checked with the full count at
d = h; his range 29991/40000 <= kappa (his sufficient condition for that gate) is replaced by the gate itself and by
kappa >= 13/18 (his Lemma kappa-extension). A per-bin choice between his two options is not modelled. The bootstrap is
his, kappa <- 2B - 1 from kappa = 3/4; it ends at a fixed point (|2B - 1 - kappa| < 1e-10), after 12 stages, or when no
point is admissible. Values are optima over the script's grids: ell on 69 points refined locally, the bins on 1501 x 201
points for delta >= 1/8 and 400 x 201 below. Every boundary here is a statement about this exponent system, not a theorem.

Gates (exit status 1 if any fails):
  R1  identity: the rotated endpoint above equals Sang's eq. endpoint (k = 2, tau = 1/(6 kappa)) at 2000 random points
      within 1e-12; S1: dropping the reflection cost U^vartheta breaks it
  R2  Sang's certificate (b_1, ell_1, kappa_1) = (17307/200000, 1253399/7500000, 29991/40000) is admissible here
  R3  the optimum of Sang's system: stage 1 (kappa = 3/4) <= his B_0 = 69991/80000, and the kappa-bootstrap fixed
      point within 2e-7 of his B_1 = 8748867/10000000; its next wall is the high side's endpoint condition ("E / E")
  R4  rotated-coordinate levers, each a fixed point of the bootstrap with its next wall: the 4th moment (Sang's) in
      exact mode gives his 0.8748867 to within 1e-6 (the high side's endpoint condition closes the b-interval from both
      ends, "E / E"); the 6th moment and Lindelof on average over bins give 0.8733860 under Sang's conditions (his
      coarse small-delta scalar binds) and 0.8701164 in exact mode (the floor bin binds)
  R5  RETRACTED in round 498, false when written. Its two values (0.8673682 with Sang's 4th moment, 0.8639728 with
      Lindelof on average, the Gram bound's exceptional term removed) took the boundary B(ell) - b/12 with every
      endpoint <= 0 relative to B(ell), and applied 87/100 to B(ell). The high side was never asked to carry the
      saving b/12, and both values lie below Sang's principal region Re s >= 87/100. levers.py computes this lever on
      the boundary max(87/100, B(ell) + max(-b/12, E_max)) and reproduces the two values on a legacy path (its gate C1).
  R6  strip coordinate z = -2i(s - 1/2): Polymath15's H_0(z) = xi(1/2 + iz/2)/8 has its zeros in |Im z| <= 2(theta - 1/2)
      when every zero has 1 - theta <= Re rho <= theta, and their Theorem debr-bound (t_0 = 0, y_0 = 2(theta - 1/2))
      gives Lambda <= 2(theta - 1/2)^2: 1/2 at theta = 1, 9/32 at 7/8, 25/72 at 11/12, all above Polymath15's 0.22
"""
import sys
import numpy as np
from scipy.optimize import minimize_scalar

ALPHA, Z0, DMIN, FLOOR = 5 / 6, 17 / 50, 1 / 100, 1 / 50
DL = np.linspace(1 / 8, 5 / 6, 1501)[:, None]
XL = np.linspace(0, 0.5, 201)[None, :]
DS = np.linspace(FLOOR, 1 / 8, 401)[:-1, None]
XS = np.linspace(0, 0.5, 201)[None, :]


def Rk(d, x, kappa):
    c = 1 / (3 * kappa)
    Dk = 3 - (1 + 2 * c) * x
    Pk = (2 - 2 * c * x) * (1 - x)
    return 1 - d + (ALPHA - d) * d * Pk / (2 * ((ALPHA - d) * Dk + d * Pk))


def geometry(b, ell):
    return (1 - b - ell) / 2, (1 + b - ell) / 2, (1 + b + 3 * ell) / 2


def endpoint_rotated(b, ell, kappa, d, x, k=2, tau=None, reflection_cost=True):
    """release's bin exponent at d = h with the numerator line rotated to 1/2 - vartheta (vartheta = tau x d)."""
    tau = 1 / (6 * kappa) if tau is None else tau
    lx, ly, h = geometry(b, ell)
    a = (1 + d) / 2
    R = Rk(d, x, kappa)
    th = tau * x * d
    E_rel = a * (1 - ly) - (11 / 12 - ell / 4) - ell / 2 + x * d * ell + h * (R + d / 2 - 1 / 6)
    numer = (1 - R) / (2 * k) - th / 2 + (th if reflection_cost else 0.0) - d / 2
    return E_rel + ly * (d / 2 - th) + h * numer


def endpoint_sang(b, ell, kappa, d, x):
    lx, ly, h = geometry(b, ell)
    c = 1 / (3 * kappa)
    C0 = -1 / 4 + b / 6 + 5 * ell / 4
    return C0 + d / 2 + d * x * (ell + c * (h / 4 - ly / 2)) - (3 * h / 4) * (1 - Rk(d, x, kappa))


class System:
    """mode 'sang': Sang's admissibility as stated; mode 'exact': small delta, case split and floor done exactly.
    gram: 'paper' (low side B(ell), absorption l_y - ell > 11b/6) or 'none' (absorption 3b <= 1 - 3 ell; best() takes
    'paper' only, and levers.py computes the boundary without the exceptional term)."""

    def __init__(self, kappa, k=2, tau=None, mode='sang', gram='paper'):
        self.kappa, self.k, self.mode, self.gram = kappa, k, mode, gram
        self.tau = 1 / (6 * kappa) if tau is None else tau
        w = 1 - 1 / (2 * k)
        R = Rk(DL, XL, kappa)
        self.gate_need = (R / (6 * kappa - 2 * XL * DL)).max()      # short gate: ell/h >= max R/(6 kappa - 2q)
        t = self.tau
        self.e0 = (-1 / 4 + DL / 2 - 2 * t * XL * DL / 8 - w * (1 - R) / 2).ravel()
        self.eb = (1 / 6 - 2 * t * XL * DL / 8 - w * (1 - R) / 2).ravel()
        self.el = (5 / 4 + XL * DL + 2 * t * XL * DL * 5 / 8 - 3 * w * (1 - R) / 2).ravel()
        self.Rs = Rk(DS, XS, kappa)

    def side(self):
        kap, rows = self.kappa, []
        add = lambda n, ab, al, rhs: rows.append((n, ab, al, rhs))       # ab*b + al*ell <= rhs
        add('b>0', -1, 0, -1e-7)
        add('ell<=1/5', 0, 1, 1 / 5)
        add('ell>=1/6', 0, -1, -1 / 6)
        add('B>87/100', 0, 1 / 4, 11 / 12 - 0.87 - 1e-9)
        add('lx>ell', 1, 3, 1 - 1e-9)
        if self.gram == 'paper':
            add('ly-ell>11b/6', 8 / 3, 3, 1 - 1e-9)
        else:
            add('Pa^2/Y<=1', 3, 3, 1)                                      # P_a^2/Y' <= 1 at d = ell
        add('6k.ell>3/4', 0, -6 * kap, -3 / 4 - 1e-9)
        if self.mode == 'sang':
            add('ell/h<1/(6k)', -1, 12 * kap - 3, 1 - 1e-9)
        add('ell/h>21/100', 0.21, -1.37, -0.21 - 1e-9)
        add('h/2<ly', -1, 5, 1 - 1e-9)
        add('ly<1/2', 1, -1, -1e-9)
        add('C0<-1/250', 1 / 6, 5 / 4, 1 / 4 - 1 / 250 - 1e-9)
        if self.mode == 'sang':
            add('floor scalar', 1 / 6, 5 / 4 + 3 / 100, 1 / 4 - 1 / 50 - 1e-9)
        s = Z0 - 1 / 6
        add('low rows', s / 2 - 1 / 4, 3 * s / 2 + 1 / 4, -1 / 20 - 2 * DMIN - s / 2 + 1 / 4 - 1e-9)
        return rows

    def interval(self, ell):
        """the b-interval allowed by every condition linear in b at this ell, and the names of its two ends."""
        names = ['E'] * len(self.eb)
        ab = list(self.eb)
        rhs = list(-self.e0 - self.el * ell - 1e-9)
        for n, cb, cl, r in self.side():
            names.append(n); ab.append(cb); rhs.append(r - cl * ell)
        ab, rhs = np.array(ab), np.array(rhs)
        pos, neg = ab > 1e-15, ab < -1e-15
        if np.any(rhs[~pos & ~neg] < 0):
            return None
        hv, lv = rhs[pos] / ab[pos], rhs[neg] / ab[neg]
        ih, il = np.argmin(hv), np.argmax(lv)
        return max(lv[il], 0.0), hv[ih], names[np.flatnonzero(neg)[il]], names[np.flatnonzero(pos)[ih]]

    def parts(self, b, ell):
        """the conditions that are not linear in b, as (value, name); each must be < 0, and each holds on an
        interval of b (E_small is convex in b, the floor bin affine, the short gate monotone)."""
        lx, ly, h = geometry(b, ell)
        C0 = -1 / 4 + b / 6 + 5 * ell / 4
        gate = (self.gate_need - ell / h) if ell / h < 1 / (6 * self.kappa) else -1.0
        if self.mode == 'sang':
            asm = 1 / 2 + (ell / 2) * (1 / 2 + 2 * ell / h) - h / 2
            return [(C0 + asm / 8 + 1 / 250, 'small-delta scalar'), (gate, 'short gate')]
        w = 1 - 1 / (2 * self.k)
        ts = min(ell / h, 1 / (6 * self.kappa))
        Es = (C0 + DS / 2 + XS * DS * (ell + 2 * ts * (h / 4 - ly / 2)) - h * w * (1 - self.Rs)).max()
        a, x = (1 + FLOOR) / 2, np.array([0.0, 0.5])
        Ef = (a * (1 - ly) - (11 / 12 - ell / 4) - ell / 2 + x * FLOOR * ell + h * (1 + FLOOR / 2 - 1 / 6)).max()
        return [(Es, 'small delta'), (Ef, 'floor bin'), (gate, 'short gate')]

    def nonlinear(self, b, ell):
        """worst of the conditions that are not linear in b, with its name; must be < 0."""
        return max(self.parts(b, ell))

    def b_set(self, ell):
        iv = self.interval(ell)
        if iv is None or iv[0] > iv[1]:
            return None
        lo, hi = iv[0], iv[1]
        f = lambda b: self.nonlinear(b, ell)[0]
        r = minimize_scalar(f, bounds=(lo, hi), method='bounded', options={'xatol': 1e-11})
        if r.fun > -1e-9:
            return None
        right = hi
        if f(hi) > -1e-9:
            a_, c_ = r.x, hi
            for _ in range(45):
                m = (a_ + c_) / 2
                a_, c_ = (m, c_) if f(m) <= -1e-9 else (a_, m)
            right = a_
        return r.x, right

    def best(self):
        """best boundary B(ell) = 11/12 - ell/4 at the largest admissible ell (gram 'paper'). Round 497's gram 'none'
        objective (max ell/4 + b/12 with every endpoint <= 0) is retracted in round 498; see levers.py."""
        if self.gram != 'paper':
            raise ValueError("gram 'none' is computed by levers.py (round 498)")
        start = max(1 / 6, 1 / (8 * self.kappa)) + 1e-7          # Sang's 6 kappa ell > 3/4
        ells = np.unique(np.concatenate([[start], np.linspace(1 / 6, 1 / 5, 69)]))
        ells = ells[ells >= start]
        ok = [e for e in ells if self.b_set(e)]
        if not ok:
            return None
        above = ells[ells > max(ok)]
        lo, hi = max(ok), (above[0] if len(above) else 1 / 5 + 1e-9)
        for _ in range(32):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if self.b_set(mid) else (lo, mid)
        iv = self.interval(hi)
        if iv is None or iv[0] > iv[1]:
            wall = f'{iv[2]} / {iv[3]}' if iv else 'linear'
        else:
            wall = self.nonlinear(self.b_set(lo)[0], hi)[1]
        return 11 / 12 - lo / 4, lo, self.b_set(lo)[0], wall


def fixed_point(k=2, mode='sang', gram='paper', stages=12):
    kappa, out = 3 / 4, []
    for _ in range(stages):
        if kappa < 13 / 18:
            break
        r = System(kappa, k=k, mode=mode, gram=gram).best()
        if r is None:
            break
        out.append((kappa, r))
        if abs(2 * r[0] - 1 - kappa) < 1e-10:
            break
        kappa = 2 * r[0] - 1
    return out


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    rng = np.random.default_rng(496)
    pts = [(rng.uniform(0.01, 0.12), rng.uniform(1 / 6, 1 / 5), rng.uniform(0.72, 0.75), rng.uniform(1 / 8, 5 / 6),
            rng.uniform(0, 0.5)) for _ in range(2000)]
    dev = max(abs(endpoint_rotated(*p) - endpoint_sang(*p)) for p in pts)
    dev_s = max(abs(endpoint_rotated(*p, reflection_cost=False) - endpoint_sang(*p)) for p in pts)
    gate('R1', dev < 1e-12, f'rotated release endpoint = Sang eq. endpoint at 2000 random points: max deviation {dev:.1e}')
    gate('S1', dev_s > 1e-3, f'sabotage, reflection cost U^vartheta dropped: max deviation {dev_s:.3f}')

    b1, l1, k1 = 17307 / 200000, 1253399 / 7500000, 29991 / 40000
    sy = System(k1)
    iv = sy.interval(l1)
    nl = sy.nonlinear(b1, l1)[0]
    emax = endpoint_sang(b1, l1, k1, np.linspace(1 / 8, 5 / 6, 6001)[:, None], np.linspace(0, 0.5, 801)[None, :]).max()
    gate('R2', iv[0] <= b1 <= iv[1] and nl < 0 and emax < 0,
         f'Sang certificate admissible: b_1 in [{iv[0]:.5f}, {iv[1]:.5f}], fine-grid max E {emax:.2e}, small-delta scalar {nl:.2e}')

    fp = fixed_point()
    B0, B_fp = fp[0][1][0], fp[-1][1][0]
    gate('R3', B0 <= 69991 / 80000 and abs(B_fp - 0.8748867) < 2e-7 and fp[-1][1][3] == 'E / E'
         and abs(2 * B_fp - 1 - fp[-1][0]) < 1e-9,
         f'stage 1: {B0:.8f} <= B_0 = {69991/80000:.7f}; fixed point {B_fp:.8f} vs B_1 = 0.8748867 (kappa {fp[-1][0]:.7f}); '
         f'next wall: {fp[-1][1][3]}')

    def boot(fp):
        kap, r = fp[-1]
        return kap, abs(2 * r[0] - 1 - kap), len(fp)

    for nm, k, mode, want, wall in [('4th moment (Sang), exact mode', 2, 'exact', 0.8748867, 'E / E'),
                                    ('6th moment, Sang conditions', 3, 'sang', 0.8733860, 'small-delta scalar'),
                                    ('Lindelof on average, Sang conditions', 10 ** 9, 'sang', 0.8733860, 'small-delta scalar'),
                                    ('6th moment, exact mode', 3, 'exact', 0.8701164, 'floor bin'),
                                    ('Lindelof on average, exact mode', 10 ** 9, 'exact', 0.8701164, 'floor bin')]:
        fp = fixed_point(k=k, mode=mode)
        r, (kap, gap, n) = fp[-1][1], boot(fp)
        gate('R4', abs(r[0] - want) < 1e-6 and r[3] == wall and gap < 1e-9,
             f'{nm:38s} B = {r[0]:.7f} (recorded {want:.7f}), next wall: {r[3]}; '
             f'kappa {kap:.7f}, |2B - 1 - kappa| = {gap:.0e} after {n} stage(s)')

    lam = {th: 2 * (th - 0.5) ** 2 for th in (1.0, 7 / 8, 11 / 12, 0.8748867)}
    gate('R6', abs(lam[1.0] - 0.5) < 1e-15 and abs(lam[7 / 8] - 9 / 32) < 1e-15 and abs(lam[11 / 12] - 25 / 72) < 1e-15
         and min(lam.values()) > 0.22,
         'Lambda <= 2(theta - 1/2)^2: ' + ', '.join(f'theta {t:.7g} -> {v:.5f}' for t, v in lam.items()) + '; Polymath15: 0.22')

    print(f'{fails} gate(s) failed' if fails else 'all gates pass')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
