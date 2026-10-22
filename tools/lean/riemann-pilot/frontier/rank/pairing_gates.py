"""Gates on the release's low estimate read through sextic theta components (PAIRING.md).

Exponents are powers of Z at the release's rescaled tuple of size d = 0 (every slot marked), in exact arithmetic.
The geometry (l_x, l_y, ell) is that of the release's eq. (old-eq:5.1): X = Z^{l_x}, Y = Z^{l_y}, slots of total
length ell, M = l_x + l_y, b = l_y - l_x, Q = q_{b*} X Y ~ Z^M, P_a = Y^2/Q ~ Z^b, h = 1 - l_x + ell, and
C(s) = l_x/2 + s - 1 + h/6 (its eq. (old-eq:5.11); Part I's C_I(s) = s - 2/3 is the case l_x = l_y = 1/2, ell = 0).
L is the completed-row norm's loss over the row count (zero at the release's geometry and on M + ell = 1 for
ell <= 1/5).

The pieces (PAIRING.md, section 2):
  |A_theta|^2   the Gram bound's exceptional term (Q/Y') P_a^{1/6}: exponent M - l_y + b/6, which is also the Kubota
                form Y^{-2/3} sum_{q_m <= Q} |rho(m)|^2 ~ Y^{-2/3} Q^{5/6}
  |B|^2         the completed-row norm Z^{M + L}
  mass          the theta mass of the completed rows: the Moebius sum of the target at a zero of real part beta,
                times the slots' amplitude Z^{ell/6}: exponent beta - 5/6 + ell/6
  |B_theta|^2   Q^{5/6} |mass|^2
  pairing       Q^{-1/2} <A_theta, B_theta> = Q^{-1/2} |A_theta| |B_theta| (both vectors lie on the theta direction)
  low           the release's bound Q^{-1/2} |A| |B| with |A| at its exceptional term

Gates (exit status 1 if any fails):
  P0  the release's completed row at n = 1 is a Moebius-weighted column of conjugate sextic Gauss sums: by its
      eq. (signal), gamma_2(c) conj(alpha(c)) conj(G(c)) = mu(c) conj(gamma_1(c)) with G(c) = conj(chi_c(4)) gamma_3(c),
      checked in the pilot's Gauss sums (composite.py, periods.c) at every squarefree primary modulus of norm <= 2500,
      together with gamma_2^3 = mu alpha and gamma_1 gamma_2 = mu alpha G
  P1  pairing = C(beta) identically in (l_x, l_y, ell, beta): checked at 2000 random rational points, at the
      release's geometry and at Part I's; its l_x and l_y coefficients are 1/3 and 0, the high side's
      X^{1/2 - z} Y^{w-1} at the principal point (w, z) = (1, 1/6)
  P2  low = l_x/2 + b/12 + L/2 at 2000 random points; at the release's geometry it is 3/16 = C(7/8) (its
      eq. (old-eq:5.10)), at Part I's 1/4 (Proposition prop:balanced-low)
  P3  the boundary beta_b, where pairing = low, is where |B_theta|^2 = |B|^2: beta_b = 5/6 - ell/6 + M/12 + L/2, the
      same for every split of M into l_x + l_y (2000 random points, five splits each).  It reproduces 7/8 (the release),
      11/12 (Part I) and 11/12 - ell/4 on M + ell = 1 (README round 503), and equals round 503's
      s_0 = 5/6 + l_x/6 - ell/6 + theta b/2 + L/2 at theta = 1/6.  With Sang's row-norm loss L = (5 ell - 1)_+/4 on
      M + ell = 1, its least value over ell in [0, 1/3] is 13/15, at ell = 1/5: README round 496's W6b, the low side's
      own minimum.  Against round 503's committed code: beta_b equals
      frontier/wall78/lowbudget.steps(l_x, l_y, ell, 1/6) at 2000 random geometries where the exceptional term is the
      Gram bound's largest (b <= 3M/8) and M + ell <= 1, with L = lowbudget's row loss
      max(0, M + ell - 1, (1 + 3 ell - 2M)/4)
  P4  the rest of the split |<A, B>| <= |<A_theta, B>| + |A_rest| |B|: with |A_rest|^2 at the Gram diagonal Q/Y',
      its boundary is beta_rest = 5/6 - ell/6 + l_x/6 + L/2 = beta_b - b/12 at 2000 random points, 83/96 at the
      release's geometry (README round 503: removing the exceptional term lowers the boundary by b/12).  With the theta
      part bounded from an input half-plane Re s > theta_0 the split returns max(theta_0, beta_rest) (PAIRING.md,
      section 4), so it cannot return a half-plane below its input unless that input is below beta_rest
  P5  unit classes (PAIRING.md, section 5): over rows closed under the six units, the weight-one rows split into
      orthogonal parts R_u by the unit character u of the modulus, and a modulus c sees only its own class:
      sum_k conj(R(k)) g(c, k) = sum_k conj(R_u(c)(k)) g(c, k).  Checked by brute force at the squarefree primary
      moduli of norm <= 600 and every row of norm <= 600
  P6  the same template for the order-N families (ORDER-RANK.md): at block sigma the dual's rows N(k) <= Z^{1-sigma}
      carry an order-N theta component of energy H^{1-1/N} |M_N(Z)|^2, with the Moebius mass
      M_N(Z) = sum_{N(n) <= Z} mu(n) N(n)^{-(1/2 - 1/N)} (exponent theta - 1/2 + 1/N at a zero of real part theta).
      It reaches the extraction's target Z^2 exactly at round 288's theta_N(sigma) (orders.theta), for every N in
      orders.ORDERS and 121 values of sigma in [0, 1]; for N = 3 this is CUBIC.md's fixed point
      (orders.component_exponent, orders.component_sigma), for N = 6 at sigma = 0 the companion's 11/12

Gates on the sextic dual projections recorded in sextic_dual.json by sextic.py and sextic_stats.py (PAIRING.md,
section 5; runs with Z = 10^4 ... 8*10^4 at H = Z^{3/4}, Z = 10^4 ... 8*10^4 at H = Z, and two at H = 100 Z), with P
the projection coefficient of a weight on the unit-class prediction, P^prof the same with the weight-one profile over
16 norm bins, and se, z from 400 random-sign draws:
  S1  the unit classes are needed: 'mixed' projects at >= 1.3 on the one-class prediction in every run, and within 0.08
      of 1 on the class prediction
  S2  primes and 'mixed', profile-corrected: within 0.05 and 0.08 of 1, with z^prof <= 2.5, in every run
  S3  the Moebius function, profile-corrected: z^prof <= 2.5 in every run, and P^prof at least 4 standard errors from 0
      at the largest Z of each regime
  S4  the twisted weights (mu times a character, and the characters alone; ray classes of orders 2 to 12, infinity
      types, Kummer characters): z^prof <= 3 in every run
  S5  the profile is not flat: in every run some log-norm bin with at least 20 moduli has a mean ratio y(c)/pred(c) more
      than 4 standard errors from 1, so the per-modulus N(c)^{-1/3} profile does not hold at these sizes
  S6  the additive polynomial's regime (rows far beyond the moduli, H = 100 Z at Z = 10^3 and 2*10^3) is not reached:
      the weight-one excess (S - diag)/diag is at most 0.05 there, so these sizes say nothing about A_theta, for which
      PAIRING.md relies on Xu-Sang's theorem
S1-S5 use the runs with H <= Z; S6 the runs with H > Z.

In session runs these perturbations fail the gates shown: the Kubota exponent 5/6 of sum |rho|^2 as 4/5 (P1, P3, P4);
the slots' amplitude ell/6 as ell/5 (P1, P3, P4); the exceptional term P_a^{1/6} as P_a^{1/12} (P1, P2; P3 and P4 still
pass, because |A_theta| enters the pairing and the low bound alike and cancels from the boundary); the diagonal Q/Y'
as Q (P4); G(c) without conj(chi_c(4)) (P0); a modulus paired with the next unit class's rows (P5); Sang's loss with
its kink at ell = 1/4 in place of 1/5 (P3); and the order-N theta energy H^{1-1/N} as H^{1-1/(2N)} (P6).
"""
import json
import os
import random
import sys
import tempfile
from fractions import Fraction as Fr

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from bias import elements_up_to                                # noqa: E402
from composite import Field, load_primes, squarefree_moduli    # noqa: E402
from identities import periods_file                            # noqa: E402
import orders                                                  # noqa: E402
sys.path.insert(0, os.path.join(HERE, '..', 'wall78'))
import lowbudget                                               # noqa: E402

RELEASE = dict(lx=Fr(17, 48), ly=Fr(23, 48), ell=Fr(1, 6), L=Fr(0))
PART1 = dict(lx=Fr(1, 2), ly=Fr(1, 2), ell=Fr(0), L=Fr(0))


def C(g, s):
    h = 1 - g['lx'] + g['ell']
    return g['lx'] / 2 + s - 1 + h / 6


def pieces(g, beta):
    lx, ly, ell, L = g['lx'], g['ly'], g['ell'], g['L']
    M, b = lx + ly, ly - lx
    A2 = M - ly + b / 6
    A2_kubota = -Fr(2, 3) * ly + Fr(5, 6) * M
    B2 = M + L
    mass = beta - Fr(5, 6) + ell / 6
    Bt2 = Fr(5, 6) * M + 2 * mass
    pairing = -M / 2 + A2 / 2 + Bt2 / 2
    low = -M / 2 + A2 / 2 + B2 / 2
    return dict(M=M, b=b, A2=A2, A2_kubota=A2_kubota, B2=B2, Bt2=Bt2, pairing=pairing, low=low)


def boundary(g):
    """solve pairing(beta) = low: pairing is beta + const, so beta_b = beta - (pairing(beta) - low) at any beta."""
    p = pieces(g, Fr(0))
    return -(p['pairing'] - p['low'])


def beta_rest(g):
    """the boundary of the split's rest term: low with |A|^2 at the Gram diagonal Q/Y' only."""
    lx, ly, L = g['lx'], g['ly'], g['L']
    M = lx + ly
    low_rest = -M / 2 + (M - ly) / 2 + (M + L) / 2
    return low_rest - C(g, Fr(0))


def rnd(rng, lo, hi, den=480):
    return Fr(rng.randint(int(lo * den), int(hi * den)), den)


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f"{name}: {'PASS' if ok else 'FAIL'}  {msg}")
        fails += 0 if ok else 1

    with tempfile.TemporaryDirectory() as tmp:
        path = periods_file('w', 2500, tmp)
        F = Field('w')
        primes = load_primes(F, path, 2500)
        nm, om, el, G, pr = squarefree_moduli(F, primes, 2500)
        primes6 = load_primes(F, path, 600)
        mod6 = squarefree_moduli(F, primes6, 600)

    # P0
    mu = (-1.0) ** om
    al = np.array([F.to_c(z) / abs(F.to_c(z)) for z in el])
    z6 = np.exp(2j * np.pi / 6)
    e4 = [P.sym((4, 0)) for P in primes]
    chi4 = np.array([z6 ** (sum(e4[i] for i in p) % 6) for p in pr])
    g1, g2, g3 = G[:, 1], G[:, 2], G[:, 3]
    Gc = np.conj(chi4) * g3
    errs = [np.max(np.abs(g2 * np.conj(al) * np.conj(Gc) - mu * np.conj(g1))),
            np.max(np.abs(g2 ** 3 - mu * al)), np.max(np.abs(g1 * g2 - mu * al * Gc))]
    gate('P0', max(errs) < 1e-9,
         f'{len(nm)} moduli; max errors {errs[0]:.1e} (B coefficient), {errs[1]:.1e}, {errs[2]:.1e}')

    rng = random.Random(20261022)
    pts = [dict(lx=rnd(rng, 0, 1), ly=rnd(rng, 0, 1), ell=rnd(rng, 0, Fr(1, 3)), L=rnd(rng, 0, Fr(1, 4)))
           for _ in range(2000)]
    betas = [rnd(rng, Fr(1, 2), 1) for _ in pts]

    # P1
    bad = sum(pieces(g, be)['pairing'] != C(g, be) for g, be in zip(pts, betas))
    bad += sum(pieces(g, be)['A2'] != pieces(g, be)['A2_kubota'] for g, be in zip(pts, betas))
    rel = all(pieces(g, be)['pairing'] == C(g, be) for g in (RELEASE, PART1) for be in (Fr(7, 8), Fr(11, 12), Fr(1)))
    base = dict(lx=Fr(0), ly=Fr(0), ell=Fr(0), L=Fr(0))
    f0 = pieces(base, Fr(5, 6))['pairing']
    cx = pieces(dict(base, lx=Fr(1)), Fr(5, 6))['pairing'] - f0
    cy = pieces(dict(base, ly=Fr(1)), Fr(5, 6))['pairing'] - f0
    gate('P1', bad == 0 and rel and cx == Fr(1, 3) and cy == 0 and C(PART1, Fr(0)) == Fr(-2, 3)
         and C(RELEASE, Fr(0)) == Fr(-11, 16),
         f'pairing = C(beta) at {len(pts)} random points and at the release and Part I; Kubota form of |A_theta|^2 '
         f'agrees; coefficients of (l_x, l_y): ({cx}, {cy}); C_I(0) = {C(PART1, Fr(0))}, C_II(0) = {C(RELEASE, Fr(0))}')

    # P2
    bad = sum(pieces(g, Fr(0))['low'] != g['lx'] / 2 + (g['ly'] - g['lx']) / 12 + g['L'] / 2 for g in pts)
    lr, l1 = pieces(RELEASE, Fr(0))['low'], pieces(PART1, Fr(0))['low']
    gate('P2', bad == 0 and lr == Fr(3, 16) == C(RELEASE, Fr(7, 8)) and l1 == Fr(1, 4),
         f'low = l_x/2 + b/12 + L/2 at {len(pts)} points; release {lr} = C(7/8) = {C(RELEASE, Fr(7, 8))}; Part I {l1}')

    # P3
    bad = 0
    for g in pts:
        bb = boundary(g)
        M = g['lx'] + g['ly']
        p = pieces(g, bb)
        if bb != Fr(5, 6) - g['ell'] / 6 + M / 12 + g['L'] / 2 or p['Bt2'] != p['B2']:
            bad += 1
        s0 = Fr(5, 6) + g['lx'] / 6 - g['ell'] / 6 + Fr(1, 6) * (g['ly'] - g['lx']) / 2 + g['L'] / 2
        if s0 != bb:
            bad += 1
        for _ in range(5):
            lx = rnd(rng, 0, M) if M > 0 else Fr(0)
            if boundary(dict(g, lx=lx, ly=M - lx)) != bb:
                bad += 1
    slice_bad = 0
    for k in range(97):
        ell = Fr(k, 480)
        if boundary(dict(lx=(1 - ell) / 2 - Fr(1, 32), ly=(1 - ell) / 2 + Fr(1, 32), ell=ell, L=Fr(0))) \
                != Fr(11, 12) - ell / 4:
            slice_bad += 1
    br, b1 = boundary(RELEASE), boundary(PART1)
    lb_bad = 0
    for _ in range(2000):
        ell = rnd(rng, 0, Fr(1, 3))
        M = rnd(rng, 0, 1 - ell)
        b = rnd(rng, 0, 3 * M / 8)
        lx, ly = (M - b) / 2, (M + b) / 2
        L = max(Fr(0), M + ell - 1, (1 + 3 * ell - 2 * M) / 4)
        if boundary(dict(lx=lx, ly=ly, ell=ell, L=L)) != lowbudget.steps(lx, ly, ell, Fr(1, 6)):
            lb_bad += 1
    sang = []
    for k in range(161):
        ell = Fr(k, 480)
        L = max(Fr(0), (5 * ell - 1) / 4)
        sang.append((boundary(dict(lx=(1 - ell) / 2, ly=(1 - ell) / 2, ell=ell, L=L)), ell))
    low_min = min(sang)
    gate('P3', bad == 0 and slice_bad == 0 and lb_bad == 0 and br == Fr(7, 8) and b1 == Fr(11, 12)
         and low_min == (Fr(13, 15), Fr(1, 5)),
         f'beta_b = 5/6 - ell/6 + M/12 + L/2 = round 503 s_0, |B_theta|^2 = |B|^2 there, split-free: '
         f'{len(pts)} points, '
         f'{bad} bad; release {br}, Part I {b1}; 11/12 - ell/4 on M + ell = 1 for ell = 0..1/5: {slice_bad} bad; '
         f'with Sang\'s loss the least is {low_min[0]} at ell = {low_min[1]}; '
         f'lowbudget.steps disagrees at {lb_bad} of 2000')

    # P4
    bad = sum(beta_rest(g) != Fr(5, 6) - g['ell'] / 6 + g['lx'] / 6 + g['L'] / 2
              or boundary(g) - beta_rest(g) != (g['ly'] - g['lx']) / 12 for g in pts)
    rest, gap = beta_rest(RELEASE), boundary(RELEASE) - beta_rest(RELEASE)
    gate('P4', bad == 0 and rest == Fr(83, 96) and gap == Fr(1, 96),
         f'beta_rest = 5/6 - ell/6 + l_x/6 + L/2 = beta_b - b/12 at {len(pts)} points ({bad} bad); '
         f'release: beta_rest = {rest}, beta_b - beta_rest = {gap}')
    # P5
    nm6, om6, el6, G6s, pr6 = mod6
    ks, kt = elements_up_to(F, 600)
    E = np.zeros((len(nm6), len(ks)), dtype=int)
    D = np.zeros((len(nm6), len(ks)), dtype=bool)
    for i, p in enumerate(pr6):
        for idx in p:
            sv = primes6[idx].sym_vec(ks, kt)
            D[i] |= sv < 0
            E[i] += np.where(sv < 0, 0, sv)
    g = np.where(D, 0, G6s[:, 1][:, None] * z6 ** (-(E % 6)))
    e1w = [P.sym((1, 1)) for P in primes6]
    u = np.array([sum(e1w[i] for i in p) % 6 for p in pr6])
    R = g.sum(axis=0)
    Ru = np.array([g[u == j].sum(axis=0) for j in range(6)])
    T = (np.conj(R)[None, :] * g).sum(axis=1)
    Tu = (np.conj(Ru[u]) * g).sum(axis=1)
    gram = np.conj(Ru) @ Ru.T
    off = np.max(np.abs(gram - np.diag(np.diag(gram))))
    gate('P5', np.max(np.abs(T - Tu)) < 1e-8 * np.max(np.abs(T)) and off < 1e-8 * np.max(np.abs(gram)),
         f'{len(nm6)} moduli, {len(ks)} rows: max |T - T_u| = {np.max(np.abs(T - Tu)):.1e} '
         f'(max |T| {np.max(np.abs(T)):.0f}); '
         f'largest cross-class inner product {off:.1e} (largest class norm {np.max(np.abs(gram)):.0f})')

    # P6
    bad = 0
    for N in orders.ORDERS:
        for k in range(121):
            sg = Fr(k, 120)
            # theta-energy boundary: (1 - 1/N)(1 - sigma) + 2(theta - 1/2 + 1/N) = 2
            th = (2 - (1 - Fr(1, N)) * (1 - sg)) / 2 + Fr(1, 2) - Fr(1, N)
            if th != orders.theta(N, sg):
                bad += 1
            if N == 3 and orders.component_exponent(th, sg) != (1 - Fr(1, 3)) * (1 - sg) + 2 * (th - Fr(1, 6)):
                bad += 1
            if N == 3 and th >= Fr(5, 6) and orders.component_sigma(th) != sg:
                bad += 1
    gate('P6', bad == 0 and orders.theta(6, 0) == Fr(11, 12),
         f'theta-energy boundary = theta_N(sigma) for N in {orders.ORDERS} at 121 sigma each ({bad} bad); '
         f'theta_6(0) = {orders.theta(6, 0)}')

    # S1-S5 on the recorded sextic dual projections
    allruns = json.load(open(os.path.join(HERE, 'sextic_dual.json')))['runs']
    runs = [r for r in allruns if r['H'] <= r['Z']]
    far = [r for r in allruns if r['H'] > r['Z']]
    W = [r['weights'] for r in runs]
    tags = [f"{r['Z']}:{r['H']}" for r in runs]
    mo = [r['mixed_one_class'] for r in runs]
    mc = [w['mixed']['P'] for w in W]
    gate('S1', all(x >= 1.3 for x in mo) and all(abs(x - 1) <= 0.08 for x in mc),
         f'{len(runs)} runs; mixed on one class {min(mo):.3f}..{max(mo):.3f}, '
         f'on unit classes {min(mc):.3f}..{max(mc):.3f}')
    ok, worst = True, 0.0
    for w in W:
        for name, tol in (('prime', 0.05), ('mixed', 0.08)):
            x = w[name]
            ok &= abs(x['P_prof'] - 1) <= tol and x['z_prof'] <= 2.5
            worst = max(worst, abs(x['P_prof'] - 1))
    pp = [w['prime']['P_prof'] for w in W]
    pm = [w['mixed']['P_prof'] for w in W]
    gate('S2', ok, f'primes {min(pp):.3f}..{max(pp):.3f}, mixed {min(pm):.3f}..{max(pm):.3f}; '
                   f'largest |P^prof - 1| {worst:.3f}')
    zmu = [w['mu']['z_prof'] for w in W]
    big = {}
    for r in runs:
        reg = 'H=Z' if r['H'] == r['Z'] else 'H<Z'
        if reg not in big or r['Z'] > big[reg]['Z']:
            big[reg] = r
    sig = {reg: r['weights']['mu']['P_prof'] / r['weights']['mu']['se_prof'] for reg, r in big.items()}
    mus = ', '.join(f"{t} {w['mu']['P_prof']:.3f}+-{w['mu']['se_prof']:.3f}" for t, w in zip(tags, W))
    gate('S3', max(zmu) <= 2.5 and len(sig) == 2 and min(sig.values()) >= 4,
         f'mu P^prof per run: {mus}; largest z^prof {max(zmu):.2f}; at the largest Z, P^prof/se = '
         + ', '.join(f'{k} {v:.1f}' for k, v in sorted(sig.items())))
    twisted = [n for n in W[0] if n not in ('prime', 'mixed', 'mu')]
    zt = max(w[n]['z_prof'] for w in W for n in twisted)
    gate('S4', zt <= 3, f'{len(twisted)} twisted weights in each of {len(runs)} runs; largest z^prof {zt:.2f}')
    devs = [max(abs(b['mean'] - 1) / b['se'] for b in r['bins'] if b['n'] >= 20) for r in runs]
    gate('S5', min(devs) > 4, f'largest bin deviation from 1, in standard errors, per run: '
         + ', '.join(f'{t} {d:.1f}' for t, d in zip(tags, devs)))
    ex = [r['forward']['one'] for r in far]
    gate('S6', len(far) >= 2 and max(ex) <= 0.05,
         f"{len(far)} runs with H > Z: weight-one excess "
         + ', '.join(f"{r['Z']}:{r['H']} {r['forward']['one']:+.4f}" for r in far))
    return fails


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
