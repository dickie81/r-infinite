"""Statistics of the sextic dual projections written by sextic.py (PAIRING.md, section 5).

For each Z, from OUTDIR/sextic_w_<Z>.npz: the per-modulus projection y(c), the prediction
pred(c) = N(c)^{-1/3} kappa(c) (no fitted constant: the two totals agree exactly, both being sum_k e(k)), and:

  shape      mean of Re y(c)/pred(c) in log-norm bins, and the slope of log(sum Re y / sum kappa) against log N(c)
             over the bins with N(c) >= Z^{1/2} (the Kubota exponent predicts -1/3);
  weights    for each test weight w the projection P_w = Re(conj(pred_w) meas_w)/|pred_w|^2, with
             meas_w = sum_c w(c) y(c) and pred_w = sum_c w(c) pred(c), its standard error from NULL random-sign
             draws (signs constant on each Galois orbit {c, conj c}, so that real weights stay real; uniform
             random phases for complex weights) applied to the residuals r(c) = y(c) - pred(c), and
             z_w = |meas_w - pred_w| / rms|null|.

The weights: 'prime', 'mixed', 'mu'; mu times ray-class characters modulo a split prime of norm 7, 13, 19 or 31
(orders 2, 3, 4, 5, 6, 9, 12); mu times alpha(c)^j, alpha(c) = c/|c| (infinity types j = 1, 2, 3, 6); mu times the
Kummer characters chi_c(2) and chi_c(lambda); and the same characters without mu.

Also reported for 'mixed': its projection against the cruder one-class prediction (kappa1), which the unit
classes correct (PAIRING.md, section 5).  And for every weight the profile-corrected projection P_w^prof, with
pred(c) multiplied by the weight-one ratio s(B) = sum_{c in B} Re y(c) / sum_{c in B} pred(c) of its log-norm bin B
(PROFILE_BINS bins, the moduli of norm below 7 in the first): it asks whether y(c) depends on the modulus only through
its norm and unit class, whatever the profile in the norm.

Usage:  python3 sextic_stats.py OUTDIR out.json STEM1 [STEM2 ...]      (a stem is Z or Z_H<H>, as sextic.py names it)
"""
import json
import math
import os
import sys

import numpy as np

NULL = 400
PROFILE_BINS = 16
SEED = 20261022
RAY = ((7, (1, 2)), (7, (3, 6)), (13, (3, 4, 12)), (19, (9,)), (31, (5,)))   # (norm of the prime, orders)
INF_TYPES = (1, 2, 3, 6)


def ray_character(el, p, order):
    """a character of exact order `order` of (O/pi)^x, pi the prime above p with w = r mod p for the least root r
    of x^2 + x + 1 mod p, evaluated on the primary moduli; zero where pi | c."""
    r = next(x for x in range(p) if (x * x + x + 1) % p == 0)
    g = next(x for x in range(2, p) if all(pow(x, (p - 1) // q, p) != 1 for q in prime_factors(p - 1)))
    ind = {pow(g, i, p): i for i in range(p - 1)}
    out = np.zeros(len(el), dtype=complex)
    for i, (a, b) in enumerate(el):
        x = (a + b * r) % p
        if x:
            out[i] = np.exp(2j * np.pi * ind[x] / order)
    return out


def prime_factors(n):
    f, d = [], 2
    while d * d <= n:
        while n % d == 0:
            f.append(d)
            n //= d
        d += 1
    if n > 1:
        f.append(n)
    return sorted(set(f))


def weights_for(r):
    nm, om, el = r['norm'], r['omega'], [tuple(z) for z in r['el']]
    mu = (-1.0) ** om
    w = {'prime': (om == 1).astype(float), 'mixed': r['mixed'], 'mu': mu}
    chars = {}
    for p, orders in RAY:
        for o in orders:
            chars[f'ray {p} order {o}'] = ray_character(el, p, o)
    zc = np.array([complex(a - 0.5 * b, math.sqrt(3) / 2 * b) for a, b in el])
    alpha = zc / np.abs(zc)
    for j in INF_TYPES:
        chars[f'alpha^{j}'] = alpha ** j
    zeta = np.exp(2j * np.pi * np.arange(6) / 6)
    names = [str(x) for x in r['kummer_names']]
    for name in ('2', 'lambda'):
        ex = r['kummer'][names.index(name)]
        chars[f'chi_c({name})'] = np.where(ex < 0, 0, zeta[np.maximum(ex, 0)])
    for k, v in chars.items():
        w['mu ' + k] = mu * v
    for k, v in chars.items():
        w[k] = v
    return w


def orbits(el):
    """index of the Galois conjugate a + b conj(w) = (a - b) - b w of each primary modulus."""
    pos = {tuple(z): i for i, z in enumerate(el)}
    return np.array([pos[(int(a - b), int(-b))] for a, b in el])


def stats(r):
    nm, y, kap = r['norm'].astype(float), r['y'], r['kappa']
    Z = int(r['Z'])
    pred = nm ** (-1 / 3) * kap
    res = y - pred
    pred1 = nm ** (-1 / 3) * r['kappa1']
    mixed = r['mixed']
    out = {'Z': Z, 'H': int(r['H']), 'moduli': int(len(nm)), 'rows': int(r['nk']),
           'mixed_one_class': float(np.sum(mixed * y).real / np.sum(mixed * pred1)),
           'forward': {str(wn): float((s - d) / d) for wn, s, d in zip(r['weights'], r['S'], r['dS'])},
           'total_check': float(abs(y.sum() - pred.sum()) / abs(pred.sum()))}
    # shape
    edges = np.unique(np.round(np.exp(np.linspace(0, math.log(Z), 11))).astype(int))
    edges[-1] = Z + 1
    bins = []
    for lo, hi in zip(edges[:-1], edges[1:]):
        m = (nm >= lo) & (nm < hi)
        if m.sum() < 5:
            continue
        rat = (y[m] / pred[m]).real
        bins.append({'lo': int(lo), 'hi': int(hi), 'n': int(m.sum()), 'mean': float(rat.mean()),
                     'se': float(rat.std() / math.sqrt(m.sum())),
                     'logN': float(np.mean(np.log(nm[m]))),
                     'log_y_over_kappa': (float(math.log(y[m].real.sum() / kap[m].sum()))
                                          if y[m].real.sum() > 0 and kap[m].sum() > 0 else None)})
    out['bins'] = bins
    big = [b for b in bins if b['lo'] >= math.sqrt(Z) and b['log_y_over_kappa'] is not None]
    X = np.array([b['logN'] for b in big])
    Y = np.array([b['log_y_over_kappa'] for b in big])
    out['slope'] = float(np.polyfit(X, Y, 1)[0]) if len(big) >= 3 else None
    # the weight-one profile in the norm
    pe = np.exp(np.linspace(math.log(7), math.log(Z + 1), PROFILE_BINS + 1))
    pe[0], pe[-1] = 0, Z + 1
    pb = np.clip(np.searchsorted(pe, nm, side='right') - 1, 0, PROFILE_BINS - 1)
    prof = np.ones(PROFILE_BINS)
    for i in range(PROFILE_BINS):
        m = pb == i
        if m.any() and pred[m].sum() > 0:
            prof[i] = y[m].real.sum() / pred[m].sum()
    preds = pred * prof[pb]
    res_s = y - preds
    out['profile'] = [float(x) for x in prof]
    out['profile_n'] = [int(np.sum(pb == i)) for i in range(PROFILE_BINS)]
    # weights
    rng = np.random.default_rng(SEED + Z)
    conj_idx = orbits(r['el'])
    rep = np.minimum(np.arange(len(nm)), conj_idx)
    W = weights_for(r)
    out['weights'] = {}
    for wn, w in W.items():
        meas, pw = np.sum(w * y), np.sum(w * pred)
        real = np.isrealobj(w) or np.max(np.abs(np.imag(w))) == 0
        nulls, nulls_s = [], []
        for _ in range(NULL):
            if real:
                s = rng.choice([-1.0, 1.0], size=len(nm))[rep]
            else:
                s = np.exp(2j * np.pi * rng.random(len(nm)))
            nulls.append(np.sum(np.abs(w) * s * res))
            nulls_s.append(np.sum(np.abs(w) * s * res_s))
        nulls, nulls_s = np.array(nulls), np.array(nulls_s)
        pws = np.sum(w * preds)
        if abs(pw) > 0:
            P = float(np.real(np.conj(pw) * meas) / abs(pw) ** 2)
            seP = float(np.sqrt(np.mean((np.real(np.conj(pw) * nulls) / abs(pw) ** 2) ** 2)))
        else:
            P, seP = None, None
        if abs(pws) > 0:
            Ps = float(np.real(np.conj(pws) * meas) / abs(pws) ** 2)
            seS = float(np.sqrt(np.mean((np.real(np.conj(pws) * nulls_s) / abs(pws) ** 2) ** 2)))
        else:
            Ps, seS = None, None
        out['weights'][wn] = {'meas': [float(meas.real), float(meas.imag)], 'pred': [float(pw.real), float(pw.imag)],
                              'P': P, 'se': seP, 'P_prof': Ps, 'se_prof': seS,
                              'z_prof': float(abs(meas - pws) / np.sqrt(np.mean(np.abs(nulls_s) ** 2))),
                              'z': float(abs(meas - pw) / np.sqrt(np.mean(np.abs(nulls) ** 2))),
                              'mass_over_noise': float(abs(pw) / np.sqrt(np.mean(np.abs(nulls) ** 2)))}
    return out


def show(o):
    print(f"Z = {o['Z']}, H = {o['H']}: {o['moduli']} moduli, {o['rows']} rows; 'mixed' against one class "
          f"{o['mixed_one_class']:.3f}; forward (S - diag)/diag "
          + ', '.join(f'{k} {v:+.4f}' for k, v in o['forward'].items())
          + ('' if o['slope'] is None else f"; slope {o['slope']:+.4f}"))
    print('  bins: ' + '  '.join(f"[{b['lo']},{b['hi']}) {b['mean']:.3f}+-{b['se']:.3f}" for b in o['bins']))
    for wn, x in o['weights'].items():
        P = 'n/a' if x['P'] is None else f"{x['P']:+.3f} +- {x['se']:.3f}"
        Pp = 'n/a' if x['P_prof'] is None else f"{x['P_prof']:+.3f} +- {x['se_prof']:.3f}"
        print(f"  {wn:22s} P {P:18s} z {x['z']:5.2f}  |pred|/noise {x['mass_over_noise']:7.2f}   "
              f"profile-corrected P {Pp:18s} z {x['z_prof']:5.2f}")


if __name__ == '__main__':
    outdir, outjson, stems = sys.argv[1], sys.argv[2], sys.argv[3:]
    runs = []
    for stem in stems:
        r = np.load(os.path.join(outdir, f'sextic_w_{stem}.npz'))
        runs.append(stats(r))
        show(runs[-1])
    json.dump({'runs': runs}, open(outjson, 'w'), indent=1)
