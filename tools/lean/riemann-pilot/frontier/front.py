"""Round 32: where does the pinning stop? Zero counting against measured fronts.

Ground state from the paper's Gram (full-precision coefficients). Zeros of ghat in (0, R) by sign
changes (step 0.005) plus bisection in arb. For each zeta zero gamma_k < R: the signed offset to the
nearest ghat zero. Fronts:
  T_pin(tau): the largest gamma_k with every gamma_j <= gamma_k within tau of a ghat zero
              (tau = 1e-6, 1e-3, 1e-1);
  T_alt:      the last gamma_k up to which sgn ghat(gamma_k) alternates;
  T_cnt:      the first gamma_k after which N_zeta(T) > N_ghat(T) (the zero budget runs out).
Prediction: N_zeta(T) ~ (T/2pi) log(T/2pi e) + 7/8 against N_ghat(T) ~ aT/pi, so the budget runs out
at T ~ 2 pi e^{2a+1} at leading order; the refined root solves the equation with both 1/T terms.
Usage: front.py <tools/research> delta:K:prec [...]"""
import sys, json, math
sys.path.insert(0, sys.argv[1])
from weil_prime_gram import gram, minimiser
from flint import arb, ctx
import numpy as np
from scipy.optimize import brentq
Z = np.array(json.load(open('gapnum/zeros6700.json')))
for spec in sys.argv[2:]:
    d, K, p = spec.split(':'); d, K, p = float(d), int(K), int(p)
    a = d / 2
    R = min(250.0, 0.8 * K * math.pi / a)
    G, N, pp = gram(d, K, p)
    c, ev = minimiser(G, N, p)
    with ctx.workprec(p):
        c = [arb(x) for x in c]
        if c[0] < 0: c = [-x for x in c]
        aa = arb(d) / 2
        om2 = [(arb(k) * arb.pi() / aa) ** 2 for k in range(K)]
        sg = [c[k] if k % 2 == 0 else -c[k] for k in range(K)]
        def gh(x):
            r = arb(x); S = arb(0)
            for k in range(K): S += sg[k] * r / (r * r - om2[k])
            return 2 * (r * aa).sin() * S
        xs = np.arange(0.00731, R, 0.005)
        v = np.array([float(gh(x).mid()) for x in xs])
        zs = []
        for i in np.nonzero(v[:-1] * v[1:] < 0)[0]:
            lo, hi, flo = xs[i], xs[i + 1], v[i]
            for _ in range(45):
                m = (lo + hi) / 2; fm = float(gh(m).mid())
                if (fm < 0) == (flo < 0): lo, flo = m, fm
                else: hi = m
            zs.append((lo + hi) / 2)
        zs = np.array(zs)
        gam = Z[Z < R - 1]
        off = np.array([zs[np.argmin(np.abs(zs - g))] - g for g in gam])
        sgn = np.array([1 if float(gh(g).mid()) > 0 else -1 for g in gam])
    def tpin(tau):
        bad = np.nonzero(np.abs(off) >= tau)[0]
        k = bad[0] if len(bad) else len(gam)
        return float(gam[k - 1]) if k > 0 else 0.0
    alt = np.nonzero(sgn[:-1] == sgn[1:])[0]
    T_alt = float(gam[alt[0]]) if len(alt) else float(gam[-1])
    # counting: N_zeta(gamma_k) = k; N_ghat(T) = number of ghat zeros below T
    Ng = np.array([np.sum(zs < g + 1e-9) for g in gam]); Nz = np.arange(1, len(gam) + 1)
    deficit = Nz - Ng
    pos = np.nonzero(deficit > 0)[0]
    T_cnt = float(gam[pos[0]]) if len(pos) else None
    lead = 2 * math.pi * math.exp(2 * a + 1)
    f = lambda T: T / (2 * math.pi) * math.log(T / (2 * math.pi * math.e)) + 7 / 8 - (a * T / math.pi)
    try: refined = brentq(f, 20, 5000)
    except Exception: refined = None
    print(json.dumps(dict(delta=d, a=a, K=K, lam1=float(ev.mid()) if hasattr(ev, 'mid') else float(ev), R=R,
        n_zeros_ghat=int(len(zs)), T_pin_1e6=tpin(1e-6), T_pin_1e3=tpin(1e-3), T_pin_1e1=tpin(1e-1),
        T_alt=T_alt, T_cnt=T_cnt, pred_leading=lead, pred_refined=refined,
        deficit_at=[[round(float(g), 2), int(dd)] for g, dd in list(zip(gam, deficit))[::10]])))
    sys.stdout.flush()
