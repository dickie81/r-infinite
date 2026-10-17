"""Round 37: saturation without RH, numerically.

(1) Is the ground state non-increasing on [0, a]? Checked by second-scale differences (step a/200
on [0, 0.995a]); the truncated cosine series carries Gibbs ripple, so the smallest step is reported.
(2) The tail. Unconditional explicit formula: Q(g) = sum_rho ghat(t_rho)^2. Zeros with |gamma| <= H
lie on the line (verified, H = 3e12). For the rest |Im t| < 1/2 and |ghat(z)| <= B/|z| with
B = 2 g(0) cosh(a/2) (g even, non-increasing on [0, a]). So Tail <= B^2 S_H with
S_H = 2 sum_{gamma > H} 1/gamma^2 <= 4 int_H^inf N+(t)/t^3 dt, where N+ is an explicit upper bound
for N(T) (Trudgian: N(T) <= (T/2pi) log(T/2pi e) + 7/8 + 0.112 log T + 0.278 log log T + 2.51).
(3) The per-zero bounds: |ghat(gamma_j)| <= sqrt((lam1 + Tail)/2), and the pinning bound
sqrt((lam1 + Tail)/2)/|ghat'(gamma_j)|, next to the RH version sqrt(lam1/2)/|ghat'|."""
import sys, json, math
import numpy as np
from scipy.integrate import quad
sys.path.insert(0, sys.argv[1])
from weil_prime_gram import gram, minimiser, rayleigh
from flint import arb, ctx
import mpmath
mpmath.mp.dps = 50
H = 3e12
Nplus = lambda t: t / (2 * math.pi) * math.log(t / (2 * math.pi * math.e)) + 7 / 8 + 0.112 * math.log(t) + 0.278 * math.log(math.log(t)) + 2.51
# int_H^inf N+(t)/t^3 dt, with the substitution t = H e^s
I = quad(lambda s: Nplus(H * math.exp(s)) / (H * math.exp(s)) ** 2, 0, 80, limit=400)[0]
S_H = 4 * I
GAM = [mpmath.zetazero(n).imag for n in range(1, 26)]
for spec in sys.argv[2:]:
    d, K, p = spec.split(':'); d, K, p = float(d), int(K), int(p)
    G, N, pp = gram(d, K, p); c, ev = minimiser(G, N, p)
    with ctx.workprec(p):
        c = [arb(x) for x in c]
        if c[0] < 0: c = [-x for x in c]
        nrm = sum(N[i] * c[i] * c[i] for i in range(K)).sqrt(); c = [x / nrm for x in c]
        lam = float(rayleigh(G, N, c, p).mid())
        a = d / 2; aa = arb(d) / 2
        cf = np.array([float(x.mid()) for x in c])
        ts = np.linspace(0, 0.995 * a, 200)
        gv = np.array([np.sum(cf * np.cos(np.arange(K) * math.pi * t / a)) for t in ts])
        g0 = float(sum(c).mid())
        steps = np.diff(gv)
        B = 2 * g0 * math.cosh(a / 2)
        tail = B * B * S_H
        om2 = [(arb(k) * arb.pi() / aa) ** 2 for k in range(K)]
        sg = [c[k] if k % 2 == 0 else -c[k] for k in range(K)]
        def dgh(r):
            S = arb(0); D = arb(0)
            for k in range(K):
                dd = r * r - om2[k]; S += sg[k] * r / dd; D += sg[k] * (-(r * r + om2[k])) / (dd * dd)
            return 2 * (aa * (r * aa).cos() * S + (r * aa).sin() * D)
        rows = []
        for j, gm in enumerate(GAM):
            gp = abs(float(dgh(arb(mpmath.nstr(gm, 45))).mid()))
            rows.append([j + 1, round(float(gm), 2), '%.2e' % gp, '%.2e' % (math.sqrt(lam / 2) / gp),
                         '%.2e' % (math.sqrt((lam + tail) / 2) / gp)])
    print(json.dumps(dict(delta=d, K=K, lam1=lam, g0=g0, B=B, S_H=S_H, tail_bound=tail,
                          monotone=bool(np.all(steps <= 0)), max_step=float(steps.max()), min_g=float(gv.min()),
                          rows=rows)))
    sys.stdout.flush()
