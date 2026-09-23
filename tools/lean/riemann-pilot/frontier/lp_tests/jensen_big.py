"""Test (b) by the Polya-Schur / Jensen criterion.
For even real g on [-a, a] with ghat real-rooted, phi(w) = ghat(sqrt(-w))/ghat(0) = sum_j gamma_j w^j / j!, with
gamma_j = j! mu_{2j}/(2j)!  and  mu_{2j} = int u^{2j} g / int g,  is in the Laguerre-Polya class (genus 0 in w).
Polya-Schur: then every Jensen polynomial J^{d,n}(w) = sum_i C(d,i) gamma_{n+i} w^i is hyperbolic (real-rooted).
A non-hyperbolic J^{d,n} proves ghat has a non-real zero (the converse needs all d).
Controls: Xi (via Riemann's Phi; must pass), and the positive decreasing probe 1_{[-a,a]} + 2*1_{[-a/3,a/3]}
(ghat = 2[sin(az) + 2 sin(az/3)]/z has non-real zeros; must fail)."""
import sys, json, math
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
import mpmath as mp
J, DMAX = 90, 44
def gammas_from_moments(mu):
    return [mp.factorial(j) * mu[j] / mp.factorial(2 * j) for j in range(len(mu))]
def jensen_report(gam, label):
    worst = None; fails = []
    for d in range(2, DMAX + 1):
        for n in range(0, len(gam) - d):
            coeffs = [mp.binomial(d, i) * gam[n + i] for i in range(d + 1)]
            r = mp.polyroots(coeffs[::-1], maxsteps=400, extraprec=600)
            im = max(abs(mp.im(x)) / max(abs(x), mp.mpf(10)**-30) for x in r)
            if im > mp.mpf(10)**-20: fails.append((d, n, float(im)))
            worst = im if worst is None or im > worst else worst
    return dict(label=label, n_polys=sum(len(gam) - d for d in range(2, DMAX + 1)), n_fail=len(fails),
                first_fails=fails[:6], worst_rel_imag=float(worst))
def moments_on(gfun, a, nodes_per=192, pan=12):
    from mpmath.calculus.quadrature import GaussLegendre
    nodes = GaussLegendre(mp.mp).calc_nodes(7, mp.mp.prec)
    pts = []
    for j in range(pan):
        lo, hi = mp.mpf(a) * j / pan, mp.mpf(a) * (j + 1) / pan
        for x, w in nodes: pts.append(((hi + lo) / 2 + (hi - lo) / 2 * x, (hi - lo) / 2 * w))
    gv = [(u, w * gfun(u)) for u, w in pts]
    m = [2 * sum(wg * u**(2 * j) for u, wg in gv) for j in range(J)]
    return [x / m[0] for x in m]
mode = sys.argv[1]
mp.mp.dps = 120
if mode == "xi":
    Phi = lambda u: sum((2*mp.pi**2*n**4*mp.e**(4.5*u) - 3*mp.pi*n**2*mp.e**(2.5*u)) * mp.e**(-mp.pi*n**2*mp.e**(2*u)) for n in range(1, 40))
    mu = moments_on(Phi, 3.0)             # Phi(3) ~ e^{-pi e^6}: truncation invisible at 120 digits
    print(json.dumps(jensen_report(gammas_from_moments(mu), "Xi (Riemann Phi)")))
elif mode == "control":
    a = mp.mpf(1)
    # exact moments of 1_{[-a,a]} + 2*1_{[-a/3,a/3]}: 2 a^{2j+1}/(2j+1) + 4 (a/3)^{2j+1}/(2j+1)
    m = [2 * a**(2*j+1)/(2*j+1) + 4 * (a/3)**(2*j+1)/(2*j+1) for j in range(J)]
    print(json.dumps(jensen_report(gammas_from_moments([x / m[0] for x in m]), "control box+2*box(a/3), non-real zeros")))
else:
    from weil_prime_gram import gram, minimiser
    d, K, p = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    a = d / 2
    G, N, pp = gram(d, K, p); c, ev = minimiser(G, N, p)
    cm = [mp.mpf((int(x.mid().man_exp()[0]), int(x.mid().man_exp()[1]))) if hasattr(x, 'mid') else mp.mpf(x) for x in c]
    if cm[0] < 0: cm = [-x for x in cm]
    g = lambda u: sum(cm[k] * mp.cos(k * mp.pi * u / a) for k in range(K))
    mu = moments_on(g, a)
    print(json.dumps(jensen_report(gammas_from_moments(mu), f"ground state delta={d} K={K}")))
