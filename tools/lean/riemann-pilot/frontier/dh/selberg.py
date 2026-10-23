"""Selberg-identity defects on the window for DH's first-failure vector g* and zeta's ground state.
A g(u) = sum_n w(n) g(u + log n), w(n) = c(n)/sqrt(n) (one-sided shifts); P = restriction to [-a, a].
  E1 = <g, P A P A P g> - <g, P A^2 P g>      (compression of the one-sided product; A^2 has weights (c*c)/sqrt)
  E2 = <g, P A P A* P g> - <g, P (A A*) P g>   (compression of the mixed product; A A* = sum w(m)w(n) T_{log m - log n})
  S  = <g, P (D + A^2 - B_mu) P g>              (Selberg with zeta's right side mu*log^2; D weights c log n)
All with n, m <= e^{2a} (terms with larger shifts vanish on the window)."""
import sys, math, json
sys.path.insert(0, '.')
import numpy as np, mpmath as mp
import dh_gram as D, dhlib as Lb
from flint import arb, ctx
def cvec(name, N):
    return [float(x.mid()) if hasattr(x, 'mid') else float(x) for x in Lb.cvec_arb(name, N, 200)]
def mobius(n):
    r, p, m = 1, 2, n
    while p*p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0: return 0
            r = -r
        p += 1
    return -r if m > 1 else r
def dconv(f, g, N):
    h = [0.0]*(N + 1)
    for d in range(1, N + 1):
        if f[d] == 0: continue
        for m in range(1, N//d + 1): h[d*m] += f[d]*g[m]
    return h
def vec(name, delta, K, prec):
    with ctx.workprec(prec + 40):
        _, z0, logq, pole = Lb.lf(name, 10)
    Nmax = int(math.exp(delta)) + 1
    c = Lb.cvec_arb(name, Nmax + 1, prec)
    w = [(n, c[n]) for n in range(2, Nmax + 1) if not (c[n] == 0)]
    G, Nn, pp = D.gram(delta, K, prec, dict(z0=z0, logq=logq, pole=pole, weights=w))
    lam, v = D.lowest_mp(G, Nn, int(prec*0.29), 1)[0]
    return lam, [float(x) for x in v]
def run(name, delta, K, prec, M=6001):
    lam, cf = vec(name, delta, K, prec)
    a = delta/2
    u = np.linspace(-a, a, M); du = u[1] - u[0]
    g = sum(ck*np.cos(k*math.pi*u/a) for k, ck in enumerate(cf))
    g /= math.sqrt(np.trapezoid(g*g, u))
    N = int(math.exp(delta))
    c = [0.0] + [0.0] + cvec(name, N)[2:N + 1] if N >= 2 else [0.0]*(N + 1)
    c = cvec(name, N)
    c = c + [0.0]*(N + 1 - len(c))
    gi = lambda x: np.interp(x, u, g, left=0.0, right=0.0)   # g extended by 0 (P)
    def Tsh(h, x): return np.interp(u + x, u, h, left=0.0, right=0.0)   # P T_x P h on the grid
    w = {n: c[n]/math.sqrt(n) for n in range(2, N + 1) if c[n] != 0}
    Ag = sum(wn*Tsh(g, math.log(n)) for n, wn in w.items())
    Asg = sum(wn*Tsh(g, -math.log(n)) for n, wn in w.items())
    ip = lambda p, q: float(np.trapezoid(p*q, u))
    # E1: <g, PAPAP g> vs <g, P A^2 P g>
    PAPAg = sum(wn*Tsh(Ag, math.log(n)) for n, wn in w.items())
    cc = dconv([0.0] + [c[n] if n >= 2 else 0.0 for n in range(1, N + 1)], [0.0] + [c[n] if n >= 2 else 0.0 for n in range(1, N + 1)], N)
    A2g = sum((cc[n]/math.sqrt(n))*Tsh(g, math.log(n)) for n in range(2, N + 1) if cc[n] != 0)
    E1 = ip(g, PAPAg) - ip(g, A2g)
    # E2: mixed product
    PAPAsg = sum(wn*Tsh(Asg, math.log(n)) for n, wn in w.items())
    AAsg = sum(wm*wn*Tsh(g, math.log(m) - math.log(n)) for m, wm in w.items() for n, wn in w.items())
    E2 = ip(g, PAPAsg) - ip(g, AAsg)
    # Selberg with mu*log^2
    mu = [0] + [mobius(n) for n in range(1, N + 1)]
    l2 = [0.0] + [math.log(n)**2 for n in range(1, N + 1)]
    b = dconv([float(x) for x in mu], l2, N)
    Dg = sum((c[n]*math.log(n)/math.sqrt(n))*Tsh(g, math.log(n)) for n in range(2, N + 1) if c[n] != 0)
    Bg = sum((b[n]/math.sqrt(n))*Tsh(g, math.log(n)) for n in range(2, N + 1) if b[n] != 0)
    S = ip(g, Dg) + ip(g, A2g) - ip(g, Bg)
    # scales
    prime = ip(g, Ag) + ip(g, Asg)
    coef = [(n, round(c[n]*math.log(n) + cc[n] - b[n], 6)) for n in range(2, min(N, 12) + 1)]
    return {"lf": name, "delta": delta, "lam": mp.nstr(lam, 5), "E1_onesided": E1, "E2_mixed": E2,
            "S_selberg_mu": S, "prime_term": prime, "|PAg|^2": ip(Ag, Ag), "coef_defect_n<=12": coef}
for name in sys.argv[1:]:
    print(json.dumps(run(name, 3.427, 80, 600)), flush=True)
