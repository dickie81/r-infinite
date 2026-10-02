"""Round 122 scoping: the finite relaxation R(g) = 2<g,w>^2 + kappa|g|^2 - sum_{|n|<=N}(tau-psi_n) p_n.
Even sector (w = cosh(t/2)) and odd sector (pole term -2<g, sinh(t/2)>^2, modes sin). Exact psi_n (quadrature) for the
ceiling, and rigorous-style psi_n >= Cin(pi n/2) + a(1 - 2 sin(pi n/2)/(pi n)) - err(a)."""
import numpy as np, mpmath as mp
from scipy.integrate import quad
from scipy.linalg import eigh
c0 = float(mp.re(mp.digamma(0.25)) - mp.log(mp.pi))
K = lambda u: np.exp(u/2)/np.sinh(u)
Far = lambda a: np.log((np.exp(a)+1)/(np.exp(a)-1)) + np.pi/2 - np.arctan(np.sinh(a))
Cin = lambda x: quad(lambda s: (1-np.cos(s))/s if s > 0 else 0.0, 0, x, limit=400)[0]
def psi_exact(a, n): return quad(lambda u: (1-np.cos(np.pi*n*u/(4*a)))*K(u), 0, 2*a, limit=400)[0]
def err(a): return a**2/6 + a**3/3 + a**4/200 + a**5/48
def psi_lb(a, n): return Cin(np.pi*n/2) + a*(1 - 2*np.sin(np.pi*n/2)/(np.pi*n)) - err(a)
def bound(a, N, parity, exact=True, NT=400):
    ps = [0.0] + [(psi_exact if exact else psi_lb)(a, n) for n in range(1, NT)]
    tau = min(ps[N+1:]) if exact else psi_lb(a, N+1) - 0*a   # Cin monotone; lb at N+1 (a-term >=0 dropped conservatively below)
    if not exact: tau = Cin(np.pi*(N+1)/2) - err(a)
    kap = c0 + Far(a) + tau
    t = np.linspace(-a, a, 4001); wq = np.full_like(t, t[1]-t[0]); wq[0] = wq[-1] = wq[0]/2
    if parity == "even":
        V = [np.cosh(t/2)] + [np.cos(np.pi*n*t/(4*a)) for n in range(0, N+1)]
        S = [2.0] + [-(tau-ps[0])/(8*a)] + [-2*(tau-ps[n])/(8*a) for n in range(1, N+1)]
    else:
        V = [np.sinh(t/2)] + [np.sin(np.pi*n*t/(4*a)) for n in range(1, N+1)]
        S = [-2.0] + [-2*(tau-ps[n])/(8*a) for n in range(1, N+1)]
    V = np.array(V); G = (V*wq) @ V.T; S = np.diag(S)
    # min over unit g of kappa + x^T S x with x = V g: = kappa + lambda_min(G^1/2 S G^1/2) (or 0)
    ev, U = np.linalg.eigh(G); ev = np.clip(ev, 0, None); Gh = U @ np.diag(np.sqrt(ev)) @ U.T
    return kap + min(0.0, np.linalg.eigvalsh(Gh @ S @ Gh).min())
for parity in ("even", "odd"):
    print("==", parity)
    for a in (0.0625, 0.08, 0.09, 0.1, 0.12, 0.15, 0.2, 0.25, 0.3):
        row = [f"{bound(a, N, parity, exact=True):+.3f}" for N in (2, 6, 12, 20)]
        rowlb = [f"{bound(a, N, parity, exact=False):+.3f}" for N in (6, 12, 20)]
        print(f"a={a:<6} exact-psi N=2,6,12,20: {row} | rigorous-psi N=6,12,20: {rowlb}")
