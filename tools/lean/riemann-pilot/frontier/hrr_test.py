"""Numerical test of the RH chain's hypotheses hRR (real-rootedness of ĝ) and hD (zeros of ĝ
track zeros of Ξ) and hκ (curvature) for ground states of Weil's form Q at support 2a."""
import numpy as np, json, sys
from scipy.integrate import quad
from scipy.linalg import eigh
from scipy.optimize import brentq
from scipy.special import digamma
from sympy import factorint
C = digamma(0.25) - np.log(np.pi)
K = lambda u: 2.0/(np.exp(u/2)-np.exp(-1.5*u))
def vm(n):
    f = factorint(n); return np.log(list(f)[0]) if len(f) == 1 else 0.0
GAM = np.array(json.load(open(sys.argv[1] if len(sys.argv) > 1 else 'zeros6700.json')))
T = GAM[-1]
S2 = (1/GAM**2).sum() + quad(lambda t: np.log(t/(2*np.pi))/(2*np.pi)/t**2, T, np.inf)[0]

def ground_state(a, n):
    h = 2*a/n
    W = np.zeros(n+1)
    for m in range(1, n+1):
        W[m] += quad(lambda u: (u-(m-1)*h)/h*K(u), (m-1)*h, m*h, limit=200)[0]
        if m < n: W[m] += quad(lambda u: ((m+1)*h-u)/h*K(u), m*h, (m+1)*h, limit=200)[0]
    Tt = quad(K, 2*a, np.inf, limit=200)[0]
    E = h*np.eye(n)*(W[1:].sum() + Tt)
    for m in range(1, n):
        Sh = np.eye(n, k=m); E -= h*W[m]*(Sh+Sh.T)/2
    Pm = np.zeros((n, n))
    for N in range(2, int(np.exp(2*a))+1):
        L = vm(N)
        if L == 0: continue
        u = np.log(N); m = int(u//h); fr = u/h - m
        for mm, wt in [(m, 1-fr), (m+1, fr)]:
            if mm < n and wt > 0:
                Sh = np.eye(n, k=mm); Pm += 2*L/np.sqrt(N)*wt*h*(Sh+Sh.T)/2
    t = -a + h*(np.arange(n)+0.5)
    wv = np.array([-2*(np.exp(-(ti+h/2)/2)-np.exp(-(ti-h/2)/2)) for ti in t])
    M = h*np.eye(n); Q = E + C*M - Pm + 2*np.outer(wv, wv)
    R = np.zeros((n, n//2))
    for i in range(n//2): R[i, i] = 1; R[n-1-i, i] = 1
    ev, V = eigh(R.T@Q@R, R.T@M@R)
    g = R@V[:, 0]
    return t, g, h, ev[:3]

def G(z, t, g, chunk=2000):   # ∫ g e^{izt} without the cell sinc factor (zero-free for |z| < 2π/h)
    z = np.atleast_1d(z)
    return np.concatenate([np.exp(1j*np.outer(z[i:i+chunk], t))@g for i in range(0, len(z), chunk)])

def analyse(a, n, Rs=(30, 60, 100)):
    t, g, h, ev = ground_state(a, n)
    if g.sum() < 0: g = -g
    out = {"a": a, "lam": ev.tolist(), "int_g": g.sum()*h}
    # real zeros on (0, R]
    xs = np.linspace(1e-6, max(Rs), 200000)
    Gr = G(xs, t, g).real
    sc = np.where(np.sign(Gr[:-1]) != np.sign(Gr[1:]))[0]
    rz = np.array([brentq(lambda x: G(x, t, g).real[0], xs[i], xs[i+1]) for i in sc])
    out["real_zeros"] = rz[:12].round(4).tolist()
    for R in Rs:
        th = np.linspace(0, 2*np.pi, 400001)
        vals = G(R*np.exp(1j*th), t, g)
        wind = np.round(np.sum(np.diff(np.unwrap(np.angle(vals))))/(2*np.pi))
        out[f"disk{R}"] = (int(wind), 2*int((rz < R).sum()))   # (all zeros, real zeros)
    # hD: match low real zeros to gamma
    k = min(len(rz), 10)
    out["tau_vs_gamma"] = [(round(rz[j], 3), round(GAM[j], 3)) for j in range(k)]
    out["eta_10"] = float(np.abs(rz[:k]**-2 - GAM[:k]**-2).sum())
    # hκ
    kap = ((t**2 + h*h/12)*g).sum()/(2*g.sum())
    out["kappa"] = kap; out["S2"] = S2
    return out
if __name__ == "__main__":
    for a in [float(x) for x in sys.argv[2:]]:
        n = max(300, int(400*a)); n += n % 2
        r = analyse(a, n)
        print(json.dumps(r)); sys.stdout.flush()
