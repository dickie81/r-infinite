import numpy as np
from scipy.integrate import quad
exec(open('ceil_lib.py').read())
def variants(a, N):
    L = 8*a; om = lambda k: 2*np.pi*k/L
    pr = primes(a)
    def psi(k):
        v = quad(lambda u:(1-np.cos(om(k)*u))*K(u),0,2*a,limit=400)[0] if k>0 else 0.0
        return v - sum(c*np.cos(om(k)*np.log(n)) for n,c in pr)
    ps = np.array([psi(k) for k in range(N+400)]); tau = ps[N+1:].min()
    ts = np.linspace(-a, a, 8001); wts = np.full(ts.size, ts[1]-ts[0]); wts[[0,-1]] /= 2
    E = np.array([(1/np.sqrt(L) if k==0 else np.sqrt(2/L))*np.cos(om(k)*ts) for k in range(N+1)])
    G = (E*wts)@E.T; wv = np.cosh(ts/2); b = (E*wts)@wv; nw = (wv*wts)@wv
    Gp = G - np.outer(b,b)/nw
    W = np.maximum(tau - ps[:N+1], 0); cap = np.diag(Gp)
    diag = tau - (W*cap).sum()
    best = diag
    for Wm in np.linspace(0, W.max(), 2000):
        best = max(best, tau - (Wm*1 + (np.maximum(W - Wm, 0)*cap).sum()))
    ev, U = np.linalg.eigh(Gp); Gh = U@np.diag(np.sqrt(np.maximum(ev,0)))@U.T
    eig = tau - np.linalg.eigvalsh(Gh@np.diag(tau-ps[:N+1])@Gh)[-1]
    return diag, best, eig
for a in [0.35, 0.4, 0.45]:
    for N in [5, 8, 10, 15, 20]:
        print(a, N, ["%.4f" % v for v in variants(a, N)])
