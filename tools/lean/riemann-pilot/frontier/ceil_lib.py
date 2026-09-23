import numpy as np
from scipy.integrate import quad
from scipy.linalg import eigh
exec(open('gapp.py').read().split('for a in')[0])
def D1_Dp(a):
    T = quad(K, 2*a, np.inf, limit=200)[0]
    l1, lp = forms(a, 500); return l1-C-T, lp-C-T
def primes(a):
    return [(N, 2*vm(N)/np.sqrt(N)) for N in range(2, int(np.exp(2*a))+1) if vm(N)>0 and np.log(N) <= 2*a]
def LB(a, N, Lf=8):
    L = Lf*a; om = lambda k: 2*np.pi*k/L
    pr = primes(a)
    def psi(k):
        v = quad(lambda u:(1-np.cos(om(k)*u))*K(u),0,2*a,limit=400)[0] if k>0 else 0.0
        return v - sum(c*np.cos(om(k)*np.log(n)) for n,c in pr)
    # exact: f(2a)=0 means we may add s*cos(om k 2a) for any s; choose s = -sum c (align with nearest prime)? keep plain
    ks = np.arange(0, N+400)
    ps = np.array([psi(k) for k in ks])
    tau = ps[N+1:].min()
    ts = np.linspace(-a, a, 8001); wts = np.full(ts.size, ts[1]-ts[0]); wts[[0,-1]] /= 2
    E = np.array([(1/np.sqrt(L) if k==0 else np.sqrt(2/L))*np.cos(om(k)*ts) for k in range(N+1)])
    G = (E*wts)@E.T; wv = np.cosh(ts/2); b = (E*wts)@wv; nw = (wv*wts)@wv
    Gp = G - np.outer(b,b)/nw
    d = tau - ps[:N+1]
    ev, U = np.linalg.eigh(Gp); ev = np.maximum(ev, 0); Gh = U@np.diag(np.sqrt(ev))@U.T
    return tau - np.linalg.eigvalsh(Gh@np.diag(d)@Gh)[-1]
def trialUB(a):
    # best over g = cosh(b t) (normalised) and 1+c t^2 via Rayleigh on 2-dim span {1, t^2, t^4}
    return None