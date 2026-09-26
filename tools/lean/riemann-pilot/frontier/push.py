import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar
exec(open('ceil_lib.py').read())
def trial_UB(a, fam):
    # D(g) = int_0^{2a} (1 - f(u)) K(u) du, pole 2<g,w>^2, prime -sum c f(log n); g normalised
    ts = np.linspace(-a, a, 4001); h = ts[1]-ts[0]
    pr = primes(a)
    def val(p):
        g = fam(ts, p); g = g/np.sqrt((g*g).sum()*h)
        def f(u):
            m = int(round(u/h));
            return (g[:len(g)-m]*g[m:]).sum()*h if m < len(g) else 0.0
        D = quad(lambda u: (1-f(u))*K(u), 0, 2*a, limit=400, points=[a])[0]
        pole = 2*((g*np.exp(-ts/2)).sum()*h)**2
        return D + pole - sum(c*f(np.log(n)) for n,c in pr)
    r = minimize_scalar(val, bounds=(-3, 3), method='bounded')
    return r.fun, r.x
def LB_const(a, N, shift=0.0):
    # Gamma = Gram of (c_k - mean) on I (a-independent after scaling); W from exact psi minus shift
    L = 8*a; om = lambda k: 2*np.pi*k/L
    pr = primes(a)
    def psi(k):
        v = quad(lambda u:(1-np.cos(om(k)*u))*K(u),0,2*a,limit=400)[0] if k>0 else 0.0
        return v - sum(c*np.cos(om(k)*np.log(n)) for n,c in pr) - shift
    ps = np.array([psi(k) for k in range(N+400)]); tau = ps[N+1:].min()
    ts = np.linspace(-a, a, 8001); wts = np.full(ts.size, ts[1]-ts[0]); wts[[0,-1]] /= 2
    E = np.array([(1/np.sqrt(L) if k==0 else np.sqrt(2/L))*np.cos(om(k)*ts) for k in range(N+1)])
    b = (E*wts).sum(1); Gp = (E*wts)@E.T - np.outer(b,b)/(2*a)   # project out constants
    W = np.maximum(tau - ps[:N+1], 0)
    Wh = np.sqrt(W); return tau - np.linalg.eigvalsh(Wh[:,None]*Gp*Wh[None,:])[-1]
fams = {'1+g t^2': lambda t,p: 1 + p*(t/t[-1])**2, 'cosh': lambda t,p: np.cosh(p*t/t[-1])}
for a in [0.35, 0.4, 0.45]:
    T = quad(K, 2*a, np.inf)[0]
    print(f"a={a} true D1={forms(a,400)[0]-C-T:.4f}", {k: "%.4f (p=%.2f)" % trial_UB(a, f) for k,f in fams.items()})
    for N in [10, 12, 15]:
        print("   N=%d LB(const-proj, exact psi)=%.4f  LB(shift .04)=%.4f" % (N, LB_const(a,N), LB_const(a,N,0.04)))
