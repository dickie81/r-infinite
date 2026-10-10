import numpy as np
from scipy.integrate import quad
exec(open('ceil_lib.py').read())
c2 = np.sqrt(2)*np.log(2)
def LB_defect(a, N, exact_cos=False, shift=0.0):
    L = 8*a; om = lambda k: 2*np.pi*k/L; eps = 2*a - np.log(2)
    def psi(k):
        v = quad(lambda u:(1-np.cos(om(k)*u))*K(u),0,2*a,limit=400)[0] if k>0 else 0.0
        if exact_cos: pen = c2*(np.cos(om(k)*np.log(2)) - np.cos(om(k)*2*a))
        else: pen = c2*min(om(k)*eps, 2)
        return v - pen - shift
    ps = np.array([psi(k) for k in range(N+600)]); tau = ps[N+1:].min()
    ts = np.linspace(-a, a, 8001); wts = np.full(ts.size, ts[1]-ts[0]); wts[[0,-1]] /= 2
    E = np.array([(1/np.sqrt(L) if k==0 else np.sqrt(2/L))*np.cos(om(k)*ts) for k in range(N+1)])
    b = (E*wts).sum(1); Gp = (E*wts)@E.T - np.outer(b,b)/(2*a)
    W = np.maximum(tau - ps[:N+1], 0); Wh = np.sqrt(W)
    return tau - np.linalg.eigvalsh(Wh[:,None]*Gp*Wh[None,:])[-1], tau
for a in [0.36, 0.38, 0.40, 0.42]:
    print(a, "defect:", ["N=%d %.4f" % (N, LB_defect(a,N)[0]) for N in [5, 8, 12, 16, 24]])
    print(a, "exactcos(f2a):", ["N=%d %.4f" % (N, LB_defect(a,N,True)[0]) for N in [5, 8, 12, 16, 24]])
