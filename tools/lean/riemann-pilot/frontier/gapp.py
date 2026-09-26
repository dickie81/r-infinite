# WARNING (round 23): double precision. Weil-form eigenvalues fall below 1e-5 from delta ~ 0.9
# (9.4e-7 at delta = 1, 6.3e-30 at delta = 2), which this discretisation cannot resolve: its
# "ground states" there are wrong states and its low eigenvalues a numerical floor. Use the paper's
# Gram at >= 500 bits (frontier/gap_hp.py, frontier/rerun_paper.py) for delta >~ 0.9.
import numpy as np
from scipy.integrate import quad
from scipy.linalg import eigh
from scipy.special import digamma
from sympy import factorint
C = digamma(0.25) - np.log(np.pi)
K = lambda u: 2.0/(np.exp(u/2)-np.exp(-1.5*u))
def vm(n):
    f = factorint(n)
    return np.log(list(f)[0]) if len(f)==1 else 0.0
def forms(a, n):
    h = 2*a/n
    W = np.zeros(n+1)
    for m in range(1, n+1):
        W[m] += quad(lambda u: (u-(m-1)*h)/h*K(u), (m-1)*h, m*h, limit=200)[0]
        if m < n: W[m] += quad(lambda u: ((m+1)*h-u)/h*K(u), m*h, (m+1)*h, limit=200)[0]
    T = quad(K, 2*a, np.inf, limit=200)[0]
    E = h*np.eye(n)*(W[1:].sum() + T)
    for m in range(1, n):
        S = np.eye(n, k=m); E -= h*W[m]*(S+S.T)/2
    # primes: -2 sum Lambda(p)/sqrt p f(log p), f(u) linear interp of f(mh)
    Pm = np.zeros((n,n))
    for N in range(2, int(np.exp(2*a))+1):
        L = vm(N)
        if L == 0: continue
        u = np.log(N); m = int(u//h); fr = u/h - m
        for mm, wt in [(m, 1-fr), (m+1, fr)]:
            if mm < n and wt > 0:
                S = np.eye(n, k=mm); Pm += 2*L/np.sqrt(N)*wt*h*(S+S.T)/2
    t = -a + h*(np.arange(n)+0.5)
    wv = np.array([-2*(np.exp(-(ti+h/2)/2)-np.exp(-(ti-h/2)/2)) for ti in t])
    M = h*np.eye(n); Q0 = E + C*M - Pm; P = 2*np.outer(wv, wv)
    R = np.zeros((n, n//2))
    for i in range(n//2): R[i,i]=1; R[n-1-i,i]=1
    Q0e, Pe, Me, we = R.T@Q0@R, R.T@P@R, R.T@M@R, R.T@wv
    lam1 = eigh(Q0e+Pe, Me, eigvals_only=True)[0]
    Z = np.linalg.svd(we[None,:])[2][1:].T
    lamp = eigh(Z.T@Q0e@Z, Z.T@Me@Z, eigvals_only=True)[0]
    return lam1, lamp
for a in [0.35, 0.4, 0.45, 0.5, 0.55, 0.6, 0.65, 0.69, 0.75, 0.8, 1.0]:
    l1, lp = forms(a, 600)
    print(f"a={a} delta={2*a:.2f} lam1={l1:.5f} lamperp={lp:.5f} gap={lp-l1:.5f}")
