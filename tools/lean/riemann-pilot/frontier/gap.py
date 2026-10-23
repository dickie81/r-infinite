# WARNING (round 23): double precision. Weil-form eigenvalues fall below 1e-5 from delta ~ 0.9
# (9.4e-7 at delta = 1, 6.3e-30 at delta = 2), which this discretisation cannot resolve: its
# "ground states" there are wrong states and its low eigenvalues a numerical floor. Use the paper's
# Gram at >= 500 bits (frontier/gap_hp.py, frontier/rerun_paper.py) for delta >~ 0.9.
import numpy as np
from scipy.integrate import quad
from scipy.linalg import eigh
from scipy.special import digamma
C = digamma(0.25) - np.log(np.pi)
K = lambda u: 2.0/(np.exp(u/2)-np.exp(-1.5*u))
def forms(a, n):
    h = 2*a/n
    # W_m = int hat_m K over [0,2a], m=1..n (last is half hat)
    W = np.zeros(n+1)
    for m in range(1, n+1):
        lo, hi = (m-1)*h, min((m+1)*h, 2*a)
        f1 = lambda u: (u-(m-1)*h)/h*K(u)
        W[m] += quad(f1, (m-1)*h, m*h, limit=200)[0] if m>1 else quad(lambda u:(u/h)*K(u) if u>0 else 1/h, 0, h, limit=200)[0]
        if m < n:
            W[m] += quad(lambda u: ((m+1)*h-u)/h*K(u), m*h, (m+1)*h, limit=200)[0]
    T = quad(K, 2*a, np.inf, limit=200)[0]
    # E(g) = sum_m (f0 - f_m) W_m + f0 T, f_m = h sum_i g_i g_{i+m}
    N = n
    E = np.zeros((N,N))
    E += h*np.eye(N)*(W[1:].sum() + T)
    for m in range(1, n):
        S = np.eye(N, k=m); E -= h*W[m]*(S+S.T)/2
    t = -a + h*(np.arange(N)+0.5)
    # exact w cell integrals
    wv = np.array([ -2*(np.exp(-(ti+h/2)/2)-np.exp(-(ti-h/2)/2)) for ti in t])
    M = h*np.eye(N)
    Q0 = E + C*M
    P = 2*np.outer(wv, wv)
    # even subspace
    R = np.zeros((N, N//2))
    for i in range(N//2): R[i,i]=1; R[N-1-i,i]=1
    Q0e, Pe, Me, we = R.T@Q0@R, R.T@P@R, R.T@M@R, R.T@wv
    lam1 = eigh(Q0e+Pe, Me, eigvals_only=True)[0]
    ev0 = eigh(Q0e, Me, eigvals_only=True)
    # restrict Q0 to w-perp (w-perp in L2 sense: <g,w> = sum g_i wv_i)
    Z = np.linalg.svd(we[None,:])[2][1:].T
    lamp = eigh(Z.T@Q0e@Z, Z.T@Me@Z, eigvals_only=True)[0]
    return lam1, lamp, ev0[0], ev0[1]
for a in [0.025, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.3466, 0.35]:
    for n in [200, 400]:
        l1, lp, m0, m1 = forms(a, n)
        print(f"a={a:.4f} n={n} lam1={l1:.5f} lamperp={lp:.5f} gap={lp-l1:.5f}  mu0={m0:.5f} mu1={m1:.5f}")
