import sys
sys.path.insert(0, "/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research")
import mpmath as mp
import weil_prime_gram as W, weil_prime_gram_odd as WO
tomp = lambda x: mp.mpf(x.mid().str(40, radius=False))
mp.mp.dps = 30
def low(G, N, k):
    D=[1/mp.sqrt(tomp(N[i])) for i in range(k)]
    S=mp.matrix(k,k)
    for i in range(k):
        for j in range(k): S[i,j]=D[i]*tomp(G[i,j])*D[j]
    return min(mp.eigsy(S, eigvals_only=True))
for a in [0.1, 0.15, 0.2, 0.25, 0.3, 0.34]:
    K=40
    Ge,Ne,_=W.gram(2*a,K,200); Go,No,_=WO.gram_odd(2*a,K+1,200)
    le=low(Ge,Ne,K); lo=low(Go,No,K)
    # parabola coefficients: par = C(1 - t^2/a^2) on [-a,a], C^2 = 15/(16a)
    A=mp.mpf(a); C=mp.sqrt(15/(16*A)); c=[]
    for k in range(K):
        w=k*mp.pi/A
        I=mp.quad(lambda t: C*(1-t**2/A**2)*mp.cos(w*t),[-A,A])
        c.append(I/tomp(Ne[k]))
    qp=mp.fsum(c[i]*tomp(Ge[i,j])*c[j] for i in range(K) for j in range(K))
    print(a, 'lam_e', mp.nstr(le,6), 'lam_o', mp.nstr(lo,6), 'Q(par)', mp.nstr(qp,6))
