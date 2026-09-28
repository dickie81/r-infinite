from mpmath import mp, mpf, log, sqrt, psi, pi, mpc, findroot, exp
from sympy import primerange, factorint
mp.dps=30
def ppowers(N):
    out=[]
    for n in range(2,N+1):
        f=factorint(n)
        if len(f)==1: out.append((n,log(list(f)[0])))
    return out
PP=ppowers(3000)
def A(a):
    return 2*sum(L/sqrt(n) for n,L in PP if log(n)<=2*a)
def arch(t): return psi(0,mpc(0.25,t/2)).real-log(pi)
def T1(a):
    Aa=A(a); t=2*pi*exp(Aa)
    return findroot(lambda t: arch(t)-Aa, t)
H0=mpf('3e12')
for a in [1.0,1.25,1.5,1.75,1.9,2.0,2.05,2.1,2.2]:
    t1=T1(a); print(a, float(A(a)), '%.3e'%float(t1), float(H0/t1))
