# Near-positivity constants: Q(g) >= -eps*||g||^2 for every real probe at support a <= a*.
from mpmath import mp, mpf, log, sqrt, exp, pi, psi, mpc, e, log10, sin
from sympy import factorint
mp.dps=50
def pp(N):
    return [(n,log(list(factorint(n))[0])) for n in range(2,N) if len(factorint(n))==1]
PP=pp(200)
H0=mpf('3e12')                      # Platt-Trudgian verification height (lower end, conservative)
astar=log(67)/2-mpf('1e-6')         # just below the prime power 67
twoa=2*astar
A=2*sum(L/sqrt(n) for n,L in PP if log(n)<=twoa)
d=log(67)-twoa                      # gap to next prime power log
# T1: arch(t)=Re psi(1/4+it/2)-log pi >= A for |t|>=T1; arch increasing; check at candidate
T1=2*pi*exp(A)*(1+mpf('1e-6'))
arch=lambda t: psi(0,mpc(mpf(1)/4,t/2)).real-log(pi)
assert arch(T1)>=A
T2=(T1+H0)/2; D=T2-T1
tau=d/2                              # type of w is tau/2 < d  (K-hat support [-tau/2,tau/2])
# choose m near optimum tau*D/(4e), capped
m=int(tau*D/(4*e)); alpha=tau/(4*m)
# c = alpha/I_m, I_m >= int_{|u|<=1} exp(-u^2/5)^{2m} du >= 2*exp(-2m/5)  (crude, rigorous since sin u/u >= exp(-u^2/5) on |u|<=1)
logc=log(alpha)-log(2)+2*m/mpf(5)
# tail: int_{|u|>X} K <= 2 c alpha^{-2m} X^{1-2m}/(2m-1) = (2c/alpha)(alpha X)^{1-2m}/(2m-1)
def logtail(X, strip=False):
    v=log(2)+logc-log(alpha)+(1-2*m)*log(alpha*X)-log(2*m-1)
    return v+(tau/4 if strip else 0)
l1=logtail(D)                       # 1-w on |t|<=T1
l2=logtail(T2,True)                 # |1-w(i/2)|
l3=logtail(H0-T2,True)              # |w| at off-line zeros, |x|>=H0 (+ zero-count factor below)
S=A+mpf('5.4')
Ga=2*(exp(astar)-1)                 # |F(z)F(-z)| <= Ga ||g||^2 on |Im z|<=1/2
E1=l1+log(S)
E2=l2+log(2*Ga)
X3=H0-T2
# zeros in [T,T+1] <= log T + 10 (Trudgian S(T) bound, generous); sum_k (X3+k)^{1-2m} <= X3^{1-2m}(1+X3/(2m-2)); log(T) <= 2 log(X3+T2) absorbed by factor 2
E3=l3+log(Ga)+log(4)+log(2*(log(H0)+10))+log(1+X3/(2*m-2))
print('a* =',astar,' delta* =',twoa)
print('A_a =',A,' T1 =',T1,' D =',D,' d =',d,' m =',m)
for nm,v in [('E1',E1),('E2',E2),('E3',E3)]: print(nm,'log10 <=',v/log(10))
