from mpmath import mp, quad, sqrt, log, pi, asin, acosh, mpf
mp.dps=30
def I(x,X):
    f=lambda t: sqrt(X*X-t*t)*log(t)*2*x/(x*x-t*t)
    return quad(f,[0,X/2,X])
def tau(x,X): return -I(x,X)/(pi*sqrt(x*x-X*X))
for X in [mpf(2),mpf(1.5),mpf(3)]:
    for x in [X*1.0001, X*1.5, X*3, X*20]:
        s=sqrt(x*x-X*X)
        # candidate closed forms
        c1 = log((x+s)*X/(2*x)) - x*log(X/2)/s
        c2 = log(X/2)*(1 - x/s) + log((x+s)/(2*x))  # variants
        c3 = -x*log(X/2)/s + log((x+s)/2) 
        print(float(X), float(x/X), tau(x,X), c1, c2, c3)
print('---')
from mpmath import exp
for X in [mpf(2),mpf(1.5),mpf(3),mpf(0.7)]:
    for x in [X*1.2, X*3]:
        s=sqrt(x*x-X*X)
        G=exp(tau(x,X)+x*log(X/2)/s-log(X))
        print(float(X), float(x/X), G, x/(x+s), X*x/(2*(x+s)) )
from mpmath import mp, quad, sqrt, log, pi, inf, mpf
mp.dps=30
X=mpf(2)
t2=lambda x: log(2*x/(x+sqrt(x*x-4)))
print("mass", quad(t2,[2,3,10,inf]), 2*(1-log(2)))
print("moment", quad(lambda x: t2(x)/x**2,[2,3,10,inf]), (log(2)-pi/2+1)/2)
