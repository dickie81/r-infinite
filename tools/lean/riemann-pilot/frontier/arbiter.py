import sys, numpy as np, math
sys.path.insert(0, '../wt-review/tools/research')
from weil_prime_gram import gram, minimiser, rayleigh
exec(open('hrr_test.py').read().split('if __name__')[0])
delta, KB, prec, n = 2.0, 160, 700, 800
a = delta/2
t, g, h, ev = ground_state(a, n)
# exact projection of the step function onto cos(k pi t / a), k < K
lo, hi = t - h/2, t + h/2
c = []
for k in range(KB):
    if k == 0: I = (g*h).sum(); Nk = 2*a
    else:
        w = k*math.pi/a; I = (g*(np.sin(w*hi) - np.sin(w*lo))/w).sum(); Nk = a
    c.append(I/Nk)
c = np.array(c)
captured = (c[0]**2*2*a + (c[1:]**2).sum()*a)/((g*g).sum()*h)
Gm, N, pp = gram(delta, KB, prec)
rq = rayleigh(Gm, N, [float(x) for x in c], prec)
cp, evp = minimiser(Gm, N, prec)
print("step-function state: discrete lambda1 =", ev[0], " norm captured by K cosines =", captured)
print("its TRUE Rayleigh quotient in the paper's Gram:", rq.mid())
print("paper's ground state lambda1 (K=%d):" % KB, evp)
