import sys, math, json, numpy as np
sys.path.insert(0, '.')
import dh_gram as D
from flint import arb
NMAX = 10
def cvec(a):
    c = np.zeros(NMAX + 1); acc = np.array([a[n]*math.log(n) if n >= 1 else 0.0 for n in range(NMAX + 1)])
    for d in range(2, NMAX + 1):
        c[d] = acc[d]
        if c[d] != 0.0:
            for m in range(2, NMAX//d + 1): acc[d*m] -= c[d]*a[m]
    return c
kap = (math.sqrt(10 - 2*math.sqrt(5)) - 2)/(math.sqrt(5) - 1)
chi5 = {1: 1, 2: 1j, 4: -1, 3: -1j}
def lf(name, N):
    if name == 'zeta':
        a = np.ones(N + 1); a[0] = 0
        z0, logq, pole = 0.25, -arb.pi().log(), True
    else:
        a = np.array([0.0] + [0.0 if n % 5 == 0 else ((1 - 1j*kap)*chi5[n % 5]).real for n in range(1, N + 1)])
        z0, logq, pole = 0.75, (arb(5)/arb.pi()).log(), False
    return a, z0, logq, pole
from flint import ctx
def cvec_arb(name, N, prec):
    with ctx.workprec(prec + 40):
        if name == 'zeta':
            a = [arb(0)] + [arb(1)]*N
        else:
            k = ((10 - 2*arb(5).sqrt()).sqrt() - 2)/(arb(5).sqrt() - 1)
            tab = {0: arb(0), 1: arb(1), 2: k, 3: -k, 4: arb(-1)}
            a = [arb(0)] + [tab[n % 5] for n in range(1, N + 1)]
        acc = [a[n]*arb(n).log() if n >= 1 else arb(0) for n in range(N + 1)]
        c = [arb(0)]*(N + 1)
        for d in range(2, N + 1):
            c[d] = acc[d]
            for m in range(2, N//d + 1): acc[d*m] -= c[d]*a[m]
        return c
