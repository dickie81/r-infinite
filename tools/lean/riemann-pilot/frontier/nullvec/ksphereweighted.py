#!/usr/bin/env python3
"""Round 171 (PREREG_sphereweighted.md): G(z) = sum_d S_{d-1}[Xi(z+ib_d)+Xi(z-ib_d)], b_d=(d-2)/4,
   = 4 int_0^inf Phi(u) W(u) cos(zu) du.  Usage: ksphereweighted.py {validate|real|disc}"""
import sys, json, mpmath as mp
mp.mp.dps = 50
def Phi(u):
    return mp.fsum((2*mp.pi**2*n**4*mp.exp(4.5*u) - 3*mp.pi*n**2*mp.exp(2.5*u))*mp.exp(-mp.pi*n*n*mp.exp(2*u)) for n in range(1, 8))
def f(x): return x/mp.sqrt(mp.pi) + x*x*mp.exp(x*x)*(1 + mp.erf(x))
def W(u): return mp.exp(-u/2)*f(mp.sqrt(mp.pi)*mp.exp(u/4)) + mp.exp(u/2)*f(mp.sqrt(mp.pi)*mp.exp(-u/4))
S = lambda d: 2*mp.pi**(mp.mpf(d)/2)/mp.gamma(mp.mpf(d)/2)
NODES = [mp.mpf(k)/8 for k in range(0, 25)]
def G(z): return 8*mp.quad(lambda u: Phi(u)*W(u)*mp.cos(z*u), NODES)
def xi(s): return s*(s - 1)/2*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
def Gdirect(t, D=200):
    return mp.fsum(S(d)*2*mp.re(xi(mp.mpf(1)/2 + abs(mp.mpf(d - 2)/4) + 1j*t)) for d in range(1, D + 1))
mode = sys.argv[1]
if mode == 'validate':
    for u in (0, 0.5, 1, 2):
        u = mp.mpf(u); ws = mp.fsum(S(d)*mp.cosh(mp.mpf(d - 2)/4*u) for d in range(1, 201))
        print('W', u, mp.nstr(abs(W(u)/ws - 1), 3))
    for t in (3, 17.5):
        a, b = G(mp.mpf(t)), Gdirect(mp.mpf(t)); print('G', t, mp.nstr(a, 15), mp.nstr(b, 15), mp.nstr(abs(a/b - 1), 3))
    # also check Xi normalisation: 2 int Phi cos = Xi(t)
    t = mp.mpf(3); X = 4*mp.quad(lambda u: Phi(u)*mp.cos(t*u), NODES); print('Xi check', mp.nstr(abs(X/xi(mp.mpf(1)/2 + 1j*t) - 1), 3))
elif mode == 'real':
    mp.mp.dps = 40; R = 40; h = mp.mpf(1)/50
    ts = [h*k for k in range(0, int(R/h) + 1)]; vals = [G(t) for t in ts]
    zs = []
    for i in range(len(ts) - 1):
        if vals[i]*vals[i + 1] < 0: zs.append(float(mp.findroot(G, (ts[i], ts[i + 1]), solver='anderson')))
    print(json.dumps(dict(R=R, n_real=len(zs), zeros=[round(z, 4) for z in zs], G0=float(vals[0]))))
elif mode == 'disc':
    R = mp.mpf(40); tot = mp.mpf(0); th = mp.mpf(0); step = mp.pi/400
    fa = G(R); 
    while th < 2*mp.pi:
        nt = min(th + step, 2*mp.pi); fb = G(R*mp.expj(nt)); da = mp.arg(fb/fa)
        if abs(da) > mp.pi/8 and step > mp.mpf(1)/10**6: step /= 2; continue
        tot += da; fa = fb; th = nt; step = min(step*1.5, mp.pi/400)
    print(json.dumps(dict(R=float(R), N_disc=float(tot/(2*mp.pi)))))
