#!/usr/bin/env python3
"""Round 174 (PREREG_fakezero.md): mirror averages G_b of a fake Xi with a planted off-line quadruple."""
import sys, json, mpmath as mp
mp.mp.dps = 40
def xi(s):
    if mp.re(s) < 0.5: s = 1 - s
    return s*(s - 1)/2*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
Xi = lambda z: xi(mp.mpf(1)/2 + 1j*z)
g1, g2 = mp.zetazero(1).imag, mp.zetazero(2).imag
def make(eta):
    if eta == 0: return Xi
    w = (g1 + g2)/2 + 1j*mp.mpf(eta)
    return lambda z: Xi(z)*(z*z - w*w)*(z*z - mp.conj(w)**2)/((z*z - g1*g1)*(z*z - g2*g2))
def run(b, eta, R=30):
    F = make(eta); b = mp.mpf(b)
    G = lambda z: F(z + 1j*b) + F(z - 1j*b)
    h = mp.mpf(1)/50; ts = [h*k + h/3 for k in range(int(R/h))]
    v = [mp.re(G(t)) for t in ts]; nreal = sum(1 for i in range(len(v) - 1) if v[i]*v[i + 1] < 0)
    tot = mp.mpf(0); th = mp.mpf(0); step = mp.pi/300; fa = G(mp.mpf(R))
    while th < 2*mp.pi:
        nt = min(th + step, 2*mp.pi); fb = G(R*mp.expj(nt)); da = mp.arg(fb/fa)
        if abs(da) > mp.pi/8 and step > mp.mpf(1)/10**6: step /= 2; continue
        tot += da; fa = fb; th = nt; step = min(step*1.5, mp.pi/300)
    nd = float(tot/(2*mp.pi))
    return dict(b=float(b), eta=eta, N_disc=round(nd, 3), N_real=2*nreal, real_rooted=abs(nd - 2*nreal) < 0.25)
b, eta = float(sys.argv[1]), float(sys.argv[2])
print(json.dumps(run(b, eta)), flush=True)
