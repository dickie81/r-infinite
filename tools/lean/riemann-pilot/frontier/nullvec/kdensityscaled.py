#!/usr/bin/env python3
"""Round 172 (PREREG_densityscaled.md): G_B(z) = int K(v) e^{izv} dv, grids rescaled to density rho_d = S_{d-1}/S_{d-2}."""
import sys, json, mpmath as mp
mp.mp.dps = 50
def Phi(u):
    u = abs(u)
    return mp.fsum((2*mp.pi**2*n**4*mp.exp(4.5*u) - 3*mp.pi*n**2*mp.exp(2.5*u))*mp.exp(-mp.pi*n*n*mp.exp(2*u)) for n in range(1, 8))
S = lambda d: 2*mp.pi**(mp.mpf(d)/2)/mp.gamma(mp.mpf(d)/2)   # S(d) = area of the unit sphere S^{d-1}
D = 200
terms = []
for d in range(2, D + 1):
    rho = S(d)/S(d - 1)                     # rho_d = S_{d-1}/S_{d-2}
    terms.append((S(d)*mp.sqrt(rho), 2*mp.log(rho)/d, mp.mpf(d - 2)/4))
# Xi = 4 int_0^inf Phi cos  =>  Xi(z) = 2 int_R Phi(|u|) e^{izu} du ; pair = 4 int Phi(|u|) cosh(bu) e^{izu} du
def K(v): return 4*mp.fsum(w*Phi(v - c)*mp.cosh(b*(v - c)) for w, c, b in terms)
xs, ws = mp.gauss_quadrature(800, 'legendre')
NV = [4*x for x in xs]; NW = [4*w for w in ws]; KV = [K(v)*w for v, w in zip(NV, NW)]
def G(z): return mp.fsum(k*mp.expj(z*v) for k, v in zip(KV, NV))
def xi(s): return s*(s - 1)/2*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
Xi = lambda z: xi(mp.mpf(1)/2 + 1j*z)
def Gdirect(z):
    return mp.fsum(w*mp.expj(c*z)*(Xi(z + 1j*b) + Xi(z - 1j*b)) for w, c, b in terms)
mode = sys.argv[1]
if mode == 'validate':
    for z in (mp.mpf(3), mp.mpc(17.5, 2)):
        a, b = G(z), Gdirect(z); print(z, mp.nstr(a, 12), mp.nstr(b, 12), mp.nstr(abs(a/b - 1), 3))
elif mode == 'disc':
    R = mp.mpf(40); tot = mp.mpf(0); th = mp.mpf(0); step = mp.pi/400; fa = G(R)
    while th < 2*mp.pi:
        nt = min(th + step, 2*mp.pi); fb = G(R*mp.expj(nt)); da = mp.arg(fb/fa)
        if abs(da) > mp.pi/8 and step > mp.mpf(1)/10**6: step /= 2; continue
        tot += da; fa = fb; th = nt; step = min(step*1.5, mp.pi/400)
    print(json.dumps(dict(R=40, N_disc=float(tot/(2*mp.pi)))))
elif mode == 'locate':
    mp.mp.dps = 40
    h = mp.mpf(1)/4; X = [h*i for i in range(-160, 161)]; Y = [h*j for j in range(-48, 49)]
    A = [[abs(G(mp.mpc(x, y))) for x in X] for y in Y]
    cand = []
    for j in range(1, len(Y) - 1):
        for i in range(1, len(X) - 1):
            a = A[j][i]
            if all(a <= A[j + dj][i + di] for dj in (-1, 0, 1) for di in (-1, 0, 1)): cand.append(mp.mpc(X[i], Y[j]))
    zs = []
    for c in cand:
        try:
            r = mp.findroot(G, c, tol=mp.mpf(10)**-25)
            if abs(r) < 40 and abs(G(r)) < mp.mpf(10)**-15 and all(abs(r - q) > 1e-6 for q in zs): zs.append(r)
        except Exception: pass
    zs.sort(key=lambda r: float(mp.re(r)))
    print(json.dumps(dict(n_located=len(zs), zeros=[[round(float(mp.re(r)), 5), round(float(mp.im(r)), 6)] for r in zs])))
