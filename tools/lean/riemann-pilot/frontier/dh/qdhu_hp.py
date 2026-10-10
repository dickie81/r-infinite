# High-precision evaluation of QDHu for the box packet g = cos(w u) 1_[-a,a], with closed forms, and the
# error-budget decomposition used by the Lean certificate. Also an independent r-space check of the
# archimedean term via (1/2pi) int ghat(r)^2 Re psi(3/4 + i r/2) dr.
import mpmath as mp, sys
mp.mp.dps = 40
chi = {0: 0, 1: 1, 2: 1j, 3: -1j, 4: -1}
eps = (2*mp.sin(2*mp.pi/5) + 2j*mp.sin(mp.pi/5))/mp.sqrt(5)
def aDH(n):
    z = mp.mpc(chi[n % 5]); return (1+mp.conj(eps))*z + (1+eps)*mp.conj(z)
a1 = aDH(1)
kappa = (aDH(2)/a1).real
kappa_rad = (mp.sqrt(10-2*mp.sqrt(5)) - 2)/(mp.sqrt(5)-1)
N = 700
u = [mp.mpf(0)]*(N+1)
for n in range(2, N+1): u[n] = (aDH(n)/a1).real
dinv = [mp.mpf(0)]*(N+1); dinv[1] = mp.mpf(1)
for n in range(2, N+1): dinv[n] = -sum(u[d]*dinv[n//d] for d in range(2, n+1) if n % d == 0)
lm = lambda n: mp.log(n)*((1 if n == 1 else 0) + u[n])
c = [mp.mpf(0)]*(N+1)
for n in range(1, N+1): c[n] = sum(lm(d)*dinv[n//d] for d in range(1, n+1) if n % d == 0)
print("kappa =", mp.nstr(kappa, 20), " radical form:", mp.nstr(kappa_rad, 20), " diff", mp.nstr(kappa-kappa_rad, 3))
print("max |Im u(n)|:", mp.nstr(max(abs((aDH(n)/a1).imag) for n in range(2, 60)), 3), " u pattern n=1..6:", [mp.nstr(u[n], 8) for n in range(1, 7)], flush=True)
psi34 = mp.digamma(mp.mpf(3)/4)
const = psi34 + mp.log(5) - mp.log(mp.pi)
def analyse(a, w, verbose=True):
    a = mp.mpf(a); w = mp.mpf(w)
    f0 = a + mp.sin(2*w*a)/(2*w)
    beta = mp.cos(2*w*a)/(2*w)
    f = lambda x: mp.mpf(1)/2*(2*a-x)*mp.cos(w*x) + mp.sin(w*(2*a-x))/(2*w) if x < 2*a else mp.mpf(0)
    K = lambda x: mp.exp(-x/2)/mp.sinh(x)
    E_direct = mp.quad(lambda x: (f0 - f(x))*K(x), mp.linspace(0, 2*a, 200)) + f0*mp.quad(K, [2*a, mp.inf])
    G = mp.re(mp.digamma(mp.mpf(3)/4 + 1j*w/2)) - psi34
    R1 = f0*mp.quad(lambda x: K(x)*mp.cos(w*x), [2*a, mp.inf])
    R2 = mp.quad(lambda x: K(x)*x/2*mp.cos(w*x), mp.linspace(0, 2*a, 200))
    R3 = beta*mp.quad(lambda x: K(x)*mp.sin(w*x), mp.linspace(0, 2*a, 200))
    E_decomp = f0*G + R1 + R2 + R3
    h = lambda t: mp.exp(-3*t/4)*(1/(1-mp.exp(-t)) - 1/t) if t > 0 else mp.mpf(1)/2
    H = mp.quad(h, [0, 1, 10, mp.inf]); Hbinet = mp.log(mp.mpf(3)/4) - psi34
    hcos = mp.quad(lambda t: h(t)*mp.cos(w*t/2), mp.linspace(0, 60, 400))
    G_split = mp.log(1 + (2*w/3)**2)/2 + Hbinet - hcos
    ghat = lambda r: mp.sin((r+w)*a)/(r+w) + mp.sin((r-w)*a)/(r-w) if abs(r-w) > 1e-30 and abs(r+w) > 1e-30 else 2*a
    arch_r = mp.quad(lambda r: ghat(r)**2*mp.re(mp.digamma(mp.mpf(3)/4 + 1j*r/2)), [-mp.inf] + mp.linspace(-w-60, w+60, 2400) + [mp.inf])/(2*mp.pi)
    Nmax = int(mp.floor(mp.exp(2*a)))
    S = sum(c[n]/mp.sqrt(n)*f(mp.log(n)) for n in range(2, Nmax+1))
    Q = const*f0 + E_direct - 2*S
    if verbose:
        print(f"\n(a, w) = ({a}, {w}):  f0 = {mp.nstr(f0,12)}  beta = {mp.nstr(beta,8)}  Nmax = {Nmax}")
        print(f"  E direct       = {mp.nstr(E_direct, 12)}")
        print(f"  E decomposed   = {mp.nstr(E_decomp, 12)}   [f0*G = {mp.nstr(f0*G,10)}, R1 = {mp.nstr(R1,6)}, R2 = {mp.nstr(R2,6)}, R3 = {mp.nstr(R3,6)}]")
        print(f"  G = Re psi(3/4+iw/2) - psi(3/4) = {mp.nstr(G, 12)};  split = {mp.nstr(G_split, 12)}  [1/2 log(1+(2w/3)^2) = {mp.nstr(mp.log(1+(2*w/3)**2)/2,10)}, H = {mp.nstr(H,10)} vs Binet {mp.nstr(Hbinet,10)}, int h cos = {mp.nstr(hcos,6)}]")
        print(f"  log|3/4+iw/2| = {mp.nstr(mp.log(abs(mp.mpf(3)/4+1j*w/2)),10)};  Re psi(3/4+iw/2) = {mp.nstr(mp.re(mp.digamma(mp.mpf(3)/4+1j*w/2)),10)}")
        print(f"  r-space (1/2pi)int ghat^2 Re psi = {mp.nstr(arch_r, 10)}  vs psi(3/4) f0 + E = {mp.nstr(psi34*f0 + E_direct, 10)}")
        print(f"  S = {mp.nstr(S, 12)}   2S = {mp.nstr(2*S,10)}")
        print(f"  QDHu = {mp.nstr(Q, 12)}   Q/f0 = {mp.nstr(Q/f0, 8)}")
        print(f"  sum_n |c(n)|/sqrt(n) (n<=Nmax) = {mp.nstr(sum(abs(c[n])/mp.sqrt(n) for n in range(2,Nmax+1)),6)}   max|c(n)| = {mp.nstr(max(abs(c[n]) for n in range(2,Nmax+1)),6)}", flush=True)
    return Q, f0
analyse(2.4, 84.5)
analyse(2.8, 84.75)
print("\nfine scan (closed forms; E by decomposition):", flush=True)
for a in [2.4, 2.5]:
    best = None
    for w in [mp.mpf(84) + mp.mpf(k)/20 for k in range(0, 21)]:
        a_ = mp.mpf(a); f0 = a_ + mp.sin(2*w*a_)/(2*w)
        f = lambda x: mp.mpf(1)/2*(2*a_-x)*mp.cos(w*x) + mp.sin(w*(2*a_-x))/(2*w)
        G = mp.re(mp.digamma(mp.mpf(3)/4 + 1j*w/2)) - psi34
        K = lambda x: mp.exp(-x/2)/mp.sinh(x)
        R = f0*mp.quad(lambda x: K(x)*mp.cos(w*x), [2*a_, mp.inf]) + mp.quad(lambda x: K(x)*(x/2*mp.cos(w*x) + mp.cos(2*w*a_)/(2*w)*mp.sin(w*x)), mp.linspace(0, 2*a_, 120))
        Nmax = int(mp.floor(mp.exp(2*a_)))
        S = sum(c[n]/mp.sqrt(n)*f(mp.log(n)) for n in range(2, Nmax+1))
        Q = const*f0 + f0*G + R - 2*S
        if best is None or Q/f0 < best[1]: best = (w, Q/f0, Q)
        print(f"  a={a} w={mp.nstr(w,6)}: Q/f0 = {mp.nstr(Q/f0, 6)}", flush=True)
    print(f"  best at a={a}: w = {mp.nstr(best[0],6)}, Q/f0 = {mp.nstr(best[1],6)}, Q = {mp.nstr(best[2],6)}", flush=True)
