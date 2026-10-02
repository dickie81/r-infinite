"""Evaluate Weil's u-space form for the Davenport-Heilbronn function, `QDHu` of src/DHBridge.lean (round 258),

  Q_dh(g) = (Re psi(3/4) + log(5/pi)) ||g||^2 + int_0^inf [f(0) - f(u)] e^{-u/2}/sinh u du - 2 sum_n c(n) n^{-1/2} f(log n),

f = autocorr g, c(n) the coefficients of -dh'/dh built exactly as `cDH chi5` (src/DHPrime.lean): a(n) =
(1 + conj eps) chi5(n) + (1 + eps) conj chi5(n), u = a/a(1) on n >= 2, dinv the Dirichlet inverse of delta + u,
c = logMul(delta + u) * dinv. Two scans (round 258 numerics): monotone profiles, which stay positive, and box
wave packets cos(omega u) 1_[-a,a], which go negative once detuned from the first off-line ordinate 85.70.
Numerical, not verified: the autocorrelation and the archimedean integral are trapezoid sums on a grid of
step a/M (M = 4000 a), the tail int_{2a}^inf by mpmath. Runtime about ten minutes."""
import numpy as np, math, mpmath as mp
mp.mp.dps = 25
chi = {0: 0, 1: 1, 2: 1j, 3: -1j, 4: -1}          # chi5(2) = i
eps = complex((2*mp.sin(2*mp.pi/5) + 2j*mp.sin(mp.pi/5))/mp.sqrt(5))   # rootNumber_chi5_eq
def aDH(n):
    z = chi[n % 5]; return (1+eps.conjugate())*z + (1+eps)*z.conjugate()
a1 = aDH(1).real
N = 1200
u = np.zeros(N+1, dtype=complex)
for n in range(2, N+1): u[n] = aDH(n)/a1
dinv = np.zeros(N+1, dtype=complex); dinv[1] = 1
for n in range(2, N+1):
    dinv[n] = -sum(u[d]*dinv[n//d] for d in range(2, n+1) if n % d == 0)
lm = lambda n: math.log(n)*((1 if n == 1 else 0) + u[n])
c = np.array([0.0] + [sum(lm(d)*dinv[n//d] for d in range(1, n+1) if n % d == 0).real for n in range(1, N+1)])
const = float(mp.digamma(mp.mpf(3)/4) + mp.log(5) - mp.log(mp.pi))
def Q(gfun, a, M=None):
    """(Q_dh(g)/||g||^2, E/||g||^2, 2S/||g||^2) for an even g supported in [-a, a]."""
    M = M or int(4000*a)
    t = np.linspace(-a, a, 2*M+1); dt = t[1]-t[0]
    g = np.array([gfun(x) for x in t])
    f = np.array([np.dot(g[:2*M+1-k], g[k:]) for k in range(2*M+1)])*dt
    f0 = f[0]; ug = np.arange(2*M+1)*dt
    integrand = np.empty_like(ug)
    integrand[1:] = (f0 - f[1:])*np.exp(-ug[1:]/2)/np.sinh(ug[1:])
    integrand[0] = -(f[1]-f0)/dt
    E = np.trapezoid(integrand, ug) + f0*float(mp.quad(lambda x: mp.exp(-x/2)/mp.sinh(x), [2*a, mp.inf]))
    S = 0.0; n = 2
    while math.log(n) <= 2*a:
        S += c[n]/math.sqrt(n)*np.interp(math.log(n), ug, f); n += 1
    return (const*f0 + E - 2*S)/f0, E/f0, 2*S/f0
if __name__ == '__main__':
    print(f"a(1) = {a1:.6f}, c(2..8) = {[round(float(x), 6) for x in c[2:9]]}, Re psi(3/4) + log(5/pi) = {const:.6f}")
    fams = {
     'box':     lambda a: (lambda x: 1.0 if abs(x) <= a else 0.0),
     'hat':     lambda a: (lambda x: max(a-abs(x), 0.0)),
     'hat^0.5': lambda a: (lambda x: max(a-abs(x), 0.0)**0.5),
     'hat^1.5': lambda a: (lambda x: max(a-abs(x), 0.0)**1.5),
     'trap.5':  lambda a: (lambda x: min(1.0, max(a-abs(x), 0.0)/(0.5*a))),
     'cos':     lambda a: (lambda x: math.cos(math.pi*x/(2*a)) if abs(x) <= a else 0.0),
     'cos+1':   lambda a: (lambda x: 1+math.cos(math.pi*x/a) if abs(x) <= a else 0.0),
     'gauss':   lambda a: (lambda x: math.exp(-(x/(a/2))**2) - math.exp(-4) if abs(x) <= a else 0.0),
    }
    As = [1.8, 2.0, 2.2, 2.4, 2.6, 2.8, 3.0, 3.4]
    print("\nMonotone profiles, Q_dh(g)/||g||^2:")
    print("family   " + "  ".join(f"a={a:<5}" for a in As))
    for name, fam in fams.items():
        print(f"{name:8s} " + "  ".join(f"{Q(fam(a), a)[0]:+.4f}" for a in As), flush=True)
    print("\nBox wave packets g(u) = cos(omega u) 1_[-a,a], minimum over omega in [80, 90] step 0.25:")
    for a in [2.2, 2.4, 2.6, 2.8, 3.0, 3.2]:
        best = min(((w,) + Q(lambda x, w=w: math.cos(w*x) if abs(x) <= a else 0.0, a) for w in np.arange(80.0, 90.01, 0.25)), key=lambda r: r[1])
        print(f"a={a}: min Q/||g||^2 = {best[1]:+.4f} at omega = {best[0]:.2f}  (E/||g||^2 = {best[2]:+.4f}, 2S/||g||^2 = {best[3]:+.4f}; prime terms n <= {int(math.exp(2*a))})", flush=True)
