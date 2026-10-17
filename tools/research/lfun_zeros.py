#!/usr/bin/env python3
"""Zero lists for the cross-L-function test (Theorem 1bq): the positive
ordinates of the zeros of L(s, chi_D) for the real primitive characters
D = -3, -4, 8 and of L(Delta, s) (weight 12, level 1) on the critical line,
by sign changes of the real function Z(t) = e^{i theta(t)} L(1/2 + it) (the
completed function divided by the modulus of its Gamma factor -- the Hardy
Z-function of the form; root number +1 for all four), refined by bisection,
with THREE CHECKS: the count against the smooth count of the argument
principle (S(T) small at these heights),
  Dirichlet:  N(T) ~ (T/2pi) ln(q T/(2 pi e)) + kappa/4 - 1/8,
  Delta:      N(T) ~ (T/pi) ln(T/(2 pi e)) + 11/4,
(theta(T)/pi with Im ln Gamma(sigma + it) ~ t ln t - t + (sigma - 1/2) pi/2 at
sigma = (1/2 + kappa)/2 and at sigma = 6; no +1: these forms have no pole)
a second scan at half the step (every zero found twice, none new), and for
the Dirichlet forms the reality of Z (the imaginary part below 1e-8 of the
modulus at every scan point -- a check of the Gamma factor and the
functional equation's phase).

EVALUATION. Dirichlet: L(s, chi) = q^{-s} sum_a chi(a) zeta(s, a/q) with the
Hurwitz zeta by Euler-Maclaurin (N = |t| + 40 direct terms, 24 Bernoulli
terms; remainder ~ (|s|/2 pi N)^{48}), vectorised over the scan in double
precision -- adequate because |Z| = O(1). Delta: Lambda(s) = 2 Re sum_n
tau(n) (2 pi n)^{-s} Gamma(s, 2 pi n) on s = 6 + it (the terms with n > 60
are below e^{-377}), the incomplete gamma by the power series of gamma(s, x)
for x < 0.8 |s| and by the Legendre continued fraction (modified Lentz) for
x >= 0.8 |s|, in mpmath at dps = 40 + 0.7 t (Lambda is e^{-pi t/2} times an
O(1) function and the series cancel to that: the working precision carries
the cancellation), then Z = Lambda (2 pi)^6 / |Gamma(6 + it)|. The
incomplete gamma is validated against mpmath.gammainc at four points.

The lists are DATA for the verifier's live gates (like zeta_zeros_6700.json):
tools/research/checkpoints/lfun_zeros_<name>.json = {"name", "q", "d",
"kappas", "T", "step", "zeros", "count", "smooth_count", "half_step_agrees",
"phase_check"}. Usage: lfun_zeros.py <chi_-3|chi_-4|chi_8|Delta> <Tmax> [step]
"""
import sys, os, json, math, time
import numpy as np
from scipy.special import loggamma

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "checkpoints")

def kronecker(D, n):
    if n == 1: return 1
    res = 1; m = n
    while m % 2 == 0:
        m //= 2
        if D % 2 == 0: return 0
        res *= 1 if D % 8 in (1, 7) else -1
    p = 3
    while p*p <= m:
        while m % p == 0:
            m //= p
            res *= legendre(D, p)
        p += 2
    if m > 1: res *= legendre(D, m)
    return res

def legendre(a, p):
    a %= p
    if a == 0: return 0
    r = pow(a, (p - 1)//2, p)
    return 1 if r == 1 else -1

def tau_list(N):
    N += 1
    poly = [0]*N; poly[0] = 1
    for n in range(1, N):
        for _ in range(24):
            for i in range(N - 1, n - 1, -1):
                poly[i] -= poly[i - n]
    return [0] + poly[:N - 1]

# ---------------------------------------------------------------- Dirichlet (numpy)
def _bernoulli_over_factorial(M):
    import mpmath as mp
    return [float(mp.bernoulli(2*k)/mp.factorial(2*k)) for k in range(1, M + 1)]
_BF = _bernoulli_over_factorial(24)

def hurwitz_em(s, a, N):
    """zeta(s, a) for an array of complex s (Euler-Maclaurin, N direct terms, 24 Bernoulli terms):
    sum_{n<N} (n+a)^{-s} + x^{1-s}/(s-1) + x^{-s}/2 + sum_k B_{2k}/(2k)! (s)_{2k-1} x^{-s-2k+1}, x = N + a."""
    s = np.asarray(s, dtype=complex)
    n = np.arange(N, dtype=float) + a
    direct = np.sum(np.exp(-np.multiply.outer(s, np.log(n))), axis=1)
    x = N + a
    tail = x**(1 - s)/(s - 1) + 0.5*x**(-s)
    poch = s.copy(); term = x**(-s - 1)         # (s)_1 x^{-s-1} at k = 1
    for k in range(1, 25):
        if k > 1:
            poch = poch*(s + 2*k - 3)*(s + 2*k - 2); term = term/(x*x)
        tail = tail + _BF[k - 1]*poch*term
    return direct + tail

def Z_dirichlet(D, t):
    """Z(t) = Re[e^{i theta} L(1/2 + it, chi_D)] on an array t; returns (Z, max |Im|/|L|)."""
    q = abs(D); kap = 0 if D > 0 else 1
    t = np.asarray(t, dtype=float); s = 0.5 + 1j*t
    N = int(np.max(np.abs(t))) + 40
    L = np.zeros_like(s)
    for a in range(1, q):
        ch = kronecker(D, a)
        if ch: L += ch*hurwitz_em(s, a/q, N)
    L *= np.exp(-s*math.log(q))
    phase = (t/2)*math.log(q/math.pi) + np.imag(loggamma((s + kap)/2))
    W = np.exp(1j*phase)*L
    return np.real(W), float(np.max(np.abs(np.imag(W))/np.maximum(np.abs(W), 1e-300)))

# ---------------------------------------------------------------- Delta (mpmath, own incomplete gamma)
def gamma_inc_upper(s, x, mp):
    """Gamma(s, x) for complex s, real x > 0: the series of gamma(s, x) for x < 0.8|s|, else the Legendre continued fraction."""
    if x < 0.8*abs(s):
        # gamma(s, x) = x^s e^{-x} sum_k x^k / (s (s+1) ... (s+k))
        term = 1/s; tot = term; k = 0
        while True:
            k += 1; term = term*x/(s + k); tot += term
            if abs(term) < abs(tot)*mp.mpf(10)**(-mp.mp.dps) and k > 5: break
        return mp.gamma(s) - mp.exp(s*mp.log(x) - x)*tot
    # Gamma(s, x) = e^{-x} x^s / (x + 1 - s - 1(1-s)/(x + 3 - s - 2(2-s)/(x + 5 - s - ...)))   (modified Lentz)
    tiny = mp.mpf(10)**(-mp.mp.dps - 20)
    b = x + 1 - s; f = b if b != 0 else tiny; C = f; Dd = mp.mpf(0)
    for i in range(1, 100000):
        an = -i*(i - s); b = b + 2
        Dd = b + an*Dd; Dd = tiny if Dd == 0 else Dd; Dd = 1/Dd
        C = b + an/C; C = tiny if C == 0 else C
        delta = C*Dd; f = f*delta
        if abs(delta - 1) < mp.mpf(10)**(-mp.mp.dps): break
    return mp.exp(s*mp.log(x) - x)/f

def make_Z_delta(mp, nterms=60):
    tau = tau_list(nterms)
    def Z(t):
        t = mp.mpf(t); s = mp.mpc(6, t)
        tot = mp.mpc(0)
        for n in range(1, nterms):
            x = 2*mp.pi*n
            tot += tau[n]*mp.exp(-s*mp.log(x))*gamma_inc_upper(s, x, mp)
        lam = 2*mp.re(tot)
        return lam*(2*mp.pi)**6/abs(mp.gamma(s))
    return Z

# ---------------------------------------------------------------- the scan
def scan_array(tgrid, Zvals, Zfun, bisect=48):
    zs = []
    for i in range(len(tgrid) - 1):
        if Zvals[i]*Zvals[i + 1] < 0:
            lo, hi = float(tgrid[i]), float(tgrid[i + 1]); flo = float(Zvals[i])
            for _ in range(bisect):
                mid = (lo + hi)/2; fm = float(Zfun(mid))
                if flo*fm < 0: hi = mid
                else: lo = mid; flo = fm
            zs.append((lo + hi)/2)
    return zs

if __name__ == "__main__":
    name = sys.argv[1]; Tmax = float(sys.argv[2])
    step = float(sys.argv[3]) if len(sys.argv) > 3 else 0.05
    t0 = time.time()
    if name == "Delta":
        import mpmath as mp
        mp.mp.dps = int(40 + 0.7*Tmax)
        # validation of the incomplete gamma against mpmath at four points
        val = []
        for s, x in ((mp.mpc(6, 10), mp.mpf(4)), (mp.mpc(6, 30), mp.mpf(20)), (mp.mpc(6, 50), mp.mpf(60)), (mp.mpc(6, 20), mp.mpf(30))):
            mine = gamma_inc_upper(s, x, mp); ref = mp.gammainc(s, x)
            val.append(float(abs(mine - ref)/abs(ref)))
        assert max(val) < 1e-25, val
        Zf = make_Z_delta(mp)
        grid1 = np.arange(step, Tmax + step/2, step); Z1 = np.array([float(Zf(t)) for t in grid1])
        grid2 = np.arange(step/2, Tmax + step/4, step/2); Z2 = np.array([float(Zf(t)) for t in grid2])
        z1 = scan_array(grid1, Z1, Zf); z2 = scan_array(grid2, Z2, Zf)
        smooth = lambda T: T/math.pi*math.log(T/(2*math.pi*math.e)) + 11/4
        meta = dict(q=1, d=2, kappas=[5.5, 6.5]); phase_check = None; gval = max(val)
    else:
        D = int(name.split("_")[1]); q = abs(D); kap = 0 if D > 0 else 1
        grid1 = np.arange(step, Tmax + step/2, step); Z1, ph1 = Z_dirichlet(D, grid1)
        grid2 = np.arange(step/2, Tmax + step/4, step/2); Z2, ph2 = Z_dirichlet(D, grid2)
        Zf = lambda t: Z_dirichlet(D, [t])[0][0]
        z1 = scan_array(grid1, Z1, Zf); z2 = scan_array(grid2, Z2, Zf)
        smooth = lambda T: T/(2*math.pi)*math.log(q*T/(2*math.pi*math.e)) + kap/4 - 1/8
        meta = dict(q=q, d=1, kappas=[kap]); phase_check = max(ph1, ph2); gval = None
        assert phase_check < 1e-8, phase_check
    same = len(z1) == len(z2) and all(abs(a - b) < 1e-9 for a, b in zip(z1, z2))
    out = dict(name=name, **meta, T=Tmax, step=step, zeros=z2, count=len(z2), smooth_count=float(smooth(z2[-1])),
               half_step_agrees=same, phase_check=phase_check, gammainc_check=gval, seconds=time.time() - t0)
    os.makedirs(OUT, exist_ok=True)
    json.dump(out, open(os.path.join(OUT, f"lfun_zeros_{name}.json"), "w"), indent=1)
    print(f"{name}: {len(z2)} zeros to {z2[-1]:.4f} (smooth count {out['smooth_count']:.2f}); half-step agrees: {same}; phase {phase_check}; first {[round(z, 6) for z in z2[:5]]}; {out['seconds']:.0f}s", flush=True)
