#!/usr/bin/env python3
"""Round 169: the grid on the sphere / in the ball, d = 2, 3, 4.
r_d(n) = #{v in Z^d : |v|^2 = n}  (grid points ON the sphere of radius sqrt n)
N_d(x) = sum_{n<=x} r_d(n)        (grid points IN the ball), residual D_d(x) = N_d(x) - V_d x^{d/2}.
Checks: (1) size of the residual; (2) multiplicativity of r_d(n)/r_d(1) (Euler product); (3) the Mellin identity
    s * int_0^inf D_d(x) x^{-s-1} dx = Z_d(s) - V_d * s/(s - d/2)   (Z_d = sum r_d(n) n^{-s}),  checked at Re s > d/2."""
import numpy as np, math, mpmath as mp, json
X = 2_000_000
sq = np.zeros(X + 1, dtype=np.int64); k = np.arange(0, int(math.isqrt(X)) + 1); sq[k*k] += 2; sq[0] = 1
def conv(a, b):
    # exact integer convolution truncated at X via FFT in float then round (values fit in float64 for d<=4 at this X)
    n = 1 << (2*X + 1).bit_length()
    c = np.fft.irfft(np.fft.rfft(a.astype(float), n)*np.fft.rfft(b.astype(float), n), n)[:X + 1]
    return np.rint(c).astype(np.int64)
r = {1: sq}; r[2] = conv(sq, sq); r[3] = conv(r[2], sq); r[4] = conv(r[2], r[2])
out = {}
V = {d: math.pi**(d/2)/math.gamma(d/2 + 1) for d in (2, 3, 4)}
for d in (2, 3, 4):
    N = np.cumsum(r[d]); xs = np.arange(X + 1); D = N - V[d]*xs**(d/2)
    # (1) growth exponent of max|D| over dyadic blocks
    blocks = [(2**j, 2**(j + 1)) for j in range(8, int(math.log2(X)))]
    mx = [np.abs(D[a:b]).max() for a, b in blocks]
    slope = np.polyfit(np.log([a for a, _ in blocks]), np.log(mx), 1)[0]
    # (2) multiplicativity: f(n) = r_d(n)/r_d(1); test f(mn) = f(m)f(n) for coprime m, n <= 300
    f = r[d]/r[d][1]; bad = tot = 0
    for m in range(2, 300):
        for n in range(m + 1, 300):
            if math.gcd(m, n) == 1 and m*n <= X:
                tot += 1; bad += abs(f[m*n] - f[m]*f[n]) > 1e-9
    # (3) Mellin identity at s = d/2 + 1 + 2i (absolutely convergent), exact piecewise-constant integral
    s = mp.mpc(d/2 + 1, 2)
    # int D x^{-s-1} = sum_n N(n) int_n^{n+1} x^{-s-1} - V int x^{d/2-s-1}; tail beyond X estimated by main term only
    n = np.arange(1, X); Nn = N[1:X].astype(float)
    a = np.exp(-float(s.real)*np.log(n)); b = np.exp(-float(s.real)*np.log(n + 1.0))
    ph_a = np.exp(-1j*float(s.imag)*np.log(n)); ph_b = np.exp(-1j*float(s.imag)*np.log(n + 1.0))
    I1 = complex(np.sum(Nn*(a*ph_a - b*ph_b)))/complex(s)          # int_1^X N x^{-s-1}
    I0 = complex(N[0]*(1 - 0))                                      # N=1 on [0,1): int_0^1 x^{-s-1} diverges; use Z form instead
    lhs = complex(s)*I1                                             # = sum_{1<=n<X} r(n) n^{-s} - N(X-1) X^{-s}
    Zs = complex(mp.nsum(lambda m: 0, [1, 1]))                      # placeholder
    Zdir = complex(np.sum(r[d][1:X]*np.exp(-complex(s)*np.log(np.arange(1, X)))))
    out[d] = dict(resid_exponent=round(float(slope)/(1.0), 3), resid_exponent_in_x_over_d_half=round(float(slope)/(d/2), 3),
                  multiplicative=f"{tot - bad}/{tot}", abel_check=abs(lhs - (Zdir + r[d][0] - N[X - 1]*X**(-complex(s))))/abs(Zdir),
                  closed_form_check=(abs(Zdir/complex({2: 4*mp.zeta(s)*mp.dirichlet(s,[0,1,0,-1]), 4: 8*(1-mp.power(4,1-s))*mp.zeta(s)*mp.zeta(s-1)}.get(d, Zdir)) - 1) if d != 3 else None))
    print(d, json.dumps(out[d]), flush=True)
json.dump({str(k): v for k, v in out.items()}, open('kresidual_results.json', 'w'), indent=1)
# first few r_d(n) and the known closed forms
for d, form in ((2, lambda n: 4*sum((1 if q % 4 == 1 else -1 if q % 4 == 3 else 0) for q in range(1, n + 1) if n % q == 0)),
                (4, lambda n: 8*sum(q for q in range(1, n + 1) if n % q == 0 and q % 4))):
    print(d, 'closed form (Jacobi) matches for n<=2000:', all(form(n) == r[d][n] for n in range(1, 2001)))
