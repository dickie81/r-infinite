#!/usr/bin/env python3
"""The count-constant theorem (Theorem 1bs's substrate): the balayage sum of
the finite-delta formula against its continuum,
    B(T) = 4 sum_{0 < gamma < T} arccosh(T/gamma),
    I(T) = 4 int_0^T arccosh(T/r) n_0(r) dr = T [ln(q (T/2pi)^d) - d (1 + ln 2)],
with n_0(r) = (1/2pi) ln(q (r/2pi)^d) the smooth zero density of a degree-d
L-function of conductor q, satisfies
    B(T) - I(T) = 4 c_L ln T + C_L + o(1),
c_L the constant term of the Riemann-von Mangoldt formula N(T) = N_0(T) + c_L
+ S(T): c_L = [pole] + sum_i (kappa_i/4 - 1/8) over the Gamma_R(s + kappa_i)
factors, so 4 c_L = 4 [pole] + sum_i (kappa_i - 1/2): 7/2 for zeta, kappa - 1/2
for a real primitive character, 11 for Delta (Gamma_C(s + 11/2) = Gamma_R(s +
11/2) Gamma_R(s + 13/2)). The proof is one Stieltjes integration by parts:
    B - I = int_0^T (N - N_0)(r) 4 / (r sqrt(1 - r^2/T^2)) dr,
then the constant c_L integrates to 4 c_L arccosh(T/gamma_1), the piece below
gamma_1 (where N = 0) to the constant -4 int_0^{gamma_1} N_0/r, and the S piece
to 4 int_{gamma_1}^inf S/r + o(1) (Littlewood's mean bound on S). Explicitly
    C_L = -4 c_L ln(gamma_1/2) - 4 int_0^{gamma_1} N_0(r)/r dr + 4 int_{gamma_1}^inf S(r)/r dr,
the last integral evaluated on the list plus the Stirling remainder's tail 4 kappa_R/T_last
(S contains, besides the argument of L, the next Stirling term kappa_R/T of the Gamma factors:
kappa_R = -4.80 for Delta, +0.0066 for zeta and the characters).
Functions: the forms' constants, B, I, the Stieltjes right-hand side (exact per
interval), the residual B - I - 4 c_L ln T, least-squares slopes, C_L by its
formula from a zero list. Floating point on the committed zero lists (data).
"""
import math, json, os
import numpy as np
from scipy.integrate import quad

HERE = os.path.dirname(os.path.abspath(__file__))
CK = os.path.join(HERE, "checkpoints")

# (q, d, kappas, pole) -> the count constant c_L = [pole] + sum(kappa_i/4 - 1/8)
FORMS = {
    "zeta":   dict(q=1, d=1, kappas=[0], pole=True,  zeros="zeta_zeros_6700.json"),
    "chi_-3": dict(q=3, d=1, kappas=[1], pole=False, zeros="lfun_zeros_chi_-3.json"),
    "chi_-4": dict(q=4, d=1, kappas=[1], pole=False, zeros="lfun_zeros_chi_-4.json"),
    "chi_8":  dict(q=8, d=1, kappas=[0], pole=False, zeros="lfun_zeros_chi_8.json"),
    "Delta":  dict(q=1, d=2, kappas=[5.5, 6.5], pole=False, zeros="lfun_zeros_Delta.json"),
}

def count_constant(F):
    """c_L = [pole] + sum_i (kappa_i/4 - 1/8)."""
    return (1.0 if F["pole"] else 0.0) + sum(k/4 - 1/8 for k in F["kappas"])

def four_cL_formula(F):
    """4 c_L = 4 [pole] + sum_i (kappa_i - 1/2)."""
    return 4*(1.0 if F["pole"] else 0.0) + sum(k - 0.5 for k in F["kappas"])

def load_zeros(F):
    p = os.path.join(CK, F["zeros"])
    j = json.load(open(p))
    return np.array(j["zeros"] if isinstance(j, dict) else j, dtype=float)

def N0(r, q, d):
    """the smooth count (T/2pi)[ln(q (T/2pi)^d) - d], with N0(0) = 0."""
    r = np.asarray(r, dtype=float)
    out = np.zeros_like(r)
    m = r > 0
    out[m] = r[m]/(2*math.pi)*(np.log(q*(r[m]/(2*math.pi))**d) - d)
    return out

def B(zs, T):
    g = zs[zs < T]
    return 4*float(np.sum(np.arccosh(T/g)))

def I(T, q, d):
    return T*(math.log(q*(T/(2*math.pi))**d) - d*(1 + math.log(2)))

def stieltjes_rhs(zs, T, q, d):
    """int_0^T (N - N_0)(r) 4/(r sqrt(1 - r^2/T^2)) dr, N the step function of the list (N = 0 below gamma_1):
    per interval between consecutive zeros N is constant and the integral is 4 N [-arccosh(T/r)] + the N_0 piece by quadrature."""
    w = lambda r: 4.0/(r*math.sqrt(1 - (r/T)**2))
    pts = [0.0] + [float(g) for g in zs[zs < T]] + [T]
    total = 0.0
    for k in range(len(pts) - 1):
        lo, hi = pts[k], pts[k + 1]
        n = k                                     # N on (gamma_k, gamma_{k+1}) = k
        # the constant part: 4 n int dr/(r sqrt(1 - r^2/T^2)) = 4 n [arccosh(T/lo) - arccosh(T/hi)]
        if n:
            total += 4*n*(math.acosh(T/lo) - (0.0 if hi >= T else math.acosh(T/hi)))
        # the -N_0 part by quadrature (N_0 ~ r ln r near 0, integrable against 1/r)
        f = lambda r: -N0(np.array([r]), q, d)[0]*w(r)
        val, err = quad(f, lo, hi, limit=200, epsabs=1e-11, epsrel=1e-11)
        total += val
    return total

def residual(zs, T, F):
    return B(zs, T) - I(T, F["q"], F["d"]) - 4*count_constant(F)*math.log(T)

def slope(zs, F, Tlo, Thi, n=12):
    Ts = np.exp(np.linspace(math.log(Tlo), math.log(Thi), n))
    x = np.log(Ts); y = np.array([B(zs, T) - I(T, F["q"], F["d"]) for T in Ts])
    A = np.vstack([x, np.ones_like(x)]).T
    sl, ic = np.linalg.lstsq(A, y, rcond=None)[0]
    return float(sl), float(ic), Ts, y

def stirling_remainder(F, T):
    """R(T) = N_smooth(T) - N_0(T) - c_L with N_smooth = theta(T)/pi + [pole] from the exact log-Gamma: the part of S that is
    not the argument of L, ~ kappa_R/T (the next Stirling term; -4.80/T for Delta, +0.0066/T for zeta and the characters)."""
    import mpmath as mp
    mp.mp.dps = 30
    q, d = F["q"], F["d"]
    th = sum(mp.im(mp.loggamma(mp.mpc(0.25 + mp.mpf(k)/2, T/2))) for k in F["kappas"]) - T/2*mp.log(mp.pi**d/q)
    Ns = float(th/mp.pi) + (1.0 if F["pole"] else 0.0)
    return Ns - N0(np.array([T]), q, d)[0] - count_constant(F)

def C_from_formula(zs, F, Tmax, tail=True):
    """C_L = -4 c_L ln(gamma_1/2) - 4 int_0^{gamma_1} N_0/r dr + 4 int_{gamma_1}^{inf} S(r)/r dr, S = N - N_0 - c_L, the integral
    over the list to Tmax plus the tail 4 int_{Tmax}^inf R(r)/r dr = 4 kappa_R/Tmax of the Stirling remainder (round 317 F317-2:
    -0.20 for Delta at Tmax = 94, negligible for zeta and the characters); the argument's own tail is the o(1)."""
    q, d, cL = F["q"], F["d"], count_constant(F); g1 = float(zs[0])
    t1 = -4*cL*math.log(g1/2)
    t2 = -4*quad(lambda r: N0(np.array([r]), q, d)[0]/r, 0, g1, limit=200)[0]
    # int S/r over [gamma_1, Tmax]: N piecewise constant
    pts = [float(g) for g in zs[zs < Tmax]] + [Tmax]
    t3 = 0.0
    for k in range(len(pts) - 1):
        lo, hi = pts[k], pts[k + 1]; n = k + 1
        t3 += 4*((n - cL)*math.log(hi/lo) - quad(lambda r: N0(np.array([r]), q, d)[0]/r, lo, hi, limit=200)[0])
    t4 = 4*Tmax*stirling_remainder(F, Tmax)/Tmax if tail else 0.0          # 4 kappa_R / Tmax with kappa_R = Tmax R(Tmax)
    return t1 + t2 + t3 + t4, (t1, t2, t3, t4)

if __name__ == "__main__":
    for name, F in FORMS.items():
        zs = load_zeros(F); Tmax = float(zs[-1])
        sl, ic, Ts, y = slope(zs, F, max(40.0, 3*float(zs[0])), Tmax)
        T = Ts[len(Ts)//2]
        lhs = B(zs, T) - I(T, F["q"], F["d"]); rhs = stieltjes_rhs(zs, T, F["q"], F["d"])
        Cf, parts = C_from_formula(zs, F, Tmax)
        res = [residual(zs, t, F) for t in Ts]
        print(f"{name:7s} 4c_L {four_cL_formula(F):+.3f} (= 4*{count_constant(F):.3f}); fitted slope {sl:+.3f}; Stieltjes identity |lhs-rhs| {abs(lhs-rhs):.2e} at T={T:.1f}; "
              f"residual C over T: min {min(res):.3f} max {max(res):.3f}; C by formula {Cf:.3f} (parts {parts[0]:.3f}, {parts[1]:.3f}, {parts[2]:.3f}, tail {parts[3]:.3f})", flush=True)
