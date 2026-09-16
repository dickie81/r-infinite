#!/usr/bin/env python3
"""Theorem 1ca (the smooth count in the unlocking functional): the verifier. The tower's member 36 (top); chain obligation to
cascade_gap_law.py (Theorem 1bz).

WHAT THE BLOCK CLAIMS. Write N(T) = N_0(T) + 7/8 + S(T) (T >= gamma_1), N_0(T) = (T/2 pi)(ln(T/2 pi) - 1) the smooth count of
Theorem 1bs, S its oscillation. (i) The split (an identity, by 1bs(ii)'s Stieltjes integration): Theorem 1by's unlocking
functional F_k(T) = 4 sum_{gamma<T} arccosh(T/gamma) - 2aT + 4 sum_h arccosh(T/h) equals F_k^s(T) + Osc(T) with the smooth
functional F_k^s(T) = I(T) - 2aT + 4 sum_h arccosh(T/h) + (7/2) arccosh(T/gamma_1) - 4 int_0^{gamma_1} N_0(r) w_T(r) dr,
I(T) = T[ln(T/2 pi) - 1 - ln 2] the continuum of the zero sum, w_T(r) = 1/(r sqrt(1 - r^2/T^2)), and the leftover
Osc(T) = 4 int_{gamma_1}^T S(r) w_T(r) dr. (ii) The smooth wall (derived): F_k^s is stationary where ln(2T_0/T) =
4 sum_h (T^2 - h^2)^{-1/2} + (7/2)(T^2 - gamma_1^2)^{-1/2} + 4 int_0^{gamma_1} N_0(r) r (T^2 - r^2)^{-3/2} dr, i.e.
T ln(2T_0/T) = 4m + 7/2 up to O((sum h^2 + gamma_1^2)/T^2) -- 1by(iii)'s continuum law with the count constant, the pole's
7/8 worth seven eighths of a hole; the minimum T^s unique (T G(T) falling from +inf at the cusp to 0, the piece below gamma_1 rising by less
than the rest falls, computed at the 45 states); for the ground state
T^s = 2T_0 e^{-eps}, eps = (7/2)/T^s. Computed: T^s/T_u within 1.9% rms at the 40 rungs against the 3.9% of 1by's law
(the bias 2.8% -> 0.3%), the law's closed form within 0.13% rms of T^s, T^s/T_u(1) within 2.1% at the five ground states.
(iii) The leftover oscillation (proved): |Osc(T) - Osc_inf| <= 4 sup_{[T-D,T]}|S| [arccosh(T/(T-D)) - ln(T/(T-D))]
+ 8 sup_{[gamma_1,T]}|S_1| D_T(T-D) + 8 sup_{>=T}|S_1|/T for every 0 < D < T - gamma_1, Osc_inf = 4 int_{gamma_1}^inf S/r
(1bs's third term), D_T(r) = w_T(r) - 1/r, S_1 the integral of S -- with S = O(ln t) (von Mangoldt) and Littlewood's S_1 = O(ln t) this is O(ln T/sqrt T):
the wall's square-root cusp reads the count's local fluctuation with a weight sqrt(2D/T). Consequences: min F_k = F_k^s(T^s)
+ Osc_inf + O(ln T/sqrt T); |T_u - T^s| = O(T^{1/4} (ln T)^{1/2}); the rung's exponent from the smooth count and the holes
alone, ln lambda_k - ln lambda_1 = 2 ln|ghat_k(0)/ghat_1(0)| + F_k^s(T_k^s) - F_1^s(T_1^s), within half a nat (computed).
(iv) The exterior tail (proved, computed): for the cut chi(r) = Phi((r - T)/D) - Phi((r - T')/D) (Phi the normal
distribution), Weil's explicit formula gives EXACTLY 2 sum_{gamma>0} ghat(gamma)^2 chi(gamma) = (1/pi) int_0^inf ghat^2 chi
ln(r/2 pi) dr + E_arch + E_pole - 2 sum_n Lambda(n) n^{-1/2} f_chi(ln n), f_chi(u) = (1/pi) int_0^inf ghat^2 chi cos(ru) dr:
the smooth count's integral of the transform squared, less the prime shells, plus the Stirling remainder
E_arch = (1/pi) int ghat^2 chi [Re psi(1/4 + ir/2) - ln(r/2)] dr, |E_arch| <= (3/(2 pi)) int ghat^2 chi r^{-2} dr (Binet), and
the pole term E_pole = 2 ghat(i/2)^2 chi(i/2), |E_pole| <= 8 a e^a e^{-(T^2 - 1/4)/(2 D^2)}: after the shells are subtracted
the leftover is the Stirling remainder, below 10^-5 of the tail. Computed at the five ground states and the 40 rungs: the
identity's residual, the smooth count's overestimate of the exterior leakage (a factor 1.9-2.9 over the whole exterior,
2.0-4.2 in the near quarter, 1.00-1.15 beyond 4 T_1), the shells of the smallest primes carrying it.

THE GATES. (0) the algebra witnessed at 60 digits (the piece below gamma_1 in closed form, the stationarity's closed form,
the Stirling remainder's -1/24 and its bound, T G's piece below gamma_1 at the cusp, the split as an identity on the list);
(1) the smooth wall at the 40 rungs; (2) the ground states; (3) the leftover oscillation on the list and the bound's terms;
(4) the exponent from the smooth count; (5) the exterior identity, the shells' share, the leftover after the shells;
(6) the paper's numbers parsed back; (7) the chain obligation; (8) the needles and census.

WHAT IS NOT CLAIMED. Explicit constants for S and S_1 (the classical O-bounds are the inputs; the list's suprema are computed);
any bound on the shells' sum in general (computed at the cells); the reduction of 1bm(iii); the odd sector; no Riemann
Hypothesis consequence.
"""
import math, os, sys, json, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ladder_caster as LC
from rung_anatomy import run as run_RA
from rung_laws import run as run_RL
from ladder_caster import run as run_LC
from leakage_profiles import run as run_LP
import mpmath as _mp
from scipy.integrate import quad as _quad
from scipy.optimize import brentq as _brentq
from scipy.special import digamma as _digamma, ndtr as _ndtr

PAPER_NEEDLES = [
    {'g': 'g8', 's': "Theorem 1ca (the smooth count", 'form': 'plain'},
    {'g': 'g8', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 18},
    {'s': '`cascade_smooth_functional.py`', 'min': 2, 'g': 'g8'},
    {'s': 'the **103 scripts cited in place** above', 'form': 'ws', 'g': 'g8'},
    {'s': 'extended by Theorems 1i–1ca:', 'form': 'ws', 'g': 'g8'},
    {'g': 'g6', 's': 'T^s/T_u averages 1.003 with rms deviation from 1 of 0.019 over [0.969, 1.063] at the 40 rungs (1.001 with 0.015 at the 30 with three or more holes), against 1.028 with 0.039 for 1by’s law without the constant; the closed form T ln(2T₀/T) = 4m + 7/2 reproduces T^s within 0.13% rms, and T^s/T_w averages 0.962 over [0.875, 1.034]', 'form': 'ws'},
    {'g': 'g6', 's': 'the ground state’s smooth wall sits at T^s/T₀ = 1.923, 1.943, 1.958, 1.972, 1.983 at the five cells, within 2.1% of its unlocking height T_u(1) (T^s/T_u(1) over [0.983, 1.021])', 'form': 'ws'},
    {'g': 'g6', 's': 'F₁^s(T^s) sits 0.0041, 0.0022, 0.0012, 0.0005, 0.0002 nats below the closed form at the five cells, the difference falling with δ, and at the 40 rungs the closed form sits within 1.23 nats of F_k^s(T^s)', 'form': 'ws'},
    {'g': 'g6', 's': 'on [0.5, 1.6]T₁ the leftover ranges over 0.88, 0.76, 0.68, 0.56, 0.44 nats at the five cells with means 0.19–0.20 against Osc_∞ = 0.19 on the list, the range times √T₁ constant to 8% (8.2–8.9)', 'form': 'ws'},
    {'g': 'g6', 's': 'with the list’s suprema sup|S| = 1.36 and sup|S₁| = 1.47 below height 6990 and Δ = 1, the bound reads 1.66, 1.42, 1.21, 1.00, 0.77 nats at T₁ against the observed sup|Osc − Osc_∞| of 0.52, 0.42, 0.40, 0.32, 0.25', 'form': 'ws'},
    {'g': 'g6', 's': 'F_k(T_u) − F_k^s(T^s) averages −0.03 with rms 0.08 over [−0.23, +0.08] at the 40 rungs, Osc(T_u) itself averaging −0.06', 'form': 'ws'},
    {'g': 'g6', 's': 'the residual averages +0.15 with rms 0.20 over [−0.11, +0.42] at the 40 rungs, against +0.13, 0.19 and [−0.16, +0.43] for 1by’s reading with the zeros', 'form': 'ws'},
    {'g': 'g6', 's': 'the identity holds within 4.4 × 10⁻⁶ of the tail at the five ground states over the five windows (6.7 × 10⁻¹² away from the cut at the edge, where the dodged zeros the cut still weighs carry the stored profile’s rounding) and within 2.7 × 10⁻¹¹ at the 40 rungs', 'form': 'ws'},
    {'g': 'g6', 's': 'the smooth count’s integral is 1.87, 1.87, 2.29, 2.88, 2.77 times the actual leakage over the whole exterior at the five cells, 2.42, 2.01, 3.06, 4.21, 3.71 in the near quarter [T₁, 1.25T₁], 1.71, 2.14, 2.00, 2.20, 3.40 on [1.25, 2]T₁, 1.28, 1.65, 1.60, 1.91, 1.46 on [2, 4]T₁ and 1.119, 1.151, 1.066, 1.000, 1.003 beyond 4T₁', 'form': 'ws'},
    {'g': 'g6', 's': 'the leftover after the shells is at most 4.0 × 10⁻⁶ of the tail, its Binet bound at most 1.4 × 10⁻⁴', 'form': 'ws'},
    {'g': 'g6', 's': 'the largest shell is n = 3, 3, 7, 5, 2 over the whole exterior and n = 3, 5, 7, 5, 2 in the near quarter', 'form': 'ws'},
    {'g': 'g6', 's': 'at the 40 rungs the smooth count’s integral runs 1.58–3.77 times the leakage beyond T₁ and 1.85–7.37 times it in the near quarter', 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ORDER = ["d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
CEN = {c: run_RA(c) for c in ORDER}
LAW = {c: run_RL(c) for c in ORDER}
EV = {c: run_LC(c) for c in ORDER}
PRO = {c: run_LP(c) for c in ORDER}
ZS = np.array(json.load(open(LC.ZD)), dtype=float)                  # Theorem 1bm's 6700-zero list (data; its hash in every key)
G1Z = float(ZS[0]); TWO_PI = 2*math.pi
SAFE = -20.0
def n_safe(c):
    st = EV[c]; pro = st["prolate_ln_leakage"]
    return len([r for r in st["rungs"][1:] if 2*r["k"] < len(pro) and pro[2*r["k"]] is not None and pro[2*r["k"]] < SAFE and r["k"] <= 12])

# ---------------------------------------------------------------- Theorems 1bm, 1bx, 1by (as at cascade_gap_law.py)
def psi(z, T): return (z/T)/(1 + math.sqrt(1 - (z/T)**2))
def dk_bal(holes, T): return -sum((1 + psi(h, T)**2)/(2*T*T) for h in holes)
def solve_T(holes, Dk):
    lo, hi = 1.0, 1e6
    for _ in range(200):
        mid = 0.5*(lo + hi)
        if dk_bal(holes, mid) < Dk: lo = mid
        else: hi = mid
    return 0.5*(lo + hi)
def B(T):                       # the balayage sum 4 sum_{gamma<T} arccosh(T/gamma)
    g = ZS[ZS < T]; return 4*float(np.sum(np.arccosh(T/g)))
def F1(T, a): return B(T) - 2*a*T
def cost(holes, T): return 4*sum(math.log(1/psi(h, T)) for h in holes)
def Fk(T, a, holes): return F1(T, a) + cost(holes, T)
def argmin_zero(a, holes, jmax):
    jmin = max(int(np.searchsorted(ZS, max(holes)*1.000001)) if holes else 1, 1)
    vals = [Fk(ZS[j], a, holes) for j in range(jmin, jmax)]
    return int(np.argmin(vals)) + jmin
def outer(r):
    Z = [z for _, z in r["dodging"]] + list(r["exterior"])
    if r["n_complex"] == 1 and r["sum_rule_residual"] < 0: Z.append(abs(r["sum_rule_residual"])**-0.5)
    return np.array(sorted(Z))

# ---------------------------------------------------------------- the smooth count in the functional (Theorem 1ca)
def N0(r): return (r/TWO_PI)*(math.log(r/TWO_PI) - 1)                          # Theorem 1bs's smooth count
def n0r(r): return (math.log(r/TWO_PI) - 1)/TWO_PI                            # N_0(r)/r
def Icont(T): return T*(math.log(T/TWO_PI) - 1 - math.log(2))                  # 1bs's continuum of the zero sum
def below(T): return 4*_quad(lambda r: n0r(r)/math.sqrt(1 - (r/T)**2), 0, G1Z, limit=200)[0]        # 4 int_0^{gamma_1} N_0 w_T
def dbelow(T): return -4*_quad(lambda r: n0r(r)*(r*r/T**3)*(1 - (r/T)**2)**-1.5, 0, G1Z, limit=200)[0]
def Fs(T, a, holes): return Icont(T) - 2*a*T + 4*sum(math.acosh(T/h) for h in holes) + 3.5*math.acosh(T/G1Z) - below(T)
def dFs(T, a, holes):
    T0 = TWO_PI*math.exp(2*a)
    return math.log(T/(2*T0)) + 4*sum(1/math.sqrt(T*T - h*h) for h in holes) + 3.5/math.sqrt(T*T - G1Z*G1Z) - dbelow(T)
def below5(T):                   # int_0^gamma_1 N_0 r (T^2 - r^2)^(-5/2) dr: the r-form where its peak ratio is at most 2^(5/2) (T >= sqrt 2 gamma_1);
    if T*T >= 2*G1Z*G1Z: return _quad(lambda r: N0(r)*r*(T*T - r*r)**-2.5, 0, G1Z, limit=200)[0]        # nearer the cusp, split at gamma_1/2:
    return (_quad(lambda r: N0(r)*r*(T*T - r*r)**-2.5, 0, G1Z/2, limit=200)[0]                          # the r-form below it (tame),
            + _quad(lambda u: N0(math.sqrt(T*T - math.exp(2*u)))*math.exp(-3*u), 0.5*math.log(T*T - G1Z*G1Z), 0.5*math.log(T*T - G1Z*G1Z/4), limit=200)[0])   # s = sqrt(T^2 - r^2) = e^u above it (r dr = -s ds; the integrand N_0 e^(-3u), no peak)
def TG(T, holes):                # T G(T) = 1 - T F'': the holes' and the constant's terms with the piece below gamma_1 exact
    return sum(4*T*T*(T*T - h*h)**-1.5 for h in holes) + 3.5*T*T*(T*T - G1Z*G1Z)**-1.5 + 12*T*T*below5(T)
def mono(holes, T0):             # T G strictly decreasing on 600 log-spaced points from the cusp to 30 T_0
    cusp = max(max(holes) if holes else 0.0, G1Z); v = [TG(T, holes) for T in np.exp(np.linspace(math.log(cusp*(1 + 1e-6)), math.log(30*T0), 600))]
    return all(v[i] > v[i + 1] for i in range(len(v) - 1))
def d2Fs(T, a, holes):
    return 1/T - 4*sum(T*(T*T - h*h)**-1.5 for h in holes) - 3.5*T*(T*T - G1Z*G1Z)**-1.5 - (dbelow(T*(1 + 1e-6)) - dbelow(T*(1 - 1e-6)))/(2e-6*T)
def smooth_wall(a, holes):      # the minimum of F_k^s on (max(h_max, gamma_1), 3 T_0): the grid minimum refined by the stationarity equation
    T0 = TWO_PI*math.exp(2*a); lo = max(max(holes) if holes else 0.0, G1Z)*1.001
    grid = np.linspace(max(lo, 0.5*T0), 3*T0, 400); vals = [Fs(T, a, holes) for T in grid]; j = int(np.argmin(vals))
    assert 0 < j < len(grid) - 1, "the smooth minimum is interior"
    return _brentq(lambda T: dFs(T, a, holes), grid[j - 1], grid[j + 1])
def Osc(T): return B(T) - Icont(T) - 3.5*math.acosh(T/G1Z) + below(T)          # the leftover: F_k - F_k^s (holes cancel)
def Sosc(r): return float(np.searchsorted(ZS, r)) - N0(r) - 0.875                # S(r) = N - N_0 - 7/8 on the list
def IN0(r): return (r*r/(2*TWO_PI))*(math.log(r/TWO_PI) - 1.5)                  # int_0^r N_0
def S1(r):                        # S_1(r) = int_{gamma_1}^r S, exact on the list
    j = int(np.searchsorted(ZS, r)); return float(np.sum(r - ZS[:j])) - (IN0(r) - IN0(G1Z)) - 0.875*(r - G1Z)
def intN0r(r): return (r/TWO_PI)*(math.log(r/TWO_PI) - 2)                       # int_0^r N_0(s)/s ds
def wgt(T, D): return math.acosh(T/(T - D)) - math.log(T/(T - D))                # int_{T-D}^T D_T dr
def dOsc(T): return 4*float(np.sum((T*T - ZS[ZS < T]**2)**-0.5)) - math.log(T/(4*math.pi)) - 3.5/math.sqrt(T*T - G1Z*G1Z) + dbelow(T)   # Osc' between zeros (analytic; +inf at a zero's right)
def osc_extrema(lo, hi):          # the exact extrema of Osc on [lo, hi]: the minima at the zeros (the cusps, infinite slope from the right), the maxima by the analytic derivative on each arc
    zz = ZS[(ZS > lo) & (ZS < hi)]; ends = [lo] + [float(z) for z in zz] + [hi]
    mins = [Osc(lo), Osc(hi)] + [Osc(float(z)) for z in zz]; maxs = []
    for a_, b_ in zip(ends[:-1], ends[1:]):
        x1, x2 = a_ + 1e-7*(b_ - a_), b_ - 1e-7*(b_ - a_)
        d1, d2 = dOsc(x1), dOsc(x2)
        maxs.append(Osc(_brentq(dOsc, x1, x2)) if d1 > 0 > d2 else max(Osc(x1), Osc(x2)))   # an interior maximum only where Osc' changes sign on the arc
    grid = np.linspace(lo, hi, 3000); return min(mins), max(maxs), float(np.mean([Osc(T) for T in grid]))
def DT(T, r): return (1/r)*((1 - (r/T)**2)**-0.5 - 1)                           # the weight defect w_T - 1/r

# ---------------------------------------------------------------- g0: the algebra witnessed at 60 digits
ok = True
with _mp.workdps(60):
    g1 = _mp.mpf(repr(G1Z)); pi = _mp.pi
    # (a) the piece below gamma_1: -4 int_0^{gamma_1} N_0(r)/r dr = -(2/pi) gamma_1 (ln(gamma_1/2 pi) - 2) (1bs's 10.70), and its w_T form at T = 87.4
    c0 = -4*_mp.quad(lambda r: (r/(2*pi))*(_mp.log(r/(2*pi)) - 1)/r, [0, g1])
    ok &= abs(c0 + (2/pi)*g1*(_mp.log(g1/(2*pi)) - 2)) <= _mp.mpf("1e-40")
    T = _mp.mpf("87.4"); bw = 4*_mp.quad(lambda r: (_mp.log(r/(2*pi)) - 1)/(2*pi)/_mp.sqrt(1 - (r/T)**2), [0, g1])
    ok &= abs(bw - _mp.mpf(repr(below(87.4)))) <= _mp.mpf("1e-9")
    # (b) the stationarity's closed form against the numerical derivative of F^s (one hole at h = 3.4, a = 1)
    a_, h_ = _mp.mpf(1), _mp.mpf("3.4"); T0_ = 2*pi*_mp.e**2
    def Fs_mp(T): return T*(_mp.log(T/(2*pi)) - 1 - _mp.log(2)) - 2*a_*T + 4*_mp.acosh(T/h_) + _mp.mpf(7)/2*_mp.acosh(T/g1) - 4*_mp.quad(lambda r: (_mp.log(r/(2*pi)) - 1)/(2*pi)/_mp.sqrt(1 - (r/T)**2), [0, g1])
    def dFs_mp(T): return _mp.log(T/(2*T0_)) + 4/_mp.sqrt(T*T - h_*h_) + _mp.mpf(7)/2/_mp.sqrt(T*T - g1*g1) + 4*_mp.quad(lambda r: (r/(2*pi))*(_mp.log(r/(2*pi)) - 1)*r*(T*T - r*r)**_mp.mpf(-1.5), [0, g1])
    for T in (_mp.mpf(80), _mp.mpf(95)):
        ok &= abs(_mp.diff(Fs_mp, T) - dFs_mp(T)) <= _mp.mpf("1e-18")
    # (c) the Stirling remainder eps(r) = Re psi(1/4 + ir/2) - ln(r/2): r^2 eps -> -1/24, and the bound |eps| <= 3/(2 r^2) at r >= 8
    for r in (100, 1000, 10000):
        r = _mp.mpf(r); eps = _mp.re(_mp.digamma(_mp.mpf(1)/4 + 1j*r/2)) - _mp.log(r/2)
        ok &= abs(eps*r*r + _mp.mpf(1)/24) <= _mp.mpf("1e-5")*(100/r)**2 + _mp.mpf("1e-12")
    for r in (8, 10, 14.13, 20, 50, 87.4, 250, 415, 1000, 7000):
        r = _mp.mpf(r); eps = _mp.re(_mp.digamma(_mp.mpf(1)/4 + 1j*r/2)) - _mp.log(r/2)
        ok &= abs(eps) <= _mp.mpf(3)/(2*r*r)
    # (c') T G's piece below gamma_1, 12 T^2 int_0^{gamma_1} N_0 r (T^2 - r^2)^{-5/2} dr, at the cusp T = gamma_1 (1 + 1e-6) (where the integrand peaks at 1e14 times its value at gamma_1/2) and at T = 15, against a 60-digit quadrature with the interval refined dyadically toward gamma_1
    for T in (g1*(1 + _mp.mpf("1e-6")), _mp.mpf(15)):
        pts = [_mp.mpf(0), g1/2] + [g1 - (g1/2)*_mp.mpf(2)**(-k) for k in range(1, 60)] + [g1]
        ref = _mp.quad(lambda r: (r/(2*pi))*(_mp.log(r/(2*pi)) - 1)*r*(T*T - r*r)**_mp.mpf(-2.5), pts)
        ok &= abs(_mp.mpf(repr(below5(float(T)))) - ref) <= _mp.mpf("1e-9")*abs(ref)
    # (d) the identity's ingredients: int_{gamma_1}^T w_T = arccosh(T/gamma_1), int_{T-D}^T D_T = arccosh(T/(T-D)) - ln(T/(T-D)), and 4 int_{gamma_1}^T S w_T on the list equals B - I - (7/2) arccosh(T/gamma_1) + below(T)
    T = _mp.mpf("87.4")
    ok &= abs(_mp.quad(lambda r: 1/(r*_mp.sqrt(1 - r*r/(T*T))), [g1, T]) - _mp.acosh(T/g1)) <= _mp.mpf("1e-25")
    D = _mp.mpf(1); ok &= abs(_mp.quad(lambda r: (1/r)*((1 - r*r/(T*T))**_mp.mpf(-0.5) - 1), [T - D, T]) - (_mp.acosh(T/(T - D)) - _mp.log(T/(T - D)))) <= _mp.mpf("1e-25")
split_ok = True
for c in ORDER:
    a = CEN[c]["delta"]/2; T1 = CEN[c]["rungs"][0]["edge"]
    for x in (0.7, 1.0, 1.3):
        T = x*T1 + 0.123; holes = [3.4, 9.0]
        lhs = Fk(T, a, holes)
        # the exact Osc on the list: 4 int_{gamma_1}^T S w_T = sum over the inter-zero intervals of (j - 7/8) [arccosh(T/r1) - arccosh(T/r2)] - 4 int_{gamma_1}^T N_0 w_T
        zz = ZS[ZS < T]; osc = 0.0
        for j in range(len(zz)):
            r1 = zz[j]; r2 = zz[j + 1] if j + 1 < len(zz) else T
            osc += (j + 1 - 0.875)*(math.acosh(T/r1) - math.acosh(T/r2))
        osc = 4*osc - 4*_quad(lambda r: n0r(r)/math.sqrt(1 - (r/T)**2), G1Z, T, limit=400, points=[0.999*T])[0]
        split_ok &= abs(lhs - (Fs(T, a, holes) + osc)) <= 1e-6*abs(lhs) and abs(osc - Osc(T)) <= 1e-6
ok &= split_ok
gate(f"g0 the algebra witnessed at 60 digits: the piece below gamma_1 in closed form -4 int_0^gamma_1 N_0/r dr = -(2/pi) gamma_1 (ln(gamma_1/2pi) - 2) = {float(c0):.4f} (1bs's 10.70) and its w_T form at T = 87.4 within 1e-9; the stationarity's closed form against the numerical derivative of F^s within 1e-18 at two heights; the Stirling remainder r^2 [Re psi(1/4 + ir/2) - ln(r/2)] -> -1/24 at r = 100, 1000, 10000 and |Re psi(1/4 + ir/2) - ln(r/2)| <= 3/(2 r^2) at ten heights from 8 to 7000 (the bound the block uses); T G's piece below gamma_1 against a 60-digit quadrature at the cusp gamma_1 (1 + 1e-6) and at T = 15 within 1e-9 relative; int_gamma_1^T w_T = arccosh(T/gamma_1) and int_(T-D)^T D_T = arccosh(T/(T-D)) - ln(T/(T-D)) within 1e-25; the split F_k = F_k^s + Osc as an identity at three heights per cell with two trial holes (within 1e-6, Osc by the exact inter-zero integrals)", ok)

# ---------------------------------------------------------------- the per-rung quantities
R = {}; W = {}; G = {}
sup_S = 0.0; sup_S1 = 0.0
for j in range(len(ZS)):
    if ZS[j] < 6990: sup_S = max(sup_S, abs(j - N0(ZS[j]) - 0.875), abs(j + 1 - N0(ZS[j]) - 0.875))
for r in np.linspace(G1Z, 6990, 200001): sup_S1 = max(sup_S1, abs(S1(float(r))))
zz = ZS[ZS < 6990]; osc_inf = 0.0
for j in range(len(zz)):
    r1 = zz[j]; r2 = zz[j + 1] if j + 1 < len(zz) else 6990.0
    osc_inf += (j + 1 - 0.875)*math.log(r2/r1)
osc_inf = 4*(osc_inf - (intN0r(6990.0) - intN0r(G1Z)))               # 4 int_{gamma_1}^{6990} S/r dr, exact on the list
c0f = -4*(G1Z/TWO_PI)*(math.log(G1Z/TWO_PI) - 2)
for c in ORDER:
    S = CEN[c]; Lw = {l["k"]: l for l in LAW[c]["laws"]}; ns = n_safe(c); g = S["rungs"][0]; T1 = g["edge"]; a = S["delta"]/2; P = PRO[c]; T0 = TWO_PI*math.exp(2*a)
    jmax = int(np.searchsorted(ZS, 3*T1)); j1 = argmin_zero(a, [], jmax); T1u = ZS[j1]
    Ts1 = smooth_wall(a, []); p1 = P["rungs"][0]
    o_lo, o_hi = 0.5*T1, 1.6*T1; o_min, o_max, o_mean = osc_extrema(o_lo, o_hi)
    G[c] = dict(T1=T1, T1u=T1u, a=a, T0=T0, Ts1=Ts1, Fs1=Fs(Ts1, a, []), F1u=F1(T1u, a), Osc1=Osc(T1u), osc_mean=o_mean, osc_min=o_min, osc_max=o_max,
                osc_sup=max(abs(o_min - osc_inf), abs(o_max - osc_inf)), cf1=-2*T0 + 3.5*math.log(4*T0/G1Z) + c0f - 3.5**2/(4*T0), eps1=math.exp(-3.5/(2*T0)),
                bound1=4*sup_S*wgt(T1, 1.0) + 8*sup_S1*DT(T1, T1 - 1.0) + 8*sup_S1/T1, curv=d2Fs(Ts1, a, []), mono=mono([], T0))
    for r, p in zip(S["rungs"][1:ns + 1], P["rungs"][1:ns + 1]):
        k = r["k"]; m = k - 1; holes = sorted(r["holes"]); Tw = solve_T(holes, Lw[k]["Dkappa"]); ju = argmin_zero(a, holes, jmax); Tu = ZS[ju]
        Ts = smooth_wall(a, holes)
        f = lambda u: u*math.log(2/u) - (2*m/math.pi)*math.exp(-2*a); Tc = _brentq(f, 2/math.e + 1e-9, 2 - 1e-12)*T0                     # 1by(iii)'s law
        f2 = lambda u: u*math.log(2/u) - (4*m + 3.5)/T0; Tc2 = _brentq(f2, 2/math.e + 1e-9, 2 - 1e-12)*T0                                 # with the count constant
        c2 = 2*math.log(abs(p["g0"]/p1["g0"])); dl = p["ln_lam"] - p1["ln_lam"]
        cf = -2*T0 + 4*sum(math.log(4*T0/h) for h in holes) + 3.5*math.log(4*T0/G1Z) + c0f - (4*m + 3.5)**2/(4*T0)
        cvx = min(T*d2Fs(T, a, holes) for T in np.linspace(2*T0/math.e, 2*T0, 200))                                              # T F'' over the bracket (2T_0/e, 2T_0)
        W[(c, k)] = dict(k=k, m=m, holes=holes, Tw=Tw, Tu=Tu, T1=T1, T1u=T1u, Ts=Ts, Tc=Tc, Tc2=Tc2, Osc_u=Osc(Tu), F_u=Fk(Tu, a, holes), Fs_min=Fs(Ts, a, holes), Fs_u=Fs(Tu, a, holes),
                         c2=c2, dl=dl, cf=cf, curv=d2Fs(Ts, a, holes), cvx=cvx, lawres=Ts*math.log(2*T0/Ts) - 4*m - 3.5, cond=(4*m + 3.5 < 2*T0/math.e), mono=mono(holes, T0))
ALL = list(W.values()); HM = [w for w in ALL if w["m"] >= 3]
assert len(ALL) == 40 and len(HM) == 30
def rms(v): v = np.asarray(v, float); return float(math.sqrt(np.mean(v*v)))
def rms1(v): return rms(np.asarray(v, float) - 1)
def mean(v): return float(np.mean(v))

# ---------------------------------------------------------------- g1: the smooth wall at the 40 rungs
tsu = [w["Ts"]/w["Tu"] for w in ALL]; tsu_hm = [w["Ts"]/w["Tu"] for w in HM]; tsw = [w["Ts"]/w["Tw"] for w in ALL]
tcu = [w["Tc"]/w["Tu"] for w in ALL]; tc2u = [w["Tc2"]/w["Tu"] for w in ALL]; tc2s = [w["Tc2"]/w["Ts"] for w in ALL]
lawres = [w["lawres"] for w in ALL]; curv_min = min(w["curv"]*w["Ts"] for w in ALL); cvx_min = min(w["cvx"] for w in ALL); n_cond = sum(w["cond"] for w in ALL); n_mono = sum(w["mono"] for w in ALL) + sum(G[c]["mono"] for c in ORDER)
ok = abs(mean(tsu) - 1) <= 0.01 and rms1(tsu) <= 0.025 and min(tsu) >= 0.95 and max(tsu) <= 1.08
ok &= abs(mean(tsu_hm) - 1) <= 0.005 and rms1(tsu_hm) <= 0.02
ok &= rms1(tc2s) <= 0.003 and max(abs(x) for x in lawres) <= 0.6 and curv_min >= 0.5 and cvx_min >= 0.2 and n_cond == 40 and n_mono == 45
ok &= rms1(tcu) >= 1.5*rms1(tsu) and abs(mean(tcu) - 1) >= 3*abs(mean(tsu) - 1) and 0.94 <= mean(tsw) <= 0.98
gate(f"g1 the smooth wall T^s (the minimum of F_k^s) against Theorem 1by's T_u at the 40 rungs: T^s/T_u mean {mean(tsu):.4f} (gated within 0.01 of 1), rms deviation from 1 {rms1(tsu):.4f} (gated 0.025), range [{min(tsu):.3f}, {max(tsu):.3f}] (gated within [0.95, 1.08]); at the 30 with three or more holes mean {mean(tsu_hm):.4f} (gated within 0.005), rms {rms1(tsu_hm):.4f} (gated 0.02); the law T ln(2T_0/T) = 4m + 7/2 against T^s: rms {rms1(tc2s):.4f} (gated 0.003), its remainder T ln(2T_0/T) - 4m - 7/2 at T^s within {max(abs(x) for x in lawres):.3f} (gated 0.6: the holes' 2 sum h^2/T^2 at up to eleven holes); T F^s'' at T^s at least {curv_min:.3f} (gated 0.5) and at least {cvx_min:.3f} over the bracket (2T_0/e, 2T_0) at every rung (gated 0.2: convex there), 4m + 7/2 < 2T_0/e at {n_cond} of 40 (gated 40), T G(T) strictly decreasing on 600 log-spaced points from the cusp to 30 T_0 at {n_mono} of the 45 states (gated 45: the uniqueness argument's monotonicity, the piece below gamma_1 exact); 1by's continuum law without the constant, uT_0/T_u mean {mean(tcu):.4f} rms {rms1(tcu):.4f} against {mean(tc2u):.4f}, {rms1(tc2u):.4f} with it (gated: the rms at least 1.5 times and the bias at least 3 times the smooth wall's); T^s/T_w mean {mean(tsw):.4f} (gated [0.94, 0.98]) over [{min(tsw):.3f}, {max(tsw):.3f}]", ok)

# ---------------------------------------------------------------- g2: the ground states
ts0 = [G[c]["Ts1"]/G[c]["T0"] for c in ORDER]; tsu1 = [G[c]["Ts1"]/G[c]["T1u"] for c in ORDER]; tsT1 = [G[c]["Ts1"]/G[c]["T1"] for c in ORDER]
epsr = [G[c]["Ts1"]/(2*G[c]["T0"])/G[c]["eps1"] for c in ORDER]; cfd = [G[c]["Fs1"] - G[c]["cf1"] for c in ORDER]; cfd_r = [w["Fs_min"] - w["cf"] for w in ALL]
ok = all(1.9 <= x <= 2.0 for x in ts0) and all(ts0[i] < ts0[i + 1] for i in range(4)) and max(abs(x - 1) for x in tsu1) <= 0.025 and max(abs(x - 1) for x in epsr) <= 0.002
ok &= all(-0.01 <= x <= 0 for x in cfd) and all(cfd[i] < cfd[i + 1] for i in range(4)) and min(cfd_r) >= -1.5 and max(cfd_r) <= 0
gate(f"g2 the ground states: T^s/T_0 = " + ", ".join(f"{x:.3f}" for x in ts0) + f" at the five cells (gated within [1.9, 2.0], increasing), T^s/(2T_0) against e^(-7/(4T_0)) within {max(abs(x - 1) for x in epsr):.4f} (gated 0.002); T^s/T_u(1) = " + ", ".join(f"{x:.4f}" for x in tsu1) + f" (gated within 0.025 of 1), T^s/T_1 = " + ", ".join(f"{x:.4f}" for x in tsT1) + "; the minimum F_1^s(T^s) against the closed form -2T_0 + (7/2) ln(4T_0/gamma_1) - 4 int_0^gamma_1 N_0/r dr - (7/2)^2/(4T_0): " + ", ".join(f"{x:+.4f}" for x in cfd) + f" (gated within [-0.01, 0], rising toward 0: the O(T_0^-2) remainder -- the cube term and the gamma_1^2 pieces); at the rungs the closed form with the holes' 4 sum ln(4T_0/h) and -(4m + 7/2)^2/(4T_0) sits {min(cfd_r):+.3f} to {max(cfd_r):+.3f} nats from F_k^s(T^s) (gated within [-1.5, 0]: the (4m + 7/2)^3/T_0^2 and sum h^2/T_0^2 remainders grow with the holes)", ok)

# ---------------------------------------------------------------- g3: the leftover oscillation
orng = [G[c]["osc_max"] - G[c]["osc_min"] for c in ORDER]; osup = [G[c]["osc_sup"] for c in ORDER]; omean = [G[c]["osc_mean"] for c in ORDER]
scal = [orng[i]*math.sqrt(G[c]["T1"]) for i, c in enumerate(ORDER)]; bnd = [G[c]["bound1"] for c in ORDER]
oscu = [w["Osc_u"] for w in ALL]; dmin = [w["F_u"] - w["Fs_min"] for w in ALL]; rise = [w["Fs_u"] - w["Fs_min"] for w in ALL]
ok = all(orng[i] > orng[i + 1] for i in range(4)) and 0.3 <= min(orng) and max(orng) <= 1.0 and max(scal)/min(scal) <= 1.15
ok &= all(abs(x - osc_inf) <= 0.02 for x in omean) and 0.15 <= osc_inf <= 0.25 and all(osup[i] < bnd[i] for i in range(5)) and all(bnd[i] > bnd[i + 1] for i in range(4))
ok &= 1.2 <= sup_S <= 1.5 and 1.3 <= sup_S1 <= 1.6 and abs(mean(dmin)) <= 0.1 and rms(dmin) <= 0.12 and min(dmin) >= -0.3 and max(dmin) <= 0.15
ok &= -0.1 <= mean(oscu) <= 0 and max(rise) <= 0.2 and min(rise) >= 0
gate(f"g3 the leftover oscillation Osc(T) = 4 int_gamma_1^T S w_T on [0.5, 1.6] T_1 at the five cells (its extrema exact: the minima at the zeros' cusps, the maxima by the analytic derivative on each arc): range " + ", ".join(f"{x:.3f}" for x in orng) + f" nats (gated within [0.3, 1.0], decreasing), mean " + ", ".join(f"{x:+.3f}" for x in omean) + f" against Osc_inf = 4 int_gamma_1^6990 S/r dr = {osc_inf:.4f} on the list (gated within 0.02; 1bs's 0.19), range times sqrt(T_1) " + ", ".join(f"{x:.2f}" for x in scal) + f" (gated within 15%: the sqrt(T) decay); sup|Osc - Osc_inf| " + ", ".join(f"{x:.3f}" for x in osup) + " against the block's bound with the list's suprema sup|S| = " + f"{sup_S:.3f} (gated [1.2, 1.5]), sup|S_1| = {sup_S1:.3f} (gated [1.3, 1.6]) and D = 1: " + ", ".join(f"{x:.3f}" for x in bnd) + f" (gated: each supremum below its bound, the bounds decreasing); at the 40 minimisers Osc(T_u) mean {mean(oscu):+.3f} (gated [-0.1, 0]: the selection), the smooth rise F^s(T_u) - F^s(T^s) at most {max(rise):.3f} (gated 0.2), and F_k(T_u) - F_k^s(T^s) mean {mean(dmin):+.3f} (gated |.| <= 0.1) rms {rms(dmin):.3f} (gated 0.12) over [{min(dmin):+.3f}, {max(dmin):+.3f}] (gated within [-0.3, 0.15])", ok)

# ---------------------------------------------------------------- g4: the exponent from the smooth count
rs = []; r1 = []
for (c, k), w in W.items():
    rs.append(w["c2"] + w["Fs_min"] - G[c]["Fs1"] - w["dl"]); r1.append(w["c2"] + w["F_u"] - G[c]["F1u"] - w["dl"])
ok = abs(mean(rs)) <= 0.25 and rms(rs) <= 0.25 and min(rs) >= -0.2 and max(rs) <= 0.5 and abs(mean(rs) - mean(r1)) <= 0.1 and abs(rms(rs) - rms(r1)) <= 0.05
gate(f"g4 the rung's exponent from the smooth count and the holes alone, ln lambda_k - ln lambda_1 against 2 ln|ghat_k(0)/ghat_1(0)| + F_k^s(T_k^s) - F_1^s(T_1^s) at the 40 rungs (formula less value): mean {mean(rs):+.3f} (gated |.| <= 0.25), rms {rms(rs):.3f} (gated 0.25), range [{min(rs):+.3f}, {max(rs):+.3f}] (gated within [-0.2, 0.5]); Theorem 1by's reading with the zeros, mean {mean(r1):+.3f}, rms {rms(r1):.3f}, range [{min(r1):+.3f}, {max(r1):+.3f}] (gated: the means within 0.1 and the rms within 0.05 of each other)", ok)

# ---------------------------------------------------------------- g5: the exterior tail by the explicit formula
def prime_powers(N):
    out = []; sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
    for p in range(2, int(N**0.5) + 1):
        if sieve[p]: sieve[p*p::p] = False
    for p in np.nonzero(sieve)[0]:
        q = int(p); lp = math.log(int(p))
        while q <= N: out.append((q, lp)); q *= int(p)
    return out
def product_form(c, r_):        # ln|ghat(r)| from the census: 2a v_0 sinc(ra) prod_designed (1 - r^2/tau^2) / prod_{0<j<K} (1 - r^2/omega_j^2)  (1bw's product form)
    K = CEN[c]["K"]; a = CEN[c]["delta"]/2
    des = np.array(sorted([z for _, z in r_["dodging"]] + list(r_["holes_fine"]) + list(r_["exterior"]) + ([abs(r_["sum_rule_residual"])**-0.5] if r_["n_complex"] == 1 and r_["sum_rule_residual"] < 0 else [])))
    assert len(des) == K - 1, (c, r_["k"], len(des), K)
    om = np.array([j*math.pi/a for j in range(1, K)]); lg0 = math.log(abs(r_["g0"]))
    def f(r):
        r = np.asarray(r, float); out = np.empty_like(r)
        for i0 in range(0, len(r), 8000):
            rr = r[i0:i0 + 8000]
            out[i0:i0 + 8000] = lg0 + np.log(np.abs(np.sinc(rr*a/math.pi))) + np.sum(np.log(np.abs(1 - (rr[:, None]/des[None, :])**2)), axis=1) - np.sum(np.log(np.abs(1 - (rr[:, None]/om[None, :])**2)), axis=1)
        return out
    return f
PPC = {}
def tail_identity(c, r_, p, T, Tp, D=1.0, h=0.05):
    a = CEN[c]["delta"]/2; delta = 2*a; lam = p["ln_lam"]; edge = r_["edge"]; lnf = product_form(c, r_)
    lst = np.array(p["ln_abs_g_at_zeros"])
    with np.errstate(divide="ignore"): pf = lnf(ZS)                                                         # -inf at a dodged zero whose stored designed zero equals it to double precision; replaced below
    lz = np.where(ZS > edge, pf, lst)         # the product form beyond the dodging edge, the stored arb values at the dodged zeros
    chi = lambda r: _ndtr((r - T)/D) - _ndtr((r - Tp)/D)
    lo, hi = max(T - 8*D, 0.5), Tp + 8*D; rr = lo + (np.arange(int((hi - lo)/h)) + 0.3141592653)*h       # the grid offset by an irrational fraction of a step: no exact hit on a sinc zero or a designed zero
    lg = lnf(rr); assert np.all(np.isfinite(lg)); G2 = np.exp(2*lg - lam)*chi(rr)
    sel = (ZS > lo) & (ZS < hi); tail = 2*float(np.sum(np.exp(2*lz[sel] - lam)*chi(ZS[sel])))
    eps = _digamma(0.25 + 0.5j*rr).real - np.log(rr/2)
    smooth = (1/math.pi)*h*float(np.sum(G2*np.log(rr/TWO_PI))); earch = (1/math.pi)*h*float(np.sum(G2*eps)); ebound = (1.5/math.pi)*h*float(np.sum(G2/rr**2))
    lpole = math.log(8*a) + a - (T*T - 0.25)/(2*D*D) - lam                                               # ln of the pole term's bound, in units of lambda
    Nmax = int(math.exp(delta + 7.5/D)) + 1
    if Nmax not in PPC: PPC[Nmax] = prime_powers(Nmax)
    PP = PPC[Nmax]; shells = 0.0; top = (0, 0.0)
    for i0 in range(0, len(PP), 64):
        blk = PP[i0:i0 + 64]; ln_n = np.array([math.log(n) for n, _ in blk]); fn = (1/math.pi)*h*(np.cos(np.outer(ln_n, rr)) @ G2)
        for (n, lp), fv in zip(blk, fn):
            t = 2*lp*n**-0.5*float(fv); shells += t
            if abs(t) > abs(top[1]): top = (n, t)
    return dict(tail=tail, smooth=smooth, earch=earch, ebound=ebound, shells=shells, top=top, resid=(smooth + earch - shells - tail)/tail, lpole=lpole, pfmax=float(np.max(np.abs(pf[ZS > edge] - lst[ZS > edge]))))
XG = {}; XR = {}
for c in ORDER:
    S = CEN[c]; P = PRO[c]; g = S["rungs"][0]; p1 = P["rungs"][0]; T1 = g["edge"]; ns = n_safe(c)
    XG[c] = [tail_identity(c, g, p1, T, Tp) for (T, Tp) in ((T1, 6980.0), (T1, 1.25*T1), (1.25*T1, 2*T1), (2*T1, 4*T1), (4*T1, 6980.0))]
    for r_, p in zip(S["rungs"][1:ns + 1], P["rungs"][1:ns + 1]):
        XR[(c, r_["k"])] = [tail_identity(c, r_, p, T, Tp) for (T, Tp) in ((T1, 6980.0), (T1, 1.25*T1))]
res_g = [abs(x["resid"]) for c in ORDER for x in XG[c]]; res_far = [abs(x["resid"]) for c in ORDER for x in XG[c][2:]]; res_r = [abs(x["resid"]) for v in XR.values() for x in v]
pfm = max([x["pfmax"] for c in ORDER for x in XG[c][:1]] + [v[0]["pfmax"] for v in XR.values()])
ratio_all = [XG[c][0]["smooth"]/XG[c][0]["tail"] for c in ORDER]; ratio_near = [XG[c][1]["smooth"]/XG[c][1]["tail"] for c in ORDER]; ratio_far = [XG[c][4]["smooth"]/XG[c][4]["tail"] for c in ORDER]
ratio_mid = [XG[c][2]["smooth"]/XG[c][2]["tail"] for c in ORDER]; ratio_2 = [XG[c][3]["smooth"]/XG[c][3]["tail"] for c in ORDER]
left = [abs(x["earch"])/x["tail"] for c in ORDER for x in XG[c]]; lbnd = [x["ebound"]/x["tail"] for c in ORDER for x in XG[c]]; ea_ok = all(abs(x["earch"]) <= x["ebound"] for c in ORDER for x in XG[c])
lpole = max(x["lpole"] for c in ORDER for x in XG[c]); tops = [XG[c][0]["top"][0] for c in ORDER]; tops_near = [XG[c][1]["top"][0] for c in ORDER]
rr_all = [v[0]["smooth"]/v[0]["tail"] for v in XR.values()]; rr_near = [v[1]["smooth"]/v[1]["tail"] for v in XR.values()]
ok = max(res_g) <= 1e-5 and max(res_far) <= 1e-9 and max(res_r) <= 1e-9 and pfm <= 1e-4 and ea_ok and max(left) <= 1e-5 and max(lbnd) <= 2e-4 and lpole <= -1000
ok &= all(1.8 <= x <= 3.0 for x in ratio_all) and all(1.9 <= x <= 4.5 for x in ratio_near) and all(0.99 <= x <= 1.2 for x in ratio_far) and all(1.3 <= x <= 3.6 for x in ratio_mid) and all(1.2 <= x <= 2.0 for x in ratio_2)
ok &= all(t in (2, 3, 5, 7) for t in tops) and 1.5 <= min(rr_all) and max(rr_all) <= 4.0 and 1.5 <= min(rr_near) and max(rr_near) <= 8.0
gate(f"g5 the exterior tail by the explicit formula (the cut chi = Phi((r - T)/D) - Phi((r - T')/D), D = 1, the grid h = 0.05, the shells to e^(delta + 7.5)): 2 sum ghat^2 chi = (1/pi) int ghat^2 chi ln(r/2pi) dr + E_arch - 2 sum Lambda(n) n^-1/2 f_chi(ln n) within {max(res_g):.1e} relative at the five ground states over the windows [T_1, 6980], [1, 1.25], [1.25, 2], [2, 4], [4, 6980/T_1] T_1 (gated 1e-5; the windows away from the cut at the edge within {max(res_far):.1e}, gated 1e-9 -- the residual at the edge is the stored arb profile's 1e-4 rounding at the dodged zeros the cut still weighs) and within {max(res_r):.1e} at the 40 rungs over [T_1, 6980] and [T_1, 1.25 T_1] (gated 1e-9); the product form against the stored profile beyond the edge within {pfm:.1e} at the 45 states (gated 1e-4); the leftover after the shells, E_arch/tail at most {max(left):.1e} (gated 1e-5), below its Binet bound (3/2pi) int ghat^2 chi r^-2 at every window (gated), the bound at most {max(lbnd):.1e} of the tail (gated 2e-4); the pole term below e^{lpole:.0f} of the tail (gated e^-1000); the smooth count's integral over the actual exterior leakage: " + ", ".join(f"{x:.2f}" for x in ratio_all) + f" over the whole exterior (gated [1.8, 3.0]), " + ", ".join(f"{x:.2f}" for x in ratio_near) + f" in the near quarter [T_1, 1.25 T_1] (gated [1.9, 4.5]), " + ", ".join(f"{x:.2f}" for x in ratio_mid) + " on [1.25, 2] T_1 (gated [1.3, 3.6]), " + ", ".join(f"{x:.2f}" for x in ratio_2) + " on [2, 4] T_1 (gated [1.2, 2.0]), " + ", ".join(f"{x:.3f}" for x in ratio_far) + f" beyond 4 T_1 (gated [0.99, 1.2]); the largest shell over the whole exterior n = " + ", ".join(str(t) for t in tops) + f" (gated among 2, 3, 5, 7), in the near quarter n = " + ", ".join(str(t) for t in tops_near) + f"; at the 40 rungs smooth/tail runs {min(rr_all):.2f}-{max(rr_all):.2f} over the whole exterior (gated within [1.5, 4.0]) and {min(rr_near):.2f}-{max(rr_near):.2f} in the near quarter (gated within [1.5, 8.0])", ok)

if os.environ.get("SMOOTH_DUMP"):
    dump = dict(osc_inf=osc_inf, sup_S=sup_S, sup_S1=sup_S1, c0f=c0f, G={c: {k: v for k, v in G[c].items()} for c in ORDER}, W=[dict((k, v) for k, v in w.items()) for w in ALL],
                tsu=tsu, tsu_hm=tsu_hm, tsw=tsw, tcu=tcu, tc2u=tc2u, tc2s=tc2s, lawres=lawres, curv_min=curv_min, ts0=ts0, tsu1=tsu1, tsT1=tsT1, epsr=epsr, cfd=cfd, cfd_r=cfd_r,
                orng=orng, osup=osup, omean=omean, scal=scal, bnd=bnd, oscu=oscu, dmin=dmin, rise=rise, rs=rs, r1=r1,
                XG={c: XG[c] for c in ORDER}, XR={f"{c}:{k}": v for (c, k), v in XR.items()}, res_g=res_g, res_far=res_far, res_r=res_r, pfm=pfm, ratio_all=ratio_all, ratio_near=ratio_near,
                ratio_far=ratio_far, ratio_mid=ratio_mid, ratio_2=ratio_2, left=left, lbnd=lbnd, lpole=lpole, tops=tops, tops_near=tops_near, rr_all=rr_all, rr_near=rr_near)
    json.dump(dump, open(os.environ["SMOOTH_DUMP"], "w"), default=float, indent=1)

# ---------------------------------------------------------------- g6: the paper's numbers parsed back from the declared needles
import paper_needles
S_WALL = 'T^s/T_u averages 1.003 with rms deviation from 1 of 0.019 over [0.969, 1.063] at the 40 rungs (1.001 with 0.015 at the 30 with three or more holes), against 1.028 with 0.039 for 1by’s law without the constant; the closed form T ln(2T₀/T) = 4m + 7/2 reproduces T^s within 0.13% rms, and T^s/T_w averages 0.962 over [0.875, 1.034]'
S_GROUND = 'the ground state’s smooth wall sits at T^s/T₀ = 1.923, 1.943, 1.958, 1.972, 1.983 at the five cells, within 2.1% of its unlocking height T_u(1) (T^s/T_u(1) over [0.983, 1.021])'
S_MIN = 'F₁^s(T^s) sits 0.0041, 0.0022, 0.0012, 0.0005, 0.0002 nats below the closed form at the five cells, the difference falling with δ, and at the 40 rungs the closed form sits within 1.23 nats of F_k^s(T^s)'
S_OSC = 'on [0.5, 1.6]T₁ the leftover ranges over 0.88, 0.76, 0.68, 0.56, 0.44 nats at the five cells with means 0.19–0.20 against Osc_∞ = 0.19 on the list, the range times √T₁ constant to 8% (8.2–8.9)'
S_BOUND = 'with the list’s suprema sup|S| = 1.36 and sup|S₁| = 1.47 below height 6990 and Δ = 1, the bound reads 1.66, 1.42, 1.21, 1.00, 0.77 nats at T₁ against the observed sup|Osc − Osc_∞| of 0.52, 0.42, 0.40, 0.32, 0.25'
S_DMIN = 'F_k(T_u) − F_k^s(T^s) averages −0.03 with rms 0.08 over [−0.23, +0.08] at the 40 rungs, Osc(T_u) itself averaging −0.06'
S_EXP = 'the residual averages +0.15 with rms 0.20 over [−0.11, +0.42] at the 40 rungs, against +0.13, 0.19 and [−0.16, +0.43] for 1by’s reading with the zeros'
S_ID = 'the identity holds within 4.4 × 10⁻⁶ of the tail at the five ground states over the five windows (6.7 × 10⁻¹² away from the cut at the edge, where the dodged zeros the cut still weighs carry the stored profile’s rounding) and within 2.7 × 10⁻¹¹ at the 40 rungs'
S_RATIO = 'the smooth count’s integral is 1.87, 1.87, 2.29, 2.88, 2.77 times the actual leakage over the whole exterior at the five cells, 2.42, 2.01, 3.06, 4.21, 3.71 in the near quarter [T₁, 1.25T₁], 1.71, 2.14, 2.00, 2.20, 3.40 on [1.25, 2]T₁, 1.28, 1.65, 1.60, 1.91, 1.46 on [2, 4]T₁ and 1.119, 1.151, 1.066, 1.000, 1.003 beyond 4T₁'
S_LEFT = 'the leftover after the shells is at most 4.0 × 10⁻⁶ of the tail, its Binet bound at most 1.4 × 10⁻⁴'
S_TOP = 'the largest shell is n = 3, 3, 7, 5, 2 over the whole exterior and n = 3, 5, 7, 5, 2 in the near quarter'
S_RUNGS = 'at the 40 rungs the smooth count’s integral runs 1.58–3.77 times the leakage beyond T₁ and 1.85–7.37 times it in the near quarter'
# each call carries its literal (the precheck's clause D); the strings equal the S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, 'T^s/T_u averages 1.003 with rms deviation from 1 of 0.019 over [0.969, 1.063] at the 40 rungs (1.001 with 0.015 at the 30 with three or more holes), against 1.028 with 0.039 for 1by’s law without the constant; the closed form T ln(2T₀/T) = 4m + 7/2 reproduces T^s within 0.13% rms, and T^s/T_w averages 0.962 over [0.875, 1.034]', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the ground state’s smooth wall sits at T^s/T₀ = 1.923, 1.943, 1.958, 1.972, 1.983 at the five cells, within 2.1% of its unlocking height T_u(1) (T^s/T_u(1) over [0.983, 1.021])', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'F₁^s(T^s) sits 0.0041, 0.0022, 0.0012, 0.0005, 0.0002 nats below the closed form at the five cells, the difference falling with δ, and at the 40 rungs the closed form sits within 1.23 nats of F_k^s(T^s)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'on [0.5, 1.6]T₁ the leftover ranges over 0.88, 0.76, 0.68, 0.56, 0.44 nats at the five cells with means 0.19–0.20 against Osc_∞ = 0.19 on the list, the range times √T₁ constant to 8% (8.2–8.9)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'with the list’s suprema sup|S| = 1.36 and sup|S₁| = 1.47 below height 6990 and Δ = 1, the bound reads 1.66, 1.42, 1.21, 1.00, 0.77 nats at T₁ against the observed sup|Osc − Osc_∞| of 0.52, 0.42, 0.40, 0.32, 0.25', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'F_k(T_u) − F_k^s(T^s) averages −0.03 with rms 0.08 over [−0.23, +0.08] at the 40 rungs, Osc(T_u) itself averaging −0.06', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the residual averages +0.15 with rms 0.20 over [−0.11, +0.42] at the 40 rungs, against +0.13, 0.19 and [−0.16, +0.43] for 1by’s reading with the zeros', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the identity holds within 4.4 × 10⁻⁶ of the tail at the five ground states over the five windows (6.7 × 10⁻¹² away from the cut at the edge, where the dodged zeros the cut still weighs carry the stored profile’s rounding) and within 2.7 × 10⁻¹¹ at the 40 rungs', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the smooth count’s integral is 1.87, 1.87, 2.29, 2.88, 2.77 times the actual leakage over the whole exterior at the five cells, 2.42, 2.01, 3.06, 4.21, 3.71 in the near quarter [T₁, 1.25T₁], 1.71, 2.14, 2.00, 2.20, 3.40 on [1.25, 2]T₁, 1.28, 1.65, 1.60, 1.91, 1.46 on [2, 4]T₁ and 1.119, 1.151, 1.066, 1.000, 1.003 beyond 4T₁', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the leftover after the shells is at most 4.0 × 10⁻⁶ of the tail, its Binet bound at most 1.4 × 10⁻⁴', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the largest shell is n = 3, 3, 7, 5, 2 over the whole exterior and n = 3, 5, 7, 5, 2 in the near quarter', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'at the 40 rungs the smooth count’s integral runs 1.58–3.77 times the leakage beyond T₁ and 1.85–7.37 times it in the near quarter', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g6'] == [S_WALL, S_GROUND, S_MIN, S_OSC, S_BOUND, S_DMIN, S_EXP, S_ID, S_RATIO, S_LEFT, S_TOP, S_RUNGS]
_re = __import__("re")
def _num(s): return float(s.strip().replace('−', '-'))
def _nums(s, pat=r"([-−+]?[0-9]+\.[0-9]+)"): return [_num(x) for x in _re.findall(pat, s)]
def _ints(s): return [int(x) for x in _re.findall(r"(?<![0-9.−-])[0-9]+(?![0-9.])", s)]
def _sci(s):   # a × 10^b with superscript digits -> float
    m = _re.search(r"([0-9.]+) × 10([⁻⁰¹²³⁴⁵⁶⁷⁸⁹]+)", s); e = m.group(2).replace("⁻", "-")
    for i, c in enumerate("⁰¹²³⁴⁵⁶⁷⁸⁹"): e = e.replace(c, str(i))
    return float(f"{m.group(1)}e{int(e)}")   # the same float as _r1's repr, no power-of-ten rounding
def _r1(x): return float(f"{x:.1e}")
ok &= _nums(S_WALL.split("averages ")[1].split(" at the 40")[0]) == [round(mean(tsu), 3), round(rms1(tsu), 3), round(min(tsu), 3), round(max(tsu), 3)] and _nums(S_WALL.split("(")[1].split(" at the 30")[0]) == [round(mean(tsu_hm), 3), round(rms1(tsu_hm), 3)]
ok &= _nums(S_WALL.split("against ")[1].split(" for 1by")[0]) == [round(mean(tcu), 3), round(rms1(tcu), 3)] and _nums(S_WALL.split("within ")[1].split("%")[0]) == [round(100*rms1(tc2s), 2)] and _nums(S_WALL.split("T^s/T_w averages ")[1]) == [round(mean(tsw), 3), round(min(tsw), 3), round(max(tsw), 3)]
ok &= _nums(S_GROUND.split("T^s/T₀ = ")[1].split(" at the five")[0]) == [round(x, 3) for x in ts0] and _nums(S_GROUND.split("within ")[1].split("%")[0]) == [round(100*max(abs(x - 1) for x in tsu1), 1)] and _nums(S_GROUND.split("over ")[1]) == [round(min(tsu1), 3), round(max(tsu1), 3)]
ok &= _nums(S_MIN.split("sits ")[1].split(" nats")[0]) == [round(abs(x), 4) for x in cfd] and all(cfd[i] < cfd[i + 1] for i in range(4)) and _nums(S_MIN.split("within ")[1].split(" nats")[0]) == [round(abs(min(cfd_r)), 2)]
ok &= _nums(S_OSC.split("ranges over ")[1].split(" nats")[0]) == [round(x, 2) for x in orng] and _nums(S_OSC.split("with means ")[1].split(" against")[0]) == [round(min(omean), 2), round(max(omean), 2)] and _nums(S_OSC.split("Osc_∞ = ")[1].split(" on the list")[0]) == [round(osc_inf, 2)] and _ints(S_OSC.split("constant to ")[1].split("%")[0]) == [round(100*(max(scal)/min(scal) - 1))] and _nums(S_OSC.split("(")[-1].split(")")[0]) == [round(min(scal), 1), round(max(scal), 1)]
ok &= _nums(S_BOUND.split("sup|S| = ")[1].split(" and")[0]) == [round(sup_S, 2)] and _nums(S_BOUND.split("sup|S₁| = ")[1].split(" below")[0]) == [round(sup_S1, 2)] and _nums(S_BOUND.split("reads ")[1].split(" nats")[0]) == [round(x, 2) for x in bnd] and _nums(S_BOUND.split("Osc_∞| of ")[1]) == [round(x, 2) for x in osup]
ok &= _nums(S_DMIN.split("averages ")[1].split(" at the 40")[0]) == [round(mean(dmin), 2), round(rms(dmin), 2), round(min(dmin), 2), round(max(dmin), 2)] and _nums(S_DMIN.split("averaging ")[1]) == [round(mean(oscu), 2)]
ok &= _nums(S_EXP.split("averages ")[1].split(" at the 40")[0]) == [round(mean(rs), 2), round(rms(rs), 2), round(min(rs), 2), round(max(rs), 2)] and _nums(S_EXP.split("against ")[1].split(" for 1by")[0]) == [round(mean(r1), 2), round(rms(r1), 2), round(min(r1), 2), round(max(r1), 2)]
ok &= _sci(S_ID.split("holds within ")[1]) == _r1(max(res_g)) and _sci(S_ID.split("windows (")[1]) == _r1(max(res_far)) and _sci(S_ID.split("and within ")[1]) == _r1(max(res_r))
ok &= _nums(S_RATIO.split("integral is ")[1].split(" times the actual")[0]) == [round(x, 2) for x in ratio_all] and _nums(S_RATIO.split("five cells, ")[1].split(" in the near")[0]) == [round(x, 2) for x in ratio_near] and _nums(S_RATIO.split("1.25T₁], ")[1].split(" on [1.25")[0]) == [round(x, 2) for x in ratio_mid] and _nums(S_RATIO.split("2]T₁, ")[1].split(" on [2, 4]")[0]) == [round(x, 2) for x in ratio_2] and _nums(S_RATIO.split("4]T₁ and ")[1].split(" beyond")[0]) == [round(x, 3) for x in ratio_far]
ok &= _sci(S_LEFT.split("at most ")[1]) == _r1(max(left)) and _sci(S_LEFT.split("bound at most ")[1]) == _r1(max(lbnd))
ok &= _ints(S_TOP.split("n = ")[1].split(" over")[0]) == list(tops) and _ints(S_TOP.split("n = ")[2].split(" in the")[0]) == list(tops_near)
ok &= _nums(S_RUNGS.split("runs ")[1].split(" times the leakage")[0]) == [round(min(rr_all), 2), round(max(rr_all), 2)] and _nums(S_RUNGS.split("and ")[1].split(" times it")[0]) == [round(min(rr_near), 2), round(max(rr_near), 2)]
gate("g6 the paper's numbers parsed back from the declared needles", ok)

# ---------------------------------------------------------------- g7
from cascade_tower import chain_ok
gate("g7 the chain obligation to cascade_gap_law.py (Theorem 1bz) met", chain_ok("cascade_gap_law.py"))

# ---------------------------------------------------------------- g8
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g8 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g8 the 1ca paper needles and the footer census (declared surface)", ok)

print(("ALL GATES PASS (9/9)" if not fails else f"FAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
