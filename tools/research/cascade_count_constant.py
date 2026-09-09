#!/usr/bin/env python3
"""Theorem 1bs -- the count-constant theorem: the discrete-to-continuum
correction of the finite-delta formula's balayage sum is 4 c_L ln T + C_L +
o(1), c_L the constant term of the Riemann-von Mangoldt formula (7/8 for zeta:
the pole's 1 less the Gamma_R's 1/8; kappa/4 - 1/8 for a real character; 11/4
for Delta), proved by one Stieltjes integration by parts; on the slack law it
says 1bm(v)'s "2 s_delta(2 T_0) + 4 pi e^delta" is (7/2)(delta + ln 4 pi) +
C_zeta + o(1) -- slope 7/2 exactly, the pole worth four orders in Fuchs' law.
Substrate balayage_count.py (imported, content-addressed); the zero lists as
data. Tower member 28 (top).

THE CLAIMS GATED. (0) THE CONSTANTS: c_L = [pole] + sum(kappa_i/4 - 1/8) and
4 c_L = 4 [pole] + sum(kappa_i - 1/2) agree for the five forms and equal 7/2,
1/2, 1/2, -1/2, 11 (exact fractions); the lists' counts against N_0 + c_L
within 1 at their last zero. (1) THE IDENTITY: B(T) - I(T) equals the
Stieltjes right-hand side int_0^T (N - N_0) 4/(r sqrt(1 - r^2/T^2)) dr,
evaluated exactly per interval (the N_0 piece by adaptive quadrature), below 1e-6 at three heights per form -- the
integration by parts of the proof, as computation. (2) THE SLOPES: the
least-squares slope of B - I against ln T (twelve log-spaced heights on
[max(40, 3 gamma_1), T_last], every height inside the list's coverage --
round 319 F319-1) within 0.05 (zeta), 0.15 (Delta)
and 0.5 (the characters, whose short lists fix no slope -- round 317 F317-6)
of 4 c_L; a wrong constant (7/8
-> 1 or 3/4 for zeta) fails the band; over the four-window set lo in
{2 gamma_1, max(40, 3 gamma_1)}, hi in {T_last, 0.75 T_last} (twelve heights
each) the fits' spans are as the paper states (outward 0.01), zeta's and
Delta's spans enclose 7/2 and 11, and chi_8's every window lies below -1/2
(round 318 F318-2). (3) THE CONSTANTS C_L: the residual
B - I - 4 c_L ln T for zeta over [max(40, 3 gamma_1), T_last] has an exact range
(concave per inter-zero arc with infinite slope at each arc's left end: the
minimum over the window at a zero or a window end, the maximum at an interior
critical point or an arc's right end, all searched -- round 319 F319-2, round
320 F320-1) of width at most 1.0 (the
S(T) fluctuation) whose mean is C_zeta from the closed formula within 0.1; the formula's three parts
and the five C_L printed. (4) THE 1bm CONSEQUENCE: at the seven cells B(2T_0)
- I(2T_0) (= 1bm(v)'s difference, recomputed) lies within 0.5 of (7/2) ln(4
pi e^delta) + C_zeta; the residual c(delta) of 1bm(v) (recomputed from
slack_law_flint's ln lambda_1 and 1bm's minimiser) has least-squares slope
against ln T_0 in [1.1, 1.5] and reproduces 1bm(v)'s seven values within
0.01; d(delta) = 2 s_delta(2T_0) - min_T 2 s_delta(T) at every cell
(nonnegative up to the grid by construction, so not gated as a sign; the
seven values pinned in (6)), the slope of c - d in [1.4, 1.8], 7/2 + that
slope within 0.1 of the direct slope of ln lambda_1 + 4 pi e^delta
(1bm(vii)'s 5.04) -- round 317 F317-1: the equation of (iv) carries
-d(delta) -- and the exact bookkeeping direct = 7/2 + slope(c - d) +
slope(dev) with dev the seven-cell deviations (least squares is linear;
round 318 C318-1), the balance slope(dev) pinned. (5) mangle probes; (6) the paper's numbers parsed back; (7) the chain
obligation to cascade_spectrum_ladder.py; (8) the needles and census.

WHAT IS NOT CLAIMED. Nothing about the ladder's rungs k >= 2; nothing about
c(delta) beyond its measured slope; the constants C_L are floating-point
evaluations on double-precision lists; no Riemann Hypothesis consequence.
"""
import math, os, sys, json
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from balayage_count import FORMS, count_constant, four_cL_formula, load_zeros, B, I, stieltjes_rhs, residual, slope, C_from_formula, N0
from slack_law_flint import run as run_SL
from scipy.optimize import minimize_scalar

PAPER_NEEDLES = [
    {'g': 'g8', 's': 'Theorem 1bs (the count-constant theorem', 'form': 'plain'},
    {'g': 'g8', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 10},
    {'s': '`cascade_count_constant.py`', 'min': 2, 'g': 'g8'},
    {'s': 'the **96 scripts cited in place** above', 'form': 'ws', 'g': 'g8'},
    {'s': 'extended by Theorems 1i–1bt:', 'form': 'ws', 'g': 'g8'},
    {'g': 'g6', 's': '3.48, 0.44, 0.61, −0.67, 10.92', 'form': 'ws'},
    {'g': 'g6', 's': '[3.52, 4.41]', 'form': 'ws'},
    {'g': 'g6', 's': '4.05', 'form': 'ws'},
    {'g': 'g6', 's': '−6.84, 10.70, 0.19', 'form': 'ws'},
    {'g': 'g6', 's': 'C_Δ with its tail is 0.35 (0.56 without it)', 'form': 'ws'},
    {'g': 'g6', 's': '2.89, 2.24, 1.22 for χ₋₃, χ₋₄, χ₈', 'form': 'ws'},
    {'g': 'g6', 's': 'sit within 0.4 of (7/2)ln(4πeᵟ) + C_ζ at the cells', 'form': 'ws'},
    {'g': 'g6', 's': '1.28 for c(δ) and −0.32 for d(δ), 1.59 for c − d', 'form': 'ws'},
    {'g': 'g6', 's': 'd(δ) := 2s_δ(2T₀) − min_T 2s_δ(T) = 1.18, 0.69, 0.27, 0.59, 0.14, 0.33, 0.29 at the cells', 'form': 'ws'},
    {'g': 'g6', 's': '7/2 + 1.59 = 5.09 against the directly fitted slope of ln λ₁ + 4πeᵟ, 5.04', 'form': 'ws'},
    {'g': 'g6', 's': 'the fits span 0.37–0.55, 0.45–0.64 and −0.85 to −0.50 for χ₋₃, χ₋₄, χ₈', 'form': 'ws'},
    {'g': 'g6', 's': 'ζ spans 3.45–3.51 and Δ 10.78–11.06', 'form': 'ws'},
    {'g': 'g6', 's': "and the cells' o(1) the balance −0.05", 'form': 'ws'},
    {'g': 'g6', 's': 'the highest −0.51 to the nearest 0.01', 'form': 'ws'},
    {'g': 'g6', 's': 'here the minimum is at the zero 48.01 and the maximum interior, at T = 44.54', 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

FORDER = ["zeta", "chi_-3", "chi_-4", "chi_8", "Delta"]
ZS = {f: load_zeros(FORMS[f]) for f in FORDER}
EXACT = {"zeta": Fraction(7, 2), "chi_-3": Fraction(1, 2), "chi_-4": Fraction(1, 2), "chi_8": Fraction(-1, 2), "Delta": Fraction(11)}
SLOPE_BAND = {"zeta": 0.05, "chi_-3": 0.5, "chi_-4": 0.5, "chi_8": 0.5, "Delta": 0.15}   # round 317 F317-6: the characters' lists fix no slope

# ---------------------------------------------------------------- g0
ok = True
for f in FORDER:
    F = FORMS[f]; cL = Fraction(1 if F["pole"] else 0) + sum(Fraction(k).limit_denominator(2)/4 - Fraction(1, 8) for k in F["kappas"])
    ok &= 4*cL == EXACT[f] and abs(4*count_constant(F) - float(EXACT[f])) < 1e-12 and abs(four_cL_formula(F) - float(EXACT[f])) < 1e-12
    zs = ZS[f]; T = float(zs[-1]); smooth = N0(np.array([T]), F["q"], F["d"])[0] + count_constant(F)
    ok &= abs(len(zs) - smooth) <= 1.0
gate("g0 the constants: c_L = [pole] + sum(kappa_i/4 - 1/8), 4 c_L = 4[pole] + sum(kappa_i - 1/2) = 7/2, 1/2, 1/2, -1/2, 11 for zeta, chi_-3, chi_-4, chi_8, Delta (exact); each list's count within 1 of N_0 + c_L at its last zero", ok)

# ---------------------------------------------------------------- g1
ok = True; worst = 0.0
for f in FORDER:
    F = FORMS[f]; zs = ZS[f]
    for frac in (0.3, 0.6, 0.95):
        T = float(zs[0])*3 + frac*(float(zs[-1]) - float(zs[0])*3)
        lhs = B(zs, T) - I(T, F["q"], F["d"]); rhs = stieltjes_rhs(zs, T, F["q"], F["d"])
        worst = max(worst, abs(lhs - rhs)); ok &= abs(lhs - rhs) <= 1e-6
gate(f"g1 the identity of the proof as computation: B - I equals the Stieltjes right-hand side int_0^T (N - N_0) 4/(r sqrt(1 - r^2/T^2)) dr at three heights on every list (max |diff| {worst:.1e})", ok)

# ---------------------------------------------------------------- g2
ok = True; slopes = {}
for f in FORDER:
    F = FORMS[f]; zs = ZS[f]
    lo = max(40.0, 3*float(zs[0])); hi = float(zs[-1])            # round 319 F319-1: every height inside the list's coverage (zeta's former [42, 7000] ran past T_last = 6996.89)
    sl, ic, Ts, y = slope(zs, F, lo, hi); slopes[f] = sl
    ok &= float(np.max(Ts)) <= float(zs[-1]) + 1e-9            # against the list itself, not the alias hi (round 320 F320-2)
    ok &= abs(sl - float(EXACT[f])) <= SLOPE_BAND[f]
# a wrong constant for zeta fails the band
ok &= abs(slopes["zeta"] - 4.0) > SLOPE_BAND["zeta"] and abs(slopes["zeta"] - 3.0) > SLOPE_BAND["zeta"]
# round 318 F318-2: the four-window set lo in {2 gamma_1, max(40, 3 gamma_1)}, hi in {T_last, 0.75 T_last}, twelve heights each
spans = {}
for f in FORDER:
    zs = ZS[f]; g1 = float(zs[0]); Tl = float(zs[-1])
    vals = [slope(zs, FORMS[f], lo, hi, 12)[0] for lo in (2*g1, max(40.0, 3*g1)) for hi in (Tl, 0.75*Tl)]
    spans[f] = (min(vals), max(vals))
ok &= spans["zeta"][0] <= 3.5 <= spans["zeta"][1] and spans["Delta"][0] <= 11.0 <= spans["Delta"][1] and spans["chi_8"][1] < -0.5
gate("g2 the slopes of B - I against ln T (least squares over twelve log-spaced heights on [max(40, 3 gamma_1), T_last], every height inside the list's coverage): " + ", ".join(f"{f}: {slopes[f]:+.3f} (4c_L = {float(EXACT[f]):+.1f}, band {SLOPE_BAND[f]})" for f in FORDER) + "; the constants 1 and 3/4 in place of 7/8 fail zeta's band"
     + "; over the four-window set the spans are " + ", ".join(f"{f}: [{spans[f][0]:+.4f}, {spans[f][1]:+.4f}]" for f in FORDER) + " (zeta's and Delta's enclose 7/2 and 11; chi_8's every window below -1/2)", ok)

# ---------------------------------------------------------------- g3
ok = True; Cf = {}; parts = {}
for f in FORDER:
    Cf[f], parts[f] = C_from_formula(ZS[f], FORMS[f], float(ZS[f][-1]))
zs = ZS["zeta"]; ZLO = max(40.0, 3*float(zs[0])); ZHI = float(zs[-1])
# round 319 F319-2: the exact range of the residual over [ZLO, ZHI] -- on each inter-zero arc B - I - (7/2) ln T is concave
# (B'' = -4 sum T/(T^2 - gamma^2)^{3/2} on the arc, the smooth part's second derivative -(T - 7/2)/T^2 < 0), so the minimum
# sits at an endpoint (a zero) and the maximum at an interior critical point, found by bounded minimisation of the negative
_f = lambda T: residual(zs, T, FORMS["zeta"])
_pts = [ZLO] + [float(g) for g in zs[(zs > ZLO) & (zs < ZHI)]] + [ZHI]
_vals = [_f(p) for p in _pts]
res_min = min(_vals); res_argmin = _pts[int(np.argmin(_vals))]
res_max = max(_vals); res_argmax = _pts[int(np.argmax(_vals))]; res_max_interior = False     # round 320 F320-1: the endpoints (zeros, window ends) searched too
for _a, _b in zip(_pts[:-1], _pts[1:]):
    _r = minimize_scalar(lambda T: -_f(T), bounds=(_a + 1e-9, _b - 1e-9), method="bounded", options={"xatol": 1e-8})
    if -float(_r.fun) > res_max: res_max, res_argmax, res_max_interior = -float(_r.fun), float(_r.x), _b - float(_r.x) > 1e-6 and float(_r.x) - _a > 1e-6
res_min_at_zero = any(abs(res_argmin - g) < 1e-9 for g in zs)
Ts = np.exp(np.linspace(math.log(ZLO), math.log(ZHI), 4000))
res = np.array([_f(T) for T in Ts])
ok &= res_max - res_min <= 1.0 and abs(res.mean() - Cf["zeta"]) <= 0.1 and res_min <= res.min() and res.max() <= res_max
ok &= abs(parts["Delta"][3] + 0.205) <= 0.01 and abs(parts["zeta"][3]) <= 1e-4        # round 317 F317-2: Delta's Stirling tail -0.20, zeta's nil
gate(f"g3 the constants: zeta's residual B - I - (7/2) ln T over T in [{ZLO:.2f}, {ZHI:.2f}] has the exact range [{res_min:.4f}, {res_max:.4f}] (the minimum at T = {res_argmin:.4f}, a zero: {res_min_at_zero}; the maximum at T = {res_argmax:.4f}, interior: {res_max_interior}; width <= 1.0: the S(T) fluctuation; the 4000-height sample inside it), its 4000-height mean {res.mean():.3f} within 0.1 of the closed formula's C_zeta = {Cf['zeta']:.3f} (parts {parts['zeta'][0]:.3f}, {parts['zeta'][1]:.3f}, {parts['zeta'][2]:.3f}, tail {parts['zeta'][3]:.4f}); "
     + "C_L by formula with the Stirling tail: " + ", ".join(f"{f}: {Cf[f]:.3f} (tail {parts[f][3]:+.3f})" for f in FORDER), ok)

# ---------------------------------------------------------------- g4
ORDER = ["d1.0", "d1.38", "d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
DELTAS = {"d1.0": 1.0, "d1.38": 1.3828125, "d2.0": 2.0, "d2.3": 2.3, "d2.6": 2.6, "d3.0": 3.0, "d3.5": 3.5}
ZETA_C = [4.70, 5.21, 5.94, 6.39, 6.64, 7.30, 7.90]     # 1bm(v)
def s_delta(delta, T):
    a = delta/2; z = zs[zs < T]
    return 2*np.sum(np.log((1 + np.sqrt(1 - z*z/(T*T)))*T/z)) - a*T
def formula_min(delta):
    T0 = 2*math.pi*math.exp(delta)
    grid = np.linspace(1.2*T0, 3.0*T0, 20001); vals = np.array([2*s_delta(delta, T) for T in grid]); k = int(np.argmin(vals))
    lo, hi = grid[max(k - 1, 0)], grid[min(k + 1, len(grid) - 1)]
    pts = [lo] + list(zs[(zs > lo) & (zs < hi)]) + [hi]; best = float(vals[k])
    for a_, b_ in zip(pts[:-1], pts[1:]):
        r = minimize_scalar(lambda T: 2*s_delta(delta, T), bounds=(a_ + 1e-9, b_ - 1e-9), method="bounded", options={"xatol": 1e-10})
        best = min(best, float(r.fun))
    return best
ok = True; dev = {}; cvals = {}; dvals = {}
for i, c in enumerate(ORDER):
    d = DELTAS[c]; T0 = 2*math.pi*math.exp(d)
    dvals[c] = B(zs, 2*T0) - I(2*T0, 1, 1)
    ok &= abs(dvals[c] - (2*s_delta(d, 2*T0) + 4*math.pi*math.exp(d))) <= 1e-9          # 1bm(v)'s quantity, the same number
    pred = 3.5*math.log(2*T0) + Cf["zeta"]; dev[c] = dvals[c] - pred; ok &= abs(dev[c]) <= 0.5
    cvals[c] = run_SL(c)["ln_eig"] - formula_min(d); ok &= abs(cvals[c] - ZETA_C[i]) <= 0.01
x = np.log([2*math.pi*math.exp(DELTAS[c]) for c in ORDER]); y = np.array([cvals[c] for c in ORDER])
A = np.vstack([x, np.ones_like(x)]).T; cslope = float(np.linalg.lstsq(A, y, rcond=None)[0][0])
ok &= 1.1 <= cslope <= 1.5
# round 317 F317-1: c(delta) is against the discrete minimum; d(delta) = 2 s_delta(2T_0) - min 2 s_delta, its slope, and the bookkeeping against 1bm(vii)'s 5.04
dv = {c: 2*s_delta(DELTAS[c], 2*2*math.pi*math.exp(DELTAS[c])) - formula_min(DELTAS[c]) for c in ORDER}     # nonnegative up to the grid by construction (round 318 C318-5: not gated as a sign; pinned in g6)
dslope = float(np.linalg.lstsq(A, np.array([dv[c] for c in ORDER]), rcond=None)[0][0])
cdslope = float(np.linalg.lstsq(A, np.array([cvals[c] - dv[c] for c in ORDER]), rcond=None)[0][0])
ok &= 1.4 <= cdslope <= 1.8
lnl = np.array([run_SL(c)["ln_eig"] + 4*math.pi*math.exp(DELTAS[c]) for c in ORDER])
direct = float(np.linalg.lstsq(A, lnl, rcond=None)[0][0])
ok &= abs(3.5 + cdslope - direct) <= 0.1 and abs(direct - 5.04) <= 0.05
devslope = float(np.linalg.lstsq(A, np.array([dev[c] for c in ORDER]), rcond=None)[0][0])
ok &= abs(3.5 + cdslope + devslope - direct) <= 1e-9        # round 318 C318-1: ln lambda_1 + 4 pi e^delta = (7/2) ln 2T_0 + C_zeta + dev + c - d exactly, so the slopes add
gate("g4 the 1bm consequence: 2 s_delta(2T_0) + 4 pi e^delta = B(2T_0) - I(2T_0) = " + ", ".join(f"{dvals[c]:.2f}" for c in ORDER) + " against (7/2) ln(4 pi e^delta) + C_zeta within 0.5 (deviations " + ", ".join(f"{dev[c]:+.2f}" for c in ORDER)
     + f"); 1bm(v)'s residual c(delta) reproduced within 0.01 (" + ", ".join(f"{cvals[c]:.2f}" for c in ORDER) + f"), its least-squares slope against ln T_0 {cslope:.3f} in [1.1, 1.5]; d(delta) = 2 s_delta(2T_0) - min = " + ", ".join(f"{dv[c]:.2f}" for c in ORDER) + f" (slope {dslope:+.3f}); slope of c - d {cdslope:.3f} in [1.4, 1.8]; 7/2 + {cdslope:.2f} = {3.5 + cdslope:.2f} against the direct slope of ln lambda_1 + 4 pi e^delta, {direct:.3f} (1bm(vii)'s 5.04); the balance: slope of the deviations {devslope:+.4f}, 7/2 + {cdslope:.4f} + ({devslope:+.4f}) = {direct:.4f} exactly", ok)

# ---------------------------------------------------------------- g5
zs2 = zs + 0.1*np.where(np.arange(len(zs)) % 2 == 0, 1.0, -1.0)         # a list with its zeros jittered by an alternating +-0.1 (S changed by O(1))
T = 687.0; lhs = B(zs2, T) - I(T, 1, 1); rhs = stieltjes_rhs(zs2, T, 1, 1)
ok = abs(lhs - rhs) <= 1e-6                                              # the identity is an identity for any list
sl2, _, _, _ = slope(zs2, FORMS["zeta"], ZLO, ZHI)
ok &= abs(sl2 - 3.5) <= SLOPE_BAND["zeta"]                               # an O(1) change of S leaves the slope
sl3, _, _, _ = slope(zs[::2], FORMS["zeta"], ZLO, ZHI)               # every other zero: a different density, the slope leaves the band
ok &= abs(sl3 - 3.5) > 1.0
gate(f"g5 mangle probes: the Stieltjes identity holds for any list (|diff| {abs(lhs - rhs):.1e} on a shifted list); an O(1) jitter of the zeros leaves the slope in the band ({sl2:+.3f}); halving the list moves it out ({sl3:+.3f})", ok)

# ---------------------------------------------------------------- g6
import paper_needles
S_SLOPES = '3.48, 0.44, 0.61, −0.67, 10.92'
S_RESZ = '[3.52, 4.41]'
S_CZ = '4.05'
S_CZPARTS = '−6.84, 10.70, 0.19'
S_CD = 'C_Δ with its tail is 0.35 (0.56 without it)'
S_CCHI = '2.89, 2.24, 1.22 for χ₋₃, χ₋₄, χ₈'
S_DEV = 'sit within 0.4 of (7/2)ln(4πeᵟ) + C_ζ at the cells'
S_CSLOPE = '1.28 for c(δ) and −0.32 for d(δ), 1.59 for c − d'
S_DLIST = 'd(δ) := 2s_δ(2T₀) − min_T 2s_δ(T) = 1.18, 0.69, 0.27, 0.59, 0.14, 0.33, 0.29 at the cells'
S_BOOK = '7/2 + 1.59 = 5.09 against the directly fitted slope of ln λ₁ + 4πeᵟ, 5.04'
S_SPANS = 'the fits span 0.37–0.55, 0.45–0.64 and −0.85 to −0.50 for χ₋₃, χ₋₄, χ₈'
S_SPANZ = 'ζ spans 3.45–3.51 and Δ 10.78–11.06'
S_BAL = "and the cells' o(1) the balance −0.05"
S_CHI8 = 'the highest −0.51 to the nearest 0.01'
S_EXT = 'here the minimum is at the zero 48.01 and the maximum interior, at T = 44.54'
# each call carries its literal (the precheck's clause D); the strings equal the S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, 'the fits span 0.37–0.55, 0.45–0.64 and −0.85 to −0.50 for χ₋₃, χ₋₄, χ₈', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'ζ spans 3.45–3.51 and Δ 10.78–11.06', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, "and the cells' o(1) the balance −0.05", 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the highest −0.51 to the nearest 0.01', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'here the minimum is at the zero 48.01 and the maximum interior, at T = 44.54', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '3.48, 0.44, 0.61, −0.67, 10.92', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '[3.52, 4.41]', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '4.05', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '−6.84, 10.70, 0.19', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'C_Δ with its tail is 0.35 (0.56 without it)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '2.89, 2.24, 1.22 for χ₋₃, χ₋₄, χ₈', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'sit within 0.4 of (7/2)ln(4πeᵟ) + C_ζ at the cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '1.28 for c(δ) and −0.32 for d(δ), 1.59 for c − d', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'd(δ) := 2s_δ(2T₀) − min_T 2s_δ(T) = 1.18, 0.69, 0.27, 0.59, 0.14, 0.33, 0.29 at the cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '7/2 + 1.59 = 5.09 against the directly fitted slope of ln λ₁ + 4πeᵟ, 5.04', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g6'] == [S_SLOPES, S_RESZ, S_CZ, S_CZPARTS, S_CD, S_CCHI, S_DEV, S_CSLOPE, S_DLIST, S_BOOK, S_SPANS, S_SPANZ, S_BAL, S_CHI8, S_EXT]
def _num(s): return float(s.strip().replace('−', '-'))
_re = __import__("re")
_m = _re.findall(r"([-−]?[0-9]+\.[0-9]{2})", S_SLOPES)
ok &= len(_m) == 5 and all(abs(_num(a) - slopes[f]) <= 5e-3 + 1e-9 for a, f in zip(_m, FORDER))            # nearest 0.01
_m = _re.search(r"\[([-−]?[0-9.]+), ([-−]?[0-9.]+)\]", S_RESZ)
ok &= _num(_m.group(1)) <= res_min < _num(_m.group(1)) + 0.01 + 1e-9 and _num(_m.group(2)) - 0.01 - 1e-9 < res_max <= _num(_m.group(2))   # outward 0.01 of the exact range (round 319 F319-2)
ok &= abs(_num(S_CZ) - Cf["zeta"]) <= 5e-3 + 1e-9
_m = _re.findall(r"([-−]?[0-9]+\.[0-9]{2})", S_CHI8.split(" to the")[0])        # the 'nearest 0.01' excluded from the parse
ok &= len(_m) == 1 and abs(_num(_m[0]) - spans["chi_8"][1]) <= 5e-3 + 1e-9                                      # nearest 0.01 (round 319 C319-1)
_m = _re.findall(r"([0-9]+\.[0-9]{2})", S_EXT)
ok &= len(_m) == 2 and abs(_num(_m[0]) - res_argmin) <= 5e-3 + 1e-9 and res_min_at_zero and abs(_num(_m[1]) - res_argmax) <= 5e-3 + 1e-9 and res_max_interior   # round 320 F320-1
_m = _re.findall(r"([0-9]+\.[0-9]{2})", S_CD)
ok &= len(_m) == 2 and abs(_num(_m[0]) - Cf["Delta"]) <= 5e-3 + 1e-9 and abs(_num(_m[1]) - C_from_formula(ZS["Delta"], FORMS["Delta"], float(ZS["Delta"][-1]), tail=False)[0]) <= 5e-3 + 1e-9
_m = _re.findall(r"([-−]?[0-9]+\.[0-9]{2})", S_CZPARTS)
ok &= len(_m) == 3 and all(abs(_num(a) - p) <= 5e-3 + 1e-9 for a, p in zip(_m, parts["zeta"]))
_m = _re.findall(r"([-−]?[0-9]+\.[0-9]{2})", S_CCHI)
ok &= len(_m) == 3 and all(abs(_num(a) - Cf[f]) <= 5e-3 + 1e-9 for a, f in zip(_m, ("chi_-3", "chi_-4", "chi_8")))
_d = _num(_re.search(r"within ([0-9.]+) of", S_DEV).group(1))
ok &= max(abs(dev[c]) for c in ORDER) <= _d < max(abs(dev[c]) for c in ORDER) + 0.1 + 1e-9                     # outward 0.1
_m = _re.findall(r"([-−]?[0-9]+\.[0-9]{2})", S_CSLOPE)
ok &= len(_m) == 3 and abs(_num(_m[0]) - cslope) <= 5e-3 + 1e-9 and abs(_num(_m[1]) - dslope) <= 5e-3 + 1e-9 and abs(_num(_m[2]) - cdslope) <= 5e-3 + 1e-9
_m = _re.findall(r"([0-9]+\.[0-9]{2})", S_DLIST.split("= ")[-1])
ok &= len(_m) == 7 and all(abs(_num(a) - dv[c]) <= 5e-3 + 1e-9 for a, c in zip(_m, ORDER))
_m = _re.findall(r"([0-9]+\.[0-9]{2})", S_BOOK)
ok &= len(_m) == 3 and abs(_num(_m[0]) - cdslope) <= 5e-3 + 1e-9 and abs(_num(_m[1]) - (3.5 + cdslope)) <= 5e-3 + 1e-9 and abs(_num(_m[1]) - round(3.5 + _num(_m[0]), 2)) < 1e-9 and abs(_num(_m[2]) - direct) <= 5e-3 + 1e-9   # round 318 F318-4: nearest 0.01 and the arithmetic
def _outward(lo_s, hi_s, lo, hi):        # the stated [lo_s, hi_s] encloses [lo, hi] and is within 0.01 of it at both ends
    return _num(lo_s) <= lo < _num(lo_s) + 0.01 + 1e-9 and _num(hi_s) - 0.01 - 1e-9 < hi <= _num(hi_s)
_m = _re.findall(r"([-−]?[0-9]+\.[0-9]{2})", S_SPANS)
ok &= len(_m) == 6 and all(_outward(_m[2*i], _m[2*i + 1], *spans[f]) for i, f in enumerate(("chi_-3", "chi_-4", "chi_8")))
_m = _re.findall(r"([0-9]+\.[0-9]{2})", S_SPANZ)
ok &= len(_m) == 4 and _outward(_m[0], _m[1], *spans["zeta"]) and _outward(_m[2], _m[3], *spans["Delta"])
_m = _re.findall(r"([-−]?[0-9]+\.[0-9]{2})", S_BAL)
ok &= len(_m) == 1 and abs(_num(_m[0]) - devslope) <= 5e-3 + 1e-9
gate("g6 the paper's numbers parsed back from the declared needles: the five slopes (nearest 0.01), zeta's residual band (outward), C_zeta, its three parts, C_Delta and the characters' constants (nearest 0.01), the seven-cell deviation bound (outward 0.1), the slopes of c, d and c - d, the seven d(delta), the 5.09-against-5.04 bookkeeping (nearest 0.01 and the arithmetic), the four-window spans (outward 0.01), the o(1) balance (nearest 0.01)", ok)


# ---------------------------------------------------------------- g7
from cascade_tower import chain_ok
gate("g7 the chain obligation to cascade_spectrum_ladder.py (Theorem 1br) met", chain_ok("cascade_spectrum_ladder.py"))

# ---------------------------------------------------------------- g8
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g8 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g8 the 1bs paper needles and the footer census (declared surface)", ok)

print(("\nALL GATES PASS (9/9)" if not fails else f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
