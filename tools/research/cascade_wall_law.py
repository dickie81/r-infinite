#!/usr/bin/env python3
"""Theorem 1by (the wall's law -- the unlocking functional, its continuum form, and the displacement law): the verifier. The
tower's member 34 (top); chain obligation to cascade_rung_balayage.py (Theorem 1bx), whose one number per rung this block derives.

WHAT THE BLOCK CLAIMS. (i) The displacement law (proved): for any eigenvector of the pencil (G, N) -- ground state or rung --
the K - 1 designed zeros with the leading coefficient are complete coordinates on the coefficient space (partial fractions),
d ln ghat/d tau = 2r^2/(tau (tau^2 - r^2)) and Rayleigh's quotient is stationary at an eigenvector, so at every designed zero tau
   2 sum_gamma ghat(gamma)^2 gamma^2/(tau^2 - gamma^2) = (lambda/pi) int_0^inf ghat(r)^2 r^2/(tau^2 - r^2) dr
(the sum over every zeta zero, the integral regular at r = tau); at a dodged zero tau_j = gamma_j - d_j the own term is
-gamma_j ghat(gamma_j) ghat'(gamma_j) to first order, so d_j = (M_j - lambda H_j)/(gamma_j ghat'(gamma_j)^2): the locked zone's
displacements are set by the field M_j of the other zeros' leakage against lambda times the interior's Cauchy moment H_j.
(ii) The unlocking functional: F_k(T) = F_1(T) + 4 sum_h ln(1/sigma_h(T)), F_1 Theorem 1bm(v)'s finite-delta functional
4 sum_{gamma<T} ln((1 + sqrt(1 - gamma^2/T^2)) T/gamma) - 2aT and 4 sum_h ln(1/sigma_h(T)) Theorem 1bx's exterior constant of the
hole pairs -- Theorem 1bu(iv)'s k-level formula (arccosh(T/tau) = ln(1/sigma_tau(T))), whose minimiser is 1bu's edge T_k of the ladder checkpoint --
read through 1bx's balayage; its minimiser T_u(k) (a zeta zero or the domain's endpoint h_max, F_k being concave between zeros; the endpoint
excluded by computation at the forty safely deep rungs) is the rung's wall and its minimum the rung's exponent:
ln lambda_k - ln lambda_1 = 2 ln|ghat_k(0)/ghat_1(0)| + F_k(T_u) - F_1(T_u(1)). (iii) The continuum law, in 1bm(iv)'s reduced problem
with the hole pairs at the origin: u ln(2/u) = (2m/pi) e^{-delta}, u = T/T_0 -- the minimiser of the exponent -e^delta f(X) + 4m ln(2X T_0/h) (1bm's maximiser convention for -ln lambda), equal to
the vanishing of the inverse-square-root edge coefficient of the rung's outer density (the ground's sqrt(X/2) ln(2/X) against
the holes' m e^{-delta} (2/pi)/sqrt(2X)); a root below 2 exists iff m < (pi/e) e^delta. (iv) Verified at the cells: the ground's
edge is F_1's minimiser (the same zero at delta = 2, 2.3; within one zero at 2.6, 3; three at 3.5); the rungs' T_u between the
census edge T_k and 1bx's sharp wall T_w at 35 of 40, the exponent within half a nat at all 40 (a half-nat window spanning an eighth of T_u in the
median and up to a quarter: the minimum is flat; the residual grows with the hole count); the continuum law within 3.9% rms of T_u and 3.3% of T_w; the displacement law at every dodged zero
of 11 rungs at delta = 2 and 2.3 within 0.0023, the floor the disclosed tail approximation's; the sharp wall's excess over T_u grows with
the hole count (from under 6% at one hole to 4-15% at the top rung; correlation +0.5 with m at t = r sqrt(n - 2)/sqrt(1 - r^2) = 3.7, -0.2 with 1bx's onset shortfall within two standard errors of zero) --
quantified, not derived, and not the soft onset's.

THE GATES. (0) the algebra witnessed at 60 digits; (1) the functional's minimisers are zeta zeros (the endpoint excluded), and the ground's is its edge;
(2) the rungs' T_u against T_k and T_w; (3) the exponent at every safely deep rung; (4) the continuum law; (5) the displacement
law at delta = 2, 2.3 (the Gram and polished eigenvectors recomputed in-process: no checkpoint, no producer); (6) the paper's
numbers parsed back; (7) the chain obligation; (8) the needles and census.

WHAT IS NOT CLAIMED. The law of the sharp wall's excess over T_u (T_w/T_u, growing with the hole count); the reduction of 1bm(iii) (conjectural there, inherited here by (iii));
the odd sector; anything beyond the safely deep rungs; no Riemann Hypothesis consequence.
"""
import math, os, sys, json, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ladder_caster as LC
from rung_anatomy import run as run_RA
from rung_laws import run as run_RL
from ladder_caster import run as run_LC
from weil_prime_gram import gram
from flint import arb, acb, arb_mat, acb_mat, ctx
import mpmath as _mp

PAPER_NEEDLES = [
    {'g': 'g8', 's': "Theorem 1by (the wall", 'form': 'plain'},
    {'g': 'g8', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 16},
    {'s': '`cascade_wall_law.py`', 'min': 2, 'g': 'g8'},
    {'s': 'the **101 scripts cited in place** above', 'form': 'ws', 'g': 'g8'},
    {'s': 'extended by Theorems 1i–1by:', 'form': 'ws', 'g': 'g8'},
    {'g': 'g6', 's': 'F₁’s minimiser is the ground state’s edge: the same zeta zero at δ = 2 and 2.3, one zero below it at δ = 2.6 and 3, three zeros above it at δ = 3.5 (T_u(1)/T₁ = 1.0000, 1.0000, 0.9901, 0.9961, 1.0117)', 'form': 'ws'},
    {'g': 'g6', 's': 'the minimiser’s margin over the runner-up zero is 0.041, 0.056, 0.003, 0.041, 0.007 nats at the five cells, and under 0.02 nats at 11 of the 40 rungs (the closest 0.00008), while a half-nat window about the minimum spans 0.088–0.249 of T_u (median 0.125)', 'form': 'ws'},
    {'g': 'g6', 's': 'the domain’s left endpoint T = h_max exceeds the minimum by at least 16.1 nats at the 40 rungs', 'form': 'ws'},
    {'g': 'g6', 's': 'T_u lies between T_k and T_w at 35 of the 40 safely deep rungs — above T_w at δ = 2.3’s rung 2 and δ = 3’s rung 3 and δ = 3.5’s rung 2, below T_k by one zero at δ = 3.5’s rungs 2, 3 and 5, the last cell’s rung 2 in both sets; T_u/T_k averages 1.023 with rms deviation from 1 of 0.036 over [0.997, 1.085], and T_u/T_w averages 0.960 with rms deviation from 1 of 0.054 over [0.871, 1.029]; T_u is Theorem 1bu(iv)’s stored minimiser at 39 of the 40 (the exception δ = 3’s rung 3, a 0.0098-nat tie that 1bu’s grid resolves the other way)', 'form': 'ws'},
    {'g': 'g6', 's': 'T_u is the ground state’s minimiser at δ = 2.3’s rung 2 and δ = 3’s rungs 2–3, and is shared with the rung below at 16 rungs', 'form': 'ws'},
    {'g': 'g6', 's': 'the residual lies within [−0.16, +0.43] nats over the 40 rungs, mean +0.13, across differences reaching 183 nats, and grows with the hole count by +0.028 nats per hole on a linear fit (correlation +0.63) — against 1.28 nats with the sharp wall in place of T_u and 0.96 from the exterior constant alone', 'form': 'ws'},
    {'g': 'g6', 's': 'uT₀/T_u averages 1.028 with rms deviation from 1 of 0.039 over [0.988, 1.116] at the 40 rungs, uT₀/T_w 0.986 with 0.033 over [0.916, 1.044]; its per-hole descent is 4.43, 4.62, 4.67, 4.50, 4.27 at the five cells, nearer the functional’s than the sharp wall’s at 4 of them; and for one hole uT₀/T₁ = 1.015, 0.999, 0.988, 1.001, 0.993', 'form': 'ws'},
    {'g': 'g6', 's': '(own + M)/(λH) = 1 within 0.0023 at all 295 dodged zeros of the 11 rungs (median 1.00002), the field ratio M/(λH) running from +4.8 to −6107, the leakage beyond the 6700-zero list 1.9–2.7% of the total, and the ground state’s ln|d| per bin of γ/T₁ (0–0.3, 0.3–0.5, 0.5–0.7, 0.7–0.8, 0.8–0.9, 0.9–1) at δ = 2.3: −78.0, −51.9, −28.1, −13.5, −7.4, −2.5', 'form': 'ws'},
    {'g': 'g6', 's': 'the residual’s correlation with the neglected term’s proxy (γ_j/γ₆₇₀₀)²|M_tail|/|λH_j| is 0.99', 'form': 'ws'},
    {'g': 'g6', 's': 'at the lowest dodged zero M/(λH) is −14.4 and −14.9 for the two ground states and between −2.4 and +2.2 for the nine rungs, its magnitude falling to 0.42 at one zero', 'form': 'ws'},
    {'g': 'g6', 's': 'T_w/T_u − 1 runs from −2.8% to +14.8% over the 40 rungs, correlating +0.52 with the hole count and −0.21 with 1bx’s onset shortfall at T₁, which itself correlates −0.11 with the hole count — the first at t = r√(n − 2)/√(1 − r²) = 3.7, the excess averaging 4.4%, the two negatives within two standard errors of zero (a null correlation’s standard error is 0.16 at n = 40)', 'form': 'ws'},
    {'g': 'g6', 's': 'per hole the functional’s wall descends by 5.43, 4.60, 4.71, 3.64 against the sharp wall’s 3.08, 3.17, 2.58, 1.68 at δ = 2.3, 2.6, 3, 3.5, the gap growing from −1.3%, +5.8%, +0.2%, −1.7% at one hole to +8.2%, +14.8%, +8.7%, +4.4% at the top rung (at δ = 2, three rungs, 3.60 against 4.22, the gap +5.6% to +4.5%)', 'form': 'ws'},
    {'g': 'g6', 's': 'at one hole the two walls agree within 2% at 3 of the five cells', 'form': 'ws'},
    {'g': 'g6', 's': 'h/T₁ ≤ 0.22 at the forty safely deep rungs (the largest 0.2189)', 'form': 'ws'},
    {'g': 'g6', 's': 'its largest magnitude per rung exceeds a thousand at three of the eleven (2154 and 6107 at the ground states, 1185 at δ = 2.3’s rung 2) and runs 37–500 at the other eight', 'form': 'ws'},
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
ZS = np.array(json.load(open(LC.ZD)), dtype=float)                  # Theorem 1bm's 6700-zero list (data; its hash in every key)
ZP = json.load(open(LC.ZP))                                          # Theorem 1bu's 800 zeros to 100 digits (data)
SAFE = -20.0
def n_safe(c):
    st = EV[c]; pro = st["prolate_ln_leakage"]
    return len([r for r in st["rungs"][1:] if 2*r["k"] < len(pro) and pro[2*r["k"]] is not None and pro[2*r["k"]] < SAFE and r["k"] <= 12])

# ---------------------------------------------------------------- the closed forms
def psi(z, T): return (z/T)/(1 + math.sqrt(1 - (z/T)**2))
def dk_bal(holes, T): return -sum((1 + psi(h, T)**2)/(2*T*T) for h in holes)
def solve_T(holes, Dk):        # Theorem 1bx's sharp wall from Delta kappa_k
    lo, hi = 1.0, 1e6
    for _ in range(200):
        mid = 0.5*(lo + hi)
        if dk_bal(holes, mid) < Dk: lo = mid
        else: hi = mid
    return 0.5*(lo + hi)
def F1(T, a):                  # Theorem 1bm(v)'s finite-delta functional
    g = ZS[ZS < T]; return 4*float(np.sum(np.log((1 + np.sqrt(1 - g*g/(T*T)))*T/g))) - 2*a*T
def cost(holes, T): return 4*sum(math.log(1/psi(h, T)) for h in holes)
def Fk(T, a, holes): return F1(T, a) + cost(holes, T)
def argmin_zero(a, holes, jmax):   # the minimiser over the zeta zeros above the holes; also the runner-up's margin and the half-nat window's width (in units of the minimiser)
    jmin = max(int(np.searchsorted(ZS, max(holes)*1.000001)) if holes else 1, 1)
    vals = [Fk(ZS[j], a, holes) for j in range(jmin, jmax)]
    i = int(np.argmin(vals)); srt = sorted(vals); win = [ZS[j + jmin] for j, v in enumerate(vals) if v <= vals[i] + 0.5]
    return i + jmin, srt[1] - srt[0], (max(win) - min(win))/ZS[i + jmin]
def outer(r):                  # Theorem 1bx's outer zero set and interpolated count (for the onset shortfall at T_1)
    Z = [z for _, z in r["dodging"]] + list(r["exterior"])
    if r["n_complex"] == 1 and r["sum_rule_residual"] < 0: Z.append(abs(r["sum_rule_residual"])**-0.5)
    return np.array(sorted(Z))
def nbar(O):
    idx = np.arange(len(O)) + 0.5
    return lambda R: np.interp(R, O, idx, left=0.0, right=float(len(O)))
def cont_u(m, delta):          # the continuum law's root below 2 (u ln(2/u) decreasing on (2/e, 2))
    rhs = 2*m*math.exp(-delta)/math.pi; lo, hi = 2/math.e, 2.0
    for _ in range(200):
        mid = 0.5*(lo + hi)
        if mid*math.log(2/mid) > rhs: lo = mid
        else: hi = mid
    return 0.5*(lo + hi)

# ---------------------------------------------------------------- g0: the algebra witnessed
with _mp.workdps(60):
    ok = True
    # (a) the hole pair's balayage cost 4 ln(1/sigma_h(T)) has derivative 4/T (1 + O(h^2/T^2)); its h -> 0 form 4 ln(2T/h)
    T, h = _mp.mpf(3), _mp.mpf("1e-4"); sig = lambda h, T: (h/T)/(1 + _mp.sqrt(1 - (h/T)**2))
    ok &= abs(4*_mp.log(1/sig(h, T)) - 4*_mp.log(2*T/h)) <= _mp.mpf("1e-8")
    ok &= abs(_mp.diff(lambda t: 4*_mp.log(1/sig(h, t)), T) - 4/T) <= _mp.mpf("1e-8")
    # (b) the continuum stationarity: d/dX [-f(X) e^delta + 4m ln(2X T_0/h)] = -2 pi e^delta ln(2/X) + 4m/X, f(X) = 2 pi X (1 + ln 2 - ln X)
    f = lambda X: 2*_mp.pi*X*(1 + _mp.log(2) - _mp.log(X))
    for X, m, d in ((_mp.mpf("1.7"), 3, _mp.mpf("2.3")), (_mp.mpf("1.95"), 1, _mp.mpf(2))):
        E = lambda x: -f(x)*_mp.exp(d) + 4*m*_mp.log(2*x*2*_mp.pi*_mp.exp(d)/_mp.mpf("0.1"))
        ok &= abs(_mp.diff(E, X) - (-2*_mp.pi*_mp.exp(d)*_mp.log(2/X) + 4*m/X)) <= _mp.mpf("1e-20")
    # (c) the root: X ln(2/X) = (2m/pi) e^{-delta} zeroes that derivative; u ln(2/u) has its maximum 2/e at u = 2/e (existence iff m < (pi/e) e^delta)
    for m, d in ((1, 2.0), (6, 2.3), (11, 3.5)):
        u = _mp.mpf(cont_u(m, d)); ok &= abs(-2*_mp.pi*_mp.exp(d)*_mp.log(2/u) + 4*m/u) <= _mp.mpf("1e-9")
    ok &= abs(_mp.diff(lambda u: u*_mp.log(2/u), 2/_mp.e)) <= _mp.mpf("1e-25") and abs((2/_mp.e)*_mp.log(2/(2/_mp.e)) - 2/_mp.e) <= _mp.mpf("1e-30") and all(u*_mp.log(2/u) < 2/_mp.e for u in (_mp.mpf("0.3"), _mp.mpf("0.5"), _mp.mpf(1), _mp.mpf("1.5"), _mp.mpf("1.9")))
    # (d) the edge coefficients: the hole pair's deficit density (2/pi) X/(x sqrt(x^2 - X^2)) has the 1/sqrt(x - X) coefficient (2/pi)/sqrt(2X);
    #     1bm's I(X) = pi X ln(X/2) (the Cauchy integral of sqrt(X^2 - t^2) ln|t| at the edge) gives the ground's sqrt(X/2) ln(2/X); the balance is (c)'s equation
    X = _mp.mpf("1.5"); eps = _mp.mpf("1e-12")
    ok &= abs(_mp.sqrt(eps)*(2/_mp.pi)*X/((X + eps)*_mp.sqrt((X + eps)**2 - X*X)) - (2/_mp.pi)/_mp.sqrt(2*X)) <= _mp.mpf("1e-6")
    I = _mp.quad(lambda t: _mp.sqrt((X + t)/(X - t))*_mp.log(abs(t)), [-X, 0, X])
    ok &= abs(I - _mp.pi*X*_mp.log(X/2)) <= _mp.mpf("1e-12")
    bal = lambda u, m, d: _mp.sqrt(u/2)*_mp.log(2/u) - m*_mp.exp(-d)*(2/_mp.pi)/_mp.sqrt(2*u)
    ok &= abs(bal(_mp.mpf(cont_u(6, 2.3)), 6, _mp.mpf("2.3"))) <= _mp.mpf("1e-9")
    # (e) the displacement law's calculus: d ln(1 - r^2/tau^2)/d tau = 2 r^2/(tau (tau^2 - r^2)); and the zero coordinates are complete --
    #     moving one root of the partial-fraction numerator maps the coefficients by v_i (omega_i^2 - tau'^2)/(omega_i^2 - tau^2) (witnessed at K = 6)
    r, tau = _mp.mpf("0.7"), _mp.mpf("1.3")
    ok &= abs(_mp.diff(lambda t: _mp.log(1 - r*r/(t*t)), tau) - 2*r*r/(tau*(tau*tau - r*r))) <= _mp.mpf("1e-25")
    om = [_mp.mpf(i)*_mp.pi for i in range(6)]; v = [_mp.mpf(x) for x in ("0.9", "-0.4", "0.3", "-0.25", "0.1", "-0.05")]
    Q = lambda x, vv: sum(((-1)**i)*vv[i]*_mp.fprod(x - om[j]**2 for j in range(6) if j != i) for i in range(6))
    root = _mp.findroot(lambda x: Q(x, v), _mp.mpf(30)); tau = _mp.sqrt(root); tau2 = tau*_mp.mpf("1.05")
    v2 = [v[i]*(om[i]**2 - tau2*tau2)/(om[i]**2 - tau*tau) for i in range(6)]
    ok &= abs(Q(tau2*tau2, v2)) <= _mp.mpf("1e-25")*abs(Q(_mp.mpf(31), v2)) and abs(Q(root, v)) <= _mp.mpf("1e-25")
gate("g0 the algebra witnessed at 60 digits: the hole pair's cost 4 ln(1/sigma_h(T)) -> 4 ln(2T/h) with derivative 4/T; the continuum stationarity d/dX[-f e^delta + 4m ln(2X T_0/h)] = -2 pi e^delta ln(2/X) + 4m/X; its root u ln(2/u) = (2m/pi)e^-delta, the maximum 2/e of u ln(2/u) at u = 2/e; the edge coefficients (the hole deficit's (2/pi)/sqrt(2X), 1bm's I(X) = pi X ln(X/2) within 1e-12) balancing at the same root; d ln(1 - r^2/tau^2)/d tau = 2r^2/(tau(tau^2 - r^2)); the zero coordinates complete (a root moved at K = 6 maps the coefficients by (omega^2 - tau'^2)/(omega^2 - tau^2))", ok)

# ---------------------------------------------------------------- g1: the minimisers
W = {}; G1 = {}
for c in ORDER:
    S = CEN[c]; L = {l["k"]: l for l in LAW[c]["laws"]}; ns = n_safe(c); g = S["rungs"][0]; T1 = g["edge"]; a = S["delta"]/2
    jmax = int(np.searchsorted(ZS, 3*T1)); j1, mg1, _w1 = argmin_zero(a, [], jmax); jedge = int(np.argmin(np.abs(ZS - T1))); N1 = nbar(outer(g))
    G1[c] = {"j1": j1, "jedge": jedge, "T1u": ZS[j1], "T1": T1, "a": a, "T0": S["T0"], "delta": S["delta"], "jmax": jmax, "margin": mg1}
    for r in S["rungs"][1:ns + 1]:
        k = r["k"]; holes = sorted(r["holes"]); Tw = solve_T(holes, L[k]["Dkappa"]); ju, mg, win = argmin_zero(a, holes, jmax); Nk = nbar(outer(r))
        W[(c, k)] = {"k": k, "m": k - 1, "holes": holes, "Tw": Tw, "T1": T1, "Tk": r["edge"], "ju": ju, "Tu": ZS[ju], "T1u": ZS[j1], "margin": mg, "win": win,
                     "Tk_bu": EV[c]["rungs"][k - 1]["Tk"], "shortfall": (Nk(T1) - N1(T1))/(k - 1) + (2/math.pi)*math.acos(min(1.0, Tw/T1)),
                     "lnlam": r["ln_lam"], "lnlam1": g["ln_lam"], "c2": 2*math.log(abs(r["g0"]/g["g0"])), "a": a, "delta": S["delta"], "T0": S["T0"]}
assert abs(ZS[G1["d2.0"]["jedge"]] - G1["d2.0"]["T1"]) <= 1e-6 and abs(ZS[G1["d3.5"]["jedge"]] - G1["d3.5"]["T1"]) <= 1e-6   # the census edge is a zeta zero
didx = [G1[c]["j1"] - G1[c]["jedge"] for c in ORDER]; rat1u = [G1[c]["T1u"]/G1[c]["T1"] for c in ORDER]
# the minimiser is a zeta zero: on a grid of 60 points per spacing over [0.5, 1.6] T_1 (the zeros themselves grid points), the minimum sits at a zero -- for F_1 and every F_k
def grid_min_is_zero(a, holes, T1):
    lo = int(np.searchsorted(ZS, 0.5*T1)); hi = int(np.searchsorted(ZS, 1.6*T1)); best = (1e300, None)
    for j in range(max(lo, 1), hi):
        pts = np.linspace(ZS[j], ZS[j + 1], 61)[:-1]                  # [gamma_j, gamma_{j+1}): the zero first
        vals = [Fk(float(t), a, holes) for t in pts]; i = int(np.argmin(vals))
        if vals[i] < best[0]: best = (vals[i], i)
    return best[1] == 0
zmin = [grid_min_is_zero(G1[c]["a"], [], G1[c]["T1"]) for c in ORDER] + [grid_min_is_zero(w["a"], w["holes"], w["T1"]) for w in W.values()]
# concavity between zeros (the proof's missing step, round 342 F342-4): every summand's slope 1/T + (z^2/T^3)/(s(1 + s)) decreases in T and -2aT is linear,
# so F_k is concave on every open spacing and its infimum on a closed spacing is an endpoint -- witnessed by second differences on the interior points of 61 per spacing
def concave(a, holes, T1):
    lo = int(np.searchsorted(ZS, 0.5*T1)); hi = int(np.searchsorted(ZS, 1.6*T1)); worst = -1e9; n = 0
    for j in range(max(lo, 1), hi):
        v = np.array([Fk(float(t), a, holes) for t in np.linspace(ZS[j], ZS[j + 1], 61)[1:-1]]); d2 = v[2:] - 2*v[1:-1] + v[:-2]; worst = max(worst, float(d2.max())); n += 1
    return worst, n
cc = [concave(G1[c]["a"], [], G1[c]["T1"]) for c in ORDER] + [concave(w["a"], w["holes"], w["T1"]) for w in W.values()]
worst2 = max(x[0] for x in cc); nsp = sum(x[1] for x in cc)
# the minimiser's margins (round 342 F342-3) and the half-nat window's width (the flatness at the minimum)
gmar = [G1[c]["margin"] for c in ORDER]; rmar = [w["margin"] for w in W.values()]; nclose = sum(1 for x in rmar if x < 0.02)
wins = [w["win"] for w in W.values()]
endgap = min(Fk(max(w["holes"])*(1 + 1e-9), w["a"], w["holes"]) - Fk(w["Tu"], w["a"], w["holes"]) for w in W.values())   # the domain's left endpoint T = h_max, a cusp of the hole terms (round 343 F343-5)
ok = didx == [0, 0, -1, -1, 3] and all(0.99 <= x <= 1.012 for x in rat1u) and all(zmin) and len(zmin) == 45 and worst2 < 0 and nsp >= 7000
ok &= nclose == 11 and min(rmar) <= 1e-3 and min(gmar) <= 0.005 and 0.10 <= float(np.median(wins)) <= 0.13 and max(wins) <= 0.25 and endgap >= 10
gate("g1 the functional's minimiser is a zeta zero at every one of the 45 functionals (F_1 at the five cells, F_k at the 40 safely deep rungs; grid of 60 per spacing over [0.5, 1.6] T_1), and F_k is concave between zeros (the largest second difference on the interior points of 61 per spacing over " + f"{nsp} spacings {worst2:.1e}, gated < 0); the domain's left endpoint T = h_max (a cusp of the hole terms) exceeds the minimum by at least {endgap:.2f} nats over the 40 rungs (gated >= 10); the ground's edge T_1 is F_1's minimiser: the minimiser's zero index minus the edge's = " + ", ".join(str(x) for x in didx) + " at the five cells (gated 0, 0, -1, -1, 3), T_1u/T_1 = " + ", ".join(f"{x:.4f}" for x in rat1u) + " (gated [0.99, 1.012]); the minimiser's margin over the runner-up zero: " + ", ".join(f"{x:.4f}" for x in gmar) + f" nats at the five ground states (gated min <= 0.005), under 0.02 nats at {nclose} of the 40 rungs (gated 11; the closest {min(rmar):.5f}); the half-nat window about the minimum spans {min(wins):.3f}-{max(wins):.3f} of T_u, median {float(np.median(wins)):.3f} (gated median in [0.10, 0.13], max <= 0.25)", ok)

# ---------------------------------------------------------------- g2: the rungs' T_u against T_k and T_w
ruk = [w["Tu"]/w["Tk"] for w in W.values()]; ruw = [w["Tu"]/w["Tw"] for w in W.values()]
between = sum(1 for w in W.values() if w["Tk"]*0.9999 <= w["Tu"] <= w["Tw"]*1.0001)
rms = lambda x: math.sqrt(float(np.mean((np.asarray(x) - 1)**2)))
STICKY = [(c, k) for (c, k), w in W.items() if w["ju"] == G1[c]["j1"]]                       # T_u = the ground's minimiser
PAIRS = [(c, k) for (c, k), w in W.items() if (c, k - 1) in W and W[(c, k - 1)]["ju"] == w["ju"]]   # T_u shared with the rung below
ABOVE = [(c, k) for (c, k), w in W.items() if w["Tu"] > w["Tw"]*1.0001]; BELOW = [(c, k) for (c, k), w in W.items() if w["Tu"] < w["Tk"]*0.9999]   # the exceptions, sided
below_one = all(int(np.argmin(np.abs(ZS - W[key]["Tk"]))) - W[key]["ju"] == 1 for key in BELOW)   # below T_k by exactly one zero
bu_match = sum(1 for w in W.values() if abs(w["Tk_bu"] - w["Tu"]) <= 1e-3)                      # Theorem 1bu(iv)'s k-level minimiser (its "edge T_k", the ladder checkpoint) is T_u
# the sharp wall's excess over T_u against the hole count (round 342 F342-1): its range, its correlations with m and with 1bx's onset shortfall at T_1, the per-cell slopes
exc = np.array([w["Tw"]/w["Tu"] - 1 for w in W.values()]); mm = np.array([w["m"] for w in W.values()]); shf = np.array([w["shortfall"] for w in W.values()])
r_m = float(np.corrcoef(mm, exc)[0, 1]); r_sh = float(np.corrcoef(shf, exc)[0, 1]); r_ms = float(np.corrcoef(mm, shf)[0, 1])   # and the shortfall itself against the hole count
DOF = 2; AGREE_TOL = 0.02                                                                          # the t-statistic's n - 2 and the one-hole agreement threshold (round 346 F346-9)
tstat = lambda r: r*math.sqrt(len(exc) - DOF)/math.sqrt(1 - r*r); SE = 1/math.sqrt(len(exc) - 3)                                 # t statistics and the standard error of a null correlation at n = 40 (round 343 F343-1)
SL = {}
for c in ORDER:
    sel = [w for (cc, _), w in W.items() if cc == c]; x = np.array([w["m"] for w in sel])
    SL[c] = (float(np.polyfit(x, [w["Tu"] for w in sel], 1)[0]), float(np.polyfit(x, [w["Tw"] for w in sel], 1)[0]), sel[0]["Tw"]/sel[0]["Tu"] - 1, sel[-1]["Tw"]/sel[-1]["Tu"] - 1)
faster = sum(1 for c in ORDER if SL[c][0] < SL[c][1])                                            # the functional's wall descending faster than the sharp wall
ok = len(W) == 40 and 1.02 <= float(np.mean(ruk)) <= 1.03 and rms(ruk) <= 0.04 and min(ruk) >= 0.99 and max(ruk) <= 1.09
ok &= 0.95 <= float(np.mean(ruw)) <= 0.97 and rms(ruw) <= 0.06 and min(ruw) >= 0.87 and max(ruw) <= 1.03
ok &= STICKY == [("d2.3", 2), ("d3.0", 2), ("d3.0", 3)] and len(PAIRS) == 16 and ABOVE == [("d2.3", 2), ("d3.0", 3), ("d3.5", 2)] and BELOW == [("d3.5", 2), ("d3.5", 3), ("d3.5", 5)] and below_one and bu_match == 39
n_agree = sum(1 for c in ORDER if abs(SL[c][2]) <= AGREE_TOL)                                          # the one-hole gap within 2% (round 344 F344-8)
# t(r_m) >= 3 and |r_sh| <= 2 SE are implied by the bounds on r_m and r_sh at n = 40 (round 344 F344-4), so not gated twice; likewise between == 35 and the union's size
# follow from len(W) == 40 with the two exact exception lists (round 345 F345-4). Round 345 F345-1: a comment placed mid-line had swallowed the three conjuncts below.
ok &= 0.45 <= r_m <= 0.6 and -0.3 <= r_sh <= -0.1 and r_ms <= 0 and abs(r_ms) <= 2*SE and n_agree == 3 and faster == 4
hmax = max(max(w["holes"])/w["T1"] for w in W.values()); mexc = float(np.mean(exc))                 # the holes' height (round 346 F346-6); the mean excess (F346-7)
EXC1 = [(c, k) for (c, k), w in W.items() if abs(w["Tk_bu"] - w["Tu"]) > 1e-3]
def runner_up(w):   # the zero with the second-lowest F_k above the holes
    jmin = max(int(np.searchsorted(ZS, max(w["holes"])*1.000001)), 1); vals = sorted((Fk(ZS[j], w["a"], w["holes"]), j) for j in range(jmin, G1[[c for c in ORDER if CEN[c]["delta"] == w["delta"]][0]]["jmax"]))
    return ZS[vals[1][1]]
other_way = len(EXC1) == 1 and abs(W[EXC1[0]]["Tk_bu"] - runner_up(W[EXC1[0]])) <= 1e-3
ok &= SL["d2.0"][0] > SL["d2.0"][1] and 0.14 <= exc.max() and hmax <= 0.22 and 0.04 <= mexc <= 0.05 and other_way   # exc.min() >= -0.03 and exc.max() <= 0.16 are implied by the bounds on ruw = 1/(1 + exc) above (round 346 F346-4)
ok &= all(SL[c][3] > SL[c][2] for c in ORDER[1:]) and all(SL[c][3] >= 0.04 for c in ORDER[1:])   # the gap grows from the one-hole rung to the top rung at the four cells with six or more rungs
gate(f"g2 the unlocking height T_u = argmin F_k at the 40 safely deep rungs: between the census edge T_k and 1bx's sharp wall T_w at {between} of 40 (the exceptions above T_w at {ABOVE} and below T_k by one zero at {BELOW}, gated exactly these, whence the 35; five rungs in all, delta = 3.5's rung 2 in both sets); T_u/T_k mean {float(np.mean(ruk)):.3f}, rms deviation from 1 {rms(ruk):.3f}, range [{min(ruk):.3f}, {max(ruk):.3f}] (gated mean in [1.02, 1.03], rms <= 0.04, range within [0.99, 1.09]); T_u/T_w mean {float(np.mean(ruw)):.3f}, rms {rms(ruw):.3f}, range [{min(ruw):.3f}, {max(ruw):.3f}] (gated mean in [0.95, 0.97], rms <= 0.06, range within [0.87, 1.03]); T_u = the ground's minimiser at {STICKY} (gated exactly these); T_u shared with the rung below at {len(PAIRS)} rungs (gated 16); T_u equals Theorem 1bu(iv)'s k-level minimiser (the ladder checkpoint's edge) at {bu_match} of 40 (gated 39); the sharp wall's excess T_w/T_u - 1 from {100*exc.min():+.1f}% to {100*exc.max():+.1f}% (max gated >= 14%; the floor -3% and ceiling 16% implied by the bounds on T_u/T_w), mean {100*mexc:.2f}% (gated [4%, 5%]), correlating {r_m:+.3f} with the hole count (gated [0.45, 0.6]) and {r_sh:+.3f} with 1bx's onset shortfall at T_1 (gated [-0.3, -0.1]), the shortfall itself correlating {r_ms:+.3f} with the hole count (gated <= 0); the first at t = {tstat(r_m):.2f}, the two negatives within two standard errors ({SE:.3f}) of zero (r_ms gated; t >= 3 and |r_sh| <= 2 SE implied by the bounds above); the one-hole gap within 2% at {n_agree} of 5 cells (gated 3); per cell dT_u/dm, dT_w/dm, the excess at one hole and at the top rung: " + "; ".join(f"{c}: {SL[c][0]:+.2f}, {SL[c][1]:+.2f}, {100*SL[c][2]:+.1f}%, {100*SL[c][3]:+.1f}%" for c in ORDER) + f" (the functional's wall descending faster at {faster} of 5 cells, gated 4, the exception delta = 2 with three rungs; the gap growing to >= 4% at the four cells with six or more rungs); the holes' height max h/T_1 = {hmax:.4f} over the 40 rungs (gated <= 0.22); the 1bu exception's stored edge is the runner-up zero ({other_way}, gated)", ok)

# ---------------------------------------------------------------- g3: the exponent at every safely deep rung (from Theorem 1bw's census: ln lambda_k and ghat_k(0))
RES = {}; RESW = {}; RESB = {}
for (c, k), w in W.items():
    dl = w["lnlam"] - w["lnlam1"] - w["c2"]
    RES[(c, k)] = Fk(w["Tu"], w["a"], w["holes"]) - F1(w["T1u"], w["a"]) - dl
    RESW[(c, k)] = Fk(w["Tw"], w["a"], w["holes"]) - F1(w["T1u"], w["a"]) - dl
    RESB[(c, k)] = cost(w["holes"], w["Tw"]) - dl
res = list(RES.values()); resw = list(RESW.values()); resb = list(RESB.values())
span = max(w["lnlam"] - w["lnlam1"] for w in W.values())
r_res = float(np.corrcoef([w["m"] for w in W.values()], res)[0, 1]); s_res = float(np.polyfit([w["m"] for w in W.values()], res, 1)[0])   # the residual against the hole count (round 343 F343-2)
ok = max(abs(x) for x in res) <= 0.45 and abs(float(np.mean(res))) <= 0.2 and max(abs(x) for x in resw) >= 1.0 and max(abs(x) for x in resb) >= 0.9 and span >= 100
ok &= 0.55 <= r_res <= 0.7 and 0.02 <= s_res <= 0.035
gate(f"g3 the exponent: ln lambda_k - ln lambda_1 - 2 ln|ghat_k(0)/ghat_1(0)| against F_k(T_u) - F_1(T_1u) at the 40 safely deep rungs (the eigenvalues and origin values from Theorem 1bw's census): residual within [{min(res):+.2f}, {max(res):+.2f}] nats (gated |.| <= 0.45), mean {float(np.mean(res)):+.2f} (gated |.| <= 0.2), over differences reaching {span:.0f} nats (gated >= 100); the residual grows with the hole count, {s_res:+.4f} nats per hole on a linear fit over the 40 (gated [0.02, 0.035]), correlation {r_res:+.3f} (gated [0.55, 0.7]); at the sharp wall T_w instead the residual reaches {max(abs(x) for x in resw):.2f} (gated >= 1.0), and Theorem 1bx's exterior constant alone reaches {max(abs(x) for x in resb):.2f} (gated >= 0.9)", ok)

# ---------------------------------------------------------------- g4: the continuum law
cu = {key: cont_u(w["m"], w["delta"])*w["T0"] for key, w in W.items()}
rcw = [cu[key]/w["Tw"] for key, w in W.items()]; rc1 = [cu[(c, 2)]/W[(c, 2)]["T1"] for c in ORDER]; rcu = [cu[key]/w["Tu"] for key, w in W.items()]
CSL = {c: float(np.polyfit([w["m"] for (cc, _), w in W.items() if cc == c], [cu[(cc, k)] for (cc, k) in W if cc == c], 1)[0]) for c in ORDER}
exist = all(w["m"] < (math.pi/math.e)*math.exp(w["delta"]) for w in W.values())
closer = sum(1 for c in ORDER if abs(CSL[c] - SL[c][0]) < abs(CSL[c] - SL[c][1]))   # the continuum descent nearer the functional's than the sharp wall's
ok = 0.98 <= float(np.mean(rcw)) <= 0.99 and rms(rcw) <= 0.035 and min(rcw) >= 0.91 and max(rcw) <= 1.05 and all(0.98 <= x <= 1.02 for x in rc1) and exist
ok &= 1.02 <= float(np.mean(rcu)) <= 1.035 and rms(rcu) <= 0.045 and min(rcu) >= 0.98 and max(rcu) <= 1.13 and all(-4.8 <= CSL[c] <= -4.2 for c in ORDER) and closer == 4 and abs(CSL["d2.0"] - SL["d2.0"][1]) < abs(CSL["d2.0"] - SL["d2.0"][0])
gate(f"g4 the continuum law u ln(2/u) = (2m/pi)e^-delta, u = T/T_0, at the 40 rungs -- against its own discrete form's minimiser T_u: uT_0/T_u mean {float(np.mean(rcu)):.3f} (gated [1.02, 1.035]), rms deviation from 1 {rms(rcu):.3f} (gated 0.045), range [{min(rcu):.3f}, {max(rcu):.3f}] (gated within [0.98, 1.13]); against 1bx's sharp wall: uT_0/T_w mean {float(np.mean(rcw)):.3f} (gated [0.98, 0.99]), rms {rms(rcw):.3f} (gated 0.035), range [{min(rcw):.3f}, {max(rcw):.3f}] (gated within [0.91, 1.05]); its per-hole descent d(uT_0)/dm = " + ", ".join(f"{CSL[c]:+.2f}" for c in ORDER) + " at the five cells (gated [-4.8, -4.2]), nearer the functional's than the sharp wall's at " + f"{closer} of 5 (gated 4, the exception delta = 2); for one hole against the ground's edge, uT_0/T_1 = " + ", ".join(f"{x:.3f}" for x in rc1) + " at the five cells (gated [0.98, 1.02]); the root in (2/e, 2) exists at every rung (m < (pi/e) e^delta)", ok)

# ---------------------------------------------------------------- g5: the displacement law at delta = 2 and 2.3 -- the Gram and polished eigenvectors in-process
def polished(cell, NR):
    cfg = LC.CELLS[cell]; d, K, prec = cfg["delta"], cfg["K"], cfg["prec"]; a = d/2
    G, N, _pp = gram(d, K, prec); out = []
    with ctx.workprec(prec):
        ZA = [arb(ZP[i]) if i < len(ZP) else arb(ZS[i]) for i in range(len(ZS))]
        Dm = arb_mat(K, K)
        for i in range(K): Dm[i, i] = 1/N[i].sqrt()
        E, Rv = acb_mat((Dm*G*Dm).mid()).eig(right=True, algorithm="approx")
        order = sorted(range(K), key=lambda i: float(E[i].real.mid()))
        Gm = G.mid(); Nm = arb_mat(K, K)
        for i in range(K): Nm[i, i] = N[i]
        aa = arb(a); om = [arb(i)*arb.pi()/aa for i in range(K)]
        for j in range(NR):
            x = arb_mat(K, 1)
            for i in range(K): x[i, 0] = Rv[i, order[j]].real.mid()/N[i].sqrt()
            lam = (x.transpose()*Gm*x)[0, 0]/(x.transpose()*Nm*x)[0, 0]
            for it in range(2):                                              # inverse iteration on the pencil
                A = Gm - Nm*(lam*(1 - arb("1e-12"))); y = A.solve(Nm*x).mid()
                nr = (y.transpose()*Nm*y)[0, 0].sqrt(); x = arb_mat(K, 1)
                for i in range(K): x[i, 0] = y[i, 0]/nr
                lam = (x.transpose()*Gm*x)[0, 0]/(x.transpose()*Nm*x)[0, 0]
            res = Gm*x - Nm*x*lam; ref = Nm*x*lam
            resid = float(max(abs(res[i, 0]) for i in range(K))/max(abs(ref[i, 0]) for i in range(K)))
            v = [x[i, 0] for i in range(K)]; nrm = (x.transpose()*Nm*x)[0, 0]
            sg = [v[i] if i % 2 == 0 else -v[i] for i in range(K)]; gz = []; gpz = []
            for r in ZA:                                                     # signed ghat and ghat' at every listed zeta zero
                s = arb(0); sp = arb(0)
                for i in range(K):
                    den = r*r - om[i]*om[i]; s += sg[i]*r/den; sp += sg[i]*(-(r*r + om[i]*om[i]))/(den*den)
                sn, cs = (r*aa).sin(), (r*aa).cos()
                gz.append(2*sn*s); gpz.append(2*aa*cs*s + 2*sn*sp)
            out.append({"k": j + 1, "lam": float(lam.mid()), "norm": float(nrm.mid()), "resid": resid, "v": [t.str(300, radius=False) for t in v],
                        "g": [t.str(40, radius=False) if t != 0 else "0" for t in gz], "gp": [t.str(40, radius=False) for t in gpz]})
    return out, K, a
def law_check(cell, NR):
    rungs, K, a = polished(cell, NR); S = CEN[cell]; T1 = S["rungs"][0]["edge"]
    omf = np.arange(K)*math.pi/a; sgn = np.array([1.0 if j % 2 == 0 else -1.0 for j in range(K)])
    Rmax = 40*T1; R = np.linspace(0, Rmax, 800001); dr = R[1] - R[0]; SP = np.diff(ZS)
    rows = []; tails = []; resids = []
    for Rk in rungs:
        k = Rk["k"]; lam = Rk["lam"]; resids.append(Rk["resid"])
        with _mp.workdps(80):
            vm = [_mp.mpf(t) for t in Rk["v"]]; g = [_mp.mpf(t) for t in Rk["g"]]; gp = [_mp.mpf(t) for t in Rk["gp"]]
            am = _mp.mpf(a); omm = [_mp.mpf(i)*_mp.pi/am for i in range(K)]; sgm = [1 if i % 2 == 0 else -1 for i in range(K)]
            def gh_mp(r):
                s = _mp.mpf(0); sp = _mp.mpf(0)
                for i in range(K):
                    den = r*r - omm[i]*omm[i]; s += sgm[i]*vm[i]*r/den; sp += sgm[i]*vm[i]*(-(r*r + omm[i]*omm[i]))/(den*den)
                sn, cs = _mp.sin(r*am), _mp.cos(r*am); return 2*sn*s, 2*am*cs*s + 2*sn*sp
            vf = np.array([float(t) for t in vm]); w = np.array([float(t*t) for t in g])
            gh = np.empty_like(R)
            for s0 in range(0, len(R), 100000):
                Rs = R[s0:s0 + 100000]
                with np.errstate(divide="ignore", invalid="ignore"):
                    gh[s0:s0 + 100000] = 2*np.sin(Rs*a)*np.sum(sgn[None, :]*vf[None, :]*Rs[:, None]/(Rs[:, None]**2 - omf[None, :]**2), axis=1)
            gh[0] = 2*a*vf[0]; gh = np.nan_to_num(gh); g2 = gh*gh; Ssum = float(np.sum(sgn*vf))
            L = 2*float(np.sum(w)); Ltrue = lam*Rk["norm"]; Mtail = -(Ltrue - L); tails.append(1 - L/Ltrue)   # the zeros beyond the list: each term -2 w_l (1 + O(gamma_j^2/gamma_l^2))
            ra = S["rungs"][k - 1]; dodge = {int(np.argmin(np.abs(ZS - gz))): z for gz, z in ra["dodging"]}
            for j, tau in sorted(dodge.items()):
                gam = ZS[j]; dj = float(g[j]/gp[j]); big = abs(dj) > 1e-9
                if big:                                                      # the exact designed zero by Newton from the census zero
                    t = _mp.mpf(tau)
                    for _ in range(8):
                        f0, f1 = gh_mp(t); t -= f0/f1
                    tau = float(t); dj = gam - tau
                tt = tau if big else gam
                with np.errstate(divide="ignore", invalid="ignore"):
                    ker = np.nan_to_num(g2*R*R/(tt*tt - R*R))
                H = float(np.sum(ker))*dr/math.pi - 2*Ssum**2/(math.pi*Rmax)
                mask = np.ones(len(ZS), bool); mask[j] = False
                with np.errstate(divide="ignore", invalid="ignore"):
                    M = 2*float(np.sum((w*ZS**2/(tt*tt - ZS**2))[mask])) + Mtail
                own = float(2*g[j]*g[j])*gam*gam/(tau*tau - gam*gam) if big else float(-gam*g[j]*gp[j])
                dform = (M - lam*H)/(gam*float(gp[j]*gp[j]))                 # the displacement formula, sign included: d_j = (M_j - lambda H_j)/(gamma_j ghat'^2)
                proxy = (gam/ZS[-1])**2*abs(Mtail)/abs(lam*H)              # the neglected O(gamma_j^2/gamma_l^2) part of the tail term, relative to lambda H (round 342 F342-6)
                rows.append((cell, k, gam/T1, (own + M)/(lam*H), M/(lam*H), math.log(abs(dj)) if dj != 0 else -1e9, dform/dj if (dj != 0 and not big) else 1.0, proxy))
    return rows, tails, resids
t0 = time.time(); rows = []; tails = []; resids = []
for cell, NR in (("d2.0", 4), ("d2.3", 7)):
    r_, t_, s_ = law_check(cell, NR); rows += r_; tails += t_; resids += s_; print(f"  g5 {cell}: {len(r_)} dodged zeros, {time.time() - t0:.0f}s", flush=True)
ratio = np.array([r[3] for r in rows]); field = np.array([r[4] for r in rows]); dsign = np.array([r[6] for r in rows]); prox = np.array([r[7] for r in rows])
r_tail = float(np.corrcoef(np.abs(ratio - 1), prox)[0, 1])                                         # the residual against the neglected tail term's proxy
BOT = {}
for r in rows:
    if (r[0], r[1]) not in BOT: BOT[(r[0], r[1])] = r[4]                                            # rows come in height order per rung: the lowest dodged zero's field ratio
gbot = [BOT[("d2.0", 1)], BOT[("d2.3", 1)]]; rbot = [v for (c, k), v in BOT.items() if k >= 2]
MAXF = {}
for r in rows: MAXF[(r[0], r[1])] = max(MAXF.get((r[0], r[1]), 0.0), abs(r[4]))                    # the field ratio's largest magnitude per rung (round 346 F346-1)
BIG = [key for key, v in MAXF.items() if v >= 1000]; small = [v for key, v in MAXF.items() if v < 1000]
BINS = [0, 0.3, 0.5, 0.7, 0.8, 0.9, 1.0]
gb = [float(np.mean([r[5] for r in rows if r[0] == "d2.3" and r[1] == 1 and lo <= r[2] < hi])) for lo, hi in zip(BINS[:-1], BINS[1:])]   # the ground's ln|d| per bin at delta = 2.3
ok = len(rows) == 295 and float(np.max(np.abs(ratio - 1))) <= 5e-3 and abs(float(np.median(ratio)) - 1) <= 2e-4 and max(resids) <= 1e-150
ok &= field.min() <= -3000 and field.max() >= 1 and all(0.015 <= t <= 0.03 for t in tails) and gb[0] <= -70 and gb[-1] >= -4
nlin = int(np.sum(dsign != 1.0)); ok &= float(np.max(np.abs(dsign - 1))) <= 5e-3 and nlin >= 100          # the displacement formula with its sign, at the linearised zeros (|d| <= 1e-9)
ok &= r_tail >= 0.95 and all(x <= -10 for x in gbot) and all(-3 <= x <= 3 for x in rbot) and float(np.min(np.abs(field))) <= 1.0 and len(BOT) == 11
ok &= BIG == [("d2.0", 1), ("d2.3", 1), ("d2.3", 2)] and len(small) == 8 and 30 <= min(small) and max(small) <= 600
gate(f"g5 the displacement law at every dodged zeta zero of the 11 rungs at delta = 2 (4) and 2.3 (7), the Gram and polished eigenvectors recomputed in-process (pencil residuals <= {max(resids):.1e}, gated 1e-150): (own + M)/(lambda H) = 1 within {float(np.max(np.abs(ratio - 1))):.6f} at all {len(rows)} (gated 5e-3; count 295), median {float(np.median(ratio)):.7f}; the field ratio M/(lambda H) from {field.max():+.3f} to {field.min():+.2f} (gated >= 1 and <= -3000: the locked zone's displacements are the leakage's field); the leakage beyond the list {min(tails):.5f}-{max(tails):.5f} of the total (gated [0.015, 0.03]); the ground's ln|d| per bin of gamma/T_1 at delta = 2.3: " + ", ".join(f"{x:.1f}" for x in gb) + " (gated <= -70 at the bottom, >= -4 at the top); " + f"the displacement formula d_j = (M_j - lambda H_j)/(gamma_j ghat'(gamma_j)^2) against ghat/ghat' within {float(np.max(np.abs(dsign - 1))):.1e} at the {nlin} linearised zeros, |d| <= 1e-9 (gated 5e-3, >= 100); the residual |ratio - 1| correlates {r_tail:.4f} with the neglected tail term's proxy (gamma_j/gamma_6700)^2 |M_tail|/|lambda H| (gated >= 0.95: the floor is the disclosed tail approximation's); the field ratio at the lowest dodged zero: {gbot[0]:+.3f} and {gbot[1]:+.3f} for the two ground states (gated <= -10), from {min(rbot):+.3f} to {max(rbot):+.3f} for the nine rungs (gated within [-3, 3]), its magnitude falling to {float(np.min(np.abs(field))):.4f} at one zero (gated <= 1); its largest magnitude per rung above a thousand at {BIG} ({MAXF[('d2.0', 1)]:.0f}, {MAXF[('d2.3', 1)]:.0f}, {MAXF[('d2.3', 2)]:.0f}; gated exactly these) and {min(small):.0f}-{max(small):.0f} at the other eight (gated within [30, 600])", ok)

# ---------------------------------------------------------------- g6
import paper_needles
S_GROUND = 'F₁’s minimiser is the ground state’s edge: the same zeta zero at δ = 2 and 2.3, one zero below it at δ = 2.6 and 3, three zeros above it at δ = 3.5 (T_u(1)/T₁ = 1.0000, 1.0000, 0.9901, 0.9961, 1.0117)'
S_MARGIN = 'the minimiser’s margin over the runner-up zero is 0.041, 0.056, 0.003, 0.041, 0.007 nats at the five cells, and under 0.02 nats at 11 of the 40 rungs (the closest 0.00008), while a half-nat window about the minimum spans 0.088–0.249 of T_u (median 0.125)'
S_END = 'the domain’s left endpoint T = h_max exceeds the minimum by at least 16.1 nats at the 40 rungs'
S_RUNGS = 'T_u lies between T_k and T_w at 35 of the 40 safely deep rungs — above T_w at δ = 2.3’s rung 2 and δ = 3’s rung 3 and δ = 3.5’s rung 2, below T_k by one zero at δ = 3.5’s rungs 2, 3 and 5, the last cell’s rung 2 in both sets; T_u/T_k averages 1.023 with rms deviation from 1 of 0.036 over [0.997, 1.085], and T_u/T_w averages 0.960 with rms deviation from 1 of 0.054 over [0.871, 1.029]; T_u is Theorem 1bu(iv)’s stored minimiser at 39 of the 40 (the exception δ = 3’s rung 3, a 0.0098-nat tie that 1bu’s grid resolves the other way)'
S_STICKY = 'T_u is the ground state’s minimiser at δ = 2.3’s rung 2 and δ = 3’s rungs 2–3, and is shared with the rung below at 16 rungs'
S_EXP = 'the residual lies within [−0.16, +0.43] nats over the 40 rungs, mean +0.13, across differences reaching 183 nats, and grows with the hole count by +0.028 nats per hole on a linear fit (correlation +0.63) — against 1.28 nats with the sharp wall in place of T_u and 0.96 from the exterior constant alone'
S_CONT = 'uT₀/T_u averages 1.028 with rms deviation from 1 of 0.039 over [0.988, 1.116] at the 40 rungs, uT₀/T_w 0.986 with 0.033 over [0.916, 1.044]; its per-hole descent is 4.43, 4.62, 4.67, 4.50, 4.27 at the five cells, nearer the functional’s than the sharp wall’s at 4 of them; and for one hole uT₀/T₁ = 1.015, 0.999, 0.988, 1.001, 0.993'
S_DISP = '(own + M)/(λH) = 1 within 0.0023 at all 295 dodged zeros of the 11 rungs (median 1.00002), the field ratio M/(λH) running from +4.8 to −6107, the leakage beyond the 6700-zero list 1.9–2.7% of the total, and the ground state’s ln|d| per bin of γ/T₁ (0–0.3, 0.3–0.5, 0.5–0.7, 0.7–0.8, 0.8–0.9, 0.9–1) at δ = 2.3: −78.0, −51.9, −28.1, −13.5, −7.4, −2.5'
S_TAIL = 'the residual’s correlation with the neglected term’s proxy (γ_j/γ₆₇₀₀)²|M_tail|/|λH_j| is 0.99'
S_BOTTOM = 'at the lowest dodged zero M/(λH) is −14.4 and −14.9 for the two ground states and between −2.4 and +2.2 for the nine rungs, its magnitude falling to 0.42 at one zero'
S_EXCESS = 'T_w/T_u − 1 runs from −2.8% to +14.8% over the 40 rungs, correlating +0.52 with the hole count and −0.21 with 1bx’s onset shortfall at T₁, which itself correlates −0.11 with the hole count — the first at t = r√(n − 2)/√(1 − r²) = 3.7, the excess averaging 4.4%, the two negatives within two standard errors of zero (a null correlation’s standard error is 0.16 at n = 40)'
S_SLOPES = 'per hole the functional’s wall descends by 5.43, 4.60, 4.71, 3.64 against the sharp wall’s 3.08, 3.17, 2.58, 1.68 at δ = 2.3, 2.6, 3, 3.5, the gap growing from −1.3%, +5.8%, +0.2%, −1.7% at one hole to +8.2%, +14.8%, +8.7%, +4.4% at the top rung (at δ = 2, three rungs, 3.60 against 4.22, the gap +5.6% to +4.5%)'
S_AGREE = 'at one hole the two walls agree within 2% at 3 of the five cells'
S_HOLES = 'h/T₁ ≤ 0.22 at the forty safely deep rungs (the largest 0.2189)'
S_MAXF = 'its largest magnitude per rung exceeds a thousand at three of the eleven (2154 and 6107 at the ground states, 1185 at δ = 2.3’s rung 2) and runs 37–500 at the other eight'
# each call carries its literal (the precheck's clause D); the strings equal the S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, 'F₁’s minimiser is the ground state’s edge: the same zeta zero at δ = 2 and 2.3, one zero below it at δ = 2.6 and 3, three zeros above it at δ = 3.5 (T_u(1)/T₁ = 1.0000, 1.0000, 0.9901, 0.9961, 1.0117)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the minimiser’s margin over the runner-up zero is 0.041, 0.056, 0.003, 0.041, 0.007 nats at the five cells, and under 0.02 nats at 11 of the 40 rungs (the closest 0.00008), while a half-nat window about the minimum spans 0.088–0.249 of T_u (median 0.125)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the domain’s left endpoint T = h_max exceeds the minimum by at least 16.1 nats at the 40 rungs', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'T_u lies between T_k and T_w at 35 of the 40 safely deep rungs — above T_w at δ = 2.3’s rung 2 and δ = 3’s rung 3 and δ = 3.5’s rung 2, below T_k by one zero at δ = 3.5’s rungs 2, 3 and 5, the last cell’s rung 2 in both sets; T_u/T_k averages 1.023 with rms deviation from 1 of 0.036 over [0.997, 1.085], and T_u/T_w averages 0.960 with rms deviation from 1 of 0.054 over [0.871, 1.029]; T_u is Theorem 1bu(iv)’s stored minimiser at 39 of the 40 (the exception δ = 3’s rung 3, a 0.0098-nat tie that 1bu’s grid resolves the other way)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'T_u is the ground state’s minimiser at δ = 2.3’s rung 2 and δ = 3’s rungs 2–3, and is shared with the rung below at 16 rungs', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the residual lies within [−0.16, +0.43] nats over the 40 rungs, mean +0.13, across differences reaching 183 nats, and grows with the hole count by +0.028 nats per hole on a linear fit (correlation +0.63) — against 1.28 nats with the sharp wall in place of T_u and 0.96 from the exterior constant alone', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'uT₀/T_u averages 1.028 with rms deviation from 1 of 0.039 over [0.988, 1.116] at the 40 rungs, uT₀/T_w 0.986 with 0.033 over [0.916, 1.044]; its per-hole descent is 4.43, 4.62, 4.67, 4.50, 4.27 at the five cells, nearer the functional’s than the sharp wall’s at 4 of them; and for one hole uT₀/T₁ = 1.015, 0.999, 0.988, 1.001, 0.993', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '(own + M)/(λH) = 1 within 0.0023 at all 295 dodged zeros of the 11 rungs (median 1.00002), the field ratio M/(λH) running from +4.8 to −6107, the leakage beyond the 6700-zero list 1.9–2.7% of the total, and the ground state’s ln|d| per bin of γ/T₁ (0–0.3, 0.3–0.5, 0.5–0.7, 0.7–0.8, 0.8–0.9, 0.9–1) at δ = 2.3: −78.0, −51.9, −28.1, −13.5, −7.4, −2.5', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the residual’s correlation with the neglected term’s proxy (γ_j/γ₆₇₀₀)²|M_tail|/|λH_j| is 0.99', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'at the lowest dodged zero M/(λH) is −14.4 and −14.9 for the two ground states and between −2.4 and +2.2 for the nine rungs, its magnitude falling to 0.42 at one zero', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'T_w/T_u − 1 runs from −2.8% to +14.8% over the 40 rungs, correlating +0.52 with the hole count and −0.21 with 1bx’s onset shortfall at T₁, which itself correlates −0.11 with the hole count — the first at t = r√(n − 2)/√(1 − r²) = 3.7, the excess averaging 4.4%, the two negatives within two standard errors of zero (a null correlation’s standard error is 0.16 at n = 40)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'per hole the functional’s wall descends by 5.43, 4.60, 4.71, 3.64 against the sharp wall’s 3.08, 3.17, 2.58, 1.68 at δ = 2.3, 2.6, 3, 3.5, the gap growing from −1.3%, +5.8%, +0.2%, −1.7% at one hole to +8.2%, +14.8%, +8.7%, +4.4% at the top rung (at δ = 2, three rungs, 3.60 against 4.22, the gap +5.6% to +4.5%)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'at one hole the two walls agree within 2% at 3 of the five cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'h/T₁ ≤ 0.22 at the forty safely deep rungs (the largest 0.2189)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'its largest magnitude per rung exceeds a thousand at three of the eleven (2154 and 6107 at the ground states, 1185 at δ = 2.3’s rung 2) and runs 37–500 at the other eight', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g6'] == [S_GROUND, S_MARGIN, S_END, S_RUNGS, S_STICKY, S_EXP, S_CONT, S_DISP, S_TAIL, S_BOTTOM, S_EXCESS, S_SLOPES, S_AGREE, S_HOLES, S_MAXF]
_re = __import__("re")
def _num(s): return float(s.strip().replace('−', '-'))
def _nums(s, pat=r"([-−+]?[0-9]+\.[0-9]+)"): return [_num(x) for x in _re.findall(pat, s)]
def _ints(s): return [int(x) for x in _re.findall(r"(?<![0-9.−-])[0-9]+(?![0-9.])", s)]
_word = {0: "the same zeta zero", -1: "one zero below it", 1: "one zero above it", 3: "three zeros above it", -3: "three zeros below it"}
def _exc(L):
    cs = sorted({c for c, _ in L}); ks = sorted(k for _, k in L)
    if len(cs) != 1 or not ks or ks != list(range(ks[0], ks[-1] + 1)): return "NOT A CELL'S CONTIGUOUS RANGE"
    return f"δ = {CEN[cs[0]]['delta']:g}’s rung" + ("s " + f"{ks[0]}–{ks[-1]}" if len(ks) > 1 else f" {ks[0]}")
def _cells(L): return " and ".join(_exc([(c, k) for c, k in L if c == cc]) for cc in ORDER if any(c == cc for c, _ in L))
_s = S_GROUND.split(": ")[1]; ok &= _s.startswith(_word[didx[0]] + " at δ = 2 and 2.3, " + _word[didx[2]] + " at δ = 2.6 and 3, " + _word[didx[4]] + " at δ = 3.5 (") and didx[0] == didx[1] and didx[2] == didx[3]
_m = _nums(S_GROUND.split("T_u(1)/T₁ = ")[1]); ok &= len(_m) == 5 and _m == [round(x, 4) for x in rat1u]
def _list(L):
    cs = sorted({c for c, _ in L}); ks = sorted(k for _, k in L)
    if len(cs) != 1 or not ks: return "NOT ONE CELL"
    return f"δ = {CEN[cs[0]]['delta']:g}’s rung" + (("s " + ", ".join(str(k) for k in ks[:-1]) + f" and {ks[-1]}") if len(ks) > 1 else f" {ks[0]}")
def _cellsl(L): return " and ".join(_list([(c, k) for c, k in L if c == cc]) for cc in ORDER if any(c == cc for c, _ in L))
_i = _ints(S_RUNGS.split(" —")[0]); ok &= _i == [between, len(W)]
ok &= S_RUNGS.split("above T_w at ")[1].split(", below T_k")[0] == _cellsl(ABOVE) and S_RUNGS.split("by one zero at ")[1].split(", the last")[0] == _cellsl(BELOW) and below_one
_m = _nums(S_RUNGS.split("T_u/T_k averages ")[1].split(", and")[0]); ok &= _m == [round(float(np.mean(ruk)), 3), round(rms(ruk), 3), round(min(ruk), 3), round(max(ruk), 3)]
_m = _nums(S_RUNGS.split("T_u/T_w averages ")[1].split("]; T_u is")[0]); ok &= _m == [round(float(np.mean(ruw)), 3), round(rms(ruw), 3), round(min(ruw), 3), round(max(ruw), 3)]
ok &= _ints(S_RUNGS.split("stored minimiser at ")[1].split(" (the exception")[0]) == [bu_match, len(W)]
_EXC1 = [(c, k) for (c, k), w in W.items() if abs(w["Tk_bu"] - w["Tu"]) > 1e-3]; ok &= len(_EXC1) == 1 and S_RUNGS.split("(the exception ")[1].split(", a ")[0] == _cellsl(_EXC1) and _nums(S_RUNGS.split(", a ")[1].split("-nat")[0]) == [round(W[_EXC1[0]]["margin"], 4)]
ok &= _nums(S_END) == [math.floor(10*endgap)/10] and _ints(S_END.split("at the ")[1]) == [len(W)]
ok &= _ints(S_AGREE.split("within 2% at ")[1]) == [n_agree] and _nums(S_AGREE.split("within ")[1].split("%")[0] + ".0") == [round(100*AGREE_TOL, 1)]
ok &= _nums(S_HOLES) == [0.22, round(hmax, 4)] and hmax <= 0.22 and _ints(S_HOLES.split("at the ")[1].split(" safely")[0] .replace("forty", "40")) == [len(W)]
ok &= _ints(S_MAXF.split("eleven (")[1].split(" at δ")[0]) == [round(MAXF[k]) for k in BIG] and _ints(S_MAXF.split("runs ")[1]) == [round(min(small)), round(max(small))] and len(BIG) == 3 and "δ = 2.3’s rung 2" in S_MAXF and BIG[2] == ("d2.3", 2)
_m = _nums(S_MARGIN.split(" nats at the five")[0]); ok &= _m == [round(x, 3) for x in gmar]
ok &= _ints(S_MARGIN.split("under 0.02 nats at ")[1].split(" of the")[0]) == [nclose] and _nums(S_MARGIN.split("the closest ")[1].split(")")[0]) == [round(min(rmar), 5)]
_m = _nums(S_MARGIN.split("spans ")[1]); ok &= _m == [round(min(wins), 3), round(max(wins), 3), round(float(np.median(wins)), 3)]
_m = _nums(S_EXCESS.split(" — the first")[0]); ok &= _nums(S_EXCESS.split("averaging ")[1].split("%")[0]) == [round(100*mexc, 1)]; ok &= _m == [round(100*exc.min(), 1), round(100*exc.max(), 1), round(r_m, 2), round(r_sh, 2), round(r_ms, 2)] and r_ms < 0
ok &= _nums(S_EXCESS.split("√(1 − r²) = ")[1].split(",")[0]) == [round(tstat(r_m), 1)] and _ints(S_EXCESS.split("r√(n − ")[1].split(")")[0]) == [DOF] and _nums(S_EXCESS.split("standard error is ")[1]) == [round(SE, 2)] and abs(r_sh) <= 2*SE and abs(r_ms) <= 2*SE and _ints(S_EXCESS.split("over the ")[1].split(" rungs")[0]) == [len(W)]
_t = S_SLOPES; ok &= _nums(_t.split("descends by ")[1].split(" against")[0]) == [round(-SL[c][0], 2) for c in ORDER[1:]] and _nums(_t.split("sharp wall’s ")[1].split(" at δ")[0]) == [round(-SL[c][1], 2) for c in ORDER[1:]]
ok &= _nums(_t.split("growing from ")[1].split(" at one hole")[0]) == [round(100*SL[c][2], 1) for c in ORDER[1:]] and _nums(_t.split("at one hole to ")[1].split(" at the top")[0]) == [round(100*SL[c][3], 1) for c in ORDER[1:]]
ok &= _nums(_t.split("three rungs, ")[1].split(")")[0]) == [round(-SL["d2.0"][0], 2), round(-SL["d2.0"][1], 2), round(100*SL["d2.0"][2], 1), round(100*SL["d2.0"][3], 1)]
ok &= S_STICKY.split("minimiser at ")[1].split(", and is shared")[0] == _cells(STICKY) and _ints(S_STICKY.split("rung below at ")[1]) == [len(PAIRS)]
_m = _nums(S_EXP.split(" nats over")[0]); ok &= _m == [round(min(res), 2), round(max(res), 2)] and _ints(S_EXP.split("over the ")[1].split(" rungs")[0]) == [len(W)]
ok &= _nums(S_EXP.split("mean ")[1].split(",")[0]) == [round(float(np.mean(res)), 2)] and _ints(S_EXP.split("reaching ")[1].split(" nats")[0]) == [round(span)]
ok &= _nums(S_EXP.split("hole count by ")[1].split(" nats per hole")[0]) == [round(s_res, 3)] and _nums(S_EXP.split("(correlation ")[1].split(")")[0]) == [round(r_res, 2)]
ok &= _nums(S_EXP.split("against ")[1].split(" nats with")[0]) == [round(max(abs(x) for x in resw), 2)] and _nums(S_EXP.split("T_u and ")[1].split(" from")[0]) == [round(max(abs(x) for x in resb), 2)]
_m = _nums(S_CONT.split(" at the")[0]); ok &= _m == [round(float(np.mean(rcu)), 3), round(rms(rcu), 3), round(min(rcu), 3), round(max(rcu), 3)] and _ints(S_CONT.split("] at the ")[1].split(" rungs")[0]) == [len(W)]
_m = _nums(S_CONT.split("uT₀/T_w ")[1].split(";")[0]); ok &= _m == [round(float(np.mean(rcw)), 3), round(rms(rcw), 3), round(min(rcw), 3), round(max(rcw), 3)]
_m = _nums(S_CONT.split("descent is ")[1].split(" at the five")[0]); ok &= _m == [round(-CSL[c], 2) for c in ORDER] and _ints(S_CONT.split("sharp wall’s at ")[1].split(" of them")[0]) == [closer]
_m = _nums(S_CONT.split("uT₀/T₁ = ")[1]); ok &= len(_m) == 5 and _m == [round(x, 3) for x in rc1]
ok &= _nums(S_TAIL) == [round(r_tail, 2)]
_m = _nums(S_BOTTOM); ok &= _m == [round(gbot[0], 1), round(gbot[1], 1), round(min(rbot), 1), round(max(rbot), 1), round(float(np.min(np.abs(field))), 2)]
_t = S_DISP; ok &= _nums(_t.split("within ")[1].split(" at all")[0]) == [round(float(np.max(np.abs(ratio - 1))), 4)] and _ints(_t.split("at all ")[1].split(" dodged")[0]) == [len(rows)]
ok &= _nums(_t.split("(median ")[1].split(")")[0]) == [round(float(np.median(ratio)), 5)] and _nums(_t.split("running from ")[1].split(" to")[0]) == [round(float(field.max()), 1)] and _re.findall(r"−[0-9]+", _t.split(" to ")[1].split(",")[0]) == ["−" + str(round(abs(float(field.min()))))] and field.min() < 0
ok &= _nums(_t.split("6700-zero list ")[1].split("% of")[0]) == [round(100*min(tails), 1), round(100*max(tails), 1)] and _nums(_t.split("at δ = 2.3: ")[1]) == [round(x, 1) for x in gb] and len(gb) == 6
gate("g6 the paper's numbers parsed back from the declared needles", ok)

# ---------------------------------------------------------------- g7
from cascade_tower import chain_ok
gate("g7 the chain obligation to cascade_rung_balayage.py (Theorem 1bx) met", chain_ok("cascade_rung_balayage.py"))

# ---------------------------------------------------------------- g8
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g8 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g8 the 1by paper needles and the footer census (declared surface)", ok)

print(("ALL GATES PASS (9/9)" if not fails else f"FAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
