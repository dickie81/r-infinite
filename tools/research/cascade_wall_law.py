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
hole pairs; its minimiser T_u(k) (a zeta zero) is the rung's wall and its minimum the rung's exponent:
ln lambda_k - ln lambda_1 = 2 ln|ghat_k(0)/ghat_1(0)| + F_k(T_u) - F_1(T_u(1)). (iii) The continuum law, in 1bm(iv)'s reduced problem
with the hole pairs at the origin: u ln(2/u) = (2m/pi) e^{-delta}, u = T/T_0 -- the maximiser of -f(X) + 4m ln(2X T_0/h), equal to
the vanishing of the inverse-square-root edge coefficient of the rung's outer density (the ground's sqrt(X/2) ln(2/X) against
the holes' m e^{-delta} (2/pi)/sqrt(2X)); a root below 2 exists iff m < (pi/e) e^delta. (iv) Verified at the cells: the ground's
edge is F_1's minimiser (the same zero at delta = 2, 2.3; within one zero at 2.6, 3; three at 3.5); the rungs' T_u between the
census edge T_k and 1bx's sharp wall T_w at 35 of 40, the exponent within half a nat at all 40; the continuum law within 3.3% rms of
T_w; the displacement law exact at every dodged zero of 11 rungs at delta = 2 and 2.3; the sharp wall's excess over T_u (4% on
average) is the soft onset's, quantified, not derived.

THE GATES. (0) the algebra witnessed at 60 digits; (1) the functional's minimisers are zeta zeros, and the ground's is its edge;
(2) the rungs' T_u against T_k and T_w; (3) the exponent at every safely deep rung; (4) the continuum law; (5) the displacement
law at delta = 2, 2.3 (the Gram and polished eigenvectors recomputed in-process: no checkpoint, no producer); (6) the paper's
numbers parsed back; (7) the chain obligation; (8) the needles and census.

WHAT IS NOT CLAIMED. The soft onset's law (T_w/T_u); the reduction of 1bm(iii) (conjectural there, inherited here by (iii));
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
    {'g': 'g6', 's': 'T_u lies between T_k and T_w at 35 of the 40 safely deep rungs; T_u/T_k averages 1.023 with rms deviation 0.036 over [0.997, 1.085], and T_u/T_w averages 0.960 with rms deviation 0.054 over [0.871, 1.029]', 'form': 'ws'},
    {'g': 'g6', 's': 'T_u is the ground state’s minimiser at δ = 2.3’s rung 2 and δ = 3’s rungs 2–3, and is shared with the rung below at 16 rungs', 'form': 'ws'},
    {'g': 'g6', 's': 'the residual lies within [−0.16, +0.43] nats over the 40 rungs, mean +0.13, across differences reaching 183 nats — against 1.28 nats with the sharp wall in place of T_u and 0.96 from the exterior constant alone', 'form': 'ws'},
    {'g': 'g6', 's': 'uT₀/T_w averages 0.986 with rms deviation 0.033 over [0.916, 1.044] at the 40 rungs, and for one hole uT₀/T₁ = 1.015, 0.999, 0.988, 1.001, 0.993 at the five cells', 'form': 'ws'},
    {'g': 'g6', 's': '(own + M)/(λH) = 1 within 0.0023 at all 295 dodged zeros of the 11 rungs (median 1.00002), the field ratio M/(λH) running from +4.8 to −6107, the leakage beyond the 6700-zero list 1.9–2.7% of the total, and the ground state’s ln|d| per bin of γ/T₁ (0–0.3, 0.3–0.5, 0.5–0.7, 0.7–0.8, 0.8–0.9, 0.9–1) at δ = 2.3: −78.0, −51.9, −28.1, −13.5, −7.4, −2.5', 'form': 'ws'},
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
def argmin_zero(a, holes, jmax):   # the minimiser over the zeta zeros above the holes
    jmin = max(int(np.searchsorted(ZS, max(holes)*1.000001)) if holes else 1, 1)
    vals = [Fk(ZS[j], a, holes) for j in range(jmin, jmax)]
    i = int(np.argmin(vals)); return i + jmin
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
    ok &= abs(_mp.diff(lambda u: u*_mp.log(2/u), 2/_mp.e)) <= _mp.mpf("1e-25") and abs((2/_mp.e)*_mp.log(_mp.e) - 2/_mp.e) <= _mp.mpf("1e-30")
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
    jmax = int(np.searchsorted(ZS, 3*T1)); j1 = argmin_zero(a, [], jmax); jedge = int(np.argmin(np.abs(ZS - T1)))
    G1[c] = {"j1": j1, "jedge": jedge, "T1u": ZS[j1], "T1": T1, "a": a, "T0": S["T0"], "delta": S["delta"], "jmax": jmax}
    for r in S["rungs"][1:ns + 1]:
        k = r["k"]; holes = sorted(r["holes"]); Tw = solve_T(holes, L[k]["Dkappa"]); ju = argmin_zero(a, holes, jmax)
        W[(c, k)] = {"k": k, "m": k - 1, "holes": holes, "Tw": Tw, "T1": T1, "Tk": r["edge"], "ju": ju, "Tu": ZS[ju], "T1u": ZS[j1],
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
ok = didx == [0, 0, -1, -1, 3] and all(0.99 <= x <= 1.012 for x in rat1u) and all(zmin) and len(zmin) == 45
gate("g1 the functional's minimiser is a zeta zero at every one of the 45 functionals (F_1 at the five cells, F_k at the 40 safely deep rungs; grid of 60 per spacing over [0.5, 1.6] T_1); the ground's edge T_1 is F_1's minimiser: the minimiser's zero index minus the edge's = " + ", ".join(str(x) for x in didx) + " at the five cells (gated 0, 0, -1, -1, 3), T_1u/T_1 = " + ", ".join(f"{x:.4f}" for x in rat1u) + " (gated [0.99, 1.012])", ok)

# ---------------------------------------------------------------- g2: the rungs' T_u against T_k and T_w
ruk = [w["Tu"]/w["Tk"] for w in W.values()]; ruw = [w["Tu"]/w["Tw"] for w in W.values()]
between = sum(1 for w in W.values() if w["Tk"]*0.9999 <= w["Tu"] <= w["Tw"]*1.0001)
rms = lambda x: math.sqrt(float(np.mean((np.asarray(x) - 1)**2)))
STICKY = [(c, k) for (c, k), w in W.items() if w["ju"] == G1[c]["j1"]]                       # T_u = the ground's minimiser
PAIRS = [(c, k) for (c, k), w in W.items() if (c, k - 1) in W and W[(c, k - 1)]["ju"] == w["ju"]]   # T_u shared with the rung below
ok = between == 35 and len(W) == 40 and 1.02 <= float(np.mean(ruk)) <= 1.03 and rms(ruk) <= 0.04 and min(ruk) >= 0.99 and max(ruk) <= 1.09
ok &= 0.95 <= float(np.mean(ruw)) <= 0.97 and rms(ruw) <= 0.06 and min(ruw) >= 0.87 and max(ruw) <= 1.03
ok &= STICKY == [("d2.3", 2), ("d3.0", 2), ("d3.0", 3)] and len(PAIRS) == 16
gate(f"g2 the unlocking height T_u = argmin F_k at the 40 safely deep rungs: between the census edge T_k and 1bx's sharp wall T_w at {between} of 40 (gated 35); T_u/T_k mean {float(np.mean(ruk)):.3f}, rms deviation {rms(ruk):.3f}, range [{min(ruk):.3f}, {max(ruk):.3f}] (gated mean in [1.02, 1.03], rms <= 0.04, range within [0.99, 1.09]); T_u/T_w mean {float(np.mean(ruw)):.3f}, rms {rms(ruw):.3f}, range [{min(ruw):.3f}, {max(ruw):.3f}] (gated mean in [0.95, 0.97], rms <= 0.06, range within [0.87, 1.03]); T_u = the ground's minimiser at {STICKY} (gated exactly these); T_u shared with the rung below at {len(PAIRS)} rungs (gated 16)", ok)

# ---------------------------------------------------------------- g3: the exponent at every safely deep rung (from Theorem 1bw's census: ln lambda_k and ghat_k(0))
RES = {}; RESW = {}; RESB = {}
for (c, k), w in W.items():
    dl = w["lnlam"] - w["lnlam1"] - w["c2"]
    RES[(c, k)] = Fk(w["Tu"], w["a"], w["holes"]) - F1(w["T1u"], w["a"]) - dl
    RESW[(c, k)] = Fk(w["Tw"], w["a"], w["holes"]) - F1(w["T1u"], w["a"]) - dl
    RESB[(c, k)] = cost(w["holes"], w["Tw"]) - dl
res = list(RES.values()); resw = list(RESW.values()); resb = list(RESB.values())
span = max(w["lnlam"] - w["lnlam1"] for w in W.values())
ok = max(abs(x) for x in res) <= 0.45 and abs(float(np.mean(res))) <= 0.2 and max(abs(x) for x in resw) >= 1.0 and max(abs(x) for x in resb) >= 0.9 and span >= 100
gate(f"g3 the exponent: ln lambda_k - ln lambda_1 - 2 ln|ghat_k(0)/ghat_1(0)| against F_k(T_u) - F_1(T_1u) at the 40 safely deep rungs (the eigenvalues and origin values from Theorem 1bw's census): residual within [{min(res):+.2f}, {max(res):+.2f}] nats (gated |.| <= 0.45), mean {float(np.mean(res)):+.2f} (gated |.| <= 0.2), over differences reaching {span:.0f} nats (gated >= 100); at the sharp wall T_w instead the residual reaches {max(abs(x) for x in resw):.2f} (gated >= 1.0), and Theorem 1bx's exterior constant alone reaches {max(abs(x) for x in resb):.2f} (gated >= 0.9)", ok)

# ---------------------------------------------------------------- g4: the continuum law
cu = {key: cont_u(w["m"], w["delta"])*w["T0"] for key, w in W.items()}
rcw = [cu[key]/w["Tw"] for key, w in W.items()]; rc1 = [cu[(c, 2)]/W[(c, 2)]["T1"] for c in ORDER]
exist = all(w["m"] < (math.pi/math.e)*math.exp(w["delta"]) for w in W.values())
ok = 0.98 <= float(np.mean(rcw)) <= 0.99 and rms(rcw) <= 0.035 and min(rcw) >= 0.91 and max(rcw) <= 1.05 and all(0.98 <= x <= 1.02 for x in rc1) and exist
gate(f"g4 the continuum law u ln(2/u) = (2m/pi)e^-delta, u = T/T_0, against 1bx's sharp wall at the 40 rungs: uT_0/T_w mean {float(np.mean(rcw)):.3f} (gated [0.98, 0.99]), rms deviation {rms(rcw):.3f} (gated 0.035), range [{min(rcw):.3f}, {max(rcw):.3f}] (gated within [0.91, 1.05]); for one hole against the ground's edge, uT_0/T_1 = " + ", ".join(f"{x:.3f}" for x in rc1) + " at the five cells (gated [0.98, 1.02]); the root exists at every rung (m < (pi/e) e^delta)", ok)

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
                rows.append((cell, k, gam/T1, (own + M)/(lam*H), M/(lam*H), math.log(abs(dj)) if dj != 0 else -1e9, dform/dj if (dj != 0 and not big) else 1.0))
    return rows, tails, resids
t0 = time.time(); rows = []; tails = []; resids = []
for cell, NR in (("d2.0", 4), ("d2.3", 7)):
    r_, t_, s_ = law_check(cell, NR); rows += r_; tails += t_; resids += s_; print(f"  g5 {cell}: {len(r_)} dodged zeros, {time.time() - t0:.0f}s", flush=True)
ratio = np.array([r[3] for r in rows]); field = np.array([r[4] for r in rows]); dsign = np.array([r[6] for r in rows])
BINS = [0, 0.3, 0.5, 0.7, 0.8, 0.9, 1.0]
gb = [float(np.mean([r[5] for r in rows if r[0] == "d2.3" and r[1] == 1 and lo <= r[2] < hi])) for lo, hi in zip(BINS[:-1], BINS[1:])]   # the ground's ln|d| per bin at delta = 2.3
ok = len(rows) == 295 and float(np.max(np.abs(ratio - 1))) <= 5e-3 and abs(float(np.median(ratio)) - 1) <= 2e-4 and max(resids) <= 1e-150
ok &= field.min() <= -3000 and field.max() >= 1 and all(0.015 <= t <= 0.03 for t in tails) and gb[0] <= -70 and gb[-1] >= -4
nlin = int(np.sum(dsign != 1.0)); ok &= float(np.max(np.abs(dsign - 1))) <= 5e-3 and nlin >= 100          # the displacement formula with its sign, at the linearised zeros (|d| <= 1e-9)
gate(f"g5 the displacement law at every dodged zeta zero of the 11 rungs at delta = 2 (4) and 2.3 (7), the Gram and polished eigenvectors recomputed in-process (pencil residuals <= {max(resids):.1e}, gated 1e-150): (own + M)/(lambda H) = 1 within {float(np.max(np.abs(ratio - 1))):.6f} at all {len(rows)} (gated 5e-3; count 295), median {float(np.median(ratio)):.7f}; the field ratio M/(lambda H) from {field.max():+.3f} to {field.min():+.2f} (gated >= 1 and <= -3000: the locked zone's displacements are the leakage's field); the leakage beyond the list {min(tails):.5f}-{max(tails):.5f} of the total (gated [0.015, 0.03]); the ground's ln|d| per bin of gamma/T_1 at delta = 2.3: " + ", ".join(f"{x:.1f}" for x in gb) + " (gated <= -70 at the bottom, >= -4 at the top); " + f"the displacement formula d_j = (M_j - lambda H_j)/(gamma_j ghat'(gamma_j)^2) against ghat/ghat' within {float(np.max(np.abs(dsign - 1))):.1e} at the {nlin} linearised zeros, |d| <= 1e-9 (gated 5e-3, >= 100)", ok)

# ---------------------------------------------------------------- g6
import paper_needles
S_GROUND = 'F₁’s minimiser is the ground state’s edge: the same zeta zero at δ = 2 and 2.3, one zero below it at δ = 2.6 and 3, three zeros above it at δ = 3.5 (T_u(1)/T₁ = 1.0000, 1.0000, 0.9901, 0.9961, 1.0117)'
S_RUNGS = 'T_u lies between T_k and T_w at 35 of the 40 safely deep rungs; T_u/T_k averages 1.023 with rms deviation 0.036 over [0.997, 1.085], and T_u/T_w averages 0.960 with rms deviation 0.054 over [0.871, 1.029]'
S_STICKY = 'T_u is the ground state’s minimiser at δ = 2.3’s rung 2 and δ = 3’s rungs 2–3, and is shared with the rung below at 16 rungs'
S_EXP = 'the residual lies within [−0.16, +0.43] nats over the 40 rungs, mean +0.13, across differences reaching 183 nats — against 1.28 nats with the sharp wall in place of T_u and 0.96 from the exterior constant alone'
S_CONT = 'uT₀/T_w averages 0.986 with rms deviation 0.033 over [0.916, 1.044] at the 40 rungs, and for one hole uT₀/T₁ = 1.015, 0.999, 0.988, 1.001, 0.993 at the five cells'
S_DISP = '(own + M)/(λH) = 1 within 0.0023 at all 295 dodged zeros of the 11 rungs (median 1.00002), the field ratio M/(λH) running from +4.8 to −6107, the leakage beyond the 6700-zero list 1.9–2.7% of the total, and the ground state’s ln|d| per bin of γ/T₁ (0–0.3, 0.3–0.5, 0.5–0.7, 0.7–0.8, 0.8–0.9, 0.9–1) at δ = 2.3: −78.0, −51.9, −28.1, −13.5, −7.4, −2.5'
# each call carries its literal (the precheck's clause D); the strings equal the S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, 'F₁’s minimiser is the ground state’s edge: the same zeta zero at δ = 2 and 2.3, one zero below it at δ = 2.6 and 3, three zeros above it at δ = 3.5 (T_u(1)/T₁ = 1.0000, 1.0000, 0.9901, 0.9961, 1.0117)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'T_u lies between T_k and T_w at 35 of the 40 safely deep rungs; T_u/T_k averages 1.023 with rms deviation 0.036 over [0.997, 1.085], and T_u/T_w averages 0.960 with rms deviation 0.054 over [0.871, 1.029]', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'T_u is the ground state’s minimiser at δ = 2.3’s rung 2 and δ = 3’s rungs 2–3, and is shared with the rung below at 16 rungs', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the residual lies within [−0.16, +0.43] nats over the 40 rungs, mean +0.13, across differences reaching 183 nats — against 1.28 nats with the sharp wall in place of T_u and 0.96 from the exterior constant alone', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'uT₀/T_w averages 0.986 with rms deviation 0.033 over [0.916, 1.044] at the 40 rungs, and for one hole uT₀/T₁ = 1.015, 0.999, 0.988, 1.001, 0.993 at the five cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '(own + M)/(λH) = 1 within 0.0023 at all 295 dodged zeros of the 11 rungs (median 1.00002), the field ratio M/(λH) running from +4.8 to −6107, the leakage beyond the 6700-zero list 1.9–2.7% of the total, and the ground state’s ln|d| per bin of γ/T₁ (0–0.3, 0.3–0.5, 0.5–0.7, 0.7–0.8, 0.8–0.9, 0.9–1) at δ = 2.3: −78.0, −51.9, −28.1, −13.5, −7.4, −2.5', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g6'] == [S_GROUND, S_RUNGS, S_STICKY, S_EXP, S_CONT, S_DISP]
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
_i = _ints(S_RUNGS.split(";")[0]); ok &= _i == [between, len(W)]
_m = _nums(S_RUNGS.split("T_u/T_k averages ")[1].split(", and")[0]); ok &= _m == [round(float(np.mean(ruk)), 3), round(rms(ruk), 3), round(min(ruk), 3), round(max(ruk), 3)]
_m = _nums(S_RUNGS.split("T_u/T_w averages ")[1]); ok &= _m == [round(float(np.mean(ruw)), 3), round(rms(ruw), 3), round(min(ruw), 3), round(max(ruw), 3)]
ok &= S_STICKY.split("minimiser at ")[1].split(", and is shared")[0] == _cells(STICKY) and _ints(S_STICKY.split("rung below at ")[1]) == [len(PAIRS)]
_m = _nums(S_EXP.split(" nats over")[0]); ok &= _m == [round(min(res), 2), round(max(res), 2)] and _ints(S_EXP.split("over the ")[1].split(" rungs")[0]) == [len(W)]
ok &= _nums(S_EXP.split("mean ")[1].split(",")[0]) == [round(float(np.mean(res)), 2)] and _ints(S_EXP.split("reaching ")[1].split(" nats")[0]) == [round(span)]
ok &= _nums(S_EXP.split("against ")[1].split(" nats with")[0]) == [round(max(abs(x) for x in resw), 2)] and _nums(S_EXP.split("T_u and ")[1].split(" from")[0]) == [round(max(abs(x) for x in resb), 2)]
_m = _nums(S_CONT.split(" at the")[0]); ok &= _m == [round(float(np.mean(rcw)), 3), round(rms(rcw), 3), round(min(rcw), 3), round(max(rcw), 3)] and _ints(S_CONT.split("] at the ")[1].split(" rungs")[0]) == [len(W)]
_m = _nums(S_CONT.split("uT₀/T₁ = ")[1]); ok &= len(_m) == 5 and _m == [round(x, 3) for x in rc1]
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
