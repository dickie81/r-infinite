#!/usr/bin/env python3
"""Theorem 1bz (the gap's law -- the two walls' leakage budget): the verifier. The tower's member 35 (top); chain obligation to
cascade_wall_law.py (Theorem 1by), whose sharp-wall excess this block derives.

WHAT THE BLOCK CLAIMS. Two walls per rung: T_u, the minimiser of Theorem 1by's unlocking functional (the onset of unlocking, a
zeta zero), and T_w, Theorem 1bx's sharp wall (the R^-2-moment wall of the outer count deficit n_1 - n_k). Shares: s_ext the
rung's share of its leakage lambda_k ||g_k||^2 at the zeta zeros beyond T_1 (the tail beyond the 6700-zero list included);
S_1(x) the ground state's share beyond x T_1 (S_1(1) = 0.96-0.98: the ground leaks two to four percent below its edge);
s_hat = s_ext/S_1(1) the rung's exterior share relative to the ground state's own. (i) The exterior reads the sharp wall: under
Hypothesis B the two exterior leakages stand in the ratio of the envelope lifts squared, so ln(lambda_k s_ext/(lambda_1 S_1(1)))
- 2 ln|ghat_k(0)/ghat_1(0)| = cost(T_w) := 4 sum_h ln(1/sigma_h(T_w)) -- within 0.11 nats rms at the 40 rungs, and not at T_u
(1.7 nats rms). The envelope itself, read by the estimator A(gamma)^2 = ghat(gamma)^2 + ghat(mid)^2 (a zero displaced by d
spacings gives ghat(gamma) = A sin(pi d), ghat(mid) = A cos(pi d)), is not lifted uniformly: its lift over the ground state's
minus B's constant runs a third of a nat low on [T_1, 1.25 T_1) and a sixth high on [1.25, 2) T_1 -- 1bx's onset lag in the
envelope, and a far-field overshoot; the deficit's log-moment (exact from the census: V(infinity) = 2[sum_{O_1} ln tau -
sum_{O_k} ln tau - sum_h ln h]) sees the same far-field excess, naming a wall 1.5% above T_w at 38 of 40 rungs -- the harmonic
measure's log-mean per hole is ln((1 + s_h) T), s_h = (1 - sigma_h^2)/(1 + sigma_h^2), witnessed in g0. (ii) The leakage budget
(an identity): the exponent read twice -- Theorem 1by's functional at T_u (the total leakage) and Hypothesis B on the exterior
at T_w (the exterior leakage) -- gives
        cost(T_w) - cost(T_u) = U - ln(1/s_hat) + epsilon,   U = F_1(T_u) - F_1(T_1u),
epsilon = r_2 - r_1 the difference of the two readings' residuals (formula less value; each within half a nat), the norm ratio
exactly 1 (the eigenvectors N-normalised). (iii) The share's law: the rung's leakage profile is the ground state's attached at
T_u -- s_ext = S_1(T_1/T_u) -- so T_w follows from the ground state alone: T_u and U (the functional, with the rung's holes its
only rung input), S_1 (the ground's leakage profile), no rung leakage consulted; to under one percent rms at the thirty rungs
with three or more holes, and not at one or two holes, where the zone is at most nine zeros wide and the identity's own residual
over four hole slopes is the gap's size. (iv) The leading law: F_1' = ln(T/2T_0) in the continuum (witnessed), so U =
dT^2/(2 T_1u), dT = T_1u - T_u, and cost' = 4m/T give ln(T_w/T_u) = dT^2/(8m T_1u) - ln(1/s_hat)/(4m); with 1by(iii)'s dT ~ 4m
in one factor, ln(T_w/T_u) = dT/(2 T_1u) - ln(1/s_hat)/(4m): the sharp wall is the geometric mean sqrt(T_u T_1u) reduced by the
zone's share, s_hat^{1/(4m)} -- 1bx's "near the geometric mean of the two edges" explained (T_1u is T_1 or a zero within three
of it; T_u is T_k or a zero above it), and the gap's growth with the hole count is the unlocking cost's; the law's forms are
gated at their residuals. (v) The zone's anatomy: the zone's zeros are half-held (sin^2(pi d) averages 0.46 over the 537 zone
zeros), the observed deficit at T_1 (0-3) lies below the sharp profile at T_u (0.5-4.4) at every rung with three or more holes,
and the zone carries under a fifth of -Delta kappa_k.

THE GATES. (0) the profiles' integrity (every state's polished eigenvalue against the census, the pencil residuals, the list's
capture) and the algebra witnessed at 60 digits (the pair deficit's two moments, the continuum slope); (1) the exterior reading
at T_w against T_u, the envelope by sub-window, the log-moment wall; (2) the identity, its residuals, T_w recovered from T_u, U
and the measured share; (3) the share's law and T_w from the ground state alone; (4) the leading law and its forms; (5) the
zone's anatomy; (6) the paper's numbers parsed back; (7) the chain obligation; (8) the needles and census.

WHAT IS NOT CLAIMED. A derivation of the ground state's leakage profile S_1 (computed from the polished ground state, a
ground-state input, not a rung input); the law at one or two holes; Hypothesis B beyond the safely deep rungs; the reduction of
1bm(iii); the odd sector; no Riemann Hypothesis consequence.
"""
import math, os, sys, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ladder_caster as LC
from rung_anatomy import run as run_RA
from rung_laws import run as run_RL
from ladder_caster import run as run_LC
from leakage_profiles import run as run_LP
import mpmath as _mp

PAPER_NEEDLES = [
    {'g': 'g8', 's': "Theorem 1bz (the gap", 'form': 'plain'},
    {'g': 'g8', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 17},
    {'s': '`cascade_gap_law.py`', 'min': 2, 'g': 'g8'},
    {'s': 'the **102 scripts cited in place** above', 'form': 'ws', 'g': 'g8'},
    {'s': 'extended by Theorems 1i–1bz:', 'form': 'ws', 'g': 'g8'},
    {'g': 'g6', 's': 'the polished eigenvalues equal the census’s within 10⁻⁸ at all 54 states of the five cells, the pencil residuals lie below 10⁻¹⁵⁰, and the 6700-zero list carries 96.1–99.7% of every state’s leakage', 'form': 'ws'},
    {'g': 'g6', 's': 'ln(λ_k s_ext/(λ₁S₁(1))) − 2 ln|ĝ_k(0)/ĝ₁(0)| equals 4Σ_h ln(1/σ_h(T_w)) within +0.01 ± 0.11 nats (mean, rms; 0.30 at most) at the 40 rungs, against −1.09 ± 1.72 with T_u in place of T_w', 'form': 'ws'},
    {'g': 'g6', 's': 'the envelope lift over the ground state’s minus that constant runs −0.34 ± 0.48 nats on [T₁, 1.25T₁), +0.16 ± 0.32 on [1.25T₁, 1.5T₁) and +0.18 ± 0.26 on [1.5T₁, 2T₁) (means and rms over the 40 rungs)', 'form': 'ws'},
    {'g': 'g6', 's': 'the log-moment wall lies above T_w at 38 of the 40 rungs, by 1.5% on average with a scatter of 0.012 about that offset (T_log/T_w over [0.987, 1.040])', 'form': 'ws'},
    {'g': 'g6', 's': 'cost(T_w) − cost(T_u) = U − ln(1/ŝ) within a residual of mean −0.12 and rms 0.23 nats over [−0.61, +0.22] at the 40 rungs (the two readings’ residuals within [−0.16, +0.43] and ±0.30 nats; the norm ratio 1)', 'form': 'ws'},
    {'g': 'g6', 's': 'T_w recovered from T_u, U and the measured share within 1.2% rms at the 40 rungs and 0.9% at the 30 with three or more holes (T_id/T_w over [0.968, 1.031])', 'form': 'ws'},
    {'g': 'g6', 's': 'ln(S₁(T₁/T_u)/s_ext) averages −0.06 with rms 0.11 over [−0.31, +0.15] at the 40 rungs (rms 0.10 at the 30 with three or more holes)', 'form': 'ws'},
    {'g': 'g6', 's': 'T_w from the ground state alone lies within 0.9% rms of 1bx’s at the 30 rungs with three or more holes (T_ss/T_w averages 1.0026 over [0.978, 1.025], beyond one percent at 6 of the 30) and within 2.1% rms at all 40, the worst δ = 2.6’s rung 2 at −10.4%', 'form': 'ws'},
    {'g': 'g6', 's': 'at one hole the exterior share is 0.92–0.94 where S₁(T₁/T_u) runs 0.67–0.97, the zone at one or two holes 0–9 zeros wide', 'form': 'ws'},
    {'g': 'g6', 's': 'at the five one-hole rungs the residual is +0.09, +0.01, +0.13, +0.04, −0.12 nats, over four hole slopes 0.2–3.2% in the wall against one-hole gaps of −1.7% to +5.8%', 'form': 'ws'},
    {'g': 'g6', 's': '√(T_uT_u(1))/T_w averages 1.016 with rms deviation from 1 of 0.023; reduced by the share, ŝ^{1/(4m)}√(T_uT_u(1))/T_w averages 1.000 with 0.016 (0.011 at the 30 rungs with three or more holes)', 'form': 'ws'},
    {'g': 'g6', 's': 'the law’s residual in ln T is 0.017 rms in the boxed form, 0.013 with the exact U in place of ΔT²/(2T_u(1)), 0.023 with U_c and 0.025 with ΔT = 4m throughout, over the 40 rungs; ΔT/(4m) runs 0.79–1.78 at the 30 rungs with three or more holes', 'form': 'ws'},
    {'g': 'g6', 's': 'U/U_c averages 0.93 over [0.24, 1.21] at the 30 rungs with three or more holes, and runs 0.24–1.64 at the 7 with one or two holes and a wall below the ground state’s minimiser', 'form': 'ws'},
    {'g': 'g6', 's': 'sin²(πd) averages 0.46 over the 537 zeta zeros of the zones (0.48 as the mean of the 39 rungs’ means, standard deviation 0.14); the observed deficit at T₁ lies below the sharp profile at T_u at all 30 rungs with three or more holes, by 0.88 zeros on average, the profile’s count there 0.48–4.39 zeros and the observed 0–3', 'form': 'ws'},
    {'g': 'g6', 's': 'the zone [T_u, T₁) carries at most 18% of −Δκ_k and the exterior beyond T₁ at least 82%', 'form': 'ws'},
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
PRO = {c: run_LP(c) for c in ORDER}                                 # Theorem 1bz's keyed producer: the polished states' leakage profiles
ZS = np.array(json.load(open(LC.ZD)), dtype=float)                  # Theorem 1bm's 6700-zero list (data; its hash in every key)
SAFE = -20.0
def n_safe(c):
    st = EV[c]; pro = st["prolate_ln_leakage"]
    return len([r for r in st["rungs"][1:] if 2*r["k"] < len(pro) and pro[2*r["k"]] is not None and pro[2*r["k"]] < SAFE and r["k"] <= 12])

# ---------------------------------------------------------------- the closed forms (Theorems 1bm, 1bx, 1by)
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
def cost(holes, T): return 4*sum(math.log(1/psi(h, T)) for h in holes)     # Theorem 1bx's exterior constant of the hole pairs (ln prod sigma_h^-4)
def Fk(T, a, holes): return F1(T, a) + cost(holes, T)
def argmin_zero(a, holes, jmax):   # Theorem 1by's minimiser over the zeta zeros above the holes
    jmin = max(int(np.searchsorted(ZS, max(holes)*1.000001)) if holes else 1, 1)
    vals = [Fk(ZS[j], a, holes) for j in range(jmin, jmax)]
    return int(np.argmin(vals)) + jmin
def solve_cost(holes, target, hi):  # cost(T) increases with T: the wall at which the hole pairs' constant equals the target
    lo = max(holes)*(1 + 1e-9)
    for _ in range(200):
        mid = 0.5*(lo + hi)
        if cost(holes, mid) < target: lo = mid
        else: hi = mid
    return 0.5*(lo + hi)
def outer(r):                  # Theorem 1bx's outer zero set (the dodging and exterior zeros, the placed pair included)
    Z = [z for _, z in r["dodging"]] + list(r["exterior"])
    if r["n_complex"] == 1 and r["sum_rule_residual"] < 0: Z.append(abs(r["sum_rule_residual"])**-0.5)
    return np.array(sorted(Z))
def P_pair(x, X, sigma):       # Theorem 1bx's pair deficit on the complement of the wall X (the harmonic measure from the pair)
    if x <= X: return 0.0
    th = math.acos(X/x); t = math.tan(th/2); A = (1 + sigma)/(1 - sigma)
    return (2/math.pi)*(math.atan(A*t) + math.atan(t/A))
def sharp(R, T, holes): return sum(P_pair(R, T, psi(h, T)) for h in holes)
def obs_moment(O1, Ok, lo, hi):   # 2 int_lo^hi (n_1 - n_k)(R) R^-3 dR for the step functions
    pts = np.concatenate([[lo], np.sort(np.concatenate([O1[(O1 > lo) & (O1 < hi)], Ok[(Ok > lo) & (Ok < hi)]])), [hi]]); tot = 0.0
    for a_, b_ in zip(pts[:-1], pts[1:]):
        mid = 0.5*(a_ + b_); D = float(np.sum(O1 < mid) - np.sum(Ok < mid))
        tot += D/(a_*a_) if b_ == np.inf else D*(1/(a_*a_) - 1/(b_*b_))
    return tot
def lse(x): x = np.asarray(x, dtype=float); m = float(x.max()); return m + math.log(float(np.sum(np.exp(x - m))))
def rms(x): return math.sqrt(float(np.mean(np.asarray(x, dtype=float)**2)))
def rms1(x): return rms(np.asarray(x, dtype=float) - 1)

# ---------------------------------------------------------------- g0: the profiles' integrity and the algebra witnessed
PI = []
for c in ORDER:
    S = CEN[c]; P = PRO[c]
    ok0 = P["NR"] == len(S["rungs"]) and P["n_zeros"] == len(ZS) and all(len(p["ln_abs_g_at_zeros"]) == len(ZS) and len(p["ln_abs_g_at_mid"]) == P["n_mid"] for p in P["rungs"])
    for r, p in zip(S["rungs"], P["rungs"]):     # every census rung against its profile
        PI.append((c, r["k"], ok0, p["ln_lam"] - r["ln_lam"], p["ln_lam"] - p["ln_lam_eig"], p["log10_resid"], p["norm"] - 1, p["g0"] - r["g0"], math.exp(p["ln_sum2_list"] - p["ln_lam"])))
n_pro = len(PI); d_lam = max(abs(x[3]) for x in PI); d_eig = max(abs(x[4]) for x in PI); resid = max(x[5] for x in PI); d_norm = max(abs(x[6]) for x in PI); d_g0 = max(abs(x[7]) for x in PI)
cap_lo = min(x[8] for x in PI); cap_hi = max(x[8] for x in PI)
with _mp.workdps(60):
    okw = True
    sig = lambda h, T: (h/T)/(1 + _mp.sqrt(1 - (h/T)**2))
    def Ppair(x, X, s):
        th = _mp.acos(X/x); t = _mp.tan(th/2); A = (1 + s)/(1 - s); return (2/_mp.pi)*(_mp.atan(A*t) + _mp.atan(t/A))
    for T, h in ((_mp.mpf(1), _mp.mpf("0.5")), (_mp.mpf(3), _mp.mpf("0.02")), (_mp.mpf(2), _mp.mpf("1.2"))):
        s = sig(h, T); sbar = (1 - s*s)/(1 + s*s)
        # (a) the pair deficit's log-moment: int ln R dP = ln T + int_T^inf (1 - P)/R dR = ln((1 + s_h) T)  (B's constant at infinity, per hole: ln(1/sigma_h) + ln h)
        lm = _mp.log(T) + _mp.quad(lambda R: (1 - Ppair(R, T, s))/R, [T, 2*T, 10*T, 100*T, _mp.inf])
        okw &= abs(lm - _mp.log((1 + sbar)*T)) <= _mp.mpf("1e-20") and abs(_mp.log(1/s) + _mp.log(h) - _mp.log((1 + sbar)*T)) <= _mp.mpf("1e-40")
        # (b) its R^-3 moment 2 int P R^-3 dR = (1 + sigma^2)/(2 T^2)  (Theorem 1bx's law)
        m3 = 2*_mp.quad(lambda R: Ppair(R, T, s)/R**3, [T, 2*T, 10*T, _mp.inf])
        okw &= abs(m3 - (1 + s*s)/(2*T*T)) <= _mp.mpf("1e-20")
    # (c) the continuum slope of F_1: (4/2pi) int_0^T ln(g/2pi)/sqrt(T^2 - g^2) dg = ln(T/4pi), so F_1' = ln(T/(2 T_0)) with 2a = delta, T_0 = 2 pi e^delta -- whence F_1'' = 1/T
    for T in (_mp.mpf(100), _mp.mpf(250)):
        I = (2/_mp.pi)*_mp.quad(lambda g: _mp.log(g/(2*_mp.pi))/_mp.sqrt(T*T - g*g), [0, T/2, T])
        okw &= abs(I - _mp.log(T/(4*_mp.pi))) <= _mp.mpf("1e-20")
    # (d) the hole pairs' constant has slope 4 sum_h 1/sqrt(T^2 - h^2) -> 4m/T
    T, h = _mp.mpf(50), _mp.mpf(3)
    okw &= abs(_mp.diff(lambda t: 4*_mp.log(1/sig(h, t)), T) - 4/_mp.sqrt(T*T - h*h)) <= _mp.mpf("1e-20")
ok = all(x[2] for x in PI) and n_pro == 54 and d_lam <= 1e-8 and d_eig <= 1e-8 and resid <= -150 and d_norm <= 1e-12 and d_g0 <= 1e-12 and 0.94 <= cap_lo and cap_hi <= 0.9995 and okw
gate(f"g0 the profiles' integrity at the {n_pro} states of the five cells (gated 54): the polished eigenvalue against the census within {d_lam:.1e} (gated 1e-8) and against the eigensolver's within {d_eig:.1e} (gated 1e-8), the pencil residuals below 1e{resid:.0f} (gated 1e-150), the N-norm 1 within {d_norm:.1e} (gated 1e-12), ghat(0) against the census within {d_g0:.1e} (gated 1e-12), the 6700-zero list carrying {cap_lo:.4f}-{cap_hi:.4f} of every state's leakage (gated within [0.94, 0.9995]); the algebra witnessed at 60 digits: the pair deficit's log-moment ln((1 + s_h)T) = ln(1/sigma_h) + ln h and its R^-3 moment (1 + sigma_h^2)/(2T^2) at three (T, h); the continuum slope (2/pi) int_0^T ln(g/2pi)/sqrt(T^2 - g^2) dg = ln(T/4pi); the hole constant's slope 4/sqrt(T^2 - h^2)", ok)

# ---------------------------------------------------------------- the per-rung quantities
W = {}; G1 = {}
for c in ORDER:
    S = CEN[c]; L = {l["k"]: l for l in LAW[c]["laws"]}; ns = n_safe(c); g = S["rungs"][0]; T1 = g["edge"]; a = S["delta"]/2; P = PRO[c]
    jmax = int(np.searchsorted(ZS, 3*T1)); j1 = argmin_zero(a, [], jmax); T1u = ZS[j1]; O1 = outer(g)
    p1 = P["rungs"][0]; l1 = np.array(p1["ln_abs_g_at_zeros"]); m1 = np.array(p1["ln_abs_g_at_mid"]); nm = P["n_mid"]
    ok1 = l1 > -1e8; w1 = np.zeros(len(ZS)); w1[ok1] = np.exp(2*l1[ok1] + math.log(2) - p1["ln_lam"])      # the ground's shares of lambda_1 (2 sum ghat^2 = lambda ||g||^2 = lambda)
    cum1 = np.cumsum(w1)
    def S1(x, cum1=cum1, T1=T1):           # the ground's leakage share beyond x T_1 (one minus the listed share below it)
        j = int(np.searchsorted(ZS, x*T1)); return 1.0 - (cum1[j - 1] if j > 0 else 0.0)
    E1 = np.full(len(ZS), -1e9)
    for j in range(nm):
        if l1[j] > -1e8 or m1[j] > -1e8: E1[j] = lse([2*l1[j] if l1[j] > -1e8 else -1e9, 2*m1[j] if m1[j] > -1e8 else -1e9])
    S1one = S1(1.0)
    G1[c] = {"T1": T1, "T1u": T1u, "a": a, "delta": S["delta"], "T0": S["T0"], "j1": j1, "S1": S1, "S1one": S1one, "n_mid": nm}
    for r, p in zip(S["rungs"][1:ns + 1], P["rungs"][1:ns + 1]):
        k = r["k"]; m = k - 1; holes = sorted(r["holes"]); Tw = solve_T(holes, L[k]["Dkappa"]); ju = argmin_zero(a, holes, jmax); Tu = ZS[ju]; Ok = outer(r)
        lk = np.array(p["ln_abs_g_at_zeros"]); mk = np.array(p["ln_abs_g_at_mid"]); ok = lk > -1e8
        wk = np.zeros(len(ZS)); wk[ok] = np.exp(2*lk[ok] + math.log(2) - p["ln_lam"])                      # the rung's shares of lambda_k
        Ek = np.full(len(ZS), -1e9)
        for j in range(nm):
            if lk[j] > -1e8 or mk[j] > -1e8: Ek[j] = lse([2*lk[j] if lk[j] > -1e8 else -1e9, 2*mk[j] if mk[j] > -1e8 else -1e9])
        s_below = float(np.sum(wk[ZS < Tu])); s_zone = float(np.sum(wk[(ZS >= Tu) & (ZS < T1)])); s_ext = 1.0 - s_below - s_zone         # the exterior: beyond T_1, the tail beyond the list included
        sh = s_ext/S1one                                                                                     # the share relative to the ground state's own exterior share
        lnN = math.log(p1["norm"]/p["norm"]); c2 = 2*math.log(abs(p["g0"]/p1["g0"])); dl = p["ln_lam"] - p1["ln_lam"]
        U = F1(Tu, a) - F1(T1u, a); gapc = cost(holes, Tw) - cost(holes, Tu)
        res_g3 = c2 + Fk(Tu, a, holes) - F1(T1u, a) - dl                                                  # Theorem 1by's reading at T_u (formula less value)
        res_B = c2 + cost(holes, Tw) + math.log(1/sh) + lnN - dl                                             # Hypothesis B's reading on the exterior at T_w (formula less value)
        res_Bu = c2 + cost(holes, Tu) + math.log(1/sh) + lnN - dl                                            # the same with T_u in place of T_w
        eps = gapc - (U - math.log(1/sh) - lnN)                                                              # = res_B - res_g3
        subs = []
        for lo_, hi_ in ((1.0, 1.25), (1.25, 1.5), (1.5, 2.0)):                                              # the envelope lift minus B's constant, by sub-window
            wsub = (ZS >= lo_*T1) & (ZS < hi_*T1) & (Ek > -1e8) & (E1 > -1e8); subs.append((float(np.mean((Ek - E1)[wsub])) - (c2 + cost(holes, Tw)), int(wsub.sum())))
        T_id = solve_cost(holes, cost(holes, Tu) + U - math.log(1/sh) - lnN, 50*T1)
        s_ss = S1(T1/Tu); sh_ss = s_ss/S1one; T_ss = solve_cost(holes, cost(holes, Tu) + U - math.log(1/sh_ss) - lnN, 50*T1)
        gm0 = math.sqrt(Tu*T1u); gm = gm0*math.exp(-(math.log(1/sh) + lnN)/(4*m)); dT = T1u - Tu
        lead_box = math.log(Tw/Tu) - (dT/(2*T1u) - math.log(1/sh)/(4*m)); lead_uc = math.log(Tw/Tu) - (dT*dT/(2*T1u)/(4*m) - math.log(1/sh)/(4*m))
        lead_U = math.log(Tw/Tu) - (U/(4*m) - math.log(1/sh)/(4*m)); lead_2m = math.log(Tw/Tu) - (2*m/T1u - math.log(1/sh)/(4*m))
        Vinf = 2*(float(np.sum(np.log(O1))) - float(np.sum(np.log(Ok))) - sum(math.log(h) for h in holes)); T_log = solve_cost(holes, 2*Vinf, 50*T1)
        Dk_c = float(np.sum(1/Ok**2) - np.sum(1/O1**2))
        mom = obs_moment(O1, Ok, 1.0, np.inf); mom_zone = obs_moment(O1, Ok, Tu, T1)/mom; mom_ext = obs_moment(O1, Ok, T1, np.inf)/mom
        zone = (ZS >= Tu) & (ZS < T1); N_zone = int(zone.sum()); S_zone = float(np.sum(np.exp(2*lk[zone & ok] - Ek[zone & ok]))) if N_zone else 0.0
        D_T1 = int(np.sum(O1 < T1) - np.sum(Ok < T1)); sharp_u = sharp(T1, Tu, holes)
        U_cont = dT*dT/(2*T1u)
        W[(c, k)] = dict(k=k, m=m, holes=holes, Tw=Tw, Tu=Tu, T1=T1, T1u=T1u, s_below=s_below, s_zone=s_zone, s_ext=s_ext, S1one=S1one, sh=sh, lnN=lnN, c2=c2, dl=dl, U=U, gapc=gapc,
                         res_g3=res_g3, res_B=res_B, res_Bu=res_Bu, eps=eps, subs=subs, T_id=T_id, s_ss=s_ss, sh_ss=sh_ss, T_ss=T_ss, gm0=gm0, gm=gm, dT=dT,
                         lead_box=lead_box, lead_uc=lead_uc, lead_U=lead_U, lead_2m=lead_2m, Vinf=Vinf, T_log=T_log, Dk_c=Dk_c, Dk=L[k]["Dkappa"],
                         mom_zone=mom_zone, mom_ext=mom_ext, N_zone=N_zone, S_zone=S_zone, D_T1=D_T1, sharp_u=sharp_u, U_cont=U_cont)
ALL = list(W.values()); HM = [w for w in ALL if w["m"] >= 3]; ONE = [w for w in ALL if w["m"] == 1]; ZN = [w for w in ALL if w["N_zone"] > 0]
assert len(ALL) == 40 and len(HM) == 30 and len(ONE) == 5                                  # the forty safely deep rungs of Theorem 1bw; thirty with three or more holes

# ---------------------------------------------------------------- g1: the exterior reads the sharp wall
rB = [w["res_B"] for w in ALL]; rBu = [w["res_Bu"] for w in ALL]; s1one = [G1[c]["S1one"] for c in ORDER]
sub = [[w["subs"][i][0] for w in ALL] for i in range(3)]; subn = [[w["subs"][i][1] for w in ALL] for i in range(3)]
tl = [w["T_log"]/w["Tw"] for w in ALL]; tl_above = sum(1 for x in tl if x > 1); tl_sd = float(np.std(tl))
ok = abs(float(np.mean(rB))) <= 0.05 and rms(rB) <= 0.15 and max(abs(x) for x in rB) <= 0.35 and min(s1one) >= 0.95 and max(s1one) <= 0.99
ok &= rms(rBu) >= 1.2 and float(np.mean(rBu)) <= -0.7
ok &= -0.5 <= float(np.mean(sub[0])) <= -0.2 and 0.05 <= float(np.mean(sub[1])) <= 0.3 and 0.05 <= float(np.mean(sub[2])) <= 0.3 and min(min(x) for x in subn) >= 5
ok &= tl_above >= 36 and 1.005 <= float(np.mean(tl)) <= 1.025 and tl_sd <= 0.02 and min(tl) >= 0.98 and max(tl) <= 1.05
gate(f"g1 the exterior reads the sharp wall: the rung's exterior leakage beyond T_1 against the ground state's (the ground's own share beyond its edge S_1(1) = " + ", ".join(f"{x:.3f}" for x in s1one) + f" at the five cells, gated within [0.95, 0.99]) less 2 ln|ghat_k(0)/ghat_1(0)| minus cost(T_w): mean {float(np.mean(rB)):+.3f} (gated |.| <= 0.05), rms {rms(rB):.3f} (gated 0.15), largest {max(abs(x) for x in rB):.2f} (gated 0.35) at the 40 rungs; with T_u in place of T_w mean {float(np.mean(rBu)):+.2f} (gated <= -0.7), rms {rms(rBu):.2f} (gated >= 1.2); the envelope lift over the ground state's (the estimator ghat(gamma)^2 + ghat(mid)^2) minus B's constant by sub-window, [1, 1.25) T_1: mean {float(np.mean(sub[0])):+.3f} rms {rms(sub[0]):.3f} (gated mean in [-0.5, -0.2]); [1.25, 1.5) T_1: {float(np.mean(sub[1])):+.3f}, {rms(sub[1]):.3f} (gated [0.05, 0.3]); [1.5, 2) T_1: {float(np.mean(sub[2])):+.3f}, {rms(sub[2]):.3f} (gated [0.05, 0.3]); the windows hold {min(min(x) for x in subn)}-{max(max(x) for x in subn)} zeros (gated >= 5); the log-moment wall (cost(T) = 2 V(infinity), V(infinity) = 2[sum_(O_1) ln tau - sum_(O_k) ln tau - sum_h ln h] from the census sets): T_log > T_w at {tl_above} of 40 (gated >= 36), T_log/T_w mean {float(np.mean(tl)):.4f} (gated [1.005, 1.025]), standard deviation {tl_sd:.4f} (gated 0.02), range [{min(tl):.4f}, {max(tl):.4f}] (gated within [0.98, 1.05])", ok)

# ---------------------------------------------------------------- g2: the leakage budget (the identity) and T_w recovered from T_u, U and the measured share
lnN_max = max(abs(w["lnN"]) for w in ALL); eps = [w["eps"] for w in ALL]; r3 = [w["res_g3"] for w in ALL]
tid = [w["T_id"]/w["Tw"] for w in ALL]; tid_hm = [w["T_id"]/w["Tw"] for w in HM]
sext = [w["s_ext"] for w in ALL]; sone = [w["s_ext"] for w in ONE]; sbel = [w["s_below"] for w in ALL]; eone = [w["eps"] for w in ONE]; elo = [w["eps"] for w in ALL if w["m"] <= 2]
ok = lnN_max <= 1e-9 and abs(float(np.mean(eps))) <= 0.2 and rms(eps) <= 0.3 and max(abs(x) for x in eps) <= 0.7
ok &= min(r3) >= -0.2 and max(r3) <= 0.5 and max(abs(x) for x in eone) <= 0.2 and rms(elo) <= 0.15
ok &= abs(float(np.mean(tid)) - 1) <= 0.01 and rms1(tid) <= 0.02 and rms1(tid_hm) <= 0.012 and min(tid) >= 0.95 and max(tid) <= 1.04
ok &= min(sone) >= 0.9 and min(sext) >= 0.4 and max(sext) <= 0.95 and max(sbel) <= 0.12
gate(f"g2 the leakage budget cost(T_w) - cost(T_u) = U - ln(1/s_hat) at the 40 rungs (the norm ratio ln(N_1/N_k) within {lnN_max:.1e} of 0, gated 1e-9): the residual epsilon = r_2 - r_1 mean {float(np.mean(eps)):+.3f} (gated |.| <= 0.2), rms {rms(eps):.3f} (gated 0.3), largest {max(abs(x) for x in eps):.2f} (gated 0.7); Theorem 1by's reading at T_u, r_1 within [{min(r3):+.2f}, {max(r3):+.2f}] (gated within [-0.2, 0.5]; B's reading r_2 gated in g1); at the five one-hole rungs epsilon = " + ", ".join(f"{x:+.3f}" for x in eone) + f" (gated |.| <= 0.2), rms {rms(elo):.3f} over the ten rungs with one or two holes (gated 0.15); the exterior share {min(sext):.3f}-{max(sext):.3f} (gated within [0.4, 0.95]), {min(sone):.3f} and above at one hole (gated >= 0.9), the share below T_u at most {max(sbel):.3f} (gated 0.12); T_w recovered from T_u, U and the measured share: T_id/T_w mean {float(np.mean(tid)):.4f} (gated within 0.01 of 1), rms deviation {rms1(tid):.4f} (gated 0.02), range [{min(tid):.4f}, {max(tid):.4f}] (gated within [0.95, 1.04]); at the 30 rungs with three or more holes rms {rms1(tid_hm):.4f} (gated 0.012)", ok)

# ---------------------------------------------------------------- g3: the share's law (the ground state's profile attached at T_u) and T_w from the ground state alone
lss = [math.log(w["s_ss"]/w["s_ext"]) for w in ALL]; lss_hm = [math.log(w["s_ss"]/w["s_ext"]) for w in HM]
tss = [w["T_ss"]/w["Tw"] for w in ALL]; tss_hm = [w["T_ss"]/w["Tw"] for w in HM]; n_over = sum(1 for x in tss_hm if abs(x - 1) > 0.01)
WORST = min(((w["T_ss"]/w["Tw"] - 1), c, k) for (c, k), w in W.items()); TSS1 = [(c, k, w["T_ss"]/w["Tw"]) for (c, k), w in W.items() if w["m"] == 1]
ssone = [w["s_ss"] for w in ONE]; nz12 = [w["N_zone"] for w in ALL if w["m"] <= 2]
ok = abs(float(np.mean(lss))) <= 0.1 and rms(lss) <= 0.15 and min(lss) >= -0.4 and max(lss) <= 0.3 and rms(lss_hm) <= 0.13
ok &= abs(float(np.mean(tss_hm)) - 1) <= 0.005 and rms1(tss_hm) <= 0.012 and min(tss_hm) >= 0.965 and max(tss_hm) <= 1.035 and n_over <= 8
ok &= rms1(tss) <= 0.03 and WORST[1:] == ("d2.6", 2) and WORST[0] <= -0.09
ok &= min(ssone) <= 0.7 and max(ssone) >= 0.95 and max(nz12) <= 9 and len(nz12) == 10
gate(f"g3 the share's law s_ext = S_1(T_1/T_u) (the ground state's share beyond T_1/T_u times its edge): ln(S_1/s_ext) mean {float(np.mean(lss)):+.3f} (gated |.| <= 0.1), rms {rms(lss):.3f} (gated 0.15), range [{min(lss):+.3f}, {max(lss):+.3f}] (gated within [-0.4, 0.3]) at the 40 rungs, rms {rms(lss_hm):.3f} at the 30 with three or more holes (gated 0.13); T_w from the ground state alone (T_u, U, S_1): T_ss/T_w at the 30 rungs with three or more holes mean {float(np.mean(tss_hm)):.4f} (gated within 0.005 of 1), rms deviation {rms1(tss_hm):.4f} (gated 0.012), range [{min(tss_hm):.4f}, {max(tss_hm):.4f}] (gated within [0.965, 1.035]), beyond one percent at {n_over} of the 30 (gated <= 8); at all 40 rms {rms1(tss):.4f} (gated 0.03), the worst {WORST[1]} rung {WORST[2]} at {100*WORST[0]:+.1f}% (gated delta = 2.6 rung 2, <= -9%); the one-hole rungs: " + ", ".join(f"{c} {x:.3f}" for c, k, x in TSS1) + f"; at one hole S_1(T_1/T_u) runs {min(ssone):.3f}-{max(ssone):.3f} (gated min <= 0.7, max >= 0.95) against the shares {min(sone):.3f}-{max(sone):.3f}, the zone at one or two holes {min(nz12)}-{max(nz12)} zeros wide over {len(nz12)} rungs (gated <= 9; 10)", ok)

# ---------------------------------------------------------------- g4: the leading law -- the geometric mean reduced by the share, and the law's forms
g0r = [w["gm0"]/w["Tw"] for w in ALL]; gr = [w["gm"]/w["Tw"] for w in ALL]; gr_hm = [w["gm"]/w["Tw"] for w in HM]
uc_hm = [w["U"]/w["U_cont"] for w in HM if w["U_cont"] > 0]; uc_lo = [w["U"]/w["U_cont"] for w in ALL if w["m"] <= 2 and w["U_cont"] > 0]
lb = [w["lead_box"] for w in ALL]; lu = [w["lead_U"] for w in ALL]; lc = [w["lead_uc"] for w in ALL]; l2 = [w["lead_2m"] for w in ALL]; dt4 = [w["dT"]/(4*w["m"]) for w in HM]
ok = 1.01 <= float(np.mean(g0r)) <= 1.025 and rms1(g0r) <= 0.03 and abs(float(np.mean(gr)) - 1) <= 0.01 and rms1(gr) <= 0.02 and rms1(gr_hm) <= 0.012
ok &= abs(float(np.mean(gr)) - 1) < abs(float(np.mean(g0r)) - 1) and rms1(gr) < rms1(g0r)
ok &= 0.2 <= min(uc_hm) and max(uc_hm) <= 1.35 and len(uc_hm) == 30 and len(uc_lo) == 7
ok &= rms(lb) <= 0.025 and rms(lu) <= 0.02 and rms(lc) <= 0.03 and rms(l2) <= 0.035 and rms(lu) < rms(lb) < rms(lc) < rms(l2) and 0.7 <= min(dt4) and max(dt4) <= 1.9
gate(f"g4 the leading law ln(T_w/T_u) = dT/(2 T_1u) - ln(1/s_hat)/(4m), dT = T_1u - T_u: sqrt(T_u T_1u)/T_w mean {float(np.mean(g0r)):.4f} (gated [1.01, 1.025]), rms deviation {rms1(g0r):.4f} (gated 0.03); reduced by the share, s_hat^(1/4m) sqrt(T_u T_1u)/T_w mean {float(np.mean(gr)):.4f} (gated within 0.01 of 1), rms {rms1(gr):.4f} (gated 0.02; the reduction lowering both the mean's distance from 1 and the rms, gated), {rms1(gr_hm):.4f} at the 30 rungs with three or more holes (gated 0.012); the law's residual in ln T: {rms(lb):.4f} rms in the boxed form (gated 0.025), {rms(lu):.4f} with the exact U in place of dT^2/(2 T_1u) (gated 0.02), {rms(lc):.4f} with U_c = dT^2/(2 T_1u) (gated 0.03), {rms(l2):.4f} with dT = 4m throughout (gated 0.035), in that order (gated); dT/(4m) runs {min(dt4):.2f}-{max(dt4):.2f} at the 30 rungs with three or more holes (gated within [0.7, 1.9]); the unlocking cost against its continuum form U_c: U/U_c mean {float(np.mean(uc_hm)):.3f}, range [{min(uc_hm):.3f}, {max(uc_hm):.3f}] at the rungs with three or more holes and [{min(uc_lo):.3f}, {max(uc_lo):.3f}] at those with one or two and a wall below T_1u (gated within [0.2, 1.35] at the 30 with three or more holes; 7 at one or two)", ok)

# ---------------------------------------------------------------- g5: the zone's anatomy
s2 = [w["S_zone"]/w["N_zone"] for w in ZN]; n_zn = len(ZN); s2_pool = float(sum(w["S_zone"] for w in ZN))/float(sum(w["N_zone"] for w in ZN)); n_zone_tot = int(sum(w["N_zone"] for w in ZN))
below = sum(1 for w in HM if w["D_T1"] < w["sharp_u"]); lag = [w["sharp_u"] - w["D_T1"] for w in HM]; shu = [w["sharp_u"] for w in HM]; dt1 = [w["D_T1"] for w in HM]
mz = [w["mom_zone"] for w in ALL]; me = [w["mom_ext"] for w in ALL]; dkr = max(abs(w["Dk_c"]/w["Dk"] - 1) for w in ALL)
ok = n_zn == 39 and 0.40 <= float(np.mean(s2)) <= 0.60 and float(np.std(s2)) <= 0.2 and min(s2) >= 0.15 and max(s2) <= 0.9 and 0.40 <= s2_pool <= 0.55 and n_zone_tot >= 500
ok &= below == 30 and 0.6 <= float(np.mean(lag)) <= 1.2 and 0.4 <= min(shu) and max(shu) <= 4.5 and min(dt1) == 0 and max(dt1) == 3
ok &= max(mz) <= 0.19 and min(me) >= 0.81 and dkr <= 1e-6
gate(f"g5 the zone's anatomy: sin^2(pi d) = ghat(gamma)^2/A(gamma)^2 averages {s2_pool:.3f} over the {n_zone_tot} zeta zeros of the zones (gated [0.40, 0.55]; >= 500) and {float(np.mean(s2)):.3f} as the mean of the {n_zn} rungs' means (gated [0.40, 0.60]; 39 rungs with a zone) with standard deviation {float(np.std(s2)):.3f} (gated <= 0.2), range [{min(s2):.2f}, {max(s2):.2f}] (gated within [0.15, 0.9]); the observed deficit at T_1 lies below the sharp profile at T_u at {below} of the 30 rungs with three or more holes (gated 30), by {float(np.mean(lag)):.2f} zeros on average (gated [0.6, 1.2]), range [{min(lag):.2f}, {max(lag):.2f}]; the profile's count at T_1 runs {min(shu):.2f}-{max(shu):.2f} (gated within [0.4, 4.5]) against the observed {min(dt1)}-{max(dt1)} (gated 0-3); the zone [T_u, T_1) carries at most {max(mz):.3f} of -Delta kappa_k (gated 0.19) and the exterior beyond T_1 at least {min(me):.3f} (gated 0.81); Delta kappa_k from the census sets against rung_laws' within {dkr:.1e} (gated 1e-6: Theorem 1bx(i))", ok)

# ---------------------------------------------------------------- g6
import paper_needles
S_PRO = 'the polished eigenvalues equal the census’s within 10⁻⁸ at all 54 states of the five cells, the pencil residuals lie below 10⁻¹⁵⁰, and the 6700-zero list carries 96.1–99.7% of every state’s leakage'
S_EXT = 'ln(λ_k s_ext/(λ₁S₁(1))) − 2 ln|ĝ_k(0)/ĝ₁(0)| equals 4Σ_h ln(1/σ_h(T_w)) within +0.01 ± 0.11 nats (mean, rms; 0.30 at most) at the 40 rungs, against −1.09 ± 1.72 with T_u in place of T_w'
S_LIFT = 'the envelope lift over the ground state’s minus that constant runs −0.34 ± 0.48 nats on [T₁, 1.25T₁), +0.16 ± 0.32 on [1.25T₁, 1.5T₁) and +0.18 ± 0.26 on [1.5T₁, 2T₁) (means and rms over the 40 rungs)'
S_LOG = 'the log-moment wall lies above T_w at 38 of the 40 rungs, by 1.5% on average with a scatter of 0.012 about that offset (T_log/T_w over [0.987, 1.040])'
S_ID = 'cost(T_w) − cost(T_u) = U − ln(1/ŝ) within a residual of mean −0.12 and rms 0.23 nats over [−0.61, +0.22] at the 40 rungs (the two readings’ residuals within [−0.16, +0.43] and ±0.30 nats; the norm ratio 1)'
S_TID = 'T_w recovered from T_u, U and the measured share within 1.2% rms at the 40 rungs and 0.9% at the 30 with three or more holes (T_id/T_w over [0.968, 1.031])'
S_SS = 'ln(S₁(T₁/T_u)/s_ext) averages −0.06 with rms 0.11 over [−0.31, +0.15] at the 40 rungs (rms 0.10 at the 30 with three or more holes)'
S_TSS = 'T_w from the ground state alone lies within 0.9% rms of 1bx’s at the 30 rungs with three or more holes (T_ss/T_w averages 1.0026 over [0.978, 1.025], beyond one percent at 6 of the 30) and within 2.1% rms at all 40, the worst δ = 2.6’s rung 2 at −10.4%'
S_ONE = 'at one hole the exterior share is 0.92–0.94 where S₁(T₁/T_u) runs 0.67–0.97, the zone at one or two holes 0–9 zeros wide'
S_EPS1 = 'at the five one-hole rungs the residual is +0.09, +0.01, +0.13, +0.04, −0.12 nats, over four hole slopes 0.2–3.2% in the wall against one-hole gaps of −1.7% to +5.8%'
S_GM = '√(T_uT_u(1))/T_w averages 1.016 with rms deviation from 1 of 0.023; reduced by the share, ŝ^{1/(4m)}√(T_uT_u(1))/T_w averages 1.000 with 0.016 (0.011 at the 30 rungs with three or more holes)'
S_LAW = 'the law’s residual in ln T is 0.017 rms in the boxed form, 0.013 with the exact U in place of ΔT²/(2T_u(1)), 0.023 with U_c and 0.025 with ΔT = 4m throughout, over the 40 rungs; ΔT/(4m) runs 0.79–1.78 at the 30 rungs with three or more holes'
S_UC = 'U/U_c averages 0.93 over [0.24, 1.21] at the 30 rungs with three or more holes, and runs 0.24–1.64 at the 7 with one or two holes and a wall below the ground state’s minimiser'
S_ZONE = 'sin²(πd) averages 0.46 over the 537 zeta zeros of the zones (0.48 as the mean of the 39 rungs’ means, standard deviation 0.14); the observed deficit at T₁ lies below the sharp profile at T_u at all 30 rungs with three or more holes, by 0.88 zeros on average, the profile’s count there 0.48–4.39 zeros and the observed 0–3'
S_MOM = 'the zone [T_u, T₁) carries at most 18% of −Δκ_k and the exterior beyond T₁ at least 82%'
# each call carries its literal (the precheck's clause D); the strings equal the S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, 'the polished eigenvalues equal the census’s within 10⁻⁸ at all 54 states of the five cells, the pencil residuals lie below 10⁻¹⁵⁰, and the 6700-zero list carries 96.1–99.7% of every state’s leakage', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'ln(λ_k s_ext/(λ₁S₁(1))) − 2 ln|ĝ_k(0)/ĝ₁(0)| equals 4Σ_h ln(1/σ_h(T_w)) within +0.01 ± 0.11 nats (mean, rms; 0.30 at most) at the 40 rungs, against −1.09 ± 1.72 with T_u in place of T_w', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the envelope lift over the ground state’s minus that constant runs −0.34 ± 0.48 nats on [T₁, 1.25T₁), +0.16 ± 0.32 on [1.25T₁, 1.5T₁) and +0.18 ± 0.26 on [1.5T₁, 2T₁) (means and rms over the 40 rungs)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the log-moment wall lies above T_w at 38 of the 40 rungs, by 1.5% on average with a scatter of 0.012 about that offset (T_log/T_w over [0.987, 1.040])', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'cost(T_w) − cost(T_u) = U − ln(1/ŝ) within a residual of mean −0.12 and rms 0.23 nats over [−0.61, +0.22] at the 40 rungs (the two readings’ residuals within [−0.16, +0.43] and ±0.30 nats; the norm ratio 1)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'T_w recovered from T_u, U and the measured share within 1.2% rms at the 40 rungs and 0.9% at the 30 with three or more holes (T_id/T_w over [0.968, 1.031])', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'ln(S₁(T₁/T_u)/s_ext) averages −0.06 with rms 0.11 over [−0.31, +0.15] at the 40 rungs (rms 0.10 at the 30 with three or more holes)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'T_w from the ground state alone lies within 0.9% rms of 1bx’s at the 30 rungs with three or more holes (T_ss/T_w averages 1.0026 over [0.978, 1.025], beyond one percent at 6 of the 30) and within 2.1% rms at all 40, the worst δ = 2.6’s rung 2 at −10.4%', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'at one hole the exterior share is 0.92–0.94 where S₁(T₁/T_u) runs 0.67–0.97, the zone at one or two holes 0–9 zeros wide', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'at the five one-hole rungs the residual is +0.09, +0.01, +0.13, +0.04, −0.12 nats, over four hole slopes 0.2–3.2% in the wall against one-hole gaps of −1.7% to +5.8%', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '√(T_uT_u(1))/T_w averages 1.016 with rms deviation from 1 of 0.023; reduced by the share, ŝ^{1/(4m)}√(T_uT_u(1))/T_w averages 1.000 with 0.016 (0.011 at the 30 rungs with three or more holes)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the law’s residual in ln T is 0.017 rms in the boxed form, 0.013 with the exact U in place of ΔT²/(2T_u(1)), 0.023 with U_c and 0.025 with ΔT = 4m throughout, over the 40 rungs; ΔT/(4m) runs 0.79–1.78 at the 30 rungs with three or more holes', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'U/U_c averages 0.93 over [0.24, 1.21] at the 30 rungs with three or more holes, and runs 0.24–1.64 at the 7 with one or two holes and a wall below the ground state’s minimiser', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'sin²(πd) averages 0.46 over the 537 zeta zeros of the zones (0.48 as the mean of the 39 rungs’ means, standard deviation 0.14); the observed deficit at T₁ lies below the sharp profile at T_u at all 30 rungs with three or more holes, by 0.88 zeros on average, the profile’s count there 0.48–4.39 zeros and the observed 0–3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the zone [T_u, T₁) carries at most 18% of −Δκ_k and the exterior beyond T₁ at least 82%', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g6'] == [S_PRO, S_EXT, S_LIFT, S_LOG, S_ID, S_TID, S_SS, S_TSS, S_ONE, S_EPS1, S_GM, S_LAW, S_UC, S_ZONE, S_MOM]
_re = __import__("re")
def _num(s): return float(s.strip().replace('−', '-'))
def _nums(s, pat=r"([-−+]?[0-9]+\.[0-9]+)"): return [_num(x) for x in _re.findall(pat, s)]
def _ints(s): return [int(x) for x in _re.findall(r"(?<![0-9.−-])[0-9]+(?![0-9.])", s)]
_mx = lambda v: round(max(abs(x) for x in v), 2)
ok &= _ints(S_PRO.split("at all ")[1].split(" states")[0]) == [n_pro] and _nums(S_PRO.split("carries ")[1]) == [round(100*cap_lo, 1), round(100*cap_hi, 1)]
ok &= _nums(S_EXT.split("within ")[1].split(" nats (mean")[0]) == [round(float(np.mean(rB)), 2), round(rms(rB), 2)] and _nums(S_EXT.split("rms; ")[1].split(" at most")[0]) == [_mx(rB)] and _nums(S_EXT.split("against ")[1].split(" with T_u")[0]) == [round(float(np.mean(rBu)), 2), round(rms(rBu), 2)] and _ints(S_EXT.split("at the ")[1].split(" rungs")[0]) == [len(ALL)]
ok &= _nums(S_LIFT.split("runs ")[1].split(" nats on")[0]) == [round(float(np.mean(sub[0])), 2), round(rms(sub[0]), 2)] and _nums(S_LIFT.split("[T₁, 1.25T₁), ")[1].split(" on [1.25T₁")[0]) == [round(float(np.mean(sub[1])), 2), round(rms(sub[1]), 2)] and _nums(S_LIFT.split("1.5T₁) and ")[1].split(" on [1.5T₁")[0]) == [round(float(np.mean(sub[2])), 2), round(rms(sub[2]), 2)]
ok &= _ints(S_LOG.split("above T_w at ")[1].split(" of the")[0]) == [tl_above] and _nums(S_LOG.split("by ")[1].split("%")[0]) == [round(100*(float(np.mean(tl)) - 1), 1)] and _nums(S_LOG.split("scatter of ")[1].split(" about")[0]) == [round(tl_sd, 3)] and _nums(S_LOG.split("over ")[1]) == [round(min(tl), 3), round(max(tl), 3)]
ok &= _nums(S_ID.split("of mean ")[1].split(" at the")[0]) == [round(float(np.mean(eps)), 2), round(rms(eps), 2), round(min(eps), 2), round(max(eps), 2)] and _ints(S_ID.split("at the ")[1].split(" rungs")[0]) == [len(ALL)]
ok &= _nums(S_ID.split("residuals within ")[1].split(" nats")[0]) == [round(min(r3), 2), round(max(r3), 2), _mx(rB)]
ok &= _nums(S_TID.split("within ")[1].split(" (T_id")[0]) == [round(100*rms1(tid), 1), round(100*rms1(tid_hm), 1)] and _ints(S_TID.split("within ")[1].split(" (T_id")[0]) == [len(ALL), len(HM)] and _nums(S_TID.split("over ")[1]) == [round(min(tid), 3), round(max(tid), 3)]
ok &= _nums(S_SS.split("averages ")[1].split(" at the 40")[0]) == [round(float(np.mean(lss)), 2), round(rms(lss), 2), round(min(lss), 2), round(max(lss), 2)] and _nums(S_SS.split("(rms ")[1].split(" at")[0]) == [round(rms(lss_hm), 2)] and _ints(S_SS.split("(rms ")[1]) == [len(HM)]
ok &= _nums(S_TSS.split("within ")[1].split("% rms")[0]) == [round(100*rms1(tss_hm), 1)] and _nums(S_TSS.split("averages ")[1].split("]")[0]) == [round(float(np.mean(tss_hm)), 4), round(min(tss_hm), 3), round(max(tss_hm), 3)] and _ints(S_TSS.split("beyond one percent at ")[1].split(" of the")[0]) == [n_over]
ok &= _nums(S_TSS.split("and within ")[1].split("%")[0]) == [round(100*rms1(tss), 1)] and _nums(S_TSS.split("rung 2 at ")[1].split("%")[0]) == [round(100*WORST[0], 1)] and _ints(S_TSS.split("at the ")[1].split(" rungs")[0]) == [len(HM)]
ok &= _nums(S_ONE.split("share is ")[1].split(" where")[0]) == [round(min(sone), 2), round(max(sone), 2)] and _nums(S_ONE.split("runs ")[1].split(",")[0]) == [round(min(ssone), 2), round(max(ssone), 2)] and _ints(S_ONE.split("holes ")[1].split(" zeros")[0]) == [min(nz12), max(nz12)]
ok &= _nums(S_EPS1.split("residual is ")[1].split(" nats")[0]) == [round(x, 2) for x in eone] and _nums(S_EPS1.split("slopes ")[1].split("%")[0]) == [round(100*min(abs(x)/4 for x in eone), 1), round(100*max(abs(x)/4 for x in eone), 1)]
_p = S_GM.split("/T_w averages "); ok &= len(_p) == 3 and _nums(_p[1].split(";")[0]) == [round(float(np.mean(g0r)), 3), round(rms1(g0r), 3)] and _nums(_p[2]) == [round(float(np.mean(gr)), 3), round(rms1(gr), 3), round(rms1(gr_hm), 3)] and _ints(_p[2].split(" (")[-1]) == [len(HM)]
ok &= _nums(S_LAW.split("ln T is ")[1].split(" over the")[0]) == [round(rms(lb), 3), round(rms(lu), 3), round(rms(lc), 3), round(rms(l2), 3)] and _nums(S_LAW.split("runs ")[1].split(" at the")[0]) == [round(min(dt4), 2), round(max(dt4), 2)] and _ints(S_LAW.split("runs ")[1]) == [len(HM)]
ok &= _nums(S_UC.split("averages ")[1].split(" at the")[0]) == [round(float(np.mean(uc_hm)), 2), round(min(uc_hm), 2), round(max(uc_hm), 2)] and _ints(S_UC.split("at the ")[1].split(" rungs")[0]) == [len(uc_hm)]
ok &= _nums(S_UC.split("runs ")[1].split(" at the")[0]) == [round(min(uc_lo), 2), round(max(uc_lo), 2)] and _ints(S_UC.split("runs ")[1].split(" with one")[0]) == [len(uc_lo)]
ok &= _nums(S_ZONE.split("averages ")[1].split(" over the")[0]) == [round(s2_pool, 2)] and _ints(S_ZONE.split("over the ")[1].split(" zeta")[0]) == [n_zone_tot] and _nums(S_ZONE.split("zones (")[1].split(" as the mean")[0]) == [round(float(np.mean(s2)), 2)] and _ints(S_ZONE.split("mean of the ")[1].split(" rungs")[0]) == [n_zn] and _nums(S_ZONE.split("deviation ")[1].split(")")[0]) == [round(float(np.std(s2)), 2)]
ok &= _ints(S_ZONE.split("at all ")[1].split(" rungs")[0]) == [below] and _nums(S_ZONE.split("by ")[1].split(" zeros on")[0]) == [round(float(np.mean(lag)), 2)] and _nums(S_ZONE.split("count there ")[1].split(" zeros and")[0]) == [round(min(shu), 2), round(max(shu), 2)] and _ints(S_ZONE.split("the observed ")[-1]) == [min(dt1), max(dt1)]
ok &= _ints(S_MOM.split("at most ")[1].split("%")[0]) == [math.ceil(100*max(mz))] and _ints(S_MOM.split("at least ")[1].split("%")[0]) == [math.floor(100*min(me))]
gate("g6 the paper's numbers parsed back from the declared needles", ok)

# ---------------------------------------------------------------- g7
from cascade_tower import chain_ok
gate("g7 the chain obligation to cascade_wall_law.py (Theorem 1by) met", chain_ok("cascade_wall_law.py"))

# ---------------------------------------------------------------- g8
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g8 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g8 the 1bz paper needles and the footer census (declared surface)", ok)

print(("ALL GATES PASS (9/9)" if not fails else f"FAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
