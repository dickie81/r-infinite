#!/usr/bin/env python3
"""Theorem 1bu -- the ladder's caster: the excited states of the true form carry
their extra zeros in the zero-free interval below the first zeta zero, at the
nodes of the orthogonal polynomials of the ground state's power spectrum; the
ground state's transform converges to Riemann's Xi function; a zero pair at
fixed height costs four prolate orders in Fuchs' law, which is why the shadow's
rungs are the orders 4k. Substrates ladder_caster.py (keyed producer, seven
cells), xi_limit.py (the Xi side, imported), zeta_zeros_precise.py (the 800
zeros to 100 digits, data). Tower member 30 (top).

THE CLAIMS GATED. (0) THE PAIR-COST LEMMA as computation: 4 arccosh(T/tau) =
4 ln(2T/tau) - tau^2/T^2 + O(tau^4/T^4) (the remainder below 1e-6 at T = 200,
tau <= 3); at the edge T = 2 T_0 a pair at fixed tau costs 4 ln T_0 + 4 ln(4/tau)
+ O(T_0^-2) and a pair at x sqrt(T_0) costs 2 ln T_0 + O(1) (the ratios to ln T_0
at T_0 = 10^6: within 0.02 of 4 and 2 after the constants). (1) THE XI SIDE:
Hadamard's product Xi(t)/Xi(0) = prod (1 - t^2/gamma^2) against the 800 zeros
plus the density tail at t = 3, 8, 13 (within 1e-4); Xi(0) = 0.49712; the limit
constants 2 pi Xi(0)^2/int Xi^2 = 0.7729 and sqrt<t^2> = 3.195 (nearest 1e-4);
K = 2 + gamma_E - ln 4 pi. (2) THE LIMIT SHAPE AT THE CELLS: Hypothesis D by
the producer's real-zero census (round 321 F4/F9) -- the K - 1 designed zero
pairs of the ground state's transform located on the real line at every
cell with the sum rule kappa = sum tau^-2 closing within 1e-16, or K - 2
located and the one unlocated pair placed beyond the region by the sum
rule; the located zeros below the edge matching the zeta zeros below it
one to one (no zero double: at the six complete cells every designed root a
simple sign change; at delta = 3.5 the located roots simple and the one
unlocated root, being single, simple too -- the entry counts being sign-change
counts because no dip was appended, gated as that precondition) -- with the
first zeta zero the ground state misses and its
first free zero within 0.2 of each other and at >= 1.4 T_0; D WITHIN THE DODGING
TOLERANCE (round 322 F322-1): the dodging zeros' displacements below the edge
stated per cell, the low half within 3e-14 at delta >= 2 (the resolution of
the double list and of the bisection), their contribution to the bound at r = 3 below 1e-4; epsilon(delta) =
sum_{|tau| >= T_D} tau^-2 + sum_{gamma >= T_D} gamma^-2 from the located zeros
(the zeta tail beyond the 800 by the density) falling across the cells, between 0.18 and 0.24 of ln T_D/T_D (the
rate is not proved: round 321 F5); the exterior mass beyond T_D/2 and T_D at
most 1e-3 and 1e-5 of the whole (F6); the curvature sum 1/tau^2 rising across
the cells and below sum gamma^-2 = -Xi''(0)/(2 Xi(0)) = 0.023105 (not K/2 =
0.023096: F3); ghat_1(0)^2 rising and below 0.7729; sqrt<r^2> falling and above
3.195. (3) THE HOLE ZEROS: at every safely deep rung up to rung 12 (its OWN
leakage ln(1 - chi_{2k}) < -20, order 4k = index 2k of the even list -- F1;
Theorem 1br's threshold) the transform of rung k has exactly k - 1 hole zeros
(the sign changes below min(100, 0.8 x the rung's dodging edge) left after one
dodging zero per zeta zero is removed -- zeros of odd multiplicity, a sign change
each; a double zero, giving no sign change, would escape the census) and the
census region covers the predicted nodes (the weight for the nodes now evaluated in balls: F10);
the ground state has none by the census of (2); the first three hole zeros of
every safely deep rung lie below the first zeta zero, rungs 6-7 have four and
rungs 8-12 four or five below it at delta >= 2.6, nondecreasing in k (F8; the
Xi-limit nodes: four for rungs 5-7, five for 8-11, six for 12); at delta >= 2
the hole zeros of rungs 2-4 sit within 1% of the nodes of P_{2(k-1)} for the
weight ghat_1^2; the first hole zero falls across the cells and stays above the
Xi-limit 3.195.
(4) THE k-LEVEL FORMULA: c_1 within 0.15 of 1bm(v)'s c(delta) at every cell;
c_k for the safely deep rungs (through rung 12) within [c_1 - 3, c_1 + 0.3];
at the cells with >= 8 such rungs the successive differences of c_k from rung 2
change sign at least twice (not monotone); THE PARITY (round 321 F2, round 322
F322-2, round 323 F323-1/7): the offsets o_k = ln lambda_k - ln(1 - chi_{2k})
of Theorem 1br(ii) split as c_k + d_k with d_k = F_k - ln(1 - chi_{2k}); at the
three balanced cells (delta = 2.6, 3.0, 3.5: the two parities' mean ranks equal,
the rungs per parity, even/odd, stated and parsed back) the even-minus-odd means of o_k and of d_k are
positive, o_k's at delta = 3.0 within 0.02 of 1br(ii)'s +0.22, d_k's at 3.5
within one standard error of zero, c_k's mean changes sign across the cells by
more than two standard errors; the standard errors (residuals about a linear
trend in k) between 0.05 and 0.25: the formula's part reproduces the parity's
sign, the magnitude is shared. (5) THE ANATOMY of c(delta): the identity
c_1 = origin + peak excess + count + far tail (1e-9); the origin rising toward
ln 0.7729; the share of Q beyond 3 T_0, the far tail included (F7), at least
0.39 at delta >= 2. (6) mangle
probes: a pair cost of 2 ln T_0 per rung misses the ladder; the Gaussian
model's first node 1/sqrt(2K) = 3.290 is not the Xi-limit's 3.195 and the cells
at delta >= 3 sit below the Gaussian value; (7) the paper's numbers parsed
back; (8) the chain obligation to cascade_pole_indefinite.py; (9) the needles
and census.

WHAT IS NOT CLAIMED. The orthogonal-polynomial structure of the excited states
is computed, not proved; the rate of epsilon(delta) is not proved; the residual
c_k's law and the parity's law are not modelled; the constants of the offsets
against the prolate ladder are not derived; no Riemann Hypothesis consequence.
"""
import math, os, sys, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ladder_caster import run as run_LC, CELLS
import xi_limit as XI

PAPER_NEEDLES = [
    {'g': 'g9', 's': "Theorem 1bu (the ladder's caster", 'form': 'plain'},
    {'g': 'g9', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 12},
    {'s': '`cascade_ladder_caster.py`', 'min': 2, 'g': 'g9'},
    {'s': 'the **97 scripts cited in place** above', 'form': 'ws', 'g': 'g9'},
    {'s': 'extended by Theorems 1i–1bu:', 'form': 'ws', 'g': 'g9'},
    {'g': 'g7', 's': 'the first missed zero at 1.46, 1.63, 1.79, 1.77, 1.86, 1.90, 1.94 T₀', 'form': 'ws'},
    {'g': 'g7', 's': 'the curvature 0.0148, 0.0177, 0.0203, 0.0210, 0.0216, 0.0221, 0.0225 rising toward Σ_γ γ⁻² = 0.0231', 'form': 'ws'},
    {'g': 'g7', 's': 'Σ_γ γ⁻² = −Ξ″(0)/(2Ξ(0)) = 0.023105, within 10⁻⁵ of K/2 = 0.023096', 'form': 'ws'},
    {'g': 'g7', 's': 'ε = 0.02336, 0.01765, 0.01115, 0.00920, 0.00707, 0.00518, 0.00348 at the cells, between 0.18 and 0.24 of ln T_D/T_D', 'form': 'ws'},
    {'g': 'g7', 's': 'displaced from the zeta zeros by at most 0.033, 0.024, 0.025, 0.004, 0.028, 0.036, 0.043', 'form': 'ws'},
    {'g': 'g7', 's': 'K − 2 of them at δ = 3.5 (K = 540: 538 of the 539 designed roots), where one root of M is unlocated — real, since M has real coefficients and a complex root would bring its conjugate — and the sum rule places it beyond the region: |τ| = 14501, real by the residual’s sign, against the region 7741', 'form': 'ws'},
    {'g': 'g7', 's': 'the residual there, 4.8 × 10⁻⁹, against a closure below 10⁻¹⁶ at the six complete cells', 'form': 'ws'},
    {'g': 'g7', 's': 'ĝ₁(0)² = 0.630, 0.683, 0.727, 0.740, 0.749, 0.757, 0.763 rising toward 0.7729', 'form': 'ws'},
    {'g': 'g7', 's': '√⟨r²⟩ = 3.86, 3.58, 3.38, 3.33, 3.29, 3.26, 3.23 falling toward 3.19', 'form': 'ws'},
    {'g': 'g7', 's': 'at δ = 2.3 rung 2 at 3.329 against the node 3.328, rung 3 at 2.413, 7.374 against 2.410, 7.366, rung 4 at 2.011, 6.061, 10.221 against 2.005, 6.045, 10.193', 'form': 'ws'},
    {'g': 'g7', 's': 'the first hole zero 3.917, 3.594, 3.383, 3.329, 3.292, 3.258, 3.233 falls toward the Ξ-limit 3.195', 'form': 'ws'},
    {'g': 'g7', 's': 'the Ξ-limit nodes 3.195; 2.321, 7.124; 1.908, 5.759, 9.730; 1.725, 5.200, 8.781, 13.670', 'form': 'ws'},
    {'g': 'g7', 's': 'c_k = 6.45, 5.80, 5.60, 5.01, 4.88, 4.26, 4.37 over rungs 1–7 at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'origin −0.46, −0.38, −0.32, −0.30, −0.29, −0.28, −0.27; peak excess 3.86, 4.02, 4.31, 4.48, 4.73, 4.56, 4.83; count 1.30, 1.59, 2.06, 2.28, 2.25, 3.07, 3.27', 'form': 'ws'},
    {'g': 'g7', 's': 'Ξ(0) = 0.49712, ∫Ξ² = 2.00906, 2πΞ(0)²/∫Ξ² = 0.7729', 'form': 'ws'},
    {'g': 'g7', 's': 'the exterior weight in units of the balayage level 5.16, 5.60, 6.36, 6.76, 6.99, 7.63, 8.10', 'form': 'ws'},
    {'g': 'g7', 's': 'slopes against ln T₀ over the cells 0.07 (the origin) and 1.19 (the exterior weight), summing to the slope of c, 1.26', 'form': 'ws'},
    {'g': 'g7', 's': '0.42, 0.40, 0.43, 0.44, 0.48 of Q beyond 3T₀ at δ ≥ 2, the far tail beyond γ₈₀₀ included', 'form': 'ws'},
    {'g': 'g7', 's': 'from 2.02 T₀ to 1.81 T₀ over the first nine rungs at δ = 3.5', 'form': 'ws'},
    {'g': 'g7', 's': 'the steps 16.50, 14.72, 13.23, 11.77, 11.19, 9.61, 8.70, 7.42 from rung 1 to rung 9 at δ = 2.3 against 4 ln T₀ = 16.55', 'form': 'ws'},
    {'g': 'g7', 's': 'change sign 4, 5, 3 times at δ = 2.6, 3.0, 3.5', 'form': 'ws'},
    {'g': 'g7', 's': 'even minus odd means of the offsets o_k +0.08, +0.21, +0.16 and of d_k +0.39, +0.24, +0.06 at δ = 2.6, 3.0, 3.5', 'form': 'ws'},
    {'g': 'g7', 's': 'against the residual c_k −0.31, −0.03, +0.11', 'form': 'ws'},
    {'g': 'g7', 's': 'the means’ standard errors, from the residuals about a linear trend in k, 0.08–0.18', 'form': 'ws'},
    {'g': 'g7', 's': 'rungs per parity (even/odd) 5/4, 6/5, 6/5', 'form': 'ws'},
    {'g': 'g7', 's': '0, 0, 3, 6, 9, 11, 11 rungs at the cells', 'form': 'ws'},
    {'g': 'g7', 's': '3.233; 2.346, 7.193; 1.935, 5.836, 9.849; 1.748, 5.269, 8.894, 14.103 against the nodes 3.233; 2.346, 7.193; 1.934, 5.835, 9.847; 1.748, 5.268, 8.892, 14.095', 'form': 'ws'},
    {'g': 'g7', 's': '15.239, 14.797, 14.402, 14.103 at δ = 2.3, 2.6, 3.0, 3.5', 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ORDER = ["d1.0", "d1.38", "d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
ST = {c: run_LC(c) for c in ORDER}
T0 = {c: ST[c]["T0"] for c in ORDER}
SAFE = -20.0                                  # the safely deep rungs: the rung's OWN leakage ln(1 - chi_{2k}) < -20 (Theorem 1br's threshold; order 4k = index 2k of the even list -- round 321 F1)
def safe_rungs(c):
    st = ST[c]; pro = st["prolate_ln_leakage"]
    return [r for r in st["rungs"][1:] if 2*r["k"] < len(pro) and pro[2*r["k"]] is not None and pro[2*r["k"]] < SAFE and r["k"] <= 12]

# ---------------------------------------------------------------- g0
ok = True; worst = 0.0
for T in (200.0, 1000.0):
    for tau in (1.0, 3.0):
        rem = 4*math.acosh(T/tau) - (4*math.log(2*T/tau) - tau*tau/(T*T)); worst = max(worst, abs(rem)); ok &= abs(rem) <= 4*(tau/T)**4
T0big = 1e6; tau = 3.0
fixed = 4*math.acosh(2*T0big/tau) - 4*math.log(4/tau); hermite = 4*math.acosh(2*T0big/(0.7*math.sqrt(T0big)))
ok &= abs(fixed/math.log(T0big) - 4) <= 0.02 and abs((hermite - 4*math.log(4/0.7))/math.log(T0big) - 2) <= 0.02
gate(f"g0 the pair-cost lemma as computation: 4 arccosh(T/tau) - 4 ln(2T/tau) + tau^2/T^2 within 4 (tau/T)^4 at T = 200, 1000 and tau = 1, 3 (max |rem| {worst:.1e}); at T_0 = 1e6 a pair at fixed tau = 3 costs {fixed/math.log(T0big):.4f} ln T_0 after its constant, a pair at 0.7 sqrt(T_0) costs {(hermite - 4*math.log(4/0.7))/math.log(T0big):.4f} ln T_0: four orders against two", ok)

# ---------------------------------------------------------------- g1
Z40 = [float(s) for s in json.load(open(os.path.join(HERE, "checkpoints", "zeta_zeros_800_100dps.json")))]
ZD = np.array(json.load(open(os.path.join(HERE, "checkpoints", "zeta_zeros_6700.json"))), dtype=float)
ok = len(Z40) == 800 and all(abs(Z40[i] - ZD[i]) <= 1e-9 for i in range(800)) and Z40[0] > 14.13 and Z40[-1] > 1183
worst = 0.0
for t in (3.0, 8.0, 13.0):
    lhs, rhs, _ = XI.hadamard_check(t, Z40); worst = max(worst, abs(lhs - rhs)); ok &= abs(lhs - rhs) <= 1e-4
XC = XI.constants()
ok &= abs(XC["Xi0"] - 0.49712) <= 5e-6 and abs(XC["g0sq_limit"] - 0.7729) <= 5e-5 and abs(math.sqrt(XC["t2_mean"]) - 3.195) <= 5e-4
ok &= abs(XC["K"] - (2 + 0.5772156649015329 - math.log(4*math.pi))) < 1e-15 and abs(XC["inv_sqrt_2K"] - 3.290) <= 5e-4
XN = XI.nodes(11); GAMMA1 = Z40[0]
below_xi = [sum(1 for v in n if v < GAMMA1) for n in XN]                   # the Xi-limit nodes below the first zeta zero, rungs 2..12 (F8)
ok &= below_xi == [1, 2, 3, 4, 4, 4, 5, 5, 5, 5, 6]
gate(f"g1 the Xi side: Hadamard's product against the 800 zeros (100 digits, agreeing with the double list within 1e-9) plus the density tail at t = 3, 8, 13 (max |diff| {worst:.1e}); Xi(0) = {XC['Xi0']:.5f}; 2 pi Xi(0)^2/int Xi^2 = {XC['g0sq_limit']:.4f}; sqrt<t^2> = {math.sqrt(XC['t2_mean']):.4f}; K = {XC['K']:.6f}, 1/sqrt(2K) = {XC['inv_sqrt_2K']:.4f}; the curvature -Xi''(0)/(2 Xi(0)) = {XC['curvature']:.6f} against K/2 = {XC['K']/2:.6f}; the Xi-limit nodes " + "; ".join(", ".join(f"{v:.3f}" for v in n) for n in XN[:4]) + "; the nodes below the first zeta zero for rungs 2-12: " + ", ".join(str(b) for b in below_xi), ok)

# ---------------------------------------------------------------- g2
ok = True; G = {c: ST[c]["ground"] for c in ORDER}
ZT = Z40[-1]; ztail = (math.log(ZT/(2*math.pi)) + 1)/(2*math.pi*ZT)        # sum_{gamma > gamma_800} gamma^-2 by the density, leading term (as xi_limit.hadamard_check)
Zb = np.array(Z40)
def _eps(c):
    """epsilon(delta) = sum_{|tau| >= T_D} tau^-2 + sum_{gamma >= T_D} gamma^-2: the first is kappa less the LOCATED zeros' sum below T_D (round 322 F322-1)"""
    g = G[c]; TD = g["first_missed"]
    return (g["kappa"] - g["sum_inv_sq_located_below"]) + float(np.sum(1/Zb[Zb >= TD]**2)) + ztail
for c in ORDER:
    g = G[c]; ok &= g["first_missed"] is not None and g["first_free"] is not None and abs(g["first_missed"] - g["first_free"]) <= 0.2 and g["first_missed"] >= 1.4*T0[c]
    # the real-zero census (round 321 F4/F9): all K - 1 designed pairs located on the real line and the sum rule closing (none missed, no
    # complex zero) -- or K - 2 located with the sum rule placing the one unlocated pair beyond the region (real or imaginary, |tau| >= R_ext:
    # outside the disc |r| < T_D either way); the located zeros below the edge and the zeta zeros below it equal in number (every zeta zero
    # below the edge has one; a dodging zero turned double would break the equality either way, detected or not)
    cen = g["n_designed_real"] == g["K_minus_1"] and abs(g["sum_rule_residual"]) <= 1e-16                                                   # kappa Richardson-extrapolated about the exact ghat_1(0): the closure is the census's (F322-3)
    cen |= g["n_designed_real"] == g["K_minus_1"] - 1 and g["missing_pair"] is not None and g["missing_pair"]["abs_tau"] >= g["R_ext"] and abs(g["sum_rule_residual"]) >= 1e-9
    # the census's entries are sign changes plus two equal entries per detected dip (a double zero within 5e-5 of a grid point): the entry count is
    # the sign-change count only when no dip was appended -- n_dips_census == 0 is gated as THAT PRECONDITION, not as evidence of absence (round 325
    # F325-1; the detector's blindness elsewhere is stated in the block); no double zero then follows from the complete count of sign changes
    # (a double root of M gives no sign change); disp_max <= TOL held by construction and is not gated (F323-4)
    ok &= cen and g["n_located_below_edge"] == g["n_zeta_below_edge"] and g["n_dips_census"] == 0
    ok &= g["disp_term_r3"] <= 1e-4 and (ST[c]["delta"] < 2.0 or (g["disp_max_low"] is not None and g["disp_max_low"] <= 3e-14))                 # the dodging displacements (F322-1; the low half at the double list's floor, F323-3)
    ok &= g["mass_beyond"]["TD/2"] <= 1e-3 and g["mass_beyond"]["TD"] <= 1e-5                # the exterior mass (F6)
eps = [_eps(c) for c in ORDER]; ratio = [eps[i]/(math.log(G[c]["first_missed"])/G[c]["first_missed"]) for i, c in enumerate(ORDER)]
ok &= all(eps[i] > eps[i + 1] for i in range(6)) and eps[-1] > 0 and all(0.18 <= x <= 0.24 for x in ratio)
kap = [G[c]["kappa"] for c in ORDER]; g0 = [math.exp(G[c]["ln_g0sq"]) for c in ORDER]; r2 = [math.sqrt(G[c]["r2_mean"]) for c in ORDER]
ok &= all(kap[i] < kap[i + 1] for i in range(6)) and kap[-1] < XC["curvature"]               # toward sum gamma^-2, not K/2 (F3)
ok &= all(g0[i] < g0[i + 1] for i in range(6)) and g0[-1] < XC["g0sq_limit"]
ok &= all(r2[i] > r2[i + 1] for i in range(6)) and r2[-1] > math.sqrt(XC["t2_mean"])
gate("g2 the limit shape at the cells: Hypothesis D by the real-zero census, within the dodging tolerance (the dodging zeros displaced from the zeta zeros by at most " + ", ".join(f"{G[c]['disp_max']:.1e}" for c in ORDER) + ", the low half by at most " + ", ".join(f"{G[c]['disp_max_low']:.0e}" if G[c]["disp_max_low"] is not None else "-" for c in ORDER) + ", adding at most " + f"{max(G[c]['disp_term_r3'] for c in ORDER):.1e}" + " to the bound at r = 3; the dip detector's counts " + ", ".join(str(G[c]["n_dips_census"]) for c in ORDER) + " -- gated as the precondition that the entry counts are sign-change counts) (designed zero pairs located " + ", ".join(f"{G[c]['n_designed_real']}/{G[c]['K_minus_1']}" for c in ORDER) + " within " + ", ".join(f"{G[c]['R_ext']:.0f}" for c in ORDER) + "; the sum rule's residual " + ", ".join(f"{G[c]['sum_rule_residual']:.1e}" for c in ORDER) + "; unlocated pairs placed by the sum rule: " + (", ".join(f"{c}: |tau| = {G[c]['missing_pair']['abs_tau']:.0f} ({'real' if G[c]['missing_pair']['real'] else 'imaginary'})" for c in ORDER if G[c]["missing_pair"] is not None) or "none") + "; located/zeta zeros below the edge " + ", ".join(f"{G[c]['n_located_below_edge']}/{G[c]['n_zeta_below_edge']}" for c in ORDER) + "); the first missed zeta zero and the first free zero within 0.2, at " + ", ".join(f"{G[c]['first_missed']/T0[c]:.2f}" for c in ORDER) + " T_0; epsilon " + ", ".join(f"{e:.5f}" for e in eps) + " falling, " + ", ".join(f"{x:.2f}" for x in ratio) + " of ln T_D/T_D; the mass beyond T_D/2 and T_D at most " + f"{max(G[c]['mass_beyond']['TD/2'] for c in ORDER):.1e} and {max(G[c]['mass_beyond']['TD'] for c in ORDER):.1e}" + "; the curvature " + ", ".join(f"{k:.4f}" for k in kap) + f" rising toward sum gamma^-2 = {XC['curvature']:.6f} (K/2 = {XC['K']/2:.6f}); ghat_1(0)^2 " + ", ".join(f"{v:.3f}" for v in g0) + f" rising toward {XC['g0sq_limit']:.4f}; sqrt<r^2> " + ", ".join(f"{v:.3f}" for v in r2) + f" falling toward {math.sqrt(XC['t2_mean']):.3f}", ok)

# ---------------------------------------------------------------- g3
ok = True; worst_rel = 0.0; nsafe = 0; below = {}
for c in ORDER:
    st = ST[c]; below[c] = []
    for r in safe_rungs(c):
        nsafe += 1; ok &= len(r["hole"]) == r["k"] - 1 and len(set(r["hole"])) == len(r["hole"])   # k - 1 entries, none duplicated (a detected dip appends two equal entries: F325-1)
        ok &= max(st["nodes"][r["k"] - 2]) < min(100.0, 0.8*r["edge"])                       # the census region covers the predicted nodes (F10)
        nb = sum(1 for h in r["hole"] if h < st["gamma1"]); below[c].append(nb)
        ok &= all(h < st["gamma1"] for h in r["hole"][:3])                                   # the first three hole zeros below the first zeta zero (F8)
        if st["delta"] >= 2.6 and r["k"] >= 6: ok &= nb in ((4,) if r["k"] <= 7 else (4, 5))
    ok &= all(below[c][i] <= below[c][i + 1] for i in range(len(below[c]) - 1))
    if st["delta"] >= 2.0:
        for r in st["rungs"][1:4]:
            nodes = st["nodes"][r["k"] - 2]
            if len(r["hole"]) == len(nodes):
                rel = max(abs(h - n)/n for h, n in zip(r["hole"], nodes)); worst_rel = max(worst_rel, rel); ok &= rel <= 0.01
            else: ok = False
first = [ST[c]["rungs"][1]["hole"][0] for c in ORDER]
ok &= all(first[i] > first[i + 1] for i in range(6)) and first[-1] > XN[0][0]
fourth = [ST[c]["rungs"][4]["hole"][3] for c in ("d2.3", "d2.6", "d3.0", "d3.5")]      # rung 5's fourth hole zero against the first zeta zero
g1 = ST["d2.3"]["gamma1"]
ok &= all(fourth[i] > fourth[i + 1] for i in range(3)) and fourth[0] > g1 and fourth[1] > g1 and fourth[2] > g1 and fourth[3] < g1 and fourth[3] > XN[3][3]
gate(f"g3 the hole zeros: every safely deep rung k through rung 12 (its own ln(1 - chi_2k) < -20; {nsafe} rungs over the seven cells, " + ", ".join(str(len(safe_rungs(c))) for c in ORDER) + ") has exactly k - 1, the census region covering the predicted nodes; the ground state none (g2's census); the first three of every rung below the first zeta zero, and below it per rung " + "; ".join(f"{c}: " + ",".join(str(b) for b in below[c]) for c in ORDER if below[c]) + f" (rungs 6-7 four, 8-12 four or five at delta >= 2.6, nondecreasing); at delta >= 2 rungs 2-4 sit within 1% of the nodes of P_(2(k-1)) for the weight ghat_1^2 (max relative deviation {worst_rel:.2%}); the first hole zero " + ", ".join(f"{v:.3f}" for v in first) + f" falling toward the Xi-limit {XN[0][0]:.3f}; rung 5's fourth hole zero " + ", ".join(f"{v:.3f}" for v in fourth) + f" at delta = 2.3, 2.6, 3.0, 3.5 crosses the first zeta zero {g1:.3f} between 3.0 and 3.5 and stays above its Xi-limit {XN[3][3]:.3f}", ok)

# ---------------------------------------------------------------- g4
CDEL = {"d1.0": 4.70, "d1.38": 5.21, "d2.0": 5.94, "d2.3": 6.39, "d2.6": 6.64, "d3.0": 7.30, "d3.5": 7.90}   # 1bm(v)
ok = True; par = {}; alt = {}; cnt = {}
for c in ORDER:
    st = ST[c]; c1 = st["rungs"][0]["ck"]; ok &= abs(c1 - CDEL[c]) <= 0.15
    sr = safe_rungs(c); pro = st["prolate_ln_leakage"]
    for r in sr: ok &= c1 - 3.0 <= r["ck"] <= c1 + 0.3
    if len(sr) >= 8:
        sgn = np.sign(np.diff([r["ck"] for r in sr]))                                           # from rung 2, the safely deep rungs only (F12)
        alt[c] = int(np.sum(sgn[1:] != sgn[:-1])); ok &= alt[c] >= 2                            # c_k is not monotone
    if len(sr) >= 8:
        # THE PARITY (round 321 F2, round 322 F322-2): 1br(ii)'s offsets o_k = ln lambda_k - ln(1 - chi_{2k}) = c_k + d_k, d_k = F_k - ln(1 - chi_{2k})
        # the formula's part; the balanced cells only (the two parities' mean ranks equal: rungs 2-10 or 2-12), with each mean's standard error
        ev = [r for r in sr if r["k"] % 2 == 0]; od = [r for r in sr if r["k"] % 2 == 1]
        ok &= abs(np.mean([r["k"] for r in ev]) - np.mean([r["k"] for r in od])) < 1e-9
        def _em(f):
            # the even-minus-odd mean and its standard error from the residuals about a linear trend in k (s^2 with two parameters removed;
            # at a balanced cell the raw mean difference equals the parity fitted with the trend removed)
            a_, b_ = np.array([f(r) for r in ev]), np.array([f(r) for r in od]); ks = np.array([r["k"] for r in sr], dtype=float); y = np.array([f(r) for r in sr])
            A_ = np.vstack([ks, np.ones(len(ks))]).T; e_ = y - A_ @ np.linalg.lstsq(A_, y, rcond=None)[0]; s2 = float(e_ @ e_)/(len(ks) - 2)
            return float(a_.mean() - b_.mean()), float(math.sqrt(s2*(1/len(a_) + 1/len(b_))))
        par[c] = (_em(lambda r: r["ln_lam"] - pro[2*r["k"]]), _em(lambda r: r["Fk"] - pro[2*r["k"]]), _em(lambda r: r["ck"]))
        ok &= par[c][0][0] > 0 and par[c][1][0] > 0                                             # even above odd in the offsets and in the formula's part (point estimates)
        cnt[c] = (len(ev), len(od))                                                             # the rungs per parity, stated in the block and parsed back in g7 (F323-1, F324-4)
ok &= list(alt) == ["d2.6", "d3.0", "d3.5"] and list(par) == ["d2.6", "d3.0", "d3.5"] and abs(par["d3.0"][0][0] - 0.22) <= 0.02
ses = [par[c][i][1] for c in par for i in range(3)]; ok &= max(ses) <= 0.25 and min(ses) >= 0.05
ok &= not all(par[c][2][0] > 0 for c in par) and not all(par[c][2][0] < 0 for c in par)          # the residual's parity changes sign across the cells
zsig = (par["d3.5"][2][0] - par["d2.6"][2][0])/math.sqrt(par["d3.5"][2][1]**2 + par["d2.6"][2][1]**2); ok &= zsig >= 2.0     # ... by more than two standard errors (F323-7)
ok &= par["d3.5"][1][0] <= par["d3.5"][1][1]                                                       # d_k's mean at 3.5 within one standard error of zero (stated, F323-7)
gate("g4 the k-level formula: c_1 within 0.15 of 1bm(v)'s c(delta) at every cell (" + ", ".join(f"{ST[c]['rungs'][0]['ck']:.2f}" for c in ORDER) + "); the safely deep rungs' c_k within [c_1 - 3, c_1 + 0.3]; not monotone -- the successive differences from rung 2 change sign " + ", ".join(f"{alt[c]}" for c in alt) + " times at delta = 2.6, 3.0, 3.5; the parity over the safely deep rungs at the balanced cells delta = 2.6, 3.0, 3.5 -- even minus odd means of the offsets " + ", ".join(f"{par[c][0][0]:+.3f}" for c in par) + " (1br(ii)'s +0.22 at 3.0 within 0.02), of the formula's part d_k " + ", ".join(f"{par[c][1][0]:+.3f}" for c in par) + ", of the residual c_k " + ", ".join(f"{par[c][2][0]:+.3f}" for c in par) + " (standard errors " + ", ".join(f"{par[c][i][1]:.2f}" for c in par for i in range(3)) + "); rungs per parity (even/odd) " + ", ".join(f"{cnt[c][0]}/{cnt[c][1]}" for c in par) + f"; c_k's change between 2.6 and 3.5 is {zsig:.1f} standard errors, d_k's mean at 3.5 within one: the formula's part reproduces the parity's sign in the point estimates", ok)

# ---------------------------------------------------------------- g5
ok = True
for c in ORDER:
    g = G[c]; ok &= abs(g["c1"] - (g["origin"] + g["peak_excess"] + g["count_800"] + g["far_tail"])) <= 1e-9
sh3 = {c: 1 - G[c]["shares"]["3"]*math.exp(-G[c]["far_tail"]) for c in ORDER}                  # the share of Q beyond 3 T_0, the far tail beyond the 800 included (F7)
for c in ORDER:
    if ST[c]["delta"] >= 2.0: ok &= sh3[c] >= 0.39
org = [G[c]["origin"] for c in ORDER]; ok &= all(org[i] < org[i + 1] for i in range(6)) and org[-1] < math.log(XC["g0sq_limit"])
extw = [G[c]["peak_excess"] + G[c]["count_800"] + G[c]["far_tail"] for c in ORDER]; ok &= all(extw[i] < extw[i + 1] for i in range(6))
lnT0 = np.array([math.log(T0[c]) for c in ORDER]); A_ = np.vstack([lnT0, np.ones(7)]).T
def _slope(y): return float(np.linalg.lstsq(A_, np.array(y), rcond=None)[0][0])
sl_org, sl_ext, sl_c = _slope(org), _slope(extw), _slope([G[c]["c1"] for c in ORDER]); ok &= abs(sl_org + sl_ext - sl_c) <= 1e-9
gate("g5 the anatomy of c(delta) = origin + peak excess + count (+ the far tail beyond the 800 zeros), an identity at every cell: origin " + ", ".join(f"{G[c]['origin']:.3f}" for c in ORDER) + f" rising toward ln 0.7729 = {math.log(XC['g0sq_limit']):.3f}; peak excess " + ", ".join(f"{G[c]['peak_excess']:.2f}" for c in ORDER) + "; count " + ", ".join(f"{G[c]['count_800'] + G[c]['far_tail']:.2f}" for c in ORDER) + "; the exterior weight in units of the balayage level (peak excess + count) " + ", ".join(f"{v:.2f}" for v in extw) + f" rising; the least-squares slopes against ln T_0: origin {sl_org:.3f}, exterior {sl_ext:.3f}, c {sl_c:.3f} (an identity); the share of Q beyond 3 T_0, the far tail included, " + ", ".join(f"{sh3[c]:.3f}" for c in ORDER), ok)

# ---------------------------------------------------------------- g6
ok = True
for c in ("d2.3", "d3.5"):
    st = ST[c]; sr = safe_rungs(c)
    # a pair cost of 2 ln T_0 per rung against the ladder's spacing: the spacing over the safely deep rungs exceeds 3 ln T_0 at the first steps
    sp = [sr[0]["ln_lam"] - st["rungs"][0]["ln_lam"]]
    ok &= sp[0] > 3*math.log(T0[c]) and sp[0] < 4.5*math.log(T0[c])
ok &= abs(XC["inv_sqrt_2K"] - math.sqrt(XC["t2_mean"])) > 0.05 and all(ST[c]["rungs"][1]["hole"][0] < XC["inv_sqrt_2K"] for c in ("d3.0", "d3.5"))
gate(f"g6 mangle probes: the first rung spacing at delta = 2.3 and 3.5 lies in (3, 4.5) ln T_0 -- a pair cost of 2 ln T_0 misses it; the Gaussian model's first node 1/sqrt(2K) = {XC['inv_sqrt_2K']:.3f} is not the Xi-limit's {math.sqrt(XC['t2_mean']):.3f}, and the cells at delta >= 3 sit below the Gaussian value", ok)

# ---------------------------------------------------------------- g7
import paper_needles
S_EDGE = 'the first missed zero at 1.46, 1.63, 1.79, 1.77, 1.86, 1.90, 1.94 T₀'
S_KAPPA = 'the curvature 0.0148, 0.0177, 0.0203, 0.0210, 0.0216, 0.0221, 0.0225 rising toward Σ_γ γ⁻² = 0.0231'
S_CURV = 'Σ_γ γ⁻² = −Ξ″(0)/(2Ξ(0)) = 0.023105, within 10⁻⁵ of K/2 = 0.023096'
S_EPS = 'ε = 0.02336, 0.01765, 0.01115, 0.00920, 0.00707, 0.00518, 0.00348 at the cells, between 0.18 and 0.24 of ln T_D/T_D'
S_DISP = 'displaced from the zeta zeros by at most 0.033, 0.024, 0.025, 0.004, 0.028, 0.036, 0.043'
S_MISS = 'K − 2 of them at δ = 3.5 (K = 540: 538 of the 539 designed roots), where one root of M is unlocated — real, since M has real coefficients and a complex root would bring its conjugate — and the sum rule places it beyond the region: |τ| = 14501, real by the residual’s sign, against the region 7741'
S_RESID = 'the residual there, 4.8 × 10⁻⁹, against a closure below 10⁻¹⁶ at the six complete cells'
S_G0 = 'ĝ₁(0)² = 0.630, 0.683, 0.727, 0.740, 0.749, 0.757, 0.763 rising toward 0.7729'
S_R2 = '√⟨r²⟩ = 3.86, 3.58, 3.38, 3.33, 3.29, 3.26, 3.23 falling toward 3.19'
S_HOLE23 = 'at δ = 2.3 rung 2 at 3.329 against the node 3.328, rung 3 at 2.413, 7.374 against 2.410, 7.366, rung 4 at 2.011, 6.061, 10.221 against 2.005, 6.045, 10.193'
S_FIRST = 'the first hole zero 3.917, 3.594, 3.383, 3.329, 3.292, 3.258, 3.233 falls toward the Ξ-limit 3.195'
S_XINODES = 'the Ξ-limit nodes 3.195; 2.321, 7.124; 1.908, 5.759, 9.730; 1.725, 5.200, 8.781, 13.670'
S_CK = 'c_k = 6.45, 5.80, 5.60, 5.01, 4.88, 4.26, 4.37 over rungs 1–7 at δ = 2.3'
S_ANAT = 'origin −0.46, −0.38, −0.32, −0.30, −0.29, −0.28, −0.27; peak excess 3.86, 4.02, 4.31, 4.48, 4.73, 4.56, 4.83; count 1.30, 1.59, 2.06, 2.28, 2.25, 3.07, 3.27'
S_XICONST = 'Ξ(0) = 0.49712, ∫Ξ² = 2.00906, 2πΞ(0)²/∫Ξ² = 0.7729'
S_EXTW = 'the exterior weight in units of the balayage level 5.16, 5.60, 6.36, 6.76, 6.99, 7.63, 8.10'
S_SLOPES = 'slopes against ln T₀ over the cells 0.07 (the origin) and 1.19 (the exterior weight), summing to the slope of c, 1.26'
S_SHARE = '0.42, 0.40, 0.43, 0.44, 0.48 of Q beyond 3T₀ at δ ≥ 2, the far tail beyond γ₈₀₀ included'
S_TK = 'from 2.02 T₀ to 1.81 T₀ over the first nine rungs at δ = 3.5'
S_SP = 'the steps 16.50, 14.72, 13.23, 11.77, 11.19, 9.61, 8.70, 7.42 from rung 1 to rung 9 at δ = 2.3 against 4 ln T₀ = 16.55'
S_ALT = 'change sign 4, 5, 3 times at δ = 2.6, 3.0, 3.5'
S_PAR = 'even minus odd means of the offsets o_k +0.08, +0.21, +0.16 and of d_k +0.39, +0.24, +0.06 at δ = 2.6, 3.0, 3.5'
S_CKPAR = 'against the residual c_k −0.31, −0.03, +0.11'
S_SE = 'the means’ standard errors, from the residuals about a linear trend in k, 0.08–0.18'
S_CNT = 'rungs per parity (even/odd) 5/4, 6/5, 6/5'
S_NSAFE = '0, 0, 3, 6, 9, 11, 11 rungs at the cells'
S_HOLE35 = '3.233; 2.346, 7.193; 1.935, 5.836, 9.849; 1.748, 5.269, 8.894, 14.103 against the nodes 3.233; 2.346, 7.193; 1.934, 5.835, 9.847; 1.748, 5.268, 8.892, 14.095'
S_FOURTH = '15.239, 14.797, 14.402, 14.103 at δ = 2.3, 2.6, 3.0, 3.5'
# each call carries its literal (the precheck's clause D); the strings equal the S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, 'the first missed zero at 1.46, 1.63, 1.79, 1.77, 1.86, 1.90, 1.94 T₀', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the curvature 0.0148, 0.0177, 0.0203, 0.0210, 0.0216, 0.0221, 0.0225 rising toward Σ_γ γ⁻² = 0.0231', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'Σ_γ γ⁻² = −Ξ″(0)/(2Ξ(0)) = 0.023105, within 10⁻⁵ of K/2 = 0.023096', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'ε = 0.02336, 0.01765, 0.01115, 0.00920, 0.00707, 0.00518, 0.00348 at the cells, between 0.18 and 0.24 of ln T_D/T_D', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'displaced from the zeta zeros by at most 0.033, 0.024, 0.025, 0.004, 0.028, 0.036, 0.043', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'K − 2 of them at δ = 3.5 (K = 540: 538 of the 539 designed roots), where one root of M is unlocated — real, since M has real coefficients and a complex root would bring its conjugate — and the sum rule places it beyond the region: |τ| = 14501, real by the residual’s sign, against the region 7741', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the residual there, 4.8 × 10⁻⁹, against a closure below 10⁻¹⁶ at the six complete cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'ĝ₁(0)² = 0.630, 0.683, 0.727, 0.740, 0.749, 0.757, 0.763 rising toward 0.7729', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '√⟨r²⟩ = 3.86, 3.58, 3.38, 3.33, 3.29, 3.26, 3.23 falling toward 3.19', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'at δ = 2.3 rung 2 at 3.329 against the node 3.328, rung 3 at 2.413, 7.374 against 2.410, 7.366, rung 4 at 2.011, 6.061, 10.221 against 2.005, 6.045, 10.193', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the first hole zero 3.917, 3.594, 3.383, 3.329, 3.292, 3.258, 3.233 falls toward the Ξ-limit 3.195', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the Ξ-limit nodes 3.195; 2.321, 7.124; 1.908, 5.759, 9.730; 1.725, 5.200, 8.781, 13.670', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'c_k = 6.45, 5.80, 5.60, 5.01, 4.88, 4.26, 4.37 over rungs 1–7 at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'origin −0.46, −0.38, −0.32, −0.30, −0.29, −0.28, −0.27; peak excess 3.86, 4.02, 4.31, 4.48, 4.73, 4.56, 4.83; count 1.30, 1.59, 2.06, 2.28, 2.25, 3.07, 3.27', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'Ξ(0) = 0.49712, ∫Ξ² = 2.00906, 2πΞ(0)²/∫Ξ² = 0.7729', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the exterior weight in units of the balayage level 5.16, 5.60, 6.36, 6.76, 6.99, 7.63, 8.10', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'slopes against ln T₀ over the cells 0.07 (the origin) and 1.19 (the exterior weight), summing to the slope of c, 1.26', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '0.42, 0.40, 0.43, 0.44, 0.48 of Q beyond 3T₀ at δ ≥ 2, the far tail beyond γ₈₀₀ included', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'from 2.02 T₀ to 1.81 T₀ over the first nine rungs at δ = 3.5', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the steps 16.50, 14.72, 13.23, 11.77, 11.19, 9.61, 8.70, 7.42 from rung 1 to rung 9 at δ = 2.3 against 4 ln T₀ = 16.55', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'change sign 4, 5, 3 times at δ = 2.6, 3.0, 3.5', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'even minus odd means of the offsets o_k +0.08, +0.21, +0.16 and of d_k +0.39, +0.24, +0.06 at δ = 2.6, 3.0, 3.5', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'against the residual c_k −0.31, −0.03, +0.11', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the means’ standard errors, from the residuals about a linear trend in k, 0.08–0.18', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'rungs per parity (even/odd) 5/4, 6/5, 6/5', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '0, 0, 3, 6, 9, 11, 11 rungs at the cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '3.233; 2.346, 7.193; 1.935, 5.836, 9.849; 1.748, 5.269, 8.894, 14.103 against the nodes 3.233; 2.346, 7.193; 1.934, 5.835, 9.847; 1.748, 5.268, 8.892, 14.095', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '15.239, 14.797, 14.402, 14.103 at δ = 2.3, 2.6, 3.0, 3.5', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g7'] == [S_EDGE, S_KAPPA, S_CURV, S_EPS, S_DISP, S_MISS, S_RESID, S_G0, S_R2, S_HOLE23, S_FIRST, S_XINODES, S_CK, S_ANAT, S_XICONST, S_EXTW, S_SLOPES, S_SHARE, S_TK, S_SP, S_ALT, S_PAR, S_CKPAR, S_SE, S_CNT, S_NSAFE, S_HOLE35, S_FOURTH]
_re = __import__("re")
def _num(s): return float(s.strip().replace('−', '-'))
def _nums(s, pat=r"([-−]?[0-9]+\.[0-9]+)"): return [_num(x) for x in _re.findall(pat, s)]
_m = _nums(S_EDGE); ok &= len(_m) == 7 and all(abs(x - G[c]["first_missed"]/T0[c]) <= 5e-3 + 1e-9 for x, c in zip(_m, ORDER))                  # nearest 0.01
_m = _nums(S_KAPPA); ok &= len(_m) == 8 and all(abs(x - k) <= 5e-5 + 1e-9 for x, k in zip(_m[:7], kap)) and abs(_m[7] - XC["curvature"]) <= 5e-5 + 1e-9   # nearest 1e-4
_m = _nums(S_CURV); ok &= len(_m) == 2 and abs(_m[0] - XC["curvature"]) <= 5e-7 + 1e-9 and abs(_m[1] - XC["K"]/2) <= 5e-7 + 1e-9                          # nearest 1e-6
_m = _nums(S_EPS.split(" at the cells")[0]); ok &= len(_m) == 7 and all(abs(x - e) <= 5e-6 + 1e-9 for x, e in zip(_m, eps))                                 # nearest 1e-5
_r = _nums(S_EPS.split(" at the cells")[1]); ok &= len(_r) == 2 and _r[0] <= min(ratio) + 5e-3 + 1e-9 and _r[1] >= max(ratio) - 5e-3 - 1e-9
_i = [int(x) for x in _re.findall(r"[0-9]+", S_MISS)]; _mp = G["d3.5"]["missing_pair"]                                                        # the K - 2 branch at delta = 3.5: |tau| and the region, nearest integers
ok &= _mp is not None and [c for c in ORDER if G[c]["n_designed_real"] == G[c]["K_minus_1"] - 1] == ["d3.5"] and abs(_i[-2] - _mp["abs_tau"]) <= 0.5 + 1e-9 and _i[-1] == round(G["d3.5"]["R_ext"]) and _mp["real"] and abs(G["d3.5"]["sum_rule_residual"]) >= 1e-9
ok &= _i[-5:-2] == [ST["d3.5"]["K"], G["d3.5"]["n_designed_real"], G["d3.5"]["K_minus_1"]]                                                     # K = 540: 538 of the 539 designed roots (F325-4)
_r = _nums(S_RESID); _oth = max(abs(G[c]["sum_rule_residual"]) for c in ORDER if c != "d3.5")                                                  # the residual in units of 1e-9 (nearest 0.1); the closure elsewhere below 1e-16
ok &= len(_r) == 1 and abs(_r[0] - abs(G["d3.5"]["sum_rule_residual"])*1e9) <= 0.05 + 1e-9 and _oth <= 1e-16
_m = _nums(S_G0); ok &= len(_m) == 8 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m[:7], g0)) and abs(_m[7] - XC["g0sq_limit"]) <= 5e-4 + 1e-9
_m = _nums(S_R2); ok &= len(_m) == 8 and all(abs(x - v) <= 5e-3 + 1e-9 for x, v in zip(_m[:7], r2)) and abs(_m[7] - math.sqrt(XC["t2_mean"])) <= 5e-3 + 1e-9
_m = _nums(S_HOLE23.split(" rung 2 at ")[1]); _h = ST["d2.3"]["rungs"][1]["hole"] + ST["d2.3"]["nodes"][0] + ST["d2.3"]["rungs"][2]["hole"] + ST["d2.3"]["nodes"][1] + ST["d2.3"]["rungs"][3]["hole"] + ST["d2.3"]["nodes"][2]
ok &= len(_m) == 12 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m, _h))                                                                       # nearest 1e-3
_m = _nums(S_FIRST); ok &= len(_m) == 8 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m[:7], first)) and abs(_m[7] - XN[0][0]) <= 5e-4 + 1e-9
_m = _nums(S_XINODES); _x = [v for n in XN for v in n]; ok &= len(_m) == 10 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m, _x))
_m = _nums(S_CK.split(" over rungs")[0]); _c = [r["ck"] for r in ST["d2.3"]["rungs"][:7]]; ok &= len(_m) == 7 and all(abs(x - v) <= 5e-3 + 1e-9 for x, v in zip(_m, _c))   # rungs 1-7: the safely deep set at delta = 2.3
_m = _nums(S_ANAT); _a = [G[c]["origin"] for c in ORDER] + [G[c]["peak_excess"] for c in ORDER] + [G[c]["count_800"] + G[c]["far_tail"] for c in ORDER]
ok &= len(_m) == 21 and all(abs(x - v) <= 5e-3 + 1e-9 for x, v in zip(_m, _a))
_m = _nums(S_XICONST); ok &= len(_m) == 3 and abs(_m[0] - XC["Xi0"]) <= 5e-6 + 1e-9 and abs(_m[1] - XC["int_Xi2"]) <= 5e-6 + 1e-9 and abs(_m[2] - XC["g0sq_limit"]) <= 5e-5 + 1e-9
_m = _nums(S_EXTW); ok &= len(_m) == 7 and all(abs(x - v) <= 5e-3 + 1e-9 for x, v in zip(_m, extw))
_m = _nums(S_SLOPES); ok &= len(_m) == 3 and abs(_m[0] - sl_org) <= 5e-3 + 1e-9 and abs(_m[1] - sl_ext) <= 5e-3 + 1e-9 and abs(_m[2] - sl_c) <= 5e-3 + 1e-9
_m = _nums(S_SHARE); ok &= len(_m) == 5 and all(abs(x - sh3[c]) <= 5e-3 + 1e-9 for x, c in zip(_m, ORDER[2:]))
_m = _nums(S_TK.split(" over")[0]); _tk = [r["Tk"]/T0["d3.5"] for r in ST["d3.5"]["rungs"][:9]]; ok &= len(_m) == 2 and abs(_m[0] - _tk[0]) <= 5e-3 + 1e-9 and abs(_m[1] - _tk[8]) <= 5e-3 + 1e-9
_m = _nums(S_SP.split(" from rung")[0]); _sp = [ST["d2.3"]["rungs"][k]["ln_lam"] - ST["d2.3"]["rungs"][k - 1]["ln_lam"] for k in range(1, 9)]
ok &= len(_m) == 8 and all(abs(x - v) <= 5e-3 + 1e-9 for x, v in zip(_m, _sp)) and abs(_nums(S_SP.split("4 ln T₀ = ")[1])[0] - 4*math.log(T0["d2.3"])) <= 5e-3 + 1e-9
_pc = [int(x) for x in _re.findall(r"sign ([0-9]+), ([0-9]+), ([0-9]+) times", S_ALT)[0]]; ok &= [alt[c] for c in ("d2.6", "d3.0", "d3.5")] == _pc
_pm = _nums(S_PAR.split(" at δ")[0]); ok &= len(_pm) == 6 and all(abs(x - par[c][0][0]) <= 5e-3 + 1e-9 for x, c in zip(_pm[:3], par)) and all(abs(x - par[c][1][0]) <= 5e-3 + 1e-9 for x, c in zip(_pm[3:], par))
_pm = _nums(S_CKPAR); ok &= len(_pm) == 3 and all(abs(x - par[c][2][0]) <= 5e-3 + 1e-9 for x, c in zip(_pm, par))
_se = _nums(S_SE); ok &= len(_se) == 2 and abs(_se[0] - min(ses)) <= 5e-3 + 1e-9 and abs(_se[1] - max(ses)) <= 5e-3 + 1e-9                             # the standard errors' range (0.01)
_cn = [(int(a), int(b)) for a, b in _re.findall(r"([0-9]+)/([0-9]+)", S_CNT)]; ok &= "(even/odd)" in S_CNT and _cn == [cnt[c] for c in par]      # the rungs per parity, even/odd (exact)
_dm = _nums(S_DISP); ok &= len(_dm) == 7 and all(abs(x - G[c]["disp_max"]) <= 5e-4 + 1e-9 for x, c in zip(_dm, ORDER))                              # the displacements (nearest 1e-3)
_ns = [int(x) for x in _re.findall(r"[0-9]+", S_NSAFE.split(" rungs")[0])]; ok &= _ns == [len(safe_rungs(c)) for c in ORDER]
_m = _nums(S_HOLE35.split(" against the nodes ")[0]) + _nums(S_HOLE35.split(" against the nodes ")[1])
_h = [v for r in ST["d3.5"]["rungs"][1:5] for v in r["hole"]] + [v for n in ST["d3.5"]["nodes"][:4] for v in n]
ok &= len(_m) == 20 and len(_h) == 20 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m, _h))
_m = _nums(S_FOURTH.split(" at δ")[0]); ok &= len(_m) == 4 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m, fourth))
gate("g7 the paper's numbers parsed back from the declared needles: the dodging edges (nearest 0.01 T_0), the curvatures (1e-4) and their limit (1e-6), epsilon (1e-5) and its range against ln T_D/T_D, ghat_1(0)^2 (1e-3), sqrt<r^2> (0.01), the hole zeros and nodes of rungs 2-4 at delta = 2.3 (1e-3), the first hole zeros (1e-3), the Xi-limit nodes (1e-3), c_k at delta = 2.3 (0.01), the anatomy (0.01), Xi's constants, the exterior weight and the slopes and the tail-inclusive shares (0.01), the edge T_k (0.01), the steps at delta = 2.3 (0.01), the sign-change counts, the parity means of the offsets, the formula's part and the residual (0.01) and their standard errors' range (0.01), the rungs per parity (exact), the dodging displacements (1e-3), the safe-rung counts, the delta = 3.5 zeros and nodes of rungs 2-5 (1e-3), rung 5's fourth zero (1e-3)", ok)

# ---------------------------------------------------------------- g8
from cascade_tower import chain_ok
gate("g8 the chain obligation to cascade_pole_indefinite.py (Theorem 1bt) met", chain_ok("cascade_pole_indefinite.py"))

# ---------------------------------------------------------------- g9
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g9 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g9 the 1bu paper needles and the footer census (declared surface)", ok)

print(("ALL GATES PASS (10/10)" if not fails else f"FAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
