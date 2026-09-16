#!/usr/bin/env python3
"""Theorem 1bx (the exterior's re-balayage -- the law of Delta kappa_k derived): the verifier. The tower's member 33 (top);
chain obligation to cascade_rung_anatomy.py (Theorem 1bw), whose one number per rung this block derives.

WHAT THE BLOCK CLAIMS. (i) Delta kappa_k = sum_{O_k} tau^-2 - sum_{O_1} tau^-2 over the outer zero sets (dodging + exterior,
the placed pair included) = 2 int (n_k - n_1)(R) R^-3 dR: the R^-3 moment of the outer counting deficit (an identity).
(ii) The balayage law (proved): if the rung's outer set is the ground state's with the k - 1 hole pairs +-h balayaged onto the
complement E_T = {|tau| >= T} of a wall (Hypothesis B: V = ln|H_k C_k| harmonic in Omega = C \\ E_T off the holes and constant
on E_T, i.e. minus the Green potential of the holes), then with psi(z) = (z/T)/(1 + sqrt(1 - z^2/T^2)) -- Theorem 1bm's map of
Omega onto the unit disk -- and sigma_h = psi(h):
   ln C_k(R) = sum_h [ ln|1 - psi(R)^2/sigma_h^2| - ln(1 - sigma_h^2 psi(R)^2) - ln|1 - R^2/h^2| ]      (C_k(0) = 1),
   Delta kappa_k = - sum_h (1 + sigma_h^2)/(2 T^2),
   the pair-deficit profile P(R) = (2/pi) arccos(T/R) on E_T and the r^4 coefficient of ln C_k 3(k - 1)/(16 T^4), both at h -> 0.
(iii) Hypothesis B verified at the cells with one wall T_w(k) per rung -- T_w solved from Delta kappa_k by the law; then the
exact ln C_k from the census products matches the Green closed form across the interior (0.3, 0.5, 0.7 T_w), the deficit
profile fitted on [1.5, 6] T_1 returns the same wall, the laws checkpoint's ratio at r = 40 matches the closed form, and the
deficit at T_1 lags the profile's (the wall soft); rung 2's wall is the ground state's edge T_1 within 1.3% at delta <= 3 and
4.8% at delta = 3.5 (Theorem 1bm's X* = 2: T_1 = 1.9-2.0 T_0); the wall lies between the rung's edge T_k and T_1 at 37 of 40 rungs,
near their geometric mean for k >= 3, non-increasing with k from rung 3 -- computed, not derived.

THE GATES. (0) the proposition's algebra witnessed numerically (the r^2 coefficient of the closed form against the law, the
profile's R^-3 moment against 1/(2T^2), the r^4 coefficient against 3/16 at h -> 0); (1) the walls: rung 2's within [0.95, 1.01] T_1,
every wall within [0.83, 1.01] T_1 and >= 0.98 T_k, for k >= 3 within [0.96, 1.02] of sqrt(T_1 T_k); neither edge is the wall's law
(T_w/T_k reaches 1.15, T_1/T_w reaches 1.15 at k >= 3); (2) Hypothesis B across the interior: the exact ln C_k within 1.5%,
2% and 7% of the closed form at 0.3, 0.5, 0.7 T_w at every safely deep rung, and off by 5% or more at 0.5 T_w with the wall at
T_1 for k >= 3; (3) the deficit profile's wall within 6% of T_w at every rung with three or more holes, within 2.5% at delta >= 3, and the window's
sensitivity (the fit to 8 T_1 at least 15% off at its worst few-hole rung, within 5% at delta >= 3);
(4) the ratio at r = 40 within 0.014 of the closed form at every safely deep rung, within 6e-4 at delta >= 3; (5) the onset lags the
harmonic measure near the wall, over the 35 rungs with two or more holes: the signed shortfall averaging 0.02-0.1 per hole at T_1,
1.25 T_1 and 1.5 T_1 and within 0.02 at 2 T_1, positive at three quarters of them at T_1 and at most 0.2 there; the deficit at T_1
under a quarter of a zero at seven of them, named exactly, against the profile's 0.3 or more; the five one-hole rungs (rung 2 of
every cell) reported apart, the profile itself predicting under a quarter of a zero at T_1 there; (6) the paper's numbers parsed back; (7) the chain obligation;
(8) the needles and census.

WHAT IS NOT CLAIMED. The wall's law (T_w(k) is computed); the odd sector; anything beyond the safely deep rungs; no Riemann
Hypothesis consequence.
"""
import math, os, sys, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ladder_caster as LC
from rung_anatomy import run as run_RA
from rung_laws import run as run_RL
from ladder_caster import run as run_LC

PAPER_NEEDLES = [
    {'g': 'g8', 's': "Theorem 1bx (the exterior", 'form': 'plain'},
    {'g': 'g8', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 15},
    {'s': '`cascade_rung_balayage.py`', 'min': 2, 'g': 'g8'},
    {'s': 'the **100 scripts cited in place** above', 'form': 'ws', 'g': 'g8'},
    {'s': 'extended by Theorems 1i–1bx:', 'form': 'ws', 'g': 'g8'},
    {'g': 'g6', 's': '−Δκ₂T₁² = 0.498, 0.513, 0.502, 0.502, 0.552 at δ = 2, 2.3, 2.6, 3, 3.5 against the law’s 0.500, 0.500, 0.500, 0.500, 0.500 with the wall at T₁', 'form': 'ws'},
    {'g': 'g6', 's': 'T_w/T₁ = 1.002, 0.987, 0.998, 0.998, 0.952 for rung 2 at the five cells', 'form': 'ws'},
    {'g': 'g6', 's': 'T₁/T₀ = 1.88, 1.94, 1.98, 1.97, 1.99 at the five cells', 'form': 'ws'},
    {'g': 'g6', 's': 'T_w/T₁ between 0.833 and 1.002 over the 40 safely deep rungs of the five cells, T_w/T_k between 0.980 and 1.245, and T_w/√(T₁T_k) between 0.966 and 1.019 at the 35 rungs with k ≥ 3', 'form': 'ws'},
    {'g': 'g6', 's': 'the exact ln C_k within 0.5%, 1.7%, 5.9% of the closed form at R = 0.3, 0.5, 0.7 T_w at every safely deep rung, against 6.9% to 51% off at 0.5 T_w with the wall at T₁ for k ≥ 3', 'form': 'ws'},
    {'g': 'g6', 's': 'the profile’s wall within 5.0% of T_w at every safely deep rung with three or more holes and within 1.8% at δ ≥ 3; the window’s upper end is the sensitive one — the same fit to 8T₁ puts the profile’s wall 22% off at its worst few-hole rung while δ ≥ 3 stays within 3.8%', 'form': 'ws'},
    {'g': 'g6', 's': 'the ratio at r = 40 within 0.0131 of the closed form at every safely deep rung, its excess over 1 reaching 0.125, and within 0.0005 at δ ≥ 3', 'form': 'ws'},
    {'g': 'g6', 's': 'over the 35 rungs with two or more holes the signed shortfall (observed minus profile, per hole) averages 0.05 at T₁, 0.05 at 1.25 T₁, 0.03 at 1.5 T₁ and −0.006 at 2T₁, positive at 32 of the 35 at T₁ and at most 0.17 there; the deficit at T₁ is under a quarter of a zero at 7 of them (δ = 2’s rung 3, δ = 2.3’s rung 3, δ = 3’s rungs 3–4, δ = 3.5’s rungs 3–5) against the profile’s 0.31–0.66 zeros; the 5 one-hole rungs, rung 2 of every cell, are reported apart — a one-hole rung’s per-hole count moves by a whole zero at a time: shortfall 0.01, 0.20, 0.26, −0.12 at T₁, 1.25, 1.5, 2 T₁, a swing of 0.38 between 1.5 and 2T₁ — and at T₁ the profile itself predicts under a quarter of a zero there (0.00–0.20), as observed (0.009–0.108)', 'form': 'ws'},
    {'g': 'g6', 's': 'strictly between T_k and T₁ at 37 of the 40 rungs, inside T_k by up to 2.0% (δ = 3.5’s rungs 2–3) and beyond T₁ by 0.2% (δ = 2’s rung 2)', 'form': 'ws'},
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
SAFE = -20.0
def n_safe(c):
    st = EV[c]; pro = st["prolate_ln_leakage"]
    return len([r for r in st["rungs"][1:] if 2*r["k"] < len(pro) and pro[2*r["k"]] is not None and pro[2*r["k"]] < SAFE and r["k"] <= 12])

# ---------------------------------------------------------------- the law (closed forms)
def psi(z, T): return (z/T)/(1 + math.sqrt(1 - (z/T)**2))
def dk_bal(holes, T): return -sum((1 + psi(h, T)**2)/(2*T*T) for h in holes)
def lnC_bal(R, holes, T):
    rho = psi(R, T); s = 0.0
    for h in holes:
        sg = psi(h, T); s += math.log(abs(1 - rho*rho/(sg*sg))) - math.log(1 - sg*sg*rho*rho) - math.log(abs(1 - R*R/(h*h)))
    return s
def profile(R, T): return (2/math.pi)*np.arccos(np.minimum(1.0, T/np.asarray(R, dtype=float)))
def solve_T(holes, Dk):        # the wall from the law: dk_bal is increasing in T (toward 0 from below)
    lo, hi = 1.0, 1e6
    for _ in range(200):
        mid = 0.5*(lo + hi)
        if dk_bal(holes, mid) < Dk: lo = mid
        else: hi = mid
    return 0.5*(lo + hi)
def lnprod(Z, R): return float(np.sum(np.log(np.abs(1 - R*R/(np.asarray(Z, dtype=float)**2)))))
def outer(r):
    Z = [z for _, z in r["dodging"]] + list(r["exterior"])
    if r["n_complex"] == 1 and r["sum_rule_residual"] < 0: Z.append(abs(r["sum_rule_residual"])**-0.5)
    return np.array(sorted(Z))
def nbar(O):
    idx = np.arange(len(O)) + 0.5
    return lambda R: np.interp(R, O, idx, left=0.0, right=float(len(O)))

# ---------------------------------------------------------------- g0: the algebra witnessed (mpmath, 60 digits: the closed form's
# two logarithms cancel to leave R^2/(2T^2) against R^2/h^2, so the witnesses need the precision)
import mpmath as _mp
with _mp.workdps(60):
    def _psi(z, T): return (z/T)/(1 + _mp.sqrt(1 - (z/T)**2))
    def _dk(h, T): return -(1 + _psi(h, T)**2)/(2*T*T)
    def _lnC(R, h, T):
        rho = _psi(R, T); sg = _psi(h, T)
        return _mp.log(abs(1 - rho*rho/(sg*sg))) - _mp.log(1 - sg*sg*rho*rho) - _mp.log(abs(1 - R*R/(h*h)))
    ok = True
    for T, h in ((_mp.mpf(1), _mp.mpf("1e-3")), (_mp.mpf(1), _mp.mpf("0.1")), (_mp.mpf(1), _mp.mpf("0.5")), (_mp.mpf(37), _mp.mpf("3.3"))):
        e = _mp.mpf("1e-6")*min(h, T); c2 = lambda eps: _lnC(eps, h, T)/(eps*eps)
        c = (4*c2(e/2) - c2(e))/3                                   # Richardson: the R^2 coefficient of ln C
        ok &= abs(c + _dk(h, T)) <= _mp.mpf("1e-9")*abs(_dk(h, T))
    # the profile's R^-3 moment: 2 int_T^inf (2/pi) arccos(T/R) R^-3 dR = (2/T^2) int_0^1 (2/pi) arccos(u) u du = 1/(2T^2)  <=>  int_0^1 arccos(u) u du = pi/8
    ok &= abs(_mp.quad(lambda u: _mp.acos(u)*u, [0, 1]) - _mp.pi/8) <= _mp.mpf("1e-20")
    # the r^4 coefficient at h -> 0: 3/(16 T^4) per pair (ln C = R^2/(2T^2) + 3 R^4/(16 T^4) + ...)
    T = _mp.mpf(1); h = _mp.mpf("1e-8"); c4 = lambda R: (_lnC(R, h, T) + _dk(h, T)*R*R)/R**4
    R1, R2 = _mp.mpf("0.01"), _mp.mpf("0.02")
    ok &= abs((4*c4(R1) - c4(R2))/3 - _mp.mpf(3)/16) <= _mp.mpf("1e-6")
    # the map sends the wall to the unit circle and the origin to the centre
    ok &= abs(_psi(T, T) - 1) <= _mp.mpf("1e-50") and _psi(_mp.mpf(0), T) == 0
gate("g0 the balayage law's algebra witnessed at 60 digits: the r^2 coefficient of the closed-form ln C against -Delta kappa within 1e-9 at four (T, h); the profile's R^-3 moment int_0^1 arccos(u) u du = pi/8 within 1e-20; the r^4 coefficient 3/16 per pair at h -> 0 within 1e-6; psi(T) = 1, psi(0) = 0", ok)

# ---------------------------------------------------------------- g1: the walls
W = {}   # (c, k) -> dict
for c in ORDER:
    S = CEN[c]; L = {l["k"]: l for l in LAW[c]["laws"]}; ns = n_safe(c); g = S["rungs"][0]; T1 = g["edge"]
    for r in S["rungs"][1:ns + 1]:
        k = r["k"]; holes = sorted(r["holes"]); Tw = solve_T(holes, L[k]["Dkappa"])
        W[(c, k)] = {"k": k, "m": k - 1, "holes": holes, "Tw": Tw, "T1": T1, "Tk": r["edge"], "Dk": L[k]["Dkappa"], "r40": L[k]["ratio_r"]["40.0"]}
wall2 = [W[(c, 2)]["Tw"]/W[(c, 2)]["T1"] for c in ORDER]
rat1 = [w["Tw"]/w["T1"] for w in W.values()]; ratk = [w["Tw"]/w["Tk"] for w in W.values()]
ratg = [w["Tw"]/math.sqrt(w["T1"]*w["Tk"]) for w in W.values() if w["k"] >= 3]
ok = all(0.95 <= x <= 1.01 for x in wall2) and all(0.83 <= x <= 1.01 for x in rat1) and min(ratk) >= 0.98 and all(0.96 <= x <= 1.02 for x in ratg)
ok &= max(ratk) >= 1.15 and max(w["T1"]/w["Tw"] for w in W.values() if w["k"] >= 3) >= 1.15          # neither edge is the wall's law
ok &= all(abs(-w["Dk"]*w["Tw"]**2/sum(1 + psi(h, w["Tw"])**2 for h in w["holes"]) - 0.5) <= 1e-9 for w in W.values())   # the wall is the law's inversion (its residual)
# the wall non-increasing with k from rung 3 at every cell; rung 2's at or beyond rung 3's at delta <= 3 and inside rungs 3-6's at delta = 3.5
mono = all(W[(c, k + 1)]["Tw"] <= W[(c, k)]["Tw"] + 1e-9 for c in ORDER for k in range(3, n_safe(c) + 1))
r2 = all((W[(c, 2)]["Tw"] >= W[(c, 3)]["Tw"]) == (CEN[c]["delta"] <= 3.0) for c in ORDER) and all(W[("d3.5", 2)]["Tw"] < W[("d3.5", k)]["Tw"] for k in (3, 4, 5, 6)) and W[("d3.5", 7)]["Tw"] < W[("d3.5", 2)]["Tw"]
INSIDE = [(c, k) for (c, k), w in W.items() if w["Tw"] < w["Tk"]]; BEYOND = [(c, k) for (c, k), w in W.items() if w["Tw"] > w["T1"]]
def _exc(L):   # a set of rungs named: one cell, a contiguous range of its rungs -- anything else renders unmatchable
    cs = sorted({c for c, _ in L}); ks = sorted(k for _, k in L)
    if len(cs) != 1 or not ks or ks != list(range(ks[0], ks[-1] + 1)): return "NOT A CELL'S CONTIGUOUS RANGE"
    return f"δ = {CEN[cs[0]]['delta']:g}’s rung" + ("s " + f"{ks[0]}–{ks[-1]}" if len(ks) > 1 else f" {ks[0]}")
def _cells(L):  # the rungs named cell by cell, in the cells' order
    return ", ".join(_exc([(c, k) for c, k in L if c == cc]) for cc in ORDER if any(c == cc for c, _ in L))
ok &= mono and r2
nb = sum(1 for w in W.values() if w["Tk"] < w["Tw"] < w["T1"])

gate("g1 the walls T_w(k) solved from Delta kappa_k by the law at every safely deep rung: rung 2's T_w/T_1 = " + ", ".join(f"{x:.3f}" for x in wall2) + f" (within [0.95, 1.01]); T_w/T_1 in [{min(rat1):.3f}, {max(rat1):.3f}] (gated [0.83, 1.01]); T_w/T_k in [{min(ratk):.3f}, {max(ratk):.3f}] (>= 0.98; reaching 1.15); T_w/sqrt(T_1 T_k) in [{min(ratg):.3f}, {max(ratg):.3f}] for k >= 3 (gated [0.96, 1.02]); T_1/T_w reaching {max(w['T1']/w['Tw'] for w in W.values() if w['k'] >= 3):.3f} at k >= 3; non-increasing with k from rung 3 at every cell, rung 2's at or beyond rung 3's at delta <= 3 and inside rungs 3-6's and above rung 7's at delta = 3.5; strictly between T_k and T_1 at {nb} of {len(W)} rungs (inside T_k: {INSIDE}; beyond T_1: {BEYOND})", ok)

# ---------------------------------------------------------------- g2: Hypothesis B across the interior
FR = (0.3, 0.5, 0.7); TOL = (0.015, 0.02, 0.07); dev = {f: [] for f in FR}; con = []
for c in ORDER:
    S = CEN[c]; g = S["rungs"][0]; O1 = outer(g)
    for r in S["rungs"][1:n_safe(c) + 1]:
        w = W[(c, r["k"])]; Ok = outer(r)
        for f in FR:
            R0 = f*w["Tw"]; i = int(np.searchsorted(ZS, R0)); R = 0.5*(ZS[i - 1] + ZS[i])       # a midpoint between zeta zeros
            ex = lnprod(Ok, R) - lnprod(O1, R); bw = lnC_bal(R, w["holes"], w["Tw"])
            dev[f].append(abs(ex/bw - 1))
            if f == 0.5 and w["k"] >= 3: con.append(abs(ex/lnC_bal(R, w["holes"], w["T1"]) - 1))
ok = all(max(dev[f]) <= t for f, t in zip(FR, TOL)) and min(con) >= 0.05
gate("g2 Hypothesis B across the interior: the exact ln C_k (the census products, rung against ground) within " + ", ".join(f"{100*max(dev[f]):.1f}%" for f in FR) + " of the Green closed form with the wall T_w at R = 0.3, 0.5, 0.7 T_w over the forty safely deep rungs (gated 1.5%, 2%, 7%); with the wall at T_1 instead, off by " + f"{100*min(con):.1f}% to {100*max(con):.0f}% at 0.5 T_w for k >= 3 (gated >= 5%)", ok)

# ---------------------------------------------------------------- g3: the deficit profile's wall
pw = []; pw3 = []; pw8 = []; pw83 = []
def fit_wall(Nk, N1, m, T1, hi):
    RR = np.linspace(1.5*T1, hi*T1, 400); Db = (Nk(RR) - N1(RR))/m
    cands = np.linspace(0.6*T1, 1.2*T1, 1201)
    err = [float(np.mean((Db + profile(RR, tw))**2)) for tw in cands]; return cands[int(np.argmin(err))]
for c in ORDER:
    S = CEN[c]; g = S["rungs"][0]; T1 = g["edge"]; N1 = nbar(outer(g))
    for r in S["rungs"][1:n_safe(c) + 1]:
        w = W[(c, r["k"])]; m = w["m"]
        if m < 3: continue
        Nk = nbar(outer(r))
        d = abs(fit_wall(Nk, N1, m, T1, 6.0)/w["Tw"] - 1); pw.append(d)
        d8 = abs(fit_wall(Nk, N1, m, T1, 8.0)/w["Tw"] - 1); pw8.append(d8)             # the window's sensitivity: the same fit to 8 T_1
        if S["delta"] >= 3.0: pw3.append(d); pw83.append(d8)
ok = max(pw) <= 0.06 and max(pw3) <= 0.025 and max(pw8) >= 0.15 and max(pw83) <= 0.05
gate(f"g3 the deficit profile (n_k - n_1)/(k - 1) on [1.5, 6] T_1 fitted by -(2/pi) arccos(T_w'/R) returns the wall: T_w' within {100*max(pw):.1f}% of T_w at every rung with three or more holes (gated 6%), within {100*max(pw3):.1f}% at delta >= 3 (gated 2.5%); the window's upper end is the sensitive one -- the same fit to 8 T_1 puts T_w' {100*max(pw8):.0f}% off at its worst few-hole rung (gated >= 15%) while delta >= 3 stays within {100*max(pw83):.1f}% (gated 5%)", ok)

# ---------------------------------------------------------------- g4: the interior ratio at r = 40 from the laws checkpoint
e40 = []; e40_3 = []; exc = []
for (c, k), w in W.items():
    b = (-lnC_bal(40.0, w["holes"], w["Tw"])/1600.0)/dk_bal(w["holes"], w["Tw"])
    e40.append(abs(w["r40"] - b)); exc.append(w["r40"] - 1)
    if CEN[c]["delta"] >= 3.0: e40_3.append(abs(w["r40"] - b))
ok = max(e40) <= 0.014 and max(e40_3) <= 6e-4
gate(f"g4 the ratio (-ln C_k/r^2)/Delta kappa_k at r = 40 (Theorem 1bw's laws checkpoint) against the closed form with T_w: within {max(e40):.4f} at every safely deep rung (gated 0.014; the excess over 1 reaching {max(exc):.3f}), within {max(e40_3):.1e} at delta >= 3 (gated 6e-4)", ok)

# ---------------------------------------------------------------- g5: the onset -- the deficit lags the profile near the wall, over the rungs with two or more holes
LAGF = (1.0, 1.25, 1.5, 2.0); SH = {}; OBS = {}; PRED = {}
for c in ORDER:
    S = CEN[c]; g = S["rungs"][0]; T1 = g["edge"]; N1 = nbar(outer(g))
    for r in S["rungs"][1:n_safe(c) + 1]:
        w = W[(c, r["k"])]; Nk = nbar(outer(r)); m = w["m"]
        SH[(c, r["k"])] = {f: (Nk(f*T1) - N1(f*T1))/m + (2/math.pi)*math.acos(min(1.0, w["Tw"]/(f*T1))) for f in LAGF}   # the signed shortfall per hole
        OBS[(c, r["k"])] = abs(Nk(T1) - N1(T1)); PRED[(c, r["k"])] = m*(2/math.pi)*math.acos(min(1.0, w["Tw"]/T1))       # the deficit at T_1 in zeros: observed, the profile's
M2 = [key for key in W if W[key]["m"] >= 2]; M1 = [key for key in W if W[key]["m"] == 1]
mean2 = {f: float(np.mean([SH[key][f] for key in M2])) for f in LAGF}; mean1 = {f: float(np.mean([SH[key][f] for key in M1])) for f in LAGF}
npos2 = sum(1 for key in M2 if SH[key][1.0] > 0); max2 = max(SH[key][1.0] for key in M2)
SEVEN = [key for key in M2 if OBS[key] <= 0.25]; FIVE = M1
ok = all(0.02 <= mean2[f] <= 0.1 for f in (1.0, 1.25, 1.5)) and abs(mean2[2.0]) <= 0.02 and npos2 >= 0.75*len(M2) and max2 <= 0.2 and len(M2) == 35 and len(M1) == 5
ok &= len(SEVEN) == 7 and all(PRED[key] >= 0.3 for key in SEVEN) and "NOT A" not in _cells(SEVEN)                        # the lag's members: under a quarter of a zero observed against the profile's 0.3 or more
ok &= {c for c, _ in FIVE} == set(ORDER) and all(k == 2 for _, k in FIVE) and all(OBS[key] <= 0.25 and PRED[key] <= 0.25 for key in FIVE)   # the one-hole rungs: the profile itself under a quarter at T_1
gate(f"g5 the onset lags the harmonic measure near the wall, over the {len(M2)} rungs with two or more holes: the signed shortfall (observed minus profile, per hole) averaging {mean2[1.0]:.2f} at T_1, {mean2[1.25]:.2f} at 1.25 T_1, {mean2[1.5]:.2f} at 1.5 T_1 (each gated [0.02, 0.1]) and {mean2[2.0]:+.3f} at 2 T_1 (gated |.| <= 0.02), positive at {npos2} of {len(M2)} at T_1 (gated >= 3/4) and at most {max2:.2f} there (gated 0.2); the deficit at T_1 under a quarter of a zero at {len(SEVEN)} of them ({_cells(SEVEN)}) against the profile's {min(PRED[key] for key in SEVEN):.2f}-{max(PRED[key] for key in SEVEN):.2f} zeros (gated >= 0.3); the {len(M1)} one-hole rungs (rung 2 of every cell) reported apart -- a one-hole rung's per-hole count moves by a whole zero at a time: shortfall {mean1[1.0]:.2f}, {mean1[1.25]:.2f}, {mean1[1.5]:.2f}, {mean1[2.0]:+.2f} at T_1, 1.25, 1.5, 2 T_1 (a swing of {mean1[1.5] - mean1[2.0]:.2f} between 1.5 and 2 T_1), the profile itself under a quarter of a zero at T_1 there ({min(PRED[key] for key in FIVE):.2f}-{max(PRED[key] for key in FIVE):.2f}) and the observed under a quarter ({min(OBS[key] for key in FIVE):.3f}-{max(OBS[key] for key in FIVE):.3f})", ok)

# ---------------------------------------------------------------- g6
import paper_needles
S_DK2LAW = '−Δκ₂T₁² = 0.498, 0.513, 0.502, 0.502, 0.552 at δ = 2, 2.3, 2.6, 3, 3.5 against the law’s 0.500, 0.500, 0.500, 0.500, 0.500 with the wall at T₁'
S_WALL2 = 'T_w/T₁ = 1.002, 0.987, 0.998, 0.998, 0.952 for rung 2 at the five cells'
S_T1T0 = 'T₁/T₀ = 1.88, 1.94, 1.98, 1.97, 1.99 at the five cells'
S_RANGE = 'T_w/T₁ between 0.833 and 1.002 over the 40 safely deep rungs of the five cells, T_w/T_k between 0.980 and 1.245, and T_w/√(T₁T_k) between 0.966 and 1.019 at the 35 rungs with k ≥ 3'
S_INTERIOR = 'the exact ln C_k within 0.5%, 1.7%, 5.9% of the closed form at R = 0.3, 0.5, 0.7 T_w at every safely deep rung, against 6.9% to 51% off at 0.5 T_w with the wall at T₁ for k ≥ 3'
S_PROFILE = 'the profile’s wall within 5.0% of T_w at every safely deep rung with three or more holes and within 1.8% at δ ≥ 3; the window’s upper end is the sensitive one — the same fit to 8T₁ puts the profile’s wall 22% off at its worst few-hole rung while δ ≥ 3 stays within 3.8%'
S_R40 = 'the ratio at r = 40 within 0.0131 of the closed form at every safely deep rung, its excess over 1 reaching 0.125, and within 0.0005 at δ ≥ 3'
S_EDGE = 'over the 35 rungs with two or more holes the signed shortfall (observed minus profile, per hole) averages 0.05 at T₁, 0.05 at 1.25 T₁, 0.03 at 1.5 T₁ and −0.006 at 2T₁, positive at 32 of the 35 at T₁ and at most 0.17 there; the deficit at T₁ is under a quarter of a zero at 7 of them (δ = 2’s rung 3, δ = 2.3’s rung 3, δ = 3’s rungs 3–4, δ = 3.5’s rungs 3–5) against the profile’s 0.31–0.66 zeros; the 5 one-hole rungs, rung 2 of every cell, are reported apart — a one-hole rung’s per-hole count moves by a whole zero at a time: shortfall 0.01, 0.20, 0.26, −0.12 at T₁, 1.25, 1.5, 2 T₁, a swing of 0.38 between 1.5 and 2T₁ — and at T₁ the profile itself predicts under a quarter of a zero there (0.00–0.20), as observed (0.009–0.108)'
S_BETWEEN = 'strictly between T_k and T₁ at 37 of the 40 rungs, inside T_k by up to 2.0% (δ = 3.5’s rungs 2–3) and beyond T₁ by 0.2% (δ = 2’s rung 2)'
# each call carries its literal (the precheck's clause D); the strings equal the S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, '−Δκ₂T₁² = 0.498, 0.513, 0.502, 0.502, 0.552 at δ = 2, 2.3, 2.6, 3, 3.5 against the law’s 0.500, 0.500, 0.500, 0.500, 0.500 with the wall at T₁', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'T_w/T₁ = 1.002, 0.987, 0.998, 0.998, 0.952 for rung 2 at the five cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'T₁/T₀ = 1.88, 1.94, 1.98, 1.97, 1.99 at the five cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'T_w/T₁ between 0.833 and 1.002 over the 40 safely deep rungs of the five cells, T_w/T_k between 0.980 and 1.245, and T_w/√(T₁T_k) between 0.966 and 1.019 at the 35 rungs with k ≥ 3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the exact ln C_k within 0.5%, 1.7%, 5.9% of the closed form at R = 0.3, 0.5, 0.7 T_w at every safely deep rung, against 6.9% to 51% off at 0.5 T_w with the wall at T₁ for k ≥ 3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the profile’s wall within 5.0% of T_w at every safely deep rung with three or more holes and within 1.8% at δ ≥ 3; the window’s upper end is the sensitive one — the same fit to 8T₁ puts the profile’s wall 22% off at its worst few-hole rung while δ ≥ 3 stays within 3.8%', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the ratio at r = 40 within 0.0131 of the closed form at every safely deep rung, its excess over 1 reaching 0.125, and within 0.0005 at δ ≥ 3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'over the 35 rungs with two or more holes the signed shortfall (observed minus profile, per hole) averages 0.05 at T₁, 0.05 at 1.25 T₁, 0.03 at 1.5 T₁ and −0.006 at 2T₁, positive at 32 of the 35 at T₁ and at most 0.17 there; the deficit at T₁ is under a quarter of a zero at 7 of them (δ = 2’s rung 3, δ = 2.3’s rung 3, δ = 3’s rungs 3–4, δ = 3.5’s rungs 3–5) against the profile’s 0.31–0.66 zeros; the 5 one-hole rungs, rung 2 of every cell, are reported apart — a one-hole rung’s per-hole count moves by a whole zero at a time: shortfall 0.01, 0.20, 0.26, −0.12 at T₁, 1.25, 1.5, 2 T₁, a swing of 0.38 between 1.5 and 2T₁ — and at T₁ the profile itself predicts under a quarter of a zero there (0.00–0.20), as observed (0.009–0.108)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'strictly between T_k and T₁ at 37 of the 40 rungs, inside T_k by up to 2.0% (δ = 3.5’s rungs 2–3) and beyond T₁ by 0.2% (δ = 2’s rung 2)', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g6'] == [S_DK2LAW, S_WALL2, S_T1T0, S_RANGE, S_INTERIOR, S_PROFILE, S_R40, S_EDGE, S_BETWEEN]
_re = __import__("re")
def _num(s): return float(s.strip().replace('−', '-'))
def _nums(s, pat=r"([-−]?[0-9]+\.[0-9]+)"): return [_num(x) for x in _re.findall(pat, s)]
def _ints(s): return [int(x) for x in _re.findall(r"(?<![0-9.])[0-9]+(?![0-9.])", s)]
_m = _nums(S_DK2LAW.split(" at δ")[0]); ok &= len(_m) == 5 and all(abs(x + W[(c, 2)]["Dk"]*W[(c, 2)]["T1"]**2) <= 5e-4 + 1e-9 for x, c in zip(_m, ORDER))
_m = _nums(S_DK2LAW.split("the law’s ")[1]); ok &= len(_m) == 5 and all(abs(x - 0.5*(1 + psi(W[(c, 2)]["holes"][0], W[(c, 2)]["T1"])**2)) <= 5e-4 + 1e-9 for x, c in zip(_m, ORDER))
_m = _nums(S_WALL2.split(" for rung")[0]); ok &= _m == [round(x, 3) for x in wall2] and len(_m) == 5
_m = _nums(S_T1T0); ok &= len(_m) == 5 and all(abs(x - W[(c, 2)]["T1"]/CEN[c]["T0"]) <= 5e-3 + 1e-9 for x, c in zip(_m, ORDER))
_m = _nums(S_RANGE); ok &= len(_m) == 6 and [round(v, 3) for v in (min(rat1), max(rat1), min(ratk), max(ratk), min(ratg), max(ratg))] == _m
_i = _ints(S_RANGE); ok &= _i == [len(W), len(ratg), 3]
_m = _nums(S_INTERIOR.split(" at R")[0]); ok &= _m == [round(100*max(dev[f]), 1) for f in FR]
_m = _nums(S_INTERIOR.split("against ")[1].split("% to")[0]); ok &= len(_m) == 1 and _m[0] == round(100*min(con), 1) and _ints(S_INTERIOR.split("% to ")[1].split("%")[0]) == [round(100*max(con))]
_m = _nums(S_PROFILE.split("; the window")[0]); ok &= _m == [round(100*max(pw), 1), round(100*max(pw3), 1)] and _ints(S_PROFILE.split("wall ")[-1].split("%")[0]) == [round(100*max(pw8))] and _nums(S_PROFILE.split("stays within ")[1]) == [round(100*max(pw83), 1)] and "fit to 8T₁" in S_PROFILE
_m = _nums(S_R40); ok &= _m == [round(max(e40), 4), round(max(exc), 3), round(max(e40_3), 4)]
_m = _nums(S_EDGE.split("; the deficit")[0]); ok &= _m == [round(mean2[1.0], 2), round(mean2[1.25], 2), 1.25, round(mean2[1.5], 2), 1.5, round(mean2[2.0], 3), round(max2, 2)] and _ints(S_EDGE.split(" rungs with")[0]) == [len(M2)] and _ints(S_EDGE.split("positive at ")[1].split(" at T₁")[0]) == [npos2, len(M2)]
_s = S_EDGE.split("; the deficit")[1].split("; the ")[0]; ok &= _ints(_s.split(" of them")[0]) == [len(SEVEN)] and _s.split("(")[1].split(")")[0] == _cells(SEVEN) and _nums(_s.split("profile’s ")[1]) == [round(min(PRED[key] for key in SEVEN), 2), round(max(PRED[key] for key in SEVEN), 2)]
_t = S_EDGE.split("whole zero at a time: shortfall ")[1]; ok &= _ints(S_EDGE.split("; the ")[2].split(" one-hole")[0]) == [len(M1)] and _nums(_t.split(" at T₁, 1.25")[0]) == [round(mean1[f], 2) for f in (1.0, 1.25, 1.5, 2.0)] and _nums(_t.split("a swing of ")[1].split(" between")[0]) == [round(mean1[1.5] - mean1[2.0], 2)] and _nums(_t.split("there (")[1].split(")")[0]) == [round(min(PRED[key] for key in FIVE), 2), round(max(PRED[key] for key in FIVE), 2)] and _nums(_t.split("as observed (")[1].split(")")[0]) == [round(min(OBS[key] for key in FIVE), 3), round(max(OBS[key] for key in FIVE), 3)] and "rung 2 of every cell" in S_EDGE
_i = _ints(S_BETWEEN.split(", inside")[0]); ok &= _i == [nb, len(W)] and _nums(S_BETWEEN.split("% (")[0])[-1] == round(100*(1 - min(ratk)), 1) and _nums(S_BETWEEN.split("beyond T₁ by ")[1])[0] == round(100*(max(rat1) - 1), 1)
ok &= S_BETWEEN.split("% (")[1].split(")")[0] == _exc(INSIDE) and S_BETWEEN.split("% (")[2].split(")")[0] == _exc(BEYOND)
gate("g6 the paper's numbers parsed back from the declared needles", ok)

# ---------------------------------------------------------------- g7
from cascade_tower import chain_ok
gate("g7 the chain obligation to cascade_rung_anatomy.py (Theorem 1bw) met", chain_ok("cascade_rung_anatomy.py"))

# ---------------------------------------------------------------- g8
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g8 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g8 the 1bx paper needles and the footer census (declared surface)", ok)

print(("ALL GATES PASS (9/9)" if not fails else f"FAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
