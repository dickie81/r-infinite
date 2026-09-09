#!/usr/bin/env python3
"""Theorem 1bv -- the odd sector: the Weil form on the odd probes of the window
is the even form with the multiplier gamma^2 on the zero side and a Dirichlet
condition (ghat = i r Ghat, an identity), its pole term is negative, its
ladder sits at the prolate orders 4k + 2 -- the orders 2 mod 4 that the even
sector cannot reach -- so the two sectors together fill every even prolate
order from 4 on; its ground state's Ghat converges to Riemann's Xi, its hole
zeros sit at the nodes of the orthogonal polynomials of the weight r^2 Ghat_1^2,
and in its anatomy the primes carry the positivity the even sector's pole
carries. Substrates odd_sector.py (keyed producer, seven cells and the
self-test), weil_prime_gram_odd.py (the odd Gram, imported), xi_limit.py (the
Xi side, imported); the even sector's checkpoints through ladder_caster.py
(Theorem 1bu's producer, imported). Tower member 31 (top).

THE CLAIMS GATED. (0) THE ODD FORM as computation: the odd Gram's Q against
the zero side 2 sum |ghat(gamma)|^2 over the 6700 zeros plus the density tail
for an odd bump at delta = 1 and 2, within 1e-12 relative (the self-test cell);
the mangles -- the cosine basis's autocorrelation signs, or the pole with the
even sector's sign, from weil_prime_gram_odd_mangles.py (the odd Gram transcribed with two
switches, its unmangled Gram gated entry for entry against the substrate's) -- miss it by
more than 1e-3 (gated in g0, round-329 sweep F329-4). (1) THE XI SIDE: the odd limits
Ghat_1(0)^2 -> 2 pi Xi(0)^2/int t^2 Xi^2 = 0.0757, sqrt<r^2> -> sqrt(int t^4 Xi^2/
int t^2 Xi^2) = 5.418, the nodes of t^2 Xi^2, the odd anatomy's limits (pole
-0.0383, primes +0.3686, archimedean +5.0418) and, by the same rule, the even
sector's (1.5637, -0.0752, 3.8837: first computed at this landing and pinned here --
Theorem 1bu records no anatomy limits); the archimedean limits computed directly,
(1/2 pi) int |ghat|^2 [Re psi(1/4 + i r/2) - psi(1/4)] dr, against the remainder-defined values. (2) THE ODD
GROUND STATE at the cells: the real-zero census of Ghat_1 (K - 2 designed pairs
plus the sinc zeros; the sum rule; an unlocated pair placed), Hypothesis D_odd
within the dodging tolerance, epsilon falling, Ghat_1(0)^2 rising toward and
below 0.0757, sqrt<r^2> falling toward and above 5.418, the curvature rising
toward and below sum gamma^-2 = 0.023105, the exterior masses beyond T_D/2 and T_D at most 0.05 and 1e-3, falling across the cells down to the evaluation floor (~1e-39). (3) THE ODD
SECTOR'S PLACE IN THE SHADOW: the odd ground state 2 ln T_0 + O(1) above the
even one (odd - even within 1 of 2 ln T_0 at every cell, the excess stated and parsed back);
at every safely deep odd rung (its leakage ln(1 - chi_{2k+1}) < -20; the paper's chi_j = sqrt(lambda_{2j})) the offset
ln lambda_k - ln(1 - chi_{2k+1}) is positive and within 1 of the even sector's
offset at the order 4k (Theorem 1br's shadow, read from Theorem 1bu's
checkpoints); the odd dodging edge inside or at the even one. (4) THE ODD HOLE
ZEROS: k - 1 at every safely deep rung through rung 12; rungs 2-4 within 1% of
the nodes of P_{2(k-1)} for the weight ghat_1^2 at delta >= 2.3 (1.26% at delta = 2); the first hole
zero falling toward and above the Xi-limit 5.418. (5) THE ODD ANATOMY: the
identity lambda_1 = pole + const + archimedean + primes with the archimedean
term from the Gram's own part (1e-9); the pole negative, its magnitude rising
toward and below 0.0383; the primes positive, rising toward and below 0.3686;
the archimedean falling toward and above 5.0418; the prime 2 carrying more
than 0.9 of the primes term. (6) mangle probes: offsets against the orders 4k
instead of 4k + 2 miss by about 2 ln T_0. (7) the paper's numbers parsed back;
(8) the chain obligation to cascade_ladder_caster.py; (9) the needles and census.

WHAT IS NOT CLAIMED. The 2 ln T_0 + O(1) spacing of the sectors is computed,
not proved (the reduction's heuristic is named); the odd hole zeros' law is
computed; no Riemann Hypothesis consequence.
"""
import math, os, sys, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from odd_sector import run as run_OS
from ladder_caster import run as run_LC
import xi_limit as XI

PAPER_NEEDLES = [
    {'g': 'g9', 's': "Theorem 1bv (the odd sector", 'form': 'plain'},
    {'g': 'g9', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 13},
    {'s': '`cascade_odd_sector.py`', 'min': 2, 'g': 'g9'},
    {'s': 'the **98 scripts cited in place** above', 'form': 'ws', 'g': 'g9'},
    {'s': 'extended by Theorems 1i–1bv:', 'form': 'ws', 'g': 'g9'},
    {'g': 'g7', 's': 'at δ = 1 and 2 the odd Gram gives 0.021912748475 and 0.000167771811 against the zero side 0.021912748475 and 0.000167771811', 'form': 'ws'},
    {'g': 'g7', 's': '∫t²Ξ² = 20.5076, ∫t⁴Ξ² = 602.05, 2πΞ(0)²/∫t²Ξ² = 0.07572, √(∫t⁴Ξ²/∫t²Ξ²) = 5.418', 'form': 'ws'},
    {'g': 'g7', 's': 'pole −0.0383, primes +0.3686 (the prime 2 alone +0.3475), archimedean +5.0418; the even sector by the same rule +1.5637, −0.0752, +3.8837', 'form': 'ws'},
    {'g': 'g7', 's': 'odd minus even 5.374, 6.514, 7.781, 8.487, 9.140, 9.995, 11.140 against 2 ln T₀ = 5.676, 6.441, 7.676, 8.276, 8.876, 9.676, 10.676 at the seven cells, the excess −0.302, +0.073, +0.105, +0.211, +0.264, +0.319, +0.464', 'form': 'ws'},
    {'g': 'g7', 's': 'the ground state’s offset against the order 6 +1.22, +1.49, +1.67, +1.77, +1.81, +2.02, +2.22 (the even sector’s against the order 4 +1.64, +1.79, +2.12, +2.18, +2.20, +2.39, +2.47), at δ = 3.5 the rungs 2–6 +1.61, +1.76, +1.43, +1.61, +1.37 against the even +1.87, +1.62, +1.74, +1.29, +1.74', 'form': 'ws'},
    {'g': 'g7', 's': 'the odd edge at 1.23, 1.50, 1.66, 1.77, 1.86, 1.84, 1.93 T₀ against the even 1.46, 1.63, 1.79, 1.77, 1.86, 1.90, 1.94', 'form': 'ws'},
    {'g': 'g7', 's': 'Ĝ₁(0)² = 0.0410, 0.0527, 0.0635, 0.0667, 0.0691, 0.0713, 0.0730 rising toward 0.0757', 'form': 'ws'},
    {'g': 'g7', 's': '√⟨r²⟩ = 6.496, 6.023, 5.705, 5.624, 5.567, 5.516, 5.477 falling toward 5.418', 'form': 'ws'},
    {'g': 'g7', 's': 'the curvature 0.01441, 0.01755, 0.02027, 0.02103, 0.02158, 0.02210, 0.02250 rising toward 0.02310', 'form': 'ws'},
    {'g': 'g7', 's': '5.477; 4.217, 8.580; 3.682, 7.431, 11.492; 3.287, 6.598, 9.980, 16.389 against the nodes 5.477; 4.217, 8.580; 3.681, 7.429, 11.489; 3.286, 6.597, 9.978, 16.384', 'form': 'ws'},
    {'g': 'g7', 's': 'the first hole zero 6.702, 6.049, 5.710, 5.626, 5.568, 5.516, 5.477 falls toward the Ξ-limit 5.418', 'form': 'ws'},
    {'g': 'g7', 's': 'the Ξ-limit nodes of t²Ξ² 5.418; 4.171, 8.499; 3.622, 7.306, 11.232; 3.249, 6.527, 9.888, 16.086', 'form': 'ws'},
    {'g': 'g7', 's': 'pole −0.0206, −0.0266, −0.0321, −0.0337, −0.0349, −0.0360, −0.0369; primes +0.1597, +0.2434, +0.3070, +0.3241, +0.3362, +0.3472, +0.3558; archimedean +5.2333, +5.1554, +5.0973, +5.0818, +5.0709, +5.0610, +5.0533', 'form': 'ws'},
    {'g': 'g7', 's': '0, 0, 3, 5, 9, 11, 11 safely deep odd rungs at the cells', 'form': 'ws'},
    {'g': 'g7', 's': 'all K − 2 designed pairs located at every cell, the sum rule closing within 10⁻¹⁶', 'form': 'ws'},
    {'g': 'g7', 's': 'rung 4 at δ = 2.0 deviates 1.26%', 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ORDER = ["d1.0", "d1.38", "d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
SELF = run_OS("selftest")
ST = {c: run_OS(c) for c in ORDER}
EV = {c: run_LC(c) for c in ORDER}                     # the even sector (Theorem 1bu's checkpoints)
T0 = {c: ST[c]["T0"] for c in ORDER}
G = {c: ST[c]["ground"] for c in ORDER}
SAFE = -20.0
def safe_rungs(c):
    st = ST[c]; pro = st["prolate_ln_leakage"]
    return [r for r in st["rungs"][1:] if 2*r["k"] + 1 < len(pro) and pro[2*r["k"] + 1] is not None and pro[2*r["k"] + 1] < SAFE and r["k"] <= 12]

# ---------------------------------------------------------------- g0
ok = len(SELF["cases"]) == 2
for cs in SELF["cases"]:
    ok &= abs(cs["prime_side_mid"] - cs["zero_side"]) <= 1e-12*abs(cs["zero_side"]) and cs["prime_side_rad"] <= 1e-12*abs(cs["zero_side"])
import mpmath as _mp
import weil_prime_gram_odd as WO
import weil_prime_gram_odd_mangles as WM
from flint import arb as _arb
_a = 0.5; _K = 48; _prec = 400
_bump = lambda t: t*_mp.e**(-1/(1 - (t/_a)**2)) if abs(t) < _a else _mp.mpf(0)
with _mp.workdps(40):
    _cv = [_arb(str(_mp.quad(lambda t: _bump(t)*_mp.sin(k*_mp.pi*t/_a), [-_a, 0, _a])/_a)) for k in range(1, _K)]
_G0, _N0, _ = WO.gram_odd(1.0, _K, _prec)
_Gs, _Ns, _ = WM.gram_odd_mangled(1.0, _K, _prec, None)
_same = WM.same_gram(_G0, _N0, _Gs, _Ns)
_z = SELF["cases"][0]["zero_side"]; _q0 = float(WO.rayleigh_odd(_G0, _N0, _cv, _prec).mid())
_miss = {}
for _mg in ("cosine_signs", "pole_sign"):
    _Gm, _Nm, _ = WM.gram_odd_mangled(1.0, _K, _prec, _mg); _miss[_mg] = abs(float(WO.rayleigh_odd(_Gm, _Nm, _cv, _prec).mid()) - _z)/abs(_z)
ok &= _same and abs(_q0 - SELF["cases"][0]["prime_side_mid"]) <= 1e-12*abs(_z) and all(v > 1e-3 for v in _miss.values())
gate("g0 the odd form as computation: the odd Gram's Q against the zero side (6700 zeros plus the density tail) for an odd bump at delta = 1, 2 -- " + f"; the transcription equal to the substrate entry for entry: {_same}; the mangles at delta = 1 (K = 48) miss the zero side by " + ", ".join(f"{k} {v:.3f}" for k, v in _miss.items()) + " relative -- " + "; ".join(f"delta {cs['delta']}: prime side {cs['prime_side_mid']:.15e}, zero side {cs['zero_side']:.15e}, prime powers {cs['prime_powers']}" for cs in SELF["cases"]) + " (within 1e-12 relative)", ok)

# ---------------------------------------------------------------- g1
XO = XI.constants_odd(); XC = XI.constants(); XNO = XI.nodes_odd(5)
ok = abs(XO["G0sq_limit"] - 0.0757) <= 5e-5 and abs(math.sqrt(XO["r2_mean_odd"]) - 5.418) <= 5e-4
ok &= abs(XO["pole_odd"] + 0.0383) <= 5e-5 and abs(XO["primes_odd"] - 0.3686) <= 5e-5 and abs(XO["arch_odd"] - 5.0418) <= 5e-5
ok &= abs(XO["pole_even"] - 1.5637) <= 5e-5 and abs(XO["primes_even"] + 0.0752) <= 5e-5 and abs(XO["arch_even"] - 3.8837) <= 5e-5     # the even limits by the same rule, pinned at the landing (1bu records none)
ok &= abs(XO["arch_odd_direct"] - XO["arch_odd"]) <= 1e-10 and abs(XO["arch_even_direct"] - XO["arch_even"]) <= 1e-10                          # the archimedean limits directly vs the remainder
ok &= abs(XNO[0][0] - math.sqrt(XO["r2_mean_odd"])) <= 1e-9                                                                            # the first node is sqrt<t^2> (the orthogonality argument)
gate(f"g1 the Xi side of the odd sector: int t^2 Xi^2 = {XO['int_t2_Xi2']:.5f}, int t^4 Xi^2 = {XO['int_t4_Xi2']:.4f}; Ghat_1(0)^2 -> {XO['G0sq_limit']:.5f}; sqrt<r^2> -> {math.sqrt(XO['r2_mean_odd']):.4f}; the odd anatomy's limits pole {XO['pole_odd']:+.4f}, primes {XO['primes_odd']:+.4f} (p = 2: {XO['prime_terms_odd'][0][1]:+.4f}), archimedean {XO['arch_odd']:+.4f}; the even sector's by the same rule {XO['pole_even']:+.4f}, {XO['primes_even']:+.4f}, {XO['arch_even']:+.4f}; the nodes of t^2 Xi^2 " + "; ".join(", ".join(f"{v:.3f}" for v in n) for n in XNO[:4]), ok)

# ---------------------------------------------------------------- g2
ok = True
Z40 = [float(s) for s in json.load(open(os.path.join(HERE, "checkpoints", "zeta_zeros_800_100dps.json")))]; Zb = np.array(Z40)
ZT = Z40[-1]; ztail = (math.log(ZT/(2*math.pi)) + 1)/(2*math.pi*ZT)
def _eps(c):
    g = G[c]; TD = g["first_missed"]
    return (g["kappa"] - g["sum_inv_sq_located_below"]) + float(np.sum(1/Zb[Zb >= TD]**2)) + ztail
for c in ORDER:
    g = G[c]; ok &= g["first_missed"] is not None and g["first_free"] is not None and abs(g["first_missed"] - g["first_free"]) <= 0.3 and g["first_missed"] >= 1.2*T0[c]
    cen = g["n_designed_real"] == g["K_minus_2"] and abs(g["sum_rule_residual"]) <= 1e-16
    cen |= g["n_designed_real"] == g["K_minus_2"] - 1 and g["missing_pair"] is not None and g["missing_pair"]["abs_tau"] >= g["R_ext"] and abs(g["sum_rule_residual"]) >= 1e-9
    ok &= cen and g["n_located_below_edge"] == g["n_zeta_below_edge"] and g["n_dips_census"] == 0
    ok &= g["disp_max"] <= 0.05 and g["disp_term_r3"] <= 1e-4
    ok &= g["mass_beyond"]["TD/2"] <= 0.05 and g["mass_beyond"]["TD"] <= 1e-3                  # the odd ground state is broader than the even (the weight r^2 Ghat^2; T_D = 1.23 T_0 at delta = 1)
mass2 = [G[c]["mass_beyond"]["TD/2"] for c in ORDER]; massD = [G[c]["mass_beyond"]["TD"] for c in ORDER]
ok &= all(mass2[i] > mass2[i + 1] or mass2[i] < 1e-30 for i in range(6)) and all(massD[i] > massD[i + 1] or massD[i] < 1e-30 for i in range(6))   # falling across the cells down to the evaluation floor (~1e-39: the far-field tail term)
eps = [_eps(c) for c in ORDER]; ok &= all(eps[i] > eps[i + 1] for i in range(6)) and eps[-1] > 0
kap = [G[c]["kappa"] for c in ORDER]; g0 = [math.exp(G[c]["ln_G0sq"]) for c in ORDER]; r2 = [math.sqrt(G[c]["r2_mean"]) for c in ORDER]
ok &= all(kap[i] < kap[i + 1] for i in range(6)) and kap[-1] < XC["curvature"]
ok &= all(g0[i] < g0[i + 1] for i in range(6)) and g0[-1] < XO["G0sq_limit"]
ok &= all(r2[i] > r2[i + 1] for i in range(6)) and r2[-1] > math.sqrt(XO["r2_mean_odd"])
gate("g2 the odd ground state at the cells: the census of Ghat_1 (designed pairs located " + ", ".join(f"{G[c]['n_designed_real']}/{G[c]['K_minus_2']}" for c in ORDER) + "; residuals " + ", ".join(f"{G[c]['sum_rule_residual']:.1e}" for c in ORDER) + "; unlocated pairs: " + (", ".join(f"{c}: |tau| = {G[c]['missing_pair']['abs_tau']:.0f} ({'real' if G[c]['missing_pair']['real'] else 'imaginary'})" for c in ORDER if G[c]["missing_pair"] is not None) or "none") + "; located/zeta below the edge " + ", ".join(f"{G[c]['n_located_below_edge']}/{G[c]['n_zeta_below_edge']}" for c in ORDER) + "; no dips); D_odd within the dodging tolerance (displacements at most " + ", ".join(f"{G[c]['disp_max']:.1e}" for c in ORDER) + "); the edge at " + ", ".join(f"{G[c]['first_missed']/T0[c]:.2f}" for c in ORDER) + " T_0; epsilon " + ", ".join(f"{e:.5f}" for e in eps) + " falling; Ghat_1(0)^2 " + ", ".join(f"{v:.4f}" for v in g0) + f" rising toward {XO['G0sq_limit']:.4f}; sqrt<r^2> " + ", ".join(f"{v:.3f}" for v in r2) + f" falling toward {math.sqrt(XO['r2_mean_odd']):.3f}; the curvature " + ", ".join(f"{k:.5f}" for k in kap) + f" rising toward {XC['curvature']:.6f}; the mass beyond T_D/2 " + ", ".join(f"{v:.1e}" for v in mass2) + " and beyond T_D " + ", ".join(f"{v:.1e}" for v in massD) + " (falling)", ok)

# ---------------------------------------------------------------- g3
ok = True; omine = {}; offs = {}
for c in ORDER:
    st = ST[c]; ev = EV[c]; pro = st["prolate_ln_leakage"]
    omine[c] = st["ground"]["ln_lam1"] - ev["ground"]["ln_lam1"]; ok &= abs(omine[c] - 2*math.log(T0[c])) <= 1.0                       # 2 ln T_0 + O(1): the O(1) is stated per cell (the excess) and parsed back
    ok &= st["ground"]["first_missed"] <= ev["ground"]["first_missed"] + 1e-9                           # the odd edge inside or at the even one
    offs[c] = []
    for r in safe_rungs(c):
        o = r["ln_lam"] - pro[2*r["k"] + 1]; ok &= o > 0
        re = next((q for q in ev["rungs"] if q["k"] == r["k"]), None)
        if re is not None and 2*r["k"] < len(pro) and pro[2*r["k"]] is not None:
            oe = re["ln_lam"] - pro[2*r["k"]]; ok &= abs(o - oe) <= 1.0; offs[c].append((r["k"], o, oe))
    o1 = st["ground"]["ln_lam1"] - pro[3]; ok &= o1 > 0 and abs(o1 - (ev["ground"]["ln_lam1"] - pro[2])) <= 1.0
exc = [omine[c] - 2*math.log(T0[c]) for c in ORDER]; ok &= all(exc[i] < exc[i + 1] for i in range(1, 6))    # the excess rising from delta = 1.38 on
gate("g3 the odd sector's place in the shadow: odd - even ground " + ", ".join(f"{omine[c]:.3f}" for c in ORDER) + " against 2 ln T_0 " + ", ".join(f"{2*math.log(T0[c]):.3f}" for c in ORDER) + " (the excess " + ", ".join(f"{e:+.3f}" for e in exc) + "); the odd edge inside or at the even one; at every safely deep odd rung (its own ln(1 - chi_(2k+1)) < -20; " + ", ".join(str(len(safe_rungs(c))) for c in ORDER) + " rungs) the offset against the order 4k + 2 is positive and within 1 of the even sector's at 4k: " + "; ".join(f"{c}: " + ", ".join(f"{o:+.2f}/{oe:+.2f}" for k, o, oe in offs[c]) for c in ORDER if offs[c]), ok)

# ---------------------------------------------------------------- g4
ok = True; worst = 0.0; nsafe = 0
for c in ORDER:
    st = ST[c]
    for r in safe_rungs(c):
        nsafe += 1; ok &= len(r["hole"]) == r["k"] - 1 and max(st["nodes"][r["k"] - 2]) < min(100.0, 0.8*r["edge"])
    if st["delta"] >= 2.3:
        for r in st["rungs"][1:4]:
            nodes = st["nodes"][r["k"] - 2]
            if len(r["hole"]) == len(nodes):
                rel = max(abs(h - n)/n for h, n in zip(r["hole"], nodes)); worst = max(worst, rel); ok &= rel <= 0.01
            else: ok = False
_r20 = ST["d2.0"]["rungs"][3]; _n20 = ST["d2.0"]["nodes"][2]; assert _r20["k"] == 4
_rel20 = max(abs(h - n)/n for h, n in zip(_r20["hole"], _n20)) if len(_r20["hole"]) == len(_n20) else float("nan")
ok &= _rel20 > 0.01                                                                                 # the reason delta = 2.0 is excluded from the 1% gate; its figure is parsed by g7
first = [ST[c]["rungs"][1]["hole"][0] for c in ORDER]; ok &= all(first[i] > first[i + 1] for i in range(6)) and first[-1] > XNO[0][0]
gate(f"g4 the odd hole zeros: every safely deep rung k through rung 12 ({nsafe} rungs over the seven cells) has exactly k - 1, the census region covering the predicted nodes; at delta >= 2.3 rungs 2-4 within 1% of the nodes of P_(2(k-1)) for the weight ghat_1^2 (max relative deviation {worst:.2%}; {_rel20:.2%} at delta = 2.0's rung 4, excluded from the 1% gate and parsed back by g7); the first hole zero " + ", ".join(f"{v:.3f}" for v in first) + f" falling toward the Xi-limit {XNO[0][0]:.3f}", ok)

# ---------------------------------------------------------------- g5
ok = True
for c in ORDER:
    g = G[c]; ok &= abs(g["identity_residual"]) <= 1e-9 and g["pole"] < 0 and g["primes"] > 0 and g["arch"] > 0
    ok &= g["prime_terms"][0][0] == 2 and g["prime_terms"][0][3] >= 0.9*g["primes"]
pol = [-G[c]["pole"] for c in ORDER]; pri = [G[c]["primes"] for c in ORDER]; arc = [G[c]["arch"] for c in ORDER]
ok &= all(pol[i] < pol[i + 1] for i in range(6)) and pol[-1] < -XO["pole_odd"]
ok &= all(pri[i] < pri[i + 1] for i in range(6)) and pri[-1] < XO["primes_odd"]
ok &= all(arc[i] > arc[i + 1] for i in range(6)) and arc[-1] > XO["arch_odd"]
ok &= all(G[c]["arch"] + XO["const"] < 0 for c in ORDER) and XO["arch_odd"] + XO["const"] < 0 and XO["arch_even"] + XO["const"] < 0     # the archimedean term and the constant taken together: negative
gate("g5 the odd anatomy lambda_1 = pole + const + archimedean + primes (the archimedean term from the Gram's own part; the identity within 1e-9): pole " + ", ".join(f"{G[c]['pole']:+.4f}" for c in ORDER) + f" (rising in magnitude toward {XO['pole_odd']:+.4f}); primes " + ", ".join(f"{G[c]['primes']:+.4f}" for c in ORDER) + f" (rising toward {XO['primes_odd']:+.4f}, the prime 2 carrying more than 0.9); archimedean " + ", ".join(f"{G[c]['arch']:+.4f}" for c in ORDER) + f" (falling toward {XO['arch_odd']:+.4f}); const {G['d1.0']['const']:+.4f}", ok)

# ---------------------------------------------------------------- g6
ok = True
for c in ("d2.3", "d3.5"):
    st = ST[c]; pro = st["prolate_ln_leakage"]
    for r in safe_rungs(c)[:3]:
        ok &= abs((r["ln_lam"] - pro[2*r["k"]]) - (r["ln_lam"] - pro[2*r["k"] + 1])) > 1.5*math.log(T0[c]) - 1.0     # the orders 4k miss by about 2 ln T_0
gate("g6 mangle probes: the odd rungs' offsets against the orders 4k instead of 4k + 2 miss by more than 1.5 ln T_0 - 1 at delta = 2.3 and 3.5", ok)

# ---------------------------------------------------------------- g7
import paper_needles
S_SELFTEST = 'at δ = 1 and 2 the odd Gram gives 0.021912748475 and 0.000167771811 against the zero side 0.021912748475 and 0.000167771811'
S_XIODD = '∫t²Ξ² = 20.5076, ∫t⁴Ξ² = 602.05, 2πΞ(0)²/∫t²Ξ² = 0.07572, √(∫t⁴Ξ²/∫t²Ξ²) = 5.418'
S_ANATLIM = 'pole −0.0383, primes +0.3686 (the prime 2 alone +0.3475), archimedean +5.0418; the even sector by the same rule +1.5637, −0.0752, +3.8837'
S_OMINE = 'odd minus even 5.374, 6.514, 7.781, 8.487, 9.140, 9.995, 11.140 against 2 ln T₀ = 5.676, 6.441, 7.676, 8.276, 8.876, 9.676, 10.676 at the seven cells, the excess −0.302, +0.073, +0.105, +0.211, +0.264, +0.319, +0.464'
S_OFFS = 'the ground state’s offset against the order 6 +1.22, +1.49, +1.67, +1.77, +1.81, +2.02, +2.22 (the even sector’s against the order 4 +1.64, +1.79, +2.12, +2.18, +2.20, +2.39, +2.47), at δ = 3.5 the rungs 2–6 +1.61, +1.76, +1.43, +1.61, +1.37 against the even +1.87, +1.62, +1.74, +1.29, +1.74'
S_EDGE = 'the odd edge at 1.23, 1.50, 1.66, 1.77, 1.86, 1.84, 1.93 T₀ against the even 1.46, 1.63, 1.79, 1.77, 1.86, 1.90, 1.94'
S_G0 = 'Ĝ₁(0)² = 0.0410, 0.0527, 0.0635, 0.0667, 0.0691, 0.0713, 0.0730 rising toward 0.0757'
S_R2 = '√⟨r²⟩ = 6.496, 6.023, 5.705, 5.624, 5.567, 5.516, 5.477 falling toward 5.418'
S_KAPPA = 'the curvature 0.01441, 0.01755, 0.02027, 0.02103, 0.02158, 0.02210, 0.02250 rising toward 0.02310'
S_HOLE35 = '5.477; 4.217, 8.580; 3.682, 7.431, 11.492; 3.287, 6.598, 9.980, 16.389 against the nodes 5.477; 4.217, 8.580; 3.681, 7.429, 11.489; 3.286, 6.597, 9.978, 16.384'
S_FIRST = 'the first hole zero 6.702, 6.049, 5.710, 5.626, 5.568, 5.516, 5.477 falls toward the Ξ-limit 5.418'
S_XINODES = 'the Ξ-limit nodes of t²Ξ² 5.418; 4.171, 8.499; 3.622, 7.306, 11.232; 3.249, 6.527, 9.888, 16.086'
S_ANAT = 'pole −0.0206, −0.0266, −0.0321, −0.0337, −0.0349, −0.0360, −0.0369; primes +0.1597, +0.2434, +0.3070, +0.3241, +0.3362, +0.3472, +0.3558; archimedean +5.2333, +5.1554, +5.0973, +5.0818, +5.0709, +5.0610, +5.0533'
S_NSAFE = '0, 0, 3, 5, 9, 11, 11 safely deep odd rungs at the cells'
S_CENSUS = 'all K − 2 designed pairs located at every cell, the sum rule closing within 10⁻¹⁶'
S_NODE20 = 'rung 4 at δ = 2.0 deviates 1.26%'
# each call carries its literal (the precheck's clause D); the strings equal the S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, 'at δ = 1 and 2 the odd Gram gives 0.021912748475 and 0.000167771811 against the zero side 0.021912748475 and 0.000167771811', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '∫t²Ξ² = 20.5076, ∫t⁴Ξ² = 602.05, 2πΞ(0)²/∫t²Ξ² = 0.07572, √(∫t⁴Ξ²/∫t²Ξ²) = 5.418', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'pole −0.0383, primes +0.3686 (the prime 2 alone +0.3475), archimedean +5.0418; the even sector by the same rule +1.5637, −0.0752, +3.8837', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'odd minus even 5.374, 6.514, 7.781, 8.487, 9.140, 9.995, 11.140 against 2 ln T₀ = 5.676, 6.441, 7.676, 8.276, 8.876, 9.676, 10.676 at the seven cells, the excess −0.302, +0.073, +0.105, +0.211, +0.264, +0.319, +0.464', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the ground state’s offset against the order 6 +1.22, +1.49, +1.67, +1.77, +1.81, +2.02, +2.22 (the even sector’s against the order 4 +1.64, +1.79, +2.12, +2.18, +2.20, +2.39, +2.47), at δ = 3.5 the rungs 2–6 +1.61, +1.76, +1.43, +1.61, +1.37 against the even +1.87, +1.62, +1.74, +1.29, +1.74', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the odd edge at 1.23, 1.50, 1.66, 1.77, 1.86, 1.84, 1.93 T₀ against the even 1.46, 1.63, 1.79, 1.77, 1.86, 1.90, 1.94', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'Ĝ₁(0)² = 0.0410, 0.0527, 0.0635, 0.0667, 0.0691, 0.0713, 0.0730 rising toward 0.0757', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '√⟨r²⟩ = 6.496, 6.023, 5.705, 5.624, 5.567, 5.516, 5.477 falling toward 5.418', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the curvature 0.01441, 0.01755, 0.02027, 0.02103, 0.02158, 0.02210, 0.02250 rising toward 0.02310', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '5.477; 4.217, 8.580; 3.682, 7.431, 11.492; 3.287, 6.598, 9.980, 16.389 against the nodes 5.477; 4.217, 8.580; 3.681, 7.429, 11.489; 3.286, 6.597, 9.978, 16.384', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the first hole zero 6.702, 6.049, 5.710, 5.626, 5.568, 5.516, 5.477 falls toward the Ξ-limit 5.418', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the Ξ-limit nodes of t²Ξ² 5.418; 4.171, 8.499; 3.622, 7.306, 11.232; 3.249, 6.527, 9.888, 16.086', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'pole −0.0206, −0.0266, −0.0321, −0.0337, −0.0349, −0.0360, −0.0369; primes +0.1597, +0.2434, +0.3070, +0.3241, +0.3362, +0.3472, +0.3558; archimedean +5.2333, +5.1554, +5.0973, +5.0818, +5.0709, +5.0610, +5.0533', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '0, 0, 3, 5, 9, 11, 11 safely deep odd rungs at the cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'all K − 2 designed pairs located at every cell, the sum rule closing within 10⁻¹⁶', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'rung 4 at δ = 2.0 deviates 1.26%', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g7'] == [S_SELFTEST, S_XIODD, S_ANATLIM, S_OMINE, S_OFFS, S_EDGE, S_G0, S_R2, S_KAPPA, S_HOLE35, S_FIRST, S_XINODES, S_ANAT, S_NSAFE, S_CENSUS, S_NODE20]
_re = __import__("re")
def _num(s): return float(s.strip().replace('−', '-'))
def _nums(s, pat=r"([-−]?[0-9]+\.[0-9]+)"): return [_num(x) for x in _re.findall(pat, s)]
_m = _nums(S_SELFTEST, r"([0-9]+\.[0-9]{12})"); ok &= len(_m) == 4 and all(abs(x - v) <= 5e-13 + 1e-15 for x, v in zip(_m, [SELF["cases"][0]["prime_side_mid"], SELF["cases"][1]["prime_side_mid"], SELF["cases"][0]["zero_side"], SELF["cases"][1]["zero_side"]]))
_m = _nums(S_XIODD); ok &= len(_m) == 4 and abs(_m[0] - XO["int_t2_Xi2"]) <= 5e-5 + 1e-9 and abs(_m[1] - XO["int_t4_Xi2"]) <= 5e-3 + 1e-9 and abs(_m[2] - XO["G0sq_limit"]) <= 5e-6 + 1e-9 and abs(_m[3] - math.sqrt(XO["r2_mean_odd"])) <= 5e-4 + 1e-9
_m = _nums(S_ANATLIM); _v = [XO["pole_odd"], XO["primes_odd"], XO["prime_terms_odd"][0][1], XO["arch_odd"], XO["pole_even"], XO["primes_even"], XO["arch_even"]]; ok &= len(_m) == 7 and all(abs(x - v) <= 5e-5 + 1e-9 for x, v in zip(_m, _v))
_m = _nums(S_OMINE); _v = [omine[c] for c in ORDER] + [2*math.log(T0[c]) for c in ORDER] + exc; ok &= len(_m) == 21 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m, _v))
_o1 = [G[c]["ln_lam1"] - ST[c]["prolate_ln_leakage"][3] for c in ORDER]; _e1 = [EV[c]["ground"]["ln_lam1"] - ST[c]["prolate_ln_leakage"][2] for c in ORDER]
_m = _nums(S_OFFS.replace("δ = 3.5", "")); _v = _o1 + _e1 + [o for k, o, oe in offs["d3.5"][:5]] + [oe for k, o, oe in offs["d3.5"][:5]]; ok &= len(_m) == 24 and all(abs(x - v) <= 5e-3 + 1e-9 for x, v in zip(_m, _v))
_m = _nums(S_EDGE); _v = [G[c]["first_missed"]/T0[c] for c in ORDER] + [EV[c]["ground"]["first_missed"]/T0[c] for c in ORDER]; ok &= len(_m) == 14 and all(abs(x - v) <= 5e-3 + 1e-9 for x, v in zip(_m, _v))
_m = _nums(S_G0); ok &= len(_m) == 8 and all(abs(x - v) <= 5e-5 + 1e-9 for x, v in zip(_m[:7], g0)) and abs(_m[7] - XO["G0sq_limit"]) <= 5e-5 + 1e-9
_m = _nums(S_R2); ok &= len(_m) == 8 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m[:7], r2)) and abs(_m[7] - math.sqrt(XO["r2_mean_odd"])) <= 5e-4 + 1e-9
_m = _nums(S_KAPPA); ok &= len(_m) == 8 and all(abs(x - v) <= 5e-6 + 1e-9 for x, v in zip(_m[:7], kap)) and abs(_m[7] - XC["curvature"]) <= 5e-6 + 1e-9
_m = _nums(S_HOLE35.split(" against the nodes ")[0]) + _nums(S_HOLE35.split(" against the nodes ")[1]); _h = [v for r in ST["d3.5"]["rungs"][1:5] for v in r["hole"]] + [v for n in ST["d3.5"]["nodes"][:4] for v in n]
ok &= len(_m) == 20 and len(_h) == 20 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m, _h))
_m = _nums(S_FIRST); ok &= len(_m) == 8 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m[:7], first)) and abs(_m[7] - XNO[0][0]) <= 5e-4 + 1e-9
_m = _nums(S_XINODES); _x = [v for n in XNO[:4] for v in n]; ok &= len(_m) == 10 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m, _x))
_m = _nums(S_ANAT); _v = [G[c]["pole"] for c in ORDER] + [G[c]["primes"] for c in ORDER] + [G[c]["arch"] for c in ORDER]; ok &= len(_m) == 21 and all(abs(x - v) <= 5e-5 + 1e-9 for x, v in zip(_m, _v))
_m = _nums(S_NODE20.split("deviates")[1]); ok &= len(_m) == 1 and abs(_m[0] - 100*_rel20) <= 5e-3 + 1e-9
_ns = [int(x) for x in _re.findall(r"[0-9]+", S_NSAFE.split(" safely")[0])]; ok &= _ns == [len(safe_rungs(c)) for c in ORDER]
_full = [c for c in ORDER if G[c]["n_designed_real"] == G[c]["K_minus_2"]]; _one = [c for c in ORDER if c not in _full]
ok &= ("K − 3" in S_CENSUS) == bool(_one) and ("every cell" in S_CENSUS) == (not _one) and all(abs(int(x) - G[c]["missing_pair"]["abs_tau"]) <= 0.5 + 1e-9 for x, c in zip(_re.findall(r"\|τ\| = ([0-9]+)", S_CENSUS), _one))
gate("g7 the paper's numbers parsed back from the declared needles: the self-test (1e-12), the Xi side's moments and limits, the anatomy's limits (1e-4), odd minus even and the excess (1e-3), the offsets (0.01), the edges (0.01), Ghat_1(0)^2 (1e-4), sqrt<r^2> (1e-3), the curvature (1e-5), the delta = 3.5 hole zeros and nodes (1e-3), the first hole zeros (1e-3), the Xi-limit nodes (1e-3), the anatomy (1e-4), the safe-rung counts, the census", ok)

# ---------------------------------------------------------------- g8
from cascade_tower import chain_ok
gate("g8 the chain obligation to cascade_ladder_caster.py (Theorem 1bu) met", chain_ok("cascade_ladder_caster.py"))

# ---------------------------------------------------------------- g9
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g9 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g9 the 1bv paper needles and the footer census (declared surface)", ok)

print(("ALL GATES PASS (10/10)" if not fails else f"FAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
