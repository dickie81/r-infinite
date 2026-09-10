#!/usr/bin/env python3
"""Theorem 1bw (the excited states' exact anatomy -- the bi-orthogonal law of the hole polynomials and the exterior's Gaussian
correction): the verifier. The tower's member 32 (top); chain obligation to cascade_ladder_caster.py (Theorem 1bu), whose
ladder this block completes at the level of the excited states.

WHAT THE BLOCK CLAIMS. At the cells delta = 2.0, 2.3, 2.6, 3.0, 3.5 and every safely deep rung k (Theorem 1bu's rungs; every
designed pair real, located or placed by the sum rule): ghat_k = ghat_1 H_k C_k with H_k the hole polynomial (k - 1 real pairs) and C_k
the ratio of the remaining zero products; ln C_k(r) = -Dkappa_k r^2 + O(r^4) with Dkappa_k = kappa_k - kappa_1 - sum_h h^-2 an
identity from the sum rules, the accounting [sum_{E_k} - sum_{E_1}] - sum_{freed}; the hole polynomial H_k determined by the
k - 1 bi-orthogonality conditions int ghat_1^2 C_k C_j H_k H_j = 0 (j < k) on the interior [0, T_1/2] (T_1 the
ground state's edge at the hole tolerance 0.2) -- with the exact C's to
the census (E), with the Gaussian truncation and the recursion's own lower polynomials (R) from ghat_1 and the Dkappa's alone,
against the naive nodes (A, the orthogonal polynomials of ghat_1^2, 1bu(iii)); the mangle (the correction's sign flipped) misses;
tau_eff = sqrt((k - 1)/(-Dkappa_k)) between 1.18 and 1.42 T_1 over the safely deep rungs (the observed range, a needle); |Dkappa_2| falling across the cells (the correction falling
toward the Xi-limit, where the orthogonal polynomials of Xi^2 are the law); the shallow rungs beyond the law at delta = 2.3
(rungs 9, 10) with unlocated designed pairs, rung 9's two complex by the touching. Substrates rung_anatomy.py (keyed: the census) and rung_laws.py (keyed on the census:
the laws), both importing ladder_caster.py's helpers.

THE GATES. (0) the census at every cell and safely deep rung: every designed pair real -- located with the sum rule within
1e-13, or exactly one unlocated and placed by a negative remainder (1bu(ii)'s K - 2 branch), the placed pair beyond the census
region or within one census step of a sinc zero (the census's blind spot: two zeros in one cell) -- no dip, exactly k - 1 holes
with the coarse and fine censuses agreeing, one dodging zero per zeta zero below the edge, the rung's edge inside the ground
state's T_1 (the edge at the hole tolerance 0.2; 1bu's T_D at 0.05 lies below it at every cell, 2.9-8.5%) and never outward with k; (0b) at delta = 2.3 the rungs' dodging
zeros against the ground state's by zeta zero (within 1e-12 below gamma = 50-70 at rungs 2-5, 1e-5 below gamma = 40 at rung 8,
the displacement 0.05-0.2 at its largest, above 0.9 of the rung's edge) and rung 9's touching at gamma_1 (no sign change, the complex pair from
the local maximum and the curvature, its 2 Re(tau^-2) the sum rule's remainder); (1) the curvature law: the
accounting residual (the displacements' part) within 1e-5, Dkappa_k < 0 and falling with k, the ratio (-ln C/r^2)/Dkappa at r = 5
within 2e-3 of 1 and at r = 40 within 0.25; (2) the bi-orthogonal law over the safely deep rungs: E within 1e-5, R within 1e-2 and
better than A at every rung, R within 1e-5 at rungs 2-3 and 1e-3 at rungs 2-7 for delta >= 2.3; the mangle worse than R by a
factor 10 at every rung; (3) tau_eff/T_1 in [1.1, 1.5], the observed range a needle; (4) |Dkappa_2| falling across the cells; the interior mass
>= 1 - 1e-6; ghat_1's census product against its direct evaluation on the low interior within 1e-6; (5) the shallow rungs at delta = 2.3: rungs 9 and 10 with unlocated pairs (2 and 8; rung 9's complex by the touching);
(6) every safely deep rung in the producer's law; (7) the paper's numbers parsed back; (8) the chain obligation; (9) the needles and census.

WHAT IS NOT CLAIMED. A derivation of Dkappa_k (the exterior's re-balayage) from the prime side or from the balayage; the law
beyond the safely deep rungs; the odd sector's laws; no Riemann Hypothesis consequence.
"""
import math, os, sys, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rung_anatomy import run as run_RA
from rung_laws import run as run_RL
from ladder_caster import run as run_LC

PAPER_NEEDLES = [
    {'g': 'g9', 's': "Theorem 1bw (the excited states", 'form': 'plain'},
    {'g': 'g9', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 14},
    {'s': '`cascade_rung_anatomy.py`', 'min': 2, 'g': 'g9'},
    {'s': 'the **99 scripts cited in place** above', 'form': 'ws', 'g': 'g9'},
    {'s': 'extended by Theorems 1i–1bw:', 'form': 'ws', 'g': 'g9'},
    {'g': 'g7', 's': '3, 6, 9, 11, 11 safely deep rungs at δ = 2, 2.3, 2.6, 3, 3.5', 'form': 'ws'},
    {'g': 'g7', 's': 'all 159, 259, 319, 399, 539 designed pairs located at every safely deep rung but rung 3 at δ = 3 (398 of 399, the last placed by the sum rule at |τ| = 1470, 0.048 below the sinc zero ω_702 inside one census cell) and every rung at δ = 3.5 (538 of 539, the last placed by the sum rule at |τ| between 8688 and 14501, beyond the region 7741) — 1bu(ii)’s branch', 'form': 'ws'},
    {'g': 'g7', 's': 'T₁ = 121.4 at δ = 2.3 against 1bu’s T_D = 111.0; T_D below T₁ by 2.9–8.5% over the five cells', 'form': 'ws'},
    {'g': 'g7', 's': 'the rungs’ edges 121.4, 111.9, 111.0, 105.4, 103.7, 94.7, 87.4 for rungs 1–7 at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'shared with the ground state’s within 10⁻¹² below γ = 69.5, 65.1, 59.3, 49.8 at rungs 2–5 and within 2.7 × 10⁻⁶ below γ = 40 at rung 8, the difference largest near the rung’s edge (above 0.9 of it), 0.11, 0.11, 0.16, 0.18, 0.08, 0.11, 0.09 at rungs 2–8 (δ = 2.3)', 'form': 'ws'},
    {'g': 'g7', 's': 'at δ = 2.3 38 + 0 + 221; 34 + 1 + 224; 33 + 2 + 224; 31 + 3 + 225 for rungs 1–4', 'form': 'ws'},
    {'g': 'g7', 's': 'rungs 9 and 10 (ln λ = −5.14, −0.67) leave 2 and 8 pairs unlocated; at rung 9 the two are complex — the hole zero has met the dodging zero at γ₁: ĝ₉ rises to −7.5 × 10⁻⁴ at r = 14.145 with no sign change on [13.9, 14.3], the pair 14.145 ± 0.081i, whose 2Re(τ⁻²) is the sum rule’s remainder to four digits', 'form': 'ws'},
    {'g': 'g7', 's': 'the accounting residual within 2.7 × 10⁻⁶ at every safely deep rung', 'form': 'ws'},
    {'g': 'g7', 's': '−Δκ_k = 3.49 × 10⁻⁵, 7.87 × 10⁻⁵, 1.21 × 10⁻⁴, 1.70 × 10⁻⁴, 2.20 × 10⁻⁴, 2.87 × 10⁻⁴ for rungs 2–7 at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'τ_eff = 1.40, 1.31, 1.30, 1.26, 1.24, 1.19 T₁ at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'between 1.18 and 1.42 T₁ over the safely deep rungs of the five cells', 'form': 'ws'},
    {'g': 'g7', 's': 'the ratio 1.049, 1.053, 1.056, 1.058, 1.062, 1.069 at r = 40 for rungs 2–7 at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'the interior carrying 1.000000, 1.000000, 1.000000, 1.000000, 1.000000 of the ground state’s mass', 'form': 'ws'},
    {'g': 'g7', 's': 'E within 1.2 × 10⁻⁸, 1.7 × 10⁻⁸, 2.0 × 10⁻⁸, 2.2 × 10⁻⁸, 2.5 × 10⁻⁸, 2.3 × 10⁻⁸ for rungs 2–7 at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'R within 6.1 × 10⁻⁷, 4.0 × 10⁻⁶, 2.7 × 10⁻⁵, 9.9 × 10⁻⁵, 2.9 × 10⁻⁴, 9.6 × 10⁻⁴ against the naive nodes’ 3.6 × 10⁻⁴, 1.1 × 10⁻³, 2.8 × 10⁻³, 6.9 × 10⁻³, 1.2 × 10⁻², 2.4 × 10⁻² for rungs 2–7 at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'the mangle’s 7.2 × 10⁻⁴, 2.2 × 10⁻³, 5.5 × 10⁻³, 1.4 × 10⁻², 2.2 × 10⁻², 4.9 × 10⁻² at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'E within 3.4 × 10⁻⁸ and R within 1.2 × 10⁻³ at every safely deep rung at every cell', 'form': 'ws'},
    {'g': 'g7', 's': 'the producer’s law extends beyond the safely deep rungs to 4, 7, 11, 12, 12 rungs, over which E is within 8.9 × 10⁻⁶ and R within 5.7 × 10⁻³', 'form': 'ws'},
    {'g': 'g7', 's': '−Δκ₂ = 6.52 × 10⁻⁵, 3.49 × 10⁻⁵, 1.80 × 10⁻⁵, 8.16 × 10⁻⁶, 3.20 × 10⁻⁶ at the five cells', 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ORDER = ["d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
CEN = {c: run_RA(c) for c in ORDER}
LAW = {c: run_RL(c) for c in ORDER}
EV = {c: run_LC(c) for c in ORDER}                     # Theorem 1bu's checkpoints: the safely deep counts
SAFE = -20.0
def n_safe(c):
    st = EV[c]; pro = st["prolate_ln_leakage"]
    return len([r for r in st["rungs"][1:] if 2*r["k"] < len(pro) and pro[2*r["k"]] is not None and pro[2*r["k"]] < SAFE and r["k"] <= 12])
def in_law(c): return [L for L in LAW[c]["laws"] if L["k"] <= n_safe(c) + 1]

# ---------------------------------------------------------------- g0
ok = True; cnt = {}; placed = {}
for c in ORDER:
    R = CEN[c]["rungs"]; g1 = R[0]; ns = n_safe(c); cnt[c] = ns
    a_ = CEN[c]["delta"]/2
    def whole(r):   # every pair located and the sum rule closing, or 1bu(ii)'s K - 2 branch: one pair placed by a negative remainder,
                    # the placed pair beyond the census region or (the census's blind spot) within one census step of a sinc zero
        if r["n_complex"] == 0 and abs(r["sum_rule_residual"]) <= 1e-13: return True
        if r["n_complex"] == 1 and r["sum_rule_residual"] < 0:
            t = abs(r["sum_rule_residual"])**-0.5; j = round(t/(math.pi/a_))
            return t >= r["R_ext"] or (j >= CEN[c]["K"] and abs(t - j*math.pi/a_) <= 0.05)
        return False
    ok &= whole(g1) and g1["n_dips"] == 0 and len(g1["holes_fine"]) == 0 and len(g1["holes"]) == 0
    ok &= EV[c]["ground"]["first_missed"] < g1["edge"]                                             # 1bu's T_D (tolerance 0.05) below T_1 (tolerance 0.2)
    for r in R[1:ns + 1]:
        ok &= whole(r) and r["n_dips"] == 0
        ok &= len(r["holes"]) == r["k"] - 1 and len(r["holes_fine"]) == r["k"] - 1 and max(abs(x - y) for x, y in zip(sorted(r["holes"]), sorted(r["holes_fine"]))) <= 1e-12   # the k - 1 holes, the coarse and the fine census agreeing (float refinement, 1e-13)
        ok &= len(r["dodging"]) == r["n_zeta_below_edge"]                                             # one dodging zero per zeta zero below the edge
        ok &= len(r["dodging"]) + len(r["holes"]) + len(r["exterior"]) + r["n_complex"] == r["K_minus_1"] and r["edge"] <= g1["edge"] + 1e-9
    ok &= all(R[i + 1]["edge"] <= R[i]["edge"] + 1e-9 for i in range(ns))                          # never outward with k over the safely deep rungs
    placed[c] = [(r["k"], abs(r["sum_rule_residual"])**-0.5) for r in R[:ns + 1] if r["n_complex"] == 1 and r["sum_rule_residual"] < 0]
gate("g0 the census at every cell and safely deep rung (" + ", ".join(f"{c}: {cnt[c]}" for c in ORDER) + "): every designed pair real -- located with the sum rule within 1e-13, or one placed by a negative remainder beyond the region or within one census step of a sinc zero (" + "; ".join(f"{c}: " + (", ".join(f"rung {k} at |tau| = {t:.0f}" for k, t in placed[c]) or "none") for c in ORDER) + ") -- no dip, exactly k - 1 holes with the coarse and fine censuses agreeing, one dodging zero per zeta zero below the edge, the edge inside the ground state's T_1 (its edge at the hole tolerance 0.2) and never outward with k", ok)

# ---------------------------------------------------------------- g0b: the shared dodging zeros and rung 9's touching at delta = 2.3
c23 = CEN["d2.3"]["rungs"]; D1 = {round(g_, 9): z for g_, z in c23[0]["dodging"]}; SH = {}
for r in c23[1:8]:
    Dk = {round(g_, 9): z for g_, z in r["dodging"]}; diffs = [(g_, abs(Dk[g_] - D1[g_])) for g_ in Dk if g_ in D1]
    SH[r["k"]] = {"first": next((g_ for g_, d in diffs if d > 1e-12), None), "max": max(d for _, d in diffs), "low40": max(d for g_, d in diffs if g_ < 40), "n": len(diffs),
                  "arg": max(diffs, key=lambda t: t[1])[0]/r["edge"]}
ok = all(SH[k]["n"] == len(c23[k - 1]["dodging"]) for k in SH)                       # every dodging zero of the rung has the ground state's counterpart
ok &= all(SH[k]["low40"] <= 1e-12 for k in (2, 3, 4, 5)) and SH[8]["low40"] <= 1e-5 and all(SH[k]["first"] is not None and SH[k]["first"] >= 40 for k in (2, 3, 4, 5))
ok &= all(0.05 <= SH[k]["max"] <= 0.2 and SH[k]["arg"] >= 0.9 for k in SH)              # the largest displacement 0.08-0.18, above 0.9 of the rung's edge
def _shared_sentence():
    return ("shared with the ground state’s within 10⁻¹² below γ = " + ", ".join(f"{SH[k]['first']:.1f}" for k in (2, 3, 4, 5)) + " at rungs 2–5 and within " + _sci_str(SH[8]["low40"]) +
            " below γ = 40 at rung 8, the difference largest near the rung’s edge (above 0.9 of it), " + ", ".join(f"{SH[k]['max']:.2f}" for k in range(2, 9)) + " at rungs 2–8 (δ = 2.3)")
def _sci_str(v):
    m, e = f"{v:.1e}".split("e"); return f"{m} × 10" + str(int(e)).translate(str.maketrans("0123456789-", "⁰¹²³⁴⁵⁶⁷⁸⁹⁻"))
_K23 = CEN["d2.3"]["K"]; _a23 = CEN["d2.3"]["delta"]/2; _om23 = np.arange(_K23)*np.pi/_a23
def _gh23(v, r): sg = np.array([v[k] if k % 2 == 0 else -v[k] for k in range(_K23)]); return 2*np.sin(r*_a23)*np.sum(sg*r/(r*r - _om23*_om23))
_xs = np.arange(13.9, 14.3, 1e-4); _ys = np.array([_gh23(CEN["d2.3"]["vecs"][8], x) for x in _xs]); _i = int(np.argmax(_ys))
_curv = (_ys[_i + 10] - 2*_ys[_i] + _ys[_i - 10])/(1e-3)**2; _y = (abs(_ys[_i])/(abs(_curv)/2))**0.5; _x = float(_xs[_i])
_re2 = 2*(_x*_x - _y*_y)/(_x*_x + _y*_y)**2
T9 = {"max": float(_ys[_i]), "x": _x, "y": _y, "sign_changes": int(np.sum(np.sign(_ys[1:]) != np.sign(_ys[:-1]))), "re2_match": abs(_re2 + c23[8]["sum_rule_residual"]) <= 5e-4*abs(c23[8]["sum_rule_residual"])}
ok &= T9["max"] < 0 and T9["sign_changes"] == 0 and _curv < 0 and abs(_x - CEN["d2.3"]["gamma1"]) <= 0.05 and T9["re2_match"]
gate("g0b the shared dodging zeros at delta = 2.3 (rung k's against the ground state's, by zeta zero): within 1e-12 below gamma = " + ", ".join(f"{SH[k]['first']:.1f}" for k in (2, 3, 4, 5)) + " at rungs 2-5, within 1e-5 below gamma = 40 at rung 8, the largest displacement above 0.9 of the rung's edge, " + ", ".join(f"{SH[k]['max']:.2f}" for k in range(2, 9)) + f" at rungs 2-8; rung 9's touching at gamma_1: ghat_9 rises to {T9['max']:.2e} at r = {_x:.3f} with no sign change, the complex pair {_x:.3f} +- {_y:.3f}i whose 2 Re(tau^-2) is the sum rule's remainder to four digits", ok)

# ---------------------------------------------------------------- g1
ok = True
for c in ORDER:
    Ls = in_law(c); dks = [L["Dkappa"] for L in Ls]
    ok &= all(L["accounting_residual"] is not None and abs(L["accounting_residual"]) <= 1e-5 for L in Ls)
    ok &= all(dk < 0 for dk in dks) and all(dks[i] > dks[i + 1] for i in range(len(dks) - 1))
    ok &= all(abs(L["ratio_r"]["5.0"] - 1) <= 2e-3 and abs(L["ratio_r"]["40.0"] - 1) <= 0.25 for L in Ls)
gate("g1 the curvature law ln C_k = -Dkappa_k r^2 + O(r^4): the accounting residual within 1e-5, Dkappa_k < 0 falling with k, the ratio at r = 5 within 2e-3 of 1 and at r = 40 within 0.25 -- " +
     "; ".join(f"{c}: Dkappa " + ", ".join(f"{L['Dkappa']:+.2e}" for L in in_law(c)) + " (ratio r=40 " + ", ".join(f"{L['ratio_r']['40.0']:.3f}" for L in in_law(c)) + ")" for c in ORDER), ok)

# ---------------------------------------------------------------- g2
ok = True
for c in ORDER:
    for L in in_law(c):
        ok &= L["dev_E"] is not None and L["dev_E"] <= 1e-5 and L["complex_E"] == 0
        ok &= L["dev_R"] is not None and L["dev_R"] <= 1e-2 and L["dev_A"] is not None and L["dev_R"] < L["dev_A"] and L["complex_R"] == 0
        ok &= L["dev_M"] is not None and L["dev_M"] >= 10*L["dev_R"]
        if CEN[c]["delta"] >= 2.3 and L["k"] <= 3: ok &= L["dev_R"] <= 1e-5
        if CEN[c]["delta"] >= 2.3 and L["k"] <= 7: ok &= L["dev_R"] <= 1e-3
gate("g2 the bi-orthogonal law: with the exact corrections the holes within 1e-5 (E); with the Gaussian corrections and the recursion's own lower polynomials within 1e-2 and better than the naive nodes at every rung, within 1e-5 at rungs 2-3 and 1e-3 at rungs 2-7 for delta >= 2.3 (R); the sign-flipped mangle worse by 10 -- " +
     "; ".join(f"{c}: E " + ", ".join(f"{L['dev_E']:.0e}" for L in in_law(c)) + " | R " + ", ".join(f"{L['dev_R']:.0e}" for L in in_law(c)) + " | A " + ", ".join(f"{L['dev_A']:.0e}" for L in in_law(c)) for c in ORDER), ok)

# ---------------------------------------------------------------- g3
ok = True
for c in ORDER:
    TD = CEN[c]["rungs"][0]["edge"]
    ok &= all(L["tau_eff"] is not None and 1.1 <= L["tau_eff"]/TD <= 1.5 for L in in_law(c))
TAU_R = [L["tau_eff"]/CEN[c]["rungs"][0]["edge"] for c in ORDER for L in in_law(c)]
gate(f"g3 tau_eff = sqrt((k - 1)/(-Dkappa_k)) between 1.1 and 1.5 T_1 at every safely deep rung (observed {min(TAU_R):.2f}-{max(TAU_R):.2f}) -- " + "; ".join(f"{c}: " + ", ".join(f"{L['tau_eff']/CEN[c]['rungs'][0]['edge']:.2f}" for L in in_law(c)) for c in ORDER), ok)

# ---------------------------------------------------------------- g4
dk2 = [-LAW[c]["laws"][0]["Dkappa"] for c in ORDER]
ok = all(dk2[i] > dk2[i + 1] for i in range(len(dk2) - 1)) and all(LAW[c]["mass_interior"] >= 1 - 1e-6 for c in ORDER)
ok &= all(LAW[c]["g1_product_check"] <= 1e-6 for c in ORDER)       # ghat_1 from its census against the direct evaluation on the low interior (ln ghat_1^2 within 1e-6)
gate("g4 |Dkappa_2| falling across the cells " + ", ".join(f"{v:.2e}" for v in dk2) + " (the correction falling toward the Xi-limit); the interior [0, T_1/2] carrying " + ", ".join(f"{LAW[c]['mass_interior']:.5f}" for c in ORDER) + " of the ground state's mass; ghat_1 from its census against the direct evaluation within " + ", ".join(f"{LAW[c]['g1_product_check']:.0e}" for c in ORDER) + " in ln ghat_1^2 on the low interior", ok)

# ---------------------------------------------------------------- g5
R23 = CEN["d2.3"]["rungs"]
ok = len(R23) >= 10 and R23[8]["n_complex"] == 2 and R23[9]["n_complex"] == 8 and all(r["n_complex"] == 0 for r in R23[:8])
gate(f"g5 the shallow rungs at delta = 2.3 beyond the law: rungs 9 and 10 leave {R23[8]['n_complex']} and {R23[9]['n_complex']} designed pairs unlocated (ln lambda {R23[8]['ln_lam']:.2f}, {R23[9]['ln_lam']:.2f}; rung 9's two complex by g0b's touching); rungs 1-8 all real", ok)

# ---------------------------------------------------------------- g6
ok = all(LAW[c]["n_in_law"] >= n_safe(c) for c in ORDER)
gate("g6 every safely deep rung is in the producer's law (the producer's whole-census rungs " + ", ".join(str(LAW[c]["n_in_law"]) for c in ORDER) + " against the safely deep " + ", ".join(str(n_safe(c)) for c in ORDER) + "; the block's bounds are stated over the safely deep rungs, the extension reported)", ok)

# ---------------------------------------------------------------- g7
import paper_needles
S_SAFE = '3, 6, 9, 11, 11 safely deep rungs at δ = 2, 2.3, 2.6, 3, 3.5'
S_LOCATED = 'all 159, 259, 319, 399, 539 designed pairs located at every safely deep rung but rung 3 at δ = 3 (398 of 399, the last placed by the sum rule at |τ| = 1470, 0.048 below the sinc zero ω_702 inside one census cell) and every rung at δ = 3.5 (538 of 539, the last placed by the sum rule at |τ| between 8688 and 14501, beyond the region 7741) — 1bu(ii)’s branch'
S_T1 = 'T₁ = 121.4 at δ = 2.3 against 1bu’s T_D = 111.0; T_D below T₁ by 2.9–8.5% over the five cells'
S_EDGES = 'the rungs’ edges 121.4, 111.9, 111.0, 105.4, 103.7, 94.7, 87.4 for rungs 1–7 at δ = 2.3'
S_SHARED = 'shared with the ground state’s within 10⁻¹² below γ = 69.5, 65.1, 59.3, 49.8 at rungs 2–5 and within 2.7 × 10⁻⁶ below γ = 40 at rung 8, the difference largest near the rung’s edge (above 0.9 of it), 0.11, 0.11, 0.16, 0.18, 0.08, 0.11, 0.09 at rungs 2–8 (δ = 2.3)'
S_ACCT = 'at δ = 2.3 38 + 0 + 221; 34 + 1 + 224; 33 + 2 + 224; 31 + 3 + 225 for rungs 1–4'
S_SHALLOW = 'rungs 9 and 10 (ln λ = −5.14, −0.67) leave 2 and 8 pairs unlocated; at rung 9 the two are complex — the hole zero has met the dodging zero at γ₁: ĝ₉ rises to −7.5 × 10⁻⁴ at r = 14.145 with no sign change on [13.9, 14.3], the pair 14.145 ± 0.081i, whose 2Re(τ⁻²) is the sum rule’s remainder to four digits'
S_ACC = 'the accounting residual within 2.7 × 10⁻⁶ at every safely deep rung'
S_DK23 = '−Δκ_k = 3.49 × 10⁻⁵, 7.87 × 10⁻⁵, 1.21 × 10⁻⁴, 1.70 × 10⁻⁴, 2.20 × 10⁻⁴, 2.87 × 10⁻⁴ for rungs 2–7 at δ = 2.3'
S_TAU = 'τ_eff = 1.40, 1.31, 1.30, 1.26, 1.24, 1.19 T₁ at δ = 2.3'
S_TAURANGE = 'between 1.18 and 1.42 T₁ over the safely deep rungs of the five cells'
S_RATIO = 'the ratio 1.049, 1.053, 1.056, 1.058, 1.062, 1.069 at r = 40 for rungs 2–7 at δ = 2.3'
S_MASS = 'the interior carrying 1.000000, 1.000000, 1.000000, 1.000000, 1.000000 of the ground state’s mass'
S_DEVE = 'E within 1.2 × 10⁻⁸, 1.7 × 10⁻⁸, 2.0 × 10⁻⁸, 2.2 × 10⁻⁸, 2.5 × 10⁻⁸, 2.3 × 10⁻⁸ for rungs 2–7 at δ = 2.3'
S_DEVR = 'R within 6.1 × 10⁻⁷, 4.0 × 10⁻⁶, 2.7 × 10⁻⁵, 9.9 × 10⁻⁵, 2.9 × 10⁻⁴, 9.6 × 10⁻⁴ against the naive nodes’ 3.6 × 10⁻⁴, 1.1 × 10⁻³, 2.8 × 10⁻³, 6.9 × 10⁻³, 1.2 × 10⁻², 2.4 × 10⁻² for rungs 2–7 at δ = 2.3'
S_DEVM = 'the mangle’s 7.2 × 10⁻⁴, 2.2 × 10⁻³, 5.5 × 10⁻³, 1.4 × 10⁻², 2.2 × 10⁻², 4.9 × 10⁻² at δ = 2.3'
S_WORST = 'E within 3.4 × 10⁻⁸ and R within 1.2 × 10⁻³ at every safely deep rung at every cell'
S_EXT = 'the producer’s law extends beyond the safely deep rungs to 4, 7, 11, 12, 12 rungs, over which E is within 8.9 × 10⁻⁶ and R within 5.7 × 10⁻³'
S_DK2 = '−Δκ₂ = 6.52 × 10⁻⁵, 3.49 × 10⁻⁵, 1.80 × 10⁻⁵, 8.16 × 10⁻⁶, 3.20 × 10⁻⁶ at the five cells'
# each call carries its literal (the precheck's clause D); the strings equal the S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, '3, 6, 9, 11, 11 safely deep rungs at δ = 2, 2.3, 2.6, 3, 3.5', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'all 159, 259, 319, 399, 539 designed pairs located at every safely deep rung but rung 3 at δ = 3 (398 of 399, the last placed by the sum rule at |τ| = 1470, 0.048 below the sinc zero ω_702 inside one census cell) and every rung at δ = 3.5 (538 of 539, the last placed by the sum rule at |τ| between 8688 and 14501, beyond the region 7741) — 1bu(ii)’s branch', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'T₁ = 121.4 at δ = 2.3 against 1bu’s T_D = 111.0; T_D below T₁ by 2.9–8.5% over the five cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the rungs’ edges 121.4, 111.9, 111.0, 105.4, 103.7, 94.7, 87.4 for rungs 1–7 at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'shared with the ground state’s within 10⁻¹² below γ = 69.5, 65.1, 59.3, 49.8 at rungs 2–5 and within 2.7 × 10⁻⁶ below γ = 40 at rung 8, the difference largest near the rung’s edge (above 0.9 of it), 0.11, 0.11, 0.16, 0.18, 0.08, 0.11, 0.09 at rungs 2–8 (δ = 2.3)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'at δ = 2.3 38 + 0 + 221; 34 + 1 + 224; 33 + 2 + 224; 31 + 3 + 225 for rungs 1–4', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'rungs 9 and 10 (ln λ = −5.14, −0.67) leave 2 and 8 pairs unlocated; at rung 9 the two are complex — the hole zero has met the dodging zero at γ₁: ĝ₉ rises to −7.5 × 10⁻⁴ at r = 14.145 with no sign change on [13.9, 14.3], the pair 14.145 ± 0.081i, whose 2Re(τ⁻²) is the sum rule’s remainder to four digits', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the accounting residual within 2.7 × 10⁻⁶ at every safely deep rung', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '−Δκ_k = 3.49 × 10⁻⁵, 7.87 × 10⁻⁵, 1.21 × 10⁻⁴, 1.70 × 10⁻⁴, 2.20 × 10⁻⁴, 2.87 × 10⁻⁴ for rungs 2–7 at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'τ_eff = 1.40, 1.31, 1.30, 1.26, 1.24, 1.19 T₁ at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'between 1.18 and 1.42 T₁ over the safely deep rungs of the five cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the ratio 1.049, 1.053, 1.056, 1.058, 1.062, 1.069 at r = 40 for rungs 2–7 at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the interior carrying 1.000000, 1.000000, 1.000000, 1.000000, 1.000000 of the ground state’s mass', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'E within 1.2 × 10⁻⁸, 1.7 × 10⁻⁸, 2.0 × 10⁻⁸, 2.2 × 10⁻⁸, 2.5 × 10⁻⁸, 2.3 × 10⁻⁸ for rungs 2–7 at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'R within 6.1 × 10⁻⁷, 4.0 × 10⁻⁶, 2.7 × 10⁻⁵, 9.9 × 10⁻⁵, 2.9 × 10⁻⁴, 9.6 × 10⁻⁴ against the naive nodes’ 3.6 × 10⁻⁴, 1.1 × 10⁻³, 2.8 × 10⁻³, 6.9 × 10⁻³, 1.2 × 10⁻², 2.4 × 10⁻² for rungs 2–7 at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the mangle’s 7.2 × 10⁻⁴, 2.2 × 10⁻³, 5.5 × 10⁻³, 1.4 × 10⁻², 2.2 × 10⁻², 4.9 × 10⁻² at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'E within 3.4 × 10⁻⁸ and R within 1.2 × 10⁻³ at every safely deep rung at every cell', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the producer’s law extends beyond the safely deep rungs to 4, 7, 11, 12, 12 rungs, over which E is within 8.9 × 10⁻⁶ and R within 5.7 × 10⁻³', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '−Δκ₂ = 6.52 × 10⁻⁵, 3.49 × 10⁻⁵, 1.80 × 10⁻⁵, 8.16 × 10⁻⁶, 3.20 × 10⁻⁶ at the five cells', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g7'] == [S_SAFE, S_LOCATED, S_T1, S_EDGES, S_SHARED, S_ACCT, S_SHALLOW, S_ACC, S_DK23, S_TAU, S_TAURANGE, S_RATIO, S_MASS, S_DEVE, S_DEVR, S_DEVM, S_WORST, S_EXT, S_DK2]
_re = __import__("re")
def _num(s): return float(s.strip().replace('−', '-'))
def _nums(s, pat=r"([-−]?[0-9]+\.[0-9]+)"): return [_num(x) for x in _re.findall(pat, s)]
def _ints(s): return [int(x) for x in _re.findall(r"(?<![0-9.])[0-9]+(?![0-9.])", s)]
_SUP = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹⁻", "0123456789-")
def _scis(s):
    """the values printed as m × 10^e with a superscript exponent, in order"""
    return [float(m)*10.0**int(e.translate(_SUP)) for m, e in _re.findall(r"([0-9]+\.?[0-9]*) × 10([⁰¹²³⁴⁵⁶⁷⁸⁹⁻]+)", s)]
def _sci_ok(printed, value):
    """the printed mantissa (1 or 2 significant digits) rounds from the value"""
    if printed == 0 or value == 0: return printed == value
    e = 10.0**__import__("math").floor(__import__("math").log10(abs(printed)))
    digits = len(f"{printed/e:.10g}".replace(".", "").rstrip("0")) or 1
    return abs(printed - value) <= 0.5*e/10**(digits - 1) + 1e-15*abs(value)
_saf = [n_safe(c) for c in ORDER]
ok &= _ints(S_SAFE.split(" safely")[0]) == _saf
_i = _ints(S_EXT.split(" rungs,")[0]); ok &= _i == [LAW[c]["n_in_law"] for c in ORDER]
_v = _scis(S_EXT); ok &= len(_v) == 2 and _sci_ok(_v[0], max(L["dev_E"] for c in ORDER for L in LAW[c]["laws"])) and _sci_ok(_v[1], max(L["dev_R"] for c in ORDER for L in LAW[c]["laws"]))
_m = _nums(S_T1); _pct = [100*(1 - EV[c]["ground"]["first_missed"]/CEN[c]["rungs"][0]["edge"]) for c in ORDER]
ok &= len(_m) == 5 and abs(_m[0] - CEN["d2.3"]["rungs"][0]["edge"]) <= 0.05 + 1e-9 and _m[1] == 2.3 and abs(_m[2] - EV["d2.3"]["ground"]["first_missed"]) <= 0.05 + 1e-9 and abs(_m[3] - min(_pct)) <= 0.05 + 1e-9 and abs(_m[4] - max(_pct)) <= 0.05 + 1e-9 and "over the five cells" in S_T1
ok &= _shared_sentence() == S_SHARED                                   # regenerated from the census, character for character
_m = _nums(S_EDGES.split(" for rungs")[0]); ok &= len(_m) == 7 and all(abs(x - r["edge"]) <= 0.05 + 1e-9 for x, r in zip(_m, CEN["d2.3"]["rungs"][:7]))
_m = _ints(S_ACCT.split("at δ = 2.3 ")[1].split(" for rungs")[0]); ok &= _m == [v for r in CEN["d2.3"]["rungs"][:4] for v in (len(r["dodging"]), len(r["holes"]), len(r["exterior"]))]
_m = _nums(S_SHALLOW.split(") leave")[0]); _i = _ints(S_SHALLOW.split(") leave ")[1].split(" pairs")[0]); _r = CEN["d2.3"]["rungs"]
ok &= len(_m) == 2 and abs(_m[0] - _r[8]["ln_lam"]) <= 5e-3 + 1e-9 and abs(_m[1] - _r[9]["ln_lam"]) <= 5e-3 + 1e-9 and _i[:2] == [_r[8]["n_complex"], _r[9]["n_complex"]]
_v = _scis(S_SHALLOW); _t = _nums(S_SHALLOW.split("rises to")[1])
ok &= len(_v) == 1 and "rises to −" in S_SHALLOW and _sci_ok(-_v[0], T9["max"]) and abs(_t[-2] - T9["x"]) <= 5e-4 + 1e-9 and abs(_t[-1] - T9["y"]) <= 5e-4 + 1e-9 and "no sign change on [13.9, 14.3]" in S_SHALLOW and T9["sign_changes"] == 0 and T9["re2_match"]
_v = _scis(S_ACC); ok &= len(_v) == 1 and _sci_ok(_v[0], max(abs(L["accounting_residual"]) for c in ORDER for L in in_law(c))) and "at every safely deep rung" in S_ACC and "at every safely deep rung" in S_WORST
_L = in_law("d2.3")
_v = _scis(S_DK23); ok &= len(_v) == len(_L) and all(_sci_ok(p, -L["Dkappa"]) for p, L in zip(_v, _L))
_TD = CEN["d2.3"]["rungs"][0]["edge"]
_m = _nums(S_TAU.split(" T₁")[0]); ok &= len(_m) == len(_L) and all(abs(x - L["tau_eff"]/_TD) <= 5e-3 + 1e-9 for x, L in zip(_m, _L))
_m = _nums(S_TAURANGE.split(" T₁")[0]); ok &= len(_m) == 2 and abs(_m[0] - min(TAU_R)) <= 5e-3 + 1e-9 and abs(_m[1] - max(TAU_R)) <= 5e-3 + 1e-9 and "over the safely deep rungs of the five cells" in S_TAURANGE
_m = _nums(S_RATIO.split(" at r = 40")[0]); ok &= len(_m) == len(_L) and all(abs(x - L["ratio_r"]["40.0"]) <= 5e-4 + 1e-9 for x, L in zip(_m, _L)) and " at r = 40 " in S_RATIO
_m = _nums(S_MASS); ok &= len(_m) == len(ORDER) and all(abs(x - LAW[c]["mass_interior"]) <= 5e-7 + 1e-12 for x, c in zip(_m, ORDER))
_v = _scis(S_DEVE); ok &= len(_v) == len(_L) and all(_sci_ok(p, L["dev_E"]) for p, L in zip(_v, _L))
_v = _scis(S_DEVR); ok &= len(_v) == 2*len(_L) and all(_sci_ok(p, L["dev_R"]) for p, L in zip(_v[:len(_L)], _L)) and all(_sci_ok(p, L["dev_A"]) for p, L in zip(_v[len(_L):], _L))
_v = _scis(S_DEVM); ok &= len(_v) == len(_L) and all(_sci_ok(p, L["dev_M"]) for p, L in zip(_v, _L))
_v = _scis(S_WORST); ok &= len(_v) == 2 and _sci_ok(_v[0], max(L["dev_E"] for c in ORDER for L in in_law(c))) and _sci_ok(_v[1], max(L["dev_R"] for c in ORDER for L in in_law(c)))
_v = _scis(S_DK2); ok &= len(_v) == len(ORDER) and all(_sci_ok(p, -LAW[c]["laws"][0]["Dkappa"]) for p, c in zip(_v, ORDER))
def _located_sentence(CEN, ORDER, n_safe):
    Kb = ", ".join(str(CEN[c]["K"] - 1) for c in ORDER); parts = []
    for c in ORDER:
        R = CEN[c]["rungs"][:n_safe(c) + 1]; un = [r for r in R if r["n_complex"] > 0]
        if not un: continue
        if not all(r["n_complex"] == 1 and r["sum_rule_residual"] < 0 for r in un): return None
        taus = [abs(r["sum_rule_residual"])**-0.5 for r in un]
        where = "every rung" if len(un) == len(R) else "rung" + ("s " if len(un) > 1 else " ") + ", ".join(str(r["k"]) for r in un)
        a_ = CEN[c]["delta"]/2
        if len(un) == 1:
            t = taus[0]; R_ext = un[0]["R_ext"]
            if t >= R_ext: at = f"|τ| = {t:.0f}, beyond the region {R_ext:.0f}"
            else:
                j = round(t/(math.pi/a_)); at = f"|τ| = {t:.0f}, {abs(t - j*math.pi/a_):.3f} {'below' if t < j*math.pi/a_ else 'above'} the sinc zero ω_{j} inside one census cell"
        else:
            at = f"|τ| between {min(taus):.0f} and {max(taus):.0f}, beyond the region {un[0]['R_ext']:.0f}" if min(taus) >= un[0]["R_ext"] else f"|τ| between {min(taus):.0f} and {max(taus):.0f}"
        parts.append(f"{where} at δ = {CEN[c]['delta']:g} ({CEN[c]['K'] - 2} of {CEN[c]['K'] - 1}, the last placed by the sum rule at {at})")
    return f"all {Kb} designed pairs located at every safely deep rung" + (" but " + " and ".join(parts) + " — 1bu(ii)’s branch" if parts else " at the five cells")
ok &= _located_sentence(CEN, ORDER, n_safe) == S_LOCATED          # the sentence regenerated from the checkpoints, character for character
gate("g7 the paper's numbers parsed back from the declared needles", ok)

# ---------------------------------------------------------------- g8
from cascade_tower import chain_ok
gate("g8 the chain obligation to cascade_ladder_caster.py (Theorem 1bu) met", chain_ok("cascade_ladder_caster.py"))

# ---------------------------------------------------------------- g9
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g9 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g9 the 1bw paper needles and the footer census (declared surface)", ok)

print(("ALL GATES PASS (11/11)" if not fails else f"FAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
