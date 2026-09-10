#!/usr/bin/env python3
"""Theorem 1bw (the excited states' exact anatomy -- the bi-orthogonal law of the hole polynomials and the exterior's Gaussian
correction): the verifier. The tower's member 32 (top); chain obligation to cascade_ladder_caster.py (Theorem 1bu), whose
ladder this block completes at the level of the excited states.

WHAT THE BLOCK CLAIMS. At the cells delta = 2.0, 2.3, 2.6, 3.0, 3.5 and every safely deep rung k (Theorem 1bu's rungs; every
designed pair real, located or placed by the sum rule): ghat_k = ghat_1 H_k C_k with H_k the hole polynomial (k - 1 real pairs) and C_k
the ratio of the remaining zero products; ln C_k(r) = -Dkappa_k r^2 + O(r^4) with Dkappa_k = kappa_k - kappa_1 - sum_h h^-2 an
identity from the sum rules, the accounting [sum_{E_k} - sum_{E_1}] - sum_{freed}; the hole polynomial H_k determined by the
k - 1 bi-orthogonality conditions int ghat_1^2 C_k C_j H_k H_j = 0 (j < k) on the interior [0, T_D/2] -- with the exact C's to
the census (E), with the Gaussian truncation and the recursion's own lower polynomials (R) from ghat_1 and the Dkappa's alone,
against the naive nodes (A, the orthogonal polynomials of ghat_1^2, 1bu(iii)); the mangle (the correction's sign flipped) misses;
tau_eff = sqrt((k - 1)/(-Dkappa_k)) between 1.0 and 1.6 T_D; |Dkappa_2| falling across the cells (the correction vanishing
toward the Xi-limit, where the orthogonal polynomials of Xi^2 are the law); the shallow rungs beyond the law at delta = 2.3
(rungs 9, 10) with complex designed pairs. Substrates rung_anatomy.py (keyed: the census) and rung_laws.py (keyed on the census:
the laws), both importing ladder_caster.py's helpers.

THE GATES. (0) the census at every cell and safely deep rung: every designed pair real -- located with the sum rule within
1e-13, or exactly one unlocated and placed by a negative remainder (1bu(ii)'s K - 2 branch) -- no dip, exactly k - 1 holes, the
accounting n_dodge + holes + exterior (+ the placed) = K - 1, the rung's edge inside the ground state's; (1) the curvature law: the
accounting residual (the displacements' part) within 1e-5, Dkappa_k < 0 and falling with k, the ratio (-ln C/r^2)/Dkappa at r = 5
within 2e-3 of 1 and at r = 40 within 0.25; (2) the bi-orthogonal law: E within 1e-5 at every rung in the law, R within 1e-2 and
better than A at every rung in the law, R within 1e-5 at rungs 2-3 and 1e-3 at rungs 2-7 for delta >= 2.3; the mangle worse than
R by a factor 10 at every rung; (3) tau_eff/T_D in [1.0, 1.6]; (4) |Dkappa_2| falling across the cells; the interior mass
>= 0.998; ghat_1's census product against its direct evaluation on the low interior within 1e-6; (5) the shallow rungs at delta = 2.3: rungs 9 and 10 with complex pairs (2 and 8); (6) the count of rungs in the law
at each cell; (7) the paper's numbers parsed back; (8) the chain obligation; (9) the needles and census.

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
    {'g': 'g7', 's': 'all 159, 259, 319, 399, 539 designed pairs located at every safely deep rung but rung 3 at δ = 3 (398 of 399, the last placed by the sum rule at |τ| = 1470) and every rung at δ = 3.5 (538 of 539, the last placed by the sum rule at |τ| between 8688 and 14501) — 1bu(ii)’s branch', 'form': 'ws'},
    {'g': 'g7', 's': 'the rungs’ edges 121.4, 111.9, 111.0, 105.4, 103.7, 94.7, 87.4 for rungs 1–7 at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'at δ = 2.3 38 + 0 + 221; 34 + 1 + 224; 33 + 2 + 224; 31 + 3 + 225 for rungs 1–4', 'form': 'ws'},
    {'g': 'g7', 's': 'rungs 9 and 10 (ln λ = −5.14, −0.67) have 2 and 8 complex pairs', 'form': 'ws'},
    {'g': 'g7', 's': 'the accounting residual within 2.7 × 10⁻⁶ everywhere', 'form': 'ws'},
    {'g': 'g7', 's': '−Δκ_k = 3.49 × 10⁻⁵, 7.87 × 10⁻⁵, 1.21 × 10⁻⁴, 1.70 × 10⁻⁴, 2.20 × 10⁻⁴, 2.87 × 10⁻⁴ for rungs 2–7 at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'τ_eff = 1.40, 1.31, 1.30, 1.26, 1.24, 1.19 T_D at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'the ratio 1.049, 1.053, 1.056, 1.058, 1.062, 1.069 at r = 40 for rungs 2–7 at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'the interior carrying 1.000000, 1.000000, 1.000000, 1.000000, 1.000000 of the ground state’s mass', 'form': 'ws'},
    {'g': 'g7', 's': 'E within 1.2 × 10⁻⁸, 1.7 × 10⁻⁸, 2.0 × 10⁻⁸, 2.2 × 10⁻⁸, 2.5 × 10⁻⁸, 2.3 × 10⁻⁸ for rungs 2–7 at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'R within 6.1 × 10⁻⁷, 4.0 × 10⁻⁶, 2.7 × 10⁻⁵, 9.9 × 10⁻⁵, 2.9 × 10⁻⁴, 9.6 × 10⁻⁴ against the naive nodes’ 3.6 × 10⁻⁴, 1.1 × 10⁻³, 2.8 × 10⁻³, 6.9 × 10⁻³, 1.2 × 10⁻², 2.4 × 10⁻² for rungs 2–7 at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'the mangle’s 7.2 × 10⁻⁴, 2.2 × 10⁻³, 5.5 × 10⁻³, 1.4 × 10⁻², 2.2 × 10⁻², 4.9 × 10⁻² at δ = 2.3', 'form': 'ws'},
    {'g': 'g7', 's': 'E within 3.4 × 10⁻⁸ and R within 1.2 × 10⁻³ at every rung in the law at every cell', 'form': 'ws'},
    {'g': 'g7', 's': 'rungs in the law 4, 7, 11, 12, 12', 'form': 'ws'},
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
    def whole(r):   # every pair located and the sum rule closing, or 1bu(ii)'s K - 2 branch: one pair placed by a negative remainder
        return (r["n_complex"] == 0 and abs(r["sum_rule_residual"]) <= 1e-13) or (r["n_complex"] == 1 and r["sum_rule_residual"] < 0)
    ok &= whole(g1) and g1["n_dips"] == 0 and len(g1["holes_fine"]) == 0
    for r in R[1:ns + 1]:
        ok &= whole(r) and r["n_dips"] == 0 and len(r["holes_fine"]) == r["k"] - 1
        ok &= len(r["dodging"]) + len(r["holes"]) + len(r["exterior"]) + r["n_complex"] == r["K_minus_1"] and r["edge"] <= g1["edge"] + 1e-9
    placed[c] = [(r["k"], abs(r["sum_rule_residual"])**-0.5) for r in R[:ns + 1] if r["n_complex"] == 1 and r["sum_rule_residual"] < 0]
gate("g0 the census at every cell and safely deep rung (" + ", ".join(f"{c}: {cnt[c]}" for c in ORDER) + "): every designed pair real -- located with the sum rule within 1e-13, or one placed by a negative remainder (" + "; ".join(f"{c}: " + (", ".join(f"rung {k} at |tau| = {t:.0f}" for k, t in placed[c]) or "none") for c in ORDER) + ") -- no dip, k - 1 holes, the accounting n_dodge + holes + exterior (+ the placed) = K - 1, the edge inside the ground state's", ok)

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
        ok &= L["dev_M"] is None or L["dev_M"] >= 10*L["dev_R"]
        if CEN[c]["delta"] >= 2.3 and L["k"] <= 3: ok &= L["dev_R"] <= 1e-5
        if CEN[c]["delta"] >= 2.3 and L["k"] <= 7: ok &= L["dev_R"] <= 1e-3
gate("g2 the bi-orthogonal law: with the exact corrections the holes within 1e-5 (E); with the Gaussian corrections and the recursion's own lower polynomials within 1e-2 and better than the naive nodes at every rung, within 1e-5 at rungs 2-3 and 1e-3 at rungs 2-7 for delta >= 2.3 (R); the sign-flipped mangle worse by 10 -- " +
     "; ".join(f"{c}: E " + ", ".join(f"{L['dev_E']:.0e}" for L in in_law(c)) + " | R " + ", ".join(f"{L['dev_R']:.0e}" for L in in_law(c)) + " | A " + ", ".join(f"{L['dev_A']:.0e}" for L in in_law(c)) for c in ORDER), ok)

# ---------------------------------------------------------------- g3
ok = True
for c in ORDER:
    TD = CEN[c]["rungs"][0]["edge"]
    ok &= all(L["tau_eff"] is not None and 1.0 <= L["tau_eff"]/TD <= 1.6 for L in in_law(c))
gate("g3 tau_eff = sqrt((k - 1)/(-Dkappa_k)) between 1.0 and 1.6 T_D at every rung in the law -- " + "; ".join(f"{c}: " + ", ".join(f"{L['tau_eff']/CEN[c]['rungs'][0]['edge']:.2f}" for L in in_law(c)) for c in ORDER), ok)

# ---------------------------------------------------------------- g4
dk2 = [-LAW[c]["laws"][0]["Dkappa"] for c in ORDER]
ok = all(dk2[i] > dk2[i + 1] for i in range(len(dk2) - 1)) and all(LAW[c]["mass_interior"] >= 0.998 for c in ORDER)
ok &= all(LAW[c]["g1_product_check"] <= 1e-6 for c in ORDER)       # ghat_1 from its census against the direct evaluation on the low interior (ln ghat_1^2 within 1e-6)
gate("g4 |Dkappa_2| falling across the cells " + ", ".join(f"{v:.2e}" for v in dk2) + " (the correction vanishing toward the Xi-limit); the interior [0, T_D/2] carrying " + ", ".join(f"{LAW[c]['mass_interior']:.5f}" for c in ORDER) + " of the ground state's mass; ghat_1 from its census against the direct evaluation within " + ", ".join(f"{LAW[c]['g1_product_check']:.0e}" for c in ORDER) + " in ln ghat_1^2 on the low interior", ok)

# ---------------------------------------------------------------- g5
R23 = CEN["d2.3"]["rungs"]
ok = len(R23) >= 10 and R23[8]["n_complex"] == 2 and R23[9]["n_complex"] == 8 and all(r["n_complex"] == 0 for r in R23[:8])
gate(f"g5 the shallow rungs at delta = 2.3 beyond the law: rungs 9 and 10 with {R23[8]['n_complex']} and {R23[9]['n_complex']} complex designed pairs (ln lambda {R23[8]['ln_lam']:.2f}, {R23[9]['ln_lam']:.2f}); rungs 1-8 all real", ok)

# ---------------------------------------------------------------- g6
ok = all(LAW[c]["n_in_law"] >= n_safe(c) for c in ORDER)
gate("g6 every safely deep rung is in the law (rungs in the law " + ", ".join(f"{c}: {LAW[c]['n_in_law']} of {n_safe(c)} safely deep" for c in ORDER) + ")", ok)

# ---------------------------------------------------------------- g7
import paper_needles
S_SAFE = '3, 6, 9, 11, 11 safely deep rungs at δ = 2, 2.3, 2.6, 3, 3.5'
S_LOCATED = 'all 159, 259, 319, 399, 539 designed pairs located at every safely deep rung but rung 3 at δ = 3 (398 of 399, the last placed by the sum rule at |τ| = 1470) and every rung at δ = 3.5 (538 of 539, the last placed by the sum rule at |τ| between 8688 and 14501) — 1bu(ii)’s branch'
S_EDGES = 'the rungs’ edges 121.4, 111.9, 111.0, 105.4, 103.7, 94.7, 87.4 for rungs 1–7 at δ = 2.3'
S_ACCT = 'at δ = 2.3 38 + 0 + 221; 34 + 1 + 224; 33 + 2 + 224; 31 + 3 + 225 for rungs 1–4'
S_SHALLOW = 'rungs 9 and 10 (ln λ = −5.14, −0.67) have 2 and 8 complex pairs'
S_ACC = 'the accounting residual within 2.7 × 10⁻⁶ everywhere'
S_DK23 = '−Δκ_k = 3.49 × 10⁻⁵, 7.87 × 10⁻⁵, 1.21 × 10⁻⁴, 1.70 × 10⁻⁴, 2.20 × 10⁻⁴, 2.87 × 10⁻⁴ for rungs 2–7 at δ = 2.3'
S_TAU = 'τ_eff = 1.40, 1.31, 1.30, 1.26, 1.24, 1.19 T_D at δ = 2.3'
S_RATIO = 'the ratio 1.049, 1.053, 1.056, 1.058, 1.062, 1.069 at r = 40 for rungs 2–7 at δ = 2.3'
S_MASS = 'the interior carrying 1.000000, 1.000000, 1.000000, 1.000000, 1.000000 of the ground state’s mass'
S_DEVE = 'E within 1.2 × 10⁻⁸, 1.7 × 10⁻⁸, 2.0 × 10⁻⁸, 2.2 × 10⁻⁸, 2.5 × 10⁻⁸, 2.3 × 10⁻⁸ for rungs 2–7 at δ = 2.3'
S_DEVR = 'R within 6.1 × 10⁻⁷, 4.0 × 10⁻⁶, 2.7 × 10⁻⁵, 9.9 × 10⁻⁵, 2.9 × 10⁻⁴, 9.6 × 10⁻⁴ against the naive nodes’ 3.6 × 10⁻⁴, 1.1 × 10⁻³, 2.8 × 10⁻³, 6.9 × 10⁻³, 1.2 × 10⁻², 2.4 × 10⁻² for rungs 2–7 at δ = 2.3'
S_DEVM = 'the mangle’s 7.2 × 10⁻⁴, 2.2 × 10⁻³, 5.5 × 10⁻³, 1.4 × 10⁻², 2.2 × 10⁻², 4.9 × 10⁻² at δ = 2.3'
S_WORST = 'E within 3.4 × 10⁻⁸ and R within 1.2 × 10⁻³ at every rung in the law at every cell'
S_NLAW = 'rungs in the law 4, 7, 11, 12, 12'
S_DK2 = '−Δκ₂ = 6.52 × 10⁻⁵, 3.49 × 10⁻⁵, 1.80 × 10⁻⁵, 8.16 × 10⁻⁶, 3.20 × 10⁻⁶ at the five cells'
# each call carries its literal (the precheck's clause D); the strings equal the S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, '3, 6, 9, 11, 11 safely deep rungs at δ = 2, 2.3, 2.6, 3, 3.5', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'all 159, 259, 319, 399, 539 designed pairs located at every safely deep rung but rung 3 at δ = 3 (398 of 399, the last placed by the sum rule at |τ| = 1470) and every rung at δ = 3.5 (538 of 539, the last placed by the sum rule at |τ| between 8688 and 14501) — 1bu(ii)’s branch', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the rungs’ edges 121.4, 111.9, 111.0, 105.4, 103.7, 94.7, 87.4 for rungs 1–7 at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'at δ = 2.3 38 + 0 + 221; 34 + 1 + 224; 33 + 2 + 224; 31 + 3 + 225 for rungs 1–4', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'rungs 9 and 10 (ln λ = −5.14, −0.67) have 2 and 8 complex pairs', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the accounting residual within 2.7 × 10⁻⁶ everywhere', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '−Δκ_k = 3.49 × 10⁻⁵, 7.87 × 10⁻⁵, 1.21 × 10⁻⁴, 1.70 × 10⁻⁴, 2.20 × 10⁻⁴, 2.87 × 10⁻⁴ for rungs 2–7 at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'τ_eff = 1.40, 1.31, 1.30, 1.26, 1.24, 1.19 T_D at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the ratio 1.049, 1.053, 1.056, 1.058, 1.062, 1.069 at r = 40 for rungs 2–7 at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the interior carrying 1.000000, 1.000000, 1.000000, 1.000000, 1.000000 of the ground state’s mass', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'E within 1.2 × 10⁻⁸, 1.7 × 10⁻⁸, 2.0 × 10⁻⁸, 2.2 × 10⁻⁸, 2.5 × 10⁻⁸, 2.3 × 10⁻⁸ for rungs 2–7 at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'R within 6.1 × 10⁻⁷, 4.0 × 10⁻⁶, 2.7 × 10⁻⁵, 9.9 × 10⁻⁵, 2.9 × 10⁻⁴, 9.6 × 10⁻⁴ against the naive nodes’ 3.6 × 10⁻⁴, 1.1 × 10⁻³, 2.8 × 10⁻³, 6.9 × 10⁻³, 1.2 × 10⁻², 2.4 × 10⁻² for rungs 2–7 at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the mangle’s 7.2 × 10⁻⁴, 2.2 × 10⁻³, 5.5 × 10⁻³, 1.4 × 10⁻², 2.2 × 10⁻², 4.9 × 10⁻² at δ = 2.3', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'E within 3.4 × 10⁻⁸ and R within 1.2 × 10⁻³ at every rung in the law at every cell', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'rungs in the law 4, 7, 11, 12, 12', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '−Δκ₂ = 6.52 × 10⁻⁵, 3.49 × 10⁻⁵, 1.80 × 10⁻⁵, 8.16 × 10⁻⁶, 3.20 × 10⁻⁶ at the five cells', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g7'] == [S_SAFE, S_LOCATED, S_EDGES, S_ACCT, S_SHALLOW, S_ACC, S_DK23, S_TAU, S_RATIO, S_MASS, S_DEVE, S_DEVR, S_DEVM, S_WORST, S_NLAW, S_DK2]
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
ok &= _ints(S_NLAW) == [LAW[c]["n_in_law"] for c in ORDER]
_m = _nums(S_EDGES.split(" for rungs")[0]); ok &= len(_m) == 7 and all(abs(x - r["edge"]) <= 0.05 + 1e-9 for x, r in zip(_m, CEN["d2.3"]["rungs"][:7]))
_m = _ints(S_ACCT.split("at δ = 2.3 ")[1].split(" for rungs")[0]); ok &= _m == [v for r in CEN["d2.3"]["rungs"][:4] for v in (len(r["dodging"]), len(r["holes"]), len(r["exterior"]))]
_m = _nums(S_SHALLOW); _i = _ints(S_SHALLOW.split(") have ")[1]); _r = CEN["d2.3"]["rungs"]
ok &= len(_m) == 2 and abs(_m[0] - _r[8]["ln_lam"]) <= 5e-3 + 1e-9 and abs(_m[1] - _r[9]["ln_lam"]) <= 5e-3 + 1e-9 and _i[:2] == [_r[8]["n_complex"], _r[9]["n_complex"]]
_v = _scis(S_ACC); ok &= len(_v) == 1 and _sci_ok(_v[0], max(abs(L["accounting_residual"]) for c in ORDER for L in in_law(c)))
_L = in_law("d2.3")
_v = _scis(S_DK23); ok &= len(_v) == len(_L) and all(_sci_ok(p, -L["Dkappa"]) for p, L in zip(_v, _L))
_TD = CEN["d2.3"]["rungs"][0]["edge"]
_m = _nums(S_TAU.split(" T_D")[0]); ok &= len(_m) == len(_L) and all(abs(x - L["tau_eff"]/_TD) <= 5e-3 + 1e-9 for x, L in zip(_m, _L))
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
        at = f"|τ| = {taus[0]:.0f}" if len(un) == 1 else f"|τ| between {min(taus):.0f} and {max(taus):.0f}"
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

print(("ALL GATES PASS (10/10)" if not fails else f"FAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
