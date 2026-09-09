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
K = 2 + gamma_E - ln 4 pi. (2) THE LIMIT SHAPE AT THE CELLS: Hypothesis D --
the first zeta zero the ground state misses and its first free zero within 0.2
of each other and at >= 1.4 T_0 at every cell; the curvature sum 1/tau^2 rising
across the cells and below K/2; ghat_1(0)^2 rising and below 0.7729;
sqrt<r^2> falling and above 3.195. (3) THE HOLE ZEROS: at every safely deep
rung up to rung 12 (ln(1 - chi_{2k}) < -5; the producer's census region
covers the nodes through rung 12) the transform of rung k has exactly k - 1
hole zeros (the real zeros below min(100, 0.8 x the dodging edge) left after
one dodging zero per zeta zero is removed; a double zero counted twice), the
ground state none; at delta >= 2 the hole zeros of rungs 2-4 sit within 1% of
the nodes of P_{2(k-1)} for the weight ghat_1^2; the first hole zero falls
across the cells and stays above the Xi-limit 3.195.
(4) THE k-LEVEL FORMULA: c_1 within 0.15 of 1bm(v)'s c(delta) at every cell;
c_k for the safely deep rungs (through rung 12) within [c_1 - 3, c_1 + 0.3];
the parity: at the cells with >= 6 such rungs the mean of c_k over even k lies
below the mean over odd k (rungs 2 on). (5) THE ANATOMY of c(delta): the identity
c_1 = origin + peak excess + count + far tail (1e-9); the origin rising toward
ln 0.7729; the share of Q beyond 3 T_0 at least 0.3 at delta >= 2. (6) mangle
probes: a pair cost of 2 ln T_0 per rung misses the ladder; the Gaussian
model's first node 1/sqrt(2K) = 3.290 is not the Xi-limit's 3.195 and the cells
at delta >= 3 sit below the Gaussian value; (7) the paper's numbers parsed
back; (8) the chain obligation to cascade_pole_indefinite.py; (9) the needles
and census.

WHAT IS NOT CLAIMED. The orthogonal-polynomial structure of the excited states
is computed, not proved; the residual c_k's law and its parity are not
modelled; the constants of the offsets against the prolate ladder are not
derived; no Riemann Hypothesis consequence.
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
    {'g': 'g7', 's': '@S_EDGE@', 'form': 'ws'},
    {'g': 'g7', 's': '@S_KAPPA@', 'form': 'ws'},
    {'g': 'g7', 's': '@S_G0@', 'form': 'ws'},
    {'g': 'g7', 's': '@S_R2@', 'form': 'ws'},
    {'g': 'g7', 's': '@S_HOLE23@', 'form': 'ws'},
    {'g': 'g7', 's': '@S_FIRST@', 'form': 'ws'},
    {'g': 'g7', 's': '@S_XINODES@', 'form': 'ws'},
    {'g': 'g7', 's': '@S_CK@', 'form': 'ws'},
    {'g': 'g7', 's': '@S_ANAT@', 'form': 'ws'},
    {'g': 'g7', 's': '@S_XICONST@', 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ORDER = ["d1.0", "d1.38", "d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
ST = {c: run_LC(c) for c in ORDER}
T0 = {c: ST[c]["T0"] for c in ORDER}
SAFE = -5.0                                   # the safely deep rungs: ln(1 - chi_{2k}) < -5
def safe_rungs(c):
    st = ST[c]; pro = st["prolate_ln_leakage"]
    return [r for r in st["rungs"][1:] if pro[2*(r["k"] - 1)] is not None and pro[2*(r["k"] - 1)] < SAFE and r["k"] <= 12]

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
XN = XI.nodes(4)
gate(f"g1 the Xi side: Hadamard's product against the 800 zeros (100 digits, agreeing with the double list within 1e-9) plus the density tail at t = 3, 8, 13 (max |diff| {worst:.1e}); Xi(0) = {XC['Xi0']:.5f}; 2 pi Xi(0)^2/int Xi^2 = {XC['g0sq_limit']:.4f}; sqrt<t^2> = {math.sqrt(XC['t2_mean']):.4f}; K = {XC['K']:.6f}, 1/sqrt(2K) = {XC['inv_sqrt_2K']:.4f}; the Xi-limit nodes " + "; ".join(", ".join(f"{v:.3f}" for v in n) for n in XN), ok)

# ---------------------------------------------------------------- g2
ok = True; G = {c: ST[c]["ground"] for c in ORDER}
for c in ORDER:
    g = G[c]; ok &= g["first_missed"] is not None and g["first_free"] is not None and abs(g["first_missed"] - g["first_free"]) <= 0.2 and g["first_missed"] >= 1.4*T0[c]
kap = [G[c]["kappa"] for c in ORDER]; g0 = [math.exp(G[c]["ln_g0sq"]) for c in ORDER]; r2 = [math.sqrt(G[c]["r2_mean"]) for c in ORDER]
ok &= all(kap[i] < kap[i + 1] for i in range(6)) and kap[-1] < XC["K"]/2
ok &= all(g0[i] < g0[i + 1] for i in range(6)) and g0[-1] < XC["g0sq_limit"]
ok &= all(r2[i] > r2[i + 1] for i in range(6)) and r2[-1] > math.sqrt(XC["t2_mean"])
gate("g2 the limit shape at the cells: Hypothesis D (the first missed zeta zero and the first free zero within 0.2, at " + ", ".join(f"{G[c]['first_missed']/T0[c]:.2f}" for c in ORDER) + " T_0); the curvature " + ", ".join(f"{k:.4f}" for k in kap) + f" rising toward K/2 = {XC['K']/2:.4f}; ghat_1(0)^2 " + ", ".join(f"{v:.3f}" for v in g0) + f" rising toward {XC['g0sq_limit']:.4f}; sqrt<r^2> " + ", ".join(f"{v:.3f}" for v in r2) + f" falling toward {math.sqrt(XC['t2_mean']):.3f}", ok)

# ---------------------------------------------------------------- g3
ok = True; worst_rel = 0.0; nsafe = 0
for c in ORDER:
    st = ST[c]; ok &= len(st["rungs"][0]["hole"]) == 0
    for r in safe_rungs(c):
        nsafe += 1; ok &= len(r["hole"]) == r["k"] - 1
    if st["delta"] >= 2.0:
        for r in st["rungs"][1:4]:
            nodes = st["nodes"][r["k"] - 2]
            if len(r["hole"]) == len(nodes):
                rel = max(abs(h - n)/n for h, n in zip(r["hole"], nodes)); worst_rel = max(worst_rel, rel); ok &= rel <= 0.01
            else: ok = False
first = [ST[c]["rungs"][1]["hole"][0] for c in ORDER]
ok &= all(first[i] > first[i + 1] for i in range(6)) and first[-1] > XN[0][0]
gate(f"g3 the hole zeros: the ground state has none; every safely deep rung k through rung 12 ({nsafe} rungs over the seven cells) has exactly k - 1; at delta >= 2 rungs 2-4 sit within 1% of the nodes of P_(2(k-1)) for the weight ghat_1^2 (max relative deviation {worst_rel:.2%}); the first hole zero " + ", ".join(f"{v:.3f}" for v in first) + f" falling toward the Xi-limit {XN[0][0]:.3f}", ok)

# ---------------------------------------------------------------- g4
CDEL = {"d1.0": 4.70, "d1.38": 5.21, "d2.0": 5.94, "d2.3": 6.39, "d2.6": 6.64, "d3.0": 7.30, "d3.5": 7.90}   # 1bm(v)
ok = True; par = {}
for c in ORDER:
    st = ST[c]; c1 = st["rungs"][0]["ck"]; ok &= abs(c1 - CDEL[c]) <= 0.15
    sr = safe_rungs(c)
    for r in sr: ok &= c1 - 3.0 <= r["ck"] <= c1 + 0.3
    if len(sr) >= 6:
        ev = [r["ck"] for r in sr if r["k"] % 2 == 0]; od = [r["ck"] for r in sr if r["k"] % 2 == 1]
        par[c] = (float(np.mean(ev)), float(np.mean(od))); ok &= par[c][0] < par[c][1]
gate("g4 the k-level formula: c_1 within 0.15 of 1bm(v)'s c(delta) at every cell (" + ", ".join(f"{ST[c]['rungs'][0]['ck']:.2f}" for c in ORDER) + "); the safely deep rungs' c_k within [c_1 - 3, c_1 + 0.3]; the parity at the cells with >= 6 such rungs: mean c_k over even k below odd k -- " + ", ".join(f"{c}: {par[c][0]:.2f} < {par[c][1]:.2f}" for c in par), ok)

# ---------------------------------------------------------------- g5
ok = True
for c in ORDER:
    g = G[c]; ok &= abs(g["c1"] - (g["origin"] + g["peak_excess"] + g["count_800"] + g["far_tail"])) <= 1e-9
    if ST[c]["delta"] >= 2.0: ok &= 1 - g["shares"]["3"] >= 0.3
org = [G[c]["origin"] for c in ORDER]; ok &= all(org[i] < org[i + 1] for i in range(6)) and org[-1] < math.log(XC["g0sq_limit"])
gate("g5 the anatomy of c(delta) = origin + peak excess + count (+ the far tail beyond the 800 zeros), an identity at every cell: origin " + ", ".join(f"{G[c]['origin']:.3f}" for c in ORDER) + f" rising toward ln 0.7729 = {math.log(XC['g0sq_limit']):.3f}; peak excess " + ", ".join(f"{G[c]['peak_excess']:.2f}" for c in ORDER) + "; count " + ", ".join(f"{G[c]['count_800'] + G[c]['far_tail']:.2f}" for c in ORDER) + "; the share of Q beyond 3 T_0 " + ", ".join(f"{1 - G[c]['shares']['3']:.2f}" for c in ORDER), ok)

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
S_EDGE = '@S_EDGE@'
S_KAPPA = '@S_KAPPA@'
S_G0 = '@S_G0@'
S_R2 = '@S_R2@'
S_HOLE23 = '@S_HOLE23@'
S_FIRST = '@S_FIRST@'
S_XINODES = '@S_XINODES@'
S_CK = '@S_CK@'
S_ANAT = '@S_ANAT@'
S_XICONST = '@S_XICONST@'
# each call carries its literal (the precheck's clause D); the strings equal the S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, '@S_EDGE@', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '@S_KAPPA@', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '@S_G0@', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '@S_R2@', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '@S_HOLE23@', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '@S_FIRST@', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '@S_XINODES@', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '@S_CK@', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '@S_ANAT@', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '@S_XICONST@', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g7'] == [S_EDGE, S_KAPPA, S_G0, S_R2, S_HOLE23, S_FIRST, S_XINODES, S_CK, S_ANAT, S_XICONST]
_re = __import__("re")
def _num(s): return float(s.strip().replace('−', '-'))
def _nums(s, pat=r"([-−]?[0-9]+\.[0-9]+)"): return [_num(x) for x in _re.findall(pat, s)]
_m = _nums(S_EDGE); ok &= len(_m) == 7 and all(abs(x - G[c]["first_missed"]/T0[c]) <= 5e-3 + 1e-9 for x, c in zip(_m, ORDER))                  # nearest 0.01
_m = _nums(S_KAPPA); ok &= len(_m) == 8 and all(abs(x - k) <= 5e-5 + 1e-9 for x, k in zip(_m[:7], kap)) and abs(_m[7] - XC["K"]/2) <= 5e-5 + 1e-9   # nearest 1e-4
_m = _nums(S_G0); ok &= len(_m) == 8 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m[:7], g0)) and abs(_m[7] - XC["g0sq_limit"]) <= 5e-4 + 1e-9
_m = _nums(S_R2); ok &= len(_m) == 8 and all(abs(x - v) <= 5e-3 + 1e-9 for x, v in zip(_m[:7], r2)) and abs(_m[7] - math.sqrt(XC["t2_mean"])) <= 5e-3 + 1e-9
_m = _nums(S_HOLE23.split(" rung 2 at ")[1]); _h = ST["d2.3"]["rungs"][1]["hole"] + ST["d2.3"]["nodes"][0] + ST["d2.3"]["rungs"][2]["hole"] + ST["d2.3"]["nodes"][1] + ST["d2.3"]["rungs"][3]["hole"] + ST["d2.3"]["nodes"][2]
ok &= len(_m) == 12 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m, _h))                                                                       # nearest 1e-3
_m = _nums(S_FIRST); ok &= len(_m) == 8 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m[:7], first)) and abs(_m[7] - XN[0][0]) <= 5e-4 + 1e-9
_m = _nums(S_XINODES); _x = [v for n in XN for v in n]; ok &= len(_m) == 10 and all(abs(x - v) <= 5e-4 + 1e-9 for x, v in zip(_m, _x))
_m = _nums(S_CK.split(" over rungs")[0]); _c = [r["ck"] for r in ST["d2.3"]["rungs"][:8]]; ok &= len(_m) == 8 and all(abs(x - v) <= 5e-3 + 1e-9 for x, v in zip(_m, _c))
_m = _nums(S_ANAT); _a = [G[c]["origin"] for c in ORDER] + [G[c]["peak_excess"] for c in ORDER] + [G[c]["count_800"] + G[c]["far_tail"] for c in ORDER]
ok &= len(_m) == 21 and all(abs(x - v) <= 5e-3 + 1e-9 for x, v in zip(_m, _a))
_m = _nums(S_XICONST); ok &= len(_m) == 3 and abs(_m[0] - XC["Xi0"]) <= 5e-6 + 1e-9 and abs(_m[1] - XC["int_Xi2"]) <= 5e-6 + 1e-9 and abs(_m[2] - XC["g0sq_limit"]) <= 5e-5 + 1e-9
gate("g7 the paper's numbers parsed back from the declared needles: the dodging edges (nearest 0.01 T_0), the curvatures (1e-4), ghat_1(0)^2 (1e-3), sqrt<r^2> (0.01), the hole zeros and nodes of rungs 2-4 at delta = 2.3 (1e-3), the first hole zeros (1e-3), the Xi-limit nodes (1e-3), c_k at delta = 2.3 (0.01), the anatomy (0.01), Xi's constants", ok)

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
