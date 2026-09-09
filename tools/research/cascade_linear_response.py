#!/usr/bin/env python3
"""Theorem 1bp -- the knife-edge is linear response: at every cell and prime
the certified shift of Theorem 1bo equals lambda_1 divided by the form's first
derivative in log p at the minimiser, to within the bracket; the pins compose
additively (the dilation edge); the archimedean constant is pinned to exactly
lambda_1 by a one-line identity. Substrate weil_linear_response.py (keyed on
its closure: weil_knife_edge.py, weil_prime_gram.py). Tower member 25 (top).

THE CLAIMS GATED. (0) THE CELLS load at their keys, the seven of Theorem 1bo,
with the same lambda_1 balls (upper ends within 1e-20 relative). (1) THE LAW:
at every (cell, prime) the first-order crossing eta_lin = lambda_1/D_p (a
ball: D_p = -(dP_p/d eta)/||g_1||^2 from the O(K) closed forms of f and f')
lies inside 1bo's certified bracket [eta_lo, eta_hi] -- the certified
crossing is the linear-response crossing to the bracket's width 1e-3; the
ratio eta_lin/eta_hi in [1 - 1e-3, 1]; D_p > 0 at every pair (the sign: g_1's
quotient rises for every upward shift to first order). (2) THE DERIVATIVE
INDEPENDENTLY: at every cell and prime the closed-form dP_p/d eta agrees with
a central difference of the producer's shell sum in balls (h = 2^{-prec/3})
to 1e-30 relative, and at delta = 1.0 and 2.0 with a central difference of the
bench's K x K shifted Gram on g_1 to 1e-20. (3) THE DILATION EDGE: at every
cell the all-shells rescaling log p -> (1 - eps) log p has a certified bracket
(negative ball at eps_hi, positive at eps_lo, width <= 1 + 1e-3), eps_lin =
lambda_1/sum_p (log p) D_p inside it, and the harmonic composition eps_hi *
sum_p log p / eta_p^hi within 1e-3 of 1; the eps_hi ball re-derived live by
the K x K path at delta = 1.0 and 2.0. (4) THE ARCHIMEDEAN PIN: the stored
quotients of g_1 on G - eps N are negative at eps = lambda_1's upper end and
positive at -eps; live at delta = 1.0 (K = 48): for three eps the Rayleigh
quotient of a vector on G - eps N equals its quotient on G minus eps to the
balls' width -- the constant psi(1/4) - log pi enters only on the diagonal
(weil_prime_gram.py), so every vector's quotient, hence the ground state,
shifts by exactly -eps. (5) THE PAPER'S NUMBERS: the block's table rows
declared as needles and parsed back (D_2 to 1e-4, the ratio band, eps_hi
outward within 2e-3, the composition to 1e-3). (6) mangle probes; (7) the
chain obligation to cascade_prime_ball.py; (8) the paper needles and the
census.

WHAT IS NOT CLAIMED. Nothing about the perturbed forms beyond the certified
points; the linear law is a statement about the fixed vector g_1's quotient
(the certified crossings ARE the fixed-vector crossings; the re-minimised
crossings of 1bo(ii) sit within 1 percent of them at delta <= 2.0); no lower
bound on any window; nothing about zeros; no Riemann Hypothesis consequence.
"""
import math, os, sys, json

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from weil_linear_response import run as run_LR, AutocorrDeriv, dP_deta
from weil_knife_edge import run as run_KE, CELLS as KCELLS, TOL, Autocorr, prime_shells
from weil_prime_gram import gram, rayleigh, minimiser
from weil_factorisation_bench import shifted, _shell_matrix
from flint import arb, arb_mat, ctx

PAPER_NEEDLES = [
    {'g': 'g8', 's': 'Theorem 1bp (the knife-edge is linear response', 'form': 'plain'},
    {'g': 'g8', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 7},
    {'s': '`cascade_linear_response.py`', 'min': 2, 'g': 'g8'},
    {'s': 'the **97 scripts cited in place** above', 'form': 'ws', 'g': 'g8'},
    {'s': 'extended by Theorems 1i–1bu:', 'form': 'ws', 'g': 'g8'},
    {'g': 'g5', 's': '| 1.0 | −13.882 | 0.1876 | 0.9993 | 7.194×10⁻⁶ | 0.9997 |', 'form': 'ws'},
    {'g': 'g5', 's': '| 1.3828125 | −27.754 | 0.3189 | 0.9993 | 3.989×10⁻¹² | 1.0001 |', 'form': 'ws'},
    {'g': 'g5', 's': '| 2.0 | −67.233 | 0.4199 | 0.9994 | 2.133×10⁻²⁹ | 1.0000 |', 'form': 'ws'},
    {'g': 'g5', 's': '| 2.3 | −98.267 | 0.4462 | 0.9994 | 6.633×10⁻⁴³ | 1.0000 |', 'form': 'ws'},
    {'g': 'g5', 's': '| 2.6 | −140.713 | 0.4644 | 0.9994 | 2.335×10⁻⁶¹ | 1.0000 |', 'form': 'ws'},
    {'g': 'g5', 's': '| 3.0 | −221.899 | 0.4807 | 0.9994 | 1.236×10⁻⁹⁶ | 1.0000 |', 'form': 'ws'},
    {'g': 'g5', 's': '| 3.5 | −383.282 | 0.4931 | 0.9996 | 9.794×10⁻¹⁶⁷ | 0.9999 |', 'form': 'ws'},
    {'g': 'g5', 's': 'η_lin/η_hi between 0.9993 and 1.0000 at the pairs (gated in [1 − 10⁻³, 1])', 'form': 'ws'},
    {'g': 'g5', 's': 'D₂ = 0.1876, 0.3189, 0.4199, 0.4462, 0.4644, 0.4807, 0.4931 at the cells', 'form': 'ws'},
    {'g': 'g5', 's': 'within 10⁻³ of 1 at every cell (0.9996–1.0002, gated)', 'form': 'ws'},
    {'g': 'g5', 's': '3.487×10⁻¹⁶⁷ from above', 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ORDER = ["d1.0", "d1.38", "d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
LR = {c: run_LR(c) for c in ORDER}
KE = {c: run_KE(c) for c in ORDER}

# ---------------------------------------------------------------- g0
ok = all(LR[c]["cell"] == c and abs(LR[c]["delta"] - KCELLS[c]["delta"]) < 1e-12 and LR[c]["K"] == KCELLS[c]["K"] and LR[c]["prec"] == KCELLS[c]["prec"] for c in ORDER)
ok &= all(abs(float(LR[c]["lambda1"]["upper"]) - float(KE[c]["lambda1"]["upper"])) <= 1e-20*float(KE[c]["lambda1"]["upper"]) for c in ORDER)
ok &= all(LR[c]["primes"] == KE[c]["primes"] for c in ORDER)
gate("g0 the seven linear-response cells load at their keys with Theorem 1bo's cells, primes and lambda_1 balls (upper ends within 1e-20)", ok)

# ---------------------------------------------------------------- g1
ok = True; ratios = []
for c in ORDER:
    for p, r in LR[c]["per_prime"].items():
        ke = KE[c]["per_prime"][p]
        ok &= r["eta_lo"] == ke["eta_lo"] and r["eta_hi"] == ke["eta_hi"]
        lo, hi = float(r["eta_lin"]["lower"]), float(r["eta_lin"]["upper"])
        ok &= r["lin_in_bracket"] and ke["eta_lo"] <= lo and hi <= ke["eta_hi"]
        ok &= r["D_positive"] and float(r["D"]["lower"]) > 0
        ratios.append(hi/ke["eta_hi"])
    ok &= LR[c]["per_prime"]["2"]["D"]["rad_log2"] <= -LR[c]["prec"]/2 + 20
ok &= min(ratios) >= 1 - TOL and max(ratios) <= 1 + 1e-12
gate("g1 the law: at every (cell, prime) eta_lin = lambda_1/D_p lies inside 1bo's certified bracket, eta_lin/eta_hi in [1 - 1e-3, 1] ("
     + f"min {min(ratios):.5f}, max {max(ratios):.5f}" + "), D_p > 0 at every pair; D_2 = " + ", ".join(f"{float(LR[c]['per_prime']['2']['D']['mid']):.4f}" for c in ORDER), ok)

# ---------------------------------------------------------------- g2
ok = True; g2 = []
for c in ORDER:
    st = LR[c]; d, K, prec = st["delta"], st["K"], st["prec"]
    with ctx.workprec(prec):
        a = arb(d)/2
        cv = [arb(x) for x in KE[c]["coeffs"]]
        fg = AutocorrDeriv(cv, a, prec)
        h = arb(2)**(-(prec//3))
        for p in st["primes"]:
            closed = dP_deta(fg, p, prec)
            cd = (prime_shells(fg, p, h, prec) - prime_shells(fg, p, -h, prec))/(2*h)
            rel = float(abs(closed - cd).upper()/abs(closed).upper()) if abs(closed).upper() > 0 else 0.0
            g2.append(rel); ok &= rel <= 1e-30
# the K x K path at delta = 1.0 and 2.0: a central difference of the bench's shifted Gram on g_1
for c in ("d1.0", "d2.0"):
    st = LR[c]; d, K, prec = st["delta"], st["K"], st["prec"]
    G, N, pp = gram(d, K, prec)
    with ctx.workprec(prec):
        a = arb(d)/2
        cv = [arb(x) for x in KE[c]["coeffs"]]
        den = arb(0)
        for i in range(K): den += N[i]*cv[i]*cv[i]
        hf = 2.0**(-(prec//3))
        for p in st["primes"]:
            Gp, _, _ = shifted(d, K, prec, p, hf); Gm, _, _ = shifted(d, K, prec, p, -hf)
            dQ = (rayleigh(Gp, N, cv, prec) - rayleigh(Gm, N, cv, prec))/(2*arb(hf))     # dQ^eta/d eta = -dP/d eta / den = D_p
            D = arb(st["per_prime"][str(p)]["D"]["mid"])
            rel = float(abs(dQ - D).upper()/abs(D).upper())
            g2.append(rel); ok &= rel <= 1e-20
gate("g2 the derivative independently: the closed-form dP_p/d eta against a central difference of the shell sum in balls at every cell and prime, and against the K x K shifted Gram at delta = 1.0 and 2.0 (max rel "
     + f"{max(g2):.1e}" + ")", ok)

# ---------------------------------------------------------------- g3
ok = True; harm = {}
for c in ORDER:
    dl = LR[c]["dilation"]
    ok &= dl["status"] == "bracketed" and dl["q_hi"]["negative"] and dl["q_lo"]["positive"] and 0 < dl["eps_lo"] < dl["eps_hi"] and dl["eps_hi"]/dl["eps_lo"] <= 1 + TOL + 1e-12
    ok &= dl["lin_in_bracket"] and abs(dl["harmonic"] - 1) <= 1e-3
    harm[c] = dl["harmonic"]
# the eps_hi ball re-derived by the K x K path at delta = 1.0 and 2.0: the Gram with every prime's shells rescaled
for c in ("d1.0", "d2.0"):
    st = LR[c]; d, K, prec = st["delta"], st["K"], st["prec"]; dl = st["dilation"]
    G, N, pp = gram(d, K, prec)
    with ctx.workprec(prec):
        a = arb(d)/2; twoa = 2*a
        cv = [arb(x) for x in KE[c]["coeffs"]]
        Ge = arb_mat(G)
        for p in st["primes"]:
            lp = arb(p).log()
            for e, sign in ((arb(0), +1), (-arb(dl["eps_hi"])*lp, -1)):
                lpe = lp + e; k = 1
                while k*lpe < twoa:
                    Ge = Ge + sign*_shell_matrix(k*lpe, lpe, K, a, prec); k += 1
        r = rayleigh(Ge, N, cv, prec)
        ok &= r.upper() < 0 and abs(float(r.mid()) - float(dl["q_hi"]["mid"])) <= 1e-20*abs(float(dl["q_hi"]["mid"]))
gate("g3 the dilation edge: at every cell a certified bracket of the all-shells rescaling (negative ball at eps_hi), eps_lin inside it, the harmonic composition eps_hi * sum_p log p / eta_p within 1e-3 of 1 ("
     + ", ".join(f"{harm[c]:.5f}" for c in ORDER) + "); the eps_hi ball re-derived by the K x K path at delta = 1.0 and 2.0", ok)

# ---------------------------------------------------------------- g4
ok = all(LR[c]["archimedean"]["at_plus_lambda_upper"]["negative"] and LR[c]["archimedean"]["at_minus_lambda_upper"]["positive"]
         and LR[c]["archimedean"]["at_half_lambda"]["positive"] for c in ORDER)
G1, N1, _ = gram(1.0, 48, 400)
c1, _ = minimiser(G1, N1, 400)
with ctx.workprec(400):
    cv = [arb(x) for x in c1]
    base = rayleigh(G1, N1, cv, 400)
    g4 = []
    for eps in (arb(1)/1000, arb(-3)/100, arb(base.mid())):
        Ge = arb_mat(G1)
        for i in range(48): Ge[i, i] = Ge[i, i] - eps*N1[i]
        r = rayleigh(Ge, N1, cv, 400)
        dev = float(abs(r - (base - eps)).upper())
        g4.append(dev); ok &= dev <= 1e-60
gate("g4 the archimedean pin: the stored quotients of g_1 on G - eps N negative at eps = lambda_1's upper end, positive at -eps and at eps/2, at every cell; live at delta = 1.0: the quotient on G - eps N equals the quotient on G minus eps to the balls' width (max "
     + f"{max(g4):.1e}" + ") -- the constant enters only on the diagonal", ok)

# ---------------------------------------------------------------- g5
import paper_needles
ROWS = ['| 1.0 | −13.882 | 0.1876 | 0.9993 | 7.194×10⁻⁶ | 0.9997 |', '| 1.3828125 | −27.754 | 0.3189 | 0.9993 | 3.989×10⁻¹² | 1.0001 |', '| 2.0 | −67.233 | 0.4199 | 0.9994 | 2.133×10⁻²⁹ | 1.0000 |', '| 2.3 | −98.267 | 0.4462 | 0.9994 | 6.633×10⁻⁴³ | 1.0000 |', '| 2.6 | −140.713 | 0.4644 | 0.9994 | 2.335×10⁻⁶¹ | 1.0000 |', '| 3.0 | −221.899 | 0.4807 | 0.9994 | 1.236×10⁻⁹⁶ | 1.0000 |', '| 3.5 | −383.282 | 0.4931 | 0.9996 | 9.794×10⁻¹⁶⁷ | 0.9999 |']
S_LAW = 'η_lin/η_hi between 0.9993 and 1.0000 at the pairs (gated in [1 − 10⁻³, 1])'
S_D2 = 'D₂ = 0.1876, 0.3189, 0.4199, 0.4462, 0.4644, 0.4807, 0.4931 at the cells'
S_HARM = 'within 10⁻³ of 1 at every cell (0.9996–1.0002, gated)'
S_PIN = '3.487×10⁻¹⁶⁷ from above'
# each call carries its literal (the precheck's clause D); the strings equal ROWS / S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, '| 1.0 | −13.882 | 0.1876 | 0.9993 | 7.194×10⁻⁶ | 0.9997 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 1.3828125 | −27.754 | 0.3189 | 0.9993 | 3.989×10⁻¹² | 1.0001 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 2.0 | −67.233 | 0.4199 | 0.9994 | 2.133×10⁻²⁹ | 1.0000 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 2.3 | −98.267 | 0.4462 | 0.9994 | 6.633×10⁻⁴³ | 1.0000 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 2.6 | −140.713 | 0.4644 | 0.9994 | 2.335×10⁻⁶¹ | 1.0000 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 3.0 | −221.899 | 0.4807 | 0.9994 | 1.236×10⁻⁹⁶ | 1.0000 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 3.5 | −383.282 | 0.4931 | 0.9996 | 9.794×10⁻¹⁶⁷ | 0.9999 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'η_lin/η_hi between 0.9993 and 1.0000 at the pairs (gated in [1 − 10⁻³, 1])', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'D₂ = 0.1876, 0.3189, 0.4199, 0.4462, 0.4644, 0.4807, 0.4931 at the cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'within 10⁻³ of 1 at every cell (0.9996–1.0002, gated)', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '3.487×10⁻¹⁶⁷ from above', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g5'] == ROWS + [S_LAW, S_D2, S_HARM, S_PIN]
_SUP = str.maketrans('⁻⁰¹²³⁴⁵⁶⁷⁸⁹', '-0123456789')
def _num(s):
    s = s.strip().replace('−', '-').replace('×10', 'e').translate(_SUP)
    return float(s)
# the table rows: delta | ln lambda_1 <= (1bn's ceiling to 1e-3) | D_2 (4 decimals, nearest) | min_p eta_lin/eta_hi (floor, 4 decimals)
#                 | eps_hi (up, 4 significant figures) | the harmonic composition (4 decimals, nearest)
_ratios = []; _harms = []; _D2 = []
for _row, c in zip(ROWS, ORDER):
    st = LR[c]; f = [x.strip() for x in _row.strip('|').split('|')]
    ok &= abs(_num(f[0]) - st["delta"]) < 1e-12
    lnl = _num(f[1]); ok &= lnl >= float(st["lambda1"]["ln_upper"]) and lnl - float(st["lambda1"]["ln_upper"]) < 1e-3 + 1e-9
    d2 = float(st["per_prime"]["2"]["D"]["mid"]); ok &= abs(_num(f[2]) - d2) <= 5e-5 + 1e-12; _D2.append(d2)
    rmin = min(float(r["eta_lin"]["upper"])/r["eta_hi"] for r in st["per_prime"].values())
    rmax = max(float(r["eta_lin"]["upper"])/r["eta_hi"] for r in st["per_prime"].values())
    ok &= _num(f[3]) <= rmin < _num(f[3]) + 1e-4 + 1e-12; _ratios += [rmin, rmax]
    eps = st["dilation"]["eps_hi"]; ok &= eps <= _num(f[4]) <= eps*(1 + 2e-3)
    h = st["dilation"]["harmonic"]; ok &= abs(_num(f[5]) - h) <= 5e-5 + 1e-12; _harms.append(h)
# the sentences
_m = __import__("re").search(r"between ([0-9.]+) and ([0-9.]+)", S_LAW)
ok &= _num(_m.group(1)) <= min(_ratios) and max(_ratios) <= _num(_m.group(2)) and _num(_m.group(2)) - _num(_m.group(1)) < 1e-3 + 1e-4
_d = [float(x) for x in S_D2.split("=")[1].split(" at ")[0].split(",")]
ok &= len(_d) == 7 and all(abs(x - y) <= 5e-5 + 1e-12 for x, y in zip(_d, _D2))
ok &= all(_D2[i] < _D2[i + 1] for i in range(6))          # "rising through the cells (gated increasing)"
ok &= all(_D2[i] < 0.5 for i in range(7))
_m = __import__("re").search(r"\(([0-9.]+)–([0-9.]+), gated\)", S_HARM)
ok &= _num(_m.group(1)) <= min(_harms) and max(_harms) <= _num(_m.group(2)) and all(abs(h - 1) <= 1e-3 for h in _harms)
_pin = _num(S_PIN.split(" from")[0]); _l35 = float(LR["d3.5"]["lambda1"]["upper"])
ok &= _l35 <= _pin <= _l35*(1 + 2e-3)
# the pair count and 1bo's ratio band as 1/D_2 to the bracket's width
ok &= sum(len(LR[c]["per_prime"]) for c in ORDER) == 36
ok &= all(abs(KE[c]["per_prime"]["2"]["hi_over_lambda"]*_D2[i] - 1) <= TOL + 1e-9 for i, c in enumerate(ORDER))
ok &= abs(KE["d1.0"]["per_prime"]["2"]["hi_over_lambda"] - 5.33) < 0.005 and abs(KE["d3.5"]["per_prime"]["2"]["hi_over_lambda"] - 2.03) < 0.005   # "from 5.33 to 2.03"
gate("g5 the paper's numbers parsed back from the declared needles: the seven rows (ln lambda_1 the ceiling to 1e-3, D_2 to 5e-5, the ratio floor to 1e-4, eps_hi outward within 2e-3, the composition to 5e-5), the ratio band, the D_2 list (increasing, below 1/2), the composition band, the delta = 3.5 pin, 36 pairs, 1bo's eta_2/lambda_1 = 1/D_2 to the bracket's width", ok)


# ---------------------------------------------------------------- g6
good = dict(LR["d2.0"]["per_prime"]["2"])
def law_ok(r, ke):
    return r["lin_in_bracket"] and ke["eta_lo"] <= float(r["eta_lin"]["lower"]) and float(r["eta_lin"]["upper"]) <= ke["eta_hi"] and float(r["D"]["lower"]) > 0
ke2 = KE["d2.0"]["per_prime"]["2"]
bad1 = dict(good); bad1["eta_lin"] = dict(good["eta_lin"]); bad1["eta_lin"]["upper"] = repr(ke2["eta_hi"]*1.01)
bad2 = dict(good); bad2["D"] = dict(good["D"]); bad2["D"]["lower"] = "-1e-5"
bad3 = dict(good); bad3["lin_in_bracket"] = False
ok = law_ok(good, ke2) and not law_ok(bad1, ke2) and not law_ok(bad2, ke2) and not law_ok(bad3, ke2)
gate("g6 mangle probes: the law predicate fails on eta_lin above the bracket, a non-positive D, a cleared flag", ok)

# ---------------------------------------------------------------- g7
from cascade_tower import chain_ok
gate("g7 the chain obligation to cascade_prime_ball.py (Theorem 1bo) met", chain_ok("cascade_prime_ball.py"))

# ---------------------------------------------------------------- g8
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g8 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g8 the 1bp paper needles and the footer census (declared surface)", ok)

print(("\nALL GATES PASS (9/9)" if not fails else f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
