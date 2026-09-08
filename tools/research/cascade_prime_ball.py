#!/usr/bin/env python3
"""Theorem 1bo -- the prime-built ball, the knife-edge, and the bench: the
adelic unit ball stated as the object (Tate, in the cascade's shell
language; every identity gated live), the precision to which Weil
positivity at support delta pins the primes CERTIFIED at the seven
slack-law cells (weil_knife_edge.py: for every prime p <= e^delta a shift
of log p at which the true form has a negative Rayleigh ball), and the
factorisation bench (weil_factorisation_bench.py) with its calibrations
gated live. Tower member 24 (top).

THE CLAIMS GATED. (0) THE KNIFE-EDGE CERTIFICATES load at their keys at the
seven cells with the cells' (delta, K, prec) equal to Theorem 1bn's (delta,
K2, prec). (1) THE VECTOR: the producer's lambda_1 ball reproduces 1bn's
stored K2 ball (the same flint eigenvector; upper ends within 1e-20
relative), K coefficients stored. (2) THE BRACKETS: at every cell and every
prime p <= e^delta the search is bracketed -- the Rayleigh ball of g_1 on
Q^{-eta_hi} negative at its upper end, on Q^{-eta_lo} positive at its lower
end, eta_hi/eta_lo <= 1 + 1e-3 -- the primes equal those of the cell's
prime-power list, and eta_2/lambda_1 lies in [1, 10] at every cell (the
paper's "comparable with lambda_1 itself"). (3) THE TWO-SIDED WINDOWS
(p = 2, the three cells at delta <= 2.0, the perturbed Gram re-minimised at
every step): both brackets bracketed, the re-minimised downward crossing
at or below the fixed-vector one, the upward crossing at least 100 times
the downward. (4) INDEPENDENT RE-CERTIFICATION, K x K path: at every cell
the O(K) shell sum at eta = 0 (the producer's evaluation path) equals the
Gram's prime part on g_1 computed shell by shell as full matrices (the
bench's path), to 1e-30 relative; and for p = 2 at every cell the bench's
shifted Gram at -eta_hi gives g_1 a negative Rayleigh ball, at -eta_lo a
positive one -- the headline shifts certified twice, by two code paths.
(5) THE SHELL IDENTITIES LIVE: the p-adic shell series against the Euler
factor in balls with the exact geometric remainder (p = 2..11, real and
complex s; 1e-50); the archimedean shell series against Gamma_R by
quadrature (1e-20); the truncated Euler product against zeta within the
rigorous tail bound P^{1-sigma}/((sigma-1)(1-P^{-sigma})) (s = 2, 3, 2+5i;
P = 100, 1000); the self-duality character sums of 1_{Z_p} (p = 2, 3, 5;
m <= 3; 1e-12); theta inversion and Lambda(s) = Lambda(1-s) (1e-30); the
shell-weight sum sum_{n<=N} Lambda(n) n^{-s} against -zeta'/zeta within its
tail bound (s = 2, 3). (6) THE BENCH CALIBRATIONS LIVE at delta = 1.0: the
zero side (6700 zeros + tail) on the C_c^inf bump within 1e-13 of the true
form and on the minimiser within [1e-5, 1e-4] (the documented limitation of
the raw cosine basis); the archimedean-only candidate rejected by a
certified margin (its Rayleigh quotient on g_1 above 1e-2, the true below
1e-6). (7) THE PAPER'S NUMBERS: the block's table rows declared as needles
and parsed back -- every stated shift at or above (rounded outward) the
stored eta_hi within 1e-3, the ratios to two decimals, the lambda_1 column
equal to 1bn's pins. (8) mangle probes; (9) the chain obligation to
cascade_true_form_bounds.py; (10) the paper needles and the census.

WHAT IS NOT CLAIMED. Nothing about the zeros; no lower bound on any
window; no statement about the perturbed forms beyond the certified points
(eta_lo is where g_1 fails to witness, not where positivity holds); no
Riemann Hypothesis consequence.
"""
import math, os, sys, json, cmath

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from weil_knife_edge import run as run_KE, CELLS as KCELLS, TOL, Autocorr, prime_shells, primes_of
from true_form_cells import run as run_TF, CELLS as TCELLS
from weil_prime_gram import gram, rayleigh
from weil_factorisation_bench import archimedean, shifted, zeros, bump_vector, compare, _shell_matrix
from flint import arb, acb, arb_mat, ctx
import mpmath as mp

PAPER_NEEDLES = [
    {'g': 'g10', 's': 'Theorem 1bo (the prime-built ball, the knife-edge, and the bench', 'form': 'plain'},
    {'g': 'g10', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 6},
    {'s': '`cascade_prime_ball.py`', 'min': 2, 'g': 'g10'},
    {'s': 'the **91 scripts cited in place** above', 'form': 'ws', 'g': 'g10'},
    {'s': 'extended by Theorems 1i–1bo:', 'form': 'ws', 'g': 'g10'},
    # the block's table rows (ws form), parsed back by g7
    #ROWS#
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ORDER = ["d1.0", "d1.38", "d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
KE = {c: run_KE(c) for c in ORDER}
TF = {c: run_TF(c) for c in ORDER}

# ---------------------------------------------------------------- g0
ok = all(KE[c]["verdict"].startswith("CERTIFIED") and KE[c]["cell"] == c for c in ORDER)
ok &= all(abs(KCELLS[c]["delta"] - TCELLS[c]["delta"]) < 1e-12 and KCELLS[c]["K"] == TCELLS[c]["K2"] and KCELLS[c]["prec"] == TCELLS[c]["prec"] for c in ORDER)
ok &= all(abs(KE[c]["delta"] - KCELLS[c]["delta"]) < 1e-12 and KE[c]["K"] == KCELLS[c]["K"] and KE[c]["prec"] == KCELLS[c]["prec"] for c in ORDER)
ok &= list(KCELLS) == ORDER
gate("g0 the seven knife-edge certificates load at their keys; the cells' (delta, K, prec) equal Theorem 1bn's (delta, K2, prec)", ok)

# ---------------------------------------------------------------- g1
ok = True
for c in ORDER:
    lu = float(KE[c]["lambda1"]["upper"]); tu = float(TF[c]["min_K2"]["upper"])
    ok &= KE[c]["lambda1"]["positive"] and abs(lu - tu) <= 1e-20*tu and len(KE[c]["coeffs"]) == KE[c]["K"]
    ok &= KE[c]["lambda1"]["rad_log2"] is not None and KE[c]["lambda1"]["rad_log2"] <= -KE[c]["prec"]/2
gate("g1 the vector: the producer's lambda_1 ball reproduces 1bn's stored K2 ball (upper ends within 1e-20 relative), radii below 2^(-prec/2), K coefficients stored", ok)

# ---------------------------------------------------------------- g2
ok = True; ratio2 = {}; loosest = {}
for c in ORDER:
    st = KE[c]; pp = st["prime_powers"]
    ok &= pp == TF[c]["prime_powers"] and st["primes"] == primes_of(pp)
    ok &= sorted(int(p) for p in st["per_prime"]) == st["primes"]
    lam = float(st["lambda1"]["upper"])
    for p, r in st["per_prime"].items():
        ok &= r.get("status") == "bracketed" and r["q_hi"]["negative"] and r["q_lo"]["positive"] and not r["q_hi"]["positive"] and not r["q_lo"]["negative"]
        ok &= 0 < r["eta_lo"] < r["eta_hi"] and r["eta_hi"]/r["eta_lo"] <= 1 + TOL + 1e-12
        ok &= abs(r["hi_over_lambda"] - r["eta_hi"]/lam) <= 1e-9*r["hi_over_lambda"]
    ratio2[c] = st["per_prime"]["2"]["hi_over_lambda"]
    ok &= 1 <= ratio2[c] <= 10
    loosest[c] = max(st["per_prime"].items(), key=lambda kv: kv[1]["eta_hi"])
gate("g2 the brackets: at every cell and every prime, Q^(-eta_hi)(g_1) negative and Q^(-eta_lo)(g_1) positive in balls, eta_hi/eta_lo <= 1 + 1e-3; the primes those of the prime-power lists; eta_2/lambda_1 in [1, 10] ("
     + ", ".join(f"{ratio2[c]:.2f}" for c in ORDER) + "); loosest prime per cell " + ", ".join(f"{loosest[c][0]}: {loosest[c][1]['eta_hi']:.3e}" for c in ORDER), ok)

# ---------------------------------------------------------------- g3
ok = True; asym = {}
for c in ORDER:
    two = KE[c]["two_sided"]
    if KCELLS[c]["two_sided"]:
        ok &= two is not None and two["p"] == 2
        m, q = two["minus"], two["plus"]
        ok &= m["status"] == "bracketed" and q["status"] == "bracketed" and m["sign"] == -1 and q["sign"] == 1
        ok &= m["q_hi"]["negative"] and m["q_lo"]["positive"] and q["q_hi"]["negative"] and q["q_lo"]["positive"]
        ok &= m["eta_hi"] <= KE[c]["per_prime"]["2"]["eta_hi"]*(1 + 1e-9)
        asym[c] = q["eta_hi"]/m["eta_hi"]
        ok &= asym[c] >= 100
    else:
        ok &= two is None
gate("g3 the two-sided windows for p = 2 at delta <= 2.0 (re-minimised): both crossings bracketed with certified signs, the downward one at or below the fixed-vector crossing, the upward/downward asymmetry >= 100 ("
     + ", ".join(f"{asym[c]:.3g}" for c in asym) + ")", ok)

# ---------------------------------------------------------------- g4
ok = True; g4 = []
for c in ORDER:
    st = KE[c]; d, K, prec = st["delta"], st["K"], st["prec"]
    G, N, pp = gram(d, K, prec)
    with ctx.workprec(prec):
        a = arb(d)/2
        cv = [arb(x) for x in st["coeffs"]]
        v = arb_mat(K, 1)
        for i in range(K): v[i, 0] = cv[i]
        den = arb(0)
        for i in range(K): den += N[i]*cv[i]*cv[i]
        # (a) the O(K) path at eta = 0 against the K x K shell matrices, prime by prime
        fg = Autocorr(cv, a, prec)
        for p in st["primes"]:
            Pm = arb_mat(K, K); k = 1; lp = arb(p).log()
            while k*lp < 2*a:
                Pm = Pm + _shell_matrix(k*lp, lp, K, a, prec); k += 1
            qK = (v.transpose()*Pm*v)[0, 0]/den
            qO = prime_shells(fg, p, 0, prec)/den
            rel = float(abs(qK - qO).upper()/abs(qK).upper()) if abs(qK).upper() > 0 else 0.0
            g4.append(rel); ok &= rel <= 1e-30
            ok &= abs(float(st["per_prime"][str(p)]["shell_sum_eta0"]) - float(qO.mid())) <= 1e-20*abs(float(qO.mid()))
        # (b) the headline shift for p = 2 re-certified through the bench's shifted Gram (K x K)
        r = st["per_prime"]["2"]
        Chi, _, _ = shifted(d, K, prec, 2, -r["eta_hi"]); Clo, _, _ = shifted(d, K, prec, 2, -r["eta_lo"])
        rhi = rayleigh(Chi, N, cv, prec); rlo = rayleigh(Clo, N, cv, prec)
        ok &= rhi.upper() < 0 and rlo.lower() > 0
        # the two paths agree on the perturbed value itself
        ok &= abs(float(rhi.mid()) - float(r["q_hi"]["mid"])) <= 1e-20*abs(float(r["q_hi"]["mid"]))
gate("g4 independent re-certification, K x K path: the O(K) shell sums at eta = 0 equal the Gram's prime part on g_1 shell by shell at every cell and prime (max rel "
     + f"{max(g4):.1e}" + " <= 1e-30); the bench's shifted Gram for p = 2 gives g_1 a negative ball at -eta_hi and a positive one at -eta_lo at every cell, the values agreeing to 1e-20", ok)

# ---------------------------------------------------------------- g5
ok = True; g5 = {}
# (a) p-adic shell series in balls
mx = 0.0
with ctx.workprec(200):
    for p in (2, 3, 5, 7, 11):
        for s in (arb(2), arb(1)/2 + arb(1)/1000, acb(arb(3)/2, arb(7))):
            T = acb if isinstance(s, acb) else arb
            r = T(p)**(-s); Kc = 200
            partial = sum((T(p)**(-k*s)) for k in range(Kc))
            dev = float(abs(partial + r**Kc/(1 - r) - 1/(1 - r)).upper())
            mx = max(mx, dev)
g5["a"] = mx; ok &= mx <= 1e-50
# (b) archimedean shell series
mp.mp.dps = 40; mx = 0.0
for s in (mp.mpf(1), mp.mpf(2), mp.mpf('0.5'), mp.mpf(5), mp.mpc(0.5, 3)):
    q = 2*mp.quad(lambda x: mp.e**(-mp.pi*x**2)*x**(s - 1), [0, 1, 2, 4, mp.inf])
    mx = max(mx, float(abs(q - mp.pi**(-s/2)*mp.gamma(s/2))))
g5["b"] = mx; ok &= mx <= 1e-20
# (c) the truncated Euler product against zeta within the rigorous tail bound
def primes_upto(P): return [n for n in range(2, P + 1) if all(n % q for q in range(2, int(n**0.5) + 1))]
worst = 0.0
for s in (mp.mpf(2), mp.mpf(3), mp.mpc(2, 5)):
    for P in (100, 1000):
        prod = mp.mpf(1)
        for p in primes_upto(P): prod *= 1/(1 - mp.mpf(p)**(-s))
        sig = mp.re(s); bound = P**(1 - sig)/((sig - 1)*(1 - P**(-sig)))
        dev = abs(mp.log(mp.zeta(s)) - mp.log(prod))
        worst = max(worst, float(dev/bound)); ok &= dev <= bound
g5["c"] = worst
# (d) self-duality character sums
mx = 0.0
for p in (2, 3, 5):
    for m in (1, 2, 3):
        for aa in (1, p - 1, p + 1):
            if aa % p: mx = max(mx, abs(sum(cmath.exp(2j*math.pi*aa*x/p**m) for x in range(p**m))/p**m))
        mx = max(mx, abs(sum(cmath.exp(0j*x) for x in range(p**m))/p**m - 1))
g5["d"] = mx; ok &= mx <= 1e-12
# (e) theta inversion and the functional equation
mx = 0.0
th = lambda t: mp.nsum(lambda n: mp.e**(-mp.pi*n**2*t), [-mp.inf, mp.inf])
for t in (mp.mpf('0.7'), mp.mpf('1.3'), mp.mpf(2)): mx = max(mx, float(abs(th(1/t) - mp.sqrt(t)*th(t))))
Lam = lambda s: mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
for s in (mp.mpc(0.3, 2), mp.mpc(2, 7), mp.mpc(0.5, 14.1)): mx = max(mx, float(abs(Lam(s) - Lam(1 - s))/abs(Lam(s))))
g5["e"] = mx; ok &= mx <= 1e-30
# (f) the shell-weight sum against -zeta'/zeta within its tail bound
def Lambda_list(N):
    out = []
    for n in range(2, N + 1):
        p = next(q for q in range(2, n + 1) if n % q == 0); m = n
        while m % p == 0: m //= p
        if m == 1: out.append((n, p))
    return out
worst = 0.0; LL = Lambda_list(2000)
for s in (mp.mpf(2), mp.mpf(3)):
    N = 2000; sm = sum(mp.log(p)*mp.mpf(n)**(-s) for n, p in LL)
    bound = N**(1 - s)*(mp.log(N)/(s - 1) + 1/(s - 1)**2)
    dev = abs(sm + mp.zeta(s, derivative=1)/mp.zeta(s))
    worst = max(worst, float(dev/bound)); ok &= dev <= bound
g5["f"] = worst
gate("g5 the shell identities LIVE: (a) p-adic shell series vs the Euler factor in balls, max " + f"{g5['a']:.1e}" + " <= 1e-50; (b) archimedean shell series vs Gamma_R, max "
     + f"{g5['b']:.1e}" + " <= 1e-20; (c) truncated Euler product within the tail bound (worst dev/bound " + f"{g5['c']:.2f}" + "); (d) 1_(Z_p) self-dual character sums, max "
     + f"{g5['d']:.1e}" + "; (e) theta inversion and Lambda(s) = Lambda(1-s), max " + f"{g5['e']:.1e}" + " <= 1e-30; (f) shell-weight sum vs -zeta'/zeta within the tail bound (worst " + f"{g5['f']:.2f}" + ")", ok)

# ---------------------------------------------------------------- g6
ok = True
G1, N1, _ = gram(1.0, 48, 400)
from weil_prime_gram import minimiser
c1, _ = minimiser(G1, N1, 400)
with ctx.workprec(400):
    vecs = {"minimiser": [arb(x) for x in c1], "bump": bump_vector(1.0, 48)}
rz = compare(G1, zeros(1.0, 48, 400), N1, vecs, 400)
ok &= rz["bump"]["rel"] <= 1e-13 and 1e-5 <= rz["minimiser"]["rel"] <= 1e-4
G2, N2, _ = gram(1.0, 120, 600)
with ctx.workprec(600):
    cv = [arb(x) for x in KE["d1.0"]["coeffs"]]
Ca, _, _ = archimedean(1.0, 120, 600)
ra = compare(G2, Ca, N2, {"g1": cv}, 600)
ok &= ra["g1"]["rq_cand"].lower() > 1e-2 and ra["g1"]["rq_true"].upper() < 1e-6 and float(ra["max_abs"]) >= 0.1
gate("g6 the bench calibrations LIVE at delta = 1.0: the zero side on the bump within 1e-13 (" + f"{rz['bump']['rel']:.1e}" + ") and on the minimiser in [1e-5, 1e-4] ("
     + f"{rz['minimiser']['rel']:.1e}" + "); the archimedean-only candidate rejected -- Rayleigh on g_1 " + ra["g1"]["rq_cand"].str(5) + " against the true " + ra["g1"]["rq_true"].str(5)
     + ", entrywise max " + ra["max_abs"], ok)

# ---------------------------------------------------------------- g7
# the paper's own numbers (the round-300 F300-2 standard): the table rows and the (iii) sentences are declared needles
# (g10 checks their presence); here the literals are parsed and tied to the stored values through the needle API
import paper_needles, re as _re
_sup = str.maketrans('⁻⁰¹²³⁴⁵⁶⁷⁸⁹', '-0123456789')
def _num(t):   # a×10^b (superscript exponent) or a plain decimal
    t = t.strip().replace('−', '-')
    m = _re.fullmatch(r'([-+]?)([0-9.]+)×10([⁻⁰¹²³⁴⁵⁶⁷⁸⁹]+)', t)
    if m: return (-1 if m.group(1) == '-' else 1)*float(m.group(2))*10**int(m.group(3).translate(_sup))
    return float(t)
def _outward(stated, certified):   # a stated shift rounded outward: at or above the certified value, within 2e-3
    return 0 <= stated - certified <= 2e-3*certified
ROWS = [#ROWLIST#]
ok = [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g7'] == ROWS + [S_RATIO, S_EDGE]
ok &= len(ROWS) == 7
for c, row in zip(ORDER, ROWS):
    f = [x.strip() for x in row.strip().strip('|').split('|')]
    st = KE[c]; r2 = st["per_prime"]["2"]; lam = float(st["lambda1"]["upper"])
    ok &= len(f) == 6 and abs(float(f[0]) - st["delta"]) < 1e-9
    ok &= abs(_num(f[1]) - round(TF[c]["min_K2"]["ln_upper"], 3)) < 1e-9 and 0 <= _num(f[1]) - TF[c]["min_K2"]["ln_upper"] <= 2e-3
    ok &= _outward(_num(f[2]), r2["eta_hi"])
    ok &= abs(_num(f[3]) - r2["hi_over_lambda"]) <= 0.005 + 1e-9
    pl, el = f[4].split(':'); lp, lr = loosest[c]
    ok &= int(pl) == int(lp) and _outward(_num(el), lr["eta_hi"])
    if KCELLS[c]["two_sided"]:
        m = _re.fullmatch(r'\((−[^,]+), \+([^)]+)\)', f[5]); ok &= m is not None
        if m:
            two = st["two_sided"]
            ok &= _outward(-_num(m.group(1)), two["minus"]["eta_hi"]) and _outward(_num(m.group(2)), two["plus"]["eta_hi"])   # the minus end is written with its sign
    else:
        ok &= f[5] == '—'
# (iii): "η₂/λ₁ between R_LO and R_HI" -- the min and max of the stored ratios to two decimals, rounded outward (down / up)
_m = _re.search(r'between ([0-9.]+) and ([0-9.]+) at the cells', S_RATIO); ok &= _m is not None
if _m:
    ok &= 0 <= min(ratio2.values()) - float(_m.group(1)) <= 0.01 + 1e-9 and 0 <= float(_m.group(2)) - max(ratio2.values()) <= 0.01 + 1e-9
_m = _re.search(r'so to e\^\{−([0-9]+)\} at δ = 3\.5', S_RATIO); ok &= _m is not None
if _m:   # eta_2(3.5) <= e^{-N}: N <= -ln eta_hi
    ok &= float(_m.group(1)) <= -math.log(KE["d3.5"]["per_prime"]["2"]["eta_hi"]) < float(_m.group(1)) + 1
# the edge sentence: the two delta = 1.0 shifts (rounded outward) and the three asymmetries (rounded down: "at least")
_v = [_num(x) for x in _re.findall(r'[0-9.]+×10[⁻⁰¹²³⁴⁵⁶⁷⁸⁹]+', S_EDGE)]
ok &= len(_v) == 2 and _outward(_v[0], KE["d1.0"]["two_sided"]["plus"]["eta_hi"]) and _outward(_v[1], KE["d1.0"]["two_sided"]["minus"]["eta_hi"])
_a = [float(x.replace(',', '')) for x in _re.findall(r'([0-9][0-9,]*)-fold', S_EDGE)]
ok &= len(_a) == 3 and all(0 <= asym[c] - a_ <= 0.05*asym[c] for c, a_ in zip(["d1.0", "d1.38", "d2.0"], _a))
# the bench sentences: the two zero-side agreements (stated at or above the live value, within 10 percent), the archimedean
# candidate's and the true quotient on g_1 (within 1 percent of the live balls), the shifted candidate's two signed values
# (within 1 percent of the stored delta = 1.0 balls for p = 2)
_b = [_num(x) for x in _re.findall(r'[−+]?[0-9.]+×10[⁻⁰¹²³⁴⁵⁶⁷⁸⁹]+', S_BENCH)]
ok &= len(_b) == 2 and rz["bump"]["rel"] <= _b[0] <= 1.1*rz["bump"]["rel"] and rz["minimiser"]["rel"] <= _b[1] <= 1.1*rz["minimiser"]["rel"]
_b = [_num(x) for x in _re.findall(r'[−+]?[0-9.]+×10[⁻⁰¹²³⁴⁵⁶⁷⁸⁹]+', S_BENCH2)]
_r2 = KE["d1.0"]["per_prime"]["2"]
ok &= len(_b) == 4 and abs(_b[0] - float(ra["g1"]["rq_cand"].mid())) <= 0.01*_b[0] and abs(_b[1] - float(ra["g1"]["rq_true"].mid())) <= 0.01*_b[1]
ok &= abs(_b[2] - float(_r2["q_hi"]["mid"])) <= 0.01*abs(_b[2]) and _b[2] < 0 and abs(_b[3] - float(_r2["q_lo"]["mid"])) <= 0.01*_b[3] and _b[3] > 0
gate("g7 the paper's own numbers: the seven table rows and the two (iii) sentences present as declared needles, tied to the declared entries and parsed back -- "
     "ln lambda_1 = 1bn's pins; every stated shift at or above the certified eta_hi within 2e-3; the ratios to 0.005; the loosest prime and its shift; the "
     "two-sided windows; the ratio range outward; e^(-N) with N <= -ln eta_2(3.5); the delta = 1.0 shifts outward; the asymmetries rounded down within 5 percent; the bench sentences' six values against the live gates and the stored delta = 1.0 balls", ok)

# ---------------------------------------------------------------- g8
good = dict(KE["d2.0"]["per_prime"]["2"])
def bracket_ok(r):
    return (r.get("status") == "bracketed" and r["q_hi"]["negative"] and r["q_lo"]["positive"] and 0 < r["eta_lo"] < r["eta_hi"]
            and r["eta_hi"]/r["eta_lo"] <= 1 + TOL + 1e-12)
bad1 = dict(good); bad1["q_hi"] = dict(good["q_hi"]); bad1["q_hi"]["negative"] = False
bad2 = dict(good); bad2["eta_hi"] = good["eta_lo"]*1.01
bad3 = dict(good); bad3["status"] = "ambiguous"
ok = bracket_ok(good) and not bracket_ok(bad1) and not bracket_ok(bad2) and not bracket_ok(bad3)
gate("g8 mangle probes: the bracket predicate fails on a non-negative upper ball, a bracket wider than 1 + 1e-3, a non-bracketed status", ok)

# ---------------------------------------------------------------- g9
from cascade_tower import chain_ok
gate("g9 the chain obligation to cascade_true_form_bounds.py (Theorem 1bn) met", chain_ok("cascade_true_form_bounds.py"))

# ---------------------------------------------------------------- g10
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g10 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g10 the 1bo paper needles and the footer census (declared surface)", ok)

print(("\nALL GATES PASS (11/11)" if not fails else f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
