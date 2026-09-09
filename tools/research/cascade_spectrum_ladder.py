#!/usr/bin/env python3
"""Theorem 1br -- the spectrum ladder: certified upper bounds on the low
eigenvalues lambda_1 .. lambda_m of the true Weil form on [-a, a] at the seven
cells, rung by rung against the prolate leakage ladder 1 - chi_j(c) at the
horizon c = T_0 = 2 pi e^delta: rung k of the true form sits nearest the
prolate of ORDER 4k (chi_{2k} in the paper's convention chi_j = sqrt(lambda_{2j}))
at every rung in the leakage regime, above it by 0.1 .. 2.5 nats, the first
rung's offset the largest at every cell; the orders 2 mod 4 and the order-0
prolate are absent; the alternative convention c = a T_0 is rejected; and the
pole term is load-bearing -- without it the form has a certified negative
direction, and its ladder from rung 2 on is the true ladder within half a nat
(Weyl interlacing under a rank-one positive update). Substrate
weil_spectrum_ladder.py (keyed on its closure: weil_prime_gram.py). Tower
member 27 (top).

THE CLAIMS GATED. (0) THE CELLS load at their keys -- Theorem 1bn's seven
(delta, K2, prec) with m = 10, 12, 18, 22, 28, 42, 68 rungs -- and rung 1 is
Theorem 1bo's lambda_1 (ln within 1e-6). (1) THE CERTIFIED LADDER: every rung
the upper end of a certified enclosure of the projected pencil's top eigenvalue
(Courant-Fischer: an upper bound on lambda_k whatever the vectors), enclosure
radius below 1e-100 relative, the approximate eigenvalue within 1e-9 in ln, the
ladder monotone in k (the spans grow). (2) LIVE at delta = 1.0: the ten rungs
re-derived from the Gram (equal to 1e-10 in ln), and at K = 96 the leakage
rungs within BAND_K of the K = 120 ones (two upper bounds; their agreement
is the basis convergence). (3) THE PROLATE LADDER: the two Legendre cutoffs
agree to 1e-9 on every leakage entry; the order-4 entry equals Theorem 1bn's
ln(1 - chi_2) at every cell; live at delta = 1.0 the ladder is reproduced to
1e-12. (4) THE SHADOW (computed, gated): at every cell and every leakage rung
(prolate ln(1 - chi_{2k}) < -1) the nearest even order to ln lambda_k is 4k;
in the deep regime (below -2) the offset ln lambda_k - ln(1 - chi_{2k}) is in
(0, 2.6], the first rung's offset the largest of the cell, in [1.6, 2.6] and
increasing with delta; over the deep rungs 2.. the offsets fall in trend (the
least-squares slope negative at every cell) but not rung by rung -- at delta >=
3.0 they alternate with the parity of k (orders 4 and 0 mod 8), rises at 6/18
and 13/31 steps, the largest consecutive rise in [0.3, 0.5] (round 313 F5);
87 leakage rungs pinned, the order-0 leakage -31.5 at delta = 1.0 gated; the top rung of a cell (prolate ln in [-2, -1), where
the ladder has flattened to a spacing of about a nat) within 0.1; the leakage
rungs number at least 80. (5) ALTERNATIVES REJECTED: the nearest order 2 mod 4
is farther than order 4k by at least 0.7 nats at every leakage rung and by at
least 2 where the prolate ln is below -20; at c = a T_0
(delta = 1.0, 1.3828125, 2.3, live) the nearest-order map is k -> 4(k-1) with
offsets of both signs at the first two cells and neither map at 2.3 (the
conventions coincide at delta = 2.0). (6) THE POLE (live at delta = 1.0,
1.3828125, 2.0): G - G_0 = 2 p p^T entrywise in balls (the pole is rank one);
the approximate lowest vector of Q_0 = Q - pole has a certified NEGATIVE
Rayleigh ball; the approximate eigenvalues mu_k of Q_0 interlace the certified
rungs (mu_k <= lambda_k <= mu_{k+1}); from rung 2 on ln lambda_k - ln mu_k in
[0, 0.5] on the leakage rungs and mu_k's nearest order is 4k. (7) mangle
probes; (8) the paper's numbers parsed back from the declared needles; (9) the
chain obligation to cascade_lfunction_test.py; (10) the needles and census.

WHAT IS NOT CLAIMED. No lower bound on any eigenvalue (every rung is an upper
bound; the approximate values agree with them to 1e-9, which is convergence,
not certification); no mechanism for the selection of the Fourier-(+1) orders
or for the offsets; nothing about zeros; no Riemann Hypothesis consequence.
"""
import math, os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from weil_spectrum_ladder import run as run_SL, CELLS as LCELLS, prolate_even_leakage, KMAX_EXTRA
from weil_knife_edge import run as run_KE, CELLS as KCELLS
from true_form_cells import run as run_TF
from weil_prime_gram import gram, rayleigh
from lfun_gram import gram_L, ZETA
from flint import arb, acb, arb_mat, acb_mat, ctx

PAPER_NEEDLES = [
    {'g': 'g10', 's': 'Theorem 1br (the spectrum ladder', 'form': 'plain'},
    {'g': 'g10', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 9},
    {'s': '`cascade_spectrum_ladder.py`', 'min': 2, 'g': 'g10'},
    {'s': 'the **94 scripts cited in place** above', 'form': 'ws', 'g': 'g10'},
    {'s': 'extended by Theorems 1i–1br:', 'form': 'ws', 'g': 'g10'},
    {'g': 'g8', 's': '| 1.0 | 2 | −4.01 | −4.98 | −0.18 | −0.28 | 1.64 | [0.96, 0.97] |', 'form': 'ws'},
    {'g': 'g8', 's': '| 1.3828125 | 3 | −15.54 | −16.73 | −5.87 | −6.81 | 1.79 | [0.93, 1.19] |', 'form': 'ws'},
    {'g': 'g8', 's': '| 2.0 | 7 | −52.11 | −53.58 | −38.75 | −40.10 | 2.12 | [0.47, 1.47] |', 'form': 'ws'},
    {'g': 'g8', 's': '| 2.3 | 9 | −81.77 | −83.34 | −67.05 | −68.42 | 2.18 | [0.59, 1.57] |', 'form': 'ws'},
    {'g': 'g8', 's': '| 2.6 | 13 | −122.98 | −124.51 | −106.67 | −108.23 | 2.20 | [0.42, 1.56] |', 'form': 'ws'},
    {'g': 'g8', 's': '| 3.0 | 19 | −202.48 | −204.21 | −184.56 | −186.19 | 2.39 | [0.53, 1.72] |', 'form': 'ws'},
    {'g': 'g8', 's': '| 3.5 | 32 | −361.73 | −363.61 | −341.85 | −343.48 | 2.47 | [0.37, 1.87] |', 'form': 'ws'},
    {'g': 'g8', 's': '1.64, 1.79, 2.12, 2.18, 2.20, 2.39, 2.47 at the cells', 'form': 'ws'},
    {'g': 'g8', 's': '[0.96, 0.97], [0.93, 1.19], [0.47, 1.47], [0.59, 1.57], [0.42, 1.56], [0.53, 1.72], [0.37, 1.87]', 'form': 'ws'},
    {'g': 'g8', 's': 'δ = 1.0: k1→0 k2→4, offsets +0.92, −1.46; δ = 1.3828125: k1→0 k2→4 k3→8, offsets +4.21, +0.38, −0.60', 'form': 'ws'},
    {'g': 'g8', 's': '−1.98, −2.82, −4.30', 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ORDER = ["d1.0", "d1.38", "d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
M_PINNED = {"d1.0": 10, "d1.38": 12, "d2.0": 18, "d2.3": 22, "d2.6": 28, "d3.0": 42, "d3.5": 68}
LEAK = -1.0          # the leakage regime: prolate ln(1 - chi) below -1 (the nearest-order map)
DEEP = -2.0          # the deep regime: below -2 (the offset band; at the top rung of a cell the ladder flattens to a spacing of about a nat)
MARGIN_ALL, MARGIN_DEEP = 0.7, 2.0   # the 2-mod-4 margin at every leakage rung, and at rungs with prolate ln below -20
OFF_MAX = 2.6        # the offset band (0, OFF_MAX]
OFF1_BAND = (1.6, 2.6)
POLE_BAND = 0.5      # ln lambda_k - ln mu_k on the leakage rungs from rung 2
BAND_K = 0.05        # ln agreement of the K = 96 and K = 120 leakage rungs at delta = 1.0
SL = {c: run_SL(c) for c in ORDER}
KE = {c: run_KE(c) for c in ORDER}
TF = {c: run_TF(c) for c in ORDER}

def leakage_rungs(st):
    """the rungs k with prolate ln(1 - chi_{2k}) < LEAK (order 4k = index 2k of the even list)."""
    P = st["prolate_ln_leakage"][str(KMAX_EXTRA)]
    return [r["k"] for r in st["ladder"] if 2*r["k"] < len(P) and P[2*r["k"]] is not None and P[2*r["k"]] < LEAK]

def nearest_order(x, P, orders):
    i = min(range(len(P)), key=lambda i: abs((P[i] if P[i] is not None else 1e9) - x))
    return orders[i], x - P[i]

# ---------------------------------------------------------------- g0
ok = all(SL[c]["cell"] == c and abs(SL[c]["delta"] - KCELLS[c]["delta"]) < 1e-12 and SL[c]["K"] == KCELLS[c]["K"]
         and SL[c]["prec"] == KCELLS[c]["prec"] and SL[c]["m"] == M_PINNED[c] and len(SL[c]["ladder"]) == M_PINNED[c] for c in ORDER)
ok &= all(abs(SL[c]["ladder"][0]["ln_upper"] - KE[c]["lambda1"]["ln_upper"]) <= 1e-6 for c in ORDER)
gate("g0 the seven ladder cells load at their keys with Theorem 1bn's (delta, K2, prec), m = " + ", ".join(str(M_PINNED[c]) for c in ORDER)
     + " rungs; rung 1 is Theorem 1bo's lambda_1 (ln within 1e-6: max |diff| " + f"{max(abs(SL[c]['ladder'][0]['ln_upper'] - KE[c]['lambda1']['ln_upper']) for c in ORDER):.1e})", ok)

# ---------------------------------------------------------------- g1
ok = True; worst_rad = 0.0; worst_ap = 0.0
for c in ORDER:
    L = SL[c]["ladder"]
    for i, r in enumerate(L):
        ok &= r["ln_upper"] is not None and r["ln_approx"] is not None and math.isfinite(r["ln_upper"])
        rel = r["enclosure_rad"]/float(r["upper"]); worst_rad = max(worst_rad, rel); ok &= rel <= 1e-100
        worst_ap = max(worst_ap, abs(r["ln_upper"] - r["ln_approx"])); ok &= abs(r["ln_upper"] - r["ln_approx"]) <= 1e-9
        if i: ok &= r["ln_upper"] >= L[i - 1]["ln_upper"] - 1e-12
gate(f"g1 the certified ladder: every rung a positive certified enclosure (max relative radius {worst_rad:.1e}), the approximate eigenvalue within 1e-9 in ln (max {worst_ap:.1e}), monotone in k at every cell (a consequence of the nested spans -- a consistency check that can fail only numerically)", ok)

# ---------------------------------------------------------------- g2
def ladder_live(d, K, prec, m):
    G, N, pp = gram(d, K, prec)
    with ctx.workprec(prec):
        Dm = arb_mat(K, K)
        for i in range(K): Dm[i, i] = 1/N[i].sqrt()
        Gs = Dm*G*Dm
        E, Rv = acb_mat(Gs.mid()).eig(right=True, algorithm="approx")
        order = sorted(range(K), key=lambda i: float(E[i].real.mid()))
        vecs = []
        for j in range(m):
            w = arb_mat(K, 1)
            for i in range(K): w[i, 0] = Rv[i, order[j]].real.mid()/N[i].sqrt()
            vecs.append(w)
        out = []
        for k in range(1, m + 1):
            Rk = arb_mat(K, k)
            for j in range(k):
                for i in range(K): Rk[i, j] = vecs[j][i, 0]
            A = Rk.transpose()*G*Rk
            Mm = arb_mat(k, k)
            for j in range(k):
                for l in range(k):
                    s = arb(0)
                    for i in range(K): s += N[i]*Rk[i, j]*Rk[i, l]
                    Mm[j, l] = s
            ev = acb_mat(Mm.inv()*A).eig(nonstop=True)
            top = max((e.real.upper() for e in ev), key=lambda x: float(x))
            out.append(float(top.log()))
        return out
live120 = ladder_live(1.0, 120, 600, 10)
ok = all(abs(live120[i] - SL["d1.0"]["ladder"][i]["ln_upper"]) <= 1e-10 for i in range(10))
lk = leakage_rungs(SL["d1.0"])
live96 = ladder_live(1.0, 96, 600, max(lk) + 1)
devK = max(abs(live96[k - 1] - SL["d1.0"]["ladder"][k - 1]["ln_upper"]) for k in lk)
ok &= devK <= BAND_K
gate(f"g2 live at delta = 1.0: the ten rungs re-derived from the Gram (max |diff| {max(abs(live120[i] - SL['d1.0']['ladder'][i]['ln_upper']) for i in range(10)):.1e}); at K = 96 the leakage rungs within {BAND_K} of the K = 120 ones in ln (max {devK:.1e})", ok)

# ---------------------------------------------------------------- g3
ok = True; worst = 0.0
for c in ORDER:
    st = SL[c]; P3 = st["prolate_ln_leakage"][str(KMAX_EXTRA)]; P5 = st["prolate_ln_leakage"][str(KMAX_EXTRA + 200)]
    ok &= st["prolate_orders"] == list(range(0, 4*st["m"] + 1, 2)) and len(P3) == len(P5) == 2*st["m"] + 1
    for i in range(len(P3)):
        if P3[i] is not None and P3[i] < LEAK:
            ok &= P5[i] is not None and abs(P3[i] - P5[i]) <= 1e-9; worst = max(worst, abs(P3[i] - P5[i]))
    ok &= abs(P3[2] - TF[c]["ln_one_minus_chi2"][0]) <= 1e-9        # order 4 = the paper's 1 - chi_2
with ctx.workprec(400):
    c0 = 2*arb.pi()*arb(1).exp()
    live = prolate_even_leakage(c0, int(float(c0)) + KMAX_EXTRA, 21, 400)
ok &= all(abs(live[i] - SL["d1.0"]["prolate_ln_leakage"][str(KMAX_EXTRA)][i]) <= 1e-12 for i in range(21) if live[i] is not None and live[i] < LEAK)
gate(f"g3 the prolate ladder: the two cutoffs agree on every leakage entry (max |diff| {worst:.1e}), the order-4 entry is Theorem 1bn's ln(1 - chi_2) at every cell, the delta = 1.0 ladder reproduced live to 1e-12", ok)

# ---------------------------------------------------------------- g4
ok = True; shadow = {}; n_leak = 0; n_deep = 0; top = {}
for c in ORDER:
    st = SL[c]; P = st["prolate_ln_leakage"][str(KMAX_EXTRA)]; orders = st["prolate_orders"]
    lk = leakage_rungs(st); n_leak += len(lk); offs = []
    for k in lk:
        x = st["ladder"][k - 1]["ln_upper"]
        o, off = nearest_order(x, P, orders)
        ok &= o == 4*k
        if P[2*k] < DEEP:
            ok &= 0 < off <= OFF_MAX; offs.append(off); n_deep += 1
        else:
            top[c] = off; ok &= abs(off) <= 0.1
    ok &= offs[0] == max(offs) and OFF1_BAND[0] <= offs[0] <= OFF1_BAND[1]
    shadow[c] = offs
ok &= n_leak == 87 and all(shadow[ORDER[i]][0] < shadow[ORDER[i + 1]][0] for i in range(6))
ok &= abs(SL["d1.0"]["prolate_ln_leakage"][str(KMAX_EXTRA)][0] + 31.5) <= 0.005      # the order-0 leakage at delta = 1.0, '-31.5'
# F5 (round 313): the trend and the alternation over the deep rungs 2..
slopes = {}; rises = {}; maxrise = {}
for c in ORDER:
    o = shadow[c][1:]; n = len(o)
    if n >= 2:
        xm = (n - 1)/2; ym = sum(o)/n
        slopes[c] = sum((i - xm)*(y - ym) for i, y in enumerate(o))/sum((i - xm)**2 for i in range(n))
        ok &= slopes[c] < 0
    rises[c] = sum(1 for i in range(1, n) if o[i] > o[i - 1]); maxrise[c] = max([o[i] - o[i - 1] for i in range(1, n)] + [0.0])
ok &= rises["d3.0"] == 6 and rises["d3.5"] == 13 and 0.3 <= max(maxrise["d3.0"], maxrise["d3.5"]) <= 0.5
gate("g4 the shadow: at every cell and leakage rung the nearest even prolate order to ln lambda_k is 4k; in the deep regime the offset is in (0, " + f"{OFF_MAX}], the first rung's the largest, in {OFF1_BAND} and increasing with delta; leakage rungs {n_leak} ({n_deep} deep); first offsets "
     + ", ".join(f"{shadow[c][0]:.2f}" for c in ORDER) + "; ranges over the deep rungs 2..: " + ", ".join(f"[{min(shadow[c][1:]):.2f}, {max(shadow[c][1:]):.2f}]" for c in ORDER)
     + "; the top rung of a cell (prolate ln in [-2, -1)) within 0.1: " + ", ".join(f"{c}: {top[c]:+.2f}" for c in top)
     + "; 87 leakage rungs pinned, the order-0 leakage -31.5 at delta = 1.0; the trend: least-squares slopes over the deep rungs 2.. " + ", ".join(f"{slopes[c]:+.3f}" for c in ORDER if c in slopes)
     + " (all negative), rung-to-rung rises " + ", ".join(f"{rises[c]}/{max(len(shadow[c]) - 2, 0)}" for c in ORDER) + f", the largest consecutive rise {max(maxrise['d3.0'], maxrise['d3.5']):.2f} at delta >= 3.0 (in [0.3, 0.5])", ok)

# ---------------------------------------------------------------- g5
ok = True; margin = 1e9; margin_deep = 1e9
for c in ORDER:
    st = SL[c]; P = st["prolate_ln_leakage"][str(KMAX_EXTRA)]; orders = st["prolate_orders"]
    for k in leakage_rungs(st):
        x = st["ladder"][k - 1]["ln_upper"]
        d4 = abs(x - P[2*k])
        d2 = min(abs(x - P[i]) for i in range(len(P)) if P[i] is not None and orders[i] % 4 == 2)
        margin = min(margin, d2 - d4); ok &= d2 - d4 >= MARGIN_ALL
        if P[2*k] < -20: margin_deep = min(margin_deep, d2 - d4); ok &= d2 - d4 >= MARGIN_DEEP
alt = {}
for c in ("d1.0", "d1.38", "d2.3"):
    st = SL[c]; d = st["delta"]
    with ctx.workprec(400):
        ca = arb(d)/2*2*arb.pi()*arb(d).exp()
        Pa = prolate_even_leakage(ca, int(float(ca)) + KMAX_EXTRA, 2*st["m"] + 1, 400)
    orders = st["prolate_orders"]; maps = []; offs = []
    for k in leakage_rungs(st):
        o, off = nearest_order(st["ladder"][k - 1]["ln_upper"], Pa, orders); maps.append((k, o)); offs.append(off)
    alt[c] = (maps, offs)
    ok &= any(o != 4*k for k, o in maps)
    if c != "d2.3": ok &= min(offs) < 0 < max(offs) and all(o == 4*(k - 1) for k, o in maps)      # the map k -> 4(k-1) at 1.0 and 1.38
    else: ok &= maps[:3] == [(1, 8), (2, 12), (3, 18)]
gate(f"g5 alternatives rejected: the nearest order 2 mod 4 is farther than order 4k by at least {MARGIN_ALL} nats at every leakage rung (min margin {margin:.2f}) and by at least {MARGIN_DEEP} where the prolate ln is below -20 (min {margin_deep:.2f}); at c = a T_0 the map is k -> 4(k-1) with offsets of both signs at delta = 1.0 and 1.38, and neither at delta = 2.3 (the two conventions coincide at delta = 2.0): "
     + "; ".join(f"{c}: " + " ".join(f"k{k}->{o}" for k, o in alt[c][0][:4]) + " offsets " + ", ".join(f"{x:+.2f}" for x in alt[c][1][:4]) for c in ("d1.0", "d1.38", "d2.3")), ok)

# ---------------------------------------------------------------- g6
ok = True; pole = {}
for c in ("d1.0", "d1.38", "d2.0"):
    st = SL[c]; d, K, prec = st["delta"], st["K"], st["prec"]
    G, N, pp = gram(d, K, prec)
    G0, N0, pp0 = gram_L(d, K, prec, dict(ZETA, pole=False))
    with ctx.workprec(prec):
        a = arb(d)/2; pi = arb.pi()
        p = [(2*(acb(arb(1)/2, arb(k)*pi/a)*a).sinh()/acb(arb(1)/2, arb(k)*pi/a)).real for k in range(K)]
        dev = max(float(abs(G[j, k] - G0[j, k] - 2*p[j]*p[k]).upper()) for j in range(K) for k in range(K))
        ok &= dev <= 1e-150 and pp0 == pp and all(N0[i] == N[i] for i in range(K))
        Dm = arb_mat(K, K)
        for i in range(K): Dm[i, i] = 1/N0[i].sqrt()
        E, Rv = acb_mat((Dm*G0*Dm).mid()).eig(right=True, algorithm="approx")
        order = sorted(range(K), key=lambda i: float(E[i].real.mid()))
        mu = [float(E[order[j]].real.mid()) for j in range(st["m"] + 1)]
        v0 = [Rv[i, order[0]].real.mid()/N0[i].sqrt() for i in range(K)]
        r0 = rayleigh(G0, N0, v0, prec)
        ok &= r0.upper() < 0                                   # a certified negative direction of Q_0
    lam = [float(r["upper"]) for r in st["ladder"]]
    ok &= all(mu[k - 1] <= lam[k - 1]*(1 + 1e-9) and lam[k - 1] <= mu[k]*(1 + 1e-9) for k in range(1, st["m"] + 1))   # interlacing
    P = st["prolate_ln_leakage"][str(KMAX_EXTRA)]; orders = st["prolate_orders"]
    gaps = []
    for k in leakage_rungs(st):
        if k == 1: continue
        g = st["ladder"][k - 1]["ln_upper"] - math.log(mu[k - 1]); gaps.append(g)
        ok &= 0 <= g <= POLE_BAND and nearest_order(math.log(mu[k - 1]), P, orders)[0] == 4*k
    pole[c] = (float(r0.upper()), mu[0], dev, gaps)
gate("g6 the pole is load-bearing (live at delta = 1.0, 1.3828125, 2.0): G - G_0 = 2 p p^T in balls (max dev " + f"{max(v[2] for v in pole.values()):.1e}" + "); the lowest approximate vector of Q_0 has a certified negative Rayleigh ball (upper ends "
     + ", ".join(f"{pole[c][0]:.3f}" for c in pole) + "); mu_k <= lambda_k <= mu_(k+1) for every rung (Weyl's theorem for the two pencils -- a consistency check that can fail only numerically); from rung 2 the leakage rungs of Q_0 sit within " + f"{POLE_BAND}" + " nats below the true ones at order 4k (gaps "
     + "; ".join(", ".join(f"{g:.2f}" for g in pole[c][3]) for c in pole) + ")", ok)

# ---------------------------------------------------------------- g7
def shadow_ok(ladder_ln, P, orders):
    for k, x in enumerate(ladder_ln, 1):
        o, off = nearest_order(x, P, orders)
        if o != 4*k or not (0 < off <= OFF_MAX): return False
    return True
st = SL["d2.0"]; P = st["prolate_ln_leakage"][str(KMAX_EXTRA)]; orders = st["prolate_orders"]
good = [st["ladder"][k - 1]["ln_upper"] for k in leakage_rungs(st)]
ok = shadow_ok(good, P, orders) and not shadow_ok([x - 5 for x in good], P, orders) and not shadow_ok([x - 3 for x in good], P, orders) and not shadow_ok([x + 1 for x in good], P, orders)
def mono_ok(L): return all(L[i] >= L[i - 1] - 1e-12 for i in range(1, len(L)))
ok &= mono_ok(good) and not mono_ok(good[::-1])
gate("g7 mangle probes: the shadow predicate fails on the ladder shifted by -5 (other orders), by -3 (negative offsets), by +1 (offsets above the band); the monotone predicate fails on the reversed ladder", ok)

# ---------------------------------------------------------------- g8
import paper_needles
ROWS = ['| 1.0 | 2 | −4.01 | −4.98 | −0.18 | −0.28 | 1.64 | [0.96, 0.97] |', '| 1.3828125 | 3 | −15.54 | −16.73 | −5.87 | −6.81 | 1.79 | [0.93, 1.19] |', '| 2.0 | 7 | −52.11 | −53.58 | −38.75 | −40.10 | 2.12 | [0.47, 1.47] |', '| 2.3 | 9 | −81.77 | −83.34 | −67.05 | −68.42 | 2.18 | [0.59, 1.57] |', '| 2.6 | 13 | −122.98 | −124.51 | −106.67 | −108.23 | 2.20 | [0.42, 1.56] |', '| 3.0 | 19 | −202.48 | −204.21 | −184.56 | −186.19 | 2.39 | [0.53, 1.72] |', '| 3.5 | 32 | −361.73 | −363.61 | −341.85 | −343.48 | 2.47 | [0.37, 1.87] |']
S_OFF1 = '1.64, 1.79, 2.12, 2.18, 2.20, 2.39, 2.47 at the cells'
S_RANGES = '[0.96, 0.97], [0.93, 1.19], [0.47, 1.47], [0.59, 1.57], [0.42, 1.56], [0.53, 1.72], [0.37, 1.87]'
S_ALT = 'δ = 1.0: k1→0 k2→4, offsets +0.92, −1.46; δ = 1.3828125: k1→0 k2→4 k3→8, offsets +4.21, +0.38, −0.60'
S_POLE = '−1.98, −2.82, −4.30'
# each call carries its literal (the precheck's clause D); the strings equal ROWS / S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, '| 1.0 | 2 | −4.01 | −4.98 | −0.18 | −0.28 | 1.64 | [0.96, 0.97] |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 1.3828125 | 3 | −15.54 | −16.73 | −5.87 | −6.81 | 1.79 | [0.93, 1.19] |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 2.0 | 7 | −52.11 | −53.58 | −38.75 | −40.10 | 2.12 | [0.47, 1.47] |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 2.3 | 9 | −81.77 | −83.34 | −67.05 | −68.42 | 2.18 | [0.59, 1.57] |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 2.6 | 13 | −122.98 | −124.51 | −106.67 | −108.23 | 2.20 | [0.42, 1.56] |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 3.0 | 19 | −202.48 | −204.21 | −184.56 | −186.19 | 2.39 | [0.53, 1.72] |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 3.5 | 32 | −361.73 | −363.61 | −341.85 | −343.48 | 2.47 | [0.37, 1.87] |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '1.64, 1.79, 2.12, 2.18, 2.20, 2.39, 2.47 at the cells', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '[0.96, 0.97], [0.93, 1.19], [0.47, 1.47], [0.59, 1.57], [0.42, 1.56], [0.53, 1.72], [0.37, 1.87]', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'δ = 1.0: k1→0 k2→4, offsets +0.92, −1.46; δ = 1.3828125: k1→0 k2→4 k3→8, offsets +4.21, +0.38, −0.60', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '−1.98, −2.82, −4.30', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g8'] == ROWS + [S_OFF1, S_RANGES, S_ALT, S_POLE]
_SUP = str.maketrans('⁻⁰¹²³⁴⁵⁶⁷⁸⁹', '-0123456789')
def _num(s):
    s = s.strip().replace('−', '-').replace('×10', 'e').translate(_SUP)
    return float(s)
# the rows: delta | leakage rungs | ln lambda_2 <= | ln(1 - chi_4) | ln lambda_3 <= | ln(1 - chi_6) | rung-1 offset | offsets of rungs 2 on (range)
for _row, c in zip(ROWS, ORDER):
    st = SL[c]; P = st["prolate_ln_leakage"][str(KMAX_EXTRA)]; fl = [x.strip() for x in _row.strip('|').split('|')]
    ok &= abs(_num(fl[0]) - st["delta"]) < 1e-12 and int(fl[1]) == sum(1 for k in leakage_rungs(st) if P[2*k] < DEEP)
    for col, k in ((fl[2], 2), (fl[4], 3)):
        v = st["ladder"][k - 1]["ln_upper"]; ok &= _num(col) >= v and _num(col) - v < 1e-2 + 1e-9        # ceilings to 1e-2
    for col, k in ((fl[3], 2), (fl[5], 3)):
        ok &= abs(_num(col) - P[2*k]) <= 5e-3 + 1e-9                                                    # nearest 1e-2
    ok &= abs(_num(fl[6]) - shadow[c][0]) <= 5e-3 + 1e-9
    _m = __import__("re").match(r"\[?([0-9.]+), ([0-9.]+)\]?", fl[7])
    ok &= _num(_m.group(1)) <= min(shadow[c][1:]) < _num(_m.group(1)) + 0.01 + 1e-9 and _num(_m.group(2)) - 0.01 - 1e-9 < max(shadow[c][1:]) <= _num(_m.group(2))
_m = __import__("re").findall(r"([0-9]\.[0-9]{2})", S_OFF1)
ok &= len(_m) == 7 and all(abs(float(a) - shadow[c][0]) <= 5e-3 + 1e-9 for a, c in zip(_m, ORDER))
ok &= S_OFF1.endswith("at the cells") and all(shadow[c][0] == max(shadow[c]) for c in ORDER)
_m = __import__("re").findall(r"\[([0-9.]+), ([0-9.]+)\]", S_RANGES)
ok &= len(_m) == 7 and all(float(a) <= min(shadow[c][1:]) and max(shadow[c][1:]) <= float(b) for (a, b), c in zip(_m, ORDER))
for c in ("d1.0", "d1.38"):
    maps, offs = alt[c]
    ok &= (" ".join(f"k{k}→{o}" for k, o in maps)) in S_ALT
_m = __import__("re").findall(r"(−[0-9]\.[0-9]{2})", S_POLE)
ok &= len(_m) == 3 and all(_num(a) >= pole[c][0] and _num(a) - pole[c][0] < 0.01 + 1e-9 for a, c in zip(_m, ("d1.0", "d1.38", "d2.0")))   # ceilings (outward: nearer zero)
ok &= margin >= MARGIN_ALL and margin_deep >= MARGIN_DEEP and n_leak >= 80
gate("g8 the paper's numbers parsed back from the declared needles: the seven rows (deep-rung counts, the rung-2 and rung-3 ceilings to 1e-2 with their prolate entries to 5e-3, the rung-1 offsets to 5e-3, the offset ranges outward), the first-offset list, the ranges, the alternative's maps, the pole-free upper ends (ceilings)", ok)


# ---------------------------------------------------------------- g9
from cascade_tower import chain_ok
gate("g9 the chain obligation to cascade_lfunction_test.py (Theorem 1bq) met", chain_ok("cascade_lfunction_test.py"))

# ---------------------------------------------------------------- g10
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g10 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g10 the 1br paper needles and the footer census (declared surface)", ok)

print(("\nALL GATES PASS (11/11)" if not fails else f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
