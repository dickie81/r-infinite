#!/usr/bin/env python3
"""Theorem 1bq -- the cross-L-function test: the true Weil form of four other
L-functions (L(s, chi_-3), L(s, chi_-4), L(s, chi_8) -- real primitive
characters of conductors 3, 4, 8 -- and L(Delta, s), Ramanujan's cusp form,
degree 2) at the seven slack-law cells: certified upper bounds on lambda_1;
the finite-delta formula of Theorem 1bm(v) on each form's OWN zeros with its
offset c_L(delta) against zeta's; the knife-edge in both directions at every
unramified prime with THE SIGN RULE -- the near crossing is downward exactly
when the first shell's coefficient c(p) is positive -- and Theorem 1bp's
linear-response law transferred live: eta_lin = lambda_1/|D_p| with the shell
coefficients c(p^k) in the slope, its sign the direction. Substrates
lfun_gram.py, lfun_cells.py (keyed producer, closure: lfun_gram.py,
weil_prime_gram.py, weil_knife_edge.py) and lfun_zeros.py (the zero lists as
data, count-checked). Tower member 26 (top).

THE CLAIMS GATED. (0) THE CELLS: 28 (form, cell) states load at their keys
with K2 = max(120, 4 (2 a T_0)/pi + 100), K1 = 0.7 K2, 600 bits, T_0 = 2 pi
(e^delta/q)^{1/d}, and the unramified primes p <= e^delta. (1) THE BOUNDS:
every K2 and K1 Rayleigh ball positive, ln K2 <= ln K1 (more modes), the pair
within BAND_K in ln; the generalised Gram reproduces Theorem 1bn's zeta Gram
entrywise at delta = 1.0, K = 48 (below 1e-100); one cell re-derived live
(chi_-4, delta = 2.0) to 1e-10 in ln. (2) THE NORMALISATION: for each form the
prime-side Rayleigh quotient of the C_c^inf bump equals the explicit
formula's zero side on the form's own zeros plus the smooth-density tail,
relative deviation below BAND_Z at delta = 1.0 (K = 24) and at delta = 2.0 (K =
40, the shells 2,4,5,7 / 3,5,7 / 3,5,7 / 2,3,4,5,7 inside -- round 313 F2: the
delta = 1.0 cell alone exercises no local coefficient beyond the shell n = 2)
(floating point; the zero lists' counts
against the smooth count of the argument principle -- recomputed here from
the Gamma factors, (T/2pi) ln(qT/2pi e) + kappa/4 - 1/8 and (T/pi) ln(T/2pi e)
+ 11/4 -- within 1, the half-step scan agreeing, the phase check below 1e-8). (3) THE
FINITE-DELTA FORMULA: at every (form, cell) -- the zero lists reach 2.5 T_0 at
all 28 -- c_L(delta) := ln lambda_1 - min_T s_delta(T) on the form's zeros
(1bm's minimiser: a 20001-point grid on [0.5, 2.5] T_0 refined inside the
zero-free intervals, the minimiser interior); zeta's own values from 1bm's
own lambda_1 reproduce 1bm(v)'s 4.70 .. 7.90 within 0.01; |c_L - c_zeta| <=
BAND_C at every pair against zeta's cosine-basis offsets; every gap c_zeta -
c_L in [0.04, 1.05], the mean growing with the conductor among the three
characters, Delta's gap increasing in delta (round 313 F4); the continuum minimum is -2 d T_0 (closed form vs numeric,
1e-6). (4) THE SIGN RULE: at every (form, cell, prime) triple exactly one
direction carries the near crossing (a certified negative ball at eta_hi,
the bracket of relative width 1e-3), and it is downward iff c(p) > 0; the
other direction has no crossing below the cap log(p)/2 -- every sample of the
doubling and of the producer's 64-point log grid up to the cap a positive
ball (round 313 F1: the first producer stopped at the last doubling sample
and missed four crossings in the unsampled interval below the cap) -- or a
far crossing at least FAR_RATIO further: the census is chi_-3, p = 2 at delta
= 2.3, 2.6, 3.0, 3.5, at 0.87-0.97 of the cap, pinned. (5) THE LAW TRANSFERRED (live):
D_p^L = -(dP_p^L/d eta)/||g||^2 with c(p^k) in the shells; its sign predicts
the witnessed direction at every triple; eta_lin = lambda_1/|D_p| lies in the
near bracket at every triple with eta_hi T_0^2 <= SMALL_X (the small-shift
regime: 105 of the 124 triples) and deviates from eta_hi by decade of
eta_hi T_0^2 within 3e-3, 0.15, 0.6 -- second order in the shift. (6) mangle probes; (7) the paper's
numbers parsed back from the declared needles; (8) the chain obligation to
cascade_linear_response.py; (9) the needles and census.

WHAT IS NOT CLAIMED. No lower bound on any lambda_1 or window; the offsets
and the zero-side agreements are floating point on double-precision zero
lists (computed, gated in bands); nothing about the zeros beyond the lists;
no statement about the Generalised Riemann Hypothesis; no Riemann Hypothesis
consequence.
"""
import math, os, sys, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from lfun_cells import run as run_LF, FORMS, CELLS as LCELLS, K_for, PREC, ETA_CAP_FRAC, prime_shells_c
from lfun_gram import gram_L, horizon, ZETA, dirichlet_coef, delta_coef
from weil_prime_gram import gram, rayleigh, minimiser
from weil_knife_edge import TOL
from weil_linear_response import AutocorrDeriv
from flint import arb, arb_mat, ctx
import mpmath as mp

PAPER_NEEDLES = [
    {'g': 'g9', 's': 'Theorem 1bq (the cross-L-function test', 'form': 'plain'},
    {'g': 'g9', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 8},
    {'s': '`cascade_lfunction_test.py`', 'min': 2, 'g': 'g9'},
    {'s': 'the **99 scripts cited in place** above', 'form': 'ws', 'g': 'g9'},
    {'s': 'extended by Theorems 1i–1bw:', 'form': 'ws', 'g': 'g9'},
    {'g': 'g7', 's': '| χ₋₃ | (3, 1) | −3.855 | −21.079 | −126.292 | 5.60 | 7.28 | 30 | 4 |', 'form': 'ws'},
    {'g': 'g7', 's': '| χ₋₄ | (4, 1) | −1.965 | −14.311 | −92.476 | 5.58 | 7.23 | 29 | 0 |', 'form': 'ws'},
    {'g': 'g7', 's': '| χ₈ | (8, 1) | −1.025 | −6.991 | −46.223 | 5.37 | 6.81 | 29 | 0 |', 'form': 'ws'},
    {'g': 'g7', 's': '| Δ | (1, 2) | −5.381 | −24.765 | −91.050 | 5.66 | 6.79 | 36 | 0 |', 'form': 'ws'},
    {'g': 'g7', 's': 'the relative deviations 6×10⁻¹¹, 5×10⁻⁹, 2×10⁻⁶, 2×10⁻⁶ at δ = 1.0 and 2×10⁻¹², 3×10⁻¹³, 9×10⁻⁸, 4×10⁻⁸ at δ = 2.0, for χ₋₃, χ₋₄, χ₈, Δ', 'form': 'ws'},
    {'g': 'g7', 's': 'χ₋₃: 4.18, 4.86, 5.60, 5.89, 6.37, 6.72, 7.28; χ₋₄: 4.06, 4.81, 5.58, 5.96, 6.15, 6.55, 7.23; χ₈: 3.87, 4.40, 5.37, 5.57, 5.85, 6.31, 6.81; Δ: 4.65, 5.13, 5.66, 5.98, 6.12, 6.46, 6.79 at δ = 1.0, 1.3828125, 2.0, 2.3, 2.6, 3.0, 3.5', 'form': 'ws'},
    {'g': 'g7', 's': '4.70, 5.22, 6.04, 6.45, 6.70, 7.35, 7.83', 'form': 'ws'},
    {'g': 'g7', 's': 'η_lin = λ₁/|D_p| lies inside the near bracket at every triple in the small-shift regime η_hi T₀² ≤ 10⁻² (105 of the 124), the deviation |η_lin/η_hi − 1| growing by decade of η_hi T₀² — at most 3×10⁻³, 0.11, 0.54 on [10⁻², 10⁻¹), [10⁻¹, 1), ≥ 1', 'form': 'ws'},
    {'g': 'g7', 's': 'χ₋₃: 1.3/1.2/1.4/1.4/1.5/1.5/1.6; χ₋₄: 2.0/1.6/1.6/1.6/1.6/1.5; χ₈: 2.2/1.3/1.3/1.4/1.4/1.4; Δ: 2.8/2.4/2.2/2.1/2.1/2.0/1.9 at the cells with an unramified prime', 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ORDER = ["d1.0", "d1.38", "d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
FORDER = ["chi_-3", "chi_-4", "chi_8", "Delta"]
BAND_K = 0.1        # ln K1 - ln K2 (basis convergence of the pair)
BAND_Z = 1e-4       # the zero-side normalisation, relative
BAND_C = 1.2        # |c_L(delta) - c_zeta(delta)|, nats
FAR_RATIO = 1e6     # a far crossing in the other direction is at least this many times further
SMALL_X = 0.01      # the small-shift regime: eta_hi T_0^2 <= SMALL_X (the law's bracket containment)
BAND_1, BAND_2, BAND_3 = 3e-3, 0.15, 0.6   # |eta_lin/eta_hi - 1| for eta_hi T_0^2 in [0.01, 0.1), [0.1, 1), >= 1
ZETA_C = [4.70, 5.21, 5.94, 6.39, 6.64, 7.30, 7.90]     # Theorem 1bm(v)
LF = {(f, c): run_LF(f, c) for f in FORDER for c in ORDER}
LDESC = {f: FORMS[f]() for f in FORDER}
ZL = {}
for f in FORDER:
    p = os.path.join(HERE, "checkpoints", f"lfun_zeros_{f}.json")
    ZL[f] = json.load(open(p)) if os.path.exists(p) else None
ZZ = json.load(open(os.path.join(HERE, "checkpoints", "zeta_zeros_6700.json")))

def unramified(delta, L):
    e = math.exp(delta); ps = [p for p in range(2, int(e) + 1) if all(p % q for q in range(2, int(p**0.5) + 1))]
    return [p for p in ps if p < e and float(L["coef"](p, 1)) != 0]

# ---------------------------------------------------------------- g0
ok = True; ntrip = 0
for f in FORDER:
    for c in ORDER:
        st = LF[(f, c)]; L = LDESC[f]; d = LCELLS[c]
        ok &= st["form"] == f and st["cell"] == c and abs(st["delta"] - d) < 1e-12 and st["q"] == L["q"] and st["d"] == L["d"]
        ok &= st["K2"] == K_for(d, L) and st["K1"] == int(0.7*st["K2"]) and st["prec"] == PREC and abs(st["T0"] - horizon(d, L)) < 1e-9
        ok &= st["primes"] == unramified(d, L)
        ntrip += len(st["primes"])
gate(f"g0 the 28 (form, cell) states load at their keys with K2 = max(120, 4(2aT_0)/pi + 100), K1 = 0.7 K2, 600 bits, T_0 = 2 pi (e^delta/q)^(1/d), the unramified primes p <= e^delta ({ntrip} triples)", ok)

# ---------------------------------------------------------------- g1
ok = True; worstK = 0.0
for key, st in LF.items():
    ok &= st["min_K2"]["positive"] and st["min_K1"]["positive"] and st["min_K2"]["ln_upper"] is not None
    ok &= st["min_K2"]["ln_upper"] <= st["min_K1"]["ln_upper"] + 1e-12
    worstK = max(worstK, st["min_K1"]["ln_upper"] - st["min_K2"]["ln_upper"]); ok &= st["min_K1"]["ln_upper"] - st["min_K2"]["ln_upper"] <= BAND_K
G0, N0, pp0 = gram(1.0, 48, 400)
G1, N1, pp1 = gram_L(1.0, 48, 400, ZETA)
with ctx.workprec(400):
    reg = max(float(abs(G0[j, k] - G1[j, k]).upper()) for j in range(48) for k in range(48))
ok &= reg <= 1e-100 and pp0 == pp1
st = LF[("chi_-4", "d2.0")]
Gl, Nl, ppl = gram_L(2.0, st["K2"], PREC, LDESC["chi_-4"]); cl, _ = minimiser(Gl, Nl, PREC); rql = rayleigh(Gl, Nl, cl, PREC)
with ctx.workprec(PREC):
    live_ln = float(rql.upper().log())
ok &= abs(live_ln - st["min_K2"]["ln_upper"]) <= 1e-10 and ppl == st["prime_powers"]
gate(f"g1 the certified bounds: every K2 and K1 ball positive, ln K2 <= ln K1, the pair within {BAND_K} in ln (max {worstK:.3f}); the generalised Gram reproduces Theorem 1bn's zeta Gram at delta = 1.0, K = 48 (max |diff| {reg:.1e}); chi_-4 at delta = 2.0 re-derived live (|diff| {abs(live_ln - st['min_K2']['ln_upper']):.1e})", ok)

# ---------------------------------------------------------------- g2
mp.mp.dps = 30
def selftest(L, zeros, delta, K):
    """the prime-side Rayleigh quotient of the C_c^inf bump against the zero side on the list plus the smooth tail; returns
    (relative deviation, tail share, the prime powers inside the Gram)."""
    a = mp.mpf(delta)/2
    bump = lambda t: mp.e**(-1/(1 - (t/a)**2)) if abs(t) < a else mp.mpf(0)
    cb = [mp.quad(lambda t: bump(t)*mp.cos(k*mp.pi*t/a), [-a, 0, a])/(a if k else 2*a) for k in range(K)]
    G, N, pp = gram_L(delta, K, 400, L)
    qp = mp.mpf(rayleigh(G, N, [arb(str(x)) for x in cb], 400).mid().str(40, radius=False))
    den = sum((a if k else 2*a)*cb[k]**2 for k in range(K))
    def ghat(r):
        s = mp.mpf(0)
        for k in range(K):
            w = k*mp.pi/a
            s += cb[0]*2*mp.sin(r*a)/r if k == 0 else cb[k]*(mp.sin((r + w)*a)/(r + w) + mp.sin((r - w)*a)/(r - w))
        return s
    zs = [mp.mpf(z) for z in zeros]
    qz = 2*sum(ghat(g)**2 for g in zs); T = zs[-1]
    dens = lambda r: mp.log(L["q"]*(r/(2*mp.pi))**L["d"])/(2*mp.pi)
    tail = 2*mp.quad(lambda r: ghat(r)**2*dens(r), [T, 2*T, 10*T, 100*T])
    zz = (qz + tail)/den
    return float((zz - qp)/qp), float(tail/den/zz), pp
ok = True; zres = {}
for f in FORDER:
    z = ZL[f]
    if z is None: ok = False; zres[f] = None; continue
    L = LDESC[f]; Tl = z["zeros"][-1]
    smooth = (Tl/math.pi*math.log(Tl/(2*math.pi*math.e)) + 11/4) if f == "Delta" else (Tl/(2*math.pi)*math.log(L["q"]*Tl/(2*math.pi*math.e)) + L["kappas"][0]/4 - 1/8)
    ok &= z["half_step_agrees"] and abs(z["count"] - smooth) <= 1.0 and abs(z["smooth_count"] - smooth) <= 1e-6 and z["q"] == L["q"] and z["d"] == L["d"]
    ok &= all(z["zeros"][i] < z["zeros"][i + 1] for i in range(len(z["zeros"]) - 1)) and (z["phase_check"] is None or z["phase_check"] < 1e-8)
    rel, share, pp1 = selftest(LDESC[f], z["zeros"], 1.0, 24)
    rel2, share2, pp2 = selftest(LDESC[f], z["zeros"], 2.0, 40)           # round 313 F2: the cell where the local coefficients are exercised
    zres[f] = (rel, share, z["count"], z["zeros"][-1], rel2, pp1, pp2); ok &= abs(rel) <= BAND_Z and abs(rel2) <= BAND_Z
ok &= zres["chi_-3"][5] == [2] and zres["chi_-4"][5] == [] and zres["chi_8"][5] == [] and zres["Delta"][5] == [2]
ok &= zres["chi_-3"][6] == [2, 4, 5, 7] and zres["chi_-4"][6] == [3, 5, 7] and zres["chi_8"][6] == [3, 5, 7] and zres["Delta"][6] == [2, 3, 4, 5, 7]
# round 314 F314-4: the delta = 2.0 cell exercises the coefficients at 2, 3, 4, 5 -- the wrong rule c(p^k) = c(p)^k for Delta fails there by more than 0.5
_Ld = LDESC["Delta"]; _wrong = dict(_Ld, coef=lambda p, k: _Ld["coef"](p, 1)**k)
_relw, _, _ = selftest(_wrong, ZL["Delta"]["zeros"], 2.0, 40)
ok &= abs(_relw) > 0.5
# round 315 C4 / 316 F316-2: dropping every shell of any one of the primes 2, 3, 5 (where present) at delta = 2.0 moves the deviation by more than 0.1 at every form
_drops = {}
for f in FORDER:
    for pd in (2, 3, 5):
        if pd not in zres[f][6]: continue
        _Lf = LDESC[f]; _dropped = dict(_Lf, coef=(lambda P: (lambda p, k: 0 if p == P else _Lf["coef"](p, k)))(pd))
        _rd, _, _ = selftest(_dropped, ZL[f]["zeros"], 2.0, 40); _drops[(f, pd)] = _rd; ok &= abs(_rd) > 0.1
gate(f"g2 the normalisation: the prime-side quotient of the C_c^inf bump equals the zero side on each form's own zeros plus the smooth tail within {BAND_Z} at delta = 1.0 (K = 24; the prime side the shell 2 for chi_-3 and Delta, empty for chi_-4 and chi_8) and at delta = 2.0 (K = 40; the shells 2,4,5,7 / 3,5,7 / 3,5,7 / 2,3,4,5,7 inside, the coefficients at 2, 3, 4, 5 exercised: the wrong rule c(p^k) = c(p)^k for Delta deviates by {_relw:+.2f}; dropping every shell of one prime deviates by " + ", ".join(f"{f} {pd}: {v:+.2f}" for (f, pd), v in _drops.items()) + ") (" + ", ".join(f"{f}: {zres[f][0]:+.1e} and {zres[f][4]:+.1e} on {zres[f][2]} zeros to {zres[f][3]:.1f}" if zres[f] else f"{f}: NO ZERO LIST" for f in FORDER)
     + "); every list count-checked against the smooth count of the argument principle (recomputed) within 1 and by a half-step rescan, ordered, the phase check below 1e-8", ok)

# ---------------------------------------------------------------- g3
from scipy.optimize import minimize_scalar
from slack_law_flint import run as run_SLF
from true_form_cells import run as run_TF
def s_disc(zs, T, a):
    g = zs[zs < T]
    return 4*np.sum(np.log((1 + np.sqrt(1 - g*g/(T*T)))*T/g)) - 2*a*T
def s_cont(T, a, q, d):
    return T*(math.log(q*(T/(2*math.pi))**d) - d*(1 + math.log(2))) - 2*a*T
def disc_min(zs, delta, T0, lo=1.2, hi=3.0):
    """Theorem 1bm's minimiser (cascade_slack_law.formula_min): a 20001-point grid on [lo, hi] T_0 refined by bounded
    minimisation inside the zero-free intervals around the grid minimum (the function has a vertical tangent at every zero)."""
    a = delta/2
    grid = np.linspace(lo*T0, hi*T0, 20001); vals = np.array([s_disc(zs, T, a) for T in grid]); k = int(np.argmin(vals))
    l, h = grid[max(k - 1, 0)], grid[min(k + 1, len(grid) - 1)]
    pts = [l] + list(zs[(zs > l) & (zs < h)]) + [h]; best = float(vals[k]); Tb = float(grid[k])
    for a_, b_ in zip(pts[:-1], pts[1:]):
        r = minimize_scalar(lambda T: s_disc(zs, T, a), bounds=(a_ + 1e-9, b_ - 1e-9), method="bounded", options={"xatol": 1e-10})
        if float(r.fun) < best: best, Tb = float(r.fun), float(r.x)
    return best, Tb
ok = True; cz_bm = []; cz = []; cL = {}; contdev = 0.0; npairs = 0
zz = np.array(ZZ, dtype=float)
for i, c in enumerate(ORDER):
    d = LCELLS[c]; T0 = 2*math.pi*math.exp(d)
    m, Tm = disc_min(zz, d, T0)
    cz_bm.append(run_SLF(c)["ln_eig"] - m); cz.append(run_TF(c)["min_K2"]["ln_upper"] - m)
    ok &= abs(cz_bm[-1] - ZETA_C[i]) <= 0.01
for f in FORDER:
    z = ZL[f]
    if z is None: ok = False; continue
    zs = np.array(z["zeros"], dtype=float); L = LDESC[f]
    for i, c in enumerate(ORDER):
        st = LF[(f, c)]; d = LCELLS[c]; T0 = st["T0"]
        if zs[-1] < 2.5*T0: cL[(f, c)] = None; continue
        m, Tm = disc_min(zs, d, T0, 0.5, 2.5)
        off = st["min_K2"]["ln_upper"] - m; cL[(f, c)] = (off, Tm/T0); npairs += 1
        ok &= abs(off - cz[i]) <= BAND_C and 0.6 <= Tm/T0 <= 2.4          # the minimiser interior to the grid
        cont = min(s_cont(T, d/2, L["q"], L["d"]) for T in np.linspace(0.5*T0, 4*T0, 40001))
        contdev = max(contdev, abs(cont + 2*L["d"]*T0)/(2*L["d"]*T0)); ok &= abs(cont + 2*L["d"]*T0) <= 1e-6*2*L["d"]*T0
ok &= npairs == 28
# the conductor trend: the mean of c_zeta - c_L over the cells grows with q among the three characters (computed); round 313 F4:
# every gap positive and at most 1.05, Delta's gap increasing in delta
_gap = {f: sum(cz[ORDER.index(c)] - cL[(f, c)][0] for c in ORDER if cL.get((f, c)))/max(1, sum(1 for c in ORDER if cL.get((f, c)))) for f in FORDER}
ok &= 0 < _gap["chi_-3"] < _gap["chi_-4"] < _gap["chi_8"]
_gaps = [cz[ORDER.index(c)] - cL[(f, c)][0] for f in FORDER for c in ORDER if cL.get((f, c))]
ok &= 0.04 <= min(_gaps) and max(_gaps) <= 1.05
_dg = [cz[i] - cL[("Delta", c)][0] for i, c in enumerate(ORDER)]
ok &= all(_dg[i] < _dg[i + 1] for i in range(6))
ok &= all(abs(_gap[f] - v) <= 5e-3 for f, v in (("chi_-3", 0.48), ("chi_-4", 0.57), ("chi_8", 0.87), ("Delta", 0.50)))   # round 315 C3: the block's means (nearest)
ok &= abs(_dg[0] - 0.05) <= 5e-3 and abs(_dg[6] - 1.04) <= 5e-3                                                        # 'from 0.05 to 1.04'
gate("g3 the finite-delta formula on each form's own zeros: zeta's offsets from Theorem 1bm's own lambda_1 reproduce 1bm(v) within 0.01 (" + ", ".join(f"{x:.2f}" for x in cz_bm) + "; from 1bn's cosine-basis lambda_1, the basis of the L-forms: "
     + ", ".join(f"{x:.2f}" for x in cz) + f"); |c_L - c_zeta| <= {BAND_C} at every one of {npairs} (form, cell) pairs reached by the zero lists (to 2.5 T_0): "
     + "; ".join(f"{f}: " + ", ".join(f"{cL[(f, c)][0]:.2f}" if cL.get((f, c)) else "-" for c in ORDER) for f in FORDER) + "; minimiser T/T_0 in ["
     + (f"{min(v[1] for v in cL.values() if v):.2f}, {max(v[1] for v in cL.values() if v):.2f}]" if any(cL.values()) else "-]") + f"; the continuum minimum is -2 d T_0 (max rel dev {contdev:.1e}); c_zeta - c_L positive at all 28 pairs, in [{min(_gaps):.4f}, {max(_gaps):.4f}] (gated [0.04, 1.05]); mean by form " + ", ".join(f"{f}: {_gap[f]:.2f}" for f in FORDER) + "; Delta's gap increasing in delta: " + ", ".join(f"{x:.2f}" for x in _dg), ok)

# ---------------------------------------------------------------- g4
def near_far(r):
    br = {s: r[s] for s in ("down", "up") if r[s].get("status") == "bracketed"}
    if not br: return None, None
    near = min(br, key=lambda s: br[s]["eta_hi"])
    far = [s for s in br if s != near]
    return near, (far[0] if far else None)
def sign_ok(r):
    near, far = near_far(r)
    if near is None: return False
    if (near == "down") != (r["c_p"] > 0): return False
    other = "up" if near == "down" else "down"
    if r[other].get("status") == "bracketed":
        return r[other]["eta_hi"]/r[near]["eta_hi"] >= FAR_RATIO
    # round 313 F1: 'no crossing below the cap' means every sample of the doubling and of the 64-point log grid up to the cap
    # itself is a positive ball (the producer's scan); a computed statement about the samples, gated on its census fields
    o = r[other]
    return o.get("status") == "no crossing below cap" and o.get("scanned") == 64 and o.get("q_cap", {}).get("positive") is True and abs(o["eta_lo"] - o["cap"]) <= 1e-12*o["cap"]
ok = True; far_census = []; near_ratio = {}; capratio = 0.0
for (f, c), st in LF.items():
    for p, r in st["per_prime"].items():
        ok &= sign_ok(r) and r[near_far(r)[0]]["q_hi"]["negative"] and r[near_far(r)[0]]["q_lo"]["positive"]
        ok &= r[near_far(r)[0]]["eta_hi"]/r[near_far(r)[0]]["eta_lo"] <= 1 + TOL + 1e-12
        near, far = near_far(r)
        capratio = max(capratio, float(st["min_K2"]["upper"])/(ETA_CAP_FRAC*math.log(int(p))))   # round 314 C6: the search's first sample lambda_1 is far below the cap
        if far is not None: far_census.append((f, c, p, r[far]["eta_hi"]/r[near]["eta_hi"], r[far]["hi_over_cap"]))
        if int(p) == st["primes"][0]: near_ratio[(f, c)] = r[near]["hi_over_lambda"]
ok &= capratio <= 0.25
gate(f"g4 the sign rule at every triple (lambda_1 at most {capratio:.3f} of the cap, so the search's first sample lies below it): the near crossing (a certified negative ball at eta_hi, a positive one at eta_lo, width 1e-3) is downward iff c(p) > 0; the other direction has no crossing below the cap or a far one at least {FAR_RATIO:.0e} further (far crossings: "
     + (", ".join(f"{f} {c} p={p} at {x:.1e}x, {hc:.3f} cap" for f, c, p, x, hc in far_census) if far_census else "none") + "); the smallest unramified prime's eta_hi/lambda_1: "
     + ", ".join(f"{f}: " + "/".join(f"{near_ratio[(f, c)]:.1f}" for c in ORDER if (f, c) in near_ratio) for f in FORDER), ok)

# ---------------------------------------------------------------- g5
def dP_L(fg, p, coef, prec):
    with ctx.workprec(prec):
        lp = arb(p).log(); tot = arb(0); k = 1
        while k*lp < fg.twoa:
            u = k*lp; cc = coef(p, k); cc = arb(cc) if not isinstance(cc, arb) else cc
            tot += 2*cc*(-u/2).exp()*((1 - u/2)*fg(u) + u*fg.deriv(u))
            k += 1
        return tot
ok = True; devs = []; small_in = 0; nsmall = 0
for (f, c), st in LF.items():
    L = LDESC[f]; K2 = st["K2"]; d = st["delta"]
    G, N, pp = gram_L(d, K2, PREC, L)
    with ctx.workprec(PREC):
        a = arb(d)/2; cv = [arb(x) for x in st["coeffs"]]
        v = arb_mat(K2, 1)
        for i in range(K2): v[i, 0] = cv[i]
        num = (v.transpose()*G*v)[0, 0]
        den = arb(0)
        for i in range(K2): den += N[i]*cv[i]*cv[i]
        lam = num/den
        ok &= abs(float(lam.upper()) - float(st["min_K2"]["upper"])) <= 1e-20*float(st["min_K2"]["upper"])
        fg = AutocorrDeriv(cv, a, PREC)
        for p, r in st["per_prime"].items():
            D = -dP_L(fg, int(p), L["coef"], PREC)/den
            near, _ = near_far(r)
            ok &= (D.lower() > 0 and near == "down") or (D.upper() < 0 and near == "up")
            eta_lin = lam/abs(D)
            x = r[near]["eta_hi"]*st["T0"]**2                       # the second-order scale: shift x horizon^2
            ratio = float(eta_lin.mid())/r[near]["eta_hi"]; devs.append((x, abs(ratio - 1)))
            if x <= SMALL_X:
                nsmall += 1
                inside = r[near]["eta_lo"] <= float(eta_lin.lower()) and float(eta_lin.upper()) <= r[near]["eta_hi"]
                small_in += inside; ok &= inside
            else:
                ok &= abs(ratio - 1) <= (BAND_1 if x < 0.1 else BAND_2 if x < 1 else BAND_3)
ok &= small_in == nsmall
def band_max(lo, hi): 
    sel = [dv for xx, dv in devs if lo <= xx < hi]
    return (len(sel), max(sel)) if sel else (0, 0.0)
bands = [band_max(0, SMALL_X), band_max(SMALL_X, 0.1), band_max(0.1, 1), band_max(1, 1e9)]
ok &= bands[0][1] <= TOL and bands[1][1] <= BAND_1 and bands[2][1] <= BAND_2 and bands[3][1] <= BAND_3 and bands[0][1] < bands[2][1] < bands[3][1]
gate(f"g5 the law transferred live: the sign of D_p^L (the slope with c(p^k) in the shells) predicts the witnessed direction at every triple; eta_lin = lambda_1/|D_p| inside the near bracket at every triple with eta_hi T_0^2 <= {SMALL_X} ({small_in}/{nsmall}); the deviation |eta_lin/eta_hi - 1| by decade of eta_hi T_0^2: "
     + ", ".join(f"{lab}: n={n}, max {m:.4f}" for lab, (n, m) in zip(("<0.01", "0.01-0.1", "0.1-1", ">=1"), bands)) + f" (bands {TOL}, {BAND_1}, {BAND_2}, {BAND_3}; increasing) -- second order in the shift", ok)

# ---------------------------------------------------------------- g6
good = LF[("chi_-3", "d2.0")]["per_prime"]["7"]
bad1 = json.loads(json.dumps(good)); bad1["c_p"] = -1.0
bad2 = json.loads(json.dumps(good)); bad2["down"], bad2["up"] = good["up"], good["down"]
bad3 = json.loads(json.dumps(LF[("chi_-3", "d2.6")]["per_prime"]["2"])); bad3["down"]["eta_hi"] = bad3["up"]["eta_hi"]*10
bad4 = json.loads(json.dumps(good)); bad4["up"]["scanned"] = 63
bad5 = json.loads(json.dumps(good)); bad5["up"]["q_cap"]["positive"] = False
ok = sign_ok(good) and not sign_ok(bad1) and not sign_ok(bad2) and sign_ok(LF[("chi_-3", "d2.6")]["per_prime"]["2"]) and not sign_ok(bad3) and not sign_ok(bad4) and not sign_ok(bad5)
gate("g6 mangle probes: the sign-rule predicate fails on a flipped c(p), on swapped directions, on a far crossing brought within the ratio, on a 'no crossing' status with an incomplete scan, and on a non-positive cap ball", ok)

# ---------------------------------------------------------------- g7
import paper_needles
ROWS = ['| χ₋₃ | (3, 1) | −3.855 | −21.079 | −126.292 | 5.60 | 7.28 | 30 | 4 |', '| χ₋₄ | (4, 1) | −1.965 | −14.311 | −92.476 | 5.58 | 7.23 | 29 | 0 |', '| χ₈ | (8, 1) | −1.025 | −6.991 | −46.223 | 5.37 | 6.81 | 29 | 0 |', '| Δ | (1, 2) | −5.381 | −24.765 | −91.050 | 5.66 | 6.79 | 36 | 0 |']
S_Z = 'the relative deviations 6×10⁻¹¹, 5×10⁻⁹, 2×10⁻⁶, 2×10⁻⁶ at δ = 1.0 and 2×10⁻¹², 3×10⁻¹³, 9×10⁻⁸, 4×10⁻⁸ at δ = 2.0, for χ₋₃, χ₋₄, χ₈, Δ'
S_CL = 'χ₋₃: 4.18, 4.86, 5.60, 5.89, 6.37, 6.72, 7.28; χ₋₄: 4.06, 4.81, 5.58, 5.96, 6.15, 6.55, 7.23; χ₈: 3.87, 4.40, 5.37, 5.57, 5.85, 6.31, 6.81; Δ: 4.65, 5.13, 5.66, 5.98, 6.12, 6.46, 6.79 at δ = 1.0, 1.3828125, 2.0, 2.3, 2.6, 3.0, 3.5'
S_CZ = '4.70, 5.22, 6.04, 6.45, 6.70, 7.35, 7.83'
S_LAW = 'η_lin = λ₁/|D_p| lies inside the near bracket at every triple in the small-shift regime η_hi T₀² ≤ 10⁻² (105 of the 124), the deviation |η_lin/η_hi − 1| growing by decade of η_hi T₀² — at most 3×10⁻³, 0.11, 0.54 on [10⁻², 10⁻¹), [10⁻¹, 1), ≥ 1'
S_NEAR = 'χ₋₃: 1.3/1.2/1.4/1.4/1.5/1.5/1.6; χ₋₄: 2.0/1.6/1.6/1.6/1.6/1.5; χ₈: 2.2/1.3/1.3/1.4/1.4/1.4; Δ: 2.8/2.4/2.2/2.1/2.1/2.0/1.9 at the cells with an unramified prime'
# each call carries its literal (the precheck's clause D); the strings equal ROWS / S_* above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, '| χ₋₃ | (3, 1) | −3.855 | −21.079 | −126.292 | 5.60 | 7.28 | 30 | 4 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| χ₋₄ | (4, 1) | −1.965 | −14.311 | −92.476 | 5.58 | 7.23 | 29 | 0 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| χ₈ | (8, 1) | −1.025 | −6.991 | −46.223 | 5.37 | 6.81 | 29 | 0 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| Δ | (1, 2) | −5.381 | −24.765 | −91.050 | 5.66 | 6.79 | 36 | 0 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the relative deviations 6×10⁻¹¹, 5×10⁻⁹, 2×10⁻⁶, 2×10⁻⁶ at δ = 1.0 and 2×10⁻¹², 3×10⁻¹³, 9×10⁻⁸, 4×10⁻⁸ at δ = 2.0, for χ₋₃, χ₋₄, χ₈, Δ', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'χ₋₃: 4.18, 4.86, 5.60, 5.89, 6.37, 6.72, 7.28; χ₋₄: 4.06, 4.81, 5.58, 5.96, 6.15, 6.55, 7.23; χ₈: 3.87, 4.40, 5.37, 5.57, 5.85, 6.31, 6.81; Δ: 4.65, 5.13, 5.66, 5.98, 6.12, 6.46, 6.79 at δ = 1.0, 1.3828125, 2.0, 2.3, 2.6, 3.0, 3.5', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '4.70, 5.22, 6.04, 6.45, 6.70, 7.35, 7.83', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'η_lin = λ₁/|D_p| lies inside the near bracket at every triple in the small-shift regime η_hi T₀² ≤ 10⁻² (105 of the 124), the deviation |η_lin/η_hi − 1| growing by decade of η_hi T₀² — at most 3×10⁻³, 0.11, 0.54 on [10⁻², 10⁻¹), [10⁻¹, 1), ≥ 1', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, 'χ₋₃: 1.3/1.2/1.4/1.4/1.5/1.5/1.6; χ₋₄: 2.0/1.6/1.6/1.6/1.6/1.5; χ₈: 2.2/1.3/1.3/1.4/1.4/1.4; Δ: 2.8/2.4/2.2/2.1/2.1/2.0/1.9 at the cells with an unramified prime', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g7'] == ROWS + [S_Z, S_CL, S_CZ, S_LAW, S_NEAR]
_SUP = str.maketrans('⁻⁰¹²³⁴⁵⁶⁷⁸⁹', '-0123456789')
def _num(s):
    s = s.strip().replace('−', '-').replace('×10', 'e').translate(_SUP)
    return float(s)
# the rows: form | (q, d) | ln lambda_1 <= at delta = 1.0 | 2.0 | 3.5 (ceilings to 1e-3) | c_L(2.0) | c_L(3.5) (nearest 1e-2) | triples | far crossings
for _row, f in zip(ROWS, FORDER):
    fl = [x.strip() for x in _row.strip('|').split('|')]
    ok &= fl[0] == {"chi_-3": "χ₋₃", "chi_-4": "χ₋₄", "chi_8": "χ₈", "Delta": "Δ"}[f]
    ok &= fl[1] == f"({LDESC[f]['q']}, {LDESC[f]['d']})"
    for col, c in zip(fl[2:5], ("d1.0", "d2.0", "d3.5")):
        v = LF[(f, c)]["min_K2"]["ln_upper"]; ok &= _num(col) >= v and _num(col) - v < 1e-3 + 1e-9
    for col, c in zip(fl[5:7], ("d2.0", "d3.5")):
        ok &= cL.get((f, c)) is not None and abs(_num(col) - cL[(f, c)][0]) <= 5e-3 + 1e-9
    ok &= int(fl[7]) == sum(len(LF[(f, c)]["per_prime"]) for c in ORDER)
    ok &= int(fl[8]) == sum(1 for ff, _c, _p, _x, _hc in far_census if ff == f)
# the sentences
_m = __import__("re").findall(r"([0-9]×10⁻[⁰¹²³⁴⁵⁶⁷⁸⁹]+)", S_Z)
ok &= len(_m) == 8 and all(abs(zres[f][0]) <= _num(a) < 10*abs(zres[f][0]) + 1e-300 and _num(a) <= BAND_Z for a, f in zip(_m[:4], FORDER))   # one significant figure, up
ok &= all(abs(zres[f][4]) <= _num(a) < 10*abs(zres[f][4]) + 1e-300 and _num(a) <= BAND_Z for a, f in zip(_m[4:], FORDER))                   # the delta = 2.0 cell
_m = __import__("re").findall(r"([0-9]+\.[0-9]{2})", S_CL.split(" at δ")[0])
_vals = [cL[(f, c)][0] for f in FORDER for c in ORDER if cL.get((f, c))]
ok &= len(_m) == len(_vals) == npairs and all(abs(float(a) - b) <= 5e-3 + 1e-9 for a, b in zip(_m, _vals))
_m = __import__("re").findall(r"([0-9]+\.[0-9]{2})", S_CZ)
ok &= len(_m) == 7 and all(abs(float(a) - b) <= 5e-3 + 1e-9 for a, b in zip(_m, cz))
ok &= max(abs(cL[(f, c)][0] - cz[ORDER.index(c)]) for f in FORDER for c in ORDER if cL.get((f, c))) <= BAND_C
_m = __import__("re").search(r"\(([0-9]+) of the ([0-9]+)\)", S_LAW)
ok &= int(_m.group(1)) == small_in == nsmall and int(_m.group(2)) == ntrip == 124
_m = __import__("re").search(r"at most ([0-9.×⁻¹²³⁴⁵⁶⁷⁸⁹⁰]+), ([0-9.]+), ([0-9.]+) on", S_LAW)
ok &= _num(_m.group(1)) >= bands[1][1] and _num(_m.group(2)) >= bands[2][1] and _num(_m.group(3)) >= bands[3][1]
ok &= _num(_m.group(1)) <= 2*bands[1][1] + 1e-4 and _num(_m.group(2)) <= bands[2][1] + 0.01 and _num(_m.group(3)) <= bands[3][1] + 0.01
_m = __import__("re").findall(r"([0-9]+\.[0-9])", S_NEAR)
_nr = [near_ratio[(f, c)] for f in FORDER for c in ORDER if (f, c) in near_ratio]
ok &= len(_m) == len(_nr) and all(abs(float(a) - b) <= 0.05 + 1e-9 for a, b in zip(_m, _nr))
ok &= len(far_census) == 4 and [(x[0], x[1], x[2]) for x in far_census] == [("chi_-3", c, "2") for c in ("d2.3", "d2.6", "d3.0", "d3.5")]
ok &= all(x[3] >= 1e13 for x in far_census) and all(0.87 <= x[4] <= 0.97 for x in far_census)
ok &= 1.1e13 <= min(x[3] for x in far_census) < 1.2e13 and 1.3e54 < max(x[3] for x in far_census) <= 1.4e54 and all(far_census[i][4] > far_census[i + 1][4] for i in range(3))   # '1.1x10^13-1.4x10^54' (outward, tight to 2 s.f.), the position falling with delta
ok &= abs(far_census[0][4] - 0.97) <= 5e-3 and abs(far_census[3][4] - 0.87) <= 5e-3                                              # 'from 0.97 to 0.87 of the cap' (nearest; round 316 F316-3)
gate("g7 the paper's numbers parsed back from the declared needles: the four rows (ln lambda_1 ceilings to 1e-3 at three cells, c_L to 5e-3, the triple and far-crossing counts), the normalisation deviations at both cells, the offset lists (L and zeta) to 5e-3 and their band, the law's census and its deviation decades, the near ratios to 0.05, the four far crossings", ok)


# ---------------------------------------------------------------- g8
from cascade_tower import chain_ok
gate("g8 the chain obligation to cascade_linear_response.py (Theorem 1bp) met", chain_ok("cascade_linear_response.py"))

# ---------------------------------------------------------------- g9
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g9 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g9 the 1bq paper needles and the footer census (declared surface)", ok)

print(("\nALL GATES PASS (10/10)" if not fails else f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
