#!/usr/bin/env python3
"""Theorem 1bm -- the slack law: the zero side's ground state against
support, the horizon scaling of its exponent, and the constant 4 pi of
the reduced problem. Tower member 22 (top).

THE CLAIMS GATED. (1) THE CELLS. For real even probes of support delta,
lambda_1(delta) = min Q(g)/||g||^2 with Q the zero side of the explicit
formula, computed on the model "6700 listed zeros + the smooth density
beyond" in the Legendre basis (slack_law_flint.py): the Rayleigh
quotient of the computed vector is a ball, a rigorous upper bound on
the truncated model's lambda_1; the basis, list and tail truncations
are MEASURED by paired cells, not certified. Seven cells delta = 1.0,
1.3828125, 2.0, 2.3, 2.6, 3.0, 3.5 (EXTRA = 120 Legendre modes beyond
2 a T0/pi) plus three convergence cells (delta 2.0 at EXTRA 35 and 80;
delta 3.5 at EXTRA 300). (2) THE LAW. f(delta) = -ln lambda_1 / e^delta
rises monotonically across the cells and stays below 4 pi. (3) THE
REDUCED PROBLEM, SOLVED (A441): the equilibrium value f(X) = 2 pi X
(1 + ln 2 - ln X) with maximum 4 pi at X = 2, from A = pi/2 and
B = -(pi/2)(1 + ln 2); the balayage density's edge singularity coefficient
sqrt(X/2) ln(2/X) vanishing exactly at X = 2, its edge value there ln 2,
positive on the exterior; the exterior potential constant at -2 pi; the
interior potential <= 0 and monotone. (4) THE FINITE-delta
FORMULA (A442): ln lambda_1 = min_T [4 sum_{gamma<T} ln((1 + sqrt(1 -
gamma^2/T^2)) T/gamma) - 2 a T] + c(delta) (the minimum located by a
fine grid plus bounded refinement, round-290 F290-2) with 0 < c(delta)
<= 3 delta + 5 at every cell, and the discrete-to-continuum difference
2 s_delta(2 T0) + 4 pi e^delta between 10 and 8 delta + 15. (5) THE
CROSS-CHECKS: the delta = 1.0 cell inside Theorem 1bj's Temple
enclosure; the delta = 1.3828125 cell above Theorem 1bl's certified
even bound (and within a factor 2 of it -- the mechanism's band slack).
(6) THE PRIOR ART's NORMALISATION AND THE RESIDUAL (block (vii),
round 293): Connes-Consani (zeta-cycles, 2023) and Connes (arXiv
2602.04022, Feb 2026) report the same eigenvalue's exponential-of-
exponential decay numerically, the latter matched by graph to the
prolate law 1 - chi_2 ~ e^{-4 pi e^L + 9L/2}; the normalisation is
checked live at delta = log 2 (lambda_1 = 1.3292e-3 against their
"~ 0.00133"), and the cells' residual ln lambda_1 + 4 pi e^delta
(20.3 ... 32.9) has least-squares slope 5.04 per unit delta, gated in
[4.5, 5.5] and increasing -- consistent with, not a test of, a shared
9/2 subleading term.

WHAT IS NOT CLAIMED. The reduction of the true lambda_1 to the
equilibrium problem (A440 Step 1; A442's five lemmas) is not a
theorem; the cells are model values with certified upper bounds, not
certified lower bounds; no Riemann Hypothesis consequence.

Gates (thirteen, g0-g12):
  g0  the ten checkpoints load at the current keys (executable
      content + the zero list's sha256) with complete states; each
      Rayleigh ball's radius <= 1e-6 of its midpoint and the
      eigensolver's value inside the ball (relative 1e-6)
  g1  the pins: the paper's stated ln lambda_1 per cell within 2e-3 of
      the stored eigenvalue (-13.884, -27.765, -67.332, -98.330,
      -140.777, -221.942, -383.219 at the seven cells, the fresh-run
      values of the landing)
  g2  the law: f increasing across the seven cells; f < 4 pi at each;
      R = f/delta decreasing from delta = 2 on
  g3  the closed form LIVE: A = pi/2 and B = -(pi/2)(1 + ln 2) by
      quadrature (1e-8); f(2) = 4 pi; f(1.9), f(2.1) < f(2)
  g4  the balayage LIVE, on the exact kernel of the doubly slit plane
      (tau(x) = -I(x)/(pi sqrt(x^2 - X^2)), I(x) the Cauchy integral
      int sqrt(X^2 - t^2) ln|t|/(x - t) dt over the band): the edge
      identity I(X) = pi X ln(X/2) at X = 1.5, 2, 2.5, checked at x = X in
      its integrable form to 1e-9 (the 1/sqrt(x - X) coefficient sqrt(X/2) ln(2/X)
      vanishes exactly at the maximiser: positive at 1.95, negative at
      2.05), the edge value ln 2 at X = 2 (1e-3), density > 0 on the
      exterior to 1e6 X, the exterior potential within 3e-3 of -2 pi at
      five points, the interior potential <= 0 and monotone at twelve
      points (round-290 F290-1, F290-4)
  g5  the finite-delta formula: 0 < c(delta) <= 3 delta + 5 at every
      cell and increasing in delta (c = 4.70, 5.21, 5.94, 6.39, 6.64,
      7.30, 7.90 at the round-290 sweep)
  g6  the discrete-to-continuum difference in (10, 8 delta + 15) at
      every cell
  g7  basis convergence: ln lambda_1 non-increasing in EXTRA at delta
      2 (35 -> 80 -> 120, total change <= 0.05) and at delta 3.5
      (120 -> 300, change <= 0.5)
  g8  cross-checks: the delta 1.0 value inside the Temple rho
      enclosure (Theorem 1bj even-1.0 cell, loaded at its key);
      the delta 1.3828125 value >= Theorem 1bl's certified even bound
      and <= 2x it (loaded at its key)
  g9  mangle probes: the cell predicate fails on a ball not containing
      the eigenvalue, on a negative value, on a missing field
  g10 the chain obligation to cascade_slepian_mechanism.py (Theorem
      1bl) met
  g11 the 1bm paper needles and the footer census (declared surface)
  g12 the prior-art normalisation LIVE: lambda_1(log 2) on the
      2000-zero list at 320 bits within 5e-6 of Connes-Consani's
      "~ 0.00133" (Rayleigh radius < 1e-9); the residuals
      ln lambda_1 + 4 pi e^delta at the seven cells within 0.05 of
      the block's 20.3, 22.3, 25.5, 27.0, 28.4, 30.5, 32.9,
      increasing, least-squares slope in [4.5, 5.5] and within 0.01
      of the block's 5.04

Checks 7/8 clean: the explicit formula, Hadamard, Cartwright, Slepian,
the Green function of the slit plane, balayage, the maximum principle,
Euler-Maclaurin -- classical; no semiclassics; no hypothesis input
(Riemann-side).
"""
import math, os, sys, json

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from slack_law_flint import run as run_SL, CELLS, ZFILE_6700
from slepian_arb_certificate import run as run_SM
from oneprime_interval_temple import run as run_T1

# declared paper surface (the needle-precheck arc, A397): the
# member touches the paper ONLY through these entries.
PAPER_NEEDLES = [
    {'g': 'g11', 's': 'Theorem 1bm (the slack law', 'form': 'plain'},
    {'g': 'g11', 's': 'the exponent is twice the horizon', 'form': 'plain'},
    {'g': 'g11', 's': 'the reduction is not a theorem', 'form': 'plain'},
    {'g': 'g11', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 4},
    {'s': '`cascade_slack_law.py`', 'min': 2, 'g': 'g11'},
    {'s': 'the **89 scripts cited in place** above', 'form': 'ws', 'g': 'g11'},
    {'s': 'extended by Theorems 1i–1bm:', 'form': 'ws', 'g': 'g11'},
    {'g': 'g12', 's': 'λ₁(log 2) = 1.3292×10⁻³', 'form': 'ws'},
    {'g': 'g12', 's': 'the constant 4π is in print there as the prolate\'s, matched to ε(λ) by graph, not derived for ε(λ)', 'form': 'plain'},
    {'g': 'g12', 's': 'residual ln λ₁ + 4πeᵟ is 20.3, 22.3, 25.5, 27.0, 28.4, 30.5, 32.9, least-squares slope 5.04 per unit δ', 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

MAIN = ["d1.0", "d1.38", "d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
ST = {c: run_SL(c) for c in CELLS}
PINS = {"d1.0": -13.884, "d1.38": -27.765, "d2.0": -67.332, "d2.3": -98.330,
        "d2.6": -140.777, "d3.0": -221.942, "d3.5": -383.219}
FIELDS = ("cell", "delta", "parity", "prec", "extra", "nz", "gmax", "m", "zeros_sha256",
          "eig_mid", "rq_mid", "rq_rad", "rq_upper", "ln_rq_upper", "ln_eig", "verdict")

def cell_ok(st):
    if not all(f in st for f in FIELDS): return False
    if st["ln_eig"] >= 0 or not st["verdict"].startswith("COMPUTED"): return False
    mid = float(st["rq_mid"]); rad = float(st["rq_rad"]); eig = float(st["eig_mid"])
    if mid <= 0 or rad > 1e-6*mid: return False
    return abs(eig - mid) <= rad + 1e-6*mid

# ---------------------------------------------------------------- g0
ok = all(cell_ok(st) for st in ST.values()) and all(st["nz"] == 6700 for st in ST.values())
ok &= all(st["cell"] == c and st["parity"] == "even" for c, st in ST.items())
gate("g0 the ten checkpoints load at the current keys with complete states; each Rayleigh "
     "ball certified to 1e-6 and containing the eigensolver's value; 6700 zeros in every cell", ok)

# ---------------------------------------------------------------- g1
ok = all(abs(ST[c]["ln_eig"] - PINS[c]) <= 2e-3 for c in MAIN)
gate("g1 the pins: the stated ln lambda_1 within 2e-3 of the stored value at the seven cells", ok)

# ---------------------------------------------------------------- g2
f = {c: -ST[c]["ln_eig"]/math.exp(ST[c]["delta"]) for c in MAIN}
R = {c: f[c]/ST[c]["delta"] for c in MAIN}
ok = all(f[MAIN[i]] < f[MAIN[i + 1]] for i in range(len(MAIN) - 1))
ok &= all(v < 4*math.pi for v in f.values())
ok &= all(R[MAIN[i]] > R[MAIN[i + 1]] for i in range(2, len(MAIN) - 1))
gate("g2 the law: f = -ln lambda_1/e^delta increasing across the cells, below 4 pi, R = f/delta "
     "decreasing from delta = 2 (" + ", ".join(f"{f[c]:.3f}" for c in MAIN) + ")", ok)

# ---------------------------------------------------------------- g3
from scipy.integrate import quad
A = quad(lambda u: math.log((1 + math.sqrt(1 - u*u))/u), 0, 1, limit=400)[0]
B = quad(lambda u: math.log((1 + math.sqrt(1 - u*u))/u)*math.log(u), 0, 1, limit=400)[0]
fX = lambda X: 2*math.pi*X*(1 + math.log(2) - math.log(X))
ok = abs(A - math.pi/2) < 1e-8 and abs(B + (math.pi/2)*(1 + math.log(2))) < 1e-8
ok &= abs(fX(2.0) - 4*math.pi) < 1e-12 and fX(1.9) < fX(2.0) and fX(2.1) < fX(2.0)
ok &= abs(-2*(2*2*(A*math.log(2) + B)) - 4*math.pi) < 1e-7      # f(2) = -2 s(2), s(X) = 2X(A ln X + B): s(2) = 4(A ln 2 + B) = -2 pi
gate(f"g3 the closed form LIVE: A = pi/2 ({A:.10f}), B = -(pi/2)(1 + ln 2) ({B:.10f}), "
     f"f(X) = 2 pi X (1 + ln 2 - ln X) maximal at X = 2 with f = 4 pi", ok)

# ---------------------------------------------------------------- g4
import numpy as np
def I_int(x, X):
    """I(x) = int_{-X}^{X} sqrt(X^2 - t^2) ln|t| / (x - t) dt  (x > X): the balayage density of
    -(ln|t| dt on [-X, X]) onto the exterior is tau(x) = -I(x)/(pi sqrt(x^2 - X^2)), from the harmonic
    measure (1/pi) sqrt(X^2 - t^2)/(sqrt(x^2 - X^2) |x - t|) of the doubly slit plane (round-290 F290-1:
    the landing's disc-map trapezoid sample carried a 14 percent error at the edge)."""
    f = lambda t: math.sqrt(X*X - t*t)*math.log(abs(t))/(x - t)
    return quad(f, -X, 0, limit=400)[0] + quad(f, 0, X, limit=400)[0]
def tau(x, X): return -I_int(x, X)/(math.pi*math.sqrt(x*x - X*X))
def I_edge(X):
    """I at the edge x = X in its integrable form, int sqrt((X+t)/(X-t)) ln|t| dt = X int_{-pi/2}^{pi/2}
    (1 + sin psi) ln|X sin psi| dpsi (round-291 F291-1: the sweep's conjunct sampled I at x = X(1 + 1e-12),
    where the true value sits on the sqrt(x - X) branch by more than its 1e-5 tolerance at X = 2.5
    (-1.018e-5; -2.7e-6 and -6.2e-6 at X = 1.5 and 2), and passed only because the quadrature could not
    resolve that layer; the identity is now checked where it holds)."""
    f = lambda p: (1 + math.sin(p))*math.log(abs(X*math.sin(p)))*X
    return quad(f, -math.pi/2, 0, limit=400)[0] + quad(f, 0, math.pi/2, limit=400)[0]
X = 2.0
# (a) the edge identity I(X) = pi X ln(X/2), checked at x = X exactly (tolerance 1e-9): the coefficient of the
#     1/sqrt(x - X) singularity is sqrt(X/2) ln(2/X), zero exactly at X = 2 (the maximiser), positive below,
#     negative above
ok = all(abs(I_edge(Xv) - math.pi*Xv*math.log(Xv/2)) < 1e-9 for Xv in (1.5, 2.0, 2.5))
ok &= tau(1.95*1.0001, 1.95) > 0 and tau(2.05*1.0001, 2.05) < 0
# (b) the edge value at X = 2 is ln 2 (the singular part gone)
edge = tau(2.0*(1 + 1e-7), 2.0)
ok &= abs(edge - math.log(2)) < 1e-3
# (c) positive on the whole exterior at X = 2, on a log grid to 1e6 X
xs = X*np.concatenate([1 + np.geomspace(1e-7, 1, 60), np.geomspace(2, 1e6, 60)])
tv = np.array([tau(x, X) for x in xs]); ok &= bool(np.all(tv > 0))
# (d) the exterior potential is -2 pi and the interior potential is monotone from 0 to -2 pi:
#     the balayage measure on a fine log grid (exact density at cell midpoints)
edges = X*(1 + np.geomspace(1e-7, 4999, 4001)); mids = 0.5*(edges[1:] + edges[:-1]); widths = np.diff(edges)   # log-spaced in x - X: the near-edge cells resolve the potential at 1.001 X
tau_w = np.array([tau(m_, X) for m_ in mids])*widths
def phi_bal(x):
    fz = lambda y: math.log(abs(1 - x*x/(y*y)))*math.log(y)
    pts = [x] if 0 < x < X else []
    v = quad(fz, 1e-12, X, points=pts, limit=400)[0]
    return v + float(np.sum(tau_w*np.log(np.abs(1 - x*x/(mids*mids)))))
outs = [phi_bal(X*r) for r in (1.001, 1.3, 2.0, 4.0, 10.0)]
ok &= all(abs(v + 2*math.pi) < 3e-3 for v in outs)
ins = [phi_bal(x) for x in (0.01, 0.2, 0.4, 0.6, 0.8, 1.0, 1.2, 1.4, 1.6, 1.8, 1.9, 1.99)]
ok &= all(v <= 0 for v in ins) and all(ins[k] >= ins[k + 1] for k in range(len(ins) - 1))
gate("g4 the balayage LIVE (exact kernel): I(X) = pi X ln(X/2) at X = 1.5, 2, 2.5 (edge singularity "
     "coefficient sqrt(X/2) ln(2/X): positive at 1.95, negative at 2.05, zero at the maximiser); edge value "
     f"at X = 2 {edge:.5f} vs ln 2 {math.log(2):.5f}; density positive on the exterior to 1e6 X (min {tv.min():.2e}); "
     "exterior potential " + ", ".join(f"{v:.4f}" for v in outs) + f" (-2 pi = {-2*math.pi:.4f}); interior potential "
     "<= 0 and monotone non-increasing at twelve points", ok)

# ---------------------------------------------------------------- g5, g6
ZEROS = np.array([float(z) for z in json.load(open(ZFILE_6700))])
def s_delta(delta, T):
    a = delta/2; z = ZEROS[ZEROS < T]
    return 2*np.sum(np.log((1 + np.sqrt(1 - z*z/(T*T)))*T/z)) - a*T
def formula_min(delta):
    """min_T 2 s_delta(T): a 20001-point grid on [1.2, 3.0] T0 refined by bounded minimisation inside the
    zero-free intervals around the grid minimum (2 s_delta has a vertical tangent at every zero; round-290
    F290-2: the landing's 181-point grid overshot the minimum by up to 0.10 nats)."""
    from scipy.optimize import minimize_scalar
    T0 = 2*math.pi*math.exp(delta)
    grid = np.linspace(1.2*T0, 3.0*T0, 20001); vals = np.array([2*s_delta(delta, T) for T in grid]); k = int(np.argmin(vals))
    lo, hi = grid[max(k - 1, 0)], grid[min(k + 1, len(grid) - 1)]
    pts = [lo] + list(ZEROS[(ZEROS > lo) & (ZEROS < hi)]) + [hi]; best = float(vals[k])
    for a_, b_ in zip(pts[:-1], pts[1:]):
        r = minimize_scalar(lambda T: 2*s_delta(delta, T), bounds=(a_ + 1e-9, b_ - 1e-9), method="bounded", options={"xatol": 1e-10})
        best = min(best, float(r.fun))
    return best
cvals = {c: ST[c]["ln_eig"] - formula_min(ST[c]["delta"]) for c in MAIN}
ok = all(0 < cvals[c] <= 3*ST[c]["delta"] + 5 for c in MAIN)
ok &= all(cvals[MAIN[i]] < cvals[MAIN[i + 1]] for i in range(len(MAIN) - 1))
gate("g5 the finite-delta formula: offset c(delta) = ln lambda_1 - min_T 2 s_delta(T) in (0, 3 delta + 5] "
     "and increasing (" + ", ".join(f"{cvals[c]:.2f}" for c in MAIN) + ")", ok)
dvals = {c: 2*s_delta(ST[c]["delta"], 2*2*math.pi*math.exp(ST[c]["delta"])) + 4*math.pi*math.exp(ST[c]["delta"]) for c in MAIN}
ok = all(10 < dvals[c] < 8*ST[c]["delta"] + 15 for c in MAIN)
gate("g6 the discrete-to-continuum difference 2 s_delta(2 T0) + 4 pi e^delta in (10, 8 delta + 15) "
     "(" + ", ".join(f"{dvals[c]:.1f}" for c in MAIN) + ")", ok)

# ---------------------------------------------------------------- g7
e35, e80, e120 = ST["d2.0_e35"]["ln_eig"], ST["d2.0_e80"]["ln_eig"], ST["d2.0"]["ln_eig"]
ok = e35 >= e80 >= e120 and e35 - e120 <= 0.05
e120b, e300 = ST["d3.5"]["ln_eig"], ST["d3.5_e300"]["ln_eig"]
ok &= e120b >= e300 and e120b - e300 <= 0.5
gate(f"g7 basis convergence: delta 2 ln lambda_1 {e35:.3f} / {e80:.3f} / {e120:.3f} at EXTRA 35/80/120 "
     f"(non-increasing, total change {e35 - e120:.3f} <= 0.05); delta 3.5 {e120b:.3f} / {e300:.3f} at 120/300 "
     f"(change {e120b - e300:.3f} <= 0.5)", ok)

# ---------------------------------------------------------------- g8
PT = run_T1(); even10 = PT.get("even:1", {})
lam10 = math.exp(ST["d1.0"]["ln_eig"]); lam138 = math.exp(ST["d1.38"]["ln_eig"])
mech = run_SM("two", "even")
ok = bool(even10) and even10.get("certified") and even10["rho"][0]*(1 - 1e-3) <= lam10 <= even10["rho"][1]*(1 + 1e-3)
ok &= mech["final"] <= lam138 <= 2*mech["final"]
gate(f"g8 cross-checks: lambda_1(1.0) = {lam10:.5e} inside the Temple enclosure {even10.get('rho')}; "
     f"lambda_1(1.3828125) = {lam138:.4e} >= 1bl's certified {mech['final']:.4e} and <= 2x", ok)

# ---------------------------------------------------------------- g9
good = dict(ST["d2.0"])
bad1 = dict(good); bad1["rq_mid"] = str(float(good["rq_mid"])*1.01)           # ball not containing the eigenvalue
bad2 = dict(good); bad2["ln_eig"] = 1.0                                          # a non-negative value
bad3 = dict(good); del bad3["rq_rad"]                                            # a missing field
ok = cell_ok(good) and not cell_ok(bad1) and not cell_ok(bad2) and not cell_ok(bad3)
gate("g9 mangle probes: the cell predicate fails on a displaced ball, a non-negative value, a missing field", ok)

# ---------------------------------------------------------------- g10
from cascade_tower import chain_ok
gate("g10 the chain obligation to cascade_slepian_mechanism.py (Theorem 1bl) met",
     chain_ok("cascade_slepian_mechanism.py"))

# ---------------------------------------------------------------- g11
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g11 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g11 the 1bm paper needles and the footer census (declared surface)", ok)

# ---------------------------------------------------------------- g12
from slack_law_flint import lam1, load_zeros
Z2000 = load_zeros(os.path.join(HERE, "checkpoints", "zeta_zeros_2000.json"))
_lam, rq_log2, m_log2, _, _ = lam1(math.log(2), "even", 320, Z2000, 35)
v_log2 = float(rq_log2.mid()); r_log2 = float(rq_log2.rad())
ok = abs(v_log2 - 1.33e-3) <= 5e-6 and r_log2 < 1e-9            # Connes-Consani, zeta-cycles Figure 5: "~ 0.00133"
res = {c: ST[c]["ln_eig"] + 4*math.pi*math.exp(ST[c]["delta"]) for c in MAIN}
RES_PINS = {"d1.0": 20.3, "d1.38": 22.3, "d2.0": 25.5, "d2.3": 27.0, "d2.6": 28.4, "d3.0": 30.5, "d3.5": 32.9}
ok &= all(abs(res[c] - RES_PINS[c]) <= 0.05 for c in MAIN)
ok &= all(res[MAIN[i]] < res[MAIN[i + 1]] for i in range(len(MAIN) - 1))
slope = float(np.polyfit([ST[c]["delta"] for c in MAIN], [res[c] for c in MAIN], 1)[0])
ok &= 4.5 <= slope <= 5.5 and abs(slope - 5.04) <= 0.01
gate(f"g12 the prior-art normalisation LIVE: lambda_1(log 2) = {v_log2:.5e} (radius {r_log2:.1e}) vs Connes-Consani's "
     "~ 0.00133; residuals ln lambda_1 + 4 pi e^delta " + ", ".join(f"{res[c]:.1f}" for c in MAIN) +
     f" (pinned, increasing), least-squares slope {slope:.3f} in [4.5, 5.5] and within 0.01 of 5.04", ok)

print(("\nALL GATES PASS (13/13)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
