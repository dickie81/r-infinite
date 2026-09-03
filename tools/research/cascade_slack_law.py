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
B = -(pi/2)(1 + ln 2); the balayage density positive on the exterior at
X = 2 and negative at the edge for X = 2.1; the exterior potential
constant at -2 pi; the interior potential <= 0. (4) THE FINITE-delta
FORMULA (A442): ln lambda_1 = min_T [4 sum_{gamma<T} ln((1 + sqrt(1 -
gamma^2/T^2)) T/gamma) - 2 a T] + c(delta) with 0 < c(delta) <= 3 delta
+ 5 at every cell, and the discrete-to-continuum difference
2 s_delta(2 T0) + 4 pi e^delta between 10 and 8 delta + 15. (5) THE
CROSS-CHECKS: the delta = 1.0 cell inside Theorem 1bj's Temple
enclosure; the delta = 1.3828125 cell above Theorem 1bl's certified
even bound (and within a factor 2 of it -- the mechanism's band slack).

WHAT IS NOT CLAIMED. The reduction of the true lambda_1 to the
equilibrium problem (A440 Step 1; A442's five lemmas) is not a
theorem; the cells are model values with certified upper bounds, not
certified lower bounds; no Riemann Hypothesis consequence.

Gates (twelve, g0-g11):
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
  g4  the balayage LIVE (harmonic measure of the doubly slit plane):
      density > 0 on the exterior at X = 2 (six points to 10 X), the
      edge density < 0 at X = 2.1, the exterior potential within 3e-3
      of -2 pi at five points, the interior potential <= 0 at five
      points
  g5  the finite-delta formula: 0 < c(delta) <= 3 delta + 5 at every
      cell and increasing in delta
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
def bal_density(x, X, n=4001):
    """-(balayage of ln|t| dt on [-X, X]) at x > X: harmonic measure of the doubly slit plane through
    the disc map w = z/(1 + sqrt(1 - z^2)); boundary point x = X/cos(theta), both sides of the slit."""
    th = math.acos(X/x); dx_dth = X*math.sin(th)/math.cos(th)**2
    ts = np.linspace(-X, X, n + 1)[1:-1]; zeta = ts/X
    w0 = zeta/(1 + np.sqrt(1 - zeta*zeta))
    P = (1 - w0*w0)/(1 - 2*w0*math.cos(th) + w0*w0)
    return -float(np.trapezoid(P/math.pi*np.log(np.abs(ts)), ts))/dx_dth
def phi_bal(x, X, mids, tau_w):
    fz = lambda y: math.log(abs(1 - x*x/(y*y)))*math.log(y)
    pts = [x] if 0 < x < X else []
    v = quad(fz, 1e-12, X, points=pts, limit=400)[0]
    return v + float(np.sum(tau_w*np.log(np.abs(1 - x*x/(mids*mids)))))
X = 2.0
edges = X*np.geomspace(1, 2000, 2001); mids = 0.5*(edges[1:] + edges[:-1]); widths = np.diff(edges)
dens = np.array([bal_density(m_, X) for m_ in mids]); tau_w = dens*widths
ok = all(bal_density(X*r, X) > 0 for r in (1.0005, 1.05, 1.3, 2.0, 4.0, 10.0))
ok &= bal_density(2.1*1.0005, 2.1) < 0
outs = [phi_bal(X*r, X, mids, tau_w) for r in (1.001, 1.3, 2.0, 4.0, 10.0)]
ok &= all(abs(v + 2*math.pi) < 3e-3 for v in outs)
ins = [phi_bal(x, X, mids, tau_w) for x in (0.01, 0.5, 1.0, 1.5, 1.99)]
ok &= all(v <= 0 for v in ins)
gate("g4 the balayage LIVE: density positive on the exterior at X = 2 (edge %.3f), negative at the "
     "edge for X = 2.1 (%.3f); exterior potential %s (-2 pi = %.4f); interior potential <= 0"
     % (bal_density(X*1.0005, X), bal_density(2.1*1.0005, 2.1), ", ".join(f"{v:.4f}" for v in outs), -2*math.pi), ok)

# ---------------------------------------------------------------- g5, g6
ZEROS = np.array([float(z) for z in json.load(open(ZFILE_6700))])
def s_delta(delta, T):
    a = delta/2; z = ZEROS[ZEROS < T]
    return 2*np.sum(np.log((1 + np.sqrt(1 - z*z/(T*T)))*T/z)) - a*T
def formula_min(delta):
    T0 = 2*math.pi*math.exp(delta)
    return min(2*s_delta(delta, x*T0) for x in np.linspace(1.2, 3.0, 181))
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

print(("\nALL GATES PASS (12/12)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
