#!/usr/bin/env python3
"""Theorem 1ax verifier: the heat-flow energy at criticality -- the
Lyapunov identity for the de Bruijn-Newman zero flow, the dissipation
(pressure) census with matched-ensemble controls, and the
backward/forward criticality demonstration.

Gates (all exit-gated; any failure exits 1):
  g1  the Lyapunov identity: along the dB-N zero flow
      xdot_k = sum_{j != k} 2/(x_k - x_j), the log-gap Coulomb energy
      E = -sum_{j<k} log|x_j - x_k| satisfies dE/dt = -1/2 sum xdot^2
      (three lines of chain rule; the gate checks the identity LIVE on
      the windowed system of the first +-60 zeta zeros: an RK4 step at
      h = 1e-7 gives the finite-difference dE/dt matching -1/2 sum v^2
      to relative deviation < 5e-7, observed ~1.7e-7).
  g2  the dissipation anatomy at t = 0 (the pressure at criticality):
      1/2 sum v^2 pinned for the +-60-zero window; the minimum gap
      among the first 60 zeros located at (gamma_34, gamma_35) and
      pinned; the two-body backward-collision law t_c = -g^2/8 at that
      gap; the Lehmer-pair scale t_c ~ -1.8e-4 at gap 0.0377, the
      gamma_6709 pair (this last conjunct is constants-only
      arithmetic pinning the published number -- nature stated per
      the 1av-g2 precedent; the landing's "0.040" corrected round
      205 F2; the classical mechanism behind the historical lower
      bounds on Lambda).
  g3  the matched-ensemble controls: at the same local density ladder
      (integrity conjunct: ladder span within (0.97, 0.99) of the
      actual span -- observed 0.982; the ~2% bias INFLATES the
      ensembles and so DEPRESSES the arithmetic's raw percentile:
      the raw figure OVERSTATES the quietness, and the
      bias-corrected reading is gated alongside it -- the landing's
      "weakens, not strengthens" had the direction inverted,
      corrected round 205 F1), Poisson windows dissipate two orders
      more (median > 2000); true-GUE spectral windows (400 trials,
      600x600 eigvalsh, central window unfolded to the ladder) have
      median in (230, 265) raw and (225, 255) bias-corrected, with
      the arithmetic value at empirical percentile in (0.5, 4.0) raw
      and (2.0, 4.0) corrected, corrected > raw -- the low zeros are
      QUIETER than GUE on both readings: more rigid than
      random-matrix statistics at this height. Seeded generators;
      windows generous against platform jitter.
  g4  the criticality demonstration: backward flow (20 RK4 steps to
      t = -2e-4) raises E strictly monotonically and contracts the
      minimum gap strictly monotonically; forward flow (to +2e-4)
      lowers E and opens the gap, both strictly; endpoint values
      pinned.
  g5  the paper needles for the 1ax block (in-code list authoritative).
  g6  the chain obligation to cascade_floor_meter.py (Theorem 1aw) met.
  g7  the footer census (this script backticked >= 2; the anchored needles "the **84 scripts cited in place** above"
      and "extended by Theorems 1i–1bh:" -- round-218 F12 mirrored
      the tower-wide anchoring into this line).

Sabotage record (each: fresh tar tree, single mangle with application
verified by assert + cmp against pristine, restore verified by cmp;
censuses are the OBSERVED results of the landing suite -- five runs,
baseline exit 0, zero probe no-ops, every prediction matched):
  (a) title needle mangled in-span single-site in the paper
      -> OBSERVED: g5 FAIL alone (exit 1)
  (b) the dissipation pin mangled in code (183.4567 -> 183.6567)
      -> OBSERVED: g2 FAIL alone (the pressure census is load-bearing)
  (c) the GUE percentile window mangled in code ((0.5, 4.0) ->
      (5.0, 9.0)) -> OBSERVED: g3 FAIL alone (the rigidity reading is
      live)
  (d) footer census reverted 74 -> 73 in the paper -> OBSERVED: g7
      FAIL AND g6 FAIL (census propagation through the chained 1aw
      verifier's own footer gate)
"""
import sys, subprocess, os
import numpy as np
from mpmath import mp, zetazero

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")
paper = open(PAPER, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

mp.dps = 20
M = 60
gams = np.array([float(zetazero(k).imag) for k in range(1, M + 1)])
X0 = np.concatenate([-gams[::-1], gams])

def vel(X):
    D = X[:, None] - X[None, :]
    np.fill_diagonal(D, np.inf)
    return (2.0/D).sum(axis=1)

def energy(X):
    D = np.abs(X[:, None] - X[None, :])
    iu = np.triu_indices(len(X), 1)
    return -np.log(D[iu]).sum()

def rk4(X, h):
    k1 = vel(X); k2 = vel(X + h/2*k1); k3 = vel(X + h/2*k2); k4 = vel(X + h*k3)
    return X + h/6*(k1 + 2*k2 + 2*k3 + k4)

# ---------------------------------------------------------------- g1
V0 = vel(X0)
diss = 0.5*(V0**2).sum()
h = 1e-7
lhs = (energy(rk4(X0, h)) - energy(X0))/h
rel = abs(lhs + diss)/diss
ok = rel < 5e-7
print(f"  g1 dE/dt numeric = {lhs:.6f}; -1/2 sum v^2 = {-diss:.6f}; rel dev {rel:.2e}", flush=True)
gate("g1 the Lyapunov identity dE/dt = -1/2 sum v^2, live on the windowed "
     "arithmetic system", ok)

# ---------------------------------------------------------------- g2
gaps = np.diff(gams)
imin = int(np.argmin(gaps))
tc = -gaps[imin]**2/8
ok = abs(diss - 183.4567) < 0.001
ok &= imin == 33                                  # (gamma_34, gamma_35)
# display-equal pins (round 205 F3: deterministic quantities, half-ULP
# of the displayed 4-dp digits; zetazero at dps 20 + fixed-order float64
# leaves ~1e-9 headroom)
ok &= abs(gaps[imin] - 0.8451) < 5e-5
ok &= abs(gams[imin] - 111.0295) < 5e-5 and abs(gams[imin+1] - 111.8747) < 5e-5
ok &= abs(tc - (-0.0893)) < 5e-5
# the Lehmer-pair scale: constants-only arithmetic pinning the published
# number (nature stated per the 1av-g2 precedent; the landing's 0.040
# corrected to the true gamma_6709-pair gap round 205 F2)
g_lehmer = 0.037698
ok &= abs(-g_lehmer**2/8 - (-1.7765e-4)) < 1e-8
print(f"  g2 pressure = {diss:.4f}; min gap {gaps[imin]:.4f} at "
      f"(gamma_{imin+1}, gamma_{imin+2}) = ({gams[imin]:.4f}, {gams[imin+1]:.4f}); "
      f"t_c = {tc:.5f}; Lehmer scale {-g_lehmer**2/8:.1e}", flush=True)
gate("g2 the dissipation anatomy: the pressure pinned, the tightest pair "
     "located, the collision law, the Lehmer scale", ok)

# ---------------------------------------------------------------- g3
def mean_spacing(g):
    return 2*np.pi/np.log(g/(2*np.pi))
ladder = sum(mean_spacing(gams[k]) for k in range(1, M))
span_ratio = ladder/(gams[-1] - gams[0])
ok = 0.97 < span_ratio < 0.99
def diss_of(gs):
    X = np.concatenate([-gs[::-1], gs])
    return 0.5*(vel(X)**2).sum()
rng = np.random.default_rng(1)
dp = []
for _ in range(200):
    gs = [gams[0]]
    for k in range(1, M):
        gs.append(gs[-1] + rng.exponential(mean_spacing(gams[k])))
    dp.append(diss_of(np.array(gs)))
ok &= np.median(dp) > 2000
rng = np.random.default_rng(7)
N = 600
dg, dgc = [], []
for _ in range(400):
    A = rng.normal(size=(N, N)) + 1j*rng.normal(size=(N, N))
    Hm = (A + A.conj().T)/2
    ev = np.linalg.eigvalsh(Hm)
    c = ev[N//2 - M//2 - 1 : N//2 + M//2]
    s = np.diff(c); s = s/s.mean()
    gs, gsc = [gams[0]], [gams[0]]
    for k in range(1, M):
        gs.append(gs[-1] + s[k-1]*mean_spacing(gams[k]))
        # bias-corrected construction (round 205 F1): the same draw with
        # spacings rescaled so the ladder matches the actual span
        gsc.append(gsc[-1] + s[k-1]*mean_spacing(gams[k])/span_ratio)
    dg.append(diss_of(np.array(gs)))
    dgc.append(diss_of(np.array(gsc)))
dg = np.array(dg); dgc = np.array(dgc)
med = float(np.median(dg))
pct = float(100*np.mean(dg < diss))
medc = float(np.median(dgc))
pctc = float(100*np.mean(dgc < diss))
ok &= 230 < med < 265
ok &= 0.5 < pct < 4.0
# round 205 F1: the ladder bias DEPRESSES the raw percentile (the raw
# figure OVERSTATES the quietness); the bias-corrected reading gated
ok &= 225 < medc < 255
ok &= 2.0 < pctc < 4.0
ok &= pctc > pct                     # the correction's direction itself
print(f"  g3 ladder/span = {span_ratio:.4f}; Poisson median {np.median(dp):.0f}; "
      f"GUE median {med:.2f} (corrected {medc:.2f}); arithmetic percentile "
      f"raw {pct:.1f}%, corrected {pctc:.1f}%", flush=True)
gate("g3 the matched-ensemble controls: Poisson two orders louder; the "
     "arithmetic below GUE raw AND bias-corrected (the raw percentile "
     "overstates the quietness -- direction corrected round 205 F1)", ok)

# ---------------------------------------------------------------- g4
Xb = X0.copy(); Eb = [energy(Xb)]; gmin = [np.min(np.diff(Xb[M:]))]
for _ in range(20):
    Xb = rk4(Xb, -1e-5)
    Eb.append(energy(Xb)); gmin.append(np.min(np.diff(Xb[M:])))
Xf = X0.copy(); Ef = [energy(Xf)]; gminf = [np.min(np.diff(Xf[M:]))]
for _ in range(20):
    Xf = rk4(Xf, 1e-5)
    Ef.append(energy(Xf)); gminf.append(np.min(np.diff(Xf[M:])))
ok = all(Eb[i+1] > Eb[i] for i in range(20))
ok &= all(gmin[i+1] < gmin[i] for i in range(20))
ok &= all(Ef[i+1] < Ef[i] for i in range(20))
ok &= all(gminf[i+1] > gminf[i] for i in range(20))
# display-equal endpoint pins (round 205 F3: deterministic RK4 at fixed
# order, half-ULP of the displayed 4-dp digits)
ok &= abs(Eb[0] - (-31326.1167)) < 5e-5 and abs(Eb[-1] - (-31326.0800)) < 5e-5
ok &= abs(Ef[-1] - (-31326.1534)) < 5e-5
ok &= abs(gmin[-1] - 0.8443) < 5e-5 and abs(gminf[-1] - 0.8459) < 5e-5
print(f"  g4 backward: E {Eb[0]:.4f} -> {Eb[-1]:.4f}, gap {gmin[0]:.4f} -> {gmin[-1]:.4f}; "
      f"forward: E -> {Ef[-1]:.4f}, gap -> {gminf[-1]:.4f}", flush=True)
gate("g4 the criticality demonstration: backward raises E and closes the "
     "tightest gap, forward the reverse, all strictly monotone, endpoints "
     "pinned", ok)

# ---------------------------------------------------------------- g5
needles = [
    "**Theorem 1ax (the heat-flow energy at criticality:",
    "monotonicity is\nalgebra, not hope",
    "dE/dt = −½ Σ ẋ_k²",
    "pressure at criticality: ½Σv² = 183.46",
    "the 1.8th\npercentile",
    "quieter than GUE",
    "t_c = −g²/8",
    "the last configuration the backward flow cannot improve",
    "not to descend an entropy gradient but to place",
    "the hardness is conserved at P4",
]
ok = all(nd in paper for nd in needles)
for nd in needles:
    if nd not in paper:
        print(f"  g5 MISSING: {nd!r}", flush=True)
gate("g5 the 1ax paper needles", ok)

# ---------------------------------------------------------------- g6
sys.path.insert(0, HERE)
from cascade_tower import chain_ok
gate("g6 the chain obligation to cascade_floor_meter.py (Theorem 1aw) met",
     chain_ok("cascade_floor_meter.py"))

# ---------------------------------------------------------------- g7
ok = paper.count("`cascade_heatflow_energy.py`") >= 2
ok &= "the **84 scripts cited in place** above" in paper
ok &= "extended by Theorems 1i–1bh:" in paper
gate("g7 the footer census (this script backticked >= 2; 84 cited in place; "
     "the range 1i–1bh)", ok)

print(flush=True)
if fails:
    print(f"FAILURES ({len(fails)}):")
    for f in fails:
        print("  " + f)
    sys.exit(1)
print("ALL GATES PASS (7/7)")
