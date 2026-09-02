#!/usr/bin/env python3
"""Theorem 1ay verifier: the saddle and the arithmetic curvature -- the
block Hessian [[L, 0], [0, -L]] of the heat-flow energy at real
configurations, the stability spectrum with exact flow rates, the
curvature census with matched-ensemble controls, and the explicit-
formula conversion of the band-limited curvature into a prime sum.

Gates (all exit-gated; any failure exits 1):
  g1  the saddle theorem: at a real configuration the full Hessian of
      E in complexified coordinates is [[L, 0], [0, -L]] with L the
      weighted graph Laplacian (weights 1/(x_j - x_k)^2) -- forced by
      2D harmonicity of the log kernel; verified by finite differences
      on the +-60-zero window at 16 index pairs spanning the tight-pair
      region (max |Hxx - L|, |Hyy + L|, |Hxy| each < 5e-6, observed
      ~6e-7/6e-7/0); the signature census (119 +, mirror -, 2 zero of
      2n = 240); the zero mode < 1e-12 (translations).
  g2  the stability spectrum: lambda_2 = 0.00413 (the soft collective
      edge), lambda_max = 3.1867 (the stiff edge), the top mode
      localized on the tightest pair (argmax at |x| = 111.8747, IPR
      0.250 -- the four-site antisymmetric structure); the two-body
      comparison printed in both currencies: eigenvalue 2/g^2 = 2.8002
      and rate 4/g^2 = 5.6004 (the actual mode's lambda_max = 3.1867
      is STIFFENED by neighbour coupling relative to the isolated
      pair's eigenvalue -- the landing's "softened", which also
      conflated the currencies, struck round 207 F3).
  g3  the exact flow rates: off-line perturbations along eigenmodes of
      L relax under the nonlinear holomorphic dB-N flow at rate
      2 lambda_k -- measured/predicted ratio in (0.999, 1.001) at the
      soft edge and (0.998, 1.001) at the stiff edge (observed 1.0000
      and 0.9998); forward flow restores the line mode by mode, the
      backward flow amplifies at the same rates.
  g4  the curvature census: tr L = 91.728 for the window (the pair
      functional sum 1/D^2); the finiteness dichotomy -- GUE's
      R2 ~ u^2 exactly cancels the 1/u^2 kernel (the unqualified
      integral is 2 pi^2/3 = 6.5797 in closed form, round 207 F2; the
      instrument's u <= 60 band gives I_gue = 6.54575, cutoff
      disclosed and gated against the closed form) while Poisson's
      R2 = 1 diverges (gated
      demonstration: seeded Poisson windows give median trace > 500,
      an order beyond the arithmetic); seeded true-GUE windows: trace
      median in (110, 140) with the arithmetic at percentile
      (0.5, 4.0) -- the same low-height rigidity as the 1ax pressure,
      now in the curvature -- while lambda_2 sits at percentile
      (5, 25): the rigidity lives in the STIFF modes (close pairs),
      not the soft collective ones.
  g5  the conversion (the curvature's arithmetic representation): the
      Weil explicit formula rebuilds the tapered zeros' exponential
      sum S(omega) from archimedean + pole + prime terms to max
      deviation < 1e-3 on scale ~52 over omega in (0.3, 4.2) (Gaussian
      taper, first 100 zeros); the ten deepest spikes of S sit at
      log n for n = 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, each within
      0.002 with the per-spike maximum gated at 0.0011 (round 207 F1;
      the log 23 spike at 0.001006); the band-limited curvature identity C_pairs = spectral
      integral to rel dev < 1e-4 (Parseval); the fill ladder: the
      no-prime (archimedean + pole + diagonal, round 207 F6) value
      294.24, primes <= 29
      give 122.40, primes <= 97 land within rel dev 1e-4 of the
      measured value 28.832 -- the primes carve the band-limited
      curvature down from the structureless baseline by an order of
      magnitude, each at its own frequency log p^k; the convergence
      is NOT monotone (the y = 53 overshoot gated: C(53) < C_pairs).
  g6  the paper needles for the 1ay block (in-code list authoritative).
  g7  the chain obligation to cascade_heatflow_energy.py (Theorem 1ax) met.
  g8  the footer census (this script backticked >= 2; the anchored needles "the **86 scripts cited in place** above"
      and "extended by Theorems 1i–1bj:" -- round-218 F12 mirrored
      the tower-wide anchoring into this line).

Sabotage record (each: fresh tar tree, single mangle with application
verified by assert + cmp against pristine, restore verified by cmp;
censuses are the OBSERVED results):
  (a) title needle mangled in-span single-site in the paper
      -> OBSERVED: g6 FAIL alone (exit 1; also observed identically in
      the first, wipe-killed suite before its container died)
  (b) the trace pin mangled in code (91.728 -> 91.928)
      -> OBSERVED: g4 FAIL alone (the curvature census is load-bearing)
  (c) the fill-ladder y = 29 pin shifted in code (122.40 -> 122.60;
      redesigned pre-run from a tighten-past-truth mangle whose no-op
      risk was caught at design time) -> OBSERVED: g5 FAIL alone
  (d) footer census reverted 75 -> 74 in the paper -> OBSERVED: g8
      FAIL AND g7 FAIL (census propagation through the chained 1ax
      verifier's own footer gate)
"""
import sys, subprocess, os
import numpy as np
from scipy.special import psi as scipy_digamma
from scipy.signal import argrelextrema
from mpmath import mp, zetazero

HERE = os.path.dirname(os.path.abspath(__file__))

# declared paper surface (the needle-precheck arc, A397): the
# member touches the paper ONLY through these entries.
PAPER_NEEDLES = [
    {'g': 'g6', 's': '**Theorem 1ay (the saddle and the arithmetic curvature:'},
    {'g': 'g6', 's': 'Hess E = [[L, 0], [0, −L]]'},
    {'g': 'g6', 's': 'a perfect saddle'},
    {'g': 'g6', 's': '(119 positive, 119 negative — exact\nmirrors, 2 zero)'},
    {'g': 'g6', 's': 'ratio 1.0000 at the soft edge and 0.9998'},
    {'g': 'g6', 's': 'finiteness is the quadratic-repulsion statement'},
    {'g': 'g6', 's': 'the rigidity has a spectral address'},
    {'g': 'g6', 's': 'the ten deepest spikes'},
    {'g': 'g6', 's': 'the primes carve the band-limited curvature'},
    {'g': 'g6', 's': 'the quantifier over test functions'},
    {'g': 'g6', 's': 'no literature sweep was run'},
    {'g': 'g8', 's': '`cascade_saddle_curvature.py`', 'min': 2},
    {'g': 'g8', 's': 'the **86 scripts cited in place** above'},
    {'g': 'g8', 's': 'extended by Theorems 1i–1bj:'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

mp.dps = 20
M100 = 100
gams100 = np.array([float(zetazero(k).imag) for k in range(1, M100 + 1)])
gams = gams100[:60]
M = 60
X0 = np.concatenate([-gams[::-1], gams])
n = len(X0)

def build_L(X):
    D = X[:, None] - X[None, :]
    np.fill_diagonal(D, np.inf)
    W = 1.0/D**2
    L = -W
    np.fill_diagonal(L, W.sum(axis=1))
    return L

L = build_L(X0)

# ---------------------------------------------------------------- g1
def E2(x, y):
    zz = x + 1j*y
    Dz = np.abs(zz[:, None] - zz[None, :])
    iu = np.triu_indices(len(zz), 1)
    return -np.log(Dz[iu]).sum()
h = 2e-3
idx = np.array([93, 94, 95, 96, 30, 31, 60, 90])
errs = []
for a in idx[:4]:
    for b in idx[4:]:
        ei = np.zeros(n); ei[a] = 1
        ej = np.zeros(n); ej[b] = 1
        fpp = E2(X0 + h*ei + h*ej, 0*X0); fpm = E2(X0 + h*ei - h*ej, 0*X0)
        fmp = E2(X0 - h*ei + h*ej, 0*X0); fmm = E2(X0 - h*ei - h*ej, 0*X0)
        Hxx = (fpp - fpm - fmp + fmm)/(4*h*h)
        fpp = E2(X0, h*ei + h*ej); fpm = E2(X0, h*ei - h*ej)
        fmp = E2(X0, -h*ei + h*ej); fmm = E2(X0, -h*ei - h*ej)
        Hyy = (fpp - fpm - fmp + fmm)/(4*h*h)
        fpp = E2(X0 + h*ei, h*ej); fpm = E2(X0 + h*ei, -h*ej)
        fmp = E2(X0 - h*ei, h*ej); fmm = E2(X0 - h*ei, -h*ej)
        Hxy = (fpp - fpm - fmp + fmm)/(4*h*h)
        errs.append((abs(Hxx - L[a, b]), abs(Hyy + L[a, b]), abs(Hxy)))
errs = np.array(errs)
ev, V = np.linalg.eigh(L)
npos = int((ev > 1e-9).sum())
ok = errs[:, 0].max() < 5e-6 and errs[:, 1].max() < 5e-6 and errs[:, 2].max() < 5e-6
ok &= npos == n - 1 and abs(ev[0]) < 1e-12
print(f"  g1 FD errs: |Hxx-L| {errs[:,0].max():.1e}, |Hyy+L| {errs[:,1].max():.1e}, "
      f"|Hxy| {errs[:,2].max():.1e}; signature ({npos} +, mirror -, 2 zero) of "
      f"{2*n}; zero mode {ev[0]:.1e}", flush=True)
gate("g1 the saddle theorem: Hess E = [[L, 0], [0, -L]] at the real "
     "configuration (2D harmonicity), signature and zero mode", ok)

# ---------------------------------------------------------------- g2
lam2, lammax = ev[1], ev[-1]
top = V[:, -1]
ipr = float((top**4).sum())
kmax = int(np.argmax(np.abs(top)))
gaps = np.diff(gams)
imin = int(np.argmin(gaps))
ok = abs(lam2 - 0.00413) < 5e-6
ok &= abs(lammax - 3.1867) < 5e-5
ok &= abs(ipr - 0.250) < 5e-4
ok &= abs(abs(X0[kmax]) - 111.8747) < 5e-5
print(f"  g2 lambda_2 = {lam2:.5f}; lambda_max = {lammax:.4f}; IPR {ipr:.3f}; "
      f"peak |x| = {abs(X0[kmax]):.4f}; two-body eigenvalue 2/g^2 = "
      f"{2/gaps[imin]**2:.4f} (rate currency 4/g^2 = {4/gaps[imin]**2:.4f})", flush=True)
gate("g2 the stability spectrum: soft edge, stiff edge, tight-pair "
     "localization", ok)

# ---------------------------------------------------------------- g3
def velC(Z):
    Dz = Z[:, None] - Z[None, :]
    np.fill_diagonal(Dz, np.inf)
    return (2.0/Dz).sum(axis=1)
def rk4C(Z, hs):
    k1 = velC(Z); k2 = velC(Z + hs/2*k1); k3 = velC(Z + hs/2*k2); k4 = velC(Z + hs*k3)
    return Z + hs/6*(k1 + 2*k2 + 2*k3 + k4)
ok = True
rates = []
for kmode, lam, hstep in ((1, ev[1], 1e-4), (n - 1, ev[-1], 1e-6)):
    v = V[:, kmode]
    eps = 1e-6
    Zp = X0 + 1j*eps*v
    Zb = X0.astype(complex)
    steps = 40
    for _ in range(steps):
        Zp = rk4C(Zp, hstep); Zb = rk4C(Zb, hstep)
    a1 = float(np.linalg.norm((Zp - Zb).imag))
    rate = -np.log(a1/eps)/(steps*hstep)
    rates.append(rate/(2*lam))
soft_r, stiff_r = rates
ok &= 0.999 < soft_r < 1.001
ok &= 0.998 < stiff_r < 1.001
print(f"  g3 rate/2lambda: soft {soft_r:.4f}, stiff {stiff_r:.4f}", flush=True)
gate("g3 the exact flow rates: off-line modes relax at 2 lambda_k under "
     "the nonlinear flow, both spectral edges", ok)

# ---------------------------------------------------------------- g4
trL = float(np.trace(L))
ok = abs(trL - 91.728) < 0.001
uu = np.linspace(1e-4, 60, 4000000)
R2 = 1 - (np.sin(np.pi*uu)/(np.pi*uu))**2
I_gue = float(2*np.trapezoid(R2/uu**2, uu))
ok &= abs(I_gue - 6.54575) < 5e-4      # the instrument's own band value
# round 207 F2: the unqualified integral has the closed form 2 pi^2/3
# = 6.579736; the committed instrument integrates the band u <= 60
# (tail 0.0333) -- cutoff disclosed, gated against the closed form
ok &= abs(I_gue - 2*np.pi**2/3) < 0.04
def mean_spacing(g):
    return 2*np.pi/np.log(g/(2*np.pi))
def trace_of(gs):
    Xg = np.concatenate([-gs[::-1], gs])
    return float(np.trace(build_L(Xg)))
rng = np.random.default_rng(1)
tp = []
for _ in range(200):
    gs = [gams[0]]
    for k in range(1, M):
        gs.append(gs[-1] + rng.exponential(mean_spacing(gams[k])))
    tp.append(trace_of(np.array(gs)))
ok &= np.median(tp) > 500
rng = np.random.default_rng(7)
N = 600
tg, l2g = [], []
for _ in range(200):
    A = rng.normal(size=(N, N)) + 1j*rng.normal(size=(N, N))
    Hm = (A + A.conj().T)/2
    evg = np.linalg.eigvalsh(Hm)
    c = evg[N//2 - M//2 - 1 : N//2 + M//2]
    s = np.diff(c); s = s/s.mean()
    gs = [gams[0]]
    for k in range(1, M):
        gs.append(gs[-1] + s[k-1]*mean_spacing(gams[k]))
    Xg = np.concatenate([-np.array(gs)[::-1], np.array(gs)])
    Lg = build_L(Xg)
    tg.append(float(np.trace(Lg)))
    l2g.append(float(np.linalg.eigvalsh(Lg)[1]))
tg = np.array(tg); l2g = np.array(l2g)
med_t = float(np.median(tg))
pct_t = float(100*np.mean(tg < trL))
pct_l2 = float(100*np.mean(l2g < lam2))
ok &= 110 < med_t < 140
ok &= 0.5 < pct_t < 4.0
ok &= 5 < pct_l2 < 25
print(f"  g4 tr L = {trL:.3f}; I_gue = {I_gue:.5f}; Poisson trace median "
      f"{np.median(tp):.0f}; GUE trace median {med_t:.1f}, arithmetic pct "
      f"{pct_t:.1f}%; lambda_2 pct {pct_l2:.1f}%", flush=True)
gate("g4 the curvature census: the finiteness dichotomy (GUE cancels, "
     "Poisson diverges), the trace below GUE, the rigidity's spectral "
     "address in the stiff modes", ok)

# ---------------------------------------------------------------- g5
gc, sig = 88.0, 25.0
phi = np.exp(-(gams100 - gc)**2/(2*sig**2))
om = np.arange(0.0005, 4.20, 0.001)
ZS = 2*(phi[None, :]*np.cos(np.outer(om, gams100))).sum(axis=1)
rg = np.linspace(-260, 260, 8001)
G = np.real(scipy_digamma(0.25 + 0.5j*rg)) - np.log(np.pi)
phir = np.exp(-(rg - gc)**2/(2*sig**2)) + np.exp(-(rg + gc)**2/(2*sig**2))
dr = rg[1] - rg[0]
ARCH = np.array([(phir*np.cos(w*rg)*G).sum()*dr/(2*np.pi) for w in om])
def h_at(z, w):
    p1 = np.exp(-(z - gc)**2/(2*sig**2)) + np.exp(-(z + gc)**2/(2*sig**2))
    return (p1*np.cos(w*z)).real*2
POLE = np.array([h_at(0.5j, w) for w in om])
def vonmangoldt(nmax):
    lamv = np.zeros(nmax + 1)
    for p in range(2, nmax + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            pk = p
            while pk <= nmax:
                lamv[pk] = np.log(p)
                pk *= p
    return lamv
NMAX = 200
lamv = vonmangoldt(NMAX)
ns = np.nonzero(lamv)[0]
def gfun(u, w):
    tot = 0.0
    for sgn in (1.0, -1.0):
        t = u - sgn*w
        tot += np.exp(-sig*sig*t*t/2)*np.cos(t*gc)
    return sig/np.sqrt(2*np.pi)*tot
def prime_side(w, y):
    tot = 0.0
    for nn in ns:
        if nn > y:
            continue
        tot += lamv[nn]/np.sqrt(nn)*gfun(np.log(nn), w)
    return -2*tot
PS_full = ARCH + POLE + np.array([prime_side(w, NMAX) for w in om])
devsel = om > 0.30
dev = np.abs(ZS - PS_full)[devsel]
ok = dev.max() < 1e-3
mins = argrelextrema(ZS, np.less, order=8)[0]
mins = [i for i in mins if om[i] > 0.4]
deep = sorted(mins, key=lambda i: ZS[i])[:10]
targets = sorted(nn for nn in ns if 0.4 < np.log(nn) < 4.1)
expect = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31}
found = set()
spike_devs = []
for i in deep:
    w = om[i]
    nbest = min(targets, key=lambda nn: abs(np.log(nn) - w))
    spike_devs.append(abs(np.log(nbest) - w))
    ok &= abs(np.log(nbest) - w) < 0.002
    found.add(int(nbest))
ok &= found == expect
# round 207 F1: the per-spike maximum gated at the display value (the
# landing's "within 0.001" read the session's 3-dp rounding as truth;
# the log 23 spike sits at 0.001006)
ok &= max(spike_devs) < 0.0011
B = 4.0
sel = om < B
X100 = np.concatenate([-gams100[::-1], gams100])
PH = np.concatenate([phi[::-1], phi])
D = X100[:, None] - X100[None, :]
np.fill_diagonal(D, 1.0)
KB = (1 - np.cos(B*D) - B*D*np.sin(B*D))/D**2
np.fill_diagonal(KB, 0.0)
C_pairs = float((PH[:, None]*PH[None, :]*KB).sum())
diag = 2*(phi**2).sum()
def curv_from(S):
    return float(-np.trapezoid(om[sel]*(S[sel]**2 - diag), om[sel]))
C_spec = curv_from(ZS)
ok &= abs(C_pairs - 28.832) < 0.001
ok &= abs(C_pairs - C_spec)/abs(C_pairs) < 1e-4
ladder = {}
for y in (1, 29, 53, 97):
    PSy = ARCH + POLE + np.array([prime_side(w, y) for w in om])
    ladder[y] = curv_from(PSy)
ok &= abs(ladder[1] - 294.24) < 0.01
ok &= abs(ladder[29] - 122.40) < 0.01
ok &= abs(ladder[97] - C_pairs)/abs(C_pairs) < 1e-4
ok &= ladder[53] < C_pairs          # the overshoot: NOT monotone convergence
print(f"  g5 rebuild max dev {dev.max():.1e}; spikes {sorted(found)}, per-spike max {max(spike_devs):.6f}; C_pairs "
      f"{C_pairs:.3f} = spec {C_spec:.3f} (rel {abs(C_pairs-C_spec)/C_pairs:.1e}); "
      f"ladder 1:{ladder[1]:.2f} 29:{ladder[29]:.2f} 53:{ladder[53]:.3f} "
      f"97:{ladder[97]:.3f}", flush=True)
gate("g5 the conversion: the explicit formula rebuilds S; the spikes are "
     "the primes; the Parseval identity; the fill ladder lands exactly with "
     "the y = 53 overshoot gated", ok)

# ---------------------------------------------------------------- g6
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES, g='g6')
for _d, _n in _miss:
    print(f"  g6 MISSING (count {_n}): {_d['s']!r}", flush=True)
gate("g6 the 1ay paper needles (declared surface)", ok)

# ---------------------------------------------------------------- g7
sys.path.insert(0, HERE)
from cascade_tower import chain_ok
gate("g7 the chain obligation to cascade_heatflow_energy.py (Theorem 1ax) met",
     chain_ok("cascade_heatflow_energy.py"))

# ---------------------------------------------------------------- g8
ok, _missC = paper_needles.verify(PAPER_NEEDLES, g='g8')
for _d, _n in _missC:
    print(f"  g8 MISSING (count {_n}): {_d['s']!r}", flush=True)
gate("g8 the footer census (this script backticked >= 2; 86 cited in place; "
     "the range 1i–1bj)", ok)

print(flush=True)
if fails:
    print(f"FAILURES ({len(fails)}):")
    for f in fails:
        print("  " + f)
    sys.exit(1)
print("ALL GATES PASS (8/8)")
