#!/usr/bin/env python3
"""Theorem 1bc verifier: the nulls and the fluctuation price -- what
the zeros' fluctuations buy and cost the dodging section, measured
against three nulls sharing one instrument (the zero-side margin at
delta = 4 on the certified 1bb section machinery -- basis, Gram,
dimensions; pole- and prime-free, distinct from 1bb's gated
Weil-side form: round-218 F4). The nulls:
  COMB -- the count-matched rigid comb at the Riemann density
     (gamma-tilde_k solving Nbar = k, maximal rigidity, zero
     fluctuation): the zeros BEAT it (the section dodges the true
     zeros more cheaply than the comb; fluctuations HELP dodging).
  CUE, count-conditioned -- unitary-ensemble synthetic zero sets
     unfolded to the Riemann density and ACCEPTED only when the
     in-band count equals the comb's (the count-conditioned design
     that removes the count artifact g4 calibrates): the zeros LOSE
     to it (generic fluctuations dodge cheaper still) -- the gap is
     the zeta-specific stiffness excess, the third instrument on the
     low-height rigidity anomaly (with the 1ax GUE-percentile and
     1ay curvature-census readings).
  CONCENTRATION -- the Landau--Widom counting model (exact Slepian
     out-of-band leakage interpolated at the smooth in-band count
     index, times the mean zero density -- the committed formula,
     round-218 F8; no arithmetic): the measured lift-off sits 40-58 above the model's
     at every bandwidth (round-218 F11), and the extrapolated edges
     land +36/+57 beyond it -- the horizon's location is counting;
     the excess over the model is SHARED by every discrete
     configuration measured (round-218 F3 struck the landing's
     "arithmetic rigidity beyond counting" attribution -- the comb
     exceeds the model by 96% of the zeros' excess); and the
     measured deep margins run DECADES BELOW the model (the
     epsilon-offset of 1bb g4 is concentration economics, not a
     hidden wall -- the 1bb block's deferred interpretation, closed).
The ordering, gated per point: COMB above zeta above CUE.

One committed instrument, exactly the session recipe: 380 verified
zeros (dps-13 pull); sections n = int(2c/pi) + 4, KL = int(1.4c) + 60,
Gram on GL-800; margins as generalized minimal eigenvalues of the
+-gamma zero-side quadratic form; grid c in {40, 60, 90, 120} x six-to
-eight heights (26 points); comb by Newton on Nbar; GUE sets by
semicircle-CDF unfolding of three seeded GUE(1400) bulks; CUE sets by
seeded 380x380 unitary_group spectra, uniform-density unfolded,
mean-anchored, count-conditioned by in-band acceptance (seed ladder
from 1000, 16 accepted per point, cap 400 tries).

Gates (all exit-gated; any failure exits 1):
  g1  the instrument: true-zero margins reproduce the session pins
      (1bc-session values of the zero-side form on the 1bb section
      machinery -- round-218 F4 struck "certified-era": the values
      appear on no certified surface; the certified 1bb margin is
      the Weil-side form, distinct) at c = 120 -- m(260) = 1.139e-7, m(300) = 3.760e-4,
      m(360) = 2.549e-1 (rel 1e-2); the zero pull (Z_1 = 14.1347 rel
      1e-4, 380 zeros to 653.6 rel 1e-3) and the count-matched comb
      (to 653.6 rel 1e-3) verified.
  g2  the comb null: R_zeta = log10(m_zeta/m_comb) < +0.10 at ALL 26
      grid points (one point, (90, 280), sits at +0.07; every other
      is negative); the c = 120 ladder pinned R(260) = -0.40 and
      R(360) = -0.58 (abs 0.06) and deepening by more than 0.10
      across it -- the zeros' fluctuations make dodging CHEAPER than
      maximal rigidity, increasingly so approaching lift-off.
  g3  the height trend: the linear fit R_zeta = b0 + b1*Z on in-band
      smooth count Z over the 26 points -- b1 in (-0.0080, -0.0035)
      (session -0.0056), rms residual < 0.28 (session 0.213): the
      discount grows with the number of levels in the band.
  g4  the count-sensitivity calibration (why conditioning is
      forced): the committed unfolding is MIS-SCALED (the ensemble's
      semicircle edge sits at sqrt(2) where the CDF assumes 1;
      round-218 F2 struck the landing's "+-1-2 level" narrative), so
      each GUE set carries ~735 levels on the 380-zero range --
      double density, in-band excess ~+65 levels at c = 120 driving
      the in-band count (134-154; round-220 F1) at or beyond the section
      dimension (80), so the margin saturates (round-219 F3) --
      R_gue(120, 260) > +5 (session +6.82)
      collapsing to |R_gue(120, 450)| < 0.3 (session -0.11);
      mean(R_zeta - R_gue) over the grid in (-4.3, -2.8) (session
      -3.557): the unconditioned comparison is count-artifact-
      dominated, which is what g5's conditioning removes.
  g5  the headline, count-conditioned: over the ten-point session
      grid (c = 60: 200/240/280/300; c = 120: 260/300/340/360/400/
      450), 16 accepted CUE sets per point (deterministic seed
      ladder), the per-point difference R_zeta - mean(R_cue) is
      POSITIVE at all ten points and its mean is
      +0.710 (|mean - 0.710| < 0.05; s.e. in (0.04, 0.14); session
      +0.710 +- 0.086, reproduced exactly across a container
      restore) -- the zeros are STIFFER than count-matched generic
      fluctuations by a factor ~5 in margin ON AVERAGE (per-point
      factors 1.4-13.4; positivity is the at-every-point claim --
      round-218 F10).
  g6  the ordering: at all ten conditioned points R_zeta < 0 <
      R_zeta - mean(R_cue): COMB above zeta above CUE -- rigidity
      ordering comb > zeta > CUE with zeta strictly between.
  g7  the pure-concentration null: the exact-Slepian LW model's
      lift-off crossings tau*(1e-3, c) = 174.55/212.47/245.15/265.01
      (abs 1.5) for c = 40/60/90/120, its 1/c extrapolation
      tau_inf(1e-3) in (303, 310) (session 306.30) and tau_inf(1e-6)
      in (260, 267) (session 263.52); the excesses of the CERTIFIED
      1bb measured edges over the model, tau_inf(meas) - tau_inf
      (model): 1e-3 in (+32, +41) (session +36.2) and 1e-6 in
      (+51, +62) (session +56.5); pointwise at c = 120, tau0 = 260..
      340: log10(m_measured/m_model) all NEGATIVE and strictly
      increasing (session -3.69 -> -0.63, abs 0.35/0.20 at the
      ends; round-218 F7 corrected the mis-transcribed -3.66): dodging BEATS pure concentration everywhere below
      lift-off, by less as the boundary nears.
  g8  the paper needles for the 1bc block (in-code list
      authoritative).
  g9  the chain obligation to cascade_prolate_horizon.py (Theorem
      1bb) met (full mode: parent executed, exit 0; manifest mode:
      ancestor hashes + census attested).
  g10 the footer census (this script backticked >= 2; the anchored
      needles "the **86 scripts cited in place** above" and
      "extended by Theorems 1i–1bj:").

Near-boundary caution (round-210 F1 standing): margins are pinned by
magnitude windows only; no balance decompositions are gated here.

Sabotage record (parallel-isolation design under MANIFEST chain mode:
baseline + four probes as five INDEPENDENT tar trees from committed
HEAD 847b711, each mangle's application verified by assert + cmp
against the committed copy before launch; the first suite attempt was
killed by container restart #12 at g5 with all trees tracking
identically; the record below is the completed relaunch; censuses are
the OBSERVED results):
  (a) title needle mangled in-span single-site in the paper
      -> OBSERVED: g8 FAIL alone (exit 1)
  (b) the headline pin shifted past truth in code (0.710 -> 0.810 at
      window +-0.05) -> OBSERVED: g5 FAIL alone (exit 1)
  (c) the excess window shifted past truth in code ((32, 41) ->
      (42, 51) against observed +36.24) -> OBSERVED: g7 FAIL alone
      (exit 1)
  (d) footer census reverted 79 -> 78 in the paper -> OBSERVED: g10
      FAIL AND g9 FAIL (the chain gate's manifest census check printed
      "paper lacks 'the **79 scripts cited in place** above'" -- the
      two-gate detection at the advanced census, the anchored needles'
      first sabotage-probe exercise since their tower-wide adoption)
      [the printed "79" is the FROZEN OBSERVED output of that
      historical probe (restored round 252 from the landing
      commit e2fff87 -- mechanical census sweeps had advanced a
      recorded observation); census sweeps must not touch it]
"""
import json, sys, os, math
import numpy as np
from numpy.polynomial import legendre as L
from scipy.special import spherical_jn
from scipy.linalg import eigh as scipy_eigh
from scipy.stats import unitary_group

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from zeta_zeros_cache import zeros_im

# declared paper surface (the needle-precheck arc, A397): the
# member touches the paper ONLY through these entries.
PAPER_NEEDLES = [
    {'g': 'g8', 's': '**Theorem 1bc (the nulls and the fluctuation price'},
    {'g': 'g8', 's': 'the count-matched rigid comb'},
    {'g': 'g8', 's': 'fluctuations make dodging cheaper'},
    {'g': 'g8', 's': 'count-conditioned CUE'},
    {'g': 'g8', 's': 'the zeta stiffness excess'},
    {'g': 'g8', 's': 'positive at every point'},
    {'g': 'g8', 's': 'comb above zeta above CUE'},
    {'g': 'g8', 's': 'the count-sensitivity calibration'},
    {'g': 'g8', 's': 'the pure-concentration null'},
    {'g': 'g8', 's': 'an excess shared by every discrete configuration measured'},
    {'g': 'g8', 's': 'concentration economics, not a hidden wall'},
    {'g': 'g8', 's': 'the third instrument on the low-height rigidity anomaly'},
    {'g': 'g10', 's': '`cascade_fluctuation_price.py`', 'min': 2},
    {'g': 'g10', 's': 'the **86 scripts cited in place** above'},
    {'g': 'g10', 's': 'extended by Theorems 1i–1bj:'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

TWO_PI = 2*math.pi
DELTA = 4.0
A = DELTA/2.0
HORIZON = TWO_PI*math.exp(DELTA)

def make_basis(c, n, KL):
    k = np.arange(KL)
    alpha = (k + 1)/np.sqrt((2*k + 1)*(2*k + 3))
    Tx = np.zeros((KL, KL))
    for i in range(KL - 1):
        Tx[i, i+1] = Tx[i+1, i] = alpha[i]
    Lm = -np.diag(k*(k + 1.0)) - c*c*(Tx @ Tx)
    ev, V = scipy_eigh(Lm)
    return V[:, np.argsort(-ev)[:n]].T

def psi_eval(coefs, x):
    KL = coefs.shape[1]
    out = np.zeros((coefs.shape[0], len(x)))
    for n in range(coefs.shape[0]):
        out[n] = L.legval(x, coefs[n]*np.sqrt(np.arange(KL) + 0.5))
    return out

def psi_hat(coefs, s):
    KL = coefs.shape[1]
    s = np.atleast_1d(s).astype(float)
    ks = np.arange(KL)
    # one broadcast call replaces the per-order loop (round 252
    # pace retrofit; bitwise-identical per (n, z) pair)
    J = spherical_jn(ks[:, None], np.abs(s)[None, :])
    sign = np.where(s[None, :] >= 0, 1.0, (-1.0)**(ks[:, None]))
    ph = (1j**ks)*np.sqrt(ks + 0.5)
    return (coefs.astype(complex)*ph[None, :]) @ (2*sign*J)

def Nbar(x):
    return x/TWO_PI*(np.log(x/TWO_PI) - 1) + 7.0/8

def inv_Nbar(t, g0=20.0):
    g = g0
    for _ in range(80):
        g -= (Nbar(g) - t)/(np.log(g/TWO_PI)/TWO_PI)
    return g

class Sect:
    def __init__(self, c):
        self.c = c
        self.n = int(2*c/math.pi) + 4
        KL = int(1.4*c) + 60
        self.P = make_basis(c, self.n, KL)
        xg, wg = np.polynomial.legendre.leggauss(800)
        PX = psi_eval(self.P, xg)
        self.G = A*np.einsum('ni,i,mi->nm', PX, wg, PX)

    def margin(self, zeros, tau0):
        s = np.concatenate([(zeros - tau0)*A, (-zeros - tau0)*A])
        V = psi_hat(self.P, s)*A
        Q = V @ V.conj().T
        Q = (Q + Q.conj().T)/2
        return scipy_eigh(Q, self.G, eigvals_only=True)[0]

# ---- the shared data: zeros, comb, GUE sets ------------------------
# round-252 pace retrofit: the zeros through the shared live-
# anchored cache; inv_Nbar call sites vectorized (the Newton
# iteration is elementwise, so the vector path is bitwise-
# identical to the scalar loop -- verified); RNG draw order
# untouched everywhere, so every seeded ensemble reproduces
# its recorded values exactly
Z = np.array(zeros_im(380, 13))
NZ = len(Z)
comb = inv_Nbar(np.arange(1, NZ + 1).astype(float))

def gue_set(seed):
    rng = np.random.default_rng(seed)
    NG = 1400
    H = rng.standard_normal((NG, NG)) + 1j*rng.standard_normal((NG, NG))
    H = (H + H.conj().T)/2
    ev = np.linalg.eigvalsh(H)
    R_ = math.sqrt(2*NG)
    x = ev/R_
    keep = np.abs(x) < 0.6
    xb = np.sort(x[keep])
    cdf = NG*(0.5 + (xb*np.sqrt(1 - xb**2) + np.arcsin(xb))/math.pi)
    u = cdf - cdf[0]
    u = u/(u[-1])*(NZ - 1)
    return inv_Nbar(1.0 + u)

GUES = [gue_set(s) for s in (11, 23, 47)]

def cue_set(seed):
    rng = np.random.default_rng(seed)
    U = unitary_group.rvs(NZ, random_state=rng)
    th = np.sort(np.angle(np.linalg.eigvals(U)))
    t = (th + math.pi)/TWO_PI*NZ
    t = t - t.mean() + (NZ + 1)/2
    return inv_Nbar(np.maximum(np.sort(t), 0.6))

# margin-state checkpoint (round-252 pace retrofit): the
# expensive computed STATE (m120, the 26-point grid rows, the
# ten conditioned points) is byte-keyed on this file -- any
# edit rotates the key; the GATES always run, on loaded or
# fresh state alike (the floor_theory phase pattern; the
# oneprime F248-5 lesson: gates must not sit behind the
# early-return)
_SELF = os.path.abspath(__file__)
_MPAR = {"stage": "margins"}
_MST = ckpt_key.load("flucprice_margins", _SELF, _MPAR)

# ---------------------------------------------------------------- g1
ok = abs(Z[0]/14.134725 - 1) < 1e-4
ok &= abs(Z[-1]/653.6 - 1) < 1e-3
ok &= abs(comb[-1]/653.6 - 1) < 1e-3
S120 = None
if _MST is None:
    S120 = Sect(120.0)
    m120 = {t0: S120.margin(Z, float(t0))
            for t0 in (260, 280, 300, 320, 340, 360)}
else:
    m120 = {int(k): float(v) for k, v in _MST["m120"].items()}
ok &= abs(m120[260]/1.139e-7 - 1) < 1e-2
ok &= abs(m120[300]/3.760e-4 - 1) < 1e-2
ok &= abs(m120[360]/2.549e-1 - 1) < 1e-2
print(f"  g1 zeros {Z[0]:.4f}..{Z[-1]:.1f}; comb to {comb[-1]:.1f}; "
      f"m120(260/300/360) {m120[260]:.3e}/{m120[300]:.3e}/{m120[360]:.3e}",
      flush=True)
gate("g1 the instrument: the session pins reproduce on the committed "
     "section (1bb machinery, zero-side form)", ok)

# ---------------------------------------------------------------- g2, g3, g4
GRID = {40.0: [160, 180, 200, 220, 240, 260],
        60.0: [200, 220, 240, 260, 280, 300],
        90.0: [240, 260, 280, 300, 320, 340],
        120.0: [260, 280, 300, 320, 340, 360, 400, 450]}
SECTS = {}
if _MST is None:
    rows = []
    for c, taus in GRID.items():
        S = SECTS.setdefault(c, S120 if c == 120.0 else Sect(c))
        W = c/A
        for t0 in taus:
            Zb = Nbar(t0 + W) - Nbar(max(t0 - W, 15))
            mz = m120[t0] if (c == 120.0 and t0 in m120) else S.margin(Z, float(t0))
            mc = S.margin(comb, float(t0))
            mg = [S.margin(gz, float(t0)) for gz in GUES]
            Rz = math.log10(mz/mc)
            Rg = [math.log10(m/mc) for m in mg]
            rows.append((c, t0, Zb, Rz, float(np.mean(Rg))))
    rows = np.array(rows)
else:
    rows = np.array(_MST["rows"])
rz_all = rows[:, 3]
lad = {int(t0): r for c, t0, _, r, _ in rows if c == 120.0}
ok = bool(np.all(rz_all < 0.10))
ok &= abs(lad[260] - (-0.40)) < 0.06
ok &= abs(lad[360] - (-0.58)) < 0.06
ok &= lad[360] < lad[260] - 0.10
print(f"  g2 max R_zeta {rz_all.max():+.2f} (grid of {len(rows)}); "
      f"c120 ladder R(260) {lad[260]:+.2f} -> R(360) {lad[360]:+.2f}",
      flush=True)
gate("g2 the comb null: the true zeros dodge cheaper than maximal "
     "rigidity, deepening along the ladder", ok)

zc = rows[:, 2]
A1 = np.vstack([np.ones(len(zc)), zc]).T
(b0, b1), *_ = np.linalg.lstsq(A1, rz_all, rcond=None)
rms = float(np.sqrt(np.mean((rz_all - (b0 + b1*zc))**2)))
ok = -0.0080 < b1 < -0.0035 and rms < 0.28
print(f"  g3 fit R_zeta = {b0:+.3f} + ({b1:+.4f})*Z; rms {rms:.3f}",
      flush=True)
gate("g3 the height trend: the comb discount grows with the in-band "
     "count", ok)

rg_all = rows[:, 4]
rg120 = {int(t0): g for c, t0, _, _, g in rows if c == 120.0}
dz = float(np.mean(rz_all - rg_all))
ok = rg120[260] > 5.0
ok &= abs(rg120[450]) < 0.3
ok &= -4.3 < dz < -2.8
print(f"  g4 R_gue(120,260) {rg120[260]:+.2f} -> R_gue(120,450) "
      f"{rg120[450]:+.2f}; mean(R_zeta - R_gue) {dz:+.3f}", flush=True)
gate("g4 the count-sensitivity calibration: unconditioned unfolding "
     "pays decades per level; conditioning is forced", ok)

# ---------------------------------------------------------------- g5, g6
CGRID = {60.0: [200, 240, 280, 300], 120.0: [260, 300, 340, 360, 400, 450]}
NSEED = 16
if _MST is not None:
    pts = [(bool(f), float(rz), float(rq))
           for f, rz, rq in _MST["pts"]]
else:
    # per-point partial (round-252: the acceptance loop is the
    # member's long pole -- a restart resumes from the last
    # completed point; the deterministic seed ladder restarts
    # per point, so a resumed point reproduces exactly)
    _pj = os.path.join(
        HERE, "checkpoints",
        f"flucprice_partial_"
        f"{ckpt_key.key(_SELF, _MPAR)[:12]}.json")
    _part = {}
    try:
        _part = json.load(open(_pj))["state"]
        print(f"  g5 partial: {len(_part)} points", flush=True)
    except Exception:
        pass
    pts = []
    for c, taus in CGRID.items():
        S = SECTS[c]
        W = c/A
        for t0 in taus:
            pk = f"{c:.0f}:{t0}"
            if pk in _part:
                pts.append(tuple(_part[pk]))
                continue
            cnt_c = int(sum(1 for g in comb if t0 - W < g < t0 + W))
            acc, tried, seed = [], 0, 1000
            while len(acc) < NSEED and tried < 400:
                q = cue_set(seed); seed += 1; tried += 1
                if int(sum(1 for g in q if t0 - W < g < t0 + W)) == cnt_c:
                    acc.append(S.margin(q, float(t0)))
            mz = S.margin(Z, float(t0))
            mc = S.margin(comb, float(t0))
            full = len(acc) == NSEED and min([mz, mc] + acc) > 1e-12
            Rz = math.log10(mz/mc) if full else float("nan")
            Rq = float(np.mean([math.log10(m/mc) for m in acc])) if full else float("nan")
            pts.append((full, Rz, Rq))
            _part[pk] = [bool(full), float(Rz), float(Rq)]
            json.dump({"key": ckpt_key.key(_SELF, _MPAR),
                       "state": _part}, open(_pj, "w"))
            print(f"  g5 c {c:.0f} tau0 {t0}: cnt {cnt_c}, acc {len(acc)}/{tried}; "
                  f"R_zeta {Rz:+.3f}; R_cue {Rq:+.3f}", flush=True)
    ckpt_key.save("flucprice_margins", _SELF, _MPAR,
                  {"m120": {str(k): float(v)
                            for k, v in m120.items()},
                   "rows": np.asarray(rows).tolist(),
                   "pts": [[bool(f), float(rz), float(rq)]
                           for f, rz, rq in pts]})
    if os.path.exists(_pj):
        os.remove(_pj)
diffs = np.array([Rz - Rq for full, Rz, Rq in pts])
mean_d = float(np.mean(diffs))
se_d = float(np.std(diffs)/math.sqrt(len(diffs)))
ok = all(full for full, _, _ in pts) and len(pts) == 10
ok &= bool(np.all(diffs > 0))
ok &= abs(mean_d - 0.710) < 0.05
ok &= 0.04 < se_d < 0.14
print(f"  g5 mean(R_zeta - R_cue_conditioned) = {mean_d:+.3f} +- {se_d:.3f} "
      f"over {len(diffs)} points", flush=True)
gate("g5 the headline: the zeta stiffness excess over count-conditioned "
     "CUE, positive at every point", ok)

ok = all(full and Rz < 0 for full, Rz, _ in pts)
ok &= bool(np.all(diffs > 0))
gate("g6 the ordering: comb above zeta above CUE at all ten conditioned "
     "points", ok)

# ---------------------------------------------------------------- g7
def one_minus_lambda(c, NB):
    KL = int(1.4*c) + 60
    P = make_basis(c, NB, KL)
    out = np.zeros(NB)
    OMAX = 60*c
    edges = [c]
    while edges[-1] < OMAX:
        edges.append(min(edges[-1]*1.5, OMAX))
    xg, wg = np.polynomial.legendre.leggauss(240)
    for lo, hi in zip(edges[:-1], edges[1:]):
        om = (hi + lo)/2 + (hi - lo)/2*xg
        ww = (hi - lo)/2*wg
        FH = psi_hat(P, om)
        out += 2*np.einsum('ni,i->n', np.abs(FH)**2, ww)/TWO_PI
    Pv = np.zeros(NB)
    for n in range(NB):
        Pv[n] = L.legval(1.0, P[n]*np.sqrt(np.arange(KL) + 0.5))
    out += 2*(2*Pv)**2*0.5/OMAX/TWO_PI
    return out

def Zcount(tau0, W):
    f = lambda r: (r*math.log(r/TWO_PI) - r)/TWO_PI
    return f(tau0 + W) - f(max(tau0 - W, TWO_PI*1.0001))

def model_logm(c):
    W = c/A
    NB = int(2*c/math.pi) + 40
    oml = one_minus_lambda(c, NB)
    log_oml = np.log10(np.maximum(oml, 1e-300))
    def lm(tau0):
        Zb = Zcount(tau0, W)
        if Zb < 0:
            Zb = 0.0
        i = min(int(Zb), NB - 2)
        f = Zb - i
        lg = log_oml[i]*(1 - f) + log_oml[i + 1]*f
        return lg + math.log10(math.log(tau0/TWO_PI)/TWO_PI)
    return lm

def tau_star(lm, eps, lo=60.0, hi=500.0):
    tgt = math.log10(eps)
    if lm(lo) - tgt > 0 or lm(hi) - tgt < 0:
        return float("nan")
    for _ in range(60):
        mid = (lo + hi)/2
        if lm(mid) - tgt < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi)/2

mod_star = {}
MODELS = {}
for c in (40.0, 60.0, 90.0, 120.0):
    lm = model_logm(c)
    MODELS[c] = lm
    mod_star[c] = {eps: tau_star(lm, eps) for eps in (1e-3, 1e-6)}
pins3 = {40.0: 174.55, 60.0: 212.47, 90.0: 245.15, 120.0: 265.01}
ok = all(abs(mod_star[c][1e-3] - pins3[c]) < 1.5 for c in pins3)

def fit_tinf(cross):
    cs = np.array([40.0, 60.0, 90.0, 120.0])
    ys = np.array([cross[c] for c in cs])
    M = np.column_stack([np.ones(4), -1.0/cs])
    (tinf, K), *_ = np.linalg.lstsq(M, ys, rcond=None)
    return float(tinf)

mod_t3 = fit_tinf({c: mod_star[c][1e-3] for c in pins3})
mod_t6 = fit_tinf({c: mod_star[c][1e-6] for c in pins3})
MEAS3 = {40.0: 222.69, 60.0: 258.50, 90.0: 285.53, 120.0: 305.79}
MEAS6 = {40.0: 158.87, 60.0: 205.15, 90.0: 243.80, 120.0: 270.60}
meas_t3 = fit_tinf(MEAS3)
meas_t6 = fit_tinf(MEAS6)
ex3 = meas_t3 - mod_t3
ex6 = meas_t6 - mod_t6
ok &= 303 < mod_t3 < 310 and 260 < mod_t6 < 267
ok &= 32 < ex3 < 41 and 51 < ex6 < 62
lm120 = MODELS[120.0]
ratios = [math.log10(m120[t0]) - lm120(float(t0))
          for t0 in (260, 280, 300, 320, 340)]
ok &= all(r < 0 for r in ratios)
ok &= all(ratios[i] < ratios[i + 1] for i in range(len(ratios) - 1))
ok &= abs(ratios[0] - (-3.69)) < 0.35
ok &= abs(ratios[-1] - (-0.63)) < 0.20
print(f"  g7 model tau*(1e-3): " +
      "/".join(f"{mod_star[c][1e-3]:.2f}" for c in (40.0, 60.0, 90.0, 120.0)) +
      f"; model tau_inf {mod_t3:.2f}/{mod_t6:.2f}; excess {ex3:+.2f}/{ex6:+.2f}; "
      f"c120 log10(meas/model) {ratios[0]:+.2f}..{ratios[-1]:+.2f}",
      flush=True)
gate("g7 the pure-concentration null: the certified edges sit far beyond "
     "counting, and dodging beats concentration below lift-off", ok)

# ---------------------------------------------------------------- g8
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES, g='g8')
for _d, _n in _miss:
    print(f"  g8 MISSING (count {_n}): {_d['s']!r}", flush=True)
gate("g8 the 1bc paper needles (declared surface)", ok)

# ---------------------------------------------------------------- g9
sys.path.insert(0, HERE)
from cascade_tower import chain_ok
gate("g9 the chain obligation to cascade_prolate_horizon.py (Theorem 1bb) "
     "met", chain_ok("cascade_prolate_horizon.py"))

# ---------------------------------------------------------------- g10
ok, _missC = paper_needles.verify(PAPER_NEEDLES, g='g10')
for _d, _n in _missC:
    print(f"  g10 MISSING (count {_n}): {_d['s']!r}", flush=True)
gate("g10 the footer census (this script backticked >= 2; the anchored "
     "count and range needles)", ok)

print(("\nALL GATES PASS (10/10)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
