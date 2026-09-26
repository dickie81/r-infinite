#!/usr/bin/env python3
"""The height-uniformity arc, first instrument (commissioned after
the 1bg certification, A363): scan the critical window through
exponentially growing heights by the APERTURE DIAL.

The structure that makes height uniformity measurable: at fixed
aperture A the high heights are deeper into saturation (the count
only grows), so the hair-thin regime -- where positivity is
informative and fragile -- is the crossing band at

    tau*(A) = 2pi e^(2A)     (derived at A = 2 by Poisson
                              summation; an OUT-OF-SAMPLE
                              PREDICTION at every other A)

one band per aperture: A = 1.5 -> 126, 2 -> 343 (the certified
regime), 2.5 -> 933, 3 -> 2536. Scanning A scans the critical
window through all heights. This instrument measures, per A:
  - the crossing ladder m(tau0) through tau*(A) (c = 120, one
    Slepian basis for all A -- the basis is A-free; only the
    s-scaling s = A(gamma - tau0) and the two convention factors
    carry the aperture);
  - the lift-off height vs the tau* prediction;
  - the deep (crossing) margin m*(A) -- the race curve's first
    axis: the floor's typical scale at the critical window vs
    height;
  - the tight-mean control Q(top) vs ln(tau0/2pi), predicted
    APERTURE-INDEPENDENT (the A factors cancel: v carries A, the
    G-norm carries 1/A, the s-density carries 1/A);
  - band count and min-gap diagnostics (feature-locality carries
    over from the saturation attack).

Honest scope: zero-side margins only in this phase (the 1bg
closure equates them with the arithmetic side at A = 2, matched
horizons, 2-3e-5; whether the closure holds at other apertures is
Phase 2 -- the prime cutoff e^(2A) moves with A and the prime
machinery is not yet generalized). Ordinates by mpmath zetazero,
extended per rung (chunked, resumable, content-keyed on (lo, hi,
dps) as pure constants per the floor_probe4 precedent). No RH
leverage claimed: this is positivity VERIFICATION moved through
heights by an instrument dial, plus the measured race curve --
the uniformity question itself stays a theorem question.

Check 7: Slepian sections, Poisson summation, mpmath ordinates --
classical. Check 8: no hypothesis input. Keying per the standing
law (A361): every ladder keyed on the producing modules' shas,
the full config, and the ordinate CONTENT (z_sha).

RESULT (both ladder sets complete; the first run's tau*-straddling
design missed the high-A climbs -- the climb width stretches as
tau0*A/(2c) per zero -- and was replaced by the deficit ladders,
both runs on the record):

  (1) THE tau* LAW HOLDS OUT-OF-SAMPLE ACROSS A FACTOR ~20 IN
      HEIGHT: lift-off tracks tau*(A) = 2pi e^(2A) at every rung
      (A = 1.5: the climb straddles 126.2 exactly, numerical zero
      below 100, 1.5e-7 by 130; A = 2.5 and 3.0: the
      deficit-parameterized calendar anchored at tau* lands every
      point on the predicted climb). The formula, derived at
      A = 2, is verified at 127, 343, 933, 2535.
  (2) THE TIGHT MEAN IS APERTURE-INDEPENDENT: Q(top) =
      ln(tau0/2pi) at every rung (rel <= 0.11% at A = 1.5, <= 2%
      at 2.5, <= 3.7% at 3.0 -- the scatter grows as the gamma-band
      narrows and Q(top) becomes feature-local, consistent with
      the saturation attack).
  (3) THE FLOOR LAW IS HEIGHT-UNIFORM OVER THE MEASURED SPAN --
      the arc's headline. At matched count deficit the climb
      slope is the same at every aperture (beta = 1.14 / 1.38 /
      1.31 / 1.30 decades per zero at A = 1.5/2/2.5/3 -- a
      drafting-run fit under an uncommitted recipe, superseded by
      the landing's declared-recipe gated values 1.0916 / 1.3122 /
      1.3721 / 1.2048; round-238 F11a), and the deep-margin scale at matched
      deficit is height-STABLE for A >= 2: at d ~ 5.4, m =
      1.14e-7 / 1.10e-7 / 6.5e-8 at heights 260 / 630 / 1580 --
      within 2x across a 6x height span; at d ~ 8.4, 8.1e-11 /
      9.7e-11 at heights 550 / 1350. THE RACE CURVE IS FLAT SO
      FAR: the critical window's positivity information does not
      degrade with height over the measured factor ~20.
  (4) THE LOW-HEIGHT ANOMALY (open): the A = 1.5 rung sits 4-5
      decades BELOW the uniform scale at matched deficit
      (d ~ 4.4: 4.7e-11 vs 1.8e-5/2.6e-5 at A = 2.5/3). Candidate
      mechanism: mirror proximity -- at tau0 ~ 110-130 the
      reflected ordinates sit only ~66 s-units beyond the band
      edge (vs ~400+ at A >= 2), adding effective constraints the
      band count does not see; low-height spacing statistics are
      the alternative. [RESOLVED at the anomaly attack,
      height_anomaly.py: BOTH hypotheses refuted -- mirrors can
      only raise margins (PSD), and the smooth-counting comb with
      no fluctuations reproduces the anomaly while the
      constant-density comb sits 7-9 decades higher. The cause is
      the deterministic density gradient: at A = 1.5 the local
      Nyquist line sits inside the band and the crossing smears.
      A computable geometry correction; the uniformity claim in
      (3) stands without a height-effect exception.]

Honest scope: c = 120 only; four apertures; heights <= 2780;
zero-side margins (Phase 2 owed: the arithmetic side at A != 2 --
the prime cutoff e^(2A) moves with the dial and the 1bg closure
is verified only at A = 2); the deep-margin statistic is
ladder-sampled, not an extreme-value census; no RH leverage
claimed -- this is the uniformity STRUCTURE measured, not a
uniform theorem. The race's second axis (the detection budget vs
height) is unmeasured.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from numpy.polynomial import legendre as L
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
from fold_D import zeros380
from fold_surrogate import make_basis, psi_hat_batch


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPSH = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "height_uniformity.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")


def _zsha(a):
    return hashlib.sha256(
        np.ascontiguousarray(a).tobytes()).hexdigest()[:16]


C0 = 120.0
# per rung: aperture A', tau0 ladder, max zetazero index needed.
# SECOND LADDER SET (the first run's tau*-straddling design missed
# the high-A climbs entirely -- the climb WIDTH in tau0 stretches
# as tau0*A/(2c) per zero, so at A = 3 the climb spans ~1350-2450,
# far below tau*; these ladders are DEFICIT-parameterized,
# tau0(d) = 2pi exp(2A - d*pi*A/c), sampling matched count
# deficits d ~ 8..0 at every aperture -- also the race curve's
# honest axis):
RUNGS = [
    (1.5, [90.0 + 10.0*i for i in range(13)]
          + [112.0, 116.5], 380),                       # tau* 126.2
    (2.0, [260.0 + 10.0*i for i in range(15)], 380),    # tau* 343.1
    (2.5, [550.0, 630.0, 715.0, 770.0, 825.0, 880.0, 910.0]
          + [850.0 + 20.0*i for i in range(11)], 810),  # tau* 932.6
    (3.0, [1350.0, 1580.0, 1850.0, 2000.0, 2170.0, 2340.0, 2440.0]
          + [2400.0 + 40.0*i for i in range(9)], 2270), # tau* 2535.9
]
EXT_CHUNK = 50
DPS = 15


class ASect:
    """c-parameterized Slepian section with a variable aperture:
    the basis is A-free; A enters only via s = A(gamma - tau0),
    the v-normalization (factor A), and the Gram convention
    (G = A * gram), mirroring fold_surrogate.Sect at A = 2."""
    def __init__(self, c):
        self.c = c
        self.n = int(2*c/math.pi) + 4
        KL = int(1.4*c) + 60
        self.P = make_basis(c, self.n, KL)
        xg, wg = np.polynomial.legendre.leggauss(800)
        PX = np.zeros((self.n, len(xg)))
        for m in range(self.n):
            PX[m] = L.legval(xg, self.P[m]*np.sqrt(np.arange(KL) + 0.5))
        self.gram = np.einsum('ni,i,mi->nm', PX, wg, PX)

    def measures(self, Z, tau0, Ap):
        G = Ap*self.gram
        s = np.concatenate([(Z - tau0)*Ap, (-Z - tau0)*Ap])
        V = psi_hat_batch(self.P, s)*Ap
        Q = V @ V.conj().T
        Q = (Q + Q.conj().T)/2
        m = float(scipy_eigh(Q, G, eigvals_only=True)[0])
        w = np.zeros(self.n)
        w[0] = 1.0/math.sqrt(G[0, 0])
        qtop = float(np.real(w @ Q @ w))
        inband = np.abs(s) <= self.c
        zb = Z[(Z > tau0 - self.c/Ap) & (Z < tau0 + self.c/Ap)]
        g = np.diff(zb) if len(zb) > 1 else np.array([0.0])
        return {"m": m, "qtop": qtop, "nb": int(np.sum(inband)),
                "min_gap": float(g.min()), "zb": int(len(zb))}


def ext_zeros_to(kmax):
    """Ordinates 381..kmax via mpmath, chunked + resumable; pure
    constants keyed on (lo, hi, dps) per the floor_probe4
    precedent (disclosed deviation from file-sha keying)."""
    if kmax <= 380:
        return np.array([])
    from mpmath import mp, zetazero
    mp.dps = DPS
    gams = []
    for lo in range(381, kmax + 1, EXT_CHUNK):
        hi = min(lo + EXT_CHUNK - 1, kmax)
        params = {"fn": "mpmath.zetazero.imag",
                  "lo": lo, "hi": hi, "dps": DPS}
        name = f"zext2_{lo}_{hi}"
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            st = [float(zetazero(k).imag) for k in range(lo, hi + 1)]
            ckpt_key.save(name, KEYFILE, params, st)
            print(f"  zext2 {lo}-{hi}: gamma {st[0]:.1f}..{st[-1]:.1f}",
                  flush=True)
        gams.extend(st)
    return np.array(gams)


def run():
    Z380 = zeros380()
    S = ASect(C0)
    for Ap, t0s, kmax in RUNGS:
        ZE = ext_zeros_to(kmax)
        Z = np.concatenate([Z380, ZE]) if len(ZE) else Z380
        tstar = 2*math.pi*math.exp(2*Ap)
        params = {"deps": DEPSH, "A": Ap, "c": C0, "t0s": t0s,
                  "kmax": kmax, "z_sha": _zsha(Z)}
        name = f"height_A{Ap:.1f}".replace(".", "p")
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            rows = []
            for t0 in t0s:
                r = S.measures(Z, t0, Ap)
                r["t0"] = t0
                rows.append(r)
            st = {"A": Ap, "tstar": tstar, "rows": rows}
            ckpt_key.save(name, KEYFILE, params, st)
        rows = st["rows"]
        # lift-off: first t0 with m > 1e-12
        lift = next((r["t0"] for r in rows if r["m"] > 1e-12), None)
        deep = [r for r in rows if 1e-12 < r["m"] < 1e-2]
        mstar = min((r["m"] for r in deep), default=None)
        print(f"== A={Ap:.1f} tau*={tstar:7.1f}: lift-off "
              f"{lift if lift else 'none-in-ladder'} | m* "
              f"{'%.2e' % mstar if mstar else 'n/a'} "
              f"({len(deep)} deep pts)", flush=True)
        for r in rows:
            Lt = math.log(r["t0"]/(2*math.pi))
            print(f"   t0={r['t0']:7.1f}: m {r['m']:+.3e} nb {r['nb']:3d} "
                  f"Qtop {r['qtop']:.3f} (L {Lt:.3f}, rel "
                  f"{r['qtop']/Lt - 1:+.4f}) ming {r['min_gap']:.3f}",
                  flush=True)


if __name__ == "__main__":
    run()
    print("height ladders complete", flush=True)
