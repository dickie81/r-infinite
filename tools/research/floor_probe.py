#!/usr/bin/env python3
"""The floor attack (commissioned after the 1bf certification, A358):
map the section floor -- m_Z(c, tau0), the truncated zero-side
dodging margin, and m_W(c, tau0), the arithmetic Weil margin -- on
tau0 ladders at c = 60 and 120; decompose both minimizers in the
prolate basis against the Slepian spectrum; and measure what sets
the floor and the certified g4 proximity ((m_W - m_Z)/m_Z in
(0, 0.10) at the four 1bf points, across seven decades of margin).

The three questions (the leverage assessment, A352/A358):
  (1) THE FLOOR LAW -- what sets m_Z's scale? Candidate: the
      Shannon-number bookkeeping (in-band zero count vs the
      section's concentrated degrees of freedom, N_sh ~ 2c/pi),
      with the floor riding the Slepian plunge (Landau-Widom
      width ~ log c). Diagnostics per point: the minimizer's
      prolate-coefficient spectrum against the Slepian leakage
      curve, the in-band zero counts at |u| <= c and c/2, n, N_sh.
  (2) THE PROXIMITY -- why is m_W only 2-10% above m_Z? The tail
      form T = Q_W - Q_Z,380 is O(1) on the generic dodger
      (tail(w_Z) = 3.12 at (60,200), certified 1bf g5) yet tiny at
      the Weil minimizer: the double dodge. Diagnostics: T's
      generalized spectrum on the section (bottom three, top one),
      T evaluated at both minimizers, and T compressed to the
      bottom-BOTK eigenspace of Q_Z (does the dodging-optimal
      subspace contain a T-null direction?).
  (3) THE TRANSFER TARGET -- min_w (A+B)(w) >= min A + min B gives
      m_W >= m_Z + lambda_min(T) unconditionally on the section;
      T positive-semidefinite on the section would make the
      measured ordering m_W > m_Z an inequality, and T's negative
      part is the section's view of unlisted/off-window mass (an
      RH-consistency instrument, not an RH input; Check 8: no
      hypothesis enters -- Q_W is arithmetic, Q_Z is the mpmath
      ordinate list, T is their difference).

Method note (Check 7): everything here is classical concentration
analysis -- Slepian prolates, Landau-Widom plunge counting, finite
eigenproblems on the committed section machinery. No semiclassical
procedure, no compactification, no sphere Green's functions.

Instrument: per-point staged compute, content-addressed on the
DEPS sha set (this file itself -- the producing code -- plus the
four substrate modules) and the per-point params (c, t0, NZ,
BOTK). [Round-236 F1: this instrument's own runs are INTENT-keyed
for the ordinate list (no z_sha), per the disclosed attack-run
status -- the landing stage re-keys the same computations by
content (floor_landing.py, rounds 234-235); the earlier 'EVERY
stage input in the key' quantifier was false at this locus and is
struck.]
Ladders resume point-by-point across container restarts (each
point is its own checkpoint; the wrapper pushes checkpoints to
origin every 10 minutes).

Ladders: c = 60: tau0 = 140..500 step 20 (19 points, band +-30,
window edge 653 clear by >120); c = 120: tau0 = 160..500 step 20
(18 points, band +-60, edge clear by >90). Both m_Z and m_W at
every point (build_QW ~ a minute per point; the 1bf landing's
50-minute stage was the probes, not the margins).

RESULT (ladders complete at f403d73; 37 points + floor_probe2's
15 dense-climb and 6 overlap points; fits are the combined set):

THE FLOOR LAW -- the dodging margin rides the Slepian plunge with
the pinning count at the Shannon number:
    m_Z(c, tau0) ~ m_sat * 10^(-beta(c) * (N*(c) - nb(c, tau0)))
on the climb, where nb = in-band zero count (|u| <= c) and
  N* (extrapolated pinning count, m_Z -> m_sat = 0.25):
      37.3 at c = 60 vs N_sh = 2c/pi = 38.2
      76.2 at c = 120 vs N_sh = 76.4     -- N* = N_sh to 1-2%;
  beta = 1.35 / 1.20 decades per zero (c = 60 / 120; rms resid
      0.9 / 0.5 dec -- the count regressor is integer-chunky);
  beta / (Slepian plunge fall rate 0.579 / 0.486 dec per mode)
      = 2.34 / 2.46 [round-234 F1 net-state marker: NOT a
      c-independent constant -- the standard-basis plunge rate is
      truncation-clipped and the ratio is (recipe, basis)-
      conditioned; see floor_probe7/8 RESULTs and the corrected
      1bg block. The raw numbers stand as landing-recipe pins].
Regimes: below the horizon (nb <~ N_sh - 8) the margin is
NUMERICAL ZERO -- free directions inside the concentrated
subspace (the minimizer is 100% concentrated-class, perfect
dodge); on the climb the minimizer migrates into the plunge
(44% plunge mass at (120, 340)); at saturation it is the top
prolate and m_sat = 0.253-0.255 at BOTH c (with unexplained
steps to ~0.42-0.46 at tau0 >~ 460, noted open). The certified
1bf deep points sit 2-8 zeros below pinning: the seven-decade
"hair-thin" margins are quantitatively the plunge attenuation.

THE CANCELLATION (the g4 proximity is NOT a double dodge): the
tail form T = Q_W - Q_Z,380 is truncation-dominated and deeply
indefinite on the section (lambda in [-7.2, +5.2]; the Rwin = 800
archimedean window, so the naive transfer inequality
m_W >= m_Z + lambda_min(T) is vacuous as posed), and the Weil
minimizer does not dodge: it pays O(3) to the windowed zeros and
recoups the same from T. Measured invariant at every one of the
37 points, both regimes, both c:
    T(w_Z) = -T(w_W)   (median relative residual 3-5e-4)
so m_W ~ m_Z is an antisymmetric cancellation identity. T
compressed to the bottom-5 Q_Z eigenspace is positive (2.1-4.0):
the ordering m_W > m_Z holds there. See floor_probe2.py for the
mechanism probe (the minimizers are nearly orthogonal -- the
symmetry is structural, not perturbative). Open: the mechanism.
[Net state, round-234 F1: the beta/plunge ~ 2.4 and 0.25
saturation "constants" both closed by deflation -- see
floor_probe6/7/8 RESULTs.]
"""
import math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
import hashlib
from fold_D import zeros380
from fold_surrogate import A
from witness_twosided import TwoSided

def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "witness_offline.py",
    "witness_twosided.py", "floor_probe.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

NZ = 380
BOTK = 5
LADDERS = {
    60.0: [140.0 + 20.0*i for i in range(19)],    # 140..500
    120.0: [160.0 + 20.0*i for i in range(18)],   # 160..500
}


def zero_form(S, Z, t0):
    """Q_Z,380 on the section (the truncated dodging form)."""
    s = np.concatenate([(Z - t0)*A, (-Z - t0)*A])
    Vb = np.asarray(S.vhat(s.astype(complex)))
    if Vb.shape[0] != len(s):
        Vb = Vb.T
    Q = Vb.conj().T @ Vb
    return (Q + Q.conj().T)/2


def floor_point(S, Z, c, t0):
    QZ = zero_form(S, Z, t0)
    evz, VZ = scipy_eigh(QZ, S.G)
    mZ, wZ = float(evz[0]), VZ[:, 0]
    mW, wW = S.weil_margin(t0)          # builds S.QW
    T = S.QW - QZ
    T = (T + T.conj().T)/2
    evT = scipy_eigh(T, S.G, eigvals_only=True)
    TwZ = float(np.real(np.conj(wZ) @ T @ wZ))
    TwW = float(np.real(np.conj(wW) @ T @ wW))
    # T compressed on the bottom-BOTK Q_Z eigenspace (G-orthonormal)
    Vb = VZ[:, :BOTK]
    Tc = Vb.conj().T @ T @ Vb
    evTc = np.linalg.eigvalsh((Tc + Tc.conj().T)/2)
    # in-band zero counts (u = A(gamma - tau0); mirrors negligible
    # at these heights but counted anyway)
    u = np.concatenate([(Z - t0)*A, (-Z - t0)*A])
    nb_c = int(np.sum(np.abs(u) <= c))
    nb_c2 = int(np.sum(np.abs(u) <= c/2))
    return {
        "c": c, "t0": t0, "mZ": mZ, "mW": mW,
        "ratio": (mW - mZ)/mZ,
        "evZ": [float(x) for x in evz[:BOTK]],
        "evT_bot": [float(x) for x in evT[:3]],
        "evT_top": float(evT[-1]),
        "TwZ": TwZ, "TwW": TwW,
        "evTc": [float(x) for x in evTc],
        "wZ2": [float(x) for x in np.abs(wZ)**2],
        "wW2": [float(x) for x in np.abs(wW)**2],
        "nband_c": nb_c, "nband_c2": nb_c2,
        "n": int(S.n), "nsh": 2*c/math.pi,
    }


def run_ladders():
    Z = zeros380()
    out = {}
    for c, t0s in LADDERS.items():
        S = TwoSided(c)
        leak = S.slepian_leakage()
        out[f"leak_{int(c)}"] = [float(x) for x in leak]
        for t0 in t0s:
            params = {"deps": DEPS, "c": c, "t0": t0,
                      "nz": NZ, "botk": BOTK}
            name = f"floor_{int(c)}_{int(t0)}"
            st = ckpt_key.load(name, KEYFILE, params)
            if st is None:
                st = floor_point(S, Z, c, t0)
                ckpt_key.save(name, KEYFILE, params, st)
            out[name] = st
            print(f"  c={c:5.0f} t0={t0:5.0f}: mZ {st['mZ']:+.3e} "
                  f"mW {st['mW']:+.3e} ratio {st['ratio']:+.3f} "
                  f"lminT {st['evT_bot'][0]:+.3e} "
                  f"T(wZ) {st['TwZ']:.3e} T(wW) {st['TwW']:.3e} "
                  f"nb {st['nband_c']}/{st['nband_c2']} "
                  f"nsh {st['nsh']:.1f}", flush=True)
    return out


if __name__ == "__main__":
    run_ladders()
    print("floor ladders complete", flush=True)
