#!/usr/bin/env python3
"""The antisymmetry attack (commissioned after the floor attack's
RESULT, 310cc20): find the mechanism behind the measured invariant
T(w_Z) = -T(w_W) (median 5e-4 across 37 floor points) with nearly
G-orthogonal minimizers.

THE MECHANISM (pre-test at (60,200), verified here across points):
one identity explains the entire phenomenology --

    Q_W  ~=  conj(Q_Z)          (entrywise, real prolate basis)

with defect ~0.2% in norm. The algebra that makes this a
reflection statement: prolates are parity eigenfunctions
(psi_k(-x) = (-1)^k psi_k(x)), so for ANY zero-sampling form
P Q P = the form with the sample set REFLECTED about tau0
(P = diag((-1)^k)), and this equals conj(Q) = Q^T exactly. Hence
Q_W ~= conj(Q_Z) says: THE WINDOWED ARITHMETIC FORM IS THE
TRUNCATED ZERO FORM WITH THE ZEROS REFLECTED ABOUT THE SECTION
CENTER. Consequences, each previously measured as a mystery:
  - conjugate Hermitian matrices are isospectral -> m_W ~= m_Z
    at every point (the certified g4 proximity, all seven decades);
  - w_W ~= conj(w_Z) -> the plain overlap |<w_Z, G w_W>| is small
    (a generic complex vector is nearly orthogonal to its own
    conjugate) while the CONJUGATE overlap |<conj(w_Z), G w_W>|
    should be ~1 -- the discriminating prediction this instrument
    tests;
  - T(conj w) = -T(w) identically for T = conj(Q_Z) - Q_Z, so
    T(w_W) ~= -T(w_Z): the antisymmetry invariant is EXACT under
    the identity, broken only by the defect;
  - T ~= -2i Im(Q_Z): the tail form is minus twice the imaginary
    part of the windowed zero form (the asymmetry of the zero
    configuration about tau0), whose spectrum is exactly
    +-symmetric -- the measured +-5 symmetry of T's spectrum.
Via the explicit formula (Q_W = Q_full - ArchTail exactly on the
section), the identity is a WINDOWED DUALITY: reflection about
tau0 exchanges the missing zero tail with the missing archimedean
tail. Why the exchange is this exact is the remaining open
question (Check 7 note: everything here is finite linear algebra
on the committed section machinery; Check 8: no hypothesis input
-- Q_W is arithmetic, Q_Z is the ordinate list).

Measurements per point (regime samples spanning both c and all
three floor regimes): the four norm ratios (raw difference,
conjugacy defect, the exact parity identity as a numerical
control, T vs -2i Im Q_Z), spectral distances, the conjugate
overlap vs the plain overlap, and the first-order defect
accounting m_W - m_Z ~= D(conj w_Z) for D = Q_W - conj(Q_Z).
Pencil symmetry (min-eig of Q_Z + theta T under theta -> 1-theta)
at two points as a corollary check.

Keying per A355: DEPS carries this file, floor_probe.py (whose
zero_form it uses), and the four substrate modules; params carry
(c, t0, nz).

RESULT (run complete; ten regime points + two pencils): the
mechanism is CONFIRMED at every point --

  THE REFLECTION IDENTITY:  Q_W ~= conj(Q_Z)  [= P Q_Z P = the
  zero form with the ordinates reflected about tau0; the parity
  identity is machine-exact, 4e-15]
  defect ||Q_W - conj(Q_Z)||/||Q_W|| = 0.0022-0.0069 across both
  c and all three floor regimes (vs 0.52-0.79 raw), rising slowly
  with tau0 (anatomy unmeasured, open).

Verified consequences, each a previously-open mystery:
  - the conjugate overlap |<conj(w_Z), G w_W>| = 1.0000 at 9/10
    points (plain overlap 0.01-0.64): w_W IS conj(w_Z). The one
    exception is the below-horizon point (120,180) at 0.61, where
    the bottom eigenvalue is a degenerate near-null subspace and
    the eigensolver's representative is arbitrary -- expected.
  - m_W - m_Z ~= D(conj w_Z) (first-order perturbation in the
    defect D = Q_W - conj Q_Z) closes to 4-10% at every point,
    from dm = -3e-12 through +1.5e-3: THE CERTIFIED g4 RATIO IS
    DERIVED -- the proximity is isospectrality of a matrix and
    its conjugate, broken only by the defect.
  - T = -2i Im(Q_Z) to 0.3-1.2%; T(conj w) = -T(w) identically:
    the antisymmetry invariant is exact under the identity.
  - the pencil min-eig curve is theta <-> 1-theta symmetric to
    1.5e-4 absolute (m(1/2) ~ 0.55-0.67).

THE ODD-PART DECOMPOSITION (the arithmetic content): writing
odd(M) = (M - P M P)/2, the identity is equivalent to
    odd(Q_Z,380) ~= -odd(PRIME) + [odd(ARCH) ~ 6% + poles 0.1%]
measured: ||odd QZ|| = 20.716 vs ||odd PRIME|| = 20.717 with
||odd QW + odd QZ|| = 0.043 at (60,200) (23.096/22.992/0.035 at
(120,300)).

[SCOPE CORRECTED at the partition attack -- floor_probe4.py
RESULT, E4/E5. This block's original closing read the identity as
a "windowed duality" ("the zeros' asymmetry is minus the primes'
asymmetry") and predicted a window-partition (in-band -1x, zero
tail +2x). Both readings are RETRACTED: E4 measured the tail
contribution at 0.0000 (269 further ordinates), and E5's
gauge-rebuild showed ||ARCH_true - conj(ARCH_code)|| = 0.0000 --
the 1bb-lineage arithmetic build is the CONJUGATE of the
explicit-formula operator, so Q_W ~= conj(Q_Z) is the plain
windowed explicit formula seen through the build's phase-gauge
convention. The measurements above all stand; the mystery
deflates to: the windowed explicit formula holds operator-wise on
concentrated sections at 0.2-0.4%, tail-free, per-prime resolved.
Certified scalars are conjugation-blind and unaffected; the g4
derivation stands in cleaner form. Open: the defect's anatomy
(0.2-0.7%, rising with tau0).] Check 7: finite linear algebra +
the unconditional explicit formula throughout; Check 8: no
hypothesis input.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
from fold_D import zeros380
from floor_probe import zero_form
from witness_twosided import TwoSided


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS3 = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "witness_offline.py",
    "witness_twosided.py", "floor_probe.py", "floor_probe3.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

NZ = 380
PTS3 = [(60.0, 200.0), (60.0, 240.0), (60.0, 300.0), (60.0, 420.0),
        (120.0, 180.0), (120.0, 240.0), (120.0, 260.0),
        (120.0, 300.0), (120.0, 340.0), (120.0, 420.0)]
PENCIL_PTS = [(60.0, 200.0), (120.0, 300.0)]


def conj_point(S, Z, c, t0):
    QZ = zero_form(S, Z, t0)
    mW, wW = S.weil_margin(t0)          # builds S.QW
    QW = S.QW
    n = S.n
    evz, VZ = scipy_eigh(QZ, S.G)
    mZ, wZ = float(evz[0]), VZ[:, 0]
    eww = scipy_eigh(QW, S.G, eigvals_only=True)
    P = np.diag([(-1.0)**k for k in range(n)])
    nQW = np.linalg.norm(QW)
    D = QW - np.conj(QZ)
    T = QW - QZ
    T = (T + T.conj().T)/2
    twoiIm = QZ - np.conj(QZ)           # 2i Im(QZ)
    out = {
        "c": c, "t0": t0, "mZ": mZ, "mW": mW, "n": n,
        "rel_raw": float(np.linalg.norm(QW - QZ)/nQW),
        "rel_conj": float(np.linalg.norm(D)/nQW),
        "rel_parity_ident": float(
            np.linalg.norm(P @ QZ @ P - np.conj(QZ)) /
            np.linalg.norm(QZ)),
        "rel_T_2iIm": float(np.linalg.norm(T + twoiIm) /
                            np.linalg.norm(T)),
        "spec_rel_med": float(np.median(
            np.abs(eww - evz)/np.maximum(np.abs(evz), 1e-12))),
        "spec_rel_max": float(np.max(
            np.abs(eww - evz)/np.maximum(np.abs(evz), 1e-12))),
        "ov_plain": float(abs(complex(np.conj(wZ) @ S.G @ wW))),
        "ov_conj": float(abs(complex(wZ @ S.G @ wW))),
        "dm": mW - mZ,
        "D_conjwZ": float(np.real(
            wZ @ D @ np.conj(wZ))),
    }
    return out


def pencil(S, Z, c, t0, ntheta=11):
    QZ = zero_form(S, Z, t0)
    S.weil_margin(t0)
    T = S.QW - QZ
    T = (T + T.conj().T)/2
    ths, ms = [], []
    for i in range(ntheta):
        th = i/(ntheta - 1)
        ev = scipy_eigh(QZ + th*T, S.G, eigvals_only=True)
        ths.append(th)
        ms.append(float(ev[0]))
    return {"c": c, "t0": t0, "theta": ths, "m": ms}


def run():
    Z = zeros380()
    sects = {}
    def sect(c):
        if c not in sects:
            sects[c] = TwoSided(c)
        return sects[c]
    for c, t0 in PTS3:
        params = {"deps": DEPS3, "c": c, "t0": t0, "nz": NZ}
        name = f"conj_{int(c)}_{int(t0)}"
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            st = conj_point(sect(c), Z, c, t0)
            ckpt_key.save(name, KEYFILE, params, st)
        print(f"  ({c:.0f},{t0:.0f}): raw {st['rel_raw']:.3f} "
              f"CONJ {st['rel_conj']:.4f} parity-ident "
              f"{st['rel_parity_ident']:.1e} T=-2iIm "
              f"{st['rel_T_2iIm']:.4f} ov {st['ov_plain']:.3f}->"
              f"{st['ov_conj']:.4f} dm {st['dm']:+.2e} "
              f"D(cwZ) {st['D_conjwZ']:+.2e}", flush=True)
    for c, t0 in PENCIL_PTS:
        params = {"deps": DEPS3, "c": c, "t0": t0, "nz": NZ,
                  "pencil": 11}
        name = f"pencil_{int(c)}_{int(t0)}"
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            st = pencil(sect(c), Z, c, t0)
            ckpt_key.save(name, KEYFILE, params, st)
        ms = st["m"]
        sym = max(abs(ms[i] - ms[len(ms)-1-i]) for i in range(len(ms)))
        print(f"  pencil ({c:.0f},{t0:.0f}): m(0) {ms[0]:.3e} "
              f"m(1/2) {ms[len(ms)//2]:.3e} m(1) {ms[-1]:.3e} "
              f"max|m(th)-m(1-th)| {sym:.2e}", flush=True)


if __name__ == "__main__":
    run()
    print("conjugacy probes complete", flush=True)
