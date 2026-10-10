#!/usr/bin/env python3
"""The defect attack (commissioned after the partition attack,
1506618): close the anatomy of the windowed explicit formula's
operator-closure defect on concentrated sections --
    ||Q_W^true - Q_Z(list)|| / ||Q_W^true|| = 0.0020 at (60,200),
    0.0037 at (120,300), rising with tau0 (conjugacy-defect trend
    0.0022 -> 0.0069 over tau0 = 200 -> 420)
where Q_W^true = ARCH(true gauge: complex vhat) + POLE +
conj(PRIME_code) per floor_probe4's E5.

Suspects and discriminators:
  D1 QUADRATURE: rebuild ARCH at NR/2 and 2NR on the base
     interval. A quadrature share moves under refinement; a
     converged one is flat.
  D2 HORIZON MISMATCH (the sharp hypothesis): the code's arch
     window is r in tau0 +- 800 while the zero list covers
     r in [-653.6, 653.6] -- wildly different windows, and the
     uncompensated arch slivers (r beyond the zero coverage on
     one side, mirror zeros beyond the arch window on the other)
     GROW with tau0, matching the rising trend. Discriminator:
     the MATCHED build -- arch integrated exactly over the zero
     coverage [-T_list, T_list] -- vs symmetric tau0 +- Rwin
     sweeps (400, 800, 1200).
  D3 LIST FINITENESS: the extended 660-ordinate list (gamma <=
     1013, floor_probe4's zext checkpoints) with the arch matched
     to +-1013. Under the mismatch theory the matched defect
     falls as T grows; saturation = an intrinsic component.
  D4 THE tau0 TREND: the matched build at (120, 420) -- does
     matching flatten the rise?
  D5 SECTOR SPLIT: even/odd Frobenius shares of each defect, and
     the margin-level impact |m(Q_W^true) - m(Q_Z)| / m at the
     base vs matched configs (what the defect costs the certified
     margin story).

Check 7: unconditional explicit formula + quadrature analysis.
Check 8: no hypothesis input. Keying per A355: DEPS carries this
file, floor_probe.py, floor_probe4.py (whose zext checkpoints the
extended list reuses), and the four substrate modules; params
carry the full config (point, NR, interval, list length).

RESULT (all 19 configs complete; single-cause verdict):

THE DEFECT IS THE HORIZON MISMATCH, ENTIRELY.
  D1 quadrature: ZERO share -- NR/2, base, NRx2 identical to every
     printed digit (0.00204/0.00204/0.00204 at (60,200)).
  D2 matched windows (arch integrated exactly over the zero
     coverage +-653.7): the defect COLLAPSES by a factor 40-70 --
     (60,200): 0.00204 -> 0.00003;  (120,300): 0.00373 -> 0.00007;
     (120,420): 0.00694 -> 0.00017. The symmetric sweeps confirm
     the sign (Rwin1200, more overhang, is worse: 0.00404/0.00596;
     ext-base, more zeros under the same overhang, halves it).
  D3 ext-MATCH (660 ordinates, arch +-1013.1): 0.00002 / 0.00002 /
     0.00003 -- tau0-UNIFORM at ~2-3e-5. The closure sharpens
     ~100x and the rising trend flattens completely: the trend was
     the arch window tau0 +- 800 growing more mismatched against
     the fixed +-653.6 list as tau0 rose.
  D5 sector split: the defect is even-sector dominated (odd share
     5-15%) -- the overhang is a smooth positive mean-density
     form, as the mechanism requires.

THE g4 RATIO IS NOW FULLY DERIVED, END TO END: dm/m at the base
(code) windows = +0.019 / +0.047 / +0.001 -- the certified 1bf g4
proximity values -- and at matched windows dm/m = -0.000 / -0.001
/ +0.000: with the arch horizon matched to the zero coverage, the
Weil and dodging margins agree to ~0.1% at every point including
the deep ones (m_W = 4.414e-7 vs m_Z = 4.415e-7 at (60,200)).
The chain across the four attacks: g4 observed (1bf, gated) ->
explained as conjugacy/isospectrality (the antisymmetry attack) ->
derived as first-order defect perturbation (the partition attack)
-> the defect itself closed as pure arch-window overhang, ratio
-> ~0 under matching (this attack). Nothing mysterious remains at
the operator level.

NET STATEMENT: the windowed explicit formula holds OPERATOR-WISE
on concentrated sections at the 2-3e-5 level (matched horizons,
660 ordinates, quadrature-converged, tau0-uniform) -- tail-free,
window-local, per-prime resolved (floor_probe4 E2). The remaining
~2e-5 (leakage x kernel-slope at the shared horizon, list-edge
and ordinate-precision effects) is unattributed but two orders
below the old defect. The arc's remaining REAL open objects were
the floor-law constants. [Net state, round-234 F1: both closed by
deflation -- the saturation is feature-local (floor_probe6), the
ratio (recipe, basis)-conditioned (floor_probe7/8).]
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from scipy.linalg import eigh as scipy_eigh
from scipy.special import digamma as scipy_digamma

import ckpt_key
from fold_D import zeros380
from fold_surrogate import A
from floor_probe import zero_form
from floor_probe4 import ext_zeros
from witness_twosided import TwoSided


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS5 = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "witness_offline.py",
    "witness_twosided.py", "floor_probe.py", "floor_probe4.py",
    "floor_probe5.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

TLIST = 653.7          # the 380-list coverage edge


def arch_true(S, rlo, rhi, NR, t0, chunk=20000):
    """True-gauge ARCH over the explicit interval [rlo, rhi]."""
    r = np.linspace(rlo, rhi, NR)
    ker = np.real(scipy_digamma(0.25 + 0.5j*r)) - np.log(np.pi)
    dr = r[1] - r[0]
    n = S.n
    AT = np.zeros((n, n), dtype=complex)
    for lo in range(0, NR, chunk):
        hi = min(lo + chunk, NR)
        Vc = np.asarray(S.vhat(((r[lo:hi] - t0)*A).astype(complex)))
        if Vc.shape[0] != hi - lo:
            Vc = Vc.T
        AT += (Vc.conj().T * ker[None, lo:hi]) @ Vc
    AT *= dr/(2*np.pi)
    return (AT + AT.conj().T)/2


def zform_list(S, gams, t0):
    g = np.asarray(gams)
    s = np.concatenate([(g - t0)*A, (-g - t0)*A])
    Vb = np.asarray(S.vhat(s.astype(complex)))
    if Vb.shape[0] != len(s):
        Vb = Vb.T
    Q = Vb.conj().T @ Vb
    return (Q + Q.conj().T)/2


def defect(S, Z, t0, rlo, rhi, NR):
    n = S.n
    S.weil_margin(t0)                    # POLE + PRIME (code build)
    POLE = S.QW - S.ARCH - S.PRIME
    AT = arch_true(S, rlo, rhi, NR, t0)
    QWt = AT + POLE + np.conj(S.PRIME)
    QWt = (QWt + QWt.conj().T)/2
    QZ = zform_list(S, Z, t0)
    D = QWt - QZ
    P = np.diag([(-1.0)**k for k in range(n)])
    Dodd = (D - P @ D @ P)/2
    nq = np.linalg.norm(QWt)
    mW = float(scipy_eigh(QWt, S.G, eigvals_only=True)[0])
    mZ = float(scipy_eigh(QZ, S.G, eigvals_only=True)[0])
    return {
        "rel": float(np.linalg.norm(D)/nq),
        "rel_odd": float(np.linalg.norm(Dodd)/nq),
        "rel_even": float(np.linalg.norm(D - Dodd)/nq),
        "mW": mW, "mZ": mZ,
        "dm_rel": (mW - mZ)/mZ if mZ != 0 else None,
    }


def run():
    Z380 = zeros380()
    ZE = np.concatenate([Z380, ext_zeros()])
    TEXT = 1013.1
    sects = {}
    def sect(c):
        if c not in sects:
            sects[c] = TwoSided(c)
        return sects[c]

    # config table: (label, c, t0, list_id, rlo_fn, rhi_fn, NR)
    cfgs = []
    for c, t0 in ((60.0, 200.0), (120.0, 300.0)):
        cfgs += [
            ("base",      c, t0, 380, t0 - 800, t0 + 800, 120001),
            ("NR/2",      c, t0, 380, t0 - 800, t0 + 800, 60001),
            ("NRx2",      c, t0, 380, t0 - 800, t0 + 800, 240001),
            ("Rwin400",   c, t0, 380, t0 - 400, t0 + 400, 60001),
            ("Rwin1200",  c, t0, 380, t0 - 1200, t0 + 1200, 180001),
            ("MATCHED",   c, t0, 380, -TLIST, TLIST, 120001),
            ("ext-base",  c, t0, 660, t0 - 800, t0 + 800, 120001),
            ("ext-MATCH", c, t0, 660, -TEXT, TEXT, 180001),
        ]
    for c, t0 in ((120.0, 420.0),):
        cfgs += [
            ("base",      c, t0, 380, t0 - 800, t0 + 800, 120001),
            ("MATCHED",   c, t0, 380, -TLIST, TLIST, 120001),
            ("ext-MATCH", c, t0, 660, -TEXT, TEXT, 180001),
        ]

    for lab, c, t0, nlist, rlo, rhi, NR in cfgs:
        Z = Z380 if nlist == 380 else ZE
        params = {"deps": DEPS5, "c": c, "t0": t0, "list": nlist,
                  "rlo": rlo, "rhi": rhi, "NR": NR}
        name = f"defect_{lab.replace('/','-')}_{int(c)}_{int(t0)}"
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            st = defect(sect(c), Z, t0, rlo, rhi, NR)
            ckpt_key.save(name, KEYFILE, params, st)
        dm = (f"{st['dm_rel']:+.3f}" if st["dm_rel"] is not None
              else "  --  ")
        print(f"  ({c:.0f},{t0:.0f}) {lab:9s} list={nlist} "
              f"arch=[{rlo:7.1f},{rhi:7.1f}] NR={NR}: rel "
              f"{st['rel']:.5f} (odd {st['rel_odd']:.5f} even "
              f"{st['rel_even']:.5f}) mW {st['mW']:+.3e} "
              f"dm/m {dm}", flush=True)


if __name__ == "__main__":
    run()
    print("defect probes complete", flush=True)
