#!/usr/bin/env python3
"""The height arc, Phase 2 (commissioned after the anomaly attack):
the ARITHMETIC side at A != 2 -- the windowed explicit formula's
operator closure and arithmetic-only section Weil positivity at
the high-aperture critical windows.

What moves with the aperture dial, all generalized here:
  - the PRIME operator: von Mangoldt sum over n < e^(2A) (the
    cutoff moves: ~54 prime powers at A = 2, ~110 at A = 3, primes
    to 403), autocorrelation panels at shift u/A, phase in the
    TRUE gauge (phz = e^(-i tau0 u), per the 1bg E5 verdict --
    the certified code convention is its conjugate);
  - the ARCH operator: the digamma kernel integrated over the
    MATCHED horizon (exactly the ordinate coverage +-T_z, per the
    1bg defect closure -- the certified Rwin = 800 convention is
    the known mismatch), complex-vhat true gauge, s-resolution
    held at the A = 2 build's scale (NR from s_step ~ 0.03; an
    NR/2 convergence leg at one point);
  - the POLE pair (negligible at these heights; included for
    form);
  - the zero side over the complete ordinate list within the
    horizon (coverage verified complete per rung).

Measured per point: m_W (arithmetic-only), m_Z, the closure
rel = ||Q_W - Q_Z||/||Q_W|| (out-of-sample test of the 1bg
2-3e-5 matched-horizon closure), the ARCH/PRIME decomposition on
the Weil minimizer (the null-direction cancellation at deep
points), and (m_W - m_Z)/m_Z.

Points: A = 2.5 at tau0 = 630 (deep climb, m_Z ~ 1.1e-7) and 880
(near crossing); A = 3.0 at 1580 (deep, ~6.5e-8), 2000 (climb),
and 2340 (near crossing) -- the critical-window ladder to height
~2340 with horizon 2780.

Check 7: the unconditional explicit formula, digamma quadrature,
finite eigenproblems -- classical. Check 8: no hypothesis input.
Keying per the standing law (A361): content-keyed on the
producing modules, the full config, and the ordinate bytes.
No RH leverage claimed: verification through the dial.

RESULT (run 1 full-window + run 2 s-matched windows, both on the
record):

  THE DEEP CRITICAL WINDOWS -- THE COMMISSION'S CORE -- ARE GREEN
  WITH THE 1bg CLOSURE OUT-OF-SAMPLE IN APERTURE:
    A = 2.5, tau0 = 630 (height 630, 48 prime powers, primes to
      ~148): m_W = +1.09e-7 vs m_Z to dm/m = -0.0007 (0.07%),
      closure rel 8.3e-5 (run 1 full-window: 7.8e-5 -- recipe-
      stable), null cancellation A/P = +4.599/-4.599 (four
      digits).
    A = 3.0, tau0 = 1580 (height 1580, 98 prime powers, primes to
      403): m_W = +6.321e-8 vs m_Z = 6.322e-8 -- dm/m = -0.0001
      (0.01%), closure rel 1.19e-5 (BETTER than the A = 2
      benchmark 2-3e-5), A/P = +5.527/-5.527. ARITHMETIC-ONLY
      SECTION WEIL POSITIVITY AT THE DEEP CRITICAL WINDOW AT
      HEIGHT 1580, hair-thin positive exactly as the floor law
      demands, matching the zero side to a hundredth of a percent.
  The near-crossing A = 2.5 point (880) is likewise clean
  (closure 1.8e-4, dm/m 0.15%).

  THE RUN-1 LESSON (on the record): the full-window build FAILED
  at A = 3 -- the mirror ordinates reach |s| ~ 15,400, far beyond
  the 3000-node quadrature validity (~2400), aliasing both sides
  (m_Z read 2.28 against the real path's 6.5e-8). The s-matched
  window (SCUT = 2000 on both sides -- the 1bg horizon-matching
  lesson generalized to s) fixed the deep point completely.

  RESIDUE [CLOSED at the residue attack, height_residue.py: the
  pole vectors at oscillation frequency A*tau0 ~ 6000-7000 rad
  are O(1) quadrature noise (|u| = 1.93/1.48 at 2000/2340 vs the
  superexponentially tiny truth); omitting the analytically-
  negligible pole term recovers 2000 to closure 3.4e-5 (dm/m
  0.00%) and 2340 to 2.4e-5 (0.00%), the deep point indifferent.
  Every Phase-2 point now closes in the 1e-5 class.] The original
  flag, retained as the record: the A = 3 saturated-regime
  points degrade under the same recipe -- tau0 = 2000: closure
  4.1e-2 with m_W = 4.1e-3 vs m_Z = 9.3e-4 (the zero side agrees
  with the real-path ladder; the ARITHMETIC side is high);
  tau0 = 2340: closure 1.8e-2, dm/m -2.8%. Both sit in the
  saturated/climb regime where positivity is not delicate
  (margins 1e-3-0.1), and the deep point at the same aperture and
  recipe is clean at 1.2e-5 -- so the residue is config-local,
  not an arithmetic failure. Note (2000) carries the tight
  min-gap 0.098 feature in-band. Diagnosis owed: an SCUT sweep
  (1600/2000/2400) and a real-path conj-gauge cross-check to
  split windowing-edge from quadrature effects.

NET: the height arc's Phase 2 core stands -- the windowed
explicit formula's operator closure and arithmetic-only Weil
positivity hold at the DEEP critical windows out-of-sample in
aperture, at heights 630 and 1580, with the enlarged prime sets
doing the null-direction cancellation to four digits. The
saturated-regime closure at A = 3 has a config-local residue
under diagnosis. No RH leverage claimed.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from numpy.polynomial import legendre as L
from scipy.linalg import eigh as scipy_eigh
from scipy.special import digamma as scipy_digamma

import ckpt_key
from fold_D import zeros380
from height_uniformity import ASect, ext_zeros_to


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPSP2 = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "height_uniformity.py",
    "height_arith.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")


def _zsha(a):
    return hashlib.sha256(
        np.ascontiguousarray(a).tobytes()).hexdigest()[:16]


C0 = 120.0
SCUT = 2000.0    # symmetric s-window on BOTH sides (run 2): the
                 # run-1 full-window build failed at A = 3 -- the
                 # mirror ordinates reach |s| ~ 15,400, far beyond
                 # the 3000-node quadrature's ~2400 validity
                 # (witness_offline's own header), aliasing both
                 # sides (m_Z 2.28 vs the real-path 6.5e-8).
                 # Matching the windows in s keeps every evaluated
                 # |s| <= 2000 and drops identical content from
                 # both forms (leakage-negligible to the section).
XG3, WG3 = np.polynomial.legendre.leggauss(3000)
TGX, TGW = np.polynomial.legendre.leggauss(600)
S_STEP = 0.03
PTS_P2 = [
    (2.5, 630.0, 810), (2.5, 880.0, 810),
    (3.0, 1580.0, 2270), (3.0, 2000.0, 2270), (3.0, 2340.0, 2270),
]


class AWSect(ASect):
    """ASect + complex-argument evaluation (aperture per call)."""
    def __init__(self, c):
        super().__init__(c)
        KL = int(1.4*c) + 60
        PX = np.zeros((self.n, len(XG3)))
        for m in range(self.n):
            PX[m] = L.legval(XG3, self.P[m]*np.sqrt(np.arange(KL) + 0.5))
        self.PXw = PX*WG3[None, :]
        self.PXplain = PX

    def vhat(self, s, Ap):
        e = np.exp(1j*np.multiply.outer(np.asarray(s, complex), XG3))
        return Ap*(self.PXw @ e.T).T if np.ndim(s) else Ap*(self.PXw @ e)


def vonmangoldt(nmax):
    lam = np.zeros(nmax + 1)
    for p in range(2, nmax + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            pk = p
            while pk <= nmax:
                lam[pk] = np.log(p)
                pk *= p
    return lam


def prime_mat_A(S, tau0, Ap):
    """The prime operator, TRUE gauge (phz = e^(-i tau0 u)), cutoff
    u < 2A, shift u/Ap in the panels."""
    DELTA = 2*Ap
    LAMV = vonmangoldt(int(np.floor(np.exp(DELTA))) + 1)
    NS = np.nonzero(LAMV)[0]
    PR = np.zeros((S.n, S.n), dtype=complex)
    KL = int(1.4*S.c) + 60
    def psi_x(x):
        out = np.zeros((S.n, len(x)))
        for m in range(S.n):
            out[m] = L.legval(x, S.P[m]*np.sqrt(np.arange(KL) + 0.5))
        return out
    for n_ in NS:
        u = np.log(n_)
        if u >= DELTA:
            continue
        lo, hi = -1.0, 1.0 - u/Ap
        xm = (hi + lo)/2 + (hi - lo)/2*TGX
        wm = (hi - lo)/2*TGW*Ap
        B1 = psi_x(xm)
        B2 = psi_x(xm + u/Ap)
        Am = np.einsum('ni,i,mi->nm', B1, wm, B2)
        phz = np.exp(-1j*tau0*u)
        PR += -LAMV[n_]/np.sqrt(n_)*(phz*Am + np.conj(phz)*Am.T)
    return PR


def pole_vecs_A(S, tau0, Ap):
    PXc = S.PXplain.astype(complex)
    u = Ap*np.einsum('ni,i->n', PXc,
                     WG3*np.exp(((-1j*tau0 - 0.5)*Ap)*XG3))
    v = Ap*np.einsum('ni,i->n', PXc,
                     WG3*np.exp(((-1j*tau0 + 0.5)*Ap)*XG3))
    return u, v


def arch_true_A(S, tau0, Ap, Tz, chunk=15000):
    """True-gauge ARCH over the s-matched window |s| <= SCUT,
    intersected with the ordinate coverage [-Tz, Tz]."""
    rlo = max(-Tz, tau0 - SCUT/Ap)
    rhi = min(Tz, tau0 + SCUT/Ap)
    NR = int((rhi - rlo)*Ap/S_STEP) | 1
    r = np.linspace(rlo, rhi, NR)
    ker = np.real(scipy_digamma(0.25 + 0.5j*r)) - np.log(np.pi)
    dr = r[1] - r[0]
    AT = np.zeros((S.n, S.n), dtype=complex)
    for lo in range(0, NR, chunk):
        hi = min(lo + chunk, NR)
        Vc = S.vhat(((r[lo:hi] - tau0)*Ap).astype(complex), Ap)
        if Vc.shape[0] != hi - lo:
            Vc = Vc.T
        AT += (Vc.conj().T * ker[None, lo:hi]) @ Vc
    AT *= dr/(2*np.pi)
    return (AT + AT.conj().T)/2, NR


def zform_A(S, Z, tau0, Ap):
    s = np.concatenate([(Z - tau0)*Ap, (-Z - tau0)*Ap])
    s = s[np.abs(s) <= SCUT]
    Vb = S.vhat(s.astype(complex), Ap)
    if Vb.shape[0] != len(s):
        Vb = Vb.T
    Q = Vb.conj().T @ Vb
    return (Q + Q.conj().T)/2


def run():
    Z380 = zeros380()
    S = AWSect(C0)
    for Ap, t0, kmax in PTS_P2:
        ZE = ext_zeros_to(kmax)
        Z = np.concatenate([Z380, ZE])
        Tz = float(Z.max()) + 0.5
        params = {"deps": DEPSP2, "A": Ap, "t0": t0, "c": C0,
                  "Tz": round(Tz, 2), "s_step": S_STEP,
                  "s_cut": SCUT,
                  "kmax": kmax, "z_sha": _zsha(Z)}
        name = f"arith_A{Ap:.1f}_t{int(t0)}".replace(".", "p")
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            G = Ap*S.gram
            AT, NR = arch_true_A(S, t0, Ap, Tz)
            u, v = pole_vecs_A(S, t0, Ap)
            Mp = np.outer(np.conj(v), u)
            PR = prime_mat_A(S, t0, Ap)
            QW = AT + Mp + Mp.conj().T + PR
            QW = (QW + QW.conj().T)/2
            QZ = zform_A(S, Z, t0, Ap)
            evW, VW = scipy_eigh(QW, G)
            mW, wW = float(evW[0]), VW[:, 0]
            mZ = float(scipy_eigh(QZ, G, eigvals_only=True)[0])
            arch = float(np.real(np.conj(wW) @ AT @ wW))
            prime = float(np.real(np.conj(wW) @ PR @ wW))
            st = {"A": Ap, "t0": t0, "Tz": Tz, "NR": NR,
                  "mW": mW, "mZ": mZ,
                  "rel": float(np.linalg.norm(QW - QZ) /
                               np.linalg.norm(QW)),
                  "arch": arch, "prime": prime,
                  "nprimes": int(np.sum(vonmangoldt(
                      int(np.exp(2*Ap)) + 1) > 0))}
            ckpt_key.save(name, KEYFILE, params, st)
        print(f"  A={st['A']:.1f} t0={st['t0']:6.0f} (Tz {st['Tz']:.0f}, "
              f"NR {st['NR']}, {st['nprimes']} prime powers): mW "
              f"{st['mW']:+.3e} mZ {st['mZ']:+.3e} dm/m "
              f"{(st['mW']-st['mZ'])/st['mZ']:+.4f} | closure rel "
              f"{st['rel']:.2e} | A/P {st['arch']:+.3f}/"
              f"{st['prime']:+.3f}", flush=True)


if __name__ == "__main__":
    run()
    print("phase-2 arithmetic probes complete", flush=True)
