#!/usr/bin/env python3
"""The off-line witness: inject a synthetic off-line zero quadruplet
{beta +- i gamma0, 1-beta +- i gamma0} into the zero-side section
form with the HONEST Weil accounting, and measure the response of
the certified margin instrument.

For an on-line zero the section contribution is the PSD rank-one
v(s) v(s)^H, s = (gamma - tau0) A. For an off-line quadruplet at
distance d = beta - 1/2 from the line, the ordinates are complex
(t = gamma -+ i d) and the contribution to the quadratic form is the
Hermitian but INDEFINITE pair block
    v(s - i dA) v(s + i dA)^H + v(s + i dA) v(s - i dA)^H
(plus the mirror at -gamma0), where v at complex argument is the
quadrature Fourier transform of the section basis (entire, type A).
The min generalized eigenvalue can then go NEGATIVE. [SCOPE
CORRECTED at the two-sided diagnostic, session at 6f82769: this
truncated zero-side form is NOT the Weil form at depth -- the
dodging minimizer exports O(1) Parseval mass beyond the measured
zero window (tail(w_Z) = 3.12 at (60,200)) -- so a negative margin
here is an INSTRUMENT-sensitivity detection, not a Weil-positivity
violation; the genuine Weil-positivity witness lives on the
arithmetic-side form and concentrated test vectors, see
witness_twosided.py.] The experiment: the detection threshold d*(c, tau0) where
the margin crosses zero, its scaling against the base margin (the
lift-off amplifier question), and the ladder-statistics witness (an
off-line pair is a doubled ordinate: a zero spacing).

Injection protocol: the donor zero nearest gamma0 is REMOVED from
the ladder and the quadruplet at (gamma0 = donor, d) replaces it --
at d = 0 this is a double zero on the line (the degenerate limit).

RESULT (session run at b4113c8; consistency real-vs-complex path
rel 6.5e-9, the certified pins reproduced to the digit):
   c   tau0   base margin    d* (in-band donor)
   60   200    4.415e-07      6.142e-04
   60   280    9.352e-03      1.017e-01
  120   260    1.139e-07      1.311e-03
  120   300    3.760e-04      3.747e-02
  120   340    8.374e-02      4.767e-01
  120   360    2.549e-01      3.706e-01
  120   400    2.526e-01      3.143e-01
  120   450    2.545e-01      5.187e-01
THE SQUARE-ROOT AMPLIFIER LAW: log-log fit of d* against the base
margin across 6.35 decades of margin gives slope 0.440 on this
committed 8-point table (0.448 on the verifier's four deep points;
the draft's "~0.51 across seven decades" was a stale session digit,
round-229 F5) -- d* ~ sqrt(m). Note the two deepest points are
anti-ordered against the monotone law ((60,200): m 4.415e-07,
d* 6.142e-04 vs (120,260): m 1.139e-07, d* 1.311e-03 -- the
smaller margin has the LARGER d*): the law is a cross-section
scaling trend, not per-point monotone. The
mechanism: the quadruplet is even in d (functional-equation
symmetry), so the indefinite response enters at O(d^2): the margin
shifts by ~ -(dA)^2 |<w, v'>|^2, crossing zero at d* ~ sqrt(m)/(A
|overlap|). Consequence (scope-corrected, see above): at the deep certified
points the DODGING INSTRUMENT's margin flips negative for an
in-band zero displaced ~6e-4 from the line -- a sensitivity law
for the certified instrument, whose relation to genuine Weil
positivity runs through the two-sided closure.
"""
import numpy as np, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from numpy.polynomial import legendre as L
from scipy.linalg import eigh as scipy_eigh
from fold_D import zeros380, inv_Nbar
from fold_surrogate import Sect, make_basis, GRIDS, NZ, A

XG, WG = np.polynomial.legendre.leggauss(3000)   # resolves |s| up to ~2400 rad (the far mirror zeros); 800 nodes lost the base margin by 5 orders


class WSect(Sect):
    """Sect + complex-argument evaluation and witness margins."""
    def __init__(self, c):
        super().__init__(c)
        KL = self.P.shape[1]
        PX = np.zeros((self.n, len(XG)))
        for m in range(self.n):
            PX[m] = L.legval(XG, self.P[m]*np.sqrt(np.arange(KL) + 0.5))
        self.PXw = PX*WG[None, :]          # n x 3000, weighted values

    def vhat(self, s):
        """psi_hat at complex s by quadrature: int psi(x) e^{isx} dx,
        times the margin convention's factor A."""
        e = np.exp(1j*np.multiply.outer(np.asarray(s, complex), XG))
        return A*(self.PXw @ e.T).T if np.ndim(s) else A*(self.PXw @ e)

    def witness_margin(self, zeros, tau0, gamma0, d):
        """Margin with the donor zero nearest gamma0 replaced by the
        off-line quadruplet at (gamma0, d)."""
        k = int(np.argmin(np.abs(zeros - gamma0)))
        Zp = np.delete(zeros, k)
        g0 = zeros[k]
        s = np.concatenate([(Zp - tau0)*A, (-Zp - tau0)*A])
        Vb = np.asarray(self.vhat(s.astype(complex)))   # (len(s), n)
        if Vb.shape[0] != len(s):
            Vb = Vb.T
        Q = Vb.conj().T @ Vb                        # n x n PSD base
        for g in (g0, -g0):
            s0 = (g - tau0)*A
            vm = self.vhat(complex(s0, -d*A))
            vp = self.vhat(complex(s0, +d*A))
            Q = Q + np.outer(vm.conj(), vp) + np.outer(vp.conj(), vm)
        Q = (Q + Q.conj().T)/2
        return scipy_eigh(Q, self.G, eigvals_only=True)[0]

    def base_margin(self, zeros, tau0):
        s = np.concatenate([(zeros - tau0)*A, (-zeros - tau0)*A])
        Vb = np.asarray(self.vhat(s.astype(complex)))
        if Vb.shape[0] != len(s):
            Vb = Vb.T
        Q = Vb.conj().T @ Vb
        Q = (Q + Q.conj().T)/2
        return scipy_eigh(Q, self.G, eigvals_only=True)[0]


def dstar(S, zeros, tau0, gamma0, dmax=1.0, tol=1e-10):
    """Bisect the smallest d where the witness margin goes negative."""
    if S.witness_margin(zeros, tau0, gamma0, dmax) >= 0:
        return None
    lo, hi = 0.0, dmax
    while hi - lo > tol*max(1, hi):
        mid = (lo + hi)/2
        if S.witness_margin(zeros, tau0, gamma0, mid) < 0:
            hi = mid
        else:
            lo = mid
    return hi


if __name__ == "__main__":
    Z = zeros380()
    pts = [(60.0, 200), (60.0, 280), (120.0, 260), (120.0, 300),
           (120.0, 340), (120.0, 360), (120.0, 400), (120.0, 450)]
    sects = {}
    print(" c   tau0   base margin      m(d=0, doubled)   d* (in-band donor)",
          flush=True)
    for c, t0 in pts:
        if c not in sects:
            sects[c] = WSect(c)
        S = sects[c]
        mb = S.base_margin(Z, float(t0))
        m0 = S.witness_margin(Z, float(t0), float(t0), 0.0)
        ds = dstar(S, Z, float(t0), float(t0))
        print(f"{c:4.0f}  {t0:4d}   {mb:.3e}      {m0:.3e}      "
              f"{'%.3e' % ds if ds is not None else '>1'}", flush=True)
    # consistency: the complex-path base margin must match Sect.margin
    S60 = sects[60.0]
    m_ref = S60.margin(Z, 200.0)
    m_cpx = S60.base_margin(Z, 200.0)
    print(f"\nconsistency: real-path {m_ref:.6e} vs complex-path "
          f"{m_cpx:.6e} (rel {abs(m_ref - m_cpx)/m_ref:.2e})", flush=True)
