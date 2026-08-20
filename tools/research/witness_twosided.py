#!/usr/bin/env python3
"""The two-sided witness (1bf GO/NO-GO): compute the WEIL-SIDE margin
m_W (arithmetic only: digamma ARCH + pole pair + von Mangoldt primes
-- certified 1bb machinery, section-agnostic) on the DEEP certified
1bc sections, alongside the on-line zero-side margin m_Z and the
truncation ordering, and fold through the sqrt-amplifier law:

  (i)  m_W >= 0 is the section-level Weil-positivity statement with
       NO zero-location input;
  (ii) the explicit formula gives zero-side = Weil-side exactly, and
       under on-line placement every truncation term is >= 0, so
       z_N (N zeros, on-line) <= m_W * nrm on any vector, monotone
       in N -- the ordering + convergence is the integrity check;
  (iii) the witness law (witness_offline: the margin flips at
       d* ~ sqrt(m)) applied to m_W bounds the line-displacement of
       any in-band zero: (d A)^2 |<w, dv/ds>|^2 <= m_W + budget.

Output per point: m_W, m_Z(380), the identity ratio ladder
z_N/(m_W nrm) for N = 260/320/380, the donor overlap factor, and
d_bound = sqrt((m_W + eps_budget))/(A |ov|).
"""
import numpy as np, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scipy.linalg import eigh as scipy_eigh
from scipy.special import digamma as scipy_digamma
from numpy.polynomial import legendre as L
from fold_D import zeros380
from fold_surrogate import A
from witness_offline import WSect, XG, WG

DELTA = 2*A            # test-function support in u = A x: |u| <= 2A = 4
TGX, TGW = np.polynomial.legendre.leggauss(600)


def vonmangoldt(nmax):
    lam = np.zeros(nmax + 1)
    for p in range(2, nmax + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            pk = p
            while pk <= nmax:
                lam[pk] = np.log(p)
                pk *= p
    return lam


LAMV = vonmangoldt(int(np.floor(np.exp(DELTA))) + 1)
NS_PR = np.nonzero(LAMV)[0]


class TwoSided(WSect):
    def psi_x(self, x):
        KL = self.P.shape[1]
        out = np.zeros((self.n, len(x)))
        for m in range(self.n):
            out[m] = L.legval(x, self.P[m]*np.sqrt(np.arange(KL) + 0.5))
        return out

    def prime_mat(self, tau0):
        PR = np.zeros((self.n, self.n), dtype=complex)
        for n_ in NS_PR:
            u = np.log(n_)
            if u >= DELTA:
                continue
            lo, hi = -1.0, 1.0 - u/A
            xm = (hi + lo)/2 + (hi - lo)/2*TGX
            wm = (hi - lo)/2*TGW*A
            B1 = self.psi_x(xm)
            B2 = self.psi_x(xm + u/A)
            Am = np.einsum('ni,i,mi->nm', B1, wm, B2)
            phz = np.exp(1j*tau0*u)
            PR += -LAMV[n_]/np.sqrt(n_)*(phz*Am + np.conj(phz)*Am.T)
        return PR

    def pole_vecs(self, tau0):
        PXc = self.psi_x(XG).astype(complex)
        u = A*np.einsum('ni,i->n', PXc, WG*np.exp(((-1j*tau0 - 0.5)*A)*XG))
        v = A*np.einsum('ni,i->n', PXc, WG*np.exp(((-1j*tau0 + 0.5)*A)*XG))
        return u, v

    def weil_margin(self, tau0, Rwin=800.0, NR=120001):
        from fold_surrogate import psi_hat_batch
        r = np.linspace(tau0 - Rwin, tau0 + Rwin, NR)
        F = psi_hat_batch(self.P, (r - tau0)*A)*A
        ker = np.real(scipy_digamma(0.25 + 0.5j*r)) - np.log(np.pi)
        dr = r[1] - r[0]
        ARCH = (F*ker[None, :]) @ F.conj().T * dr/(2*np.pi)
        u, v = self.pole_vecs(tau0)
        Mp = np.outer(np.conj(v), u)
        Q = ARCH + Mp + Mp.conj().T + self.prime_mat(tau0)
        Q = (Q + Q.conj().T)/2
        ev, V = scipy_eigh(Q, self.G)
        return float(ev[0]), V[:, 0]

    def zero_side_on(self, w, zeros, tau0):
        s = np.concatenate([(zeros - tau0)*A, (-zeros - tau0)*A])
        Vb = np.asarray(self.vhat(s.astype(complex)))
        if Vb.shape[0] != len(s):
            Vb = Vb.T
        amps = Vb @ w.astype(complex)
        return float(np.sum(np.abs(amps)**2))

    def overlap_deriv(self, w, tau0, gamma0, eps=1e-5):
        s0 = (gamma0 - tau0)*A
        vp = self.vhat(complex(s0 + eps, 0.0))
        vm = self.vhat(complex(s0 - eps, 0.0))
        dv = (vp - vm)/(2*eps)
        return abs(np.vdot(w.astype(complex), dv))


if __name__ == "__main__":
    Z = zeros380()
    pts = [(60.0, 200.0), (120.0, 260.0), (60.0, 280.0), (120.0, 300.0)]
    sects = {}
    for c, t0 in pts:
        if c not in sects:
            sects[c] = TwoSided(c)
        S = sects[c]
        mW, w = S.weil_margin(t0)
        nrm = float(np.real(np.conj(w) @ S.G @ w))
        mZ = S.base_margin(Z, t0)
        ratios = []
        for N in (260, 320, 380):
            zN = S.zero_side_on(w, Z[:N], t0)
            ratios.append(zN/(mW*nrm) if mW > 0 else float('nan'))
        k = int(np.argmin(np.abs(Z - t0)))
        ov = S.overlap_deriv(w, t0, Z[k])
        eps_budget = abs(mW*nrm - S.zero_side_on(w, Z, t0))
        d_bound = math.sqrt(max(mW*nrm, 0) + eps_budget)/(A*ov) if ov > 0 else float('inf')
        print(f"c={c:4.0f} t0={t0:4.0f}: m_W {mW:+.3e}  m_Z {mZ:.3e}  "
              f"ratios(260/320/380) {ratios[0]:.4f}/{ratios[1]:.4f}/"
              f"{ratios[2]:.4f}  ov {ov:.3e}  d_bound {d_bound:.3e}",
              flush=True)
