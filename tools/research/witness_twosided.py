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
       a CORE-LOCAL in-band zero -- one inside the concentrated
       probes' ppm response radius (|gamma - tau0| <~ 20 at
       (120,300), the support edge ~41.5; the collision response
       coefficient collapses off-center, round-229 F1 / round-230
       F4): (d A)^2 |<w, dv/ds>|^2 <= m_W + budget.

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

    def build_QW(self, tau0, Rwin=800.0, NR=120001):
        from fold_surrogate import psi_hat_batch
        r = np.linspace(tau0 - Rwin, tau0 + Rwin, NR)
        F = psi_hat_batch(self.P, (r - tau0)*A)*A
        ker = np.real(scipy_digamma(0.25 + 0.5j*r)) - np.log(np.pi)
        dr = r[1] - r[0]
        ARCH = (F*ker[None, :]) @ F.conj().T * dr/(2*np.pi)
        u, v = self.pole_vecs(tau0)
        Mp = np.outer(np.conj(v), u)
        PRIME = self.prime_mat(tau0)
        Q = ARCH + Mp + Mp.conj().T + PRIME
        Q = (Q + Q.conj().T)/2
        self.QW, self.ARCH, self.PRIME = Q, ARCH, PRIME
        return Q

    def weil_margin(self, tau0, Rwin=800.0, NR=120001):
        Q = self.build_QW(tau0, Rwin, NR)
        ev, V = scipy_eigh(Q, self.G)
        return float(ev[0]), V[:, 0]

    def slepian_leakage(self):
        """1 - lambda_k for the section's prolates (sinc kernel)."""
        PX = self.psi_x(XG)
        D = XG[:, None] - XG[None, :]
        K = np.where(np.abs(D) < 1e-12, self.c/np.pi,
                     np.sin(self.c*D)/(np.pi*np.where(np.abs(D) < 1e-12,
                                                      1.0, D)))
        lam = np.array([(PX[n]*WG) @ K @ (PX[n]*WG)/((PX[n]*WG) @ PX[n])
                        for n in range(self.n)])
        return 1.0 - lam

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


def concentrated_witness(S, Z, tau0, ktop=8):
    """The honest two-sided witness on leakage-bounded vectors: for
    the top-k prolates (Slepian eigenvalue ~ 1, out-of-band leakage
    1 - lambda_k exponentially small), T_k = <psi_k, Q_W psi_k> -
    z_380(psi_k) must equal tail + numerics; a core-local off-line
    zero at distance d would shift T by ~ -(dA)^2 |<psi_k, v'>|^2.
    Returns per-k: T_k, the Slepian leakage bound, z, qw. (The
    earlier d_probe branch -- the single-donor injection -- is
    removed: superseded by collision_probe, whose two-donor topology
    fixed the single-donor doubling artifact; round-229 c3.)"""
    if not hasattr(S, "QW"):
        S.build_QW(tau0)
    out = []
    ei = np.eye(S.n)
    for k in range(ktop):
        w = ei[:, k]/math.sqrt(S.G[k, k])       # G ~ A I: unit G-norm
        qw = float(np.real(np.conj(w) @ S.QW @ w))
        z = S.zero_side_on(w, Z, tau0)
        out.append((k, qw, z, qw - z))
    return out


def collision_probe(S, Z, tau0, w, d):
    """The honest off-line injection: TWO adjacent in-band donors
    (gamma_k, gamma_k+1) collide to the off-line pair at their mean
    (gbar, +-d) [quadruplet with the -gbar mirror]. Returns the
    injected T minus the base T (the pure off-line response; even in
    d, O(d^2) with the collision-limit baseline at d = 0)."""
    kz = int(np.argmin(np.abs(Z - tau0)))
    g1, g2 = Z[kz], Z[kz + 1]
    gbar = 0.5*(g1 + g2)
    Zp = np.delete(Z, [kz, kz + 1])
    z = S.zero_side_on(w, Zp, tau0)
    for g in (gbar, -gbar):
        s0 = (g - tau0)*A
        vm = S.vhat(complex(s0, -d*A))
        vp = S.vhat(complex(s0, +d*A))
        z += 2*float(np.real(np.vdot(w.astype(complex), vm.conj())
                             * np.vdot(vp.conj(), w.astype(complex))))
    z_base = S.zero_side_on(w, Z, tau0)
    return z_base - z    # T_injected - T_base = z_base - z_injected


def jitter_budget(S, Z, tau0, w, scale=2e-11, nreal=8, seed=5):
    """Empirical |T| budget from ordinate uncertainty: rms of the
    zero-side response to Gaussian ordinate jitter at the dps-13
    worst-case absolute scale."""
    rng = np.random.default_rng(seed)
    z0 = S.zero_side_on(w, Z, tau0)
    dz = [S.zero_side_on(w, Z + rng.standard_normal(len(Z))*scale, tau0) - z0
          for _ in range(nreal)]
    return float(np.std(dz))


def landing_stage(dstar_tol=1e-6,
                  pts=((60.0, 200.0), (120.0, 260.0),
                       (60.0, 280.0), (120.0, 300.0))):
    """The 1bf verifier's staged compute, relocated here from the
    verifier so the producing code is itself content-addressed into
    the checkpoint key via this module's sha (round-229 F7: the
    verifier's in-file stage body was not keyed -- an edit to it
    would have reused a stale checkpoint). Per point: the Weil
    margin with its ARCH/PRIME decomposition, the on-line base
    margin, the dodging minimizer's truncation tail, the
    concentrated-identity rows, and per top-8 prolate the jitter
    budget, collision response, alarm, and d_bound; for the
    best-bound prolate additionally the 1e-9-scale jitter rms
    (the linearity census, round-229 F4) and the dodging-instrument
    d* at the honest tolerance."""
    from witness_offline import dstar
    Z = zeros380()
    out = {"pts": []}
    sects = {}
    for c, t0 in pts:
        if c not in sects:
            sects[c] = TwoSided(c)
        S = sects[c]
        mW, wW = S.weil_margin(t0)
        arch = float(np.real(np.conj(wW) @ S.ARCH @ wW))
        prime = float(np.real(np.conj(wW) @ S.PRIME @ wW))
        mZ = S.base_margin(Z, t0)
        # dodging minimizer for the tail measurement
        s = np.concatenate([(Z - t0)*A, (-Z - t0)*A])
        Vb = np.asarray(S.vhat(s.astype(complex)))
        if Vb.shape[0] != len(s):
            Vb = Vb.T
        QZ = Vb.conj().T @ Vb
        QZ = (QZ + QZ.conj().T)/2
        evz, VZ = scipy_eigh(QZ, S.G)
        wZ = VZ[:, 0]
        tail = float(np.real(np.conj(wZ) @ S.QW @ wZ))
        rows = concentrated_witness(S, Z, t0, ktop=8)
        leak = S.slepian_leakage()
        Tmax = max(abs(r[3]) for r in rows)
        per_k = []
        for k, qw, z, T in rows:
            w = np.eye(S.n)[:, k]/math.sqrt(S.G[k, k])
            bud = jitter_budget(S, Z, t0, w)
            rP = collision_probe(S, Z, t0, w, 1e-3)
            rM = collision_probe(S, Z, t0, w, -1e-3)
            r0 = collision_probe(S, Z, t0, w, 1e-6)
            resp2 = abs(rP - r0)/((1e-3*A)**2)
            alarm = abs(collision_probe(S, Z, t0, w, 2e-3) - r0)
            even_rel = abs(rP - rM)/max(abs(rP), 1e-30)
            db = math.sqrt((abs(T) + bud)/resp2)/A if resp2 > 0 else None
            per_k.append({"k": k, "T": T, "bud": bud, "resp2": resp2,
                          "db": db, "even_rel": even_rel, "alarm": alarm})
        best = min((p for p in per_k if p["db"]), key=lambda p: p["db"])
        kb = best["k"]
        wb = np.eye(S.n)[:, kb]/math.sqrt(S.G[kb, kb])
        best["bud9"] = jitter_budget(S, Z, t0, wb, scale=1e-9)
        best["lin_ratio"] = best["bud9"]/best["bud"]
        ds = dstar(S, Z, t0, t0, tol=dstar_tol)
        out["pts"].append({
            "c": c, "t0": t0, "mW": mW, "arch": arch, "prime": prime,
            "mZ": mZ, "tail": tail, "Tmax": Tmax,
            "leak_max": float(leak[:8].max()), "best": best,
            "dstar": ds, "consist_rel": None})
    # consistency at the first point's bandwidth
    S = sects[pts[0][0]]
    m_ref = S.margin(Z, pts[0][1])
    m_cpx = S.base_margin(Z, pts[0][1])
    out["consist_rel"] = abs(m_ref - m_cpx)/m_ref
    return out


def final_report():
    Z = zeros380()
    pts = [(60.0, 200.0), (120.0, 260.0), (60.0, 280.0), (120.0, 300.0)]
    sects = {}
    for c, t0 in pts:
        if c not in sects:
            sects[c] = TwoSided(c)
        S = sects[c]
        mW, wW = S.weil_margin(t0)
        leak = S.slepian_leakage()
        rows = concentrated_witness(S, Z, t0, ktop=8)
        Tmax = max(abs(r[3]) for r in rows)
        print(f"\nc={c:4.0f} t0={t0:4.0f}: m_W {mW:+.3e}  "
              f"max|T| over k<8: {Tmax:.2e}  leak {leak[:8].max():.1e}",
              flush=True)
        best = None
        for k, qw, z, T in rows:
            w = np.eye(S.n)[:, k]/math.sqrt(S.G[k, k])
            bud = jitter_budget(S, Z, t0, w)
            # response coefficient from the collision probe at two ds
            r1 = collision_probe(S, Z, t0, w, 1e-3) - collision_probe(S, Z, t0, w, 1e-6)
            resp2 = abs(r1)/((1e-3*A)**2) if abs(r1) > 0 else 0.0
            if resp2 <= 0:
                continue
            db = math.sqrt((abs(T) + bud)/resp2)/A   # resp2 is per (dA)^2
            if best is None or db < best[1]:
                best = (k, db, bud, resp2, abs(T))
        print(f"  best k={best[0]}: d_bound {best[1]:.3e}  "
              f"(|T| {best[4]:.1e}, jitter budget {best[2]:.1e}, "
              f"resp2 {best[3]:.3e})", flush=True)


if __name__ == "__main__":
    final_report()
