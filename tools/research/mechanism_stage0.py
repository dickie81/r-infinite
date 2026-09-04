"""THE MECHANISM PROOF, STAGE 0 (owner: "Do the mechanism proof over the
one-prime window"): float64 feasibility of a Slepian-concentration LOWER
bound on the one-prime Weil form, uniform over all probes.

For probes g of support a = delta/2 (type a), with ghat = Fourier transform,
the one-prime form is  Q(g) = (1/2pi) int |ghat|^2 W dr +/- 2 <chi, g>^2,
W = W_inf - C2 cos(r log 2).  Fix a bandwidth Omega beyond the kernel's last
negative piece and put  W_out = inf_{|r| >= Omega} W > 0  (W_inf increases
for r > 0, so W_out >= W_inf(Omega) - C2).  Then, for EVERY g,

   Q(g) >= <g, M g>,   M = A_in + W_out (I - K) +/- 2 chi chi^T,

A_in the form (1/2pi) int_{|r|<=Omega} |ghat|^2 W, K the Slepian concentration
operator of (a, Omega) (PSD, K <= I).  In the prolate basis {phi_k} of
L^2[-a,a] (the eigenfunctions of K, K phi_k = lambda_k phi_k, doubly
orthogonal), split head (k <= n) / tail (k > n):
   * the tail block of M is >= q_perp = W_out (1 - lambda_{n+1})
                                        - M_W lambda_{n+1} - [odd: 2 |chi_tail|^2],
     M_W = max_{[-Omega,Omega]} |W|  (|A_in(phi_j, phi_k)| <= M_W sqrt(lambda_j lambda_k));
   * the head-tail coupling is <= b = M_W sqrt(lambda_{n+1}) + 2 |c_head| |c_tail|;
   * hence  lambda_min(M) >= lambda_min([[lambda_min(M_head), -b], [-b, q_perp]]).
If that is > 0 the form is positive at delta for ALL probes -- by the
uncertainty principle (Slepian) and a finite matrix, no Temple trial, no
Birman-Schwinger count, no zeros.  Stage 0 measures the bound in float64
against the margin curve; Stage 1 would make every quantity an enclosure.

PSWFs: Legendre-tridiagonal (Xiao-Rokhlin-Yarvin) for c = a Omega, per
parity; Fourier transforms by the Legendre-Bessel identity
  int_{-1}^{1} e^{i c x y} P_n(y) dy = 2 i^n j_n(c x).
Usage: mechanism_stage0.py Omega [deltas...]
"""
import sys, math, json
import numpy as np
from scipy.special import digamma, spherical_jn
from scipy.linalg import eigh_tridiagonal, eigh

C2 = math.sqrt(2)*math.log(2)
def W_of(r):
    r = np.asarray(r, float)
    return digamma(0.25 + 0.5j*r).real - math.log(math.pi) - C2*np.cos(r*math.log(2))
def W_inf(r):
    return digamma(0.25 + 0.5j*r).real - math.log(math.pi)

def pswf(c, parity, nmax):
    """Legendre coefficients (normalized Legendre on [-1,1]) of the PSWFs of
    parity 'even'/'odd' for bandwidth-interval product c, ordered by
    increasing differential eigenvalue chi (= decreasing concentration).
    Returns coeff matrix (K x nmax) over ALL Legendre indices (zeros for
    the other parity)."""
    ns = np.arange(0 if parity == "even" else 1, nmax, 2)
    diag = ns*(ns + 1) + c*c*(2*ns*ns + 2*ns - 1)/((2*ns + 3)*(2*ns - 1))
    off = c*c*(ns[:-1] + 2)*(ns[:-1] + 1)/((2*ns[:-1] + 3)*np.sqrt((2*ns[:-1] + 1)*(2*ns[:-1] + 5)))
    chi, V = eigh_tridiagonal(diag, off)
    coeffs = np.zeros((len(ns), nmax))
    coeffs[:, ns] = V.T
    return chi, coeffs, ns

def fourier(coeffs, a, r):
    """ghat_k(r) = int_{-a}^{a} e^{irt} phi_k(t) dt with phi_k(t) = sum_n beta_kn Pbar_n(t/a)
    normalized so that int phi_k^2 dt = 1  (beta with sum beta^2 = 1/a)."""
    nmax = coeffs.shape[1]
    ns = np.arange(nmax)
    J = np.array([spherical_jn(n, r*a) for n in ns])            # nmax x len(r)
    fac = a*np.sqrt((2*ns + 1)/2.0)*2.0*(1j**ns)
    return (coeffs/math.sqrt(a)) @ (fac[:, None]*J)             # K x len(r), complex

def gl(lo, hi, m=24):
    x, w = np.polynomial.legendre.leggauss(m)
    return 0.5*(hi - lo)*x + 0.5*(hi + lo), 0.5*(hi - lo)*w

def panels(lo, hi, width=0.5, m=24):
    edges = np.linspace(lo, hi, int(math.ceil((hi - lo)/width)) + 1)
    xs, ws = zip(*[gl(l, h, m) for l, h in zip(edges[:-1], edges[1:])])
    return np.concatenate(xs), np.concatenate(ws)

def bound(delta, parity, Omega, extra=20, nmax=None):
    a = delta/2; c = a*Omega
    nsh = 2*c/math.pi
    nhead = int(math.ceil(nsh/2)) + extra                        # per parity: half the Shannon number
    nmax = nmax or 2*(nhead + 60) + 40
    chi, coeffs, ns = pswf(c, parity, nmax)
    coeffs = coeffs[:nhead + 1]                                  # head + the first tail function
    # Fourier transforms on [0, Omega] (symmetric) and the concentration
    r, w = panels(0.0, Omega, width=0.5)
    F = fourier(coeffs, a, r)                                    # (nhead+1) x m
    prof = (F*np.conj(F)).real
    lam = 2*(prof @ w)/(2*math.pi)                               # concentration eigenvalues (both signs of r)
    G = 2*((F*w[None, :]) @ np.conj(F).T).real/(2*math.pi)       # concentration Gram (should be diag(lam))
    Wr = W_of(r)
    A = 2*((F*(w*Wr)[None, :]) @ np.conj(F).T).real/(2*math.pi)  # the inside form
    M_W = float(np.max(np.abs(Wr)))
    W_out = W_inf(Omega) - C2
    # the pole vector in t
    t, wt = gl(0.0, a, 200)
    Pn = np.polynomial.legendre.legvander(t/a, coeffs.shape[1] - 1)*np.sqrt((2*np.arange(coeffs.shape[1]) + 1)/2.0)
    phi = (coeffs/math.sqrt(a)) @ Pn.T                           # values on [0, a]
    chi_t = np.cosh(t/2) if parity == "even" else np.sinh(t/2)
    cvec = 2*(phi @ (wt*chi_t))                                  # int_{-a}^{a} phi chi (parity-symmetric)
    sign = +1.0 if parity == "even" else -1.0
    Mfull = A + W_out*(np.eye(nhead + 1) - G) + sign*2*np.outer(cvec, cvec)
    Mh = Mfull[:nhead, :nhead]
    lam_head = float(np.linalg.eigvalsh((Mh + Mh.T)/2)[0])
    lam_next = float(lam[nhead])                                 # concentration of the first tail prolate
    chi_norm2 = 2*float(np.sum(wt*chi_t**2))
    c_tail2 = max(chi_norm2 - float(np.sum(cvec[:nhead]**2)), 0.0)
    q_perp = W_out*(1 - lam_next) - M_W*lam_next - (2*c_tail2 if parity == "odd" else 0.0)
    b = M_W*math.sqrt(max(lam_next, 0.0)) + 2*math.sqrt(float(np.sum(cvec[:nhead]**2))*c_tail2)
    blk = np.array([[lam_head, -b], [-b, q_perp]])
    lam_bound = float(np.linalg.eigvalsh(blk)[0])
    return dict(delta=delta, parity=parity, Omega=Omega, c=c, shannon=nsh, nhead=nhead,
                lam_head=lam_head, lam_next=lam_next, q_perp=q_perp, b=b, bound=lam_bound,
                W_out=W_out, M_W=M_W, gram_offdiag=float(np.max(np.abs(G - np.diag(np.diag(G))))),
                lam0=float(lam[0]), c_tail2=c_tail2)

if __name__ == "__main__":
    Omega = float(sys.argv[1]) if len(sys.argv) > 1 else 100.0
    deltas = [float(s) for s in sys.argv[2:]] or [0.8, 0.9, 1.0, 1.09]
    ref = {("even", 0.8): 1.8144e-4, ("odd", 0.8): 1.4715e-2, ("even", 0.9): 1.6178e-5, ("odd", 0.9): 2.4074e-3,
           ("even", 1.0): 9.4063e-7, ("odd", 1.0): 1.9406e-4, ("even", 1.09): 7.90e-8, ("odd", 1.09): 1.954e-5}
    print(f"Omega {Omega}: W_out = {W_inf(Omega) - C2:.4f}")
    print("delta par | c shannon nhead | lam_head  lam_next  q_perp  b | BOUND | lambda_1 (margin curve) | Gram offdiag")
    for d in deltas:
        for par in ("even", "odd"):
            r = bound(d, par, Omega)
            print(f"{d:5.2f} {par:4s} | {r['c']:6.1f} {r['shannon']:6.1f} {r['nhead']:3d} | {r['lam_head']:+.4e} {r['lam_next']:.2e} {r['q_perp']:+.3f} {r['b']:.2e} | {r['bound']:+.4e} | {ref.get((par, d), float('nan')):+.4e} | {r['gram_offdiag']:.1e}", flush=True)
