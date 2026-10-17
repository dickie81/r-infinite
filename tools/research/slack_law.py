"""THE SLACK LAW (owner: "Derive the slack law").  Research instrument.

Object.  For a real probe g of fixed parity on [-a, a] (delta = 2a), with
ghat(r) = int g(t) e^{irt} dt, the zero side of the explicit formula gives
    Q(g) = sum_gamma |ghat(gamma)|^2         (sum over all zeros 1/2 + i gamma)
(A420: verified equal to the prime-side form to the pipeline's resolution;
unconditional for the verified zeros, which is all a probe of these
supports can feel).  lambda_1(delta) = min_{||g||=1} Q(g).

Derivation, in steps this script tests numerically:
  (1) HORIZON.  The zeros have local density (1/2pi) log(|r|/2pi) on the
      line; a function of exponential type a has Nyquist density a/pi.
      Below T0 = 2 pi e^delta the zeros are sub-Nyquist and ghat can vanish
      at all of them; above T0 it cannot: the dodging horizon (1az-1bb).
  (2) LEAKAGE.  Vanishing at the K = 2N(T) zeros below T <= T0 costs K
      degrees of freedom; the most concentrated type-a function on [-T, T]
      orthogonal to K evaluation functionals has band concentration at most
      lambda_K(c), c = aT (the K-th prolate eigenvalue -- the K constraints
      consume the K most concentrated directions: a modelling step, tested
      here).  Its mass beyond T is 1 - lambda_K(c) and sits near the band
      edge, where the zero density is (1/2pi) log(T/2pi), so
          Q >= ~ (1 - lambda_K(aT)) * log(T/2pi)          (||ghat||^2 = 2pi).
  (3) OPTIMUM.  lambda_1(delta) ~ min over T of the right-hand side; the
      minimiser sits at T_eff = theta T0.  Fuchs / Landau-Widom asymptotics
      then give the rate:  ln lambda_1 ~ -2 c_eff + O(ln c_eff),
      c_eff = a T_eff = pi theta delta e^delta.
The script computes (A) the exact zero-side lambda_1(delta) on a delta grid
(2000 verified zeros, Legendre basis, both parities), (B) the model
min_T (1 - lambda_K(aT)) log(T/2pi) with exact prolate eigenvalues, (C)
theta(delta) from the ground state's band mass, and (D) the fitted rate
against e^delta and delta e^delta.

Usage: slack_law.py [deltas...]
"""
import sys, math, json, os
import numpy as np
from scipy.special import spherical_jn
from scipy.linalg import eigh, eigh_tridiagonal

HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = json.load(open(os.path.join(HERE, "checkpoints", "zeta_zeros_2000.json")))
ZEROS = np.array(ZEROS)

def legendre_fourier(a, r, nmax, parity):
    """ghat_n(r) for the orthonormal basis phi_n(t) = sqrt((2n+1)/(2a)) P_n(t/a):
    ghat_n(r) = sqrt((2n+1)/(2a)) * a * 2 i^n j_n(a r)."""
    ns = np.arange(0 if parity == "even" else 1, nmax, 2)
    J = np.array([spherical_jn(n, a*r) for n in ns])                  # len(ns) x len(r)
    fac = np.sqrt((2*ns + 1)/(2*a))*a*2.0
    ph = np.array([1j**n for n in ns])
    return (fac*ph)[:, None]*J, ns

def zero_side(delta, parity, nmax=None, nz=None):
    """lambda_1 of Z = 2 sum_{gamma <= gmax} Re ghat_j ghat_k^* + the smooth tail
    (1/2pi) int_{|r| > gmax} ghat_j ghat_k^* log(|r|/2pi) dr  (the zeros beyond the
    list replaced by their density -- without it the truncated problem can hide
    mass beyond the last zero)."""
    a = delta/2
    zs = ZEROS if nz is None else ZEROS[:nz]
    c0 = a*2*math.pi*math.exp(delta)
    nmax = nmax or 2*(int(2*c0/math.pi) + 35)
    G, ns = legendre_fourier(a, zs, nmax, parity)
    Z = 2*np.real(G @ np.conj(G).T)
    gmax = zs[-1]
    # tail: panels on [gmax, 200 gmax], log-spaced
    edges = np.geomspace(gmax, 200*gmax, 60)
    xg, wg = np.polynomial.legendre.leggauss(24)
    rs = np.concatenate([0.5*(hi - lo)*xg + 0.5*(hi + lo) for lo, hi in zip(edges[:-1], edges[1:])])
    ws = np.concatenate([0.5*(hi - lo)*wg for lo, hi in zip(edges[:-1], edges[1:])])
    Gt, _ = legendre_fourier(a, rs, nmax, parity)
    dens = np.log(rs/(2*math.pi))/(2*math.pi)
    Z = Z + 2*np.real((Gt*(ws*dens)[None, :]) @ np.conj(Gt).T)
    w, V = eigh((Z + Z.T)/2)
    return w[0], V[:, 0], ns, a

def prolate_lams(c, parity, kmax, nmax=None):
    """Concentration eigenvalues lambda_0..lambda_kmax of the (a, Omega) pair with
    a Omega = c, by the Legendre tridiagonal + numerical band integral."""
    nmax = nmax or int(2*c) + 120
    ns = np.arange(0 if parity == "even" else 1, nmax, 2)
    diag = ns*(ns + 1) + c*c*(2*ns*ns + 2*ns - 1)/((2*ns + 3)*(2*ns - 1))
    off = c*c*(ns[:-1] + 2)*(ns[:-1] + 1)/((2*ns[:-1] + 3)*np.sqrt((2*ns[:-1] + 1)*(2*ns[:-1] + 5)))
    chi, V = eigh_tridiagonal(diag, off)
    V = V[:, :kmax + 1]
    # band integral of |psi_k hat|^2 over [-1, 1] in x = r/Omega with a = 1, Omega = c
    x, wq = np.polynomial.legendre.leggauss(400)
    x = 0.5*(x + 1); wq = 0.5*wq                                       # [0, 1], doubled below
    J = np.array([spherical_jn(n, c*x) for n in ns])                   # len(ns) x 400
    fac = np.sqrt((2*ns + 1)/2.0)*2.0
    F = (fac[:, None]*J).T @ V                                         # 400 x (kmax+1)   (phases drop in |.|^2)
    lam = 2*(wq @ (F*F))*c/(2*math.pi)
    return np.clip(lam, 0, 1)

def model(delta, parity, Ts):
    a = delta/2
    out = []
    for T in Ts:
        K = 2*int(np.sum(ZEROS < T))
        c = a*T
        lam = prolate_lams(c, parity, K + 1)
        lk = lam[K] if K < len(lam) else lam[-1]
        out.append((T, K, c, (1 - lk)*math.log(T/(2*math.pi))))
    return out

def band_mass(vec, ns, a, T, parity):
    """fraction of ||ghat||^2 = 2pi inside |r| <= T for the ground state."""
    r, w = np.polynomial.legendre.leggauss(2000)
    r = 0.5*T*(r + 1); w = 0.5*T*w
    G, _ = legendre_fourier(a, r, ns[-1] + 2, parity)
    gh = vec @ G
    return 2*float(w @ np.abs(gh)**2)/(2*math.pi)

if __name__ == "__main__":
    deltas = [float(s) for s in sys.argv[1:]] or [0.8, 1.0, 1.09375, 1.2, 1.3828125, 1.5, 1.7, 1.9, 2.1, 2.3]
    print(f"{'delta':>8} {'par':>4} {'lambda_1':>12} {'ln':>8} {'ln/e^d':>8} {'ln/(d e^d)':>10} | {'model':>10} {'T_eff':>7} {'theta':>6} {'K':>4} {'c_eff':>7} | {'T50':>7} {'T90':>7}")
    for d in deltas:
        for par in ("even", "odd"):
            lam1, vec, ns, a = zero_side(d, par)
            T0 = 2*math.pi*math.exp(d)
            Ts = np.linspace(0.3*T0, 1.2*T0, 46)
            m = model(d, par, Ts)
            Tbest, Kbest, cbest, mbest = min(m, key=lambda t: t[3])
            # the ground state's band mass: T at which 50% / 90% of |ghat|^2 lies inside
            def mass(T): return band_mass(vec, ns, a, T, par)
            Tg = np.linspace(0.2*T0, 3*T0, 60); ms = [mass(T) for T in Tg]
            T50 = float(np.interp(0.5, ms, Tg)); T90 = float(np.interp(0.9, ms, Tg))
            ln = math.log(lam1)
            print(f"{d:8.4f} {par:>4} {lam1:12.4e} {ln:8.2f} {ln/math.exp(d):8.3f} {ln/(d*math.exp(d)):10.3f} | {mbest:10.3e} {Tbest:7.2f} {Tbest/T0:6.3f} {Kbest:4d} {cbest:7.2f} | {T50:7.2f} {T90:7.2f}", flush=True)
