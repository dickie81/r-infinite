"""Ground-space dimension of the Davenport-Heilbronn Weil form versus support (round 258 numerics, task 4).

Weil's u-space form for dh, `QDHu` of src/DHBridge.lean, restricted to the even cosine basis
phi_k(u) = cos(k pi u / a) on [-a, a], k = 0..K-1, is the K x K Gram matrix
  G = log(5/pi) N + A + P,
  N_jk = <phi_j, phi_k>  (diagonal: 2a, a, a, ...),
  A_jk = (1/2pi) int phihat_j(r) phihat_k(r) Re psi(3/4 + i r/2) dr   (the archimedean term with the
         psi(3/4)||g||^2 piece included, by ArchShift.arch_termQ),
  P_jk = -2 sum_{n <= e^{2a}} c(n) n^{-1/2} X_jk(log n),  X_jk(u) = (1/2)(xcorr(phi_j, phi_k)(u) + xcorr(phi_k, phi_j)(u)),
with phihat_k(r) = sin((r + k pi/a) a)/(r + k pi/a) + sin((r - k pi/a) a)/(r - k pi/a) and the
cross-correlations in closed form. The negative eigenvalues of the pencil (G, N) are the negative
directions of Q_dh on this K-dimensional subspace: their number is a lower bound for the ground-space
dimension gdim(a), and the lowest eigenvalue is lambda_1^{DH}(2a) of round 165 (frontier/dh/cert.py),
which certified -7.8e-30, -2.24e-7, -0.7028 at delta = 2a = 3.45, 3.6, 4.0 with K = 80.
c(n) is built exactly as `cDH chi5` (src/DHPrime.lean). Numerical, not verified. Usage:
  python3 gdim_scan.py            # validation at delta = 3.45, 3.6, 4.0, then the scan
"""
import numpy as np, math, sys, json
from scipy.special import digamma
from scipy.linalg import eigh

# --- c(n): the coefficients of -dh'/dh, exactly as cDH chi5 --------------------------------------
def coeffs(N):
    chi = {0: 0, 1: 1, 2: 1j, 3: -1j, 4: -1}          # chi5(2) = i
    eps = complex((2*math.sin(2*math.pi/5) + 2j*math.sin(math.pi/5))/math.sqrt(5))
    def aDH(n):
        z = chi[n % 5]; return (1+eps.conjugate())*z + (1+eps)*z.conjugate()
    a1 = aDH(1).real
    u = np.zeros(N+1); u[2:] = [aDH(n).real/a1 for n in range(2, N+1)]
    dinv = np.zeros(N+1); dinv[1] = 1.0
    for n in range(2, N+1):
        s = 0.0
        d = 2
        while d*d <= n:
            if n % d == 0:
                s += u[d]*dinv[n//d]
                if d*d != n: s += u[n//d]*dinv[d]
            d += 1
        s += u[n]*dinv[1]
        dinv[n] = -s
    lm = np.zeros(N+1); lm[1] = 0.0
    for n in range(2, N+1): lm[n] = math.log(n)*u[n]
    c = np.zeros(N+1)
    for d in range(1, N+1):          # c = lm(delta + u) * dinv, with (delta+u)(1) = 1 -> lm[1] = 0
        if lm[d] == 0.0: continue
        c[d::d] += lm[d]*dinv[1:N//d+1]
    return c

# --- the Gram matrix --------------------------------------------------------------------------
def gram(a, K, c, R=None, dr=0.01):
    om = np.arange(K)*math.pi/a
    # norm
    Nm = np.diag([2*a] + [a]*(K-1))
    # archimedean, r-space
    R = R or (om[-1] + 400.0)
    r = np.arange(-R, R + dr/2, dr)
    def phat(k):
        w = om[k]
        with np.errstate(divide='ignore', invalid='ignore'):
            t1 = np.where(np.abs(r + w) < 1e-12, a, np.sin((r + w)*a)/(r + w))
            t2 = np.where(np.abs(r - w) < 1e-12, a, np.sin((r - w)*a)/(r - w))
        return t1 + t2
    Phi = np.vstack([phat(k) for k in range(K)])
    psi_re = digamma(0.75 + 0.5j*r).real
    A = (Phi*(psi_re*dr)) @ Phi.T/(2*math.pi)
    # tail beyond R: |phihat_j phihat_k| <= 4/(r-om)^2 roughly; contributes < 8 log R /(R - om_max)/(2pi) per entry
    # prime side: X_jk(u) = 1/2 [xcorr(j,k)(u) + xcorr(k,j)(u)], xcorr(j,k)(u) = int_{-a}^{a-u} cos(om_j t) cos(om_k (t+u)) dt
    Nmax = int(math.floor(math.exp(2*a)))
    ns = np.array([n for n in range(2, Nmax+1) if c[n] != 0.0])
    ln = np.log(ns); wts = -2*c[ns]/np.sqrt(ns)
    P = np.zeros((K, K))
    for j in range(K):
        for k in range(j, K):
            al, be = om[j], om[k]
            # int_{-a}^{a-u} cos(al t) cos(be t + be u) dt = 1/2 int [cos((al-be)t - be u) + cos((al+be)t + be u)] dt
            def I(al, be, u):
                lo, hi = -a, a - u
                out = np.zeros_like(u)
                d = al - be
                if abs(d) < 1e-14:
                    out += 0.5*(hi - lo)*np.cos(be*u)
                else:
                    out += 0.5*(np.sin(d*hi - be*u) - np.sin(d*lo - be*u))/d
                s = al + be
                if abs(s) < 1e-14:
                    out += 0.5*(hi - lo)*np.cos(be*u)
                else:
                    out += 0.5*(np.sin(s*hi + be*u) - np.sin(s*lo + be*u))/s
                return out
            X = 0.5*(I(al, be, ln) + I(be, al, ln))
            P[j, k] = P[k, j] = np.dot(wts, X)
    G = math.log(5/math.pi)*Nm + A + P
    return G, Nm

def analyse(a, K, c, nshow=4, thresh=-1e-6):
    """negative count (eigenvalues below `thresh`, which discards the numerical zeros of the null modes),
    the lowest eigenvalues, and the ordinate where |ghat| of the lowest eigenvector peaks (its target zero)."""
    G, Nm = gram(a, K, c)
    ev, V = eigh(G, Nm)
    neg = int(np.sum(ev < thresh))
    v = V[:, 0]; om = np.arange(K)*math.pi/a
    r = np.arange(0.0, om[-1] + 50.0, 0.05)
    with np.errstate(divide='ignore', invalid='ignore'):
        Phi = np.vstack([np.where(np.abs(r + w) < 1e-12, a, np.sin((r + w)*a)/(r + w))
                         + np.where(np.abs(r - w) < 1e-12, a, np.sin((r - w)*a)/(r - w)) for w in om])
    gh = np.abs(v @ Phi)
    peaks = []
    for _ in range(3):
        i = int(np.argmax(gh)); peaks.append(round(float(r[i]), 2))
        lo, hi = max(0, i - 40), min(len(gh), i + 40); gh[lo:hi] = 0.0
    return neg, ev[:nshow], peaks

if __name__ == '__main__':
    amax = float(sys.argv[1]) if len(sys.argv) > 1 else 5.0
    c = coeffs(int(math.exp(2*amax)) + 2)
    print("c(2..8) =", [round(float(x), 6) for x in c[2:9]])
    print("validation against frontier/dh/cert_results.jsonl (delta = 2a, K = 80): lowest eigenvalue")
    for delta, ref in [(3.45, -7.8e-30), (3.6, -2.24e-7), (4.0, -0.702768)]:
        neg, ev, peaks = analyse(delta/2, 80, c)
        print(f"  delta={delta}: lowest = {ev[0]:+.6e} (cert.py: {ref:+.3e}), negative count (< -1e-6) = {neg}, |ghat| peaks of the ground state at t = {peaks}", flush=True)
    print("\nscan: a, K, number of eigenvalues below -1e-6, lowest four eigenvalues (Rayleigh quotients Q/||g||^2), ordinates where |ghat| of the ground state peaks")
    print("(off-line zeros of dh below height 180, from README: 85.70, 114.16, 166.48, 176.70)")
    out = []
    for a in np.arange(1.5, amax + 1e-9, 0.25):
        K = int(60*a) + 40          # resolves frequencies up to (K-1) pi/a > 180
        neg, ev, peaks = analyse(a, K, c)
        rec = {"a": round(float(a), 3), "K": K, "neg": neg, "lowest": [float(x) for x in ev], "peaks": peaks}
        out.append(rec)
        print(f"  a={a:5.2f} K={K:4d}  neg={neg:2d}  lowest={['%+.4e' % x for x in ev]}  peaks={peaks}", flush=True)
    with open('gdim_scan_results.jsonl', 'w') as fh:
        for rec in out: fh.write(json.dumps(rec) + "\n")
