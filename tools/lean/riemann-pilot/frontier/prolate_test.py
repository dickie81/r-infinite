"""Round 31: does the truncated Weil form nearly commute with a Sturm-Liouville operator?

Slepian's lucky accident: band-limiting to |r| < W on [-a, a] commutes with
  L = -d/dt((a^2 - t^2) d/dt) + W^2 t^2.
Test for a symbol Phi (Gram G from universality.py, cosine basis K = 60): with p = a^2 - t^2
fixed and q(t) = sum_{m<=M} q_m t^{2m}, find the q minimising ||[G^, L^]||_F (G^, L^ in
N-orthonormal coordinates, restricted to the first Ks modes so that truncation matters less).
This is linear least squares in q. Then, in the eigenbasis of L^ (first Ks eigenvectors):
  offdiag = ||offdiag(V^T G^ V)|| / ||V^T G^ V - mean(diag)||   (0 = commuting),
  overlap = max_i |<ground state of G^, v_i>|.
Control 'prolate' (Phi = 1_{|r|>12}) must give q ~ 144 t^2 and small values; that residual is the
truncation floor.
Usage: prolate_test.py <symbol> delta [...]"""
import sys, math, json
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh, sqrtm
sys.path.insert(0, 'debr')
import universality as U
U.RETURN_GRAM = True
K = U.K; M = 4; Ks = 30
def run(name, delta):
    G, N, a = U.ground(name, delta)
    x, w = leggauss(6000); t = a * x; w = a * w
    om = np.arange(K) * math.pi / a
    C = np.cos(np.outer(om, t)); S = np.sin(np.outer(om, t)) * om[:, None]
    P = (S * ((a * a - t * t) * w)) @ S.T
    Qm = [(C * (t ** (2 * m) * w)) @ C.T for m in range(M + 1)]
    Nih = np.diag(1 / np.sqrt(np.diag(N)))
    Gh = Nih @ G @ Nih; Ph = Nih @ P @ Nih; Qh = [Nih @ q @ Nih for q in Qm]
    sub = slice(0, Ks)
    def comm(A, B): return (A @ B - B @ A)[sub, sub].ravel()
    # least squares: comm(Gh, Ph) + sum q_m comm(Gh, Qh_m) = 0
    A = np.stack([comm(Gh, q) for q in Qh[1:]], axis=1); b = -comm(Gh, Ph)
    # scale columns for conditioning
    sc = np.linalg.norm(A, axis=0); qs, *_ = np.linalg.lstsq(A / sc, b, rcond=None); qv = qs / sc
    qv = np.concatenate([[0.0], qv])
    Lh = Ph + sum(qv[m] * Qh[m] for m in range(M + 1))
    res = np.linalg.norm(A @ qv[1:] - b) / np.linalg.norm(b)
    ev, V = eigh(Lh)
    Vs = V[:, :Ks]
    Gt = Vs.T @ Gh @ Vs
    off = Gt - np.diag(np.diag(Gt))
    offdiag = np.linalg.norm(off) / np.linalg.norm(Gt - np.mean(np.diag(Gt)) * np.eye(Ks))
    eg, VG = eigh(Gh); g0 = VG[:, 0]
    ov = np.abs(V.T @ g0); imax = int(np.argmax(ov))
    return dict(symbol=name, delta=delta, q=[float('%.4g' % v) for v in qv], rel_residual=float(res),
                offdiag=float(offdiag), overlap=float(ov[imax]), with_L_eigenvector=imax)
if __name__ == "__main__":
    name = sys.argv[1]
    for d in map(float, sys.argv[2:]):
        print(json.dumps(run(name, d))); sys.stdout.flush()
