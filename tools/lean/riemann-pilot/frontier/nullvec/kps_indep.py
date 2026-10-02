"""Independent u-space evaluation of the explicit-formula matrix (small K) to check kprimeside's closed forms."""
import mpmath as mp, math, sys, kps_chol as C
from flint import ctx
mp.mp.dps = 30
xv = mp.mpf(sys.argv[1]); K = int(sys.argv[2]); a = mp.log(xv)/2
w = [k*mp.pi/a for k in range(K)]
def G(j, k, u):   # (phi_j * phi_k)(u), u >= 0
    if u >= 2*a: return mp.mpf(0)
    return mp.quad(lambda v: mp.cos(w[j]*v)*mp.cos(w[k]*(u - v)), [u - a, a])
def ghat(k, s): return mp.quad(lambda u: mp.cos(w[k]*u)*mp.exp(s*u), [-a, a])
pp = []
for p in [2,3,5,7,11,13]:
    n = p
    while n <= xv + mp.mpf('1e-9'): pp.append((p, n)); n *= p
A = mp.matrix(K, K)
for j in range(K):
    for k in range(j, K):
        G0 = G(j, k, 0)
        arch = -mp.euler*G0 + mp.quad(lambda t: (G0*mp.exp(-t) - mp.exp(-t/4)*G(j, k, t/2))/(1 - mp.exp(-t)), [0, 1, 4*a]) \
               + G0*mp.quad(lambda t: mp.exp(-t)/(1 - mp.exp(-t)), [4*a, mp.inf])
        pole = 2*ghat(j, mp.mpf(1)/2)*ghat(k, mp.mpf(1)/2)
        prim = -2*sum(mp.log(p)/mp.sqrt(n)*G(j, k, mp.log(n)) for p, n in pp)
        A[j, k] = A[k, j] = (pole - mp.log(mp.pi)*G0 + arch + prim)/2
with ctx.workprec(200):
    B = C.build(float(xv), K)
d = max(abs(A[j, k] - mp.mpf(B[j][k].mid().str(40, radius=False))) for j in range(K) for k in range(K))
print("x", xv, "K", K, "max |independent - closed form| =", mp.nstr(d, 5))
for j in range(min(K,4)): print([mp.nstr(A[j, k] - mp.mpf(B[j][k].mid().str(40, radius=False)), 3) for k in range(min(K,4))])
E, Q = mp.eigsy(A)
i = min(range(K), key=lambda i: E[i]); v = Q[:, i]
print("eigenvalues:", [mp.nstr(e, 4) for e in E])
# the same direction on the zero side: sum over the 6700 zeros (+ smooth tail), which is >= 0 by construction
import json
Z = json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json"))
def gh(t): return sum(v[k]*(-1)**k*2*t*mp.sin(t*a)/(t*t - w[k]**2) for k in range(K))
zs = sum(gh(mp.mpf(g))**2 for g in Z)
sg = sum(v[k]*(-1)**k for k in range(K))
tail = sg**2*mp.quad(lambda t: 2*mp.log(t/(2*mp.pi))/(2*mp.pi)/t**2, [Z[-1], mp.inf])
print("min-eigvec: prime-side v^T M v =", mp.nstr(E[i], 5), "| zero side (6700 zeros) =", mp.nstr(zs, 5), "+ tail", mp.nstr(tail, 5), "| sum_k (-1)^k v_k =", mp.nstr(sg, 4))
