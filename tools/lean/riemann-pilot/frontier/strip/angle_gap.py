"""Round 62: the ground state g_a against Riemann's kernel Phi_a = Phi 1_[-a,a] in the paper's Gram.

For each support: lambda_1, lambda_2 (generalised eigenvalues of G v = lam N v), the Rayleigh
quotient R(Phi_a) of the projection of Phi_a on the K cosine modes, sin(theta) between g_a and
Phi_a, and rho = (R(Phi_a) - lambda_1)/(lambda_2 - lambda_1) >= sin^2(theta) (min-max).
Strip criterion (round 62): RH follows if sin(theta_a) sqrt(a) e^{a/2} -> 0."""
import sys, json, os, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
from weil_prime_gram import gram
from flint import arb, acb, arb_mat, acb_mat, ctx
import mpmath as mp

d, K, prec = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
a = d / 2
t0 = time.time()
G, N, pp = gram(d, K, prec)
t1 = time.time()
with ctx.workprec(prec):
    D = arb_mat(K, K)
    for i in range(K): D[i, i] = 1 / N[i].sqrt()
    Gs = D * G * D
    E, R = acb_mat(Gs.mid()).eig(right=True, algorithm="approx")
    order = sorted(range(K), key=lambda i: E[i].real.mid())
    lam = [E[i].real.mid() for i in order[:3]]
    # ground state in orthonormal coordinates: y = D^{-1} c
    y = [R[i, order[0]].real.mid() for i in range(K)]
t2 = time.time()
# Riemann's kernel and its cosine coefficients, in orthonormal coordinates
mp.mp.dps = max(50, prec // 12)
def Phi(u):
    u = mp.mpf(u)
    return sum((2 * mp.pi**2 * n**4 * mp.e**(4.5 * u) - 3 * mp.pi * n**2 * mp.e**(2.5 * u))
               * mp.e**(-mp.pi * n**2 * mp.e**(2 * u)) for n in range(1, 12))
am = mp.mpf(d) / 2
# Gauss-Legendre on 2K equal pieces of [0, a]; Phi is evaluated once and reused for every mode
from mpmath.calculus.quadrature import GaussLegendre
deg = 5                                   # 3*2^(deg-1) = 48 nodes per piece
gl = GaussLegendre(mp.mp).calc_nodes(deg, mp.mp.prec)
M = 2 * K
nodes, wts = [], []
for j in range(M):
    lo, hi = am * j / M, am * (j + 1) / M
    for x, w in gl:
        nodes.append((hi - lo) / 2 * x + (hi + lo) / 2); wts.append((hi - lo) / 2 * w)
PhiW = [w * Phi(t) for t, w in zip(nodes, wts)]
def coef(k):
    # c_k = int_{-a}^a Phi cos(k pi t/a) dt = 2 int_0^a
    return 2 * mp.fsum(pw * mp.cos(k * mp.pi * t / am) for pw, t in zip(PhiW, nodes))
cPhi = [coef(k) for k in range(K)]
Nk = [2 * am] + [am] * (K - 1)
z = [cPhi[k] / mp.sqrt(Nk[k]) for k in range(K)]      # orthonormal coordinates of P_K Phi_a
t3 = time.time()
with ctx.workprec(prec):
    zv = arb_mat(K, 1); yv = arb_mat(K, 1)
    for i in range(K):
        zv[i, 0] = arb(mp.nstr(z[i], prec // 3 + 10))
        yv[i, 0] = y[i]
    zz = sum((zv[i, 0]**2 for i in range(K)), arb(0))
    yy = sum((yv[i, 0]**2 for i in range(K)), arb(0))
    yz = sum((yv[i, 0] * zv[i, 0] for i in range(K)), arb(0))
    RPhi = ((zv.transpose() * Gs * zv)[0, 0] / zz).mid()
    cos2 = (yz**2 / (yy * zz)).mid()
    sin2 = (1 - cos2)
    rho = (RPhi - lam[0]) / (lam[1] - lam[0])
    out = dict(delta=d, a=a, K=K, prec=prec,
               lam1=lam[0].str(12, radius=False), lam2=lam[1].str(12, radius=False),
               lam3=lam[2].str(12, radius=False), R_Phi=RPhi.str(12, radius=False),
               sin_theta=float(sin2.sqrt()) if sin2 > 0 else 0.0,
               rho=rho.str(12, radius=False),
               strip_quantity=float((sin2.sqrt() * arb(a).sqrt() * arb(a / 2).exp())) if sin2 > 0 else 0.0,
               times=dict(gram=t1 - t0, eig=t2 - t1, phi=t3 - t2))
print(json.dumps(out), flush=True)
