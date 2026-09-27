"""Kaiser trial, fast form. lam = e^a, eta = 1/lam, mu = lam - 4 eta, beta = 2 pi mu.
H(w) = w^2 (w^2 - alpha) C(w^2 - lam^2) sinc(pi eta w)^8, alpha = m4/m2 (so H(0) = int H = 0).
By Poisson (f = h + H self-dual, h = F^{-1}H supported in [-lam, lam]):
  G(u) = E(H)(e^u) + E(H)(e^{-u}),  E(H)(x) = x^{1/2} sum_n H(n x).
Tail (u > a): G(u) = E(H)(e^u) only (the other part is E(h)(e^u) = 0).  Q = sum_rho |2 int_a^inf G cos(gamma u)|^2."""
import mpmath as mp, sys, json
a = mp.mpf(sys.argv[1]); nz = int(sys.argv[2]); mp.mp.dps = 50
lam = mp.e**a; eta = 1/lam; mu = lam - 4*eta; beta = 2*mp.pi*mu
def C(v): return mp.cos(beta*mp.sqrt(v)) if v >= 0 else mp.cosh(beta*mp.sqrt(-v))
def sinc(x): return mp.sin(x)/x if x != 0 else mp.mpf(1)
def H0(w): return C(w*w - lam*lam)*sinc(mp.pi*eta*w)**8
pts = [0, lam/4, lam/2, lam, 2*lam, 8*lam, mp.inf]
m2 = 2*mp.quad(lambda w: w**2*H0(w), pts); m4 = 2*mp.quad(lambda w: w**4*H0(w), pts)
alpha = m4/m2
def H(w): return w*w*(w*w - alpha)*H0(w)
def EH(x):
    s = 0; n = 1
    while True:
        t = H(n*x); s += t; n += 1
        if n*x > 40*lam and abs(t) < mp.mpf(10)**(-40): break
    return mp.sqrt(x)*s
def G(u): return EH(mp.e**u) + EH(mp.e**(-u))
chk = EH(mp.e**(-(a + mp.mpf('0.3'))))
nodes = 64
U = [(-a + 2*a*k/nodes) for k in range(nodes + 1)]
gv = [G(u) for u in U]
norm2 = mp.fsum(((gv[k]**2 + gv[k+1]**2)/2)*(2*a/nodes) for k in range(nodes))
Z = json.load(open("/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research/checkpoints/zeta_zeros_6700.json"))[:nz]
grid = [a + mp.mpf(k)/200 for k in range(0, 1201)]
tv = [EH(mp.e**u) for u in grid]
Q = 0
for gam in Z:
    vals = [tv[k]*mp.cos(gam*grid[k]) for k in range(len(grid))]
    I = mp.fsum((vals[k] + vals[k+1])/2 for k in range(len(grid)-1))/200
    Q += 2*(2*I)**2
X = mp.pi*mp.e**(2*a)
print(json.dumps({"a": float(a), "X": mp.nstr(X, 5), "alpha": mp.nstr(alpha, 4), "Poisson check E(H)(e^-(a+.3))": mp.nstr(chk, 3),
  "G(0)": mp.nstr(G(0), 4), "norm2": mp.nstr(norm2, 4), "Q": mp.nstr(Q, 4), "-ln RQ": mp.nstr(-mp.log(Q/norm2), 5),
  "4X": mp.nstr(4*X, 5), "lam_dexp 2X-16a": mp.nstr(2*X - 16*a, 5)}), flush=True)
