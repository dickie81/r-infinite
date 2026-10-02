"""Gauss-Legendre panels on [0, T#] with rigorous per-entry quadrature error bounds.
Bound (Trefethen 2008, Thm 4.5): n-point Gauss on [-1,1], f analytic in the Bernstein ellipse E_rho
with |f| <= M there:  |I - I_n| <= (64/15) M rho^(-2n) / (rho^2 - 1).  On a panel of half-width h: times h.
Integrand of C_nm: (1/pi)(Psi - beta) F_n F_m with F_n(z) = i^n sqrt(2L(2n+1)) j_n(Lz).
 |j_n(w)| <= e^{|Im w|} (Poisson integral, |P_n| <= 1), so |F_n F_m| <= 2L(2nmax+1) e^{2 L b}, b = semi-minor axis.
 |cos(z log k)| <= cosh(b log k).
 The digamma part (1/2)[psi(1/4+iz/2)+psi(1/4-iz/2)] - log pi - beta is bounded on the ellipse boundary by
 acb ball evaluation on a covering of the boundary (maximum modulus; poles at z = +-i(2k+1/2) kept outside)."""
import pickle, math
from flint import arb, acb, ctx
from params import *
ctx.prec = 320
L, cn, AL, T, beta = consts()
nmax = 2 * N - 2
TARGET = arb('1e-60')
def rho_of(u):
    import cmath; s = cmath.sqrt(u * u - 1)
    return max(abs(complex(u + s)), abs(complex(u - s)))
def dig_bound(c, h, rho, arcs=2048):
    old = ctx.prec; ctx.prec = 64   # ball digamma is sharp only at low precision; this is an upper bound
    try:
        return _dig_bound(c, h, rho, arcs)
    finally:
        ctx.prec = old
def _dig_bound(c, h, rho, arcs):
    m = arb(0)
    two_pi = 2 * arb.pi()
    for j in range(arcs):
        th = two_pi * (arb(j) + arb(1) / 2) / arcs
        th = arb(th.mid(), arb.pi() / arcs)           # ball covering [j, j+1] * 2pi/arcs
        e = acb(th.cos(), th.sin())
        z = acb(c) + acb(h) * (acb(rho) * e + e.conjugate() / acb(rho)) / 2
        g = ((acb(0.25) + acb(0, 0.5) * z).digamma() + (acb(0.25) - acb(0, 0.5) * z).digamma()) / 2 - arb.pi().log() - beta
        v = abs(g).upper()
        if not v.is_finite(): return None
        m = v if v > m else m
    return m
out = []
qerr = arb(0)
cache = {}
for (a0, a1) in panels():
    c = (a0 + a1) / 2; h = (a1 - a0) / 2
    rp = min(rho_of(complex(0, s * (2 * k + 0.5)) / h - c / h) for k in range(0, 60) for s in (1, -1))
    best = None
    for frac in [0.3, 0.45, 0.6, 0.75, 0.9]:
        rho = 1 + frac * (rp - 1) if rp < 50 else 1 + frac * 49
        rho = min(rho, 1 + 3.0 * 64 / (2 * h) + 3)  # keep b moderate
        rho_a = arb(rho)
        b = arb(h) * (rho_a - 1 / rho_a) / 2
        Mdig = dig_bound(c, h, rho)
        if Mdig is None: continue
        comb = sum(cc * (b * arb(n).log()).cosh() for n, cc in cn)
        M = (Mdig + comb) * 2 * L * (2 * nmax + 1) * (2 * L * b).exp() / arb.pi()
        pre = arb(h) * 64 / 15 * M / (rho_a ** 2 - 1)
        # need pre * rho^(-2n) <= TARGET
        n = int(math.ceil(float(((pre / TARGET).log() / (2 * rho_a.log())).upper())))
        n = max(n, 8)
        if best is None or n < best[0]:
            best = (n, rho, pre)
    n, rho, pre = best
    err = pre / arb(rho) ** (2 * n)
    qerr += err
    ctx.prec = 4400   # nodes to ~2^-4400: the Bessel recurrence amplifies input radius by up to ~2^(1.5 t)
    if n not in cache:
        cache[n] = [arb.legendre_p_root(n, k, weight=True) for k in range(n)]
    for x, w in cache[n]:
        t = arb(c) + arb(h) * x; wt = arb(h) * w
        out.append((t.mid().man_exp(), t.rad().man_exp(), wt.mid().man_exp(), wt.rad().man_exp()))
    ctx.prec = 320
    print(f"panel [{a0},{a1}] rho_pole={rp:.3f} rho={rho:.3f} n={n} err<={float(err.upper()):.2e}", flush=True)
print("nodes", len(out), "total per-entry quadrature error <=", qerr.upper())
pickle.dump({"nodes": out, "qerr": qerr.upper().man_exp() if hasattr(qerr.upper(),'man_exp') else str(qerr)}, open("nodes.pkl", "wb"))
