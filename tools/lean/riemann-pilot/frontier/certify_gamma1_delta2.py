"""Round 39: certified slope and pinning at gamma_1 for the TRUE ground state at delta = 2 (L = 1),
from our own certified eigenvalue bounds (gap_L1/: lam1_even >= 5.192e-30, lam2_even >= 1.8854e-23).
Same five steps as certify_gamma1.py, with the sharper Davis-Kahan form
sin^2 theta <= (rho - lam1_lo)/(lam2_lo - lam1_lo), ||phi - g||^2 <= 2 sin^2 theta.
Usage: python3 certify_gamma1_delta2.py K prec [window]   (round 39: 240 1000 5e-3).
Step 5 still assumes g non-increasing on [0, a] with g(0) <= 2 (computed 1.62), plus the round-37 inputs."""
import sys, json, math
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../research"))
from weil_prime_gram import gram, minimiser, rayleigh
from flint import arb, ctx
import mpmath
mpmath.mp.dps = 50
d, K, p = 2.0, int(sys.argv[1]), int(sys.argv[2])
LAM1_LO, LAM2_LO = arb('5.192e-30'), arb('1.8854e-23')   # minus eps_B < 1e-130: absorbed below
LAM1_LO = LAM1_LO - arb('1e-120')
G, N, pp = gram(d, K, p); c, ev = minimiser(G, N, p)
with ctx.workprec(p):
    c = [arb(x) for x in c]
    if c[0] < 0: c = [-x for x in c]
    nrm = sum(N[i] * c[i] * c[i] for i in range(K)).sqrt(); c = [x / nrm for x in c]
    rho = rayleigh(G, N, c, p)                                   # ball; use its upper end
    rho_hi = arb(rho.upper())
    a = arb(d) / 2
    dk2 = 2 * (rho_hi - LAM1_LO) / (LAM2_LO - LAM1_LO)
    dist = arb(dk2.upper()).sqrt()                               # ||phi - g|| upper bound
    slope_err = (2 * a ** 3 / 3).sqrt() * dist
    om2 = [(arb(k) * arb.pi() / a) ** 2 for k in range(K)]
    sg = [c[k] if k % 2 == 0 else -c[k] for k in range(K)]
    def dgh(r):
        S = arb(0); D = arb(0)
        for k in range(K):
            dd = r * r - om2[k]; S += sg[k] * r / dd; D += sg[k] * (-(r * r + om2[k])) / (dd * dd)
        return 2 * (a * (r * a).cos() * S + (r * a).sin() * D)
    out = dict(delta=d, K=K, rho=[float(rho.lower()), float(rho.upper())], dist_phi_g=float(dist.upper()),
               slope_err=float(slope_err.upper()), zeros=[])
    H_tail = (2 * 2.0 * math.cosh(1.0 / 2)) ** 2 * 5.7067e-12             # B^2 S_H, B = 2 g(0) cosh(a/2), g(0) <= 2
    for j in (1, 2):
        gm = mpmath.zetazero(j).imag
        rad = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-3
        ball = arb(mpmath.nstr(gm, 40), rad)
        enc = dgh(ball)                                          # encloses phihat' on [gamma - r, gamma + r]
        lo, hi = float(enc.lower()), float(enc.upper())
        fixed_sign = lo > 0 or hi < 0
        mmin = min(abs(lo), abs(hi)) if fixed_sign else 0.0
        m = mmin - float(slope_err.upper())
        eta = math.sqrt(float(rho_hi.upper()) + H_tail)
        rec = dict(j=j, gamma=float(gm), window=rad, phihatprime_enclosure=[lo, hi], m_certified=m)
        if m > 0:
            rec['pin_radius'] = eta / m
            rec['window_ok'] = eta / m <= rad
        out['zeros'].append(rec)
print(json.dumps(out))
