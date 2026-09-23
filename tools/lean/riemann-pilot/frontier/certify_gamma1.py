"""Round 38: a certified slope for the TRUE ground state at delta = 1.6, from Zhu's certified gap.
Usage: python3 certify_gamma1.py K prec [window]   (round 38: 160 800 5e-3).

Named inputs, from Zhu (arXiv 2608.24827, Theorem 6.2, L = 0.8 in his notation, delta = 2L = 1.6):
certified lam1 >= 8.9e-18 and lam2(even) >= 2.085e-12 over all real even f supported in [-0.8, 0.8].
The ground state is simple and even.
1. phi = our computed ground state (cosine basis, K modes). Its Rayleigh quotient rho = Q(phi)/||phi||^2
   is evaluated in balls from the ball Gram: a rigorous upper value for phi itself.
2. Davis-Kahan, elementary form. With phi unit and g the unit ground state (sign chosen so <phi,g> >= 0):
   1 - <phi,g>^2 <= (rho - lam1)/(lam2 - lam1), so ||phi - g||^2 <= 2(rho - lam1_lo)/(lam2_lo - rho).
3. |ghat'(x) - phihat'(x)| <= int |u| |phi - g| du <= sqrt(2a^3/3) ||phi - g||.
4. phihat'(x) is enclosed for every x in the ball gamma_1 +- r by ball arithmetic. Then
   m = min|phihat'| - (step 3) is a certified lower bound for |ghat'| on the window, with fixed sign.
5. Pinning radius eta/m, with eta = sqrt(rho_true + B^2 S_H). This step needs the round-37 inputs
   (verified RH to H, the zero count, the explicit formula) plus monotonicity of g with g(0) <= G.
   g(0) is not controlled by L^2 closeness, so G = 2 (computed value 1.65) is an explicit assumption."""
import sys, json, math
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../research"))
from weil_prime_gram import gram, minimiser, rayleigh
from flint import arb, ctx
import mpmath
mpmath.mp.dps = 50
d, K, p = 1.6, int(sys.argv[1]), int(sys.argv[2])
LAM1_LO, LAM2_LO, LAM1_HI_ZHU = arb('8.9e-18'), arb('2.085e-12'), arb('2.523e-16')
G, N, pp = gram(d, K, p); c, ev = minimiser(G, N, p)
with ctx.workprec(p):
    c = [arb(x) for x in c]
    if c[0] < 0: c = [-x for x in c]
    nrm = sum(N[i] * c[i] * c[i] for i in range(K)).sqrt(); c = [x / nrm for x in c]
    rho = rayleigh(G, N, c, p)                                   # ball; use its upper end
    rho_hi = arb(rho.upper())
    a = arb(d) / 2
    dk2 = 2 * (rho_hi - LAM1_LO) / (LAM2_LO - rho_hi)
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
    H_tail = 7.1e-11 * (2.0 / 1.65) ** 2                         # B^2 S_H with g(0) <= 2 (round 37 had g(0) = 1.65)
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
