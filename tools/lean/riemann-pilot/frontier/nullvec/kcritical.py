#!/usr/bin/env python3
"""Round 173: the critical gap. Terms T_d(z) = S_{d-1}[Xi(z+ib_d)+Xi(z-ib_d)], b_d = kappa(d-2), at z = 0 and z = 10.
Identity used for the explanation (round 142): pi^{-s/2} Gamma(s/2) = 2/S_{s-1}  (S continued in the dimension)."""
import mpmath as mp
mp.mp.dps = 40
S = lambda d: 2*mp.pi**(mp.mpf(d)/2)/mp.gamma(mp.mpf(d)/2)        # area of S^{d-1}
xi = lambda s: s*(s - 1)/2*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
Xi = lambda z: xi(mp.mpf(1)/2 + 1j*z)
def T(d, k, z): b = abs(k*(d - 2)); return S(d)*2*mp.re(xi(mp.mpf(1)/2 + b + 1j*z))   # real z; uses xi(s)=xi(1-s)
print('|T_d| at z=0 for d = 10, 20, 40, 80')
for k in (0.25, 0.5, 0.75, 1.0, 1.25):
    print(' kappa=%.2f' % k, [mp.nstr(abs(T(d, k, 0)), 4) for d in (10, 20, 40, 80)])
# at kappa = 1: T_d(z) = S_{d-1} * 2 Re xi(d - 3/2 + iz); predicted asymptotic ~ C d^{3/4} * zeta(d - 3/2 + iz)
print('kappa=1: |T_d(0)| / d^{3/4}, and the pure-arithmetic remainder (zeta - 1) part:')
for d in (20, 40, 80, 160):
    s = mp.mpf(d) - mp.mpf(3)/2
    arch = S(d)*s*(s - 1)*mp.pi**(-s/2)*mp.gamma(s/2)                    # geometric (Gamma) part
    print('  d=%d' % d, 'T/d^.75 =', mp.nstr(abs(T(d, 1, 0))/mp.mpf(d)**0.75, 6),
          ' S*Gamma-part/d^.75 =', mp.nstr(arch/mp.mpf(d)**0.75, 6), ' zeta(s)-1 =', mp.nstr(mp.zeta(s) - 1, 4))
