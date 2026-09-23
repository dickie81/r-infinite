"""Theorem A (unconditional): lambda*(L) <= Q(Phi_L)/||Phi_L||^2 <= S * e1(L)^2 / ||Phi_L||^2, with
Phi_L = Riemann's kernel truncated to [-L, L], S = 2(197/196) B >= sum_rho 1/gamma_rho^2 (B = 1 + gamma_E/2 - log(4 pi)/2),
e1(L) = 2 [Phi(L) cosh(L/2) + int_L^inf |Phi'(u)| cosh(u/2) du]  (then |E_L(z)| <= e1/|z| on |Im z| <= 1/2)."""
import mpmath as mp, json
mp.mp.dps = 60
def Phi(u, d=0):
    s = mp.mpf(0)
    for n in range(1, 40):
        f = lambda v: (2*mp.pi**2*n**4*mp.e**(4.5*v) - 3*mp.pi*n**2*mp.e**(2.5*v)) * mp.e**(-mp.pi*n**2*mp.e**(2*v))
        s += f(u) if d == 0 else mp.diff(f, u)
    return s
B = 1 + mp.euler/2 - mp.log(4*mp.pi)/2
S = 2 * mp.mpf(197)/196 * B
zhu = {0.5: 13.76, 0.6: 20.13, 0.7: 28.33, 0.8: 38.32, 0.9: 51.18, 1.0: 66.99, 1.1: 86.48, 1.2: 110.53, 1.4: 176.65, 1.6: 276.46, 1.8: 426.22, 2.0: 650.47}
for L in sorted(zhu):
    L_ = mp.mpf(L)
    e1 = 2 * (Phi(L_) * mp.cosh(L_/2) + mp.quad(lambda u: abs(Phi(u, 1)) * mp.cosh(u/2), [L_, L_ + 0.5, L_ + 2]))
    nrm2 = 2 * mp.quad(lambda u: Phi(u)**2, [0, L_])
    bound = S * e1**2 / nrm2
    print(json.dumps(dict(L=L, minus_log_bound=float(-mp.log(bound)), two_pi_e2L=float(2*mp.pi*mp.e**(2*L_)),
        zhu_cert_minus_log=zhu[L], zhu_thm13_exponent=float(L_*mp.e**L_))))
