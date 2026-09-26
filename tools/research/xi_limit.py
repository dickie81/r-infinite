#!/usr/bin/env python3
"""The Xi-limit of the ground state (Theorem 1bu's substrate, the delta -> infinity side). Riemann's
    Xi(t) = xi(1/2 + i t),  xi(s) = (1/2) s (s - 1) pi^{-s/2} Gamma(s/2) zeta(s),
an even real entire function with Hadamard's product Xi(t)/Xi(0) = prod_gamma (1 - t^2/gamma^2) over the zeros
1/2 + i gamma (gamma paired with -gamma; complex gamma if RH fails, the product the same). Functions:
  Xi(t)                         by mpmath (30 digits)
  constants()                   Xi(0), int_R Xi^2 dt, the limit ghat_1(0)^2 = 2 pi Xi(0)^2/int Xi^2, <t^2> under Xi^2,
                                K = 2 + gamma_E - ln 4 pi (Hadamard: sum_rho 1/(rho(1-rho))), 1/sqrt(2K), 2 sqrt(pi K),
                                the curvature -Xi''(0)/(2 Xi(0)) = sum gamma^-2 (not K/2: round 321 F3)
  nodes(mmax)                   the positive zeros of the even orthogonal polynomials P_{2m} of the weight Xi(t)^2 on R
                                (Stieltjes in s = t^2 on Gauss-Legendre nodes of [0, R]), m = 1..mmax
  hadamard_check(t, zeros, N0)  ln[Xi(t)/Xi(0)] against sum_{gamma in the list} ln(1 - t^2/gamma^2) plus the smooth tail
The weight is negligible beyond t = 90 (|Xi(t)| ~ t^{7/4} e^{-pi t/4}: e^{-70} there). Floating point (mpmath, numpy)."""
import math
import numpy as np
import mpmath as mp

EULER = 0.57721566490153286060651209
K_HADAMARD = 2 + EULER - math.log(4*math.pi)
R_CUT = 90.0
NODES = 3000

def Xi(t):
    with mp.workdps(30):
        s = mp.mpc(0.5, t)
        return float((s*(s - 1)/2*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)).real)

def _grid():
    x, wq = np.polynomial.legendre.leggauss(NODES)
    x = 0.5*R_CUT*(x + 1); wq = 0.5*R_CUT*wq
    E = np.array([Xi(t) for t in x])
    return x, wq*E*E

def curvature():
    """-Xi''(0)/(2 Xi(0)) = sum_{gamma > 0} gamma^-2, the curvature of ln Xi at the origin (mpmath, 30 digits); it is not
    K/2 = sum 1/(1/4 + gamma^2) -- the two differ by sum 1/(4 gamma^2 (gamma^2 + 1/4)) = 9.3e-6 (round 321 F3)."""
    with mp.workdps(30):
        f = lambda t: (lambda s: (s*(s - 1)/2*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)).real)(mp.mpc(0.5, t))
        return float(-mp.diff(f, 0, 2)/(2*f(0)))

def constants():
    x, w = _grid()
    X0 = Xi(0.0); I2 = 2*float(np.sum(w)); m2 = float(np.sum(w*x*x)/np.sum(w))
    return {"Xi0": X0, "int_Xi2": I2, "g0sq_limit": 2*math.pi*X0*X0/I2, "t2_mean": m2, "K": K_HADAMARD, "curvature": curvature(),
            "inv_sqrt_2K": 1/math.sqrt(2*K_HADAMARD), "two_sqrt_piK": 2*math.sqrt(math.pi*K_HADAMARD)}

def nodes(mmax, x=None, w=None):
    """the positive zeros of P_{2m}, m = 1..mmax, for the even weight w(t) dt on [0, R] (default Xi^2): the monic
    orthogonal polynomials p_m(s) of the measure w dt in s = t^2, zeros from the Jacobi matrix."""
    if x is None: x, w = _grid()
    s = x*x; al = []; be = []; out = []
    p_prev = np.zeros_like(s); p = np.ones_like(s); nrm_prev = 1.0
    for m in range(mmax + 1):
        nrm = float(np.sum(w*p*p)); a_m = float(np.sum(w*s*p*p)/nrm); b_m = nrm/nrm_prev if m > 0 else 0.0
        al.append(a_m); be.append(b_m)
        if m >= 1:
            J = np.diag(al[:m]) + np.diag(np.sqrt(be[1:m]), 1) + np.diag(np.sqrt(be[1:m]), -1)
            out.append([float(v) for v in np.sqrt(np.maximum(np.linalg.eigvalsh(J), 0))])
        p_next = (s - a_m)*p - b_m*p_prev; p_prev, p, nrm_prev = p, p_next, nrm
    return out

def hadamard_check(t, zeros, N0=None):
    """ln[Xi(t)/Xi(0)] and sum over the listed zeros of ln(1 - t^2/gamma^2) plus the tail -t^2 int_{T}^inf n0(r)/r^2 dr
    with n0 = ln(r/2pi)/(2pi), T the last listed zero (the tail's leading term)."""
    z = np.asarray(zeros, dtype=float); T = float(z[-1])
    s = float(np.sum(np.log(np.abs(1 - t*t/(z*z)))))
    tail = -t*t*(math.log(T/(2*math.pi)) + 1)/(2*math.pi*T)
    return math.log(abs(Xi(t)/Xi(0.0))), s + tail, s

if __name__ == "__main__":
    c = constants()
    print("Xi(0) = %.10f; int Xi^2 = %.6f; limit ghat_1(0)^2 = %.5f; sqrt<t^2> = %.5f; K = %.6f; 1/sqrt(2K) = %.5f; 2 sqrt(pi K) = %.5f"
          % (c["Xi0"], c["int_Xi2"], c["g0sq_limit"], math.sqrt(c["t2_mean"]), c["K"], c["inv_sqrt_2K"], c["two_sqrt_piK"]))
    for m, z in enumerate(nodes(8), start=1):
        print(f"m = {m} (rung {m + 1}): nodes {[round(v, 4) for v in z]}")
def constants_odd():
    """The odd sector's limits: with Ghat_1 -> c Xi and int r^2 Ghat_1^2 = 2 pi, c^2 = 2 pi/int t^2 Xi^2 -- Ghat_1(0)^2 ->
    2 pi Xi(0)^2/int t^2 Xi^2; <r^2> under ghat_1^2 = r^2 Ghat_1^2 -> int t^4 Xi^2/int t^2 Xi^2; the odd anatomy's limits
    (Theorem 1bv(vi)): pole -2 p^2 with p = Ghat(i/2)/2 -> -c^2 xi(0)^2/2, xi(0) = 1/2; primes -2 sum Lambda(n) n^{-1/2} f_g(ln n)
    with f_g = -f_G'' and f_G -> c^2 (Phi*Phi), (Phi*Phi)''(u) = -(1/2 pi) int r^2 Xi^2 cos(ru) dr; the archimedean term the
    remainder to 0 (lambda_1 -> 0); arch_odd_direct and arch_even_direct are the archimedean term computed directly on the same grid,
    (1/2 pi) int |ghat|^2 [Re psi(1/4 + i r/2) - psi(1/4)] dr (the check that the remainder is the archimedean term; on this grid the even sector's residual, 7e-11 at 3000 nodes,
    is the endpoint offset of about 4e-13 in every f(ln n) -- the float64 accuracy of the degree-3000 Gauss-Legendre
    weights at t = 0 (the first weight 2e-7 relative; the nodes exact), where Xi^2 concentrates -- summed with the
    weights Lambda(n) n^{-1/2} over the prime powers and scaled by 2 c^2, while int Xi^2 is good to 2e-12; the odd weight
    t^2 Xi^2 kills the endpoint, residual 1e-13. The 4e-13, the 2e-12 and the first weight's 2e-7 are a session
    decomposition against an mpmath reference (rounds 330-333); the residuals themselves are the instrument's). The even
    sector's limits by the same rule, 1.5637/-5.3722/3.8837/-0.0752, are first computed here (Theorem 1bu records no anatomy limits)."""
    from weil_prime_gram import prime_powers
    x, w = _grid()
    I2 = 2*float(np.sum(w)); I4 = 2*float(np.sum(w*x*x)); I6 = 2*float(np.sum(w*x*x*x*x)); X0 = Xi(0.0)
    const = float(mp.digamma(mp.mpf(1)/4) - mp.log(mp.pi))
    c2o = 2*math.pi/I4; c2e = 2*math.pi/I2
    def phi2(u): return 2*float(np.sum(w*np.cos(x*u)))/(2*math.pi)
    def phi2dd(u): return -2*float(np.sum(w*x*x*np.cos(x*u)))/(2*math.pi)
    pp = prime_powers(200)
    pole_o = -2*(c2o*0.25)/4; primes_o = -2*c2o*sum(math.log(p)/math.sqrt(n)*(-phi2dd(math.log(n))) for n, p in pp)
    pole_e = 2*c2e*0.25; primes_e = -2*c2e*sum(math.log(p)/math.sqrt(n)*phi2(math.log(n)) for n, p in pp)
    psi_re = np.array([float(mp.digamma(mp.mpc(0.25, t/2)).real) for t in x]) - float(mp.digamma(mp.mpf(1)/4))
    arch_o_direct = c2o*2*float(np.sum(w*x*x*psi_re))/(2*math.pi); arch_e_direct = c2e*2*float(np.sum(w*psi_re))/(2*math.pi)
    return {"int_t2_Xi2": I4, "int_t4_Xi2": I6, "G0sq_limit": 2*math.pi*X0*X0/I4, "r2_mean_odd": I6/I4, "const": const,
            "pole_odd": pole_o, "primes_odd": primes_o, "arch_odd": -(pole_o + const + primes_o),
            "pole_even": pole_e, "primes_even": primes_e, "arch_even": -(pole_e + const + primes_e),
            "arch_odd_direct": arch_o_direct, "arch_even_direct": arch_e_direct,
            "prime_terms_odd": [(n, -2*c2o*math.log(p)/math.sqrt(n)*(-phi2dd(math.log(n)))) for n, p in pp[:4]]}

def nodes_odd(mmax):
    """the positive zeros of P_{2m} for the weight t^2 Xi(t)^2 (the odd sector's ladder), m = 1..mmax."""
    x, w = _grid(); return nodes(mmax, x, w*x*x)
