#!/usr/bin/env python3
"""SCRATCH (the odd sector): the prime-side Gram of Weil's form in the ODD sine basis on [-a, a], every entry a ball.

THE FORM for a real ODD probe g: with H(r) = ghat(r) ghat(-r) (entire; |ghat|^2 on the line) the explicit formula gives
  Q(g) = sum_gamma |ghat(gamma)|^2 = H(i/2) + H(-i/2) + (psi(1/4) - log pi) ||g||^2 + int_0^inf [f(0) - f(u)] K(u) du
         - 2 sum Lambda(n) n^{-1/2} f(log n),   K(u) = e^{u/2}/sinh u,   f = the autocorrelation (even for either parity);
for odd g, ghat(-r) = -ghat(r) so H(i/2) = -ghat(i/2)^2 with ghat(i/2) = -int g sinh(t/2) dt: THE POLE TERM IS
-2 p^2, p = int g(t) sinh(t/2) dt -- negative, unlike the even sector's +2 (int g cosh(t/2))^2.

THE BASIS. phi_k(t) = sin(omega_k t), omega_k = k pi/a, k = 1..K-1; <phi_j, phi_k> = a delta_jk. Autocorrelation
f_jk(u) = int_{-a+u}^{a} sin(omega_j t) sin(omega_k (t - u)) dt:
  j != k: f_jk(u) = (-1)^{j+k} [omega_j sin(omega_k u) - omega_k sin(omega_j u)]/(omega_j^2 - omega_k^2)
  j = k:  f_kk(u) = [(2a - u) cos(omega_k u) + sin(omega_k u)/omega_k]/2
(the cosine basis has omega_k sin(omega_k u) - omega_j sin(omega_j u), and a minus on the sine term). The archimedean
integrals per k are the same S, C1, U as the even instrument (weil_prime_gram.gram); the pole integral is
p_k = int sin(omega_k t) sinh(t/2) dt = Im[2 sinh((1/2 + i omega_k) a)/(1/2 + i omega_k)].
Transform: ghat_k(r) = i (-1)^k sin(ra) 2 omega_k/(r^2 - omega_k^2); ghat(omega_k) = i a v_k (the Nyquist samples)."""
import sys, os, json, math, time
from flint import arb, acb, arb_mat, acb_mat, ctx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from weil_prime_gram import prime_powers

def gram_odd(delta, K, prec, parts=False):
    """The odd Gram ((K-1) x (K-1) arb_mat, index k-1 for phi_k), the norm diagonal (list of arb) and the prime powers;
    with parts=True also the archimedean part A (arb_mat) so that G = -2 p p^T + const N + A - P_r term by term."""
    with ctx.workprec(prec):
        a = arb(delta)/2; twoa = 2*a
        pi = arb.pi(); half = arb(1)/2; quarter = arb(1)/4
        om = [arb(k)*pi/a for k in range(K)]
        psi_q = quarter.digamma(); tri_q = acb(quarter).polygamma(1).real
        logpi = pi.log()
        z = [acb(quarter, o/2) for o in om]
        psi = [zz.digamma() for zz in z]
        tri = [zz.polygamma(1) for zz in z]
        M = int(prec*math.log(2)/(2*float(delta))) + 4
        T0 = arb(0)
        Tc = [arb(0)]*K; Tuc = [arb(0)]*K; Ts = [arb(0)]*K
        for m in range(M):
            s = arb(2*m) + half
            e = (-twoa*s).exp()
            T0 += 2*e/s
            for k in range(1, K):
                w = acb(s, -om[k]); ew = (-twoa*w).exp(); q = ew/w
                Tc[k] += 2*q.real; Ts[k] += 2*q.imag
                Tuc[k] += 2*(ew*(twoa/w + 1/(w*w))).real
        sM = arb(2*M) + half
        bound = (-twoa*sM).exp()*(twoa + 1)/(sM*(1 - (-2*twoa).exp()))*2
        err = arb(0, bound)
        T0 += err
        for k in range(1, K):
            Tc[k] += err; Ts[k] += err; Tuc[k] += err
        S = [arb(0)]*K; C1 = [arb(0)]*K; U = [arb(0)]*K
        for k in range(1, K):
            S[k] = psi[k].imag - Ts[k]
            C1[k] = (psi[k].real - psi_q) - (T0 - Tc[k])
            U[k] = tri[k].real/2 - Tuc[k]
        P = [arb(0)]*K
        for k in range(1, K):
            w = acb(half, om[k]); P[k] = (2*(w*a).sinh()/w).imag
        pp = prime_powers(int(math.floor(float(twoa.exp()) + 1e-9)))
        pp = [(n, p) for n, p in pp if arb(n).log() < twoa]
        lam = [(arb(n).log(), arb(p).log()/arb(n).sqrt()) for n, p in pp]
        sinl = [[(om[k]*u).sin() for k in range(K)] for u, _ in lam]
        cosl = [[(om[k]*u).cos() for k in range(K)] for u, _ in lam]
        const = psi_q - logpi
        n = K - 1
        G = arb_mat(n, n); N = [a]*n; Am = arb_mat(n, n)
        for j in range(1, K):
            for k in range(j, K):
                if j == k:
                    A = a*C1[k] + U[k]/2 - S[k]/(2*om[k]) + a*T0
                    Pr = arb(0)
                    for i, (u, wgt) in enumerate(lam):
                        Pr += 2*wgt*((twoa - u)*cosl[i][k] + sinl[i][k]/om[k])/2
                    val = -2*P[k]*P[k] + const*a + A - Pr
                else:
                    sg = -1 if (j + k) % 2 else 1
                    den = om[j]*om[j] - om[k]*om[k]
                    A = sg*(om[k]*S[j] - om[j]*S[k])/den
                    Pr = arb(0)
                    for i, (u, wgt) in enumerate(lam):
                        Pr += 2*wgt*sg*(om[j]*sinl[i][k] - om[k]*sinl[i][j])/den
                    val = -2*P[j]*P[k] + A - Pr
                G[j - 1, k - 1] = val; G[k - 1, j - 1] = val; Am[j - 1, k - 1] = A; Am[k - 1, j - 1] = A
        if parts: return G, N, [q for q, _ in pp], Am
        return G, N, [q for q, _ in pp]

def rayleigh_odd(G, N, c, prec):
    with ctx.workprec(prec):
        n = len(c); v = arb_mat(n, 1)
        for i in range(n): v[i, 0] = arb(c[i])
        num = (v.transpose()*G*v)[0, 0]; den = arb(0)
        for i in range(n): den += N[i]*v[i, 0]*v[i, 0]
        return num/den

def minimiser(G, N, prec):
    with ctx.workprec(prec):
        n = G.nrows(); D = arb_mat(n, n)
        for i in range(n): D[i, i] = 1/N[i].sqrt()
        E, R = acb_mat((D*G*D).mid()).eig(right=True, algorithm="approx")
        order = sorted(range(n), key=lambda i: E[i].real.mid())
        return order, E, R, D

def selftest():
    """Q from the odd Gram against 2 sum_gamma |ghat(gamma)|^2 over the 6700 zeros plus the smooth tail for an odd bump."""
    zeros = [float(z) for z in json.load(open("/home/user/r-infinite/tools/research/checkpoints/zeta_zeros_6700.json"))]
    import mpmath as mp
    mp.mp.dps = 40
    for delta, K, prec in ((1.0, 48, 400), (2.0, 80, 400)):
        a = delta/2
        bump = lambda t: t*mp.e**(-1/(1 - (t/a)**2)) if abs(t) < a else mp.mpf(0)      # odd
        c = [mp.quad(lambda t: bump(t)*mp.sin(k*mp.pi*t/a), [-a, 0, a])/a for k in range(1, K)]
        G, N, pp = gram_odd(delta, K, prec)
        q_prime = rayleigh_odd(G, N, [arb(str(x)) for x in c], prec)
        den = sum(a*x**2 for x in c)
        def ghat_over_i(r):      # ghat(r)/i = sum c_k [sin((r-w)a)/(r-w) - sin((r+w)a)/(r+w)]
            s = mp.mpf(0)
            for k in range(1, K):
                w = k*mp.pi/a; s += c[k - 1]*(mp.sin((r - w)*a)/(r - w) - mp.sin((r + w)*a)/(r + w))
            return s
        qz = 2*sum(ghat_over_i(g)**2 for g in zeros)
        tail = 2*mp.quad(lambda r: ghat_over_i(r)**2*mp.log(r/(2*mp.pi))/(2*mp.pi), [zeros[-1], 2*zeros[-1], 10*zeros[-1], 100*zeros[-1]])
        print(f"delta {delta} K {K}: odd prime-side Q/||g||^2 = {q_prime.str(20)}   zero-side = {mp.nstr(qz/den, 20)} (+tail {mp.nstr(tail/den, 5)}) -> {mp.nstr((qz + tail)/den, 20)}   prime powers {pp}", flush=True)

if __name__ == "__main__":
    if sys.argv[1] == "selftest": selftest()
    elif sys.argv[1] == "lam1":
        d = float(sys.argv[2]); K = int(sys.argv[3]); prec = int(sys.argv[4])
        t0 = time.time(); G, N, pp = gram_odd(d, K, prec); t1 = time.time()
        order, E, R, D = minimiser(G, N, prec)
        with ctx.workprec(prec):
            for j in range(min(6, len(order))):
                ev = E[order[j]].real.mid(); print(f"delta {d} K {K}: odd eigenvalue {j + 1}: ln {float(ev.log()) if ev > 0 else float('nan'):.4f}  ({ev.str(12, radius=False)})", flush=True)
            c = [(R[i, order[0]].real.mid()*D[i, i]).mid() for i in range(len(order))]
            rq = rayleigh_odd(G, N, c, prec); print(f"   Rayleigh of the ground state: ln upper {float(rq.upper().log()):.4f} rad {float(rq.rad().str(5, radius=False)):.1e} | gram {t1 - t0:.0f}s eig {time.time() - t1:.0f}s")
