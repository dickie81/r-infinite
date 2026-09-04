#!/usr/bin/env python3
"""The TRUE Weil form on a window, in balls: the prime-side Gram of Weil's
quadratic functional in the even cosine basis on [-a, a] (delta = 2a), every
entry an ARB ball -- and certified upper bounds on its ground state
(Rayleigh quotients of trial vectors evaluated in balls). Unconditional:
no zeros enter; primes p^k <= e^delta, the archimedean term by
digamma/trigamma, the pole term in closed form. (Owner: "Certify CCM's
trial vector on the true form in balls at every cell".)

THE FORM. For a real even probe g on [-a, a] with ghat(r) = int g e^{irt} dt
and f = g * g~ its autocorrelation (f(0) = ||g||^2, f(u) = 0 for u > 2a),
Weil's explicit formula gives, with Q(g) := sum_gamma |ghat(gamma)|^2 under RH
and in general the arithmetic side (verified against the 6700 zeros on
Gaussian probes to 1e-17, Addendum 447/454):

  Q(g) = 2 ghat(i/2)^2 + (psi(1/4) - log pi) ||g||^2
         + int_0^inf [f(0) - f(u)] e^{u/2}/sinh(u) du
         - 2 sum_{n>=2} Lambda(n) n^{-1/2} f(log n).

THE BASIS. phi_k(t) = cos(omega_k t) 1_{[-a,a]}, omega_k = k pi / a,
k = 0..K-1 (Yoshida's periodic class K(a)); <phi_j, phi_k> = a delta_jk
(2a for j = k = 0). The bilinear autocorrelation
f_jk(u) = int_{-a+u}^{a} cos(omega_j t) cos(omega_k (t - u)) dt is elementary:
  j != k:  f_jk(u) = (-1)^{j+k} [omega_k sin(omega_k u) - omega_j sin(omega_j u)]
                     / (omega_j^2 - omega_k^2)
  j = k>0: f_kk(u) = [(2a - u) cos(omega_k u) - sin(omega_k u)/omega_k]/2
  j = k=0: f_00(u) = 2a - u.
With K(u) = e^{u/2}/sinh u = 2 sum_{m>=0} e^{-s_m u}, s_m = 2m + 1/2, the
archimedean integrals over [0, 2a] are digamma/trigamma values at
1/4 + i omega/2 minus geometric tails over [2a, inf):
  int_0^inf sin(omega u) K du      = Im psi(1/4 + i omega/2)
  int_0^inf (1 - cos omega u) K du = Re psi(1/4 + i omega/2) - psi(1/4)
  int_0^inf u cos(omega u) K du    = Re psi'(1/4 + i omega/2) / 2
and the tails 2 sum_m e^{-2a s_m} (...) summed in balls with a rigorous
geometric remainder. The pole term uses p_k = int cos(omega_k t) e^{t/2} dt
= Re[2 sinh((1/2 + i omega_k) a)/(1/2 + i omega_k)].

THE GRAM. G_jk = 2 p_j p_k + (psi(1/4) - log pi) N_jk + A_jk - P_jk with
  A_jk = int_0^inf [N_jk - f_jk(u) 1_{u<=2a}] K(u) du,
  P_jk = 2 sum_{n <= e^{2a}} Lambda(n) n^{-1/2} f_jk(log n).
Every entry is a ball at `prec` bits. For any coefficient vector c, the
Rayleigh quotient c^T G c / c^T N c evaluated in balls is a RIGOROUS UPPER
BOUND on the true lambda_1(delta) = min Q(g)/||g||^2 over L^2(-a, a).

WHAT IS CERTIFIED / NOT. Certified: the Gram entries (balls), hence every
Rayleigh quotient printed (a two-sided enclosure of Q(g)/||g||^2 for the
stated g, whose upper end bounds lambda_1 from above). Not certified: that
any trial is the minimiser; the basis truncation (the bound only improves
with K); a negative certified upper bound would disprove RH (the forward
Weil criterion) -- none occurs.

Self-test (`python3 weil_prime_gram.py selftest`): Q from the Gram against
sum_gamma |ghat(gamma)|^2 over the 6700 zeros (plus the smooth tail) for a
C_c^infty bump's cosine expansion at delta = 1 and 2.
Usage: weil_prime_gram.py certify <delta> <K> <prec>   -- the Gram minimiser
       weil_prime_gram.py selftest
"""
import sys, os, json, math, time
from flint import arb, acb, arb_mat, acb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))

def prime_powers(N):
    """[(n, log p)] for the prime powers 2 <= n <= N (Lambda(n) = log p)."""
    out = []
    for n in range(2, N + 1):
        p = None
        for q in range(2, int(n**0.5) + 1):
            if n % q == 0:
                p = q; break
        if p is None: p = n
        m = n
        while m % p == 0: m //= p
        if m == 1: out.append((n, p))
    return out

def gram(delta, K, prec):
    """The Gram (arb_mat K x K) and the norm diagonal (list of arb)."""
    with ctx.workprec(prec):
        a = arb(delta)/2; twoa = 2*a
        pi = arb.pi(); half = arb(1)/2; quarter = arb(1)/4
        om = [arb(k)*pi/a for k in range(K)]
        psi_q = quarter.digamma(); tri_q = acb(quarter).polygamma(1).real
        logpi = pi.log()
        z = [acb(quarter, o/2) for o in om]
        psi = [zz.digamma() for zz in z]
        tri = [zz.polygamma(1) for zz in z]
        # tails over [2a, inf): 2 sum_m e^{-2a s_m} (...), s_m = 2m + 1/2
        M = int(prec*math.log(2)/(2*float(delta))) + 4
        T0 = arb(0); Tu0 = arb(0)
        Tc = [arb(0)]*K; Tuc = [arb(0)]*K; Ts = [arb(0)]*K
        for m in range(M):
            s = arb(2*m) + half
            e = (-twoa*s).exp()
            T0 += 2*e/s
            Tu0 += 2*e*(twoa/s + 1/(s*s))
            for k in range(1, K):
                w = acb(s, -om[k])            # s - i omega
                ew = (-twoa*w).exp()           # e^{-(s - i omega) 2a}
                q = ew/w
                Tc[k] += 2*q.real
                Ts[k] += 2*q.imag
                Tuc[k] += 2*(ew*(twoa/w + 1/(w*w))).real
        sM = arb(2*M) + half
        bound = (-twoa*sM).exp()*(twoa + 1)/(sM*(1 - (-2*twoa).exp()))*2
        err = arb(0, bound)
        T0 += err; Tu0 += err
        for k in range(1, K):
            Tc[k] += err; Ts[k] += err; Tuc[k] += err
        # per-k integrals over [0, 2a]
        S = [arb(0)]*K; C1 = [arb(0)]*K; U = [arb(0)]*K
        for k in range(1, K):
            S[k] = psi[k].imag - Ts[k]
            C1[k] = (psi[k].real - psi_q) - (T0 - Tc[k])
            U[k] = tri[k].real/2 - Tuc[k]
        U0 = tri_q/2 - Tu0
        # pole integrals
        P = []
        for k in range(K):
            w = acb(half, om[k])
            P.append((2*(w*a).sinh()/w).real)
        # prime powers
        pp = prime_powers(int(math.floor(float(twoa.exp()) + 1e-9)))
        pp = [(n, p) for n, p in pp if arb(n).log() < twoa or arb(n).log() == twoa]   # the equality branch never fires (ball equality); harmless: f_jk(2a) = 0 (round-298 F298-10)
        lam = [(arb(n).log(), arb(p).log()/arb(n).sqrt()) for n, p in pp]
        sinl = [[(om[k]*u).sin() for k in range(K)] for u, _ in lam]
        cosl = [[(om[k]*u).cos() for k in range(K)] for u, _ in lam]
        const = psi_q - logpi
        G = arb_mat(K, K); N = [a]*K; N[0] = twoa
        for j in range(K):
            for k in range(j, K):
                if j == k:
                    if k == 0:
                        A = U0 + twoa*T0
                        Pr = arb(0)
                        for i, (u, wgt) in enumerate(lam):
                            Pr += 2*wgt*(twoa - u)
                    else:
                        A = a*C1[k] + U[k]/2 + S[k]/(2*om[k]) + a*T0
                        Pr = arb(0)
                        for i, (u, wgt) in enumerate(lam):
                            Pr += 2*wgt*((twoa - u)*cosl[i][k] - sinl[i][k]/om[k])/2
                    val = 2*P[k]*P[k] + const*N[k] + A - Pr
                else:
                    sg = -1 if (j + k) % 2 else 1
                    den = om[j]*om[j] - om[k]*om[k]
                    A = sg*(om[j]*S[j] - om[k]*S[k])/den
                    Pr = arb(0)
                    for i, (u, wgt) in enumerate(lam):
                        Pr += 2*wgt*sg*(om[k]*sinl[i][k] - om[j]*sinl[i][j])/den
                    val = 2*P[j]*P[k] + A - Pr
                G[j, k] = val; G[k, j] = val
        return G, N, [n for n, _ in pp]

def rayleigh(G, N, c, prec):
    """Ball enclosure of c^T G c / c^T N c for a coefficient list c (arb or float)."""
    with ctx.workprec(prec):
        K = len(c)
        v = arb_mat(K, 1)
        for i in range(K): v[i, 0] = arb(c[i])
        num = (v.transpose()*G*v)[0, 0]
        den = arb(0)
        for i in range(K): den += N[i]*v[i, 0]*v[i, 0]
        return num/den

def minimiser(G, N, prec):
    """Approximate ground state of the generalised problem G v = lam N v (midpoints)."""
    with ctx.workprec(prec):
        K = G.nrows()
        D = arb_mat(K, K)
        for i in range(K): D[i, i] = 1/N[i].sqrt()
        Gs = D*G*D
        E, R = acb_mat(Gs.mid()).eig(right=True, algorithm="approx")
        k0 = min(range(K), key=lambda i: E[i].real.mid())
        c = [(R[i, k0].real.mid()*D[i, i]).mid() for i in range(K)]
        return c, E[k0].real.mid()

def certify(delta, K, prec):
    t0 = time.time()
    G, N, pp = gram(delta, K, prec)
    t1 = time.time()
    c, ev = minimiser(G, N, prec)
    rq = rayleigh(G, N, c, prec)
    t2 = time.time()
    with ctx.workprec(prec):
        return {"delta": delta, "K": K, "prec": prec, "prime_powers": pp,
                "eig_mid": ev.str(30, radius=False),
                "rq_mid": rq.mid().str(30, radius=False), "rq_rad": float(rq.rad().str(5, radius=False)),
                "rq_upper": rq.upper().str(30, radius=False),
                "ln_rq_upper": float(rq.upper().log()) if rq.upper() > 0 else None,
                "ln_eig": float(ev.log()) if ev > 0 else None,
                "gram_s": t1 - t0, "eig_s": t2 - t1, "coeffs": [str(x) for x in c]}

# ------------------------------------------------------------ self-test
def selftest():
    zeros = [float(z) for z in json.load(open(os.path.join(HERE, "checkpoints", "zeta_zeros_6700.json")))]
    import mpmath as mp
    mp.mp.dps = 40
    for delta, K, prec in ((1.0, 48, 400), (2.0, 80, 400)):
        a = delta/2
        # cosine coefficients of the bump exp(-1/(1 - (t/a)^2)) on [-a, a]
        bump = lambda t: mp.e**(-1/(1 - (t/a)**2)) if abs(t) < a else mp.mpf(0)
        c = []
        for k in range(K):
            ck = mp.quad(lambda t: bump(t)*mp.cos(k*mp.pi*t/a), [-a, 0, a])/(a if k else 2*a)
            c.append(ck)
        G, N, pp = gram(delta, K, prec)
        q_prime = rayleigh(G, N, [arb(str(x)) for x in c], prec)
        den = sum((a if k else 2*a)*c[k]**2 for k in range(K))
        # zero side: ghat_K(r) = sum c_k [sin((r+w)a)/(r+w) + sin((r-w)a)/(r-w)]
        def ghat(r):
            s = mp.mpf(0)
            for k in range(K):
                w = k*mp.pi/a
                if k == 0: s += c[0]*2*mp.sin(r*a)/r
                else: s += c[k]*(mp.sin((r+w)*a)/(r+w) + mp.sin((r-w)*a)/(r-w))
            return s
        qz = 2*sum(ghat(g)**2 for g in zeros)
        tail = 2*mp.quad(lambda r: ghat(r)**2*mp.log(r/(2*mp.pi))/(2*mp.pi), [zeros[-1], 2*zeros[-1], 10*zeros[-1], 100*zeros[-1]])
        print(f"delta {delta} K {K}: prime-side Q/||g||^2 = {q_prime.str(20)}   zero-side = {mp.nstr(qz/den, 20)} (+tail {mp.nstr(tail/den, 5)})   prime powers {pp}", flush=True)

def certify_trial(delta, prec, path):
    """Certified Rayleigh quotient of a stored trial vector (ccm_trial_vector.py output)."""
    st = json.load(open(path))
    K = st["K"]; assert abs(st["delta"] - delta) < 1e-12
    t0 = time.time()
    G, N, pp = gram(delta, K, prec)
    with ctx.workprec(prec):
        c = [arb(x) for x in st["coeffs"]]
        rq = rayleigh(G, N, c, prec)
        return {"delta": delta, "K": K, "prec": prec, "prime_powers": pp, "trial": os.path.basename(path),
                "rq_mid": rq.mid().str(30, radius=False), "rq_rad": float(rq.rad().str(5, radius=False)),
                "rq_upper": rq.upper().str(30, radius=False),
                "ln_rq_upper": float(rq.upper().log()) if rq.upper() > 0 else None,
                "seconds": time.time() - t0}

if __name__ == "__main__":
    if sys.argv[1] == "selftest":
        selftest()
    elif sys.argv[1] == "trial":
        d = float(sys.argv[2]); prec = int(sys.argv[3]); path = sys.argv[4]
        st = certify_trial(d, prec, path)
        print(f"delta {d} K {st['K']} prec {prec} trial {st['trial']}: Rayleigh [{st['rq_mid'][:14]} +/- {st['rq_rad']:.1e}] upper ln {st['ln_rq_upper']:.4f} | primes {st['prime_powers']} | {st['seconds']:.0f}s", flush=True)
    elif sys.argv[1] == "certify":
        d = float(sys.argv[2]); K = int(sys.argv[3]); prec = int(sys.argv[4])
        st = certify(d, K, prec)
        print(f"delta {d} K {K} prec {prec}: eig {st['eig_mid'][:14]} ln {st['ln_eig']:.4f} | Rayleigh upper {st['rq_upper'][:14]} ln {st['ln_rq_upper']:.4f} rad {st['rq_rad']:.1e} | primes {st['prime_powers']} | gram {st['gram_s']:.0f}s eig {st['eig_s']:.0f}s", flush=True)
