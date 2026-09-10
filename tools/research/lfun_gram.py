#!/usr/bin/env python3
"""The true Weil form of a degree-d L-function with conductor q in the even
cosine basis of weil_prime_gram.py, every entry an ARB ball (Theorem 1bq's
substrate; originated as the round-313 workflow's prototype, adopted after
review). Generalises weil_prime_gram.gram() by:
  * Gamma factors prod_i Gamma_R(s + kappa_i) -> archimedean kernel
        K(u) = sum_i e^{(1/2 - kappa_i) u} / sinh u,
    digamma/trigamma at z_i = 1/4 + kappa_i/2 + i omega/2, geometric tails with
    s_m = 2m + 1/2 + kappa_i (the same remainder bound as weil_prime_gram);
  * the constant log q - d log pi + sum_i psi(1/4 + kappa_i/2);
  * the pole term 2 p_j p_k only for zeta (pole=True);
  * the prime side 2 sum_{n = p^k <= e^delta} (log p) c(p^k) n^{-1/2} f_jk(log n),
    c(p^k) = the local coefficient: chi(p)^k for a Dirichlet character (the
    Kronecker symbol of a fundamental discriminant D; kappa = 0 for D > 0,
    1 for D < 0; q = |D|), alpha^k + beta^k for GL(2) with alpha + beta =
    tau(p) p^{-11/2}, alpha beta = 1 for Ramanujan's Delta (Gamma_C(s + 11/2)
    = Gamma_R(s + 11/2) Gamma_R(s + 13/2), q = 1).
The Rayleigh quotient of any coefficient vector on the returned pencil is a
rigorous upper bound on lambda_1 of the form on L^2(-a, a). Verified: with
the zeta descriptor the Gram reproduces weil_prime_gram.gram() (regression in
__main__), and for chi_-4, chi_8 and Delta the Rayleigh quotient of a C_c^inf
bump agrees with the explicit formula's zero side (lfun_selftest in the
verifier).
"""
import sys, os, math, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, acb, arb_mat, acb_mat, ctx
from weil_prime_gram import prime_powers, minimiser, rayleigh

# ---------------------------------------------------------------- characters
def kronecker(D, n):
    """Kronecker symbol (D/n) for n >= 1 (D a fundamental discriminant)."""
    if n == 1: return 1
    res = 1; m = n
    while m % 2 == 0:
        m //= 2
        if D % 2 == 0: return 0
        res *= 1 if D % 8 in (1, 7) else -1
    p = 3
    while p*p <= m:
        while m % p == 0:
            m //= p
            res *= legendre(D, p)
        p += 2
    if m > 1: res *= legendre(D, m)
    return res

def legendre(a, p):
    a %= p
    if a == 0: return 0
    r = pow(a, (p - 1)//2, p)
    return 1 if r == 1 else -1

def dirichlet_coef(D):
    """c(p^k) = chi_D(p)^k, kappa = 0 (D > 0) or 1 (D < 0), q = |D|."""
    def coef(p, k): return kronecker(D, p)**k
    return dict(q=abs(D), kappas=[0 if D > 0 else 1], coef=coef, pole=False, d=1, name=f"chi_{D}")

def tau_list(N):
    """Ramanujan tau(n), n <= N, from q prod (1 - q^n)^24."""
    N += 1
    poly = [0]*N; poly[0] = 1
    for n in range(1, N):
        for _ in range(24):
            for i in range(N - 1, n - 1, -1):
                poly[i] -= poly[i - n]
    return [0] + poly[:N - 1]   # tau(n) = coefficient of q^n in q * prod

def delta_coef():
    """GL(2), Ramanujan Delta: Gamma_C(s + 11/2) = Gamma_R(s + 11/2) Gamma_R(s + 13/2), q = 1,
    c(p^k) = alpha^k + beta^k, alpha + beta = tau(p) p^{-11/2}, alpha beta = 1 (recurrence)."""
    T = tau_list(64)
    def coef(p, k):
        with ctx.workprec(200):
            c1 = arb(T[p])/arb(p)**(arb(11)/2)
            cm, c = arb(2), c1
            for _ in range(k - 1):
                cm, c = c, c1*c - cm
            return c
    return dict(q=1, kappas=[arb(11)/2, arb(13)/2], coef=coef, pole=False, d=2, name="Delta")

ZETA = dict(q=1, kappas=[0], coef=lambda p, k: 1, pole=True, d=1, name="zeta")

# ---------------------------------------------------------------- the Gram
def gram_L(delta, K, prec, L):
    q, kappas, coef, pole = L["q"], L["kappas"], L["coef"], L["pole"]
    with ctx.workprec(prec):
        a = arb(delta)/2; twoa = 2*a
        pi = arb.pi(); half = arb(1)/2; quarter = arb(1)/4
        om = [arb(k)*pi/a for k in range(K)]
        logpi = pi.log()
        M = int(prec*math.log(2)/(2*float(delta))) + 4
        # accumulate over Gamma factors
        psi_q = arb(0); tri_q = arb(0)
        T0 = arb(0); Tu0 = arb(0)
        Tc = [arb(0)]*K; Tuc = [arb(0)]*K; Ts = [arb(0)]*K
        psi = [acb(0)]*K; tri = [acb(0)]*K
        for kap in kappas:
            kap = arb(kap)
            z0 = quarter + kap/2
            psi_q += z0.digamma(); tri_q += acb(z0).polygamma(1).real
            for k in range(K):
                zz = acb(z0, om[k]/2)
                psi[k] = psi[k] + zz.digamma(); tri[k] = tri[k] + zz.polygamma(1)
            for m in range(M):
                s = arb(2*m) + half + kap
                e = (-twoa*s).exp()
                T0 += 2*e/s
                Tu0 += 2*e*(twoa/s + 1/(s*s))
                for k in range(1, K):
                    w = acb(s, -om[k])
                    ew = (-twoa*w).exp()
                    qq = ew/w
                    Tc[k] += 2*qq.real
                    Ts[k] += 2*qq.imag
                    Tuc[k] += 2*(ew*(twoa/w + 1/(w*w))).real
            sM = arb(2*M) + half + kap
            bound = (-twoa*sM).exp()*(twoa + 1)/(sM*(1 - (-2*twoa).exp()))*2
            err = arb(0, bound)
            T0 += err; Tu0 += err
            for k in range(1, K):
                Tc[k] += err; Ts[k] += err; Tuc[k] += err
        S = [arb(0)]*K; C1 = [arb(0)]*K; U = [arb(0)]*K
        for k in range(1, K):
            S[k] = psi[k].imag - Ts[k]
            C1[k] = (psi[k].real - psi_q) - (T0 - Tc[k])
            U[k] = tri[k].real/2 - Tuc[k]
        U0 = tri_q/2 - Tu0
        P = []
        for k in range(K):
            if pole:
                w = acb(half, om[k])
                P.append((2*(w*a).sinh()/w).real)
            else:
                P.append(arb(0))
        pp = prime_powers(int(math.floor(float(twoa.exp()) + 1e-9)))
        pp = [(n, p) for n, p in pp if arb(n).log() < twoa]
        lam = []
        used = []
        for n, p in pp:
            k = round(math.log(n)/math.log(p))
            c = coef(p, k)
            c = arb(c) if not isinstance(c, arb) else c
            if c == 0: continue
            lam.append((arb(n).log(), arb(p).log()*c/arb(n).sqrt()))
            used.append(n)
        sinl = [[(om[k]*u).sin() for k in range(K)] for u, _ in lam]
        cosl = [[(om[k]*u).cos() for k in range(K)] for u, _ in lam]
        const = psi_q - len(kappas)*logpi + arb(q).log()
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
        return G, N, used

def certify_L(delta, K, prec, L):
    G, N, pp = gram_L(delta, K, prec, L)
    c, ev = minimiser(G, N, prec)
    rq = rayleigh(G, N, c, prec)
    with ctx.workprec(prec):
        up = rq.upper(); lo = rq.lower()
        return dict(delta=delta, K=K, prec=prec, name=L["name"], q=L["q"], d=L["d"], prime_powers=pp,
                    ln_upper=float(up.log()) if up > 0 else None, positive=bool(lo > 0), negative=bool(up < 0),
                    upper=up.str(20, radius=False), lower=lo.str(20, radius=False), rad_log2=float(rq.rad().log()/arb(2).log()) if rq.rad() > 0 else None,
                    coeffs=c, G=G, N=N)

def horizon(delta, L):
    return 2*math.pi*(math.exp(delta)/L["q"])**(1.0/L["d"])

if __name__ == "__main__":
    # regression: zeta at delta = 1, K = 48, prec 400 against the committed gram()
    from weil_prime_gram import gram
    G0, N0, pp0 = gram(1.0, 48, 400)
    G1, N1, pp1 = gram_L(1.0, 48, 400, ZETA)
    with ctx.workprec(400):
        mx = max(float(abs(G0[j, k] - G1[j, k]).upper()) for j in range(48) for k in range(48))
    print("regression zeta delta=1 K=48: max |G - G_L| =", mx, "pp equal:", pp0 == pp1)
