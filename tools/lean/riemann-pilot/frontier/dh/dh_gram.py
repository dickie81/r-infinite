"""Weil's form on [-a, a] in the even cosine basis, in balls, for an L-function with a functional equation.
Generalises tools/research/weil_prime_gram.py:
  Q(g) = [2 ghat(i/2)^2 if pole] + (psi(z0) + logq) ||g||^2 + int_0^inf [f(0) - f(u)] K_z0(u) du
         - 2 sum_n c(n) n^{-1/2} f(log n),
with K_z0(u) = 2 sum_m e^{-(2m + 2 z0) u}; z0 = 1/4, logq = -log pi, pole for zeta;
z0 = 3/4 (Gamma((s+1)/2)), logq = log(q/pi), no pole for an odd character of conductor q;
c(n) the coefficients of -F'/F (for Davenport-Heilbronn, not supported on prime powers and not >= 0)."""
import math
from flint import arb, acb, arb_mat, acb_mat, ctx
def gram(delta, K, prec, lf):
    """The Gram for the L-function data lf = dict(z0=1/4 or 3/4, logq=log(conductor/pi) term,
    pole=bool, weights=[(n, c(n))] with c(n) the coefficients of -F'/F)."""
    with ctx.workprec(prec):
        a = arb(delta)/2; twoa = 2*a
        pi = arb.pi(); half = arb(1)/2; quarter = arb(1)/4
        om = [arb(k)*pi/a for k in range(K)]
        z0 = arb(1)/4 if lf['z0'] == 0.25 else arb(3)/4; psi_q = z0.digamma(); tri_q = acb(z0).polygamma(1).real
        logpi = pi.log()
        z = [acb(z0, o/2) for o in om]
        psi = [zz.digamma() for zz in z]
        tri = [zz.polygamma(1) for zz in z]
        # tails over [2a, inf): 2 sum_m e^{-2a s_m} (...), s_m = 2m + 1/2
        M = int(prec*math.log(2)/(2*float(delta))) + 4
        T0 = arb(0); Tu0 = arb(0)
        Tc = [arb(0)]*K; Tuc = [arb(0)]*K; Ts = [arb(0)]*K
        for m in range(M):
            s = arb(2*m) + 2*z0
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
        sM = arb(2*M) + 2*z0
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
        Nmax = int(math.floor(float(twoa.exp()) + 1e-9))
        lam = [(arb(n).log(), c/arb(n).sqrt()) for n, c in lf['weights'] if 2 <= n <= Nmax]
        pp = [n for n, c in lf['weights'] if 2 <= n <= Nmax]
        sinl = [[(om[k]*u).sin() for k in range(K)] for u, _ in lam]
        cosl = [[(om[k]*u).cos() for k in range(K)] for u, _ in lam]
        const = psi_q + lf['logq']
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
                    val = (2*P[k]*P[k] if lf['pole'] else 0) + const*N[k] + A - Pr
                else:
                    sg = -1 if (j + k) % 2 else 1
                    den = om[j]*om[j] - om[k]*om[k]
                    A = sg*(om[j]*S[j] - om[k]*S[k])/den
                    Pr = arb(0)
                    for i, (u, wgt) in enumerate(lam):
                        Pr += 2*wgt*sg*(om[k]*sinl[i][k] - om[j]*sinl[i][j])/den
                    val = (2*P[j]*P[k] if lf['pole'] else 0) + A - Pr
                G[j, k] = val; G[k, j] = val
        return G, N, pp


def lowest(G, N, prec, m=1):
    with ctx.workprec(prec):
        K = G.nrows()
        D = arb_mat(K, K)
        for i in range(K): D[i, i] = 1/N[i].sqrt()
        E, R = acb_mat((D*G*D).mid()).eig(right=True, algorithm="approx")
        idx = sorted(range(K), key=lambda i: float(E[i].real.mid()))[:m]
        return [(float(E[i].real.mid()), [float((R[j, i].real.mid()*D[j, j]).mid()) for j in range(K)]) for i in idx]

def lowest_mp(G, N, dps, m=3):
    """Lowest eigenpairs of G v = lam N v at `dps` digits (entries from ball midpoints)."""
    import mpmath as mp
    mp.mp.dps = dps
    K = G.nrows()
    tomp = lambda x: mp.mpf(x.mid().str(dps + 10, radius=False))
    Dg = [1/mp.sqrt(tomp(N[i])) for i in range(K)]
    S = mp.matrix(K, K)
    for i in range(K):
        for j in range(K): S[i, j] = Dg[i]*tomp(G[i, j])*Dg[j]
    E, V = mp.eigsy(S)
    idx = sorted(range(K), key=lambda i: E[i])[:m]
    return [(E[j], [Dg[i]*V[i, j] for i in range(K)]) for j in idx]
