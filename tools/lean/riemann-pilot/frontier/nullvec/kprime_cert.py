#!/usr/bin/env python3
"""Round 123: arb certificate for PrimeRelax.lean at a* = 2/5 (support 2a = 0.8, past the first prime log 2).
(A1) rigorous mode energies psi_m = int_{(0,2a]} (1 - cos(pi m u/4a)) e^{u/2}/sinh u du, m = 1..N, by acb.integral on
     [delta, 2a] plus the bound 0 <= int_0^delta <= w^2 (delta^2/4 + delta^3/12)  (1 - cos <= w^2u^2/2, K <= 1/u + 1/2);
     the certificate uses psiC_m = a decimal <= the enclosure's lower end.
(A2) with c = sqrt2 log 2, u0 = log 2 (prime n = 2), tau = 5.098076 - errK(a) - c (cinH61 tail):
     weights s_0 = 2 (pole), s_1 = (-c - tau)/8a, s_{k+2} = 2(psiC_{k+1} - c cos(pi(k+1)u0/4a) - tau)/8a;
     kappa = weilConst + Far(a) + tau; G = gram (closed forms gC, N+2 vectors).
     Certify: G > 0, eps <= kappa, M = (kappa-eps)G + G diag(s) G > 0, directly (ball Cholesky) and via the congruence
     M = L M' L^T, M' = (kappa-eps)I + L^T diag(s) L (option 2; its pivots are O(margin))."""
import sys, json, math
from flint import arb, acb, arb_mat, ctx
import kpole_cert as KP
A_STR = "0.4"; N = 60
def psi_enclosure(a, m, delta="1e-15"):
    w = arb.pi()*m/(4*a)
    f = lambda z, analytic: (1 - (z*acb(w)).cos())*(z/2).exp()/z.sinh()
    I = acb.integral(f, acb(delta), acb(2*a)).real
    d = arb(delta); head = w**2*(d**2/4 + d**3/12)
    return I, I + head
def run(eps_str="0.0001", prec=2400):
    out = {"a": A_STR, "N": N, "eps": eps_str}
    with ctx.workprec(200):
        a = arb(A_STR)
        psiC = {}
        for m in range(1, N + 1):
            lo, hi = psi_enclosure(a, m)
            v = math.floor(float(lo.lower())*1e12)/1e12      # decimal below the enclosure
            psiC[m] = f"{v:.12f}"
            assert arb(psiC[m]) < lo, (m, psiC[m], lo)        # rigorous: the decimal lies strictly below psi_m
    out["psiC"] = psiC; out["psiC_below_enclosures"] = True
    with ctx.workprec(prec):
        a = arb(A_STR); eps = arb(eps_str)
        c = arb(2).sqrt()*arb(2).log(); u0 = arb(2).log()
        tau = arb("5.098076") - KP.errK(a) - c
        n = N + 2
        s = [arb(2), (-c - tau)/(8*a)] + [2*(arb(psiC[k + 1]) - c*(arb.pi()*(k + 1)*u0/(4*a)).cos() - tau)/(8*a) for k in range(N)]
        ea = a.exp()
        kap = KP.weilConst() + (-((ea - 1)/(ea + 1)).log() + (arb.pi()/2 - a.sinh().atan())) + tau
        G = [[KP.gC(a, i, j) for j in range(n)] for i in range(n)]
        okG, pG = KP.chol_ok(G, n)
        out["gram_posdef"] = okG; out["min_gram_pivot"] = min(pG, key=lambda p: float(p.mid())).str(3)
        out["kappa"] = kap.str(10); out["eps_le_kappa"] = bool(kap - eps > 0)
        # direct M
        GS = [[G[i][l]*s[l] for l in range(n)] for i in range(n)]
        M = [[(kap - eps)*G[i][j] + sum((GS[i][l]*G[l][j] for l in range(n)), arb(0)) for j in range(n)] for i in range(n)]
        okM, pM = KP.chol_ok(M, n)
        out["M_posdef_direct"] = okM; out["min_M_pivot"] = min(pM, key=lambda p: float(p.mid())).str(3)
        # congruence (option 2): L from G's Cholesky, M' = (kappa-eps) I + L^T S L
        L = [[arb(0)]*n for _ in range(n)]
        for j in range(n):
            d = G[j][j] - sum((L[j][k]*L[j][k] for k in range(j)), arb(0)); L[j][j] = d.sqrt()
            for i in range(j + 1, n): L[i][j] = (G[i][j] - sum((L[i][k]*L[j][k] for k in range(j)), arb(0)))/L[j][j]
        Mp = [[(kap - eps if i == j else arb(0)) + sum((L[l][i]*s[l]*L[l][j] for l in range(n)), arb(0)) for j in range(n)] for i in range(n)]
        okMp, pMp = KP.chol_ok(Mp, n)
        out["Mprime_posdef"] = okMp; out["min_Mprime_pivot"] = min(pMp, key=lambda p: float(p.mid())).str(3)
        out["max_radius_Mprime"] = max(float(p.rad()) for p in pMp)
    return out
if __name__ == "__main__":
    r = run(*(sys.argv[1:2] or []))
    print(json.dumps({k: v for k, v in r.items() if k != "psiC"}, indent=1))
    json.dump(r, open("kprime_cert_result.json", "w"), indent=1)
