#!/usr/bin/env python3
"""Round 134: arb certificate for PrimeRelax3.lean at a* = 0.5493 (support 2a* = 1.0986 < log 3), the last support
before the second prime n = 3 enters. Same construction as kprime_cert.py (round 123), re-run at a*:
(A1) rigorous mode energies psi_m = int_{(0,2a]} (1 - cos(pi m u/4a)) e^{u/2}/sinh u du, m = 1..N, by acb.integral on
     [delta, 2a] plus the head bound 0 <= int_0^delta <= w^2 (delta^2/4 + delta^3/12); psiC_m = a 12-decimal rational
     strictly below the enclosure.
(A2) c = sqrt2 log 2, u0 = log 2, tau = TAIL - errK(a) - c with TAIL the Lean constant of the Cin bound at mode N+1
     (cinH61: 5.098076 <= Cin(61 pi/2) for N = 60);
     s_0 = 2, s_1 = (-c - tau)/8a, s_{k+2} = 2(psiC_{k+1} - c cos(pi(k+1)u0/4a) - tau)/8a; kappa = weilConst + Far(a) + tau.
     Certify: G > 0, eps <= kappa, M = (kappa-eps)G + G diag(s) G > 0 (direct ball Cholesky), and the congruent
     M' = (kappa-eps)I + L^T diag(s) L > 0 (G = L L^T), whose pivots read off the margin.
Usage: kprime3_cert.py scope            (float bound kappa + lambda_min(L^T S L), no eps)
       kprime3_cert.py cert EPS [PREC]  (the certificate; writes kprime3_cert_result.json)"""
import sys, json, math, os
from flint import arb, acb, ctx
import mpmath as mp
import kpole_cert as KP
A_STR = "0.5493"; N = 60; TAIL = "5.098076"
PSI_CACHE = "kprime3_psiC.json"
def psi_enclosure(a, m, delta="1e-15"):
    w = arb.pi()*m/(4*a)
    f = lambda z, analytic: (1 - (z*acb(w)).cos())*(z/2).exp()/z.sinh()
    I = acb.integral(f, acb(delta), acb(2*a)).real
    d = arb(delta); head = w**2*(d**2/4 + d**3/12)
    return I, I + head
def psi_certified():
    if os.path.exists(PSI_CACHE):
        r = json.load(open(PSI_CACHE))
        if r["a"] == A_STR and r["N"] == N: return r["psiC"]
    psiC = {}
    with ctx.workprec(200):
        a = arb(A_STR)
        for m in range(1, N + 1):
            lo, hi = psi_enclosure(a, m)
            v = math.floor(float(lo.lower())*1e12)/1e12
            psiC[str(m)] = f"{v:.12f}"
            assert arb(psiC[str(m)]) < lo, (m, psiC[str(m)], lo)
            print("psi", m, psiC[str(m)], flush=True)
    json.dump({"a": A_STR, "N": N, "psiC": psiC}, open(PSI_CACHE, "w"), indent=1)
    return psiC
def system(psiC):
    a = arb(A_STR)
    c = arb(2).sqrt()*arb(2).log(); u0 = arb(2).log()
    tau = arb(TAIL) - KP.errK(a) - c
    n = N + 2
    s = [arb(2), (-c - tau)/(8*a)] + [2*(arb(psiC[str(k + 1)]) - c*(arb.pi()*(k + 1)*u0/(4*a)).cos() - tau)/(8*a)
                                      for k in range(N)]
    ea = a.exp()
    kap = KP.weilConst() + (-((ea - 1)/(ea + 1)).log() + (arb.pi()/2 - a.sinh().atan())) + tau
    G = [[KP.gC(a, i, j) for j in range(n)] for i in range(n)]
    return n, s, kap, G, tau
def chol_L(G, n):
    L = [[arb(0)]*n for _ in range(n)]
    for j in range(n):
        d = G[j][j] - sum((L[j][k]*L[j][k] for k in range(j)), arb(0)); L[j][j] = d.sqrt()
        for i in range(j + 1, n): L[i][j] = (G[i][j] - sum((L[i][k]*L[j][k] for k in range(j)), arb(0)))/L[j][j]
    return L
def scope(prec=2400):
    psiC = psi_certified()
    with ctx.workprec(prec):
        n, s, kap, G, tau = system(psiC)
        L = chol_L(G, n)
        S = [[sum((L[l][i]*s[l]*L[l][j] for l in range(n)), arb(0)) for j in range(n)] for i in range(n)]
        mp.mp.dps = 60
        Sm = mp.matrix([[mp.mpf(S[i][j].mid().str(50, radius=False)) for j in range(n)] for i in range(n)])
        ev = mp.eigsy(Sm)[0]
        lmin = min(ev)
        print(json.dumps({"a": A_STR, "N": N, "tail": TAIL, "tau": tau.str(8), "kappa": kap.str(10),
                          "lambda_min_LtSL": mp.nstr(lmin, 10), "bound": mp.nstr(kap + lmin, 6),
                          "max_S_radius": max(float(S[i][j].rad()) for i in range(n) for j in range(n))}, indent=1))
def run(eps_str, prec=2400):
    out = {"a": A_STR, "N": N, "eps": eps_str, "tail": TAIL, "prec": prec}
    psiC = psi_certified()
    out["psiC"] = psiC; out["psiC_below_enclosures"] = True
    lean = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../src/PrimeRelax3.lean")).read()
    lst = lean.split("def psiCq3 : List ℚ := [")[1].split("]")[0].split(", ")
    out["lean_psiCq3_matches"] = lst == [psiC[str(m)] for m in range(1, N + 1)]
    assert out["lean_psiCq3_matches"]
    with ctx.workprec(prec):
        eps = arb(eps_str)
        n, s, kap, G, tau = system(psiC)
        okG, pG = KP.chol_ok(G, n)
        out["gram_posdef"] = okG; out["min_gram_pivot"] = min(pG, key=lambda p: float(p.mid())).str(3)
        out["kappa"] = kap.str(12); out["eps_le_kappa"] = bool(kap - eps > 0)
        GS = [[G[i][l]*s[l] for l in range(n)] for i in range(n)]
        M = [[(kap - eps)*G[i][j] + sum((GS[i][l]*G[l][j] for l in range(n)), arb(0)) for j in range(n)] for i in range(n)]
        okM, pM = KP.chol_ok(M, n)
        out["M_posdef_direct"] = okM; out["min_M_pivot"] = min(pM, key=lambda p: float(p.mid())).str(3)
        L = chol_L(G, n)
        Mp = [[(kap - eps if i == j else arb(0)) + sum((L[l][i]*s[l]*L[l][j] for l in range(n)), arb(0))
               for j in range(n)] for i in range(n)]
        okMp, pMp = KP.chol_ok(Mp, n)
        out["Mprime_posdef"] = okMp; out["min_Mprime_pivot"] = min(pMp, key=lambda p: float(p.mid())).str(3)
        out["max_radius_Mprime_pivot"] = max(float(p.rad()) for p in pMp)
    return out
if __name__ == "__main__":
    if sys.argv[1] == "scope":
        scope(*(int(x) for x in sys.argv[2:3]))
    else:
        r = run(sys.argv[2], *(int(x) for x in sys.argv[3:4]))
        print(json.dumps({k: v for k, v in r.items() if k != "psiC"}, indent=1))
        json.dump(r, open("kprime3_cert_result.json", "w"), indent=1)
