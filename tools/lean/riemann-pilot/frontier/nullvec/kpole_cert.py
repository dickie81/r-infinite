#!/usr/bin/env python3
"""Round 122 part 2: arb certificate for PoleRelax.weilQ_ge_of_cert. Every quantity mirrors the Lean definitions
exactly: errK, tau6, cv6, dd6, psil6, sfun, kappa6 (weilConst_eq + farField_eq closed forms), gC (Gram closed forms,
Lean-proved equal to the integrals by gramM_eq). For a-intervals [lo, hi] (arb balls), certify by ball Cholesky:
  (1) gram6 a positive definite, (2) eps <= kappa6 a, (3) (kappa6 a - eps) G + G diag(s) G positive definite.
Usage: kpole_cert.py lo hi nint eps  |  kpole_cert.py scan"""
import sys, json, math
from flint import arb, arb_mat, ctx
ctx.prec = 200
Q = lambda s: arb(s)          # exact decimal constants as in Lean
CV = {1: "0.5408", 2: "1.6214", 3: "2.2965", 4: "2.4081", 5: "2.4848", 6: "2.7801"}
DD = {1: "0.36338", 2: "1", 3: "1.212206", 4: "1", 5: "0.872676", 6: "1"}
def errK(a): return a**2/6 + a**3/3 + a**4/200 + a**5/48
def tau6(a): return Q("3.033953") - errK(a)
def psil6(a, k): return Q(CV[k]) + a*Q(DD[k]) - errK(a)
def sfun(a, i):
    t = tau6(a)
    if i == 0: return arb(2)
    if i == 1: return -t/(8*a)
    return 2*(psil6(a, i - 1) - t)/(8*a)
def weilConst():
    return -arb.const_euler() - arb.pi()/2 - 3*arb(2).log() - arb.pi().log()
def kappa6(a):
    ea = a.exp()
    return weilConst() + (-((ea - 1)/(ea + 1)).log() + (arb.pi()/2 - a.sinh().atan())) + tau6(a)
def omk(a, k): return arb.pi()*k/(4*a)
def omka(k): return arb.pi()*k/4       # omk a k * a, exactly (avoids the a/a dependency)
def gC(a, i, j):
    if i == 0 or j == 0:
        if i == 0 and j == 0: return a + a.sinh()
        k = (j if i == 0 else i) - 1; w = omk(a, k)
        return (omka(k).cos()*(a/2).sinh() + 2*w*omka(k).sin()*(a/2).cosh())/(w**2 + Q("0.25"))
    if i == j:
        if i == 1: return 2*a
        w = omk(a, i - 1); return a + (2*omka(i - 1)).sin()/(2*w)
    wi, wj = omk(a, i - 1), omk(a, j - 1)
    return (omka(i - 1) - omka(j - 1)).sin()/(wi - wj) + (omka(i - 1) + omka(j - 1)).sin()/(wi + wj)
def chol_ok(M, n):
    L = [[arb(0)]*n for _ in range(n)]; piv = []
    for j in range(n):
        d = M[j][j] - sum((L[j][k]*L[j][k] for k in range(j)), arb(0)); piv.append(d)
        if not d > 0: return False, piv
        L[j][j] = d.sqrt()
        for i in range(j + 1, n): L[i][j] = (M[i][j] - sum((L[i][k]*L[j][k] for k in range(j)), arb(0)))/L[j][j]
    return True, piv
def check(a, eps):
    n = 8
    G = [[gC(a, i, j) for j in range(n)] for i in range(n)]
    okG, pG = chol_ok(G, n)
    k = kappa6(a); s = [sfun(a, i) for i in range(n)]
    GSG = [[sum((G[i][l]*s[l]*G[l][j] for l in range(n)), arb(0)) for j in range(n)] for i in range(n)]
    M = [[(k - eps)*G[i][j] + GSG[i][j] for j in range(n)] for i in range(n)]
    okM, pM = chol_ok(M, n)
    return okG, (k - eps) > 0, okM, pG, pM, k
if __name__ == "__main__":
    if sys.argv[1] == "scan":
        for av in ("0.0625", "0.1", "0.15", "0.2", "0.22", "0.24", "0.25"):
            a = arb(av); okG, okk, okM, pG, pM, k = check(a, arb("0.001"))
            print(av, "G pd", okG, "min G pivot %.2e" % min(float(p.mid()) for p in pG), "| kappa", k.str(5),
                  "| M pd", okM, "min M pivot %.2e" % min(float(p.mid()) for p in pM))
        sys.exit()
    lo, hi, nint, eps = arb(sys.argv[1]), arb(sys.argv[2]), int(sys.argv[3]), arb(sys.argv[4])
    fails = []
    for i in range(nint):
        l = lo + (hi - lo)*i/nint; h = lo + (hi - lo)*(i + 1)/nint
        a = arb((l + h)/2, float(((h - l)/2).upper())*1.0000001 + 1e-30)
        okG, okk, okM, pG, pM, k = check(a, eps)
        if not (okG and okk and okM): fails.append((float(l.mid()), float(h.mid()), okG, bool(okk), okM))
    print(json.dumps({"lo": sys.argv[1], "hi": sys.argv[2], "nint": nint, "eps": sys.argv[4], "fails": len(fails), "first_fails": fails[:5]}))

def certify_point(astr="0.25", epsstr="0.001", prec=400):
    """Cert14 of PoleRelax.lean at the exact point a = 1/4, eps = 1/1000 (monotonicity in a does the rest)."""
    with ctx.workprec(prec):
        a, eps = arb(astr), arb(epsstr)
        okG, okk, okM, pG, pM, k = check(a, eps)
        return {"a": astr, "eps": epsstr, "prec": prec, "gram6_posdef": okG, "eps_le_kappa6": bool(okk),
                "M_posdef": okM, "kappa6": k.str(12), "gram_pivots": [p.str(4) for p in pG],
                "M_pivots": [p.str(4) for p in pM], "max_pivot_radius": max(float(p.rad()) for p in pG + pM)}
