#!/usr/bin/env python3
"""Round 135: parity-general arb certificate/scoping for the relaxation of Weil's form on [-a, a].
Sector 'even': vectors v_0 = cosh(t/2) (pole, weight +2), v_{k+1} = cos(pi k t/4a), k = 0..N  (as kprime_cert.py).
Sector 'odd' : vectors v_0 = sinh(t/2) (pole, weight -2: the odd pole term is -2 poleR^2, poleR = -int g sinh(t/2)),
               v_k = sin(pi k t/4a), k = 1..N  (odd mode masses p_k = Y_k^2/8a, p_0 = 0).
Primes: every n <= e^{2a} with c_n = 2 Lambda(n)/sqrt(n), u_n = log n; 2S(g) = sum_n c_n f(log n) (f = autocorr).
Mode weights: E_k = psi_k - sum_n c_n cos(pi k log n/4a); psiC_k = 12-decimal rationals below arb enclosures of psi_k.
Tail: tau = TAIL - errK(a) - sum_n c_n (TAIL = 5.098076 <= Cin(61 pi/2), valid for every N >= 60).
kappa = weilConst + Far(a) + tau. Certify G > 0, eps <= kappa, M = (kappa-eps)G + G diag(s) G > 0 (ball Cholesky) and
the congruent M' = (kappa-eps)I + L^T S L.
Usage: kpar_cert.py scope SECTOR A N [PREC]  |  kpar_cert.py cert SECTOR A N EPS [PREC]"""
import sys, json, math, os
from flint import arb, acb, ctx
import mpmath as mp
import kpole_cert as KP
TAIL = "5.098076"
def lam(n):
    if n < 2: return None
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0: m //= p
            return p if m == 1 else None
def primes_upto(a):   # n with log n <= 2a
    X = math.exp(2*float(arb(a).mid()))
    return [n for n in range(2, int(X) + 2) if lam(n) and arb(n).log() <= 2*arb(a)]
def psi_enclosure(a, m, delta="1e-15"):
    w = arb.pi()*m/(4*a)
    f = lambda z, analytic: (1 - (z*acb(w)).cos())*(z/2).exp()/z.sinh()
    I = acb.integral(f, acb(delta), acb(2*a)).real
    d = arb(delta)
    return I, I + w**2*(d**2/4 + d**3/12)
def psi_certified(astr, N):
    fn = f"kpar_psiC_{astr}.json"
    r = json.load(open(fn)) if os.path.exists(fn) else {"a": astr, "psiC": {}}
    ps = r["psiC"]; new = False
    with ctx.workprec(200):
        a = arb(astr)
        for m in range(1, N + 1):
            if str(m) in ps: continue
            lo, hi = psi_enclosure(a, m)
            v = (math.floor(float(lo.lower())*1e12) - 1)/1e12   # one extra unit below: float rounding margin
            ps[str(m)] = f"{v:.12f}"; new = True
            assert arb(ps[str(m)]) < lo, (m, ps[str(m)], lo)
    if new: json.dump(r, open(fn, "w"), indent=0)
    return ps
def gram_odd(a, i, j):
    om = lambda k: arb.pi()*k/(4*a); oma = lambda k: arb.pi()*k/4
    if i == 0 or j == 0:
        if i == 0 and j == 0: return a.sinh() - a
        k = j if i == 0 else i; w = om(k)
        return ((a/2).cosh()*oma(k).sin() - 2*w*(a/2).sinh()*oma(k).cos())/(w**2 + arb("0.25"))
    if i == j: return a - (2*oma(i)).sin()/(2*om(i))
    return (oma(i) - oma(j)).sin()/(om(i) - om(j)) - (oma(i) + oma(j)).sin()/(om(i) + om(j))
def tail_const(N):
    t = os.environ.get("TAIL", TAIL)
    if t == "exact":      # scoping only: Cin(pi(N+1)/2) - 1e-6
        mp.mp.dps = 30; x = mp.pi*(N + 1)/2
        return arb(mp.nstr(mp.euler + mp.log(x) - mp.ci(x) - mp.mpf("1e-6"), 20))
    return arb(t)
def system(sector, astr, N, psiC):
    a = arb(astr)
    ns = primes_upto(astr)
    cs = [(2*arb(lam(n)).log()/arb(n).sqrt(), arb(n).log()) for n in ns]
    csum = sum((c for c, _ in cs), arb(0))
    tau = tail_const(N) - KP.errK(a) - csum
    Ek = lambda k: arb(psiC[str(k)]) - sum((c*(arb.pi()*k*u/(4*a)).cos() for c, u in cs), arb(0))
    if sector == "even":
        n = N + 2
        s = [arb(2), (-csum - tau)/(8*a)] + [2*(Ek(k + 1) - tau)/(8*a) for k in range(N)]
        G = [[KP.gC(a, i, j) for j in range(n)] for i in range(n)]
    else:
        n = N + 1
        s = [arb(-2)] + [2*(Ek(k) - tau)/(8*a) for k in range(1, N + 1)]
        G = [[gram_odd(a, i, j) for j in range(n)] for i in range(n)]
    ea = a.exp()
    kap = KP.weilConst() + (-((ea - 1)/(ea + 1)).log() + (arb.pi()/2 - a.sinh().atan())) + tau
    return n, s, kap, G, tau, ns
def chol_L(G, n):
    L = [[arb(0)]*n for _ in range(n)]
    for j in range(n):
        d = G[j][j] - sum((L[j][k]*L[j][k] for k in range(j)), arb(0))
        if not d > 0: raise ValueError(f"Gram not PD at pivot {j}: {d}")
        L[j][j] = d.sqrt()
        for i in range(j + 1, n): L[i][j] = (G[i][j] - sum((L[i][k]*L[j][k] for k in range(j)), arb(0)))/L[j][j]
    return L
def scope(sector, astr, N, prec=3000):
    psiC = psi_certified(astr, N)
    with ctx.workprec(prec):
        n, s, kap, G, tau, ns = system(sector, astr, N, psiC)
        L = chol_L(G, n)
        S = [[sum((L[l][i]*s[l]*L[l][j] for l in range(n)), arb(0)) for j in range(n)] for i in range(n)]
        mp.mp.dps = 50
        Sm = mp.matrix([[mp.mpf(S[i][j].mid().str(45, radius=False)) for j in range(n)] for i in range(n)])
        lmin = min(mp.eigsy(Sm)[0])
        return {"sector": sector, "a": astr, "N": N, "primes": ns, "tau": float(tau.mid()), "kappa": float(kap.mid()),
                "bound": float(kap.mid() + lmin), "maxrad": max(float(S[i][j].rad()) for i in range(n) for j in range(n))}
def run(sector, astr, N, eps_str, prec=3000):
    out = {"sector": sector, "a": astr, "N": N, "eps": eps_str, "prec": prec}
    psiC = psi_certified(astr, N)
    out["psiC"] = {str(m): psiC[str(m)] for m in range(1, N + 1)}
    with ctx.workprec(prec):
        eps = arb(eps_str)
        n, s, kap, G, tau, ns = system(sector, astr, N, psiC)
        out["prime_powers"] = ns
        out["K"] = int(math.exp(2*float(arb(astr).mid()))) + 1   # Lean sums n < K: log(K-1) <= 2a < log K
        out["tail_T"] = str(os.environ.get("TAIL", TAIL)); out["tau"] = tau.str(12)
        out["s_min"] = min(s, key=lambda x: float(x.mid())).str(6)
        okG, pG = KP.chol_ok(G, n)
        out["gram_posdef"] = okG; out["min_gram_pivot"] = min(pG, key=lambda p: float(p.mid())).str(3)
        out["kappa"] = kap.str(12); out["eps_le_kappa"] = bool(kap - eps > 0)
        GS = [[G[i][l]*s[l] for l in range(n)] for i in range(n)]
        M = [[(kap - eps)*G[i][j] + sum((GS[i][l]*G[l][j] for l in range(n)), arb(0)) for j in range(n)] for i in range(n)]
        okM, pM = KP.chol_ok(M, n)
        out["M_posdef_direct"] = okM; out["min_M_pivot"] = min(pM, key=lambda p: float(p.mid())).str(3)
        out["max_M_pivot_radius"] = max(float(p.rad()) for p in pM)
    return out
if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "scope":
        print(json.dumps(scope(sys.argv[2], sys.argv[3], int(sys.argv[4]), *(int(x) for x in sys.argv[5:6]))), flush=True)
    else:
        r = run(sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5], *(int(x) for x in sys.argv[6:7]))
        print(json.dumps({k: v for k, v in r.items() if k != "psiC"}, indent=1))
        json.dump(r, open(f"kpar_cert_{sys.argv[2]}_{sys.argv[3]}.json", "w"), indent=1)
