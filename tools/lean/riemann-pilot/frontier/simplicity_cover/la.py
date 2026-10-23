"""Assemble M = beta I + 2 p p^T + C (leading N even Legendre modes of Zhu's reduced form R at L = GAP_L),
bound the discarded Legendre tail, and certify eigenvalue counts of M below shifts s by a Schur-complement
inertia argument.  Usage: python3 la.py s1 s2 [n0] [parity]   or   python3 la.py bisect x [n0] [parity]   (parity 0 even, 1 odd)."""
import sys, os, pickle, math, json, time
import numpy as np
from flint import arb, acb, arb_mat, ctx, fmpz
from params import *
ctx.prec = 256
t0 = time.time()
par = int(sys.argv[4]) if len(sys.argv) > 4 else 0      # 0 even sector, 1 odd sector (pole sign reversed)
sfx = "" if par == 0 else "_odd"
L, cn, AL, T, beta = consts()
def mk(me): return arb(fmpz(int(me[0]))) * arb(2) ** int(me[1])
nd = pickle.load(open("nodes.pkl", "rb"))
qerr = mk(nd["qerr"]) if isinstance(nd["qerr"], tuple) else arb(nd["qerr"])
# ---- C from the four partial sums (upper triangles, row-major)
parts = [pickle.load(open(f"part{sfx}_{k}.pkl", "rb")) for k in range(4)]
if par == 1: qerr = qerr * arb("1.001")   # nodes.py bounded with nmax = 2N-2; odd nmax = 2N-1
Cu = [None] * len(parts[0])
for idx in range(len(parts[0])):
    s = arb(0)
    for P in parts:
        (m, r) = P[idx]; s += mk(m) + arb(0, 1) * mk(r)
    Cu[idx] = s + arb(0, 1) * qerr
del parts
# ---- pole vector p_n = sqrt(2L(2n+1)) i_n(L/2), series with all-positive terms, geometric tail bound
def i_n(n, z):
    z2 = z * z / 2; T_ = arb(1); S = arb(1); k = 0
    while True:
        k += 1; T_ = T_ * z2 / (k * (2 * n + 2 * k + 1)); S += T_
        if T_ < arb(2) ** -300:
            S += arb(0, 1) * 2 * T_; break           # ratio of later terms < 1/2
    return z ** n / (arb.fac_ui(2 * n + 1) / (arb(2) ** n * arb.fac_ui(n))) * S
half = L / 2
p = [(2 * L * (2 * n + 1)).sqrt() * i_n(n, half) for n in range(par, 2 * N, 2)]
sg = 2 if par == 0 else -2
# ---- M
M = arb_mat(N, N)
idx = 0
for i in range(N):
    for j in range(i, N):
        v = Cu[idx] + sg * p[i] * p[j]; idx += 1
        if i == j: v += beta
        M[i, j] = v; M[j, i] = v
del Cu
print(f"assembled M ({time.time()-t0:.0f}s); beta* = {beta.str(12)}", flush=True)
# ---- Legendre tail beyond order 2N (Theorem 1.1 of Zhu, constants recomputed here)
# K_Psi = sup_[0,T#] |Psi - beta|, by ball evaluation on a covering of [0, T#]
ctx.prec = 64
KP = arb(0); step = arb(1) / 4; a = arb(0)
lnc = [(arb(n).log(), c) for n, c in cn]
while a < T:
    tb = a + step / 2 + arb(0, 1) * step / 2
    v = (acb(arb(1) / 4, tb / 2).digamma()).real - arb.pi().log() - sum(c * (tb * l).cos() for l, c in lnc) - beta
    u = abs(v).upper(); KP = u if u > KP else KP; a += step
ctx.prec = 256
# b_m = sup_[0,T#] |F_m| <= sqrt(2L(2m+1)) (L T#)^m/(2m+1)!!  (|j_m(x)| <= x^m/(2m+1)!!)
def bm(m): return (2 * L * (2 * m + 1)).sqrt() * (L * T) ** m / (arb.fac_ui(2 * m + 1) / (arb(2) ** m * arb.fac_ui(m)))
m0 = 2 * N + par
b0 = bm(m0); r = (L * T) ** 4 / ((2 * m0 + 3) * (2 * m0 + 5)) ** 2 * (2 * m0 + 5) / (2 * m0 + 1)   # b_{m+2}^2/b_m^2 <= r for m >= m0
assert r < arb(1) / 2
Sb2 = b0 ** 2 / (1 - r)
pt0 = (2 * L * (2 * m0 + 1)).sqrt() * half ** m0 * half.exp() / (arb.fac_ui(2 * m0 + 1) / (arb(2) ** m0 * arb.fac_ui(m0)))
pt = pt0 * 2                                          # ||p_tail||, ratios <= 1/4
Sl = sum(2 * L * (2 * n + 1) for n in range(par, 2 * N, 2))
pl = sum(x * x for x in p).sqrt()
epsD = T * KP / arb.pi() * Sb2 + 2 * pt * pt      # tail block >= beta - ||C_tt|| - 2||p_t||^2 (either pole sign)
epsB = T * KP / arb.pi() * Sl.sqrt() * Sb2.sqrt() + 2 * pl * pt
print("K_Psi <=", KP.str(6), " eps_D <=", epsD.upper().str(3), " eps_B <=", epsB.upper().str(3), flush=True)
# ---- inertia certificate
n0 = int(sys.argv[3]) if len(sys.argv) > 3 else 16
Nh = N - n0
Mmid = np.array([[float(M[i, j].mid()) for j in range(N)] for i in range(N)])
def sub(A, r0, r1, c0, c1):
    B = arb_mat(r1 - r0, c1 - c0)
    for i in range(r0, r1):
        for j in range(c0, c1): B[i - r0, j - c0] = A[i, j]
    return B
Mll, Mhl, Mhh = sub(M, 0, n0, 0, n0), sub(M, n0, N, 0, n0), sub(M, n0, N, n0, N)
Mhl_f = Mmid[n0:, :n0]
gam = lambda k: k * 2.0 ** -53 / (1 - k * 2.0 ** -53)
def certify(s):
    s = arb(s)
    Dp = arb_mat(Nh, Nh)
    for i in range(Nh):
        for j in range(Nh): Dp[i, j] = Mhh[i, j]
        Dp[i, i] = Mhh[i, i] - s
    Df = np.array([[float(Dp[i, j].mid()) for j in range(Nh)] for i in range(Nh)])
    # rigorous lambda_min(Dp) >= mu via float Cholesky with a residual bound
    E1 = math.sqrt(sum((float(Dp[i, j].rad()) + abs(Df[i, j]) * 2.0 ** -52) ** 2 for i in range(Nh) for j in range(Nh)))
    tau = 0.5 * float(np.linalg.eigvalsh(Df)[0])        # target; certified below
    H = Df - tau * np.eye(Nh)
    Lc = np.linalg.cholesky(H)
    G = H - Lc @ Lc.T
    bnd = 2 * gam(Nh + 2) * (np.abs(H) + np.abs(Lc) @ np.abs(Lc).T) + np.abs(G)
    Gn = float(np.sqrt((bnd ** 2).sum())) * (1 + 1e-10) + 2 * Nh * tau * 2.0 ** -52
    mu = tau - Gn - E1
    assert mu > 0
    # X ~ Dp^{-1} Mhl, refined with arb residuals
    import scipy.linalg as sl
    cf = sl.cho_factor(Df)
    X = arb_mat(Nh, n0, [float(v) for v in sl.cho_solve(cf, Mhl_f).ravel()])
    for it in range(6):
        Rr = Mhl - Dp * X
        corr = sl.cho_solve(cf, np.array([[float(Rr[i, j].mid()) for j in range(n0)] for i in range(Nh)]))
        X = X + arb_mat(Nh, n0, [float(v) for v in corr.ravel()])
        X = X.mid()
    DX = Dp * X
    Rr = Mhl - DX
    rn2 = sum(float(abs(Rr[i, j]).upper()) ** 2 for i in range(Nh) for j in range(n0))
    eta = arb(rn2) / arb(mu)
    Xt = X.transpose()
    S = Mll - Xt * Mhl - Mhl.transpose() * X + Xt * DX
    for i in range(n0): S[i, i] = S[i, i] - s
    for i in range(n0):
        for j in range(n0): S[i, j] = S[i, j] + arb(0, 1) * eta
    # LDL^T in ball arithmetic; Sylvester: inertia = signs of pivots (all pivots must exclude 0)
    A_ = [[S[i, j] for j in range(n0)] for i in range(n0)]
    piv = []
    for k in range(n0):
        d = A_[k][k]
        if d.contains(0): return {"s": s.str(5), "ok": False, "failed_pivot": k, "pivot": d.str(5)}
        piv.append(d)
        for i in range(k + 1, n0):
            f = A_[i][k] / d
            for j in range(k + 1, n0): A_[i][j] = A_[i][j] - f * A_[k][j]
    neg = sum(1 for d in piv if d < 0)
    return {"s": s.str(5), "ok": True, "negatives_below_s": neg, "mu": mu, "resid2": rn2, "eta": float(eta.upper()),
            "pivots": [d.str(4) for d in piv]}
out = {"parity": ["even", "odd"][par], "L": f"{LP}/{LQ}", "Tsharp": TS, "N": N, "n0": n0, "beta": beta.str(15), "K_Psi": KP.str(8), "qerr_entry": qerr.str(4),
       "eps_D": epsD.upper().str(4), "eps_B": epsB.upper().str(4), "shifts": []}
def bis(target, lo, hi, steps=14):
    # lo: certified count <= target; hi: not.  log-scale bisection on s; returns best certified record
    best = None
    for _ in range(steps):
        mid = 10 ** ((math.log10(lo) + math.log10(hi)) / 2)
        sv = "%.4e" % mid
        res = certify(sv)
        good = res["ok"] and res["negatives_below_s"] <= target
        print(sv, good, res.get("negatives_below_s"), flush=True)
        if good: lo, best = float(sv), res
        else: hi = float(sv)
    return best
if sys.argv[1] == "lam2":
    # certified lower bound for the second even value: bisect s in [lo, hi] (log scale) for count <= 1
    r2 = bis(1, float(sys.argv[2]), float(sys.argv[5]) if len(sys.argv) > 5 else 1.0, steps=int(os.environ.get("GAP_STEPS", "12")))
    out["shifts"] = [r2]; print(r2)
    json.dump(out, open("la_lam2.json", "w"), indent=1, default=str); print("done", time.time() - t0); sys.exit(0)
elif sys.argv[1] == "bisect":
    if par == 0: r1 = bis(0, 1e-40, 1e-26); r2 = bis(1, 1e-26, 1e-18)
    else: r1 = bis(0, 1e-40, 1e-8); r2 = bis(1, 1e-30, 1e-4)
    out["shifts"] = [r1, r2]; print(r1); print(r2)
else:
    for sv in sys.argv[1:3]:
        res = certify(sv); print(res, flush=True); out["shifts"].append(res)
json.dump(out, open(f"la_{sys.argv[1]}_{sys.argv[2]}.json" if sys.argv[1] != "bisect" else f"la_bisect{sfx}.json", "w"), indent=1, default=str)
pickle.dump({"Mmid": Mmid}, open(f"Mmid{sfx}.pkl", "wb"))
print("done", time.time() - t0)
