"""Pre-registered numerics for the sharpening plan (round 213). See PREREG_sharpen.md."""
import math, json
out = {}
# P1: window count
bad = []
for R in range(16, 100001):
    j1 = -(-(R + 5) // 12)
    j3 = (5 * R - 6) // 24
    G = max(0, j3 - j1 + 1)
    if G < 1 or R * G / 6 - 2 < R * R / 100:
        bad.append(R)
out["P1_failures"] = bad[:20]
out["P1_holds"] = not bad
# P2: weak VMVT q=3; per-block rho in N-units = (R#G/6 - 2)/(20*2*l^2)
def rho(R, ell):
    j1 = -(-(R + 5) // 12); j3 = (5 * R - 6) // 24; G = j3 - j1 + 1
    return (R * G / 6 - 2) / (40 * ell ** 2)
def ell_weak(K): return K + 2 * K ** 3
def needed_logN(L, a, ellf):
    # smallest nu (log N) with rho >= L^-a for all nu' >= nu up to 5L/4 (scan)
    delta = L ** (-a)
    lo = None
    nus = [5 * L / 4 * (0.999 ** i) for i in range(20000)]
    for nu in nus:
        tau = 20 * L / nu
        if tau < 16: continue
        R = int(math.floor(tau)); K = R // 4 + 6
        if rho(R, ellf(K)) >= delta: lo = nu
        else: break
    return lo
res2 = {}
for a in (0.79, 0.80, 0.81):
    ratios = []
    for L in [10 ** e for e in (2, 3, 4, 5, 6, 8, 10, 12)]:
        nu = needed_logN(L, a, ell_weak)
        ratios.append(None if nu is None else nu * L ** (-a))
    res2[a] = ratios
out["P2_Lambda_times_L^-a"] = res2
# P3: S2 constants. Recursion as in VinoConst: C_{m+1} = max(trivial, 2*Kmain(C_m)).
def lgamma(x): return math.lgamma(x)
def logbinom(n, r): return lgamma(n + 1) - lgamma(r + 1) - lgamma(n - r + 1)
worst = 0; ellratio = 0
for k in range(2, 201):
    m_star = math.ceil(k * math.log(4 * k * k))
    logC = lgamma(k + 1)  # C_0 = k!
    eta = k * (k - 1) / 2
    for m in range(m_star):
        s = k + m * k
        e = 2 * s - k * (k + 1) / 2 + eta
        logKmain = math.log(16) + 2 * logbinom(s + k, k) + lgamma(k + 1) + k * k * math.log(2) \
            + (2 * s) * math.log(2) + e * math.log(2) + logC + math.log(2)
        eta2 = (1 - 1 / k) * eta
        e2 = 2 * (s + k) - k * (k + 1) / 2 + eta2
        logtriv = (2 * (s + k) - e2) * 8 * k * math.log(4 * k)
        logC = max(logKmain, logtriv); eta = eta2
    ell = k * (m_star + 1)
    worst = max(worst, logC / ell ** 2)
    ellratio = max(ellratio, ell / (k * k * math.log(4 * k)))
    assert eta <= 1 / 8 + 1e-12, (k, eta)
out["P3_max_logC_over_ell2"] = worst
out["P3_max_ell_over_k2log4k"] = ellratio
out["P3_holds"] = worst < 3 and ellratio <= 3
# P4
def ell_s2(K):
    m = math.ceil(K * math.log(4 * K * K)); return K * (m + 1)
cmin = float("inf")
for i in range(4000):
    lam = 0.8 * (10 ** (i / 4000 * math.log10(1e4 / 0.8)))
    R = int(math.floor(20 * lam)); K = R // 4 + 6
    r = rho(R, ell_s2(K)) * 20  # in N-units: u = N^{1/20}
    cmin = min(cmin, r * lam ** 2 * math.log(lam + 2) ** 2)
out["P4_c"] = cmin
out["P4_holds"] = cmin > 0
print(json.dumps(out, indent=1, default=str))
json.dump(out, open(__file__.replace(".py", "_results.json"), "w"), indent=1, default=str)
