"""Round 179: floor-first gear sets. See PREREG_smoothfloor.md (committed before this was run)."""
import json, sys, math
import numpy as np
from multiprocessing import Pool
from kfakegears import apply, exponent, primes_upto
import kfakegears as K

X = K.X

def target(sysid):
    if sysid == "S1": return lambda n: float(n)
    if sysid.startswith("A="):
        A = eval(sysid[2:], {"pi": math.pi, "e": math.e, "sqrt": math.sqrt})
        return lambda n: 1 + A * (n - 1)
    th = {"W25": 0.25, "W40": 0.40}[sysid]
    return lambda n: n + (0.5 * n**th * math.cos(5 * math.log(n)) if n >= 1000 else 0.0)

def run(sysid):
    T = target(sysid)
    a = np.zeros(X + 1, np.int64); a[1] = 1
    lam = np.zeros(X + 1)
    N, gears, overshoot = 1, [], 0
    for n in range(2, X + 1):
        an = int(a[n])
        g = round(T(n) - N - an)
        if g < 0: overshoot += 1; g = 0
        if g:
            for _ in range(g): apply(a, n, 1)
            gears.append((n, g)); L = math.log(n); p = n
            while p <= X: lam[p] += g * L; p *= n
        N += int(a[n])
    Ncum = np.cumsum(a).astype(float)
    x = np.arange(X + 1, dtype=float)
    Tv = np.array([T(v) if v >= 1 else 0.0 for v in range(X + 1)]) if sysid.startswith("W") else None
    if Tv is None:
        Tv = x.copy() if sysid == "S1" else None
        if Tv is None:
            A = eval(sysid[2:], {"pi": math.pi, "e": math.e, "sqrt": math.sqrt}); Tv = 1 + A * (x - 1)
    F = Ncum - Tv
    D = np.cumsum(lam) - x
    r = dict(sys=sysid, ngears=len(gears), gear_mass=int(sum(g for _, g in gears)),
             max_mult=int(max(g for _, g in gears)), overshoot_steps=overshoot,
             theta_F=exponent(x, F) - 0.0, theta_D=exponent(x, D),
             maxabsF_last_block=float(np.max(np.abs(F[2**22:2**23]))))
    if sysid == "S1":
        P = primes_upto(X); r["gears_equal_primes"] = bool(len(gears) == len(P) and all(g == 1 for _, g in gears)
                                                          and np.array_equal(np.array([q for q, _ in gears]), P))
    if sysid.startswith("W"):
        th = {"W25": 0.25, "W40": 0.40}[sysid]
        s = np.unique(np.geomspace(10**5, X, 4000).astype(int))
        M = np.c_[np.ones(s.size), np.cos(5 * np.log(x[s])), np.sin(5 * np.log(x[s]))]
        amps = {}
        for lab, y in (("floor", F[s]), ("drift", D[s])):
            c, *_ = np.linalg.lstsq(M, y / x[s]**th, rcond=None); amps[lab] = float(np.hypot(c[1], c[2]))
        r["tone_amp_floor"], r["tone_amp_drift"] = amps["floor"], amps["drift"]
        r["drift_over_floor_tone"] = amps["drift"] / amps["floor"]
    return r

if __name__ == "__main__":
    jobs = ["S1", "A=pi/4", "A=0.9", "A=1.1", "A=sqrt(2)", "A=2", "A=e", "W25", "W40"]
    if len(sys.argv) > 1: K.X = X = int(float(sys.argv[1]))
    with Pool(4) as pool:
        out = []
        for r in pool.imap_unordered(run, jobs):
            print(json.dumps(r), flush=True); out.append(r)
    if X == 10**7:
        json.dump(sorted(out, key=lambda r: r["sys"]), open("ksmoothfloor_results.json", "w"), indent=1)
