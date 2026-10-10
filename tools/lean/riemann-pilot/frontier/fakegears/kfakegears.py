"""Round 178: fake gear sets. See PREREG_fakegears.md (committed before this was run).

Each system is a set of gears (norm q, weight w): the Euler factor 1/(1 - w q^{-s}).
Floor N(x) = generalised-integer count; drift D(x) = log-weighted gear count - main term.
"""
import json, sys
import numpy as np
from multiprocessing import Pool

X = 10**7
RHO = 0.75 + 5j

def primes_upto(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def cramer(seed):
    rng = np.random.default_rng(seed)
    n = np.arange(2, X + 1)
    return n[rng.random(n.size) < np.minimum(1.0, 1.0 / np.log(n))]

def apply(a, q, w):
    """Multiply the Dirichlet series in a by 1/(1 - w q^{-s})."""
    orig = a[1:X // q + 1].copy()
    step, wk = q, w
    while step <= X:
        a[step::step] += wk * orig[:X // step]
        if step > X // q: break
        step *= q; wk *= w

def build(gears):
    """gears: list of (norm, weight, log-weight for drift)."""
    a = np.zeros(X + 1, np.int64); a[1] = 1
    g = np.zeros(X + 1)
    for q, w, lw in gears:
        apply(a, int(q), int(w)); g[int(q)] += lw
    return np.cumsum(a).astype(float), np.cumsum(g)

def gears_for(sysid, seed):
    P = primes_upto(X)
    if sysid == "R1": return [(p, 1, np.log(p)) for p in P], 1, 1.0, "x"
    if sysid == "C1": return [(q, 1, np.log(q)) for q in cramer(seed)], 1, None, "x"
    if sysid in ("R2", "T2", "CT2"):
        base = cramer(seed) if sysid == "CT2" else P
        rng = np.random.default_rng(1000 + seed)
        G = []
        for p in base:
            if p == 2: G.append((2, 1, np.log(2))); continue
            split = (p % 4 == 1) if sysid == "R2" else (rng.random() < 0.5)
            if split: G += [(p, 1, np.log(p)), (p, 1, np.log(p))]
            elif p * p <= X: G.append((p * p, 1, 2 * np.log(p)))
        return G, 1, (np.pi / 4 if sysid == "R2" else None), "x"
    if sysid in ("R4", "C4"):
        base = P if sysid == "R4" else cramer(seed)
        G = []
        for q in base:
            G += [(q, 1, np.log(q)), (q, q, q * np.log(q))]
        return G, 2, (np.pi**2 / 12 if sysid == "R4" else None), "x+x2"
    raise ValueError(sysid)

def plant_gears(sign):
    P = primes_upto(X)
    n = np.arange(X + 1, dtype=float); n[0] = 1
    th = np.zeros(X + 1); th[P] = np.log(P); th = np.cumsum(th)
    t = np.clip((np.log10(n) - 3.0), 0, 1); ramp = t * t * (3 - 2 * t)
    delta = sign * 2 * np.real(n.astype(complex) ** RHO / RHO) * ramp
    T = (th + delta).tolist(); L = np.log(n).tolist()
    cur, G = 0.0, []
    for k in range(2, X + 1):
        if T[k] - cur > 0.5 * L[k]:
            cur += L[k]; G.append((k, 1, L[k]))
    return G

def exponent(x, err):
    js = range(14, 23); lx, ly = [], []
    for j in js:
        lo, hi = 2**j, 2**(j + 1)
        lx.append(np.log(lo)); ly.append(np.log(np.max(np.abs(err[lo:hi])) + 1e-300))
    return float(np.polyfit(lx, ly, 1)[0])

def run(job):
    sysid, seed = job
    if sysid in ("Z1", "P1"):
        G, k, A, main = plant_gears(-1 if sysid == "Z1" else +1), 1, None, "x"
    else:
        G, k, A, main = gears_for(sysid, seed)
    N, th = build(G)
    x = np.arange(X + 1, dtype=float)
    if A is None:
        s = np.unique(np.geomspace(X // 100, X, 2000).astype(int))
        A = float(np.sum(N[s] * x[s]**k) / np.sum(x[s]**(2 * k)))
    F = N - A * x**k
    D = th - (x if main == "x" else x + x**2 / 2)
    tF, tD = exponent(x, F) - (k - 1), exponent(x, D) - (k - 1)
    return dict(sys=sysid, seed=seed, A=A, theta_F=tF, theta_D=tD,
                G_margin=tD - max(0.5, tF), ngears=len(G))

if __name__ == "__main__":
    jobs = [("R1", 0), ("R2", 0), ("R4", 0), ("Z1", 0), ("P1", 0)]
    jobs += [(s, seed) for s in ("C1", "T2", "CT2", "C4") for seed in (1, 2, 3)]
    with Pool(4) as pool:
        out = []
        for r in pool.imap_unordered(run, jobs):
            print(json.dumps(r), flush=True); out.append(r)
    json.dump(sorted(out, key=lambda r: (r["sys"], r["seed"])),
              open("kfakegears_results.json", "w"), indent=1)
