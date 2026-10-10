"""Round 179 post-hoc (not pre-registered): shape of the drift in the A != 1 floor-first systems.
Is D(x) an oscillation (zeros of the gear zeta) or a one-signed bias (a slow main-term correction)?"""
import json, math, numpy as np
from multiprocessing import Pool
import kfakegears as K
X = K.X
def run(A):
    a = np.zeros(X + 1, np.int64); a[1] = 1; lam = np.zeros(X + 1); N = 1
    for n in range(2, X + 1):
        g = max(0, round(1 + A * (n - 1) - N - int(a[n])))
        for _ in range(g): K.apply(a, n, 1)
        if g:
            L = math.log(n); p = n
            while p <= X: lam[p] += g * L; p *= n
        N += int(a[n])
    x = np.arange(X + 1, dtype=float); D = np.cumsum(lam) - x; F = np.cumsum(a) - (1 + A * (x - 1))
    s = np.unique(np.geomspace(10**4, X, 400).astype(int))
    blocks = []
    for j in range(14, 23):
        seg = D[2**j:2**(j + 1)]
        blocks.append(dict(j=j, min=float(seg.min()), max=float(seg.max()), frac_positive=float(np.mean(seg > 0))))
    return dict(A=A, D_over_x_at=[[int(v), float(D[v] / v)] for v in (10**4, 10**5, 10**6, 10**7)],
                F_over_x_at=[[int(v), float(F[v] / v)] for v in (10**4, 10**5, 10**6, 10**7)],
                sign_changes_of_D=int(np.sum(np.diff(np.sign(D[s])) != 0)), blocks=blocks)
if __name__ == "__main__":
    with Pool(3) as p: out = p.map(run, [math.pi / 4, 0.9, 1.1])
    for r in out: print(json.dumps({k: r[k] for k in ("A", "D_over_x_at", "sign_changes_of_D")}), [b["frac_positive"] for b in r["blocks"]])
    json.dump(out, open("ksmoothfloor_posthoc.json", "w"), indent=1)
