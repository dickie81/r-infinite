"""Round 203: numerical check of spec steps (B) and (D)."""
import itertools, math, json, random
import numpy as np
from collections import Counter
random.seed(203)

def e(x):
    return np.exp(2j * np.pi * x)

def pv(t, K):
    return tuple(sum(v ** j for v in t) for j in range(1, K + 1))

def check_D(K, M, l, trials=200):
    nu = Counter(pv(b, K) for b in itertools.product(range(1, M + 1), repeat=l))
    X = list(nu)
    J = sum(c * c for c in nu.values())
    Xa = np.array(X, dtype=float)
    ratios, ok = [], True
    for _ in range(trials):
        al = np.array([random.uniform(-0.5, 0.5) for _ in range(K)])
        S = sum(e(sum(al[j] * a ** (j + 1) * b ** (j + 1) for j in range(K)))
                for a in range(1, M + 1) for b in range(1, M + 1))
        Z = 0.0
        for x in Xa:
            Z = max(Z, sum(abs(np.sum(e(((x - xp) * al) @ Xa.T))) for xp in Xa))
        lhs = abs(S) ** (2 * l * l)
        rhs = M ** (4 * l * (l - 1)) * J ** 2 * Z
        ok &= lhs <= rhs * (1 + 1e-9)
        ratios.append(rhs / max(lhs, 1e-300))
    return bool(ok), float(np.median(ratios))

def dist(x):
    return abs(x - round(x))

def check_B(trials=500):
    ok, rat = True, []
    for _ in range(trials):
        a = random.uniform(1e-3, 0.5)
        Xn, Y = random.randint(1, 60), random.randint(1, 60)
        lhs = sum(min(Y, 1 / (2 * dist(a * z)) if dist(a * z) > 0 else Y)
                  for z in range(-Xn, Xn + 1))
        rhs = (4 * Xn * a + 2) * (2 * Y + (2 / a) * (1 + math.log(1 / a)))
        ok &= lhs <= rhs
        rat.append(rhs / lhs)
    return bool(ok), float(np.median(rat))

out = {"D": {}, "B": None}
for (K, M, l) in [(2, 4, 1), (2, 4, 2), (3, 3, 2), (2, 6, 2)]:
    out["D"][f"K{K}M{M}l{l}"] = check_D(K, M, l)
out["B"] = check_B()
print(json.dumps(out, indent=1))
json.dump(out, open("kexpsum_results.json", "w"), indent=1)
