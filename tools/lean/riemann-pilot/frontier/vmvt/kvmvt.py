"""Round 194: exact Vinogradov mean values J_{s,k}(N) by counting power-sum vectors."""
import itertools, math, json
from collections import Counter

def J(s, k, N):
    r = Counter()
    for x in itertools.product(range(1, N + 1), repeat=s):
        r[tuple(sum(v ** j for v in x) for j in range(1, k + 1))] += 1
    return sum(c * c for c in r.values())

def perm_pairs(s, N):
    tot = 0
    for x in itertools.product(range(1, N + 1), repeat=s):
        c = Counter(x)
        tot += math.factorial(s) // math.prod(math.factorial(m) for m in c.values())
    return tot

out = {"P1": [], "P3": []}
for (s, k, N) in [(1, 1, 9), (2, 2, 9), (2, 3, 8), (3, 3, 8), (3, 4, 7), (4, 4, 6)]:
    a, b = J(s, k, N), perm_pairs(s, N)
    out["P1"].append((s, k, N, a, b, a == b))
for (k, s) in [(2, 3), (2, 4), (3, 4), (3, 5), (3, 6)]:
    rows = []
    for N in ([4, 6, 8, 10, 12, 16, 20] if s <= 4 else [3, 4, 5, 6, 7, 8]):
        if N ** s > 3_000_000:
            break
        j = J(s, k, N)
        main = N ** s + N ** (2 * s - k * (k + 1) // 2)
        assert N ** s <= j <= N ** (2 * s)
        rows.append((N, j, round(j / main, 3)))
    out["P3"].append({"k": k, "s": s, "rows": rows})
print(json.dumps(out, indent=1))
json.dump(out, open("kvmvt_results.json", "w"), indent=1)
