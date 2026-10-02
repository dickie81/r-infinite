"""Round 196: exact counts for Linnik's lemma."""
import itertools, json
from collections import Counter

def counts(p, k, a):
    M = p ** k
    ranges = [range(ai % p, M, p) for ai in a]
    cnt = Counter()
    for x in itertools.product(*ranges):
        cnt[tuple(sum(v ** j for v in x) % p ** j for j in range(1, k + 1))] += 1
    return max(cnt.values())

out = []
for (p, k) in [(3, 2), (5, 2), (7, 2), (5, 3)]:
    bound = p ** (k * (k - 1) // 2)
    best = 0
    for a in itertools.combinations(range(p), k):
        best = max(best, counts(p, k, a))
    rep = counts(p, k, (1,) * k)
    out.append(dict(p=p, k=k, bound=bound, max_distinct=best, L1=best <= bound,
                    L2=best == bound, repeated_max=rep, L3=rep > bound))
print(json.dumps(out, indent=1))
json.dump(out, open("klinnik_results.json", "w"), indent=1)
