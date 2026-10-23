"""Round 197: exact check of the Karatsuba step inequalities (spec Steps A-C)."""
import itertools, math, json
from collections import Counter

def pv(t, k):
    return tuple(sum(v ** j for v in t) for j in range(1, k + 1))

def J(vals, s, k):
    r = Counter(pv(x, k) for x in itertools.product(vals, repeat=s))
    return sum(c * c for c in r.values())

def distinct_mod(t, p):
    return len({v % p for v in t}) == len(t)

out = []
k, p = 2, 3
for s in (1, 2):
    for P in range(3, 10):
        I = range(1, P + 1)
        Q = -(-P // p)
        T = J(I, s + k, k)
        rb = Counter(pv(x, k) for x in itertools.product(I, repeat=s + k)
                     if len({v % p for v in x}) < k)
        TBB = sum(c * c for c in rb.values())
        U = [u for u in itertools.product(I, repeat=k) if distinct_mod(u, p)]
        ru = Counter(pv(u, k) for u in U)

        def conv(cls):
            W = Counter(pv(w, k) for w in itertools.product(cls, repeat=s))
            tot = Counter()
            for a1, c1 in ru.items():
                for a2, c2 in W.items():
                    tot[tuple(x + y for x, y in zip(a1, a2))] += c1 * c2
            return sum(c * c for c in tot.values())
        G = conv(list(I))
        Ga = [conv([n for n in I if n % p == a]) for a in range(p)]
        JQ = J(range(1, Q + 1), s, k)
        rhs3 = math.factorial(k) * P ** k * p ** (k * (k - 1) // 2) * JQ
        binom = math.comb(s + k, k)
        out.append(dict(s=s, P=P, T=T, TBB=TBB, G=G, K1=T <= 2 * TBB + 16 * binom ** 2 * G,
                        K2=G <= p ** (2 * s - 1) * sum(Ga),
                        K3=all(g <= rhs3 for g in Ga),
                        K3_slack=round(rhs3 / max(Ga), 2)))
for o in out:
    print(o)
json.dump(out, open("kkaratsuba_results.json", "w"), indent=1)
