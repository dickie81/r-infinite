"""Round 181: check the shell counts of the four 'multiplicative lattice balls' against their closed forms.
Z (1D), Z[i] and Z[w] (2D), Hurwitz quaternions (4D), integral octonions = E8 (8D). Also: every
element of norm p in the Hurwitz order is (up to the 24 units) one of p+1 'wheels'."""
import itertools, json, math
import numpy as np

def divs(n): return [d for d in range(1, n + 1) if n % d == 0]
def chi4(d): return 0 if d % 2 == 0 else (1 if d % 4 == 1 else -1)
def chi3(d): return 0 if d % 3 == 0 else (1 if d % 3 == 1 else -1)
M = 12
out = {}
# Z[i]: points of Z^2 with a^2+b^2=n ; closed form 4*sum chi4(d)
zi = [sum(1 for a in range(-4, 5) for b in range(-4, 5) if a*a + b*b == n) for n in range(1, M + 1)]
out["Z[i]"] = [zi, [4 * sum(chi4(d) for d in divs(n)) for n in range(1, M + 1)]]
# Z[w]: a^2+ab+b^2=n ; closed form 6*sum chi3(d)
zw = [sum(1 for a in range(-5, 6) for b in range(-5, 6) if a*a + a*b + b*b == n) for n in range(1, M + 1)]
out["Z[w]"] = [zw, [6 * sum(chi3(d) for d in divs(n)) for n in range(1, M + 1)]]
# Hurwitz: all-integer or all-half-integer 4-tuples; norm = sum of squares. Closed form 24*sum_{d|n, d odd} d
cnt = [0] * (M + 1)
for v in itertools.product(range(-4, 5), repeat=4):
    n = sum(x * x for x in v)
    if 1 <= n <= M: cnt[n] += 1
for v in itertools.product([x + 0.5 for x in range(-4, 4)], repeat=4):
    n = sum(x * x for x in v)
    if 1 <= n <= M and abs(n - round(n)) < 1e-9: cnt[round(n)] += 1
out["Hurwitz"] = [cnt[1:], [24 * sum(d for d in divs(n) if d % 2) for n in range(1, M + 1)]]
# E8 (norm = half the squared length, so the shells are 2n): D8 u (D8 + 1/2); closed form 240*sigma_3(n)
M8 = 4; cnt8 = [0] * (M8 + 1)
for v in itertools.product(range(-3, 4), repeat=8):
    s = sum(x * x for x in v)
    if s % 2 == 0 and sum(v) % 2 == 0 and 2 <= s <= 2 * M8: cnt8[s // 2] += 1
for v in itertools.product([x + 0.5 for x in range(-3, 3)], repeat=8):
    s = sum(x * x for x in v)
    if sum(v) % 2 == 0 and 2 <= s <= 2 * M8 and abs(s - round(s)) < 1e-9 and round(s) % 2 == 0: cnt8[round(s) // 2] += 1
out["E8"] = [cnt8[1:], [240 * sum(d**3 for d in divs(n)) for n in range(1, M8 + 1)]]
for k, (got, want) in out.items(): print(k, got == want, got)
# wheels: Hurwitz elements of odd prime norm p, divided by the 24 units, should be p+1
print("Hurwitz wheels per prime:", {p: out["Hurwitz"][0][p - 1] // 24 for p in (3, 5, 7, 11)})
json.dump({k: dict(counts=v[0], closed_form=v[1], match=v[0] == v[1]) for k, v in out.items()},
          open("klatticeballs_results.json", "w"), indent=1)
