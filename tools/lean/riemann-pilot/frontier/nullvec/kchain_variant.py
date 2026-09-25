#!/usr/bin/env python3
"""Round 91: kchain_list.py with a modified prime side. VARIANT = 'le:M' (keep prime powers n <= M), 'gt:M' (drop n <= M),
'lam:L' (scale every Lambda(n) by L), 'drop:n1,n2,..' (drop those n), 'full'.
Usage: kchain_variant.py VARIANT Kfac PF x1 x2 ...  (JSON lines, with the variant recorded)"""
import sys, math, json
import nullvec_fast  # noqa: path
import weil_prime_gram as W
V = sys.argv[1]; orig = W.prime_powers
kind, _, arg = V.partition(":")
if kind == "le": W.prime_powers = lambda N: [t for t in orig(N) if t[0] <= float(arg)]
elif kind == "gt": W.prime_powers = lambda N: [t for t in orig(N) if t[0] > float(arg)]
elif kind == "lam": W.prime_powers = lambda N: [(n, p**float(arg)) for n, p in orig(N)]
elif kind == "drop": S = {int(s) for s in arg.split(",")}; W.prime_powers = lambda N: [t for t in orig(N) if t[0] not in S]
else: assert kind == "full"
src = open(__file__.replace("kchain_variant.py", "kchain.py")).read().split("d0, d1, st =")[0]
exec(src)
Kf, PF = float(sys.argv[2]), float(sys.argv[3])
for xv in map(float, sys.argv[4:]):
    d = round(math.log(xv), 7); K = max(40, int(Kf*math.exp(d)) + 40); prec = int(300 + PF*math.exp(d))
    try: r = run(d, K, prec)
    except Exception as e: r = {"delta": d, "K": K, "error": repr(e)[:120]}
    r["variant"] = V; print(json.dumps(r), flush=True)
