"""Round 183: the ball tower from integers alone.

Step 1 (counting, integer d): the number of points of Z^d within |x|^2 <= x is the cumulative sum of the
coefficients of theta(q)^d, theta = sum_k q^{k^2} (only the squares go in). N_d(x)/x^{d/2} -> V_d?
Step 2 (every real d): the fine<->coarse symmetry of the integers (Poisson) gives
theta(e^{-pi t}) = t^{-1/2} theta(e^{-pi/t}), so t^{d/2} theta(e^{-pi t})^d -> 1 as t -> 0 for ANY real d.
Undoing the averaging-over-scales (Laplace) of x^{d/2} produces Gamma(d/2+1): V_d = pi^{d/2}/Gamma(d/2+1).
"""
import json, math
import numpy as np
from numpy.fft import rfft, irfft

N = 40000
g = np.zeros(N + 1); g[0] = 1
for k in range(1, int(N**0.5) + 1): g[k * k] += 2

def power_int(d):
    L = 1 << (2 * N + 2).bit_length(); G = rfft(g, L); f = np.zeros(N + 1); f[0] = 1.0
    F = rfft(f, L)
    for _ in range(d): F = rfft(irfft(F * G, L)[:N + 1], L)
    return irfft(F, L)[:N + 1]

out = {"step1_counting": {}, "step2_symmetry": {}}
print("Step 1: count integer points, d = 1..10")
for d in range(1, 11):
    Ncum = np.cumsum(power_int(d)); xs = np.arange(N // 2, N + 1)
    est = float(np.mean(Ncum[xs] / xs**(d / 2))); Vd = math.pi**(d / 2) / math.gamma(d / 2 + 1)
    out["step1_counting"][d] = dict(counted=est, V_d=Vd, rel_err=abs(est - Vd) / Vd)
    print(f"  d={d:2d}  counted {est:.5f}  formula {Vd:.5f}  rel err {abs(est-Vd)/Vd:.1e}")
c = {d: v["counted"] for d, v in out["step1_counting"].items()}
out["argmax_counted_volume"] = max(c, key=c.get)
S = {d: d * c[d] for d in c}          # sphere area S_{d-1} = d V_d, also from counting
out["argmax_counted_sphere_area_S_{d-1}"] = max(S, key=S.get)
print("  counted volume largest at d =", out["argmax_counted_volume"],
      "; counted sphere area S_{d-1} largest at d =", out["argmax_counted_sphere_area_S_{d-1}"])

print("Step 2: t^{d/2} theta(e^{-pi t})^d -> 1 for real d (Poisson symmetry of the integers)")
def theta(t): k = np.arange(-60, 61); return float(np.sum(np.exp(-math.pi * t * k * k)))
for d in [0.5, 2.5, 7.256946, 19.0, 217.0]:
    vals = [t**(d / 2) * theta(t)**d for t in (0.1, 0.03, 0.01)]
    out["step2_symmetry"][str(d)] = vals
    print(f"  d={d:<9} t=0.1,0.03,0.01 -> {[f'{v:.12f}' for v in vals]}")
json.dump(out, open("ktower_results.json", "w"), indent=1)
