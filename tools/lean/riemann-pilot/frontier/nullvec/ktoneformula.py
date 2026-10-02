#!/usr/bin/env python3
"""Round 109: evaluate the derived tone formula
   omega_p = 4 pi * stat_r [ r (1 + ln(p/2) - ln r) + K~(r) ],   K~' = kappa_c = kappa - ln x,  K~(1.4) = beta'/(4 pi),
from the round-108 chirp fits (kappa_c) and the fitted window-phase rate beta' (no tone information used)."""
import numpy as np
P = np.load("kchirp_params.npy"); x = P[:, 0]; c0, c1, c2 = P[:, 1].mean(), P[:, 2].mean(), P[:, 3].mean()
kc = lambda r: c0 + c1*(r - 1.4) + c2*(r - 1.4)**2
Kint = lambda r: c0*(r - 1.4) + c1*(r - 1.4)**2/2 + c2*(r - 1.4)**3/3
u = np.unwrap(np.mod(P[:, 4], 2*np.pi)); seg = []
for lo, hi in ((3, 6), (6, 9), (9, 12.01)):
    m = (x >= lo) & (x < hi); seg.append(np.polyfit(x[m], u[m], 1)[0] - np.mean(4*np.pi*1.4*(np.log(x[m]) + 1)))   # fitted rate minus the rate 4 pi 1.4 (ln x + 1) of a pure 2a gamma phase
bp = float(np.mean(seg)); C = bp/(4*np.pi)
print("beta' per segment:", [round(s, 3) for s in seg], " mean", round(bp, 3), " -> K~(1.4) =", round(C, 4))
def tone(p, K0):
    r = np.linspace(0.8, 2.6, 36001); f = np.log(2*r/p) - kc(r); j = np.where(np.diff(np.sign(f)) != 0)[0]
    out = []
    for i in j:
        rs = r[i] - f[i]*(r[i + 1] - r[i])/(f[i + 1] - f[i]); out.append((rs, 4*np.pi*(rs*(1 + np.log(p/(2*rs))) + K0 + Kint(rs))))
    return out
for p, obs in ((2, 9.47), (3, 16.75), (4, None), (5, None), (7, None)):
    sols = tone(p, C); print(f"p={p}:", "; ".join(f"r*={rs:.3f} omega={w:.2f}" + ("" if 1.0 <= rs <= 2.2 else " [extrapolated]") for rs, w in sols) or "no stationary point in r in [0.8, 2.6]", f"| observed {obs}" if obs else "")
print("sensitivity: beta' range", [round(min(seg), 2), round(max(seg), 2)], "->",
      {p: [round(tone(p, s/(4*np.pi))[0][1], 2) for s in (min(seg), max(seg))] for p in (2, 3)})
print("no-chirp limit (K~ = 0): 2 pi p =", [round(2*np.pi*p, 2) for p in (2, 3)])
