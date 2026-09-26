#!/usr/bin/env python3
"""Round 82: tabulate the window chain's Hamiltonian H(a) = diag(e^{2 phi}, e^{-2 phi}),
e^{2 phi} = h = dK_a(0,0)/da = K00 L,  phi = (l + ln L)/2,  Dirac potential q = dphi/da.
Usage: ktable.py 'grid*.jsonl' out.json [hw] [plot.png]"""
import sys, json, glob, math
import numpy as np
from mpmath import mpf
rows = []
for f in sorted(glob.glob(sys.argv[1])): rows += [json.loads(l) for l in open(f) if l.strip()]
rows.sort(key=lambda x: x["delta"])
d = np.array([x["delta"] for x in rows]); l = np.array([float(mpf(x["lnK00"])) for x in rows])
hw = float(sys.argv[3]) if len(sys.argv) > 3 else 0.02
def fit(dd):
    m = np.abs(d - dd) <= hw + 1e-12
    c = np.polyfit(d[m] - dd, l[m], 3); return c[2], 2*c[1]      # l', l''
tab = []
for dd in d:
    if dd - d[0] < hw or d[-1] - dd < hw: continue
    lp, lpp = fit(dd)
    L = 2*lp                                  # d ln K00 / da
    phi = 0.5*(np.interp(dd, d, l) + math.log(L))
    q = 2*0.5*(lp + lpp/lp)                   # dphi/da = 2 dphi/ddelta
    tab.append({"a": dd/2, "delta": dd, "lnK00": float(np.interp(dd, d, l)), "L": L, "phi": phi, "q": q,
                "q_smooth_model": 4*math.pi*math.exp(dd)})
json.dump({"note": "H(a) = diag(e^{2phi}, e^{-2phi}); q = phi'(a); K00 = K_a(0,0) = sup (int g)^2/Q(g) over g supported in [-a,a]",
           "hw": hw, "table": tab}, open(sys.argv[2], "w"), indent=0)
print(f"{len(tab)} rows; a in [{tab[0]['a']:.4f}, {tab[-1]['a']:.4f}]")
if len(sys.argv) > 4:
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    a = np.array([t["a"] for t in tab]); q = np.array([t["q"] for t in tab])
    fig, ax = plt.subplots(2, 1, figsize=(9, 7), sharex=True)
    ax[0].plot(a, q, lw=1, label="q(a) = φ'(a), measured")
    ax[0].plot(a, 4*np.pi*np.exp(2*a), "--", lw=1, label="4π e^{2a} (reduced model)")
    ax[0].set_ylabel("Dirac potential q"); ax[0].legend()
    ax[1].plot(a, q - 4*np.pi*np.exp(2*a), lw=1)
    for n in range(2, 60):
        f = [p for p in range(2, n + 1) if n % p == 0][0]; m = n
        while m % f == 0: m //= f
        if m == 1 and a[0] <= math.log(n)/2 <= a[-1]:
            ax[1].axvline(math.log(n)/2, color="r", lw=0.6, alpha=0.6)
            ax[1].text(math.log(n)/2, ax[1].get_ylim()[1]*0.9 if n < 20 else 0, str(n), fontsize=7, color="r")
    ax[1].set_ylabel("q − 4π e^{2a}"); ax[1].set_xlabel("window half-width a  (prime powers n at a = ½ log n, red)")
    fig.suptitle("Hamiltonian of the Weil window chain: H(a) = diag(e^{2φ}, e^{−2φ})")
    fig.tight_layout(); fig.savefig(sys.argv[4], dpi=130)
