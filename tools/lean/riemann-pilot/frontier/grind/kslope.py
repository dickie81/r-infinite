#!/usr/bin/env python3
"""Round 177: what sets each tone's volume 2/|rho zeta'(rho)|?  |rho| = hypotenuse of (1/2, gamma);
|zeta'(rho)| vs the gaps to the neighbouring zeros (Hadamard: zeta'(rho) ~ product over the other zeros)."""
import mpmath as mp, numpy as np, json
mp.mp.dps = 25
K = 300
g = [float(mp.zetazero(k).imag) for k in range(1, K + 2)]
rows = []
for k in range(1, K):          # skip first (one-sided neighbour)
    rho = mp.mpc(0.5, g[k]); d = abs(mp.zeta(rho, derivative=1))
    gl, gr = g[k] - g[k - 1], g[k + 1] - g[k]
    dens = np.log(g[k]/(2*np.pi))/(2*np.pi)
    rows.append((g[k], float(d), gl*dens, gr*dens))
G = np.array(rows); logd = np.log(G[:, 1]); t = G[:, 0]
# remove smooth growth of |zeta'| with height, then compare with normalised neighbour gaps
A = np.vstack([np.ones_like(t), np.log(np.log(t))]).T
res = logd - A @ np.linalg.lstsq(A, logd, rcond=None)[0]
lg = np.log(G[:, 2]) + np.log(G[:, 3])      # product of the two normalised neighbour gaps
nn = np.log(np.minimum(G[:, 2], G[:, 3]))
out = dict(K=K - 1, corr_logslope_vs_log_gap_product=round(float(np.corrcoef(res, lg)[0, 1]), 3),
           corr_logslope_vs_log_nearest_gap=round(float(np.corrcoef(res, nn)[0, 1]), 3))
print(json.dumps(out)); json.dump(out, open('kslope_results.json', 'w'))
