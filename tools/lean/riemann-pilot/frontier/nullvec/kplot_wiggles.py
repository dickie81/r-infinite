#!/usr/bin/env python3
"""Round 90 figure: the Hamiltonian e^{2phi} = dK_a(0,0)/da against the wiggles of ln K_a(0,0).
All grids merged (to3, x20_37_fine, x20_55). Residuals after the smooth fit (e^d, d, 1, e^-d) plus the x = 20 basis step."""
import json, numpy as np, matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
from mpmath import mpf
g, src = {}, {}
for f, tag in (("hamiltonian_grid_to3.jsonl", 0), ("hamiltonian_grid_x20_55.jsonl", 1), ("hamiltonian_grid_x20_37_fine.jsonl", 1)):
    for l in open(f):
        if l.strip(): r = json.loads(l); k = round(r["delta"], 7); g[k] = float(mpf(r["lnK00"])); src.setdefault(k, tag)
d = np.array(sorted(g)); d = d[d >= 0.5]; lk = np.array([g[k] for k in d]); x = np.exp(d)
hi = np.array([src[k] == 1 for k in d], float)
# Hamiltonian: e^{2phi} = dK00/da = 2 K00 dlnK00/ddelta, so 2phi = lnK00 + ln(2 dlnK00/ddelta); derivative per basis segment
L = np.empty_like(lk)
for m in (hi == 0, hi == 1): L[m] = np.gradient(lk[m], d[m])
tphi = lk + np.log(2*L)
B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d), hi, hi*d]).T
res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
rk, rh = res(lk), res(tphi)
edge = np.zeros_like(d, bool)
for m in (hi == 0, hi == 1): i = np.where(m)[0]; edge[i[:2]] = edge[i[-2:]] = True   # one-sided derivative ends
def spec(r, lo, hi_):
    s = (x >= lo) & (x <= hi_) & ~edge; u = x[s]; G = np.linspace(u[0], u[-1], 8192)
    y = np.interp(G, u, r[s]); y = (y - np.polyval(np.polyfit(G, y, 3), G))*np.hanning(len(G))
    P = np.abs(np.fft.rfft(y))**2; w = 2*np.pi*np.fft.rfftfreq(len(G), G[1] - G[0]); return w, P/P[w <= 26].max()
BLUE, ORANGE, INK, MUTED, GRID, SURF = "#2a78d6", "#eb6834", "#1f1f1e", "#6b6a65", "#e4e3dd", "#fcfcfb"
plt.rcParams.update({"font.size": 10, "axes.edgecolor": MUTED, "axes.labelcolor": INK, "xtick.color": MUTED,
                     "ytick.color": MUTED, "axes.spines.top": False, "axes.spines.right": False, "figure.facecolor": SURF,
                     "axes.facecolor": SURF, "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.6})
fig, ax = plt.subplots(4, 1, figsize=(11, 13), gridspec_kw={"height_ratios": [1, 1.1, 1.1, 1]})
ok = ~edge
ax[0].plot(x[ok], tphi[ok]/x[ok], color=BLUE, lw=2)
ax[0].set_ylabel("2φ / x   (nats per unit x)"); ax[0].set_xscale("log")
ax[0].set_title("The Hamiltonian H(a) = diag(e^{2φ}, e^{−2φ}),  e^{2φ} = dK_a(0,0)/da:  smooth to the eye, 2φ/x → 4π", loc="left", color=INK)
ax[0].axhline(4*np.pi, color=MUTED, lw=1, ls="--"); ax[0].text(1.7, 4*np.pi + 0.08, "4π", color=MUTED)
for a_, lo, hi_, t in ((ax[1], 1.65, 54.6, "Fine structure over the whole measured range"), (ax[2], 20, 30, "Zoom: x ∈ [20, 30] (0.03 grid)")):
    s = (x >= lo) & (x <= hi_) & ok
    a_.plot(x[s], rh[s], color=ORANGE, lw=1.4, label="Hamiltonian 2φ − smooth fit")
    a_.plot(x[s], rk[s], color=BLUE, lw=2, label="ln K_a(0,0) − smooth fit  (the wiggles)")
    a_.set_ylabel("residual (nats)"); a_.set_title(t, loc="left", color=INK); a_.axhline(0, color=MUTED, lw=0.8)
ax[1].axvline(20, color=MUTED, lw=0.8, ls=":"); ax[1].text(20.3, ax[1].get_ylim()[1]*0.85, "basis change", color=MUTED, fontsize=8)
ax[1].legend(loc="lower left", frameon=False); ax[2].set_xlabel("x = e^δ = e^{2a}")
c = np.corrcoef(rh[(x >= 1.65) & ok], rk[(x >= 1.65) & ok])[0, 1]
ax[2].text(0.99, 0.04, f"correlation {c:.3f}", transform=ax[2].transAxes, ha="right", color=MUTED)
for r, col, lab, lw in ((rh, ORANGE, "Hamiltonian 2φ", 1.4), (rk, BLUE, "ln K_a(0,0)", 2)):
    w, P = spec(r, 20, 37.04); m = w <= 80; ax[3].plot(w[m], P[m], color=col, lw=lw, label=lab)
for k in range(1, 9): ax[3].axvline(k*9.586, color=MUTED, lw=0.7, ls=":")
ax[3].text(9.586*8, 0.9, "8ω₁ (Bott lattice line)", color=MUTED, ha="right", fontsize=8)
ax[3].text(9.9, 0.9, "ω₁ = 9.59 ≈ 3π", color=MUTED, fontsize=8)
ax[3].set_yscale("log"); ax[3].set_ylim(1e-6, 2); ax[3].set_xlabel("ω (angular frequency in x)"); ax[3].set_ylabel("power (normalised)")
ax[3].set_title("Spectrum on x ∈ [20, 37] (Nyquist 105): nothing at the harmonics kω₁ (dotted); 16.7 and 23.5 are not multiples of ω₁", loc="left", color=INK)
ax[3].legend(loc="upper right", frameon=False, bbox_to_anchor=(1, 0.85))
fig.tight_layout(); fig.savefig("hamiltonian_wiggles.png", dpi=130)
print("corr", c, "rms rk", rk[ok].std(), "rms rh", rh[ok].std())
