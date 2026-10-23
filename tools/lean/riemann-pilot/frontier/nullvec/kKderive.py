#!/usr/bin/env python3
"""Round 114: K~ derived from Gamma. Beyond the wall (w = r > 1) the closed-form multiplier
ln M = T0 [w arcsin w + sqrt(1-w^2) - 1] (T0 = 2 pi x) has phase T0 [sqrt(w^2-1) - w arccosh w]; the kernel F F' carries twice
it; on the Gamma nodes (2 theta(g_k) = (2k-3) pi) the wave is represented shifted by 2 theta(g) ~ g ln x + 4 pi x r (ln 2r - 1).
=> Phi(g, x) = g ln x + 4 pi x K(r),  K(r) = r ln(2r) - r + sqrt(r^2-1) - r arccosh(r)   (no fitted constant).
Checks (kernel level, no tones): (a) K'(r) = ln 2r - arccosh r vs the round-108 fitted chirp; (b) K(1.4) vs the measured window-phase
offset beta'/4pi; (c) a per-window fit of ONLY (phase offset, amplitude) with the derived phase: variance captured vs round 108's
5-parameter chirp; (d) per-prime first-order tones with that kernel."""
import json, glob, numpy as np
from scipy.optimize import least_squares
exec(open("kheterodyne.py").read().split("W, M1, M2, KAP, FRAC = [], [], [], [], []")[0])     # R, x, q, rho, re, gsmooth
K = lambda r: r*np.log(2*r) - r + np.sqrt(np.maximum(r*r - 1, 0)) - r*np.arccosh(np.maximum(r, 1))
Kp = lambda r: np.log(2*r) - np.arccosh(np.maximum(r, 1))
P = np.load("kchirp_params.npy"); c = P[:, 1:4].mean(0)
kc_fit = lambda r: c[0] + c[1]*(r - 1.4) + c[2]*(r - 1.4)**2
print("(a) chirp  r:  fitted kappa_c  |  derived ln2r - arccosh r")
for r in (1.0, 1.2, 1.4, 1.6, 1.8, 2.0, 2.2): print(f"      {r:.1f}:    {kc_fit(r):.3f}     |    {Kp(r):.3f}")
print(f"(b) K(1.4): derived {K(1.4):.4f}  vs measured beta'/4pi = -0.1834 (range -0.195 .. -0.170)")
def Sp(g, p): return -np.imag(np.log(1 - p**(-0.5 - 1j*g)))/np.pi
d = np.log(x); B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T; res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
def peaks(y, lo=1.5, hi=40, n=3):
    rr = res(y); G = np.linspace(x[0], x[-1], 4096); yy = np.interp(G, x, rr); yy = (yy - np.polyval(np.polyfit(G, yy, 3), G))*np.hanning(len(G))
    Y = np.abs(np.fft.rfft(yy, 16*len(G)))**2; w = 2*np.pi*np.fft.rfftfreq(16*len(G), G[1] - G[0]); s = (w > lo) & (w < hi); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])[:n]
    return [(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc]
W, MD, FR, PH = [], [], [], []
for i, xv in enumerate(x):
    w = np.array(R[xv]["w"]); r = q/(4*np.pi*xv); ins = r < re[i]; out = ~ins
    s = gsmooth(w, q, ins) + gsmooth(w, q, out); osc = w - s; env = np.sqrt(2)*gsmooth(np.abs(osc), q, out)
    b = out & (r <= 2.2); g, e, o = q[b], env[b], osc[b]
    base = g*np.log(xv) + 4*np.pi*xv*K(g/(4*np.pi*xv))
    X = np.vstack([e*np.cos(base), e*np.sin(base)]).T; cc, *_ = np.linalg.lstsq(X, o, rcond=None)   # only amplitude and phase offset
    FR.append(1 - np.sum((o - X @ cc)**2)/np.sum(o**2)); PH.append(np.arctan2(-cc[1], cc[0]))
    wave = np.zeros_like(w); bo = out; gb = q[bo]; bb = gb*np.log(xv) + 4*np.pi*xv*K(gb/(4*np.pi*xv))
    wave[bo] = env[bo]*(cc[0]*np.cos(bb) + cc[1]*np.sin(bb)); W.append(w); MD.append(s + wave)
W, MD = np.array(W), np.array(MD); PH = np.unwrap(np.array(PH))
print(f"(c) variance of the oscillation captured with the DERIVED phase (2 params/window): {np.mean(FR):.3f}  [round 108 fitted chirp, 5 params: 0.942]")
print(f"    residual phase offset across windows: sd {np.std(PH):.3f} rad, drift slope {np.polyfit(x, PH, 1)[0]:.3f} rad per unit x")
for p, obs in ((2, 9.47), (3, 16.75)):
    print(f"(d) p={p}: true kernel {peaks(-W @ (Sp(q, p)/rho))} | derived-phase kernel {peaks(-MD @ (Sp(q, p)/rho))}")
