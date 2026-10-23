#!/usr/bin/env python3
"""Round 88: score pre-registration 3 (PREREG_wiggles_balayage.md).
Model: F(delta) = min_T [4 sum_{g<T} ln((1+sqrt(1-g^2/T^2)) T/g) - delta*T], zeros of zeta (first 6700), T in [1.2 T0, 2.8 T0].
Between consecutive zeros dF/dT is decreasing (it is +inf just past each zero), so F is concave on each gap and
the minimum over T is attained exactly at a zero or at an end of the search interval: evaluated exactly there.
Null: the same with the zeros replaced by the smooth density (1/2pi) ln(g/2pi) (g > 2pi); convex, minimised numerically.
Measured: ln K00 on hamiltonian_grid_to3 + x20_55 (smooth fit + junction step, as kspectrum2.py).
Usage: kbalayage_model.py [out.json]"""
import sys, json, math, numpy as np
from mpmath import mpf
from scipy.integrate import quad
from scipy.optimize import minimize_scalar
Z = np.array(json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json")))
def load(f):
    return {round(x["delta"], 7): float(mpf(x["lnK00"])) for x in map(json.loads, filter(str.strip, open(f)))}
old = load("hamiltonian_grid_to3.jsonl"); new = load("hamiltonian_grid_x20_55.jsonl")
d = np.array(sorted(set(old) | set(new))); d = d[d >= 0.5]
meas = np.array([new.get(k, old.get(k)) for k in d]); isnew = np.array([k in new and k not in old for k in d], float)
x = np.exp(d)
def S(T):  # 4 sum_{g<T} ln((1+sqrt(1-g^2/T^2)) T/g)
    g = Z[Z < T]; return 4*np.sum(np.log((1 + np.sqrt(1 - (g/T)**2))*T/g))
def F_disc(dl):
    T0 = 2*np.pi*np.exp(dl); lo, hi = 1.2*T0, 2.8*T0
    cand = np.concatenate([[lo, hi], Z[(Z > lo) & (Z < hi)]])
    v = np.array([S(T) - dl*T for T in cand]); i = np.argmin(v)
    return v[i], cand[i]
def S_cont(T):
    f = lambda u: np.log((1 + np.sqrt(1 - u*u))/u)*np.log(T*u/(2*np.pi))/(2*np.pi)*T
    return 4*quad(f, 2*np.pi/T, 1, limit=200)[0]
def F_cont(dl):
    T0 = 2*np.pi*np.exp(dl); r = minimize_scalar(lambda T: S_cont(T) - dl*T, bounds=(1.2*T0, 2.8*T0), method="bounded", options={"xatol": 1e-9*T0})
    return r.fun, r.x
assert Z.max() > 2.8*2*np.pi*x.max(), "zero list too short"
md = np.array([F_disc(k) for k in d]); mc = np.array([F_cont(k) for k in d])
Md, Mc = -md[:, 0], -mc[:, 0]
B4 = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T
B6 = np.hstack([B4, isnew[:, None], (isnew*d)[:, None]])
res = lambda y, B: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
rm = res(meas, B6); rd = res(Md, B4); rc = res(Mc, B4)
def lines(r, lo=1.65, hi=54.6, nl=8):
    s = (x >= lo) & (x <= hi); u = x[s]
    g = np.linspace(u[0], u[-1], 8192); y = np.interp(g, u, r[s]); y = (y - np.polyval(np.polyfit(g, y, 3), g))*np.hanning(len(g))
    P = np.abs(np.fft.rfft(y))**2; w = 2*np.pi*np.fft.rfftfreq(len(g), g[1] - g[0]); pk = []
    for i in np.argsort(P)[::-1]:
        if i < 3 or w[i] > 26: continue
        if all(abs(i - j) > 3 for j in pk): pk.append(i)
        if len(pk) == nl: break
    tot = P[3:(w <= 26).sum()].sum()
    return [(round(float(w[i]), 2), round(float(P[i]/tot), 3)) for i in pk]  # sorted by power, strongest first
Lm, Ld, Lc = lines(rm), lines(rd), lines(rc)
corr = float(np.corrcoef(rm, rd)[0, 1])
gu = np.linspace(x[0], x[-1], 8192); corr_u = float(np.corrcoef(np.interp(gu, x, rm), np.interp(gu, x, rd))[0, 1])
vr = float(np.var(rc)/np.var(rd))
i_ok = abs(Ld[0][0] - 9.42) <= 0.2; ii_ok = corr >= 0.5; null_ok = vr < 0.1
out = dict(n=len(d), measured_lines=Lm, model_lines=Ld, null_lines=Lc, corr_gridpoints=corr, corr_uniform_x=corr_u,
           rms_measured=float(np.std(rm)), rms_model=float(np.std(rd)), rms_null=float(np.std(rc)), null_var_ratio=vr,
           Tstar_over_T0_range=[float((md[:, 1]/(2*np.pi*x)).min()), float((md[:, 1]/(2*np.pi*x)).max())],
           smooth_fit_model=[float(c) for c in np.linalg.lstsq(B4, Md, rcond=None)[0]],
           criterion_i=bool(i_ok), criterion_ii=bool(ii_ok), null=bool(null_ok), P3=bool(i_ok and ii_ok and null_ok))
for k, v in out.items(): print(k, v)
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
np.savez("kbalayage_model_series.npz", delta=d, measured=meas, model=Md, null=Mc, r_meas=rm, r_model=rd, r_null=rc, Tstar=md[:, 1])
