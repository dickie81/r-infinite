#!/usr/bin/env python3
"""Round 112: widened kernel fit (PREREG_Lwide.md) for an L lens and the formula predictions.
Env: LQ (conductor), LTAG (file prefix: 'L' chi_-4, 'L3' chi_-3). Reads {TAG}106_*.jsonl kernel dumps, {TAG}quant.json.
Fit: oscillation / envelope on [r_e, 4.0 lambda], cubic chirp kappa = ln x + c0 + c1 s' + c2 s'^2 + c3 s'^3, s' = r/lambda - 1.4."""
import os, json, glob, numpy as np
from scipy.optimize import least_squares
from sympy import primerange
qc = int(os.environ["LQ"]); TAG = os.environ["LTAG"]; U = 4.0
R = {}
for f in glob.glob(TAG + "106_*.jsonl"):
    for l in open(f): o = json.loads(l); R[o["x"]] = o
x = np.array(sorted(R)); assert len(x) == 226, len(x)
q = np.array(json.load(open(TAG + "quant.json")))[:len(R[x[0]]["w"])]; rho = np.log(qc*q/(2*np.pi))/(2*np.pi); spacing = 1/rho
re = []
for v in x:
    lg = np.log10(np.abs(np.array(R[v]["g"])) + 1e-300); r = q/(4*np.pi*v); jj = np.where(lg > 0)[0]
    if len(jj) == 0: re.append(np.nan); continue
    j = jj[-1]; re.append(float(r[j] + (r[j + 1] - r[j])*(lg[j]/(lg[j] - lg[j + 1]))))
re = np.array(re); ok = ~np.isnan(re); lam = float(np.nanmean(re))/0.8613; re = np.where(ok, re, np.nanmean(re))
print(f"{TAG}: r_e mean {np.nanmean(re):.4f} sd {np.nanstd(re):.4f} ({(~ok).sum()} excluded) lambda {lam:.4f}")
def gsmooth(v, g, mask):
    out = np.zeros_like(v); idx = np.where(mask)[0]
    for i in idx:
        wts = np.exp(-0.5*((g[idx] - g[i])/(3*spacing[i]))**2); out[i] = np.sum(wts*v[idx])/np.sum(wts)
    return out
def phase(par, g, xv):
    c0, c1, c2, c3, ph = par; L = 4*np.pi*xv*lam; u = g - 1.4*L
    return ph + (np.log(xv) + c0)*u + c1*u**2/(2*L) + c2*u**3/(3*L*L) + c3*u**4/(4*L**3)
PARS, FRAC = [], []
for i, xv in enumerate(x):
    w = np.array(R[xv]["w"]); r = q/(4*np.pi*xv); ins = r < re[i]; out = ~ins
    s = gsmooth(w, q, ins) + gsmooth(w, q, out); osc = w - s; env = np.sqrt(2)*gsmooth(np.abs(osc), q, out)
    b = out & (r <= U*lam); g = q[b]; e = np.maximum(env[b], 0.1*np.median(env[b])); o = osc[b]/e
    best = None
    for ph0 in np.linspace(0, 2*np.pi, 8, endpoint=False):
        f = least_squares(lambda p: p[5]*np.cos(phase(p[:5], g, xv)) - o, [0.2, 0.0, 0.0, 0.0, ph0, 1.0],
                          bounds=([-0.8, -3, -3, -3, -20, 0], [1.5, 3, 3, 3, 20, 3]))
        if best is None or f.cost < best.cost: best = f
    PARS.append(best.x); FRAC.append(1 - 2*best.cost/np.sum(o**2))
PARS = np.array(PARS); np.save(TAG + "wide_params.npy", np.column_stack([x, PARS]))
c = PARS[:, :4].mean(0); print("chirp c0..c3:", np.round(c, 3), "sd", np.round(PARS[:, :4].std(0), 3), "| normalised variance captured", round(float(np.mean(FRAC)), 3))
kc = lambda r: c[0] + c[1]*(r/lam - 1.4) + c[2]*(r/lam - 1.4)**2 + c[3]*(r/lam - 1.4)**3
Kint = lambda r: lam*(c[0]*(r/lam - 1.4) + c[1]*(r/lam - 1.4)**2/2 + c[2]*(r/lam - 1.4)**3/3 + c[3]*(r/lam - 1.4)**4/4)
u = np.unwrap(np.mod(PARS[:, 4], 2*np.pi)); seg = []
for lo, hi in ((3, 6), (6, 9), (9, 12.01)):
    m = (x >= lo) & (x < hi); seg.append(np.polyfit(x[m], u[m], 1)[0] - np.mean(4*np.pi*1.4*lam*(np.log(x[m]) + 1)))
bp = float(np.mean(seg)); C = bp/(4*np.pi); print("beta' segments", np.round(seg, 3), "mean", round(bp, 3))
def chi(p):
    if qc == 4: return 0 if p == 2 else (1 if p % 4 == 1 else -1)
    return 0 if p == 3 else (1 if p % 3 == 1 else -1)
preds = []
for p in primerange(2, 102):
    if chi(p) == 0: continue
    r = np.linspace(float(re.mean()), U*lam, 40001); f = np.log(2*qc*r/p) - kc(r); j = np.where(np.diff(np.sign(f)) != 0)[0]
    for i in j:
        rs = r[i] - f[i]*(r[i+1] - r[i])/(f[i+1] - f[i]); wv = lambda s: 4*np.pi*(rs*(1 + np.log(p/(2*qc*rs))) + s/(4*np.pi) + Kint(rs))
        preds.append(dict(p=p, chi=chi(p), r_star=round(float(rs), 3), r_star_over_lambda=round(float(rs/lam), 2), far=bool(rs > 3.0*lam),
                          omega=round(float(wv(bp)), 2), omega_range=[round(float(min(wv(s) for s in seg)), 2), round(float(max(wv(s) for s in seg)), 2)]))
for pr in preds: print(pr)
json.dump(dict(lam=lam, r_e_mean=float(re.mean()), chirp=c.tolist(), chirp_sd=PARS[:, :4].std(0).tolist(), beta_prime=bp, beta_segments=seg,
               var_captured=float(np.mean(FRAC)), predictions=preds), open(TAG + "wide_predictions.json", "w"), indent=1)
