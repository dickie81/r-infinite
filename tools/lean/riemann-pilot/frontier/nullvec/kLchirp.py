#!/usr/bin/env python3
"""Round 111, kernel stage (no tone information): for the L(s, chi_-4) lens, r_e (F'^2/s crossing 1), the round-108 chirp fit
(identical procedure), the window-phase rate beta', and the formula predictions
omega_p = 4 pi stat_r [ r (1 + ln(p/2qr)) + K~(r) ],  K~' = kappa - ln x,  K~(1.4) = beta'/4 pi,  q = 4."""
import json, glob, numpy as np
from scipy.optimize import least_squares
from sympy import primerange
import os
qc = int(os.environ.get('LQ', '4')); TAG = os.environ.get('LTAG', 'L'); DUMP = os.environ.get('LDUMP', 'rL106_')   # round 112: generalised
R = {}
for f in glob.glob(DUMP + "*.jsonl"):
    for l in open(f): o = json.loads(l); R[o["x"]] = o
x = np.array(sorted(R)); assert len(x) == 226
q = np.array(json.load(open(TAG + "quant.json")))[:len(R[x[0]]["w"])]; rho = np.log(qc*q/(2*np.pi))/(2*np.pi); spacing = 1/rho
re = []
for v in x:
    lg = np.log10(np.abs(np.array(R[v]["g"])) + 1e-300); r = q/(4*np.pi*v); jj = np.where(lg > 0)[0]
    if len(jj) == 0: re.append(np.nan); continue
    j = jj[-1]; re.append(float(r[j] + (r[j + 1] - r[j])*(lg[j]/(lg[j] - lg[j + 1]))))
re = np.array(re); ok = ~np.isnan(re); lam = float(np.nanmean(re))/0.8613
print(f"r_e: mean {np.nanmean(re):.4f} sd {np.nanstd(re):.4f} ({(~ok).sum()} windows excluded) -> lambda = {lam:.4f}")
re = np.where(ok, re, np.nanmean(re))
def gsmooth(v, g, mask):
    out = np.zeros_like(v); idx = np.where(mask)[0]
    for i in idx:
        wts = np.exp(-0.5*((g[idx] - g[i])/(3*spacing[i]))**2); out[i] = np.sum(wts*v[idx])/np.sum(wts)
    return out
def wave(par, g, xv, env):
    c0, c1, c2, ph, amp = par; L = 4*np.pi*xv*lam; u = g - 1.4*L        # amendment 1: region scaled by lambda
    return amp*env*np.cos(ph + (np.log(xv) + c0)*u + c1*u**2/(2*L) + c2*u**3/(3*L*L))
PARS, FRAC = [], []
for i, xv in enumerate(x):
    w = np.array(R[xv]["w"]); r = q/(4*np.pi*xv); ins = r < re[i]; out = ~ins
    s = gsmooth(w, q, ins) + gsmooth(w, q, out); osc = w - s; env = np.sqrt(2)*gsmooth(np.abs(osc), q, out)
    b = out & (r <= 2.2*lam); g, e, o = q[b], env[b], osc[b]; best = None
    for ph0 in np.linspace(0, 2*np.pi, 8, endpoint=False):
        f = least_squares(lambda p: wave(p, g, xv, e) - o, [0.33, 0.0, 0.0, ph0, 1.0], bounds=([-0.5, -3, -3, -20, 0], [1.2, 3, 3, 20, 3]))
        if best is None or f.cost < best.cost: best = f
    PARS.append(best.x); FRAC.append(1 - 2*best.cost/np.sum(o**2))
PARS = np.array(PARS); np.save(TAG + "chirp_params.npy", np.column_stack([x, PARS]))
c0, c1, c2 = PARS[:, 0].mean(), PARS[:, 1].mean(), PARS[:, 2].mean()
print(f"chirp: c0 {c0:.3f}±{PARS[:,0].std():.3f}  c1 {c1:.3f}±{PARS[:,1].std():.3f}  c2 {c2:.3f}±{PARS[:,2].std():.3f} | variance captured {np.mean(FRAC):.3f}")
kc = lambda r: c0 + c1*(r/lam - 1.4) + c2*(r/lam - 1.4)**2; Kint = lambda r: lam*(c0*(r/lam - 1.4) + c1*(r/lam - 1.4)**2/2 + c2*(r/lam - 1.4)**3/3)
u = np.unwrap(np.mod(PARS[:, 3], 2*np.pi)); seg = []
for lo, hi in ((3, 6), (6, 9), (9, 12.01)):
    m = (x >= lo) & (x < hi); seg.append(np.polyfit(x[m], u[m], 1)[0] - np.mean(4*np.pi*1.4*lam*(np.log(x[m]) + 1)))
bp = float(np.mean(seg)); C = bp/(4*np.pi); print("beta' per segment:", [round(s, 3) for s in seg], "mean", round(bp, 3))
rlo, rhi = float(re.mean()), 2.2*lam
def chi(p):
    if qc == 4: return 0 if p == 2 else (1 if p % 4 == 1 else -1)
    if qc == 8: return 0 if p == 2 else (1 if p % 8 in (1, 3) else -1)   # round 115: chi_-8
    return 0 if p == 3 else (1 if p % 3 == 1 else -1)
preds = []
for p in primerange(2, 102):
    if chi(p) == 0: continue
    r = np.linspace(rlo, rhi, 20001); f = np.log(2*qc*r/p) - kc(r); j = np.where(np.diff(np.sign(f)) != 0)[0]
    for i in j:
        rs = r[i] - f[i]*(r[i+1] - r[i])/(f[i+1] - f[i]); w = 4*np.pi*(rs*(1 + np.log(p/(2*qc*rs))) + C + Kint(rs))
        wl = [4*np.pi*(rs*(1 + np.log(p/(2*qc*rs))) + s/(4*np.pi) + Kint(rs)) for s in (min(seg), max(seg))]
        preds.append(dict(p=p, chi=chi(p), r_star=round(float(rs), 3), omega=round(float(w), 2), omega_range=[round(float(min(wl)), 2), round(float(max(wl)), 2)]))
for pr in preds: print(pr)
json.dump(dict(lam=lam, r_e_mean=float(re.mean()), r_e=re.tolist(), chirp=[c0, c1, c2], beta_prime=bp, beta_segments=seg, variance_captured=float(np.mean(FRAC)), predictions=preds), open(TAG + "predictions.json", "w"), indent=1)
