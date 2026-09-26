#!/usr/bin/env python3
"""Round 111, step 2: the L(s, chi_-4) lens. (a) merge zeros, check the count; (b) quantile base theta_chi/pi + c = k - 1/2 with c
from the mean of N(t) - theta_chi/pi over the zeros; (c) after kernel dumps rL106_*.jsonl exist: r_e and the chirp fit
(round 106/108 procedures with rho = ln(q t/2 pi)/2 pi). Usage: kLlens.py zeros | kLlens.py chirp"""
import sys, json, glob, numpy as np, mpmath as mp
from scipy.special import loggamma
import os
q = int(os.environ.get('LQ', '4')); TAG = os.environ.get('LTAG', 'L')   # round 112: 'L' = chi_-4 files, 'L3' = chi_-3
def theta(t): return t/2*np.log(q/np.pi) + np.imag(loggamma(0.75 + 0.5j*np.asarray(t)))
if sys.argv[1] == "zeros":
    Z, mx = [], 0
    for f in sorted(glob.glob(TAG + "z_*.json"), key=lambda s: float(s[len(TAG) + 2:-5])):
        o = json.load(open(f)); Z += o["zeros"]; mx = max(mx, o["max_rel_imag"])
    Z = np.array(sorted(set(np.round(Z, 10)))); print("zeros:", len(Z), "first", Z[:4], "last", Z[-1], "| max |Im Z|/|Z| on grid:", mx)
    Nsm = theta(Z)/np.pi; c = np.mean(np.arange(1, len(Z) + 1) - 0.5 - Nsm); print("count offset c =", round(float(c), 4), "(N(t) ~ theta/pi + c)")
    dev = np.arange(1, len(Z) + 1) - 0.5 - Nsm - c; print("max |N - smooth| at zeros:", round(float(np.max(abs(dev))), 3), "(a jump > 1.5 would signal a missed zero)")
    t = np.arange(1.0, 1000.0, 0.001); th = theta(t); k = np.floor(th/np.pi + c + 0.5); idx = np.where(np.diff(k) > 0)[0]
    Q = [float(t[i] + (t[i+1] - t[i])*((k[i+1] - 0.5 - c)*np.pi - th[i])/(th[i+1] - th[i])) for i in idx]
    Q = [v for v in Q if v >= min(Z) - 3]; n = min(len(Q), len(Z)); print("quantiles:", len(Q), "zeros:", len(Z), "-> using", n)
    json.dump([float(v) for v in Z[:n]], open(TAG + "zeros.json", "w")); json.dump(Q[:n], open(TAG + "quant.json", "w"))
    print("mean |zero - quantile|/spacing:", round(float(np.mean(abs(Z[:n] - np.array(Q[:n]))*np.log(q*Z[:n]/(2*np.pi))/(2*np.pi))), 3))
