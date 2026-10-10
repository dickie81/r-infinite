#!/usr/bin/env python3
"""Weak-form test: is {v_j} (both parities) a set of simultaneous eigenfunctions of
  L v = -(p v')' + q v,  p = (1 - s^2) sum_{m<=D} alpha_m s^{2m},  q = sum_{1<=m<=D} beta_m s^{2m},  s = t/a ?
Galerkin in the orthonormal cos/sin basis e_i (K modes per parity): (Lv)_i = int p e_i' v' + q e_i v.
rho = min over (alpha, beta) of sqrt( sum_j |(I - v_j v_j^T) L v_j|^2 / sum_j |L v_j|^2 ), and the fitted operator."""
import numpy as np, json, sys
from numpy.polynomial.legendre import leggauss

def basis(kind, K, a, t):
    ks = range(K) if kind == "even" else range(1, K + 1)
    E, dE = [], []
    for k in ks:
        w = k*np.pi/a; nrm = np.sqrt(2*a if k == 0 else a)
        if kind == "even": E.append(np.cos(w*t)/nrm); dE.append(-w*np.sin(w*t)/nrm)
        else: E.append(np.sin(w*t)/nrm); dE.append(w*np.cos(w*t)/nrm)
    return np.array(E), np.array(dE)

def weak_fit(funcs, a, D, K, n=4000):
    """funcs: list of (kind, v, dv) sampled on the Gauss nodes."""
    x, w = leggauss(n); t = a*x; w = a*w; s = x
    B = {k: basis(k, K, a, t) for k in ("even", "odd")}
    terms = [("p", m) for m in range(D + 1)] + [("q", m) for m in range(1, D + 1)]
    cols_A, cols_B = [], []
    for kind_, m in terms:
        cA, cB = [], []
        for kind, v, dv in funcs:
            E, dE = B[kind]
            if kind_ == "p": Lv = dE @ (w*(1 - s**2)*s**(2*m)*dv)
            else: Lv = E @ (w*s**(2*m)*v)
            vc = E @ (w*v); vc = vc/np.linalg.norm(vc)
            cA.append(Lv - vc*(vc @ Lv)); cB.append(Lv)
        cols_A.append(np.concatenate(cA)); cols_B.append(np.concatenate(cB))
    A = np.array(cols_A).T; Bm = np.array(cols_B).T
    Q, R = np.linalg.qr(Bm)
    U, sv, Vt = np.linalg.svd(A @ np.linalg.inv(R), full_matrices=False)
    th = np.linalg.solve(R, Vt[-1])
    L = len(funcs); per = []
    nK = A.shape[0]//L
    for j in range(L):
        per.append(float(np.linalg.norm(A[j*nK:(j+1)*nK] @ th)/np.linalg.norm(Bm[j*nK:(j+1)*nK] @ th)))
    return sv[-1], th/np.max(np.abs(th)), per, terms

def sample(coefs, kind, a, t):
    k0 = 0 if kind == "even" else 1
    v = np.zeros_like(t); dv = np.zeros_like(t)
    for i, c in enumerate(coefs):
        w = (i + k0)*np.pi/a
        if kind == "even": v += c*np.cos(w*t); dv += -c*w*np.sin(w*t)
        else: v += c*np.sin(w*t); dv += c*w*np.cos(w*t)
    return v, dv

def report(tag, funcs, a, K, Dmax):
    for D in range(0, Dmax + 1):
        rho, th, per, terms = weak_fit(funcs, a, D, K)
        print(json.dumps({"case": tag, "D": D, "rho": float(rho), "per_level": [round(p, 8) for p in per],
                          "theta": {f"{b}{m}": round(float(v), 5) for (b, m), v in zip(terms, th)}}), flush=True)
