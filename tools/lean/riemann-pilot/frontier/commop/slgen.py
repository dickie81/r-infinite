#!/usr/bin/env python3
"""General weak-form fit: L v = -(p v')' + q v with p, q in user bases (lists of even functions of t).
Boundary term p(±a) v'(±a) e(±a) is reported (negligible when v is edge-flat)."""
import numpy as np, json, sys
from numpy.polynomial.legendre import leggauss
from slweak import basis, sample

def gen_fit(funcs, a, K, pbasis, qbasis, n=4000):
    x, w = leggauss(n); t = a*x; w = a*w
    B = {k: basis(k, K, a, t) for k in ("even", "odd")}
    cols_A, cols_B = [], []
    for kind_, f in [("p", f) for f in pbasis] + [("q", f) for f in qbasis]:
        cA, cB = [], []
        for kind, v, dv in funcs:
            E, dE = B[kind]
            Lv = dE @ (w*f(t)*dv) if kind_ == "p" else E @ (w*f(t)*v)
            vc = E @ (w*v); vc = vc/np.linalg.norm(vc)
            cA.append(Lv - vc*(vc @ Lv)); cB.append(Lv)
        cols_A.append(np.concatenate(cA)); cols_B.append(np.concatenate(cB))
    A = np.array(cols_A).T; Bm = np.array(cols_B).T
    Q, R = np.linalg.qr(Bm)
    U, sv, Vt = np.linalg.svd(A @ np.linalg.inv(R), full_matrices=False)
    th = np.linalg.solve(R, Vt[-1]); nK = A.shape[0]//len(funcs)
    per = [float(np.linalg.norm(A[j*nK:(j+1)*nK] @ th)/np.linalg.norm(Bm[j*nK:(j+1)*nK] @ th)) for j in range(len(funcs))]
    edge = max(abs(dv[-1]) + abs(dv[0]) for _, v, dv in funcs)/max(np.max(np.abs(dv)) for _, v, dv in funcs)
    return float(sv[-1]), per, edge

def families(a, D):
    s = lambda m: (lambda t: (t/a)**(2*m))
    ch = lambda m: (lambda t: np.cosh(2*m*t))
    return {
      "poly p free": ([s(m) for m in range(D+1)], [s(m) for m in range(1, D+1)]),
      "cosh(2mt)":   ([ch(m) for m in range(D+1)], [ch(m) for m in range(1, D+1)]),
      "poly+cosh":   ([s(m) for m in range(D+1)] + [ch(m) for m in range(1, D+1)],
                      [s(m) for m in range(1, D+1)] + [ch(m) for m in range(1, D+1)]),
    }
