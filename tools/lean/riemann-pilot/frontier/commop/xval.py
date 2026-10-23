#!/usr/bin/env python3
"""Train/test for a commuting Sturm-Liouville operator: fit (p, q) on the lowest levels, then measure the
relative non-commutation of the SAME operator on held-out higher levels."""
import numpy as np, json, pickle, sys
from numpy.polynomial import legendre as Lg
from numpy.polynomial.legendre import leggauss
from slweak import basis

def columns(funcs, t, w, a, K, pb, qb):
    B = {k: basis(k, K, a, t) for k in ("even", "odd")}
    cA, cB = [], []
    for kind_, f in [("p", f) for f in pb] + [("q", f) for f in qb]:
        A_, B_ = [], []
        for kind, v, dv in funcs:
            E, dE = B[kind]
            Lv = dE @ (w*f(t)*dv) if kind_ == "p" else E @ (w*f(t)*v)
            vc = E @ (w*v); vc = vc/np.linalg.norm(vc)
            A_.append(Lv - vc*(vc @ Lv)); B_.append(Lv)
        cA.append(A_); cB.append(B_)
    return cA, cB   # [param][func] -> vector

def fit_eval(train, test, t, w, a, K, pb, qb):
    cA, cB = columns(train + test, t, w, a, K, pb, qb)
    nt = len(train); npar = len(cA)
    A = np.array([np.concatenate(cA[p][:nt]) for p in range(npar)]).T
    B = np.array([np.concatenate(cB[p][:nt]) for p in range(npar)]).T
    Q, R = np.linalg.qr(B)
    U, sv, Vt = np.linalg.svd(A @ np.linalg.inv(R), full_matrices=False)
    th = np.linalg.solve(R, Vt[-1])
    def rel(j):
        a_ = sum(th[p]*cA[p][j] for p in range(npar)); b_ = sum(th[p]*cB[p][j] for p in range(npar))
        return float(np.linalg.norm(a_)/np.linalg.norm(b_))
    return float(sv[-1]), [rel(j) for j in range(nt)], [rel(j) for j in range(nt, nt + len(test))]

def fams(a, D):
    s = lambda m: (lambda t: (t/a)**(2*m)); ch = lambda m: (lambda t: np.cosh(2*m*t))
    return {"cosh": ([ch(m) for m in range(D+1)], [ch(m) for m in range(1, D+1)]),
            "poly": ([s(m) for m in range(D+1)], [s(m) for m in range(1, D+1)]),
            "poly+cosh": ([s(m) for m in range(D+1)] + [ch(m) for m in range(1, D+1)],
                          [s(m) for m in range(1, D+1)] + [ch(m) for m in range(1, D+1)])}

def interleave(ev, od):
    out = []
    for i in range(max(len(ev), len(od))):
        if i < len(ev): out.append(("even",) + tuple(ev[i]))
        if i < len(od): out.append(("odd",) + tuple(od[i]))
    return out

def leg_eigs(a, M, H_fn, m, n=2000):
    xs, ws = leggauss(400)
    P = np.array([Lg.legval(xs, np.eye(M)[k])*np.sqrt((2*k+1)/2) for k in range(M)])
    H = H_fn(P, xs, ws); E, V = np.linalg.eigh(H)
    x, w = leggauss(n); t = a*x; w = a*w; out = []
    for j in np.argsort(-E)[:m]:
        d = V[:, j]*np.array([np.sqrt((2*k+1)/2) for k in range(M)])
        v = Lg.legval(x, d)/np.sqrt(a); dv = Lg.legval(x, Lg.legder(d))/np.sqrt(a)/a
        kind = "even" if abs(Lg.legval(0.37, d) - Lg.legval(-0.37, d)) < 1e-6*np.max(np.abs(v)) else "odd"
        out.append((kind, v, dv))
    return t, w, out

if __name__ == "__main__":
    a = 2.0; K = 160; ntrain = 10
    J = pickle.load(open("phijets_2.0_17.pkl", "rb")); t, w = J["t"], J["w"]
    cases = {"Phi-jet ladder": interleave(J["even"], J["odd"])}
    # prolate control, same window, c chosen so ~16 concentrated functions
    c = 12.0
    t2, w2, pro = leg_eigs(a, 80, lambda P, xs, ws: -(np.diag([k*(k+1) for k in range(80)]) + (c*a)**2*((P*ws*xs**2) @ P.T)), 16)
    # gaussian-kernel control
    sig = 0.25
    t3, w3, gau = leg_eigs(a, 80, lambda P, xs, ws: (P*ws) @ (np.exp(-(a*(xs[:, None]-xs[None, :]))**2/(2*sig**2))*a) @ (P*ws).T, 16)
    for tag, fs, tt, ww in (("Phi-jet ladder", cases["Phi-jet ladder"], t, w), ("prolate c=12", pro, t2, w2), ("gauss s=0.25", gau, t3, w3)):
        fs = fs[:16]
        for D in (1, 2, 3, 4):
            for name, (pb, qb) in fams(a, D).items():
                if len(pb) + len(qb) > ntrain - 1: continue
                rho, tr, te = fit_eval(fs[:ntrain], fs[ntrain:], tt, ww, a, K, pb, qb)
                print(json.dumps({"case": tag, "fam": name, "D": D, "npar": len(pb) + len(qb),
                                  "train_rho": f"{rho:.2e}", "test_max": f"{max(te):.2e}", "test": [f"{x:.1e}" for x in te]}), flush=True)
