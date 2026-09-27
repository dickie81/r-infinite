#!/usr/bin/env python3
"""Controls for slfit: top eigenfunctions of translation-invariant kernels on [-a,a] with Fourier weight W(w):
<phi_i, K phi_j> = (1/2pi) int phihat_i phihat_j^* W.  prolate: W = 1_{|w|<c}; gauss: W = exp(-s^2 w^2/2)."""
import numpy as np, json, sys
from numpy.polynomial.legendre import leggauss
from slfit import series, fit

def hat(k, kind, a, om):
    w = k*np.pi/a
    if kind == "even":
        return a*(np.sinc((om - w)*a/np.pi) + np.sinc((om + w)*a/np.pi))  # int cos(wt) e^{i om t}
    return a*(np.sinc((om - w)*a/np.pi) - np.sinc((om + w)*a/np.pi))      # (1/i) int sin(wt) e^{i om t}

def eigfuncs(a, K, W, om, dw, m):
    out = []
    for kind in ("even", "odd"):
        ks = range(K) if kind == "even" else range(1, K)
        H = np.array([hat(k, kind, a, om) for k in ks])
        N = np.array([2*a if (kind == "even" and k == 0) else a for k in ks])
        G = (H*W*dw) @ H.T/(2*np.pi)
        Dm = 1/np.sqrt(N); S = Dm[:, None]*G*Dm[None, :]
        E, V = np.linalg.eigh(S)
        for j in range(1, m + 1):
            out.append((E[-j], kind, list(Dm*V[:, -j])))
    out.sort(key=lambda z: -z[0])
    return out

if __name__ == "__main__":
    a, K, m, which, par = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], float(sys.argv[5])
    xw, ww = leggauss(8000)
    L = 60.0 if which == "gauss" else par
    om = L*xw; dw = L*ww
    W = (om*0 + 1) if which == "prolate" else np.exp(-par**2*om**2/2)
    lev = eigfuncs(a, K, W, om, dw, m)
    n = 1200; xx, _ = leggauss(n); t = a*xx
    funcs = [series(c, k, a, t) for _, k, c in lev]
    for D in (1, 2, 3):
        rho, th, per, basis = fit(funcs, a, D, n)
        print(json.dumps({"control": which, "par": par, "eig": [f"{e:.2e}" for e, _, _ in lev], "D": D, "rho": rho,
                          "theta": {f"{b}{mm}": round(float(v), 5) for (b, mm), v in zip(basis, th)}}))
