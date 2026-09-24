#!/usr/bin/env python3
"""Round 70: the multiplier M_a = (ghat/ghat(0)) / (Xi/Xi(0)) of the ground state, along the imaginary
and real axes. The Paley–Wiener heuristic: |ghat(iy)| <= ||g||_1 e^{a y} while log Xi(iy) ~ (y/2) log(y/2 pi e),
so M(iy) must decay once y > y0 = 2 pi e e^{delta}; a Gaussian M = e^{tau z^2} needs tau >= e^{-delta}/(4 pi e^2).
Prints log M(iy) against -tau y^2 (tau from the fitted beta) and log M on the real axis away from zeros.
Usage: explain.py <delta> <K> <prec>"""
import sys, json, math
from flint import arb, arb_mat, ctx
import mpmath as mp
import nullvec_fast as nf
from weil_prime_gram import gram

def run(delta, K, prec, tau_fit):
    with ctx.workprec(prec):
        a = arb(delta)/2
        G, N, pp = gram(delta, K, prec)
        D = [1/N[i].sqrt() for i in range(K)]
        M = arb_mat(K, K)
        for i in range(K):
            for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
        Minv = M.inv(); Minv = arb_mat([[Minv[i, j].mid() for j in range(K)] for i in range(K)])
        l1, g1 = nf.inv_iter(Minv, M, K, arb_mat([[arb(1)/(i + 1)] for i in range(K)]))
        g = [g1[i, 0]*D[i] for i in range(K)]
        pi = arb.pi()
        def ghat_imag(y):   # int_{-a}^{a} g(t) e^{-y t} dt
            y = arb(y)
            if y == 0: return 2*a*g[0]
            s = 2*a*g[0]*(y*a).sinh()/(y*a)
            for k in range(1, K):
                om = k*pi/a
                s += g[k]*2*(-1)**k*y*(y*a).sinh()/(y*y + om*om)
            return s
        def ghat_real(x):   # int g(t) cos(x t) dt
            x = arb(x)
            s = 2*g[0]*(x*a).sin()/x
            for k in range(1, K):
                om = k*pi/a
                s += g[k]*(((x - om)*a).sin()/(x - om) + ((x + om)*a).sin()/(x + om))
            return s
        mp.mp.prec = 200
        Xi = lambda s: mp.re(0.5*s*(s - 1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s))   # xi(s)
        g0 = ghat_imag(0); X0 = Xi(mp.mpf(0.5))
        y0 = 2*math.pi*math.e*math.exp(delta)
        out = {"delta": delta, "tau_fit": tau_fit, "tau_PW": math.exp(-delta)/(4*math.pi*math.e**2), "y0": y0, "imag": [], "real": []}
        for frac in [0.05, 0.1, 0.2, 0.3, 0.5, 0.7, 1.0, 1.5, 2.0, 2.718, 3.5, 5.0]:
            y = frac*y0
            gh = ghat_imag(y)/g0
            xi = Xi(mp.mpf(0.5) + y)/X0
            logM = float((gh.log()).mid()) - float(mp.log(xi)) if gh > 0 else None
            bound = float(((2*a*arb(y)).exp()).log().mid())   # crude: log e^{a y} scale (reference)
            out["imag"].append({"y/y0": frac, "y": round(y, 3), "logM": logM, "-tau_fit*y^2": -tau_fit*y*y,
                                "log_ghat_norm": float(gh.log().mid()) if gh > 0 else None, "a*y": float(a.mid())*y})
        # real axis: sample midway between consecutive zeta zeros is awkward; use points where Xi is not small
        gr0 = ghat_real(arb(1)/10**6)
        for x in [2.0, 5.0, 8.0, 11.0, 13.0, 16.0, 19.0, 23.0, 26.0, 29.0]:
            gr = ghat_real(x)/gr0
            xi = Xi(mp.mpf(0.5) + 1j*x)/X0
            if abs(xi) > 1e-40:
                ratio = float(gr.mid())/float(xi)
                out["real"].append({"x": x, "M": ratio, "exp(tau x^2)": math.exp(tau_fit*x*x)})
        return out

if __name__ == "__main__":
    d, K, p, tau = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    print(json.dumps(run(d, K, p, tau)))
