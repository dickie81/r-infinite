#!/usr/bin/env python3
"""Predicted rate of Davenport-Heilbronn zeros right of the critical line, from the inert primes alone.

f(s) = sum_n u(n mod 5) n^-s, u = (0, 1, kappa, -kappa, -1), equals c1 L(s,chi) + c2 L(s,chibar) with
chi = chi5 (chi(2) = i), c1 = (1 - i kappa)/2, c2 = (1 + i kappa)/2.  Off-line zeros (Re s > 1/2) are the zeros
of c1 R(s) + c2, R = L(s,chi)/L(s,chibar) = prod_{p = +-2 mod 5} (1 + chi(p) p^-s)/(1 - chi(p) p^-s): the primes
= +-1 mod 5 cancel from R exactly, and the gamma factor (the same for chi and chibar) cancels too.
Random model (Bohr-Jessen): p^-it -> independent uniform phases, so R(sigma) = prod (1 + V_p x_p)/(1 - V_p x_p),
x_p = p^-sigma, V_p iid uniform on the circle.  Jensen function M(sigma) = E log|c1 R(sigma) + c2| (the split
primes contribute E log|1 - W x| = 0).  Littlewood's lemma: zeros with Re rho > sigma0 per unit height
r(sigma0) = -M'(sigma0)/(2 pi).
Exact factors for inert primes p <= P1; primes in (P1, X] as a complex Gaussian (G, dG/dsigma) with the exact
second moments (prime sums by sieve to Y, integral with density 1/(2 log x) beyond Y).
Estimators: M by the sample mean of log|F|; M' by the sample mean of Re[c1 R D/(c1 R + c2)], D = d log R/dsigma
(heavy-tailed: reported with batch-mean standard errors), cross-checked by central differences of M.
Usage: model_rate.py [N_samples] [X]   (X = 'inf' or a number)
"""
import sys, math, json, time
import numpy as np
from scipy.special import exp1, gammaincc, gamma as Gam

kappa = (math.sqrt(10 - 2*math.sqrt(5)) - 2)/(math.sqrt(5) - 1)
c1 = 0.5*(1 - 1j*kappa); c2 = 0.5*(1 + 1j*kappa)
N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 4_000_000
Xarg = sys.argv[2] if len(sys.argv) > 2 else 'inf'
X = math.inf if Xarg == 'inf' else float(Xarg)
P1 = 500; Y = 20_000_000
SIGMAS = [0.52, 0.55, 0.575, 0.60, 0.625, 0.65, 0.675, 0.70, 0.75, 0.80, 0.85, 0.90, 1.00, 1.10, 1.20]

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
pr = primes_upto(Y)
inert = pr[(pr % 5 == 2) | (pr % 5 == 3)]
ex = inert[inert <= min(P1, X)].astype(float)
tail = inert[inert > P1].astype(float)

def tail_moments(sig):
    """S_k = sum over inert p in (P1, X] of p^-2sig (log p)^k, k = 0, 1, 2."""
    tp = tail[tail <= X] if math.isfinite(X) else tail
    lp = np.log(tp); w = tp**(-2*sig)
    S = [float(np.sum(w)), float(np.sum(w*lp)), float(np.sum(w*lp*lp))]
    if not math.isfinite(X) or X > Y:
        # beyond Y: inert primes have density 1/(2 log x); int_U^inf e^{-a u} u^{k-1} du, U = log Y (or to log X)
        a = 2*sig - 1; U = math.log(Y)
        def I(k, U0):
            if k == 0: return exp1(a*U0)
            return gammaincc(k, a*U0)*Gam(k)/a**k
        for k in range(3):
            v = I(k, U)
            if math.isfinite(X): v -= I(k, math.log(X))
            S[k] += 0.5*v
    return S

def run(sig, rng, nb):
    x = ex**(-sig); lx = np.log(ex)
    S0, S1, S2 = tail_moments(sig) if X > P1 else (0.0, 0.0, 0.0)
    a0 = 2*math.sqrt(S0); b1 = -2*S1/math.sqrt(S0) if S0 > 0 else 0.0; b2 = 2*math.sqrt(max(S2 - S1*S1/S0, 0.0)) if S0 > 0 else 0.0
    Ms, Ds = [], []
    for _ in range(nb):
        n = N // nb
        th = rng.random((n, ex.size))*2*np.pi
        V = np.exp(1j*th)
        Vx = V*x
        logR = np.sum(np.log1p(Vx) - np.log1p(-Vx), axis=1)
        D = np.sum(-2*Vx*lx/(1 - Vx*Vx), axis=1)
        z1 = (rng.standard_normal(n) + 1j*rng.standard_normal(n))/math.sqrt(2)
        z2 = (rng.standard_normal(n) + 1j*rng.standard_normal(n))/math.sqrt(2)
        logR = logR + a0*z1
        D = D + b1*z1 + b2*z2
        R = np.exp(logR)
        F = c1*R + c2
        Ms.append(np.mean(np.log(np.abs(F))))
        Ds.append(np.mean(np.real(c1*R*D/F)))
    Ms = np.array(Ms); Ds = np.array(Ds)
    return (float(Ms.mean()), float(Ms.std(ddof=1)/math.sqrt(nb)),
            float(Ds.mean()), float(Ds.std(ddof=1)/math.sqrt(nb)), (S0, S1, S2))

t0 = time.time()
out = {'N': N, 'X': Xarg, 'P1': P1, 'Y': Y, 'kappa': kappa, 'rows': []}
for sig in SIGMAS:
    rng = np.random.default_rng(20261001)   # common random numbers across sigma
    M, Mse, Md, Mdse, S = run(sig, rng, 40)
    r = -Md/(2*math.pi); rse = Mdse/(2*math.pi)
    out['rows'].append({'sigma': sig, 'M': M, 'M_se': Mse, 'dM': Md, 'dM_se': Mdse, 'rate': r, 'rate_se': rse,
                        'tailS0': S[0]})
    print(f"sigma={sig:.3f}  M={M:.6f}±{Mse:.1e}  M'={Md:.5f}±{Mdse:.1e}  rate(Re>sigma)={r:.5f}±{rse:.5f}"
          f"  tail var 4S0={4*S[0]:.4f}   [{time.time()-t0:.0f}s]", flush=True)
json.dump(out, open(f'model_rate_N{N}_X{Xarg}.json', 'w'), indent=1)
