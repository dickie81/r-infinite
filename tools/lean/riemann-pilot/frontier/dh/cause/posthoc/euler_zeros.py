#!/usr/bin/env python3
"""Post-hoc (not pre-registered): zeros of the truncated inert Euler product at the census heights.

g_X(s) = c1 P_X(s) + c2, P_X(s) = prod over inert primes p <= X (p = +-2 mod 5) of (1 + chi(p) p^-s)/(1 - chi(p) p^-s),
chi = chi5 with chi(2) = i, c1 = (1 - i kappa)/2, c2 = (1 + i kappa)/2.  P_X -> R = L(s,chi)/L(s,chibar) as X -> oo
for Re s > 1/2 (the anatomy of the four kernel-located zeros: |R_P - R| = 0.002-0.11 at P = 2e6), and the zeros of
g_oo with Re s > 1/2 are the census zeros (dh(s) = 0 iff R(s) = -eps, DHChannels.dh_eq_zero_iff_channel, with
c2/c1 = eps).  For finite X, g_X is holomorphic on Re s > 0 and almost periodic in t; by Jessen-Tornehave its zeros
with Re > sigma0 have density -M_X'(sigma0)/(2 pi) per unit height, M_X(sigma) = E log|c1 R_X + c2| over independent
uniform prime phases: the random model of model/model_rate.py at cutoff X.  This script counts those zeros at the
census heights, by the argument principle on the rectangle [sigma0, 3] x [T1, T2], for X = 30 ... 1e5 and
sigma0 = 0.6, 0.7, 0.8, 0.85, on the three P3 windows, so that the census counts (the true function) can be
compared with (i) the deterministic product at the same heights and (ii) the random model, at each X.
On Re s = 3, |g_X - 1| <= |c1|(exp(2 sum_p p^-3 / (1 - p^-3)) - 1) < 1, so g_X has no zero with Re >= 3 and the right
side contributes its principal-argument difference.  The left and horizontal sides are tracked on a grid
(dt = 0.01, dsigma = 0.002) refined recursively wherever one step turns the argument by more than 0.5 rad;
the winding is reported with its distance from an integer.
Usage: euler_zeros.py T1 T2 out.json   (window (T1, T2])
"""
import sys, json, math, time
import numpy as np

kappa = (math.sqrt(10 - 2*math.sqrt(5)) - 2)/(math.sqrt(5) - 1)
c1 = 0.5*(1 - 1j*kappa); c2 = 0.5*(1 + 1j*kappa)
XS = [30, 100, 300, 1000, 3000, 10_000, 100_000]
SIG0 = [0.6, 0.7, 0.8, 0.85]
SR = 3.0
DT = 0.01; DS = 0.002; TURN = 0.5; MAXDEPTH = 12

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
pr = primes_upto(max(XS))
inert = pr[(pr % 5 == 2) | (pr % 5 == 3)]
chi = np.where(inert % 5 == 2, 1j, -1j)
logp = np.log(inert.astype(float))
KX = [int(np.searchsorted(inert, X, side='right')) for X in XS]     # number of inert primes <= X

def logP_blocks(sig, t):
    """log P_X(sig + i t) for every X in XS, arrays sig and t broadcast to one shape (n,); returns (n, len(XS))."""
    sig = np.broadcast_to(np.asarray(sig, float), np.shape(t)); t = np.asarray(t, float)
    n = t.size; out = np.zeros((n, len(XS)), complex)
    CH = max(1, 2_000_000 // KX[-1])
    for a in range(0, n, CH):
        tt = t[a:a + CH]; ss = sig[a:a + CH]
        lo = 0; acc = np.zeros(tt.size, complex)
        for j, k in enumerate(KX):
            if k > lo:
                Z = chi[None, lo:k]*np.exp(-np.outer(ss, logp[lo:k]) - 1j*np.outer(tt, logp[lo:k]))
                acc = acc + np.sum(np.log1p(Z) - np.log1p(-Z), axis=1)
            out[a:a + CH, j] = acc
            lo = k
    return out

def g_of(sig, t, j):
    """g_X at the points (sig, t) for the single cutoff XS[j]."""
    sig = np.broadcast_to(np.asarray(sig, float), np.shape(t)); t = np.asarray(t, float)
    k = KX[j]; out = np.zeros(t.size, complex)
    CH = max(1, 2_000_000 // max(k, 1))
    for a in range(0, t.size, CH):
        tt = t[a:a + CH]; ss = sig[a:a + CH]
        Z = chi[None, :k]*np.exp(-np.outer(ss, logp[:k]) - 1j*np.outer(tt, logp[:k]))
        out[a:a + CH] = c1*np.exp(np.sum(np.log1p(Z) - np.log1p(-Z), axis=1)) + c2
    return out

def winding(path_fn, u, G, j, stats):
    """Total argument change of g along a path u -> (sig(u), t(u)), sampled at u with values G (for cutoff j),
    refining every step that turns by more than TURN rad."""
    total = 0.0
    d = np.angle(G[1:]/G[:-1])
    bad = np.nonzero(np.abs(d) > TURN)[0]
    good = np.ones(d.size, bool); good[bad] = False
    total += float(np.sum(d[good]))
    for i in bad:
        total += refine(path_fn, u[i], u[i + 1], G[i], G[i + 1], j, 0, stats)
    return total

def refine(path_fn, u0, u1, g0, g1, j, depth, stats):
    stats['refined'] += 1
    if depth >= MAXDEPTH:
        stats['unresolved'] += 1
        return float(np.angle(g1/g0))
    uu = np.linspace(u0, u1, 9)
    s, t = path_fn(uu[1:-1])
    gi = g_of(s, t, j)
    G = np.concatenate([[g0], gi, [g1]])
    d = np.angle(G[1:]/G[:-1])
    tot = 0.0
    for i in range(8):
        if abs(d[i]) > TURN:
            tot += refine(path_fn, uu[i], uu[i + 1], G[i], G[i + 1], j, depth + 1, stats)
        else:
            tot += float(d[i])
    return tot

def count(T1, T2, sig0):
    """Zeros of g_X with sig0 < Re s < 3, T1 < Im s < T2, for every X in XS (argument principle)."""
    stats = {'refined': 0, 'unresolved': 0}
    res = []
    # left side, upwards along Re s = sig0 (subtracted below: the contour runs downwards there)
    tl = np.arange(T1, T2 + DT/2, DT); tl[-1] = T2
    GL = c1*np.exp(logP_blocks(sig0, tl)) + c2
    sb = np.arange(sig0, SR + DS/2, DS); sb[-1] = SR
    GB = c1*np.exp(logP_blocks(sb, np.full(sb.size, T1))) + c2
    GT = c1*np.exp(logP_blocks(sb, np.full(sb.size, T2))) + c2
    for j, X in enumerate(XS):
        left = winding(lambda u: (np.full(np.size(u), sig0), u), tl, GL[:, j], j, stats)
        bottom = winding(lambda u: (u, np.full(np.size(u), T1)), sb, GB[:, j], j, stats)
        top = winding(lambda u: (u, np.full(np.size(u), T2)), sb, GT[:, j], j, stats)
        gr = g_of(np.array([SR, SR]), np.array([T1, T2]), j)
        right = float(np.angle(gr[1]/gr[0]))
        w = (bottom + right - top - left)/(2*math.pi)
        res.append({'X': X, 'winding': w, 'N': int(round(w)), 'frac_err': abs(w - round(w))})
    return res, stats

def right_side_bound():
    s = float(np.sum(inert.astype(float)**-SR/(1 - inert.astype(float)**-SR)))
    return abs(c1)*(math.exp(2*s) - 1)

if __name__ == '__main__':
    T1, T2, out = float(sys.argv[1]), float(sys.argv[2]), sys.argv[3]
    rb = right_side_bound()
    print(f'window ({T1}, {T2}]: inert primes <= X: {dict(zip(XS, KX))}; |g - 1| on Re s = 3 <= {rb:.3f}', flush=True)
    assert rb < 1
    rows = []
    for sig0 in SIG0:
        t0 = time.time()
        res, stats = count(T1, T2, sig0)
        rows.append({'sigma0': sig0, 'res': res, 'stats': stats})
        print(f'sigma0 = {sig0}: ' + ', '.join(f"X={r['X']}: {r['N']} ({r['frac_err']:.1e})" for r in res)
              + f"  [refined {stats['refined']}, unresolved {stats['unresolved']}; {time.time() - t0:.0f}s]", flush=True)
    json.dump({'T1': T1, 'T2': T2, 'XS': XS, 'rows': rows, 'right_bound': rb}, open(out, 'w'), indent=1)
