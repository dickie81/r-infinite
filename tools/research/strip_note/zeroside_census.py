#!/usr/bin/env python3
"""The per-zero accuracy of zeroside.py's exact-truncation quadrature at delta = 2 (research instrument of the
working note; committed; not a verifier).

zeroside.py evaluates E_a(gamma) = 2 int_a^inf Phi cos(gamma u) du with a five-panel tanh-sinh quadrature on
[a, a + 3] (a = delta/2). This census compares it, on every eighth zero above gamma = 4500 (2707 zeros -> 339 samples;
the paper's 6700 zeros, checkpoints/zeta_zeros_6700.json), with a reference: composite 12-point Gauss-Legendre on
30 000 panels of [a, a + 3] in double precision, Phi tabulated once at 30 digits; the reference is first checked
against a 600-panel mp.quad at three zeros (gamma_1, gamma_3001, gamma_6700). It prints the number of sampled zeros
whose relative error exceeds 6.5%, the median relative error over the sampled zeros in (5000, 7000], the number of
sign flips and the largest relative error. Adapted from round 386's review script (the reviewer's census_r386.py,
re-run by the lead with the same result line); the elapsed-time fields are dropped so the log is reproducible.
Usage: zeroside_census.py   (about 20 minutes: the 339 five-panel quadratures dominate)
"""
import json, os
import numpy as np, mpmath as mp
HERE = os.path.dirname(os.path.abspath(__file__))
mp.mp.dps = 30
zeros = [mp.mpf(z) for z in json.load(open(os.path.join(HERE, '..', 'checkpoints', 'zeta_zeros_6700.json')))]
d = json.load(open(os.path.join(HERE, 'ledger_d2.0.json')))
a = mp.mpf(d['delta'])/2

def Phi(u):
    u = mp.mpf(u); s = mp.mpf(0)
    for n in range(1, 14):
        s += (2*mp.pi**2*n**4*mp.exp(mp.mpf(9)*u/2) - 3*mp.pi*n*n*mp.exp(mp.mpf(5)*u/2))*mp.exp(-mp.pi*n*n*mp.exp(2*u))
    return s

def E5(g):   # zeroside.py's quadrature, verbatim
    return 2*mp.quad(lambda u: Phi(u)*mp.cos(g*u), [a, a + mp.mpf('0.1'), a + mp.mpf('0.3'), a + 1, a + 3])

xg, wg = np.polynomial.legendre.leggauss(12)
edges = np.linspace(float(a), float(a) + 3.0, 30001)
mids = (edges[1:] + edges[:-1])/2; half = (edges[1:] - edges[:-1])/2
U = (mids[:, None] + half[:, None]*xg[None, :]).ravel(); W = (half[:, None]*wg[None, :]).ravel()
PhiU = np.array([float(Phi(u)) for u in U], dtype=float)
print(f'Phi tabulated at {len(U)} nodes', flush=True)
def Eref(g): return 2*float(np.sum(W*PhiU*np.cos(float(g)*U)))

for g in (zeros[0], zeros[3000], zeros[-1]):
    pts = [a + 3*mp.mpf(i)/600 for i in range(601)]
    e600 = 2*mp.quad(lambda u: Phi(u)*mp.cos(g*u), pts)
    print(f'validate gamma={mp.nstr(g, 10)}: Eref={Eref(g):.6e} E600={mp.nstr(e600, 7)} E5={mp.nstr(E5(g), 7)}', flush=True)

idx = [i for i, g in enumerate(zeros) if g > 4500]
sample = idx[::8]
print('zeros above 4500:', len(idx), ' sampled (stride 8):', len(sample), flush=True)
errs = []
for k, i in enumerate(sample):
    g = zeros[i]; e5 = float(E5(g)); er = Eref(g)
    rel = abs(e5 - er)/abs(er) if er != 0 else float('inf')
    errs.append((float(g), e5, er, rel))
    if k % 40 == 0:
        print(f'  {k}/{len(sample)} gamma={float(g):.2f} E5={e5:.4e} Eref={er:.4e} rel={rel:.3f}', flush=True)
over = sum(1 for *_, r in errs if r > 0.065)
hi = [r for g, _, _, r in errs if 5000 < g <= 7000]
sign = sum(1 for _, e5, er, _ in errs if e5*er < 0)
print(f'RESULT: {over} of {len(errs)} sampled zeros above 4500 exceed 6.5% relative error; median rel error in (5000,7000] = '
      f'{np.median(hi):.3f} over {len(hi)} zeros; sign flips: {sign}; max rel = {max(r for *_, r in errs):.2f}', flush=True)
