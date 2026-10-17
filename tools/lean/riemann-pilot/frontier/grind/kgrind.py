#!/usr/bin/env python3
"""Round 175: the prime 'grinding' error E(u) = (psi(x) - x)/sqrt(x), x = e^u, up to 1e8.
Explicit formula: psi(x) - x = -sum_rho x^rho/rho - log(2 pi) - 1/2 log(1 - x^-2),
so E(u) ~ -sum_gamma 2 Re(e^{i gamma u}/rho): tones at the zero heights gamma, each of amplitude 2/|rho| (RH: all at the same sqrt(x) volume)."""
import numpy as np, mpmath as mp, json, math
X = 10**8
s = np.ones(X + 1, dtype=bool); s[:2] = False
for i in range(2, int(X**0.5) + 1):
    if s[i]: s[i*i::i] = False
primes = np.nonzero(s)[0]; del s
pos = [primes]; wts = [np.log(primes.astype(float))]
for p in primes[primes <= int(X**0.5)]:
    q = int(p)*int(p)
    while q <= X: pos.append(np.array([q])); wts.append(np.array([math.log(p)])); q *= int(p)
pos = np.concatenate(pos); wts = np.concatenate(wts); o = np.argsort(pos); pos = pos[o]; cw = np.cumsum(wts[o])
u = np.linspace(math.log(100), math.log(X), 1 << 16); x = np.exp(u)
idx = np.searchsorted(pos, x, side='right') - 1; psi = np.where(idx >= 0, cw[np.maximum(idx, 0)], 0.0)
E = (psi - x)/np.sqrt(x)
# explicit-formula prediction from the first 200 zeros
gam = [float(mp.zetazero(k).imag) for k in range(1, 201)]
Epred = np.zeros_like(u)
for g in gam:
    rho = complex(0.5, g); Epred += -2*np.real(np.exp(1j*g*u)*np.exp(0.5*u)/rho)/np.exp(0.5*u)
Epred += (-math.log(2*math.pi) - 0.5*np.log(1 - x**-2))/np.sqrt(x)
corr = float(np.corrcoef(E, Epred)[0, 1])
# spectrum on the log scale (Hann window)
L = u[-1] - u[0]; w = np.hanning(len(u)); du = u[1] - u[0]
om = np.arange(0.5, 60, 0.01)
S = np.abs(np.array([np.sum(w*(E - E.mean())*np.exp(-1j*o*u))*du for o in om]))
pk = [i for i in range(1, len(S) - 1) if S[i] > S[i - 1] and S[i] >= S[i + 1] and S[i] > 0.25*S.max()]
peaks = sorted([(float(om[i]), float(S[i])) for i in pk], key=lambda t: t[0])
match = [(round(p, 3), round(min(gam, key=lambda g: abs(g - p)), 3)) for p, _ in peaks]
# loudness per decade
dec = [(10**k, float(np.abs(E[(x >= 10**k) & (x < 10**(k + 1))]).max())) for k in range(2, 8)]
out = dict(X=X, n_samples=len(u), corr_with_200_zero_formula=round(corr, 4), peaks_vs_zeros=match, max_absE_per_decade=dec)
print(json.dumps(out, indent=1)); json.dump(out, open('kgrind_results.json', 'w'), indent=1)
np.savez_compressed('kgrind_series.npz', u=u, E=E, Epred=Epred, om=om, S=S, gam=np.array(gam))
