#!/usr/bin/env python3
"""Round 176: gear slippage = Mertens function M(x) = sum_{n<=x} mu(n), up to 1e8.
mu(n): -1/+1 for an odd/even number of distinct prime 'gears' touching n once each; 0 if a gear touches twice (p^2 | n).
Explicit formula (simple zeros): M(x) ~ sum_rho x^rho/(rho zeta'(rho)) + ..., so M/sqrt(x) has tones at the zero heights with
amplitude 2/|rho zeta'(rho)|."""
import numpy as np, math, json, mpmath as mp
X = 10**8
isp = np.ones(X + 1, dtype=bool); isp[:2] = False
for i in range(2, int(X**0.5) + 1):
    if isp[i]: isp[i*i::i] = False
primes = np.nonzero(isp)[0]; del isp
mu = np.ones(X + 1, dtype=np.int8); mu[0] = 0
for p in primes:
    p = int(p); mu[p::p] *= -1
    if p*p <= X: mu[p*p::p*p] = 0
M = np.cumsum(mu, dtype=np.int64)
u = np.linspace(math.log(100), math.log(X), 1 << 16); x = np.exp(u)
Mx = M[np.floor(x).astype(np.int64)]; Es = Mx/np.sqrt(x)
L = u[-1] - u[0]; w = np.hanning(len(u)); du = u[1] - u[0]
om = np.arange(0.5, 60, 0.01)
S = np.abs(np.array([np.sum(w*(Es - Es.mean())*np.exp(-1j*o*u))*du for o in om]))
gam = [mp.zetazero(k) for k in range(1, 13)]
pred = [2/abs(r*mp.zeta(r, derivative=1)) for r in gam]
meas = [float(S[np.argmin(abs(om - float(r.imag)))]) for r in gam]
ratio_meas = [m/meas[0] for m in meas]; ratio_pred = [float(p/pred[0]) for p in pred]
dec = [(10**k, float(np.abs(Es[(x >= 10**k) & (x < 10**(k + 1))]).max())) for k in range(2, 8)]
pk = [i for i in range(1, len(S) - 1) if S[i] > S[i - 1] and S[i] >= S[i + 1] and S[i] > 0.1*S.max()]
out = dict(X=X, max_absM_over_sqrtx_per_decade=dec, M_at_1e8=int(M[X]),
           peaks=[round(float(om[i]), 3) for i in pk],
           zero_heights=[round(float(r.imag), 3) for r in gam],
           tone_strength_relative_measured=[round(v, 3) for v in ratio_meas],
           tone_strength_relative_predicted=[round(v, 3) for v in ratio_pred])
print(json.dumps(out, indent=1)); json.dump(out, open('kslip_results.json', 'w'), indent=1)
np.savez_compressed('kslip_series.npz', u=u, E=Es, om=om, S=S, gam=np.array([float(r.imag) for r in gam]),
                    pred=np.array(ratio_pred), meas=np.array(ratio_meas))
