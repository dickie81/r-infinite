#!/usr/bin/env python3
"""The ZERO SIDE of the ledger at delta = 2 (research instrument of the working note; committed; not a verifier).

For the two profiles of ledger.py at delta = 2 (the ground state g_1 and the K-term cosine projection Phi_a^K,
coefficient vectors read from ledger_d2.0.json), the zero side of Weil's form, Q = sum_rho ghat(gamma_rho)^2
= 2 sum_{gamma > 0} ghat(gamma)^2 for even real g, summed over the paper's 6700 zeros
(checkpoints/zeta_zeros_6700.json, to height 6997) plus a tail estimate; and, for the EXACT truncation
Phi_a = Phi 1_[-a,a] (not its projection), Q(Phi_a)/||Phi_a||^2 = 2 sum E_a(gamma)^2/||Phi_a||^2 with
E_a(gamma) = 2 int_a^inf Phi cos(gamma u) du (Phi_a's transform at a zero is -E_a, since Xi vanishes there)
and ||Phi_a||^2 = 2 int_0^a Phi^2 (the round-383 correction: an earlier session script used 2 int_0^a Phi).
Tail beyond the last zero: the mean of gamma^2 ghat^2 over the last 100 zeros times int_T^inf (ln(r/2pi)/2pi) r^-2 dr.
Caveat (rounds 384-385): the five-panel tanh-sinh quadrature of E_a(gamma) under-resolves the oscillation above
gamma ~ 4500: the per-zero error is typically a few percent in (5000, 7000] (median 4%), and of order one -- including
the sign -- at zeros where E_a is near a sign change (42 of 339 sampled zeros above 4500 exceed 6.5%); the zeros above
5000 carry 0.5% of the sum, so the quotient Q(Phi_a)/||Phi_a||^2 is affected at 2e-5 relative (a 600-panel grid gives
1.1611876e-14 against this file's 1.1612094e-14). The round-385 sweep also fixed the 'ledger Q' display, which the
round-384 change to the JSON's precision had broken (a fixed-notation string sliced to twelve characters).
Usage: zeroside.py   (about 40 minutes: the 6700 tail quadratures dominate)
"""
import os, sys, json
import mpmath as mp
HERE = os.path.dirname(os.path.abspath(__file__))
mp.mp.dps = 30
zeros = [mp.mpf(z) for z in json.load(open(os.path.join(HERE, '..', 'checkpoints', 'zeta_zeros_6700.json')))]
d = json.load(open(os.path.join(HERE, 'ledger_d2.0.json')))
a = mp.mpf(d['delta'])/2; K = d['K']; om = [mp.mpf(k)*mp.pi/a for k in range(K)]

def Phi(u):
    u = mp.mpf(u); s = mp.mpf(0)
    for n in range(1, 14):
        s += (2*mp.pi**2*n**4*mp.exp(mp.mpf(9)*u/2) - 3*mp.pi*n*n*mp.exp(mp.mpf(5)*u/2))*mp.exp(-mp.pi*n*n*mp.exp(2*u))
    return s

def ghat(c, r):
    s = c[0]*2*mp.sin(r*a)/r
    for k in range(1, K):
        s += c[k]*(mp.sin((r - om[k])*a)/(r - om[k]) + mp.sin((r + om[k])*a)/(r + om[k]))
    return s

def tail_after(vals_last, T):
    m = sum(v*g*g for v, g in vals_last)/len(vals_last)
    return m*mp.quad(lambda r: mp.log(r/(2*mp.pi))/(2*mp.pi)/r**2, [T, mp.inf])

for name, label in [('c1', 'g_1'), ('cP', 'Phi_a^K')]:
    c = [mp.mpf(x) for x in d[name]]
    Q = mp.mpf(0); last = []
    for i, g in enumerate(zeros):
        e = ghat(c, g)**2; Q += e
        if i >= len(zeros) - 100: last.append((e, g))
    t = tail_after(last, zeros[-1])
    print(f"{label}: sum over 6700 zeros = {mp.nstr(Q, 8)}  tail est = {mp.nstr(t, 3)}  Q = 2(sum + tail) = {mp.nstr(2*(Q + t), 8)}   ledger Q = {mp.nstr(mp.mpf(d['ledger_' + ('g1' if name == 'c1' else 'Phi')]['Q']), 12)}")

# the exact truncation
pts = [a*mp.mpf(i)/20 for i in range(21)]
norm2 = 2*mp.quad(lambda u: Phi(u)**2, pts)
def E(g): return 2*mp.quad(lambda u: Phi(u)*mp.cos(g*u), [a, a + mp.mpf('0.1'), a + mp.mpf('0.3'), a + 1, a + 3])
Q = mp.mpf(0); last = []
for i, g in enumerate(zeros):
    e = E(g)**2; Q += e
    if i >= len(zeros) - 100: last.append((e, g))
t = tail_after(last, zeros[-1])
print(f"exact Phi_a: ||Phi_a||^2 = {mp.nstr(norm2, 12)}  sum E_a^2 over 6700 zeros = {mp.nstr(Q, 8)}  tail est = {mp.nstr(t, 3)}  Q(Phi_a)/||Phi_a||^2 = {mp.nstr(2*(Q + t)/norm2, 8)}")
print(f"first zeros, exact -E_a/||Phi_a|| vs projection ghat: " + "; ".join(f"{mp.nstr(-E(g)/mp.sqrt(norm2), 6)} vs {mp.nstr(ghat([mp.mpf(x) for x in d['cP']], g), 6)}" for g in zeros[:3]))
