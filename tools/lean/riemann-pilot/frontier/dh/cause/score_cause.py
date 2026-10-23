#!/usr/bin/env python3
"""Scoring of PREREG_cause.md (P1 the phase signature, P2 the beat law, P3 the rates) from the census output.
Usage: score_cause.py --lo 200 --hi 10000 FILE.jsonl [FILE.jsonl ...]
The census files are dh_census.py outputs; files covering [1, lo] may be included (they enter only the cumulative
beat counts of P2(b)).  Beat signs are decided by evaluating Z_chi * Z_chibar at each merged-segment midpoint with
python-flint balls (precision raised until the ball excludes 0)."""
import sys, json, math, argparse, cmath
from collections import Counter
from flint import acb, arb, ctx
from scipy.stats import poisson

ap = argparse.ArgumentParser(); ap.add_argument('--lo', type=float, default=200.0); ap.add_argument('--hi', type=float, default=10000.0)
ap.add_argument('files', nargs='+'); A_ = ap.parse_args()
LO, HI = A_.lo, A_.hi
kappa = (math.sqrt(10 - 2*math.sqrt(5)) - 2)/(math.sqrt(5) - 1); th = math.atan(kappa)
CHI = [0, 1, 1j, -1j, -1]

def zz(t, prec=53):
    """(Z_chi, Z_chibar) at height t as arb balls, raising precision until both signs are certain."""
    while True:
        ctx.prec = prec
        s = acb(0.5, t)
        H = [acb.zeta(s, acb(a)/5) for a in range(1, 5)]
        p = acb(5)**(-s)
        Lc = p*sum(acb(CHI[a].real, CHI[a].imag)*H[a-1] for a in range(1, 5))
        Lb = p*sum(acb(CHI[a].real, -CHI[a].imag)*H[a-1] for a in range(1, 5))
        vt = acb(0.75, t/2).lgamma().imag + arb(t)/2*(arb(5)/arb.pi()).log()
        rc = acb.exp_pi_i(acb(vt/arb.pi() - arb(th)/arb.pi()))
        rb = acb.exp_pi_i(acb(vt/arb.pi() + arb(th)/arb.pi()))
        zc, zb = (Lc*rc).real, (Lb*rb).real
        if (0 not in zc) and (0 not in zb): return zc, zb
        prec *= 2
        if prec > 1024: raise RuntimeError(f'sign undecided at t = {t}')

W = []
for f in A_.files:
    for line in open(f):
        line = line.strip()
        if line: W.append(json.loads(line))
W.sort(key=lambda w: w['T0'])
complete = [w for w in W if not w['flags']]
bad = [w for w in W if w['flags']]
inrange = [w for w in W if w['T0'] >= LO - 1 and w['T1'] <= HI + 1]
print(f"windows: {len(W)} total, {len(bad)} with flags; in (lo, hi]: {len(inrange)}, flagged {sum(1 for w in inrange if w['flags'])}")
fr = sum(1 for w in inrange if w['flags'])/max(1, len(inrange))
print(f"census completeness: {'OK' if fr <= 0.01 else 'FAILED'} (flagged fraction {fr:.4f})")
roots_f = sorted(r for w in W for r in w['roots_f']); A = sorted(r for w in W for r in w['roots_chi'])
B = sorted(r for w in W for r in w['roots_chibar'])
off = sorted([tuple(z[:2]) for w in W for z in w['offline']], key=lambda z: z[1])
inside = lambda t: LO < t <= HI

# ---------------- P1 the phase signature
Om = [z for z in off if z[0] >= 0.6 and inside(z[1])]
K = len(Om)
def m1(q, heights):
    if not heights: return complex('nan')
    return sum(cmath.exp(-1j*g*math.log(q)) for g in heights)/len(heights)
gOm = [z[1] for z in Om]; gA = [t for t in A if inside(t)]
print(f"\nP1: K = {K} zeros with Re >= 0.6 in ({LO}, {HI}]")
res = {}
for q in [2, 3, 7, 13, 17, 23, 37, 43, 11, 19, 29, 31, 41, 59, 61, 71]:
    res[q] = (m1(q, gOm), m1(q, gA))
    kind = 'inert ' + ('2' if q % 5 == 2 else '3') if q % 5 in (2, 3) else 'split ' + str(q % 5)
    print(f"  q = {q:3d} ({kind}): m1 = {res[q][0].real:+.3f}{res[q][0].imag:+.3f}i   m1(A-train) = {res[q][1].real:+.3f}{res[q][1].imag:+.3f}i")
pa = res[2][0].real <= -0.30 and abs(res[2][0].imag) <= 0.10
pb = res[3][0].real >= 0.20 and abs(res[3][0].imag) <= 0.10
pc = res[7][0].real <= -0.10
pd = sum(1 for q in [13, 17, 23, 37, 43] if (res[q][0].real < 0) == (q % 5 == 2)) >= 4
pe = all(abs(res[q][0]) <= 0.20 and abs(res[q][0] - res[q][1]) <= 0.15 for q in [11, 19, 29, 31, 41, 59, 61, 71])
print(f"  (a) {pa}  (b) {pb}  (c) {pc}  (d) {pd}  (e) {pe}   => P1 {'PASS' if (pa and pb and pc and pd and pe) else 'FAIL'}")

# ---------------- P2 the beat law
ev = sorted([(t, 'A') for t in A] + [(t, 'B') for t in B])
beats = []  # (t0, t1, type, n_f)
fi = 0
for i in range(len(ev) - 1):
    (t0, k0), (t1, k1) = ev[i], ev[i + 1]
    zc, zb = zz((t0 + t1)/2)
    O = (zc*zb) < 0
    nf = sum(1 for r in roots_f if t0 < r < t1)
    if not O and nf: print(f"  THEOREM CHECK FAILED: f-zero in a same-sign segment ({t0:.4f}, {t1:.4f})")
    if O: beats.append((t0, t1, 'mixed' if k0 != k1 else k0 + k1, nf))
    elif nf: beats.append((t0, t1, 'S!', nf))
bin_ = [b for b in beats if inside((b[0] + b[1])/2)]
mixed = [b for b in bin_ if b[2] == 'mixed']; same = [b for b in bin_ if b[2] in ('AA', 'BB')]
parity_bad = [b for b in mixed if b[3] % 2 == 0] + [b for b in same if b[3] % 2 == 1]
print(f"\nP2: beats in range {len(bin_)}: mixed {len(mixed)}, same-type {len(same)}; parity violations {len(parity_bad)} (theorem: 0)")
one = sum(1 for b in mixed if b[3] == 1); E = sum((b[3] - 1)//2 for b in mixed)
S0 = sum(1 for b in same if b[3] == 0); S2 = sum(1 for b in same if b[3] == 2); Sx = sum(1 for b in same if b[3] > 2)
p2a = one >= 0.995*len(mixed)
print(f"  (a) mixed beats with exactly one zero: {one}/{len(mixed)} = {one/max(1,len(mixed)):.5f}  => {p2a}")
# (b) at window ends: N_f vs number of beats below
ends = sorted({w['T1'] for w in W} | {w['T0'] for w in W})
Nf_at = {}
for w in W:
    Nf_at[round(w['T0'], 9)] = w['Nf0'][1] if isinstance(w['Nf0'], list) else round(w['Nf0'])
    Nf_at[round(w['T1'], 9)] = w['Nf1'][1] if isinstance(w['Nf1'], list) else round(w['Nf1'])
ok_ends = 0; tot_ends = 0; worst = []
for T in ends:
    if not (LO <= T <= HI): continue
    nb = sum(1 for b in beats if b[2] != 'S!' and (b[0] + b[1])/2 < T)
    d = Nf_at[round(T, 9)] - nb
    tot_ends += 1; ok_ends += abs(d) <= 1
    if abs(d) > 1: worst.append((T, d))
p2b = ok_ends >= 0.99*tot_ends
print(f"  (b) window ends with N_f = #beats +-1: {ok_ends}/{tot_ends}  => {p2b}; exceptions {worst[:10]}")
Kall = sum(1 for z in off if inside(z[1]))
lhs = 2*Kall; rhs = S0 - S2 - 2*E
p2c = abs(lhs - rhs) <= 2
print(f"  (c) 2K = {lhs} vs S0 - S2 - 2E = {S0} - {S2} - 2*{E} = {rhs}  => {p2c}   (S>2: {Sx})")
lam = lambda t: 2*math.pi/math.log(5*t/(2*math.pi))
same0 = [((b[0] + b[1])/2) for b in same if b[3] == 0]
offin = [z for z in off if inside(z[1])]
def flanked(g):
    L = lam(g); return any(g - 2*L <= m < g for m in same0) and any(g < m <= g + 2*L for m in same0)
fl = sum(1 for z in offin if flanked(z[1]))
near = sum(1 for m in same0 if any(abs(z[1] - m) <= 2*lam(m) for z in offin))
p2d = fl >= 0.95*max(1, len(offin)) and near >= 0.95*max(1, len(same0))
print(f"  (d) zeros flanked below and above: {fl}/{len(offin)};  zero-free same-type beats with a zero within 2 lambda: {near}/{len(same0)}  => {p2d}")
print(f"  P2 {'PASS' if (p2a and p2b and p2c and p2d and not parity_bad) else 'FAIL'};   split S0 : S2 = {S0} : {S2}")

# ---------------- P3 the rates
brackets = {0.60: [(57.9, 115.3), (116.6, 214.5), (215.0, 374.1)], 0.65: [(39.4, 69.9), (78.7, 124.5), (143.2, 215.4)],
            0.70: [(21.8, 40.8), (46.7, 72.3), (87.2, 122.4)], 0.80: [(2.9, 7.7), (7.6, 13.4), (15.0, 22.3)]}
wins = [(200, 2000), (2000, 5000), (5000, 10000)]
cells = 0; print("\nP3:")
for s0, br in brackets.items():
    row = []
    for (a, b), (lo, hi) in zip(wins, br):
        n = sum(1 for z in off if z[0] >= s0 and a < z[1] <= b)
        ok = poisson.ppf(0.025, lo) <= n <= poisson.ppf(0.975, hi)
        cells += ok; row.append(f"({a},{b}]: {n} in [{poisson.ppf(0.025, lo):.0f}, {poisson.ppf(0.975, hi):.0f}] {'ok' if ok else 'OUT'}")
    print(f"  sigma0 = {s0}: " + ";  ".join(row))
print(f"  cells passing: {cells}/12  => P3 {'PASS' if cells >= 10 else 'FAIL'}")

# ---------------- P5 exploratory
print("\nP5: Re rho histogram (zeros with Re > 1/2 in range):")
h = Counter(min(int((z[0] - 0.5)*20), 19) for z in offin)
for k in sorted(h): print(f"  [{0.5 + k/20:.2f}, {0.5 + (k + 1)/20:.2f}): {h[k]}")
print(f"  zeros with Re > 1: {sum(1 for z in offin if z[0] > 1)};  total zeros with Re > 1/2: {len(offin)}")
