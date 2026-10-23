#!/usr/bin/env python3
"""Round 82: integrate the chain's canonical system from its Hamiltonian and compare with the direct kernel.
H(a) = diag(h, 1/h), h = dK_a(0,0)/da. With b = B/K00 and L(a) = d ln K00/da:
   A' = -(z/L) b,   b' = L (z A - b),   K_a(z,0)/K_a(0,0) = b/z.
L comes from the grid of l(delta) = ln K00 (kchain.py), smoothed by local polynomial fits.
Initial data at the first grid window: A = 1 - z^2 c, b = z (1 - z^2 r) (first order in the tiny window).
Usage: kham.py 'grid*.jsonl' zdirect.json [halfwin]"""
import sys, json, glob
import numpy as np
from scipy.integrate import solve_ivp
from mpmath import mpf
rows = []
for f in sorted(glob.glob(sys.argv[1])):
    rows += [json.loads(l) for l in open(f) if l.strip()]
rows.sort(key=lambda x: x["delta"])
dl = np.array([x["delta"] for x in rows]); ll = np.array([float(mpf(x["lnK00"])) for x in rows])
rr = np.array([float(mpf(x["r"])) for x in rows])
hw = float(sys.argv[3]) if len(sys.argv) > 3 else 0.04
def lprime(dd):
    m = np.abs(dl - dd) <= hw + 1e-12
    if m.sum() < 5: m = np.argsort(np.abs(dl - dd))[:7]
    c = np.polyfit(dl[m] - dd, ll[m], 3)
    return c[2]
tgt = json.load(open(sys.argv[2])); d1 = tgt["delta"]
a0 = dl[0]/2; a1 = d1/2
START = None
if len(sys.argv) > 4:   # exact initial data from the direct kernel at delta0 and delta0 +- h
    d0 = float(sys.argv[4]); h = 0.01
    import os; ZD = os.environ.get("ZDIR", "runs/hgrid")
    zs = [json.load(open(f"{ZD}/zdirect_{x}.json")) for x in (round(d0 - h, 2), d0, round(d0 + h, 2))]
    START = (d0, h, zs); a0 = d0/2
if hw < 0:   # closed-form model l' = 4 pi e^delta + C (C from runs/hgrid/model_fit.json)
    Cm = json.load(open("runs/hgrid/model_fit.json"))["C"]
    Lfun = lambda a: 2*(4*np.pi*np.exp(2*a) + Cm)
elif hw > 0:
    Lfun = lambda a: 2*lprime(2*a)
else:   # hw <= 0: cell-wise secant slopes, no smoothing
    sec = np.diff(ll)/np.diff(dl)
    def Lfun(a):
        i = min(max(np.searchsorted(dl, 2*a) - 1, 0), len(sec) - 1)
        return 2*sec[i]
# first-order initial data
r0 = rr[0]; c0 = r0     # c = r + r'/l' ~ r at a tiny window
print(f"integrating a in [{a0}, {a1}] ; grid {len(dl)} windows ; smoothing half-window {hw}")
print("   z        direct K(z,0)/K(0,0)     from Hamiltonian      rel.err")
for key, val in tgt["real"].items():
    z = float(key)
    def rhs(a, Y):
        L = Lfun(a); A, b = Y
        return [-(z/L)*b, L*(z*A - b)]
    if START:
        d0, h, zs = START
        bm, b0v, bp = (z*float(mpf(q["real"][key])) for q in zs)
        L0 = Lfun(d0/2); db = (bp - bm)/h            # d/da = 2 d/d delta; (bp - bm)/(2h) per delta -> x2
        init = [(b0v + db/L0)/z, b0v]
    else:
        init = [1 - z*z*c0, z*(1 - z*z*r0)]
    sol = solve_ivp(rhs, [a0, a1], init, method="Radau", rtol=1e-10, atol=1e-14)
    pred = sol.y[1, -1]/z; dirv = float(mpf(val))
    print(f"{z:9.4f}   {dirv: .10e}   {pred: .10e}   {abs(pred - dirv)/max(abs(dirv), 1e-300):.2e}")
for key, val in tgt["imag"].items():
    y = float(key); z = 1j*y
    def rhs(a, Y):
        L = Lfun(a); A, b = Y[0] + 1j*Y[1], Y[2] + 1j*Y[3]
        dA = -(z/L)*b; db = L*(z*A - b)
        return [dA.real, dA.imag, db.real, db.imag]
    if START:
        d0, h, zs = START
        bm, b0, bp = (z*float(mpf(q["imag"][key])) for q in zs)
        A0 = (b0 + ((bp - bm)/h)/Lfun(d0/2))/z
    else:
        A0 = 1 - z*z*c0; b0 = z*(1 - z*z*r0)
    sol = solve_ivp(rhs, [a0, a1], [A0.real, A0.imag, b0.real, b0.imag], method="Radau", rtol=1e-10, atol=1e-14)
    pred = ((sol.y[2, -1] + 1j*sol.y[3, -1])/z).real; dirv = float(mpf(val))
    print(f"{y:7.1f}i   {dirv: .10e}   {pred: .10e}   {abs(pred - dirv)/abs(dirv):.2e}")
