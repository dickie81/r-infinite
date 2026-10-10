#!/usr/bin/env python3
"""Round 391: the locus |χ(s)| = 1 of ζ(s) = χ(s)ζ(1 − s) contains more than the critical line.
χ(s) = Γ_ℝ(1 − s)/Γ_ℝ(s), Γ_ℝ(s) = π^{−s/2}Γ(s/2). Every gate fails the run if it fails.
  C1  (python-flint's Arb ball arithmetic, 200 bits, a proof): for σ in {0.1, 0.3, 0.7, 0.9}, the balls
      containing |χ(σ + 6.27i)| − 1 and |χ(σ + 6.30i)| − 1 lie on opposite sides of 0. By continuity in t,
      |χ(σ + it)| = 1 for some t in (6.27, 6.30): a point of the locus with Re s = σ ≠ ½.
  C2  (mpmath, 30 digits): ∂σ log|χ(σ + it)| at σ = ½ equals −2θ′(t), θ the Riemann–Siegel theta, at
      t = 3, 6, 7, 10 (to 10⁻²⁰), and θ′(t₀) = 0 at t₀ = 6.2898359888369…; at ½ + it₀ the gradient of the
      harmonic function log|χ| vanishes, which is where a second branch of its zero set crosses the line.
  C3  (mpmath, descriptive): the branch t = τ(σ), found by root-finding at σ = 0.05, 0.1, 0.3, 0.45, 0.55, 0.7,
      0.9, 0.95, stays within 0.006 of t₀ and agrees with τ(σ) ≈ t₀ + θ‴(t₀)/(6θ″(t₀))·(σ − ½)² to 10⁻⁵, and
      τ(σ) = τ(1 − σ) to 10⁻²⁰ (log|χ| is odd about σ = ½).
  C4  (mpmath, 20 digits, a census on grids, not a proof): along t in (0, 40] in steps of 0.001, at each of
      those eight σ, log|χ(σ + it)| changes sign exactly once, at τ(σ); along σ = j/100, j = 1..99, at each
      t = k/20, k = 1..399, it changes sign only next to σ = ½ (between grid points within 0.015 of ½).
  C5  (Arb, a proof) the Davenport–Heilbronn factor of 1as(vi), χ_DH(s) = G(1 − s)/G(s) with
      G(s) = (5/π)^((s+1)/2)Γ((s+1)/2), so that f(s) = χ_DH(s)f(1 − s): for σ in {0.1, 0.3, 0.7, 0.9},
      |χ_DH(σ + 1.19i)| − 1 and |χ_DH(σ + 1.23i)| − 1 lie in balls of opposite strict signs, while 40 balls
      covering |χ(σ + it)| − 1 for t in [1.19, 1.23] all lie on one side of 0. So |χ_DH| = 1 at a point with
      Re s = σ ≠ ½ where |χ| ≠ 1: the two loci share the line and differ off it. With mpmath, the D–H branch
      crosses the line at t₁ = 1.2116358 (to 10⁻⁶), where ∂σ log|χ_DH| vanishes on the line."""
import sys
from flint import acb, arb, ctx
from mpmath import mp, mpf, mpc, gamma, pi, log, findroot, diff, siegeltheta, fabs
fails = 0
def gate(name, ok, detail):
    global fails
    fails += (not ok)
    print(f"{'PASS' if ok else 'FAIL'} {name}: {detail}")
ctx.prec = 200
def chi_arb(s):
    GR = lambda w: acb.pi() ** (-w / 2) * (w / 2).gamma()
    return GR(1 - s) / GR(s)
for sg in ('0.1', '0.3', '0.7', '0.9'):
    lo = abs(chi_arb(acb(arb(sg), arb('6.27')))) - 1
    hi = abs(chi_arb(acb(arb(sg), arb('6.30')))) - 1
    ok = (lo > 0 and hi < 0) or (lo < 0 and hi > 0)
    gate(f"C1 σ = {sg}", ok, f"|χ|−1 at t = 6.27: {lo.str(6)}; at t = 6.30: {hi.str(6)}")
def chiDH_arb(s):
    G = lambda w: (5 / acb.pi()) ** ((w + 1) / 2) * ((w + 1) / 2).gamma()
    return G(1 - s) / G(s)
for sg in ('0.1', '0.3', '0.7', '0.9'):
    lo = abs(chiDH_arb(acb(arb(sg), arb('1.19')))) - 1
    hi = abs(chiDH_arb(acb(arb(sg), arb('1.23')))) - 1
    # [1.19, 1.23] as 40 balls of radius 0.0005 centred at 1.1905, 1.1915, ..., 1.2295
    seg = [abs(chi_arb(acb(arb(sg), arb(f'{1.1905 + k / 1000:.4f}', '0.0005')))) - 1 for k in range(40)]
    seg_pos, seg_neg = all(b > 0 for b in seg), all(b < 0 for b in seg)
    ok = ((lo > 0 and hi < 0) or (lo < 0 and hi > 0)) and (seg_pos or seg_neg)
    gate(f"C5 σ = {sg}", ok, f"|χ_DH|−1 at t = 1.19: {lo.str(6)}; at t = 1.23: {hi.str(6)}; "
         f"|χ|−1 on [1.19, 1.23] (40 balls): all {'> 0' if seg_pos else '< 0' if seg_neg else 'not one-signed'}, "
         f"first {seg[0].str(4)}")
mp.dps = 30
GR = lambda s: pi**(-s/2)*gamma(s/2)
L = lambda sg, t: log(abs(GR(1 - mpc(sg, t))/GR(mpc(sg, t))))
err = max(fabs(diff(lambda x: L(x, t), mpf('0.5')) + 2*diff(siegeltheta, t)) for t in (3, 6, 7, 10))
gate("C2 ∂σ log|χ| = −2θ′ on the line", err < mpf(10)**-20, f"max error {mp.nstr(err, 3)}")
t0 = findroot(lambda t: diff(siegeltheta, t), 6.3)
gate("C2 θ′(t₀) = 0", fabs(t0 - mpf('6.2898359888369')) < mpf(10)**-12, f"t₀ = {mp.nstr(t0, 16)}")
GD = lambda s: (5/pi)**((s+1)/2)*gamma((s+1)/2)
LD = lambda sg, t: log(abs(GD(1 - mpc(sg, t))/GD(mpc(sg, t))))
t1 = findroot(lambda t: diff(lambda x: LD(x, t), mpf('0.5')), 1.2)
gate("C5 t₁ (D–H)", fabs(t1 - mpf('1.2116358')) < mpf(10)**-6, f"t₁ = {mp.nstr(t1, 12)}")
c = diff(siegeltheta, t0, 3)/(6*diff(siegeltheta, t0, 2))
taus = {}
for sg in ('0.05', '0.1', '0.3', '0.45', '0.55', '0.7', '0.9', '0.95'):
    taus[sg] = findroot(lambda t: L(mpf(sg), t), t0)
dev = max(fabs(taus[sg] - t0) for sg in taus)
pred = max(fabs(taus[sg] - (t0 + c*(mpf(sg) - mpf('0.5'))**2)) for sg in taus)
sym = max(fabs(taus[a] - taus[b]) for a, b in (('0.05', '0.95'), ('0.1', '0.9'), ('0.3', '0.7'), ('0.45', '0.55')))
gate("C3 |τ(σ) − t₀| < 0.006", dev < mpf('0.006'), f"max {mp.nstr(dev, 4)}; τ(0.05) = {mp.nstr(taus['0.05'], 12)}")
gate("C3 second-order prediction", pred < mpf(10)**-5, f"max error {mp.nstr(pred, 3)}, curvature {mp.nstr(c, 6)}")
gate("C3 τ(σ) = τ(1 − σ)", sym < mpf(10)**-20, f"max error {mp.nstr(sym, 3)}")
mp.dps = 20
tcount = {}
for sg in taus:
    s0, prev, n = mpf(sg), None, []
    for k in range(1, 40001):
        v = L(s0, mpf(k)/1000)
        if prev is not None and (prev < 0) != (v < 0):
            n.append(mpf(k)/1000)
        prev = v
    tcount[sg] = n
ok = all(len(n) == 1 and fabs(n[0] - taus[sg]) < mpf('0.002') for sg, n in tcount.items())
gate("C4 one crossing along t at each σ", ok,
     ", ".join(f"σ={sg}: {len(n)}" for sg, n in tcount.items()))
off = []
for k in range(1, 400):
    t, prev = mpf(k)/20, None
    for j in range(1, 100):
        v = L(mpf(j)/100, t)
        if prev is not None and (prev < 0) != (v < 0) and fabs(mpf(j)/100 - mpf('0.5')) > mpf('0.015'):
            off.append((k, j))
        prev = v
gate("C4 no crossing off the line along σ", not off, f"{len(off)} off-line sign changes on 399 × 99 grid")
print("all gates pass" if fails == 0 else f"{fails} gate(s) failed")
sys.exit(1 if fails else 0)
