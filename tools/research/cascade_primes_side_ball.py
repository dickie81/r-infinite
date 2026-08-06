#!/usr/bin/env python3
"""Theorem 1as verifier: the ball from the primes -- roundness selected by
self-duality, the two-channel ledger, the pure-phase equivalence, and the
insufficiency certificate.

Gates (all exit-gated; any failure exits 1):
  g1  Maxwell-Borel: exact sphere-marginal density f_d(x) =
      c_d (1 - x^2/d)^((d-3)/2) -> N(0,1) in sup-norm, decreasing at
      d = 10/100/1000, with the d = 1000 distance < 1e-3.
  g2  the l^p selection lever: e^(-pi x^2) Fourier-self-dual to 1e-10
      (normalized shapes); scale-scanned p = 1 and p = 4 families have
      self-duality deviation minima > 0.05; the width-2 Gaussian is not
      self-dual (deviation > 0.1); PLUS the round-189 obstruction
      witnesses upgrading the scan to the classical argument: the
      p = 4 transform attains negative values (min < -0.1) against a
      positive function, and the p = 1 transform IS the Lorentzian
      2/(1+4 pi^2 xi^2) to 1e-4 (polynomial decay -- no scaling
      matches stretched-exponential).
  g3  theta functional equation theta(1/t) = sqrt(t) theta(t) to 25 digits.
  g4  the p-adic unit-ball shell identity: Z_p(1_{Z_p}, s) (1 - p^(-s))
      = 1 - 1/p exactly (p = 2, 3 at s = 2.3) -- the Euler factor as the
      unit-ball self-pairing.
  g5  the gap IS the zeros: explicit formula at x = 1000.5 with 200 zero
      pairs -- psi = 996.681, |psi - explicit| < 0.7 (truncation), gap
      -3.819 +- 0.01, zero-term -4.452 +- 0.01, |gap| < sqrt(x).
  g6  pure-phase fragments: 3+4cos+cos2 grid min >= 0; the 3-4-1 product
      >= 1 at five t-values; |zeta(1 + i gamma_1)| > 0.3; Turing count --
      sign changes of Z on (0,100] == 29 == round(theta(100)/pi + 1);
      |xi(s) - xi(1-s)| < 1e-25 at 0.3 + 7.7i.
  g7  the congruence locus: ||chi(1/2 + 50i)| - 1| < 1e-12; |chi(1 + 50i)|
      matches (50/2pi)^(-1/2) to 1e-6; Euler floor min |zeta(1.1 + it)|
      >= zeta(2.2)/zeta(1.1) over t in [0,200]; Riemann-Siegel main-sum
      sign change brackets gamma_1.
  g8  the insufficiency certificate (Davenport-Heilbronn): kappa to 12
      digits; Lambda(s) = Lambda(1-s) to 1e-28; both off-line zeros
      (Re = 0.808517..., 0.650830...) with |f| < 1e-25 and FE partners;
      component congruence |L(chi)| = |L(chibar)| != 0 with ratio exactly
      -c2/c1 to 1e-20 at both roots.
  g9  the log-spectrum anatomy: Lambda_zeta supported exactly on prime
      powers (zero at 6,10,12,14,15,18,20), positive, no negatives to
      n = 20; Lambda_DH leaks (Lambda(6) > 1.9) and goes negative at
      exactly {3,4,9,12,13,14,19} within n <= 20.
  g10 evolution as condensation: correlation of the truncated Euler
      product's line profile with log|zeta| climbs 0.70/0.83/0.92/0.94 at
      y = 3/10/100/1000 (strictly increasing) and FALLS to 0.79 at
      y = 20000 (the pole-term fall -- the raw products diverge at every
      strip point, so there is no edge in y; the fall is where the pole
      term swamps the profile; phrasing corrected round 191); y = 100
      dips within 0.15 of the first three zeros.
  g11 the CC identity: numeric (log Gamma_R)'(d+1) equals part0's
      p(d) = -ln(pi)/2 + psi((d+1)/2)/2 to 1e-15 for d = 1..10; source
      needles in part0.tex and this paper's Section 2 primitive line.
  g12 the declared-conjecture arithmetic (gated as arithmetic, fenced as
      conjecture): N = t_universe/t_Planck = 8.07e60; N^2 * Lambda*l_Pl^2
      = 1.88 +- 0.03; S_dS/N^2 = 5.0 +- 0.15; N_sat/N = 2.24 +- 0.02;
      fill 20 +- 1 %; p_max in (2.5e63, 2.8e63); fence needles present.
  g13 the paper needles for the 1as block (title; selection sentence;
      product-state restatement; fairness sentence; both off-line zero
      values; the statistical-vs-completed sentence).
  g14 the chain: cascade_lattice_forcing.py (Theorem 1ar) exits 0.
  g15 the footer census (this script backticked >= 2; "70 scripts cited
      in place"; "Theorems 1i-1at").

Sabotage record (each: fresh tree, single mangle, restore from pristine;
clean baselines B1/B2 15/15 around the suite; restore integrity by cmp;
all censuses below are the OBSERVED suite results):
  (a) title needle mangled in the paper -> g13 FAIL alone (14/15 stand)
  (b) paper constant 1.88 -> 1.98       -> g12 FAIL alone
  (c) DH root real-part digit mangled in the paper -> g13 FAIL (value
      needle) while g8 (recomputed root) STANDS -- the pair demonstrates
      paper-vs-computation independence
  (d) Lambda_DH negative-census set edited in code -> g9 FAIL alone
  (e) footer census reverted 69 -> 68   -> g15 FAIL AND g14 FAIL: the
      chained 1ar verifier's own footer gate catches the same reversion,
      so the census defect propagates through the chain (observed, not
      designed -- a stronger containment than the single-gate plan)
  (f) chain target renamed in code      -> g14 FAIL alone
"""
import sys, math, subprocess, os
import numpy as np
from mpmath import (mp, mpf, mpc, zeta, gamma, pi, sqrt, log, cos, exp,
                    siegelz, siegeltheta, findroot, psi as digamma, diff,
                    jtheta, isnan)

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")
PART0 = os.path.join(HERE, "..", "..", "src", "cascade-series-part0.tex")
paper = open(PAPER, encoding="utf-8").read()
part0 = open(PART0, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label)
    if not ok:
        fails.append(label)

mp.dps = 30

# ---------------------------------------------------------------- g1
def marginal_sup(d):
    cd = float(gamma(mpf(d)/2)/(sqrt(mpf(d)*pi)*gamma((mpf(d)-1)/2)))
    xs = np.linspace(-4, 4, 4001)
    fd = np.where(xs**2 < d, cd*np.maximum(0.0, 1 - xs**2/d)**((d-3)/2), 0.0)
    ph = np.exp(-xs**2/2)/math.sqrt(2*math.pi)
    return float(np.max(np.abs(fd - ph)))
s10, s100, s1000 = marginal_sup(10), marginal_sup(100), marginal_sup(1000)
ok = s10 > s100 > s1000 and s1000 < 1e-3
print(f"  g1 sup-norm: d=10 {s10:.2e}  d=100 {s100:.2e}  d=1000 {s1000:.2e}")
gate("g1 Maxwell-Borel exact marginal -> Gaussian, decreasing, <1e-3 at d=1000", ok)

# ---------------------------------------------------------------- g2
X = np.linspace(-10, 10, 4097)
def selfdual_dev(g):
    gv = g(X)
    F = np.array([np.trapezoid(gv*np.exp(-2j*np.pi*x*X), X) for x in X]).real
    gn = gv/math.sqrt(np.trapezoid(gv**2, X))
    Fn = F/math.sqrt(max(np.trapezoid(F**2, X), 1e-300))
    return float(np.max(np.abs(Fn - gn)))
dev2 = selfdual_dev(lambda x: np.exp(-np.pi*x**2))
devw = selfdual_dev(lambda x: np.exp(-x**2/2))
def scan_min(p):
    best = 1e9
    for a in np.logspace(-1.2, 1.2, 25):
        best = min(best, selfdual_dev(lambda x: np.exp(-a*np.abs(x)**p)))
    return best
m1, m4 = scan_min(1), scan_min(4)
# round-189 obstruction witnesses (F1): negativity at p = 4; Lorentzian at p = 1
XW = np.linspace(-14, 14, 8193)
g4v = np.exp(-XW**4)
F4min = min(float(np.trapezoid(g4v*np.exp(-2j*np.pi*x*XW), XW).real)
            for x in np.linspace(0, 3, 300))
g1v = np.exp(-np.abs(XW))
xiw = np.linspace(0, 5, 200)
F1dev = max(abs(float(np.trapezoid(g1v*np.exp(-2j*np.pi*x*XW), XW).real)
                - 2/(1 + 4*math.pi**2*x**2)) for x in xiw)
print(f"  g2 devs: e^(-pi x^2) {dev2:.2e}; width-2 {devw:.2e}; min p=1 {m1:.3f}; "
      f"min p=4 {m4:.3f}; FT(e^-x^4) min {F4min:.3f}; Lorentzian dev {F1dev:.1e}")
gate("g2 l^p selection: only the round ball's limit is Fourier-self-dual "
     "(scan + round-189 obstruction witnesses)",
     dev2 < 1e-10 and devw > 0.1 and m1 > 0.05 and m4 > 0.05
     and F4min < -0.1 and F1dev < 1e-4)

# ---------------------------------------------------------------- g3
def theta_fn(t):
    return jtheta(3, 0, exp(-pi*t))
t0 = mpf("0.37")
ok = abs(theta_fn(1/t0) - sqrt(t0)*theta_fn(t0)) < mpf(10)**-25
gate("g3 theta FE theta(1/t) = sqrt(t) theta(t) to 25 digits", ok)

# ---------------------------------------------------------------- g4
ok = True
s = mpf("2.3")
for p in (2, 3):
    Zp = sum((1 - mpf(1)/p) * mpf(p)**(-k) * mpf(p)**(-k*(s-1)) for k in range(0, 400))
    ok &= abs(Zp*(1 - mpf(p)**(-s)) - (1 - mpf(1)/p)) < mpf(10)**-25
gate("g4 p-adic shell identity: the Euler factor is the unit-ball pairing (p=2,3)", ok)

# ---------------------------------------------------------------- g5
mp.dps = 20
from sympy import factorint, primerange
from mpmath import zetazero
x = mpf("1000.5")
psi_x = mpf(0)
for n in range(2, 1001):
    f = factorint(n)
    if len(f) == 1:
        psi_x += log(list(f.keys())[0])
zsum = mpf(0)
for k in range(1, 201):
    rho = zetazero(k)
    zsum += 2*(x**rho/rho).real
zterm = -zsum - log(2*pi) - mpf("0.5")*log(1 - x**-2)
explicit = x + zterm
gap = psi_x - x
print(f"  g5 psi={float(psi_x):.4f} explicit={float(explicit):.4f} gap={float(gap):.4f} zterm={float(zterm):.4f}")
ok = (abs(psi_x - explicit) < mpf("0.7") and abs(gap + mpf("3.8191")) < mpf("0.01")
      and abs(zterm + mpf("4.4516")) < mpf("0.01") and abs(gap) < sqrt(x))
gate("g5 the gap IS the zeros: explicit formula at x=1000.5, inside the sqrt(x) envelope", ok)

# ---------------------------------------------------------------- g6
mp.dps = 25
grid_min = min(3 + 4*cos(mpf(k)/100) + cos(2*mpf(k)/100) for k in range(0, 629))
ok = grid_min > -mpf(10)**-10
sig = mpf("1.001")
for t in (1, mpf("14.1347"), mpf("21.022"), 50, 100):
    v = abs(zeta(sig))**3 * abs(zeta(mpc(sig, t)))**4 * abs(zeta(mpc(sig, 2*t)))
    ok &= v >= 1
ok &= abs(zeta(mpc(1, mpf("14.134725")))) > mpf("0.3")
T = 100
vals = [siegelz(mpf(i)/50) for i in range(1, 50*T + 1)]
changes = sum(1 for a, b in zip(vals, vals[1:]) if a*b < 0)
strip = round(float(siegeltheta(T)/pi + 1))
ok &= (changes == 29 and strip == 29)
def xi(sv):
    return sv*(sv-1)/2 * pi**(-sv/2) * gamma(sv/2) * zeta(sv)
s0 = mpc(mpf("0.3"), mpf("7.7"))
ok &= abs(xi(s0) - xi(1 - s0)) < mpf(10)**-25
print(f"  g6 grid min {float(grid_min):.1e}; Turing {changes} == strip {strip}")
gate("g6 pure-phase fragments: 3-4-1 ceiling, Turing 29==29, xi-symmetry", ok)

# ---------------------------------------------------------------- g7
def GR(sv): return pi**(-sv/2)*gamma(sv/2)
def chi_fe(sv): return GR(1-sv)/GR(sv)
t = mpf(50)
ok = abs(abs(chi_fe(mpc(mpf("0.5"), t))) - 1) < mpf(10)**-12
ok &= abs(abs(chi_fe(mpc(1, t))) - (t/(2*pi))**mpf("-0.5")) < mpf(10)**-6
floor_ = zeta(mpf("2.2"))/zeta(mpf("1.1"))
mn = min(abs(zeta(mpc(mpf("1.1"), mpf(k)))) for k in range(0, 201, 2))
ok &= mn >= floor_
def rs_main(tv):
    N = int(sqrt(tv/(2*pi)))
    return 2*sum(cos(siegeltheta(tv) - tv*log(n))/sqrt(n) for n in range(1, N+1))
g1v = mpf("14.134725141734693790")
ok &= (rs_main(g1v - mpf("0.5")) < 0) and (rs_main(g1v + mpf("0.5")) > 0)
print(f"  g7 |chi(1/2+50i)|-1 tiny; floor {float(floor_):.4f} <= min {float(mn):.4f}")
gate("g7 congruence locus |chi|=1, Euler floor, RS null bracket", ok)

# ---------------------------------------------------------------- g8
mp.dps = 30
kappa = (sqrt(10 - 2*sqrt(5)) - 2)/(sqrt(5) - 1)
ok = abs(kappa - mpf("0.284079043840")) < mpf(10)**-12
cdh = [mpf(1), kappa, -kappa, mpf(-1)]
def fdh(sv):
    return 5**(-sv) * sum(cdh[a-1]*zeta(sv, mpf(a)/5) for a in range(1, 5))
def Lam(sv):
    return (mpf(5)/pi)**((sv+1)/2) * gamma((sv+1)/2) * fdh(sv)
for sv in (mpc("0.3", "7.7"), mpc("0.72", "30.1")):
    ok &= abs(Lam(sv) - Lam(1 - sv)) < mpf(10)**-28
chi5 = [mpc(1), mpc(0, 1), mpc(0, -1), mpc(-1)]
def Lfun(sv, ch):
    return 5**(-sv) * sum(ch[a-1]*zeta(sv, mpf(a)/5) for a in range(1, 5))
c1, c2 = (1 - mpc(0, 1)*kappa)/2, (1 + mpc(0, 1)*kappa)/2
target = -c2/c1
for seed, re_expect in ((mpc("0.81", "85.7"), mpf("0.808517182456")),
                        (mpc("0.65", "114.16"), mpf("0.650830080609"))):
    r = findroot(fdh, seed)
    ok &= abs(fdh(r)) < mpf(10)**-25
    ok &= abs(r.real - re_expect) < mpf(10)**-8
    ok &= abs(fdh(1 - mpc(r.real, -r.imag))) < mpf(10)**-24
    L1 = Lfun(r, chi5); L2 = Lfun(r, [z.conjugate() for z in chi5])
    ok &= abs(abs(L1) - abs(L2)) < mpf(10)**-20 and abs(L1) > mpf("0.4")
    ok &= abs(L1/L2 - target) < mpf(10)**-20
gate("g8 Davenport-Heilbronn: same FE geometry, off-line zeros, component congruence", ok)

# ---------------------------------------------------------------- g9
def lam_table(a, N):
    L = {1: mpf(0)}
    for n in range(2, N+1):
        sv = a[n]*log(n)
        for d in range(2, n):
            if n % d == 0:
                sv -= L[d]*a[n//d]
        L[n] = sv
    return L
N9 = 20
Lz = lam_table({n: mpf(1) for n in range(1, N9+1)}, N9)
pat = [mpf(1), kappa, -kappa, mpf(-1), mpf(0)]
Ld = lam_table({n: pat[(n-1) % 5] for n in range(1, N9+1)}, N9)
pp = {2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19}
ok = all(abs(Lz[n]) < mpf(10)**-12 for n in range(2, N9+1) if n not in pp)
ok &= all(Lz[n] > mpf("0.1") for n in pp)
ok &= Ld[6] > mpf("1.9")
neg = {n for n in range(2, N9+1) if Ld[n] < -mpf(10)**-12}
ok &= neg == {3, 4, 9, 12, 13, 14, 19}
gate("g9 log-spectrum anatomy: prime-power support + positivity vs leak + negatives", ok)

# ---------------------------------------------------------------- g10
mp.dps = 15
ts = np.arange(10.0, 27.0, 0.05)
lz = np.array([float(log(abs(zeta(mpc(0.5, float(tv)))))) for tv in ts])
def logabs_P(y):
    ps = np.array(list(primerange(2, y+1)), dtype=float)
    out = np.zeros_like(ts)
    for i, tv in enumerate(ts):
        z = 1 - ps**(-0.5)*np.exp(-1j*tv*np.log(ps))
        out[i] = -np.sum(np.log(np.abs(z)))
    return out
corrs = {}
prof100 = None
for y in (3, 10, 100, 1000, 20000):
    lp = logabs_P(y)
    corrs[y] = float(np.corrcoef(lp, lz)[0, 1])
    if y == 100:
        prof100 = lp
expected = {3: 0.6971, 10: 0.8330, 100: 0.9175, 1000: 0.9425, 20000: 0.7885}
ok = all(abs(corrs[y] - expected[y]) < 0.02 for y in expected)
ok &= corrs[3] < corrs[10] < corrs[100] < corrs[1000] and corrs[20000] < corrs[1000]
mins = [ts[i] for i in range(1, len(ts)-1)
        if prof100[i] < prof100[i-1] and prof100[i] < prof100[i+1]]
mins = sorted(mins, key=lambda t0: prof100[list(ts).index(t0)])[:3]
ok &= all(min(abs(m - z0) for m in mins) < 0.15 for z0 in (14.1347, 21.0220, 25.0109))
print(f"  g10 corrs: {[round(corrs[y],4) for y in (3,10,100,1000,20000)]}")
gate("g10 condensation: corr ladder rises then falls at the pole-term fall; dips on zeros", ok)

# ---------------------------------------------------------------- g11
mp.dps = 25
ok = True
for d in range(1, 11):
    numeric = diff(lambda sv: log(pi**(-sv/2)*gamma(sv/2)), mpf(d+1))
    closed = -log(pi)/2 + digamma(0, (mpf(d)+1)/2)/2
    ok &= abs(numeric - closed) < mpf(10)**-15
ok &= r"p(d) = -\tfrac{1}{2}\ln\pi" in part0
ok &= "p(d) = (log Γ_ℝ)′(d+1)" in paper
gate("g11 the CC identity: part0's p(d) == (log Gamma_R)'(d+1), source-anchored", ok)

# ---------------------------------------------------------------- g12
t_u = 13.787e9*3.1557e7
N = t_u/5.3912e-44
lam = 1.1056e-52*(1.616255e-35)**2
S = 3*math.pi/lam
ok = abs(N - 8.07e60) < 0.02e60
ok &= abs(N*N*lam - 1.88) < 0.03
ok &= abs(S/(N*N) - 5.0) < 0.15
ok &= abs(math.sqrt(S)/N - 2.24) < 0.02
ok &= abs(N*N/S - 0.20) < 0.01
p_max = math.sqrt(S)*(math.log(math.sqrt(S)) + math.log(math.log(math.sqrt(S))))
ok &= 2.5e63 < p_max < 2.8e63
ok &= "THE FOLLOWING ARE DECLARED CONJECTURES," in paper
ok &= "the classic Λ ~ 1/N² coincidence rebranded" in paper
ok &= "N²·(Λℓ²_Pl) = 1.88 and S_dS/N² = 5.0" in paper
gate("g12 conjecture-block arithmetic gated, paper values pinned, fence and "
     "caveat needles present", ok)

# ---------------------------------------------------------------- g13
needles = [
    "**Theorem 1as (the ball from the primes: roundness selected by",
    "Roundness is selected by the primes' self-duality requirement",
    "a pure product state over the primes admits",
    "exact cancellation requires fairness",
    "0.808517",
    "0.650830",
    "physics realizes the statistical theorem; only the completed",
    # round-189 repair needles
    "either obstruction kills self-duality at",
    "Θ = sup Re ρ ∈ [½, 1], and Θ = ½ ⟺ RH",
    "114.163342…i",
    "§3's Theorem 1e, the A1 dynamics block",
    "Theorem 2 fixes its occupant in two steps:",
    "The free commutative monoid on",
    "enters part0's invariant I₀ = Ω₁₉ × Ω₂₁₇ ≈ 1.2051×10⁻¹²⁰",
]
ok = all(nd in paper for nd in needles)
for nd in needles:
    if nd not in paper:
        print(f"  g13 MISSING: {nd!r}")
gate("g13 the 1as paper needles", ok)

# ---------------------------------------------------------------- g14
r = subprocess.run([sys.executable, os.path.join(HERE, "cascade_lattice_forcing.py")],
                   capture_output=True, text=True)
gate("g14 the chain: cascade_lattice_forcing.py (Theorem 1ar) exits 0", r.returncode == 0)

# ---------------------------------------------------------------- g15
ok = paper.count("`cascade_primes_side_ball.py`") >= 2
ok &= "70 scripts cited in place" in paper
ok &= "Theorems 1i–1at" in paper
gate("g15 the footer census (this script backticked >= 2; 70 cited in place; "
     "the range 1i–1at)", ok)

print()
if fails:
    print(f"FAILURES ({len(fails)}):")
    for f in fails:
        print("  " + f)
    sys.exit(1)
print("ALL GATES PASS (15/15)")
