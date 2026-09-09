#!/usr/bin/env python3
"""Theorem 1bt -- the pole-free form is indefinite: Q_0 = Q - 2 ghat(i/2)^2
has a negative direction on L^2(-a, a) for every a >= 0.2, unconditionally,
witnessed by cosh(u/2); at the certified cells it has exactly one. Substrate
pole_witness.py (imported, content-addressed); the certified balls re-derived
live from the Grams. Tower member 29 (top).

THE CLAIMS GATED. (0) THE CONSTANTS: Hadamard's K = 2 + gamma_E - ln 4 pi
against the 6700-zero list's partial sum plus the density tail (within 1e-5);
K' = K (1 + 5/(4 * 14^2)) and the first zero above 14. (1) THE CLOSED FORMS:
ghat_a(r) against quadrature at twenty points and four supports (below 1e-12);
ghat_a(i/2) = a + sinh a against quadrature; V(a) = 4 cosh(a/2) - 2 against the
jumps plus the total variation by quadrature. (2) THE BOUND: on [0.2, 1] the
margin 2 (a + sinh a)^2 - K' V(a)^2 e^a has a positive lower ball end on 2000
subintervals (arb interval arithmetic -- a certified evaluation); for a >= 1
the elementary ratio (1 - e^{-2a})^2 / (8 K' (1 + 2 e^{-a} + e^{-2a})) exceeds
1 at a = 1 and both its factors are monotone (checked on a grid to a = 15, beyond which they are 1 to double precision);
the bound fails at a = 0.15 (the threshold is the bound's). (3) THE FORM'S
VALUE: on the 6700-zero list Q_0(g_a) = 2 sum ghat^2 + tail - 2 ghat(i/2)^2 is
negative at a = 0.15, 0.2, 0.5, 0.6914, 1.0, 1.75 (floating point; the stated
four values pinned). (4) AT THE CELLS: the Rayleigh ball of Q_0's lowest
approximate vector re-derived live at delta = 1.0, 1.3828125, 2.0 is negative
(upper ends within 0.01 of -1.98, -2.82, -4.30) and the first cosine mode's
positive; the interlacing lambda_2(Q_0) >= lambda_1(Q) holds on the approximate
spectra; the certified positivity of the form at delta = 1.0 (1bj's Temple
enclosure) and 1.3828125 (1bl's certificate) loaded and positive -- exactly
one negative direction there. (5) mangle probes; (6) the paper's numbers
parsed back; (7) the chain obligation to cascade_count_constant.py; (8) the
needles and census.

WHAT IS NOT CLAIMED. Nothing about positivity of Q beyond the cited
certificates; the zero-side values are floating point on the list; no Riemann
Hypothesis consequence.
"""
import math, os, sys, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from pole_witness import K_HADAMARD, K_PRIME, EULER, V, ghat, ghat_quad, ghat_pole, bound_lhs, bound_rhs, margin, Q0_zero_side, hadamard_check
from weil_prime_gram import gram, rayleigh
from lfun_gram import gram_L, ZETA
from oneprime_interval_temple import run as run_T1
from slepian_arb_certificate import run as run_SM
from flint import arb, acb, arb_mat, acb_mat, ctx
from scipy.integrate import quad

PAPER_NEEDLES = [
    {'g': 'g8', 's': 'Theorem 1bt (the pole-free form is indefinite', 'form': 'plain'},
    {'g': 'g8', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 11},
    {'s': '`cascade_pole_indefinite.py`', 'min': 2, 'g': 'g8'},
    {'s': 'the **96 scripts cited in place** above', 'form': 'ws', 'g': 'g8'},
    {'s': 'extended by Theorems 1i–1bt:', 'form': 'ws', 'g': 'g8'},
    {'g': 'g6', 's': '−1.99, −4.03, −9.33, −41.09', 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ZS = np.array(json.load(open(os.path.join(HERE, "checkpoints", "zeta_zeros_6700.json"))), dtype=float)

# ---------------------------------------------------------------- g0
tot, s, tail = hadamard_check(ZS)
ok = abs(tot - K_HADAMARD) <= 1e-5 and abs(K_HADAMARD - (2 + EULER - math.log(4*math.pi))) < 1e-15
ok &= abs(K_PRIME - K_HADAMARD*(1 + 1.25/196)) < 1e-15 and ZS[0] > 14.0 and K_PRIME <= 0.0465
gate(f"g0 the constants: K = 2 + gamma_E - ln 4 pi = {K_HADAMARD:.6f} against the list's sum plus the density tail {tot:.6f}; K' = K (1 + 5/(4*14^2)) = {K_PRIME:.6f} <= 0.0465; the first zero {ZS[0]:.4f} > 14", ok)

# ---------------------------------------------------------------- g1
ok = True; worst = 0.0
for a in (0.2, 0.5, 1.0, 1.75):
    for r in np.linspace(0.3, 60.0, 20):
        d = abs(float(ghat(r, a)) - ghat_quad(r, a)); worst = max(worst, d); ok &= d <= 1e-12
    ok &= abs(ghat_pole(a) - quad(lambda u: math.cosh(u/2)*math.exp(-u/2), -a, a)[0]) <= 1e-12
    tv = quad(lambda u: abs(0.5*math.sinh(u/2)), -a, a)[0] + 2*math.cosh(a/2)
    ok &= abs(V(a) - tv) <= 1e-12
gate(f"g1 the closed forms: ghat_a(r) against quadrature (max |diff| {worst:.1e}), ghat_a(i/2) = a + sinh a, V(a) = 4 cosh(a/2) - 2 = the jumps plus the variation, at four supports", ok)

# ---------------------------------------------------------------- g2
with ctx.workprec(200):
    Kp = (2 + arb.const_euler() - (4*arb.pi()).log())*(1 + arb(5)/(4*196))
    Kp_up = arb(Kp.upper())                                         # an upper bound suffices: the margin only shrinks
    n = 2000; lo_min = None; ok = True
    for i in range(n):
        a = arb(0.2 + 0.8*(i + 0.5)/n, 0.4/n)                       # the subinterval as a ball
        m = 2*(a + a.sinh())**2 - Kp_up*(4*(a/2).cosh() - 2)**2*a.exp()
        lo = m.lower(); lo_min = lo if lo_min is None or lo < lo_min else lo_min
        ok &= lo > 0
    lo_min = float(lo_min)
def ratio(a): return (1 - math.exp(-2*a))**2/(8*K_PRIME*(1 + 2*math.exp(-a) + math.exp(-2*a)))
grid = np.linspace(1.0, 15.0, 4000)                                  # beyond 15 the factors are 1 to double precision
num = [(1 - math.exp(-2*a))**2 for a in grid]; den = [(1 + 2*math.exp(-a) + math.exp(-2*a)) for a in grid]
ok &= ratio(1.0) > 1 and all(num[i] < num[i + 1] for i in range(len(grid) - 1)) and all(den[i] > den[i + 1] for i in range(len(grid) - 1))
ok &= margin(0.15) < 0 < margin(0.2)
gate(f"g2 the bound: on [0.2, 1] the margin's lower ball end positive on 2000 subintervals (min {lo_min:.4f}, certified); for a >= 1 the ratio (1 - e^-2a)^2/(8 K'(1 + 2e^-a + e^-2a)) = {ratio(1.0):.3f} at a = 1 with its factors monotone; the bound fails at a = 0.15 (margin {margin(0.15):+.4f}) and holds at 0.2 ({margin(0.2):+.4f})", ok)

# ---------------------------------------------------------------- g3
ok = True; q0 = {}
for a in (0.15, 0.2, 0.5, 0.6914, 1.0, 1.75):
    v, s, t = Q0_zero_side(a, ZS); q0[a] = v; ok &= v < 0 and t < 0.01
gate("g3 the form's value on the list (computed): Q_0(g_a) = " + ", ".join(f"{q0[a]:+.3f} at a = {a}" for a in q0) + " -- negative at every support, the tail below 0.01", ok)

# ---------------------------------------------------------------- g4
CELLS = {"d1.0": (1.0, 120, 600), "d1.38": (1.3828125, 140, 600), "d2.0": (2.0, 160, 700)}
EXPECT = {"d1.0": -1.98, "d1.38": -2.82, "d2.0": -4.30}
ok = True; ups = {}
for c, (d, K, prec) in CELLS.items():
    G, N, pp = gram(d, K, prec)
    G0, N0, pp0 = gram_L(d, K, prec, dict(ZETA, pole=False))
    with ctx.workprec(prec):
        Dm = arb_mat(K, K)
        for i in range(K): Dm[i, i] = 1/N0[i].sqrt()
        E, Rv = acb_mat((Dm*G0*Dm).mid()).eig(right=True, algorithm="approx")
        order = sorted(range(K), key=lambda i: float(E[i].real.mid()))
        mu = [float(E[order[j]].real.mid()) for j in range(3)]
        v0 = [Rv[i, order[0]].real.mid()/N0[i].sqrt() for i in range(K)]
        r0 = rayleigh(G0, N0, v0, prec); ups[c] = float(r0.upper())
        ok &= r0.upper() < 0 and abs(ups[c] - EXPECT[c]) <= 0.01 + 1e-9 and ups[c] <= EXPECT[c] + 1e-9
        e1 = [arb(1 if i == 1 else 0) for i in range(K)]
        ok &= rayleigh(G0, N0, e1, prec).lower() > 0
        Eq, _ = acb_mat((Dm*G*Dm).mid()).eig(right=True, algorithm="approx")
        lam1 = min(float(Eq[i].real.mid()) for i in range(K))
        ok &= mu[0] < 0 < lam1 <= mu[1]*(1 + 1e-9)                      # interlacing on the approximate spectra: lambda_2(Q_0) >= lambda_1(Q)
PT = run_T1(); even10 = PT.get("even:1", {})
mech = run_SM("two", "even")
ok &= bool(even10) and even10.get("certified") and even10["rho"][0] > 0 and mech["final"] > 0
gate("g4 at the cells: Q_0's lowest approximate vector has a certified negative Rayleigh ball at delta = 1.0, 1.3828125, 2.0 (upper ends " + ", ".join(f"{ups[c]:.3f}" for c in CELLS)
     + ") and the first cosine mode a positive one; lambda_2(Q_0) >= lambda_1(Q) on the approximate spectra; the form's certified positivity loaded at delta = 1.0 (1bj's Temple enclosure, lower end "
     + f"{even10.get('rho', [0])[0]:.3e}) and 1.3828125 (1bl's certificate {mech['final']:.3e}) -- exactly one negative direction there", ok)

# ---------------------------------------------------------------- g5
def bound_ok(a, Kp): return 2*(a + math.sinh(a))**2 - Kp*(4*math.cosh(a/2) - 2)**2*math.exp(a) > 0
ok = bound_ok(0.2, K_PRIME) and not bound_ok(0.2, 10*K_PRIME) and not bound_ok(0.15, K_PRIME) and bound_ok(1.0, K_PRIME) and not bound_ok(1.0, 12*K_PRIME)
ok &= abs(hadamard_check(ZS[1:])[0] - K_HADAMARD) > 1e-3                  # the constant needs the first zero
gate("g5 mangle probes: the bound fails with K' tenfold at a = 0.2, with 12 K' at a = 1, and at a = 0.15; the Hadamard sum misses K without the first zero", ok)

# ---------------------------------------------------------------- g6
import paper_needles
S_Q0 = '−1.99, −4.03, −9.33, −41.09'
# the call carries its literal (the precheck's clause D); the string equals S_Q0 above by construction
ok = True
ok &= paper_needles.needle(PAPER_NEEDLES, '−1.99, −4.03, −9.33, −41.09', 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g6'] == [S_Q0]
def _num(s): return float(s.strip().replace('−', '-'))
_m = __import__("re").findall(r"(−[0-9]+\.[0-9]{2})", S_Q0)
ok &= len(_m) == 4 and all(abs(_num(x) - q0[a]) <= 5e-3 + 1e-9 for x, a in zip(_m, (0.5, 0.6914, 1.0, 1.75)))      # nearest 0.01
ok &= all(abs(ups[c] - EXPECT[c]) <= 0.01 + 1e-9 for c in CELLS) and K_PRIME <= 0.0465 and abs(K_HADAMARD - 0.04619) < 5e-6
gate("g6 the paper's numbers parsed back from the declared needles: the four zero-side values (nearest 0.01), the three upper ends (ceilings), K' <= 0.0465, K = 0.04619", ok)


# ---------------------------------------------------------------- g7
from cascade_tower import chain_ok
gate("g7 the chain obligation to cascade_count_constant.py (Theorem 1bs) met", chain_ok("cascade_count_constant.py"))

# ---------------------------------------------------------------- g8
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g8 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g8 the 1bt paper needles and the footer census (declared surface)", ok)

print(("\nALL GATES PASS (9/9)" if not fails else f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
