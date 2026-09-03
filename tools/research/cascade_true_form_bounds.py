#!/usr/bin/env python3
"""Theorem 1bn -- the true Weil form certified from above at every slack-law
cell: unconditional, model-free upper bounds on lambda_1(delta) = min
Q(g)/||g||^2 over L^2(-a, a) from the prime-side Gram in balls
(weil_prime_gram.py; primes <= e^delta, the archimedean term by
digamma/trigamma, the pole in closed form), with two trial vectors -- the
Gram minimiser in the even cosine basis and Connes-Consani-Moscovici's
k_lambda = E(h_lambda) (ccm_trial_vector.py) -- and the prolate deficit
1 - chi_2 alongside. Tower member 23 (top).

THE CLAIMS GATED. (1) THE CERTIFICATES: at the seven cells delta = 1.0,
1.3828125, 2.0, 2.3, 2.6, 3.0, 3.5 the stored Rayleigh balls of the
minimiser (K1 and K2 modes) and of the CCM trial (K2 modes) load at their
keys (executable content of the producer closure), are positive at their
lower ends, and have radii below 2^{-prec/2}; the paper's stated ln upper
bounds within 2e-3. (2) AGREEMENT WITH THE ZERO SIDE: the certified
upper bound (K2) sits within 0.15 nats of Theorem 1bm's model value at
every cell (the two are the same eigenvalue under RH; the model is
truncated, the certificate is not). (3) BASIS CONVERGENCE: K2 <= K1 and
the change <= 0.2 nats. (4) THE CCM TRIAL: its certified quotient is >=
the minimiser's (same subspace, up to the approximate eigenvector's
1e-6 relative slack) and within [0.1, 0.5] nats above it; its build
diagnostics (odd part <= 1e-12 of the norm, the finite-Fourier checks of
psi_0 and psi_4 agreeing at two points to 1e-10, the coefficient tail <=
1e-12 of the largest). (5) CROSS-CHECKS: the delta = 1.0 upper bound >=
Theorem 1bj's certified Temple lower bound (loaded at its key) and the
delta = 1.3828125 upper bound >= Theorem 1bl's certified even bound -- an
upper bound on the true lambda_1 must exceed any certified lower bound.
(6) THE GRAM LIVE: the prime-side Q of a C_c^inf bump's cosine expansion
against sum_gamma |ghat(gamma)|^2 over the 6700 zeros plus the smooth
tail, at delta = 1 and 2, to 1e-13 relative. (7) THE ARCHIMEDEAN
IDENTITIES LIVE, independently of the producer's code: the three
closed forms on [0, 2a] (Im psi, Re psi - psi(1/4), Re psi'/2 minus the
geometric tails) against mpmath quadrature at two omega, to 1e-12.
(8) THE PRIME-POWER LISTS: at every cell equal to {n <= e^delta :
Lambda(n) > 0} computed independently. (9) 1 - chi_2: the producer's
value (two points agreeing to 1e-8 relative) sits below the Fuchs law
by 0.03-0.6 nats and the minimiser sits 1.5-2.6 nats above it. (10)
mangle probes; (11) the chain obligation to cascade_slack_law.py; (12)
the paper needles and the census.

WHAT IS NOT CLAIMED. No lower bound beyond delta = 1.3828125 (Theorems
1bj-1bl); the truncation in K only loosens the bound; no Riemann
Hypothesis consequence -- a negative certified value would disprove RH
by the forward Weil criterion, and none occurs.
"""
import math, os, sys, json

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from true_form_cells import run as run_TF, CELLS
from slack_law_flint import run as run_SL
from slepian_arb_certificate import run as run_SM
from oneprime_interval_temple import run as run_T1
from weil_prime_gram import gram, rayleigh, prime_powers

PAPER_NEEDLES = [
    {'g': 'g12', 's': 'Theorem 1bn (the true form certified from above', 'form': 'plain'},
    {'g': 'g12', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 5},
    {'s': '`cascade_true_form_bounds.py`', 'min': 2, 'g': 'g12'},
    {'s': 'the **90 scripts cited in place** above', 'form': 'ws', 'g': 'g12'},
    {'s': 'extended by Theorems 1i–1bn:', 'form': 'ws', 'g': 'g12'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ORDER = ["d1.0", "d1.38", "d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
ST = {c: run_TF(c) for c in ORDER}
# the paper's stated certified upper bounds (ln), K2 minimiser -- PINS
PINS = {"d1.0": None, "d1.38": None, "d2.0": None, "d2.3": None, "d2.6": None, "d3.0": None, "d3.5": None}
CCM_PINS = {"d1.0": None, "d1.38": None, "d2.0": None, "d2.3": None, "d2.6": None, "d3.0": None, "d3.5": None}

def ball_ok(b, prec):
    return (all(k in b for k in ("mid", "rad_log2", "upper", "ln_upper", "positive")) and b["positive"]
            and b["ln_upper"] is not None and b["rad_log2"] is not None and b["rad_log2"] <= -prec/2)

# ---------------------------------------------------------------- g0
ok = all(st["verdict"].startswith("CERTIFIED") for st in ST.values())
ok &= all(ball_ok(st[k], st["prec"]) for st in ST.values() for k in ("min_K1", "min_K2", "ccm"))
ok &= all(st["cell"] == c and abs(st["delta"] - CELLS[c]["delta"]) < 1e-12 for c, st in ST.items())
gate("g0 the seven certificates load at their keys: three positive Rayleigh balls per cell with radii below 2^(-prec/2)", ok)

# ---------------------------------------------------------------- g1
ok = all(PINS[c] is not None and abs(ST[c]["min_K2"]["ln_upper"] - PINS[c]) <= 2e-3 for c in ORDER)
ok &= all(CCM_PINS[c] is not None and abs(ST[c]["ccm"]["ln_upper"] - CCM_PINS[c]) <= 2e-3 for c in ORDER)
gate("g1 the pins: the stated ln upper bounds (minimiser K2 and the CCM trial) within 2e-3 at the seven cells ("
     + ", ".join(f"{ST[c]['min_K2']['ln_upper']:.3f}" for c in ORDER) + " | " + ", ".join(f"{ST[c]['ccm']['ln_upper']:.3f}" for c in ORDER) + ")", ok)

# ---------------------------------------------------------------- g2
SL = {"d1.0": "d1.0", "d1.38": "d1.38", "d2.0": "d2.0", "d2.3": "d2.3", "d2.6": "d2.6", "d3.0": "d3.0", "d3.5": "d3.5"}
model = {c: run_SL(SL[c])["ln_eig"] for c in ORDER}
diff = {c: ST[c]["min_K2"]["ln_upper"] - model[c] for c in ORDER}
ok = all(abs(diff[c]) <= 0.15 for c in ORDER)
gate("g2 agreement with the zero side: certified upper (K2) minus Theorem 1bm's model ln lambda_1 within 0.15 nats ("
     + ", ".join(f"{diff[c]:+.3f}" for c in ORDER) + ")", ok)

# ---------------------------------------------------------------- g3
conv = {c: ST[c]["min_K1"]["ln_upper"] - ST[c]["min_K2"]["ln_upper"] for c in ORDER}
ok = all(0 <= conv[c] <= 0.2 for c in ORDER)
gate("g3 basis convergence: the K2 bound below the K1 bound by 0 to 0.2 nats (" + ", ".join(f"{conv[c]:.3f}" for c in ORDER) + ")", ok)

# ---------------------------------------------------------------- g4
gap = {c: ST[c]["ccm"]["ln_upper"] - ST[c]["min_K2"]["ln_upper"] for c in ORDER}
ok = all(-1e-6 <= gap[c] <= 0.5 and gap[c] >= 0.1 for c in ORDER)
for c in ORDER:
    tr = ST[c]["ccm_trial"]
    f0 = [float(x) for x in tr["fourier_check_psi0"]]; f4 = [float(x) for x in tr["fourier_check_psi4"]]
    ok &= abs(f0[0] - f0[1]) <= 1e-10*abs(f0[0]) and abs(f4[0] - f4[1]) <= 1e-10*abs(f4[0])
    ok &= tr["odd_part_max"] <= 1e-12*math.sqrt(float(tr["norm2"]))
    ok &= max(tr["coeff_tail"]) <= 1e-12
gate("g4 the CCM trial: certified quotient 0.1-0.5 nats above the minimiser (" + ", ".join(f"{gap[c]:.3f}" for c in ORDER)
     + "); prolate Fourier checks agree at two points to 1e-10; odd part <= 1e-12; coefficient tail <= 1e-12", ok)

# ---------------------------------------------------------------- g5
PT = run_T1(); even10 = PT.get("even:1", {})
mech = run_SM("two", "even")
up10 = float(ST["d1.0"]["min_K2"]["upper"]); up138 = float(ST["d1.38"]["min_K2"]["upper"])
ok = bool(even10) and even10.get("certified") and up10 >= even10["temple_lo"]
ok &= up138 >= mech["final"]
gate(f"g5 cross-checks: the delta = 1.0 upper bound {up10:.5e} >= 1bj's certified Temple {even10.get('temple_lo')}; "
     f"the delta = 1.3828125 upper bound {up138:.4e} >= 1bl's certified {mech['final']:.4e}", ok)

# ---------------------------------------------------------------- g6
import mpmath as mp
from flint import arb, ctx
zeros = [float(z) for z in json.load(open(os.path.join(HERE, "checkpoints", "zeta_zeros_6700.json")))]
mp.mp.dps = 40
ok = True; g6 = []
for delta, K, prec in ((1.0, 48, 400), (2.0, 80, 400)):
    a = delta/2
    bump = lambda t: mp.e**(-1/(1 - (t/a)**2)) if abs(t) < a else mp.mpf(0)
    c = [mp.quad(lambda t: bump(t)*mp.cos(k*mp.pi*t/a), [-a, 0, a])/(a if k else 2*a) for k in range(K)]
    G, N, pp = gram(delta, K, prec)
    qp = rayleigh(G, N, [arb(str(x)) for x in c], prec)
    den = sum((a if k else 2*a)*c[k]**2 for k in range(K))
    def ghat(r):
        s = mp.mpf(0)
        for k in range(K):
            w = k*mp.pi/a
            s += c[0]*2*mp.sin(r*a)/r if k == 0 else c[k]*(mp.sin((r+w)*a)/(r+w) + mp.sin((r-w)*a)/(r-w))
        return s
    qz = 2*sum(ghat(g)**2 for g in zeros)/den
    tail = 2*mp.quad(lambda r: ghat(r)**2*mp.log(r/(2*mp.pi))/(2*mp.pi), [zeros[-1], 2*zeros[-1], 10*zeros[-1], 100*zeros[-1]])/den
    rel = abs(float(qp.mid()) - float(qz + tail))/float(qz)
    g6.append(rel); ok &= rel <= 1e-13
gate("g6 the Gram LIVE against the zeros: a bump's cosine expansion at delta = 1 and 2, relative differences "
     + ", ".join(f"{r:.1e}" for r in g6) + " <= 1e-13", ok)

# ---------------------------------------------------------------- g7
mp.mp.dps = 30
Kk = lambda u: mp.e**(u/2)/mp.sinh(u)
ok = True; g7 = []
for delta in (1.5,):
    a = mp.mpf(delta)/2
    for om in (mp.mpf('4.1'), mp.mpf('12.3')):
        z = mp.mpc(0.25, om/2)
        # tails over [2a, inf) summed with the geometric series in m
        M = 400
        T0 = sum(2*mp.e**(-2*a*(2*m + 0.5))/(2*m + 0.5) for m in range(M))
        Tc = sum(2*mp.re(mp.e**(-(2*m + 0.5 - 1j*om)*2*a)/(2*m + 0.5 - 1j*om)) for m in range(M))
        Ts = sum(2*mp.im(mp.e**(-(2*m + 0.5 - 1j*om)*2*a)/(2*m + 0.5 - 1j*om)) for m in range(M))
        Tuc = sum(2*mp.re(mp.e**(-(2*m + 0.5 - 1j*om)*2*a)*(2*a/(2*m + 0.5 - 1j*om) + 1/(2*m + 0.5 - 1j*om)**2)) for m in range(M))
        S_cf = mp.im(mp.digamma(z)) - Ts
        C_cf = (mp.re(mp.digamma(z)) - mp.digamma(0.25)) - (T0 - Tc)
        U_cf = mp.re(mp.polygamma(1, z))/2 - Tuc
        S_q = mp.quad(lambda u: mp.sin(om*u)*Kk(u), mp.linspace(0, 2*a, 40))
        C_q = mp.quad(lambda u: (1 - mp.cos(om*u))*Kk(u), mp.linspace(0, 2*a, 40))
        U_q = mp.quad(lambda u: u*mp.cos(om*u)*Kk(u), mp.linspace(0, 2*a, 40))
        for x, y in ((S_cf, S_q), (C_cf, C_q), (U_cf, U_q)):
            g7.append(float(abs(x - y))); ok &= abs(x - y) <= 1e-12
gate("g7 the archimedean identities LIVE on [0, 2a] at delta = 1.5, omega = 4.1 and 12.3 (Im psi, Re psi - psi(1/4), Re psi'/2, minus "
     "geometric tails, against quadrature; max deviation " + f"{max(g7):.1e}" + " <= 1e-12)", ok)

# ---------------------------------------------------------------- g8
def lam_list(delta):
    out = []
    n = 2
    while mp.log(n) <= delta:
        m = n; p = None
        for q in range(2, int(n**0.5) + 1):
            if n % q == 0: p = q; break
        if p is None: p = n
        while m % p == 0: m //= p
        if m == 1: out.append(n)
        n += 1
    return out
ok = all(ST[c]["prime_powers"] == lam_list(ST[c]["delta"]) for c in ORDER)
gate("g8 the prime-power lists equal {n <= e^delta : Lambda(n) > 0} at every cell (" + ", ".join(str(len(ST[c]["prime_powers"])) for c in ORDER) + " entries)", ok)

# ---------------------------------------------------------------- g9
C_FUCHS = math.log(2**14/3*math.sqrt(2)*math.pi**5)
ok = True; below = {}; above = {}
for c in ORDER:
    v = ST[c]["ln_one_minus_chi2"]; d = ST[c]["delta"]
    ok &= abs(v[0] - v[1]) <= 1e-8*abs(v[0])
    below[c] = (C_FUCHS + 4.5*d - 4*math.pi*math.exp(d)) - v[0]
    above[c] = ST[c]["min_K2"]["ln_upper"] - v[0]
    ok &= 0.03 <= below[c] <= 0.6 and 1.5 <= above[c] <= 2.6
gate("g9 1 - chi_2 at the cells (Legendre cutoffs c + 300 and c + 500 agreeing to 1e-8): below the Fuchs law by " + ", ".join(f"{below[c]:.3f}" for c in ORDER)
     + " nats (in [0.03, 0.6]); the certified minimiser above it by " + ", ".join(f"{above[c]:.2f}" for c in ORDER) + " (in [1.5, 2.6])", ok)

# ---------------------------------------------------------------- g10
good = dict(ST["d2.0"]); prec = good["prec"]
bad1 = dict(good); bad1["min_K2"] = dict(good["min_K2"]); bad1["min_K2"]["positive"] = False
bad2 = dict(good); bad2["min_K2"] = dict(good["min_K2"]); bad2["min_K2"]["rad_log2"] = -10.0
bad3 = dict(good); bad3["ccm"] = dict(good["ccm"]); del bad3["ccm"]["upper"]
ok = ball_ok(good["min_K2"], prec) and not ball_ok(bad1["min_K2"], prec) and not ball_ok(bad2["min_K2"], prec) and not ball_ok(bad3["ccm"], prec)
gate("g10 mangle probes: the ball predicate fails on a non-positive lower end, an inflated radius, a missing field", ok)

# ---------------------------------------------------------------- g11
from cascade_tower import chain_ok
gate("g11 the chain obligation to cascade_slack_law.py (Theorem 1bm) met", chain_ok("cascade_slack_law.py"))

# ---------------------------------------------------------------- g12
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g12 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g12 the 1bn paper needles and the footer census (declared surface)", ok)

print(("\nALL GATES PASS (13/13)" if not fails else f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
