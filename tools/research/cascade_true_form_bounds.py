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
bounds (rounded outward) at or above the stored upper ends and within
2e-3 (round-298 F298-1); the bold line and the seven table rows declared
as needles and parsed back against the pins, the cells' parameters and
the stored model / 1 - chi_2 values (round-300 F300-2), the parsed copies
tied to the declared entries (round-301 F301-1); clause (v)'s values
likewise declared, parsed and pinned directionally in g5 (F301-2). (2) AGREEMENT WITH THE ZERO SIDE: the certified
upper bound (K2) sits within 0.15 nats of Theorem 1bm's model value at
every cell (the two are the same eigenvalue under RH; the model is
truncated, the certificate is not). (3) BASIS CONVERGENCE: K2 <= K1 and
the change <= 0.2 nats. (4) THE CCM TRIAL: its certified quotient is
within [0.1, 0.6] nats above the minimiser's (same subspace); its build
diagnostics: the finite-Fourier checks of psi_0 and psi_4 agreeing at
two points to 1e-10; the odd part of k_lambda at most 30 times the
Poisson defect sqrt(1 - chi_2) ||k_lambda|| (observed 3.7-10.6 times);
the cosine tail at most 5 percent of the odd part (observed 0.47-1.79 percent). (5) CROSS-CHECKS: the delta = 1.0 upper bound >=
Theorem 1bj's certified Temple lower bound (loaded at its key) and the
delta = 1.3828125 upper bound >= Theorem 1bl's certified even bound -- an
upper bound on the true lambda_1 must exceed any certified lower bound;
clause (v)'s two sentences as declared needles, parsed and pinned
directionally (F301-2), the enclosure at its parsed exponent with
tolerances on both sides (F302-1), a missing or reformatted enclosure a
gate failure rather than a traceback (F303-2).
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
    # the block's numeric claims (round-300 F300-2): the bold line and the seven table rows, as literals that g1
    # parses back against the pins and the stored model / 1 - chi_2 values
    {'g': 'g1', 's': '−ln λ₁(δ) ≥ 13.88, 27.75, 67.23, 98.26, 140.71, 221.89, 383.28', 'form': 'plain'},
    {'g': 'g1', 's': '| 1.0 | 1 | 70/120 | −13.882 | −13.878 | −13.884 | −13.669 | −15.522 |', 'form': 'ws'},
    {'g': 'g1', 's': '| 1.3828125 | 2 | 80/140 | −27.754 | −27.722 | −27.765 | −27.588 | −29.540 |', 'form': 'ws'},
    {'g': 'g1', 's': '| 2.0 | 5 | 100/160 | −67.233 | −67.205 | −67.332 | −66.890 | −69.357 |', 'form': 'ws'},
    {'g': 'g1', 's': '| 2.3 | 7 | 170/260 | −98.267 | −98.234 | −98.330 | −97.880 | −100.445 |', 'form': 'ws'},
    {'g': 'g1', 's': '| 2.6 | 9 | 220/320 | −140.713 | −140.672 | −140.777 | −140.287 | −142.911 |', 'form': 'ws'},
    {'g': 'g1', 's': '| 3.0 | 12 | 280/400 | −221.899 | −221.819 | −221.942 | −221.488 | −224.291 |', 'form': 'ws'},
    {'g': 'g1', 's': '| 3.5 | 18 | 420/540 | −383.282 | −383.176 | −383.219 | −382.799 | −385.754 |', 'form': 'ws'},
    # clause (v)'s certified values (round-301 F301-2), parsed back by g5
    {'g': 'g5', 's': "The δ = 1.0 bound 9.3524×10⁻⁷ exceeds Theorem 1bj's certified Temple lower bound 2.6832×10⁻⁷ and lies inside 1bj's trial enclosure [9.2494, 9.4548]×10⁻⁷", 'form': 'ws'},
    {'g': 'g5', 's': "the δ = 1.3828125 bound 8.8392×10⁻¹³ exceeds Theorem 1bl's certified 5.7134×10⁻¹³ (as 1bl states it)", 'form': 'ws'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ORDER = ["d1.0", "d1.38", "d2.0", "d2.3", "d2.6", "d3.0", "d3.5"]
ST = {c: run_TF(c) for c in ORDER}
# the paper's stated certified upper bounds (ln), K2 minimiser -- PINS
PINS = {"d1.0": -13.882, "d1.38": -27.754, "d2.0": -67.233, "d2.3": -98.267, "d2.6": -140.713, "d3.0": -221.899, "d3.5": -383.282}
CCM_PINS = {"d1.0": -13.669, "d1.38": -27.588, "d2.0": -66.890, "d2.3": -97.880, "d2.6": -140.287, "d3.0": -221.488, "d3.5": -382.799}
K1_PINS = {"d1.0": -13.878, "d1.38": -27.722, "d2.0": -67.205, "d2.3": -98.234, "d2.6": -140.672, "d3.0": -221.819, "d3.5": -383.176}

def ball_ok(b, prec):
    return (all(k in b for k in ("mid", "rad_log2", "upper", "ln_upper", "positive")) and b["positive"]
            and b["ln_upper"] is not None and b["rad_log2"] is not None and b["rad_log2"] <= -prec/2)

# ---------------------------------------------------------------- g0
ok = all(st["verdict"].startswith("CERTIFIED") for st in ST.values())
ok &= all(ball_ok(st[k], st["prec"]) for st in ST.values() for k in ("min_K1", "min_K2", "ccm"))
ok &= all(st["cell"] == c and abs(st["delta"] - CELLS[c]["delta"]) < 1e-12 for c, st in ST.items())
gate("g0 the seven certificates load at their keys: three positive Rayleigh balls per cell with radii below 2^(-prec/2)", ok)

# ---------------------------------------------------------------- g1
# the paper's stated bounds are rounded OUTWARD (round-298 F298-1): each pin must be >= the stored ln upper
# (a valid, weaker statement) and within 2e-3 of it
ok = all(PINS[c] is not None and 0 <= PINS[c] - ST[c]["min_K2"]["ln_upper"] <= 2e-3 for c in ORDER)
ok &= all(CCM_PINS[c] is not None and 0 <= CCM_PINS[c] - ST[c]["ccm"]["ln_upper"] <= 2e-3 for c in ORDER)
ok &= all(K1_PINS[c] is not None and 0 <= K1_PINS[c] - ST[c]["min_K1"]["ln_upper"] <= 2e-3 for c in ORDER)   # round-299 F299-3
# round-300 F300-2: the paper's own numbers -- the bold line and the seven table rows are declared needles (g12 checks
# their presence in the paper); here the literals are parsed and tied to the pins and to the stored model / 1 - chi_2
# (the literals below are the same strings as the g1 entries of PAPER_NEEDLES; paper_needles.needle raises KeyError
# for an undeclared (s, form), so each parsed literal is proved declared AND present in the paper -- the declared
# list itself is read only through verify/needle, per the precheck's clause C)
import paper_needles
BOLD_CLAIM = '−ln λ₁(δ) ≥ 13.88, 27.75, 67.23, 98.26, 140.71, 221.89, 383.28'
ROW_CLAIMS = ['| 1.0 | 1 | 70/120 | −13.882 | −13.878 | −13.884 | −13.669 | −15.522 |',
              '| 1.3828125 | 2 | 80/140 | −27.754 | −27.722 | −27.765 | −27.588 | −29.540 |',
              '| 2.0 | 5 | 100/160 | −67.233 | −67.205 | −67.332 | −66.890 | −69.357 |',
              '| 2.3 | 7 | 170/260 | −98.267 | −98.234 | −98.330 | −97.880 | −100.445 |',
              '| 2.6 | 9 | 220/320 | −140.713 | −140.672 | −140.777 | −140.287 | −142.911 |',
              '| 3.0 | 12 | 280/400 | −221.899 | −221.819 | −221.942 | −221.488 | −224.291 |',
              '| 3.5 | 18 | 420/540 | −383.282 | −383.176 | −383.219 | −382.799 | −385.754 |']
# each call carries its literal (the precheck's clause D); the strings equal BOLD_CLAIM / ROW_CLAIMS above by construction
ok &= paper_needles.needle(PAPER_NEEDLES, '−ln λ₁(δ) ≥ 13.88, 27.75, 67.23, 98.26, 140.71, 221.89, 383.28', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 1.0 | 1 | 70/120 | −13.882 | −13.878 | −13.884 | −13.669 | −15.522 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 1.3828125 | 2 | 80/140 | −27.754 | −27.722 | −27.765 | −27.588 | −29.540 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 2.0 | 5 | 100/160 | −67.233 | −67.205 | −67.332 | −66.890 | −69.357 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 2.3 | 7 | 170/260 | −98.267 | −98.234 | −98.330 | −97.880 | −100.445 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 2.6 | 9 | 220/320 | −140.713 | −140.672 | −140.777 | −140.287 | −142.911 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 3.0 | 12 | 280/400 | −221.899 | −221.819 | −221.942 | −221.488 | −224.291 |', 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, '| 3.5 | 18 | 420/540 | −383.282 | −383.176 | −383.219 | −382.799 | −385.754 |', 'ws')
# round-301 F301-1: the parsed copies tied to the declared entries (the declared list read through the API)
_lits = [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g1']
ok &= _lits == [BOLD_CLAIM] + ROW_CLAIMS and len(set(_lits)) == 8
_bvals = [float(x) for x in BOLD_CLAIM.split('≥')[1].replace('−', '-').split(',')]
ok &= len(ROW_CLAIMS) == 7 and len(_bvals) == 7
for c, row, bv in zip(ORDER, ROW_CLAIMS, _bvals):
    f = [x.strip().replace('−', '-') for x in row.strip('|').split('|')]
    ok &= abs(float(f[0]) - ST[c]["delta"]) < 1e-9 and int(f[1]) == len(ST[c]["prime_powers"]) and f[2] == f"{CELLS[c]['K1']}/{CELLS[c]['K2']}"
    ok &= float(f[3]) == PINS[c] and float(f[4]) == K1_PINS[c] and float(f[6]) == CCM_PINS[c]
    ok &= abs(float(f[5]) - round(run_SL(c)["ln_eig"], 3)) < 1e-9 and abs(float(f[7]) - round(ST[c]["ln_one_minus_chi2"][0], 3)) < 1e-9
    ok &= 0 <= -ST[c]["min_K2"]["ln_upper"] - bv <= 1e-2 + 1e-9        # the bold value is the floor to 1e-2 of -ln upper
gate("g1 the pins and the paper's own numbers: the stated ln upper bounds (minimiser K2, the CCM trial, and the K1 column) at or above the stored upper ends and within 2e-3; the bold line and the seven table rows present as declared needles, parsed back (delta, prime-power count, K1/K2, the three pinned columns, the model and 1 - chi_2 columns to 1e-3, the bold floors) ("
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
ok = all(0.1 <= gap[c] <= 0.6 for c in ORDER)
for c in ORDER:
    tr = ST[c]["ccm_trial"]
    f0 = [float(x) for x in tr["fourier_check_psi0"]]; f4 = [float(x) for x in tr["fourier_check_psi4"]]
    ok &= abs(f0[0] - f0[1]) <= 1e-10*abs(f0[0]) and abs(f4[0] - f4[1]) <= 1e-10*abs(f4[0])
    # the odd part of k_lambda and its cosine tail are the Poisson defect of the truncated prolates, of size
    # sqrt(1 - chi_2) times the norm (observed 3.7-10.6x); gated at 30x, the tail at 5 percent of the odd part
    sq = math.exp(ST[c]["ln_one_minus_chi2"][0]/2)*math.sqrt(float(tr["norm2"]))
    ok &= tr["odd_part_max"] <= 30*sq
    ok &= max(tr["coeff_tail"]) <= 0.05*tr["odd_part_max"]
gate("g4 the CCM trial: certified quotient 0.1-0.6 nats above the minimiser (" + ", ".join(f"{gap[c]:.3f}" for c in ORDER)
     + "); prolate Fourier checks agree at two points to 1e-10; the odd part <= 30 sqrt(1 - chi_2) ||k|| (the Poisson defect) "
     "and the coefficient tail <= 5 percent of it", ok)

# ---------------------------------------------------------------- g5
PT = run_T1(); even10 = PT.get("even:1", {})
mech = run_SM("two", "even")
up10 = float(ST["d1.0"]["min_K2"]["upper"]); up138 = float(ST["d1.38"]["min_K2"]["upper"])
ok = bool(even10) and even10.get("certified") and up10 >= even10["temple_lo"]
ok &= up138 >= mech["final"]
# round-301 F301-2: clause (v)'s stated values, declared as needles, parsed back and pinned directionally
V1 = "The δ = 1.0 bound 9.3524×10⁻⁷ exceeds Theorem 1bj's certified Temple lower bound 2.6832×10⁻⁷ and lies inside 1bj's trial enclosure [9.2494, 9.4548]×10⁻⁷"
V2 = "the δ = 1.3828125 bound 8.8392×10⁻¹³ exceeds Theorem 1bl's certified 5.7134×10⁻¹³ (as 1bl states it)"
ok &= paper_needles.needle(PAPER_NEEDLES, "The δ = 1.0 bound 9.3524×10⁻⁷ exceeds Theorem 1bj's certified Temple lower bound 2.6832×10⁻⁷ and lies inside 1bj's trial enclosure [9.2494, 9.4548]×10⁻⁷", 'ws')
ok &= paper_needles.needle(PAPER_NEEDLES, "the δ = 1.3828125 bound 8.8392×10⁻¹³ exceeds Theorem 1bl's certified 5.7134×10⁻¹³ (as 1bl states it)", 'ws')
ok &= [d['s'] for d in paper_needles.declared(PAPER_NEEDLES) if d.get('g') == 'g5'] == [V1, V2]
import re as _re
_sup = str.maketrans('⁻⁰¹²³⁴⁵⁶⁷⁸⁹', '-0123456789')
def _nums(t):   # every a×10^b in the literal, in order
    return [float(m.group(1))*10**int(m.group(2).translate(_sup)) for m in _re.finditer(r'([0-9.]+)×10([⁻⁰¹²³⁴⁵⁶⁷⁸⁹]+)', t.replace('[', '').replace(']', ''))]
v1 = _nums(V1); v2 = _nums(V2)
# V1: the bound (an upper bound: stated >= stored, within 1e-4), 1bj's Temple (stated <= loaded), the enclosure ends outward of rho
ok &= len(v1) == 3 and 0 <= v1[0] - up10 <= 1e-4*up10 and v1[1] <= even10["temple_lo"] <= v1[1]*(1 + 1e-4)
# the enclosure: both ends scaled by the PARSED exponent (round-302 F302-1: the scale was hardcoded and the outward side
# untoleranced), outward of the stored rho within 1e-4 relative, containing the delta = 1.0 upper bound. A missing or
# reformatted enclosure fails the gate rather than raising (round-303 F303-2); the former tie of v1[2] to _rhi was a
# conjunct that could not fail on its own (F303-1: given the three conjuncts above, v1[2] IS the same parse) and is dropped.
_m = _re.search(r'\[([0-9.]+), ([0-9.]+)\]×10([⁻⁰¹²³⁴⁵⁶⁷⁸⁹]+)', V1)
ok &= _m is not None
if _m is not None:
    _sc = 10**int(_m.group(3).translate(_sup)); _rlo = float(_m.group(1))*_sc; _rhi = float(_m.group(2))*_sc
    ok &= _rlo <= even10["rho"][0] <= _rlo*(1 + 1e-4) and _rhi*(1 - 1e-4) <= even10["rho"][1] <= _rhi and _rlo <= up10 <= _rhi
ok &= len(v2) == 2 and 0 <= v2[0] - up138 <= 1e-4*up138 and v2[1] <= mech["final"] <= v2[1]*(1 + 1e-4)
gate(f"g5 cross-checks: the delta = 1.0 upper bound {up10:.7e} >= 1bj's certified Temple {even10.get('temple_lo')}; "
     f"the delta = 1.3828125 upper bound {up138:.7e} >= 1bl's certified {mech['final']:.7e}; clause (v)'s two sentences present "
     "as declared needles, tied to the declared entries and parsed: the stated upper bounds >= the stored uppers within 1e-4, the "
     "quoted 1bj/1bl bounds <= the loaded certificates within 1e-4, the enclosure (both ends at the parsed exponent) outward of "
     "the stored rho within 1e-4 and containing the delta = 1.0 upper bound", ok)

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
