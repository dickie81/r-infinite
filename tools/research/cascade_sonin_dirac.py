#!/usr/bin/env python3
"""Theorem 1bd verifier: the archimedean comb -- the Connes-Moscovici
prolate operator carries the zeros' counting and none of their
fluctuations.

The operator (C-M, PNAS 119 (2022), arXiv:2112.05500; theorem
numbers below are the PNAS version's -- the arXiv version numbers
them Thm 2.6 / Cor 3.2 / Prop 4.2 / Thm 6.1): W_lam =
-d/dx (lam^2 - x^2) d/dx + (2 pi lam)^2 x^2 on J = [-lam, lam]'s
complement pairing, deficiency (4,4); its self-adjoint realization
W_sa commutes with both the space cutoff P_lam and the Fourier cutoff
(convention e^{-2 pi i x xi}; their Theorem 1.6), so the negative
spectrum lives in the SONIN SPACE S_lam = {f : f = 0 on J and
fhat = 0 on J} (their Corollary 2.2; round-222 F2 corrected the
landing's Theorem-1.6 tag on this conclusion). The per-parity
count of negative eigenvalues with -xi <= E^2 is 2 sigma(E, lam)
-- their Prop. 3.2 verbatim: "on even functions is the same as on
odd functions and is equal to 2 sigma(E, lam)"; round-222 F1
corrected the landing's "sigma" label (the code below always
implemented 2 sigma) -- with sigma(E, lam) ~ (E/2pi)(log(E/2pi)
- 1 + log 4 - 2 log lam) + lam^2, i.e. per-parity count of
s = 2E below s0: (s0/2pi)(log(s0/2pi) - 1 + log 2 - 2 log lam)
+ 2 lam^2 (the constant shifts by -log 2 in s-units), so at
lam = sqrt2 (2 log lam = log 2) EACH PARITY's count of s matches
the Riemann counting N(s) to its constant term.

The instrument (committed: tools/research/sonin_outside.py): basis
supported on the outside region [lam, X] only (f = 0 on J exact,
even/odd reflection), the Fourier-vanishing constraint imposed on a
xi-grid resolving the 1/X kernel period and cut at the Slepian knee
(rank ~ the Landau count 2 lam (X - lam); a machine-precision cut
over-constrains: truncated true eigenfunctions carry O(1/X) Fourier
residual on J from their universal sin/cos(2 pi lam x)/x tails);
W compressed onto the null basis by its quadratic form; negative
eigenvalues xi -> s = 2 sqrt(-xi). Compute is content-addressed
through tools/research/ckpt_key.py KEYED ON THE INSTRUMENT's bytes:
any edit to sonin_outside.py self-invalidates every checkpoint here,
while gate-pin edits to this verifier do not discard compute.
CASCADE_COMPUTE=fresh forces full recomputation (~20 min); cached
runs take seconds. Eigenvalues below s = 10 are excluded from every
census as the sub-cut class: at sqrt2 these are knee-leakage
entries (tol-wander ~2 vs the ladder's ~1, and all below the sqrt2
ladder's start >= 12 -- round-222 F5 softened the landing's
absolute wander dichotomy); at lam = 1 the same numeric cut
excludes one tol-STABLE mode at s ~ 8.0 (semiclassically expected
there; keeping it moves g7's difference 0.717 -> 0.736, in-window
either way -- round-222 F6: a disclosed uniform convention, not a
wander class).

Gates:
  g0  all pins set (a None pin prints its observed candidate, fails)
  g1  the zeros census: 102 zeros with gamma <= 240 (dps-13 pull)
  g2  the lam = sqrt2 counting identity: log 4 - 2 log sqrt2 = log 2
      (< 1e-12) and |N(240) - 102| < 1.2
  g3  Slepian-knee ranks: exact pins per config AND every rank
      within 25 of the Landau count 2 lam (X - lam)
  g4  per-parity counts of s in (10, 240]: exact pins; monotone
      non-decreasing in X at sqrt2; all <= the zeros' 102 over the
      measured configs (the X -> inf constant is open within O(1))
  g5  the rigid comb: unfolded increment sd in (0.004, 0.05) at
      every sqrt2 config vs the zeros' own (0.33, 0.37)
  g6  the decorrelation: |corr(instrument increments, zero
      increments)| < 0.06 per config and |mean| < 0.03
  g7  the constant law: c0 fits sit BELOW their targets (log 4 at
      lam = 1, log 2 at sqrt2; the truncation direction), and the
      matched-X difference c0(1) - c0(sqrt2) = log 2 +- 0.08
      (the -2 log lam law, truncation bias cancelled)
  g8  the dilation trend: every affine slope vs the zeros in
      (1.0, 1.05) and the endpoint shrink a(X=400) < a(X=120)
      (round-222 F4 synced this list to the code: the middle
      ordering is soft under shallow-end index wander)
  g9  the shallow end: the per-config MERGED shallowest ladder
      entry (the parities interlace) within 2.5 of gamma_1 =
      14.1347 at every sqrt2 config; the X = 120 odd first entry
      reproduces its pin +- 0.05 (round-222 F4 synced: the landing
      docstring's per-parity 1.6 window was never the coded gate
      and the shipped C config would fail it)
  g10 the chain obligation to cascade_fluctuation_price.py
      (Theorem 1bc) met (manifest or full mode)
  g11 the footer census (this script backticked >= 2; the anchored
      count and range needles) and the 1bd paper needles

Sabotage suite (run live at the landing battery; each probe edits,
runs, observes, restores):
  (a) instrument mangle -- sonin_outside.py even-parity Fourier
      kernel cos -> sin (hands the even sector the odd constraint)
      -> OBSERVED: all 8 ckpt keys changed, RECOMPUTING on all 8
      configs (self-invalidation live), g4 FAIL alone with the even
      counts becoming the odd sector's (A even 96 -> 97, D even
      123 -> 122; Landau ranks unchanged so g3 holds -- the count
      pins, not the rank pins, carry the detection), exit 1
  (b) pin mangle -- g4 count pin A-even 96 -> 95 -> OBSERVED:
      REUSED on all 8 (cached compute, seconds), g4 FAIL alone,
      exit 1
  (c) census revert -- footer 80 -> 79 -> OBSERVED: g10 FAIL (the
      manifest-mode chain gate prints the missing census string)
      AND g11 FAIL, exit 1 (two-gate detection)
"""
import math, os, sys

import numpy as np
from mpmath import mp, zetazero

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from sonin_outside import build            # the committed instrument
import ckpt_key


# declared paper surface (the needle-precheck arc, A397): the
# member touches the paper ONLY through these entries.
PAPER_NEEDLES = [
    {'g': 'g11', 's': 'Theorem 1bd (the archimedean comb', 'form': 'plain'},
    {'g': 'g11', 's': 'the Sonin space', 'form': 'plain'},
    {'g': 'g11', 's': 'carries the counting and none of the fluctuations', 'form': 'plain'},
    {'g': 'g11', 's': 'the Slepian knee', 'form': 'plain'},
    {'g': 'g11', 's': 'The rigid-comb verdict', 'form': 'plain'},
    {'g': 'g11', 's': '−2 log λ constant law', 'form': 'plain'},
    {'g': 'g11', 's': "each parity's counting matches the zeros' counting", 'form': 'plain'},
    {'s': '`cascade_sonin_dirac.py`', 'min': 2, 'g': 'g11'},
    {'s': 'the **86 scripts cited in place** above', 'form': 'ws', 'g': 'g11'},
    {'s': 'extended by Theorems 1i–1bj:', 'form': 'ws', 'g': 'g11'},
]
INSTRUMENT = os.path.join(HERE, "sonin_outside.py")

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

SQRT2 = math.sqrt(2)
LOG2 = math.log(2)
TOL = 3e-4
SMIN, SMAX = 10.0, 240.0

# configs: (tag, lam, K, X)
CONFIGS = [("A", SQRT2, 1600, 120.0), ("B", SQRT2, 2600, 200.0),
           ("C", SQRT2, 3200, 400.0), ("D", 1.0, 1300, 200.0)]

# ---- pins (from this verifier's own first fresh run) ----------------
PIN_RANK = {("A", "even"): 345, ("A", "odd"): 345,
            ("B", "even"): 572, ("B", "odd"): 572,
            ("C", "even"): 1138, ("C", "odd"): 1138,
            ("D", "even"): 407, ("D", "odd"): 407}
PIN_COUNT = {("A", "even"): 96, ("A", "odd"): 97,
             ("B", "even"): 98, ("B", "odd"): 98,
             ("C", "even"): 99, ("C", "odd"): 99,
             ("D", "even"): 123, ("D", "odd"): 122}
PIN_ODD_A_S1 = 13.226


def compute(tag, lam, K, X, parity):
    NJ = max(160, int(6*lam*X))
    NQ = max(1600, 4*K)
    params = {"lam": lam, "K": K, "X": X, "NJ": NJ, "NQ": NQ,
              "tol": TOL, "parity": parity}
    name = f"sonin_{tag}_{parity}"
    st = ckpt_key.load(name, INSTRUMENT, params)
    if st is None:
        dims, rank, s = build(lam, K, X, NJ, TOL, NQ, parity)
        st = {"dim": int(dims), "rank": int(rank),
              "s": [float(v) for v in s[:300]]}
        ckpt_key.save(name, INSTRUMENT, params, st)
    return st


def ladder(st):
    s = np.array(st["s"])
    return s[(s > SMIN) & (s <= SMAX)]


def c0_fit(s, lam):
    E = s/2.0
    n = np.arange(1, len(s) + 1) - 0.5
    base = E/math.pi*(np.log(E/(2*math.pi)) - 1) + 2*lam*lam
    return float(np.sum((n - base)*E/math.pi)/np.sum((E/math.pi)**2))


def inc_sd(s, lam):
    E = s/2.0
    c0 = LOG2 if abs(lam - SQRT2) < 1e-9 else math.log(4)
    u = E/math.pi*(np.log(E/(2*math.pi)) - 1 + c0) + 2*lam*lam
    return np.diff(u) - 1


# ---- compute all eight ----------------------------------------------
res = {}
for tag, lam, K, X in CONFIGS:
    for parity in ("even", "odd"):
        res[(tag, parity)] = compute(tag, lam, K, X, parity)
        print(f"  [{tag} {parity}] rank {res[(tag, parity)]['rank']}, "
              f"count(10,240] {len(ladder(res[(tag, parity)]))}", flush=True)

# ---------------------------------------------------------------- g0
gate("g0 all pins set", all(v is not None for v in
     list(PIN_RANK.values()) + list(PIN_COUNT.values()) + [PIN_ODD_A_S1]))

# ---------------------------------------------------------------- g1
mp.dps = 13
Zg = []
k = 1
while True:
    z = float(zetazero(k).imag)
    if z > SMAX:
        break
    Zg.append(z)
    k += 1
Zg = np.array(Zg)
gate("g1 the zeros census: 102 zeros below 240", len(Zg) == 102)

# ---------------------------------------------------------------- g2
ok = abs(math.log(4) - 2*math.log(SQRT2) - LOG2) < 1e-12
Nsm = 240/(2*math.pi)*(math.log(240/(2*math.pi)) - 1) + 7.0/8
ok &= abs(Nsm - 102) < 1.2
gate("g2 the sqrt2 counting identity (log4 - 2 log sqrt2 = log2; "
     "N(240) ~ 102)", ok)

# ---------------------------------------------------------------- g3
ok = True
for tag, lam, K, X in CONFIGS:
    landau = 2*lam*(X - lam)
    for parity in ("even", "odd"):
        r = res[(tag, parity)]["rank"]
        if PIN_RANK[(tag, parity)] != r:
            print(f"  g3 rank pin miss [{tag} {parity}]: observed {r}",
                  flush=True)
            ok = False
        if abs(r - landau) > 25:
            print(f"  g3 Landau miss [{tag} {parity}]: rank {r} vs "
                  f"2 lam (X-lam) = {landau:.1f}", flush=True)
            ok = False
gate("g3 Slepian-knee ranks: pins exact, all within 25 of the Landau "
     "count", ok)

# ---------------------------------------------------------------- g4
ok = True
for key_, pin in PIN_COUNT.items():
    c = len(ladder(res[key_]))
    if c != pin:
        print(f"  g4 count pin miss [{key_}]: observed {c}", flush=True)
        ok = False
for parity in ("even", "odd"):
    seq = [len(ladder(res[(t, parity)])) for t in ("A", "B", "C")]
    ok &= seq[0] <= seq[1] <= seq[2] <= 102
gate("g4 per-parity counts in (10, 240]: pins exact, monotone in X at "
     "sqrt2, <= the zeros' 102 over the measured configs (the X -> inf "
     "constant is open within O(1), round-222 F9)", ok)

# ---------------------------------------------------------------- g5
gN = Zg/(2*math.pi)*np.log(Zg/(2*math.pi)) - Zg/(2*math.pi) + 7.0/8
gi = np.diff(gN) - 1
ok = 0.33 < np.std(gi) < 0.37
for tag in ("A", "B", "C"):
    for parity in ("even", "odd"):
        sd = float(np.std(inc_sd(ladder(res[(tag, parity)]), SQRT2)))
        if not (0.004 < sd < 0.05):
            print(f"  g5 inc-sd miss [{tag} {parity}]: {sd:.4f}", flush=True)
            ok = False
gate("g5 the rigid comb: instrument increment sd in (0.004, 0.05) at "
     "every sqrt2 config; the zeros' own 0.33-0.37", ok)

# ---------------------------------------------------------------- g6
ok = True
cs = []
for tag in ("A", "B", "C"):
    for parity in ("even", "odd"):
        inc = inc_sd(ladder(res[(tag, parity)]), SQRT2)
        m = min(len(inc), len(gi))
        c = float(np.corrcoef(inc[:m], gi[:m])[0, 1])
        cs.append(c)
        if abs(c) >= 0.06:
            print(f"  g6 corr miss [{tag} {parity}]: {c:+.4f}", flush=True)
            ok = False
ok &= abs(float(np.mean(cs))) < 0.03
print(f"  g6 per-config corr: {[f'{c:+.4f}' for c in cs]}; "
      f"mean {np.mean(cs):+.4f}", flush=True)
gate("g6 the decorrelation: |corr| < 0.06 per config, |mean| < 0.03", ok)

# ---------------------------------------------------------------- g7
c0_s2 = np.mean([c0_fit(ladder(res[("B", p)]), SQRT2)
                 for p in ("even", "odd")])
c0_1 = np.mean([c0_fit(ladder(res[("D", p)]), 1.0)
                for p in ("even", "odd")])
d = c0_1 - c0_s2
print(f"  g7 c0(sqrt2, X=200) = {c0_s2:.4f} (target log2 = {LOG2:.4f}); "
      f"c0(1, X=200) = {c0_1:.4f} (target log4 = {math.log(4):.4f}); "
      f"difference {d:.4f}", flush=True)
ok = (c0_s2 < LOG2) and (c0_1 < math.log(4)) and abs(d - LOG2) < 0.08
gate("g7 the constant law: both c0 below target (truncation direction); "
     "matched-X difference = log2 +- 0.08 (the -2 log lam law)", ok)

# ---------------------------------------------------------------- g8
slopes = []
for tag in ("A", "B", "C"):
    s = ladder(res[(tag, "odd")])
    m = min(len(s), len(Zg))
    a, b = np.polyfit(Zg[:m], s[:m], 1)
    slopes.append(float(a))
print(f"  g8 dilation slopes (odd, X=120/200/400): "
      f"{[f'{a:.4f}' for a in slopes]}", flush=True)
gate("g8 the dilation trend: every slope in (1.0, 1.05), endpoint "
     "shrink a(400) < a(120) (shallow-end index wander makes the "
     "middle ordering soft; the endpoints and the >1 floor are the "
     "trend)", all(1.0 < a < 1.05 for a in slopes)
     and slopes[2] < slopes[0])

# ---------------------------------------------------------------- g9
ok = True
for tag in ("A", "B", "C"):
    s1 = min(float(ladder(res[(tag, p)])[0]) for p in ("even", "odd"))
    print(f"  g9 [{tag}] merged shallowest ladder entry {s1:.3f}", flush=True)
    if abs(s1 - 14.1347) > 2.5:
        ok = False
sA = float(ladder(res[("A", "odd")])[0])
ok &= abs(sA - PIN_ODD_A_S1) < 0.05
print(f"  g9 X=120 odd s1 = {sA:.3f} (pin {PIN_ODD_A_S1})", flush=True)
gate("g9 the shallow end lands on the zeros' region (the parities "
     "interlace, so the per-config MERGED shallowest ladder entry is "
     "the gamma_1 analogue: within 2.5 of gamma_1 at every sqrt2 "
     "config; the X=120 odd pin +- 0.05)", ok)

# ---------------------------------------------------------------- g10
from cascade_tower import chain_ok
gate("g10 the chain obligation to cascade_fluctuation_price.py "
     "(Theorem 1bc) met", chain_ok("cascade_fluctuation_price.py"))

# ---------------------------------------------------------------- g11
import re
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d, _n in _miss:
    print(f"  g11 MISSING (count {_n}): {_d['s']!r}", flush=True)
gate("g11 the 1bd paper needles and the footer census "
     "(backticked >= 2; the anchored count and range needles) "
     "(declared surface)", ok)

print(("\nALL GATES PASS (12/12)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
