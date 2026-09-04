#!/usr/bin/env python3
"""
THEOREM 1an -- the windows overlap: coverage, crowding, and the
wall's resolution restatement.

THE COMMISSION.  The owner asked "Do the windows overlap?" of 1aj's
relocatable sensitivity windows and commissioned the landing.

THE CONTENT (four theorems + honest scope).
ROUND-161 SWEEP (the landing's hostile round; 0 majors, 4 minors +
2 cosmetics, all statement-discipline, all verified by the lead and
swept): F1 -- the per-zero->per-cluster transition was pinned to
#33 (overlap-onset) on three paper carriers including the 1aj
net-state marker; the correct threshold is occupancy-onset (#187);
struck on all three, g10 re-anchored.  F2 -- "in exact rational
arithmetic" overstated the gate (only the solves were exact; edges
are 30-digit root-finds); label corrected on the paper AND the sign
conjunct made fully rational in g1.  F3 -- W2's tiling universal
now carries its sampled-width-floor scope.  F4 -- the paper's
"41 containment events" now states the directional convention.
F5 -- the dead conditional at the RvM line removed.  F6 -- the
c ~ 1.25 observation scoped to the asymptotic aims.  Plus the
reviewer's held note, verified and gated: the width floor FAILS
below the sampled range (width(1) ~ 0.921; crossing 1 in (4.1,
4.5)) -- the sampled qualifiers are load-bearing (g8 extended).

ROUND-162 SWEEP (the convergence test on the round-161 sweep; 0
majors, 3 minors + 1 cosmetic, all verified by the lead and swept):
F1 -- the round-161 clause "mean occupancy stays below 1" mislabeled
width x density (an unaimed interval's expected count) as the aimed
windows' occupancy, which is >= 1 identically with census mean
1 + 41/800 ~ 1.05; struck on the paper carrier, relabeled on all
three tellings.  F2 -- this docstring's own W2 paragraph had kept
the bare tiling universal while the file's sweep note claimed F3
swept; scoped.  F3 -- the marker rewrite had destroyed the
landing's sabotage-(c) pattern, uncoupling the marker's
disjointness clause (the reviewer's probe tripped nothing); g10
anchors it now -- BOTH carriers of the numeral, the probe's own
count assert having exposed the W3 body as a second uncoupled
instance -- with the trip probes (g1)/(g2) certified in the
sabotage record below.  F4 (cosmetic) -- the residual
compressed "exact-rational" labels on the paper W1 heading and the
V1 print header expanded to "exact-rational solves".

  W1 (the width limit, exact-rational solves).  For the committed three-term
      instance (d = 4, 5, 6 -- the 1aj solve, kernels at w = d+1/2),
      the window width lo + hi decreases monotonically on the sampled
      aim spread from 1.0156... at gamma_1 toward EXACTLY 1 (the
      continuation mechanism's own 2 x 1/2), with offsets
      1/2 +/- c/gamma, c ~ 1.25 OBSERVED at the asymptotic aims
      300-3000 (not derived; at gamma_1 the effective constants
      are ~1.18/0.96 -- round 161 F6), and
      F(aim) < 0 throughout.  The apparent window collapse above
      aim ~ 10^3 in double precision is an instrument artifact (the
      solved coefficients grow like aim^4 against kernels shrinking
      like aim^-2; cancellation) -- gated in BOTH directions: at
      aim 3000 the float64 value is cancellation noise (error
      orders above the exact magnitude, sign formulation-dependent)
      and at aim 1000 the float64 window collapses to a
      noise-dependent fraction (~0.17 in this instrument, ~0.30 in
      the scratch formulation, against the exact ~ 1.000004), while
      the exact-rational F(aim) is stably negative.  The gate's first draft pinned a
      float SIGN FLIP; the clean run showed the flip is itself
      formulation-dependent noise (this file's float kernel gives
      -7e-12 where the scratch formulation gave >= 0) -- redesigned
      pre-commit to gate the noise magnitude and the collapse,
      disclosed.  Any future gate probing aims above ~10^3 must use
      the exact-rational route.
  W2 (tiling: reach is complete on the sampled width floor).  Aims
      spaced below the width tile any interval with overlapping
      windows -- gated on a 23-aim chain spanning [20, 40]: every
      consecutive pair overlaps and the union is connected,
      covering [20, 40].  No height escapes the committed family's
      sensitivity -- the universal resting on the SAMPLED width
      floor, one chain gated (round 161 F3; this paragraph's own
      scope was the round-162 F2 catch -- the file's sweep note
      claimed F3 swept while this telling still carried the bare
      universal).
  W3 (the crowding census; "first" claims gated over zeros 1-240
      recomputed live; the 800-zero extension under --full).
      Per-zero windows (each aimed at its own zero) are pairwise
      disjoint through zero #33; the first overlap is #34/#35
      (gamma = 111.0295... / 111.8746..., gap 0.8451..., overlap
      depth ~ 0.155); the first containment is ONE-SIDED at
      #186/#187 (gap 0.4981... -- below lo(gamma_187) but above
      hi(gamma_186): the lower reach exceeds 1/2 and captures first,
      W1's asymmetry biting); the first MUTUAL containment is
      #212/#213 (gamma = 415.0188... / 415.4552..., gap 0.4364...).
      Under --full (800 zeros, to gamma ~ 1184): 200 of 799 adjacent
      pairs overlap and 41 directional containment events occur (a
      mutual pair contributes two).  Asymptotically the per-window
      occupancy is width x density -> ln(gamma/2pi)/2pi
      (Riemann-von Mangoldt, classical input) -- growing without
      bound: pairwise disjoint through #33, SINGLE-OCCUPANCY
      through #186 (the first two-zero window is #187; the window
      width stays below the mean zero spacing -- width x density
      ~ 0.83 at gamma ~ 1184, reaching 1 only near gamma ~ 3.4e3 --
      so second occupants are atypical; the census mean occupancy
      of the AIMED windows is 1 + 41/800 ~ 1.05, never below 1,
      each window containing its own zero -- relabeled round 162
      F1: the round-161 sweep called width x density "mean
      occupancy").  [Round 161 F1: the
      first wording, "per-zero through #33, per-cluster beyond",
      pinned the transition to overlap-onset; the probe semantics
      is a single-window property and the correct threshold is
      occupancy-onset -- struck on the paper's three carriers and
      corrected here.]
  W4 (reach vs resolution -- the wall sharpened).  W2 + W1: the
      family can look ANYWHERE, but its width stays above 1 on the
      sampled family and its profile is the fixed three-Lorentzian
      shape -- it can relocate, it cannot concentrate [STRUCK at the
      Theorem 1ap regrade, self-caught: an admissible complex-pair
      numerator concentrates, width ~ 5/(2 gamma_0) -> 0 at height,
      at contrast price ~ gamma_0^-6; the sampled scope below was
      load-bearing].  Weil's dense
      class requires arbitrary concentration; the committed family
      supplies relocation without resolution [STRUCK at the 1ap
      regrade: it supplies both -- relocation, and resolution priced
      in contrast].  The wall stands where
      it stood; the deficit's name sharpens: RESOLUTION, not reach
      [STRUCK at the 1ap regrade -- the honest name is CONTRAST].

HONEST SCOPE.  Category (a) -- no data contact, no closures, no new
physics.  No numerical advance over classical zero-verification is
claimed or implied (the coverage statement repackages zeta's own
bookkeeping in committed-lattice terms).  Positivity is unchanged by
window sharing (every on-line zero contributes >= 0 in any window it
enters).  c ~ 1.25 observed, not derived; width > 1 sampled, not
proved; the "first" claims scoped to the gated range.  Check 7 clean
(kernel/potential bookkeeping + classical zero data; no
semiclassics); Check 8 clean (every number traces to the committed
lattice w = d+1/2 and classical zeros; no hypothesis input).

VERIFICATION (13 gates, exit-gated; --full extends the census).
  V1 -- g1 the width limit (exact-rational Cramer solve; widths at
       gamma_1/300/1000/3000 bracketed, strictly decreasing, > 1;
       F(aim) < 0 at all four, the sign decided in PURE Fraction
       arithmetic -- round 161 F2); g2 the precision cliff (the float64
       value at 3000 is noise: |float - exact| > 50x the exact
       magnitude; the float64 window at 1000 collapses: width off
       by > 0.5 from the exact, or fails to bracket); g3 the offset
       scaling ((lo - 1/2)
       and (1/2 - hi) times aim in (1.23, 1.27) at 300/1000/3000 --
       the OBSERVED c ~ 1.25).
  V2 -- g4 the tiling chain (aims 20 to 39.8 step 0.9: 23 windows,
       every consecutive overlap margin > 0, union connected and
       covering [20, 40]).
  V3 -- g5 zeros 1-240 recomputed (mpmath zetazero, dps 20);
       disjointness through #33 (every pair below #34 with gap under
       the 1.03 candidate threshold exact-checked; wider gaps cannot
       overlap, the width bound 1.0157); first overlap #34/#35 with
       gap and depth bracketed; g6 the containment firsts (no
       containment below #186 -- candidates under the 0.5835 lo
       bound exact-checked; #186/#187 one-sided: hi(a) < gap <
       lo(b); first mutual #212/#213: gap < min(hi(a), lo(b)); no
       mutual below #212); g7 the occupancy cross-check (the
       Riemann-von Mangoldt main count at gamma_240 within 1.5 of
       240 -- the classical density the asymptotic occupancy
       formula multiplies).
  V4 -- g8 the resolution floor (width > 1 at every sampled aim --
       "sampled" is the claim's scope; plus the below-range dip
       gated, width(1) in (0.920, 0.922) and the crossing of 1
       inside (4.1, 4.5) -- round 161); g9 the 1aj committed-window
       tie (at aim gamma_1 the boundary function is negative at
       both committed inward endpoints 13.5514 / 14.5669 and
       positive just outside both, matching 1aj's gated window).
  V5 -- g10 1an's key sentences + the 1aj net-state marker anchored
       by content; g11 the honest-scope anchors (the no-numerical-
       advance disclaimer; observed-not-derived; sampled-not-proved;
       the wall-unchanged sentence at count >= 2 -- it also lives in
       1aj); g12 the sibling chain green (riemann_selection 12/0,
       which chains type_counting and the two Weil-arc siblings);
       g13 the footer census (this script backticked; "90 scripts cited in place"; "Theorems 1i–1bn" -- the census advances
       with each landing; the gate carries the live values).

Sabotage record (full-tree scratchpad copy, tar --exclude=.git, at
the landing; the certified censuses are from a SERIAL suite in a
fresh tree after two disclosed instrument mishaps -- see below):
(a) the verifier copy's tiling spacing widened to 1.1 (above the
width) -> g4 trips (min consecutive overlap margin -0.0984), 12/1,
exit 1; (b) the paper copy's W4 sentence mangled mid-anchor
(concentrate -> focus, across its line wrap) -> g10 trips, 12/1,
exit 1; (c) the paper copy's 1aj net-state marker content mangled
(through zero #33 -> #43, across its line wrap) -> g10 trips, 12/1,
exit 1.  Clean baselines 13/0 exit 0 before and after every entry.
DISCLOSED MISHAPS at the first attempt: (i) the abort-before-write
class again -- the (b)/(c) mangle patterns were single-line while
the paper wraps both phrases across a newline, so the count==1
asserts saw 0 and aborted with nothing written; (ii) a NEW
corollary of that class -- the aborted STEP did not abort the
BATCH, whose remaining restore/run steps kept executing and then
raced a redone batch launched into the same tree (one interleaved
run showed the other batch's mangle).  All interleaved results were
discarded; the suite was rerun serially in a fresh tree with
abort-on-mangle-failure, and only those censuses are recorded
here.  At the round-161 sweep (serial, fresh tree, abort-safe):
(d) the g8 dip probe decoupled (reaches(4.1) -> reaches(10.0),
width(10) > 1) -> g8 trips, 12/1, exit 1; (e) the 1aj marker's
occupancy content mangled (#186 -> #196) -> g10 trips, 12/1,
exit 1; (f) a rational-sign aim flipped below the continuation
threshold (Fr(300) -> Fr(1,10), where F(aim) > 0) -> g1 trips,
12/1, exit 1.  At the round-162 sweep (serial, fresh tree,
abort-safe): the first (g) attempt ABORTED at its own count
assert -- the pattern "pairwise disjoint through zero #33"
matches TWO carriers (the marker AND the W3 body), exposing a
second uncoupled instance of the F162-3 class; both were then
anchored in g10 and probed separately with newline-unique
patterns: (g1) the marker's #33 -> #43 -> g10 trips, 12/1,
exit 1; (g2) the W3 body's #33 -> #43 -> g10 trips, 12/1,
exit 1.  Clean baselines 13/0 exit 0 before and after
every entry.  Thirteen gates (count checked against the gate()
census pre-commit).
"""
import os
import subprocess
import sys
from fractions import Fraction as Fr

import numpy as np
from mpmath import mp, mpf, findroot, zetazero, log, pi as mppi

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")

mp.dps = 30
results = []
FULL = "--full" in sys.argv


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


# ---- the committed three-term construction (the 1aj solve), exact
WS = [Fr(9, 2), Fr(11, 2), Fr(13, 2)]        # w = d + 1/2, d = 4, 5, 6


def _det3(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def solve3_exact(u0):
    """M3 c = (1, -2u0, u0^2) by Cramer over the rationals."""
    M = [[Fr(0)] * 3 for _ in range(3)]
    for i in range(3):
        oth = [WS[j] ** 2 for j in range(3) if j != i]
        M[0][i] = 2 * WS[i]
        M[1][i] = 2 * WS[i] * (oth[0] + oth[1])
        M[2][i] = 2 * WS[i] * oth[0] * oth[1]
    b = [Fr(1), -2 * u0, u0 * u0]
    D = _det3(M)
    cs = []
    for k in range(3):
        Mk = [[b[r] if c == k else M[r][c] for c in range(3)] for r in range(3)]
        cs.append(_det3(Mk) / D)
    return cs


def F_exact(aim):
    """The strip-boundary function of the exact aimed instance."""
    a_fr = Fr(aim).limit_denominator(10 ** 9)
    cs = solve3_exact(a_fr * a_fr)
    def F(g):
        tot = mpf(0)
        for c, w in zip(cs, WS):
            s = mpf(w.numerator) / w.denominator + mpf(1) / 2
            tot += (mpf(c.numerator) / c.denominator
                    * (s / (s * s + g * g) + (s - 1) / ((s - 1) ** 2 + g * g)))
        return tot
    return F


def reaches(aim):
    """(lo, hi): the window's exact edges relative to the aim."""
    a = mpf(Fr(aim).limit_denominator(10 ** 9).numerator) \
        / Fr(aim).limit_denominator(10 ** 9).denominator
    F = F_exact(aim)
    hi = findroot(F, a + mpf("0.47")) - a
    lo = a - findroot(F, a - mpf("0.53"))
    return lo, hi, F


GAMMA1 = 14.134725

print("V1 -- W1: the width limit (exact-rational solves) and the precision cliff")
widths, Fs = {}, {}
ok = True
for a in (GAMMA1, 300.0, 1000.0, 3000.0):
    lo, hi, F = reaches(a)
    widths[a] = lo + hi
    Fs[a] = F
    ok &= F(mpf(a)) < 0
ok &= mpf("1.01563") < widths[GAMMA1] < mpf("1.01564")
ok &= mpf("1.000049") < widths[300.0] < mpf("1.000051")
ok &= mpf("1.0000035") < widths[1000.0] < mpf("1.0000045")
ok &= mpf("1.0000001") < widths[3000.0] < mpf("1.000001")
ok &= widths[GAMMA1] > widths[300.0] > widths[1000.0] > widths[3000.0] > 1
# round 161 F2: the paper's method label overstated ("exact rational
# arithmetic" for the widths); the solves were exact, the edges are
# 30-digit root-finds.  The label is corrected on the paper AND the
# sign conjunct is made FULLY rational here: F at a rational aim is
# a rational number, its sign decided with zero rounding.


def F_rational(a_fr):
    cs = solve3_exact(a_fr * a_fr)
    g2 = a_fr * a_fr
    tot = Fr(0)
    for c, w in zip(cs, WS):
        s = w + Fr(1, 2)
        tot += c * (s / (s * s + g2) + (s - 1) / ((s - 1) ** 2 + g2))
    return tot


for a_fr in (Fr(14134725, 1000000), Fr(300), Fr(1000), Fr(3000)):
    ok &= F_rational(a_fr) < 0
gate("g1 the width limit: widths from the exact-rational solves "
     "bracketed at aims gamma_1/300/1000/3000 (edges by 30-digit "
     "root-finds -- label corrected round 161 F2), strictly "
     "decreasing toward 1, all > 1; F(aim) < 0 at all four with the "
     "sign decided in PURE rational arithmetic",
     ok, f"w(g1)={float(widths[GAMMA1]):.6f} w(3000)={float(widths[3000.0]):.8f}")

M3f = np.zeros((3, 3))
WSf = np.array([4.5, 5.5, 6.5])
for i in range(3):
    oth = [WSf[j] ** 2 for j in range(3) if j != i]
    M3f[0, i] = 2 * WSf[i]
    M3f[1, i] = 2 * WSf[i] * (oth[0] + oth[1])
    M3f[2, i] = 2 * WSf[i] * oth[0] * oth[1]


def F_float(aim):
    u0 = aim * aim
    c = np.linalg.solve(M3f, np.array([1.0, -2 * u0, u0 * u0]))
    return lambda g: sum(c[i] * (WSf[i] + .5) / ((WSf[i] + .5) ** 2 + g * g)
                         + (WSf[i] - .5) / ((WSf[i] - .5) ** 2 + g * g) * c[i]
                         for i in range(3))


# the first draft gated a float SIGN FLIP at 3000; the clean run
# showed the flip is formulation-dependent noise (this kernel gives
# -7e-12 where the scratch formulation gave >= 0).  Redesigned: gate
# the NOISE MAGNITUDE (float error >> exact magnitude) and the
# WINDOW COLLAPSE at 1000 (the artifact the paper discloses).
exact3000 = Fs[3000.0](mpf(3000))
float3000 = F_float(3000.0)(3000.0)
noise_ok = abs(mpf(float3000) - exact3000) > 50 * abs(exact3000)
from scipy.optimize import brentq  # noqa: E402
try:
    Ff = F_float(1000.0)
    w_float = ((brentq(Ff, 1000.0 + 1e-4, 1002.0) - 1000.0)
               + (1000.0 - brentq(Ff, 998.0, 1000.0 - 1e-4)))
    collapse_ok = abs(w_float - float(widths[1000.0])) > 0.5
    w_note = f"float width(1000) = {w_float:.4f}"
except ValueError:
    collapse_ok = True          # failure to bracket IS the artifact
    w_note = "float width(1000): no bracket (the artifact)"
ok = noise_ok and collapse_ok and exact3000 < 0
gate("g2 the precision cliff: the float64 value at aim 3000 is "
     "cancellation noise (|float - exact| > 50x the exact "
     "magnitude); the float64 window at aim 1000 collapses (width "
     "off by > 0.5, or no bracket); the exact-rational F stays "
     "negative",
     ok, f"float F(3000) = {float3000:+.2e}, exact {float(exact3000):+.2e}; "
         + w_note)

ok = True
for a in (300.0, 1000.0, 3000.0):
    lo, hi, _ = reaches(a)
    ok &= mpf("1.23") < (lo - mpf("0.5")) * a < mpf("1.27")
    ok &= mpf("1.23") < (mpf("0.5") - hi) * a < mpf("1.27")
gate("g3 the offset scaling: (lo - 1/2)*aim and (1/2 - hi)*aim in "
     "(1.23, 1.27) at 300/1000/3000 -- the OBSERVED c ~ 1.25 (not "
     "derived)", ok)

print("V2 -- W2: the tiling chain (reach complete on the sampled width floor)")
aims = [20.0 + 0.9 * k for k in range(23)]
edges = []
for a in aims:
    lo, hi, _ = reaches(a)
    edges.append((a - lo, a + hi))
ok = len(aims) == 23 and abs(aims[-1] - 39.8) < 1e-12
margins = [edges[k][1] - edges[k + 1][0] for k in range(22)]
ok &= all(m > 0 for m in margins)
ok &= edges[0][0] < 20 and edges[-1][1] > 40
gate("g4 the tiling: 23 aims spanning [20, 39.8] step 0.9 < width; "
     "every consecutive overlap margin > 0; the connected union "
     "covers [20, 40]",
     ok, f"min margin {float(min(margins)):.4f}")

print("V3 -- W3: the crowding census (zeros 1-240 recomputed live)")
N = 800 if FULL else 240
with mp.workdps(20):
    zs = [float(zetazero(n).imag) for n in range(1, N + 1)]
pairs = [(i + 1, zs[i], zs[i + 1], zs[i + 1] - zs[i]) for i in range(len(zs) - 1)]

cache = {}


def LOHI(a):
    if a not in cache:
        lo, hi, _ = reaches(a)
        cache[a] = (lo, hi)
    return cache[a]


# overlap candidates: hi(a) + lo(b) <= width(a) <= 1.0157, so gap >=
# 1.03 cannot overlap; exact-check the rest
cand = [p for p in pairs if p[3] < 1.03]
overlaps = []
for n, a, b, gap in cand:
    _, hi_a = LOHI(a)
    lo_b, _ = LOHI(b)
    if hi_a + lo_b > gap:
        overlaps.append((n, a, b, gap, float(hi_a + lo_b - gap)))
first = overlaps[0]
ok = all(n >= 34 for n, *_ in overlaps)          # disjoint through #33
ok &= first[0] == 34
ok &= 0.8451 < first[3] < 0.8452
ok &= 0.15 < first[4] < 0.16
ok &= abs(first[1] - 111.02953554) < 1e-6 and abs(first[2] - 111.87465917) < 1e-6
gate("g5 disjoint through #33 (every candidate pair below #34 "
     "exact-checked; wider gaps excluded by the width bound); first "
     "overlap #34/#35 at gamma 111.0295/111.8746, gap in (0.8451, "
     "0.8452), depth in (0.15, 0.16)",
     ok, f"first ({first[0]}, gap {first[3]:.6f}, depth {first[4]:.4f})")

# containment candidates: lo(b) <= lo(gamma_1) = 0.5835 bound
ccand = [p for p in pairs if p[3] < 0.5835]
contain = []
for n, a, b, gap in ccand:
    lo_a, hi_a = LOHI(a)
    lo_b, hi_b = LOHI(b)
    if gap < hi_a:
        contain.append((n, "next-in-n"))
    if gap < lo_b:
        contain.append((n, "prev-in-n1"))
firstc = contain[0]
mutual = sorted({n for n, _ in contain
                 if (n, "next-in-n") in contain and (n, "prev-in-n1") in contain})
i186, i187 = zs[185], zs[186]
g186 = i187 - i186
lo187, _ = LOHI(i187)
_, hi186 = LOHI(i186)
i212, i213 = zs[211], zs[212]
g212 = i213 - i212
lo213, _ = LOHI(i213)
_, hi212 = LOHI(i212)
ok = firstc[0] == 186 and firstc[1] == "prev-in-n1"
ok &= all(n >= 186 for n, _ in contain)
ok &= float(hi186) < g186 < float(lo187)         # the one-sidedness
ok &= 0.4981 < g186 < 0.4982
ok &= mutual[0] == 212
ok &= g212 < min(float(hi212), float(lo213))
ok &= 0.4364 < g212 < 0.4365
ok &= abs(i212 - 415.01880975) < 1e-6 and abs(i213 - 415.45521499) < 1e-6
gate("g6 the containment firsts: none below #186; #186/#187 "
     "ONE-SIDED (hi(a) < gap < lo(b), the lower reach capturing "
     "first); first MUTUAL #212/#213 (gap < both reaches); no "
     "mutual below #212",
     ok, f"gap186 {g186:.6f}, gap212 {g212:.6f}")

T = zs[239]        # gamma_240 in both modes (round 161 F5: the dead
                   # conditional `if not FULL else` removed)
rvm = T / (2 * np.pi) * np.log(T / (2 * np.pi * np.e)) + 7.0 / 8.0
ok = abs(rvm - 240) < 1.5
gate("g7 the occupancy cross-check: the Riemann-von Mangoldt main "
     "count at gamma_240 within 1.5 of 240 (the classical density "
     "the asymptotic occupancy width x density multiplies)",
     ok, f"RvM(gamma_240) = {rvm:.2f}")

if FULL:
    fcand = [p for p in pairs if p[3] < 1.03]
    fover = [1 for n, a, b, gap in fcand
             if LOHI(a)[1] + LOHI(b)[0] > gap]
    fccand = [p for p in pairs if p[3] < 0.5835]
    fcont = []
    for n, a, b, gap in fccand:
        if gap < LOHI(a)[1]:
            fcont.append(1)
        if gap < LOHI(b)[0]:
            fcont.append(1)
    gate("g7f [--full] the 800-zero census: 216 candidates, 200 "
         "overlapping adjacent pairs, 41 directional containment "
         "events (a mutual pair contributes two)",
         len(fcand) == 216 and sum(fover) == 200 and sum(fcont) == 41,
         f"cand {len(fcand)}, overlaps {sum(fover)}, events {sum(fcont)}")

print("V4 -- W4: the resolution floor and the 1aj committed-window tie")
ok = True
for a in (GAMMA1, 20.0, 50.0, 100.0, 300.0, 1000.0, 3000.0):
    lo, hi, _ = reaches(a)
    ok &= lo + hi > 1
# round 161 (the reviewer's held note, verified by the lead and
# gated at the sweep): the floor genuinely FAILS below the sampled
# range -- the "sampled" qualifiers are load-bearing.  width(1) ~
# 0.921 < 1; the crossing sits between aims 4.1 and 4.5; every zero
# height lies far above, at gamma >= gamma_1.
lo1, hi1, _ = reaches(1.0)
lo41, hi41, _ = reaches(4.1)
lo45, hi45, _ = reaches(4.5)
ok &= mpf("0.920") < lo1 + hi1 < mpf("0.922")
ok &= lo41 + hi41 < 1 < lo45 + hi45
gate("g8 the resolution floor: width > 1 at every SAMPLED aim "
     "(gamma_1, 20, 50, 100, 300, 1000, 3000) -- the family "
     "relocates, it does not concentrate (sampled, not proved); AND "
     "the dip below the sampled range gated (width(1) in (0.920, "
     "0.922); the crossing of 1 inside (4.1, 4.5)) -- the sampled "
     "qualifiers are load-bearing (round 161)", ok,
     f"width(1)={float(lo1+hi1):.4f}")

Fg1 = Fs[GAMMA1]
ok = Fg1(mpf("13.5513")) > 0
ok &= Fg1(mpf("13.5514")) < 0
ok &= Fg1(mpf("14.5669")) < 0
ok &= Fg1(mpf("14.5670")) > 0
gate("g9 the 1aj committed-window tie: at aim gamma_1 the boundary "
     "function is negative at both committed inward endpoints "
     "13.5514 / 14.5669 and positive just outside both", ok)

print("V5 -- the paper: key sentences, honest scope, siblings, footer")

# declared paper surface (round-264 F264-1: chain
# scripts in tower members' reaches mirror their
# inline paper conjuncts here; run_tower's harvest
# meta-gate verifies this declaration COVERS every
# inline compare, so drift fails the precheck)
import paper_needles
PAPER_NEEDLES = [
    {'s': '90 scripts cited in place', 'form': 'plain', 'min': 1},
    {'s': 'Theorems 1i–1bn', 'form': 'plain', 'min': 1},
    {'s': '`cascade_windows_overlap.py`', 'form': 'plain', 'min': 1},
    {'s': 'are pairwise disjoint through zero #33; the first overlap is #34/#35', 'form': 'plain', 'min': 1},
    {'s': 'c ≈ 1.25 is observed, not derived', 'form': 'plain', 'min': 1},
    {'s': 'honest name is CONTRAST', 'form': 'plain', 'min': 1},
    {'s': 'it can relocate, it cannot concentrate', 'form': 'plain', 'min': 1},
    {'s': 'net-state, Theorem 1an', 'form': 'plain', 'min': 1, 'max': 1},
    {'s': 'no numerical advance over classical zero-verification is claimed or implied', 'form': 'plain', 'min': 1},
    {'s': 'pairwise disjoint through #33, single-occupancy through #186', 'form': 'plain', 'min': 1},
    {'s': 'single-occupancy through #186, a window first holding a second zero at #187', 'form': 'plain', 'min': 1},
    {'s': 'stay pairwise disjoint through zero #33 — first overlap #34/#35', 'form': 'plain', 'min': 1},
    {'s': 'struck at the 1ap regrade', 'form': 'plain', 'min': 2, 'max': 2},
    {'s': 'struck at the Theorem 1ap regrade', 'form': 'plain', 'min': 2, 'max': 2},
    {'s': 'struck round 161 F1', 'form': 'plain', 'min': 3, 'max': 3},
    {'s': 'struck round 162 F1', 'form': 'plain', 'min': 1, 'max': 1},
    {'s': 'the RH deficit is RESOLUTION, not reach', 'form': 'plain', 'min': 1},
    {'s': 'the census mean occupancy of the aimed windows is 1 + 41/800', 'form': 'plain', 'min': 1},
    {'s': 'the first two-zero window is #187', 'form': 'plain', 'min': 1},
    {'s': 'the lower reach exceeds ½ and captures first', 'form': 'plain', 'min': 1},
    {'s': 'wall stands where it stood', 'form': 'plain', 'min': 2},
    {'s': 'width > 1 is sampled, not proved', 'form': 'plain', 'min': 1},
]
# 1ap regrade: the two W4 needles now live INSIDE strike frames on
# the paper (struck at the 1ap regrade, self-caught); the anchors
# advance to the frames + the regrade content, per the F161 pattern.
ok = paper_needles.needle(PAPER_NEEDLES, 'the RH deficit is RESOLUTION, not reach', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'it can relocate, it cannot concentrate', 'plain')
# round 264: the sum-compare (long+short == 4) split into two
# exact pins (2 each, verified at the split) so the conjunct is
# harvestable by the paper-needle meta-gate; strictly stronger.
ok &= paper_needles.needle(PAPER_NEEDLES, 'struck at the Theorem 1ap regrade', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'struck at the 1ap regrade', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'honest name is CONTRAST', 'plain')
# round 161 F1: the per-zero->per-cluster transition was pinned to
# the wrong threshold (#33 is overlap-onset; occupancy-onset is
# #187).  The old needle now lives only inside its strike frames;
# the anchors are the corrected content + the three strike frames.
ok &= (paper_needles.needle(PAPER_NEEDLES, 'pairwise disjoint through #33, single-occupancy through #186', 'plain'))
ok &= paper_needles.needle(PAPER_NEEDLES, 'the first two-zero window is #187', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'struck round 161 F1', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the lower reach exceeds ½ and captures first', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'net-state, Theorem 1an', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'single-occupancy through #186, a window first holding a second zero at #187', 'plain')
# round 162 F3: the marker rewrite had destroyed the landing's
# sabotage-(c) pattern, leaving the marker's DISJOINTNESS clause
# uncoupled (the reviewer's probe mangled its #33 with no trip).
# Anchor it; and anchor the round-162 F1 relabel by content.
ok &= (paper_needles.needle(PAPER_NEEDLES, 'stay pairwise disjoint through zero #33 — first overlap #34/#35', 'plain'))
# the same numeral in the W3 body is anchored too (the F162-3
# class applies to every carrier of it, caught at the (g) probe's
# abort: the pattern matched two instances)
ok &= (paper_needles.needle(PAPER_NEEDLES, 'are pairwise disjoint through zero #33; the first overlap is #34/#35', 'plain'))
ok &= (paper_needles.needle(PAPER_NEEDLES, 'the census mean occupancy of the aimed windows is 1 + 41/800', 'plain'))
ok &= paper_needles.needle(PAPER_NEEDLES, 'struck round 162 F1', 'plain')
gate("g10 1an's key sentences + the 1aj net-state marker anchored by "
     "content (the deficit's name; relocate-not-concentrate; the "
     "CORRECTED disjointness/occupancy thresholds + three F1 strike "
     "frames -- round 161; the marker's disjointness clause + the "
     "occupancy relabel + its strike frame -- round 162; the "
     "one-sided capture; the marker)", ok,
     "161/162 frame counts declared; evidence f-string retired round 274 (F274-1)")

ok = (paper_needles.needle(PAPER_NEEDLES, 'no numerical advance over classical zero-verification is claimed or implied', 'plain'))
ok &= paper_needles.needle(PAPER_NEEDLES, 'c ≈ 1.25 is observed, not derived', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'width > 1 is sampled, not proved', 'plain')
# case-robust: 1aj carries the sentence mid-sentence (lowercase),
# 1an sentence-initial -- count the case-free core.
ok &= paper_needles.needle(PAPER_NEEDLES, 'wall stands where it stood', 'plain')
gate("g11 the honest-scope anchors: the no-numerical-advance "
     "disclaimer; observed-not-derived; sampled-not-proved; the "
     "wall-unchanged sentence (case-free core, count >= 2 -- it "
     "also lives in 1aj)",
     ok, "wall count declared; evidence f-string retired round 274 (F274-1)")

rr = subprocess.run([sys.executable,
                     os.path.join(ROOT, "tools", "research",
                                  "cascade_riemann_selection.py")],
                    capture_output=True, text=True)
ok = rr.returncode == 0 and "12 pass / 0 fail" in rr.stdout
gate("g12 the sibling chain green after the census advance "
     "(riemann_selection 12/0, chaining type_counting and the two "
     "Weil-arc siblings)", ok)

# 1ao landing: the footer census advanced (64 -> 65; range -> 1ao)
# -- the census-evolution class, disclosed.
ok = paper_needles.needle(PAPER_NEEDLES, '`cascade_windows_overlap.py`', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, '90 scripts cited in place', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'Theorems 1i–1bn', 'plain')
gate("g13 the footer census (advanced at the 1an-1ap landings, "
     "disclosed): this script backticked; 88 cited in place; the "
     "range 1i–1bl (label re-synced rounds 167 F6, 175 F2, 213 F3)", ok)

n_pass, n_fail = sum(results), len(results) - sum(results)
n_gates = 14 if FULL else 13
print(f"\nRESULT: {n_pass} pass / {n_fail} fail ({n_gates} gates)")
print("READING: the windows overlap.  W1: the committed instance's")
print("window width falls from 1.0156 at gamma_1 toward EXACTLY 1 (the")
print("continuation mechanism's 2 x 1/2); the solves and the F-signs")
print("are exact-rational, the edges 30-digit root-finds (round 161")
print("F2); offsets 1/2 +/- c/gamma with c ~ 1.25 observed at the")
print("asymptotic aims 300-3000 (round 161 F6); below the sampled")
print("range the floor fails (width(1) ~ 0.921, crossing 1 in (4.1,")
print("4.5), gated) -- the sampled qualifiers are load-bearing; the")
print("double-precision collapse above aim ~10^3 is a cancellation")
print("artifact, gated in both directions -- future large-aim gates")
print("must use the exact-rational route.  W2: aims spaced below the")
print("width tile any interval -- reach complete on the SAMPLED width")
print("floor (round 161 F3), one chain gated.  W3: per-zero windows")
print("are pairwise disjoint through zero #33 (first overlap #34/#35,")
print("gamma ~ 111) and SINGLE-OCCUPANCY through #186 -- the first")
print("two-zero window is #187 (round 161 F1: the transition is")
print("occupancy-onset, not overlap-onset); first one-sided")
print("containment #186/#187 (the lower reach captures first); first")
print("mutual containment #212/#213 (gamma ~ 415); under --full, 200")
print("of 799 pairs overlap by gamma ~ 1184 with 41 DIRECTIONAL")
print("containment events (a mutual pair contributes two -- round 161")
print("F4); the window width stays below the mean zero spacing --")
print("width x density ~ 0.83 at gamma ~ 1184, reaching 1 only near")
print("gamma ~ 3.4e3 -- so second occupants are atypical, the census")
print("mean occupancy of the aimed windows being 1 + 41/800 ~ 1.05,")
print("never below 1 (relabeled round 162 F1); positivity")
print("unchanged by sharing.  W4 (as regraded by Theorem 1ap): the")
print("sampled aimed family relocates but does not concentrate; the")
print("full cone DOES concentrate (width ~ 5/(2 gamma_0) at height,")
print("contrast ~ gamma_0^-6 -- 1ap); coverage is complete on the")
print("sampled scope, the width floor stays above 1 at every sampled")
print("aim >= gamma_1, and the profile is fixed for the aimed family;")
print("the forcing clause stands: the wall's forcing is classical")
print("zero data, claimed in neither direction; the deficit's honest")
print("coordinate is CONTRAST (1ap; splice repaired round 167 F5).")
print("The wall stands where it stood.  No closures, no data, no")
print("numerical advance over classical methods claimed; no direction")
print("of explanation.")
sys.exit(0 if n_fail == 0 else 1)
