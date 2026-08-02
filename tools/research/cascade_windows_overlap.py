#!/usr/bin/env python3
"""
THEOREM 1an -- the windows overlap: coverage, crowding, and the
wall's resolution restatement.

THE COMMISSION.  The owner asked "Do the windows overlap?" of 1aj's
relocatable sensitivity windows and commissioned the landing.

THE CONTENT (four theorems + honest scope).
  W1 (the width limit, exact-rational).  For the committed three-term
      instance (d = 4, 5, 6 -- the 1aj solve, kernels at w = d+1/2),
      the window width lo + hi decreases monotonically on the sampled
      aim spread from 1.0156... at gamma_1 toward EXACTLY 1 (the
      continuation mechanism's own 2 x 1/2), with offsets
      1/2 +/- c/gamma, c ~ 1.25 OBSERVED (not derived), and
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
  W2 (tiling: reach is complete).  Aims spaced below the width tile
      any interval with overlapping windows -- gated on a 23-aim
      chain spanning [20, 40]: every consecutive pair overlaps and
      the union is connected, covering [20, 40].  No height escapes
      the committed family's sensitivity.
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
      bound: per-zero through #33, per-cluster beyond.
  W4 (reach vs resolution -- the wall sharpened).  W2 + W1: the
      family can look ANYWHERE, but its width stays above 1 on the
      sampled family and its profile is the fixed three-Lorentzian
      shape -- it can relocate, it cannot concentrate.  Weil's dense
      class requires arbitrary concentration; the committed family
      supplies relocation without resolution.  The wall stands where
      it stood; the deficit's name sharpens: RESOLUTION, not reach.

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
       F(aim) < 0 at all four); g2 the precision cliff (the float64
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
       "sampled" is the claim's scope); g9 the 1aj committed-window
       tie (at aim gamma_1 the boundary function is negative at
       both committed inward endpoints 13.5514 / 14.5669 and
       positive just outside both, matching 1aj's gated window).
  V5 -- g10 1an's key sentences + the 1aj net-state marker anchored
       by content; g11 the honest-scope anchors (the no-numerical-
       advance disclaimer; observed-not-derived; sampled-not-proved;
       the wall-unchanged sentence at count >= 2 -- it also lives in
       1aj); g12 the sibling chain green (riemann_selection 12/0,
       which chains type_counting and the two Weil-arc siblings);
       g13 the footer census (this script backticked; "64 scripts
       cited in place"; "Theorems 1i-1an").

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
here.  Thirteen gates (count checked against the gate() census
pre-commit).
"""
import os
import subprocess
import sys
from fractions import Fraction as Fr

import numpy as np
from mpmath import mp, mpf, findroot, zetazero, log, pi as mppi

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")

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

print("V1 -- W1: the width limit (exact-rational) and the precision cliff")
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
gate("g1 the width limit: exact-rational widths bracketed at aims "
     "gamma_1/300/1000/3000, strictly decreasing toward 1, all > 1, "
     "F(aim) < 0 at all four",
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

print("V2 -- W2: the tiling chain (reach is complete)")
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

T = zs[239] if not FULL else zs[239]
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
gate("g8 the resolution floor: width > 1 at every SAMPLED aim "
     "(gamma_1, 20, 50, 100, 300, 1000, 3000) -- the family "
     "relocates, it does not concentrate (sampled, not proved)", ok)

Fg1 = Fs[GAMMA1]
ok = Fg1(mpf("13.5513")) > 0
ok &= Fg1(mpf("13.5514")) < 0
ok &= Fg1(mpf("14.5669")) < 0
ok &= Fg1(mpf("14.5670")) > 0
gate("g9 the 1aj committed-window tie: at aim gamma_1 the boundary "
     "function is negative at both committed inward endpoints "
     "13.5514 / 14.5669 and positive just outside both", ok)

print("V5 -- the paper: key sentences, honest scope, siblings, footer")
paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")
ok = "the RH deficit is RESOLUTION, not reach" in paper
ok &= "it can relocate, it cannot concentrate" in paper
ok &= "the probe is per-zero through #33 and per-cluster beyond" in paper
ok &= "the lower reach exceeds ½ and captures first" in paper
ok &= paper.count("net-state, Theorem 1an") == 1
ok &= "per-zero literally through zero #33" in paper
gate("g10 1an's key sentences + the 1aj net-state marker anchored by "
     "content (the deficit's name; relocate-not-concentrate; the "
     "per-cluster scope; the one-sided capture; the marker)", ok)

ok = ("no numerical advance over classical zero-verification is "
      "claimed or implied" in paper)
ok &= "c ≈ 1.25 is observed, not derived" in paper
ok &= "width > 1 is sampled, not proved" in paper
# case-robust: 1aj carries the sentence mid-sentence (lowercase),
# 1an sentence-initial -- count the case-free core.
ok &= paper.count("wall stands where it stood") >= 2
gate("g11 the honest-scope anchors: the no-numerical-advance "
     "disclaimer; observed-not-derived; sampled-not-proved; the "
     "wall-unchanged sentence (case-free core, count >= 2 -- it "
     "also lives in 1aj)",
     ok, f"wall count {paper.count('wall stands where it stood')}")

rr = subprocess.run([sys.executable,
                     os.path.join(ROOT, "tools", "research",
                                  "cascade_riemann_selection.py")],
                    capture_output=True, text=True)
ok = rr.returncode == 0 and "12 pass / 0 fail" in rr.stdout
gate("g12 the sibling chain green after the census advance "
     "(riemann_selection 12/0, chaining type_counting and the two "
     "Weil-arc siblings)", ok)

ok = "`cascade_windows_overlap.py`" in paper
ok &= "64 scripts cited in place" in paper
ok &= "Theorems 1i–1an" in paper
gate("g13 the footer census (advanced at this landing, disclosed): "
     "this script backticked; 64 cited in place; the range 1i–1an", ok)

n_pass, n_fail = sum(results), len(results) - sum(results)
n_gates = 14 if FULL else 13
print(f"\nRESULT: {n_pass} pass / {n_fail} fail ({n_gates} gates)")
print("READING: the windows overlap.  W1: the committed instance's")
print("window width falls from 1.0156 at gamma_1 to EXACTLY 1 (the")
print("continuation mechanism's 2 x 1/2), offsets 1/2 +/- c/gamma with")
print("c ~ 1.25 observed; the double-precision collapse above aim ~10^3")
print("is a cancellation artifact, gated in both directions -- future")
print("large-aim gates must use the exact-rational route.  W2: aims")
print("spaced below the width tile any interval -- reach is complete,")
print("no height escapes the family.  W3: per-zero windows are")
print("disjoint through zero #33; first overlap #34/#35 (gamma ~ 111);")
print("first one-sided containment #186/#187 (the lower reach captures")
print("first); first mutual containment #212/#213 (gamma ~ 415); under")
print("--full, 200 of 799 pairs overlap by gamma ~ 1184 with 41")
print("directional containment events; occupancy grows as")
print("ln(gamma/2pi)/2pi -- per-zero through #33, per-cluster beyond,")
print("positivity unchanged by sharing.  W4: the family relocates but")
print("cannot concentrate -- coverage is complete while the width")
print("floor stays above 1 (sampled) and the profile is fixed; Weil's")
print("dense class needs arbitrary concentration, so the RH deficit is")
print("RESOLUTION, not reach.  The wall stands where it stood.  No")
print("closures, no data, no numerical advance over classical methods")
print("claimed; no direction of explanation.")
sys.exit(0 if n_fail == 0 else 1)
