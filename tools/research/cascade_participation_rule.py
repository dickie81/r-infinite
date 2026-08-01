#!/usr/bin/env python3
"""Theorem 1ad verifier: the participation rule.

Claim under test: partitioning the descent's 27 Dirac seats
(d mod 8 = 5 in [4, 217]) into trailing Bott cells (d-8, d], the
rule "a seat hosts propagating content iff its cell contains a
distinguished source layer" (round-124 F4 wording) -- the committed source set
{5, 7, 14, 19} of part4b's prop:source-selection -- yields exactly
the three SM generation seats {5, 13, 21} (cell contents {5}, {7},
{14, 19}; the four-source/three-generation mismatch is the 14/19
cell collision) and empties every cell from seat 29 onward.  The
CENSUS is a theorem (finite arithmetic over structure-forced data
-- Gamma for {5, 7, 19}, Adams/Bott for 14 (round-124 F4) --
recomputed here); the COUPLING MECHANISM (sourced cell <=>
time-coupled) is proposition-grade -- grounded in the committed
neutrino formula m_nu(Gen g) = m_29 alpha(d_g)/chi^(29-d_g), whose
heaviest-neutrino filter exponent is exactly one Bott period
(chi^8), read structurally as the cross-cell coupling cost; the
biconditional itself is NOT derived (the named remaining theorem,
part4a's resolution route (a)).  Postdictions gated: the alpha_em
exactly-three brake; d=29's committed source-only role
(cascade_neutrino_mass_audit.py, gated as of the round-124 F1
hardening, subprocess exit-gated here); the cut = last source +
one Bott period = 27 (integer; part4a's own committed candidate,
anchored), with the continuous variant d*_1 + 8 = 27.73 a
disclosed different anchor, both strictly inside part4a's
empirical bracket (21.0, 29.0).  Disclosures gated: the
two part4a-named tower scripts are ANALYSIS-GRADE (tables, no
verdict gates) -- run for runnability only, so stated; the by-catch
(part4a prose tower masses vs the tower script's table disagree by
one factor ~2 sqrt(pi) on non-load-bearing values) was flagged at
the landing and ADJUDICATED in the round-124 sweep (part4a's prose
correct; see the SWEEP paragraph below).

Gates:
  P1 -- the census arithmetic, exact: 27 seats; occupied cells
        exactly {5: {5}, 13: {7}, 21: {14, 19}}; first failing seat
        29; all 24 later cells empty; threshold d*_1 solved from
        psi((d+1)/2) = 2 ln pi at 19.731 (half-ULP of part4a's
        quoted digits); the cut 27 = 19 + 8 declared as an
        identity with both anchors' bracket containment gated; the
        8-offset orientation-robustness census (round-124 F5).
  P2 -- part4a's tension + candidate anchored verbatim (the
        infinite-ladder sentence; the hidden-empirical-input
        sentence; the exactly-three sentence; OQ-T4's
        mass-not-charge + accessibility sentences; the
        time-decoupling candidate; route (a)).
  P3 -- part4b's source set and neutrino formula anchored (the set
        {5, 7, 14, 19}; the formula with exponent 29 - d_g; the
        0.0493 eV value).  chi^8 = 256 and 29 - 21 = 8 are literal
        arithmetic -- DECLARED identities, not gated (the 1l(iv)
        discipline).
  P4 -- instruments: cascade_neutrino_mass_audit.py subprocess
        exit 0 + RESULT 4/0 (gated as of the round-124 F1
        hardening; the landing's "contains sys.exit" was vacuous);
        cascade_bott_tower_beyond_29.py and
        cascade_d29_sterile_neutrino.py subprocess exit 0
        (RUNNABILITY ONLY -- analysis-grade, no verdict gates;
        the paper discloses this and the disclosure is gated in
        P5).
  P5 -- 1ad's key sentences anchored (the rule; the census-theorem
        grading; the proposition grading + underived biconditional;
        the analysis-grade disclosure; the by-catch; the round-124
        sweep anchors -- orientation disclosure, forcer naming,
        corrected falsifier); the by-catch ratios at the quoted
        values within 5% of 2 sqrt(pi).

No data consumed; no number changes; category (a) plus one stated
candidate criterion.  Sabotage record (full-tree scratchpad copy,
at the landing commit; mid-anchor perturbations per the twice-
recorded append-after-anchor trap): (a) perturbing part4a's
"hidden empirical input" sentence trips P2, exit 1; (b) perturbing
the source-set display in part4b trips P3, exit 1; (c) removing 19
from the source set in the SCRATCHPAD COPY of this script (an
instrument-expectation perturbation, the forcing_ledger sabotage
precedent) trips P1's occupied-cells gate, exit 1.  Nineteen gates
post the round-124 sweep (the landing had 15; the RESULT line's
first draft said 13 -- corrected pre-commit, the recurring count
defect).

ROUND-124 SWEEP (3 majors, 3 of 4 minors on this arc's surfaces,
all lead-verified): F1 -- the landing labeled
cascade_neutrino_mass_audit.py "a GATED verifier" on the strength
of a `sys.exit(main())` whose main() returned 0 unconditionally --
the round-120 F3 vacuous-gate class, third instance; the script
received real verdict gating (4 verdicts) in the sweep, the paper
claim was struck-and-annotated, and this file's subprocess gate now
also checks the RESULT line.  F2 -- the landing inverted part4a
OQ-T3's Reading labels (A = propagating sterile, B = structural
source mass; the rule instantiates B) and stated its falsifier
backwards (a KATRIN detection would FALSIFY the rule -- the rule
predicts the null; part4a: "Reading~B and Reading~C predict no such
observation"); both corrected in the paper, both anchors gated.
F3 -- the landing's "d_1 + 8 = 27.7" conflated the integer last
source (19 + 8 = 27) with the continuous threshold (d*_1 + 8 =
27.73, not a source), and the cut-27 criterion is part4a's own
committed candidate (anchored), not this theorem's invention; the
paper rewritten, the cut declared as the integer identity with
both anchors' bracket containment gated.  F4 -- "Gamma-forced" was
false for source 14 (Adams/Bott-forced, part4b's own attribution);
labels corrected on all surfaces.  F5 -- the trailing-cell
orientation was load-bearing and undisclosed; now disclosed in the
paper with the 8-offset robustness census gated here ({5,13,21} at
6 of 8 offsets; N=2 at the two leading-most; the quoted contents
unique to trailing).  F6 -- the "in-cell coupling carries no
filter" exemption was an unmarked new input contradicting the
chi^(layer distance) reading; struck, the mechanism claim confined
to the committed cross-cell instances (chi^8/16/24).  F7 (sibling
surface) -- neutrino_mass_audit's stale "Part IVb line 936" defect
report corrected to net-state (the papers-side fix landed long
ago).  The by-catch adjudicated (reviewer-supplied, lead-verified):
part4a's prose is correct; the tower script drops one 2 sqrt(pi)
factor and self-contradicts at its d=29 row (1999 eV vs the
committed 543 eV) -- repair left to a future commit.
"""
import math
import os
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
PART4A = os.path.join(ROOT, "src", "cascade-series-part4a.tex")
PART4B = os.path.join(ROOT, "src", "cascade-series-part4b.tex")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


print("P1 -- the census arithmetic")
seats = [d for d in range(4, 218) if d % 8 == 5]
gate("27 Dirac seats in the descent [4, 217]", len(seats) == 27,
     f"{len(seats)}")
DIST = {5, 7, 14, 19}
cells = {s: set(range(s - 7, s + 1)) & DIST for s in seats}
occupied = {s: sorted(c) for s, c in cells.items() if c}
gate("occupied cells exactly {5: [5], 13: [7], 21: [14, 19]} -- three "
     "sourced cells, the 14/19 collision explaining 4 sources -> 3 "
     "generations",
     occupied == {5: [5], 13: [7], 21: [14, 19]}, f"{occupied}")
empty_from_29 = [s for s in seats if s >= 29 and cells[s]]
gate("every cell from seat 29 onward empty (all sources <= 19)",
     empty_from_29 == [] and (not cells[29]), f"violations = {empty_from_29}")


def p_minus_c1(d):
    # p(d) - c_1 = (1/2) psi((d+1)/2) - ln(pi)
    x = (d + 1) / 2.0
    # digamma via math.lgamma numerical derivative is too coarse; use
    # the recurrence-free series through mpmath-quality approximation:
    # psi(x) ~ ln x - 1/(2x) - 1/(12x^2) + 1/(120x^4) (x ~ 10, ample)
    psi = math.log(x) - 1 / (2 * x) - 1 / (12 * x**2) + 1 / (120 * x**4)
    return 0.5 * psi - math.log(math.pi)


lo, hi = 19.0, 21.0
for _ in range(200):
    mid = (lo + hi) / 2
    if p_minus_c1(mid) < 0:
        lo = mid
    else:
        hi = mid
d_star = (lo + hi) / 2
gate("the threshold d*_1 = 19.731 recomputed (half-ULP of part4a's quoted "
     "3 dp)", abs(d_star - 19.731) < 5e-4, f"{d_star:.6f}")
# round-124 F3: the rule's cut is the INTEGER last-source + one period
# -- 19 + 8 = 27, literal arithmetic (DECLARED, not gated); what is
# gated is bracket containment for both anchors, disclosed as distinct.
print("  IDENTITY (declared, not gated): the cut = last source + one "
      "Bott period = 19 + 8 = 27 -- literal arithmetic")
print("  IDENTITY (declared, not gated): d*_1 + 1.3 < d*_1 + 8 -- the "
      "continuous anchor's lower containment is 1.3 < 8, tautological "
      "(round-125 F3)")
gate("both cut anchors' falsifiable containments: d*_1 + 1.3 < 27 < 29 "
     "(integer) and d*_1 + 8 < 29 (continuous variant, a different "
     "anchor -- round-124 F3)",
     d_star + 1.3 < 27 < 29.0 and d_star + 8 < 29.0,
     f"27 and {d_star + 8:.3f}")
# round-124 F5: the orientation robustness census -- the headline
# N_gen = 3 at seats {5, 13, 21} holds at offsets k = 0..5 (6 of 8);
# the two leading-most offsets give N_gen = 2; only k = 0 (trailing)
# yields the quoted contents {5}, {7}, {14, 19}.
offs = {}
for k in range(8):
    o = {s: sorted(set(range(s - 7 + k, s + 1 + k)) & DIST)
         for s in seats}
    offs[k] = {s: c for s, c in o.items() if c}
ok = all(sorted(offs[k]) == [5, 13, 21] for k in range(6))
ok &= all(len(offs[k]) == 2 for k in (6, 7))
ok &= offs[0] == {5: [5], 13: [7], 21: [14, 19]}
ok &= not any(offs[k] == {5: [5], 13: [7], 21: [14, 19]}
              for k in range(1, 8))
gate("the offset census (round-124 F5): {5,13,21} at 6 of 8 offsets; "
     "N=2 at the two leading-most; the quoted contents unique to "
     "trailing", ok, f"{ {k: len(v) for k, v in offs.items()} }")

print("P2 -- part4a's tension and candidate, verbatim")
part4a = norm(open(PART4A, encoding="utf-8").read())
ok = "with no cascade-internal termination of the replication" in part4a
ok &= ("$N_{\\rm gen}=3$ is currently a hidden empirical input the cascade "
       "relies on without deriving" in part4a)
ok &= "requires \\emph{exactly three} Dirac layers to contribute" in part4a
gate("the (D1)/(D2) tension sentences anchored", ok)
ok = "applies to the \\emph{mass}, not the \\emph{charge}" in part4a
ok &= "it produces enhanced low-energy accessibility" in part4a
gate("OQ-T4's mass-not-charge + accessibility sentences anchored", ok)
ok = "decoupled from time" in part4a
ok &= ("terminating the Bott-replication of propagating fermion content at "
       "the third orbit" in part4a)
gate("the time-decoupling candidate + resolution route (a) anchored", ok)
ok = ("would give $d \\leq d_1 + 8 = 27$, capturing $d=21$ but not $d=29$"
      in part4a)
gate("part4a's own committed cut-27 precedent anchored (round-124 F3: the "
     "rule grounds it, does not invent it)", ok)
ok = ('Reading~B and Reading~C predict no such observation' in part4a)
gate("part4a's null-prediction sentence anchored (round-124 F2: the "
     "corrected falsifier logic)", ok)

print("P3 -- part4b's source set and neutrino formula")
part4b = norm(open(PART4B, encoding="utf-8").read())
ok = "\\{d_V, d_0, d_{\\rm gw}, d_1\\} = \\{5, 7, 14, 19\\}" in part4b
gate("the committed source set anchored", ok)
ok = "m_{29}\\cdot\\alpha(d_g)/\\chi^{29 - d_g}" in part4b
ok &= "m_{29}\\cdot\\alpha(21)/\\chi^8 = 0.0493" in part4b
gate("the neutrino formula (exponent = layer distance) + the heaviest "
     "value anchored", ok)
print("  IDENTITY (declared, not gated): chi^8 = 2^8 = 256; 29 - 21 = 8 = "
      "one Bott period -- literal arithmetic")

print("P4 -- the instruments")
r = subprocess.run([sys.executable,
                    os.path.join(ROOT, "tools", "research",
                                 "cascade_neutrino_mass_audit.py")],
                   capture_output=True, text=True)
gate("cascade_neutrino_mass_audit.py exit 0 -- gated as of the round-124 "
     "F1 hardening (4 verdicts; at the landing commit its exit was "
     "unconditional and this gate was vacuous, struck in the paper)",
     r.returncode == 0 and "RESULT: 4 pass / 0 fail" in r.stdout,
     f"exit {r.returncode}")
ok = True
for s in ("cascade_bott_tower_beyond_29", "cascade_d29_sterile_neutrino"):
    rr = subprocess.run([sys.executable,
                         os.path.join(ROOT, "tools", "research", s + ".py")],
                        capture_output=True, text=True)
    ok &= rr.returncode == 0
gate("the two analysis-grade tower scripts run (RUNNABILITY ONLY -- no "
     "verdict gates; disclosed)", ok)

print("P5 -- 1ad's key sentences and the by-catch")
paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")
ok = ("a seat hosts propagating (time-coupled) content iff its cell "
      "contains a distinguished source layer" in paper)
ok &= "N_gen = 3 as a counting theorem" in paper
gate("the rule + the census-theorem grading anchored (round-124 F4 "
     "wording)", ok)
ok = "coupling mechanism is proposition-grade" in paper
ok &= "the biconditional itself is not derived" in paper
ok &= "analysis-grade — tables without verdict gates" in paper
gate("the proposition grading + the analysis-grade disclosure anchored", ok)
ok = "the trailing choice is a convention, stated not forced" in paper
ok &= "14 by Adams' theorem and the Bott mirror" in paper
ok &= "the rule PREDICTS a null KATRIN/TRISTAN result" in paper
ok &= "the rule instantiates Reading B" in paper
gate("the round-124 sweep anchors: the orientation disclosure (F5), the "
     "forcer naming (F4), the corrected falsifier + Reading-B "
     "instantiation (F2)", ok)
r1, r2 = 0.704 / 0.2, 105.0 / 30.0
tsp = 2 * math.sqrt(math.pi)
ok = abs(r1 / tsp - 1) < 0.05 and abs(r2 / tsp - 1) < 0.05
ok &= "×3.5 ≈ 2√π" in paper
gate("the by-catch: both prose-vs-table ratios within 5% of 2√π at the "
     "quoted values, and flagged in the paper",
     ok, f"{r1:.3f}, {r2:.3f} vs {tsp:.3f}")

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (19 gates; 2 identities declared, not counted)")
print("READING: the participation rule -- a Dirac seat propagates iff its")
print("trailing Bott cell contains a distinguished source layer (Gamma-")
print("forced at {5, 7, 19}, Adams/Bott-forced at 14 -- round-124 F4;")
print("READING aligned round 125 F1).  The")
print("census is a theorem: 27 seats, three sourced cells ({5}, {7},")
print("{14, 19} -- the 14/19 collision is why four sources give three")
print("generations), every cell from 29 onward empty.  It postdicts the")
print("alpha_em exactly-three brake, d=29's source-only role (the chi^8 =")
print("one-period filter, the formula's own exponent); the cut is the")
print("integer last source + one period = 27, part4a's own committed")
print("candidate grounded in the source set (the 27.73 continuous")
print("variant a disclosed different anchor).  The coupling")
print("biconditional is proposition-grade and underived -- the named")
print("remaining theorem.  The flags' precedence stays open; Check 8")
print("clean (the source set is structure-forced, Gamma + Adams,")
print("observer-free).")
sys.exit(0 if n_fail == 0 else 1)
