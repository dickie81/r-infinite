#!/usr/bin/env python3
"""Theorem 1ac verifier: A3's underived rules audited.

Claim under test: A3's tail sentence ("the increment and per-period
rules are underived") is SUPERSEDED-TRUE against the committed
record on its own surface: the increment rule is gap-ledger row 1's
"derived from arithmetic first principles (T5, Addendum 33) --
closed as mathematics," with attach-once proved on the arithmetic
side (Z's total order, T5) AND the physical side (unit source
strength, the marginal Green's-function identity with source
coefficient exactly 1 via Sturm-Liouville assembly -- the committed
verifier run here), plus the 1/chi^k filtering derivation and the
slot-precedence proposition (conditional on the strict G-flag
reading -- disclosed in part4b's Tier-2 summary and closure note,
adjudicated empirically there, per round 120 F6); the per-period
rule is row 2's decomposition (shape derived; mechanism at Tier-2
(A38/A43), form conditional on availability assignments; the unit
normalization and marked coset the residue). The axiom block is
byte-identity gated (the adoption's discipline), so the net-state
marker sits ADJACENT to the block, and the block's untouchedness
is gated here by re-running riemann_kernel. A3's net residue, six
items (round 120 F6): {occupancy, (m,k) counts, P>L>G, the
per-period unit normalization, the marked coset, the strict
G-flag reading} -- instantiation, convention, or empirically
anchored reading; zero underived rules-in-form, with row 2's
mechanism carried at Tier-2 per its own ledger row.
The 1z route narrowed: the strict-boundary stipulation's committed
home is thm:alpha-s-closure's scope condition; the marginal-Green's
reading is the named open derivation route. Thirteen gates.

ROUND-120 SWEEP (three majors, three minors, all lead-verified):
the landing's two subprocess gates were vacuous -- riemann_kernel
and unit_source_strength both exited 0 unconditionally, and the
marker's first placement (between A4 and the section-2 heading) sat
INSIDE riemann_kernel V1's compared span, so V1 was FAILING on the
landing commit d4f3c63, masked (F1/F2); unit_source_strength
printed its conclusions even under a falsified identity (F3). The
sweep relocated the marker below the heading (outside the span),
added real exit gating to both instruments, and both falsification
probes now trip: an axiom-block byte edit -> kernel exit 1 -> R5
11/1 exit 1 (13-gate tree: 12/1); greens_function scaled x2 ->
unit_source_strength exit 1 -> R2 trip. Minors: the 1v carrying
surfaces' missing net-state markers added (F4, gated here); row
2's Tier-2 header restored in the marker and 1ac(iii) (F5); the
strict-G-flag conditional re-attributed to part4b's Tier-2
summary/closure note and counted in the residue set (F6).

Gates:
  R1 -- A3's tail + components anchored in the (unedited) block;
        T5's header, attach-once sentence, and what-arithmetic-does-
        not-supply list anchored; ledger row 1's grading anchored.
  R2 -- the committed physical-side instrument run as a subprocess
        (cascade_unit_source_strength.py, exit 0); part4b's unit-
        source sentences anchored (coefficient exactly 1; every
        layer machine precision).
  R3 -- the filtering-rule derivation + structural channel count
        anchored (part4b); the flags' 9/9 partial derivation (A3's
        in-block parenthetical) + the categorical-route Open
        Question (syntactic, Tier 3) anchored.
  R4 -- ledger row 2's per-period decomposition anchored (shape
        derived; flip-count 4; x3 incoherence; the unit
        normalization convention; the JUNO cannot-convict clause).
  R5 -- the block untouched (riemann_kernel subprocess, exit 0);
        the adjacent marker anchored in the formulation; 1ac's key
        sentences anchored (superseded-true; the qualified
        zero-underived-rules-in-form license; the six-item residue
        set; the 1z narrowing with thm:alpha-s-closure's scope
        quote); the strict-G-flag conditional plus its empirical
        adjudication anchored in part4b (Tier-2 summary + closure
        note); the 1v carrying-surface markers on both surfaces.

No data consumed; no number changes; category (a). Sabotage record
(scratchpad copies, at the landing commit): (a) "closed as
mathematics; only its physical instantiation" -> "closed as
mathematics(SABOTAGE); only its physical instantiation" in the
formulation copy tripped R1's ledger-row-1 gate, 11/1, exit 1; (b)
"the axiom block above is byte-identity-gated" -> "... is
byte-identity-SABOTAGED" tripped R5's marker gate, 11/1, exit 1.
(A first attempt at (b) appended "(SABOTAGE)" AFTER the anchored
substring, leaving the anchor intact -- 12/0, no trip: a sabotage-
design error, not a gate defect; redone inside the anchor span and
disclosed here per the instrument rules.) Clean scratchpad baseline
12/0 exit 0 confirmed before and after each perturbation. Both
sabotages re-run on the post-sweep 13-gate tree: 12/1 exit 1 each,
clean baseline 13/0 exit 0 before and after.
"""
import os
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
FORM = os.path.join(ROOT, "cascade-riemann-formulation.md")
PART4B = os.path.join(ROOT, "src", "cascade-series-part4b.tex")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


paper = open(PAPER, encoding="utf-8").read()
form = open(FORM, encoding="utf-8").read()
part4b = open(PART4B, encoding="utf-8").read()
nf, np_, n4b = norm(form), norm(paper), norm(part4b)

print("R1 -- A3, T5, and ledger row 1")
ok1 = "the increment and per-period rules are underived" in nf
ok1 &= "the increment rule (corrections attach once, at sub-lead)" in nf
ok1 &= "*This is the load-bearing axiom.*" in nf
gate("A3's tail + components anchored in the block", ok1)
ok2 = "Arithmetic increment rule — PROVED from Tate's thesis alone; Addendum 33" in nf
ok2 &= "ℤ's total order gives\nattach-once".replace("\n", " ") in nf
ok2 &= ("P > L > G precedence, the physical occupancy assignment, the (m,k) "
        "counts" in nf)
gate("T5's header + attach-once + the not-supplied list anchored", ok2)
ok3 = "**derived from arithmetic first principles** (T5, Addendum 33" in nf
ok3 &= "closed as mathematics; only its physical instantiation (occupancy, m/k counts) remains with C1" in nf
gate("ledger row 1's grading anchored", ok3)

print("R2 -- the physical-side instrument")
r = subprocess.run([sys.executable,
                    os.path.join(ROOT, "tools", "research",
                                 "cascade_unit_source_strength.py")],
                   capture_output=True, text=True)
gate("cascade_unit_source_strength.py runs, exit 0", r.returncode == 0,
     f"exit {r.returncode}")
ok4 = "the source coefficient is exactly $1$ (no fitted prefactor) by assembly via Sturm--Liouville structure" in n4b
ok4 &= "holds at \\emph{every} layer at machine precision" in n4b
gate("part4b's unit-source sentences anchored", ok4)

print("R3 -- the filtering rule + the flags")
ok5 = "Why $1/\\chi$ per channel (derivation of the filtering rule)" in n4b
ok5 &= "The channel count $k$ is not fitted" in n4b
gate("the filtering derivation + structural channel count anchored", ok5)
ok6 = "Addendum 12: the\nflags recovered 9/9 from ξ's factorization".replace("\n", " ") in nf
ok6 &= "stated syntactically rather than derived from a formal object" in n4b
gate("the flags' 9/9 + the categorical-route OQ anchored", ok6)

print("R4 -- the per-period rule (ledger row 2)")
ok7 = "**shape derived** (T6, A34)" in nf
ok7 &= "mechanism at Tier-2 (A38/A43" in nf
ok7 &= "unique colour-free form *conditional on availability assignments*" in nf
ok7 &= "flip-count 4 derived (minimal torsion word)" in nf
ok7 &= "×3 incoherence derived (factorization)" in nf
ok7 &= ("**the unit normalization carrying Γ(½) is a convention, empirically "
        "anchored not arithmetically forced**" in nf)
ok7 &= "cannot convict the form over its 0.1% twins" in nf
gate("row 2's decomposition + the JUNO clause anchored", ok7)

print("R5 -- the block untouched, the marker, 1ac's keys")
r2 = subprocess.run([sys.executable,
                     os.path.join(ROOT, "tools", "research",
                                  "cascade_riemann_kernel.py")],
                    capture_output=True, text=True)
gate("the axiom block untouched (riemann_kernel exit 0)", r2.returncode == 0,
     f"exit {r2.returncode}")
ok8 = "Net-state on A3's tail, Theorem 1ac of the review paper, round 120" in nf
ok8 &= "placed adjacent because the axiom block above is byte-identity-gated" in nf
gate("the adjacent marker anchored (outside the gated span)", ok8)
npp = np_.replace("**", "")
ok9 = "the residue is instantiation, not law" in npp
ok9 &= ("Zero underived rules-in-form remain — with row 2's mechanism carried "
        "at Tier-2 (A38/A43)" in npp)
ok9 &= "the delayed-observation class of 1y, disclosed as such" in npp
ok9 &= "any observable whose cascade path lies strictly below" in npp
gate("1ac's key sentences anchored (round-120 F5/F6 wording)", ok9)
ok10 = "Conditional on the strict reading of the $G$ flag" in n4b
ok10 &= "empirically does not match the residual" in n4b
ok10 &= "The strict reading is therefore the structurally correct one" in n4b
gate("the strict-G-flag conditional + its empirical adjudication anchored in "
     "part4b (round-120 F6: Tier-2 summary + closure note, not the "
     "proposition's own statement)", ok10)
ok11 = "net-state, Theorem 1ac round 120: superseded-true" in npp
ok11 &= "net-state, T1ac of the review paper, round 120" in nf
gate("the 1v carrying-surface markers present on both surfaces "
     "(round-120 F4)", ok11)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (13 gates)")
print("READING (aligned round 121 F1 to the paper's post-sweep wording):")
print("A3's tail is superseded-true -- the increment rule is the ledger's")
print("own 'derived from arithmetic first principles ... closed as")
print("mathematics' (attach-once proved twice over: Z's total order; unit")
print("source strength via Sturm-Liouville, the committed instrument run")
print("here), the filtering derived, the slot placement proposition-grade")
print("and conditional on the strict G-flag reading (part4b's Tier-2")
print("summary + closure note, adjudicated empirically); the per-period")
print("rule is row 2's decomposition, mechanism at Tier-2 (A38/A43), form")
print("conditional on availability assignments. A3's net residue, six")
print("items: occupancy, (m,k), precedence, the unit normalization, the")
print("marked coset, the strict G-flag reading -- instantiation,")
print("convention, or empirically anchored reading. Zero underived")
print("rules-in-form remain, with row 2's mechanism carried at Tier-2")
print("per its own ledger row.")
sys.exit(0 if n_fail == 0 else 1)
