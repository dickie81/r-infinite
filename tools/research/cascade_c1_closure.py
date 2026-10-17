#!/usr/bin/env python3
"""Theorem 1ah verifier: C1 attacked from first principles.

Claim under test: the C1 fork (minimal-spinor vs full-algebra
fiber) DISSOLVES via three graded legs:

  U (uniformity): no minimal-spinor fiber, real or complex, grows
    uniformly per layer (complex ratios alternate 1,2; real Bott
    dims 1,2,4,4,8,8,8,8 lumpier); the full algebra grows
    uniformly at 2.  The committed formula's FORM (a uniform
    integer per-layer exponent across all three generations)
    selects the algebra -- by form, not by the tuned base,
    answering round 133's circularity charge.  Conditional on the
    committed formula's form.
  K (canonicity): the algebra ladder is the unique
    inclusion-canonical transport; a spinor ladder needs an
    unforced binary choice at each of the 107 odd layers in
    [4, 217] (2^107 alternatives).  The zero-free-parameter
    constitution (cited as meta-principle) selects the canonical
    ladder.
  B (bilinear reconciliation): 2^d = (2^floor(d/2))^2 x (2 if d
    odd) EXACTLY at every layer -- the algebra is the spinor
    bilinear space; part4a's minimal spinors carry amplitudes
    (sqrt(2)-average rate), the algebra carries bilinears --
    masses and couplings -- at the squared rate 2.  The committed
    formula transports "the source mass m_29" (part4b's words): a
    bilinear-class object.  Disclosed reading R-bilinear.

Net (REGRADED round 137, within the round): both selection legs
fell -- U's form/value division is empty on the committed record
(every committed Delta is a whole Bott period, where both fibers
are exactly uniform; the selection remains by value, the round-133
circularity); K's 2^107 count is a single gauge orbit under
flag-preserving reflections (lead-verified in Cl_C(3)).  C1 stays
OPEN: reconciled in classification (B, under R-bilinear, with the
amplitude side disclosed as classification without committed
instance -- F137-3) but selected only by the value of the
underived formula.  The unproved set remains (v-b) + C1 + C2 + C3.
What would close C1: an odd-Delta committed instance, or the
formula's derivation.

Gates:
  U1 -- complex spinor per-layer ratios alternate (1,2) and are
        never uniform on [4, 19]; algebra ratios uniformly 2.
  U2 -- real Bott spinor dims (1,2,4,4,8,8,8,8) ratios computed;
        not uniform.
  U3 -- the discrimination exhibit: spinor ratio 28->21 == 29->21
        == 16 (indistinguishable); algebra 128 vs 256 (distinct).
  U4 -- the committed formula's three-generation uniform form
        anchored (part4b: the formula + "the source mass m_29").
  K1 -- the odd-layer census: 107 odd layers in [4, 217]; the
        2^107 count stated.
  B1 -- the bilinear identity exact for every d in 1..217.
  P1 -- part4a's "complex minimal spinors" + part4b's basins
        sentence anchored (the two committed structures the fork
        opposed).
  P2 -- 1ah's key sentences anchored (the form-not-value
        selection; the false-dichotomy dissolution; the R-bilinear
        disclosure; the reduced unproved set).
  P3 -- the two net-state markers anchored (1ag(vii) C1; the 1ae
        marker's reduction).
  P4 -- the sibling cascade_spinor_transport.py subprocess exit 0
        at RESULT 15/0.

No data consumed; no number changes.  Grading: U and B exact
arithmetic + committed anchors (U conditional on the committed
formula's form; B carrying the disclosed R-bilinear reading); K
exact counting + the constitutional selection cited as meta.
Sabotage record (full-tree scratchpad copy, at the landing
commit; mid-anchor perturbations): (a) "the source mass
$m_{29}$" -> mid-anchor SAB in the part4b copy tripped U4, 9/1,
exit 1; (b) the B1 parity factor flipped in the SCRATCHPAD COPY
tripped B1, 9/1, exit 1; (c) the paper's false-dichotomy sentence
-> mid-anchor SAB tripped P2, 9/1, exit 1.  Clean baselines 10/0
exit 0 before and after each.  Ten gates (correct at first
draft).  Sibling-anchor note: cascade_spinor_transport.py's
"(C1) the fiber assignment." anchor dropped its period round 137
(the 1ah net-state marker sits inside the bold), disclosed there.
"""
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


print("U -- the uniformity theorem")
sp = [2 ** (d // 2) for d in range(4, 20)]
sp_ratios = [sp[i + 1] // sp[i] for i in range(len(sp) - 1)]
alg_ratios = sorted(set(2 ** (d + 1) // 2 ** d for d in range(4, 19)))
gate("complex spinor ratios alternate 1,2 (never uniform); algebra "
     "uniformly 2",
     sorted(set(sp_ratios)) == [1, 2] and alg_ratios == [2],
     f"spinor {sp_ratios[:6]}..., algebra {alg_ratios}")
real_sp = [1, 2, 4, 4, 8, 8, 8, 8]
rr = [real_sp[i + 1] // real_sp[i] for i in range(7)]
gate("real Bott spinor dims 1,2,4,4,8,8,8,8: ratios not uniform",
     sorted(set(rr)) == [1, 2], f"{rr}")
gate("the discrimination exhibit: spinor 28->21 == 29->21 == 16; "
     "algebra 128 vs 256",
     2 ** (28 // 2) // 2 ** (21 // 2) == 2 ** (29 // 2) // 2 ** (21 // 2) == 16
     and 2 ** 7 == 128 and 2 ** 8 == 256)
part4b = norm(open(PART4B, encoding="utf-8").read())
ok = "m_\\nu(\\text{Gen}~g) = m_{29}\\cdot\\alpha(d_g)/\\chi^{29 - d_g}" in part4b
ok &= "the source mass $m_{29}$" in part4b
gate("the committed formula's uniform three-generation form + 'the source "
     "mass m_29' anchored", ok)

print("K -- the canonicity theorem")
odd = [d for d in range(5, 218, 2)]
gate("107 odd layers in the descent [4, 217]; the 2^107 choice-vector "
     "count -- a single gauge orbit per round 137 F2, arithmetic only "
     "(gate name aligned round 138 F1)", len(odd) == 107, f"{len(odd)}")

print("B -- the bilinear reconciliation")
gate("2^d = (2^floor(d/2))^2 x (2 if d odd), exact for every d in 1..217",
     all(2 ** d == (2 ** (d // 2)) ** 2 * (2 if d % 2 else 1)
         for d in range(1, 218)))

print("P -- the papers and the sibling")
part4a = norm(open(PART4A, encoding="utf-8").read())
ok = "complex minimal spinors" in part4a
ok &= "splitting the spinor bundle into two equal-weight chirality basins" in part4b
gate("the two committed structures the fork opposed, anchored", ok)
paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")
ok = ("What U honestly proves: per-SINGLE-layer non-uniformity of every "
      "spinor fiber" in paper)
ok &= "the fork was a false dichotomy" in paper
ok &= "Disclosed reading (R-bilinear):" in paper
ok &= "K selects nothing; the census stands as arithmetic only." in paper
ok &= "The unproved set remains (v-b), C1, C2, C3" in paper
ok &= "classification without instance" in paper
gate("1ah's REGRADED sentences anchored (round 137: U's honest residue; "
     "K selects nothing; the F3 disclosure; C1 stays open)", ok)
ok = "regraded within the round: ~~CLOSED~~ — the selection legs fell" in paper
ok &= "C1 stays open, reconciled in\nclassification only".replace("\n", " ") in paper
gate("the two REGRADED net-state markers anchored (round 137)", ok)
r = subprocess.run([sys.executable,
                    os.path.join(ROOT, "tools", "research",
                                 "cascade_spinor_transport.py")],
                   capture_output=True, text=True)
gate("the sibling cascade_spinor_transport.py exit 0 at RESULT 15/0",
     r.returncode == 0 and "RESULT: 15 pass / 0 fail" in r.stdout,
     f"exit {r.returncode}")

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (10 gates)")
print("READING (regraded round 137; header tagged round 138 F2): C1")
print("attacked from first principles -- the original claim set follows")
print("as recital, the controlling regrade below.")
print("Uniformity: no minimal-spinor fiber (real or complex) grows")
print("uniformly per layer; the algebra does; the committed formula's")
print("FORM (uniform per-layer exponent across three generations) selects")
print("the algebra -- by form, not the tuned base.  Canonicity: the")
print("algebra ladder is choice-free; a spinor ladder needs 107 unforced")
print("binary choices.  Reconciliation: the algebra IS the spinor")
print("bilinear space (2^d = spinor^2 x factors, exact); amplitudes")
print("travel at the spinor rate, masses and couplings (the committed")
print("formula transports a MASS) at its square.  REGRADED round 137:")
print("both selection legs fell -- the committed instances are all")
print("whole-period (both fibers uniform there; selection by value only)")
print("and the 2^107 count is a gauge orbit.  C1 stays OPEN, reconciled")
print("in classification, selected by value; the unproved set remains")
print("(v-b) + C1 + C2 + C3.  What would close it: an odd-Delta")
print("committed instance, or the formula's derivation.")
sys.exit(0 if n_fail == 0 else 1)
