#!/usr/bin/env python3
"""THE RIEMANN KERNEL (Theorem 1v): A1 re-founded on Gamma_R
entire, by the owner's decision (round 98) -- the foundational
choice Theorem 1u stated is now made, and the boundary labeling is
FORCED by the amended axiom's non-degeneracy clause.  Category (a)
plus one axiom-adoption record; no data, no RH/GRH, no
semiclassics (Check 7); the PHYSICAL hypothesis is untouched
(Check 8) -- this is a math-side re-founding of the formulation's
skeleton.

CONTEXT.  1u classified the regularity/coherence given as
irreducible relative to A1-A4 as then committed (their asserted
content lattice-only; the given's condition at Gamma_R's negative
arguments) and transformed the open question into a foundational
choice: is the weight function's global identity axiom content?
The owner has decided: THE FRAMEWORK FOLLOWS RIEMANN.  The kernel
is Gamma_R as its full global object ("Gamma_R entire", the
owner's phrase -- "entire" in the sense of IN ITS ENTIRETY; the
function itself is meromorphic, its poles load-bearing) -- the
continuation and functional equation Riemann added to Euler's
value table -- with mirror coherence as its non-degeneracy clause,
worded as the SELECTOR (round-98 F1: the first wording constrained
the variationally-defined invariant and was entailed; the clause
now states the labeling selection explicitly).

  V1 THE AMENDMENT, ANCHORED AND CONTAINED.  The amended A1
     carries the re-founding note, the kernel-object sentence
     (xi's functional equation named), and the non-degeneracy
     clause (anchored verbatim); the state-space and dynamics
     sentences of the old A1 survive unchanged (anchored); and
     A2-A4 are UNTOUCHED -- the block from "**A2" onward is
     byte-identical to the embedded pre-adoption text (gated by
     string equality, so any drift or collateral edit fails).
  V2 THE FORCING.  Under the amended A1, the labeling is DERIVED:
     the coherence clause admits exactly one labeling of the
     eight -- (7, 19, 217) -- 1q's exact-value census re-gated
     here (finite-nonzero uniquely at the sup; zero at three;
     infinite at one; indeterminate at three).
  V3 THE COROLLARY CHAIN.  The five prior faces -- argmax I,
     argmin S_dS, the odd-member rule, the unique
     zeta-mirror-nonzero labeling, per-label regularity --
     coincide with the forced labeling (re-gated): what 1n/1o/1p
     recorded as equivalents-with-the-forcing-open are now
     corollaries of the clause.
  V4 NO EMPIRICAL CONTENT.  The adoption changes no number: the
     invariant re-derived from its definition to twelve digits
     (1.09894538952e-120, half-ULP gate); the observer-corrected
     ratio (2/pi) I = 6.996e-121 unchanged.  No prediction moves.
  V5 THE LEDGER AND THE RESIDUE.  The cost stated in the open on
     every carrying surface (anchored: the formulation's A1 cost
     ledger; part0's adoption sentence); what does NOT resolve
     enumerated and anchored: the site-E pairing (1k's first
     given), the pairing-act (Door-4 bookkeeping per 1t), A3's
     underived rules ("the increment and per-period rules are
     underived" -- anchored in the amended block itself).  Honest
     falsifier: the adoption adds no empirical content, so it is
     tested exactly where the framework is; any future committed
     derivation of the clause from a weaker kernel makes the
     adoption redundant, to be recorded as such.
"""

import itertools
import math
import os

import mpmath as mp
import sympy as sp
from scipy.special import gammaln

mp.mp.dps = 30

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PI = math.pi
PAIRS = [(6, 7), (19, 20), (217, 218)]
LABS = list(itertools.product(*PAIRS))
GAMMA_GRAM = 0.02108

# the pre-adoption block from "**A2" onward, byte-exact (commit 6402a62):
A2_TO_END = "**A2 (Local-constant calculus).** Every multiplicative factor attached to a descent is drawn\nfrom the local constants of the adelic structure:\n\n| Constant | Identity | Arithmetic home |\n|---|---|---|\n| χ = 2 | \\|μ(ℝ)\\| | torsion of the real units |\n| Γ(½) = √π | Γ_ℝ critical value | the functional equation's symmetry point |\n| 2π | χ·Γ(½)² | Tate's self-dual period at the real place |\n| ½ | half-argument of Γ_ℝ | the Gaussian, Tate's self-dual test function |\n| mod-8 grading | Brauer–Wall group BW(ℝ) ≅ ℤ/8 | graded Brauer group of the real place (Wall 1964) — the arithmetic avatar of Bott/Clifford periodicity |\n| N_c = 3 = 2^(v₂(12))−1 | Radon–Hurwitz count | a 2-adic invariant (value depends only on v₂) |\n| cos(π/6) | weight–root angle of ℤ[ω] | ring of integers of ℚ(ζ₃) |\n| phases i, ζ₈ | quaternionic frame, Bott | the cyclotomic tower ζ₂, ζ₃, ζ₄, ζ₈ |\n\n**A3 (Assignment rules).** Which constant attaches where: the source-selection flags (P, L, G)\nas ξ-occupancy functors; the increment rule (corrections attach once, at sub-lead); source\nlayers at the analytic features of Γ_ℝ; the per-Bott-period attachment below the phase\ntransition. *This is the load-bearing axiom.* Partial derivation exists (Addendum 12: the\nflags recovered 9/9 from ξ's factorization); the increment and per-period rules are underived.\n\n**A4 (Measurement).** Measurement records the typical value of a Gaussian mode (weight\ne^(±½) per measured mode — lemma S4, anchored by equipartition); projection is along root\nframes (lemma S5).\n\n"


def Om(d):
    return 2 * math.exp((d + 1) / 2 * math.log(PI) - gammaln((d + 1) / 2))


def GR(x):
    return sp.pi ** (-sp.Rational(x, 2)) * sp.gamma(sp.Rational(x, 2))


def Omt(d):
    return 2 / GR(-d)


def classify(l0, l1, l2):
    den = sp.simplify(Omt(l0))
    nz = [d for d in (l1, l2) if sp.simplify(Omt(d)) == 0]
    if den == 0 and nz:
        return "INDETERMINATE"
    if den == 0:
        return "INF"
    if nz:
        return "ZERO"
    return "finite-nonzero"


def main():
    print("=" * 74)
    print("THE RIEMANN KERNEL (Theorem 1v)")
    print("=" * 74)

    form = open(os.path.join(ROOT, "cascade-riemann-formulation.md"),
                encoding="utf-8").read()
    part0 = open(os.path.join(ROOT, "src", "cascade-series-part0.tex"),
                 encoding="utf-8").read().replace("\n", " ")
    paper = open(os.path.join(ROOT, "riemann-indistinguishability.md"),
                 encoding="utf-8").read().replace("\n", " ")

    i0 = form.find("## 1. The axiom system")
    i1 = form.find("## 2. The theorems")
    block = form[i0:i1]

    # ---- V1: the amendment anchored; A2-A4 contained
    print()
    print("V1 the amendment anchored; A2-A4 byte-identical:")
    ok1 = "re-founded on the Riemann kernel by the owner's decision" in block
    ok1 &= "Non-degeneracy clause (mirror coherence) — the boundary-labeling selector:" \
        in block
    ok1 &= "the labeling\nis the one at which the branch-swapped invariant" \
        in block or "the labeling is the one at which" in block.replace("\n", " ")
    #      round-98 F1: the SELECTOR sentence anchored -- the clause
    #      states the selection, not an entailed property of the
    #      variationally-defined invariant
    ok1 &= "ξ(s) = ½s(s−1)Γ_ℝ(s)ζ(s), ξ(s) = ξ(1−s)" in block
    ok1 &= "The state space is the descent lattice" in block
    ok1 &= "the unique Gaussian elastic action with bond compliance" in block
    ok1 &= "Cost ledger, stated in the open" in block
    ia2 = block.find("**A2")
    ok1 &= ia2 > 0 and block[ia2:] == A2_TO_END
    print("   the re-founding note, the kernel-object sentence (xi's")
    print("   functional equation named), the coherence clause, the old")
    print("   A1's surviving sentences, and the cost ledger all anchored;")
    print("   the block from **A2 onward is byte-identical to the embedded")
    print("   pre-adoption text (any collateral edit fails)   "
          + ("PASS" if ok1 else "FAIL"))

    # ---- V2: the forcing under the amended A1
    print()
    print("V2 the forcing: the clause admits exactly one labeling:")
    census = {l: classify(*l) for l in LABS}
    ok_set = [l for l, t in census.items() if t == "finite-nonzero"]
    ok2 = (ok_set == [(7, 19, 217)]
           and sorted(census.values()).count("ZERO") == 3
           and sorted(census.values()).count("INF") == 1
           and sorted(census.values()).count("INDETERMINATE") == 3)
    print("   the branch-swapped invariant evaluates finite-nonzero")
    print(f"   uniquely at {ok_set[0] if ok_set else None} (zero x3, infinite")
    print("   x1, indeterminate x3 -- 1q's census re-gated): the labeling")
    print("   is DERIVED from the amended axiom   "
          + ("PASS" if ok2 else "FAIL"))

    # ---- V3: the corollary chain
    print()
    print("V3 the five prior faces are now corollaries:")
    vals = {l: (Om(5) / Om(l[0])) ** 2 * Om(l[1]) * Om(l[2]) for l in LABS}
    sup = max(vals, key=vals.get)
    S = {l: 24 * PI ** 2 / ((2 / PI) * math.exp(GAMMA_GRAM) * vals[l])
         for l in LABS}
    smin = min(S, key=S.get)
    odd = tuple(x if x % 2 == 1 else y for x, y in PAIRS)
    zmir = [l for l in LABS if all(sp.zeta(-d) != 0 for d in l)]
    reg = [l for l in LABS if all(sp.simplify(Omt(d)) != 0 for d in l)]
    ok3 = sup == smin == odd == (7, 19, 217) and zmir == reg == [sup] \
        and ok_set == [sup]
    print("   argmax I = argmin S = odd rule = zeta-mirror survivor =")
    print(f"   regular = coherent = {sup}: the 1n/1o/1p equivalents follow")
    print("   from the clause as corollaries   " + ("PASS" if ok3 else "FAIL"))

    # ---- V4: no empirical content
    print()
    print("V4 no number changes:")

    def om_mp(d):
        return 2 * mp.pi ** ((d + 1) / mp.mpf(2)) \
            / mp.gamma((d + 1) / mp.mpf(2))

    I_def = (om_mp(5) / om_mp(7)) ** 2 * om_mp(19) * om_mp(217)
    ok4 = abs(I_def - mp.mpf("1.09894538952e-120")) < mp.mpf("5e-132")
    ok4 &= abs(2 / mp.pi * I_def - mp.mpf("6.996e-121")) < mp.mpf("5e-125")
    print("   I = 1.09894538952e-120 (twelve digits, half-ULP gate) and")
    print("   (2/pi) I = 6.996e-121 unchanged: the adoption buys")
    print("   derivational structure, not predictions   "
          + ("PASS" if ok4 else "FAIL"))

    # ---- V5: the ledger and the residue
    print()
    print("V5 the cost ledger and the unresolved residue, anchored:")
    ok5 = "the axiom thereby enlarges from a" in block
    ok5 &= "That choice has now been made" in part0
    ok5 &= "adds no empirical content and changes no number" in part0
    ok5 &= "the increment and per-period rules are underived" in block
    ok5 &= "the site-E pairing plus the" in paper          # 1k first given
    ok5 &= "is Door-4 bookkeeping" in paper                # 1t's residue
    print("   the formulation's cost ledger and part0's adoption sentence")
    print("   anchored; the residue enumerated and anchored (the site-E")
    print("   pairing; the pairing-act as Door-4 bookkeeping; A3's")
    print("   underived rules -- in the amended block itself).  Falsifier:")
    print("   no empirical content added; a future derivation of the")
    print("   clause from a weaker kernel makes the adoption redundant   "
          + ("PASS" if ok5 else "FAIL"))

    print()
    print("=" * 74)
    print("READING (the adoption record; grading in docstring)")
    print("=" * 74)
    print("  The framework follows Riemann: the kernel is the global")
    print("  meromorphic function with its functional equation -- the")
    print("  object Riemann added to Euler's value table -- and mirror")
    print("  coherence is its non-degeneracy clause.  The boundary")
    print("  labeling is thereby forced, the five prior faces becoming")
    print("  corollaries; the cost (one enlarged axiom) is on the ledger;")
    print("  no number changes; the physical hypothesis is untouched.")


if __name__ == "__main__":
    main()
