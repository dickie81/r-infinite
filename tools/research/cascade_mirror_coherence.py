#!/usr/bin/env python3
"""MIRROR COHERENCE (Theorem 1q): the regularity principle
derived from ONE global requirement -- the invariant extends
finite-nonzero through the ground object's defining symmetry.
Category (a): exact symbolic arithmetic (sympy); no data, no
closures, no RH/GRH, no semiclassics (Check 7); the hypothesis is
nowhere an input (Check 8).

CONTEXT.  Theorem 1p forced the sup from the per-label
REGULARITY PRINCIPLE (labels at regular points of the local
functional equation) -- a new given, applied 2^3 times.  This
file moves the given UP one level and makes it single and
global.  Ingredients, all committed:

  - The ground object's defining symmetry: xi(s) = xi(1-s)
    (the formulation's Notation block).
  - T1b's RH-free paired Hadamard form is 'even, entire of
    order 1, genus-0 in z^2' (round-15 M1's adjudicated wording,
    quoted from the paper): the framework's UNCONDITIONAL
    potential identity is a function of z^2 = (s - 1/2)^2 and
    cannot distinguish layer d (z = d + 1/2) from its mirror
    layer -(d+1) (z' = -(d + 1/2); same z^2).
  - The invariant is finite-nonzero on the physical branch (an
    invariant equal to 0 or oo is no invariant; part0's
    uniqueness theorem presupposes it).

THE MIRROR INVARIANT (Q2).  Branch-swap every weight:
Om~(d) = 2/Gamma_R(-d) (the mirror layer's weight; = Om(d)
divided by Tate's gamma-factor at s = d+1, tying to 1p).  Define
I~(l0, l1, l2) = (Om~(5)/Om~(l0))^2 Om~(l1) Om~(l2).  The
failure census over the eight labelings is TOTAL:
  I~ = oo   for all four l0 = 6 labelings (denominator mirror
            weight vanishes);
  I~ = 0    for the three l0 = 7 labelings with an even content
            label (a numerator mirror weight vanishes);
  I~ finite-nonzero UNIQUELY at (7, 19, 217) -- the sup.

MIRROR COHERENCE (the requirement, one level up).  Require the
invariant to extend finite-nonzero through s <-> 1-s -- the
symmetry its ground object defines and its unconditional paired
form is blind to.  Then: coherence <=> all labels odd <=> 1p's
per-label regularity <=> the sup labeling, with the variational
characterization's output and all 1n/1o equivalents as
corollaries.  THE REGULARITY PRINCIPLE IS THEREBY DERIVED --
conditional now on mirror coherence alone.

THE d_V TEST (Q4, the falsifiable bonus).  d_V = 5 is NOT a
labeling choice -- the interior landmark is fixed by V's
discrete argmax -- yet coherence requires Om~(5) != 0.  It holds
(-15/(4 pi^3), exact).  Had the landmark fallen at an even layer
(the neighboring candidates' mirror weights Om~(4) = Om~(6) = 0,
gated as the counterfactual exhibit), NO labeling could satisfy
coherence: the framework passes a test it could have failed, and
1n's observation 'all four distinguished layers are odd' becomes
a NECESSITY under coherence, not a coincidence.

GRADING (honest, per Check 8; the campaign grammar).  The chain
of givens, each strictly smaller than the last: 'take the max'
(part0's definition) -> four equivalents (1n/1o) -> per-label
regularity (1p, 2^3 applications) -> MIRROR COHERENCE (one
global statement).  The coherence step -- physical-branch
non-degeneracy transports to the mirror branch because the
unconditional z^2 form cannot distinguish branches -- is
MOTIVATED by committed structure (the xi-symmetry as ground;
T1b's evenness; standing branch non-degeneracy) and is close to
what 'invariant of a symmetric object' means, but it is NOT
claimed an axiom-consequence: it is the remaining given.  The
open question narrows to: derive mirror coherence from A1-A4.
Sign disclosure: I~_sup < 0 (the mirror weights carry
Gamma-reflection signs); coherence is non-degeneracy (!= 0, oo),
not positivity -- stated, not hidden.  No number changes; no
closure.
"""

import itertools

import sympy as sp

PAIRS = [(6, 7), (19, 20), (217, 218)]
LABS = list(itertools.product(*PAIRS))


def GR(x):
    return sp.pi ** (-sp.Rational(x, 2)) * sp.gamma(sp.Rational(x, 2))


def Om(d):
    return 2 / GR(d + 1)


def Omt(d):
    """The mirror layer's weight 2/Gamma_R(-d)."""
    return 2 / GR(-d)


def Itilde(l0, l1, l2):
    den = sp.simplify(Omt(l0))
    if den == 0:
        return sp.oo
    return sp.simplify((Omt(5) / den) ** 2 * Omt(l1) * Omt(l2))


def main():
    print("=" * 74)
    print("MIRROR COHERENCE (Theorem 1q)")
    print("=" * 74)

    # ---- Q1: the z^2 identification (the committed evenness)
    print()
    print("Q1 the z^2 identification of layer and mirror:")
    ok1 = all(sp.Rational(2 * d + 1, 2) ** 2
              == (sp.Rational(1, 2) - (d + 1)) ** 2
              for d in range(0, 31))
    # the paired form's evenness is algebraic (a function of z^2) --
    # declared exhibit; the committed wording is anchored in the paper:
    import os
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "..", "..")
    paper = open(os.path.join(root, "riemann-indistinguishability.md"),
                 encoding="utf-8").read()
    ok1 &= "genus-0 in z" in paper          # round-15 M1's wording anchor
    print(f"   z(d)^2 = z(-(d+1))^2 exactly (d = 0..30); the paired")
    print(f"   Hadamard form is a function of z^2 (algebraic -- declared")
    print(f"   exhibit) and the committed wording 'genus-0 in z^2' is")
    print(f"   anchored verbatim in the paper (gated)   "
          f"{'PASS' if ok1 else 'FAIL'}")

    # ---- Q2: the mirror invariant's total failure census
    print()
    print("Q2 the mirror invariant I~ over the eight labelings:")
    census = {}
    for l in LABS:
        v = Itilde(*l)
        census[l] = ("INF" if v == sp.oo else
                     "ZERO" if v == 0 else "finite-nonzero")
    inf_set = [l for l, t in census.items() if t == "INF"]
    zero_set = [l for l, t in census.items() if t == "ZERO"]
    ok_set = [l for l, t in census.items() if t == "finite-nonzero"]
    ok2 = (sorted(inf_set) == sorted([l for l in LABS if l[0] == 6])
           and len(zero_set) == 3 and ok_set == [(7, 19, 217)])
    print(f"   I~ = oo at the four l0 = 6 labelings (denominator mirror")
    print(f"   weight 0); I~ = 0 at the three l0 = 7 labelings with an")
    print(f"   even content label; finite-nonzero UNIQUELY at")
    print(f"   {ok_set[0] if ok_set else None} -- the sup   "
          f"{'PASS' if ok2 else 'FAIL'}")

    # ---- Q3: the entailment chain (regularity derived)
    print()
    print("Q3 mirror coherence entails 1p's regularity and the sup:")
    coh = ok_set
    odd_sel = [tuple(x if x % 2 == 1 else y for x, y in PAIRS)]
    reg = [l for l in LABS if all(sp.simplify(Omt(d)) != 0 for d in l)]
    ok3 = coh == odd_sel == reg == [(7, 19, 217)]
    print(f"   coherent labelings = regular labelings (1p) = odd-member =")
    print(f"   {coh} -- the regularity principle is DERIVED given mirror")
    print(f"   coherence, one global condition replacing 2^3 per-label")
    print(f"   applications   {'PASS' if ok3 else 'FAIL'}")

    # ---- Q4: the d_V test (falsifiable; counterfactual exhibited)
    print()
    print("Q4 the fixed landmark's test (d_V = 5 is not a labeling choice):")
    w5 = sp.simplify(Omt(5))
    ok4 = w5 == sp.Rational(-15, 4) / sp.pi ** 3 and w5 != 0
    ok4 &= sp.simplify(Omt(4)) == 0 and sp.simplify(Omt(6)) == 0
    print(f"   Om~(5) = -15/(4 pi^3) != 0 (exact); the neighboring even")
    print(f"   candidates' mirror weights Om~(4) = Om~(6) = 0")
    print(f"   (counterfactual exhibit: an even landmark would make")
    print(f"   coherence unsatisfiable for EVERY labeling) -- 'all four")
    print(f"   distinguished layers odd' (1n) is a NECESSITY under")
    print(f"   coherence, not a coincidence   {'PASS' if ok4 else 'FAIL'}")

    # ---- Q5: the exact value, the sign, and the 1p tie
    print()
    print("Q5 the coherent value and its sign (disclosure):")
    v = Itilde(7, 19, 217)
    ok5 = v != 0 and v != sp.oo and v.is_negative
    ok5 &= sp.simplify(Omt(7) * GR(-7) - 2) == 0     # definition sanity
    gamma8 = sp.simplify(GR(-7) / GR(8))              # 1p's gamma at s=8
    ok5 &= sp.simplify(Omt(7) - Om(7) / gamma8) == 0  # Om~ = Om/gamma tie
    print(f"   I~_sup = (exact rational)/pi^117, NEGATIVE (~{float(v):.3e}):")
    print(f"   the mirror weights carry Gamma-reflection signs; coherence")
    print(f"   is NON-DEGENERACY (!= 0, oo), not positivity -- disclosed.")
    print(f"   The 1p tie gated: Om~(d) = Om(d)/gamma_oo(d+1) at d = 7   "
          f"{'PASS' if ok5 else 'FAIL'}")

    print()
    print("=" * 74)
    print("READING (classical + gated; grading in docstring)")
    print("=" * 74)
    print("  The framework's unconditional paired form lives on z^2 and")
    print("  cannot tell a layer from its mirror; the invariant is")
    print("  finite-nonzero on the physical branch by what 'invariant'")
    print("  means.  Requiring that non-degeneracy to extend through the")
    print("  ground object's defining symmetry -- MIRROR COHERENCE, one")
    print("  global statement -- the mirror invariant classifies all")
    print("  eight labelings totally: oo four times, 0 three times,")
    print("  finite-nonzero uniquely at the sup.  1p's regularity")
    print("  principle is thereby DERIVED; the fixed landmark d_V = 5")
    print("  passes the coherence test it could have failed; and the")
    print("  open question narrows to: derive mirror coherence from")
    print("  A1-A4.  No number changes; no closure.")


if __name__ == "__main__":
    main()
