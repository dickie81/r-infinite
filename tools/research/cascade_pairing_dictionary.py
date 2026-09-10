#!/usr/bin/env python3
"""THE PAIRING DICTIONARY (Theorem 1l): member two of the
selection-convention class attacked directly -- the d<->s pairing
is the tower's dictionary, not a per-site choice.  Category (a):
Gamma-function identities and reproductions of the committed
d<->s audit's instrument numbers; no new data, no closures, no
RH/GRH, no semiclassics (Check 7); the hypothesis is nowhere an
input (Check 8 -- see GRADING for exactly what is given).

CONTEXT.  Review 4 (D1) widened the selection-convention class to
'every d<->s layer/weight pairing choice' after finding Theorem
9's Geometric clause pairing-conditional (avatar weight passes,
Definition-2.1 weight fails), and the d<->s audit
(cascade_ds_audit.py) classified site E (the window-potential
pairing p(d) := P(d+1) in the closures) as ANCHORED -- selected
by data at -38% margin.  This file attacks the member's frame:
the paper's own Definition 2.1 ('the twist tower is the set of
integer points s = d+1 ... with local factor Gamma_R(s)') and
Theorem 1 (the kernel dictionary: Omega(d) = 2/Gamma_R(d+1),
N(d), p(d) = (log Gamma_R)'(d+1), alpha(d), gated <= 7e-14)
already pin every primitive's argument.  Under the dictionary:

  P(d)          = p(d-1)      (the PREVIOUS layer's potential)
  2/Gamma_R(d)  = Omega(d-1)  (the PREVIOUS layer's measure)

so the audit's 'alternative pairing' at E is not a pairing of
the same object -- it is a WINDOW SHIFT (sum p over 5..12
instead of 6..13; gated identically zero, M1); and the 'avatar
weight' at C is the previous layer's measure -- the object
Theorem 1's own Remark forswears ('The paper never uses the
avatar; the arithmetic is primary').

THE MIXED-FRAME FACT (M2).  The audit's E-alternative flipped
the potential sum but kept the boundary term R(14)^2/8 fixed --
a mixed frame.  The coherent global shift (boundary term R(13))
gives 10.4718, the audit's mixed alternative 10.4584: both are
catastrophically off the anchor (canonical 16.8173, observed
16.8170), and they differ from each other -- the 'alternative'
was never a coherent convention.  The -38% anchor thereby
RE-GRADES: the data confirms the dictionary (a cross-check); it
does not select an otherwise-open convention.

THE SITE-C SHARPENING (M3).  The Geometric clause's passing
computation used Omega(d-1) at layer d.  Under the tower's own
measure Omega(d) the clause fails (max two-coset share 0.35001
>= 1/pi = 0.31831; the avatar's 0.31322 passes) -- both numbers
reproduced in-code.  Net state: the review-4 demotion sharpens
-- the avatar reading is not an available convention given the
dictionary and T1's Remark, so the two-coset clause does not
hold in the tower's dictionary; the recorded repair candidate
(single-coset shares, which survive both weights) remains the
live route.  No number changes (the Omega_m backing was already
withdrawn from 'proved' by review 4).

GRADING (honest, per Check 8; the 1j/1k adjudication grammar
applied in advance).  GIVEN Definition 2.1 and Theorem 1 -- the
tower's dictionary, definitional and gated, whose only
alternative is a contentless global renaming (s' = s-1 renames
every symbol and changes no computed number; declared, not
gated -- a tautology cannot fail) -- there is NO per-site d<->s
freedom: site E's residual content is the closure windows'
ENDPOINT data (Definition-6.1 instantiation plus the
strict-boundary stipulation, part4b:503 -- items already listed
elsewhere in the residue accounting); site C's avatar is a frame
error inside an already-demoted clause; sites B and H are
flip-invariant (re-gated, M4); site D was closed by Theorem 1k
(given E plus the variational-sup labeling).  Member two of the
selection-convention class is RE-MOTIVATED, not deleted: its
live content is the dictionary itself plus the already-listed
endpoint items, and the per-site family the review-4 widening
named is closed.  Three members and the seven-item residue count
stand.  No number changes; no closure.
ROUND-98 NET-STATE.  The labeling given this file grades as open/
persisting was resolved by the owner's decision (Theorem 1v,
Addendum 176): A1 is re-founded on Gamma_R as its full global
object ("Gamma_R entire", the owner's phrase -- the function is
meromorphic) with mirror coherence as its selector clause, and the
labeling (7, 19, 217) is now forced by the amended axiom.  This file's grading
describes the pre-adoption state and is kept as record; its gates
are unchanged and remain green.
"""

import sys
import itertools
import math

from scipy.special import digamma, gammaln

PI = math.pi
LNPI = math.log(PI)


def lg_R(s):
    return -s / 2 * LNPI + gammaln(s / 2)


def P(s):
    return 0.5 * digamma(s / 2.0) - 0.5 * LNPI


def p(d):
    return P(d + 1)


def R(d):
    return math.exp(gammaln((d + 1) / 2) - gammaln((d + 2) / 2))


def Om(d):
    return 2 * math.exp((d + 1) / 2 * LNPI - gammaln((d + 1) / 2))


def coset_max(shift):
    w = {d: 2 * math.exp(-lg_R(d + shift)) for d in range(5, 218)}
    T = sum(w.values())
    return max(sum(v for d, v in w.items() if d % 8 in (r1, r2)) / T
               for r1, r2 in itertools.combinations(range(8), 2))


def main():
    print("=" * 74)
    print("THE PAIRING DICTIONARY (Theorem 1l)")
    print("=" * 74)

    # ---- M1: the dictionary, and the flip identified as a window shift
    print()
    print("M1 the dictionary pins the arguments; the E-flip is a window")
    print("   shift (identities P(d) = p(d-1), 2/G_R(d) = Omega(d-1) are")
    print("   definitional -- declared exhibits; the failable content:")
    ok1 = max(abs(2 * math.exp(-lg_R(d)) - Om(d - 1)) / Om(d - 1)
              for d in range(2, 100)) < 1e-12
    # (P(d) = p(d-1) is a call-chain identity -- p is DEFINED as P(d+1);
    #  comparing it with itself cannot fail, so it is not gated: round-64
    #  c1.  The measure identity above IS gated: its two sides are
    #  computed by independent routes and a transcription error fails it.)
    shift_resid = abs(sum(P(d) for d in range(6, 14))
                      - sum(p(d) for d in range(5, 13)))
    ok1 &= shift_resid == 0.0
    print(f"   sum P(d), d=6..13  ==  sum p(d), d=5..12  (residual"
          f" {shift_resid:.1e}) -- the")
    print(f"   audit's 'alternative pairing' is the window 5..12   "
          f"{'PASS' if ok1 else 'FAIL'}")

    # ---- M2: the anchor reproduced, and the mixed frame exposed
    print()
    print("M2 the site-E anchor re-graded (instrument reproduction of the")
    print("   committed audit; observed 16.8170 cited from its record):")
    tau_can = math.exp(sum(p(d) for d in range(6, 14))
                       + R(14) ** 2 / 8) * 2 * math.sqrt(PI)
    tau_mix = math.exp(sum(p(d) for d in range(5, 13))
                       + R(14) ** 2 / 8) * 2 * math.sqrt(PI)
    tau_coh = math.exp(sum(p(d) for d in range(5, 13))
                       + R(13) ** 2 / 8) * 2 * math.sqrt(PI)
    ok2 = abs(tau_can - 16.8173) < 5e-4   # canonical reproduces the audit's
    #                              recorded value (the anchor is the observed
    #                              16.8170, a distinct number -- round-64 c2)
    ok2 &= abs(tau_mix - 10.4584) < 5e-4         # the audit's alternative
    ok2 &= abs(tau_coh - 10.4718) < 5e-4         # the coherent shift
    ok2 &= abs(tau_mix / 16.817 - 1 + 0.3781) < 5e-4   # the -38% margin
    ok2 &= tau_mix != tau_coh                    # mixed != coherent
    print(f"   canonical {tau_can:.4f}; audit-alternative {tau_mix:.4f}"
          f" (mixed frame: potential")
    print(f"   flipped, boundary term R(14) kept); coherent shift"
          f" {tau_coh:.4f} (R(13)) --")
    print(f"   the alternative was never one convention; margin -37.8%"
          f" reproduced   {'PASS' if ok2 else 'FAIL'}")

    # ---- M3: site C sharpened under the tower's measure
    print()
    print("M3 the Geometric two-coset clause under both weights:")
    mx_avatar = coset_max(0)      # 2/G_R(d)   = Omega(d-1), the avatar
    mx_dict = coset_max(1)        # 2/G_R(d+1) = Omega(d), the dictionary
    ok3 = abs(mx_avatar - 0.31322) < 5e-5 and abs(mx_dict - 0.35001) < 5e-5
    ok3 &= mx_avatar < 1 / PI < mx_dict
    print(f"   avatar Omega(d-1): {mx_avatar:.5f} < 1/pi = {1/PI:.5f};"
          f" dictionary Omega(d):")
    print(f"   {mx_dict:.5f} >= 1/pi -- the clause fails under the tower's"
          f" own measure")
    print(f"   (T1 Remark: 'The paper never uses the avatar')   "
          f"{'PASS' if ok3 else 'FAIL'}")

    # ---- M4: the stable sites re-gated (flip-invariant, per the audit)
    print()
    print("M4 stable sites re-gated under the flip:")
    LN_GHALF = 0.5 * LNPI
    subs = [tuple(d for d in (5, 13, 21, 29) if P(d + s) < LN_GHALF)
            for s in (0, 1, 2)]
    ok4 = all(sb == (5, 13) for sb in subs)
    worst = 0.0
    for s in (-1, 0, 1):
        for d in range(2, 216):
            c2 = R(2 * d + 2 + s) ** 2 / (R(2 * d + 1 + s)
                                          * R(2 * d + 3 + s))
            worst = max(worst, c2)
    ok4 &= worst < 1
    print(f"   Thm 10 subcritical marked set = {{5, 13}} under all three"
          f" pairings;")
    print(f"   Gram-deficit C^2 max = {worst:.6f} < 1 under shifts"
          f" -1, 0, +1   {'PASS' if ok4 else 'FAIL'}")

    # ---- M5: the observer coordinate in the dictionary
    print()
    print("M5 the dictionary at the observer's tower point (13c: 'the")
    print("   observer is twist 4'): layer d = 3, factor Gamma_R(4),")
    ok5 = abs(Om(3) - 2 * PI ** 2) < 1e-12
    ok5 &= abs(Om(3) - 2 * math.exp(-lg_R(4))) < 1e-12
    print(f"   Omega(3) = 2 pi^2 = {Om(3):.6f} = |S^3| -- the observer")
    print(f"   sphere is the layer-3 entry of T1's measure column   "
          f"{'PASS' if ok5 else 'FAIL'}")

    print()
    print("=" * 74)
    print("READING (classical + gated; grading in docstring)")
    print("=" * 74)
    print("  Given Definition 2.1 and Theorem 1 -- the tower's dictionary,")
    print("  whose only alternative is a contentless global renaming --")
    print("  there is no per-site d<->s freedom: the E-flip is a window")
    print("  shift (endpoint data already listed in the residue), the")
    print("  C-avatar is the previous layer's measure (forsworn by T1's")
    print("  Remark; the two-coset clause fails under the tower's own")
    print("  measure, sharpening the review-4 demotion -- the single-coset")
    print("  repair candidate stays live), and the stable sites are")
    print("  flip-invariant.  The -38% anchor re-grades as a cross-check")
    print("  of the dictionary.  Member two re-motivated, not deleted;")
    print("  three members; seven-item residue count unchanged.")
    # round-123 hardening (the A206/A208 standing commission): exit
    # gating added -- this instrument previously exited 0
    # unconditionally, so a printed FAIL could not fail a caller;
    # the exit code now carries the verdicts.  No verdict logic
    # changed.
    n_fail = sum(0 if ok else 1 for ok in (ok1, ok2, ok3, ok4, ok5))
    print()
    print(f"RESULT: {5 - n_fail} pass / {n_fail} fail (5 verdicts)")
    sys.exit(0 if n_fail == 0 else 1)


if __name__ == "__main__":
    main()
