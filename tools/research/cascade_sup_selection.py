#!/usr/bin/env python3
"""THE SUP'S EXACT EQUIVALENTS (Theorem 1n): part0's open
max-over-min question attacked -- the anchor narrowed, not
discharged.  Category (a): Gamma-function arithmetic plus algebra
on cascade-derived relations (S = A/4 is the cascade's own,
Part II=III Sec. 7, derived without QFT on curved spacetime or
Bogoliubov transformations; the de Sitter algebra S = 24 pi^2
M^4/rho_Lambda uses Part I's Friedmann/de-Sitter relations and
the w = -1 theorem); no data, no closures, no RH/GRH, no
semiclassics (Check 7); the hypothesis is nowhere an input
(Check 8 -- the equivalences are statements about the eight
labelings' arithmetic, not about the observer).

CONTEXT.  part0's variational theorem defines the invariant as
the SUP of the bilinear form over the eight boundary labelings
(unique at (7,19,217)); its max-over-min remark grades the choice
honestly: '...A principled derivation of max from the cascade's
own axioms -- connecting the supremum to a distinguished
quantity such as an entropy, a boundary area, or a
characteristic of the observer's layer -- remains open.'  This
is Theorem 1k's second given.  This file establishes three exact
reformulations and one equivalence of the sup, each gated:

  (1) PARITY: the sup labels (7, 19, 217) are exactly the ODD
      members of the three straddling pairs; the inf labels
      (6, 20, 218) exactly the EVEN members.  Each consecutive
      pair has exactly one odd member, so odd-selection is a
      uniform, total rule -- and it reproduces the sup.
  (2) OBSTRUCTION: in the tower's dictionary (layer d <-> S^d,
      Theorem 1l), chi(S^d) = 1 + (-1)^d: the sup labels'
      spheres are Euler-null (chi = 0, odd-dimensional --
      nowhere-zero fields exist), the inf labels' spheres carry
      chi = 2 -- the SAME chi(S^{2n}) = 2 that is the chirality
      factor of the obstruction toll (Theorem 1m; part0's shift
      family 'chi = chi(S^{2n}) = 2').  All FOUR distinguished
      layers {5, 7, 19, 217} are odd: the entire invariant is
      evaluated on Euler-null spheres.
  (3) THE HORIZON BUDGET: S_dS = 24 pi^2 M^4/rho_Lambda is
      strictly decreasing in the invariant (rho = (2/pi)
      e^{0.02108} I, Part I's closure), so over the eight
      labelings SUP I = MIN horizon entropy = MIN boundary area:
      the sup is the labeling with the SMALLEST asymptotic
      information budget (3.315e122 nats = 4.783e122 bits; the
      inf labeling's budget is 10.76x larger -- the round-62
      ratio as entropy stakes).  This is the exact connection
      part0's open clause requested ('an entropy, a boundary
      area'), with the direction stated: the sup MINIMIZES the
      horizon budget.
  Plus the farther-integer re-description (already printed by
  tools/verifiers/verify_continuous_boundary.py section [9]) and
  the window-proximal one (in-or-nearest [7,19]) -- verified.

DISTINCTNESS AND HONESTY (W5).  The characterizations are
DISTINCT principles that AGREE at the actual crossings: a
synthetic crossing at 20.5 (between even 20 and odd 21) would
separate content-floor (20) from odd-member (21) -- gated as a
clearly-labeled synthetic exhibit.  The agreement at the three
actual crossings decomposes as: content crossings have ODD
integer parts (19, 217), and the scale crossing has EVEN integer
part (6) AND Omega_7 < Omega_6 -- three parity facts plus one
inequality, each gated separately.  Fixed-target disclosure: the
characterizations were found by inspection knowing the sup.

GRADING (honest, per Check 8; the campaign grammar).  NOTHING
here forces the sup: each reformulation is an exact equivalence
converting 'max over min' into a named structural statement, and
WHY odd/Euler-null/minimal-budget remains the residual selection
content.  What changes: part0's open clause 'connecting the
supremum to ... an entropy, a boundary area' is DISCHARGED AS AN
EQUIVALENCE (with direction: minimal), and the 1k second given
is RE-MOTIVATED -- from a bare max convention to the
odd-sphere/minimal-horizon-budget selection, tied to the
load-bearing chi machinery.  The forcing question stays OPEN and
part0's remark keeps 'remains open'.  No number changes; no
closure.
"""

import itertools
import math

from scipy.optimize import brentq
from scipy.special import digamma, gammaln

PI = math.pi
GAMMA_GRAM = 0.02108          # Part I's Gram exponent


def P(s):
    return 0.5 * digamma(s / 2.0) - 0.5 * math.log(PI)


def p(d):
    return P(d + 1)


def Om(d):
    return 2 * math.exp((d + 1) / 2 * math.log(PI) - gammaln((d + 1) / 2))


def I(l0, l1, l2):
    return (Om(5) / Om(l0)) ** 2 * Om(l1) * Om(l2)


def chi(d):
    """Euler characteristic of S^d."""
    return 1 + (-1) ** d


PAIRS = [(6, 7), (19, 20), (217, 218)]
LABS = list(itertools.product(*PAIRS))


def main():
    print("=" * 74)
    print("THE SUP'S EXACT EQUIVALENTS (Theorem 1n)")
    print("=" * 74)

    vals = {l: I(*l) for l in LABS}
    sup = max(vals, key=vals.get)
    inf = min(vals, key=vals.get)

    # ---- W1: parity -- the sup is the odd member of every pair
    print()
    print("W1 parity: the sup labels are the odd members, the inf the even:")
    c0 = brentq(lambda d: p(d), 5.0, 10.0)
    c1 = brentq(lambda d: p(d) - 0.5 * math.log(PI), 15.0, 25.0)
    c2 = brentq(lambda d: p(d) - math.sqrt(PI), 200.0, 250.0)
    odd = tuple(x if x % 2 == 1 else y for x, y in PAIRS)
    even = tuple(x if x % 2 == 0 else y for x, y in PAIRS)
    ok1 = sup == (7, 19, 217) == odd and inf == (6, 20, 218) == even
    ok1 &= abs(c0 - 6.2569) < 5e-4 and abs(c1 - 19.7308) < 5e-4 \
        and abs(c2 - 217.6267) < 5e-4
    print(f"   crossings {c0:.4f}, {c1:.4f}, {c2:.4f}; argmax I = {sup} ="
          f" odd members;")
    print(f"   argmin I = {inf} = even members (each consecutive pair has")
    print(f"   exactly one odd member: odd-selection is total and uniform)   "
          f"{'PASS' if ok1 else 'FAIL'}")

    # ---- W2: obstruction -- Euler-null spheres carry the invariant
    print()
    print("W2 obstruction: chi(S^d) on the labels (dictionary d <-> S^d):")
    ok2 = all(chi(d) == 0 for d in sup) and all(chi(d) == 2 for d in inf)
    ok2 &= all(d % 2 == 1 for d in (5, 7, 19, 217))    # all four distinguished
    print(f"   sup labels chi = {[chi(d) for d in sup]} (Euler-null,")
    print(f"   odd-dimensional -- nowhere-zero fields exist); inf labels")
    print(f"   chi = {[chi(d) for d in inf]} -- the same chi(S^2n) = 2 that is")
    print(f"   the obstruction toll's chirality factor (1m; part0's shift")
    print(f"   family).  All four distinguished layers {{5,7,19,217}} odd:")
    print(f"   the invariant is evaluated on Euler-null spheres only   "
          f"{'PASS' if ok2 else 'FAIL'}")

    # ---- W3: the coincidence anatomy + the two other re-descriptions
    print()
    print("W3 anatomy: why odd-selection meets the sup at these crossings:")
    ok3 = int(c1) % 2 == 1 and int(c2) % 2 == 1     # content int-parts odd
    ok3 &= int(c0) % 2 == 0 and Om(7) < Om(6)       # scale: even + inequality
    farther = tuple(max(pr, key=lambda x: abs(x - c))
                    for pr, c in zip(PAIRS, (c0, c1, c2)))
    prox = tuple(min(pr, key=lambda x: (0 if 7 <= x <= 19 else
                                        min(abs(x - 7), abs(x - 19))))
                 for pr in PAIRS)
    ok3 &= farther == sup and prox == sup
    print(f"   content crossings have odd int-parts ({int(c1)}, {int(c2)});"
          f" the scale")
    print(f"   crossing has even int-part ({int(c0)}) and Om(7) < Om(6)"
          f" (gated);")
    print(f"   farther-integer = {farther} = sup; window-proximal"
          f" (in-or-nearest")
    print(f"   [7,19]) = {prox} = sup   {'PASS' if ok3 else 'FAIL'}")

    # ---- W4: the horizon budget -- sup I = min entropy, exactly
    print()
    print("W4 the horizon budget: S = 24 pi^2 M^4/rho, rho = (2/pi)e^g I:")
    rho = {l: (2 / PI) * math.exp(GAMMA_GRAM) * vals[l] for l in LABS}
    S = {l: 24 * PI ** 2 / rho[l] for l in LABS}
    smin = min(S, key=S.get)
    order_I = sorted(LABS, key=vals.get)
    order_S = sorted(LABS, key=S.get, reverse=True)
    ok4 = smin == sup and order_I == order_S        # monotone bijection
    ok4 &= abs(S[sup] / 3.3151e122 - 1) < 1e-3
    ok4 &= abs(S[sup] / math.log(2) / 4.7827e122 - 1) < 1e-3
    ok4 &= abs(S[inf] / S[sup] - vals[sup] / vals[inf]) < 1e-9
    print(f"   argmin S = {smin} = the sup labeling; S strictly decreasing")
    print(f"   in I over all eight (monotone bijection gated); S_sup =")
    print(f"   {S[sup]:.4e} nats = {S[sup]/math.log(2):.4e} bits; the inf")
    print(f"   labeling's budget is {S[inf]/S[sup]:.3f}x larger (= I_sup/"
          f"I_inf,")
    print(f"   the round-62 ratio as entropy stakes)   "
          f"{'PASS' if ok4 else 'FAIL'}")

    # ---- W5: distinctness -- the principles diverge off the actual cells
    print()
    print("W5 distinctness (SYNTHETIC exhibit, clearly labeled):")
    synth = 20.5                       # hypothetical crossing in (20, 21)
    synth_floor = math.floor(synth)    # content-floor reading -> 20 (even)
    synth_odd = 21                     # odd member of (20, 21)
    ok5 = synth_floor % 2 == 0 and synth_odd % 2 == 1 \
        and synth_floor != synth_odd
    print(f"   a crossing at {synth} would separate content-floor"
          f" ({synth_floor}, even)")
    print(f"   from odd-member ({synth_odd}): the characterizations are")
    print(f"   DISTINCT principles; their agreement at the three actual")
    print(f"   crossings is the gated content (fixed-target disclosed)   "
          f"{'PASS' if ok5 else 'FAIL'}")

    print()
    print("=" * 74)
    print("READING (classical + gated; grading in docstring)")
    print("=" * 74)
    print("  part0's open clause -- 'connecting the supremum to ... an")
    print("  entropy, a boundary area' -- is discharged AS AN EQUIVALENCE,")
    print("  with the direction stated: the sup is the MINIMAL-horizon-")
    print("  budget labeling, exactly; and it is the odd (Euler-null)")
    print("  member of every straddling pair, tying the selection to the")
    print("  tower's load-bearing chi machinery.  Nothing here forces the")
    print("  sup: why odd / why minimal-budget is the residual selection")
    print("  content, so the forcing question stays OPEN and 1k's second")
    print("  given persists -- re-motivated from a bare max convention to")
    print("  named structural equivalents.  No number changes; no closure.")


if __name__ == "__main__":
    main()
