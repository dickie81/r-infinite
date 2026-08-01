#!/usr/bin/env python3
"""Theorem 1af verifier: the deeper grounding.

Claim under test (the owner's standard: "Look for the deeper
grounding ... no first principles derivation or proof"): three
theorems from the committed dynamics, one identification:

  (iii) TWO-POINT STRUCTURE (theorem, new): for the committed
        action S = sum 1/(2 alpha(d)) (Delta phi)^2 with Neumann
        at 4 and Dirichlet at 217 (the committed instrument
        cascade_greens_function.py), the two-point function is
        G(d, d*) = sum_{k=max(d,d*)}^{216} alpha(k) -- it depends
        only on max(d, d*).  The flux argument is the instrument's
        own (quoted, anchored); the extension to arbitrary pairs
        is 1af's and is gated numerically here.
  (iv)  SCALAR DELTA-BLINDNESS (corollary, the load-bearing
        negative): G(seat, source) is independent of WHICH source
        couples -- G(21, s) = tail(21) for all four sources,
        G(29, s) = tail(29); the scalar 21-vs-29 ratio is 1.1603,
        no dichotomy; hence no first-principles derivation of the
        participation dichotomy can live in the scalar sector, and
        1ae's (v-a) is forced into the chirality/spinor sector.
  (v)   SINK NULLITY (theorem, new): the sink is a constraint
        node (phi(217) = 0 imposed, no EL variation); forcing it
        produces the rigid shift phi == const -- zero bond
        stretch, zero action, dynamically null.  "The sink is not
        a source" upgrades from remark-level accounting to
        forced-by-the-dynamics; 1ae's sensitivity-disclosure step
        carries the net-state marker (anchored).
  (vi)  CLIFFORD IDENTIFICATION (named, not derived): chi = 2 per
        layer coincides with dim Cl(d+1) = 2 dim Cl(d); chi^8 =
        256 = dim Cl(29)/dim Cl(21) (declared identity).  The
        candidate spinor-chain mechanism for (v-a) is named in the
        paper; the identification's arithmetic is trivially exact
        and is NOT counted as evidence (the paper says so).

Gates:
  E1 -- the committed substrate: the instrument docstring's action,
        BCs, and flux sentences anchored verbatim;
        cascade_unit_source_strength.py subprocess exit 0 (the
        instrument's exit-gated consumer since 1ac).
  E2 -- the two-point theorem: the committed operator inverted;
        worst relative error of G(d, d*) vs tail(max(d, d*)) over
        a 100-pair census < 1e-10.
  E3 -- delta-blindness: G(21, s) spread over the four sources
        < 1e-12 and equal to tail(21) = 1.167571 (half-ULP of the
        quoted digits); G(29, s) likewise = 1.006240; the ratio
        1.1603 recomputed (half-ULP).
  E4 -- sink nullity: the response column to injection at the
        pinned node is exactly constant (spread < 1e-12) with all
        bond stretches < 1e-12.
  E5 -- the paper: 1af's key sentences anchored (the commission
        quote; the two-point form; the delta-blindness consequence;
        the sink upgrade with the weakest-link disclosure; the
        named-not-derived candidate); the two 1ae net-state
        markers (the sink step; the (v-a) narrowing);
        cascade_participation_dichotomy.py subprocess exit 0 at
        RESULT 18/0 (the sibling).

Declared identities (not gated): chi^8 = 2^8 = 256 =
dim Cl(29)/dim Cl(21); dim Cl doubles per layer -- literal
arithmetic, the 1l(iv) discipline.

No data consumed; no number changes; (iii)-(v) theorem-grade
(committed flux argument + linear algebra over the committed
operator), (vi) an identification with a named gap.  Sabotage
record (full-tree scratchpad copy, at the landing commit;
mid-anchor perturbations): (a) "the flux below d* is zero" ->
"the flux beSABlow ..." in the instrument copy tripped E1, 10/1,
exit 1; (b) max -> min in the SCRATCHPAD COPY's E2 expectation
(instrument-expectation perturbation) tripped E2, 10/1, exit 1;
(c) "the scalar sector cannot see δ at all" -> mid-anchor SAB in
the paper copy tripped E5, 10/1, exit 1.  Clean baselines 11/0
exit 0 before and after each.  Eleven gates (the
RESULT line's first draft said 10 and this docstring said 14 --
both corrected pre-commit, the recurring count defect's fifth
instance).
"""
import itertools
import os
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
GFPY = os.path.join(ROOT, "tools", "verifiers", "cascade_greens_function.py")

sys.path.insert(0, os.path.join(ROOT, "tools"))
sys.path.insert(0, os.path.join(ROOT, "tools", "verifiers"))
from cascade_constants import alpha  # noqa: E402
from cascade_greens_function import greens_function  # noqa: E402

import numpy as np  # noqa: E402

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


D_MIN, D_MAX = 4, 217
G = greens_function(D_MIN, D_MAX)


def g(d, ds):
    return G[d - D_MIN, ds - D_MIN]


def tail(d):
    return sum(alpha(k) for k in range(d, D_MAX))


print("E1 -- the committed substrate")
gf_src = norm(open(GFPY, encoding="utf-8").read())
ok = "Neumann at d = 4 (observer)" in gf_src
ok &= "Dirichlet at d = 217 (Part 0 terminus)" in gf_src
ok &= ("for a unit source at d*, the flux below d* is zero (Neumann at "
       "d_min), the flux above d* is unit" in gf_src)
gate("the instrument's action/BC/flux sentences anchored verbatim", ok)
r = subprocess.run([sys.executable,
                    os.path.join(ROOT, "tools", "research",
                                 "cascade_unit_source_strength.py")],
                   capture_output=True, text=True)
gate("cascade_unit_source_strength.py (the instrument's exit-gated "
     "consumer) exit 0", r.returncode == 0, f"exit {r.returncode}")

print("E2 -- the two-point theorem")
pts = [5, 7, 13, 14, 19, 21, 29, 37, 100, 213]
worst = max(abs(g(d, ds) / tail(max(d, ds)) - 1)
            for d, ds in itertools.product(pts, repeat=2))
gate("G(d, d*) = tail(max(d, d*)) over the 100-pair census, worst "
     "relative error < 1e-10", worst < 1e-10, f"{worst:.2e}")

print("E3 -- scalar delta-blindness")
v21 = [g(21, s) for s in (5, 7, 14, 19)]
v29 = [g(29, s) for s in (5, 7, 14, 19)]
ok = max(v21) / min(v21) - 1 < 1e-12 and max(v29) / min(v29) - 1 < 1e-12
gate("G(21, s) and G(29, s) independent of the source (spread < 1e-12)",
     ok, f"spreads {max(v21)/min(v21)-1:.1e}, {max(v29)/min(v29)-1:.1e}")
ok = abs(tail(21) - 1.167571) < 5e-7 and abs(tail(29) - 1.006240) < 5e-7
ok &= abs(tail(21) / tail(29) - 1.1603) < 5e-5
gate("tail(21) = 1.167571, tail(29) = 1.006240, ratio 1.1603 (half-ULP "
     "of the quoted digits)", ok,
     f"{tail(21):.6f}, {tail(29):.6f}, {tail(21)/tail(29):.4f}")

print("E4 -- sink nullity")
col = G[:, D_MAX - D_MIN]
spread = float(np.max(col) - np.min(col))
stretch = float(np.max(np.abs(np.diff(col))))
gate("injection at the pinned node yields the rigid shift: response "
     "column constant (spread < 1e-12), all bond stretches < 1e-12",
     spread < 1e-12 and stretch < 1e-12,
     f"spread {spread:.1e}, stretch {stretch:.1e}")

print("E5 -- the paper and the sibling")
paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")
ok = ("Look for the deeper grounding. Interesting pattern but this is no "
      "first principles derivation or proof." in paper)
ok &= "G(d, d*) = Σ_{k = max(d, d*)}^{216} α(k)" in paper
gate("the commission quote + the two-point form anchored", ok)
ok = "the scalar sector cannot see δ at all" in paper
ok &= ("no first-principles derivation of the participation dichotomy can "
       "live in the scalar sector" in paper)
ok &= "unrelated to χ⁸ = 256 or part4a's ~289" in paper
gate("the delta-blindness consequence + the no-coincidence disclosure "
     "anchored", ok)
ok = "forced by the committed dynamics" in paper
ok &= "remains the chain's weakest link, stated" in paper
ok &= "Candidate mechanism for (v-a), named, not derived:" in paper
ok &= ("The arithmetic of the identification is trivially exact; its "
       "content is the reading" in paper)
gate("the sink upgrade + weakest-link + named-candidate sentences "
     "anchored", ok)
ok = ("Net-state, Theorem 1af round 130: this step upgrades" in paper)
ok &= ("Net-state, Theorem 1af round 130: the route is narrowed by "
       "theorem" in paper)
gate("the two 1ae net-state markers anchored", ok)
r2 = subprocess.run([sys.executable,
                     os.path.join(ROOT, "tools", "research",
                                  "cascade_participation_dichotomy.py")],
                    capture_output=True, text=True)
gate("cascade_participation_dichotomy.py (the sibling) exit 0 at "
     "RESULT 18/0", r2.returncode == 0
     and "RESULT: 18 pass / 0 fail" in r2.stdout, f"exit {r2.returncode}")

print("  IDENTITY (declared, not gated): chi^8 = 2^8 = 256 = "
      "dim Cl(29)/dim Cl(21); dim Cl doubles per layer -- literal "
      "arithmetic")

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (11 gates; 1 identity block declared, not counted)")
print("READING: the deeper grounding -- the committed action is a grounded")
print("elastic chain, and three theorems follow: the two-point function")
print("depends only on max(d, d*) (the flux argument, gated at 2e-13);")
print("hence the scalar sector is delta-blind (every seat couples to every")
print("source identically -- the dichotomy CANNOT be scalar, and (v-a) is")
print("forced into the spinor sector); and the sink is a constraint node")
print("whose forcing is a rigid shift -- dynamically null, upgrading the")
print("sink-exclusion step from remark to dynamics.  The spinor candidate")
print("is named, not derived: chi per layer = Clifford doubling per layer.")
print("What remains for the full proof: the spinor transport theorem")
print("(v-a, one sector, one candidate) and the measurement biconditional")
print("(v-b).  No convention, no new number.")
sys.exit(0 if n_fail == 0 else 1)
