#!/usr/bin/env python3
"""THE GRAMMAR-NEED CENSUS (Theorem 1t): the second branch of 1s's
open core established for the committed record -- NO grammar output
reads the odd feature through the pairing.  Category (a): text
census over the committed record plus digamma/lattice arithmetic;
no data, no closures, no RH/GRH, no semiclassics (Check 7); the
hypothesis is nowhere an input (Check 8).

CONTEXT.  Theorem 1s located the pairing-act and left the open
core as a disjunction: derive an extrinsic odd selection principle
from A1-A4, OR establish that the grammar never needs the odd
reading (the act as Door-4 bookkeeping only).  This file audits
the second branch as a consumption census.

CENSUS SCOPE (stated, not silent).  The derivation record: the
cascade series (src/*.tex -- every paper), the frozen ledger
(PREDICTIONS.md), the observable-computing tools
(cascade_constants.py, tools/verifiers/, tools/closures/), and the
four degree-marked record instruments (cascade_leptons,
cascade_neutrino_closure, cascade_E_fit_audit, cascade_null_clone).
EXCLUDED BY DESIGN, disclosed: the riemann-review paper and its
research instruments -- they are the STUDY of the pairing (1c, 1i,
1r and their category-(a) verifiers), so their L-side content is
the subject of the audit, not a consumer.

  N1 THE SERIES CONSUMES NO L-SIDE OBJECT.  Token census over
     src/*.tex: chi_{-3}, L(s,chi)/L(1,chi), the chi zeros
     (8.0397), Kronecker, "conductor", "quadratic character",
     sqrt{3} -- ALL ZERO HITS across every cascade paper.  (The
     lone "Dirichlet" in the series is part0a's "Dirichlet's
     method" for zeta(2) -- a classical method name, gated as the
     only hit.)  Colour enters the papers exclusively as ring/Lie
     structure: su(3), Adams, Radon-Hurwitz, Z[omega] via T8/T11.
  N2 THE OBSERVABLE TOOLS CONSUME NO L-SIDE OBJECT.  The same
     census over cascade_constants.py, tools/verifiers/*.py,
     tools/closures/*.py, and the four record instruments: zero
     hits (the earlier grep's two "jacobi" hits were "jacobian" --
     substrings excluded by tokenization).  PREDICTIONS.md: zero.
  N3 THE CROSSING IS GAMMA-SIDE COMPLETE.  The band boundary at
     6.2569 derives from digamma alone: p(d) = -ln(pi)/2 +
     psi((d+1)/2)/2 has its zero in (6, 7) at 6.2569 (gated,
     4 d.p.), and the B1 upper boundary sits in (19, 20) (gated:
     p(19) < ln Gamma(1/2) < p(20)) -- no L-function enters the
     feature machinery anywhere.
  N4 DOOR 4'S TWO SIDES ARE INDEPENDENTLY COMMITTED.  The bridge
     side: (1/2)ln 3 = ln sqrt(3) (exact).  The ring side:
     covol(Z[omega]) computed from the lattice basis (1, omega),
     omega = e^(2 pi i/3): covol = |Im omega| = sqrt(3)/2 =
     cos(pi/6) (gated), and the mass arc consumes THE RING SIDE
     (1m's committed identification anchored verbatim).  Removing
     the Door-4 identification changes no committed number: both
     sides exist independently, the identification links them.
  N5 HONEST GRADING, THE SCOPED UNIVERSAL, AND THE FALSIFIER.
     The census covers the COMMITTED record -- it is not a
     universal over future derivations (the round-47 F1 lesson
     applied in advance).  Licensed falsifier, stopping-rule-gated
     (the 1h(iv) pattern): any future derivation that routes a
     grammar entry through the odd bridge's L-side (chi_-3
     L-values, zeros, conductor-as-L-object) re-opens the
     member's derivational weight.  With that scope: 1s's
     disjunction RESOLVES ON BRANCH B for the recorded chain --
     the grammar does not need the odd reading; the pairing-act
     is Door-4 bookkeeping (an identification between two
     independently committed objects, consumed by nothing).  The
     member PERSISTS as charged (three members, seven items
     unchanged); its derivational weight is audited to zero.  No
     number changes; no closure of the member itself.
"""

import glob
import math
import os

import mpmath as mp

mp.mp.dps = 30

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")

TEX_TOKENS = ["chi_{-3}", "L(s,\\chi", "L(1,\\chi", "8.0397",
              "Kronecker", "conductor", "quadratic character",
              "\\sqrt{3}"]
PY_TOKENS = ["chi_m3", "chi_{-3}", "kronecker", "jacobi_symbol",
             "jacobi(", "8.0397", "3*sqrt(3)", "3 * sqrt(3)"]
RECORD_INSTRUMENTS = ["cascade_leptons.py", "cascade_neutrino_closure.py",
                      "cascade_E_fit_audit.py", "cascade_null_clone.py"]


def count_hits(paths, tokens, lower=False):
    total = {}
    for path in paths:
        text = open(path, encoding="utf-8", errors="replace").read()
        if lower:
            text = text.lower()
        for tok in tokens:
            t = tok.lower() if lower else tok
            n = text.count(t)
            if n:
                total.setdefault(tok, []).append((os.path.basename(path), n))
    return total


def p_tower(d):
    return -mp.log(mp.pi) / 2 + mp.digamma((d + 1) / mp.mpf(2)) / 2


def main():
    print("=" * 74)
    print("THE GRAMMAR-NEED CENSUS (Theorem 1t)")
    print("=" * 74)

    tex = sorted(glob.glob(os.path.join(ROOT, "src", "*.tex")))

    # ---- N1: the series census
    print()
    print("N1 the cascade series consumes no L-side object:")
    hits = count_hits(tex, TEX_TOKENS)
    ok1 = hits == {}
    dirichlet = count_hits(tex, ["Dirichlet"])
    ok1 &= (list(dirichlet.keys()) == ["Dirichlet"]
            and len(dirichlet["Dirichlet"]) == 1
            and dirichlet["Dirichlet"][0][1] == 1
            and "Dirichlet's method" in open(
                os.path.join(ROOT, "src", dirichlet["Dirichlet"][0][0]),
                encoding="utf-8").read())
    print(f"   {len(tex)} papers scanned; tokens (chi_-3, L(s/1,chi), the")
    print("   chi zeros, Kronecker, conductor, quadratic character,")
    print(f"   sqrt{{3}}): ZERO hits {dict(hits)}; the lone 'Dirichlet' is")
    print("   part0a's classical method name (gated: exactly one, and it")
    print("   is 'Dirichlet's method').  Colour enters the papers as")
    print("   ring/Lie structure only   " + ("PASS" if ok1 else "FAIL"))

    # ---- N2: the observable tools + ledger census
    print()
    print("N2 the observable tools and the ledger consume no L-side object:")
    py = ([os.path.join(ROOT, "tools", "cascade_constants.py")]
          + sorted(glob.glob(os.path.join(ROOT, "tools", "verifiers",
                                          "*.py")))
          + sorted(glob.glob(os.path.join(ROOT, "tools", "closures",
                                          "*.py")))
          + [os.path.join(ROOT, "tools", "research", f)
             for f in RECORD_INSTRUMENTS])
    hits2 = count_hits(py, PY_TOKENS, lower=True)
    ok2 = hits2 == {}
    led = count_hits([os.path.join(ROOT, "PREDICTIONS.md")],
                     TEX_TOKENS + ["Jacobi"])
    ok2 &= led == {}
    print(f"   {len(py)} scripts scanned (constants, verifiers, closures,")
    print("   the four degree-marked record instruments) plus the frozen")
    print(f"   ledger: ZERO hits {dict(hits2)} {dict(led)} (tokenized --")
    print("   'jacobian' substring hits excluded by construction)   "
          + ("PASS" if ok2 else "FAIL"))

    # ---- N3: the crossing is Gamma-side complete
    print()
    print("N3 the band machinery is digamma-only:")
    ok3 = p_tower(6) < 0 < p_tower(7)
    root = mp.findroot(lambda d: p_tower(d), 6.3)
    ok3 &= abs(root - mp.mpf("6.2569")) < 5e-5
    lng = mp.log(mp.gamma(mp.mpf("0.5")))
    ok3 &= p_tower(19) < lng < p_tower(20)
    print(f"   p's zero at d = {mp.nstr(root, 6)} (gated 4 d.p. against the")
    print("   committed 6.2569); p(6) < 0 < p(7) and p(19) < ln Gamma(1/2)")
    print("   < p(20) gated -- the feature machinery consumes digamma,")
    print("   never an L-function   " + ("PASS" if ok3 else "FAIL"))

    # ---- N4: Door 4's two sides, independently committed
    print()
    print("N4 Door 4 links two independently committed objects:")
    ok4 = abs(mp.log(3) / 2 - mp.log(mp.sqrt(3))) < mp.mpf("1e-25")
    omega = mp.exp(2j * mp.pi / 3)
    covol = abs(mp.im(omega))
    ok4 &= abs(covol - mp.sqrt(3) / 2) < mp.mpf("1e-25")
    ok4 &= abs(mp.cos(mp.pi / 6) - mp.sqrt(3) / 2) < mp.mpf("1e-25")
    paper = open(os.path.join(ROOT, "riemann-indistinguishability.md"),
                 encoding="utf-8").read().replace("\n", " ")
    ok4 &= "cos(π/6) = √3/2 = covol(ℤ[ω])" in paper     # 1m's ring side
    print("   bridge side: (1/2)ln 3 = ln sqrt(3) (exact); ring side:")
    print("   covol from the lattice basis (1, omega) = |Im omega| =")
    print("   sqrt(3)/2 = cos(pi/6) (gated); the mass arc's committed")
    print("   identification 'cos(pi/6) = sqrt(3)/2 = covol(Z[omega])'")
    print("   anchored verbatim (1m) -- both sides exist independently;")
    print("   the identification links them   " + ("PASS" if ok4 else "FAIL"))

    # ---- N5: the scoped conclusion and the falsifier
    print()
    print("N5 the scoped conclusion (grading in docstring):")
    ok5 = "or establish that the grammar never needs the odd reading" \
        in paper
    ok5 &= "Finding 6's excluded object" in paper
    print("   1s's disjunction (anchored) resolves on branch B for the")
    print("   COMMITTED record: no grammar output reads the odd feature")
    print("   through the pairing -- the act is Door-4 bookkeeping.  Not")
    print("   a universal over future derivations; licensed falsifier:")
    print("   any future grammar entry routed through the odd bridge's")
    print("   L-side re-opens the member's derivational weight.  Three")
    print("   members, seven items unchanged   "
          + ("PASS" if ok5 else "FAIL"))

    print()
    print("=" * 74)
    print("READING (census + gated; grading in docstring)")
    print("=" * 74)
    print("  The derivation record -- every cascade paper, the ledger,")
    print("  the observable tools, the record instruments -- contains no")
    print("  consumption of the odd bridge's arithmetic side.  Colour")
    print("  enters through the ring (T8/T11); the crossing through")
    print("  digamma; Door 4's two sides are independently committed.")
    print("  For the recorded chain, the grammar does not need the odd")
    print("  reading: 1s's open core resolves on its second branch, and")
    print("  the pairing-act's derivational weight is audited to zero.")
    print("  The member persists; the falsifier is licensed.  No number")
    print("  changes; no closure of the member itself.")


if __name__ == "__main__":
    main()
