#!/usr/bin/env python3
"""
Pre-flight inventory for the steel-theorem version of the
source-selection rule (ROADMAP.md item 1).

The selection rule's domain is observables whose leading cascade
prediction is corrected by a multiplicative shift exp(delta Phi)
with delta Phi = +/- alpha(d*)/chi^k, where d* is one of the four
non-sink distinguished layers {d_V=5, d_0=7, d_gw=14, d_1=19}.

For the steel-theorem version we need:
 (1) Forced uniqueness:  only one (d*, k) per observable.
 (2) Exhaustive coverage: every cascade observable falls into the
     four type slots OR is explicitly out of scope on stated grounds.
 (3) Falsifiability:     each future closure is a forward test of
     the rule's prediction.

This script enumerates every cascade-derived observable in the series
and assigns one of:

  - VERIFIED   : closed correction-family observable, rule prediction
                 matches the paper's assignment.
  - CANDIDATE  : not yet closed, rule predicts (d*, k); future closure
                 attempt is a forward test.
  - AMBIGUOUS  : flag classification produces a (d*, k) that conflicts
                 with the actual closure mechanism's structural
                 condition; needs sharpening before the steel theorem.
  - STRUCTURAL : exact / forced theorem outside the rule's scope (no
                 perturbative shift to assign).
  - DERIVED    : closed via a different mechanism (Gram path-distributed,
                 chirality theorem, geometric, geodesic, anchored ratio,
                 or non-perturbative); rule would or wouldn't apply
                 depending on whether the alternative mechanism is the
                 only one available.

Run:
    python3 tools/research/source_selection_inventory.py

Output: a single table grouped by status, ending with a short list
of items that require attention before the steel theorem closes.
"""

from dataclasses import dataclass
from typing import Optional


# ---------------------------------------------------------------------
# The classifier (same logic as tools/verifiers/verify_selection_rule.py)
# ---------------------------------------------------------------------

D_V, D_0, D_GW, D_1, D_2 = 5, 7, 14, 19, 217
NON_SINK = frozenset({D_V, D_0, D_GW, D_1})


def classify(P: bool, L: bool, G: bool) -> str:
    if P:
        return "Absolute"
    if L:
        return "Observer"
    if G:
        return "Gauge"
    return "Amplitude"


def predict_source(t: str) -> int:
    return {
        "Absolute": D_1,
        "Observer": D_V,
        "Gauge": D_GW,
        "Amplitude": D_0,
    }[t]


# ---------------------------------------------------------------------
# The inventory.
# ---------------------------------------------------------------------

@dataclass(frozen=True)
class Entry:
    name: str
    formula: str          # canonical cascade formula, terse
    flags: Optional[tuple]  # (P, L, G) or None if not in scope
    actual_source: Optional[tuple]  # (d*, k, sign) if closed, else None
    status: str           # VERIFIED / CANDIDATE / AMBIGUOUS / STRUCTURAL / DERIVED
    notes: str


INVENTORY = [

    # ---- VERIFIED: closed correction-family observables (9/9) --------------
    Entry("alpha_s(M_Z)",
          "alpha(12) * exp(Phi(12->4) + alpha(14)/chi)",
          (False, False, True),
          (14, 1, "+"),
          "VERIFIED",
          "Gauge: descent crosses gauge window {12,13,14}."),
    Entry("m_tau/m_mu",
          "exp(Phi(13)-Phi(5) + alpha(14)/chi) * 2sqrt(pi)",
          (False, False, True),
          (14, 1, "+"),
          "VERIFIED",
          "Gauge: descent path d=6..13 enters gauge window."),
    Entry("m_tau absolute",
          "(alpha_s v / sqrt2) * exp(-Phi(5) + alpha(19)/chi) * (2sqrt(pi))^-2",
          (True, False, False),
          (19, 1, "+"),
          "VERIFIED",
          "Absolute: contains M_{Pl,red} via v."),
    Entry("ell_A (acoustic scale)",
          "from cascade (H_0, Omega_m, r_d) with alpha(19)/chi shift",
          (True, False, False),
          (19, 1, "+"),
          "VERIFIED",
          "Absolute: r_d Planck-anchored."),
    Entry("sin^2 theta_W",
          "R(14)^2 / [pi R(13)^2 + R(14)^2] * exp(alpha(5)/chi^3)",
          (False, True, False),
          (5, 3, "+"),
          "VERIFIED",
          "Observer: ratio of N(d) at d=4 with no descent-integral exponential."),
    Entry("Omega_m (Bott)",
          "Bott partition * exp(-alpha(5)/chi^3)",
          (False, True, False),
          (5, 3, "-"),
          "VERIFIED",
          "Observer: density ratio at observer; geometric population (-)."),
    Entry("theta_C (Cabibbo)",
          "tan(arccos(N(13)/N(12))) * exp(-p(13)/2 - alpha(7)/chi^2)",
          (False, False, False),
          (7, 2, "-"),
          "VERIFIED",
          "Amplitude: Born-rule overlap between gauge layers."),
    Entry("b/s",
          "(m_tau/m_mu) * e * exp(-alpha(7)/chi^4)",
          (False, False, False),
          (7, 4, "-"),
          "VERIFIED",
          "Amplitude: cross-generation quark transition."),
    Entry("theta_23 (CKM)",
          "Cabibbo template * exp(-Sum_{d=13..20} p(d)/2 - alpha(7)/chi^4)",
          (False, False, False),
          (7, 4, "-"),
          "VERIFIED",
          "Amplitude: extended Cabibbo descent across phase transition."),

    # ---- CANDIDATE: rule predicts, no closure attempted yet -----------------
    Entry("alpha_em(M_Z) running",
          "U(1) descent through gauge window",
          (False, False, True),
          None,
          "CANDIDATE",
          "Gauge: predicts d*=14. Distinct from 1/alpha_em closure (chirality theorem)."),
    Entry("m_W absolute",
          "m_Z cos theta_W (anchored) OR cascade-direct closure",
          (True, False, False),
          None,
          "CANDIDATE",
          "Absolute: predicts d*=19 if attempted via direct cascade descent. "
          "Currently derived from m_Z anchor + theta_W; rule prediction is a forward test."),
    Entry("theta_13 (CKM)",
          "tan theta_C * tan theta_23 (CKM closure) + Wolfenstein factor",
          (False, False, False),
          None,
          "CANDIDATE",
          "Amplitude: predicts d*=7. Cascade structurally derives "
          "|V_ub|=|V_us||V_cb|; observed deviation = SM Wolfenstein input."),
    Entry("PMNS theta_12",
          "cascade-internal mixing TBD",
          (False, False, False),
          None,
          "CANDIDATE",
          "Amplitude: predicts d*=7. Cabibbo-template extension partial-negative; "
          "needs cascade-native mechanism distinct from CKM."),
    Entry("PMNS theta_23",
          "cascade-internal mixing TBD",
          (False, False, False),
          None,
          "CANDIDATE",
          "Amplitude: predicts d*=7. Same status as PMNS theta_12."),
    Entry("PMNS theta_13",
          "cascade-internal mixing TBD",
          (False, False, False),
          None,
          "CANDIDATE",
          "Amplitude: predicts d*=7. Same status as PMNS theta_12."),
    Entry("Up-type quark Weyl factor",
          "(t/b)/(c/s) = N_c (Tier 4)",
          (False, True, False),
          None,
          "CANDIDATE",
          "Observer: predicts d*=5 if closure shift attempted. "
          "Currently closed by ratio-of-ratios at ~1.5%."),
    Entry("m_b/m_tau",
          "Georgi-Jarlskog: ~3 outside gauge window",
          (False, True, False),
          None,
          "CANDIDATE",
          "Observer: predicts d*=5 if closure shift attempted (Tier 4)."),

    # ---- AMBIGUOUS: needs flag-definition sharpening before steel theorem ---
    Entry("m_mu/m_e",
          "exp(Phi(21)-Phi(13)) * 2sqrt(pi)",
          (False, False, True),  # G=T per literal flag, since [14,21] meets {12,13,14}
          None,
          "AMBIGUOUS",
          "Path d=14..21 has [d_A,d_B] cap {12,13,14} = {14} so literal G=T predicts "
          "d*=14. But Part IVb's actual closure condition for delta Phi_U(1) requires "
          "the path 'strictly below' d=14, which m_mu/m_e fails. Rule's prediction "
          "(d*=14) and closure-mechanism's applicability (no) are inconsistent. "
          "Flag G needs sharpening: 'crosses gauge window from strictly above' "
          "vs 'merely intersects {12,13,14}'. Under 'strictly above' reading, "
          "G=F and rule predicts Amplitude -> d*=7, k unknown (residual 0.13% "
          "matches no alpha(7)/chi^k). See Part IVb oq:mu-e-residual."),
    Entry("m_e/m_mu (inverse)",
          "1 / (m_mu/m_e)",
          (False, False, True),  # same path, same flags
          None,
          "AMBIGUOUS",
          "Same path as m_mu/m_e; same ambiguity. "
          "verify_selection_rule.py lists this with G=T -> d*=14, but the "
          "closure condition 'strictly below' is not met."),

    # ---- STRUCTURAL: exact / forced theorems, no shift to assign ------------
    Entry("d=4 (spacetime dimension)",
          "Lovelock cap Clifford",
          None, None,
          "STRUCTURAL",
          "Tier 1 forced. Not a numerical observable for shift assignment."),
    Entry("Gauge group SU(3)xSU(2)xU(1)",
          "Adams + Bott",
          None, None,
          "STRUCTURAL",
          "Tier 1 forced. Structural, not numeric."),
    Entry("3 generations",
          "Bott + d_1 phase transition",
          None, None,
          "STRUCTURAL",
          "Tier 1 forced (modulo Bott-tower-open empirical brake)."),
    Entry("w = -1 (dark energy EoS)",
          "Fixed Lambda; GB vanishes",
          None, None,
          "STRUCTURAL",
          "Tier 1 exact theorem. No correction shift applies."),
    Entry("theta_QCD = 0",
          "pi_3(S^11) = 0",
          None, None,
          "STRUCTURAL",
          "Tier 1 topological (Tier 4b for pi_3(S^11) replacing pi_3(SU(3)))."),
    Entry("No SUSY / DM particles / extra Higgs / axion / graviton",
          "Forced negatives",
          None, None,
          "STRUCTURAL",
          "Tier 1 qualitative; not numerical."),
    Entry("z_eq",
          "Omega_m / Omega_r = 4 pi^6",
          None, None,
          "STRUCTURAL",
          "Exact ratio; cascade-internal."),
    Entry("Omega_Lambda",
          "(pi-1)/pi",
          None, None,
          "STRUCTURAL",
          "Exact lapse complement; -0.5%."),

    # ---- DERIVED: closed via a different cascade mechanism ------------------
    Entry("rho_Lambda / M^4_Pl,red",
          "18 Omega_19 Omega_217 / pi^3 * exp(delta_path Gram)",
          (True, False, True),
          None,
          "DERIVED",
          "Closed by Gram path-distributed (Part 0), not single-source. "
          "Note flags would predict Absolute (P=T) -> d*=19; rule out of scope here "
          "because the closure mechanism is multi-layer Gram, not single-source shift."),
    Entry("1/alpha_em",
          "1/alpha(13) + pi/alpha(14) + 6pi (chirality theorem)",
          None, None,
          "DERIVED",
          "Closed by chirality selection rule (m=1, k=0) + per-leg primitive "
          "Gamma(1/2). Not a source-selection-rule observable."),
    Entry("(g-2) at 1-loop",
          "alpha_em / (2 pi) * chi^0",
          None, None,
          "DERIVED",
          "Closed by chirality selection rule at m-k=0. Schwinger reproduction."),
    Entry("m_H / m_W",
          "pi/2 (geodesic on S^12)",
          None, None,
          "DERIVED",
          "Geometric/topological, not perturbative. +0.8% leading."),
    Entry("Higgs quartic lambda",
          "pi^2 g^2 / 32 (curvature on S^12)",
          None, None,
          "DERIVED",
          "Geometric, derived from V''(pi/2)=1 on S^12."),
    Entry("m_W absolute (anchored)",
          "m_Z cos theta_W",
          None, None,
          "DERIVED",
          "Anchored to m_Z + cascade theta_W. Independent rule prediction "
          "(see CANDIDATE entry above) is a forward test of direct closure."),
    Entry("m_H absolute",
          "m_W * pi/2",
          None, None,
          "DERIVED",
          "Anchored chain m_Z -> theta_W -> m_W -> m_H."),
    Entry("v (electroweak VEV)",
          "M_Pl,red alpha_s exp(-pi/alpha(5))",
          None, None,
          "DERIVED",
          "Non-perturbative factor exp(-pi/alpha(5)) = Kosterlitz-Thouless-like "
          "vortex on S^4 cross-section (Part IVb rem:v-closure). Distinct mechanism."),
    Entry("1/alpha_GUT",
          "4 pi / N(12)^2",
          None, None,
          "DERIVED",
          "Geometric at d=12; 0.08% match. No descent shift."),
    Entry("Omega_b",
          "1 / (2 pi^2)",
          None, None,
          "DERIVED",
          "'One unit of content on S^3' (Tier 5). +2.8%. "
          "Not a perturbative-shift observable; structural argument needs strengthening."),
    Entry("Omega_r",
          "1 / (4 pi^7)",
          None, None,
          "DERIVED",
          "Interior content over 7 cascade steps. +0.1% match. Geometric."),
    Entry("Omega_m (lapse)",
          "1/pi",
          None, None,
          "DERIVED",
          "Lapse identity; +1.1% leading. Bott reading is the corrected version "
          "(VERIFIED above)."),
    Entry("H_0",
          "M_Pl,red sqrt(2I/(3(pi-1)))",
          None, None,
          "DERIVED",
          "Friedmann from rho_Lambda; -0.9% leading, ~Planck after Gram."),
    Entry("t_0 (universe age)",
          "LambdaCDM integral with cascade params",
          None, None,
          "DERIVED",
          "+0.6% match. ODE evolution, not a shift target."),
    Entry("T_CMB",
          "from Omega_r, M_Pl,red, H_0, g_eff",
          None, None,
          "DERIVED",
          "-3.1% leading; -2.1% Gram-corrected. Open (ROADMAP item 6)."),
    Entry("r_d (sound horizon)",
          "from cascade (Omega_b, Omega_m, H_0) via E&H98",
          None, None,
          "DERIVED",
          "~Planck (147.75 vs 147.6). Not a shift target."),
    Entry("S = A/d (BH entropy)",
          "Boundary dominance",
          None, None,
          "DERIVED",
          "Geometric; II=III. T = 1/(8 pi M) follows from Birkhoff."),
    Entry("m_nu (heaviest)",
          "m_29 alpha(21) / chi^8",
          None, None,
          "DERIVED",
          "Cascade neutrino chain (Tier 2). Uses alpha(d_g) source at "
          "Bott layer of fermion, not single-source rule. Distinct mechanism "
          "from correction family but uses the same alpha/chi^k structure."),
    Entry("m_e absolute",
          "(alpha_s v / sqrt2) exp(-Phi(21)) (2sqrt(pi))^-4",
          (True, False, False),
          None,
          "DERIVED",
          "Absolute via v anchor. Rule prediction d*=19 if attempted as "
          "direct closure parallel to m_tau. 0.6% leading."),
    Entry("m_mu absolute",
          "(alpha_s v / sqrt2) exp(-Phi(13)) (2sqrt(pi))^-3",
          (True, False, False),
          None,
          "DERIVED",
          "Absolute. Rule prediction d*=19. 0.47% leading."),
]


# ---------------------------------------------------------------------
# Reporting.
# ---------------------------------------------------------------------

def flag_str(flags) -> str:
    if flags is None:
        return "---"
    P, L, G = flags
    return f"{'P' if P else '.'}{'L' if L else '.'}{'G' if G else '.'}"


def report():
    by_status = {}
    for e in INVENTORY:
        by_status.setdefault(e.status, []).append(e)

    order = ["VERIFIED", "AMBIGUOUS", "CANDIDATE", "STRUCTURAL", "DERIVED"]

    print("=" * 100)
    print("Source-selection rule: pre-flight inventory")
    print("=" * 100)
    print()

    for status in order:
        entries = by_status.get(status, [])
        print(f"--- {status} ({len(entries)}) ---")
        for e in entries:
            pred = ""
            if e.flags is not None:
                t = classify(*e.flags)
                d_pred = predict_source(t)
                pred = f"{flag_str(e.flags)} -> {t}/d*={d_pred}"
            actual = ""
            if e.actual_source is not None:
                d, k, s = e.actual_source
                actual = f"actual d*={d},k={k},{s}"
                # consistency check
                if e.flags is not None:
                    t = classify(*e.flags)
                    if predict_source(t) != d:
                        actual += "  [MISMATCH]"
            print(f"  {e.name:<32} {pred:<28} {actual}")
            print(f"    formula: {e.formula}")
            print(f"    notes:   {e.notes}")
        print()

    # Roll-up.
    print("=" * 100)
    print("ROLL-UP")
    print("=" * 100)
    n_total = len(INVENTORY)
    n_verified = sum(1 for e in INVENTORY if e.status == "VERIFIED")
    n_ambiguous = sum(1 for e in INVENTORY if e.status == "AMBIGUOUS")
    n_candidate = sum(1 for e in INVENTORY if e.status == "CANDIDATE")
    n_structural = sum(1 for e in INVENTORY if e.status == "STRUCTURAL")
    n_derived = sum(1 for e in INVENTORY if e.status == "DERIVED")
    print(f"  Total entries:               {n_total}")
    print(f"  VERIFIED (rule matches):     {n_verified}")
    print(f"  AMBIGUOUS (needs sharpening): {n_ambiguous}")
    print(f"  CANDIDATE (forward tests):   {n_candidate}")
    print(f"  STRUCTURAL (out of scope):   {n_structural}")
    print(f"  DERIVED (other mechanism):   {n_derived}")
    print()

    # Items that block the steel theorem.
    print("=" * 100)
    print("BLOCKERS for the steel-theorem version")
    print("=" * 100)
    print()
    print("Items that need attention before the source-selection rule can be")
    print("promoted from 'empirical 9/9 + structural rationale' to forced theorem:")
    print()
    blockers = [e for e in INVENTORY if e.status == "AMBIGUOUS"]
    for e in blockers:
        print(f"  {e.name}")
        print(f"    {e.notes}")
        print()

    # Cleanest exposed test: contradictions on closed observables.
    print("FALSIFICATION CHECK on closed observables:")
    bad = [e for e in INVENTORY if e.status == "VERIFIED"
           and e.flags is not None and e.actual_source is not None
           and predict_source(classify(*e.flags)) != e.actual_source[0]]
    if bad:
        print("  CONTRADICTIONS FOUND:")
        for e in bad:
            print(f"    {e.name}: flags predict d*={predict_source(classify(*e.flags))}, "
                  f"actual d*={e.actual_source[0]}")
        return 1
    else:
        print(f"  No contradictions on the {n_verified} closed observables.")

    return 0


if __name__ == "__main__":
    import sys
    sys.exit(report())
