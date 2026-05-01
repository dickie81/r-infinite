#!/usr/bin/env python3
"""
Mechanical verification of the source selection rule for the cascade's
correction family delta_Phi = alpha(d*)/chi^k.

Reference: Part IVb, Section "The Source Selection Rule" (Proposition
"Source selection rule", Definition "Observable type").

The selection rule reduces the post-hoc observable-class assignment
of Remark "alpha(d*)/chi^k family and the cascade action principle"
to a deterministic three-flag decision procedure:

    Input for each observable: three booleans (P, L, G)
        P  Planck-anchored  : does Q's cascade value require the
                              Planck sink d_2=217 as a normalisation?
        L  Observer-local   : is Q measured as a local ratio at d=4
                              without its value encoding the cascade
                              descent?
        G  Gauge-mediated   : is Q's hierarchy controlled by a gauge
                              coupling running through {12,13,14}?

    Classify in order:
        if P:           type = "Absolute"   -> d* = 19  (d_1)
        elif L:         type = "Observer"   -> d* =  5  (d_V)
        elif G:         type = "Gauge"      -> d* = 14  (d_gw)
        else:           type = "Amplitude"  -> d* =  7  (d_0)

The four non-sink distinguished layers {5, 7, 14, 19} are the complete
set of cascade sources: Part 0 gives {5, 7, 19, 217}, Part IVa adds
the gauge window boundary 14, and the Planck sink 217 is excluded
because the cascade ends there (it cannot act as a perturbation
source).  Exactly four types, exactly four sources, bijective map.

This script runs the classifier on all eight closed observables of
the correction-family table and confirms that each prediction matches
the paper's assignment.  The three flags are physics meta-data about
each observable, not derived mechanically from the cascade formulas
(see the "Does not" remark in Part IVb).
"""

from dataclasses import dataclass
from typing import Optional


# The four non-sink distinguished layers.
D_V = 5      # volume maximum (Part 0, d_V)
D_0 = 7      # area maximum (Part 0, d_0)
D_GW = 14    # gauge-window boundary (Part IVa)
D_1 = 19     # first threshold (Part 0, d_1)
D_2 = 217    # Planck sink (Part 0, d_2) -- NEVER a source.

NON_SINK_DISTINGUISHED = frozenset({D_V, D_0, D_GW, D_1})


@dataclass(frozen=True)
class Observable:
    name: str
    planck_anchored: bool     # flag P
    observer_local: bool      # flag L
    gauge_mediated: bool      # flag G
    rationale: str
    paper_d_star: int
    paper_k: int
    paper_sign: str           # "+" or "-"


def classify(obs: Observable) -> str:
    """Definition 'Observable type' applied in decision-procedure order."""
    if obs.planck_anchored:
        return "Absolute"
    if obs.observer_local:
        return "Observer"
    if obs.gauge_mediated:
        return "Gauge"
    return "Amplitude"


def predict_source(obs_type: str) -> int:
    """Proposition 'Source selection rule'."""
    return {
        "Absolute": D_1,
        "Observer": D_V,
        "Gauge": D_GW,
        "Amplitude": D_0,
    }[obs_type]


# The eight closed observables of Part IVb's correction-family table.
# Flags are read from the physical definition of each observable.
OBSERVABLES = [
    Observable(
        name="alpha_s(M_Z)",
        planck_anchored=False,
        observer_local=False,
        gauge_mediated=True,
        rationale="running SU(3) coupling; value encodes gauge-window descent",
        paper_d_star=14,
        paper_k=1,
        paper_sign="+",
    ),
    Observable(
        name="m_tau/m_mu",
        planck_anchored=False,    # Planck cancels in the ratio
        observer_local=False,     # hierarchy set by cascade descent
        gauge_mediated=True,      # 2sqrt(pi) from U(1) hairy ball at d=14
        rationale="lepton mass ratio mediated by U(1) hypercharge hierarchy",
        paper_d_star=14,
        paper_k=1,
        paper_sign="+",
    ),
    Observable(
        name="m_tau absolute",
        planck_anchored=True,     # dimensional mass
        observer_local=False,
        gauge_mediated=False,
        rationale="dimensional mass anchored to Planck scale",
        paper_d_star=19,
        paper_k=1,
        paper_sign="+",
    ),
    Observable(
        name="ell_A",
        planck_anchored=True,     # dimensionless but built from r_d (Planck-anchored)
        observer_local=False,
        gauge_mediated=False,
        rationale="acoustic angle anchored via sound horizon r_d",
        paper_d_star=19,
        paper_k=1,
        paper_sign="+",
    ),
    Observable(
        name="sin^2 theta_W",
        planck_anchored=False,
        observer_local=True,      # local ratio of couplings at observer
        gauge_mediated=False,     # gauge scale factors out of ratio
        rationale="local weak-mixing ratio at observer's d=4 frame",
        paper_d_star=5,
        paper_k=3,
        paper_sign="+",
    ),
    Observable(
        name="Omega_m",
        planck_anchored=False,
        observer_local=True,      # matter density at observer today
        gauge_mediated=False,
        rationale="matter fraction at d=5 (observer-adjacent volume max)",
        paper_d_star=5,
        paper_k=3,
        paper_sign="-",
    ),
    Observable(
        name="theta_C",
        planck_anchored=False,
        observer_local=False,     # encodes inter-generation descent
        gauge_mediated=False,     # N(12),N(13) used as static normalisations
        rationale="geometric amplitude between generations, no running coupling",
        paper_d_star=7,
        paper_k=2,
        paper_sign="-",
    ),
    Observable(
        name="b/s",
        planck_anchored=False,    # mass ratio, Planck cancels
        observer_local=False,     # encodes inter-generation descent
        gauge_mediated=False,     # static SU(3)-algebra normalisation at d_0=7
        rationale="cross-generation quark mass ratio at the SU(3)-algebra layer",
        paper_d_star=7,
        paper_k=4,
        paper_sign="-",
    ),
]


def flag_str(obs: Observable) -> str:
    return (("T" if obs.planck_anchored else "F")
            + ("T" if obs.observer_local else "F")
            + ("T" if obs.gauge_mediated else "F"))


def verify() -> int:
    print("=" * 78)
    print("Source Selection Rule: Mechanical Verification")
    print("=" * 78)
    print()
    print("Flags: P = Planck-anchored, L = Observer-local, G = Gauge-mediated")
    print()
    print(f"{'observable':<18} {'PLG':<4} {'type':<10} "
          f"{'d* pred':>8} {'d* paper':>9}  match")
    print("-" * 78)

    ok_count = 0
    for obs in OBSERVABLES:
        obs_type = classify(obs)
        d_star_pred = predict_source(obs_type)
        match = "OK" if d_star_pred == obs.paper_d_star else "FAIL"
        if match == "OK":
            ok_count += 1

        print(f"{obs.name:<18} {flag_str(obs):<4} {obs_type:<10} "
              f"{d_star_pred:>8} {obs.paper_d_star:>9}  {match}")

    print("-" * 78)
    print(f"Matches: {ok_count}/{len(OBSERVABLES)}")
    print()

    # Bijection check: every non-sink distinguished layer is used.
    used = {classify(obs): predict_source(classify(obs)) for obs in OBSERVABLES}
    used_layers = frozenset(used.values())
    print(f"Non-sink distinguished layers: {sorted(NON_SINK_DISTINGUISHED)}")
    print(f"Layers used by classifier:     {sorted(used_layers)}")
    print(f"Bijection?                     "
          f"{'YES' if used_layers == NON_SINK_DISTINGUISHED else 'NO'}")
    print()

    print("Rationale (physics meta-data for each flag reading):")
    for obs in OBSERVABLES:
        print(f"  {obs.name:<18} {obs.rationale}")
    print()

    print("Under a random type->source assignment, the probability of")
    print("matching the paper's table by chance is at most 1/4! = 1/24 ~ 4.2%.")
    print("Within each type, the assigned d* is structurally unique")
    print("(see Remark 'Why the specific pairings type -> d*').")
    print()

    if ok_count == len(OBSERVABLES) and used_layers == NON_SINK_DISTINGUISHED:
        print(f"Selection rule VERIFIED on all {len(OBSERVABLES)} closed observables.")
        return 0
    print("Selection rule FAILED verification.")
    return 1


def worked_candidates() -> None:
    """Apply the rule to candidate observables not yet in the table."""
    print()
    print("=" * 78)
    print("Predictions for candidate observables not yet in the table")
    print("=" * 78)
    print()

    candidates = [
        Observable(
            name="alpha_em(M_Z)",
            planck_anchored=False,
            observer_local=False,
            gauge_mediated=True,
            rationale="running QED coupling, U(1) descent",
            paper_d_star=-1, paper_k=1, paper_sign="+",
        ),
        Observable(
            name="m_W absolute",
            planck_anchored=True,
            observer_local=False,
            gauge_mediated=False,
            rationale="dimensional W boson mass, Planck-anchored",
            paper_d_star=-1, paper_k=1, paper_sign="+",
        ),
        Observable(
            name="m_e/m_mu",
            planck_anchored=False,
            observer_local=False,
            gauge_mediated=True,
            rationale="lepton mass ratio, U(1) hypercharge hierarchy",
            paper_d_star=-1, paper_k=1, paper_sign="+",
        ),
        Observable(
            name="theta_13 (CKM)",
            planck_anchored=False,
            observer_local=False,
            gauge_mediated=False,
            rationale="pure amplitude mixing between generations",
            paper_d_star=-1, paper_k=2, paper_sign="-",
        ),
        Observable(
            name="theta_23 (CKM)",
            planck_anchored=False,
            observer_local=False,
            gauge_mediated=False,
            rationale="pure amplitude mixing between generations",
            paper_d_star=-1, paper_k=2, paper_sign="-",
        ),
    ]

    print(f"{'candidate':<18} {'PLG':<4} {'type':<10} {'predicted d*':>13}")
    print("-" * 50)
    for obs in candidates:
        obs_type = classify(obs)
        d_star = predict_source(obs_type)
        print(f"{obs.name:<18} {flag_str(obs):<4} {obs_type:<10} {d_star:>13}")
    print()
    print("Each candidate receives a sharp prediction: if its leading-order")
    print("deviation closes under alpha(d*)/chi^k with the listed d*, the")
    print("rule is confirmed. If it closes with a different d*, the rule")
    print("is falsified.")


if __name__ == "__main__":
    import sys
    status = verify()
    worked_candidates()
    sys.exit(status)
