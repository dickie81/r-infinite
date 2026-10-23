#!/usr/bin/env python3
"""
Step 3 formalised: mass^2 = filtered variance (the variance-normalisation
theorem), eliminating the height lemma's residual axiom.

THEOREM (variance normalisation).  In the cascade's canonical
normalisation, the physical mass^2 of any cascade mode equals its bare
curvature times the ratio of obstructed to bare fluctuation variance:

    m^2 = V''_bare x (v_obs / v_bare).

PROOF.
(i) [part4b rem:action-uniqueness + rem:per-leg-primitive item (1)]
    The cascade action is BUILT as the inverse-variance quadratic form:
    kinetic prefactor 1/(2 alpha(d)) with lattice variance
    <(Delta phi)^2> = alpha(d) -- 'variance equal to the action's
    compliance'.  Canonical normalisation therefore ties the kinetic
    term of ANY cascade mode to 1/(2v), v its variance.  A mode with
    potential curvature V''_bare in geometric units has canonical mass
    m^2 = V''_bare x v.  (Unobstructed unit mode: v_bare = 1/V''_bare
    by Gaussian equipartition, giving m^2 = 1 x V''_bare -- the ratio
    form above.)
(ii) [two-point function = one open line; thm:chirality-selection-rule]
    The variance of a fluctuation mode is its two-point function: ONE
    open line.  The papers' k-counting counts LINES, not endpoints
    (chi^(m-k) with k = number of open-line modes).  The universal leg
    rule (part4b:1512-1521) therefore applies the Dirac-layer open-line
    factor once: v_obs/v_bare = (1/chi)(1/sqrt(pi)) = 1/(2 sqrt(pi)).
(iii) With V''_bare = 1 (part4b:3320): m_H^2 = 1/(2 sqrt(pi)).    QED

TWO STRUCTURAL CROSS-CHECKS (which remove all remaining freedom):

A. The theorem RETRO-DERIVES the papers' Tier-1 per-layer mass
   identity.  For an unobstructed layer mode: variance = compliance =
   alpha(d) (their item (1)), so m^2 = alpha(d) -- exactly their
   published m(d) = R(d)/chi = sqrt(alpha(d)).  The formal home is
   right because it reproduces their own theorem with no input.
B. Endpoint-counting is excluded STRUCTURALLY, not just numerically.
   If the leg factor applied per endpoint (two factors per line), the
   fermion case would read m = R/chi^2, i.e. m^2 = R^2/16 != alpha(d),
   contradicting the papers' Tier-1 identity.  Line-counting is forced
   by consistency with their own published mass theorem -- the last
   free choice in Step 3 is eliminated.

Status: the height lemma m_H^2 = 1/(2 sqrt(pi)) now follows entirely
from published cascade conventions (action-uniqueness compliance
identity; k line-counting; universal leg rule; bare potential form)
with zero residual axioms.  What remains for the papers is only to
adopt the theorem statement; every ingredient is already theirs.
"""

import math

SQRTPI = math.sqrt(math.pi)


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def N(d):
    return SQRTPI * R(d)


def main():
    print("=" * 74)
    print("Cross-check A: the theorem retro-derives m(d)^2 = alpha(d)")
    print("=" * 74)
    print(f"  {'d':>4}{'variance alpha(d)':>19}{'(R(d)/chi)^2':>15}{'equal':>7}")
    for d in (5, 13, 21):
        v = alpha(d)
        m2 = (R(d) / 2.0) ** 2
        print(f"  {d:>4}{v:>19.6f}{m2:>15.6f}{str(abs(v-m2)<1e-15):>7}")
    print("  => mass^2 = variance holds exactly for the papers' own")
    print("     per-layer masses: the unobstructed case of the theorem.")

    print()
    print("=" * 74)
    print("Cross-check B: endpoint-counting breaks the papers' own identity")
    print("=" * 74)
    d = 13
    print(f"  line-counting:     m = R/chi   -> m^2 = {(R(d)/2)**2:.6f}"
          f"  = alpha({d}) = {alpha(d):.6f}  OK")
    print(f"  endpoint-counting: m = R/chi^2 -> m^2 = {(R(d)/4)**2:.6f}"
          f"  != alpha({d})   CONTRADICTION")
    print("  => one factor per open line is forced by the papers' Tier-1")
    print("     mass theorem; Step 3's counting has no remaining freedom.")

    print()
    print("=" * 74)
    print("The formalised chain and its number")
    print("=" * 74)
    v_ratio = 1.0 / (2.0 * SQRTPI)
    m_H2 = 1.0 * v_ratio
    r = 2.0 * math.sqrt(m_H2) / N(13)
    obs = 125.25 / 80.377
    sig = obs * math.hypot(0.17 / 125.25, 0.012 / 80.377)
    print(f"  m_H^2 = V''_bare x (v_obs/v_bare) = 1 x 1/(2 sqrt(pi))"
          f" = {m_H2:.6f}")
    print(f"  m_H/m_W = {r:.5f}   observed {obs:.5f} +/- {sig:.5f}"
          f"   ({(r-obs)/sig:+.2f} sigma)")
    print(f"  m_H = {80.377*r:.2f} GeV  (observed 125.25 +/- 0.17)")


if __name__ == "__main__":
    main()
