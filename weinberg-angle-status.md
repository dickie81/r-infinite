# Weinberg Angle from the Cascade — Honest Status Report

## Bottom line

**The cascade has not derived the Weinberg angle from first principles.**

This document records what was tried and why it didn't work, so future
attempts don't repeat the same mistakes.

## Approaches that failed

### 1. Gauge-coupling descent (Part IVb's current approach)

Compute α₂(M_Z), α₁(M_Z) from cascade descent of the bare couplings at
the gauge window {12, 13, 14} and form the ratio:

    sin²θ_W = (3/5)α₁ / ((3/5)α₁ + α₂)

**Result**: At leading order, exp(Φ(d→4)) gives α_s correctly (1.7%)
but α₂ and α₁ at M_Z are each ~39% off. The ratio gives sin²θ_W = 0.45
(off by +96%). Part IVb resorts to standard RG running as a proxy.

**Why it fails**: The cascade potential exp(Φ) is the same for all
content types at leading order. It doesn't differentiate gauge couplings
the way the SM β-functions do.

### 2. Topological obstruction at Dirac layers

Apply the (2√π)⁻¹ factor (derived in Part IVb Theorem 2.3.1 for fermion
masses) to gauge couplings that cross Dirac layers during descent.

**Result**: Best case (only U(1) gets the extra factor because it crosses
d=13 while SU(2) sits at it) gives sin²θ_W = 0.1905 (off by −17.6%).

**Why it fails**: The topological factor was derived for fermions, not
gauge bosons. The chirality-branching argument doesn't apply to vector
bosons. And even granting the factor, the numerical match is poor.

### 3. Cabibbo-style adjacent-layer angle

By analogy with Cabibbo (Part IVb Theorem 6.1), compute:
    arccos(N(14)/N(13)) modified by amplitude descent exp(-p(14)/2)

**Result**: 12.56°, sin² = 0.0473, off from observed by −80%.

**Why it fails**: This is the first-principles cascade derivation that
*does* work for Cabibbo. Its failure for Weinberg shows that the
Weinberg angle is a fundamentally different geometric object — not a
"mixing angle between consecutive gauge layers."

### 4. Pattern matching: σ(4) = 1/√4 ≈ θ_W

Notice that sin(0.5 rad) ≈ 0.481 and sin²(0.5) ≈ 0.230, very close to
the observed sin²θ_W = 0.231. The number 0.5 = 1/√4 is the Gaussian
width σ(d) = 1/√d at the observer's dimension d=4.

**Status**: Pattern match, not a derivation. There is no a priori reason
to identify the Weinberg angle (a gauge mixing angle on the SU(2) sphere)
with the cascade slicing width at the observer's dimension. The match
to 0.32% in the angle is suggestive but unsupported.

### 5. Pattern matching: ℓ_dec(13) = 2/√16 = 1/2

The same number 1/2 can be written as the cascade decoherence length
ℓ_dec(d) = 2/√(d+3) at d=13 (the SU(2) layer, forced by Bott periodicity).
This is *more* cascade-native than σ(4) because d=13 is naturally
associated with the SU(2) gauge group.

**Status**: Still pattern matching. Two problems:
- The decoherence length ℓ_dec(d) = 2 R_eff(d) has the factor of 2 from
  a definitional choice (the e⁻¹ threshold), not from a forced derivation.
  Other multiples of R_eff are equally cascade-natural.
- It doesn't generalize. The Cabibbo angle (0.2276 rad) doesn't equal
  ℓ_dec at any layer, so "Weinberg = ℓ_dec(SU(2) layer)" is not a rule.
  It's a single coincidence.

## What a real derivation would look like

A genuine first-principles derivation would:

1. Identify W³ and the photon as specific tangent vectors at a specific
   point on a specific cascade sphere.
2. Compute the angle between them using only the cascade's geometric
   structure (slicing recurrence, Bott periodicity, hairy ball obstruction).
3. The answer should fall out as a theorem, not be checked against
   the observed value.

For Cabibbo, this is exactly what Part IVb Theorem 6.1 does:
- The W³ and W⁻ couplings live at d=13, the SU(3) couplings at d=12.
- The geometric angle between them is arccos(N(13)/N(12)).
- The amplitude descent through one cascade step is exp(-p(13)/2).
- Result: tan θ_C = tan(15.78°) × exp(-p(13)/2) = 0.2356 → θ_C = 13.26°.

For Weinberg, no analogous derivation has been found. The geometric
identification of W³ and the photon as specific cascade objects has
not been worked out.

## What's still worth investigating

The most promising direction is probably:

- The Higgs lives at the hairy ball zero on S^12 (the d=13 sphere). Its
  position and the Higgs mass formula m_H/m_W = π/2 use geodesic
  distances on S^12 (Part IVa Theorem 3.3).
- The W³ direction at the Higgs VEV is tangent to the meridian (the
  great circle from the hairy ball zero to the VEV).
- The U(1)_em direction is some specific tangent direction at the VEV,
  determined by the cascade's connection between d=13 and d=14.
- The Weinberg angle is the geodesic angle between W³ and U(1)_em in
  the tangent space at the VEV.

What's missing: a cascade-natural identification of the U(1)_em direction
on the d=13 tangent space. Without this, no derivation is possible.

## Recommendation for the cascade series

Until a real derivation is found:

- **Keep the existing Part IVb treatment** (Tier 3, "standard RG as a proxy").
- **Do not promote sin²θ_W to Tier 1** based on numerical coincidences.
- **Add this status report** as a record of what's been tried and why it
  failed, so future attempts can build on it instead of rediscovering
  the same dead ends.

The user's instinct was right: retrofitting numerical coincidences into
the cascade structure is exactly the kind of thing the series is built
to make impossible. Pattern-matched results don't belong in a framework
whose central claim is "every prediction is a theorem."

## Files affected

- `tools/cascade_weinberg.py` — kept (it's an honest exploration of
  the failed scenarios, useful for future work).
- `weinberg-angle-derivation.md` — DELETED (made false claims).
- `weinberg-angle-status.md` — this file, replacing the deleted one.
