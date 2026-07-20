# Response to the External Review of `riemann-indistinguishability.md`

**Review:** `riemann-indistinguishability-review.md` (branch
`claude/riemann-indistinguishability-review-iczt8s`, reviewing commit `d162920`).
**Disposition:** 6 of 7 major/moderate findings **accepted with corrections applied**; 1
finding (F6) **answered with a new verified argument**; all 3 minor findings **fixed**. The
paper, the formulation, and the audit are amended in this commit. The review is exactly the
hostile external pass §10.3 requested, and it did its job: the headline residue count was
wrong and is now corrected.

| Finding | Disposition | Action |
|---|---|---|
| F1 — J1 is a normalization convention | **Accepted.** The polar decomposition is an identity, but the choice of the x²-normalized integral as unit-carrier is data-decided (self-dual form ⟹ E = 3, excluded ~99σ). The A38→A43 unit-redecomposition holding E fixed is fairly read as target-first. | Mechanism M restated: count-4 and ×3 derived; unit = convention, empirically anchored; residue grows. Gap ledger reverted. |
| F2 — P > L > G "derivation" is an unfalsifiable analogy | **Accepted.** No λ→∞ exists in the framework; magnitude ordering ≠ tie-break; the check cannot fail. | Remark after Thm 8 downgraded to "motivated"; residue grows; gap 5b reverted. |
| F3 — Thm 13 filters against the stored answer key | **Accepted.** The exhaustion verifies single-valuedness + arithmetic correctness, not forcedness; availability is tabulated, not computed. | Thm 13 restated as *address-book determination*; the ~60-entry size of Definition 6.1 stated explicitly; "U2 as a function" registered as the open formal target. |
| F4 — residue is six, not three | **Accepted.** Lovelock + D1 + C1 + closed grammar (A2) + unit convention + precedence. | Abstract corrected to the six-item count, attributed to the review. |
| F5 — ℓ_A σ mislabel; precision language; m_ν3 input-dependence | **Accepted on all three.** Reproducing an already-flagged mislabel was a genuine process failure. | ℓ_A → **−1.8σ** (the largest strain, stated as such); two-metric discipline added to §8; m_ν3 NuFit −2.9σ tension added. |
| F6 — the 6.2569 feature (sgn tower's critical point) | **Answered** (`cascade_feature_monoid.py`, both identities to ~4×10⁻¹⁶). The factor monoid ⟨s, s−1, Γ_ℝ(s), ζ⟩ generates only *even* shifts (s·Γ_ℝ(s) = 2π·Γ_ℝ(s+2) — how the volume feature is already inside). The odd shift requires Γ_ℝ(s)Γ_ℝ(s+1) = Γ_ℂ(s) (Legendre) — the L-factor of a **complex place, and ℚ has r₂ = 0**. So 6.2569 is a feature of odd Dirichlet L-functions, not ζ_ℚ; the observer-address pinning stands, with the feature list's completeness now argued from the arithmetic of ℚ rather than asserted. Caveat kept: "features come from ξ's factorization" is a scope definition. |
| F7 — colour-free uniqueness is conditional; JUNO tests window not form | **Accepted.** | Stated in Mechanism M itself: exclusion conditional on availability assignments; JUNO can execute the mechanism but cannot convict 3π² over its 0.1% twins — the form is decided by derivation or not at all. |
| Minors 1–3 | **Fixed.** s5 docstring now matches its output (90°/projection 0 cases); kernel bound requoted ≤7×10⁻¹⁴; T4 script enumerates all ten forms (naive 40, matching the paper). |

**Net effect on the paper's claim.** Theorem 14 survives with its conditional widened: the
non-arithmetic residue is six items, the strongest single strain in §8 is ℓ_A at −1.8σ, and
the open formal target is U2-as-a-function (computing availability from address data alone —
the theorem that would collapse the ~60-entry table toward the handful of high-level
addresses). The falsification schedule is unchanged. The review strengthened the paper in
the only way reviews can: by making its assumptions the same size as its assumptions.
