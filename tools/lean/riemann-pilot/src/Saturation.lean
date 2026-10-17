import Mathlib

/-! # The saturation step, reduced to an envelope bound

Rounds 33–34's model assumes saturation: below the edge, every zeta zero `γ_j` has a zero of the
ground state's transform `ĝ` exponentially close to it. That statement is about the zeta zeros, so
it has to go through the explicit formula `Q(g) = Σ_ρ ĝ(t_ρ)²`. Off the critical line those terms are
complex and cannot be bounded one at a time, so full saturation from the prime side alone is as
hard as Hypothesis D (item 1(a)).

What is proved here is the reduction. Assume the explicit formula with the zeros on the line,
`Q = 2 Σ_{γ>0} ĝ(γ)²` (named input `hQ`). Then:
* `sq_le_of_explicit`: each `ĝ(γ_j)² ≤ Q/2 ≤ λ/2`, so `|ĝ(γ_j)| ≤ √(λ/2)`.
* `zero_near_of_deriv_ge` and `zero_near_of_deriv_le`: a function that is at most `η` in size at
  `γ`, with `|F'| ≥ m` of fixed sign on `[γ − r, γ + r]` and `η/m ≤ r`, vanishes within `η/m`
  of `γ`.
* `pinned_of_explicit`: a zero of `ĝ` lies within `√(λ/2)/m` of every `γ_j` near which `|ĝ'| ≥ m`.

So saturation holds wherever the envelope `|ĝ'|` exceeds `√λ₁`, which is the model's saturated
region. The pinning rate is `e^{−Δ}` rather than the model's `e^{−2Δ}`. What remains open is a
lower bound on the envelope, together with the explicit-formula input. -/

open Set

namespace Pilot1ca

/-- **A small value and a steep increasing slope force a nearby zero.** -/
theorem zero_near_of_deriv_ge {F : ℝ → ℝ} {γ η m r : ℝ} (hm : 0 < m) (hη : 0 ≤ η) (hr : η / m ≤ r)
    (hc : ContinuousOn F (Icc (γ - r) (γ + r))) (hd : DifferentiableOn ℝ F (Ioo (γ - r) (γ + r)))
    (hslope : ∀ x ∈ Ioo (γ - r) (γ + r), m ≤ deriv F x) (hsmall : |F γ| ≤ η) :
    ∃ x ∈ Icc (γ - η / m) (γ + η / m), F x = 0 := by
  set s := η / m with hs
  have hs0 : 0 ≤ s := div_nonneg hη hm.le
  have hms : m * s = η := by rw [hs]; field_simp
  have hint : interior (Icc (γ - r) (γ + r)) = Ioo (γ - r) (γ + r) := interior_Icc
  have key := (convex_Icc (γ - r) (γ + r)).mul_sub_le_image_sub_of_le_deriv hc
    (by rwa [hint]) (fun x hx => hslope x (by rwa [hint] at hx))
  have hr0 : 0 ≤ r := hs0.trans hr
  have mem1 : γ - s ∈ Icc (γ - r) (γ + r) := ⟨by linarith, by linarith⟩
  have mem2 : γ ∈ Icc (γ - r) (γ + r) := ⟨by linarith, by linarith⟩
  have mem3 : γ + s ∈ Icc (γ - r) (γ + r) := ⟨by linarith, by linarith⟩
  have h1 := key _ mem1 _ mem2 (by linarith)
  have h2 := key _ mem2 _ mem3 (by linarith)
  have hab := abs_le.1 hsmall
  have hlo : F (γ - s) ≤ 0 := by
    have : m * (γ - (γ - s)) = η := by rw [← hms]; ring
    linarith
  have hhi : 0 ≤ F (γ + s) := by
    have : m * (γ + s - γ) = η := by rw [← hms]; ring
    linarith
  have hsub : Icc (γ - s) (γ + s) ⊆ Icc (γ - r) (γ + r) :=
    Icc_subset_Icc (by linarith) (by linarith)
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc (by linarith : γ - s ≤ γ + s) (hc.mono hsub)
    ⟨hlo, hhi⟩
  exact ⟨x, hx, hFx⟩

/-- The decreasing case. -/
theorem zero_near_of_deriv_le {F : ℝ → ℝ} {γ η m r : ℝ} (hm : 0 < m) (hη : 0 ≤ η) (hr : η / m ≤ r)
    (hc : ContinuousOn F (Icc (γ - r) (γ + r))) (hd : DifferentiableOn ℝ F (Ioo (γ - r) (γ + r)))
    (hslope : ∀ x ∈ Ioo (γ - r) (γ + r), deriv F x ≤ -m) (hsmall : |F γ| ≤ η) :
    ∃ x ∈ Icc (γ - η / m) (γ + η / m), F x = 0 := by
  obtain ⟨x, hx, h⟩ := zero_near_of_deriv_ge (F := fun x => -F x) hm hη hr hc.neg hd.neg
    (fun x hx => by
      have := hslope x hx
      rw [deriv.fun_neg]; linarith)
    (by simpa [abs_neg] using hsmall)
  exact ⟨x, hx, by simpa using h⟩

/-- **Each term of the zero-side sum is bounded by the energy.** Named input: the explicit formula
with the zeros on the line, `Q = 2 Σ_k F(γ_k)²` (for the normalised ground state `Q = λ₁`). -/
theorem sq_le_of_explicit {F : ℝ → ℝ} {γ : ℕ → ℝ} {Q Λ : ℝ} (hs : Summable fun k => F (γ k) ^ 2)
    (hQ : Q = 2 * ∑' k, F (γ k) ^ 2) (hQΛ : Q ≤ Λ) (j : ℕ) : |F (γ j)| ≤ Real.sqrt (Λ / 2) := by
  have h1 : F (γ j) ^ 2 ≤ ∑' k, F (γ k) ^ 2 :=
    hs.le_tsum j (fun k _ => sq_nonneg _)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Saturation, reduced to the envelope.** Under the explicit formula with the zeros on the line,
if `|ĝ'| ≥ m` with fixed sign on `[γ_j − r, γ_j + r]` and `√(λ/2)/m ≤ r`, then `ĝ` has a zero within
`√(λ/2)/m` of `γ_j`. -/
theorem pinned_of_explicit {F : ℝ → ℝ} {γ : ℕ → ℝ} {Q Λ : ℝ} (hs : Summable fun k => F (γ k) ^ 2)
    (hQ : Q = 2 * ∑' k, F (γ k) ^ 2) (hQΛ : Q ≤ Λ) (j : ℕ) {m r : ℝ} (hm : 0 < m)
    (hr : Real.sqrt (Λ / 2) / m ≤ r)
    (hc : ContinuousOn F (Icc (γ j - r) (γ j + r))) (hd : DifferentiableOn ℝ F (Ioo (γ j - r) (γ j + r)))
    (hslope : (∀ x ∈ Ioo (γ j - r) (γ j + r), m ≤ deriv F x) ∨
      (∀ x ∈ Ioo (γ j - r) (γ j + r), deriv F x ≤ -m)) :
    ∃ x ∈ Icc (γ j - Real.sqrt (Λ / 2) / m) (γ j + Real.sqrt (Λ / 2) / m), F x = 0 := by
  have hsmall := sq_le_of_explicit hs hQ hQΛ j
  rcases hslope with h | h
  · exact zero_near_of_deriv_ge hm (Real.sqrt_nonneg _) hr hc hd h hsmall
  · exact zero_near_of_deriv_le hm (Real.sqrt_nonneg _) hr hc hd h hsmall

end Pilot1ca

#print axioms Pilot1ca.zero_near_of_deriv_ge
#print axioms Pilot1ca.zero_near_of_deriv_le
#print axioms Pilot1ca.sq_le_of_explicit
#print axioms Pilot1ca.pinned_of_explicit
