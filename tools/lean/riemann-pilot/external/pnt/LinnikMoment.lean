import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Round 536: the Guth–Maynard moment inequality

Built on Mathlib alone; no PrimeNumberTheoremAnd file is imported.

Plain statement (`moment_three`). For a complex matrix `A` with rows indexed by `ι` and columns by `κ`, and any
`b : κ → ℂ`, `‖Ab‖⁶ ≤ ‖b‖⁶ · Re tr((AAᴴ)³)`, with `‖·‖` the `ℓ²` norm. With `A_{χ,n} = c_n χ(n)` for the characters
`χ` of a finite set `W` and the integers `n` of a finite set `S` (`moment_three_chars`) this reads
`(Σ_{χ∈W} |Σ_{n∈S} b_n c_n χ(n)|²)³ ≤ (Σ_{n∈S} |b_n|²)³ · Re Σ_{χ₁,χ₂,χ₃∈W} G(χ₁,χ₂)G(χ₂,χ₃)G(χ₃,χ₁)`, where
`G(χ, χ′) = Σ_{n∈S} c_n χ(n) · conj(c_n χ′(n))` is the Gram matrix of `W` on `S`. This is the first step of the
Guth–Maynard method as Chen–Gupta–Li use it: a large value `|D(χ)| ≥ V` on all of `W` gives `|W|V² ≤ ‖Ab‖²`, so
`(|W|V²)³ ≤ ‖b‖⁶ tr(G³)`, and the rest of their argument bounds `tr(G³)`.

The proof uses no spectral theory. With `y = Ab`, `u = Aᴴy`, `z = Au` and `v = Aᴴz`, Cauchy–Schwarz gives
`‖y‖⁴ ≤ ‖b‖²‖u‖²`, `‖u‖⁴ ≤ ‖z‖²‖y‖²` and `‖z‖⁴ ≤ ‖v‖²‖u‖²`; and `v = Cy` with `C = Aᴴ(AAᴴ)`, so row by row
`‖v‖² ≤ ‖C‖_F²‖y‖²`, where `‖C‖_F² = Re tr(CCᴴ) = Re tr((AAᴴ)³)` by cyclicity of the trace. Eliminating `u`, `z`
and `v` gives the inequality.

* `norm_sum_mul_sq_le`: `|Σ a_i b_i|² ≤ (Σ|a_i|²)(Σ|b_i|²)`.
* `sum_star_mulVec`: `Σ_i conj(v_i)(Aw)_i = Σ_j conj((Aᴴv)_j)w_j`.
* `nsq_mulVec_le`: `‖Cy‖² ≤ ‖C‖_F²‖y‖²`, and `frob_eq_trace`: `‖C‖_F² = Re tr(CCᴴ)`.
* `moment_three`, `moment_three_chars`.
-/

open Matrix Finset

noncomputable section

namespace LinnikMoment

/-- The squared `ℓ²` norm `Σ_i |v_i|²`. -/
def nsq {α : Type*} [Fintype α] (v : α → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

lemma nsq_nonneg {α : Type*} [Fintype α] (v : α → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- Cauchy–Schwarz for finite sums of complex numbers. -/
lemma norm_sum_mul_sq_le {α : Type*} [Fintype α] (a b : α → ℂ) :
    ‖∑ i, a i * b i‖ ^ 2 ≤ nsq a * nsq b := by
  have h1 : ‖∑ i, a i * b i‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
  calc ‖∑ i, a i * b i‖ ^ 2 ≤ (∑ i, ‖a i‖ * ‖b i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ nsq a * nsq b := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma nsq_star {α : Type*} [Fintype α] (v : α → ℂ) : nsq (fun i => star (v i)) = nsq v := by
  simp only [nsq, norm_star]

/-- `|Σ_i conj(v_i) w_i|² ≤ ‖v‖²‖w‖²`. -/
lemma norm_inner_sq_le {α : Type*} [Fintype α] (v w : α → ℂ) :
    ‖∑ i, star (v i) * w i‖ ^ 2 ≤ nsq v * nsq w := by
  have := norm_sum_mul_sq_le (fun i => star (v i)) w
  rwa [nsq_star] at this

/-- `‖v‖²`, as a complex number, is `Σ_i conj(v_i) v_i`. -/
lemma nsq_eq_sum {α : Type*} [Fintype α] (v : α → ℂ) : (nsq v : ℂ) = ∑ i, star (v i) * v i := by
  simp only [nsq, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

/-- A nonnegative real equal, as a complex number, to `X` is `|X|`. -/
lemma eq_norm_of_ofReal_eq {r : ℝ} (hr : 0 ≤ r) {X : ℂ} (h : (r : ℂ) = X) : r = ‖X‖ := by
  rw [← h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `Σ_i conj(v_i)(Aw)_i = Σ_j conj((Aᴴv)_j)w_j`. -/
lemma sum_star_mulVec (A : Matrix ι κ ℂ) (v : ι → ℂ) (w : κ → ℂ) :
    ∑ i, star (v i) * (A *ᵥ w) i = ∑ j, star ((Aᴴ *ᵥ v) j) * w j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul', star_star,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- One Cauchy–Schwarz step: `‖Aw‖⁴ ≤ ‖Aᴴ(Aw)‖²‖w‖²`. -/
lemma nsq_sq_le (A : Matrix ι κ ℂ) (w : κ → ℂ) :
    nsq (A *ᵥ w) ^ 2 ≤ nsq (Aᴴ *ᵥ (A *ᵥ w)) * nsq w := by
  have h := (nsq_eq_sum (A *ᵥ w)).trans (sum_star_mulVec A (A *ᵥ w) w)
  rw [eq_norm_of_ofReal_eq (nsq_nonneg _) h]
  exact norm_inner_sq_le _ _

/-- The squared Frobenius norm `Σ_{j,i}|C_{ji}|²`. -/
def frob {α β : Type*} [Fintype α] [Fintype β] (C : Matrix α β ℂ) : ℝ := ∑ j, ∑ i, ‖C j i‖ ^ 2

lemma frob_nonneg {α β : Type*} [Fintype α] [Fintype β] (C : Matrix α β ℂ) : 0 ≤ frob C :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- Row by row Cauchy–Schwarz: `‖Cy‖² ≤ ‖C‖_F²‖y‖²`. -/
lemma nsq_mulVec_le {α β : Type*} [Fintype α] [Fintype β] (C : Matrix α β ℂ) (y : β → ℂ) :
    nsq (C *ᵥ y) ≤ frob C * nsq y := by
  rw [frob, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => norm_sum_mul_sq_le (fun i => C j i) y

/-- `‖C‖_F² = Re tr(CCᴴ)`. -/
lemma frob_eq_trace {α β : Type*} [Fintype α] [Fintype β] (C : Matrix α β ℂ) :
    frob C = (C * Cᴴ).trace.re := by
  simp only [frob, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- `Re tr(CCᴴ)` for `C = Aᴴ(AAᴴ)` is `Re tr((AAᴴ)³)`. -/
lemma frob_cube (A : Matrix ι κ ℂ) :
    frob (Aᴴ * (A * Aᴴ)) = (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace.re := by
  rw [frob_eq_trace]
  congr 2
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc]

/-- **The Guth–Maynard moment inequality**: `‖Ab‖⁶ ≤ ‖b‖⁶ · Re tr((AAᴴ)³)`. -/
theorem moment_three (A : Matrix ι κ ℂ) (b : κ → ℂ) :
    nsq (A *ᵥ b) ^ 3 ≤ nsq b ^ 3 * (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace.re := by
  set y := A *ᵥ b with hy
  set u := Aᴴ *ᵥ y with hu
  set z := A *ᵥ u with hz
  set v := Aᴴ *ᵥ z with hv
  set t := (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace.re with ht
  have h1 : nsq y ^ 2 ≤ nsq u * nsq b := nsq_sq_le A b
  have h2 : nsq u ^ 2 ≤ nsq z * nsq y := by
    have := nsq_sq_le Aᴴ y
    rwa [Matrix.conjTranspose_conjTranspose] at this
  have h3 : nsq z ^ 2 ≤ nsq v * nsq u := nsq_sq_le A u
  have h4 : nsq v ≤ t * nsq y := by
    have hvC : v = (Aᴴ * (A * Aᴴ)) *ᵥ y := by
      rw [hv, hz, hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hvC, ht, ← frob_cube]
    exact nsq_mulVec_le _ _
  have ht0 : 0 ≤ t := by rw [ht, ← frob_cube]; exact frob_nonneg _
  have ha := nsq_nonneg y
  have hb := nsq_nonneg b
  have hg1 := nsq_nonneg u
  have hg2 := nsq_nonneg z
  have hg3 := nsq_nonneg v
  rcases ha.eq_or_lt with ha0 | hapos
  · rw [← ha0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity
  have hg1pos : 0 < nsq u := by
    by_contra hcon
    have : nsq u = 0 := le_antisymm (not_lt.mp hcon) hg1
    rw [this, zero_mul] at h1
    nlinarith
  -- `‖u‖⁶ ≤ t‖y‖³` from h2, h3, h4
  have k1 : nsq u ^ 4 ≤ t * nsq y ^ 3 * nsq u := by
    calc nsq u ^ 4 = (nsq u ^ 2) ^ 2 := by ring
      _ ≤ (nsq z * nsq y) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      _ = nsq z ^ 2 * nsq y ^ 2 := by ring
      _ ≤ (nsq v * nsq u) * nsq y ^ 2 := by gcongr
      _ ≤ (t * nsq y * nsq u) * nsq y ^ 2 := by gcongr
      _ = t * nsq y ^ 3 * nsq u := by ring
  have k2 : nsq u ^ 3 ≤ t * nsq y ^ 3 := by
    have : nsq u ^ 3 * nsq u ≤ t * nsq y ^ 3 * nsq u := by
      calc nsq u ^ 3 * nsq u = nsq u ^ 4 := by ring
        _ ≤ _ := k1
    exact le_of_mul_le_mul_right this hg1pos
  have k3 : nsq y ^ 6 ≤ nsq b ^ 3 * t * nsq y ^ 3 := by
    calc nsq y ^ 6 = (nsq y ^ 2) ^ 3 := by ring
      _ ≤ (nsq u * nsq b) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      _ = nsq u ^ 3 * nsq b ^ 3 := by ring
      _ ≤ (t * nsq y ^ 3) * nsq b ^ 3 := by gcongr
      _ = nsq b ^ 3 * t * nsq y ^ 3 := by ring
  have hy3 : 0 < nsq y ^ 3 := by positivity
  have : nsq y ^ 3 * nsq y ^ 3 ≤ nsq b ^ 3 * t * nsq y ^ 3 := by
    calc nsq y ^ 3 * nsq y ^ 3 = nsq y ^ 6 := by ring
      _ ≤ _ := k3
  exact le_of_mul_le_mul_right this hy3

/-- The Gram matrix `G(χ, χ′) = Σ_{n∈S} c_n χ(n) · conj(c_n χ′(n))` of a set of characters on `S`. -/
def gram {q : ℕ} (S : Finset ℕ) (c : ℕ → ℂ) (χ χ' : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ S, (c n * χ n) * star (c n * χ' n)

/-- **The Guth–Maynard moment inequality over the characters mod `q`**:
`(Σ_{χ∈W}|Σ_{n∈S} b_n c_n χ(n)|²)³ ≤ (Σ_{n∈S}|b_n|²)³ · Re Σ_{χ₁,χ₂,χ₃∈W} G(χ₁,χ₂)G(χ₂,χ₃)G(χ₃,χ₁)`. -/
theorem moment_three_chars {q : ℕ} (W : Finset (DirichletCharacter ℂ q)) (S : Finset ℕ) (b c : ℕ → ℂ) :
    (∑ χ ∈ W, ‖∑ n ∈ S, c n * χ n * b n‖ ^ 2) ^ 3 ≤
      (∑ n ∈ S, ‖b n‖ ^ 2) ^ 3 *
        (∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, gram S c χ₁ χ₂ * gram S c χ₂ χ₃ * gram S c χ₃ χ₁).re := by
  let A : Matrix W S ℂ := fun χ n => c n * (χ : DirichletCharacter ℂ q) n
  let b' : S → ℂ := fun n => b n
  have hl : nsq (A *ᵥ b') = ∑ χ ∈ W, ‖∑ n ∈ S, c n * χ n * b n‖ ^ 2 := by
    simp only [nsq, Matrix.mulVec, dotProduct, A, b']
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finset.sum_coe_sort S (fun n => c n * (χ : DirichletCharacter ℂ q) n * b n)]
  have hb : nsq b' = ∑ n ∈ S, ‖b n‖ ^ 2 := by
    simp only [nsq, b']
    exact Finset.sum_coe_sort S (fun n => ‖b n‖ ^ 2)
  have hG : ∀ χ χ' : W, (A * Aᴴ) χ χ' = gram S c χ.1 χ'.1 := by
    intro χ χ'
    simp only [A, gram]
    exact Finset.sum_coe_sort S (fun n => c n * (χ : DirichletCharacter ℂ q) n *
      star (c n * (χ' : DirichletCharacter ℂ q) n))
  have ht : (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace =
      ∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, gram S c χ₁ χ₂ * gram S c χ₂ χ₃ * gram S c χ₃ χ₁ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hG, Finset.sum_mul]
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ₁ _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ₂ _ => ?_
    rw [← Finset.sum_coe_sort W]
  have := moment_three A b'
  rw [hl, hb, ht] at this
  exact this

end LinnikMoment
