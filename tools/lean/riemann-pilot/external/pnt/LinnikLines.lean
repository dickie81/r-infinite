import LinnikMoment
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Round 538: the line-sum identity for prime moduli

Built on Mathlib and `LinnikMoment` (rounds 536–537); no PrimeNumberTheoremAnd file is imported.

For a prime `q`, a finite set `W` of Dirichlet characters mod `q` and residue weights `w : ZMod q → ℂ`, put
`G(χ, χ′) = Σ_a w(a)χ(a)conj(χ′(a))` (`gramZ`), `R(b) = Σ_{χ∈W} χ(b)` (`Rsum`) and `ŵ(k) = Σ_a w(a)e(−ak/q)`
(`what`, with `e(x/q)` Mathlib's `ZMod.stdAddChar`).

* `triple_eq`: `Σ_{χ₁,χ₂,χ₃∈W} G₁₂G₂₃G₃₁ = Σ_{a₁,a₂,a₃} w(a₁)w(a₂)w(a₃)R(a₂/a₁)R(a₃/a₂)R(a₁/a₃)`, by cyclicity of
  the trace: `G = A·diag(w)·Aᴴ` with `A_{χ,a} = χ(a)`, and `(AᴴA)_{a,a′} = R(a′/a)` because `conj χ(a) = χ(a⁻¹)` in
  the field `ZMod q`; `0⁻¹ = 0` and `χ(0) = 0` take care of the zero residue.
* `inversion`: `w(a) = q⁻¹Σ_k ŵ(k)e(ak/q)`.
* `sum_a_eq_lines`: with `a₂ = a₁u` and `a₃ = a₁v`, `Σ_{a₁≠0} e(a₁c/q) = q·[c = 0] − 1`.
* `line_sum_identity`: `Σ G₁₂G₂₃G₃₁ = q⁻³Σ_k ŵ(k₁)ŵ(k₂)ŵ(k₃)Σ_{u,v} R(u)R(v/u)conj(R(v))·(q·[k₁ + k₂u + k₃v = 0] − 1)`.
* `line_sum_identity_of_zero`: if `w(0) = 0`, then `Σ G₁₂G₂₃G₃₁ = q⁻²Σ_k ŵ(k₁)ŵ(k₂)ŵ(k₃)L(k)`, with the line sums
  `L(k) = Σ_{k₁ + k₂u + k₃v = 0} R(u)R(v/u)conj(R(v))` (`lineSum`), because `Σ_k ŵ(k) = q·w(0)` (`sum_what`).
* `gram_eq_gramZ`: round 536's `gram S c` is `gramZ` with the residue weights `w(a) = Σ_{n∈S, n≡a}|c_n|²` (`resW`).
* `large_values_lines`: with round 537's `refined_moment_chars`, if `|D(χ)| ≥ V` on `W`, where
  `D(χ) = Σ_{n∈S} c_nχ(n)b_n` with `S` prime to `q`, and `N_cβ ≤ |W|V²`, then
  `(|W|V² − N_cβ)³ ≤ β³(Re q⁻²Σ_k ŵ(k₁)ŵ(k₂)ŵ(k₃)L(k) − |W|N_c³)`, with `N_c = Σ|c_n|²` and `β = Σ|b_n|²`.

This is an exact finite form of Chen–Gupta–Li's Lemma 4.5 at `t = 0` for prime `q`, with their frequencies
`m ∈ ℤ³` folded modulo `q`. For the weight `w(n/N)²` on `[N, 2N]`, Poisson summation gives
`ŵ(k) = Σ_{m≡k} Nĥ(Nm/q)`. The identity does not use that; Poisson summation is needed only to show that `ŵ(k)` is
small unless `k` is within about `q/N` of `0`. The line sums are `frontier/linnik/SEVEN-THIRDS.md` §6's `L(m)`, with
`(m₁, m₂, m₃) = (k₂, k₃, k₁)`.
-/

open Matrix Finset

noncomputable section

namespace LinnikLines

variable {q : ℕ} [hq : Fact q.Prime]

/-- `R(b) = Σ_{χ∈W} χ(b)`. -/
def Rsum (W : Finset (DirichletCharacter ℂ q)) (b : ZMod q) : ℂ := ∑ χ ∈ W, χ b

/-- The Gram matrix of `W` with residue weights `w`: `G(χ, χ′) = Σ_a w(a) χ(a) conj(χ′(a))`. -/
def gramZ (w : ZMod q → ℂ) (χ χ' : DirichletCharacter ℂ q) : ℂ := ∑ a, w a * χ a * star (χ' a)

/-- The residue sums of the weight: `ŵ(k) = Σ_a w(a) e(−ak/q)`. -/
def what (w : ZMod q → ℂ) (k : ZMod q) : ℂ := ∑ a, w a * ZMod.stdAddChar (-(a * k))

lemma star_apply_eq (χ : DirichletCharacter ℂ q) (a : ZMod q) : star (χ a) = χ a⁻¹ := by
  rw [MulChar.star_apply', MulChar.inv_apply']

lemma Rsum_inv (W : Finset (DirichletCharacter ℂ q)) (b : ZMod q) : Rsum W b⁻¹ = star (Rsum W b) := by
  simp only [Rsum, star_sum, star_apply_eq]

lemma Rsum_zero (W : Finset (DirichletCharacter ℂ q)) : Rsum W 0 = 0 := by
  have : Nontrivial (ZMod q) := ZMod.nontrivial_iff.2 hq.out.one_lt.ne'
  simp only [Rsum, MulChar.map_zero, Finset.sum_const_zero]

/-- **Step 1**, by cyclicity of the trace: `Σ_{χ₁,χ₂,χ₃∈W} G₁₂G₂₃G₃₁ =
Σ_{a₁,a₂,a₃} w(a₁)w(a₂)w(a₃) R(a₂/a₁) R(a₃/a₂) R(a₁/a₃)`. -/
theorem triple_eq (W : Finset (DirichletCharacter ℂ q)) (w : ZMod q → ℂ) :
    ∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, gramZ w χ₁ χ₂ * gramZ w χ₂ χ₃ * gramZ w χ₃ χ₁ =
      ∑ a₁, ∑ a₂, ∑ a₃, w a₁ * w a₂ * w a₃ *
        (Rsum W (a₂ * a₁⁻¹) * Rsum W (a₃ * a₂⁻¹) * Rsum W (a₁ * a₃⁻¹)) := by
  set A : Matrix W (ZMod q) ℂ := Matrix.of fun χ a => (χ : DirichletCharacter ℂ q) a with hAdef
  have hA : ∀ χ a, A χ a = (χ : DirichletCharacter ℂ q) a := fun _ _ => rfl
  have hG : ∀ χ χ' : W, (A * Matrix.diagonal w * Aᴴ) χ χ' = gramZ w χ.1 χ'.1 := by
    intro χ χ'
    simp only [Matrix.mul_apply (M := A * Matrix.diagonal w), Matrix.mul_diagonal, Matrix.conjTranspose_apply, hA,
      gramZ]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hK : ∀ a a' : ZMod q, (Matrix.diagonal w * (Aᴴ * A)) a a' = w a * Rsum W (a' * a⁻¹) := by
    intro a a'
    rw [Matrix.diagonal_mul]
    congr 1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hA, Rsum]
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [star_apply_eq, ← map_mul, mul_comm]
  set G := A * Matrix.diagonal w * Aᴴ with hGdef
  have htr1 : (G * G * G).trace =
      ∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, gramZ w χ₁ χ₂ * gramZ w χ₂ χ₃ * gramZ w χ₃ χ₁ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply (M := G * G), Matrix.mul_apply (M := G) (N := G), hG,
      Finset.sum_mul]
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ₁ _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ₂ _ => ?_
    rw [← Finset.sum_coe_sort W]
  set M := Matrix.diagonal w * (Aᴴ * A) with hM
  have hcyc : (G * G * G).trace = (M * M * M).trace := by
    rw [hGdef, hM, show A * Matrix.diagonal w * Aᴴ * (A * Matrix.diagonal w * Aᴴ) * (A * Matrix.diagonal w * Aᴴ) =
        A * (Matrix.diagonal w * Aᴴ * (A * Matrix.diagonal w * Aᴴ) * (A * Matrix.diagonal w * Aᴴ)) by
          simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    congr 1
    simp only [Matrix.mul_assoc]
  have htr2 : (M * M * M).trace = ∑ a₁, ∑ a₂, ∑ a₃, w a₁ * w a₂ * w a₃ *
      (Rsum W (a₂ * a₁⁻¹) * Rsum W (a₃ * a₂⁻¹) * Rsum W (a₁ * a₃⁻¹)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply (M := M * M), Matrix.mul_apply (M := M) (N := M), hK,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a₂ _ => Finset.sum_congr rfl fun a₃ _ => by ring
  rw [← htr1, hcyc, htr2]

/-- **Step 2**, Fourier inversion on `ZMod q`: `w(a) = q⁻¹ Σ_k ŵ(k) e(ak/q)`. -/
lemma inversion (w : ZMod q → ℂ) (a : ZMod q) :
    w a = (q : ℂ)⁻¹ * ∑ k, what w k * ZMod.stdAddChar (a * k) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have key : ∑ k, what w k * ZMod.stdAddChar (a * k) = q * w a := by
    simp only [what, Finset.sum_mul]
    rw [Finset.sum_comm]
    have h : ∀ a' : ZMod q, ∑ k, w a' * ZMod.stdAddChar (-(a' * k)) * ZMod.stdAddChar (a * k) =
        w a' * (if a - a' = 0 then (q : ℂ) else 0) := by
      intro a'
      have hs := AddChar.sum_mulShift (a - a') (ZMod.isPrimitive_stdAddChar q)
      rw [ZMod.card] at hs
      simp only [Nat.cast_ite, Nat.cast_zero] at hs
      rw [← hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2; ring
    rw [Finset.sum_congr rfl fun a' _ => h a']
    simp only [sub_eq_zero, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [mul_comm]
  rw [key, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]

/-- **Step 3**: with `a₂ = a₁u` and `a₃ = a₁v`, the sum over `a₁ ≠ 0` is `q·[k₁ + k₂u + k₃v = 0] − 1`. -/
theorem sum_a_eq_lines (W : Finset (DirichletCharacter ℂ q)) (k₁ k₂ k₃ : ZMod q) :
    ∑ a₁, ∑ a₂, ∑ a₃, ZMod.stdAddChar (a₁ * k₁ + a₂ * k₂ + a₃ * k₃) *
        (Rsum W (a₂ * a₁⁻¹) * Rsum W (a₃ * a₂⁻¹) * Rsum W (a₁ * a₃⁻¹)) =
      ∑ u, ∑ v, Rsum W u * Rsum W (v * u⁻¹) * star (Rsum W v) *
        ((if k₁ + k₂ * u + k₃ * v = 0 then (q : ℂ) else 0) - 1) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
  have h0 : ∑ a₂, ∑ a₃, ZMod.stdAddChar (0 * k₁ + a₂ * k₂ + a₃ * k₃) *
      (Rsum W (a₂ * 0⁻¹) * Rsum W (a₃ * a₂⁻¹) * Rsum W (0 * a₃⁻¹)) = 0 := by
    simp [Rsum_zero]
  rw [h0, zero_add]
  have hx : ∀ x ∈ univ.erase (0 : ZMod q), ∑ a₂, ∑ a₃, ZMod.stdAddChar (x * k₁ + a₂ * k₂ + a₃ * k₃) *
      (Rsum W (a₂ * x⁻¹) * Rsum W (a₃ * a₂⁻¹) * Rsum W (x * a₃⁻¹)) =
      ∑ u, ∑ v, ZMod.stdAddChar (x * (k₁ + k₂ * u + k₃ * v)) *
        (Rsum W u * Rsum W (v * u⁻¹) * star (Rsum W v)) := by
    intro x hx
    have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ x hx0)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ x hx0)]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Equiv.mulLeft₀_apply]
    have e1 : x * u * x⁻¹ = u := by rw [mul_comm x u, mul_assoc, mul_inv_cancel₀ hx0, mul_one]
    have e2 : x * v * (x * u)⁻¹ = v * u⁻¹ := by
      rw [mul_inv, show x * v * (x⁻¹ * u⁻¹) = x * x⁻¹ * (v * u⁻¹) by ring, mul_inv_cancel₀ hx0, one_mul]
    have e3 : x * (x * v)⁻¹ = v⁻¹ := by rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
    rw [e1, e2, e3, Rsum_inv]
    congr 2; ring
  rw [Finset.sum_congr rfl hx, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_mul, mul_comm]
  congr 1
  have hs := AddChar.sum_mulShift (k₁ + k₂ * u + k₃ * v) (ZMod.isPrimitive_stdAddChar q)
  rw [ZMod.card, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))] at hs
  simp only [zero_mul, AddChar.map_zero_eq_one, Nat.cast_ite, Nat.cast_zero] at hs
  rw [eq_sub_iff_add_eq, add_comm, hs]

/-- Moving one outer sum past three inner ones. -/
lemma swap_out {α β : Type*} [Fintype α] [Fintype β] (G : α → α → α → β → ℂ) :
    ∑ a₁, ∑ a₂, ∑ a₃, ∑ k, G a₁ a₂ a₃ k = ∑ k, ∑ a₁, ∑ a₂, ∑ a₃, G a₁ a₂ a₃ k := by
  calc ∑ a₁, ∑ a₂, ∑ a₃, ∑ k, G a₁ a₂ a₃ k = ∑ a₁, ∑ a₂, ∑ k, ∑ a₃, G a₁ a₂ a₃ k :=
        Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => Finset.sum_comm
    _ = ∑ a₁, ∑ k, ∑ a₂, ∑ a₃, G a₁ a₂ a₃ k := Finset.sum_congr rfl fun a₁ _ => Finset.sum_comm
    _ = ∑ k, ∑ a₁, ∑ a₂, ∑ a₃, G a₁ a₂ a₃ k := Finset.sum_comm

/-- **The line-sum identity** (Chen–Gupta–Li's Lemma 4.5 at `t = 0`, folded modulo `q`). -/
theorem line_sum_identity (W : Finset (DirichletCharacter ℂ q)) (w : ZMod q → ℂ) :
    ∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, gramZ w χ₁ χ₂ * gramZ w χ₂ χ₃ * gramZ w χ₃ χ₁ =
      (q : ℂ)⁻¹ ^ 3 * ∑ k₁, ∑ k₂, ∑ k₃, what w k₁ * what w k₂ * what w k₃ *
        ∑ u, ∑ v, Rsum W u * Rsum W (v * u⁻¹) * star (Rsum W v) *
          ((if k₁ + k₂ * u + k₃ * v = 0 then (q : ℂ) else 0) - 1) := by
  have hw3 : ∀ a₁ a₂ a₃ : ZMod q, w a₁ * w a₂ * w a₃ = (q : ℂ)⁻¹ ^ 3 * ∑ k₁, ∑ k₂, ∑ k₃,
      what w k₁ * what w k₂ * what w k₃ * ZMod.stdAddChar (a₁ * k₁ + a₂ * k₂ + a₃ * k₃) := by
    intro a₁ a₂ a₃
    calc w a₁ * w a₂ * w a₃ = (q : ℂ)⁻¹ ^ 3 * ((∑ k₁, what w k₁ * ZMod.stdAddChar (a₁ * k₁)) *
        (∑ k₂, what w k₂ * ZMod.stdAddChar (a₂ * k₂)) * (∑ k₃, what w k₃ * ZMod.stdAddChar (a₃ * k₃))) := by
          rw [inversion w a₁, inversion w a₂, inversion w a₃]; ring
      _ = (q : ℂ)⁻¹ ^ 3 * ∑ k₁, ∑ k₂, ∑ k₃, (what w k₁ * ZMod.stdAddChar (a₁ * k₁)) *
          (what w k₂ * ZMod.stdAddChar (a₂ * k₂)) * (what w k₃ * ZMod.stdAddChar (a₃ * k₃)) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun k₁ _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k₂ _ => ?_
          rw [Finset.mul_sum]
      _ = _ := by
          congr 1
          refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ =>
            Finset.sum_congr rfl fun k₃ _ => ?_
          rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
          ring
  have hR : ∀ k₁ k₂ k₃ : ZMod q, (∑ u, ∑ v, Rsum W u * Rsum W (v * u⁻¹) * star (Rsum W v) *
      ((if k₁ + k₂ * u + k₃ * v = 0 then (q : ℂ) else 0) - 1)) =
      ∑ a₁, ∑ a₂, ∑ a₃, ZMod.stdAddChar (a₁ * k₁ + a₂ * k₂ + a₃ * k₃) *
        (Rsum W (a₂ * a₁⁻¹) * Rsum W (a₃ * a₂⁻¹) * Rsum W (a₁ * a₃⁻¹)) :=
    fun k₁ k₂ k₃ => (sum_a_eq_lines W k₁ k₂ k₃).symm
  rw [triple_eq]
  simp only [hR, hw3]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [swap_out]
  refine Finset.sum_congr rfl fun k₁ _ => ?_
  rw [swap_out]
  refine Finset.sum_congr rfl fun k₂ _ => ?_
  rw [swap_out]
  refine Finset.sum_congr rfl fun k₃ _ => ?_
  refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ =>
    Finset.sum_congr rfl fun a₃ _ => by ring


/-- `Σ_k ŵ(k) = q·w(0)`. -/
lemma sum_what (w : ZMod q → ℂ) : ∑ k, what w k = q * w 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have h := inversion w 0
  simp only [zero_mul, AddChar.map_zero_eq_one, mul_one] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]

/-- The line sum `L(k) = Σ_{k₁ + k₂u + k₃v = 0} R(u) R(v/u) conj R(v)`. -/
def lineSum (W : Finset (DirichletCharacter ℂ q)) (k₁ k₂ k₃ : ZMod q) : ℂ :=
  ∑ u, ∑ v, if k₁ + k₂ * u + k₃ * v = 0 then Rsum W u * Rsum W (v * u⁻¹) * star (Rsum W v) else 0

/-- **The line-sum identity for weights off `0`**: if `w(0) = 0`, then
`Σ_{χ₁,χ₂,χ₃∈W} G₁₂G₂₃G₃₁ = q⁻² Σ_k ŵ(k₁)ŵ(k₂)ŵ(k₃) L(k)`. -/
theorem line_sum_identity_of_zero (W : Finset (DirichletCharacter ℂ q)) (w : ZMod q → ℂ) (h0 : w 0 = 0) :
    ∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, gramZ w χ₁ χ₂ * gramZ w χ₂ χ₃ * gramZ w χ₃ χ₁ =
      (q : ℂ)⁻¹ ^ 2 * ∑ k₁, ∑ k₂, ∑ k₃, what w k₁ * what w k₂ * what w k₃ * lineSum W k₁ k₂ k₃ := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  set T₀ := ∑ u, ∑ v, Rsum W u * Rsum W (v * u⁻¹) * star (Rsum W v) with hT₀
  have hsplit : ∀ k₁ k₂ k₃ : ZMod q, (∑ u, ∑ v, Rsum W u * Rsum W (v * u⁻¹) * star (Rsum W v) *
      ((if k₁ + k₂ * u + k₃ * v = 0 then (q : ℂ) else 0) - 1)) = q * lineSum W k₁ k₂ k₃ - T₀ := by
    intro k₁ k₂ k₃
    simp only [lineSum, hT₀, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring
  rw [line_sum_identity]
  have hs2 : ∑ k₁, ∑ k₂, ∑ k₃, what w k₁ * what w k₂ * what w k₃ *
      (∑ u, ∑ v, Rsum W u * Rsum W (v * u⁻¹) * star (Rsum W v) *
        ((if k₁ + k₂ * u + k₃ * v = 0 then (q : ℂ) else 0) - 1)) =
      ∑ k₁, ∑ k₂, ∑ k₃, what w k₁ * what w k₂ * what w k₃ * (q * lineSum W k₁ k₂ k₃ - T₀) :=
    Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ =>
      Finset.sum_congr rfl fun k₃ _ => by rw [hsplit]
  rw [hs2]
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hz : ∑ k₁, ∑ k₂, ∑ k₃, what w k₁ * what w k₂ * what w k₃ * T₀ = 0 := by
    have e : ∑ k₁, ∑ k₂, ∑ k₃, what w k₁ * what w k₂ * what w k₃ * T₀ = (∑ k, what w k) ^ 3 * T₀ := by
      simp only [pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ =>
        Finset.sum_congr rfl fun k₃ _ => by ring
    rw [e, sum_what, h0, mul_zero, zero_pow (by norm_num), zero_mul]
  rw [hz, mul_zero, sub_zero, Finset.mul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ =>
    Finset.sum_congr rfl fun k₃ _ => ?_
  field_simp

/-- The residue weights of `c` on `S`: `w(a) = Σ_{n∈S, n ≡ a} |c_n|²`. -/
def resW (S : Finset ℕ) (c : ℕ → ℂ) (a : ZMod q) : ℂ :=
  ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = a), ((‖c n‖ ^ 2 : ℝ) : ℂ)

/-- The Gram matrix on `S` is the Gram matrix with the residue weights of `c`. -/
lemma gram_eq_gramZ (S : Finset ℕ) (c : ℕ → ℂ) (χ χ' : DirichletCharacter ℂ q) :
    LinnikMoment.gram S c χ χ' = gramZ (resW S c) χ χ' := by
  simp only [LinnikMoment.gram, gramZ, resW, Finset.sum_mul]
  have e : ∀ x : ZMod q, ∑ i ∈ S.filter (fun n : ℕ => (n : ZMod q) = x),
      ((‖c i‖ ^ 2 : ℝ) : ℂ) * χ x * star (χ' x) = ∑ i ∈ S.filter (fun n : ℕ => (n : ZMod q) = x),
      ((‖c i‖ ^ 2 : ℝ) : ℂ) * χ (i : ZMod q) * star (χ' (i : ZMod q)) :=
    fun x => Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
  rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_fiberwise S (fun n => (n : ZMod q))
    (fun n => ((‖c n‖ ^ 2 : ℝ) : ℂ) * χ (n : ZMod q) * star (χ' (n : ZMod q)))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [star_mul', show (c n * χ n) * (star (c n) * star (χ' n)) = (c n * star (c n)) * χ n * star (χ' n) by ring,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

lemma resW_zero (S : Finset ℕ) (c : ℕ → ℂ) (hS : ∀ n ∈ S, IsUnit (n : ZMod q)) : resW S c (0 : ZMod q) = 0 := by
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Finset.mem_filter] at hn
  exact absurd (hn.2 ▸ hS n hn.1) not_isUnit_zero

lemma gram_self (S : Finset ℕ) (c : ℕ → ℂ) (hS : ∀ n ∈ S, IsUnit (n : ZMod q)) (χ : DirichletCharacter ℂ q) :
    LinnikMoment.gram S c χ χ = ((∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
  simp only [LinnikMoment.gram, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨u, hu⟩ := hS n hn
  have h1 : ‖χ n‖ = 1 := by rw [← hu]; exact DirichletCharacter.unit_norm_eq_one χ u
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, h1, mul_one, Complex.ofReal_pow]

/-- **Large values and the line sums** (Chen–Gupta–Li's Lemmas 4.1, 4.2 and 4.5 at `t = 0` for prime `q`, folded
modulo `q`). If `|D(χ)| ≥ V` for every `χ ∈ W`, where `D(χ) = Σ_{n∈S} c_n χ(n) b_n` with `S` prime to `q`, and
`N_cβ ≤ |W|V²` for `N_c = Σ|c_n|²` and `β = Σ|b_n|²`, then
`(|W|V² − N_cβ)³ ≤ β³ (Re q⁻² Σ_k ŵ(k₁)ŵ(k₂)ŵ(k₃) L(k) − |W|N_c³)`, where `ŵ` are the residue sums of the weights
`|c_n|²` and `L(k)` the line sums of `R(b) = Σ_{χ∈W} χ(b)`. -/
theorem large_values_lines [DecidableEq (DirichletCharacter ℂ q)] (W : Finset (DirichletCharacter ℂ q))
    (S : Finset ℕ) (b c : ℕ → ℂ) (hS : ∀ n ∈ S, IsUnit (n : ZMod q)) {V : ℝ}
    (hV : ∀ χ ∈ W, V ^ 2 ≤ ‖∑ n ∈ S, c n * χ n * b n‖ ^ 2)
    (hge : (∑ n ∈ S, ‖c n‖ ^ 2) * (∑ n ∈ S, ‖b n‖ ^ 2) ≤ W.card * V ^ 2) :
    (W.card * V ^ 2 - (∑ n ∈ S, ‖c n‖ ^ 2) * (∑ n ∈ S, ‖b n‖ ^ 2)) ^ 3 ≤
      (∑ n ∈ S, ‖b n‖ ^ 2) ^ 3 * (((q : ℂ)⁻¹ ^ 2 * ∑ k₁, ∑ k₂, ∑ k₃,
        what (resW S c) k₁ * what (resW S c) k₂ * what (resW S c) k₃ * lineSum W k₁ k₂ k₃).re -
          W.card * (∑ n ∈ S, ‖c n‖ ^ 2) ^ 3) := by
  set Nc := ∑ n ∈ S, ‖c n‖ ^ 2 with hNc
  set β := ∑ n ∈ S, ‖b n‖ ^ 2 with hβ
  set Sd := ∑ χ ∈ W, ‖∑ n ∈ S, c n * χ n * b n‖ ^ 2 with hSd
  have hsum : W.card * V ^ 2 ≤ Sd := by
    have := Finset.sum_le_sum hV
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have key := LinnikMoment.refined_moment_chars W S b c hS (le_trans hge hsum)
  -- the triples that are not all equal, through the line sums
  have hsplit := LinnikMoment.sum_triples_split W
    (fun χ₁ χ₂ χ₃ => LinnikMoment.gram S c χ₁ χ₂ * LinnikMoment.gram S c χ₂ χ₃ * LinnikMoment.gram S c χ₃ χ₁)
  have hdiag : ∑ a ∈ W, LinnikMoment.gram S c a a * LinnikMoment.gram S c a a * LinnikMoment.gram S c a a =
      ((W.card * Nc ^ 3 : ℝ) : ℂ) := by
    simp only [gram_self S c hS, Finset.sum_const, nsmul_eq_mul, ← hNc]; push_cast; ring
  have hall : ∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W,
      LinnikMoment.gram S c χ₁ χ₂ * LinnikMoment.gram S c χ₂ χ₃ * LinnikMoment.gram S c χ₃ χ₁ =
      (q : ℂ)⁻¹ ^ 2 * ∑ k₁, ∑ k₂, ∑ k₃,
        what (resW S c) k₁ * what (resW S c) k₂ * what (resW S c) k₃ * lineSum W k₁ k₂ k₃ := by
    simp only [gram_eq_gramZ]
    exact line_sum_identity_of_zero W (resW S c) (resW_zero S c hS)
  have hX : (∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, if χ₁ = χ₂ ∧ χ₂ = χ₃ then 0 else
      LinnikMoment.gram S c χ₁ χ₂ * LinnikMoment.gram S c χ₂ χ₃ * LinnikMoment.gram S c χ₃ χ₁).re =
      ((q : ℂ)⁻¹ ^ 2 * ∑ k₁, ∑ k₂, ∑ k₃,
        what (resW S c) k₁ * what (resW S c) k₂ * what (resW S c) k₃ * lineSum W k₁ k₂ k₃).re - W.card * Nc ^ 3 := by
    rw [← hall, hsplit, hdiag, Complex.add_re, Complex.ofReal_re]; ring
  rw [hX] at key
  have h0 : 0 ≤ W.card * V ^ 2 - Nc * β := by linarith
  calc (W.card * V ^ 2 - Nc * β) ^ 3 ≤ (Sd - Nc * β) ^ 3 := pow_le_pow_left₀ h0 (by linarith) 3
    _ ≤ _ := key

end LinnikLines
