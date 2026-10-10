import Mathlib

/-!
# Response kernel and tone calculus (rounds 104–112 of the pilot), unconditional

* `RespKernel.response_kernel`: for a Gram family `M(s) = C + Σ_k φ_k(s)φ_k(s)ᵀ` (C symmetric, M(t) invertible) and
  `S = e ⬝ M⁻¹ e > 0`, `d/ds log S = −(2/S) Σ_k (y ⬝ φ_k)(y ⬝ φ_k')` with `y = M(t)⁻¹ e`: the first-order kernel
  `w_k = −2F_kF_k'/s` of round 104, for any family of sampling points (no RH, no zeta input).
* `ToneCalc`: the calculus of the tone formula (round 109): for the idealised phase
  `Ψ(γ,x) = γ log x + 4πx K(γ/4πx) + γ log p − 2θ(γ)` with `2θ' = log(qγ/2π)`, the γ-derivative is free of `log x`,
  stationarity is `K'(r) = log(2qr/p)`, and the x-rate there is `4π[r(1 + log(p/2qr)) + K(r)]`.
-/

open Matrix

namespace RespKernel

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- Derivative of `t ↦ v ⬝ (M t)⁻¹ v` for a differentiable family of invertible matrices. -/
theorem hasDerivAt_quad_inv {M : ℝ → Matrix n n ℝ} {M' : Matrix n n ℝ} {t : ℝ}
    (hM : HasDerivAt M M' t) (hdet : IsUnit (M t).det) (v : n → ℝ) :
    HasDerivAt (fun s => v ⬝ᵥ ((M s)⁻¹ *ᵥ v)) (-(v ⬝ᵥ (((M t)⁻¹ * M' * (M t)⁻¹) *ᵥ v))) t := by
  have hu : IsUnit (M t) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  obtain ⟨u, hu'⟩ := hu
  have hinvf : (fun s => (M s)⁻¹) = fun s => Ring.inverse (M s) := by
    funext s; exact (Matrix.nonsing_inv_eq_ringInverse (M s))
  have h0 := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu'] at h0
  have hR := h0.comp_hasDerivAt t hM
  have hui : ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) = (M t)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu', Ring.inverse_unit]
  have hR' : HasDerivAt (fun s => (M s)⁻¹) (-(M t)⁻¹ * M' * (M t)⁻¹) t := by
    rw [hinvf]
    refine hR.congr_deriv ?_
    rw [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hui, neg_mul, neg_mul]
  let L : Matrix n n ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun A => v ⬝ᵥ (A *ᵥ v)
      map_add' := by intro A B; simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := by intro c A; simp [Matrix.smul_mulVec, dotProduct_smul] }
  have hL := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t hR'
  refine hL.congr_deriv ?_
  show L _ = _
  simp [L, Matrix.neg_mulVec]


/-- For a symmetric invertible `M`: `v ⬝ (M⁻¹ M' M⁻¹) v = y ⬝ M' y` with `y = M⁻¹ v`. -/
theorem quad_sym {A M' : Matrix n n ℝ} (hA : Aᵀ = A) (v : n → ℝ) :
    v ⬝ᵥ ((A⁻¹ * M' * A⁻¹) *ᵥ v) = (A⁻¹ *ᵥ v) ⬝ᵥ (M' *ᵥ (A⁻¹ *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_nonsing_inv, hA]

/-- `vecMulVec` as a continuous bilinear map. -/
noncomputable def vmv : (n → ℝ) →L[ℝ] (n → ℝ) →L[ℝ] Matrix n n ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((n → ℝ) →ₗ[ℝ] Matrix n n ℝ) ≃ₗ[ℝ] ((n → ℝ) →L[ℝ] Matrix n n ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun a b => vecMulVec a b) (fun a a' b => add_vecMulVec a a' b)
        (fun c a b => smul_vecMulVec c a b) (fun a b b' => vecMulVec_add a b b') (fun c a b => vecMulVec_smul c a b))

omit [DecidableEq n] in
theorem vmv_apply (a b : n → ℝ) : vmv a b = vecMulVec a b := rfl

omit [DecidableEq n] in
/-- Derivative of a Gram family `C + Σ_k φ_k φ_kᵀ`. -/
theorem hasDerivAt_gram {ι : Type*} [Fintype ι] (C : Matrix n n ℝ) {φ : ι → ℝ → n → ℝ} {φ' : ι → n → ℝ} {t : ℝ}
    (hφ : ∀ k, HasDerivAt (φ k) (φ' k) t) :
    HasDerivAt (fun s => C + ∑ k, vecMulVec (φ k s) (φ k s))
      (∑ k, (vecMulVec (φ k t) (φ' k) + vecMulVec (φ' k) (φ k t))) t := by
  have h : ∀ k ∈ (Finset.univ : Finset ι), HasDerivAt (fun s => vecMulVec (φ k s) (φ k s))
      (vecMulVec (φ k t) (φ' k) + vecMulVec (φ' k) (φ k t)) t := fun k _ =>
    (vmv (n := n)).hasDerivAt_of_bilinear (fun _ => hφ k) (fun _ => hφ k)
  exact (HasDerivAt.fun_sum h).const_add C

/-- **The response kernel (round 104's first order), unconditional.** For a Gram family
`M(s) = C + Σ_k φ_k(s) φ_k(s)ᵀ` with `C` symmetric and `M(t)` invertible, and `S = e ⬝ M⁻¹ e > 0`,
`d/ds log(e ⬝ M(s)⁻¹ e) = −(2/S) Σ_k (y ⬝ φ_k)(y ⬝ φ_k')`, with `y = M(t)⁻¹ e`. -/
theorem response_kernel {ι : Type*} [Fintype ι] (C : Matrix n n ℝ) (hC : Cᵀ = C) {φ : ι → ℝ → n → ℝ}
    {φ' : ι → n → ℝ} {t : ℝ} (hφ : ∀ k, HasDerivAt (φ k) (φ' k) t)
    (hdet : IsUnit (C + ∑ k, vecMulVec (φ k t) (φ k t)).det) (e : n → ℝ)
    (hS : 0 < e ⬝ᵥ ((C + ∑ k, vecMulVec (φ k t) (φ k t))⁻¹ *ᵥ e)) :
    HasDerivAt (fun s => Real.log (e ⬝ᵥ ((C + ∑ k, vecMulVec (φ k s) (φ k s))⁻¹ *ᵥ e)))
      (-(2 / (e ⬝ᵥ ((C + ∑ k, vecMulVec (φ k t) (φ k t))⁻¹ *ᵥ e))) *
        ∑ k, (((C + ∑ j, vecMulVec (φ j t) (φ j t))⁻¹ *ᵥ e) ⬝ᵥ φ k t) *
             (((C + ∑ j, vecMulVec (φ j t) (φ j t))⁻¹ *ᵥ e) ⬝ᵥ φ' k)) t := by
  set A := C + ∑ k, vecMulVec (φ k t) (φ k t) with hAdef
  set y := A⁻¹ *ᵥ e
  have hsym : Aᵀ = A := by
    simp [hAdef, Matrix.transpose_add, Matrix.transpose_sum, transpose_vecMulVec, hC]
  have hq := hasDerivAt_quad_inv (hasDerivAt_gram C hφ) hdet e
  have hlog := hq.log hS.ne'
  rw [← hAdef] at hlog
  refine hlog.congr_deriv ?_
  rw [quad_sym hsym]
  have hsum : y ⬝ᵥ ((∑ k, (vecMulVec (φ k t) (φ' k) + vecMulVec (φ' k) (φ k t))) *ᵥ y)
      = 2 * ∑ k, (y ⬝ᵥ φ k t) * (y ⬝ᵥ φ' k) := by
    simp only [Matrix.sum_mulVec, Matrix.add_mulVec, vecMulVec_mulVec, dotProduct_sum, dotProduct_add,
      Finset.mul_sum, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, dotProduct_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dotProduct_comm (φ' k) y, dotProduct_comm (φ k t) y]; ring
  have hS0 : e ⬝ᵥ y ≠ 0 := hS.ne'
  rw [hsum]; field_simp
  rw [show e ⬝ᵥ A⁻¹ *ᵥ e = e ⬝ᵥ y from rfl, mul_div_assoc, div_self hS0, mul_one]

end RespKernel


open Real

/-! Piece 2: the tone formula's calculus (rounds 109–112), for the idealised phase
`Ψ(γ, x) = γ log x + 4πx K(γ/4πx) + γ log p − 2θ(γ)` with `2θ'(γ) = log(qγ/2π)`. -/

namespace ToneCalc

variable {K K' θ : ℝ → ℝ}

/-- The γ-derivative: `log x` cancels, leaving `K'(r) + log p − log(2qr)` with `r = γ/(4πx)`. -/
theorem hasDerivAt_gamma {p q x γ : ℝ} (hK : ∀ r, HasDerivAt K (K' r) r)
    (hθ : ∀ g, 0 < g → HasDerivAt θ (Real.log (q * g / (2 * π)) / 2) g) (hq : 0 < q) (hx : 0 < x) (hγ : 0 < γ) :
    HasDerivAt (fun g => g * Real.log x + 4 * π * x * K (g / (4 * π * x)) + g * Real.log p - 2 * θ g)
      (K' (γ / (4 * π * x)) + Real.log p - Real.log (2 * q * (γ / (4 * π * x)))) γ := by
  have hc : (4 * π * x) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun g => g * Real.log x) (Real.log x) γ := by
    simpa using (hasDerivAt_id γ).mul_const (Real.log x)
  have h2 : HasDerivAt (fun g => 4 * π * x * K (g / (4 * π * x))) (4 * π * x * (K' (γ / (4 * π * x)) * (1 / (4 * π * x)))) γ := by
    have hin : HasDerivAt (fun g => g / (4 * π * x)) (1 / (4 * π * x)) γ := by
      simpa using (hasDerivAt_id γ).div_const (4 * π * x)
    exact ((hK _).comp γ hin).const_mul (4 * π * x)
  have h3 : HasDerivAt (fun g => g * Real.log p) (Real.log p) γ := by
    simpa using (hasDerivAt_id γ).mul_const (Real.log p)
  have h4 : HasDerivAt (fun g => 2 * θ g) (2 * (Real.log (q * γ / (2 * π)) / 2)) γ := (hθ γ hγ).const_mul 2
  convert ((h1.add h2).add h3).sub h4 using 1
  have hlog : Real.log (q * γ / (2 * π)) = Real.log x + Real.log (2 * q * (γ / (4 * π * x))) := by
    rw [← Real.log_mul hx.ne' (by positivity)]
    congr 1; field_simp; ring
  rw [hlog]; field_simp; ring

/-- Stationarity in γ ⇔ `K'(r) = log(2qr/p)`. -/
theorem stationary_iff {p q r k : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    k + Real.log p - Real.log (2 * q * r) = 0 ↔ k = Real.log (2 * q * r / p) := by
  rw [Real.log_div (by positivity) hp.ne']; constructor <;> intro h <;> linarith

/-- The x-derivative at fixed γ: `4π (r + K(r) − r K'(r))`. -/
theorem hasDerivAt_x (hK : ∀ r, HasDerivAt K (K' r) r) {γ x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => γ * Real.log y + 4 * π * y * K (γ / (4 * π * y)))
      (4 * π * (γ / (4 * π * x) + K (γ / (4 * π * x)) - γ / (4 * π * x) * K' (γ / (4 * π * x)))) x := by
  have hc : (4 * π * x) ≠ 0 := by positivity
  have hinner : HasDerivAt (fun y => γ / (4 * π * y)) (-(γ * (4 * π)) / (4 * π * x) ^ 2) x := by
    have := ((hasDerivAt_id x).const_mul (4 * π)).inv (by simpa using hc)
    have := this.const_mul γ
    convert this using 1
    · funext y; simp [div_eq_mul_inv]
    · simp; field_simp
  have h1 : HasDerivAt (fun y => γ * Real.log y) (γ * x⁻¹) x := (Real.hasDerivAt_log hx.ne').const_mul γ
  have hl : HasDerivAt (fun y => 4 * π * y) (4 * π) x := by simpa using (hasDerivAt_id x).const_mul (4 * π)
  have h2 := hl.mul ((hK _).comp x hinner)
  convert h1.add h2 using 1
  · funext y; rfl
  · simp only [Function.comp]; field_simp; ring

/-- The tone: at a stationary point the x-rate is the Legendre form `4π [r(1 + log(p/2qr)) + K(r)]`. -/
theorem tone_at_stationary {p q r Kr k : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hstat : k = Real.log (2 * q * r / p)) :
    4 * π * (r + Kr - r * k) = 4 * π * (r * (1 + Real.log (p / (2 * q * r))) + Kr) := by
  rw [hstat, show p / (2 * q * r) = (2 * q * r / p)⁻¹ by field_simp, Real.log_inv]; ring

end ToneCalc

#print axioms RespKernel.hasDerivAt_quad_inv
#print axioms RespKernel.hasDerivAt_gram
#print axioms RespKernel.response_kernel
#print axioms ToneCalc.hasDerivAt_gamma
#print axioms ToneCalc.stationary_iff
#print axioms ToneCalc.hasDerivAt_x
#print axioms ToneCalc.tone_at_stationary
