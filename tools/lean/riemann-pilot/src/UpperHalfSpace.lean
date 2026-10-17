import Mathlib

/-! # Upper half-space and the action of `SL_2(ℂ)` (round 361)

S5f-1 of round 360's plan, part 1. Upper half-space is `{z + vj : z ∈ ℂ, v > 0}` inside the real
quaternions, and `SL_2(ℂ)` acts by `w ↦ (aw + b)(cw + d)⁻¹` (Dunn and Radziwiłł's §5.1, after
Elstrodt, Grunewald and Mennicke).

* **The action in coordinates** (`mob_uhsPt`): for `ad − bc = 1` and `v > 0`, `(a(z + vj) + b)(c(z +
  vj) + d)⁻¹ = z′ + v′j` with `z′ = ((az + b)·conj(cz + d) + a·conj c·v²)/(|cz + d|² + |c|²v²)` and
  `v′ = v/(|cz + d|² + |c|²v²)` (`uhsZ`, `uhsV`), the formula of Dunn and Radziwiłł's (5.1).
* **Composition** (`mob_comp`, `mobM_mul`): the Möbius action of a product is the composite, in any
  division ring, whenever `cw + d ≠ 0`; on upper half-space, `uhsAct_mul`: `(gh)·w = g·(h·w)` for
  `det g = det h = 1`.
* **Translations and the inversion** (`uhsAct_transl`, `uhsAct_inv`): `(1, b; 0, 1)` acts by
  `z ↦ z + b`, and `(0, −1; 1, 0)` by `(z, v) ↦ (−z̄/(|z|² + v²), v/(|z|² + v²))`.
-/

open Quaternion
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-- The point `z + vj` of upper half-space, as a real quaternion. -/
def uhsPt (z : ℂ) (v : ℝ) : ℍ := ⟨z.re, z.im, v, 0⟩

/-- The Möbius action `w ↦ (aw + b)(cw + d)⁻¹` on `ℍ`, for complex `a, b, c, d`. -/
def mobQ (a b c d : ℂ) (w : ℍ) : ℍ := ((a : ℍ) * w + (b : ℍ)) * ((c : ℍ) * w + (d : ℍ))⁻¹

/-- The denominator `|cz + d|² + |c|²v²`. -/
def uhsDen (c d z : ℂ) (v : ℝ) : ℝ := Complex.normSq (c * z + d) + Complex.normSq c * v ^ 2

/-- The horizontal coordinate of `γ(z + vj)`: `((az + b)·conj(cz + d) + a·conj c·v²)/(|cz + d|² + |c|²v²)`. -/
def uhsZ (a b c d z : ℂ) (v : ℝ) : ℂ :=
  ((a * z + b) * conj (c * z + d) + a * conj c * ((v ^ 2 : ℝ) : ℂ)) / (uhsDen c d z v : ℂ)

/-- The height of `γ(z + vj)`: `v/(|cz + d|² + |c|²v²)`. -/
def uhsV (c d z : ℂ) (v : ℝ) : ℝ := v / uhsDen c d z v

theorem uhsPt_injective {z z' : ℂ} {v v' : ℝ} (h : uhsPt z v = uhsPt z' v') : z = z' ∧ v = v' := by
  have h1 := congrArg (fun q : ℍ => q.re) h
  have h2 := congrArg (fun q : ℍ => q.imI) h
  have h3 := congrArg (fun q : ℍ => q.imJ) h
  simp only [uhsPt] at h1 h2 h3
  exact ⟨Complex.ext h1 h2, h3⟩

theorem uhsDen_nonneg (c d z : ℂ) (v : ℝ) : 0 ≤ uhsDen c d z v := by
  unfold uhsDen; have := Complex.normSq_nonneg (c * z + d); have := Complex.normSq_nonneg c; positivity

theorem uhsDen_pos {c d z : ℂ} {v : ℝ} (hv : 0 < v) (hcd : c ≠ 0 ∨ d ≠ 0) : 0 < uhsDen c d z v := by
  unfold uhsDen
  rcases hcd with hc | hd
  · have h1 := Complex.normSq_nonneg (c * z + d)
    have h2 : 0 < Complex.normSq c := Complex.normSq_pos.2 hc
    have h3 : 0 < v ^ 2 := by positivity
    nlinarith
  · by_cases hc : c = 0
    · subst hc; simp only [zero_mul, zero_add, map_zero]
      have := Complex.normSq_pos.2 hd; nlinarith
    · have h1 := Complex.normSq_nonneg (c * z + d)
      have h2 : 0 < Complex.normSq c := Complex.normSq_pos.2 hc
      have h3 : 0 < v ^ 2 := by positivity
      nlinarith

theorem cd_ne_zero_of_det {a b c d : ℂ} (hdet : a * d - b * c = 1) : c ≠ 0 ∨ d ≠ 0 := by
  by_contra h
  push Not at h
  rw [h.1, h.2] at hdet; simp at hdet

theorem uhsV_pos {a b c d z : ℂ} {v : ℝ} (hdet : a * d - b * c = 1) (hv : 0 < v) : 0 < uhsV c d z v :=
  div_pos hv (uhsDen_pos hv (cd_ne_zero_of_det hdet))

/-- `cw + d = (cz + d) + (cv)j` in coordinates. -/
theorem lin_uhsPt (c d z : ℂ) (v : ℝ) :
    (c : ℍ) * uhsPt z v + (d : ℍ) =
      ⟨(c * z + d).re, (c * z + d).im, c.re * v, c.im * v⟩ := by
  ext <;> simp [uhsPt, Quaternion.coeComplex, Complex.mul_re, Complex.mul_im]; ring

theorem normSq_lin_uhsPt (c d z : ℂ) (v : ℝ) :
    normSq ((c : ℍ) * uhsPt z v + (d : ℍ)) = uhsDen c d z v := by
  rw [lin_uhsPt, normSq_def', uhsDen, Complex.normSq_apply, Complex.normSq_apply]
  simp only
  ring

/-- **The action in coordinates**: `(a(z + vj) + b)(c(z + vj) + d)⁻¹ = uhsZ + uhsV·j` when `ad − bc = 1`. -/
theorem mob_uhsPt {a b c d : ℂ} (hdet : a * d - b * c = 1) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    mobQ a b c d (uhsPt z v) = uhsPt (uhsZ a b c d z v) (uhsV c d z v) := by
  have hD := uhsDen_pos (z := z) hv (cd_ne_zero_of_det hdet)
  have hre : (a * d - b * c).re = 1 := by rw [hdet]; simp
  have him : (a * d - b * c).im = 0 := by rw [hdet]; simp
  simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im] at hre him
  unfold mobQ
  rw [Quaternion.inv_def, normSq_lin_uhsPt, lin_uhsPt, lin_uhsPt]
  have hD' : (uhsDen c d z v : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  ext
  · simp only [uhsPt, uhsZ, Quaternion.re_mul, Quaternion.re_smul, Quaternion.imI_smul,
      Quaternion.imJ_smul, Quaternion.imK_smul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, smul_eq_mul]
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.mul_re,
      Complex.mul_im, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.normSq_ofReal]
    field_simp
    ring
  · simp only [uhsPt, uhsZ, Quaternion.imI_mul, Quaternion.re_smul, Quaternion.imI_smul,
      Quaternion.imJ_smul, Quaternion.imK_smul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, smul_eq_mul]
    rw [Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.mul_re,
      Complex.mul_im, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.normSq_ofReal]
    field_simp
    ring
  · simp only [uhsPt, uhsV, Quaternion.imJ_mul, Quaternion.re_smul, Quaternion.imI_smul,
      Quaternion.imJ_smul, Quaternion.imK_smul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, smul_eq_mul]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im]
    field_simp
    linear_combination hre
  · simp only [uhsPt, Quaternion.imK_mul, Quaternion.re_smul, Quaternion.imI_smul,
      Quaternion.imJ_smul, Quaternion.imK_smul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, smul_eq_mul]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im]
    field_simp
    linear_combination v * him

theorem mob_comp_aux {D : Type*} [DivisionRing D] (a b c d X Y : D) (hY : Y ≠ 0) :
    (a * (X * Y⁻¹) + b) * (c * (X * Y⁻¹) + d)⁻¹ = (a * X + b * Y) * (c * X + d * Y)⁻¹ := by
  have e1 : a * (X * Y⁻¹) + b = (a * X + b * Y) * Y⁻¹ := by
    rw [add_mul, mul_assoc b, mul_inv_cancel₀ hY, mul_one, mul_assoc]
  have e2 : c * (X * Y⁻¹) + d = (c * X + d * Y) * Y⁻¹ := by
    rw [add_mul, mul_assoc d, mul_inv_cancel₀ hY, mul_one, mul_assoc]
  rw [e1, e2, mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc Y⁻¹, inv_mul_cancel₀ hY, one_mul]

/-- **Composition**: `(a, b; c, d)·((a', b'; c', d')·w)` is the action of the product, whenever
`c'w + d' ≠ 0`. -/
theorem mob_comp (a b c d a' b' c' d' : ℂ) {w : ℍ} (hY : (c' : ℍ) * w + (d' : ℍ) ≠ 0) :
    mobQ a b c d (mobQ a' b' c' d' w) =
      mobQ (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') w := by
  unfold mobQ
  rw [mob_comp_aux _ _ _ _ _ _ hY]
  have e3 : (a : ℍ) * ((a' : ℍ) * w + (b' : ℍ)) + (b : ℍ) * ((c' : ℍ) * w + (d' : ℍ)) =
      ((a * a' + b * c' : ℂ) : ℍ) * w + ((a * b' + b * d' : ℂ) : ℍ) := by
    simp only [Quaternion.coeComplex_add, Quaternion.coeComplex_mul]; noncomm_ring
  have e4 : (c : ℍ) * ((a' : ℍ) * w + (b' : ℍ)) + (d : ℍ) * ((c' : ℍ) * w + (d' : ℍ)) =
      ((c * a' + d * c' : ℂ) : ℍ) * w + ((c * b' + d * d' : ℂ) : ℍ) := by
    simp only [Quaternion.coeComplex_add, Quaternion.coeComplex_mul]; noncomm_ring
  rw [e3, e4]

/-- The action of a `2 × 2` complex matrix. -/
def mobM (g : Matrix (Fin 2) (Fin 2) ℂ) (w : ℍ) : ℍ := mobQ (g 0 0) (g 0 1) (g 1 0) (g 1 1) w

theorem mobM_mul (g h : Matrix (Fin 2) (Fin 2) ℂ) {w : ℍ}
    (hY : ((h 1 0 : ℂ) : ℍ) * w + ((h 1 1 : ℂ) : ℍ) ≠ 0) :
    mobM (g * h) w = mobM g (mobM h w) := by
  unfold mobM
  rw [mob_comp _ _ _ _ _ _ _ _ hY]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The action of a matrix on upper half-space, in coordinates. -/
def uhsAct (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) (v : ℝ) : ℂ × ℝ :=
  (uhsZ (g 0 0) (g 0 1) (g 1 0) (g 1 1) z v, uhsV (g 1 0) (g 1 1) z v)

theorem det_two_eq_one (g : Matrix (Fin 2) (Fin 2) ℂ) (h : g.det = 1) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  rw [Matrix.det_fin_two] at h; exact h

theorem mobM_uhsPt {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    mobM g (uhsPt z v) = uhsPt (uhsAct g z v).1 (uhsAct g z v).2 :=
  mob_uhsPt (det_two_eq_one g hg) z hv

theorem uhsAct_pos {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    0 < (uhsAct g z v).2 := uhsV_pos (det_two_eq_one g hg) hv

/-- **The action is an action**: `(gh)·w = g·(h·w)` on upper half-space, for `det g = det h = 1`. -/
theorem uhsAct_mul {g h : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) (hh : h.det = 1) (z : ℂ) {v : ℝ}
    (hv : 0 < v) : uhsAct (g * h) z v = uhsAct g (uhsAct h z v).1 (uhsAct h z v).2 := by
  have hgh : (g * h).det = 1 := by rw [Matrix.det_mul, hg, hh, one_mul]
  have hY : ((h 1 0 : ℂ) : ℍ) * uhsPt z v + ((h 1 1 : ℂ) : ℍ) ≠ 0 := by
    intro h0
    have := normSq_lin_uhsPt (h 1 0) (h 1 1) z v
    rw [h0, map_zero] at this
    exact (uhsDen_pos hv (cd_ne_zero_of_det (det_two_eq_one h hh))).ne' this.symm
  have e := mobM_mul g h hY
  rw [mobM_uhsPt hgh z hv, mobM_uhsPt hh z hv, mobM_uhsPt hg _ (uhsAct_pos hh z hv)] at e
  obtain ⟨e1, e2⟩ := uhsPt_injective e
  exact Prod.ext e1 e2

/-- Translations act by `z ↦ z + b`. -/
theorem uhsAct_transl (b z : ℂ) (v : ℝ) : uhsAct !![1, b; 0, 1] z v = (z + b, v) := by
  simp [uhsAct, uhsZ, uhsV, uhsDen]

/-- The inversion `(0, −1; 1, 0)` acts by `(z, v) ↦ (−z̄/(|z|² + v²), v/(|z|² + v²))`. -/
theorem uhsAct_inv (z : ℂ) (v : ℝ) :
    uhsAct !![0, -1; 1, 0] z v =
      (-conj z / ((Complex.normSq z + v ^ 2 : ℝ) : ℂ), v / (Complex.normSq z + v ^ 2)) := by
  simp [uhsAct, uhsZ, uhsV, uhsDen]

end Eis

end

#print axioms Eis.uhsPt_injective
#print axioms Eis.uhsDen_nonneg
#print axioms Eis.uhsDen_pos
#print axioms Eis.cd_ne_zero_of_det
#print axioms Eis.uhsV_pos
#print axioms Eis.lin_uhsPt
#print axioms Eis.normSq_lin_uhsPt
#print axioms Eis.mob_uhsPt
#print axioms Eis.mob_comp_aux
#print axioms Eis.mob_comp
#print axioms Eis.mobM_mul
#print axioms Eis.det_two_eq_one
#print axioms Eis.mobM_uhsPt
#print axioms Eis.uhsAct_pos
#print axioms Eis.uhsAct_mul
#print axioms Eis.uhsAct_transl
#print axioms Eis.uhsAct_inv
