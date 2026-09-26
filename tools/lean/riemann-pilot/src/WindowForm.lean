import Mathlib

/-!
# The prime-side window form: its algebra, its certification logic, and the counterexample mechanism (rounds 118–119)

Unconditional: no hypothesis about ζ, RH or any zero appears.

**Round 118: closed forms.** The window basis is `φ_k(u) = cos(ω_k u)` on `[−a, a]` with `ω_k = kπ/a`.
* `ghat_cos`: its transform is `∫ cos(ω_k u) cos(tu) du = (−1)^k · 2t sin(ta)/(t² − ω_k²)`. These are the rows of every chain
  since round 95.
* `ghat_pole`: at the pole, `∫ cos(ω_k u) cosh(u/2) du = (−1)^k sinh(a/2)/(ω_k² + ¼)`. This is the rank-one pole term.
* `product_dd`, `hasDerivAt_uA`: the product of two transforms is a divided difference, in `A = ω²`, of `u_A = A sin²(ta)/(t² − A)`.
  On the diagonal it is the `A`-derivative. So every linear functional of `ĝ_j ĝ_k` reduces to one scalar function.
* `phi_u_trig`, `basis_trig`: the trigonometric reduction of the prime term `Φ_u`, and the values at the basis frequencies.

**Round 119: certification logic.**
* `posDef_of_cholesky`: `L Lᵀ` is positive definite if `L` is lower triangular with a positive diagonal. This is the
  certificate that the arb Cholesky produces.
* `gram_quadratic`, `gram_pos`: a positive-definite Gram matrix makes the form strictly positive on every nonzero
  combination of the basis.

**Round 119: the counterexample mechanism.**
* `quadruple_sum`: for a transform that is even and real on the real axis, the four points `±γ₀ ± iδ` (the zeros
  `½ ± δ + iγ₀` and their conjugates) contribute `4 Re ĝ(γ₀ + iδ)²` to `Σ_ρ ĝ(γ_ρ)²`.
* `offline_second_order`: if `F(γ₀) = 0` and `F'(γ₀) = c` is real, then `Re F(γ₀ + iδ)² = −c²δ² + o(δ²)`.
* `offline_negative`: consequently, if `c ≠ 0`, that contribution is strictly negative for all small `δ ≠ 0`. An off-line
  pair next to a zero of the test transform pushes the form negative. This is how positivity is lost past the horizon.

**Not formalised** (hand derivations or classical inputs, checked numerically):
* the Guinand–Weil explicit formula;
* the principal-value and digamma evaluations of the archimedean term;
* the arb enclosures themselves;
* the empirical horizon `x_h = γ₀/(4π · 0.8613)`.
-/

open Real Complex Filter Asymptotics Topology Matrix

namespace WindowForm

/-! ### Closed forms (round 118) -/

theorem sin_sub_nat_mul_pi (y : ℝ) (k : ℕ) : Real.sin (y - k * π) = (-1) ^ k * Real.sin y := by
  rw [Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]; ring

theorem sin_add_nat_mul_pi (y : ℝ) (k : ℕ) : Real.sin (y + k * π) = (-1) ^ k * Real.sin y := by
  rw [Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]; ring

/-- **General closed forms** on `[−a, a]` (used for the Gram entries in PoleRelax.lean). -/
theorem int_coshsq {a : ℝ} : (∫ t in (-a)..a, Real.cosh (t / 2) * Real.cosh (t / 2)) = a + Real.sinh a := by
  have hd : ∀ t ∈ Set.uIcc (-a) a, HasDerivAt (fun t => (t + Real.sinh t) / 2)
      (Real.cosh (t / 2) * Real.cosh (t / 2)) t := by
    intro t _
    have := ((hasDerivAt_id t).add (Real.hasDerivAt_sinh t)).div_const 2
    convert this using 1
    · rfl
    have h1 : Real.cosh t = Real.cosh (2 * (t / 2)) := by ring_nf
    rw [h1, Real.cosh_two_mul]; have := Real.cosh_sq (t / 2); nlinarith [this]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t => Real.cosh (t / 2) * Real.cosh (t / 2)).intervalIntegrable _ _),
    Real.sinh_neg]
  ring

theorem int_cosh_cos {a : ℝ} (ω : ℝ) :
    (∫ t in (-a)..a, Real.cosh (t / 2) * Real.cos (ω * t))
      = (Real.cos (ω * a) * Real.sinh (a / 2) + 2 * ω * Real.sin (ω * a) * Real.cosh (a / 2)) / (ω ^ 2 + 1 / 4) := by
  have hden : ω ^ 2 + 1 / 4 ≠ 0 := by positivity
  have hderiv : ∀ u ∈ Set.uIcc (-a) a, HasDerivAt
      (fun u => (1 / 2 * Real.cos (ω * u) * Real.sinh (u / 2) + ω * Real.sin (ω * u) * Real.cosh (u / 2)) / (ω ^ 2 + 1 / 4))
      (Real.cosh (u / 2) * Real.cos (ω * u)) u := by
    intro u _
    have hc := ((hasDerivAt_id u).const_mul ω).cos
    have hs := ((hasDerivAt_id u).const_mul ω).sin
    have hsh := ((hasDerivAt_id u).div_const 2).sinh
    have hch := ((hasDerivAt_id u).div_const 2).cosh
    have := (((hc.const_mul (1 / 2)).mul hsh).add ((hs.const_mul ω).mul hch)).div_const (ω ^ 2 + 1 / 4)
    convert this using 1
    · funext v; simp [id]
    · simp only [id, mul_one]; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun u => Real.cosh (u / 2) * Real.cos (ω * u)).intervalIntegrable _ _)]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, neg_div, Real.sinh_neg, Real.cosh_neg]
  field_simp; ring

theorem int_cos_cos {a α β : ℝ} (hm : α - β ≠ 0) (hp : α + β ≠ 0) :
    (∫ t in (-a)..a, Real.cos (α * t) * Real.cos (β * t))
      = Real.sin ((α - β) * a) / (α - β) + Real.sin ((α + β) * a) / (α + β) := by
  have hderiv : ∀ u ∈ Set.uIcc (-a) a, HasDerivAt
      (fun u => (Real.sin ((α - β) * u) / (α - β) + Real.sin ((α + β) * u) / (α + β)) / 2)
      (Real.cos (α * u) * Real.cos (β * u)) u := by
    intro u _
    have e1 := (((hasDerivAt_id u).const_mul (α - β)).sin).div_const (α - β)
    have e2 := (((hasDerivAt_id u).const_mul (α + β)).sin).div_const (α + β)
    have := (e1.add e2).div_const 2
    convert this using 1
    · funext v; simp [id]
    · simp only [id, mul_one]
      rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun u => Real.cos (α * u) * Real.cos (β * u)).intervalIntegrable _ _)]
  simp only [mul_neg, Real.sin_neg, neg_div]; ring

theorem int_cos_sq {a α : ℝ} (hα : α ≠ 0) :
    (∫ t in (-a)..a, Real.cos (α * t) * Real.cos (α * t)) = a + Real.sin (2 * α * a) / (2 * α) := by
  have hderiv : ∀ u ∈ Set.uIcc (-a) a, HasDerivAt (fun u => u / 2 + Real.sin (2 * α * u) / (4 * α))
      (Real.cos (α * u) * Real.cos (α * u)) u := by
    intro u _
    have e1 := (hasDerivAt_id u).div_const 2
    have e2 := (((hasDerivAt_id u).const_mul (2 * α)).sin).div_const (4 * α)
    convert e1.add e2 using 1
    · funext v; simp [id]
    · simp only [id, mul_one]
      rw [show 2 * α * u = 2 * (α * u) by ring, Real.cos_two_mul]; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun u => Real.cos (α * u) * Real.cos (α * u)).intervalIntegrable _ _)]
  simp only [mul_neg, Real.sin_neg, neg_div]; ring

/-- The window basis transform: `∫_{−a}^{a} cos(ω_k u) cos(tu) du = (−1)^k 2t sin(ta)/(t² − ω_k²)`. -/
theorem ghat_cos {a t : ℝ} (k : ℕ) (ha : 0 < a) (h1 : t ≠ k * π / a) (h2 : t ≠ -(k * π / a)) :
    ∫ u in (-a)..a, Real.cos (k * π / a * u) * Real.cos (t * u) =
      (-1) ^ k * (2 * t * Real.sin (t * a) / (t ^ 2 - (k * π / a) ^ 2)) := by
  set ω := k * π / a with hω
  have hm : ω - t ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hp : ω + t ≠ 0 := by intro h; apply h2; linarith
  have hωa : ω * a = k * π := by rw [hω]; field_simp
  rw [int_cos_cos hm hp, sub_mul, add_mul, hωa, show (k : ℝ) * π - t * a = -(t * a - k * π) by ring,
    Real.sin_neg, sin_sub_nat_mul_pi, add_comm (k * π), sin_add_nat_mul_pi]
  have hsq : t ^ 2 - ω ^ 2 ≠ 0 := by
    rw [show t ^ 2 - ω ^ 2 = -((ω - t) * (ω + t)) by ring]; exact neg_ne_zero.2 (mul_ne_zero hm hp)
  field_simp
  ring

/-- The pole value: `∫_{−a}^{a} cos(ω_k u) cosh(u/2) du = (−1)^k sinh(a/2)/(ω_k² + ¼)`. -/
theorem ghat_pole {a : ℝ} (k : ℕ) (ha : 0 < a) :
    ∫ u in (-a)..a, Real.cos (k * π / a * u) * Real.cosh (u / 2) =
      (-1) ^ k * Real.sinh (a / 2) / ((k * π / a) ^ 2 + 1 / 4) := by
  have hωa : k * π / a * a = k * π := by field_simp
  simp_rw [mul_comm (Real.cos _)]
  rw [int_cosh_cos, hωa, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  ring

/-- Products of transforms are divided differences: `s/((s − A)(s − B)) = (A/(s − A) − B/(s − B))/(A − B)`. -/
theorem product_dd {s A B : ℝ} (hA : s ≠ A) (hB : s ≠ B) (hAB : A ≠ B) :
    s / ((s - A) * (s - B)) = (A / (s - A) - B / (s - B)) / (A - B) := by
  have h1 : s - A ≠ 0 := sub_ne_zero.mpr hA
  have h2 : s - B ≠ 0 := sub_ne_zero.mpr hB
  have h3 : A - B ≠ 0 := sub_ne_zero.mpr hAB
  field_simp; ring

/-- On the diagonal, the divided difference becomes the `A`-derivative of `u_A = A c/(s − A)`, which is `c s/(s − A)²`.
With `s = t²` and `c = sin²(ta)`, `4` times it is `ĝ_k(t)²`. -/
theorem hasDerivAt_uA {s c A : ℝ} (hA : s ≠ A) :
    HasDerivAt (fun B => B * c / (s - B)) (c * s / (s - A) ^ 2) A := by
  have h1 : s - A ≠ 0 := sub_ne_zero.mpr hA
  have := ((hasDerivAt_id A).mul_const c).div ((hasDerivAt_const A s).sub (hasDerivAt_id A)) h1
  convert this using 1
  · funext B; simp [Pi.div_apply]
  · simp only [id, Pi.sub_apply]; field_simp; ring

/-- The prime term's trigonometric reduction:
`½ sin(uω) − ¼ sin((2a + u)ω) − ¼ sin((2a − u)ω) = ½[sin(uω) − sin(2aω) cos(uω)]`. -/
theorem phi_u_trig (a u ω : ℝ) :
    1 / 2 * Real.sin (u * ω) - 1 / 4 * Real.sin ((2 * a + u) * ω) - 1 / 4 * Real.sin ((2 * a - u) * ω) =
      1 / 2 * (Real.sin (u * ω) - Real.sin (2 * a * ω) * Real.cos (u * ω)) := by
  rw [add_mul, sub_mul, Real.sin_add, Real.sin_sub]; ring

/-- At the basis frequencies `ω_k = kπ/a`: `sin(2aω_k) = 0` and `cos(2aω_k) = 1`. -/
theorem basis_trig {a : ℝ} (k : ℕ) (ha : 0 < a) :
    Real.sin (2 * a * (k * π / a)) = 0 ∧ Real.cos (2 * a * (k * π / a)) = 1 := by
  have : 2 * a * (k * π / a) = ((2 * k : ℕ) : ℝ) * π := by push_cast; field_simp
  rw [this, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, pow_mul]; norm_num

/-! ### Certification logic (round 119, part 1) -/

/-- A Cholesky certificate: if `L` is lower triangular with a strictly positive diagonal, `L Lᵀ` is positive definite. -/
theorem posDef_of_cholesky {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (hL : L.IsLowerTriangular)
    (hd : ∀ i, 0 < L i i) : (L * Lᵀ).PosDef := by
  have hdet : L.det ≠ 0 := by
    rw [det_of_isLowerTriangular L hL]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hd i).ne'
  have hu : IsUnit L := (isUnit_iff_isUnit_det L).mpr (Ne.isUnit hdet)
  have hinj : Function.Injective L.vecMul := vecMul_injective_iff_isUnit.mpr hu
  have := PosDef.mul_conjTranspose_self L hinj
  simpa [conjTranspose_eq_transpose_of_trivial] using this

/-- The quadratic form of a basis combination is its Gram quadratic form: `B(Σ c_j φ_j, Σ c_k φ_k) = c ⬝ (G c)`. -/
theorem gram_quadratic {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (B : LinearMap.BilinForm ℝ V)
    (φ : Fin n → V) (c : Fin n → ℝ) :
    B (∑ j, c j • φ j) (∑ k, c k • φ k) = c ⬝ᵥ (Matrix.of (fun j k => B (φ j) (φ k)) *ᵥ c) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec,
    Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- A positive-definite Gram matrix makes the form strictly positive on every nonzero combination of the basis:
this is the statement `Q(g) > 0` certified in round 119. -/
theorem gram_pos {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (B : LinearMap.BilinForm ℝ V)
    (φ : Fin n → V) (hG : (Matrix.of (fun j k => B (φ j) (φ k))).PosDef) {c : Fin n → ℝ} (hc : c ≠ 0) :
    0 < B (∑ j, c j • φ j) (∑ k, c k • φ k) := by
  rw [gram_quadratic]
  simpa using hG.dotProduct_mulVec_pos hc

/-! ### The counterexample mechanism (round 119, part 2) -/

/-- The off-line quadruple. For `f` even and real on the real axis (`f(z̄) = conj f(z)`), the four points `±z, ±z̄`,
with `z = γ₀ + iδ` (the zeros `½ ± δ ± iγ₀`), contribute `4 Re f(z)²`. -/
theorem quadruple_sum (f : ℂ → ℂ) (hconj : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (heven : ∀ z, f (-z) = f z) (z : ℂ) :
    f z ^ 2 + f (starRingEnd ℂ z) ^ 2 + f (-z) ^ 2 + f (-(starRingEnd ℂ z)) ^ 2 = 4 * ((f z ^ 2).re : ℂ) := by
  rw [heven, heven, hconj, ← map_pow]
  have := Complex.add_conj (f z ^ 2)
  push_cast at this ⊢
  linear_combination 2 * this

/-- Second order at a zero of the test transform: if `F(γ₀) = 0` and `F'(γ₀) = c` is real, then
`Re F(γ₀ + iδ)² = −c²δ² + o(δ²)`. -/
theorem offline_second_order {F : ℂ → ℂ} {c γ₀ : ℝ} (hF : HasDerivAt F (c : ℂ) (γ₀ : ℂ)) (h0 : F γ₀ = 0) :
    (fun δ : ℝ => (F (γ₀ + δ * I) ^ 2).re + c ^ 2 * δ ^ 2) =o[𝓝 0] fun δ : ℝ => δ ^ 2 := by
  -- r(δ) = F(γ₀ + iδ) − c·iδ is o(δ)
  have hlin : (fun h : ℂ => F (γ₀ + h) - F γ₀ - h * c) =o[𝓝 0] fun h => h := by
    have := hF.hasFDerivAt.isLittleO
    have ht : Tendsto (fun h : ℂ => (γ₀ : ℂ) + h) (𝓝 0) (𝓝 (γ₀ : ℂ)) := by
      simpa using tendsto_const_nhds.add (tendsto_id (x := 𝓝 (0 : ℂ)))
    have := this.comp_tendsto ht
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using this
  have hpath : Tendsto (fun δ : ℝ => (δ : ℂ) * I) (𝓝 0) (𝓝 0) := by
    have : Continuous fun δ : ℝ => (δ : ℂ) * I := by fun_prop
    simpa using this.tendsto 0
  have hr := hlin.comp_tendsto hpath
  simp only [Function.comp_def, h0, sub_zero] at hr
  set r : ℝ → ℂ := fun δ => F (γ₀ + δ * I) - δ * I * c with hrdef
  have hr' : r =o[𝓝 0] fun δ : ℝ => (δ : ℂ) * I := hr
  have hrδ : r =o[𝓝 0] fun δ : ℝ => δ := by
    refine hr'.trans_isBigO ?_
    refine IsBigO.of_bound 1 (Eventually.of_forall fun δ => ?_)
    simp
  -- F(γ₀+iδ)² = −c²δ² + 2cδ i r + r²
  have hsq : ∀ δ : ℝ, (F (γ₀ + δ * I) ^ 2).re + c ^ 2 * δ ^ 2 = (2 * (δ * I * c) * r δ + r δ ^ 2).re := by
    intro δ
    have : F (γ₀ + δ * I) = δ * I * c + r δ := by simp [hrdef]
    rw [this]
    have e : ((δ : ℂ) * I * c + r δ) ^ 2 = -(c ^ 2 * δ ^ 2 : ℝ) + (2 * (δ * I * c) * r δ + r δ ^ 2) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [e, Complex.add_re, Complex.neg_re, Complex.ofReal_re]; ring
  simp_rw [hsq]
  have hA : (fun δ : ℝ => 2 * ((δ : ℂ) * I * c) * r δ) =o[𝓝 0] fun δ : ℝ => δ ^ 2 := by
    have hb : (fun δ : ℝ => 2 * ((δ : ℂ) * I * c)) =O[𝓝 0] fun δ : ℝ => δ :=
      IsBigO.of_bound (2 * |c|) (Eventually.of_forall fun δ => by
        simp; nlinarith [abs_nonneg c, abs_nonneg δ])
    simpa [pow_two] using hb.mul_isLittleO hrδ
  have hB : (fun δ : ℝ => r δ ^ 2) =o[𝓝 0] fun δ : ℝ => δ ^ 2 := by
    simpa [pow_two] using hrδ.mul_isBigO hrδ.isBigO
  have hsum := hA.add hB
  refine IsBigO.trans_isLittleO ?_ hsum
  exact IsBigO.of_bound 1 (Eventually.of_forall fun δ => by
    rw [one_mul, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)

/-- **The mechanism of positivity loss.** If the test transform vanishes at `γ₀` with a nonzero real slope, then the
off-line quadruple's contribution `Re F(γ₀ + iδ)²` is strictly negative for every small `δ ≠ 0`. -/
theorem offline_negative {F : ℂ → ℂ} {c γ₀ : ℝ} (hF : HasDerivAt F (c : ℂ) (γ₀ : ℂ)) (h0 : F γ₀ = 0) (hc : c ≠ 0) :
    ∀ᶠ δ : ℝ in 𝓝[≠] (0 : ℝ), (F ((γ₀ : ℂ) + (δ : ℂ) * I) ^ 2).re < 0 := by
  have ho := offline_second_order hF h0
  have hε : 0 < c ^ 2 / 2 := by positivity
  have hev := (ho.def hε).filter_mono (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
  filter_upwards [hev, self_mem_nhdsWithin] with δ hδ hne
  have hδne : δ ≠ 0 := hne
  have hδ2 : 0 < δ ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hδ2] at hδ
  have := (abs_le.mp hδ).2
  nlinarith

end WindowForm

#print axioms WindowForm.ghat_cos
#print axioms WindowForm.ghat_pole
#print axioms WindowForm.product_dd
#print axioms WindowForm.hasDerivAt_uA
#print axioms WindowForm.phi_u_trig
#print axioms WindowForm.basis_trig
#print axioms WindowForm.posDef_of_cholesky
#print axioms WindowForm.gram_quadratic
#print axioms WindowForm.gram_pos
#print axioms WindowForm.quadruple_sum
#print axioms WindowForm.offline_second_order
#print axioms WindowForm.offline_negative
