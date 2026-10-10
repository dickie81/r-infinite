import Mathlib

/-! # The critical line is the unit sphere of the Bohr lift (round 391)

The owner asked for a proof that the critical line is the surface of the infinite unit ball. This file proves it
for the Bohr lift `z(s) = (p^{−s})_p`, one coordinate for each prime, in the precise senses listed below. It proves
nothing about where the zeros of `ζ` are.

* **The `ℓ^q` threshold** (**`summable_norm_bohr_rpow_iff`**, **`memℓp_bohr_iff`** and **`memℓp_two_bohr_iff`**,
  with `norm_bohr`): for `q > 0`, `z(s) ∈ ℓ^q(primes)` if and only if `Re s > 1/q`. In the Hilbert space `ℓ²` the
  domain is the half-plane `Re s > ½`, whose boundary is the critical line.
* **The reflection in the line is Hölder conjugation** (`lineRefl`, a definition, `s ↦ 1 − s̄`;
  **`not_summable_and_summable_lineRefl`**, **`holderConjugate_critExp`**, **`critExp_eq_iff`** and
  **`holderConjugate_self_iff`**, with `lineRefl_re`, `lineRefl_im`, `lineRefl_lineRefl` and
  `lineRefl_eq_self_iff`): for `0 < σ < 1` the critical exponents `1/σ` of `s` and `1/(1 − σ)` of its mirror image
  are Hölder conjugate, and they coincide only at `σ = ½`, where both are `2`, the only self-conjugate exponent. No
  Hölder pair `(q, q′)` has both `z(s) ∈ ℓ^q` and `z(1 − s̄) ∈ ℓ^{q′}`.
* **The unit sphere in every finite dimension** (`cF`, `bohrSqSum` and `vF`, definitions; **`vF_mem_sphere_iff`**,
  **`norm_vF_lt_norm_vF`** and **`norm_vF_eq_of_re_eq`**, with `cF_nonneg`, `cF_pos`, `bohrSqSum_nonneg`,
  `bohrSqSum_half`, `strictAnti_bohrSqSum`, `vF_apply`, `norm_vF_sq` and `norm_vF`): for a nonempty finite set `F`
  of primes, `v_F(s) = (p^{−s})_{p ∈ F}/√c_F` with `c_F = Σ_{p ∈ F} 1/p` is a vector of the Euclidean space `ℂ^F`
  (real dimension `2|F|`), `‖v_F(s)‖² = Σ_{p ∈ F} p^{−2 Re s}/c_F`, and `v_F(s)` lies on the unit sphere if and
  only if `Re s = ½`. The radius `‖v_F(s)‖` is strictly decreasing in `Re s` and does not depend on `Im s`.
* **The polarity** (`zF`, a definition; **`inner_zF_lineRefl`**, **`inner_vF_lineRefl`** and
  **`inner_smul_zF_lineRefl_eq_one_iff`**, with `conj_bohr`, `bohr_conj_mul_bohr_lineRefl` and `zF_apply`):
  `⟨z_F(s), z_F(1 − s̄)⟩ = c_F` for every `s`, so `⟨v_F(s), v_F(1 − s̄)⟩ = 1`: a point and its mirror image are
  conjugate in the polarity of the unit sphere, whose self-conjugate points are the points of the sphere. The
  scale `√c_F` is the only one with this property.
* **Cauchy–Schwarz** (**`one_le_norm_vF_mul_norm_vF_lineRefl`** and
  **`norm_vF_mul_norm_vF_lineRefl_eq_one_iff`**): `‖v_F(s)‖·‖v_F(1 − s̄)‖ ≥ 1`; when `F` contains two primes,
  equality holds exactly on the line.
* **The infinite-dimensional limit** (`primesLT`, a definition; **`tendsto_cF_primesLT`**,
  **`tendsto_norm_vF_of_half_lt`**, **`norm_vF_primesLT_of_re_eq_half`**, **`tendsto_norm_vF_of_lt_half`** and
  **`tendsto_norm_vF_one_iff`**, with `mem_primesLT` and `primesLT_nonempty`): with `F` the primes below `N`,
  `c_N → ∞` (Euler, through Mathlib's `not_summable_one_div_on_primes`), and as `N → ∞` the radius
  `‖v_N(s)‖` tends to `0` for `Re s > ½`, equals `1` for `Re s = ½` and every `N ≥ 3`, and tends to `∞` for
  `Re s < ½`. So the line is exactly the set of `s` whose radius tends to `1`.
* **RH, restated** (**`riemannHypothesis_iff_mem_sphere`** and **`riemannHypothesis_iff_tendsto`**): RH holds if
  and only if every nontrivial zero lies on the unit sphere of `ℂ^F`, for any one nonempty `F`, and if and only
  if the radius of every nontrivial zero tends to `1`. These are restatements; nothing in this file constrains a
  zero.
* **The part of the Euler product that converges on `ℓ²` has no zeros** (`regTerm` and `zetaReduced`,
  definitions; **`summable_regTerm`**, **`differentiableOn_logD2`**, **`riemannZeta_eq_exp_mul_exp`**,
  **`zetaReduced_eq`**, **`differentiableOn_zetaReduced`**, **`zetaReduced_eq_zero_iff`** and
  **`not_memℓp_one`**, with `two_rpow_neg_half_lt_one`, `norm_bohr_le_two_rpow`, `norm_regTerm_le` and
  `differentiableAt_regTerm`): `log D₂(s) = Σ_p (−log(1 − p^{−s}) − p^{−s})` converges, its terms bounded by
  a constant times `p^{−2 Re s}`, and is holomorphic on `Re s > ½`, where `z(s) ∈ ℓ²`, so `D₂ = exp(log D₂)` has no zero there. For `Re s > 1`,
  `ζ(s) = exp(Σ_p p^{−s})·D₂(s)`. The function `ζ/D₂` is holomorphic on `Re s > ½`, `s ≠ 1`, equals
  `exp(Σ_p p^{−s})` on `Re s > 1`, and has the same zeros as `ζ`. The sum `Σ_p p^{−s}` pairs `z(s)` with the
  all-ones vector, which lies in no `ℓ^q` with `q < ∞`.

What this file does not prove: anything about the location of the zeros of `ζ`. In round 390's terms it
supplies condition 1 (a radial coordinate, strictly monotone in `Re s`, whose unit sphere is the line) in every
finite dimension, and a pointwise form of condition 2 in the limit (the radius of every point off the line
tends to `0` or to `∞`, never to `1`); there is no probability measure here. Condition 3, that the zeros lie on the
sphere, is RH itself (`riemannHypothesis_iff_mem_sphere`). Every zero of `ζ` with `Re s > ½` is a zero of
`ζ/D₂`, which on `Re s > 1` is the exponential of the pairing of `z(s)` with a vector outside every `ℓ^q`,
`q < ∞`.
-/

open Complex Filter Topology

namespace BohrSphere

/-- The Bohr lift: the coordinate of `s` at the prime `p` is `p^{-s}`. -/
noncomputable def bohr (s : ℂ) (p : Nat.Primes) : ℂ := ((p : ℕ) : ℂ) ^ (-s)

lemma norm_bohr (s : ℂ) (p : Nat.Primes) : ‖bohr s p‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
  rw [bohr, norm_natCast_cpow_of_pos p.prop.pos, neg_re]

/-! ## Part A: the ℓ^q threshold -/

/-- `z(s) ∈ ℓ^q(primes)` if and only if `Re s > 1/q`. -/
theorem summable_norm_bohr_rpow_iff {q : ℝ} (hq : 0 < q) (s : ℂ) :
    Summable (fun p : Nat.Primes => ‖bohr s p‖ ^ q) ↔ 1 / q < s.re := by
  have h : (fun p : Nat.Primes => ‖bohr s p‖ ^ q) = fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(s.re * q)) := by
    ext p
    rw [norm_bohr, ← Real.rpow_mul (Nat.cast_nonneg _), neg_mul]
  rw [h, Nat.Primes.summable_rpow, neg_lt_neg_iff, div_lt_iff₀ hq]

/-- The same statement in Mathlib's `ℓ^q` language. -/
theorem memℓp_bohr_iff {q : ENNReal} (hq : 0 < q.toReal) (s : ℂ) :
    Memℓp (bohr s) q ↔ 1 / q.toReal < s.re := by
  rw [memℓp_gen_iff hq, summable_norm_bohr_rpow_iff hq]

/-- The Hilbert-space case: `z(s) ∈ ℓ²(primes)` if and only if `Re s > ½`. -/
theorem memℓp_two_bohr_iff (s : ℂ) : Memℓp (bohr s) 2 ↔ 1 / 2 < s.re := by
  rw [memℓp_bohr_iff (by norm_num) s]
  norm_num

/-! ## Part B: the reflection in the line is Hölder conjugation -/

/-- The reflection in the critical line, `s ↦ 1 − s̄`. -/
noncomputable def lineRefl (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s

@[simp] lemma lineRefl_re (s : ℂ) : (lineRefl s).re = 1 - s.re := by simp [lineRefl]

@[simp] lemma lineRefl_im (s : ℂ) : (lineRefl s).im = s.im := by simp [lineRefl]

lemma lineRefl_lineRefl (s : ℂ) : lineRefl (lineRefl s) = s := by simp [lineRefl]

lemma lineRefl_eq_self_iff (s : ℂ) : lineRefl s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    rw [lineRefl_re] at this
    linarith
  · intro h
    apply Complex.ext
    · rw [lineRefl_re, h]; norm_num
    · rw [lineRefl_im]

/-- No pair of Hölder conjugate exponents holds a point and its mirror image together. -/
theorem not_summable_and_summable_lineRefl {q q' : ℝ} (h : q.HolderConjugate q') (s : ℂ) :
    ¬ (Summable (fun p : Nat.Primes => ‖bohr s p‖ ^ q) ∧
      Summable (fun p : Nat.Primes => ‖bohr (lineRefl s) p‖ ^ q')) := by
  rintro ⟨h1, h2⟩
  rw [summable_norm_bohr_rpow_iff h.left_pos] at h1
  rw [summable_norm_bohr_rpow_iff h.right_pos, lineRefl_re] at h2
  have e := h.inv_add_inv_eq_inv
  rw [inv_one] at e
  rw [one_div] at h1 h2
  linarith

/-- The critical exponents `1/σ` and `1/(1 − σ)` of a point and of its mirror image are Hölder
conjugate. -/
theorem holderConjugate_critExp {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (1 / σ).HolderConjugate (1 / (1 - σ)) where
  inv_add_inv_eq_inv := by rw [one_div, one_div, inv_inv, inv_inv, inv_one]; ring
  left_pos := by positivity
  right_pos := by
    have : 0 < 1 - σ := by linarith
    positivity

/-- The two critical exponents coincide exactly on the critical line. -/
theorem critExp_eq_iff {σ : ℝ} (h1 : σ < 1) : 1 / σ = 1 / (1 - σ) ↔ σ = 1 / 2 := by
  constructor
  · intro h
    have h0 : σ ≠ 0 := by
      rintro rfl
      norm_num at h
    have h1' : 1 - σ ≠ 0 := by linarith
    field_simp at h
    linarith
  · rintro rfl
    norm_num

/-- `2` is the only self-conjugate exponent. -/
theorem holderConjugate_self_iff {q : ℝ} : q.HolderConjugate q ↔ q = 2 := by
  constructor
  · intro h
    have e := h.inv_add_inv_eq_inv
    have hq := h.left_pos
    rw [inv_one] at e
    field_simp at e
    linarith
  · rintro rfl
    exact ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## Part C: in every finite dimension the line is exactly the unit sphere -/

/-- The pairing constant `c_F = Σ_{p ∈ F} 1/p`. -/
noncomputable def cF (F : Finset Nat.Primes) : ℝ := ∑ p ∈ F, ((p : ℕ) : ℝ)⁻¹

lemma cF_nonneg (F : Finset Nat.Primes) : 0 ≤ cF F :=
  Finset.sum_nonneg fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _)

lemma cF_pos {F : Finset Nat.Primes} (hF : F.Nonempty) : 0 < cF F :=
  Finset.sum_pos (fun p _ => inv_pos.2 (Nat.cast_pos.2 p.prop.pos)) hF

/-- `A_F(σ) = Σ_{p ∈ F} p^{−2σ}`. -/
noncomputable def bohrSqSum (F : Finset Nat.Primes) (σ : ℝ) : ℝ :=
  ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(2 * σ))

lemma bohrSqSum_nonneg (F : Finset Nat.Primes) (σ : ℝ) : 0 ≤ bohrSqSum F σ :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma bohrSqSum_half (F : Finset Nat.Primes) : bohrSqSum F (1 / 2) = cF F := by
  unfold bohrSqSum cF
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]

lemma strictAnti_bohrSqSum {F : Finset Nat.Primes} (hF : F.Nonempty) : StrictAnti (bohrSqSum F) := by
  intro a b hab
  exact Finset.sum_lt_sum_of_nonempty hF fun p _ =>
    Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast p.prop.one_lt) (by linarith)

/-- The normalised Bohr vector of `s`, one complex coordinate per prime of `F`. -/
noncomputable def vF (F : Finset Nat.Primes) (s : ℂ) : EuclideanSpace ℂ F :=
  WithLp.toLp 2 fun p : F => bohr s p / ((√(cF F) : ℝ) : ℂ)

lemma vF_apply (F : Finset Nat.Primes) (s : ℂ) (p : F) :
    vF F s p = bohr s p / ((√(cF F) : ℝ) : ℂ) := rfl

/-- `‖v_F(s)‖² = A_F(Re s)/c_F`. -/
theorem norm_vF_sq (F : Finset Nat.Primes) (s : ℂ) : ‖vF F s‖ ^ 2 = bohrSqSum F s.re / cF F := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [vF_apply, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (cF_nonneg F), norm_bohr]
  rw [← Finset.sum_div, bohrSqSum,
    Finset.sum_coe_sort F (fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ (-s.re)) ^ 2)]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

lemma norm_vF (F : Finset Nat.Primes) (s : ℂ) : ‖vF F s‖ = √(bohrSqSum F s.re / cF F) := by
  rw [← norm_vF_sq, Real.sqrt_sq (norm_nonneg _)]

/-- **The critical line is the unit sphere, in every finite dimension.** -/
theorem vF_mem_sphere_iff {F : Finset Nat.Primes} (hF : F.Nonempty) (s : ℂ) :
    vF F s ∈ Metric.sphere (0 : EuclideanSpace ℂ F) 1 ↔ s.re = 1 / 2 := by
  rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    norm_vF_sq, div_eq_one_iff_eq (cF_pos hF).ne', ← bohrSqSum_half,
    (strictAnti_bohrSqSum hF).injective.eq_iff]

/-- The radius is strictly decreasing in `Re s`. -/
theorem norm_vF_lt_norm_vF {F : Finset Nat.Primes} (hF : F.Nonempty) {s s' : ℂ}
    (h : s.re < s'.re) : ‖vF F s'‖ < ‖vF F s‖ := by
  rw [norm_vF, norm_vF]
  exact Real.sqrt_lt_sqrt (div_nonneg (bohrSqSum_nonneg _ _) (cF_nonneg F))
    ((div_lt_div_iff_of_pos_right (cF_pos hF)).2 (strictAnti_bohrSqSum hF h))

/-- The radius depends on `s` only through `Re s`. -/
theorem norm_vF_eq_of_re_eq (F : Finset Nat.Primes) {s s' : ℂ} (h : s.re = s'.re) :
    ‖vF F s‖ = ‖vF F s'‖ := by
  rw [norm_vF, norm_vF, h]

/-! ## Part D: the reflection is the polarity of the unit sphere -/

lemma conj_bohr (s : ℂ) (p : Nat.Primes) :
    (starRingEnd ℂ) (bohr s p) = bohr ((starRingEnd ℂ) s) p := by
  have h := Complex.cpow_conj ((p : ℕ) : ℂ) (-s)
    (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
  rw [Complex.conj_natCast, map_neg] at h
  rw [bohr, bohr, h]

lemma bohr_conj_mul_bohr_lineRefl (s : ℂ) (p : Nat.Primes) :
    bohr ((starRingEnd ℂ) s) p * bohr (lineRefl s) p = ((((p : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
  rw [bohr, bohr, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.2 p.prop.ne_zero),
    show -(starRingEnd ℂ) s + -lineRefl s = -1 by simp [lineRefl]; ring, Complex.cpow_neg_one]
  push_cast
  rfl

/-- The unnormalised vector `z_F(s) = (p^{−s})_{p ∈ F}`. -/
noncomputable def zF (F : Finset Nat.Primes) (s : ℂ) : EuclideanSpace ℂ F :=
  WithLp.toLp 2 fun p : F => bohr s p

lemma zF_apply (F : Finset Nat.Primes) (s : ℂ) (p : F) : zF F s p = bohr s p := rfl

/-- The pairing of a point with its mirror image does not depend on the point: it is `c_F`. -/
theorem inner_zF_lineRefl (F : Finset Nat.Primes) (s : ℂ) :
    inner ℂ (zF F s) (zF F (lineRefl s)) = (cF F : ℂ) := by
  rw [PiLp.inner_apply]
  simp_rw [RCLike.inner_apply', zF_apply, conj_bohr, bohr_conj_mul_bohr_lineRefl]
  rw [cF, Complex.ofReal_sum,
    Finset.sum_coe_sort F (fun p : Nat.Primes => ((((p : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))]

/-- **The polarity.** The normalised vectors of a point and of its mirror image pair to `1`. -/
theorem inner_vF_lineRefl {F : Finset Nat.Primes} (hF : F.Nonempty) (s : ℂ) :
    inner ℂ (vF F s) (vF F (lineRefl s)) = 1 := by
  have hc := cF_pos hF
  have key : ∀ p : F, (starRingEnd ℂ) (vF F s p) * vF F (lineRefl s) p =
      (((((p : Nat.Primes) : ℕ) : ℝ)⁻¹ / cF F : ℝ) : ℂ) := by
    intro p
    rw [vF_apply, vF_apply, map_div₀, Complex.conj_ofReal, conj_bohr, div_mul_div_comm,
      bohr_conj_mul_bohr_lineRefl, ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le,
      ← Complex.ofReal_div]
  rw [PiLp.inner_apply]
  simp_rw [RCLike.inner_apply', key]
  rw [← Complex.ofReal_sum,
    Finset.sum_coe_sort F (fun p : Nat.Primes => ((p : ℕ) : ℝ)⁻¹ / cF F), ← Finset.sum_div,
    ← cF, div_self hc.ne', Complex.ofReal_one]

/-- The normalisation is forced: rescaling `z_F` by `1/r` makes mirror pairs pair to `1` exactly when
`r = √c_F`. -/
theorem inner_smul_zF_lineRefl_eq_one_iff {F : Finset Nat.Primes} (hF : F.Nonempty) {r : ℝ}
    (hr : 0 < r) (s : ℂ) :
    inner ℂ ((r : ℂ)⁻¹ • zF F s) ((r : ℂ)⁻¹ • zF F (lineRefl s)) = 1 ↔ r = √(cF F) := by
  rw [inner_smul_left, inner_smul_right, inner_zF_lineRefl, map_inv₀, Complex.conj_ofReal,
    ← mul_assoc, ← mul_inv, ← Complex.ofReal_mul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    Complex.ofReal_eq_one]
  have hc := cF_pos hF
  constructor
  · intro h
    have hrr : r * r = cF F := by
      have hr0 : r * r ≠ 0 := by positivity
      field_simp at h
      linarith
    rw [← hrr, Real.sqrt_mul_self hr.le]
  · rintro rfl
    rw [Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']

/-! ## Part E: Cauchy–Schwarz -/

/-- `‖v_F(s)‖ · ‖v_F(1 − s̄)‖ ≥ 1`. -/
theorem one_le_norm_vF_mul_norm_vF_lineRefl {F : Finset Nat.Primes} (hF : F.Nonempty) (s : ℂ) :
    1 ≤ ‖vF F s‖ * ‖vF F (lineRefl s)‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (vF F s) (vF F (lineRefl s))
  rwa [inner_vF_lineRefl hF, norm_one] at h

/-- With two distinct primes, equality holds exactly on the critical line. -/
theorem norm_vF_mul_norm_vF_lineRefl_eq_one_iff {F : Finset Nat.Primes} {p₁ p₂ : Nat.Primes}
    (h₁ : p₁ ∈ F) (h₂ : p₂ ∈ F) (hne : p₁ ≠ p₂) (s : ℂ) :
    ‖vF F s‖ * ‖vF F (lineRefl s)‖ = 1 ↔ s.re = 1 / 2 := by
  have hF : F.Nonempty := ⟨p₁, h₁⟩
  have hc := cF_pos hF
  constructor
  · intro h
    have hx : vF F s ≠ 0 := by
      intro h0
      rw [h0, norm_zero, zero_mul] at h
      exact zero_ne_one h
    have hy : vF F (lineRefl s) ≠ 0 := by
      intro h0
      rw [h0, norm_zero, mul_zero] at h
      exact zero_ne_one h
    have h' : ‖inner ℂ (vF F s) (vF F (lineRefl s))‖ = ‖vF F s‖ * ‖vF F (lineRefl s)‖ := by
      rw [inner_vF_lineRefl hF, norm_one, h]
    obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff hx hy).1 h'
    have key : ∀ p : F, (((p : Nat.Primes) : ℕ) : ℝ) ^ (2 * s.re - 1) = ‖r‖ := by
      intro p
      have hp : (0 : ℝ) < ((p : Nat.Primes) : ℕ) := Nat.cast_pos.2 (p : Nat.Primes).prop.pos
      have e : ‖vF F (lineRefl s) p‖ = ‖r‖ * ‖vF F s p‖ := by
        rw [hr]
        simp
      rw [vF_apply, vF_apply, norm_div, norm_div, norm_bohr, norm_bohr, lineRefl_re] at e
      have hs : (0 : ℝ) < ‖((√(cF F) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hc)]
        exact Real.sqrt_pos.2 hc
      rw [← mul_div_assoc, div_left_inj' hs.ne'] at e
      rw [show 2 * s.re - 1 = -(1 - s.re) + s.re by ring, Real.rpow_add hp, e, mul_assoc,
        ← Real.rpow_add hp, neg_add_cancel, Real.rpow_zero, mul_one]
    by_contra hσ
    have ha : 2 * s.re - 1 ≠ 0 := fun h0 => hσ (by linarith)
    have e := (key ⟨p₁, h₁⟩).trans (key ⟨p₂, h₂⟩).symm
    have e2 := congrArg (fun x : ℝ => x ^ (2 * s.re - 1)⁻¹) e
    simp only at e2
    rw [Real.rpow_rpow_inv (Nat.cast_nonneg _) ha, Real.rpow_rpow_inv (Nat.cast_nonneg _) ha]
      at e2
    exact hne (Subtype.ext (Nat.cast_injective e2))
  · intro h
    have h2 : (lineRefl s).re = 1 / 2 := by rw [lineRefl_re, h]; norm_num
    rw [mem_sphere_zero_iff_norm.1 ((vF_mem_sphere_iff hF s).2 h),
      mem_sphere_zero_iff_norm.1 ((vF_mem_sphere_iff hF _).2 h2), one_mul]

/-! ## Part F: the infinite-dimensional limit -/

/-- The primes below `N`. -/
noncomputable def primesLT (N : ℕ) : Finset Nat.Primes :=
  (Finset.range N).preimage (↑) Nat.Primes.coe_nat_injective.injOn

lemma mem_primesLT {N : ℕ} {p : Nat.Primes} : p ∈ primesLT N ↔ (p : ℕ) < N :=
  Finset.mem_preimage.trans Finset.mem_range

lemma primesLT_nonempty {N : ℕ} (hN : 3 ≤ N) : (primesLT N).Nonempty :=
  ⟨⟨2, Nat.prime_two⟩, mem_primesLT.2 (by simp only; omega)⟩

/-- `c_N = Σ_{p < N} 1/p → ∞` (Euler). -/
theorem tendsto_cF_primesLT : Tendsto (fun N => cF (primesLT N)) atTop atTop := by
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => Set.indicator_nonneg (fun k _ => by positivity) n)).1 not_summable_one_div_on_primes
  refine h.congr fun N => ?_
  refine (Finset.sum_preimage ((↑) : Nat.Primes → ℕ) (Finset.range N)
    Nat.Primes.coe_nat_injective.injOn _
    fun n _ hn => Set.indicator_of_notMem (fun hp => hn ⟨⟨n, hp⟩, rfl⟩) _).symm.trans ?_
  rw [cF]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact (Set.indicator_of_mem (show ((p : ℕ)) ∈ {n : ℕ | n.Prime} from p.2) _).trans
    (one_div _)

/-- Off the line to the right, the radius tends to `0`. -/
theorem tendsto_norm_vF_of_half_lt {s : ℂ} (h : 1 / 2 < s.re) :
    Tendsto (fun N => ‖vF (primesLT N) s‖) atTop (𝓝 0) := by
  have hsum : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * s.re))) :=
    Nat.Primes.summable_rpow.2 (by linarith)
  have hle : ∀ N, bohrSqSum (primesLT N) s.re ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * s.re)) :=
    fun N => hsum.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h0 : Tendsto (fun N => bohrSqSum (primesLT N) s.re / cF (primesLT N)) atTop (𝓝 0) := by
    have hP := (tendsto_const_nhds (x := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * s.re)))).div_atTop
      tendsto_cF_primesLT
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP
      (fun N => div_nonneg (bohrSqSum_nonneg _ _) (cF_nonneg _))
      (fun N => div_le_div_of_nonneg_right (hle N) (cF_nonneg _))
  have := (Real.continuous_sqrt.tendsto 0).comp h0
  rw [Real.sqrt_zero] at this
  simpa [Function.comp_def, norm_vF] using this

/-- On the line, the radius is `1` in every dimension. -/
theorem norm_vF_primesLT_of_re_eq_half {N : ℕ} (hN : 3 ≤ N) {s : ℂ} (h : s.re = 1 / 2) :
    ‖vF (primesLT N) s‖ = 1 :=
  mem_sphere_zero_iff_norm.1 ((vF_mem_sphere_iff (primesLT_nonempty hN) s).2 h)

/-- Off the line to the left, the radius tends to `∞`. -/
theorem tendsto_norm_vF_of_lt_half {s : ℂ} (h : s.re < 1 / 2) :
    Tendsto (fun N => ‖vF (primesLT N) s‖) atTop atTop := by
  suffices hr : Tendsto (fun N => bohrSqSum (primesLT N) s.re / cF (primesLT N)) atTop atTop by
    simp_rw [norm_vF]
    exact Real.tendsto_sqrt_atTop.comp hr
  rw [tendsto_atTop]
  intro M
  have ha : 0 < 1 - 2 * s.re := by linarith
  set B := 2 * (|M| + 1) with hB
  obtain ⟨K, hK⟩ : ∃ K : ℕ, B ≤ (K : ℝ) ^ (1 - 2 * s.re) :=
    (((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B).exists
  have hterm : ∀ p : Nat.Primes, K ≤ (p : ℕ) →
      B * ((p : ℕ) : ℝ)⁻¹ ≤ ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℕ) := Nat.cast_pos.2 p.prop.pos
    rw [show -(2 * s.re) = (1 - 2 * s.re) + -1 by ring, Real.rpow_add hp0, Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_right (hK.trans (Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast hp) ha.le)) (inv_nonneg.2 hp0.le)
  have hcK := tendsto_cF_primesLT.eventually_ge_atTop (2 * cF (primesLT K) + 1)
  filter_upwards [hcK] with N hcN
  have hcpos : 0 < cF (primesLT N) := by linarith [cF_nonneg (primesLT K)]
  -- split the primes below `N` at `K`
  have hsplitA := Finset.sum_filter_add_sum_filter_not (primesLT N)
    (fun p : Nat.Primes => (p : ℕ) < K) (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * s.re)))
  have hsplitC := Finset.sum_filter_add_sum_filter_not (primesLT N)
    (fun p : Nat.Primes => (p : ℕ) < K) (fun p : Nat.Primes => ((p : ℕ) : ℝ)⁻¹)
  have hlow : ∑ p ∈ (primesLT N).filter (fun p : Nat.Primes => (p : ℕ) < K), ((p : ℕ) : ℝ)⁻¹ ≤
      cF (primesLT K) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
      (fun _ _ _ => inv_nonneg.2 (Nat.cast_nonneg _))
    exact mem_primesLT.2 (Finset.mem_filter.1 hp).2
  have hhigh : B * ∑ p ∈ (primesLT N).filter (fun p : Nat.Primes => ¬ (p : ℕ) < K),
      ((p : ℕ) : ℝ)⁻¹ ≤ ∑ p ∈ (primesLT N).filter (fun p : Nat.Primes => ¬ (p : ℕ) < K),
      ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => hterm p (not_lt.1 (Finset.mem_filter.1 hp).2)
  have hlowA : 0 ≤ ∑ p ∈ (primesLT N).filter (fun p : Nat.Primes => (p : ℕ) < K),
      ((p : ℕ) : ℝ) ^ (-(2 * s.re)) :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA : bohrSqSum (primesLT N) s.re =
      ∑ p ∈ (primesLT N).filter (fun p : Nat.Primes => (p : ℕ) < K),
        ((p : ℕ) : ℝ) ^ (-(2 * s.re)) +
      ∑ p ∈ (primesLT N).filter (fun p : Nat.Primes => ¬ (p : ℕ) < K),
        ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by
    rw [bohrSqSum, hsplitA]
  have hC : cF (primesLT N) =
      ∑ p ∈ (primesLT N).filter (fun p : Nat.Primes => (p : ℕ) < K), ((p : ℕ) : ℝ)⁻¹ +
      ∑ p ∈ (primesLT N).filter (fun p : Nat.Primes => ¬ (p : ℕ) < K), ((p : ℕ) : ℝ)⁻¹ := by
    rw [cF, hsplitC]
  have hM : 0 ≤ |M| + 1 := by positivity
  have hB0 : 0 ≤ B := by positivity
  have k1 := mul_le_mul_of_nonneg_left hlow hB0
  have e1 : B * ∑ p ∈ (primesLT N).filter (fun p : Nat.Primes => ¬ (p : ℕ) < K),
      ((p : ℕ) : ℝ)⁻¹ = B * cF (primesLT N) -
        B * ∑ p ∈ (primesLT N).filter (fun p : Nat.Primes => (p : ℕ) < K), ((p : ℕ) : ℝ)⁻¹ := by
    rw [hC]
    ring
  have e2 : B * cF (primesLT N) = 2 * ((|M| + 1) * cF (primesLT N)) := by rw [hB]; ring
  have e3 : B * cF (primesLT K) = 2 * ((|M| + 1) * cF (primesLT K)) := by rw [hB]; ring
  have k2 : 0 ≤ (|M| + 1) * cF (primesLT N) - 2 * ((|M| + 1) * cF (primesLT K)) := by
    have := mul_nonneg hM (show 0 ≤ cF (primesLT N) - 2 * cF (primesLT K) by linarith)
    linarith [this, show (|M| + 1) * (cF (primesLT N) - 2 * cF (primesLT K)) =
      (|M| + 1) * cF (primesLT N) - 2 * ((|M| + 1) * cF (primesLT K)) by ring]
  have hmain : (|M| + 1) * cF (primesLT N) ≤ bohrSqSum (primesLT N) s.re := by
    linarith [hA, hhigh, e1, e2, e3, k1, k2, hlowA]
  rw [le_div_iff₀ hcpos]
  exact (mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) hcpos.le).trans hmain

/-- **The line is exactly the set of points whose normalised Bohr vectors tend to the unit
sphere.** -/
theorem tendsto_norm_vF_one_iff (s : ℂ) :
    Tendsto (fun N => ‖vF (primesLT N) s‖) atTop (𝓝 1) ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · exact absurd h (not_tendsto_nhds_of_tendsto_atTop (tendsto_norm_vF_of_lt_half hlt) 1)
    · exact heq
    · exact absurd (tendsto_nhds_unique h (tendsto_norm_vF_of_half_lt hgt)) one_ne_zero
  · intro h
    exact tendsto_const_nhds.congr' ((eventually_ge_atTop 3).mono fun N hN =>
      (norm_vF_primesLT_of_re_eq_half hN h).symm)

/-! ## Part G: RH in this language is a restatement -/

/-- For every nonempty finite set of primes, RH says that every nontrivial zero lies on the unit
sphere. A reformulation: nothing here constrains the zeros. -/
theorem riemannHypothesis_iff_mem_sphere {F : Finset Nat.Primes} (hF : F.Nonempty) :
    RiemannHypothesis ↔ ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
      vF F s ∈ Metric.sphere (0 : EuclideanSpace ℂ F) 1 := by
  simp only [RiemannHypothesis, vF_mem_sphere_iff hF]

/-- The same in the limit. -/
theorem riemannHypothesis_iff_tendsto :
    RiemannHypothesis ↔ ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
      Tendsto (fun N => ‖vF (primesLT N) s‖) atTop (𝓝 1) := by
  simp only [RiemannHypothesis, tendsto_norm_vF_one_iff]

/-! ## Part H: the ball's part of the Euler product has no zeros -/

/-- The terms `−log(1 − x) − x` at `x = p^{−s}` of the regularised logarithm of the Euler
product. -/
noncomputable def regTerm (s : ℂ) (p : Nat.Primes) : ℂ := -Complex.log (1 - bohr s p) - bohr s p

lemma two_rpow_neg_half_lt_one : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)

lemma norm_bohr_le_two_rpow {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    ‖bohr s p‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [norm_bohr]
  exact (Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.prop.two_le)
    (by linarith)).trans (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith))

/-- `‖−log(1 − x) − x‖ ≤ C‖x‖²` with `C = (1 − 2^{−1/2})⁻¹/2`, uniformly on `Re s ≥ σ₀ ≥ ½`. -/
lemma norm_regTerm_le {s : ℂ} {σ₀ : ℝ} (h0 : 1 / 2 ≤ σ₀) (hs : σ₀ ≤ s.re) (p : Nat.Primes) :
    ‖regTerm s p‖ ≤ (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ / 2 * ((p : ℕ) : ℝ) ^ (-(2 * σ₀)) := by
  have hx2 := norm_bohr_le_two_rpow (h0.trans hs) p
  have hlt : ‖-bohr s p‖ < 1 := by
    rw [norm_neg]
    exact hx2.trans_lt two_rpow_neg_half_lt_one
  have e : regTerm s p = -(Complex.log (1 + -bohr s p) - -bohr s p) := by
    rw [regTerm, ← sub_eq_add_neg]
    ring
  rw [e, norm_neg]
  refine (Complex.norm_log_one_add_sub_self_le hlt).trans ?_
  rw [norm_neg]
  have hsq : ‖bohr s p‖ ^ 2 ≤ ((p : ℕ) : ℝ) ^ (-(2 * σ₀)) := by
    have hx : ‖bohr s p‖ ≤ ((p : ℕ) : ℝ) ^ (-σ₀) := by
      rw [norm_bohr]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_lt.le) (by linarith)
    calc ‖bohr s p‖ ^ 2 ≤ (((p : ℕ) : ℝ) ^ (-σ₀)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
      _ = ((p : ℕ) : ℝ) ^ (-(2 * σ₀)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        ring
  have hinv : (1 - ‖bohr s p‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ :=
    inv_anti₀ (by linarith [two_rpow_neg_half_lt_one]) (by linarith)
  have hm := mul_le_mul hsq hinv (inv_nonneg.2 (by linarith [two_rpow_neg_half_lt_one]))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc ‖bohr s p‖ ^ 2 * (1 - ‖bohr s p‖)⁻¹ / 2
      ≤ ((p : ℕ) : ℝ) ^ (-(2 * σ₀)) * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ / 2 :=
        div_le_div_of_nonneg_right hm two_pos.le
    _ = _ := by ring

/-- The regularised logarithm converges absolutely on the whole half-plane `Re s > ½`, the
half-plane where `z(s) ∈ ℓ²`. -/
theorem summable_regTerm {s : ℂ} (hs : 1 / 2 < s.re) : Summable (regTerm s) :=
  Summable.of_norm_bounded
    ((Nat.Primes.summable_rpow.2 (by linarith : -(2 * s.re) < -1)).mul_left _)
    (norm_regTerm_le hs.le le_rfl)

lemma differentiableAt_regTerm {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    DifferentiableAt ℂ (fun w => regTerm w p) s := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 p.prop.ne_zero
  have hb : DifferentiableAt ℂ (fun w => bohr w p) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hp0)
  have hlt : ‖bohr s p‖ < 1 := by
    rw [norm_bohr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
  have hslit : 1 - bohr s p ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    rw [Complex.sub_re, Complex.one_re]
    linarith [Complex.re_le_norm (bohr s p)]
  exact (((differentiableAt_const _).sub hb).clog hslit).neg.sub hb

/-- `log D₂ = Σ_p (−log(1 − p^{−s}) − p^{−s})` is holomorphic on `Re s > ½`. -/
theorem differentiableOn_logD2 :
    DifferentiableOn ℂ (fun s => ∑' p, regTerm s p) {s | 1 / 2 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 / 2 < s₀.re := hs₀
  have h1 : 1 / 2 < (s₀.re + 1 / 2) / 2 := by linarith
  have h2 : (s₀.re + 1 / 2) / 2 < s₀.re := by linarith
  have hU : IsOpen {s : ℂ | (s₀.re + 1 / 2) / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun s => ∑' p, regTerm s p) {s : ℂ | (s₀.re + 1 / 2) / 2 < s.re} :=
    differentiableOn_tsum_of_summable_norm
      ((Nat.Primes.summable_rpow.2 (by linarith : -(2 * ((s₀.re + 1 / 2) / 2)) < -1)).mul_left
        ((1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ / 2))
      (fun p w hw => (differentiableAt_regTerm
        (by linarith [show (s₀.re + 1 / 2) / 2 < w.re from hw]) p).differentiableWithinAt) hU
      (fun p w hw => norm_regTerm_le h1.le (le_of_lt hw) p)
  exact (hd.differentiableAt (hU.mem_nhds h2)).differentiableWithinAt

/-- **The split of the Euler product** (`Re s > 1`): `ζ(s) = exp(Σ_p p^{−s}) · D₂(s)`, with
`D₂ = exp(log D₂)`. -/
theorem riemannZeta_eq_exp_mul_exp {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = Complex.exp (∑' p : Nat.Primes, bohr s p) *
      Complex.exp (∑' p, regTerm s p) := by
  rw [← Complex.exp_add, ← riemannZeta_eulerProduct_exp_log hs]
  have h1 : Summable (bohr s) := by
    have := (summable_norm_bohr_rpow_iff one_pos s).2 (by rw [div_one]; exact hs)
    simp only [Real.rpow_one] at this
    exact this.of_norm
  rw [← h1.tsum_add (summable_regTerm (by linarith))]
  congr 1
  refine tsum_congr fun p => ?_
  simp only [regTerm, bohr]
  ring

/-- `ζ` with the ball's factor removed: `ζ(s) · exp(−log D₂(s))`. -/
noncomputable def zetaReduced (s : ℂ) : ℂ := riemannZeta s * Complex.exp (-(∑' p, regTerm s p))

/-- On `Re s > 1` it is `exp(Σ_p p^{−s})`, the exponential of the pairing of `z(s)` with the
all-ones vector. -/
theorem zetaReduced_eq {s : ℂ} (hs : 1 < s.re) :
    zetaReduced s = Complex.exp (∑' p : Nat.Primes, bohr s p) := by
  rw [zetaReduced, riemannZeta_eq_exp_mul_exp hs, mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, mul_one]

/-- It is holomorphic on `Re s > ½`, `s ≠ 1`. -/
theorem differentiableOn_zetaReduced :
    DifferentiableOn ℂ zetaReduced ({s | 1 / 2 < s.re} \ {1}) := by
  intro s hs
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdAt := differentiableOn_logD2.differentiableAt (hopen.mem_nhds hs.1)
  exact ((differentiableAt_riemannZeta hs.2).mul hdAt.neg.cexp).differentiableWithinAt

/-- Its zeros are exactly the zeros of `ζ`. -/
theorem zetaReduced_eq_zero_iff (s : ℂ) : zetaReduced s = 0 ↔ riemannZeta s = 0 := by
  rw [zetaReduced, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _)]

/-- The all-ones vector lies in no `ℓ^q` with `q < ∞`. -/
theorem not_memℓp_one {q : ENNReal} (hq : 0 < q.toReal) :
    ¬ Memℓp (fun _ : Nat.Primes => (1 : ℂ)) q := by
  rw [memℓp_gen_iff hq]
  simp only [norm_one, Real.one_rpow]
  exact fun h => one_ne_zero ((summable_const_iff _).1 h)

end BohrSphere

#print axioms BohrSphere.norm_bohr
#print axioms BohrSphere.summable_norm_bohr_rpow_iff
#print axioms BohrSphere.memℓp_bohr_iff
#print axioms BohrSphere.memℓp_two_bohr_iff
#print axioms BohrSphere.lineRefl_re
#print axioms BohrSphere.lineRefl_im
#print axioms BohrSphere.lineRefl_lineRefl
#print axioms BohrSphere.lineRefl_eq_self_iff
#print axioms BohrSphere.not_summable_and_summable_lineRefl
#print axioms BohrSphere.holderConjugate_critExp
#print axioms BohrSphere.critExp_eq_iff
#print axioms BohrSphere.holderConjugate_self_iff
#print axioms BohrSphere.cF_nonneg
#print axioms BohrSphere.cF_pos
#print axioms BohrSphere.bohrSqSum_nonneg
#print axioms BohrSphere.bohrSqSum_half
#print axioms BohrSphere.strictAnti_bohrSqSum
#print axioms BohrSphere.vF_apply
#print axioms BohrSphere.norm_vF_sq
#print axioms BohrSphere.norm_vF
#print axioms BohrSphere.vF_mem_sphere_iff
#print axioms BohrSphere.norm_vF_lt_norm_vF
#print axioms BohrSphere.norm_vF_eq_of_re_eq
#print axioms BohrSphere.conj_bohr
#print axioms BohrSphere.bohr_conj_mul_bohr_lineRefl
#print axioms BohrSphere.zF_apply
#print axioms BohrSphere.inner_zF_lineRefl
#print axioms BohrSphere.inner_vF_lineRefl
#print axioms BohrSphere.inner_smul_zF_lineRefl_eq_one_iff
#print axioms BohrSphere.one_le_norm_vF_mul_norm_vF_lineRefl
#print axioms BohrSphere.norm_vF_mul_norm_vF_lineRefl_eq_one_iff
#print axioms BohrSphere.mem_primesLT
#print axioms BohrSphere.primesLT_nonempty
#print axioms BohrSphere.tendsto_cF_primesLT
#print axioms BohrSphere.tendsto_norm_vF_of_half_lt
#print axioms BohrSphere.norm_vF_primesLT_of_re_eq_half
#print axioms BohrSphere.tendsto_norm_vF_of_lt_half
#print axioms BohrSphere.tendsto_norm_vF_one_iff
#print axioms BohrSphere.riemannHypothesis_iff_mem_sphere
#print axioms BohrSphere.riemannHypothesis_iff_tendsto
#print axioms BohrSphere.two_rpow_neg_half_lt_one
#print axioms BohrSphere.norm_bohr_le_two_rpow
#print axioms BohrSphere.norm_regTerm_le
#print axioms BohrSphere.summable_regTerm
#print axioms BohrSphere.differentiableAt_regTerm
#print axioms BohrSphere.differentiableOn_logD2
#print axioms BohrSphere.riemannZeta_eq_exp_mul_exp
#print axioms BohrSphere.zetaReduced_eq
#print axioms BohrSphere.differentiableOn_zetaReduced
#print axioms BohrSphere.zetaReduced_eq_zero_iff
#print axioms BohrSphere.not_memℓp_one
