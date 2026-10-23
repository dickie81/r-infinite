import KubotaEnergy
import KubotaCharacter

/-! # Reduction theory for `SL_2(ℤ[ω])`: the Siegel set, a partition of unity, finite volume (round 385)

S5f-8 of round 360's plan, part 3 (S5f-8c, part 1). Rounds 383 and 384 proved that `dz dv/v³` and the energy
are invariant under `SL_2(ℂ)`. This file proves that every orbit of `SL_2(ℤ[ω])` on upper half-space meets the
Siegel set `K = {(z, v) : z ∈ P, v ≥ 1/2}`, for `P` the fundamental parallelogram of `σ(ℤ[ω])`, and meets it
in finitely many `γ·p`. So `ρ = 1_K/#{γ : γ·p ∈ K}` is a measurable partition of unity, `Σ_γ ρ(γ·p) = 1`, and
`∫ρ dz dv/v³ < ∞`.

* **The action** (`slAct`, a definition; `slAct_mul`, `slAct_mem`, `slAct_one`, `slAct_snd`, `slDen_pos` and
  `measurable_slAct`): `γ` acts through `σ : ℤ[ω] → ℂ`, by round 383's `actP`. The height of `γ·p` is
  `v/(|cz + d|² + |c|²v²)`, with `(c, d)` the bottom row of `γ`.
* **Bounded denominators** (`finite_bottom_rows`, with `finite_normSq_le` and `normSq_Mw`): for `v > 0`, only
  finitely many `(c, d) ∈ ℤ[ω]²` have `|cz + d|² + |c|²v² ≤ B`.
* **Maximal height** (**`exists_max_height`**): the height attains its maximum on every orbit.
* **The Siegel set** (`fundP`, `siegelK`, `slT` and `slS`, definitions; **`exists_mem_siegelK`**, with
  `exists_transl_mem_fundP`, `exists_near`, `half_le_of_max`, `slAct_slT`, `slAct_slS_snd`, `coe_slT`,
  `slT_zero` and `Mw_symm_σO_crd`): some `t ∈ ℤ[ω]` has `|z − t|² ≤ 3/4`, so a point of maximal height has
  `v ≥ 1/2`; a translation then moves `z` into `P` and keeps the height.
* **Finiteness** (**`finite_hits`**, with `eq_slT_mul`, `bottom_row_aux` and `eq_zero_of_mem_fundP`): `γ·p ∈ K`
  forces `|cz + d|² + |c|²v² ≤ 2v`. Two such `γ` with the same bottom row differ by a translation on the left,
  and a translation keeps a point of `P` in `P` only if it is trivial.
* **The partition of unity** (`hitsK` and `rhoK`, definitions, and the instance `countable_SL`;
  **`tsum_rhoK`**, with `hitsK_slAct`, `one_le_hitsK`, `hitsK_ne_top`, `measurable_hitsK`, `measurable_rhoK`,
  `measurableSet_fundP`, `measurableSet_siegelK`, `continuous_Mw` and `continuous_Mw_symm`).
* **Finite volume** (**`lintegral_rhoK_lt_top`**, with `uhsMeasure_siegelK_lt_top`, `rhoK_le`,
  `siegelK_subset_UHS`, `fundP_subset`, `volume_fundP_lt_top` and `lintegral_Ioi_zpow_lt_top`).
-/

open MeasureTheory Set Module Filter NumberField Ideal PlanePoisson
open scoped ENNReal ComplexConjugate MatrixGroups

noncomputable section

namespace Eis

/-- The action of `γ ∈ SL_2(ℤ[ω])` on upper half-space, through `σ : ℤ[ω] → ℂ`. -/
def slAct (γ : SL(2, 𝓞 K)) (p : ℂ × ℝ) : ℂ × ℝ :=
  actP ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) p

/-- The action of a product, on upper half-space. -/
theorem slAct_mul (γ γ' : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    slAct (γ * γ') p = slAct γ (slAct γ' p) := by
  unfold slAct
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]
  exact actP_mul (det_map_σO γ.2) (det_map_σO γ'.2) hp

theorem slAct_mem (γ : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hp : p ∈ UHS) : slAct γ p ∈ UHS :=
  actP_mem (det_map_σO γ.2) hp

/-- The height of `γ·p` is `v/(|cz + d|² + |c|²v²)`. -/
theorem slAct_snd (γ : SL(2, 𝓞 K)) (p : ℂ × ℝ) :
    (slAct γ p).2 = p.2 / uhsDen (σO (γ 1 0)) (σO (γ 1 1)) p.1 p.2 := rfl

/-- `|a + bϖ|² = a² − ab + b²` for real `a, b`. -/
theorem normSq_Mw (w : ℂ) : Complex.normSq (Mw w) = w.re ^ 2 - w.re * w.im + w.im ^ 2 := by
  obtain ⟨hre, him⟩ := varpi_re_im
  rw [Mw_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_im, Complex.mul_im, add_zero, zero_add]
  rw [hre]
  nlinarith [him]

/-- **Finitely many lattice points in a disc**. -/
theorem finite_normSq_le (R : ℝ) : {x : 𝓞 K | Complex.normSq (σO x) ≤ R}.Finite := by
  have hsub : {x : 𝓞 K | Complex.normSq (σO x) ≤ R} ⊆
      crdEquiv '' (Set.pi Set.univ fun _ => Set.Icc (-⌈2 * R⌉) ⌈2 * R⌉) := by
    intro x hx
    obtain ⟨n, rfl⟩ := crdEquiv.surjective x
    refine ⟨n, fun i _ => ?_, rfl⟩
    have h := normSq_σO_crd n
    have hx' : Complex.normSq (σO (crd n)) ≤ R := hx
    rw [h] at hx'
    have h0 : ((n 0 : ℝ)) ^ 2 ≤ 2 * R := by nlinarith [sq_nonneg ((n 0 : ℝ) - n 1)]
    have h1 : ((n 1 : ℝ)) ^ 2 ≤ 2 * R := by nlinarith [sq_nonneg ((n 0 : ℝ) - n 1)]
    have key : ∀ m : ℤ, (m : ℝ) ^ 2 ≤ 2 * R → m ∈ Set.Icc (-⌈2 * R⌉) ⌈2 * R⌉ := by
      intro m hm
      have habs : ((|m| : ℤ) : ℝ) ≤ 2 * R := by
        have : ((|m| : ℤ) : ℝ) ≤ (m : ℝ) ^ 2 := by
          rw [Int.cast_abs]
          rcases eq_or_ne m 0 with rfl | hm0
          · simp
          · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
            calc |(m : ℝ)| ≤ |(m : ℝ)| * |(m : ℝ)| := le_mul_of_one_le_left (abs_nonneg _) h1
              _ = (m : ℝ) ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
        linarith
      have hc : (|m| : ℤ) ≤ ⌈2 * R⌉ := by
        have := Int.le_ceil (2 * R)
        exact_mod_cast habs.trans this
      exact ⟨by linarith [neg_abs_le m], le_trans (le_abs_self m) hc⟩
    fin_cases i
    · exact key _ h0
    · exact key _ h1
  exact ((Set.Finite.pi fun _ => Set.finite_Icc _ _).image _).subset hsub

/-- **Finitely many bottom rows of bounded denominator**: `|cz + d|² + |c|²v² ≤ B`. -/
theorem finite_bottom_rows {z : ℂ} {v : ℝ} (hv : 0 < v) (B : ℝ) :
    {cd : 𝓞 K × 𝓞 K | uhsDen (σO cd.1) (σO cd.2) z v ≤ B}.Finite := by
  set Rc := B / v ^ 2
  set Rd := (Real.sqrt (max B 0) + Real.sqrt (max Rc 0) * ‖z‖) ^ 2
  refine ((finite_normSq_le Rc).prod (finite_normSq_le Rd)).subset ?_
  rintro ⟨c, d⟩ h
  change uhsDen (σO c) (σO d) z v ≤ B at h
  unfold uhsDen at h
  have h1 := Complex.normSq_nonneg (σO c * z + σO d)
  have h2 := Complex.normSq_nonneg (σO c)
  have hv2 : 0 < v ^ 2 := by positivity
  have hc : Complex.normSq (σO c) ≤ Rc := by
    rw [le_div_iff₀ hv2]; nlinarith
  refine ⟨hc, ?_⟩
  change Complex.normSq (σO d) ≤ Rd
  -- `|σd| ≤ |σc·z + σd| + |σc|·|z|`
  have e1 : ‖σO c * z + σO d‖ ≤ Real.sqrt (max B 0) := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq]
    exact Real.sqrt_le_sqrt (le_max_of_le_left (by nlinarith))
  have e2 : ‖σO c‖ ≤ Real.sqrt (max Rc 0) := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq]
    exact Real.sqrt_le_sqrt (le_max_of_le_left hc)
  have e3 : ‖σO d‖ ≤ Real.sqrt (max B 0) + Real.sqrt (max Rc 0) * ‖z‖ := by
    calc ‖σO d‖ = ‖(σO c * z + σO d) - σO c * z‖ := by ring_nf
      _ ≤ ‖σO c * z + σO d‖ + ‖σO c * z‖ := norm_sub_le _ _
      _ ≤ Real.sqrt (max B 0) + Real.sqrt (max Rc 0) * ‖z‖ := by
        rw [norm_mul]
        exact add_le_add e1 (mul_le_mul_of_nonneg_right e2 (norm_nonneg _))
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) e3 2

theorem slDen_pos (γ : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    0 < uhsDen (σO (γ 1 0)) (σO (γ 1 1)) p.1 p.2 :=
  uhsDen_pos hp (cd_ne_zero_of_det (det_two_eq_one _ (det_map_σO γ.2)))

theorem slAct_one (p : ℂ × ℝ) : slAct 1 p = p := by
  unfold slAct actP
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero σO) (map_one σO)]
  simp [uhsAct, uhsZ, uhsV, uhsDen]

theorem measurable_slAct (γ : SL(2, 𝓞 K)) : Measurable (slAct γ) := measurable_actP _

/-- **A point of maximal height** in every orbit: `γ₀` minimizes `|cz + d|² + |c|²v²`. -/
theorem exists_max_height {p : ℂ × ℝ} (hp : p ∈ UHS) :
    ∃ γ₀ : SL(2, 𝓞 K), ∀ γ : SL(2, 𝓞 K), (slAct γ p).2 ≤ (slAct γ₀ p).2 := by
  set D : 𝓞 K × 𝓞 K → ℝ := fun cd => uhsDen (σO cd.1) (σO cd.2) p.1 p.2 with hDdef
  set B := (fun γ : SL(2, 𝓞 K) => ((γ 1 0, γ 1 1) : 𝓞 K × 𝓞 K)) '' {γ | D (γ 1 0, γ 1 1) ≤ 1}
  have hB : B.Finite := (finite_bottom_rows hp 1).subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hγ)
  have hD1 : D (0, 1) = 1 := by simp [hDdef, uhsDen]
  have hB1 : ((0, 1) : 𝓞 K × 𝓞 K) ∈ B := ⟨1, by simp [hD1], by simp⟩
  obtain ⟨_, ⟨γ₀, -, rfl⟩, hmin⟩ := Set.exists_min_image B D hB ⟨_, hB1⟩
  have hle : ∀ γ : SL(2, 𝓞 K), D (γ₀ 1 0, γ₀ 1 1) ≤ D (γ 1 0, γ 1 1) := by
    intro γ
    by_cases h : D (γ 1 0, γ 1 1) ≤ 1
    · exact hmin _ ⟨γ, h, rfl⟩
    · have := hmin _ hB1
      linarith
  refine ⟨γ₀, fun γ => ?_⟩
  rw [slAct_snd, slAct_snd]
  exact div_le_div_of_nonneg_left (le_of_lt hp) (slDen_pos γ₀ hp) (hle γ)

/-- The translation `(1, t; 0, 1)`. -/
def slT (t : 𝓞 K) : SL(2, 𝓞 K) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- `(0, −1; 1, −t)`, which sends `(z, v)` to height `v/(|z − t|² + v²)`. -/
def slS (t : 𝓞 K) : SL(2, 𝓞 K) := ⟨!![0, -1; 1, -t], by simp [Matrix.det_fin_two]⟩

theorem slAct_slT (t : 𝓞 K) (p : ℂ × ℝ) : slAct (slT t) p = (p.1 + σO t, p.2) := by
  have e : ((slT t : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) = !![1, σO t; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [slT]
  unfold slAct actP; rw [e, uhsAct_transl]

theorem coe_slT (t : 𝓞 K) : (slT t : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, t; 0, 1] := rfl

theorem slT_zero : slT 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [slT]

theorem slAct_slS_snd (t : 𝓞 K) (p : ℂ × ℝ) :
    (slAct (slS t) p).2 = p.2 / (Complex.normSq (p.1 - σO t) + p.2 ^ 2) := by
  rw [slAct_snd]
  simp [slS, uhsDen, sub_eq_add_neg]

/-- **The fundamental parallelogram** `{x + yϖ : 0 ≤ x, y < 1}` of `σ(ℤ[ω])`. -/
def fundP : Set ℂ := {z | (Mw.symm z).re ∈ Ico (0 : ℝ) 1 ∧ (Mw.symm z).im ∈ Ico (0 : ℝ) 1}

/-- **The Siegel set** `{(z, v) : z ∈ P, v ≥ 1/2}`. -/
def siegelK : Set (ℂ × ℝ) := {p | p.1 ∈ fundP ∧ 1 / 2 ≤ p.2}

theorem Mw_symm_σO_crd (n : Fin 2 → ℤ) : Mw.symm (σO (crd n)) = cpt (nR n) := by
  rw [σO_crd, LinearEquiv.symm_apply_apply]

/-- Every `z` has a translate in `P`. -/
theorem exists_transl_mem_fundP (z : ℂ) : ∃ t : 𝓞 K, z + σO t ∈ fundP := by
  set w := Mw.symm z
  refine ⟨crd ![-⌊w.re⌋, -⌊w.im⌋], ?_⟩
  have e : Mw.symm (z + σO (crd ![-⌊w.re⌋, -⌊w.im⌋])) = w + cpt (nR ![-⌊w.re⌋, -⌊w.im⌋]) := by
    rw [map_add, Mw_symm_σO_crd]
  change (Mw.symm _).re ∈ Ico (0 : ℝ) 1 ∧ (Mw.symm _).im ∈ Ico (0 : ℝ) 1
  rw [e]
  simp only [cpt, nR, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_neg, mul_zero, sub_zero,
    mul_one, zero_add, add_zero]
  rw [← sub_eq_add_neg, ← sub_eq_add_neg, Int.self_sub_floor, Int.self_sub_floor]
  exact ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩⟩

/-- **A nearest lattice point**: `|z − t|² ≤ 3/4` for some `t ∈ ℤ[ω]`. -/
theorem exists_near (z : ℂ) : ∃ t : 𝓞 K, Complex.normSq (z - σO t) ≤ 3 / 4 := by
  set w := Mw.symm z
  refine ⟨crd ![round w.re, round w.im], ?_⟩
  have e : z - σO (crd ![round w.re, round w.im]) =
      Mw (w - cpt (nR ![round w.re, round w.im])) := by
    rw [map_sub, σO_crd, LinearEquiv.apply_symm_apply]
  rw [e, normSq_Mw]
  have h1 := abs_sub_round w.re
  have h2 := abs_sub_round w.im
  simp only [cpt, nR, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, sub_zero, mul_one,
    zero_add, add_zero]
  rw [abs_le] at h1 h2
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - (w.re - round w.re))
      (by linarith : (0 : ℝ) ≤ 1 / 2 + (w.re - round w.re)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - (w.im - round w.im))
      (by linarith : (0 : ℝ) ≤ 1 / 2 + (w.im - round w.im)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - (w.re - round w.re))
      (by linarith : (0 : ℝ) ≤ 1 / 2 - (w.im - round w.im)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 + (w.re - round w.re))
      (by linarith : (0 : ℝ) ≤ 1 / 2 + (w.im - round w.im))]

/-- **A point of maximal height has `v ≥ 1/2`.** -/
theorem half_le_of_max {q : ℂ × ℝ} (hq : q ∈ UHS)
    (hmax : ∀ γ : SL(2, 𝓞 K), (slAct γ q).2 ≤ q.2) : 1 / 2 ≤ q.2 := by
  have hv : 0 < q.2 := hq
  obtain ⟨t, ht⟩ := exists_near q.1
  have h := hmax (slS t)
  rw [slAct_slS_snd] at h
  have hD : 0 < Complex.normSq (q.1 - σO t) + q.2 ^ 2 := by
    have := Complex.normSq_nonneg (q.1 - σO t); positivity
  rw [div_le_iff₀ hD] at h
  have h1 : 1 ≤ Complex.normSq (q.1 - σO t) + q.2 ^ 2 := by
    by_contra hlt
    have := not_le.1 hlt
    nlinarith
  nlinarith

/-- **Every orbit meets the Siegel set.** -/
theorem exists_mem_siegelK {p : ℂ × ℝ} (hp : p ∈ UHS) : ∃ γ : SL(2, 𝓞 K), slAct γ p ∈ siegelK := by
  obtain ⟨γ₀, h₀⟩ := exists_max_height hp
  have hq : slAct γ₀ p ∈ UHS := slAct_mem γ₀ hp
  obtain ⟨t, ht⟩ := exists_transl_mem_fundP (slAct γ₀ p).1
  refine ⟨slT t * γ₀, ?_⟩
  have e : slAct (slT t * γ₀) p = ((slAct γ₀ p).1 + σO t, (slAct γ₀ p).2) := by
    rw [slAct_mul _ _ hp, slAct_slT]
  refine ⟨by rw [e]; exact ht, ?_⟩
  have hmem : slAct (slT t * γ₀) p ∈ UHS := slAct_mem _ hp
  refine half_le_of_max hmem fun γ => ?_
  rw [← slAct_mul _ _ hp, e]
  exact h₀ _

/-- A translate by `σ(ℤ[ω])` stays in `P` only for `t = 0`. -/
theorem eq_zero_of_mem_fundP {z : ℂ} {t : 𝓞 K} (hz : z ∈ fundP) (hzt : z + σO t ∈ fundP) :
    t = 0 := by
  obtain ⟨n, rfl⟩ := crd_surjective t
  have e : Mw.symm (z + σO (crd n)) = Mw.symm z + cpt (nR n) := by rw [map_add, Mw_symm_σO_crd]
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  obtain ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩ := hzt
  rw [e] at h5 h6 h7 h8
  simp only [cpt, nR, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one,
    zero_add, add_zero] at h5 h6 h7 h8
  have k0 : n 0 = 0 := by
    have a : (n 0 : ℝ) < 1 := by linarith
    have b : (-1 : ℝ) < n 0 := by linarith
    have a' : n 0 < 1 := by exact_mod_cast a
    have b' : -1 < n 0 := by exact_mod_cast b
    omega
  have k1 : n 1 = 0 := by
    have a : (n 1 : ℝ) < 1 := by linarith
    have b : (-1 : ℝ) < n 1 := by linarith
    have a' : n 1 < 1 := by exact_mod_cast a
    have b' : -1 < n 1 := by exact_mod_cast b
    omega
  simp [crd, k0, k1]

/-- `(a′, b′) = (a, b) + (ab′ − a′b)(c, d)` when both rows complete `(c, d)` to determinant `1`. -/
theorem bottom_row_aux {R : Type*} [CommRing R] {a b c d a' b' : R} (hd : a * d - b * c = 1)
    (hd' : a' * d - b' * c = 1) :
    a' = a + (a * b' - a' * b) * c ∧ b' = b + (a * b' - a' * b) * d := by
  constructor
  · linear_combination (-a') * hd + a * hd'
  · linear_combination (-b') * hd + b * hd'

/-- Two elements with the same bottom row differ by a translation on the left. -/
theorem eq_slT_mul {γ γ' : SL(2, 𝓞 K)} (h10 : γ' 1 0 = γ 1 0) (h11 : γ' 1 1 = γ 1 1) :
    γ' = slT (γ 0 0 * γ' 0 1 - γ' 0 0 * γ 0 1) * γ := by
  have hd : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rwa [Matrix.det_fin_two] at this
  have hd' : γ' 0 0 * γ' 1 1 - γ' 0 1 * γ' 1 0 = 1 := by
    have := γ'.2; rwa [Matrix.det_fin_two] at this
  rw [h10, h11] at hd'
  have e : (γ' : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
      (slT (γ 0 0 * γ' 0 1 - γ' 0 0 * γ 0 1) : Matrix (Fin 2) (Fin 2) (𝓞 K)) * γ := by
    rw [coe_slT]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.zero_eta, Fin.mk_one, Fin.isValue, one_mul, zero_mul, zero_add]
    · linear_combination (bottom_row_aux hd hd').1
    · linear_combination (bottom_row_aux hd hd').2
    · exact h10
    · exact h11
  exact Subtype.ext (e.trans (Matrix.SpecialLinearGroup.coe_mul _ _).symm)

/-- **Finitely many `γ` send a point into the Siegel set.** -/
theorem finite_hits {p : ℂ × ℝ} (hp : p ∈ UHS) :
    {γ : SL(2, 𝓞 K) | slAct γ p ∈ siegelK}.Finite := by
  have hv : 0 < p.2 := hp
  refine Set.Finite.of_finite_image (f := fun γ : SL(2, 𝓞 K) => ((γ 1 0, γ 1 1) : 𝓞 K × 𝓞 K))
    ?_ ?_
  · refine (finite_bottom_rows (z := p.1) hv (2 * p.2)).subset ?_
    rintro _ ⟨γ, hγ, rfl⟩
    have h := hγ.2
    rw [slAct_snd, le_div_iff₀ (slDen_pos γ hp)] at h
    change uhsDen (σO (γ 1 0)) (σO (γ 1 1)) p.1 p.2 ≤ 2 * p.2
    linarith
  · intro γ hγ γ' hγ' heq
    simp only [Prod.mk.injEq] at heq
    have e := eq_slT_mul heq.1.symm heq.2.symm
    have h2 : slAct γ' p ∈ siegelK := hγ'
    rw [e, slAct_mul _ _ hp, slAct_slT] at h2
    have ht := eq_zero_of_mem_fundP (hγ : slAct γ p ∈ siegelK).1 h2.1
    rw [e, ht, slT_zero, one_mul]

instance countable_SL : Countable SL(2, 𝓞 K) :=
  Function.Injective.countable (f := fun γ : SL(2, 𝓞 K) => fun i j : Fin 2 => γ i j)
    fun _ _ h => Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h i) j

theorem continuous_Mw : Continuous (Mw : ℂ → ℂ) :=
  (Mw : ℂ →ₗ[ℝ] ℂ).continuous_of_finiteDimensional

theorem continuous_Mw_symm : Continuous (Mw.symm : ℂ → ℂ) :=
  (Mw.symm : ℂ →ₗ[ℝ] ℂ).continuous_of_finiteDimensional

theorem measurableSet_fundP : MeasurableSet fundP := by
  have hm : Measurable (Mw.symm : ℂ → ℂ) := continuous_Mw_symm.measurable
  exact ((Complex.measurable_re.comp hm) measurableSet_Ico).inter
    ((Complex.measurable_im.comp hm) measurableSet_Ico)

theorem measurableSet_siegelK : MeasurableSet siegelK :=
  (measurable_fst measurableSet_fundP).inter (measurableSet_le measurable_const measurable_snd)

theorem siegelK_subset_UHS : siegelK ⊆ UHS := fun p hp => by
  have := hp.2
  show (0 : ℝ) < p.2
  linarith

/-- The number of `γ` with `γ·p` in the Siegel set, as a sum. -/
def hitsK (p : ℂ × ℝ) : ℝ≥0∞ := ∑' γ : SL(2, 𝓞 K), siegelK.indicator 1 (slAct γ p)

/-- **The partition of unity** `ρ = 1_K/#{γ : γ·p ∈ K}`. -/
def rhoK (p : ℂ × ℝ) : ℝ≥0∞ := (hitsK p)⁻¹ * siegelK.indicator 1 p

theorem measurable_hitsK : Measurable hitsK :=
  Measurable.tsum fun γ =>
    (measurable_one.indicator measurableSet_siegelK).comp (measurable_slAct γ)

theorem measurable_rhoK : Measurable rhoK :=
  measurable_hitsK.inv.mul (measurable_one.indicator measurableSet_siegelK)

theorem hitsK_slAct (g : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    hitsK (slAct g p) = hitsK p := by
  unfold hitsK
  calc ∑' γ : SL(2, 𝓞 K), siegelK.indicator 1 (slAct γ (slAct g p))
      = ∑' γ : SL(2, 𝓞 K), siegelK.indicator 1 (slAct (Equiv.mulRight g γ) p) := by
        refine tsum_congr fun γ => ?_
        rw [Equiv.coe_mulRight, slAct_mul _ _ hp]
    _ = ∑' γ : SL(2, 𝓞 K), siegelK.indicator 1 (slAct γ p) :=
        (Equiv.mulRight g).tsum_eq (fun γ => siegelK.indicator 1 (slAct γ p))

theorem one_le_hitsK {p : ℂ × ℝ} (hp : p ∈ UHS) : 1 ≤ hitsK p := by
  obtain ⟨γ, hγ⟩ := exists_mem_siegelK hp
  calc (1 : ℝ≥0∞) = siegelK.indicator 1 (slAct γ p) := by
        rw [Set.indicator_of_mem hγ, Pi.one_apply]
    _ ≤ hitsK p := ENNReal.le_tsum (f := fun γ => siegelK.indicator 1 (slAct γ p)) γ

theorem hitsK_ne_top {p : ℂ × ℝ} (hp : p ∈ UHS) : hitsK p ≠ ⊤ := by
  have hfin := finite_hits hp
  unfold hitsK
  rw [tsum_eq_sum (s := hfin.toFinset) fun γ hγ => ?_]
  · refine ENNReal.sum_ne_top.2 fun γ _ => ?_
    by_cases h : slAct γ p ∈ siegelK
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  · rw [Set.Finite.mem_toFinset] at hγ
    exact Set.indicator_of_notMem (show slAct γ p ∉ siegelK from hγ) _

/-- **`ρ` is a partition of unity for `SL_2(ℤ[ω])`**: `Σ_γ ρ(γ·p) = 1` on upper half-space. -/
theorem tsum_rhoK {p : ℂ × ℝ} (hp : p ∈ UHS) : ∑' γ : SL(2, 𝓞 K), rhoK (slAct γ p) = 1 := by
  unfold rhoK
  calc ∑' γ : SL(2, 𝓞 K), (hitsK (slAct γ p))⁻¹ * siegelK.indicator 1 (slAct γ p)
      = ∑' γ : SL(2, 𝓞 K), (hitsK p)⁻¹ * siegelK.indicator 1 (slAct γ p) := by
        refine tsum_congr fun γ => ?_
        rw [hitsK_slAct γ hp]
    _ = (hitsK p)⁻¹ * hitsK p := ENNReal.tsum_mul_left
    _ = 1 := ENNReal.inv_mul_cancel (zero_lt_one.trans_le (one_le_hitsK hp)).ne'
        (hitsK_ne_top hp)

theorem rhoK_le (p : ℂ × ℝ) : rhoK p ≤ siegelK.indicator 1 p := by
  unfold rhoK
  by_cases h : p ∈ siegelK
  · rw [Set.indicator_of_mem h, Pi.one_apply, mul_one]
    exact ENNReal.inv_le_one.2 (one_le_hitsK (siegelK_subset_UHS h))
  · rw [Set.indicator_of_notMem h, mul_zero]

theorem fundP_subset : fundP ⊆ Mw '' Metric.closedBall 0 2 := by
  intro z hz
  refine ⟨Mw.symm z, ?_, Mw.apply_symm_apply z⟩
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖Mw.symm z‖ ≤ |(Mw.symm z).re| + |(Mw.symm z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 := by rw [abs_of_nonneg h1, abs_of_nonneg h3]; linarith

theorem volume_fundP_lt_top : volume fundP < ⊤ :=
  (measure_mono fundP_subset).trans_lt ((isCompact_closedBall 0 2).image continuous_Mw).measure_lt_top

theorem lintegral_Ioi_zpow_lt_top :
    ∫⁻ v in Ioi (1 / 4 : ℝ), ENNReal.ofReal (v ^ (-3 : ℤ)) < ⊤ := by
  have h : IntegrableOn (fun v : ℝ => v ^ (-3 : ℝ)) (Ioi (1 / 4)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h' : IntegrableOn (fun v : ℝ => v ^ (-3 : ℤ)) (Ioi (1 / 4)) := by
    refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
    have := Real.rpow_intCast v (-3)
    simp only [Int.cast_neg, Int.cast_ofNat] at this
    exact this
  exact Integrable.lintegral_lt_top h'

/-- **The Siegel set has finite volume.** -/
theorem uhsMeasure_siegelK_lt_top : uhsMeasure siegelK < ⊤ := by
  rw [uhsMeasure, withDensity_apply _ measurableSet_siegelK,
    Measure.restrict_restrict measurableSet_siegelK]
  have hsub : siegelK ∩ UHS ⊆ fundP ×ˢ Ioi (1 / 4 : ℝ) := fun p hp => by
    have := hp.1.2
    exact ⟨hp.1.1, show (1 / 4 : ℝ) < p.2 by linarith⟩
  have e : ∫⁻ p in fundP ×ˢ Ioi (1 / 4 : ℝ), uhsW p =
      volume fundP * ∫⁻ v in Ioi (1 / 4 : ℝ), ENNReal.ofReal (v ^ (-3 : ℤ)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    have := lintegral_prod_mul (μ := volume.restrict fundP) (ν := volume.restrict (Ioi (1 / 4 : ℝ)))
      (f := fun _ => (1 : ℝ≥0∞)) (g := fun v : ℝ => ENNReal.ofReal (v ^ (-3 : ℤ)))
      aemeasurable_const (by fun_prop)
    simp only [one_mul] at this
    rw [show (fun p : ℂ × ℝ => uhsW p) = fun p => ENNReal.ofReal (p.2 ^ (-3 : ℤ)) from rfl, this]
    simp
  calc ∫⁻ p in siegelK ∩ UHS, uhsW p ≤ ∫⁻ p in fundP ×ˢ Ioi (1 / 4 : ℝ), uhsW p :=
        lintegral_mono_set hsub
    _ < ⊤ := by
        rw [e]; exact ENNReal.mul_lt_top volume_fundP_lt_top lintegral_Ioi_zpow_lt_top

/-- **The quotient has finite volume**: `∫ρ dz dv/v³ < ∞`. -/
theorem lintegral_rhoK_lt_top : ∫⁻ p, rhoK p ∂uhsMeasure < ⊤ :=
  calc ∫⁻ p, rhoK p ∂uhsMeasure ≤ ∫⁻ p, siegelK.indicator 1 p ∂uhsMeasure := lintegral_mono rhoK_le
    _ = uhsMeasure siegelK := lintegral_indicator_one measurableSet_siegelK
    _ < ⊤ := uhsMeasure_siegelK_lt_top

end Eis

end

#print axioms Eis.slAct_mul
#print axioms Eis.slAct_mem
#print axioms Eis.slAct_snd
#print axioms Eis.normSq_Mw
#print axioms Eis.finite_normSq_le
#print axioms Eis.finite_bottom_rows
#print axioms Eis.slDen_pos
#print axioms Eis.slAct_one
#print axioms Eis.measurable_slAct
#print axioms Eis.exists_max_height
#print axioms Eis.slAct_slT
#print axioms Eis.coe_slT
#print axioms Eis.slT_zero
#print axioms Eis.slAct_slS_snd
#print axioms Eis.Mw_symm_σO_crd
#print axioms Eis.exists_transl_mem_fundP
#print axioms Eis.exists_near
#print axioms Eis.half_le_of_max
#print axioms Eis.exists_mem_siegelK
#print axioms Eis.eq_zero_of_mem_fundP
#print axioms Eis.bottom_row_aux
#print axioms Eis.eq_slT_mul
#print axioms Eis.finite_hits
#print axioms Eis.continuous_Mw
#print axioms Eis.continuous_Mw_symm
#print axioms Eis.measurableSet_fundP
#print axioms Eis.measurableSet_siegelK
#print axioms Eis.siegelK_subset_UHS
#print axioms Eis.measurable_hitsK
#print axioms Eis.measurable_rhoK
#print axioms Eis.hitsK_slAct
#print axioms Eis.one_le_hitsK
#print axioms Eis.hitsK_ne_top
#print axioms Eis.tsum_rhoK
#print axioms Eis.rhoK_le
#print axioms Eis.fundP_subset
#print axioms Eis.volume_fundP_lt_top
#print axioms Eis.lintegral_Ioi_zpow_lt_top
#print axioms Eis.uhsMeasure_siegelK_lt_top
#print axioms Eis.lintegral_rhoK_lt_top
