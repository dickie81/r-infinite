import KubotaCubeEigen

/-! # θ's coefficients at `p³m` (round 449)

S5f-12 of round 360's plan, part 10. Round 448's next step planned the cube average of a theta-type series
and, from round 448's `thS_cube_eigen_coord`, the relation `τ(p³m) = |p|·τ(m)` for θ's coefficients `τ` (round
436's `tauTh`). This round proves them, for a primary prime `p`:

* **The character sum** (`sum_ebr_quot`): `Σ_{q mod c} ĕ(σ(δ₃x)·(σ(3q)/σ(c))/9)` is `N(c)` when `c ∣ x` and
  `0` otherwise, for `c ≠ 0` (round 363's `ebr_shift` and `sum_ψc_mul`).
* **The cube average of a theta-type series** (`thTerm_add_div`, `thTerm_cube` and `sum_thTerm_cube`;
  **`cube_avg_thSer`**): for `d` with `|d(m)| ≤ C|m|⁵` and `d(0) = 0`, supported on `δ₃ℤ[ω]`,
  `N(p)⁻³Σ_{q mod p³} thSer(c, d)((z + 3q)/p³, v/|p|³) = thSer(N(p)⁻¹c, d′)(z, v)` with `d′(m) = |p|⁻³d(p³m)`,
  for every `z ∈ ℂ` and `v > 0`. The sum over `q` keeps the terms whose index is divisible by `p³δ₃`.
* **The coefficients** (`thSer_coef_eq`; **`tauTh_cube`** and **`rhoM_cube`**): a theta-type series determines
  its coefficients (round 436's `integral_ebr_thSer`), so the cube eigenrelation gives `τ(p³m) = |p|·τ(m)` for
  every `m ∈ ℤ[ω]`, and `ρ(p³x) = |p|·ρ(x)` for `x ≠ 0` (round 431's `rhoM`).
-/

open Ideal NumberField MeasureTheory Set
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Eis

/-! ### The character sum -/

open Classical in
/-- **The character sum over `ℤ[ω]/c`**: `Σ_{q mod c} ĕ(σ(δ₃x)·(σ(3q)/σ(c))/9) = N(c)·1_{c ∣ x}` for `c ≠ 0`
(round 363's `ebr_shift` and `sum_ψc_mul`). -/
theorem sum_ebr_quot (c : 𝓞 K) (hc : c ≠ 0) [Fintype (𝓞 K ⧸ span {c})] (x : 𝓞 K) :
    ∑ q : 𝓞 K ⧸ span {c}, ebr (σO (δ3 * x) * (σO (3 * repQ c q) / σO c) / 9) =
      if c ∣ x then (absNorm (span {c}) : ℂ) else 0 := by
  classical
  have e : ∀ q : 𝓞 K ⧸ span {c},
      ebr (σO (δ3 * x) * (σO (3 * repQ c q) / σO c) / 9) = ψc c (repQ c q * -x) := by
    intro q
    have h := ebr_shift c (-repQ c q) x
    have e1 : σO (δ3 ^ 2 * -repQ c q) = σO (3 * repQ c q) := by rw [δ3_sq]; congr 1; ring
    rw [e1] at h
    rw [h]; congr 1; ring
  simp_rw [e]
  rw [sum_ψc_mul c hc (-x)]
  have hiff : Ideal.Quotient.mk (span {c}) (-x) = 0 ↔ c ∣ x := by
    rw [map_neg, neg_eq_zero, Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton]
  exact if_congr hiff rfl rfl

/-! ### The cube average of a theta-type series -/

/-- Round 436's term `thTerm` at `(z + s)/P` is its term at `z/P` times the phase `ĕ(σ(m)·(s/P)/9)`. -/
theorem thTerm_add_div (d : 𝓞 K → ℂ) (m : 𝓞 K) (z s P : ℂ) (v : ℝ) :
    thTerm d m ((z + s) / P, v) = thTerm d m (z / P, v) * ebr (σO m * (s / P) / 9) := by
  unfold thTerm
  dsimp only
  rw [show σO m * ((z + s) / P) / 9 = σO m * (z / P) / 9 + σO m * (s / P) / 9 by ring, ebr_add]
  ring

/-- For `p ≠ 0`, the term of index `p³m` at `(z/p³, v/|p|³)` is the term of index `m` at `(z, v)` of the
coefficients `m ↦ |p|⁻³d(p³m)`. -/
theorem thTerm_cube (d : 𝓞 K → ℂ) {p : 𝓞 K} (hp : p ≠ 0) (m : 𝓞 K) (z : ℂ) (v : ℝ) :
    thTerm d (p ^ 3 * m) (z / σO p ^ 3, v / ‖σO p‖ ^ 3) =
      thTerm (fun m => ((‖σO p‖ ^ 3 : ℝ) : ℂ)⁻¹ * d (p ^ 3 * m)) m (z, v) := by
  have hσp : σO p ≠ 0 := σO_ne_zero hp
  have hnp : ‖σO p‖ ≠ 0 := norm_ne_zero_iff.2 hσp
  have earg : 4 * Real.pi * ‖σO (p ^ 3 * m)‖ * (v / ‖σO p‖ ^ 3) / 9 = 4 * Real.pi * ‖σO m‖ * v / 9 := by
    rw [map_mul, map_pow, norm_mul, norm_pow]; field_simp
  have ephase : σO (p ^ 3 * m) * (z / σO p ^ 3) / 9 = σO m * z / 9 := by
    rw [map_mul, map_pow]; field_simp
  show d (p ^ 3 * m) * ((v / ‖σO p‖ ^ 3 : ℝ) : ℂ) *
      besselK (1 / 3) (4 * Real.pi * ‖σO (p ^ 3 * m)‖ * (v / ‖σO p‖ ^ 3) / 9) *
      ebr (σO (p ^ 3 * m) * (z / σO p ^ 3) / 9) =
    ((‖σO p‖ ^ 3 : ℝ) : ℂ)⁻¹ * d (p ^ 3 * m) * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) *
      ebr (σO m * z / 9)
  rw [earg, ephase]
  push_cast
  ring

open Classical in
/-- **The sum over `q mod p³` of the terms of index `m`** at `((z + 3q)/p³, v)`: `N(p)³` times the term at
`(z/p³, v)` when `p³δ₃ ∣ m`, and `0` otherwise, for `d` supported on `δ₃ℤ[ω]` and `p ≠ 0`. -/
theorem sum_thTerm_cube {d : 𝓞 K → ℂ} (hsupp : ∀ m, d m ≠ 0 → δ3 ∣ m) {p : 𝓞 K} (hp : p ≠ 0)
    [Fintype (𝓞 K ⧸ span {p ^ 3})] (m : 𝓞 K) (z : ℂ) (v : ℝ) :
    ∑ q : 𝓞 K ⧸ span {p ^ 3}, thTerm d m ((z + σO (3 * repQ (p ^ 3) q)) / σO p ^ 3, v) =
      if p ^ 3 * δ3 ∣ m then (absNorm (span {p}) : ℂ) ^ 3 * thTerm d m (z / σO p ^ 3, v) else 0 := by
  have hp3 : p ^ 3 ≠ 0 := pow_ne_zero 3 hp
  by_cases hdm : d m = 0
  · simp [thTerm, hdm]
  obtain ⟨x, rfl⟩ := hsupp m hdm
  simp_rw [thTerm_add_div]
  rw [← Finset.mul_sum]
  have hP : σO p ^ 3 = σO (p ^ 3) := (map_pow σO p 3).symm
  simp_rw [hP]
  rw [sum_ebr_quot (p ^ 3) hp3 x]
  have hN3 : ((absNorm (span {p ^ 3}) : ℕ) : ℂ) = (absNorm (span {p}) : ℂ) ^ 3 := by
    rw [← Ideal.span_singleton_pow, map_pow, Nat.cast_pow]
  have hiff : p ^ 3 * δ3 ∣ δ3 * x ↔ p ^ 3 ∣ x := by
    rw [mul_comm (p ^ 3) δ3]; exact mul_dvd_mul_iff_left δ3_ne_zero
  by_cases hx : p ^ 3 ∣ x
  · rw [ite_eq_left hx, ite_eq_left (hiff.2 hx), hN3]; ring
  · rw [ite_eq_right hx, ite_eq_right (mt hiff.1 hx), mul_zero]

/-- **The cube average of a theta-type series**: for `d` with `|d(m)| ≤ C|m|⁵`, `d(0) = 0`, supported on
`δ₃ℤ[ω]`, `p` primary and `v > 0`, `N(p)⁻³Σ_{q mod p³} thSer(c, d)((z + 3q)/p³, v/|p|³)` is
`thSer(N(p)⁻¹c, d′)(z, v)` with `d′(m) = |p|⁻³d(p³m)`. -/
theorem cube_avg_thSer (c : ℂ) {d : 𝓞 K → ℂ} {C : ℝ} (hC : 0 ≤ C) (hd : ∀ m, ‖d m‖ ≤ C * ‖σO m‖ ^ 5)
    (hd0 : d 0 = 0) (hsupp : ∀ m, d m ≠ 0 → δ3 ∣ m) {p : 𝓞 K} (hpp : Primary p) (z : ℂ) {v : ℝ}
    (hv : 0 < v) :
    ((absNorm (span {p}) : ℂ) ^ 3)⁻¹ * ∑' q : 𝓞 K ⧸ span {p ^ 3},
        thSer c d ((z + σO (3 * repQ (p ^ 3) q)) / σO p ^ 3) (v / ‖σO p‖ ^ 3) =
      thSer ((absNorm (span {p}) : ℂ)⁻¹ * c) (fun m => ((‖σO p‖ ^ 3 : ℝ) : ℂ)⁻¹ * d (p ^ 3 * m)) z v := by
  classical
  have hp := primary_ne_zero hpp
  have hp3 : p ^ 3 ≠ 0 := pow_ne_zero 3 hp
  have := finite_quot_pow3 hp
  have := Fintype.ofFinite (𝓞 K ⧸ span {p ^ 3})
  have hσp : σO p ≠ 0 := σO_ne_zero hp
  have hnp : 0 < ‖σO p‖ := norm_pos_iff.2 hσp
  have hv' : 0 < v / ‖σO p‖ ^ 3 := by positivity
  have hN0 : (absNorm (span {p}) : ℂ) ≠ 0 := absNorm_span_ne_zero hp
  have hN3 : ((absNorm (span {p ^ 3}) : ℕ) : ℂ) = (absNorm (span {p}) : ℂ) ^ 3 := by
    rw [← Ideal.span_singleton_pow, map_pow, Nat.cast_pow]
  have hcop : IsCoprime δ3 (p ^ 3) := (isCoprime_δ3 hpp).pow_right
  rw [tsum_fintype]
  simp only [thSer_eq]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_quot, nsmul_eq_mul, hN3,
    ← Summable.tsum_finsetSum fun q _ => summable_thTerm hC hd hd0
      (p := ((z + σO (3 * repQ (p ^ 3) q)) / σO p ^ 3, v / ‖σO p‖ ^ 3)) hv']
  simp_rw [sum_thTerm_cube hsupp hp]
  have hinj : Function.Injective fun m' : 𝓞 K => p ^ 3 * m' := mul_right_injective₀ hp3
  have hsub : Function.support (fun m : 𝓞 K => if p ^ 3 * δ3 ∣ m then
      (absNorm (span {p}) : ℂ) ^ 3 * thTerm d m (z / σO p ^ 3, v / ‖σO p‖ ^ 3) else 0) ⊆
      Set.range fun m' : 𝓞 K => p ^ 3 * m' := by
    intro m hm
    by_contra hr
    apply hm
    refine ite_eq_right fun ⟨k, hk⟩ => hr ⟨δ3 * k, ?_⟩
    rw [hk]; ring
  rw [← hinj.tsum_eq hsub]
  have hterm : ∀ m' : 𝓞 K, (if p ^ 3 * δ3 ∣ p ^ 3 * m' then
      (absNorm (span {p}) : ℂ) ^ 3 * thTerm d (p ^ 3 * m') (z / σO p ^ 3, v / ‖σO p‖ ^ 3) else 0) =
      (absNorm (span {p}) : ℂ) ^ 3 *
        thTerm (fun m => ((‖σO p‖ ^ 3 : ℝ) : ℂ)⁻¹ * d (p ^ 3 * m)) m' (z, v) := by
    intro m'
    rw [← thTerm_cube d hp m' z v]
    by_cases h : δ3 ∣ m'
    · rw [ite_eq_left (mul_dvd_mul_left _ h)]
    · rw [ite_eq_right fun h' => h ((mul_dvd_mul_iff_left hp3).1 h')]
      have h0 : d (p ^ 3 * m') = 0 := by
        by_contra h0
        exact h (hcop.dvd_of_dvd_mul_left (hsupp _ h0))
      simp [thTerm, h0]
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hv23 : (v / ‖σO p‖ ^ 3) ^ (2 / 3 : ℝ) = v ^ (2 / 3 : ℝ) / ‖σO p‖ ^ 2 := by
    rw [Real.div_rpow hv.le (by positivity), ← Real.rpow_natCast ‖σO p‖ 3, ← Real.rpow_mul hnp.le]
    norm_num
  have hN2 : ((‖σO p‖ : ℂ)) ^ 2 = (absNorm (span {p}) : ℂ) := by
    have := sq_norm_σO p
    exact_mod_cast this
  rw [hv23]
  push_cast
  rw [hN2]
  field_simp

/-! ### θ's coefficients at `p³m` -/

/-- **A theta-type series determines its coefficients**: if `thSer(c₁, d₁)(z, v) = thSer(c₂, d₂)(z, v)` for
every `z`, at a height `v > 0`, for coefficients as in round 436's `integral_ebr_thSer`, then
`d₁(δ₃x) = d₂(δ₃x)` for `x ≠ 0`. -/
theorem thSer_coef_eq {c₁ c₂ : ℂ} {d₁ d₂ : 𝓞 K → ℂ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hd₁ : ∀ m, ‖d₁ m‖ ≤ C₁ * ‖σO m‖ ^ 5) (hd₂ : ∀ m, ‖d₂ m‖ ≤ C₂ * ‖σO m‖ ^ 5) (h0₁ : d₁ 0 = 0)
    (h0₂ : d₂ 0 = 0) (hs₁ : ∀ m, d₁ m ≠ 0 → δ3 ∣ m) (hs₂ : ∀ m, d₂ m ≠ 0 → δ3 ∣ m) {v : ℝ} (hv : 0 < v)
    (h : ∀ z, thSer c₁ d₁ z v = thSer c₂ d₂ z v) {x : 𝓞 K} (hx : x ≠ 0) : d₁ (δ3 * x) = d₂ (δ3 * x) := by
  have e1 := integral_ebr_thSer c₁ hC₁ hd₁ h0₁ hs₁ x hv
  have e2 := integral_ebr_thSer c₂ hC₂ hd₂ h0₂ hs₂ x hv
  simp only [h] at e1
  rw [e1, ite_eq_right hx, ite_eq_right hx, zero_add, zero_add] at e2
  have hσ : σO (δ3 * x) ≠ 0 := σO_ne_zero (mul_ne_zero δ3_ne_zero hx)
  have hK : besselK (1 / 3) (4 * Real.pi * ‖σO (δ3 * x)‖ * v / 9) ≠ 0 := by
    rw [besselK_third_ofReal]
    have : 0 < 4 * Real.pi * ‖σO (δ3 * x)‖ * v / 9 := by
      have := norm_pos_iff.2 hσ
      positivity
    exact_mod_cast (mul_pos one_half_pos (bkR_pos this _)).ne'
  have hv0 : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have := mul_left_cancel₀ nine_sqrt_ne_zero e2
  exact mul_right_cancel₀ hv0 (mul_right_cancel₀ hK this)

/-- **θ's coefficients at `p³m`**: `τ(p³m) = |p|·τ(m)` for a primary prime `p` and every `m ∈ ℤ[ω]`, with `τ`
θ's coefficients (round 436's `tauTh`). -/
theorem tauTh_cube {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p) (hpp : Primary p)
    (m : 𝓞 K) : tauTh r Y hY (p ^ 3 * m) = (‖σO p‖ : ℂ) * tauTh r Y hY m := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_norm_tauTh_le hr hY
  have hp0 := hp.ne_zero
  have hσp : σO p ≠ 0 := σO_ne_zero hp0
  have hnp : 0 < ‖σO p‖ := norm_pos_iff.2 hσp
  have hcop : IsCoprime δ3 (p ^ 3) := (isCoprime_δ3 hpp).pow_right
  have hs : ∀ m, tauTh r Y hY m ≠ 0 → δ3 ∣ m := fun m h => dvd_of_tauTh_ne_zero h
  have hN0 : (absNorm (span {p}) : ℂ) ≠ 0 := absNorm_span_ne_zero hp0
  have hN2 : ((‖σO p‖ : ℂ)) ^ 2 = (absNorm (span {p}) : ℂ) := by
    have := sq_norm_σO p
    exact_mod_cast this
  have key : ∀ z, thSer ((absNorm (span {p}) : ℂ)⁻¹ * (phiG (4 / 3) / 3))
      (fun m => ((‖σO p‖ ^ 3 : ℝ) : ℂ)⁻¹ * tauTh r Y hY (p ^ 3 * m)) z 1 =
      thSer ((absNorm (span {p}) : ℂ)⁻¹ * (phiG (4 / 3) / 3))
        (fun m => (absNorm (span {p}) : ℂ)⁻¹ * tauTh r Y hY m) z 1 := by
    intro z
    rw [← cube_avg_thSer _ hC0 hC (tauTh_zero r Y hY) hs hpp z one_pos, thSer_mul_const]
    exact thS_cube_eigen_coord hr hY hp hpp z one_pos
  have hb₁ : ∀ m, ‖((‖σO p‖ ^ 3 : ℝ) : ℂ)⁻¹ * tauTh r Y hY (p ^ 3 * m)‖ ≤
      C * ‖σO p‖ ^ 12 * ‖σO m‖ ^ 5 := by
    intro m
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc (‖σO p‖ ^ 3)⁻¹ * ‖tauTh r Y hY (p ^ 3 * m)‖ ≤ (‖σO p‖ ^ 3)⁻¹ * (C * ‖σO (p ^ 3 * m)‖ ^ 5) :=
          mul_le_mul_of_nonneg_left (hC _) (by positivity)
      _ = C * ‖σO p‖ ^ 12 * ‖σO m‖ ^ 5 := by
          rw [map_mul, map_pow, norm_mul, norm_pow]; field_simp
  have hb₂ : ∀ m, ‖(absNorm (span {p}) : ℂ)⁻¹ * tauTh r Y hY m‖ ≤
      ‖(absNorm (span {p}) : ℂ)⁻¹‖ * C * ‖σO m‖ ^ 5 := by
    intro m
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC m) (norm_nonneg _)
  have hz₁ : ((‖σO p‖ ^ 3 : ℝ) : ℂ)⁻¹ * tauTh r Y hY (p ^ 3 * 0) = 0 := by
    rw [mul_zero, tauTh_zero, mul_zero]
  have hz₂ : (absNorm (span {p}) : ℂ)⁻¹ * tauTh r Y hY 0 = 0 := by rw [tauTh_zero, mul_zero]
  have hs₁ : ∀ m, ((‖σO p‖ ^ 3 : ℝ) : ℂ)⁻¹ * tauTh r Y hY (p ^ 3 * m) ≠ 0 → δ3 ∣ m :=
    fun m h => hcop.dvd_of_dvd_mul_left (hs _ (right_ne_zero_of_mul h))
  have hs₂ : ∀ m, (absNorm (span {p}) : ℂ)⁻¹ * tauTh r Y hY m ≠ 0 → δ3 ∣ m :=
    fun m h => hs _ (right_ne_zero_of_mul h)
  by_cases hm : ∃ x, x ≠ 0 ∧ m = δ3 * x
  · obtain ⟨x, hx, rfl⟩ := hm
    have h := thSer_coef_eq (by positivity) (mul_nonneg (norm_nonneg _) hC0) hb₁
      (fun m => (hb₂ m).trans_eq (by ring)) hz₁ hz₂ hs₁ hs₂ one_pos key hx
    have hn3 : ((‖σO p‖ ^ 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hnp 3).ne'
    rw [show p ^ 3 * (δ3 * x) = δ3 * (p ^ 3 * x) by ring] at *
    have h' : tauTh r Y hY (δ3 * (p ^ 3 * x)) =
        ((‖σO p‖ ^ 3 : ℝ) : ℂ) * ((absNorm (span {p}) : ℂ)⁻¹ * tauTh r Y hY (δ3 * x)) := by
      rw [← h]; field_simp
    rw [h', ← hN2]
    push_cast
    field_simp
  · have h0 : tauTh r Y hY m = 0 := tauTh_of_not r Y hY hm
    have h1 : tauTh r Y hY (p ^ 3 * m) = 0 := by
      refine tauTh_of_not r Y hY fun ⟨y, hy, hpy⟩ => hm ?_
      obtain ⟨x, rfl⟩ := hcop.dvd_of_dvd_mul_left (hpy ▸ dvd_mul_right δ3 y)
      refine ⟨x, ?_, rfl⟩
      rintro rfl
      rw [mul_zero, mul_zero] at hpy
      exact hy ((mul_eq_zero.1 hpy.symm).resolve_left δ3_ne_zero)
    rw [h0, h1, mul_zero]

/-- **θ's Fourier coefficients at `p³x`**: `ρ(p³x) = |p|·ρ(x)` for a primary prime `p` and `x ≠ 0`, with round
431's `rhoM` (round 436's `tauTh_δ3_mul`). -/
theorem rhoM_cube {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p) (hpp : Primary p)
    {x : 𝓞 K} (hx : x ≠ 0) : rhoM (p ^ 3 * x) r Y hY = (‖σO p‖ : ℂ) * rhoM x r Y hY := by
  have h := tauTh_cube hr hY hp hpp (δ3 * x)
  rw [show p ^ 3 * (δ3 * x) = δ3 * (p ^ 3 * x) by ring,
    tauTh_δ3_mul r Y hY (mul_ne_zero (pow_ne_zero 3 hp.ne_zero) hx), tauTh_δ3_mul r Y hY hx,
    div_eq_iff nine_sqrt_ne_zero] at h
  rw [h]
  field_simp

end Eis

end

#print axioms Eis.sum_ebr_quot
#print axioms Eis.thTerm_add_div
#print axioms Eis.thTerm_cube
#print axioms Eis.sum_thTerm_cube
#print axioms Eis.cube_avg_thSer
#print axioms Eis.thSer_coef_eq
#print axioms Eis.tauTh_cube
#print axioms Eis.rhoM_cube
