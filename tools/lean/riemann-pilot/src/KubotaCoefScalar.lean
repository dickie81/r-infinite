import KubotaCoefUnit

/-! # The display's scalar: `C = τ(δ₃) ≠ 0` (round 457)

S5f-14 of round 360's plan, part 2. Round 456's next step planned the display's `C ≠ 0`, that is `τ(δ₃) ≠ 0`,
with θ's coefficients at the unit multiples by `ω`. This round proves both, with `S` round 436's `thS`:

* **The mask from `T`** (`besselK_third_ne_zero`, `thS_add_one`, `ebr_eq_one_of_rhoM_ne_zero`,
  `two_re_σO_δ3_crd`, `mask_of_ebr` and **`tauTh_mask`**): `S(z + 1, v) = S(z, v)` gives `ĕ(σ(δ₃x)/9) = 1`
  where `ρ(x) ≠ 0`, and for `x = a + bω` that is `3 ∣ b`; so `τ(δ₃x) ≠ 0` only if `3 ∣ x` or `x ≡ ±1 (mod 3)`.
* **The primary indices** (**`rhoM_primary_eq_zero`**): `ρ(x) = 0` for every primary `x` when `ρ(1) = 0`.
* **Periodicity under `ℤ[ω]`** (`rhoM_one_eq_zero`, `dvd_of_tauTh_ne_zero_of_scalar` and `thSer_add_O`): if
  `τ(δ₃) = 0`, `τ` is supported on `3δ₃ℤ[ω]` and `S` is periodic under `ℤ[ω]`.
* **The witness** (`perW`, `lowThree`, `perW_eq`, `perW_mem`, `absNorm_span_one_add_three_ω`,
  `isMaximal_span_one_add_three_ω`, `three_not_mem_span_one_add_three_ω` and **`kub_perW_ne_one`**):
  `W = T_{−ω}·(1, 0; −3, 1)·T_ω = (1 + 3ω, 3ω²; −3, 1 − 3ω)` lies in `Γ_1(3)`, and
  `κ(W) = ((−3)/(1 + 3ω))₃ ≠ 1`.
* **`C ≠ 0`** (`thS_eq_zero_of_scalar`, **`tauTh_δ3_ne_zero`** and **`exists_display_coef`**): if `τ(δ₃) = 0`,
  `W` fixes `S` and multiplies it by `κ(W) ≠ 1`, so `S = 0`, against its constant term
  `(9√3/2)·Res φ·v^{2/3} ≠ 0`.
-/

open Ideal NumberField MeasureTheory
open scoped BigOperators ComplexConjugate MatrixGroups

noncomputable section

namespace Eis

/-! ### The mask from `T` -/

/-- **`K_{1/3}(u) ≠ 0` for `u > 0`**: it is half of round 361's `bkR` (round 374's `besselK_third_ofReal`),
which is positive (round 431's `bkR_pos`). -/
theorem besselK_third_ne_zero {u : ℝ} (hu : 0 < u) : besselK (1 / 3) u ≠ 0 := by
  rw [besselK_third_ofReal]
  have h := bkR_pos hu (1 / 3)
  exact_mod_cast (by positivity : (0 : ℝ) < 1 / 2 * bkR (1 / 3) u).ne'

/-- **`S(z + 1, v) = S(z, v)`**, round 443's `thS_slAct_toSL` at `T`. -/
theorem thS_add_one {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    thS r Y hY (z + 1, v) = thS r Y hY (z, v) := by
  have h := thS_slAct_toSL hr hY ModularGroup.T (p := (z, v)) (show (z, v) ∈ UHS from hv)
  rwa [slAct_sT] at h

/-- **`ĕ(σ(δ₃x)/9) = 1` where `ρ(x) ≠ 0`**: the coefficient of `S(z + 1, v)` at `δ₃x` is `ĕ(σ(δ₃x)/9)` times
that of `S(z, v)` (round 443's `integral_fundP3_add`), and the two agree (`thS_add_one`). The coefficient is
`ρ(x)·v·K_{1/3}(4π|σ(δ₃x)/9|v)` (round 436's `integral_ebr_thS`), nonzero for `ρ(x) ≠ 0`. -/
theorem ebr_eq_one_of_rhoM_ne_zero {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {x : 𝓞 K} (hx : x ≠ 0)
    (hρ : rhoM x r Y hY ≠ 0) : ebr (σO (δ3 * x) / 9) = 1 := by
  set a : ℂ := σO (δ3 * x) / 9 with ha
  set g : ℂ → ℂ := fun z => ebr (-(a * z)) * thS r Y hY (z, 1) with hg
  have hper : ∀ z u, g (z + σO (3 * u)) = g z := by
    intro z u
    simp only [hg, ha]
    rw [ebr_neg_mul_add_period, thS_add_period]
  have h1 := integral_fundP3_add hper 1
  have h2 : ∀ z, g (z + 1) = ebr (-a) * g z := by
    intro z
    simp only [hg]
    rw [thS_add_one hr hY z one_pos, show -(a * (z + 1)) = -a + -(a * z) by ring, ebr_add]
    ring
  simp_rw [h2] at h1
  rw [integral_const_mul] at h1
  have hI : ∫ z in fundP3, g z = rhoM x r Y hY *
      (((1 : ℝ) : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO (δ3 * x) / 9‖ * 1)) :=
    integral_ebr_thS hr hY hx one_pos
  have hpos : 0 < 4 * Real.pi * ‖σO (δ3 * x) / 9‖ * 1 := by
    have : 0 < ‖σO (δ3 * x) / 9‖ :=
      norm_pos_iff.2 (div_ne_zero (σO_ne_zero (mul_ne_zero δ3_ne_zero hx)) (by norm_num))
    positivity
  have hne : rhoM x r Y hY *
      (((1 : ℝ) : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO (δ3 * x) / 9‖ * 1)) ≠ 0 :=
    mul_ne_zero hρ (mul_ne_zero (by norm_num) (besselK_third_ne_zero hpos))
  rw [hI] at h1
  have h3 : ebr (-a) = 1 := (mul_eq_right₀ hne).1 h1
  have h4 : ebr a * ebr (-a) = 1 := by rw [← ebr_add, add_neg_cancel, ebr_zero]
  rw [h3, mul_one] at h4
  exact h4

/-- **`2·Re(σ(δ₃x)/9) = −b/3`** for `x = a + bω` (round 294's `crd`). -/
theorem two_re_σO_δ3_crd (c : Fin 2 → ℤ) : 2 * (σO (δ3 * crd c) / 9).re = -(c 1 : ℝ) / 3 := by
  have hs := varpi_re_im
  rw [map_mul, σO_δ3]
  simp only [crd, map_add, map_mul, map_intCast, σO_ω]
  simp [Complex.mul_re, Complex.mul_im, hs.1]
  linear_combination (-(4 / 9) * (c 1 : ℝ)) * hs.2

/-- **The mask**: `ĕ(σ(δ₃x)/9) = e^{−2πib/3}` for `x = a + bω`, so `ĕ(σ(δ₃x)/9) = 1` gives `3 ∣ b`, and then
`3 ∣ x`, `x` primary or `−x` primary, as `a ≡ 0`, `1` or `2 (mod 3)`. -/
theorem mask_of_ebr {x : 𝓞 K} (h : ebr (σO (δ3 * x) / 9) = 1) :
    (3 : 𝓞 K) ∣ x ∨ Primary x ∨ Primary (-x) := by
  obtain ⟨c, rfl⟩ := crdEquiv.surjective x
  change ebr (σO (δ3 * crd c) / 9) = 1 at h
  change (3 : 𝓞 K) ∣ crd c ∨ Primary (crd c) ∨ Primary (-crd c)
  unfold ebr at h
  rw [two_re_σO_δ3_crd] at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h
  have hk' : ((-(c 1 : ℝ) / 3 : ℝ) : ℂ) = (k : ℂ) := by
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    rw [hk]
    ring
  have hk'' : -(c 1 : ℝ) / 3 = k := by exact_mod_cast hk'
  have hc1 : c 1 = -3 * k := by
    have : (c 1 : ℝ) = -3 * k := by linarith
    exact_mod_cast this
  have hcrd : crd c = (c 0 : 𝓞 K) + 3 * (-(k : 𝓞 K) * ω) := by
    simp only [crd, hc1]
    push_cast
    ring
  rw [hcrd]
  obtain ⟨q, s, hs, hq⟩ : ∃ q s : ℤ, (s = 0 ∨ s = 1 ∨ s = 2) ∧ c 0 = 3 * q + s :=
    ⟨c 0 / 3, c 0 % 3, by omega, by omega⟩
  rw [hq]
  rcases hs with rfl | rfl | rfl
  · left
    exact ⟨q - k * ω, by push_cast; ring⟩
  · right; left
    exact ⟨q - k * ω, by push_cast; ring⟩
  · right; right
    exact ⟨-(q + 1) + k * ω, by push_cast; ring⟩

/-! ### The primary indices -/

/-- **`ρ(x) = 0` for every primary `x` when `ρ(1) = 0`**, by induction on `N(x)`: a primary `x` of norm `1` is
`1` (round 290's `primary_unique`). Otherwise `x` has a prime factor `P`, with `3 ∉ P` since `x ≡ 1 (mod 3)`,
and its primary generator `p` (round 290's `pgen_maximal`; `p = −2` for `P = (2)`). Round 449's `rhoM_cube`
(`p³ ∣ x`), round 454's `rhoM_mul_sq` (`p² ∥ x`) and round 454's `rhoM_mul_prime_eq` (`p ∥ x`) reduce `ρ(x)`
to `0` or to `ρ` at a primary index of smaller norm (round 414's `primary_mul_iff`). -/
theorem rhoM_primary_eq_zero {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (h1 : rhoM 1 r Y hY = 0)
    {x : 𝓞 K} (hx : Primary x) : rhoM x r Y hY = 0 := by
  suffices H : ∀ N : ℕ, ∀ x : 𝓞 K, absNorm (span {x}) = N → Primary x → rhoM x r Y hY = 0 from
    H _ x rfl hx
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x hN hx
    have hx0 : x ≠ 0 := primary_ne_zero hx
    by_cases hu : IsUnit x
    · have : x = 1 := primary_unique hx primary_one
        (by rw [Ideal.span_singleton_eq_top.2 hu, Ideal.span_singleton_one])
      rw [this]
      exact h1
    have hI0 : span {x} ≠ (0 : Ideal (𝓞 K)) := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx0
    have hIu : ¬ IsUnit (span {x} : Ideal (𝓞 K)) := by
      rw [Ideal.isUnit_iff, Ideal.span_singleton_eq_top]; exact hu
    obtain ⟨P, hP⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hI0 hIu
    have hPm : P.IsMaximal := isMaximal_of_factor hP
    have hxP : x ∈ P := Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
      (Ideal.mem_span_singleton_self x)
    have hP3 : (3 : 𝓞 K) ∉ P := by
      intro h3
      obtain ⟨t, ht⟩ := hx
      have h1P : (1 : 𝓞 K) ∈ P := by
        have : (1 : 𝓞 K) = x - 3 * t := by linear_combination -ht
        rw [this]
        exact P.sub_mem hxP (P.mul_mem_right t h3)
      exact hPm.ne_top ((Ideal.eq_top_iff_one P).2 h1P)
    obtain ⟨hpp, hpP⟩ := pgen_maximal P hP3
    set p := pgen P
    have hp0 : p ≠ 0 := by
      intro h
      rw [h, Ideal.span_singleton_eq_bot.2 rfl] at hpP
      rw [← hpP] at hxP
      exact hx0 ((Submodule.mem_bot _).1 hxP)
    have hp : Prime p := (Ideal.span_singleton_prime hp0).1 (hpP ▸ hPm.isPrime)
    have hNp : 1 < absNorm (span {p}) := by
      have h0 : absNorm (span {p}) ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hp0
      have h1 : absNorm (span {p}) ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]; exact hp.not_isUnit
      omega
    have hNmul : ∀ a b : 𝓞 K, absNorm (span {a * b}) = absNorm (span {a}) * absNorm (span {b}) := by
      intro a b
      rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
    have hNpos : ∀ b : 𝓞 K, b ≠ 0 → 0 < absNorm (span {b}) := by
      intro b hb
      rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
    have hpx : p ∣ x := by
      rw [← Ideal.mem_span_singleton, hpP]; exact hxP
    by_cases h3 : p ^ 3 ∣ x
    · obtain ⟨y, rfl⟩ := h3
      have hy : Primary y := (primary_mul_iff (primary_pow hpp 3)).1 hx
      have hy0 : y ≠ 0 := primary_ne_zero hy
      have hlt : absNorm (span {y}) < N := by
        rw [← hN, hNmul, pow_succ, hNmul, sq, hNmul]
        have := hNpos y hy0
        have : 1 < absNorm (span {p}) * absNorm (span {p}) * absNorm (span {p}) := by nlinarith
        nlinarith
      rw [rhoM_cube hr hY hp hpp hy0, ih _ hlt y rfl hy, mul_zero]
    by_cases h2 : p ^ 2 ∣ x
    · obtain ⟨h, rfl⟩ := h2
      have hph : ¬ p ∣ h := by
        rintro ⟨t, rfl⟩
        exact h3 ⟨t, by ring⟩
      rw [show p ^ 2 * h = h * p ^ 2 by ring]
      exact rhoM_mul_sq hr hY hp hpp hph
    · obtain ⟨h, rfl⟩ := hpx
      have hph : ¬ p ∣ h := by
        rintro ⟨t, rfl⟩
        exact h2 ⟨t, by ring⟩
      have hh : Primary h := (primary_mul_iff hpp).1 hx
      have hh0 : h ≠ 0 := primary_ne_zero hh
      have hlt : absNorm (span {h}) < N := by
        rw [← hN, hNmul]
        have := hNpos h hh0
        nlinarith
      rw [show p * h = h * p by ring, rhoM_mul_prime_eq hr hY hp hpp hph, ih _ hlt h rfl hh]
      simp

/-! ### The support when `τ(δ₃) = 0` -/

/-- `τ(δ₃) = ρ(1)/(9√3/2)` (round 436's `tauTh_δ3_mul`). -/
theorem rhoM_one_eq_zero {r : ℝ} {Y : ℝ} {hY : 0 < Y} (h0 : tauTh r Y hY δ3 = 0) : rhoM 1 r Y hY = 0 := by
  have h := tauTh_δ3_mul r Y hY (one_ne_zero (α := 𝓞 K))
  rw [mul_one, h0, eq_comm, div_eq_zero_iff] at h
  exact h.resolve_right nine_sqrt_ne_zero

/-- **If `τ(δ₃) = 0`, `τ` is supported on `3δ₃ℤ[ω]`**: the mask leaves `3 ∣ x` or `±x` primary, and the
primary indices vanish (`rhoM_primary_eq_zero`, with round 456's `rhoM_neg`). -/
theorem dvd_of_tauTh_ne_zero_of_scalar {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y)
    (h0 : tauTh r Y hY δ3 = 0) {m : 𝓞 K} (hm : tauTh r Y hY m ≠ 0) : 3 * δ3 ∣ m := by
  by_cases h : ∃ x, x ≠ 0 ∧ m = δ3 * x
  · obtain ⟨x, hx, rfl⟩ := h
    have hρ : rhoM x r Y hY ≠ 0 := by
      intro hz
      apply hm
      rw [tauTh_δ3_mul r Y hY hx, hz, zero_div]
    have h1 := rhoM_one_eq_zero h0
    rcases mask_of_ebr (ebr_eq_one_of_rhoM_ne_zero hr hY hx hρ) with h3 | hp | hp
    · obtain ⟨y, rfl⟩ := h3
      exact ⟨y, by ring⟩
    · exact absurd (rhoM_primary_eq_zero hr hY h1 hp) hρ
    · have := rhoM_primary_eq_zero hr hY h1 hp
      rw [rhoM_neg hr hY hx] at this
      exact absurd this hρ
  · exact absurd (tauTh_of_not r Y hY h) hm

/-! ### Periodicity under `ℤ[ω]` -/

/-- **Periodicity under `ℤ[ω]`**, for coefficients supported on `3δ₃ℤ[ω]`: `ĕ(σ(3δ₃y)·σ(u)/9)` is
`ĕ(σ(δ₃y)·σ(3u)/9) = 1` (round 428's `ebr_period`). -/
theorem thSer_add_O (c : ℂ) {d : 𝓞 K → ℂ} (hsupp : ∀ m, d m ≠ 0 → 3 * δ3 ∣ m) (z : ℂ) (u : 𝓞 K)
    (v : ℝ) : thSer c d (z + σO u) v = thSer c d z v := by
  simp only [thSer_eq]
  congr 1
  refine tsum_congr fun m => ?_
  by_cases h : d m = 0
  · simp [thTerm, h]
  obtain ⟨y, rfl⟩ := hsupp m h
  simp only [thTerm]
  congr 1
  rw [show σO (3 * δ3 * y) * (z + σO u) / 9 = σO (3 * δ3 * y) * z / 9 + σO (δ3 * y) * σO (3 * u) / 9 by
    simp only [map_mul]; ring, ebr_add, ebr_period, mul_one]

/-! ### The witness -/

/-- **The witness** `W = (1 + 3ω, 3ω²; −3, 1 − 3ω)`. -/
def perW : SL(2, 𝓞 K) := ⟨!![1 + 3 * ω, 3 * ω ^ 2; -3, 1 - 3 * ω], by
  rw [Matrix.det_fin_two_of]; ring⟩

/-- `(1, 0; −3, 1)` in `SL_2(ℤ)`. -/
def lowThree : SL(2, ℤ) := ⟨!![1, 0; -3, 1], by simp [Matrix.det_fin_two]⟩

/-- **`W = T_{−ω}·(1, 0; −3, 1)·T_ω`**, with round 385's translations `slT`. -/
theorem perW_eq : perW = slT (-ω) * (toSL lowThree * slT ω) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, toSL, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [perW, lowThree, slT, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **`W ∈ Γ_1(3)`** (round 382's `mem_Gam3`). -/
theorem perW_mem : perW ∈ Gam3 := by
  rw [mem_Gam3]
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨ω, by simp [perW]⟩
  · exact ⟨ω ^ 2, by simp [perW]⟩
  · exact ⟨-1, by simp [perW]⟩
  · exact ⟨-ω, by simp [perW]⟩

/-! ### `κ(W) ≠ 1` -/

/-- **`N(1 + 3ω) = 7`** (round 308's `absNorm_crd`). -/
theorem absNorm_span_one_add_three_ω : absNorm (span {(1 : 𝓞 K) + 3 * ω}) = 7 := by
  have h := absNorm_crd ![1, 3]
  have hc : crd ![1, 3] = (1 : 𝓞 K) + 3 * ω := by simp [crd]
  rw [hc] at h
  have h7 : (absNorm (span {(1 : 𝓞 K) + 3 * ω}) : ℝ) = 7 := by
    rw [h]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  exact_mod_cast h7

/-- **`(1 + 3ω)` is maximal**: its norm `7` is prime (Mathlib's `Ideal.isPrime_of_irreducible_absNorm`). -/
theorem isMaximal_span_one_add_three_ω : (span {(1 : 𝓞 K) + 3 * ω}).IsMaximal := by
  have hprime : (span {(1 : 𝓞 K) + 3 * ω}).IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by
      rw [absNorm_span_one_add_three_ω]
      have h7 : Nat.Prime 7 := by norm_num
      exact h7)
  refine hprime.isMaximal ?_
  intro h
  have := absNorm_span_one_add_three_ω
  rw [h, Ideal.absNorm_bot] at this
  norm_num at this

/-- **`3 ∉ (1 + 3ω)`**: `7 ∤ N(3) = 9`. -/
theorem three_not_mem_span_one_add_three_ω : (3 : 𝓞 K) ∉ span {(1 : 𝓞 K) + 3 * ω} := by
  intro h
  have hle : span {(3 : 𝓞 K)} ≤ span {(1 : 𝓞 K) + 3 * ω} := (Ideal.span_singleton_le_iff_mem _).2 h
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  have h9 : absNorm (span {(3 : 𝓞 K)}) = 9 := by
    have := absNorm_span_intCast 3
    push_cast at this
    simpa using this
  rw [absNorm_span_one_add_three_ω, h9] at hd
  norm_num at hd

/-- **`κ(W) ≠ 1`**: `κ(W) = ((−3)/(1 + 3ω))₃ = (3/(1 + 3ω))₃` (round 362's `cub_neg`), and by the defining
congruence of round 290's `cubChar` (`cubChar_spec`), with `(N(1 + 3ω) − 1)/3 = 2`, the value `1` would give
`3² ≡ 1 (mod 1 + 3ω)`, that is `7 ∣ N(8) = 64`. -/
theorem kub_perW_ne_one : kub (perW : Matrix (Fin 2) (Fin 2) (𝓞 K)) ≠ 1 := by
  have hPm := isMaximal_span_one_add_three_ω
  have hP3 := three_not_mem_span_one_add_three_ω
  set P := span {(1 : 𝓞 K) + 3 * ω} with hP
  have h30 : (-3 : 𝓞 K) ≠ 0 := by
    intro h
    have := congrArg σO h
    rw [map_neg, map_ofNat, map_zero] at this
    norm_num at this
  have h10 : (perW : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = -3 := rfl
  have h00 : (perW : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0 = 1 + 3 * ω := rfl
  have hk : kub (perW : Matrix (Fin 2) (Fin 2) (𝓞 K)) = σO (cub (-3) P) := by
    unfold kub
    rw [h10, h00, ite_eq_right h30]
  rw [hk]
  intro h1
  have hc : cub (-3) P = 1 := σO_injective (by rw [h1, map_one])
  have hpr : Primary ((1 : 𝓞 K) + 3 * ω) := ⟨ω, by ring⟩
  rw [hP, cub_neg hpr, ← hP, cub_prime, chi3_eq hP3] at hc
  have hne : Ideal.Quotient.mk P 3 ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hs := (cubChar_spec P hP3 (Units.mk0 _ hne)).1
  simp only [Units.val_mk0] at hs
  rw [hc, map_one] at hs
  have hm3 : m3 P = 2 := by
    rw [(absNorm_mod_three hP3).2, hP, absNorm_span_one_add_three_ω]
  rw [hm3] at hs
  have h9 : Ideal.Quotient.mk P (3 ^ 2) = Ideal.Quotient.mk P 1 := by rw [map_pow, map_one, ← hs]
  rw [Ideal.Quotient.eq] at h9
  have h8 : span {(8 : 𝓞 K)} ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    have e : (8 : 𝓞 K) = 3 ^ 2 - 1 := by norm_num
    rw [e]
    exact h9
  have hd := Ideal.absNorm_dvd_absNorm_of_le h8
  have h64 : absNorm (span {(8 : 𝓞 K)}) = 64 := by
    have := absNorm_span_intCast 8
    push_cast at this
    simpa using this
  rw [hP, absNorm_span_one_add_three_ω, h64] at hd
  norm_num at hd

/-! ### `C ≠ 0` -/

/-- **If `τ(δ₃) = 0`, `S = 0`**: `S` is periodic under `ℤ[ω]` (`thSer_add_O`) and invariant under `SL_2(ℤ)`
(round 443's `thS_slAct_toSL`), so `W = T_{−ω}·(1, 0; −3, 1)·T_ω` fixes it (round 385's `slAct_mul` and
`slAct_slT`), while round 437's `isAut_thS` multiplies it by `κ(W) ≠ 1`. -/
theorem thS_eq_zero_of_scalar {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (h0 : tauTh r Y hY δ3 = 0)
    {p : ℂ × ℝ} (hp : p ∈ UHS) : thS r Y hY p = 0 := by
  have hper : ∀ (z : ℂ) (u : 𝓞 K) (v : ℝ), thS r Y hY (z + σO u, v) = thS r Y hY (z, v) :=
    fun z u v => thSer_add_O _ (fun m hm => dvd_of_tauTh_ne_zero_of_scalar hr hY h0 hm) z u v
  have hT : ∀ (u : 𝓞 K) (q : ℂ × ℝ), thS r Y hY (slAct (slT u) q) = thS r Y hY q := by
    intro u q
    rw [slAct_slT]
    exact hper q.1 u q.2
  have hq : slAct (slT ω) p ∈ UHS := by
    rw [slAct_slT]; exact hp
  have hW : thS r Y hY (slAct perW p) = thS r Y hY p := by
    rw [perW_eq, slAct_mul _ _ hp, slAct_mul _ _ hp, hT, thS_slAct_toSL hr hY lowThree hq, hT]
  have hA : thS r Y hY (slAct perW p) = kub (perW : Matrix (Fin 2) (Fin 2) (𝓞 K)) * thS r Y hY p :=
    isAut_thS hr hY perW perW_mem p hp
  rw [hW] at hA
  have h : (kub (perW : Matrix (Fin 2) (Fin 2) (𝓞 K)) - 1) * thS r Y hY p = 0 := by
    rw [sub_mul, one_mul, ← hA, sub_self]
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 kub_perW_ne_one)

/-- **`C = τ(δ₃) ≠ 0`**: otherwise `S = 0` on upper half-space, while its constant term is
`(9√3/2)·Res φ·v^{2/3} ≠ 0` (round 436's `integral_thS`, round 443's `const_theta_ne_zero`). -/
theorem tauTh_δ3_ne_zero {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) : tauTh r Y hY δ3 ≠ 0 := by
  intro h0
  have hI := integral_thS hr hY (v := 1) one_pos
  have hz : ∫ z in fundP3, thS r Y hY (z, 1) = 0 := by
    have : (fun z => thS r Y hY (z, 1)) = fun _ => 0 := by
      funext z
      exact thS_eq_zero_of_scalar hr hY h0 (show (z, (1 : ℝ)) ∈ UHS from (one_pos : (0 : ℝ) < 1))
    rw [this, integral_zero]
  rw [hz] at hI
  exact const_theta_ne_zero one_pos hI.symm

/-- **θ's coefficients at the unit multiples by `ω`**: `τ(δ₃x) ≠ 0` only if `3 ∣ x`, `x` primary or `−x`
primary; so `τ(δ₃x) = 0` for `x = ±ωy` and `x = ±ω²y` with `y` primary, and for `λ ∥ x`. -/
theorem tauTh_mask {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {x : 𝓞 K} (hx : tauTh r Y hY (δ3 * x) ≠ 0) :
    (3 : 𝓞 K) ∣ x ∨ Primary x ∨ Primary (-x) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [mul_zero, tauTh_zero] at hx
    exact hx rfl
  have hρ : rhoM x r Y hY ≠ 0 := by
    intro hz
    apply hx
    rw [tauTh_δ3_mul r Y hY hx0, hz, zero_div]
  exact mask_of_ebr (ebr_eq_one_of_rhoM_ne_zero hr hY hx0 hρ)

/-- **The display's coefficient clause for θ**: `C = τ(δ₃) ≠ 0` (`tauTh_δ3_ne_zero`) with round 456's
`tauTh_display_coef`, in the form of round 361's `KubotaTheta`. -/
theorem exists_display_coef {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ n b : 𝓞 K, Primary n → Primary b → Squarefree (span {n}) →
      (absNorm (span {n * b})).Coprime 6 →
      tauTh r Y hY (δ3 * n * b ^ 3) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})) ∧
      tauTh r Y hY (-(δ3 * n * b ^ 3)) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})) :=
  ⟨tauTh r Y hY δ3, tauTh_δ3_ne_zero hr hY, tauTh_display_coef hr hY⟩

end Eis

end

#print axioms Eis.besselK_third_ne_zero
#print axioms Eis.thS_add_one
#print axioms Eis.ebr_eq_one_of_rhoM_ne_zero
#print axioms Eis.two_re_σO_δ3_crd
#print axioms Eis.mask_of_ebr
#print axioms Eis.rhoM_primary_eq_zero
#print axioms Eis.rhoM_one_eq_zero
#print axioms Eis.dvd_of_tauTh_ne_zero_of_scalar
#print axioms Eis.thSer_add_O
#print axioms Eis.perW_eq
#print axioms Eis.perW_mem
#print axioms Eis.absNorm_span_one_add_three_ω
#print axioms Eis.isMaximal_span_one_add_three_ω
#print axioms Eis.three_not_mem_span_one_add_three_ω
#print axioms Eis.kub_perW_ne_one
#print axioms Eis.thS_eq_zero_of_scalar
#print axioms Eis.tauTh_δ3_ne_zero
#print axioms Eis.tauTh_mask
#print axioms Eis.exists_display_coef
