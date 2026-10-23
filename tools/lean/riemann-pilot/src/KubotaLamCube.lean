import KubotaCoefSupp

/-! # The bound at `λ` and θ's support and size condition (round 459)

S5f-14 of round 360's plan, part 4. Round 458 reduced round 361's support and size condition `ThetaSupp` for
θ's coefficients at `∞` to the bound `|ρ(uλ^j)| ≤ A·3^{j/6}` at `λ = ω − 1`. This round proves the bound,
through two identities for round 428's sums `S_M(c)` at `λ`, and with it `ThetaSupp` for `τ`:

* **`S_{λ³M}(λ³c) = 27·S_M(c)`** for `M = δ₃x`, `3 ∣ c` and `c ≠ 0` (`lam_ne_zero`,
  `isCoprime_lam_of_primary`, `lam_sq_dvd_iff`, `bRow_lam_cube_iff`, `smTerm_lam_cube` and
  **`cuspSm_lam_cube`**): `(λ³c/d)₃ = (c/d)₃` for primary `d`, the phase is unchanged, and the classes modulo
  `3λ³c` are `27` copies of the classes modulo `3c`.
* **`S_{λ³M}(c) = S_M(c)`** for `M = δ₃x` with `λ⁶ ∣ x`, and `c ≠ 0` with `λ⁵ ∤ c` (`smTerm_mul_cube` and
  **`cuspSm_lam_shift`**): for `c = uλ^a·y` with `y` primary, a primary `v ≡ λ` modulo `y` has
  `(c/v³d)₃ = (c/d)₃` and `M·v³d − λ³M·d ∈ 3δ₃c·ℤ[ω]`, so `d ↦ v³d` carries the one sum to the other.
* **The relation among the `D` at `λ`** (`normSq_lam_cube_mul`, `dirD_lam_split` and **`dirD_lam_rec`**):
  `D_{λ⁶M} = (1 + 27^{1−s})·D_{λ³M} − 27^{1−s}·D_M` for `M = δ₃x` with `λ³ ∣ x` and `Re s > 2`.
* **The relation among the `Λ` and the `ρ`** (`norm_σO_δ3_lam_cube`, `dirL_lam_rec`, `rpow_twentyseven`,
  `rpow_three_sqrt_three` and **`rhoM_lam_rec`**): `Λ_{λ⁶x} = (1 + 27^{1−s})·(3√3)^{s−1}·Λ_{λ³x} − Λ_x`, and
  round 450's `sum_rhoM_eq_zero` at `s = 4/3` gives `ρ(λ⁶x) = (4/√3)·ρ(λ³x) − ρ(x)` for `x ≠ 0` with `λ³ ∣ x`.
* **The bound at `λ`** (`norm_le_of_lam_rec` and **`rhoM_lam_bound`**): `e_j = ρ(uλ^{j+3}) − ρ(uλ^j)/√3` has
  `e_{j+3} = √3·e_j`, and `|ρ(uλ^j)| ≤ A·3^{j/6}` follows by induction, uniformly over the six units.
* **Round 361's support and size condition for θ** (**`thetaSupp_tauTh`**): `ThetaSupp K τ` for some `K`, by
  round 458's `thetaSupp_tauTh_of_lam`.
-/

open Ideal NumberField
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Eis

/-! ### Bottom rows and symbols under `c ↦ λ³c` -/

/-- `λ = ω − 1 ≠ 0`, as `N(λ) = 3` (round 458's `absNorm_span_lam`). -/
theorem lam_ne_zero : (ω - 1 : 𝓞 K) ≠ 0 := by
  intro h
  have := absNorm_span_lam
  rw [h, Ideal.span_singleton_eq_bot.2 rfl, Ideal.absNorm_bot] at this
  norm_num at this

/-- `λ` is prime to every primary `d`: `δ₃ = λ·(−ω)` (round 362's `isCoprime_δ3`). -/
theorem isCoprime_lam_of_primary {d : 𝓞 K} (hd : Primary d) : IsCoprime (ω - 1 : 𝓞 K) d := by
  have h := isCoprime_δ3 hd
  have he : δ3 = (ω - 1) * -ω := by unfold δ3; linear_combination ω_sq_add
  rw [he] at h
  exact h.of_mul_left_left

/-- `λ² ∣ c ↔ 3 ∣ c`: `λ² = −3ω` (round 281's `lam_sq`). -/
theorem lam_sq_dvd_iff {c : 𝓞 K} : (ω - 1 : 𝓞 K) ^ 2 ∣ c ↔ (3 : 𝓞 K) ∣ c := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨-ω * t, by rw [lam_sq]; ring⟩
  · rintro ⟨t, rfl⟩
    exact ⟨-ω ^ 2 * t, by linear_combination (ω ^ 2 * t) * lam_sq - (3 * t) * ω_cube⟩

/-- For `3 ∣ c`, `(λ³c, d)` is a bottom row (round 387's `BRow`) if and only if `(c, d)` is. -/
theorem bRow_lam_cube_iff {c d : 𝓞 K} (hc : (3 : 𝓞 K) ∣ c) :
    BRow ((ω - 1) ^ 3 * c, d) ↔ BRow (c, d) := by
  unfold BRow
  constructor
  · rintro ⟨h1, _, h3⟩
    exact ⟨h1.of_mul_left_right, hc, h3⟩
  · rintro ⟨h1, _, h3⟩
    exact ⟨((isCoprime_lam_of_primary h3).pow_left).mul_left h1, dvd_mul_of_dvd_right hc _, h3⟩

/-- **The summand under `c ↦ λ³c`**, for `M = δ₃x`, `3 ∣ c` and `c ≠ 0`: `(λ³c/d)₃ = (c/d)₃` for primary
`d` (round 362's `cub_pow_three`), and the phase is unchanged. -/
theorem smTerm_lam_cube (x c d : 𝓞 K) (hc : (3 : 𝓞 K) ∣ c) (hc0 : c ≠ 0) :
    smTerm (δ3 * ((ω - 1) ^ 3 * x)) ((ω - 1) ^ 3 * c) d = smTerm (δ3 * x) c d := by
  classical
  unfold smTerm
  by_cases h : BRow (c, d)
  · rw [ite_eq_left ((bRow_lam_cube_iff hc).2 h), ite_eq_left h, cub_mul_left, cub_pow_left h.2.2,
      cub_pow_three h.2.2 (isCoprime_lam_of_primary h.2.2), one_mul]
    congr 2
    have hl : σO (ω - 1) ≠ 0 := σO_ne_zero lam_ne_zero
    have hc' : σO c ≠ 0 := σO_ne_zero hc0
    simp only [map_mul, map_pow]
    field_simp
  · rw [ite_eq_right (mt (bRow_lam_cube_iff hc).1 h), ite_eq_right h]

/-- **`S_{λ³M}(λ³c) = 27·S_M(c)`** for `M = δ₃x` and `3 ∣ c`, `c ≠ 0`: the summand is periodic modulo `3c`
(round 451's `smTerm_add`), and round 452's `tsum_quot_dvd_fiber` counts `N(λ³) = 27` copies. -/
theorem cuspSm_lam_cube (x : 𝓞 K) {c : 𝓞 K} (hc : (3 : 𝓞 K) ∣ c) (hc0 : c ≠ 0) :
    cuspSm (δ3 * ((ω - 1) ^ 3 * x)) ((ω - 1) ^ 3 * c) = 27 * cuspSm (δ3 * x) c := by
  have h3 : (3 : 𝓞 K) ≠ 0 := by
    intro h
    have := congrArg σO h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  have hM : (3 : 𝓞 K) * c ≠ 0 := mul_ne_zero h3 hc0
  have hN : (3 : 𝓞 K) * ((ω - 1) ^ 3 * c) ≠ 0 :=
    mul_ne_zero h3 (mul_ne_zero (pow_ne_zero 3 lam_ne_zero) hc0)
  have hMN : 3 * c ∣ 3 * ((ω - 1) ^ 3 * c) := ⟨(ω - 1) ^ 3, by ring⟩
  have hF : ∀ y y', 3 * c ∣ y - y' → smTerm (δ3 * x) c y = smTerm (δ3 * x) c y' := by
    intro y y' hyy
    obtain ⟨t, ht⟩ := hyy
    rw [show y = y' + 3 * c * t by linear_combination ht]
    exact smTerm_add x c y' t hc0
  have hfib := tsum_quot_dvd_fiber hM hN hMN hF
  have hNrel : (absNorm (span {3 * ((ω - 1) ^ 3 * c)}) : ℂ) = 27 * absNorm (span {3 * c}) := by
    rw [show (3 : 𝓞 K) * ((ω - 1) ^ 3 * c) = (ω - 1) ^ 3 * (3 * c) by ring,
      ← Ideal.span_singleton_mul_span_singleton, map_mul, ← Ideal.span_singleton_pow, map_pow,
      absNorm_span_lam]
    push_cast
    ring
  have hN0 : (absNorm (span {3 * c}) : ℂ) ≠ 0 := absNorm_span_ne_zero hM
  rw [cuspSm_eq, cuspSm_eq]
  simp_rw [smTerm_lam_cube x c _ hc hc0]
  rw [hNrel] at hfib
  apply mul_left_cancel₀ hN0
  linear_combination hfib

/-! ### The shift `d ↦ v³d` -/

/-- **The shift `d ↦ v³d`**: for primary `v` prime to `c`, `(c/v³d)₃ = (c/d)₃`, so the summand of `S_M(c)` at
`v³d` is the summand of `S_{λ³M}(c)` at `d` when the phases agree. -/
theorem smTerm_mul_cube {x c v : 𝓞 K} (hv : Primary v) (hvc : IsCoprime v c)
    (hphase : ∀ d : 𝓞 K, ebr (σO (δ3 * x) / 9 * (σO (v ^ 3 * d) / σO c)) =
      ebr (σO (δ3 * ((ω - 1) ^ 3 * x)) / 9 * (σO d / σO c))) (d : 𝓞 K) :
    smTerm (δ3 * x) c (v ^ 3 * d) = smTerm (δ3 * ((ω - 1) ^ 3 * x)) c d := by
  classical
  unfold smTerm
  have hv3 : IsCoprime c (v ^ 3) := hvc.symm.pow_right
  have hrow : BRow (c, v ^ 3 * d) ↔ BRow (c, d) := by
    unfold BRow
    rw [IsCoprime.mul_right_iff, primary_mul_iff (primary_pow hv 3)]
    exact ⟨fun h => ⟨h.1.2, h.2.1, h.2.2⟩, fun h => ⟨⟨hv3, h.1⟩, h.2.1, h.2.2⟩⟩
  by_cases h : BRow (c, d)
  · rw [ite_eq_left (hrow.2 h), ite_eq_left h, hphase d]
    have hd0 : d ≠ 0 := primary_ne_zero h.2.2
    have hv0 : v ≠ 0 := primary_ne_zero hv
    rw [cub_mul_span c (pow_ne_zero 3 hv0) hd0, show v ^ 3 = v * v * v by ring,
      cub_mul_span c (mul_ne_zero hv0 hv0) hv0, cub_mul_span c hv0 hv0]
    have h3 := cub_pow_three hv hvc.symm
    rw [show cub c (span {v}) * cub c (span {v}) * cub c (span {v}) = cub c (span {v}) ^ 3 by ring, h3,
      one_mul]
  · rw [ite_eq_right (mt hrow.1 h), ite_eq_right h]

/-- **`S_{λ³M}(c) = S_M(c)`** for `M = δ₃x` with `λ⁶ ∣ x`, and `c ≠ 0` with `λ⁵ ∤ c`. Write `c = uλ^a·y` with
`y` primary (round 458's `exists_unit_lam_pow_primary`), so `a ≤ 4`. From `3s + ty = 1` (round 370's
`isCoprime_three_of_primary`), `v = ty + 3sλ` is primary with `v ≡ λ` modulo `y`, so
`M·v³d − λ³M·d ∈ 3δ₃c·ℤ[ω]` and the phases differ by a period (round 428's `ebr_period`); `d ↦ v³d` permutes
the classes modulo `3c` (round 452's `tsum_quot_affine'`). -/
theorem cuspSm_lam_shift {x c : 𝓞 K} (hc0 : c ≠ 0) (hc5 : ¬ (ω - 1) ^ 5 ∣ c)
    (hx : (ω - 1) ^ 6 ∣ x) :
    cuspSm (δ3 * ((ω - 1) ^ 3 * x)) c = cuspSm (δ3 * x) c := by
  obtain ⟨u, a, y, hy, hcuy⟩ := exists_unit_lam_pow_primary hc0
  have ha : a ≤ 4 := by
    by_contra h
    push Not at h
    apply hc5
    rw [hcuy]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow _ h) _) _
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨s, t, hst⟩ := isCoprime_three_of_primary hy
  set v : 𝓞 K := t * y + s * 3 * (ω - 1) with hvdef
  have hvp : Primary v := ⟨s * (ω - 2), by rw [hvdef]; linear_combination hst⟩
  have hvl : v - (ω - 1) = y * (t * (2 - ω)) := by rw [hvdef]; linear_combination (ω - 1) * hst
  have hv3 : (3 : 𝓞 K) ∣ v - 1 := hvp
  have hcop3 : IsCoprime v 3 := by
    obtain ⟨k, hk⟩ := hv3
    exact ⟨1, -k, by linear_combination hk⟩
  have hcopl : IsCoprime v (ω - 1) := hcop3.of_isCoprime_of_dvd_right lam_dvd_three
  have hcopy : IsCoprime v y := by
    have h1 : IsCoprime (ω - 1) y := isCoprime_lam_of_primary hy
    have h2 : v = (ω - 1) + y * (t * (2 - ω)) := by linear_combination hvl
    rw [h2]
    exact h1.add_mul_left_left _
  have hcopu : IsCoprime v (u : 𝓞 K) := isCoprime_one_right.of_isCoprime_of_dvd_right
    (by exact ⟨(u⁻¹ : (𝓞 K)ˣ), by simp⟩)
  have hvc : IsCoprime v c := by
    rw [hcuy]
    exact (hcopu.mul_right (hcopl.pow_right)).mul_right hcopy
  have hv3c : IsCoprime (v ^ 3) (3 * c) := (hcop3.mul_right hvc).pow_left
  set W : 𝓞 K := t * (2 - ω) * (v ^ 2 + v * (ω - 1) + (ω - 1) ^ 2) with hWdef
  have hW : v ^ 3 - (ω - 1) ^ 3 = y * W := by
    rw [hWdef]; linear_combination (v ^ 2 + v * (ω - 1) + (ω - 1) ^ 2) * hvl
  have hef : (ω - 1) ^ (4 - a) * (ω - 1) ^ a = (ω - 1 : 𝓞 K) ^ 4 := by
    rw [← pow_add, Nat.sub_add_cancel ha]
  have huu : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K) = 1 := by simp
  have hphase : ∀ d : 𝓞 K, ebr (σO (δ3 * ((ω - 1) ^ 6 * x')) / 9 * (σO (v ^ 3 * d) / σO c)) =
      ebr (σO (δ3 * ((ω - 1) ^ 3 * ((ω - 1) ^ 6 * x'))) / 9 * (σO d / σO c)) := by
    intro d
    set Y : 𝓞 K := -ω * (ω - 1) ^ (4 - a) * x' * d * W * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) with hYdef
    have hO : δ3 * ((ω - 1) ^ 6 * x') * (v ^ 3 * d) =
        δ3 * ((ω - 1) ^ 3 * ((ω - 1) ^ 6 * x')) * d + δ3 * 1 * (3 * Y) * c := by
      rw [hYdef, hcuy]
      linear_combination (δ3 * (ω - 1) ^ 6 * x' * d) * hW +
        (3 * ω * δ3 * x' * d * W * y * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K)) * hef +
        (3 * ω * δ3 * (ω - 1) ^ 4 * x' * d * W * y) * huu +
        (δ3 * (ω - 1) ^ 4 * x' * d * W * y) * lam_sq
    have hc' : σO c ≠ 0 := σO_ne_zero hc0
    have hOC := congrArg σO hO
    simp only [map_mul, map_add, map_one] at hOC
    have key : σO (δ3 * ((ω - 1) ^ 6 * x')) / 9 * (σO (v ^ 3 * d) / σO c) =
        σO (δ3 * ((ω - 1) ^ 3 * ((ω - 1) ^ 6 * x'))) / 9 * (σO d / σO c) +
          σO (δ3 * 1) * σO (3 * Y) / 9 := by
      simp only [map_mul, map_one]
      field_simp
      linear_combination hOC
    rw [key, ebr_add, ebr_period, mul_one]
  have hF : ∀ y y', 3 * c ∣ y - y' →
      smTerm (δ3 * ((ω - 1) ^ 6 * x')) c y = smTerm (δ3 * ((ω - 1) ^ 6 * x')) c y' := by
    intro y y' hyy
    obtain ⟨t, ht⟩ := hyy
    rw [show y = y' + 3 * c * t by linear_combination ht]
    exact smTerm_add _ c y' t hc0
  have h3c : (3 : 𝓞 K) * c ≠ 0 := by
    refine mul_ne_zero ?_ hc0
    intro h
    have := congrArg σO h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  rw [cuspSm_eq, cuspSm_eq, ← tsum_quot_affine' h3c hv3c hF 0]
  refine tsum_congr fun q => ?_
  rw [zero_add]
  exact (smTerm_mul_cube hvp hvc hphase _).symm

/-! ### The relation among the `D` at `λ` -/

/-- `|λ³c|² = 27·|c|²`. -/
theorem normSq_lam_cube_mul (c : 𝓞 K) :
    Complex.normSq (σO ((ω - 1) ^ 3 * c)) = 27 * Complex.normSq (σO c) := by
  rw [map_mul, Complex.normSq_mul, map_pow, map_pow, normSq_σO, absNorm_span_lam]
  norm_num

/-- **The part of `D_{λ³M}` at `λ⁵ ∣ c`**, for `M = δ₃x` and `Re s > 2`: the moduli `c = λ³c₁` with `λ² ∣ c₁`
give `27^{1−s}·D_M(s)` (`cuspSm_lam_cube`; the `c₁` with `λ² ∤ c₁` have `S_M(c₁) = 0`, round 453's
`cuspSm_of_not_dvd`), leaving the sum over `λ⁵ ∤ c`. -/
theorem dirD_lam_split (x : 𝓞 K) {s : ℂ} (hs : 2 < s.re) :
    dirD (δ3 * ((ω - 1) ^ 3 * x)) s = (27 : ℂ) ^ (1 - s) * dirD (δ3 * x) s +
      ∑' c : {c : 𝓞 K // ¬ (ω - 1) ^ 5 ∣ c},
        cuspSm (δ3 * ((ω - 1) ^ 3 * x)) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) := by
  have hs0 : -s ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  set f : 𝓞 K → ℂ := fun c =>
    cuspSm (δ3 * ((ω - 1) ^ 3 * x)) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) with hf
  set g : 𝓞 K → ℂ := fun c => cuspSm (δ3 * x) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) with hg
  have hsum : Summable f := summable_dirD _ hs
  have hD : dirD (δ3 * ((ω - 1) ^ 3 * x)) s = ∑' c, f c := rfl
  have hD0 : dirD (δ3 * x) s = ∑' c, g c := rfl
  rw [hD, hD0, ← hsum.tsum_subtype_add_tsum_subtype_compl {c | (ω - 1) ^ 5 ∣ c}]
  congr 1
  -- the part with `λ⁵ ∣ c`
  have hl3 : (ω - 1 : 𝓞 K) ^ 3 ≠ 0 := pow_ne_zero 3 lam_ne_zero
  let e : {c₁ : 𝓞 K | (ω - 1) ^ 2 ∣ c₁} → {c : 𝓞 K | (ω - 1) ^ 5 ∣ c} := fun c₁ =>
    ⟨(ω - 1) ^ 3 * c₁, by
      obtain ⟨k, hk⟩ := c₁.2
      exact ⟨k, by rw [hk]; ring⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b hab
      exact Subtype.ext (mul_left_cancel₀ hl3 (congrArg Subtype.val hab))
    · intro c
      obtain ⟨k, hk⟩ := c.2
      refine ⟨⟨(ω - 1) ^ 2 * k, ⟨k, rfl⟩⟩, Subtype.ext ?_⟩
      show (ω - 1) ^ 3 * ((ω - 1) ^ 2 * k) = c
      rw [hk]
      ring
  rw [← (Equiv.ofBijective e he).tsum_eq]
  have hterm : ∀ c₁ : {c₁ : 𝓞 K | (ω - 1) ^ 2 ∣ c₁},
      f ((Equiv.ofBijective e he) c₁) = (27 : ℂ) ^ (1 - s) * g c₁ := by
    intro c₁
    show f ((ω - 1) ^ 3 * c₁) = _
    by_cases h0 : (c₁ : 𝓞 K) = 0
    · simp [hf, hg, h0, Complex.zero_cpow hs0]
    have h3 : (3 : 𝓞 K) ∣ c₁ := lam_sq_dvd_iff.1 c₁.2
    simp only [hf, hg]
    rw [cuspSm_lam_cube x h3 h0, normSq_lam_cube_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by norm_num) (Complex.normSq_nonneg _),
      show (1 : ℂ) - s = 1 + -s by ring, Complex.cpow_add _ _ (by norm_num : (27 : ℂ) ≠ 0),
      Complex.cpow_one]
    push_cast
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  congr 1
  refine tsum_subtype_eq_of_support_subset fun c hc => ?_
  show (ω - 1) ^ 2 ∣ c
  by_contra hn
  apply hc
  show cuspSm (δ3 * x) c * _ = 0
  rw [cuspSm_of_not_dvd _ (mt lam_sq_dvd_iff.2 hn), zero_mul]

/-- **The relation among the `D` at `λ`**: `D_{λ⁶M} = (1 + 27^{1−s})·D_{λ³M} − 27^{1−s}·D_M` for `M = δ₃x`
with `λ³ ∣ x` and `Re s > 2`. The sums over `λ⁵ ∤ c` left by `dirD_lam_split` at `λ³x` and at `x` agree by
`cuspSm_lam_shift`. -/
theorem dirD_lam_rec {x : 𝓞 K} (hx : (ω - 1) ^ 3 ∣ x) {s : ℂ} (hs : 2 < s.re) :
    dirD (δ3 * ((ω - 1) ^ 6 * x)) s = (1 + (27 : ℂ) ^ (1 - s)) * dirD (δ3 * ((ω - 1) ^ 3 * x)) s -
      (27 : ℂ) ^ (1 - s) * dirD (δ3 * x) s := by
  have h1 := dirD_lam_split x hs
  have h2 := dirD_lam_split ((ω - 1) ^ 3 * x) hs
  have hL : (∑' c : {c : 𝓞 K // ¬ (ω - 1) ^ 5 ∣ c},
      cuspSm (δ3 * ((ω - 1) ^ 3 * ((ω - 1) ^ 3 * x))) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)) =
      ∑' c : {c : 𝓞 K // ¬ (ω - 1) ^ 5 ∣ c},
        cuspSm (δ3 * ((ω - 1) ^ 3 * x)) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) := by
    refine tsum_congr fun c => ?_
    have hc0 : (c : 𝓞 K) ≠ 0 := fun h => c.2 (h ▸ dvd_zero _)
    have hx6 : (ω - 1) ^ 6 ∣ (ω - 1) ^ 3 * x := by
      obtain ⟨k, rfl⟩ := hx
      exact ⟨k, by ring⟩
    rw [cuspSm_lam_shift hc0 c.2 hx6]
  rw [show (ω - 1 : 𝓞 K) ^ 6 * x = (ω - 1) ^ 3 * ((ω - 1) ^ 3 * x) by ring, h2, hL]
  linear_combination -h1

/-! ### The relation among the `Λ` and the `ρ` at `λ` -/

/-- `|δ₃λ³x/9| = 3√3·|δ₃x/9|`: `|λ| = √3` (round 307's `norm_σO_eq_sqrt`). -/
theorem norm_σO_δ3_lam_cube (x : 𝓞 K) :
    ‖σO (δ3 * ((ω - 1) ^ 3 * x)) / 9‖ = 3 * Real.sqrt 3 * ‖σO (δ3 * x) / 9‖ := by
  have hl : ‖σO (ω - 1 : 𝓞 K)‖ = Real.sqrt 3 := by
    rw [norm_σO_eq_sqrt, absNorm_span_lam]
    norm_num
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [show δ3 * ((ω - 1 : 𝓞 K) ^ 3 * x) = (ω - 1) ^ 3 * (δ3 * x) by ring, map_mul, mul_div_assoc,
    norm_mul, map_pow, norm_pow, hl]
  linear_combination (Real.sqrt 3 * ‖σO (δ3 * x) / 9‖) * h3

/-- **The relation among the `Λ` at `λ`**: `Λ_{λ⁶x} = (1 + 27^{1−s})·(3√3)^{s−1}·Λ_{λ³x} − Λ_x` for `λ³ ∣ x`
and `Re s > 2` (round 453's `dirL_eq` and `dirD_lam_rec`): `|δ₃λ⁶x/9| = 27·|δ₃x/9|` and
`27^{s−1} = ((3√3)^{s−1})²`. -/
theorem dirL_lam_rec {x : 𝓞 K} (hx : (ω - 1) ^ 3 ∣ x) {s : ℂ} (hs : 2 < s.re) :
    dirL ((ω - 1) ^ 6 * x) s =
      (1 + (27 : ℂ) ^ (1 - s)) * ((3 * Real.sqrt 3 : ℝ) : ℂ) ^ (s - 1) * dirL ((ω - 1) ^ 3 * x) s -
        dirL x s := by
  rw [dirL_eq, dirL_eq, dirL_eq, dirD_lam_rec hx hs]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h6 : ‖σO (δ3 * ((ω - 1) ^ 6 * x)) / 9‖ = 27 * ‖σO (δ3 * x) / 9‖ := by
    rw [show (ω - 1 : 𝓞 K) ^ 6 * x = (ω - 1) ^ 3 * ((ω - 1) ^ 3 * x) by ring, norm_σO_δ3_lam_cube,
      norm_σO_δ3_lam_cube]
    linear_combination (9 * ‖σO (δ3 * x) / 9‖) * h3
  rw [h6, norm_σO_δ3_lam_cube]
  set N : ℝ := ‖σO (δ3 * x) / 9‖ with hN
  have hN0 : 0 ≤ 2 * Real.pi * N := by positivity
  have hq0 : (0 : ℝ) ≤ 3 * Real.sqrt 3 := by positivity
  set X : ℂ := ((2 * Real.pi * N : ℝ) : ℂ) ^ (s - 1) with hX
  set T : ℂ := ((3 * Real.sqrt 3 : ℝ) : ℂ) ^ (s - 1) with hT
  have h27 : ((2 * Real.pi * (27 * N) : ℝ) : ℂ) ^ (s - 1) = (27 : ℂ) ^ (s - 1) * X := by
    rw [show (2 * Real.pi * (27 * N) : ℝ) = 27 * (2 * Real.pi * N) by ring, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by norm_num) hN0, Complex.ofReal_ofNat]
  have h33 : ((2 * Real.pi * (3 * Real.sqrt 3 * N) : ℝ) : ℂ) ^ (s - 1) = T * X := by
    rw [show (2 * Real.pi * (3 * Real.sqrt 3 * N) : ℝ) = (3 * Real.sqrt 3) * (2 * Real.pi * N) by ring,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hq0 hN0]
  have hTT : (27 : ℂ) ^ (s - 1) = T * T := by
    rw [hT, ← Complex.mul_cpow_ofReal_nonneg hq0 hq0, ← Complex.ofReal_mul,
      show (3 * Real.sqrt 3 * (3 * Real.sqrt 3) : ℝ) = 27 by linear_combination 9 * h3, Complex.ofReal_ofNat]
  have hinv : (27 : ℂ) ^ (s - 1) * (27 : ℂ) ^ (1 - s) = 1 := by
    rw [← Complex.cpow_add _ _ (by norm_num), show s - 1 + (1 - s) = 0 by ring, Complex.cpow_zero]
  rw [h27, h33]
  linear_combination
    (2 * Real.pi / Complex.Gamma s * X * (1 + (27 : ℂ) ^ (1 - s)) * dirD (δ3 * ((ω - 1) ^ 3 * x)) s) * hTT -
      (2 * Real.pi / Complex.Gamma s * X * dirD (δ3 * x) s) * hinv

/-- `27^{−1/3} = 1/3`. -/
theorem rpow_twentyseven : (27 : ℝ) ^ (-1 / 3 : ℝ) = 1 / 3 := by
  rw [show (27 : ℝ) = (3 : ℝ) ^ ((3 : ℕ) : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
    show ((3 : ℕ) : ℝ) * (-1 / 3) = -1 by norm_num, Real.rpow_neg_one]
  norm_num

/-- `(3√3)^{1/3} = √3`. -/
theorem rpow_three_sqrt_three : (3 * Real.sqrt 3 : ℝ) ^ (1 / 3 : ℝ) = Real.sqrt 3 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [show (3 * Real.sqrt 3 : ℝ) = Real.sqrt 3 ^ 3 by linear_combination (-Real.sqrt 3) * h3,
    show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast (Real.sqrt_nonneg 3) (by norm_num)

/-- **The recurrence at `λ`**: `ρ(λ⁶x) = (4/√3)·ρ(λ³x) − ρ(x)` for `x ≠ 0` with `λ³ ∣ x`. Round 450's
`sum_rhoM_eq_zero` applies to `dirL_lam_rec`, with the entire coefficients `1`, `−(1 + 27^{1−s})(3√3)^{s−1}`
and `1`, and at `s = 4/3` the middle one is `−(1 + 1/3)·√3 = −4/√3`. -/
theorem rhoM_lam_rec {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {x : 𝓞 K} (hx0 : x ≠ 0)
    (hx : (ω - 1) ^ 3 ∣ x) :
    rhoM ((ω - 1) ^ 6 * x) r Y hY =
      ((4 / Real.sqrt 3 : ℝ) : ℂ) * rhoM ((ω - 1) ^ 3 * x) r Y hY - rhoM x r Y hY := by
  have hl : (ω - 1 : 𝓞 K) ≠ 0 := lam_ne_zero
  have hxs : ∀ i, (![(ω - 1) ^ 6 * x, (ω - 1) ^ 3 * x, x] : Fin 3 → 𝓞 K) i ≠ 0 := by
    intro i
    fin_cases i
    · exact mul_ne_zero (pow_ne_zero _ hl) hx0
    · exact mul_ne_zero (pow_ne_zero _ hl) hx0
    · exact hx0
  have hd : Differentiable ℂ fun s : ℂ =>
      -((1 + (27 : ℂ) ^ (1 - s)) * ((3 * Real.sqrt 3 : ℝ) : ℂ) ^ (s - 1)) := by
    refine (((differentiable_const _).add ?_).mul ?_).neg
    · exact ((differentiable_const _).sub differentiable_id).const_cpow (Or.inl (by norm_num))
    · refine (differentiable_id.sub (differentiable_const _)).const_cpow (Or.inl ?_)
      rw [Complex.ofReal_ne_zero]
      positivity
  have h := sum_rhoM_eq_zero hr hY (ι := Fin 3) ![(ω - 1) ^ 6 * x, (ω - 1) ^ 3 * x, x] hxs
    ![fun _ => 1, fun s => -((1 + (27 : ℂ) ^ (1 - s)) * ((3 * Real.sqrt 3 : ℝ) : ℂ) ^ (s - 1)),
      fun _ => 1] (by
        intro i
        fin_cases i
        · exact differentiable_const _
        · exact hd
        · exact differentiable_const _) (by
        intro s hs
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        rw [dirL_lam_rec hx hs]
        ring)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h
  have h27 : (27 : ℂ) ^ (1 - (4 / 3 : ℂ)) = 1 / 3 := by
    rw [show (1 - (4 / 3 : ℂ)) = ((-1 / 3 : ℝ) : ℂ) by push_cast; ring,
      show (27 : ℂ) = ((27 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (by norm_num), rpow_twentyseven]
    push_cast
    ring
  have hT : ((3 * Real.sqrt 3 : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 1) = (Real.sqrt 3 : ℂ) := by
    rw [show ((4 / 3 : ℂ) - 1) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), rpow_three_sqrt_three]
  rw [h27, hT] at h
  have hs3 : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs0 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    positivity
  have hc : ((4 / Real.sqrt 3 : ℝ) : ℂ) = (1 + 1 / 3) * (Real.sqrt 3 : ℂ) := by
    push_cast
    field_simp
    linear_combination (-4 : ℂ) * hs3
  rw [hc]
  linear_combination h

/-! ### The bound at `λ` -/

/-- **The recurrence bound**: a sequence with `ρ(j + 6) = (4/√3)·ρ(j + 3) − ρ(j)` for `j ≥ 3` has
`|ρ(j)| ≤ A·3^{j/6}` for every `j`. The roots of `t² − (4/√3)t + 1` are `√3` and `1/√3`, and
`e_j = ρ(j + 3) − ρ(j)/√3` has `e_{j+3} = √3·e_j`. -/
theorem norm_le_of_lam_rec {ρ : ℕ → ℂ}
    (h : ∀ j, 3 ≤ j → ρ (j + 6) = ((4 / Real.sqrt 3 : ℝ) : ℂ) * ρ (j + 3) - ρ j) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j : ℕ, ‖ρ j‖ ≤ A * (3 : ℝ) ^ ((j : ℝ) / 6) := by
  set q : ℝ := Real.sqrt 3 with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hqq : q * q = 3 := Real.mul_self_sqrt (by norm_num)
  set w : ℝ := (3 : ℝ) ^ ((1 : ℝ) / 6) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos (by norm_num) _
  have hwj : ∀ j : ℕ, w ^ j = (3 : ℝ) ^ ((j : ℝ) / 6) := by
    intro j
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hw3 : w ^ 3 = q := by
    rw [hwj, hq, Real.sqrt_eq_rpow]
    norm_num
  have hqC : (q : ℂ) * ((q⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hq0.ne', Complex.ofReal_one]
  have hc : ((4 / Real.sqrt 3 : ℝ) : ℂ) = (q : ℂ) + ((q⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add]
    congr 1
    rw [← hq]
    field_simp
    linarith
  set e : ℕ → ℂ := fun j => ρ (j + 3) - ((q⁻¹ : ℝ) : ℂ) * ρ j with he
  have hrec : ∀ j, 3 ≤ j → e (j + 3) = (q : ℂ) * e j := by
    intro j hj
    simp only [he]
    rw [show j + 3 + 3 = j + 6 by ring, h j hj, hc]
    linear_combination (ρ j) * hqC
  set E : ℝ := ‖e 3‖ / w ^ 3 + ‖e 4‖ / w ^ 4 + ‖e 5‖ / w ^ 5 with hE
  have hE3 : 0 ≤ ‖e 3‖ / w ^ 3 := by positivity
  have hE4 : 0 ≤ ‖e 4‖ / w ^ 4 := by positivity
  have hE5 : 0 ≤ ‖e 5‖ / w ^ 5 := by positivity
  have hE0 : 0 ≤ E := by positivity
  have he_le : ∀ j, 3 ≤ j → ‖e j‖ ≤ E * w ^ j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hj6 : j < 6
      · have hterm : ‖e j‖ / w ^ j ≤ E := by
          interval_cases j <;> linarith
        exact (div_le_iff₀ (pow_pos hw0 j)).1 hterm
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
        have hi : 3 ≤ i := by omega
        rw [hrec i hi, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0.le, pow_add, hw3]
        have := ih i (by omega) hi
        nlinarith
  set B : ℝ := ∑ j ∈ Finset.range 6, ‖ρ j‖ / w ^ j with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨B + E * q / 2, by positivity, fun j => ?_⟩
  rw [← hwj]
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj6 : j < 6
    · have hterm : ‖ρ j‖ / w ^ j ≤ B :=
        Finset.single_le_sum (f := fun j => ‖ρ j‖ / w ^ j) (fun i _ => by positivity)
          (Finset.mem_range.2 hj6)
      have h1 := (div_le_iff₀ (pow_pos hw0 j)).1 hterm
      have h2 : 0 ≤ E * q / 2 * w ^ j := by positivity
      nlinarith
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
      have hi : 3 ≤ i := by omega
      have hρ : ρ (i + 3) = e i + ((q⁻¹ : ℝ) : ℂ) * ρ i := by
        simp only [he]
        ring
      have h1 := he_le i hi
      have h2 := ih i (by omega)
      have hwi : 0 < w ^ i := pow_pos hw0 i
      have hqinv : q⁻¹ = q / 3 := by
        field_simp
        linarith
      rw [hρ, pow_add, hw3]
      calc ‖e i + ((q⁻¹ : ℝ) : ℂ) * ρ i‖ ≤ ‖e i‖ + q⁻¹ * ‖ρ i‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hq0.le)]
        _ ≤ E * w ^ i + q⁻¹ * ((B + E * q / 2) * w ^ i) := by gcongr
        _ ≤ (B + E * q / 2) * (w ^ i * q) := by
            rw [hqinv]
            have hx : E * w ^ i * (q * q) = E * w ^ i * 3 := by rw [hqq]
            nlinarith [mul_nonneg (mul_nonneg hB0 hq0.le) hwi.le]

/-- **The bound at `λ`**: `|ρ(uλ^j)| ≤ A·3^{j/6}` for every unit `u` and every `j`. `rhoM_lam_rec` at
`x = uλ^j`, `j ≥ 3`, gives `norm_le_of_lam_rec`'s recurrence; `A` is the sum of the constants for the six
units (round 281's `units_mem`). -/
theorem rhoM_lam_bound {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (u : (𝓞 K)ˣ) (j : ℕ),
      ‖rhoM ((u : 𝓞 K) * (ω - 1) ^ j) r Y hY‖ ≤ A * (3 : ℝ) ^ ((j : ℝ) / 6) := by
  classical
  have hu : ∀ u : (𝓞 K)ˣ, ∃ A : ℝ, 0 ≤ A ∧ ∀ j : ℕ,
      ‖rhoM ((u : 𝓞 K) * (ω - 1) ^ j) r Y hY‖ ≤ A * (3 : ℝ) ^ ((j : ℝ) / 6) := by
    intro u
    refine norm_le_of_lam_rec (ρ := fun j => rhoM ((u : 𝓞 K) * (ω - 1) ^ j) r Y hY) fun j hj => ?_
    have hx0 : (u : 𝓞 K) * (ω - 1) ^ j ≠ 0 := mul_ne_zero u.ne_zero (pow_ne_zero _ lam_ne_zero)
    have hx : (ω - 1) ^ 3 ∣ (u : 𝓞 K) * (ω - 1) ^ j := dvd_mul_of_dvd_right (pow_dvd_pow _ hj) _
    have := rhoM_lam_rec hr hY hx0 hx
    rw [show (u : 𝓞 K) * (ω - 1) ^ (j + 6) = (ω - 1) ^ 6 * ((u : 𝓞 K) * (ω - 1) ^ j) by ring,
      show (u : 𝓞 K) * (ω - 1) ^ (j + 3) = (ω - 1) ^ 3 * ((u : 𝓞 K) * (ω - 1) ^ j) by ring]
    exact this
  choose A hA0 hA using hu
  set L : Finset (𝓞 K)ˣ := ([1, -1, ωu, -ωu, ωu ^ 2, -ωu ^ 2] : List (𝓞 K)ˣ).toFinset
  refine ⟨∑ v ∈ L, A v, Finset.sum_nonneg fun v _ => hA0 v, fun u j => ?_⟩
  have hle : A u ≤ ∑ v ∈ L, A v :=
    Finset.single_le_sum (fun v _ => hA0 v) (List.mem_toFinset.2 (units_mem u))
  exact (hA u j).trans (mul_le_mul_of_nonneg_right hle (by positivity))

/-- **θ's coefficients satisfy round 361's support and size condition**: `ThetaSupp K τ` for some `K`, by
`rhoM_lam_bound` and round 458's `thetaSupp_tauTh_of_lam`. -/
theorem thetaSupp_tauTh {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∃ Kc : ℝ, ThetaSupp Kc (tauTh r Y hY) := by
  obtain ⟨A, hA0, hA⟩ := rhoM_lam_bound hr hY
  exact ⟨_, thetaSupp_tauTh_of_lam hr hY hA0 hA⟩

end Eis

end

#print axioms Eis.lam_ne_zero
#print axioms Eis.isCoprime_lam_of_primary
#print axioms Eis.lam_sq_dvd_iff
#print axioms Eis.bRow_lam_cube_iff
#print axioms Eis.smTerm_lam_cube
#print axioms Eis.cuspSm_lam_cube
#print axioms Eis.smTerm_mul_cube
#print axioms Eis.cuspSm_lam_shift
#print axioms Eis.normSq_lam_cube_mul
#print axioms Eis.dirD_lam_split
#print axioms Eis.dirD_lam_rec
#print axioms Eis.norm_σO_δ3_lam_cube
#print axioms Eis.dirL_lam_rec
#print axioms Eis.rpow_twentyseven
#print axioms Eis.rpow_three_sqrt_three
#print axioms Eis.rhoM_lam_rec
#print axioms Eis.norm_le_of_lam_rec
#print axioms Eis.rhoM_lam_bound
#print axioms Eis.thetaSupp_tauTh
