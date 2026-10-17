/-
# Round 526, part 6: a large-values estimate of Huxley's shape over the characters mod `q`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`huxley_large_values`). Let `F(χ, u) = Σ_{n∈S}a_nχ(n)n^{−u}` with `S ⊆ [2, N]` and `G = Σ|a_n|²`, and let
`R` be a set of characters mod `q` with `|F(χ, δ_χ + iγ_χ)| ≥ V > 0` for every `χ ∈ R`, where `0 ≤ δ_χ ≤ η ≤ 1/16` and
`|γ_χ| ≤ T`. If `e^{−n/U} − e^{−2n/U} ≥ c₀ > 0` on `S` (`U ≥ 2`), `X ≥ N(2q²(1 + 2T) + 1)2^J` and `d(n) ≤ τ` for
`n ≤ X`, then `|R| ≤ 2c₀⁻¹GU/V² + c₀⁻²4^{ω(q)}G³A²/V⁶` with
`A = K₀(B + 1)((J + 2)X^η(τL(X)(Uq(2T + 1) + 4Nq(1 + 2T)))^{1/2} + q^{1/4}(2q(1 + 2T))^{3/4}2^{−J/16}ζ(9/8)(qN)^{1/2})`,
`K₀ = 12·KG·CG·EQ(q)q^{2η}(q(1 + 2T))^η`, `B = bkt(q(1 + 2T))` and `L(X)` as in part 5. For `S ⊆ (N/2, N]` with
`U ≍ N` (so `c₀ ≍ 1`) and `X`, `J`, `τ` chosen in terms of `qNT`, this has the shape
`|R| ≪ (GN/V² + G³NqT/V⁶)(qNT)^ε` of Huxley's large-values estimate in the `q`-aspect, for one point per character.

* `pair_reflect`: for one pair, `|H_U(χχ′⁻¹, z_{χχ′})| ≤ (1/2π)Σ_T(∫|J₁| + ∫|J₂|)` at `Λ = U/d_T` (part 3's
  `norm_hTerm_le_reflect` on the lines `c₁ = 3/4 − 2δ_χ`, `c₂ = −1/4 − 2δ_χ`).
* `per_T_bound`: for one set `T` of primes of `q` and one `χ′`, `Σ_{χ≠χ′}(∫|J₁| + ∫|J₂|) ≤ π·W` (part 5's
  `pair_sum_pointwise` at `D = q(1 + 2T)` and `M = q`, integrated against `(1 + v²)⁻¹`, whose integral is `π`).
* `kernel_sum_le`: `Σ_{χ,χ′∈R}|H_U(χχ′⁻¹, z_{χχ′})| ≤ |R|U + 2^{ω(q)}/2·|R|·W`.
* `solve_count`, `huxley_large_values`: part 3's `hm_duality_W` at `σ = 0` with this kernel sum, solved for `|R|`; the
  far tail is absorbed with `|R| ≤ q` (`LinnikDensity.card_chars_le`) and `V ≤ (NG)^{1/2}` (`norm_pv_le_sqrt`).
-/

import LinnikBuckets

open Complex Real Finset MeasureTheory Filter Topology

noncomputable section

namespace LinnikReflect

open DirichletCharacter LinnikPower

variable {q : ℕ}

/-! ### The off-diagonal of the Halász–Montgomery inequality -/

lemma zz_re (δ γ : DirichletCharacter ℂ q → ℝ) (χ χ' : DirichletCharacter ℂ q) :
    (zz δ γ χ χ').re = δ χ + δ χ' := by simp [zz]

/-- **One pair, reflected**: `|H_U(χχ′⁻¹, z_{χχ′})| ≤ (1/2π)Σ_T(∫|J₁| + ∫|J₂|)` at `Λ = U/d_T`. -/
theorem pair_reflect [NeZero q] {χ χ' : DirichletCharacter ℂ q} (hne : χ ≠ χ') {δ γ : DirichletCharacter ℂ q → ℝ}
    {η : ℝ} (hη : η ≤ 1 / 16) (hδ : 0 ≤ δ χ ∧ δ χ ≤ η) (hδ' : 0 ≤ δ χ' ∧ δ χ' ≤ η) {U : ℝ} (hU : 2 ≤ U) :
    ‖∑' n, hTerm (χ * χ'⁻¹) U (zz δ γ χ χ') n‖ ≤ (1 / (2 * π)) * ∑ T ∈ q.primeFactors.powerset,
      ((∫ v : ℝ, ‖J1 δ γ χ χ' (U / ((∏ p ∈ T, p : ℕ) : ℝ)) v‖) +
        ∫ v : ℝ, ‖J2 δ γ χ χ' (U / ((∏ p ∈ T, p : ℕ) : ℝ)) v‖) := by
  have hψ : χ * χ'⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.1 h)
  have hre := zz_re δ γ χ χ'
  exact norm_hTerm_le_reflect hψ hU (by rw [hre]; linarith [hδ.1, hδ'.1]) (by rw [hre]; linarith [hδ.2, hδ'.2])
    (c₁ := 3 / 4 - 2 * δ χ) (c₂ := -1 / 4 - 2 * δ χ) (by linarith [hδ.1]) (by linarith [hδ.2])
    (by linarith [hδ.2]) (by linarith [hδ.1]) (by rw [hre]; linarith [hδ.2, hδ'.1])
    (by rw [hre]; linarith [hδ.1, hδ'.2]) (by rw [hre]; linarith [hδ.1, hδ'.2])
    (fun T => Zt (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (bkt (pairCond χ χ' γ)))

/-- The two integrands of a pair are integrable. -/
theorem pair_integrable [NeZero q] {χ χ' : DirichletCharacter ℂ q} (hne : χ ≠ χ') {δ γ : DirichletCharacter ℂ q → ℝ}
    {η : ℝ} (hη : η ≤ 1 / 16) (hδ : 0 ≤ δ χ ∧ δ χ ≤ η) (hδ' : 0 ≤ δ χ' ∧ δ χ' ≤ η) {Λ : ℝ} (hΛ : 0 < Λ) :
    (Integrable fun v : ℝ => ‖J1 δ γ χ χ' Λ v‖) ∧ (Integrable fun v : ℝ => ‖J2 δ γ χ χ' Λ v‖) := by
  have hψ : χ * χ'⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.1 h)
  have hre := zz_re δ γ χ χ'
  obtain ⟨h1, h2⟩ := integrable_reflect hψ hΛ (z := zz δ γ χ χ') (c₁ := 3 / 4 - 2 * δ χ) (c₂ := -1 / 4 - 2 * δ χ)
    (by linarith [hδ.1]) (by linarith [hδ.2]) (by linarith [hδ.2]) (by linarith [hδ.1])
    (by rw [hre]; linarith [hδ.2, hδ'.1]) (by rw [hre]; linarith [hδ.1, hδ'.2]) (by rw [hre]; linarith [hδ.1, hδ'.2])
    (Zt Λ (bkt (pairCond χ χ' γ))) (q := q)
  exact ⟨h1.norm, h2.norm⟩

/-- `(1 + |v|)^{−4} ≤ (1 + v²)^{−1}`. -/
lemma inv_pow_four_le (v : ℝ) : ((1 + |v|) ^ 4)⁻¹ ≤ (1 + v ^ 2)⁻¹ := by
  apply inv_anti₀ (by positivity)
  have h1 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
  have h2 : 1 + v ^ 2 ≤ (1 + |v|) ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
  calc 1 + v ^ 2 ≤ (1 + |v|) ^ 2 := h2
    _ ≤ (1 + |v|) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)

/-- `d_T ≤ q` for `T` a set of primes of `q`. -/
lemma prod_le_of_mem_powerset {q : ℕ} [NeZero q] {T : Finset ℕ} (hT : T ∈ q.primeFactors.powerset) :
    (∏ p ∈ T, p : ℕ) ≤ q := by
  have h1 : (∏ p ∈ T, p : ℕ) ∣ ∏ p ∈ q.primeFactors, p :=
    Finset.prod_dvd_prod_of_subset T q.primeFactors (fun p => p) (mem_powerset.1 hT)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (h1.trans (Nat.prod_primeFactors_dvd q))

lemma pairCond_le [NeZero q] (χ χ' : DirichletCharacter ℂ q) {γ : DirichletCharacter ℂ q → ℝ} {T : ℝ}
    (hχ : |γ χ| ≤ T) (hχ' : |γ χ'| ≤ T) : pairCond χ χ' γ ≤ q * (1 + 2 * T) := by
  unfold pairCond
  have hf : (((χ * χ'⁻¹).conductor : ℕ) : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (χ * χ'⁻¹).conductor_dvd_level
  have hg : |γ χ - γ χ'| ≤ 2 * T := by
    have := abs_sub (γ χ) (γ χ')
    linarith
  have h0 : (0 : ℝ) ≤ ((χ * χ'⁻¹).conductor : ℕ) := Nat.cast_nonneg _
  have h1 : 0 ≤ 1 + |γ χ - γ χ'| := by positivity
  calc (((χ * χ'⁻¹).conductor : ℕ) : ℝ) * (1 + |γ χ - γ χ'|) ≤ q * (1 + 2 * T) := by gcongr

/-- **One subset `T` of the primes of `q` and one second character**:
`Σ_{χ≠χ′}(∫|J₁| + ∫|J₂|) ≤ π·W(U)` at `Λ = U/d_T` (`pair_sum_pointwise`, integrated against `(1 + v²)^{−1}`). -/
theorem per_T_bound [NeZero q] {R : Finset (DirichletCharacter ℂ q)} {δ γ : DirichletCharacter ℂ q → ℝ}
    {η : ℝ} (hη : η ≤ 1 / 16) (hδ : ∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ η) {T : ℝ} (hT : 0 ≤ T)
    (hγ : ∀ χ ∈ R, |γ χ| ≤ T) {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Icc 2 N) (a : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ χ ∈ R, V ≤ ‖pv S a χ ((δ χ : ℂ) + γ χ * I)‖) {χ' : DirichletCharacter ℂ q} (hχ' : χ' ∈ R)
    {U : ℝ} (hU : 2 ≤ U) {Tq : Finset ℕ} (hTq : Tq ∈ q.primeFactors.powerset) (J : ℕ) {X : ℕ} (hX : 1 ≤ X)
    (hN : 1 ≤ N) (hXD : (N : ℝ) * (2 * (q * (1 + 2 * T)) * q + 1) * 2 ^ J ≤ X) {τ : ℝ}
    (hτ : ∀ n, n ≤ X → (n.divisors.card : ℝ) ≤ τ) :
    ∑ χ ∈ R.erase χ', ((∫ v : ℝ, ‖J1 δ γ χ χ' (U / ((∏ p ∈ Tq, p : ℕ) : ℝ)) v‖) +
        ∫ v : ℝ, ‖J2 δ γ χ χ' (U / ((∏ p ∈ Tq, p : ℕ) : ℝ)) v‖) ≤
      π * ((12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η) *
        (bkt (q * (1 + 2 * T)) + 1) *
        ((J + 2) * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt (R.card * τ * (∑ n ∈ S, ‖a n‖ ^ 2) * LSmax X *
          (U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T))))) +
        (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * R.card *
          ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98)) := by
  classical
  set d : ℕ := ∏ p ∈ Tq, p with hd
  have hd0 : 0 < d := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (mem_powerset.1 hTq hp)).pos
  have hdq : d ≤ q := prod_le_of_mem_powerset hTq
  set Λ : ℝ := U / (d : ℝ) with hΛ
  have hΛ0 : 0 < Λ := div_pos (by linarith) (by exact_mod_cast hd0)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hΛM : Λ⁻¹ ≤ q := by
    rw [hΛ, inv_div, div_le_iff₀ (by linarith)]
    have : (d : ℝ) ≤ q := by exact_mod_cast hdq
    nlinarith
  have hΛU : Λ ≤ U := by
    rw [hΛ, div_le_iff₀ (by exact_mod_cast hd0)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    nlinarith
  set Dq : ℝ := q * (1 + 2 * T) with hDq
  have hD1 : 1 ≤ Dq := by rw [hDq]; nlinarith
  have hD : ∀ χ ∈ R, pairCond χ χ' γ ≤ Dq := fun χ hχ => pairCond_le χ χ' (hγ χ hχ) (hγ χ' hχ')
  set K₀ := 12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * Dq ^ η with hK₀
  have hK₀0 : 0 ≤ K₀ := by
    have := InghamDensity.KG_pos; have := CG_pos; have := EQ_pos q; rw [hK₀]; positivity
  have hτ0 : 0 ≤ τ := (Nat.cast_nonneg _).trans (hτ 1 hX)
  set G := ∑ n ∈ S, ‖a n‖ ^ 2 with hG
  have hG0 : 0 ≤ G := sum_nonneg fun _ _ => by positivity
  set WΛ := K₀ * (bkt Dq + 1) * ((J + 2) * ((X : ℝ) ^ η * V⁻¹ *
      Real.sqrt (R.card * τ * G * LSmax X * (Λ * q * (2 * T + 1) + 4 * N * Dq))) +
      (q : ℝ) ^ (1 / 4 : ℝ) * (2 * Dq) ^ (3 / 4 : ℝ) * R.card * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98)
    with hWΛ
  have hWΛ0 : 0 ≤ WΛ := by have := zeta98_nonneg; rw [hWΛ]; positivity
  -- integrability
  have hint : ∀ χ ∈ R.erase χ', (Integrable fun v : ℝ => ‖J1 δ γ χ χ' Λ v‖) ∧
      (Integrable fun v : ℝ => ‖J2 δ γ χ χ' Λ v‖) := fun χ hχ =>
    pair_integrable (mem_erase.1 hχ).1 hη (hδ χ (mem_erase.1 hχ).2) (hδ χ' hχ') hΛ0
  have hsum : ∑ χ ∈ R.erase χ', ((∫ v : ℝ, ‖J1 δ γ χ χ' Λ v‖) + ∫ v : ℝ, ‖J2 δ γ χ χ' Λ v‖) =
      ∫ v : ℝ, ∑ χ ∈ R.erase χ', (‖J1 δ γ χ χ' Λ v‖ + ‖J2 δ γ χ χ' Λ v‖) := by
    have h := integral_finsetSum (μ := volume) (R.erase χ')
      (f := fun χ v => ‖J1 δ γ χ χ' Λ v‖ + ‖J2 δ γ χ χ' Λ v‖) (fun χ hχ => (hint χ hχ).1.add (hint χ hχ).2)
    rw [h]
    exact sum_congr rfl fun χ hχ => (integral_add (hint χ hχ).1 (hint χ hχ).2).symm
  have hpt : ∀ v : ℝ, ∑ χ ∈ R.erase χ', (‖J1 δ γ χ χ' Λ v‖ + ‖J2 δ γ χ χ' Λ v‖) ≤ (1 + v ^ 2)⁻¹ * WΛ := by
    intro v
    have h := pair_sum_pointwise hη hδ hT hγ hS a hV hbig hχ' hΛ0 hq1 hΛM hD1 hD v J hX hN hXD hτ
    refine h.trans ?_
    rw [hWΛ, hK₀]
    have h4 := inv_pow_four_le v
    have : 0 ≤ (12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * Dq ^ η) * (bkt Dq + 1) *
        ((J + 2) * ((X : ℝ) ^ η * V⁻¹ *
          Real.sqrt (R.card * τ * G * LSmax X * (Λ * q * (2 * T + 1) + 4 * N * Dq))) +
        (q : ℝ) ^ (1 / 4 : ℝ) * (2 * Dq) ^ (3 / 4 : ℝ) * R.card * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
          zeta98) := by rw [← hK₀, ← hWΛ]; exact hWΛ0
    calc ((1 + |v|) ^ 4)⁻¹ * (12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * Dq ^ η) * (bkt Dq + 1) *
          ((J + 2) * ((X : ℝ) ^ η * V⁻¹ *
            Real.sqrt (R.card * τ * G * LSmax X * (Λ * q * (2 * T + 1) + 4 * N * Dq))) +
          (q : ℝ) ^ (1 / 4 : ℝ) * (2 * Dq) ^ (3 / 4 : ℝ) * R.card * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98)
        = ((1 + |v|) ^ 4)⁻¹ * ((12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * Dq ^ η) * (bkt Dq + 1) *
          ((J + 2) * ((X : ℝ) ^ η * V⁻¹ *
            Real.sqrt (R.card * τ * G * LSmax X * (Λ * q * (2 * T + 1) + 4 * N * Dq))) +
          (q : ℝ) ^ (1 / 4 : ℝ) * (2 * Dq) ^ (3 / 4 : ℝ) * R.card * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
            zeta98)) := by ring
      _ ≤ (1 + v ^ 2)⁻¹ * ((12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * Dq ^ η) * (bkt Dq + 1) *
          ((J + 2) * ((X : ℝ) ^ η * V⁻¹ *
            Real.sqrt (R.card * τ * G * LSmax X * (Λ * q * (2 * T + 1) + 4 * N * Dq))) +
          (q : ℝ) ^ (1 / 4 : ℝ) * (2 * Dq) ^ (3 / 4 : ℝ) * R.card * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
            zeta98)) := mul_le_mul_of_nonneg_right h4 this
  have hmono : (∫ v : ℝ, ∑ χ ∈ R.erase χ', (‖J1 δ γ χ χ' Λ v‖ + ‖J2 δ γ χ χ' Λ v‖)) ≤
      ∫ v : ℝ, (1 + v ^ 2)⁻¹ * WΛ :=
    integral_mono_of_nonneg (Eventually.of_forall fun v => sum_nonneg fun _ _ => by positivity)
      (integrable_inv_one_add_sq.mul_const WΛ) (Eventually.of_forall hpt)
  rw [integral_mul_const, integral_univ_inv_one_add_sq] at hmono
  rw [hsum]
  refine hmono.trans (mul_le_mul_of_nonneg_left ?_ pi_pos.le)
  -- `Λ ≤ U` inside the square root
  rw [hWΛ, hK₀]
  have hs : Real.sqrt (R.card * τ * G * LSmax X * (Λ * q * (2 * T + 1) + 4 * N * Dq)) ≤
      Real.sqrt (R.card * τ * G * LSmax X * (U * q * (2 * T + 1) + 4 * N * Dq)) := by
    apply Real.sqrt_le_sqrt
    have := LSmax_nonneg X
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have : Λ * q * (2 * T + 1) ≤ U * q * (2 * T + 1) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΛU hq0) (by linarith)
    gcongr
  have := zeta98_nonneg
  gcongr

/-! ### The off-diagonal total and Huxley's large-values estimate over the characters mod `q` -/

lemma sum_erase_comm {α : Type*} [DecidableEq α] (s : Finset α) (f : α → α → ℝ) :
    ∑ x ∈ s, ∑ y ∈ s.erase x, f x y = ∑ y ∈ s, ∑ x ∈ s.erase y, f x y := by
  simp_rw [← filter_ne' s, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
  simp only [ne_comm]

/-- The off-diagonal weight `W`: the bracket of `per_T_bound` at `Λ = U`. -/
def Wtot (q : ℕ) (Rc τ G η T U N V : ℝ) (X J : ℕ) : ℝ :=
  (12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η) * (bkt (q * (1 + 2 * T)) + 1) *
    ((J + 2) * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt (Rc * τ * G * LSmax X *
      (U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T))))) +
    (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * Rc * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98)

/-- **The kernel sum of the Halász–Montgomery inequality**: the diagonal gives `|R|U`, each off-diagonal pair is
reflected (`pair_reflect`), and the pairs are summed in buckets and integrated (`per_T_bound`):
`Σ_{χ,χ′}|H_U(χχ′⁻¹, z_{χχ′})| ≤ |R|U + 2^{ω(q)}/2·|R|·W`. -/
theorem kernel_sum_le [NeZero q] {R : Finset (DirichletCharacter ℂ q)} {δ γ : DirichletCharacter ℂ q → ℝ}
    {η : ℝ} (hη : η ≤ 1 / 16) (hδ : ∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ η) {T : ℝ} (hT : 0 ≤ T)
    (hγ : ∀ χ ∈ R, |γ χ| ≤ T) {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Icc 2 N) (a : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ χ ∈ R, V ≤ ‖pv S a χ ((δ χ : ℂ) + γ χ * I)‖) {U : ℝ} (hU : 2 ≤ U) (J : ℕ) {X : ℕ} (hX : 1 ≤ X)
    (hN : 1 ≤ N) (hXD : (N : ℝ) * (2 * (q * (1 + 2 * T)) * q + 1) * 2 ^ J ≤ X) {τ : ℝ}
    (hτ : ∀ n, n ≤ X → (n.divisors.card : ℝ) ≤ τ) :
    ∑ χ ∈ R, ∑ χ' ∈ R, ‖∑' n, hTerm (χ * χ'⁻¹) U (zz δ γ χ χ') n‖ ≤
      R.card * U + (q.primeFactors.powerset.card : ℝ) / 2 *
        (R.card * Wtot q R.card τ (∑ n ∈ S, ‖a n‖ ^ 2) η T U N V X J) := by
  classical
  set W := Wtot q R.card τ (∑ n ∈ S, ‖a n‖ ^ 2) η T U N V X J with hW
  set P := q.primeFactors.powerset with hP
  set I : DirichletCharacter ℂ q → DirichletCharacter ℂ q → Finset ℕ → ℝ := fun χ χ' Tq =>
    (∫ v : ℝ, ‖J1 δ γ χ χ' (U / ((∏ p ∈ Tq, p : ℕ) : ℝ)) v‖) +
      ∫ v : ℝ, ‖J2 δ γ χ χ' (U / ((∏ p ∈ Tq, p : ℕ) : ℝ)) v‖ with hI
  have hrow : ∀ χ ∈ R, ∑ χ' ∈ R, ‖∑' n, hTerm (χ * χ'⁻¹) U (zz δ γ χ χ') n‖ ≤
      U + ∑ χ' ∈ R.erase χ, (1 / (2 * π)) * ∑ Tq ∈ P, I χ χ' Tq := by
    intro χ hχ
    rw [← add_sum_erase R _ hχ]
    refine add_le_add ?_ (sum_le_sum fun χ' hχ' => ?_)
    · exact norm_tsum_hTerm_le _ (by linarith) (by rw [zz_re]; linarith [(hδ χ hχ).1])
    · exact pair_reflect (mem_erase.1 hχ').1.symm hη (hδ χ hχ) (hδ χ' (mem_erase.1 hχ').2) hU
  have hcol : ∀ χ' ∈ R, ∀ Tq ∈ P, ∑ χ ∈ R.erase χ', I χ χ' Tq ≤ π * W := fun χ' hχ' Tq hTq =>
    per_T_bound hη hδ hT hγ hS a hV hbig hχ' hU hTq J hX hN hXD hτ
  calc ∑ χ ∈ R, ∑ χ' ∈ R, ‖∑' n, hTerm (χ * χ'⁻¹) U (zz δ γ χ χ') n‖
      ≤ ∑ χ ∈ R, (U + ∑ χ' ∈ R.erase χ, (1 / (2 * π)) * ∑ Tq ∈ P, I χ χ' Tq) := sum_le_sum hrow
    _ = R.card * U + (1 / (2 * π)) * ∑ χ' ∈ R, ∑ Tq ∈ P, ∑ χ ∈ R.erase χ', I χ χ' Tq := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
        congr 1
        rw [sum_erase_comm R (fun χ χ' => (1 / (2 * π)) * ∑ Tq ∈ P, I χ χ' Tq), mul_sum]
        refine sum_congr rfl fun χ' _ => ?_
        rw [← mul_sum, sum_comm]
    _ ≤ R.card * U + (1 / (2 * π)) * ∑ _χ' ∈ R, ∑ _Tq ∈ P, π * W := by
        gcongr with χ' hχ' Tq hTq
        exact hcol χ' hχ' Tq hTq
    _ = R.card * U + (P.card : ℝ) / 2 * (R.card * W) := by
        rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
        field_simp

/-! ### Huxley's large-values estimate over the characters mod `q` -/

/-- `s²V² ≤ α + βs` gives `s² ≤ 2α/V² + β²/V⁴`. -/
lemma quad_solve {s V α β : ℝ} (hV : 0 < V) (h : s ^ 2 * V ^ 2 ≤ α + β * s) :
    s ^ 2 ≤ 2 * α / V ^ 2 + β ^ 2 / V ^ 4 := by
  have hV2 : 0 < V ^ 2 := by positivity
  have hamgm : β * s ≤ V ^ 2 * s ^ 2 / 2 + β ^ 2 / (2 * V ^ 2) := by
    have h0 : 0 ≤ (V ^ 2 * s - β) ^ 2 := sq_nonneg _
    have e : V ^ 2 * s ^ 2 / 2 + β ^ 2 / (2 * V ^ 2) - β * s = (V ^ 2 * s - β) ^ 2 / (2 * V ^ 2) := by
      field_simp; ring
    have : 0 ≤ V ^ 2 * s ^ 2 / 2 + β ^ 2 / (2 * V ^ 2) - β * s := by rw [e]; positivity
    linarith
  have h3 : s ^ 2 * V ^ 2 ≤ 2 * α + β ^ 2 / V ^ 2 := by
    have e : β ^ 2 / (2 * V ^ 2) = (β ^ 2 / V ^ 2) / 2 := by field_simp
    nlinarith [h, hamgm, e]
  have e : 2 * α / V ^ 2 + β ^ 2 / V ^ 4 = (2 * α + β ^ 2 / V ^ 2) / V ^ 2 := by
    field_simp
  rw [e, le_div_iff₀ hV2]
  exact h3

/-- The far tail against the large values: `A₂r ≤ A₂√(QN)V⁻¹·√r√G` when `r ≤ Q` and `V ≤ √(NG)`. -/
lemma far_absorb {r V G A₂ Q N : ℝ} (hr : 0 < r) (hV : 0 < V) (hA₂ : 0 ≤ A₂) (hrQ : r ≤ Q)
    (hVG : V ≤ Real.sqrt (N * G)) (hN : 0 ≤ N) :
    A₂ * r ≤ A₂ * Real.sqrt (Q * N) * V⁻¹ * (Real.sqrt r * Real.sqrt G) := by
  have hQ : 0 < Q := hr.trans_le hrQ
  have hs0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have h1 : Real.sqrt r ≤ Real.sqrt Q := Real.sqrt_le_sqrt hrQ
  have h2 : 1 ≤ Real.sqrt (N * G) * V⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hV, one_mul]; exact hVG
  have e : Real.sqrt (Q * N) * V⁻¹ * (Real.sqrt r * Real.sqrt G) =
      Real.sqrt r * (Real.sqrt Q * (Real.sqrt (N * G) * V⁻¹)) := by
    rw [Real.sqrt_mul hQ.le, Real.sqrt_mul hN]; ring
  have hr2 : r = Real.sqrt r * Real.sqrt r := (Real.mul_self_sqrt hr.le).symm
  rw [mul_assoc A₂, mul_assoc A₂, e]
  apply mul_le_mul_of_nonneg_left _ hA₂
  conv_lhs => rw [hr2]
  apply mul_le_mul_of_nonneg_left _ hs0
  calc Real.sqrt r ≤ Real.sqrt Q := h1
    _ = Real.sqrt Q * 1 := (mul_one _).symm
    _ ≤ Real.sqrt Q * (Real.sqrt (N * G) * V⁻¹) := by gcongr

/-- **Solving the Halász–Montgomery inequality for the count**: from
`r²V² ≤ c⁻¹G(rU + (P/2)r(A₁V⁻¹√(rG) + A₂r))`, `r ≤ Q` and `V ≤ √(NG)`,
`r ≤ 2c⁻¹GU/V² + c⁻²P²G³(A₁ + A₂√(QN))²/V⁶`. -/
lemma solve_count {r V G U c P A₁ A₂ Q N : ℝ} (hr : 0 < r) (hV : 0 < V) (hG : 0 ≤ G) (hc : 0 < c) (hP : 0 ≤ P)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hrQ : r ≤ Q) (hVG : V ≤ Real.sqrt (N * G)) (hN : 0 ≤ N)
    (h : r ^ 2 * V ^ 2 ≤ c⁻¹ * G * (r * U + P / 2 * (r * (A₁ * V⁻¹ * Real.sqrt (r * G) + A₂ * r)))) :
    r ≤ 2 * c⁻¹ * G * U / V ^ 2 + (c⁻¹) ^ 2 * P ^ 2 * G ^ 3 * (A₁ + A₂ * Real.sqrt (Q * N)) ^ 2 / V ^ 6 := by
  set s := Real.sqrt r with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg r
  have hss : s ^ 2 = r := Real.sq_sqrt hr.le
  set g := Real.sqrt G with hg
  have hg0 : 0 ≤ g := Real.sqrt_nonneg G
  have hgg : g ^ 2 = G := Real.sq_sqrt hG
  set A := A₁ + A₂ * Real.sqrt (Q * N) with hA
  have hA0 : 0 ≤ A := by positivity
  have hfar := far_absorb (G := G) hr hV hA₂ hrQ hVG hN
  have hbr : A₁ * V⁻¹ * Real.sqrt (r * G) + A₂ * r ≤ A * V⁻¹ * (s * g) := by
    rw [Real.sqrt_mul hr.le, hA]
    have : A₂ * Real.sqrt (Q * N) * V⁻¹ * (s * g) = A₂ * Real.sqrt (Q * N) * V⁻¹ * (Real.sqrt r * Real.sqrt G) := rfl
    nlinarith [hfar]
  have hc0 : 0 ≤ c⁻¹ * G := by positivity
  have h' : r * (r * V ^ 2) ≤ r * (c⁻¹ * G * U + (c⁻¹ * (P / 2) * A * V⁻¹ * G * g) * s) := by
    have h1 : r ^ 2 * V ^ 2 ≤ c⁻¹ * G * (r * U + P / 2 * (r * (A * V⁻¹ * (s * g)))) := by
      refine h.trans ?_
      gcongr
    calc r * (r * V ^ 2) = r ^ 2 * V ^ 2 := by ring
      _ ≤ c⁻¹ * G * (r * U + P / 2 * (r * (A * V⁻¹ * (s * g)))) := h1
      _ = r * (c⁻¹ * G * U + (c⁻¹ * (P / 2) * A * V⁻¹ * G * g) * s) := by ring
  have h2 : r * V ^ 2 ≤ c⁻¹ * G * U + (c⁻¹ * (P / 2) * A * V⁻¹ * G * g) * s := le_of_mul_le_mul_left h' hr
  rw [← hss] at h2
  have h3 := quad_solve hV h2
  rw [hss] at h3
  refine h3.trans ?_
  have hβ : (c⁻¹ * (P / 2) * A * V⁻¹ * G * g) ^ 2 / V ^ 4 ≤ (c⁻¹) ^ 2 * P ^ 2 * G ^ 3 * A ^ 2 / V ^ 6 := by
    have e : (c⁻¹ * (P / 2) * A * V⁻¹ * G * g) ^ 2 / V ^ 4 =
        ((c⁻¹) ^ 2 * P ^ 2 * G ^ 3 * A ^ 2 / V ^ 6) / 4 := by
      rw [show (c⁻¹ * (P / 2) * A * V⁻¹ * G * g) ^ 2 = (c⁻¹) ^ 2 * P ^ 2 * G ^ 2 * g ^ 2 * A ^ 2 * (V⁻¹) ^ 2 / 4 by ring,
        hgg]
      field_simp
    rw [e]
    have : 0 ≤ (c⁻¹) ^ 2 * P ^ 2 * G ^ 3 * A ^ 2 / V ^ 6 := by positivity
    linarith
  have e2 : 2 * (c⁻¹ * G * U) / V ^ 2 = 2 * c⁻¹ * G * U / V ^ 2 := by ring
  linarith

/-- A Dirichlet polynomial on `[2, N]` at a point with `Re u ≥ 0` is at most `(NΣ|a_n|²)^{1/2}`. -/
lemma norm_pv_le_sqrt {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Icc 2 N) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) {u : ℂ}
    (hu : 0 ≤ u.re) : ‖pv S a χ u‖ ≤ Real.sqrt (N * ∑ n ∈ S, ‖a n‖ ^ 2) := by
  have h1 : ‖pv S a χ u‖ ≤ ∑ n ∈ S, ‖a n‖ := by
    unfold pv
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
    have hn1 : 1 ≤ n := by have := (mem_Icc.1 (hS hn)).1; omega
    rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    have h2 := DirichletCharacter.norm_le_one χ n
    have h3 : (n : ℝ) ^ (-u).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by simp; linarith)
    calc ‖a n‖ * ‖χ n‖ * (n : ℝ) ^ (-u).re ≤ ‖a n‖ * 1 * 1 := by gcongr
      _ = ‖a n‖ := by ring
  have hcard : (S.card : ℝ) ≤ N := by
    have := card_le_card hS
    rw [Nat.card_Icc] at this
    exact_mod_cast this.trans (by omega)
  have h2 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun n => ‖a n‖)
  refine h1.trans ((Real.le_sqrt (sum_nonneg fun _ _ => norm_nonneg _) (by positivity)).2 (h2.trans ?_))
  exact mul_le_mul_of_nonneg_right hcard (sum_nonneg fun _ _ => by positivity)

/-- **Huxley's large-values estimate over the characters mod `q`** (one point per character): if `|F(χ)| ≥ V > 0`
at `u_χ = δ_χ + iγ_χ` for every `χ ∈ R`, with `0 ≤ δ_χ ≤ η ≤ 1/16`, `|γ_χ| ≤ T`, `F = Σ_{n∈S}a_nχ(n)n^{−u}` on
`[2, N]`, and the weight `e^{−n/U} − e^{−2n/U} ≥ c₀` on `S`, then for `X ≥ N(2q²(1 + 2T) + 1)2^J` with `d(n) ≤ τ` for
`n ≤ X`, `|R| ≤ 2c₀⁻¹GU/V² + c₀⁻²·4^{ω(q)}G³A²/V⁶`, `G = Σ|a_n|²`, with
`A = K₀(B + 1)((J + 2)X^η(τL(X)(Uq(2T + 1) + 4N·q(1 + 2T)))^{1/2} + q^{1/4}(2q(1 + 2T))^{3/4}2^{−J/16}ζ(9/8)(qN)^{1/2})`,
`K₀ = 12·KG·CG·EQ(q)q^{2η}(q(1 + 2T))^η`, `B + 1` the number of dyadic buckets of the analytic conductor
(`B = bkt(q(1 + 2T))`) and `J` the number of dyadic blocks of the dual tail. The Halász–Montgomery inequality
`hm_duality_W` with the reflected kernel sum `kernel_sum_le`, solved for `|R|` (`solve_count`). -/
theorem huxley_large_values [NeZero q] {R : Finset (DirichletCharacter ℂ q)} {δ γ : DirichletCharacter ℂ q → ℝ}
    {η : ℝ} (hη : η ≤ 1 / 16) (hδ : ∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ η) {T : ℝ} (hT : 0 ≤ T)
    (hγ : ∀ χ ∈ R, |γ χ| ≤ T) {S : Finset ℕ} {N : ℕ} (hN : 1 ≤ N) (hS : S ⊆ Icc 2 N) (a : ℕ → ℂ) {V : ℝ}
    (hV : 0 < V) (hbig : ∀ χ ∈ R, V ≤ ‖pv S a χ ((δ χ : ℂ) + γ χ * I)‖) {U : ℝ} (hU : 2 ≤ U) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hSW : ∀ n ∈ S, c₀ ≤ wW U n) (J : ℕ) {X : ℕ} (hX : 1 ≤ X)
    (hXD : (N : ℝ) * (2 * (q * (1 + 2 * T)) * q + 1) * 2 ^ J ≤ X) {τ : ℝ}
    (hτ : ∀ n, n ≤ X → (n.divisors.card : ℝ) ≤ τ) :
    (R.card : ℝ) ≤ 2 * c₀⁻¹ * (∑ n ∈ S, ‖a n‖ ^ 2) * U / V ^ 2 +
      (c₀⁻¹) ^ 2 * (q.primeFactors.powerset.card : ℝ) ^ 2 * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 3 *
        ((12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η) *
            (bkt (q * (1 + 2 * T)) + 1) * ((J + 2) * ((X : ℝ) ^ η *
              Real.sqrt (τ * LSmax X * (U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T)))))) +
          (12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η) *
            (bkt (q * (1 + 2 * T)) + 1) * ((q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) *
              ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98) * Real.sqrt (q * N)) ^ 2 / V ^ 6 := by
  classical
  set G := ∑ n ∈ S, ‖a n‖ ^ 2 with hG
  have hG0 : 0 ≤ G := sum_nonneg fun _ _ => by positivity
  set K₀ := 12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η with hK₀
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hK₀0 : 0 ≤ K₀ := by
    have := InghamDensity.KG_pos; have := CG_pos; have := EQ_pos q; rw [hK₀]; positivity
  have hτ0 : 0 ≤ τ := (Nat.cast_nonneg _).trans (hτ 1 hX)
  set A₁ := K₀ * (bkt (q * (1 + 2 * T)) + 1) * ((J + 2) * ((X : ℝ) ^ η *
      Real.sqrt (τ * LSmax X * (U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T)))))) with hA₁
  set A₂ := K₀ * (bkt (q * (1 + 2 * T)) + 1) * ((q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) *
      ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98) with hA₂
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hA₂0 : 0 ≤ A₂ := by have := zeta98_nonneg; rw [hA₂]; positivity
  rcases R.eq_empty_or_nonempty with hR | ⟨χ₀, hχ₀⟩
  · rw [hR, card_empty, Nat.cast_zero]
    positivity
  have hr : (0 : ℝ) < R.card := by exact_mod_cast card_pos.2 ⟨χ₀, hχ₀⟩
  have hrq : (R.card : ℝ) ≤ q := LinnikDensity.card_chars_le R
  have hVG : V ≤ Real.sqrt (N * G) :=
    (hbig χ₀ hχ₀).trans (norm_pv_le_sqrt hS a χ₀ (by simp; exact (hδ χ₀ hχ₀).1))
  -- the Halász–Montgomery inequality
  have hS0 : 0 ∉ S := fun h => by have := (mem_Icc.1 (hS h)).1; omega
  have hHM := hm_duality_W hS0 (by linarith : (0 : ℝ) < U) hc₀ hSW a (σ := 0) δ γ (fun χ hχ => (hδ χ hχ).1)
  have hz : ∀ χ χ' : DirichletCharacter ℂ q,
      (((δ χ + δ χ' - 2 * 0 : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I) = zz δ γ χ χ' := fun χ χ' => by
    simp [zz]
  simp_rw [hz] at hHM
  have hGs : ∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-(0 : ℝ))) ^ 2 = G := by simp [hG]
  rw [hGs] at hHM
  have hK := kernel_sum_le hη hδ hT hγ hS a hV hbig hU J hX hN hXD hτ
  -- the off-diagonal weight in the shape of `solve_count`
  have hW : Wtot q R.card τ G η T U N V X J = A₁ * V⁻¹ * Real.sqrt (R.card * G) + A₂ * R.card := by
    unfold Wtot
    rw [hA₁, hA₂, hK₀]
    have e : (R.card : ℝ) * τ * G * LSmax X * (U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T))) =
        (R.card * G) * (τ * LSmax X * (U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T)))) := by ring
    rw [e, Real.sqrt_mul (by positivity)]
    ring
  rw [hW] at hK
  have hlow : (R.card : ℝ) * V ≤ ∑ χ ∈ R, ‖pv S a χ ((δ χ : ℂ) + γ χ * I)‖ := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hbig
  have hmain : (R.card : ℝ) ^ 2 * V ^ 2 ≤ c₀⁻¹ * G * ((R.card : ℝ) * U + (q.primeFactors.powerset.card : ℝ) / 2 *
      ((R.card : ℝ) * (A₁ * V⁻¹ * Real.sqrt (R.card * G) + A₂ * R.card))) := by
    have h1 : ((R.card : ℝ) * V) ^ 2 ≤ (∑ χ ∈ R, ‖pv S a χ ((δ χ : ℂ) + γ χ * I)‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    have h2 : 0 ≤ c₀⁻¹ * G := by positivity
    calc (R.card : ℝ) ^ 2 * V ^ 2 = ((R.card : ℝ) * V) ^ 2 := by ring
      _ ≤ _ := h1.trans (hHM.trans (mul_le_mul_of_nonneg_left hK h2))
  exact solve_count hr hV hG0 hc₀ (Nat.cast_nonneg _) hA₁0 hA₂0 hrq hVG (Nat.cast_nonneg N) hmain

end LinnikReflect

#print axioms LinnikReflect.pair_reflect
#print axioms LinnikReflect.per_T_bound
#print axioms LinnikReflect.kernel_sum_le
#print axioms LinnikReflect.solve_count
#print axioms LinnikReflect.huxley_large_values
