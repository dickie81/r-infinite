/-
# Round 526, part 5: the off-diagonal pairs in dyadic buckets of the analytic conductor

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Fix `χ′ ∈ R` and sort the characters `χ ≠ χ′` of `R` by the bucket `k = bkt(Δ) = ⌈log₂⌈Δ⌉⌉` of the analytic
conductor `Δ = f(χχ′⁻¹)(1 + |γ_χ − γ_χ′|)` of the pair (`pairCond`). In the bucket `k` the dual sum is truncated at
`Z = ⌊2^k/Λ⌋` (`Zt`): `J₁` is the reflected integrand on the line `c₁ = 3/4 − 2δ_χ` with the dual sum up to `Z`, and
`J₂` the one on `c₂ = −1/4 − 2δ_χ` with the dual tail beyond `Z`. Throughout, `|F(χ, u_χ)| ≥ V` at
`u_χ = δ_χ + iγ_χ` with `F = Σ_{n∈S}a_nχ(n)n^{−u}` on `[2, N]`, `G = Σ|a_n|²`, `d(n) ≤ τ` for `n ≤ X`,
`L(X) = 8e(1 + log X)(2 + log²(2X))(log₂X + 1)` (`LSmax`), `Δ ≤ D` for every pair, and `K₀ = 12·KG·CG·EQ(q)M^{2η}D^η`.

* `main_fiber`: `Σ_χ|J₁(χ)| ≤ (1 + |v|)^{−4}K₀·2X^ηV^{−1}(|R|τG·L(X)(Λq(2T + 1) + N2^k))^{1/2}` over the bucket, when
  `NZ ≤ X`: part 4's kernel bound and dual polynomial, and part 3's product trick `huxley_core`.
* `tail_block_le`, `tail_fiber`: each of `J` dyadic blocks of the tail by the product trick, and the rest from
  `(Z + 1)2^J` on by `norm_far_tail_le`, when `N(Z + 1)2^J ≤ X`:
  `Σ_χ|J₂(χ)| ≤ (1 + |v|)^{−4}K₀(J·X^ηV^{−1}(|R|τG·L(X)(Λq(2T + 1) + 2N2^k))^{1/2} + M^{1/4}2^{3k/4}|R|2^{−J/16}ζ(9/8))`.
* `pair_sum_pointwise`: all buckets `k ≤ B = bkt(D)` at once, when `N(2DM + 1)2^J ≤ X`:
  `Σ_{χ≠χ′}(|J₁| + |J₂|) ≤ (1 + |v|)^{−4}K₀(B + 1)((J + 2)X^ηV^{−1}(|R|τG·L(X)(Λq(2T + 1) + 4ND))^{1/2}
  + M^{1/4}(2D)^{3/4}|R|2^{−J/16}ζ(9/8))`.
-/

import LinnikDual

open Complex Real Finset MeasureTheory Filter Topology

noncomputable section

namespace LinnikReflect

open DirichletCharacter LinnikPower

variable {q : ℕ}

/-! ### Buckets of the analytic conductor and the large-sieve factor -/

/-- The analytic conductor `f(χχ′⁻¹)(1 + |γ_χ − γ_χ′|)` of a pair. -/
def pairCond (χ χ' : DirichletCharacter ℂ q) (γ : DirichletCharacter ℂ q → ℝ) : ℝ :=
  ((χ * χ'⁻¹).conductor : ℝ) * (1 + |γ χ - γ χ'|)

/-- The dyadic bucket `⌈log₂⌈x⌉⌉`. -/
def bkt (x : ℝ) : ℕ := Nat.clog 2 ⌈x⌉₊

lemma bkt_spec {x : ℝ} (hx : 1 ≤ x) : x ≤ 2 ^ bkt x ∧ (2 : ℝ) ^ bkt x ≤ 2 * x := by
  have hc : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  refine ⟨hc.trans (by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) ⌈x⌉₊), ?_⟩
  unfold bkt
  rcases le_or_gt ⌈x⌉₊ 1 with h | h
  · rw [Nat.clog_of_right_le_one h]; simp; linarith
  · have h1 := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h
    have hpos := Nat.clog_pos (by norm_num : 1 < 2) h
    have h2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
    have h3 : ((2 ^ (Nat.clog 2 ⌈x⌉₊).pred : ℕ) : ℝ) + 1 ≤ ⌈x⌉₊ := by exact_mod_cast h1
    have e : (2 : ℝ) ^ Nat.clog 2 ⌈x⌉₊ = 2 * ((2 ^ (Nat.clog 2 ⌈x⌉₊).pred : ℕ) : ℝ) := by
      obtain ⟨c, hc⟩ : ∃ c, Nat.clog 2 ⌈x⌉₊ = c + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hc]; push_cast; simp [pow_succ]; ring
    rw [e]
    linarith

lemma bkt_mono {x y : ℝ} (hxy : x ≤ y) : bkt x ≤ bkt y :=
  Nat.clog_mono_right 2 (Nat.ceil_mono hxy)

lemma one_le_pairCond [NeZero q] (χ χ' : DirichletCharacter ℂ q) (γ : DirichletCharacter ℂ q → ℝ) :
    1 ≤ pairCond χ χ' γ := by
  unfold pairCond
  have hf : (1 : ℝ) ≤ (χ * χ'⁻¹).conductor := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (χ * χ'⁻¹).conductor_ne_zero
  nlinarith [abs_nonneg (γ χ - γ χ')]

/-- The truncation `⌊2^k/Λ⌋` of the dual sum in the bucket `k`. -/
def Zt (Λ : ℝ) (k : ℕ) : ℕ := ⌊(2 : ℝ) ^ k / Λ⌋₊

lemma Zt_le {Λ : ℝ} (hΛ : 0 < Λ) (k : ℕ) : Λ * Zt Λ k ≤ 2 ^ k := by
  have h := Nat.floor_le (a := (2 : ℝ) ^ k / Λ) (by positivity)
  unfold Zt
  rw [le_div_iff₀ hΛ] at h
  linarith

lemma Zt_add_one {Λ : ℝ} (hΛ : 0 < Λ) (k : ℕ) : (2 : ℝ) ^ k ≤ Λ * ((Zt Λ k : ℝ) + 1) := by
  have h := Nat.lt_floor_add_one ((2 : ℝ) ^ k / Λ)
  unfold Zt
  rw [div_lt_iff₀ hΛ] at h
  linarith

/-- The uniform large-sieve factor `L(X) = 8e(1 + log X)(2 + log²(2X))(log₂X + 1)`. -/
def LSmax (X : ℕ) : ℝ :=
  Real.exp 1 * 8 * (1 + Real.log X) * (2 + Real.log (2 * X) ^ 2) * (Nat.log 2 X + 1)

lemma LSmax_nonneg (X : ℕ) : 0 ≤ LSmax X := by
  unfold LSmax
  have : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  positivity

/-- `LSX(Y) ≤ L(X)(q(2T + 1) + Y)` for `Y ≤ X`, `X ≥ 1`. -/
lemma LSX_le (q : ℕ) {T : ℝ} (hT : 0 ≤ T) {Y X : ℕ} (hYX : Y ≤ X) (hX : 1 ≤ X) :
    LSX q T Y ≤ LSmax X * (q * (2 * T + 1) + Y) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hlX : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hl2X : 0 ≤ Real.log (2 * X) :=
    Real.log_nonneg (by have : (1 : ℝ) ≤ X := (by exact_mod_cast hX); linarith)
  have hlog : Real.log Y ≤ Real.log X ∧ Real.log (2 * Y) ^ 2 ≤ Real.log (2 * X) ^ 2 := by
    rcases Nat.eq_zero_or_pos Y with h0 | hY
    · subst h0; simp [hlX, sq_nonneg]
    · have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
      have hYX' : (Y : ℝ) ≤ X := by exact_mod_cast hYX
      refine ⟨Real.log_le_log hY0 hYX', ?_⟩
      have h1 : 0 ≤ Real.log (2 * Y) :=
        Real.log_nonneg (by have : (1 : ℝ) ≤ Y := (by exact_mod_cast hY); linarith)
      have h2 : Real.log (2 * Y) ≤ Real.log (2 * X) := Real.log_le_log (by positivity) (by linarith)
      exact pow_le_pow_left₀ h1 h2 2
  have hnl : ((Nat.log 2 Y : ℕ) : ℝ) ≤ Nat.log 2 X := by exact_mod_cast Nat.log_mono_right hYX
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hY0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y
  have hlY : 0 ≤ 1 + Real.log Y := by
    rcases Nat.eq_zero_or_pos Y with h0 | hY
    · subst h0; simp
    · have : 0 ≤ Real.log Y := Real.log_natCast_nonneg Y
      linarith
  have hA : (q : ℝ) * (2 * T + 1) + 8 * Y * (1 + Real.log Y) ≤ 8 * (1 + Real.log X) * (q * (2 * T + 1) + Y) := by
    have h1 : (q : ℝ) * (2 * T + 1) ≤ 8 * (1 + Real.log X) * (q * (2 * T + 1)) := by
      have : 0 ≤ (q : ℝ) * (2 * T + 1) := by positivity
      nlinarith
    have h2 : 8 * (Y : ℝ) * (1 + Real.log Y) ≤ 8 * (1 + Real.log X) * Y := by nlinarith [hlog.1]
    nlinarith
  unfold LSX LSmax
  have hB0 : 0 ≤ (q : ℝ) * (2 * T + 1) + 8 * Y * (1 + Real.log Y) := by positivity
  calc Real.exp 1 * (((q : ℝ) * (2 * T + 1) + 8 * Y * (1 + Real.log Y)) * (2 + Real.log (2 * Y) ^ 2)) *
        ((Nat.log 2 Y : ℕ) + 1)
      ≤ Real.exp 1 * ((8 * (1 + Real.log X) * (q * (2 * T + 1) + Y)) * (2 + Real.log (2 * X) ^ 2)) *
        ((Nat.log 2 X : ℕ) + 1) := by
        have h2 : (2 : ℝ) + Real.log (2 * Y) ^ 2 ≤ 2 + Real.log (2 * X) ^ 2 := by linarith [hlog.2]
        refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul hA h2 (by positivity) (by positivity))
          (Real.exp_pos 1).le) (by linarith) (by positivity) (by positivity)
    _ = Real.exp 1 * 8 * (1 + Real.log X) * (2 + Real.log (2 * X) ^ 2) * ((Nat.log 2 X : ℕ) + 1) *
          (q * (2 * T + 1) + Y) := by ring

lemma kernel_dual_aux {Λ P Z A : ℝ} (hP : 0 < P) (hZ : 0 ≤ Z) (hΛZ : Λ * Z ≤ P)
    (hΛ0 : 0 ≤ Λ) (hA4 : A ^ 4 = Λ ^ 3 * (P / 2)⁻¹) : A ^ 2 * Real.sqrt Z ≤ Real.sqrt 2 * Λ := by
  have hP2 : 0 < P / 2 := by positivity
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, mul_pow, Real.sq_sqrt hZ, mul_pow,
    Real.sq_sqrt (by norm_num), ← pow_mul, hA4]
  rw [show Λ ^ 3 * (P / 2)⁻¹ * Z = Λ ^ 2 * (Λ * Z) / (P / 2) by field_simp, div_le_iff₀ hP2]
  calc Λ ^ 2 * (Λ * Z) ≤ Λ ^ 2 * P := by gcongr
    _ = 2 * Λ ^ 2 * (P / 2) := by ring

/-- `(Λ^{3/4}(P/2)^{−1/4})²·√Z ≤ √2·Λ` when `ΛZ ≤ P`. -/
lemma kernel_dual_num {Λ P Z : ℝ} (hΛ : 0 < Λ) (hP : 0 < P) (hZ : 0 ≤ Z) (hΛZ : Λ * Z ≤ P) :
    (Λ ^ (3 / 4 : ℝ) * (P / 2) ^ (-1 / 4 : ℝ)) ^ 2 * Real.sqrt Z ≤ Real.sqrt 2 * Λ := by
  have hP2 : 0 < P / 2 := by positivity
  refine kernel_dual_aux hP hZ hΛZ hΛ.le ?_
  rw [mul_pow, ← Real.rpow_natCast (Λ ^ (3 / 4 : ℝ)), ← Real.rpow_natCast ((P / 2) ^ (-1 / 4 : ℝ)),
    ← Real.rpow_mul hΛ.le, ← Real.rpow_mul hP2.le,
    show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    show (-1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_natCast, Real.rpow_neg_one]

/-- `Z^{1/2+2a′}/(1/2 + 2a′) ≤ 2√Z·(X^η)²` for `Z ≤ X` and `0 ≤ a′ ≤ η`. -/
lemma mass_main_le {Z X : ℕ} (hZX : Z ≤ X) {a' η : ℝ} (ha0 : 0 ≤ a') (haη : a' ≤ η) :
    (Z : ℝ) ^ (1 / 2 + 2 * a') / (1 / 2 + 2 * a') ≤ 2 * Real.sqrt Z * ((X : ℝ) ^ η) ^ 2 := by
  have hη : 0 ≤ η := ha0.trans haη
  rcases Nat.eq_zero_or_pos Z with h0 | hZ
  · subst h0
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), zero_div]
    positivity
  · have hZ1 : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
    have hZX' : (Z : ℝ) ≤ X := by exact_mod_cast hZX
    have h1 : (Z : ℝ) ^ (1 / 2 + 2 * a') = Real.sqrt Z * (Z : ℝ) ^ (2 * a') := by
      rw [Real.rpow_add (by linarith), Real.sqrt_eq_rpow]
    have h2 : (Z : ℝ) ^ (2 * a') ≤ ((X : ℝ) ^ η) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      calc (Z : ℝ) ^ (2 * a') ≤ (Z : ℝ) ^ (η * ((2 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hZ1 (by push_cast; linarith)
        _ ≤ (X : ℝ) ^ (η * ((2 : ℕ) : ℝ)) := Real.rpow_le_rpow (by linarith) hZX' (by positivity)
    have h3 : 1 / (1 / 2 + 2 * a') ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    rw [h1, div_eq_mul_one_div]
    calc Real.sqrt Z * (Z : ℝ) ^ (2 * a') * (1 / (1 / 2 + 2 * a'))
        ≤ Real.sqrt Z * ((X : ℝ) ^ η) ^ 2 * 2 := by gcongr
      _ = 2 * Real.sqrt Z * ((X : ℝ) ^ η) ^ 2 := by ring

/-- The arithmetic of one bucket on the first line. -/
lemma fiber_num {B₁ Rk R LS Lm Q0 NZ NP SE Xe Λ Z : ℝ} (hB₁ : 0 ≤ B₁) (hRk0 : 0 ≤ Rk) (hR : Rk ≤ R)
    (hLS0 : 0 ≤ LS) (hL : LS ≤ Lm * (Q0 + NZ)) (hSE0 : 0 ≤ SE) (hE : SE ≤ 2 * Real.sqrt Z * Xe) (hXe : 0 ≤ Xe)
    (hK : B₁ * Real.sqrt Z ≤ Real.sqrt 2 * Λ) (hZP : Λ * NZ ≤ NP) (hΛ : 0 ≤ Λ) (hQ0 : 0 ≤ Q0) (hNZ : 0 ≤ NZ)
    (hLm : 0 ≤ Lm) :
    B₁ * (Rk * (LS * SE)) ≤ 4 * Xe * (R * (Lm * (Λ * Q0 + NP))) := by
  have hR0 : 0 ≤ R := hRk0.trans hR
  have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  calc B₁ * (Rk * (LS * SE)) ≤ B₁ * (R * ((Lm * (Q0 + NZ)) * (2 * Real.sqrt Z * Xe))) := by gcongr
    _ = 2 * Xe * (R * (Lm * (Q0 + NZ))) * (B₁ * Real.sqrt Z) := by ring
    _ ≤ 2 * Xe * (R * (Lm * (Q0 + NZ))) * (Real.sqrt 2 * Λ) := by gcongr
    _ = 2 * Real.sqrt 2 * Xe * (R * (Lm * (Λ * Q0 + Λ * NZ))) := by ring
    _ ≤ 4 * Xe * (R * (Lm * (Λ * Q0 + NP))) := by
        have h4 : 2 * Real.sqrt 2 ≤ 4 := by linarith
        have h5 : Λ * Q0 + Λ * NZ ≤ Λ * Q0 + NP := by linarith
        have h6 : 0 ≤ Xe * (R * (Lm * (Λ * Q0 + Λ * NZ))) := by positivity
        calc 2 * Real.sqrt 2 * Xe * (R * (Lm * (Λ * Q0 + Λ * NZ)))
            = (2 * Real.sqrt 2) * (Xe * (R * (Lm * (Λ * Q0 + Λ * NZ)))) := by ring
          _ ≤ 4 * (Xe * (R * (Lm * (Λ * Q0 + Λ * NZ)))) := mul_le_mul_of_nonneg_right h4 h6
          _ ≤ 4 * (Xe * (R * (Lm * (Λ * Q0 + NP)))) := by gcongr
          _ = 4 * Xe * (R * (Lm * (Λ * Q0 + NP))) := by ring

/-! ### One bucket of the first line -/

/-- The point `z = (δ_χ + δ_χ′) + i(γ_χ − γ_χ′)` of a pair. -/
def zz (δ γ : DirichletCharacter ℂ q → ℝ) (χ χ' : DirichletCharacter ℂ q) : ℂ :=
  ((δ χ + δ χ' : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I

/-- The reflected integrand of a pair on the first line `c₁ = 3/4 − 2δ_χ`, with the dual sum truncated at
`⌊2^k/Λ⌋`, `k` the bucket of the pair's conductor. -/
def J1 [NeZero q] (δ γ : DirichletCharacter ℂ q → ℝ) (χ χ' : DirichletCharacter ℂ q) (Λ v : ℝ) : ℂ :=
  kW Λ (((3 / 4 - 2 * δ χ : ℝ) : ℂ) + v * I) *
    Phi (χ * χ'⁻¹).primitiveCharacter q (zz δ γ χ χ' + (((3 / 4 - 2 * δ χ : ℝ) : ℂ) + v * I)) *
    dualS (χ * χ'⁻¹)⁻¹ (Zt Λ (bkt (pairCond χ χ' γ))) (zz δ γ χ χ' + (((3 / 4 - 2 * δ χ : ℝ) : ℂ) + v * I))

/-- **One bucket of the first line.** For the characters `χ ≠ χ′` of `R` whose pair conductor lies in the bucket `k`,
`Σ_χ |J₁(χ)| ≤ (1 + |v|)^{−4}·K₀·2X^η·V^{−1}(|R|τG·L(X)(Λq(2T + 1) + N2^k))^{1/2}`,
`K₀ = 12·KG·CG·EQ(q)M^{2η}D^η`: the kernel bound `pair_kernel_one`, the dual sum as a polynomial at the points of `χ`
(`dualS_eq_conj_pv`), and the product trick `huxley_core` against the large values `|F(χ)| ≥ V`. -/
theorem main_fiber [NeZero q] {R : Finset (DirichletCharacter ℂ q)} {δ γ : DirichletCharacter ℂ q → ℝ} {η : ℝ}
    (hη : η ≤ 1 / 16) (hδ : ∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ η) {T : ℝ} (hT : 0 ≤ T) (hγ : ∀ χ ∈ R, |γ χ| ≤ T)
    {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Icc 2 N) (a : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ χ ∈ R, V ≤ ‖pv S a χ ((δ χ : ℂ) + γ χ * I)‖) {χ' : DirichletCharacter ℂ q} (hχ' : χ' ∈ R)
    {Λ M D : ℝ} (hΛ : 0 < Λ) (hM : 1 ≤ M) (hΛM : Λ⁻¹ ≤ M) (hD1 : 1 ≤ D) (hD : ∀ χ ∈ R, pairCond χ χ' γ ≤ D)
    (v : ℝ) (k : ℕ) {X : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXZ : N * Zt Λ k ≤ X) {τ : ℝ} (hτ : ∀ n, n ≤ X → (n.divisors.card : ℝ) ≤ τ) :
    ∑ χ ∈ (R.erase χ').filter (fun χ => bkt (pairCond χ χ' γ) = k), ‖J1 δ γ χ χ' Λ v‖ ≤
      ((1 + |v|) ^ 4)⁻¹ * (12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η) * 2 * (X : ℝ) ^ η * V⁻¹ *
        Real.sqrt (R.card * τ * (∑ n ∈ S, ‖a n‖ ^ 2) * LSmax X * (Λ * q * (2 * T + 1) + N * 2 ^ k)) := by
  classical
  set Rk := (R.erase χ').filter (fun χ => bkt (pairCond χ χ' γ) = k) with hRk
  set Z := Zt Λ k with hZ
  set P : ℝ := 2 ^ k with hP
  set K₀ := 12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η with hK₀
  set g : ℝ := ((1 + |v|) ^ 4)⁻¹ with hg
  set E := dualCo χ' (3 / 4) (δ χ') (γ χ') v with hE
  set G := ∑ n ∈ S, ‖a n‖ ^ 2 with hG
  have hP0 : 0 < P := by positivity
  have hP2 : 0 < P / 2 := by positivity
  have hK₀0 : 0 ≤ K₀ := by
    have := InghamDensity.KG_pos; have := CG_pos; have := EQ_pos q; rw [hK₀]; positivity
  have hg0 : 0 ≤ g := by positivity
  have hmem : ∀ χ ∈ Rk, χ ∈ R ∧ χ ≠ χ' ∧ bkt (pairCond χ χ' γ) = k := by
    intro χ hχ
    obtain ⟨h1, h2⟩ := mem_filter.1 hχ
    obtain ⟨h3, h4⟩ := mem_erase.1 h1
    exact ⟨h4, h3, h2⟩
  -- one character at a time
  have hpt : ∀ χ ∈ Rk, ‖J1 δ γ χ χ' Λ v‖ ≤
      K₀ * (Λ ^ (3 / 4 : ℝ) * (P / 2) ^ (-1 / 4 : ℝ)) * g * ‖pv (Icc 1 Z) E χ ((δ χ : ℂ) + γ χ * I)‖ := by
    intro χ hχ
    obtain ⟨hχR, -, hk⟩ := hmem χ hχ
    have hker := pair_kernel_one (χ * χ'⁻¹).primitiveCharacter_isPrimitive q hΛ (hδ χ hχR).1 (hδ χ hχR).2
      (hδ χ' hχ').1 (hδ χ' hχ').2 hη (γ χ) (γ χ') v hM hΛM (hD χ hχR)
    have hb := bkt_spec (one_le_pairCond χ χ' γ)
    rw [hk] at hb
    have hΔ : (pairCond χ χ' γ) ^ (-1 / 4 : ℝ) ≤ (P / 2) ^ (-1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hP2 (by rw [hP]; linarith [hb.2]) (by norm_num)
    have hdual : ‖dualS (χ * χ'⁻¹)⁻¹ Z (zz δ γ χ χ' + (((3 / 4 - 2 * δ χ : ℝ) : ℂ) + v * I))‖ =
        ‖pv (Icc 1 Z) E χ ((δ χ : ℂ) + γ χ * I)‖ := by
      unfold zz; rw [dualS_eq_conj_pv, Complex.norm_conj]
    unfold J1
    rw [hk, ← hZ, norm_mul, norm_mul, hdual]
    have hker' : ‖kW Λ (((3 / 4 - 2 * δ χ : ℝ) : ℂ) + v * I)‖ *
        ‖Phi (χ * χ'⁻¹).primitiveCharacter q (zz δ γ χ χ' + (((3 / 4 - 2 * δ χ : ℝ) : ℂ) + v * I))‖ ≤
        K₀ * (Λ ^ (3 / 4 : ℝ) * (P / 2) ^ (-1 / 4 : ℝ)) * g := by
      refine hker.trans ?_
      rw [hK₀, hg]
      unfold pairCond at hΔ
      have hΛ34 : 0 ≤ Λ ^ (3 / 4 : ℝ) := by positivity
      have : 0 ≤ 12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η * Λ ^ (3 / 4 : ℝ) := by
        have := InghamDensity.KG_pos; have := CG_pos; have := EQ_pos q; positivity
      calc 12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η * Λ ^ (3 / 4 : ℝ) *
            (((χ * χ'⁻¹).conductor : ℝ) * (1 + |γ χ - γ χ'|)) ^ (-1 / 4 : ℝ) * ((1 + |v|) ^ 4)⁻¹
          ≤ 12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η * Λ ^ (3 / 4 : ℝ) *
            (P / 2) ^ (-1 / 4 : ℝ) * ((1 + |v|) ^ 4)⁻¹ := by gcongr
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right hker' (norm_nonneg _)
  have hA0 : 0 ≤ K₀ * (Λ ^ (3 / 4 : ℝ) * (P / 2) ^ (-1 / 4 : ℝ)) * g := by positivity
  have hsum : ∑ χ ∈ Rk, ‖J1 δ γ χ χ' Λ v‖ ≤ K₀ * (Λ ^ (3 / 4 : ℝ) * (P / 2) ^ (-1 / 4 : ℝ)) * g * ∑ χ ∈ Rk, ‖pv (Icc 1 Z) E χ ((δ χ : ℂ) + γ χ * I)‖ := by
    rw [mul_sum]; exact sum_le_sum hpt
  -- the product trick over the bucket
  have hcore := huxley_core (M := Icc 1 Z) (K := Z) hS (Subset.refl _) a E q hT Rk δ γ
    (fun χ hχ => ⟨(hδ χ (hmem χ hχ).1).1, by linarith [(hδ χ (hmem χ hχ).1).2]⟩)
    (fun χ hχ => hγ χ (hmem χ hχ).1) hV (fun χ hχ => hbig χ (hmem χ hχ).1) (τ := τ)
    (fun n hn => hτ n (hn.trans hXZ))
  set Q₁ := (V ^ 2)⁻¹ * (Rk.card * (LSX q T (N * Z) * (τ * (G * ∑ m ∈ Icc 1 Z, ‖E m‖ ^ 2)))) with hQ₁
  have hτ0 : 0 ≤ τ := (Nat.cast_nonneg _).trans (hτ 1 hX)
  have hQ₁0 : 0 ≤ Q₁ := by
    have := LSX_nonneg q hT (N * Z)
    rw [hQ₁]; positivity
  have hpv0 : 0 ≤ ∑ χ ∈ Rk, ‖pv (Icc 1 Z) E χ ((δ χ : ℂ) + γ χ * I)‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hpvle : ∑ χ ∈ Rk, ‖pv (Icc 1 Z) E χ ((δ χ : ℂ) + γ χ * I)‖ ≤ Real.sqrt Q₁ :=
    (Real.le_sqrt hpv0 hQ₁0).2 hcore
  -- the arithmetic
  have hmass := mass_dualCo_one χ' (hδ χ' hχ').1 (by linarith [(hδ χ' hχ').2]) (γ χ') v Z
  have hZX : Z ≤ X := le_trans (Nat.le_mul_of_pos_left Z hN) hXZ
  have hE2 := (hmass.trans (mass_main_le hZX (hδ χ' hχ').1 (hδ χ' hχ').2))
  have hLS := LSX_le q hT hXZ hX
  have hZ0 : (0 : ℝ) ≤ Z := Nat.cast_nonneg Z
  have hΛZ : Λ * Z ≤ P := Zt_le hΛ k
  have hK := kernel_dual_num hΛ hP0 hZ0 hΛZ
  have hRk : (Rk.card : ℝ) ≤ R.card := by
    exact_mod_cast card_le_card ((filter_subset _ _).trans (erase_subset _ _))
  have hNZP : Λ * ((N * Z : ℕ) : ℝ) ≤ N * P := by
    push_cast
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hfib := fiber_num (B₁ := (Λ ^ (3 / 4 : ℝ) * (P / 2) ^ (-1 / 4 : ℝ)) ^ 2) (Rk := Rk.card) (R := R.card)
    (LS := LSX q T (N * Z)) (Lm := LSmax X) (Q0 := q * (2 * T + 1)) (NZ := ((N * Z : ℕ) : ℝ)) (NP := N * P)
    (SE := ∑ m ∈ Icc 1 Z, ‖E m‖ ^ 2) (Xe := ((X : ℝ) ^ η) ^ 2) (Λ := Λ) (Z := Z) (by positivity)
    (Nat.cast_nonneg _) hRk (LSX_nonneg q hT _) hLS (sum_nonneg fun _ _ => by positivity) hE2 (by positivity) hK
    hNZP hΛ.le (by positivity) (Nat.cast_nonneg _) (LSmax_nonneg X)
  set W := (R.card : ℝ) * τ * G * LSmax X * (Λ * q * (2 * T + 1) + N * P) with hW
  have hG0 : 0 ≤ G := sum_nonneg fun _ _ => by positivity
  have hW0 : 0 ≤ W := by
    have := LSmax_nonneg X
    rw [hW]; positivity
  have hXη : 0 ≤ (X : ℝ) ^ η := by positivity
  calc ∑ χ ∈ Rk, ‖J1 δ γ χ χ' Λ v‖
      ≤ K₀ * (Λ ^ (3 / 4 : ℝ) * (P / 2) ^ (-1 / 4 : ℝ)) * g *
          ∑ χ ∈ Rk, ‖pv (Icc 1 Z) E χ ((δ χ : ℂ) + γ χ * I)‖ := hsum
    _ ≤ K₀ * (Λ ^ (3 / 4 : ℝ) * (P / 2) ^ (-1 / 4 : ℝ)) * g * Real.sqrt Q₁ :=
        mul_le_mul_of_nonneg_left hpvle hA0
    _ ≤ g * K₀ * 2 * (X : ℝ) ^ η * V⁻¹ * Real.sqrt W := by
        rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero]
        rw [mul_pow (K₀ * (Λ ^ (3 / 4 : ℝ) * (P / 2) ^ (-1 / 4 : ℝ)) * g) (Real.sqrt Q₁), Real.sq_sqrt hQ₁0,
          mul_pow (g * K₀ * 2 * (X : ℝ) ^ η * V⁻¹) (Real.sqrt W), Real.sq_sqrt hW0, hQ₁, hW]
        have hV2 : (V ^ 2)⁻¹ = (V⁻¹) ^ 2 := by rw [inv_pow]
        rw [hV2]
        have hc : 0 ≤ K₀ ^ 2 * g ^ 2 * (V⁻¹) ^ 2 * τ * G := by positivity
        have := mul_le_mul_of_nonneg_left hfib hc
        calc (K₀ * (Λ ^ (3 / 4 : ℝ) * (P / 2) ^ (-1 / 4 : ℝ)) * g) ^ 2 *
              ((V⁻¹) ^ 2 * (Rk.card * (LSX q T (N * Z) * (τ * (G * ∑ m ∈ Icc 1 Z, ‖E m‖ ^ 2)))))
            = K₀ ^ 2 * g ^ 2 * (V⁻¹) ^ 2 * τ * G * ((Λ ^ (3 / 4 : ℝ) * (P / 2) ^ (-1 / 4 : ℝ)) ^ 2 *
              (Rk.card * (LSX q T (N * Z) * ∑ m ∈ Icc 1 Z, ‖E m‖ ^ 2))) := by ring
          _ ≤ K₀ ^ 2 * g ^ 2 * (V⁻¹) ^ 2 * τ * G * (4 * ((X : ℝ) ^ η) ^ 2 * (R.card * (LSmax X *
              (Λ * (q * (2 * T + 1)) + N * P)))) := this
          _ = (g * K₀ * 2 * (X : ℝ) ^ η * V⁻¹) ^ 2 *
              (R.card * τ * G * LSmax X * (Λ * q * (2 * T + 1) + N * P)) := by ring

/-! ### One bucket of the second line: the dual tail in dyadic blocks -/

/-- The arithmetic of one tail block: `C²(Q₀ + 2NY)·Y^{−3/2} ≤ ΛQ₀ + 2NP` for `C⁴ = Λ⁻¹P³` and `P ≤ ΛY`. -/
lemma tail_num_aux {Λ P Y C Q0 N : ℝ} (hΛ : 0 < Λ) (hP : 0 < P) (hY : 0 < Y) (hPY : P ≤ Λ * Y)
    (hC4 : C ^ 4 = Λ⁻¹ * P ^ 3) (hQ0 : 0 ≤ Q0) (hN : 0 ≤ N) :
    C ^ 2 * (Q0 + 2 * N * Y) * (Y⁻¹ * (Real.sqrt Y)⁻¹) ≤ Λ * Q0 + 2 * N * P := by
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY
  have h1 : C ^ 2 * (Y⁻¹ * (Real.sqrt Y)⁻¹) ≤ Λ := by
    rw [← mul_inv, mul_inv_le_iff₀ (by positivity)]
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, ← pow_mul, hC4, mul_pow, mul_pow,
      Real.sq_sqrt hY.le]
    rw [inv_mul_le_iff₀ hΛ]
    have : P ^ 3 ≤ (Λ * Y) ^ 3 := pow_le_pow_left₀ hP.le hPY 3
    nlinarith [this]
  have h2 : C ^ 2 * Y * (Y⁻¹ * (Real.sqrt Y)⁻¹) ≤ P := by
    rw [show C ^ 2 * Y * (Y⁻¹ * (Real.sqrt Y)⁻¹) = C ^ 2 * (Real.sqrt Y)⁻¹ by field_simp]
    rw [mul_inv_le_iff₀ hsY]
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, ← pow_mul, hC4, mul_pow,
      Real.sq_sqrt hY.le]
    rw [inv_mul_le_iff₀ hΛ]
    have : P ^ 3 ≤ P ^ 2 * (Λ * Y) := by
      have : P ^ 3 = P ^ 2 * P := by ring
      rw [this]; gcongr
    nlinarith [this]
  calc C ^ 2 * (Q0 + 2 * N * Y) * (Y⁻¹ * (Real.sqrt Y)⁻¹)
      = Q0 * (C ^ 2 * (Y⁻¹ * (Real.sqrt Y)⁻¹)) + 2 * N * (C ^ 2 * Y * (Y⁻¹ * (Real.sqrt Y)⁻¹)) := by ring
    _ ≤ Q0 * Λ + 2 * N * P := by gcongr
    _ = Λ * Q0 + 2 * N * P := by ring

lemma tail_C4 {Λ P : ℝ} (hΛ : 0 < Λ) (hP : 0 < P) :
    (Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ)) ^ 4 = Λ⁻¹ * P ^ 3 := by
  rw [mul_pow, ← Real.rpow_natCast (Λ ^ (-1 / 4 : ℝ)), ← Real.rpow_natCast (P ^ (3 / 4 : ℝ)),
    ← Real.rpow_mul hΛ.le, ← Real.rpow_mul hP.le,
    show (-1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = -1 by norm_num,
    show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_neg_one]

/-- `Y^{−3/2+2a′} ≤ (X^η)²·Y⁻¹(√Y)⁻¹` for `1 ≤ Y ≤ X` and `0 ≤ a′ ≤ η`. -/
lemma block_mass_le {Y X a' η : ℝ} (hY : 1 ≤ Y) (hYX : Y ≤ X) (ha0 : 0 ≤ a') (haη : a' ≤ η) :
    Y ^ (-3 / 2 + 2 * a') ≤ (X ^ η) ^ 2 * (Y⁻¹ * (Real.sqrt Y)⁻¹) := by
  have hY0 : 0 < Y := by linarith
  have e : Y ^ (-3 / 2 + 2 * a') = Y ^ (2 * a') * (Y⁻¹ * (Real.sqrt Y)⁻¹) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_neg hY0.le, ← Real.rpow_add hY0,
      ← Real.rpow_add hY0]
    congr 1; ring
  rw [e]
  gcongr
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  calc Y ^ (2 * a') ≤ Y ^ (η * ((2 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hY (by push_cast; linarith)
    _ ≤ X ^ (η * ((2 : ℕ) : ℝ)) := Real.rpow_le_rpow hY0.le hYX (by have := ha0.trans haη; positivity)

/-- The arithmetic of one tail block against the large sieve. -/
lemma block_num {C Rk R LS Lm Q0 N Y SE Xe Λ P : ℝ} (hRk0 : 0 ≤ Rk) (hR : Rk ≤ R) (hLS0 : 0 ≤ LS)
    (hL : LS ≤ Lm * (Q0 + 2 * N * Y)) (hSE0 : 0 ≤ SE) (hE : SE ≤ Xe * (Y⁻¹ * (Real.sqrt Y)⁻¹)) (hXe : 0 ≤ Xe)
    (hcore : C ^ 2 * (Q0 + 2 * N * Y) * (Y⁻¹ * (Real.sqrt Y)⁻¹) ≤ Λ * Q0 + 2 * N * P) (hY : 0 < Y) (hQ0 : 0 ≤ Q0)
    (hN : 0 ≤ N) (hLm : 0 ≤ Lm) :
    C ^ 2 * (Rk * (LS * SE)) ≤ Xe * (R * (Lm * (Λ * Q0 + 2 * N * P))) := by
  have hR0 : 0 ≤ R := hRk0.trans hR
  calc C ^ 2 * (Rk * (LS * SE)) ≤ C ^ 2 * (R * ((Lm * (Q0 + 2 * N * Y)) * (Xe * (Y⁻¹ * (Real.sqrt Y)⁻¹)))) := by
        gcongr
    _ = Xe * (R * (Lm * (C ^ 2 * (Q0 + 2 * N * Y) * (Y⁻¹ * (Real.sqrt Y)⁻¹)))) := by ring
    _ ≤ Xe * (R * (Lm * (Λ * Q0 + 2 * N * P))) := by gcongr

/-- **One tail block by the product trick**: for the points of `Rs` with large values `|F(χ)| ≥ V`,
`Λ^{−1/4}P^{3/4}·Σ_χ |Σ_{m∈B_j} dualCo(m)χ(m)m^{−u_χ}| ≤ X^ηV^{−1}(R_c τG·L(X)(ΛQ₀ + 2NP))^{1/2}` when
`P ≤ ΛA2^j`, `Q₀ = q(2T + 1)`. -/
theorem tail_block_le [NeZero q] {Rs : Finset (DirichletCharacter ℂ q)} {δ γ : DirichletCharacter ℂ q → ℝ}
    {η : ℝ} (hη : η ≤ 1 / 16) (hδ : ∀ χ ∈ Rs, 0 ≤ δ χ ∧ δ χ ≤ η) {T : ℝ} (hT : 0 ≤ T)
    (hγ : ∀ χ ∈ Rs, |γ χ| ≤ T) {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Icc 2 N) (a : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ χ ∈ Rs, V ≤ ‖pv S a χ ((δ χ : ℂ) + γ χ * I)‖) (χ' : DirichletCharacter ℂ q) {a' : ℝ}
    (ha0 : 0 ≤ a') (haη : a' ≤ η) (g' v : ℝ) {Λ P : ℝ} (hΛ : 0 < Λ) (hP : 0 < P) {A J j : ℕ} (hA : 1 ≤ A)
    (hjJ : j + 1 ≤ J) (hPY : P ≤ Λ * ((A * 2 ^ j : ℕ) : ℝ)) {X : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N)
    (hXZ : N * (A * 2 ^ J) ≤ X) {τ : ℝ} (hτ : ∀ n, n ≤ X → (n.divisors.card : ℝ) ≤ τ) {Rc : ℝ}
    (hRc : (Rs.card : ℝ) ≤ Rc) :
    (Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ)) *
        ∑ χ ∈ Rs, ‖pv (tailBlock A J j) (dualCo χ' (-1 / 4) a' g' v) χ ((δ χ : ℂ) + γ χ * I)‖ ≤
      (X : ℝ) ^ η * V⁻¹ *
        Real.sqrt (Rc * τ * (∑ n ∈ S, ‖a n‖ ^ 2) * LSmax X * (Λ * q * (2 * T + 1) + 2 * N * P)) := by
  have hNK : N * (A * 2 ^ (j + 1)) ≤ X :=
    le_trans (Nat.mul_le_mul_left N (Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) hjJ))) hXZ
  have hcore := huxley_core (M := tailBlock A J j) (K := A * 2 ^ (j + 1)) hS (tailBlock_sub hA) a
    (dualCo χ' (-1 / 4) a' g' v) q hT Rs δ γ (fun χ hχ => ⟨(hδ χ hχ).1, by linarith [(hδ χ hχ).2]⟩) hγ hV hbig
    (τ := τ) (fun n hn => hτ n (hn.trans hNK))
  have hτ0 : 0 ≤ τ := (Nat.cast_nonneg _).trans (hτ 1 hX)
  have hG0 : 0 ≤ ∑ n ∈ S, ‖a n‖ ^ 2 := sum_nonneg fun _ _ => by positivity
  have hQ0 : 0 ≤ (V ^ 2)⁻¹ * (Rs.card * (LSX q T (N * (A * 2 ^ (j + 1))) *
      (τ * ((∑ n ∈ S, ‖a n‖ ^ 2) * ∑ m ∈ tailBlock A J j, ‖dualCo χ' (-1 / 4) a' g' v m‖ ^ 2)))) := by
    have := LSX_nonneg q hT (N * (A * 2 ^ (j + 1))); positivity
  have hpv0 : 0 ≤ ∑ χ ∈ Rs, ‖pv (tailBlock A J j) (dualCo χ' (-1 / 4) a' g' v) χ ((δ χ : ℂ) + γ χ * I)‖ :=
    sum_nonneg fun _ _ => norm_nonneg _
  have hpvle := (Real.le_sqrt hpv0 hQ0).2 hcore
  have hY1 : (1 : ℝ) ≤ ((A * 2 ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hYX : ((A * 2 ^ j : ℕ) : ℝ) ≤ X := by
    exact_mod_cast le_trans (Nat.le_mul_of_pos_left _ hN)
      (le_trans (Nat.mul_le_mul_left N (Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) (by omega))))
        hXZ)
  have hmass := (mass_dualCo_block χ' (by linarith) g' v (J := J) (j := j) hA).trans
    (block_mass_le hY1 hYX ha0 haη)
  have hLS := LSX_le q hT hNK hX
  have hcast : ((N * (A * 2 ^ (j + 1)) : ℕ) : ℝ) = 2 * N * ((A * 2 ^ j : ℕ) : ℝ) := by push_cast; ring
  rw [hcast] at hLS
  have htn := tail_num_aux hΛ hP (by linarith) hPY (tail_C4 hΛ hP) (Q0 := q * (2 * T + 1)) (by positivity)
    (Nat.cast_nonneg N)
  have hbn := block_num (C := Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ)) (Rk := Rs.card) (R := Rc)
    (LS := LSX q T (N * (A * 2 ^ (j + 1)))) (Lm := LSmax X) (Q0 := q * (2 * T + 1)) (N := N)
    (Y := ((A * 2 ^ j : ℕ) : ℝ)) (SE := ∑ m ∈ tailBlock A J j, ‖dualCo χ' (-1 / 4) a' g' v m‖ ^ 2)
    (Xe := ((X : ℝ) ^ η) ^ 2) (Λ := Λ) (P := P) (Nat.cast_nonneg _) hRc (LSX_nonneg q hT _) hLS
    (sum_nonneg fun _ _ => by positivity) hmass (by positivity) htn (by linarith) (by positivity) (Nat.cast_nonneg N)
    (LSmax_nonneg X)
  have hRc0 : 0 ≤ Rc := (Nat.cast_nonneg _).trans hRc
  have hW0 : 0 ≤ Rc * τ * (∑ n ∈ S, ‖a n‖ ^ 2) * LSmax X * (Λ * q * (2 * T + 1) + 2 * N * P) := by
    have := LSmax_nonneg X; positivity
  have hC0 : 0 ≤ Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ) := by positivity
  refine (mul_le_mul_of_nonneg_left hpvle hC0).trans ?_
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero,
    mul_pow (Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ)) (Real.sqrt _), Real.sq_sqrt hQ0,
    mul_pow ((X : ℝ) ^ η * V⁻¹) (Real.sqrt _), Real.sq_sqrt hW0, show (V ^ 2)⁻¹ = (V⁻¹) ^ 2 by rw [inv_pow]]
  have hc : 0 ≤ (V⁻¹) ^ 2 * τ * (∑ n ∈ S, ‖a n‖ ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_left hbn hc
  calc (Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ)) ^ 2 * ((V⁻¹) ^ 2 * (Rs.card * (LSX q T (N * (A * 2 ^ (j + 1))) *
        (τ * ((∑ n ∈ S, ‖a n‖ ^ 2) * ∑ m ∈ tailBlock A J j, ‖dualCo χ' (-1 / 4) a' g' v m‖ ^ 2)))))
      = (V⁻¹) ^ 2 * τ * (∑ n ∈ S, ‖a n‖ ^ 2) * ((Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ)) ^ 2 *
        (Rs.card * (LSX q T (N * (A * 2 ^ (j + 1))) *
          ∑ m ∈ tailBlock A J j, ‖dualCo χ' (-1 / 4) a' g' v m‖ ^ 2))) := by ring
    _ ≤ (V⁻¹) ^ 2 * τ * (∑ n ∈ S, ‖a n‖ ^ 2) * (((X : ℝ) ^ η) ^ 2 * (Rc * (LSmax X *
        (Λ * (q * (2 * T + 1)) + 2 * N * P)))) := this
    _ = ((X : ℝ) ^ η * V⁻¹) ^ 2 *
        (Rc * τ * (∑ n ∈ S, ‖a n‖ ^ 2) * LSmax X * (Λ * q * (2 * T + 1) + 2 * N * P)) := by ring

/-- The reflected integrand of a pair on the second line `c₂ = −1/4 − 2δ_χ`: the dual tail beyond `⌊2^k/Λ⌋`, `k` the
bucket of the pair's conductor. -/
def J2 [NeZero q] (δ γ : DirichletCharacter ℂ q → ℝ) (χ χ' : DirichletCharacter ℂ q) (Λ v : ℝ) : ℂ :=
  kW Λ (((-1 / 4 - 2 * δ χ : ℝ) : ℂ) + v * I) *
    Phi (χ * χ'⁻¹).primitiveCharacter q (zz δ γ χ χ' + (((-1 / 4 - 2 * δ χ : ℝ) : ℂ) + v * I)) *
    dualT (χ * χ'⁻¹)⁻¹ (Zt Λ (bkt (pairCond χ χ' γ))) (zz δ γ χ χ' + (((-1 / 4 - 2 * δ χ : ℝ) : ℂ) + v * I))

/-- `ζ(9/8) = Σ_{m≥1} m^{−9/8}`. -/
def zeta98 : ℝ := ∑' m : ℕ, ((m : ℝ) ^ (9 / 8 : ℝ))⁻¹

lemma zeta98_nonneg : 0 ≤ zeta98 := tsum_nonneg fun m => by positivity

/-- **One bucket of the second line.** With `J` dyadic blocks of the dual tail beyond `Z = ⌊2^k/Λ⌋` and the rest
beyond `(Z + 1)2^J`, `Σ_χ |J₂(χ)| ≤ (1 + |v|)^{−4}K₀(J·X^ηV^{−1}(|R|τG·L(X)(Λq(2T + 1) + 2N2^k))^{1/2}
+ M^{1/4}2^{3k/4}|R|·2^{−J/16}ζ(9/8))`: each block by the product trick, the rest by `norm_far_tail_le`. -/
theorem tail_fiber [NeZero q] {R : Finset (DirichletCharacter ℂ q)} {δ γ : DirichletCharacter ℂ q → ℝ} {η : ℝ}
    (hη : η ≤ 1 / 16) (hδ : ∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ η) {T : ℝ} (hT : 0 ≤ T) (hγ : ∀ χ ∈ R, |γ χ| ≤ T)
    {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Icc 2 N) (a : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ χ ∈ R, V ≤ ‖pv S a χ ((δ χ : ℂ) + γ χ * I)‖) {χ' : DirichletCharacter ℂ q} (hχ' : χ' ∈ R)
    {Λ M D : ℝ} (hΛ : 0 < Λ) (hM : 1 ≤ M) (hΛM : Λ⁻¹ ≤ M) (hD1 : 1 ≤ D) (hD : ∀ χ ∈ R, pairCond χ χ' γ ≤ D)
    (v : ℝ) (k J : ℕ) {X : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXZ : N * ((Zt Λ k + 1) * 2 ^ J) ≤ X) {τ : ℝ}
    (hτ : ∀ n, n ≤ X → (n.divisors.card : ℝ) ≤ τ) :
    ∑ χ ∈ (R.erase χ').filter (fun χ => bkt (pairCond χ χ' γ) = k), ‖J2 δ γ χ χ' Λ v‖ ≤
      ((1 + |v|) ^ 4)⁻¹ * (12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η) *
        (J * ((X : ℝ) ^ η * V⁻¹ *
          Real.sqrt (R.card * τ * (∑ n ∈ S, ‖a n‖ ^ 2) * LSmax X * (Λ * q * (2 * T + 1) + 2 * N * 2 ^ k))) +
        M ^ (1 / 4 : ℝ) * ((2 : ℝ) ^ k) ^ (3 / 4 : ℝ) * R.card * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98) := by
  classical
  set Rk := (R.erase χ').filter (fun χ => bkt (pairCond χ χ' γ) = k) with hRk
  set Z := Zt Λ k with hZ
  set A := Z + 1 with hA
  set P : ℝ := 2 ^ k with hP
  set K₀ := 12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η with hK₀
  set g : ℝ := ((1 + |v|) ^ 4)⁻¹ with hg
  set E := dualCo χ' (-1 / 4) (δ χ') (γ χ') v with hE
  set G := ∑ n ∈ S, ‖a n‖ ^ 2 with hG
  have hP0 : 0 < P := by positivity
  have hA1 : 1 ≤ A := by omega
  have hK₀0 : 0 ≤ K₀ := by
    have := InghamDensity.KG_pos; have := CG_pos; have := EQ_pos q; rw [hK₀]; positivity
  have hg0 : 0 ≤ g := by positivity
  have hτ0 : 0 ≤ τ := (Nat.cast_nonneg _).trans (hτ 1 hX)
  have hG0 : 0 ≤ G := sum_nonneg fun _ _ => by positivity
  have hmem : ∀ χ ∈ Rk, χ ∈ R ∧ χ ≠ χ' ∧ bkt (pairCond χ χ' γ) = k := by
    intro χ hχ
    obtain ⟨h1, h2⟩ := mem_filter.1 hχ
    obtain ⟨h3, h4⟩ := mem_erase.1 h1
    exact ⟨h4, h3, h2⟩
  set C₂ := K₀ * (Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ)) * g with hC₂
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  set far : ℝ := ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98 with hfar
  have hfar0 : 0 ≤ far := by have := zeta98_nonneg; rw [hfar]; positivity
  -- one character: the kernel, the blocks and the far tail
  have hpt : ∀ χ ∈ Rk, ‖J2 δ γ χ χ' Λ v‖ ≤
      C₂ * (∑ j ∈ range J, ‖pv (tailBlock A J j) E χ ((δ χ : ℂ) + γ χ * I)‖ + far) := by
    intro χ hχ
    obtain ⟨hχR, -, hk⟩ := hmem χ hχ
    have hker := pair_kernel_two (χ * χ'⁻¹).primitiveCharacter_isPrimitive q hΛ (hδ χ hχR).1 (hδ χ hχR).2
      (hδ χ' hχ').1 (hδ χ' hχ').2 hη (γ χ) (γ χ') v hM hΛM (hD χ hχR)
    have hb := bkt_spec (one_le_pairCond χ χ' γ)
    rw [hk] at hb
    have hΔ : (pairCond χ χ' γ) ^ (3 / 4 : ℝ) ≤ P ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith [one_le_pairCond χ χ' γ]) hb.1 (by norm_num)
    set s : ℂ := zz δ γ χ χ' + (((-1 / 4 - 2 * δ χ : ℝ) : ℂ) + v * I) with hs
    have hsre : s.re = -1 / 4 + δ χ' - δ χ := by simp [hs, zz]; ring
    have hsplit := dualT_split (χ * χ'⁻¹)⁻¹ Z J (s := s) (by rw [hsre]; linarith [(hδ χ hχR).1, (hδ χ' hχ').2])
    have hblock : ∀ j ∈ range J, ‖∑ m ∈ tailBlock (Z + 1) J j, (χ * χ'⁻¹)⁻¹ m * (m : ℂ) ^ (s - 1)‖ =
        ‖pv (tailBlock A J j) E χ ((δ χ : ℂ) + γ χ * I)‖ := by
      intro j _
      have h0 : 0 ∉ tailBlock A J j := fun h => by
        have := (mem_tailBlock hA1 h).1
        have : 1 ≤ A * 2 ^ j := Nat.one_le_iff_ne_zero.2 (by positivity)
        omega
      rw [hs]; unfold zz
      rw [sum_dual_eq_conj_pv χ χ' h0, Complex.norm_conj]
    have hfarle : ‖∑' m : ℕ, if (Z + 1) * 2 ^ J ≤ m then (χ * χ'⁻¹)⁻¹ m * (m : ℂ) ^ (s - 1) else 0‖ ≤ far := by
      have hM1 : 1 ≤ (Z + 1) * 2 ^ J := Nat.one_le_iff_ne_zero.2 (by positivity)
      refine (norm_far_tail_le (χ * χ'⁻¹)⁻¹ (by rw [hsre]; linarith [(hδ χ hχR).1, (hδ χ' hχ').2]) hM1).trans ?_
      rw [hfar, zeta98]
      have h2J : (0 : ℝ) < ((2 ^ J : ℕ) : ℝ) := by positivity
      have hle : ((2 ^ J : ℕ) : ℝ) ≤ (((Z + 1) * 2 ^ J : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_left (2 ^ J) (by omega : 0 < Z + 1)
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos h2J hle (by norm_num))
        (tsum_nonneg fun m => by positivity)
    have hT2 : ‖dualT (χ * χ'⁻¹)⁻¹ Z s‖ ≤
        ∑ j ∈ range J, ‖pv (tailBlock A J j) E χ ((δ χ : ℂ) + γ χ * I)‖ + far := by
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (le_of_eq ?_)) hfarle)
      exact sum_congr rfl hblock
    unfold J2
    rw [hk, ← hZ, norm_mul, norm_mul, ← hs]
    have hker' : ‖kW Λ (((-1 / 4 - 2 * δ χ : ℝ) : ℂ) + v * I)‖ *
        ‖Phi (χ * χ'⁻¹).primitiveCharacter q s‖ ≤ C₂ := by
      refine hker.trans ?_
      rw [hC₂, hK₀, hg]
      unfold pairCond at hΔ
      have : 0 ≤ 12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η * Λ ^ (-1 / 4 : ℝ) := by
        have := InghamDensity.KG_pos; have := CG_pos; have := EQ_pos q; positivity
      calc 12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η * Λ ^ (-1 / 4 : ℝ) *
            (((χ * χ'⁻¹).conductor : ℝ) * (1 + |γ χ - γ χ'|)) ^ (3 / 4 : ℝ) * ((1 + |v|) ^ 4)⁻¹
          ≤ 12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η * Λ ^ (-1 / 4 : ℝ) *
            P ^ (3 / 4 : ℝ) * ((1 + |v|) ^ 4)⁻¹ := by gcongr
        _ = _ := by ring
    exact mul_le_mul hker' hT2 (norm_nonneg _) hC₂0
  -- the blocks, by the product trick
  set W₂ := (R.card : ℝ) * τ * G * LSmax X * (Λ * q * (2 * T + 1) + 2 * N * P) with hW₂
  have hW₂0 : 0 ≤ W₂ := by have := LSmax_nonneg X; rw [hW₂]; positivity
  have hRk : (Rk.card : ℝ) ≤ R.card := by
    exact_mod_cast card_le_card ((filter_subset _ _).trans (erase_subset _ _))
  have hblk : ∀ j ∈ range J, C₂ * ∑ χ ∈ Rk, ‖pv (tailBlock A J j) E χ ((δ χ : ℂ) + γ χ * I)‖ ≤
      g * K₀ * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt W₂) := by
    intro j hj
    have hjJ : j + 1 ≤ J := Finset.mem_range.1 hj
    have hPY : P ≤ Λ * ((A * 2 ^ j : ℕ) : ℝ) := by
      have h1 := Zt_add_one hΛ k
      have h2 : ((Z : ℝ) + 1) ≤ ((A * 2 ^ j : ℕ) : ℝ) := by
        have hAc : ((A * 2 ^ j : ℕ) : ℝ) = ((Z : ℝ) + 1) * 2 ^ j := by rw [hA]; push_cast; ring
        rw [hAc]
        have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        have hZ0 : (0 : ℝ) ≤ Z := Nat.cast_nonneg Z
        nlinarith
      calc P = 2 ^ k := rfl
        _ ≤ Λ * ((Z : ℝ) + 1) := h1
        _ ≤ Λ * ((A * 2 ^ j : ℕ) : ℝ) := by gcongr
    have h := tail_block_le hη (fun χ hχ => hδ χ (hmem χ hχ).1) hT (fun χ hχ => hγ χ (hmem χ hχ).1) hS a hV
      (fun χ hχ => hbig χ (hmem χ hχ).1) χ' (hδ χ' hχ').1 (hδ χ' hχ').2 (γ χ') v hΛ hP0 hA1 hjJ hPY hX hN hXZ hτ hRk
    rw [hC₂]
    calc K₀ * (Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ)) * g * ∑ χ ∈ Rk, ‖pv (tailBlock A J j) E χ ((δ χ : ℂ) + γ χ * I)‖
        = K₀ * g * ((Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ)) *
          ∑ χ ∈ Rk, ‖pv (tailBlock A J j) E χ ((δ χ : ℂ) + γ χ * I)‖) := by ring
      _ ≤ K₀ * g * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt W₂) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = g * K₀ * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt W₂) := by ring
  -- the far tail
  have hΛM4 : Λ ^ (-1 / 4 : ℝ) ≤ M ^ (1 / 4 : ℝ) := by
    rw [show (-1 / 4 : ℝ) = -(1 / 4) by ring, Real.rpow_neg hΛ.le, ← Real.inv_rpow hΛ.le]
    exact Real.rpow_le_rpow (by positivity) hΛM (by norm_num)
  have hfarC : C₂ * (Rk.card * far) ≤ K₀ * (M ^ (1 / 4 : ℝ) * P ^ (3 / 4 : ℝ) * R.card * far) * g := by
    rw [hC₂]
    have h1 : Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ) ≤ M ^ (1 / 4 : ℝ) * P ^ (3 / 4 : ℝ) := by gcongr
    calc K₀ * (Λ ^ (-1 / 4 : ℝ) * P ^ (3 / 4 : ℝ)) * g * (Rk.card * far)
        ≤ K₀ * (M ^ (1 / 4 : ℝ) * P ^ (3 / 4 : ℝ)) * g * (R.card * far) := by gcongr
      _ = K₀ * (M ^ (1 / 4 : ℝ) * P ^ (3 / 4 : ℝ) * R.card * far) * g := by ring
  calc ∑ χ ∈ Rk, ‖J2 δ γ χ χ' Λ v‖
      ≤ ∑ χ ∈ Rk, C₂ * (∑ j ∈ range J, ‖pv (tailBlock A J j) E χ ((δ χ : ℂ) + γ χ * I)‖ + far) :=
        sum_le_sum hpt
    _ = ∑ j ∈ range J, C₂ * ∑ χ ∈ Rk, ‖pv (tailBlock A J j) E χ ((δ χ : ℂ) + γ χ * I)‖ +
          C₂ * (Rk.card * far) := by
        rw [← mul_sum, sum_add_distrib, sum_comm, sum_const, nsmul_eq_mul, mul_add, mul_sum]
    _ ≤ ∑ _j ∈ range J, g * K₀ * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt W₂) +
          K₀ * (M ^ (1 / 4 : ℝ) * P ^ (3 / 4 : ℝ) * R.card * far) * g :=
        add_le_add (sum_le_sum hblk) hfarC
    _ = g * K₀ * (J * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt W₂) +
          M ^ (1 / 4 : ℝ) * P ^ (3 / 4 : ℝ) * R.card * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98) := by
        rw [sum_const, card_range, nsmul_eq_mul, hfar]; ring

/-! ### All buckets at once, pointwise on the lines -/

lemma Zt_le_of {Λ M D : ℝ} (hΛ : 0 < Λ) (hΛM : Λ⁻¹ ≤ M) (hD1 : 1 ≤ D) {k : ℕ} (hk : k ≤ bkt D) :
    (Zt Λ k : ℝ) ≤ 2 * D * M := by
  have h1 := Zt_le hΛ k
  have h2 : (2 : ℝ) ^ k ≤ 2 * D := by
    calc (2 : ℝ) ^ k ≤ 2 ^ bkt D := pow_le_pow_right₀ (by norm_num) hk
      _ ≤ 2 * D := (bkt_spec hD1).2
  have hZ0 : (0 : ℝ) ≤ Zt Λ k := Nat.cast_nonneg _
  have hΛinv : 0 < Λ⁻¹ := inv_pos.2 hΛ
  calc (Zt Λ k : ℝ) = Λ⁻¹ * (Λ * Zt Λ k) := by field_simp
    _ ≤ M * (2 * D) := mul_le_mul hΛM (h1.trans h2) (by positivity) (by linarith)
    _ = 2 * D * M := by ring

/-- **Pointwise in `v`, all characters `χ ≠ χ′` at once**: with `B = bkt D` buckets and `J` tail blocks,
`Σ_{χ≠χ′}(|J₁| + |J₂|) ≤ (1 + |v|)^{−4}K₀(B + 1)((J + 2)X^ηV^{−1}(|R|τG·L(X)(Λq(2T + 1) + 4ND))^{1/2}
+ M^{1/4}(2D)^{3/4}|R|·2^{−J/16}ζ(9/8))` (`main_fiber`, `tail_fiber` in each bucket). -/
theorem pair_sum_pointwise [NeZero q] {R : Finset (DirichletCharacter ℂ q)} {δ γ : DirichletCharacter ℂ q → ℝ}
    {η : ℝ} (hη : η ≤ 1 / 16) (hδ : ∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ η) {T : ℝ} (hT : 0 ≤ T)
    (hγ : ∀ χ ∈ R, |γ χ| ≤ T) {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Icc 2 N) (a : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ χ ∈ R, V ≤ ‖pv S a χ ((δ χ : ℂ) + γ χ * I)‖) {χ' : DirichletCharacter ℂ q} (hχ' : χ' ∈ R)
    {Λ M D : ℝ} (hΛ : 0 < Λ) (hM : 1 ≤ M) (hΛM : Λ⁻¹ ≤ M) (hD1 : 1 ≤ D) (hD : ∀ χ ∈ R, pairCond χ χ' γ ≤ D)
    (v : ℝ) (J : ℕ) {X : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXD : (N : ℝ) * (2 * D * M + 1) * 2 ^ J ≤ X) {τ : ℝ}
    (hτ : ∀ n, n ≤ X → (n.divisors.card : ℝ) ≤ τ) :
    ∑ χ ∈ R.erase χ', (‖J1 δ γ χ χ' Λ v‖ + ‖J2 δ γ χ χ' Λ v‖) ≤
      ((1 + |v|) ^ 4)⁻¹ * (12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η) * (bkt D + 1) *
        ((J + 2) * ((X : ℝ) ^ η * V⁻¹ *
          Real.sqrt (R.card * τ * (∑ n ∈ S, ‖a n‖ ^ 2) * LSmax X * (Λ * q * (2 * T + 1) + 4 * N * D))) +
        M ^ (1 / 4 : ℝ) * (2 * D) ^ (3 / 4 : ℝ) * R.card * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98) := by
  classical
  set B := bkt D with hB
  set K₀ := 12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η with hK₀
  set g : ℝ := ((1 + |v|) ^ 4)⁻¹ with hg
  set G := ∑ n ∈ S, ‖a n‖ ^ 2 with hG
  have hK₀0 : 0 ≤ K₀ := by
    have := InghamDensity.KG_pos; have := CG_pos; have := EQ_pos q; rw [hK₀]; positivity
  have hg0 : 0 ≤ g := by positivity
  have hτ0 : 0 ≤ τ := (Nat.cast_nonneg _).trans (hτ 1 hX)
  have hG0 : 0 ≤ G := sum_nonneg fun _ _ => by positivity
  set W := (R.card : ℝ) * τ * G * LSmax X * (Λ * q * (2 * T + 1) + 4 * N * D) with hW
  have hW0 : 0 ≤ W := by have := LSmax_nonneg X; rw [hW]; positivity
  set far := M ^ (1 / 4 : ℝ) * (2 * D) ^ (3 / 4 : ℝ) * R.card * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98
    with hfar
  have hfar0 : 0 ≤ far := by have := zeta98_nonneg; rw [hfar]; positivity
  have hmaps : ∀ χ ∈ R.erase χ', bkt (pairCond χ χ' γ) ∈ range (B + 1) := fun χ hχ =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (bkt_mono (hD χ (mem_erase.1 hχ).2)))
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hbk : ∀ k ∈ range (B + 1),
      ∑ χ ∈ (R.erase χ').filter (fun χ => bkt (pairCond χ χ' γ) = k), (‖J1 δ γ χ χ' Λ v‖ + ‖J2 δ γ χ χ' Λ v‖) ≤
        g * K₀ * ((J + 2) * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt W) + far) := by
    intro k hk
    have hkB : k ≤ B := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hZ := Zt_le_of hΛ hΛM hD1 hkB
    have hP2 : (2 : ℝ) ^ k ≤ 2 * D := (pow_le_pow_right₀ (by norm_num) hkB).trans (bkt_spec hD1).2
    have hXZt : N * ((Zt Λ k + 1) * 2 ^ J) ≤ X := by
      have : ((N * ((Zt Λ k + 1) * 2 ^ J) : ℕ) : ℝ) ≤ X := by
        push_cast
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        calc (N : ℝ) * ((((Zt Λ k : ℕ) : ℝ) + 1) * 2 ^ J) = (N : ℝ) * (((Zt Λ k : ℕ) : ℝ) + 1) * 2 ^ J := by
              ring
          _ ≤ (N : ℝ) * (2 * D * M + 1) * 2 ^ J := by gcongr
          _ ≤ X := hXD
      exact_mod_cast this
    have hXZ : N * Zt Λ k ≤ X :=
      le_trans (Nat.mul_le_mul_left N (le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_right _ (by positivity))))
        hXZt
    have h1 := main_fiber hη hδ hT hγ hS a hV hbig hχ' hΛ hM hΛM hD1 hD v k hX hN hXZ hτ
    have h2 := tail_fiber hη hδ hT hγ hS a hV hbig hχ' hΛ hM hΛM hD1 hD v k J hX hN hXZt hτ
    rw [sum_add_distrib]
    -- the bucket's bounds against the uniform ones
    have hW1 : Real.sqrt (R.card * τ * G * LSmax X * (Λ * q * (2 * T + 1) + N * 2 ^ k)) ≤ Real.sqrt W := by
      apply Real.sqrt_le_sqrt
      rw [hW]
      have := LSmax_nonneg X
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have : (N : ℝ) * 2 ^ k ≤ 4 * N * D := by nlinarith
      gcongr
    have hW2 : Real.sqrt (R.card * τ * G * LSmax X * (Λ * q * (2 * T + 1) + 2 * N * 2 ^ k)) ≤ Real.sqrt W := by
      apply Real.sqrt_le_sqrt
      rw [hW]
      have := LSmax_nonneg X
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have : 2 * (N : ℝ) * 2 ^ k ≤ 4 * N * D := by nlinarith
      gcongr
    have hfar2 : M ^ (1 / 4 : ℝ) * ((2 : ℝ) ^ k) ^ (3 / 4 : ℝ) * R.card * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
        zeta98 ≤ far := by
      rw [hfar]
      have := zeta98_nonneg
      gcongr
    have hXV : 0 ≤ (X : ℝ) ^ η * V⁻¹ := by positivity
    calc ∑ χ ∈ (R.erase χ').filter (fun χ => bkt (pairCond χ χ' γ) = k), ‖J1 δ γ χ χ' Λ v‖ +
          ∑ χ ∈ (R.erase χ').filter (fun χ => bkt (pairCond χ χ' γ) = k), ‖J2 δ γ χ χ' Λ v‖
        ≤ g * K₀ * 2 * (X : ℝ) ^ η * V⁻¹ *
            Real.sqrt (R.card * τ * G * LSmax X * (Λ * q * (2 * T + 1) + N * 2 ^ k)) +
          g * K₀ * (J * ((X : ℝ) ^ η * V⁻¹ *
            Real.sqrt (R.card * τ * G * LSmax X * (Λ * q * (2 * T + 1) + 2 * N * 2 ^ k))) +
            M ^ (1 / 4 : ℝ) * ((2 : ℝ) ^ k) ^ (3 / 4 : ℝ) * R.card * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
              zeta98) := add_le_add h1 h2
      _ ≤ g * K₀ * 2 * (X : ℝ) ^ η * V⁻¹ * Real.sqrt W +
          g * K₀ * (J * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt W) + far) := by
        gcongr
      _ = g * K₀ * ((J + 2) * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt W) + far) := by ring
  calc ∑ k ∈ range (B + 1), ∑ χ ∈ (R.erase χ').filter (fun χ => bkt (pairCond χ χ' γ) = k),
        (‖J1 δ γ χ χ' Λ v‖ + ‖J2 δ γ χ χ' Λ v‖)
      ≤ ∑ _k ∈ range (B + 1), g * K₀ * ((J + 2) * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt W) + far) := sum_le_sum hbk
    _ = g * K₀ * (B + 1) * ((J + 2) * ((X : ℝ) ^ η * V⁻¹ * Real.sqrt W) + far) := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

end LinnikReflect

#print axioms LinnikReflect.main_fiber
#print axioms LinnikReflect.tail_fiber
#print axioms LinnikReflect.pair_sum_pointwise
