/-
# Round 527, part 1: one block and one bin by round 526's large-values estimate, and Ingham's method at `c = 1/10`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`block_bin_hux`). Let `F(χ, s) = Σ_{P<j≤2P}c_jχ(j)j^{−s}` with `|c_j| ≤ d(j)`, and let `R` be a set of
characters mod `q` with `|F(χ, β_χ + iγ_χ)| ≥ V > 0` for every `χ ∈ R`, where `0 ≤ σ_b ≤ β_χ ≤ σ_b + η`, `η ≤ 1/16`
and `|γ_χ| ≤ T`. For every `m ≥ 1`, with `Λ = (2P)^m`, `X ≥ Λ(2q²(1 + 2T) + 1)2^J` and `d(n) ≤ τ` for `n ≤ X`,
`|R| ≤ 2·8·2^m·G_mΛ/V^{2m} + (8·2^m)²4^{ω(q)}G_m³A²/V^{6m}`, where `G_m = G_m(σ_b)` is round 525's bound for the
mass of `F^m` at `σ_b` (`LinnikHuxley.mass_pow_le`) and `A = hxA` is the off-diagonal factor of round 526's
`huxley_large_values` at `U = N = Λ`.

Plain statement (`count_middle_c10`). Given the fourth moment `Σ|L(½ + it_χ, χ)|⁴ ≤ C₄(q(T + 2))^{1+ε}` over sets of
characters `χ ≠ 1` (round 524), for `7/12 ≤ σ ≤ 3/4` and `T ≥ 2` at most `Mc(log Q)¹⁰Q^{(12/5+4ε)(1−σ)}`,
`Q = q(T + 6)`, characters `χ ≠ 1` mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.

* `wW_ge_pow`: the weight `e^{−n/U} − e^{−2n/U}` is at least `2^{−m}/8` on `(P^m, (2P)^m]` at `U = (2P)^m`.
* `block_bin_hux`: `huxley_large_values` for `F^m` normalised at `σ_b` (`pv_powCoσ`, `mass_powCoσ`).
* `bound_class2_c10`, `count_middle_c10`: round 524's `count_nontrivial_ingham` at `c = 1/10`, `δ = 1/12`, so
  `Y = Q^{6/5}` and the polynomial class carries `Q^{(2+4c)(1−σ)} = Q^{(12/5)(1−σ)}`; the integral class carries
  `Q^{(8/5)(½−σ)+1+ε/3}`, and `(8/5)(½ − σ) + 1 ≤ (12/5)(1 − σ)` exactly when `σ ≤ 3/4`.
-/

import LinnikLargeValues

open Complex Real Finset MeasureTheory Filter Topology

noncomputable section

namespace LinnikTwelve

open InghamDensity Linnik LinnikDetect LinnikHybrid LinnikDensity LinnikIngham DirichletCharacter ShortWeil
  DirMean LinnikPower LinnikOffDiag LinnikHuxley LinnikReflect

variable {q : ℕ}

/-! ### One block and one bin of the polynomial class, by Huxley's estimate -/

/-- `e^{−x} − e^{−2x} ≥ x/8` for `0 ≤ x ≤ 1`. -/
lemma exp_sub_exp_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x / 8 ≤ Real.exp (-x) - Real.exp (-(2 * x)) := by
  have h1 : Real.exp (-x) * (1 + x) ≤ 1 := by
    have := Real.add_one_le_exp x
    calc Real.exp (-x) * (1 + x) ≤ Real.exp (-x) * Real.exp x := by gcongr; linarith
      _ = 1 := by rw [← Real.exp_add]; simp
  have h2 : Real.exp (-1) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
  have h3 : 1 / 3 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have e2 : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by rw [← Real.exp_add]; ring_nf
  rw [e2]
  have hE : 0 < Real.exp (-x) := Real.exp_pos _
  -- `1 − e^{−x} ≥ x/(1 + x) ≥ x/2`
  have h4 : x / 2 ≤ 1 - Real.exp (-x) := by
    have : Real.exp (-x) ≤ 1 / (1 + x) := by rw [le_div_iff₀ (by linarith)]; linarith
    have h5 : 1 / (1 + x) ≤ 1 - x / 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  nlinarith

/-- **The weight on the support of the power**: `e^{−n/U} − e^{−2n/U} ≥ 2^{−m}/8` for `P^m < n ≤ U = (2P)^m`. -/
lemma wW_ge_pow {P m n : ℕ} (hP : 1 ≤ P) (hn : n ∈ Ioc (P ^ m) ((2 * P) ^ m)) :
    (2 : ℝ)⁻¹ ^ m / 8 ≤ wW (((2 * P : ℕ) : ℝ) ^ m) n := by
  obtain ⟨hn1, hn2⟩ := mem_Ioc.1 hn
  set U : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hU
  have hU0 : 0 < U := by
    rw [hU]; exact pow_pos (by exact_mod_cast (by omega : 0 < 2 * P)) m
  have hn0 : n ≠ 0 := by omega
  have hnU : (n : ℝ) ≤ U := by rw [hU]; exact_mod_cast hn2
  have hlow : (2 : ℝ)⁻¹ ^ m ≤ (n : ℝ) / U := by
    rw [le_div_iff₀ hU0, hU]
    have h1 : ((P ^ m : ℕ) : ℝ) < n := by exact_mod_cast hn1
    have e : (2 : ℝ)⁻¹ ^ m * ((2 * P : ℕ) : ℝ) ^ m = ((P ^ m : ℕ) : ℝ) := by
      push_cast; rw [← mul_pow]; congr 1; field_simp
    linarith
  have hx1 : (n : ℝ) / U ≤ 1 := by rw [div_le_one hU0]; exact hnU
  have hx0 : 0 ≤ (n : ℝ) / U := by positivity
  have hw := exp_sub_exp_ge hx0 hx1
  unfold wW
  rw [ite_eq_right hn0]
  have e : (n : ℝ) / (U / 2) = 2 * ((n : ℝ) / U) := by field_simp
  rw [e]
  linarith

/-- The coefficients of `F^m` at the line `σ_b`: `a_n = c^{(m)}_n n^{−σ_b}`. -/
def powCoσ (S : Finset ℕ) (c : ℕ → ℂ) (m : ℕ) (σb : ℝ) (n : ℕ) : ℂ :=
  powCo S c m n * (((n : ℝ) ^ (-σb) : ℝ) : ℂ)

lemma pv_powCoσ (S : Finset ℕ) (c : ℕ → ℂ) (m : ℕ) (σb : ℝ) (χ : DirichletCharacter ℂ q) {P : ℕ}
    (hS : S ⊆ Ioc P (2 * P)) (hm : 1 ≤ m) (δ γ : ℝ) :
    pv (powSupp S m) (powCoσ S c m σb) χ ((δ : ℂ) + γ * I) = pv S c χ (((σb + δ : ℝ) : ℂ) + γ * I) ^ m := by
  rw [pv_pow]
  unfold pv powCoσ
  refine sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (mem_Ioc.1 (powSupp_sub hS hm hn)).1; omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hc : (((n : ℝ) ^ (-σb) : ℝ) : ℂ) = (n : ℂ) ^ (-(σb : ℂ)) := by
    rw [Complex.ofReal_cpow hnpos.le]; push_cast; ring_nf
  rw [hc]
  have hn0' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have e : (n : ℂ) ^ (-(σb : ℂ)) * (n : ℂ) ^ (-((δ : ℂ) + γ * I)) = (n : ℂ) ^ (-(((σb + δ : ℝ) : ℂ) + γ * I)) := by
    rw [← Complex.cpow_add _ _ hn0']; congr 1; push_cast; ring
  calc powCo S c m n * (n : ℂ) ^ (-(σb : ℂ)) * χ n * (n : ℂ) ^ (-((δ : ℂ) + γ * I))
      = powCo S c m n * χ n * ((n : ℂ) ^ (-(σb : ℂ)) * (n : ℂ) ^ (-((δ : ℂ) + γ * I))) := by ring
    _ = powCo S c m n * χ n * (n : ℂ) ^ (-(((σb + δ : ℝ) : ℂ) + γ * I)) := by rw [e]

lemma mass_powCoσ (S : Finset ℕ) (c : ℕ → ℂ) (m : ℕ) (σb : ℝ) :
    ∑ n ∈ powSupp S m, ‖powCoσ S c m σb n‖ ^ 2 = ∑ n ∈ powSupp S m, ‖powCo S c m n‖ ^ 2 * ((n : ℝ) ^ (-σb)) ^ 2 := by
  refine sum_congr rfl fun n _ => ?_
  unfold powCoσ
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]

/-- The off-diagonal factor `A = A₁ + A₂(qN)^{1/2}` of `huxley_large_values`. -/
def hxA (q : ℕ) (τ η T U N : ℝ) (X J : ℕ) : ℝ :=
  (12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η) *
      (bkt (q * (1 + 2 * T)) + 1) * ((J + 2) * ((X : ℝ) ^ η *
        Real.sqrt (τ * LSmax X * (U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T)))))) +
    (12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η) *
      (bkt (q * (1 + 2 * T)) + 1) * ((q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) *
        ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98) * Real.sqrt (q * N)

lemma hxA_nonneg (q : ℕ) [NeZero q] {τ η T U N : ℝ} (hT : 0 ≤ T) (X J : ℕ) :
    0 ≤ hxA q τ η T U N X J := by
  unfold hxA
  have := InghamDensity.KG_pos; have := CG_pos; have := EQ_pos q; have := zeta98_nonneg
  have := LSmax_nonneg X
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  positivity

/-- **One dyadic block and one bin, by Huxley's estimate**: characters with `|F(χ, β_χ + iγ_χ)| ≥ V > 0` for a block
`F` on `(P, 2P]` with `|c_j| ≤ d(j)`, `σ_b ≤ β_χ ≤ σ_b + η`, `η ≤ 1/16`, `|γ_χ| ≤ T`, number at most
`2c₀⁻¹G_mΛ/V^{2m} + c₀⁻²4^{ω(q)}G_m³A²/V^{6m}` with `Λ = (2P)^m`, `c₀ = 2^{−m}/8` (`wW_ge_pow`), `G_m = G_m(σ_b)` the
mass of the power (`mass_pow_le`) and `A = hxA` at `U = N = Λ`, for `X ≥ Λ(2q²(1 + 2T) + 1)2^J` with `d(n) ≤ τ` for
`n ≤ X`: `huxley_large_values` for `F^m` normalised at `σ_b`. -/
theorem block_bin_hux [NeZero q] {R : Finset (DirichletCharacter ℂ q)} {Sk : Finset ℕ} {P : ℕ} (hP : 1 ≤ P)
    (hS : Sk ⊆ Ioc P (2 * P)) {c : ℕ → ℂ} (hc : ∀ j ∈ Sk, ‖c j‖ ≤ (j.divisors.card : ℝ)) {m : ℕ} (hm : 1 ≤ m)
    {σb η : ℝ} (hσb : 0 ≤ σb) (hη : η ≤ 1 / 16) (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ R, σb ≤ β χ ∧ β χ ≤ σb + η) {T : ℝ} (hT : 0 ≤ T) (hγ : ∀ χ ∈ R, |γ χ| ≤ T) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ χ ∈ R, V ≤ ‖pv Sk c χ ((β χ : ℂ) + γ χ * I)‖) {εd : ℝ} (hεd : 0 < εd) (hεd1 : εd ≤ 1) (J : ℕ)
    {X : ℕ} (hX : 1 ≤ X) (hXD : (((2 * P) ^ m : ℕ) : ℝ) * (2 * (q * (1 + 2 * T)) * q + 1) * 2 ^ J ≤ X) {τ : ℝ}
    (hτ : ∀ n, n ≤ X → (n.divisors.card : ℝ) ≤ τ) :
    (R.card : ℝ) ≤ 2 * (8 * 2 ^ m) * Gm εd P m σb * ((2 * P : ℕ) : ℝ) ^ m / (V ^ m) ^ 2 +
      (8 * 2 ^ m) ^ 2 * (q.primeFactors.powerset.card : ℝ) ^ 2 * Gm εd P m σb ^ 3 *
        hxA q τ η T (((2 * P : ℕ) : ℝ) ^ m) ((2 * P) ^ m : ℕ) X J ^ 2 / (V ^ m) ^ 6 := by
  classical
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛ
  have h2P : (2 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * P)
  have hΛ2 : 2 ≤ Λ := by
    rw [hΛ]
    calc (2 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := h2P
      _ = ((2 * P : ℕ) : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ ((2 * P : ℕ) : ℝ) ^ m := pow_le_pow_right₀ (by linarith) hm
  have hsub := powSupp_sub hS hm
  have hS2 : powSupp Sk m ⊆ Icc 2 ((2 * P) ^ m) := fun n hn => by
    have h := mem_Ioc.1 (hsub hn)
    have : 1 ≤ P ^ m := Nat.one_le_pow _ _ (by omega)
    exact mem_Icc.2 ⟨by omega, h.2⟩
  have hN1 : 1 ≤ (2 * P) ^ m := Nat.one_le_pow _ _ (by omega)
  set c₀ : ℝ := (2 : ℝ)⁻¹ ^ m / 8 with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  have hSW : ∀ n ∈ powSupp Sk m, c₀ ≤ wW Λ n := fun n hn => wW_ge_pow hP (hsub hn)
  set δ : DirichletCharacter ℂ q → ℝ := fun χ => β χ - σb with hδ
  have hδR : ∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ η := fun χ hχ => ⟨by simp [hδ]; linarith [(hβ χ hχ).1],
    by simp [hδ]; linarith [(hβ χ hχ).2]⟩
  have hbig' : ∀ χ ∈ R, V ^ m ≤ ‖pv (powSupp Sk m) (powCoσ Sk c m σb) χ ((δ χ : ℂ) + γ χ * I)‖ := by
    intro χ hχ
    rw [pv_powCoσ Sk c m σb χ hS hm, norm_pow]
    have e : σb + δ χ = β χ := by simp [hδ]
    rw [e]
    exact pow_le_pow_left₀ hV.le (hbig χ hχ) m
  have hH := huxley_large_values (hη.trans le_rfl) hδR hT hγ hN1 hS2 (powCoσ Sk c m σb) (by positivity) hbig'
    hΛ2 hc₀0 hSW J hX (by push_cast at hXD ⊢; exact hXD) hτ
  -- the mass of the power
  have hmass : ∑ n ∈ powSupp Sk m, ‖powCoσ Sk c m σb n‖ ^ 2 ≤ Gm εd P m σb := by
    rw [mass_powCoσ]; exact mass_pow_le hP hS hc hm hσb hεd hεd1
  have hG0 : 0 ≤ ∑ n ∈ powSupp Sk m, ‖powCoσ Sk c m σb n‖ ^ 2 := sum_nonneg fun _ _ => by positivity
  have hτ0 : 0 ≤ τ := (Nat.cast_nonneg _).trans (hτ 1 hX)
  have hA0 := hxA_nonneg q (τ := τ) (η := η) (U := Λ) (N := ((2 * P) ^ m : ℕ)) hT X J
  have hc₀inv : c₀⁻¹ = 8 * 2 ^ m := by rw [hc₀, div_eq_mul_inv, mul_inv, inv_pow, inv_inv, inv_inv]; ring
  have hVm : 0 < V ^ m := by positivity
  refine hH.trans ?_
  rw [hc₀inv]
  -- monotonicity in the mass
  have hA : hxA q τ η T Λ ((2 * P) ^ m : ℕ) X J = (12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) *
      (q * (1 + 2 * T)) ^ η) * (bkt (q * (1 + 2 * T)) + 1) * ((J + 2) * ((X : ℝ) ^ η *
        Real.sqrt (τ * LSmax X * (Λ * q * (2 * T + 1) + 4 * ((2 * P) ^ m : ℕ) * (q * (1 + 2 * T)))))) +
      (12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η) *
        (bkt (q * (1 + 2 * T)) + 1) * ((q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) *
          ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98) * Real.sqrt (q * ((2 * P) ^ m : ℕ)) := rfl
  rw [← hA]
  have h2m : (0 : ℝ) ≤ 8 * 2 ^ m := by positivity
  gcongr

/-! ### Ingham's method at `c = 1/10` below `σ = 3/4` -/

/-- **The integral class at `X = ⌊Q⌋`, `Y = Q^{6/5}`, `λ = Q^{(2/5)(½−σ)+ε/3}`**, for `σ ≤ 3/4` and `q(T + 2) ≤ Q`: at
most `(3200 KG/δ₀ + (KG/δ₀)²C₄)(log Q)¹⁰ Q^{(12/5+4ε)(1−σ)}`, `δ₀ = 1/12` (round 524's `bound_class2_ingham` at
`c = 1/10`). Both terms carry `Q^{(8/5)(½−σ)+1+ε/3}`, and `(8/5)(½ − σ) + 1 ≤ (12/5)(1 − σ)` exactly when `σ ≤ 3/4`. -/
theorem bound_class2_c10 {ε C₄ σ T Q : ℝ} (hε0 : 0 ≤ ε) (hC₄ : 0 ≤ C₄) (hσ1 : σ ≤ 3 / 4) (hQ : 8 ≤ Q)
    (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q) :
    2 * (KG * (Yw (1 / 10) Q) ^ (1 / 2 - σ) / (1 / 12)) * Q ^ (2 / 5 * (1 / 2 - σ) + ε / 3) *
        (MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q))) +
      (KG * (Yw (1 / 10) Q) ^ (1 / 2 - σ) / (1 / 12)) ^ 2 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε)) /
        (Q ^ (2 / 5 * (1 / 2 - σ) + ε / 3)) ^ 2
      ≤ (3200 * (KG / (1 / 12)) + (KG / (1 / 12)) ^ 2 * C₄) * Real.log Q ^ 10 *
        Q ^ ((12 / 5 + 4 * ε) * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hKG := KG_pos
  set K := KG / (1 / 12) with hK
  have hK0 : 0 < K := by positivity
  set a := 6 / 5 * (1 / 2 - σ) with ha
  set e := 2 / 5 * (1 / 2 - σ) + ε / 3 with he
  set E₂ := 8 / 5 * (1 / 2 - σ) + 1 + ε / 3 with hE₂
  set E := (12 / 5 + 4 * ε) * (1 - σ) with hE
  have hY : (Yw (1 / 10) Q) ^ (1 / 2 - σ) = Q ^ a := by
    unfold Yw; rw [← Real.rpow_mul hQ0.le]; congr 1; rw [ha]; ring
  have hA : KG * (Yw (1 / 10) Q) ^ (1 / 2 - σ) / (1 / 12) = K * Q ^ a := by rw [hY, hK]; ring
  rw [hA]
  have hMV := bound_MV hQ
  have hMV0 : 0 ≤ MV (Xw Q) := by
    unfold MV; have := Real.log_nonneg (by exact_mod_cast Xw_one hQ : (1 : ℝ) ≤ Xw Q); positivity
  have hXQ := Xw_le hQ
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hW : (q : ℝ) * (T + 1) + (Xw Q) ≤ 2 * Q := by nlinarith
  have hW0 : 0 ≤ (q : ℝ) * (T + 1) + (Xw Q) := by positivity
  have hL2 : 2 ≤ Real.log Q := log_ge_two hQ
  have hM1 : MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q)) ≤ 1600 * Real.log Q ^ 5 * Q := by
    calc MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q)) ≤ (800 * Real.log Q ^ 5) * (2 * Q) :=
          mul_le_mul hMV hW hW0 (by positivity)
      _ = 1600 * Real.log Q ^ 5 * Q := by ring
  have hM2 : C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε) ≤ C₄ * Q ^ (1 + ε) := by
    gcongr
  have hQa : Q ^ a * Q ^ e * Q = Q ^ E₂ := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add_one hQ0.ne']; congr 1; rw [ha, he, hE₂]; ring
  have hQb : (Q ^ a) ^ 2 * Q ^ (1 + ε) / (Q ^ e) ^ 2 = Q ^ E₂ := by
    rw [← Real.rpow_natCast (Q ^ a), ← Real.rpow_natCast (Q ^ e), ← Real.rpow_mul hQ0.le,
      ← Real.rpow_mul hQ0.le, ← Real.rpow_add hQ0, ← Real.rpow_sub hQ0]
    congr 1; rw [ha, he, hE₂]; push_cast; ring
  have hEE : Q ^ E₂ ≤ Q ^ E := by
    refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
    rw [hE₂, hE]
    nlinarith
  have hL5 : Real.log Q ^ 5 ≤ Real.log Q ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hL10 : 1 ≤ Real.log Q ^ 10 := one_le_pow₀ (by linarith)
  have hQe : 0 < Q ^ e := Real.rpow_pos_of_pos hQ0 e
  have hQE₂ : 0 ≤ Q ^ E₂ := by positivity
  have hpow2 : 0 ≤ (Q ^ a) ^ 2 := by positivity
  calc 2 * (K * Q ^ a) * Q ^ e * (MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q))) +
        (K * Q ^ a) ^ 2 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε)) / (Q ^ e) ^ 2
      ≤ 2 * (K * Q ^ a) * Q ^ e * (1600 * Real.log Q ^ 5 * Q) +
        (K * Q ^ a) ^ 2 * (C₄ * Q ^ (1 + ε)) / (Q ^ e) ^ 2 := by gcongr
    _ = 3200 * K * Real.log Q ^ 5 * (Q ^ a * Q ^ e * Q) +
        K ^ 2 * C₄ * ((Q ^ a) ^ 2 * Q ^ (1 + ε) / (Q ^ e) ^ 2) := by ring
    _ = (3200 * K * Real.log Q ^ 5 + K ^ 2 * C₄) * Q ^ E₂ := by rw [hQa, hQb]; ring
    _ ≤ (3200 * K * Real.log Q ^ 10 + K ^ 2 * C₄ * Real.log Q ^ 10) * Q ^ E := by
        have h1 : 3200 * K * Real.log Q ^ 5 ≤ 3200 * K * Real.log Q ^ 10 :=
          mul_le_mul_of_nonneg_left hL5 (by positivity)
        have h2 : K ^ 2 * C₄ ≤ K ^ 2 * C₄ * Real.log Q ^ 10 := le_mul_of_one_le_right (by positivity) hL10
        exact mul_le_mul (add_le_add h1 h2) hEE hQE₂ (by positivity)
    _ = (3200 * K + K ^ 2 * C₄) * Real.log Q ^ 10 * Q ^ E := by ring

open scoped Classical in
/-- **The range `7/12 ≤ σ ≤ 3/4` at `Q = q(T + 6)`**: at most `Mc(log Q)¹⁰Q^{(12/5+4ε)(1−σ)}` characters `χ ≠ 1`
have a zero in `Re s ≥ σ`, `|Im s| ≤ T`, with `Mc = 16·13³·96·9⁶·71 + 3200 KG/δ₀ + (KG/δ₀)²C₄`, `δ₀ = 1/12`: round
524's `count_nontrivial_ingham` at `c = 1/10` (so `Y = Q^{6/5}` and round 521's polynomial class carries
`Q^{(2+4c)(1−σ)} = Q^{(12/5)(1−σ)}`, `bound_class1`) and `λ = Q^{(2/5)(½−σ)+ε/3}` (`bound_class2_c10`). -/
theorem count_middle_c10 [NeZero q] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {C₄ : ℝ} (hC₄0 : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε))
    {σ T : ℝ} (hmid : 7 / 12 ≤ σ) (hle : σ ≤ 3 / 4) (hT : 2 ≤ T) :
    ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / (1 / 12)) + (KG / (1 / 12)) ^ 2 * C₄)) *
        Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ ((12 / 5 + 4 * ε) * (1 - σ)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ8 : 8 ≤ (q : ℝ) * (T + 6) := by nlinarith
  have hQ0 : 0 < (q : ℝ) * (T + 6) := by linarith
  have hQ1 : 1 ≤ (q : ℝ) * (T + 6) := by linarith
  have hlam0 : 0 < ((q : ℝ) * (T + 6)) ^ (2 / 5 * (1 / 2 - σ) + ε / 3) := Real.rpow_pos_of_pos hQ0 _
  have hcount := count_nontrivial_ingham hε.le hε1 hC₄0 h4 (c := 1 / 10) (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 12) (by linarith : 1 / 2 + 1 / 12 ≤ σ) (by linarith) hT
    (le_refl ((q : ℝ) * (T + 6))) hlam0
  have hb1 := bound_class1 (c := 1 / 10) (σ := σ) (by norm_num) (by norm_num) (by linarith) (by linarith) hQ8
  have hb2 := bound_class2_c10 (q := q) hε.le hC₄0 hle hQ8 (by linarith)
    (by nlinarith : (q : ℝ) * (T + 2) ≤ (q : ℝ) * (T + 6))
  have hE1' : ((q : ℝ) * (T + 6)) ^ ((2 + 4 * (1 / 10 : ℝ)) * (1 - σ)) ≤
      ((q : ℝ) * (T + 6)) ^ ((12 / 5 + 4 * ε) * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by nlinarith)
  have hL10 : 0 ≤ Real.log ((q : ℝ) * (T + 6)) ^ 10 := by
    have := log_ge_two hQ8; positivity
  have hc : (0 : ℝ) ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 := by norm_num
  refine hcount.trans ((add_le_add hb1 hb2).trans ?_)
  have h1 : 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log ((q : ℝ) * (T + 6)) ^ 10 *
      ((q : ℝ) * (T + 6)) ^ ((2 + 4 * (1 / 10 : ℝ)) * (1 - σ)) ≤
      16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log ((q : ℝ) * (T + 6)) ^ 10 *
      ((q : ℝ) * (T + 6)) ^ ((12 / 5 + 4 * ε) * (1 - σ)) :=
    mul_le_mul_of_nonneg_left hE1' (mul_nonneg hc hL10)
  linarith

end LinnikTwelve

#print axioms LinnikTwelve.wW_ge_pow
#print axioms LinnikTwelve.block_bin_hux
#print axioms LinnikTwelve.bound_class2_c10
#print axioms LinnikTwelve.count_middle_c10
