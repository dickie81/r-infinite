/-
# Round 524, part 2: the hybrid fourth moment of `L(½ + it, χ)` over the characters mod `q`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every `0 < ε ≤ 1` there is `C` such that `Σ_{χ ∈ R} |L(½ + it_χ, χ)|⁴ ≤ C(q(T + 2))^{1+ε}` for
every modulus `q ≥ 1`, every set `R` of characters `χ ≠ 1` mod `q` and every choice of one point `|t_χ| ≤ T` per
character (`fourth_moment`). This is the hybrid fourth moment (one ordinate per character) behind Ingham's density
estimate over the characters mod `q` (`LinnikIngham.lean`).

* `norm_LFunction_four_le`: `|L(½ + it, χ)|⁴ ≤ 2|D(½ + it, χ)|² + 2|D(½ − it, χ⁻¹)|²` for primitive `χ ≠ 1`, with
  `D = J/γ_χ²` (`afeD`), from `LinnikGamma.afe` with `|ε(χ)| = 1` and `|γ_χ(½ − it)| = |γ_χ(½ + it)|`.
* `Pd`, `Tl`: `L(z, χ)² = P(z) + T(z)` with `P(z) = Σ_{n ≤ N₀} d(n)χ(n)n^{−z}`; `|T(z)| ≤ 2N₀^{3−Re z}` on `Re z ≥ 3`
  (`norm_Tl_le`), from `d(n) ≤ n`.
* `sum_norm_Pd_sq_le`: `Σ_χ |P(½ + c₀ + ix_χ)|²` at one point per character, by the dyadic blocks of `P`, round 521's
  `LinnikHybrid.large_values_chars_off` and round 518's `InghamDensity.block_mass_le_b`.
* `afeJ_split`: `J = (1/2πi)∫_{(c₀)} γ²P N^w e^{w²}dw/w + (1/2πi)∫_{(c₁)} γ²T N^w e^{w²}dw/w` for `0 < c₀ ≤ 2 ≤ c₁`
  (round 472's `SmoothPerron.verticalIntegral_shift`, no pole crossed). On the line `Re w = c > 0` the integrand is at
  most `KG2(c, t)|M(½ + it + w)|W_{c+1/2}(v)` (`norm_GG_le`), with `W_a(v) = (1 + |v|)^a e^{π|v|/2}e^{−v²}` and
  `KG2 = (e^{KR(c)}(1 + |t|)^{c/2}|γ_χ(½ + it)|)²e^{c²}N^c/c`, from `LinnikGamma.norm_gammaFactor_ratio_le`.
* `sum_norm_DP_sq_le`: Cauchy–Schwarz in `v` against `W` (`sq_integral_mul_le`), then `sum_norm_Pd_sq_le` at the
  points `t_χ + v`; `norm_DT_le`: `norm_Tl_le` on `Re z = ½ + c₁`.
* `sum_norm_afeD_sq_le`: `Σ_χ |D(½ + it_χ, χ)|² ≤ C(N(T + 2))^{1+ε}` at `c₀ = ε/8`, `c₁ = 40/ε`,
  `N₀ = ⌈(N(T + 2))^{1+ε/8}⌉`; `fourth_moment_primitive`: the same for `|L|⁴` over primitive characters, with the
  inverse characters at `−t_χ` for the second term.
* `fourth_moment`: each `χ ≠ 1` mod `q` against its primitive character `χ*` mod the conductor `N | q`
  (`norm_LFunction_le_toPrim`, Mathlib's `LFunction_changeLevel`, round 522's `LinnikSubconvex.prod_primeFactors_le`),
  grouped by conductor (`χ ↦ χ*` is injective on each group), and `Σ_{N | q} N^{1+ε} ≤ ζ(1 + ε)q^{1+ε}`
  (`sum_divisors_rpow_le`).
-/
import LinnikAFE

open Complex Real Set MeasureTheory DirichletCharacter Finset
open scoped LSeries.notation

noncomputable section

namespace LinnikFourth

open LinnikGamma DirMean ShortWeil InghamDensity LinnikHybrid

/-! ### From the approximate functional equation to `|L|²` -/

/-- `D(s, χ) = J(s, χ)/γ_χ(s)²`. -/
def afeD {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := afeJ χ s / gammaFactor χ s ^ 2

lemma gammaFactor_inv {N : ℕ} (χ : DirichletCharacter ℂ N) (z : ℂ) : gammaFactor χ⁻¹ z = gammaFactor χ z := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def, ((LinnikFE.even_inv_iff χ).2 h).gammaFactor_def]
  · rw [h.gammaFactor_def, ((LinnikFE.odd_inv_iff χ).2 h).gammaFactor_def]

lemma norm_Gammaℝ_conj (z : ℂ) : ‖Gammaℝ (starRingEnd ℂ z)‖ = ‖Gammaℝ z‖ := by
  rw [Gammaℝ_def, Gammaℝ_def, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 1
  · simp
  · rw [show starRingEnd ℂ z / 2 = starRingEnd ℂ (z / 2) by rw [map_div₀, map_ofNat], Complex.Gamma_conj,
      Complex.norm_conj]

/-- On the critical line `|γ_χ(1 − s)| = |γ_χ(s)|`. -/
lemma norm_gammaFactor_one_sub {N : ℕ} (χ : DirichletCharacter ℂ N) (t : ℝ) :
    ‖gammaFactor χ (1 - (1 / 2 + t * I))‖ = ‖gammaFactor χ (1 / 2 + t * I)‖ := by
  have h : (1 : ℂ) - (1 / 2 + t * I) = starRingEnd ℂ (1 / 2 + t * I) := by
    apply Complex.ext <;> norm_num
  rcases χ.even_or_odd with hp | hp
  · rw [hp.gammaFactor_def, hp.gammaFactor_def, h, norm_Gammaℝ_conj]
  · rw [hp.gammaFactor_def, hp.gammaFactor_def, h,
      show starRingEnd ℂ (1 / 2 + t * I) + 1 = starRingEnd ℂ (1 / 2 + t * I + 1) by simp,
      norm_Gammaℝ_conj]

/-- **`|L(1/2 + it, χ)|² ≤ |D(1/2 + it, χ)| + |D(1/2 − it, χ⁻¹)|`** for primitive `χ ≠ 1`: the approximate
functional equation with `|ε(χ)| = 1` and `|N^{1−2s}| = 1` on the critical line. -/
theorem norm_LFunction_sq_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖LFunction χ (1 / 2 + t * I)‖ ^ 2 ≤ ‖afeD χ (1 / 2 + t * I)‖ + ‖afeD χ⁻¹ (1 / 2 + (-t : ℝ) * I)‖ := by
  set s : ℂ := 1 / 2 + t * I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hA := afe hprim hχ (s := s) (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
  have h1s : (1 : ℂ) - s = 1 / 2 + ((-t : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
  have hγ : gammaFactor χ s ≠ 0 := gammaFactor_ne_zero χ (by rw [hsre]; norm_num)
  have hγn : 0 < ‖gammaFactor χ s‖ := norm_pos_iff.2 hγ
  have hΛ : completedLFunction χ s = LFunction χ s * gammaFactor χ s :=
    completed_eq_mul χ (by rw [hsre]; norm_num)
  have hN1 : ‖(N : ℂ) ^ (1 - 2 * s)‖ = 1 := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))]
    have : (1 - 2 * s).re = 0 := by simp [hs]
    rw [this, Real.rpow_zero]
  have hmain : ‖LFunction χ s‖ ^ 2 * ‖gammaFactor χ s‖ ^ 2 ≤ ‖afeJ χ s‖ + ‖afeJ χ⁻¹ (1 - s)‖ := by
    have e : ‖completedLFunction χ s ^ 2‖ = ‖LFunction χ s‖ ^ 2 * ‖gammaFactor χ s‖ ^ 2 := by
      rw [hΛ, norm_pow, norm_mul, mul_pow]
    rw [← e, hA]
    calc ‖afeJ χ s + rootNumber χ ^ 2 * (N : ℂ) ^ (1 - 2 * s) * afeJ χ⁻¹ (1 - s)‖
        ≤ ‖afeJ χ s‖ + ‖rootNumber χ ^ 2 * (N : ℂ) ^ (1 - 2 * s) * afeJ χ⁻¹ (1 - s)‖ := norm_add_le _ _
      _ = ‖afeJ χ s‖ + ‖afeJ χ⁻¹ (1 - s)‖ := by
          rw [norm_mul, norm_mul, norm_pow, LinnikFE.norm_rootNumber hprim, hN1]; ring
  have hγ' : ‖gammaFactor χ⁻¹ (1 - s)‖ = ‖gammaFactor χ s‖ := by
    rw [gammaFactor_inv, hs, norm_gammaFactor_one_sub]
  have hD1 : ‖afeD χ s‖ = ‖afeJ χ s‖ / ‖gammaFactor χ s‖ ^ 2 := by
    rw [afeD, norm_div, norm_pow]
  have hD2 : ‖afeD χ⁻¹ (1 / 2 + ((-t : ℝ) : ℂ) * I)‖ = ‖afeJ χ⁻¹ (1 - s)‖ / ‖gammaFactor χ s‖ ^ 2 := by
    rw [← h1s, afeD, norm_div, norm_pow, hγ']
  rw [hD1, hD2, ← add_div, le_div_iff₀ (by positivity)]
  exact hmain

/-- **`|L(1/2 + it, χ)|⁴ ≤ 2|D(1/2 + it, χ)|² + 2|D(1/2 − it, χ⁻¹)|²`** for primitive `χ ≠ 1`. -/
theorem norm_LFunction_four_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖LFunction χ (1 / 2 + t * I)‖ ^ 4 ≤
      2 * ‖afeD χ (1 / 2 + t * I)‖ ^ 2 + 2 * ‖afeD χ⁻¹ (1 / 2 + (-t : ℝ) * I)‖ ^ 2 := by
  have h := norm_LFunction_sq_le hprim hχ t
  have h0 : 0 ≤ ‖LFunction χ (1 / 2 + t * I)‖ ^ 2 := by positivity
  calc ‖LFunction χ (1 / 2 + t * I)‖ ^ 4 = (‖LFunction χ (1 / 2 + t * I)‖ ^ 2) ^ 2 := by ring
    _ ≤ (‖afeD χ (1 / 2 + t * I)‖ + ‖afeD χ⁻¹ (1 / 2 + (-t : ℝ) * I)‖) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ ≤ _ := by nlinarith [sq_nonneg (‖afeD χ (1 / 2 + t * I)‖ - ‖afeD χ⁻¹ (1 / 2 + (-t : ℝ) * I)‖)]

/-! ### The Dirichlet polynomial of `d(n)χ(n)` and its large values -/

/-- `P(z) = Σ_{n ≤ N₀} d(n)χ(n)n^{−z}`. -/
def Pd {N : ℕ} (χ : DirichletCharacter ℂ N) (N₀ : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N₀, (n.divisors.card : ℂ) * χ n * (n : ℂ) ^ (-z)

lemma natCast_cpow_neg_eq (n : ℕ) (hn : 1 ≤ n) (σ τ : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + τ * I)) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-(I * ((τ * Real.log n : ℝ) : ℂ))) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [neg_add, Complex.cpow_add _ _ hn0]
  congr 1
  · rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow hnr.le]
  · rw [Complex.cpow_def_of_ne_zero hn0, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hnr.le]
    congr 1; push_cast; ring

/-- `P(σ + iτ)` as `DirMean.dp` over `{1} ∪ (1, N₀]`. -/
lemma Pd_eq_dp {N : ℕ} (χ : DirichletCharacter ℂ N) (N₀ : ℕ) (σ τ : ℝ) :
    Pd χ N₀ (σ + τ * I) =
      dp (Icc 1 N₀) (fun j => (j.divisors.card : ℂ) * χ j * (((j : ℝ) ^ (-σ) : ℝ) : ℂ)) τ := by
  unfold Pd dp
  refine sum_congr rfl fun n hn => ?_
  rw [natCast_cpow_neg_eq n (mem_Icc.1 hn).1]
  ring

/-- `Σ_{j ≤ M}`-type bound: `(1 + log M)^k ≤ (1 + 1/a)^k M^{ka}` for `M ≥ 1`, `a > 0`. -/
lemma one_add_log_pow_le {M a : ℝ} (hM : 1 ≤ M) (ha : 0 < a) (k : ℕ) :
    (1 + Real.log M) ^ k ≤ (1 + 1 / a) ^ k * M ^ (k * a) := by
  have hl := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ M) ha
  have hMa : 1 ≤ M ^ a := Real.one_le_rpow hM ha.le
  have h1 : 1 + Real.log M ≤ (1 + 1 / a) * M ^ a := by
    have : M ^ a / a = 1 / a * M ^ a := by ring
    nlinarith
  have h0 : 0 ≤ 1 + Real.log M := by have := Real.log_nonneg hM; linarith
  calc (1 + Real.log M) ^ k ≤ ((1 + 1 / a) * M ^ a) ^ k := pow_le_pow_left₀ h0 h1 k
    _ = (1 + 1 / a) ^ k * M ^ (k * a) := by
        rw [mul_pow, ← Real.rpow_natCast (M ^ a), ← Real.rpow_mul (by linarith)]; ring_nf

/-- **Large values of `P` at one point per character**: for `0 < c₀ ≤ 1/2` and points `|x_χ| ≤ X`,
`Σ_χ |P(1/2 + c₀ + ix_χ)|² ≤ 2#R + 2K²·e(N(2X + 1) + 8N₀(1 + log N₀))(2 + log²(2N₀))·2(1 + log 2N₀)³`,
`K = ⌊log₂ N₀⌋ + 1`: the term `n = 1`, the dyadic blocks of `(1, N₀]`, round 521's
`LinnikHybrid.large_values_chars_off` and round 518's `InghamDensity.block_mass_le_b`. -/
theorem sum_norm_Pd_sq_le {N : ℕ} [NeZero N] {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 2)
    (Rs : Finset (DirichletCharacter ℂ N)) {X : ℝ} (hX : 0 ≤ X) (x : DirichletCharacter ℂ N → ℝ)
    (hx : ∀ χ ∈ Rs, |x χ| ≤ X) :
    ∑ χ ∈ Rs, ‖Pd χ N₀ ((1 / 2 + c₀ : ℝ) + x χ * I)‖ ^ 2 ≤
      2 * Rs.card + 2 * ((Nat.log 2 N₀ + 1 : ℕ) : ℝ) ^ 2 * (Real.exp 1 *
        (((N : ℝ) * (2 * X + 1) + 8 * N₀ * (1 + Real.log N₀)) * (2 + Real.log (2 * N₀) ^ 2)) *
          (2 * (1 + Real.log (2 * N₀)) ^ 3)) := by
  set σ₀ : ℝ := 1 / 2 + c₀ with hσ₀
  set K := Nat.log 2 N₀ + 1 with hK
  set B := fun (χ : DirichletCharacter ℂ N) (k : ℕ) =>
    dp ((Finset.Ioc 1 (1 * N₀)).filter (fun j => blk 1 j = k))
      (fun j => (j.divisors.card : ℂ) * χ j * (((j : ℝ) ^ (-σ₀) : ℝ) : ℂ)) (x χ) with hB
  have hN₀r : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  -- the polynomial: the term `n = 1` and the blocks
  have hsplit : ∀ χ : DirichletCharacter ℂ N, Pd χ N₀ (σ₀ + x χ * I) = 1 + ∑ k ∈ range K, B χ k := by
    intro χ
    rw [Pd_eq_dp, ← Finset.Ioc_insert_left hN₀]
    have h1 : dp (insert 1 (Finset.Ioc 1 N₀)) (fun j => (j.divisors.card : ℂ) * χ j * (((j : ℝ) ^ (-σ₀) : ℝ) : ℂ))
          (x χ) = 1 + dp (Finset.Ioc 1 N₀)
            (fun j => (j.divisors.card : ℂ) * χ j * (((j : ℝ) ^ (-σ₀) : ℝ) : ℂ)) (x χ) := by
      unfold dp
      rw [Finset.sum_insert (by simp)]
      congr 1
      simp
    rw [h1, show Finset.Ioc 1 N₀ = Finset.Ioc 1 (1 * N₀) by rw [one_mul], dp_blocks 1 N₀ le_rfl]
  -- pointwise: `|P|² ≤ 2 + 2K Σ_k |B_k|²`
  have hpt : ∀ χ : DirichletCharacter ℂ N, ‖Pd χ N₀ (σ₀ + x χ * I)‖ ^ 2 ≤
      2 + 2 * K * ∑ k ∈ range K, ‖B χ k‖ ^ 2 := by
    intro χ
    rw [hsplit]
    have h1 : ‖(1 : ℂ) + ∑ k ∈ range K, B χ k‖ ≤ 1 + ∑ k ∈ range K, ‖B χ k‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_one]
      gcongr
      exact norm_sum_le _ _
    have h2 : (∑ k ∈ range K, ‖B χ k‖) ^ 2 ≤ K * ∑ k ∈ range K, ‖B χ k‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := range K) (f := fun k => ‖B χ k‖)
      simpa using this
    have h0 : 0 ≤ ∑ k ∈ range K, ‖B χ k‖ := sum_nonneg fun _ _ => norm_nonneg _
    calc ‖(1 : ℂ) + ∑ k ∈ range K, B χ k‖ ^ 2 ≤ (1 + ∑ k ∈ range K, ‖B χ k‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ 2 + 2 * (∑ k ∈ range K, ‖B χ k‖) ^ 2 := by nlinarith [sq_nonneg (1 - ∑ k ∈ range K, ‖B χ k‖)]
      _ ≤ 2 + 2 * (K * ∑ k ∈ range K, ‖B χ k‖ ^ 2) := by gcongr
      _ = 2 + 2 * K * ∑ k ∈ range K, ‖B χ k‖ ^ 2 := by ring
  -- one block over the characters
  set Lb := Real.exp 1 * (((N : ℝ) * (2 * X + 1) + 8 * N₀ * (1 + Real.log N₀)) * (2 + Real.log (2 * N₀) ^ 2)) *
    (2 * (1 + Real.log (2 * N₀)) ^ 3) with hLb
  have hblock : ∀ k ∈ range K, ∑ χ ∈ Rs, ‖B χ k‖ ^ 2 ≤ Lb := by
    intro k hk
    have hkK : k < Nat.log 2 N₀ + 1 := mem_range.1 hk
    set P := 2 ^ k * 1 with hPdef
    have hP : 1 ≤ P := by rw [hPdef]; exact Nat.one_le_iff_ne_zero.2 (by positivity)
    have hPN : P ≤ N₀ := by rw [hPdef, mul_one]; exact pow_blk_le hkK hN₀
    have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
    have hPNr : (P : ℝ) ≤ N₀ := by exact_mod_cast hPN
    have hsub := block_sub (X := 1) (N := N₀) (k := k) le_rfl
    have hLV := large_values_chars_off hP hsub (fun j => (j.divisors.card : ℂ)) N (σ := σ₀)
      (lo := -X - 1 / 2) (hi := X + 1 / 2) (by linarith) Rs x (fun _ => σ₀)
      (fun χ hχ => by have := abs_le.1 (hx χ hχ); constructor <;> linarith)
      (fun _ _ => ⟨le_rfl, by linarith⟩)
    have hmass := block_mass_le_b (fun j => (j.divisors.card : ℂ)) (fun j => by simp) hP hsub
      (by linarith : 0 ≤ σ₀)
    have hlogP : Real.log P ≤ Real.log N₀ := Real.log_le_log (by linarith) hPNr
    have hlog2P : Real.log (2 * P) ≤ Real.log (2 * N₀) := Real.log_le_log (by linarith) (by linarith)
    have hlogP0 : 0 ≤ Real.log P := Real.log_nonneg hPr
    have hlog2P0 : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by linarith)
    have hPpow : (P : ℝ) ^ (1 - 2 * σ₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hPr (by linarith)
    have hmass' : ∑ j ∈ (Finset.Ioc 1 (1 * N₀)).filter (fun j => blk 1 j = k),
        ‖(j.divisors.card : ℂ)‖ ^ 2 * ((j : ℝ) ^ (-σ₀)) ^ 2 ≤ 2 * (1 + Real.log (2 * N₀)) ^ 3 := by
      refine hmass.trans ?_
      have h3 : (1 + Real.log (2 * P)) ^ 3 ≤ (1 + Real.log (2 * N₀)) ^ 3 := by gcongr
      have h4 : 0 ≤ (1 + Real.log (2 * P)) ^ 3 := by positivity
      nlinarith
    have hfirst : ((N : ℝ) * (X + 1 / 2 - (-X - 1 / 2)) + 8 * P * (1 + Real.log P)) *
        (2 + Real.log (2 * P) ^ 2) ≤ ((N : ℝ) * (2 * X + 1) + 8 * N₀ * (1 + Real.log N₀)) *
          (2 + Real.log (2 * N₀) ^ 2) := by
      have e : (N : ℝ) * (X + 1 / 2 - (-X - 1 / 2)) = N * (2 * X + 1) := by ring
      rw [e]
      have hNX : 0 ≤ (N : ℝ) * (2 * X + 1) := by positivity
      gcongr
    have hB' : ∀ χ ∈ Rs, B χ k = dp ((Finset.Ioc 1 (1 * N₀)).filter (fun j => blk 1 j = k))
        (fun j => (j.divisors.card : ℂ) * χ j * (((j : ℝ) ^ (-(fun _ => σ₀) χ) : ℝ) : ℂ)) (x χ) :=
      fun χ _ => rfl
    rw [sum_congr rfl fun χ hχ => by rw [hB' χ hχ]]
    refine hLV.trans ?_
    rw [hLb]
    have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    have hm0 : 0 ≤ ∑ j ∈ (Finset.Ioc 1 (1 * N₀)).filter (fun j => blk 1 j = k),
        ‖(j.divisors.card : ℂ)‖ ^ 2 * ((j : ℝ) ^ (-σ₀)) ^ 2 := sum_nonneg fun _ _ => by positivity
    have hf0 : 0 ≤ ((N : ℝ) * (X + 1 / 2 - (-X - 1 / 2)) + 8 * P * (1 + Real.log P)) *
        (2 + Real.log (2 * P) ^ 2) := by
      have : 0 ≤ (N : ℝ) * (X + 1 / 2 - (-X - 1 / 2)) := by
        have : X + 1 / 2 - (-X - 1 / 2) = 2 * X + 1 := by ring
        rw [this]; positivity
      positivity
    gcongr
  -- assemble
  calc ∑ χ ∈ Rs, ‖Pd χ N₀ ((1 / 2 + c₀ : ℝ) + x χ * I)‖ ^ 2
      ≤ ∑ χ ∈ Rs, (2 + 2 * K * ∑ k ∈ range K, ‖B χ k‖ ^ 2) := sum_le_sum fun χ _ => hpt χ
    _ = 2 * Rs.card + 2 * K * ∑ k ∈ range K, ∑ χ ∈ Rs, ‖B χ k‖ ^ 2 := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, sum_comm]; ring
    _ ≤ 2 * Rs.card + 2 * K * ∑ k ∈ range K, Lb := by
        gcongr with k hk
        exact hblock k hk
    _ = 2 * Rs.card + 2 * (K : ℝ) ^ 2 * Lb := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ = _ := by rw [hLb]

/-! ### `L(z, χ)² = P(z) + T(z)` and the tail `T` -/

/-- The coefficients of `L(s, χ)²`: `χ ⍟ χ`. -/
def cc {N : ℕ} (χ : DirichletCharacter ℂ N) : ℕ → ℂ := (χ ·) ⍟ (χ ·)

/-- `(χ ⍟ χ)(n) = d(n)χ(n)`. -/
lemma cc_apply {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : cc χ n = (n.divisors.card : ℂ) * χ n := by
  unfold cc
  rw [LSeries.convolution_def]
  have h : ∀ p ∈ n.divisorsAntidiagonal, χ p.1 * χ p.2 = χ n := by
    intro p hp
    obtain ⟨hpn, _⟩ := Nat.mem_divisorsAntidiagonal.1 hp
    rw [← map_mul, ← Nat.cast_mul, hpn]
  simp only
  rw [sum_congr rfl h, sum_const, nsmul_eq_mul, ← Nat.map_div_right_divisors, card_map]

lemma LSeriesSummable_cc {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (cc χ) z :=
  (LSeriesSummable_of_one_lt_re χ hz).convolution (LSeriesSummable_of_one_lt_re χ hz)

lemma LFunction_sq_eq_LSeries {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 1 < z.re) :
    LFunction χ z ^ 2 = LSeries (cc χ) z := by
  unfold cc
  rw [LSeries_convolution' (LSeriesSummable_of_one_lt_re χ hz) (LSeriesSummable_of_one_lt_re χ hz),
    ← LFunction_eq_LSeries χ hz, sq]

/-- The tail `T(z) = L(z, χ)² − P(z)`. -/
def Tl {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (N₀ : ℕ) (z : ℂ) : ℂ := LFunction χ z ^ 2 - Pd χ N₀ z

lemma tsum_inv_add_one_sq_le_two : ∑' i : ℕ, (1 : ℝ) / ((i : ℝ) + 1) ^ 2 ≤ 2 := by
  have hs := hasSum_zeta_two
  have h0 := hs.summable.tsum_eq_zero_add
  have e : ∑' b : ℕ, (1 : ℝ) / ((b + 1 : ℕ) : ℝ) ^ 2 = ∑' i : ℕ, (1 : ℝ) / ((i : ℝ) + 1) ^ 2 := by
    congr 1; ext i; push_cast; ring
  rw [hs.tsum_eq] at h0
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
    zero_add] at h0
  rw [← e, ← h0]
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- `P(z)` as the first `N₀ + 1` terms of the Dirichlet series of `χ ⍟ χ`. -/
lemma Pd_eq_sum_term {N : ℕ} (χ : DirichletCharacter ℂ N) (N₀ : ℕ) (z : ℂ) :
    Pd χ N₀ z = ∑ i ∈ range (N₀ + 1), LSeries.term (cc χ) z i := by
  rw [Finset.sum_range_succ', LSeries.term_zero, add_zero]
  unfold Pd
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [add_tsub_cancel_right]
  refine sum_congr rfl fun i _ => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero i), cc_apply, Complex.cpow_neg, div_eq_mul_inv,
    add_comm 1 i]

/-- One term of the tail: `|(χ ⍟ χ)(m)m^{−z}| ≤ N₀^{3−Re z}/(i + 1)²` for `m = i + N₀ + 1`, `Re z ≥ 3`. -/
lemma norm_term_tail_le {N : ℕ} (χ : DirichletCharacter ℂ N) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {z : ℂ}
    (hz : 3 ≤ z.re) (i : ℕ) :
    ‖LSeries.term (cc χ) z (i + (N₀ + 1))‖ ≤ (N₀ : ℝ) ^ (3 - z.re) * ((1 : ℝ) / ((i : ℝ) + 1) ^ 2) := by
  have hN₀r : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  set m := i + (N₀ + 1) with hm
  have hm0 : m ≠ 0 := by omega
  have hmr : (N₀ : ℝ) ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hm1 : (0 : ℝ) < m := by linarith
  have hi : (i : ℝ) + 1 ≤ m := by rw [hm]; push_cast; linarith
  simp only [LSeries.norm_term_eq, hm0, ↓reduceIte]
  rw [cc_apply, norm_mul, Complex.norm_natCast]
  have hd : ((m.divisors.card : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.card_divisors_le_self m
  have hχ1 : ‖χ m‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hpow : (0 : ℝ) < (m : ℝ) ^ z.re := Real.rpow_pos_of_pos hm1 _
  rw [div_le_iff₀ hpow]
  have e1 : (m : ℝ) ^ z.re = (m : ℝ) ^ (3 : ℝ) * (m : ℝ) ^ (z.re - 3) := by
    rw [← Real.rpow_add hm1]; ring_nf
  have h2 : 1 ≤ (N₀ : ℝ) ^ (3 - z.re) * (m : ℝ) ^ (z.re - 3) := by
    rw [show (3 : ℝ) - z.re = -(z.re - 3) by ring, Real.rpow_neg (by linarith), ← div_eq_inv_mul,
      one_le_div (Real.rpow_pos_of_pos (by linarith) _)]
    exact Real.rpow_le_rpow (by linarith) hmr (by linarith)
  have h3 : (m : ℝ) ^ (3 : ℝ) = (m : ℝ) * (m : ℝ) ^ 2 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have hi2 : ((i : ℝ) + 1) ^ 2 ≤ (m : ℝ) ^ 2 := by gcongr
  have hip : 0 < ((i : ℝ) + 1) ^ 2 := by positivity
  have hq : 1 ≤ (m : ℝ) ^ 2 / ((i : ℝ) + 1) ^ 2 := by rw [one_le_div hip]; exact hi2
  set A := (N₀ : ℝ) ^ (3 - z.re) * (m : ℝ) ^ (z.re - 3) with hA
  have hrhs : (N₀ : ℝ) ^ (3 - z.re) * (1 / ((i : ℝ) + 1) ^ 2) * (m : ℝ) ^ z.re =
      (m : ℝ) * ((m : ℝ) ^ 2 / ((i : ℝ) + 1) ^ 2) * A := by
    rw [e1, h3, hA]; field_simp
  rw [hrhs]
  have h4 : (m : ℝ) * 1 * 1 ≤ (m : ℝ) * ((m : ℝ) ^ 2 / ((i : ℝ) + 1) ^ 2) * A := by
    have := mul_le_mul hq h2 zero_le_one (by positivity)
    nlinarith
  calc ((m.divisors.card : ℕ) : ℝ) * ‖χ m‖ ≤ (m : ℝ) * 1 := mul_le_mul hd hχ1 (norm_nonneg _) (by positivity)
    _ = (m : ℝ) * 1 * 1 := by ring
    _ ≤ _ := h4

lemma Tl_eq_tsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (N₀ : ℕ) {z : ℂ} (hz : 1 < z.re) :
    Tl χ N₀ z = ∑' i : ℕ, LSeries.term (cc χ) z (i + (N₀ + 1)) := by
  have hsplit := (LSeriesSummable_cc χ hz).sum_add_tsum_nat_add (N₀ + 1)
  unfold Tl
  rw [LFunction_sq_eq_LSeries χ hz, LSeries, Pd_eq_sum_term, ← hsplit]
  ring

lemma summable_inv_add_one_sq : Summable fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1) ^ 2 := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have h2 := (summable_nat_add_iff 1).2 h
  refine h2.congr fun i => ?_
  push_cast; ring

lemma summable_norm_term_tail {N : ℕ} (χ : DirichletCharacter ℂ N) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {z : ℂ}
    (hz : 3 ≤ z.re) : Summable fun i : ℕ => ‖LSeries.term (cc χ) z (i + (N₀ + 1))‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_tail_le χ hN₀ hz)
    (summable_inv_add_one_sq.mul_left _)

/-- **The tail**: `|T(z)| ≤ 2N₀^{3 − Re z}` on `Re z ≥ 3`, since `d(n) ≤ n` and `n^{1−Re z} ≤ n^{−2}N₀^{3−Re z}` for
`n > N₀`. -/
theorem norm_Tl_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {z : ℂ}
    (hz : 3 ≤ z.re) : ‖Tl χ N₀ z‖ ≤ 2 * (N₀ : ℝ) ^ (3 - z.re) := by
  have hz1 : 1 < z.re := by linarith
  rw [Tl_eq_tsum χ N₀ hz1]
  have hsum' := summable_norm_term_tail χ hN₀ hz
  have hsumR : Summable fun i : ℕ => (N₀ : ℝ) ^ (3 - z.re) * ((1 : ℝ) / ((i : ℝ) + 1) ^ 2) :=
    summable_inv_add_one_sq.mul_left _
  have h1 : ∑' i : ℕ, ‖LSeries.term (cc χ) z (i + (N₀ + 1))‖ ≤
      ∑' i : ℕ, (N₀ : ℝ) ^ (3 - z.re) * ((1 : ℝ) / ((i : ℝ) + 1) ^ 2) :=
    Summable.tsum_le_tsum (norm_term_tail_le χ hN₀ hz) hsum' hsumR
  have h2 : ∑' i : ℕ, (N₀ : ℝ) ^ (3 - z.re) * ((1 : ℝ) / ((i : ℝ) + 1) ^ 2) =
      (N₀ : ℝ) ^ (3 - z.re) * ∑' i : ℕ, (1 : ℝ) / ((i : ℝ) + 1) ^ 2 := tsum_mul_left
  have h3 := tsum_inv_add_one_sq_le_two
  have hN0 : 0 ≤ (N₀ : ℝ) ^ (3 - z.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h4 := norm_tsum_le_tsum_norm hsum'
  calc ‖∑' i : ℕ, LSeries.term (cc χ) z (i + (N₀ + 1))‖ ≤ (N₀ : ℝ) ^ (3 - z.re) * 2 := by
        rw [h2] at h1
        nlinarith
    _ = 2 * (N₀ : ℝ) ^ (3 - z.re) := by ring

/-- `|P(z)| ≤ N₀²` on `Re z ≥ 0`. -/
lemma norm_Pd_le {N : ℕ} (χ : DirichletCharacter ℂ N) (N₀ : ℕ) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Pd χ N₀ z‖ ≤ (N₀ : ℝ) ^ 2 := by
  unfold Pd
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ n ∈ Finset.Icc 1 N₀, ‖(n.divisors.card : ℂ) * χ n * (n : ℂ) ^ (-z)‖ ≤ N₀ := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hn
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [norm_mul, norm_mul, Complex.norm_natCast,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
    have hd : ((n.divisors.card : ℕ) : ℝ) ≤ N₀ := by
      exact_mod_cast (Nat.card_divisors_le_self n).trans hnN
    have hχ1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hp : (n : ℝ) ^ (-z).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hnr (by simp; linarith)
    calc ((n.divisors.card : ℕ) : ℝ) * ‖χ n‖ * (n : ℝ) ^ (-z).re ≤ N₀ * 1 * 1 := by gcongr
      _ = N₀ := by ring
  calc ∑ n ∈ Finset.Icc 1 N₀, ‖(n.divisors.card : ℂ) * χ n * (n : ℂ) ^ (-z)‖ ≤ ∑ n ∈ Finset.Icc 1 N₀, (N₀ : ℝ) :=
        sum_le_sum hpt
    _ = (N₀ : ℝ) ^ 2 := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring

/-- `|T(z)| ≤ ζ(3/2)² + N₀²` on `Re z ≥ 3/2`. -/
lemma norm_Tl_le_crude {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (N₀ : ℕ) {z : ℂ} (hz : 3 / 2 ≤ z.re) :
    ‖Tl χ N₀ z‖ ≤ ChiUniform.zeta32 ^ 2 + (N₀ : ℝ) ^ 2 := by
  unfold Tl
  refine (norm_sub_le _ _).trans ?_
  rw [norm_pow]
  gcongr
  · exact LinnikLindelof.norm_LFunction_le_zeta32 χ hz
  · exact norm_Pd_le χ N₀ (by linarith)

end LinnikFourth

open Filter Topology

namespace LinnikFourth

open LinnikGamma

/-! ### The weight `W_a` -/

/-- `W_a(v) = (1 + |v|)^a e^{π|v|/2} e^{−v²}`. -/
def Wf (a v : ℝ) : ℝ := (1 + |v|) ^ a * Real.exp (Real.pi * |v| / 2) * Real.exp (-v ^ 2)

lemma Wf_nonneg (a v : ℝ) : 0 ≤ Wf a v := by unfold Wf; positivity

lemma continuous_Wf (a : ℝ) : Continuous (Wf a) := by
  unfold Wf
  refine Continuous.mul (Continuous.mul ?_ (by fun_prop)) (by fun_prop)
  exact (continuous_const.add continuous_abs).rpow_const fun v =>
    Or.inl (by positivity : (0 : ℝ) < 1 + |v|).ne'

/-- `W_a(v) ≤ e^{a² + π²/4}e^{−v²/2}` for `a ≥ 0`. -/
lemma Wf_le {a : ℝ} (ha : 0 ≤ a) (v : ℝ) :
    Wf a v ≤ Real.exp (a ^ 2 + Real.pi ^ 2 / 4) * Real.exp (-v ^ 2 / 2) := by
  unfold Wf
  have hu := abs_nonneg v
  have h1 : (1 + |v|) ^ a ≤ Real.exp (a * |v|) := by
    calc (1 + |v|) ^ a ≤ (Real.exp |v|) ^ a :=
          Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp |v|]) ha
      _ = Real.exp (a * |v|) := by rw [← Real.exp_mul]; ring_nf
  have hv2 : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
  calc (1 + |v|) ^ a * Real.exp (Real.pi * |v| / 2) * Real.exp (-v ^ 2)
      ≤ Real.exp (a * |v|) * Real.exp (Real.pi * |v| / 2) * Real.exp (-v ^ 2) := by gcongr
    _ = Real.exp (a * |v| + Real.pi * |v| / 2 + -v ^ 2) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (a ^ 2 + Real.pi ^ 2 / 4 + -v ^ 2 / 2) := by
        apply Real.exp_le_exp.2
        rw [hv2]
        nlinarith [sq_nonneg (|v| - (a + Real.pi / 2)), sq_nonneg (a - Real.pi / 2)]
    _ = Real.exp (a ^ 2 + Real.pi ^ 2 / 4) * Real.exp (-v ^ 2 / 2) := by rw [← Real.exp_add]

/-- `W_a(v) ≤ e^{a² + π²/4}` for `a ≥ 0`. -/
lemma Wf_le' {a : ℝ} (ha : 0 ≤ a) (v : ℝ) : Wf a v ≤ Real.exp (a ^ 2 + Real.pi ^ 2 / 4) := by
  refine (Wf_le ha v).trans ?_
  have : Real.exp (-v ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg v])
  calc Real.exp (a ^ 2 + Real.pi ^ 2 / 4) * Real.exp (-v ^ 2 / 2) ≤ Real.exp (a ^ 2 + Real.pi ^ 2 / 4) * 1 := by
        gcongr
    _ = _ := mul_one _

lemma integrable_Wf {a : ℝ} (ha : 0 ≤ a) : Integrable (Wf a) := by
  have hg : Integrable fun v : ℝ => Real.exp (a ^ 2 + Real.pi ^ 2 / 4) * Real.exp (-(1 / 2) * v ^ 2) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
  refine hg.mono' (continuous_Wf a).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Wf_nonneg a v)]
  refine (Wf_le ha v).trans (le_of_eq ?_)
  congr 2; ring

lemma one_add_abs_mul_Wf (a v : ℝ) : (1 + |v|) * Wf a v = Wf (a + 1) v := by
  unfold Wf
  have h : 0 < 1 + |v| := by positivity
  rw [Real.rpow_add h, Real.rpow_one]; ring

lemma Wf_mono {a a' : ℝ} (haa : a ≤ a') (v : ℝ) : Wf a v ≤ Wf a' v := by
  unfold Wf
  have h1 : (1 + |v|) ^ a ≤ (1 + |v|) ^ a' :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) haa
  gcongr

/-! ### The split integrands -/

lemma differentiableAt_Gammaℝ {u : ℂ} (hu : 0 < u.re) : DifferentiableAt ℂ Gammaℝ u := by
  have h : DifferentiableAt ℂ (fun s => ((Gammaℝ s)⁻¹)⁻¹) u :=
    (differentiable_Gammaℝ_inv u).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hu))
  simp only [inv_inv] at h
  exact h

lemma differentiableAt_gammaFactor {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ} (h : 0 < z.re) :
    DifferentiableAt ℂ (gammaFactor χ) z := by
  rcases χ.even_or_odd with hp | hp
  · have e : gammaFactor χ = Gammaℝ := funext hp.gammaFactor_def
    rw [e]; exact differentiableAt_Gammaℝ h
  · have e : gammaFactor χ = fun u => Gammaℝ (u + 1) := funext hp.gammaFactor_def
    rw [e]
    have h1 : DifferentiableAt ℂ (fun u : ℂ => u + 1) z := by fun_prop
    have h2 : DifferentiableAt ℂ Gammaℝ (z + 1) := differentiableAt_Gammaℝ (by simp; linarith)
    exact h2.comp z h1

/-- The split integrand `γ_χ(s + w)² M(s + w) N^w e^{w²}/w`. -/
def GG {N : ℕ} (χ : DirichletCharacter ℂ N) (M : ℂ → ℂ) (s w : ℂ) : ℂ :=
  gammaFactor χ (s + w) ^ 2 * M (s + w) * (N : ℂ) ^ w * Complex.exp (w ^ 2) / w

lemma afeG_eq_GG {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s w : ℂ} (h : 0 < (s + w).re) :
    afeG χ s w = GG χ (fun z => LFunction χ z ^ 2) s w := by
  unfold afeG GG
  rw [completed_eq_mul χ h]
  ring

lemma GG_add {N : ℕ} (χ : DirichletCharacter ℂ N) (M₁ M₂ : ℂ → ℂ) (s w : ℂ) :
    GG χ (fun z => M₁ z + M₂ z) s w = GG χ M₁ s w + GG χ M₂ s w := by
  unfold GG; ring

lemma KR_mono {c c' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') : KR c ≤ KR c' := by
  unfold KR
  have h5 : (1 : ℝ) ≤ 5 * Real.exp 4 := by
    have := Real.add_one_le_exp 4; linarith
  have hm : max 1 (3 / 4 + c / 2) ≤ max 1 (3 / 4 + c' / 2) := max_le_max le_rfl (by linarith)
  have hm1 : 1 ≤ max 1 (3 / 4 + c / 2) := le_max_left _ _
  have hlog : Real.log (5 * Real.exp 4 * max 1 (3 / 4 + c / 2)) ≤
      Real.log (5 * Real.exp 4 * max 1 (3 / 4 + c' / 2)) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hlog0 : 0 ≤ Real.log (5 * Real.exp 4 * max 1 (3 / 4 + c / 2)) := Real.log_nonneg (by nlinarith)
  have : (c / 2 + 1 / 4) * Real.log (5 * Real.exp 4 * max 1 (3 / 4 + c / 2)) ≤
      (c' / 2 + 1 / 4) * Real.log (5 * Real.exp 4 * max 1 (3 / 4 + c' / 2)) :=
    mul_le_mul (by linarith) hlog hlog0 (by linarith)
  linarith

/-- The constant of `norm_GG_le`: `(e^{KR(c)}(1 + |t|)^{c/2}|γ_χ(½ + it)|)² e^{c²} N^c/c`. -/
def KG2 {N : ℕ} (χ : DirichletCharacter ℂ N) (c t : ℝ) : ℝ :=
  (Real.exp (KR c) * (1 + |t|) ^ (c / 2) * ‖gammaFactor χ (1 / 2 + t * I)‖) ^ 2 * Real.exp (c ^ 2) *
    (N : ℝ) ^ c / c

lemma KG2_nonneg {N : ℕ} (χ : DirichletCharacter ℂ N) {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 ≤ KG2 χ c t := by
  unfold KG2; positivity

/-- **The integrand on a vertical line**: for `c > 0`,
`|G(c + iv)| ≤ KG2(c, t)|M(½ + it + c + iv)|W_{c+1/2}(v)`. -/
lemma norm_GG_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (M : ℂ → ℂ) {c : ℝ} (hc : 0 < c) (t v : ℝ) :
    ‖GG χ M (1 / 2 + t * I) (c + v * I)‖ ≤
      KG2 χ c t * ‖M (1 / 2 + t * I + (c + v * I))‖ * Wf (c + 1 / 2) v := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hγ := norm_gammaFactor_ratio_le χ hc.le t v
  have hNw : ‖(N : ℂ) ^ ((c : ℂ) + v * I)‖ = (N : ℝ) ^ c := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp
  have hexp : ‖Complex.exp (((c : ℂ) + v * I) ^ 2)‖ = Real.exp (c ^ 2) * Real.exp (-v ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]; congr 1; simp [sq]; ring
  have hw : c ≤ ‖(c : ℂ) + v * I‖ := by
    have := Complex.abs_re_le_norm ((c : ℂ) + v * I)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
      add_zero] at this
    rwa [abs_of_pos hc] at this
  unfold GG
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, hNw, hexp]
  set m := ‖M (1 / 2 + t * I + (c + v * I))‖ with hm
  set g := ‖gammaFactor χ (1 / 2 + t * I + (c + v * I))‖ with hg
  have hm0 : 0 ≤ m := norm_nonneg _
  have hpv : ((1 + |v|) ^ (c / 2 + 1 / 4)) ^ 2 = (1 + |v|) ^ (c + 1 / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
  have hev : (Real.exp (Real.pi * |v| / 4)) ^ 2 = Real.exp (Real.pi * |v| / 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hnum : 0 ≤ g ^ 2 * m * (N : ℝ) ^ c * (Real.exp (c ^ 2) * Real.exp (-v ^ 2)) := by positivity
  calc g ^ 2 * m * (N : ℝ) ^ c * (Real.exp (c ^ 2) * Real.exp (-v ^ 2)) / ‖(c : ℂ) + v * I‖
      ≤ g ^ 2 * m * (N : ℝ) ^ c * (Real.exp (c ^ 2) * Real.exp (-v ^ 2)) / c :=
        div_le_div_of_nonneg_left hnum hc hw
    _ ≤ (Real.exp (KR c) * (1 + |t|) ^ (c / 2) * (1 + |v|) ^ (c / 2 + 1 / 4) * Real.exp (Real.pi * |v| / 4) *
          ‖gammaFactor χ (1 / 2 + t * I)‖) ^ 2 * m * (N : ℝ) ^ c * (Real.exp (c ^ 2) * Real.exp (-v ^ 2)) / c := by
        gcongr
    _ = KG2 χ c t * m * Wf (c + 1 / 2) v := by
        unfold KG2 Wf
        rw [mul_pow, mul_pow, mul_pow, mul_pow, hpv, hev]
        field_simp

/-- `|G(x + iy)|(1 + |y|)² ≤ KG2(b, t)·(b/a)·B·e^{(b+5/2)² + π²/4}` on the strip `a ≤ x ≤ b`, when `|M| ≤ B` there. -/
lemma norm_GG_strip_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (M : ℂ → ℂ) {a b : ℝ} (ha : 0 < a)
    (t : ℝ) {B : ℝ} (hB : ∀ x ∈ Icc a b, ∀ y : ℝ, ‖M (1 / 2 + t * I + (x + y * I))‖ ≤ B)
    {x : ℝ} (hx : x ∈ Icc a b) (y : ℝ) :
    ‖GG χ M (1 / 2 + t * I) (x + y * I)‖ * (1 + |y|) ^ 2 ≤
      KG2 χ b t * (b / a) * B * Real.exp ((b + 5 / 2) ^ 2 + Real.pi ^ 2 / 4) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  obtain ⟨hax, hxb⟩ := hx
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < b := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x ⟨hax, hxb⟩ y)
  have h1 := norm_GG_le χ M hx0 t y
  have hK : KG2 χ x t ≤ KG2 χ b t * (b / a) := by
    unfold KG2
    have e1 : Real.exp (KR x) ≤ Real.exp (KR b) := Real.exp_le_exp.2 (KR_mono hx0.le hxb)
    have e2 : (1 + |t|) ^ (x / 2) ≤ (1 + |t|) ^ (b / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
    have e3 : Real.exp (x ^ 2) ≤ Real.exp (b ^ 2) := Real.exp_le_exp.2 (by nlinarith)
    have e4 : (N : ℝ) ^ x ≤ (N : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_le hN1 hxb
    have e5 : 1 / x ≤ (b / a) / b := by
      have e : (b / a) / b = 1 / a := by field_simp
      rw [e]
      exact one_div_le_one_div_of_le ha hax
    have e6 : ∀ z : ℝ, 0 ≤ z → z / x ≤ z * ((b / a) / b) := fun z hz => by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left e5 hz
    calc (Real.exp (KR x) * (1 + |t|) ^ (x / 2) * ‖gammaFactor χ (1 / 2 + t * I)‖) ^ 2 * Real.exp (x ^ 2) *
          (N : ℝ) ^ x / x
        ≤ (Real.exp (KR x) * (1 + |t|) ^ (x / 2) * ‖gammaFactor χ (1 / 2 + t * I)‖) ^ 2 * Real.exp (x ^ 2) *
          (N : ℝ) ^ x * ((b / a) / b) := e6 _ (by positivity)
      _ ≤ (Real.exp (KR b) * (1 + |t|) ^ (b / 2) * ‖gammaFactor χ (1 / 2 + t * I)‖) ^ 2 * Real.exp (b ^ 2) *
          (N : ℝ) ^ b * ((b / a) / b) := by gcongr
      _ = _ := by field_simp
  have hW : Wf (x + 1 / 2) y * (1 + |y|) ^ 2 ≤ Real.exp ((b + 5 / 2) ^ 2 + Real.pi ^ 2 / 4) := by
    have e : Wf (x + 1 / 2) y * (1 + |y|) ^ 2 = Wf (x + 5 / 2) y := by
      rw [show x + 5 / 2 = x + 1 / 2 + 1 + 1 by ring, ← one_add_abs_mul_Wf, ← one_add_abs_mul_Wf]; ring
    rw [e]
    exact (Wf_mono (by linarith) y).trans (Wf_le' (by linarith) y)
  have hm := hB x ⟨hax, hxb⟩ y
  have hK0 := KG2_nonneg χ hx0 t
  have hW0 := Wf_nonneg (x + 1 / 2) y
  have hKb := KG2_nonneg χ hb0 t
  calc ‖GG χ M (1 / 2 + t * I) (x + y * I)‖ * (1 + |y|) ^ 2
      ≤ KG2 χ x t * ‖M (1 / 2 + t * I + (x + y * I))‖ * Wf (x + 1 / 2) y * (1 + |y|) ^ 2 := by gcongr
    _ = KG2 χ x t * ‖M (1 / 2 + t * I + (x + y * I))‖ * (Wf (x + 1 / 2) y * (1 + |y|) ^ 2) := by ring
    _ ≤ (KG2 χ b t * (b / a)) * B * Real.exp ((b + 5 / 2) ^ 2 + Real.pi ^ 2 / 4) := by gcongr

/-- `G` is holomorphic on `Re w > 0`, for `M` entire and `Re s ≥ 0`. -/
lemma differentiableOn_GG {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {M : ℂ → ℂ}
    (hM : Differentiable ℂ M) {s : ℂ} (hs : 0 ≤ s.re) : DifferentiableOn ℂ (GG χ M s) {w | 0 < w.re} := by
  intro w hw
  have hw' : 0 < w.re := hw
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw'; simp at hw'
  have h1 : DifferentiableAt ℂ (fun w => gammaFactor χ (s + w)) w :=
    (differentiableAt_gammaFactor χ (z := s + w) (by simp; linarith)).comp w (by fun_prop)
  have h2 : DifferentiableAt ℂ (fun w => M (s + w)) w := (hM (s + w)).comp w (by fun_prop)
  have h3 : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ w) w := differentiableAt_id.const_cpow (Or.inl hN0)
  have h4 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w ^ 2)) w := by fun_prop
  exact ((((h1.pow 2).mul h2).mul h3).mul h4).div differentiableAt_id hw0 |>.differentiableWithinAt

lemma continuous_GG_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {M : ℂ → ℂ}
    (hM : Differentiable ℂ M) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Continuous fun v : ℝ => GG χ M (1 / 2 + t * I) (c + v * I) := by
  have hd := differentiableOn_GG χ hM (s := 1 / 2 + t * I) (by simp)
  refine hd.continuousOn.comp_continuous (by fun_prop) fun v => ?_
  show 0 < ((c : ℂ) + v * I).re
  simp [hc]

/-- `G` is integrable on a vertical line `Re w = c > 0` when `|M| ≤ B` there. -/
lemma integrable_GG {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {M : ℂ → ℂ} (hM : Differentiable ℂ M)
    {c : ℝ} (hc : 0 < c) (t : ℝ) {B : ℝ} (hB : ∀ y : ℝ, ‖M (1 / 2 + t * I + (c + y * I))‖ ≤ B) :
    Integrable fun v : ℝ => GG χ M (1 / 2 + t * I) (c + v * I) :=
  InghamDensity.integrable_of_le_sq (continuous_GG_line χ hM hc t) fun y =>
    norm_GG_strip_le χ M hc t (a := c) (b := c) (fun x hx y' => by
      rw [show x = c from le_antisymm hx.2 hx.1]; exact hB y') ⟨le_rfl, le_rfl⟩ y

/-- `G` tends to `0` uniformly on the strip `a ≤ Re w ≤ b` when `|M| ≤ B` there. -/
lemma decay_GG {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (M : ℂ → ℂ) {a b : ℝ} (ha : 0 < a)
    (t : ℝ) {B : ℝ} (hB : ∀ x ∈ Icc a b, ∀ y : ℝ, ‖M (1 / 2 + t * I + (x + y * I))‖ ≤ B) :
    ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc a b, ∀ y : ℝ, T₀ ≤ |y| → ‖GG χ M (1 / 2 + t * I) (x + y * I)‖ ≤ η := by
  intro η hη
  set C := KG2 χ b t * (b / a) * B * Real.exp ((b + 5 / 2) ^ 2 + Real.pi ^ 2 / 4) with hC
  refine ⟨C / η, fun x hx y hy => ?_⟩
  have hb := norm_GG_strip_le χ M ha t hB hx y
  have hpos : 0 < 1 + |y| := by positivity
  have h2 : 1 + |y| ≤ (1 + |y|) ^ 2 := le_self_pow₀ (by linarith [abs_nonneg y]) (by norm_num)
  have hCη : C ≤ η * |y| := by rwa [div_le_iff₀ hη, mul_comm] at hy
  have hG0 := norm_nonneg (GG χ M (1 / 2 + t * I) (x + y * I))
  have : ‖GG χ M (1 / 2 + t * I) (x + y * I)‖ * (1 + |y|) ≤ η * (1 + |y|) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hG0]
  exact le_of_mul_le_mul_right this hpos

/-! ### The contour split `J = J_P + J_T` -/

lemma differentiable_Pd {N : ℕ} (χ : DirichletCharacter ℂ N) (N₀ : ℕ) : Differentiable ℂ (Pd χ N₀) := by
  intro z
  unfold Pd
  refine DifferentiableAt.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (Finset.mem_Icc.1 hn).1; omega)
  exact (differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hn0))

lemma differentiable_Tl {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (N₀ : ℕ) :
    Differentiable ℂ (Tl χ N₀) := by
  intro z
  unfold Tl
  exact (((differentiable_LFunction hχ) z).pow 2).sub (differentiable_Pd χ N₀ z)

/-- **The split of `J`**: for `0 < c₀ ≤ 2 ≤ c₁`, `J(½ + it, χ) = (1/2πi)∫_{(c₀)} G_P + (1/2πi)∫_{(c₁)} G_T` with
`G_P = γ²P N^w e^{w²}/w` and `G_T = γ²T N^w e^{w²}/w`: on `Re w = 2` the integrand is `G_P + G_T`, and each piece moves
to its own line with no pole crossed. -/
theorem afeJ_split {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (N₀ : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₀2 : c₀ ≤ 2) (hc₁ : 2 ≤ c₁) (t : ℝ) :
    afeJ χ (1 / 2 + t * I) = VerticalIntegral' (GG χ (Pd χ N₀) (1 / 2 + t * I)) c₀ +
      VerticalIntegral' (GG χ (Tl χ N₀) (1 / 2 + t * I)) c₁ := by
  have hre : ∀ x y : ℝ, (1 / 2 + t * I + ((x : ℂ) + y * I)).re = 1 / 2 + x := fun x y => by simp
  have hPdB : ∀ x ∈ Icc c₀ 2, ∀ y : ℝ, ‖Pd χ N₀ (1 / 2 + t * I + (x + y * I))‖ ≤ (N₀ : ℝ) ^ 2 :=
    fun x hx y => norm_Pd_le χ N₀ (by rw [hre]; linarith [hx.1])
  have hTlB : ∀ x ∈ Icc 2 c₁, ∀ y : ℝ,
      ‖Tl χ N₀ (1 / 2 + t * I + (x + y * I))‖ ≤ ChiUniform.zeta32 ^ 2 + (N₀ : ℝ) ^ 2 :=
    fun x hx y => norm_Tl_le_crude χ N₀ (by rw [hre]; linarith [hx.1])
  have hiP2 := integrable_GG χ (differentiable_Pd χ N₀) (by norm_num : (0 : ℝ) < 2) t
    (fun y => hPdB 2 ⟨hc₀2, le_rfl⟩ y)
  have hiP0 := integrable_GG χ (differentiable_Pd χ N₀) hc₀ t (fun y => hPdB c₀ ⟨le_rfl, hc₀2⟩ y)
  have hiT2 := integrable_GG χ (differentiable_Tl hχ N₀) (by norm_num : (0 : ℝ) < 2) t
    (fun y => hTlB 2 ⟨le_rfl, hc₁⟩ y)
  have hiT1 := integrable_GG χ (differentiable_Tl hχ N₀) (by linarith : (0 : ℝ) < c₁) t
    (fun y => hTlB c₁ ⟨hc₁, le_rfl⟩ y)
  have hsplit2 : ∀ v : ℝ, afeG χ (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I) =
      GG χ (Pd χ N₀) (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I) +
        GG χ (Tl χ N₀) (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I) := by
    intro v
    rw [afeG_eq_GG χ (by rw [hre]; norm_num), ← GG_add]
    congr 1
    funext z
    unfold Tl; ring
  have hfun : (fun v : ℝ => afeG χ (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I)) =
      fun v : ℝ => GG χ (Pd χ N₀) (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I) +
        GG χ (Tl χ N₀) (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I) := funext hsplit2
  have hsub : ∀ {a b : ℝ}, 0 < a → Icc a b ×ℂ univ ⊆ {w : ℂ | 0 < w.re} := fun ha w hw => by
    rw [mem_reProdIm] at hw
    show 0 < w.re
    linarith [hw.1.1]
  have hshP : VerticalIntegral (GG χ (Pd χ N₀) (1 / 2 + t * I)) 2 =
      VerticalIntegral (GG χ (Pd χ N₀) (1 / 2 + t * I)) c₀ :=
    SmoothPerron.verticalIntegral_shift hc₀2
      ((differentiableOn_GG χ (differentiable_Pd χ N₀) (by simp)).mono (hsub hc₀))
      hiP2 hiP0 (decay_GG χ _ hc₀ t hPdB)
  have hshT : VerticalIntegral (GG χ (Tl χ N₀) (1 / 2 + t * I)) c₁ =
      VerticalIntegral (GG χ (Tl χ N₀) (1 / 2 + t * I)) 2 :=
    SmoothPerron.verticalIntegral_shift hc₁
      ((differentiableOn_GG χ (differentiable_Tl hχ N₀) (by simp)).mono (hsub (by norm_num)))
      hiT1 hiT2 (decay_GG χ _ (by norm_num) t hTlB)
  simp only [afeJ, VerticalIntegral', VerticalIntegral] at hshP hshT ⊢
  rw [hfun, integral_add hiP2 hiT2, smul_add, smul_add, hshP, ← hshT]

/-- `‖(1/2πi)∫_{(c)} G‖ ≤ (1/2π)∫ g` for `|G(c + iv)| ≤ g(v)`, `g` integrable. -/
lemma norm_verticalIntegral'_le {G : ℂ → ℂ} {c : ℝ} {g : ℝ → ℝ} (hg : Integrable g)
    (hG : ∀ v : ℝ, ‖G (c + v * I)‖ ≤ g v) : ‖VerticalIntegral' G c‖ ≤ 1 / (2 * π) * ∫ v, g v := by
  simp only [VerticalIntegral', VerticalIntegral]
  rw [norm_smul, norm_smul, Complex.norm_I, one_mul]
  have h1 : ‖(1 / (2 * π * I) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [h1]
  gcongr
  exact norm_integral_le_of_norm_le hg (Eventually.of_forall hG)

/-! ### The polynomial part `D_P` -/

/-- `KG2 = KG3·|γ_χ(½ + it)|²`. -/
def KG3 (c t : ℝ) (N : ℕ) : ℝ :=
  (Real.exp (KR c) * (1 + |t|) ^ (c / 2)) ^ 2 * Real.exp (c ^ 2) * (N : ℝ) ^ c / c

lemma KG2_eq {N : ℕ} (χ : DirichletCharacter ℂ N) (c t : ℝ) :
    KG2 χ c t = KG3 c t N * ‖gammaFactor χ (1 / 2 + t * I)‖ ^ 2 := by
  unfold KG2 KG3; ring

lemma KG3_nonneg {c : ℝ} (hc : 0 < c) (t : ℝ) (N : ℕ) : 0 ≤ KG3 c t N := by unfold KG3; positivity

lemma KG3_mono {c t T : ℝ} (hc : 0 < c) (htT : |t| ≤ |T|) (N : ℕ) : KG3 c t N ≤ KG3 c T N := by
  unfold KG3
  have h : (1 + |t|) ^ (c / 2) ≤ (1 + |T|) ^ (c / 2) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  gcongr

/-- `|J_c(G)/γ_χ(½ + it)²| ≤ KG3(c, t)/(2π)·∫ |M(½ + it + c + iv)|W_{c+1/2}(v) dv`. -/
lemma norm_VI'_GG_div_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (M : ℂ → ℂ) {c : ℝ} (hc : 0 < c)
    (t : ℝ) (hint : Integrable fun v : ℝ => ‖M (1 / 2 + t * I + (c + v * I))‖ * Wf (c + 1 / 2) v) :
    ‖VerticalIntegral' (GG χ M (1 / 2 + t * I)) c / gammaFactor χ (1 / 2 + t * I) ^ 2‖ ≤
      KG3 c t N / (2 * π) * ∫ v : ℝ, ‖M (1 / 2 + t * I + ((c : ℂ) + (v : ℂ) * I))‖ * Wf (c + 1 / 2) v := by
  have hγ : gammaFactor χ (1 / 2 + t * I) ≠ 0 := gammaFactor_ne_zero χ (by simp)
  have hγn : 0 < ‖gammaFactor χ (1 / 2 + t * I)‖ ^ 2 := pow_pos (norm_pos_iff.2 hγ) 2
  have h := norm_verticalIntegral'_le (G := GG χ M (1 / 2 + t * I)) (c := c)
    (hint.const_mul (KG2 χ c t)) (fun (v : ℝ) => by
      have := norm_GG_le χ M hc t v
      calc _ ≤ _ := this
        _ = KG2 χ c t * (‖M (1 / 2 + t * I + ((c : ℂ) + (v : ℂ) * I))‖ * Wf (c + 1 / 2) v) := by ring)
  rw [integral_const_mul, KG2_eq] at h
  rw [norm_div, norm_pow, div_le_iff₀ hγn]
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **Cauchy–Schwarz**: `(∫ pW)² ≤ (∫ W)(∫ p²W)` for `W ≥ 0` with `∫ W > 0`. -/
lemma sq_integral_mul_le {W p : ℝ → ℝ} (hW : ∀ v, 0 ≤ W v) (hWi : Integrable W) (hWpos : 0 < ∫ v, W v)
    (h1 : Integrable fun v => p v * W v) (h2 : Integrable fun v => p v ^ 2 * W v) :
    (∫ v, p v * W v) ^ 2 ≤ (∫ v, W v) * ∫ v, p v ^ 2 * W v := by
  have key : ∀ A B C : ℝ, 0 < A → 0 ≤ C - 2 * (B / A) * B + (B / A) ^ 2 * A → B ^ 2 ≤ A * C := by
    intro A B C hA h
    have e : C - 2 * (B / A) * B + (B / A) ^ 2 * A = C - B ^ 2 / A := by field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ hA] at h
    linarith
  have hq : 0 ≤ ∫ v, (p v - (∫ v, p v * W v) / (∫ v, W v)) ^ 2 * W v :=
    integral_nonneg fun v => mul_nonneg (sq_nonneg _) (hW v)
  have e : (fun v => (p v - (∫ v, p v * W v) / (∫ v, W v)) ^ 2 * W v) =
      fun v => p v ^ 2 * W v - 2 * ((∫ v, p v * W v) / (∫ v, W v)) * (p v * W v) +
        ((∫ v, p v * W v) / (∫ v, W v)) ^ 2 * W v := by
    funext v; ring
  set k := (∫ v, p v * W v) / (∫ v, W v) with hk
  have i1 : Integrable fun v => p v ^ 2 * W v - 2 * k * (p v * W v) := h2.sub (h1.const_mul _)
  have i2 : Integrable fun v => k ^ 2 * W v := hWi.const_mul _
  have i3 : Integrable fun v => 2 * k * (p v * W v) := h1.const_mul _
  rw [e, integral_add i1 i2, integral_sub h2 i3, integral_const_mul, integral_const_mul] at hq
  exact key _ _ _ hWpos hq

lemma Wf_pos (a v : ℝ) : 0 < Wf a v := by
  unfold Wf
  have : 0 < (1 + |v|) ^ a := Real.rpow_pos_of_pos (by positivity) a
  positivity

lemma integral_Wf_pos {a : ℝ} (ha : 0 ≤ a) : 0 < ∫ v, Wf a v := by
  rw [integral_pos_iff_support_of_nonneg (fun v => Wf_nonneg a v) (integrable_Wf ha)]
  have : Function.support (Wf a) = univ := by
    ext v; simp only [Function.mem_support, mem_univ, iff_true]; exact (Wf_pos a v).ne'
  rw [this, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-- The large-values bound of `sum_norm_Pd_sq_le` at `|x_χ| ≤ X`. -/
def LSb (R N N₀ : ℕ) (X : ℝ) : ℝ :=
  2 * R + 2 * ((Nat.log 2 N₀ + 1 : ℕ) : ℝ) ^ 2 * (Real.exp 1 *
    (((N : ℝ) * (2 * X + 1) + 8 * N₀ * (1 + Real.log N₀)) * (2 + Real.log (2 * N₀) ^ 2)) *
      (2 * (1 + Real.log (2 * N₀)) ^ 3))

lemma LSb_shift_le (R N N₀ : ℕ) (hN₀ : 1 ≤ N₀) {T u : ℝ} (hT : 0 ≤ T) (hu : 0 ≤ u) :
    LSb R N N₀ (T + u) ≤ LSb R N N₀ (T + 1) * (1 + u) := by
  have hN₀r : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  have hl1 : 0 ≤ Real.log N₀ := Real.log_nonneg hN₀r
  have hl2 : 0 ≤ Real.log (2 * N₀) := Real.log_nonneg (by linarith)
  set E := 2 * ((Nat.log 2 N₀ + 1 : ℕ) : ℝ) ^ 2 * Real.exp 1 * (2 + Real.log (2 * N₀) ^ 2) *
    (2 * (1 + Real.log (2 * N₀)) ^ 3) with hE
  set Qn := 8 * (N₀ : ℝ) * (1 + Real.log N₀) with hQn
  have hE0 : 0 ≤ E := by
    have h3 : 0 ≤ (1 + Real.log (2 * N₀)) ^ 3 := pow_nonneg (by linarith) 3
    rw [hE]; positivity
  have hQn0 : 0 ≤ Qn := by rw [hQn]; positivity
  have key : ∀ X, LSb R N N₀ X = 2 * R + E * ((N : ℝ) * (2 * X + 1) + Qn) := fun X => by
    unfold LSb; rw [hE, hQn]; ring
  rw [key, key]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  nlinarith [mul_nonneg hR0 hu, mul_nonneg hE0 (mul_nonneg hN0 hu), mul_nonneg hE0 (mul_nonneg hQn0 hu),
    mul_nonneg hE0 hN0, mul_nonneg (mul_nonneg hE0 hN0) (mul_nonneg hT hu)]

/-- **The polynomial part over the characters**: for `0 < c₀ ≤ ½` and `|t_χ| ≤ T`,
`Σ_χ |J_{c₀}(G_P)/γ_χ(½ + it_χ)²|² ≤ (KG3(c₀, T)/2π)²·∫W_{c₀+1/2}·LSb(T + 1)·∫W_{c₀+3/2}`: Cauchy–Schwarz in `v`
against `W_{c₀+1/2}`, then `sum_norm_Pd_sq_le` at the points `t_χ + v` for each `v`. -/
theorem sum_norm_DP_sq_le {N : ℕ} [NeZero N] {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ ≤ 1 / 2) (Rs : Finset (DirichletCharacter ℂ N)) {T : ℝ} (hT : 0 ≤ T)
    (t : DirichletCharacter ℂ N → ℝ) (ht : ∀ χ ∈ Rs, |t χ| ≤ T) :
    ∑ χ ∈ Rs, ‖VerticalIntegral' (GG χ (Pd χ N₀) (1 / 2 + t χ * I)) c₀ /
        gammaFactor χ (1 / 2 + t χ * I) ^ 2‖ ^ 2 ≤
      (KG3 c₀ T N / (2 * π)) ^ 2 * (∫ v, Wf (c₀ + 1 / 2) v) *
        (LSb Rs.card N N₀ (T + 1) * ∫ v, Wf (c₀ + 3 / 2) v) := by
  set W := Wf (c₀ + 1 / 2) with hWdef
  set p : DirichletCharacter ℂ N → ℝ → ℝ :=
    fun χ v => ‖Pd χ N₀ (1 / 2 + t χ * I + ((c₀ : ℂ) + (v : ℂ) * I))‖ with hp
  have hW0 : ∀ v, 0 ≤ W v := Wf_nonneg _
  have hWi : Integrable W := integrable_Wf (by linarith)
  have hWpos : 0 < ∫ v, W v := integral_Wf_pos (by linarith)
  have hpc : ∀ χ, Continuous (p χ) := fun χ =>
    ((differentiable_Pd χ N₀).continuous.comp (by fun_prop)).norm
  have hpb : ∀ χ v, p χ v ≤ (N₀ : ℝ) ^ 2 := fun χ v => norm_Pd_le χ N₀ (by simp; linarith)
  have hp0 : ∀ χ v, 0 ≤ p χ v := fun χ v => norm_nonneg _
  have hi1 : ∀ χ, Integrable fun v => p χ v * W v := fun χ =>
    (hWi.const_mul ((N₀ : ℝ) ^ 2)).mono' ((hpc χ).mul (continuous_Wf _)).aestronglyMeasurable
      (Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp0 χ v) (hW0 v))]
        exact mul_le_mul_of_nonneg_right (hpb χ v) (hW0 v))
  have hi2 : ∀ χ, Integrable fun v => p χ v ^ 2 * W v := fun χ =>
    (hWi.const_mul ((N₀ : ℝ) ^ 2 * (N₀ : ℝ) ^ 2)).mono'
      (((hpc χ).pow 2).mul (continuous_Wf _)).aestronglyMeasurable
      (Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hW0 v))]
        have h := hpb χ v
        have h2 : p χ v ^ 2 ≤ (N₀ : ℝ) ^ 2 * (N₀ : ℝ) ^ 2 := by nlinarith [hp0 χ v]
        exact mul_le_mul_of_nonneg_right h2 (hW0 v))
  set K := KG3 c₀ T N / (2 * π) with hK
  have hK0 : 0 ≤ K := div_nonneg (KG3_nonneg hc₀ T N) (by positivity)
  -- each character
  have hone : ∀ χ ∈ Rs, ‖VerticalIntegral' (GG χ (Pd χ N₀) (1 / 2 + t χ * I)) c₀ /
      gammaFactor χ (1 / 2 + t χ * I) ^ 2‖ ^ 2 ≤ K ^ 2 * ((∫ v, W v) * ∫ v, p χ v ^ 2 * W v) := by
    intro χ hχ
    have h := norm_VI'_GG_div_le χ (Pd χ N₀) hc₀ (t χ) (hi1 χ)
    have hKm : KG3 c₀ (t χ) N / (2 * π) ≤ K :=
      div_le_div_of_nonneg_right (KG3_mono hc₀ (by rw [abs_of_nonneg hT]; exact ht χ hχ) N) (by positivity)
    have hI0 : 0 ≤ ∫ v, p χ v * W v := integral_nonneg fun v => mul_nonneg (hp0 χ v) (hW0 v)
    have h' : ‖VerticalIntegral' (GG χ (Pd χ N₀) (1 / 2 + t χ * I)) c₀ /
        gammaFactor χ (1 / 2 + t χ * I) ^ 2‖ ≤ K * ∫ v, p χ v * W v :=
      h.trans (mul_le_mul_of_nonneg_right hKm hI0)
    have hcs := sq_integral_mul_le hW0 hWi hWpos (hi1 χ) (hi2 χ)
    calc _ ≤ (K * ∫ v, p χ v * W v) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h' 2
      _ = K ^ 2 * (∫ v, p χ v * W v) ^ 2 := by ring
      _ ≤ K ^ 2 * ((∫ v, W v) * ∫ v, p χ v ^ 2 * W v) := by gcongr
  -- the pointwise large-values bound
  have hpt : ∀ v, ∑ χ ∈ Rs, p χ v ^ 2 * W v ≤ LSb Rs.card N N₀ (T + 1) * Wf (c₀ + 3 / 2) v := by
    intro v
    have hLV := sum_norm_Pd_sq_le hN₀ hc₀ hc₀' Rs (X := T + |v|) (by positivity) (fun χ => t χ + v)
      (fun χ hχ => (abs_add_le _ _).trans (by linarith [ht χ hχ]))
    have e : ∀ χ : DirichletCharacter ℂ N, Pd χ N₀ (((1 / 2 + c₀ : ℝ) : ℂ) + ((t χ + v : ℝ) : ℂ) * I) =
        Pd χ N₀ (1 / 2 + t χ * I + ((c₀ : ℂ) + (v : ℂ) * I)) := by
      intro χ; congr 1; push_cast; ring
    simp only [e] at hLV
    have hsh := LSb_shift_le Rs.card N N₀ hN₀ hT (abs_nonneg v)
    have hLV' : ∑ χ ∈ Rs, p χ v ^ 2 ≤ LSb Rs.card N N₀ (T + |v|) := hLV
    calc ∑ χ ∈ Rs, p χ v ^ 2 * W v = (∑ χ ∈ Rs, p χ v ^ 2) * W v := by rw [sum_mul]
      _ ≤ LSb Rs.card N N₀ (T + |v|) * W v := mul_le_mul_of_nonneg_right hLV' (hW0 v)
      _ ≤ (LSb Rs.card N N₀ (T + 1) * (1 + |v|)) * W v := mul_le_mul_of_nonneg_right hsh (hW0 v)
      _ = LSb Rs.card N N₀ (T + 1) * Wf (c₀ + 3 / 2) v := by
          rw [mul_assoc, hWdef, one_add_abs_mul_Wf, show c₀ + 1 / 2 + 1 = c₀ + 3 / 2 by ring]
  have hsumint : ∫ v, ∑ χ ∈ Rs, p χ v ^ 2 * W v ≤ LSb Rs.card N N₀ (T + 1) * ∫ v, Wf (c₀ + 3 / 2) v := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_finsetSum Rs fun χ _ => hi2 χ)
      ((integrable_Wf (by linarith)).const_mul _) hpt
  have hA0 : 0 ≤ ∫ v, W v := hWpos.le
  calc _ ≤ ∑ χ ∈ Rs, K ^ 2 * ((∫ v, W v) * ∫ v, p χ v ^ 2 * W v) := sum_le_sum hone
    _ = K ^ 2 * (∫ v, W v) * ∫ v, ∑ χ ∈ Rs, p χ v ^ 2 * W v := by
        rw [integral_finsetSum Rs fun χ _ => hi2 χ, mul_sum]
        exact sum_congr rfl fun χ _ => by ring
    _ ≤ K ^ 2 * (∫ v, W v) * (LSb Rs.card N N₀ (T + 1) * ∫ v, Wf (c₀ + 3 / 2) v) := by gcongr

/-- **The tail part**: for `c₁ ≥ 5/2` and `|t| ≤ T`,
`|J_{c₁}(G_T)/γ_χ(½ + it)²| ≤ KG3(c₁, T)/(2π)·2N₀^{5/2−c₁}·∫W_{c₁+1/2}` (`norm_Tl_le` on `Re z = ½ + c₁`). -/
theorem norm_DT_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    {c₁ : ℝ} (hc₁ : 5 / 2 ≤ c₁) {T t : ℝ} (hT : 0 ≤ T) (htT : |t| ≤ T) :
    ‖VerticalIntegral' (GG χ (Tl χ N₀) (1 / 2 + t * I)) c₁ / gammaFactor χ (1 / 2 + t * I) ^ 2‖ ≤
      KG3 c₁ T N / (2 * π) * (2 * (N₀ : ℝ) ^ (5 / 2 - c₁) * ∫ v, Wf (c₁ + 1 / 2) v) := by
  have hc₁0 : 0 < c₁ := by linarith
  set q : ℝ → ℝ := fun v => ‖Tl χ N₀ (1 / 2 + t * I + ((c₁ : ℂ) + (v : ℂ) * I))‖ with hq
  have hqb : ∀ v, q v ≤ 2 * (N₀ : ℝ) ^ (5 / 2 - c₁) := fun v => by
    have hre : (1 / 2 + (t : ℂ) * I + ((c₁ : ℂ) + (v : ℂ) * I)).re = 1 / 2 + c₁ := by simp
    have h := norm_Tl_le χ hN₀ (z := 1 / 2 + t * I + ((c₁ : ℂ) + (v : ℂ) * I)) (by rw [hre]; linarith)
    rw [hre, show (3 : ℝ) - (1 / 2 + c₁) = 5 / 2 - c₁ by ring] at h
    exact h
  have hq0 : ∀ v, 0 ≤ q v := fun v => norm_nonneg _
  have hqc : Continuous q := ((differentiable_Tl hχ N₀).continuous.comp (by fun_prop)).norm
  have hWi := integrable_Wf (a := c₁ + 1 / 2) (by linarith)
  have hint : Integrable fun v => q v * Wf (c₁ + 1 / 2) v :=
    (hWi.const_mul (2 * (N₀ : ℝ) ^ (5 / 2 - c₁))).mono' (hqc.mul (continuous_Wf _)).aestronglyMeasurable
      (Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 v) (Wf_nonneg _ v))]
        exact mul_le_mul_of_nonneg_right (hqb v) (Wf_nonneg _ v))
  have h := norm_VI'_GG_div_le χ (Tl χ N₀) hc₁0 t hint
  have hKm : KG3 c₁ t N / (2 * π) ≤ KG3 c₁ T N / (2 * π) :=
    div_le_div_of_nonneg_right (KG3_mono hc₁0 (by rw [abs_of_nonneg hT]; exact htT) N) (by positivity)
  have hI : ∫ v, q v * Wf (c₁ + 1 / 2) v ≤ 2 * (N₀ : ℝ) ^ (5 / 2 - c₁) * ∫ v, Wf (c₁ + 1 / 2) v := by
    rw [← integral_const_mul]
    exact integral_mono hint (hWi.const_mul _) fun v => mul_le_mul_of_nonneg_right (hqb v) (Wf_nonneg _ v)
  have hI0 : 0 ≤ ∫ v, q v * Wf (c₁ + 1 / 2) v := integral_nonneg fun v => mul_nonneg (hq0 v) (Wf_nonneg _ v)
  calc _ ≤ KG3 c₁ t N / (2 * π) * ∫ v, q v * Wf (c₁ + 1 / 2) v := h
    _ ≤ KG3 c₁ T N / (2 * π) * (2 * (N₀ : ℝ) ^ (5 / 2 - c₁) * ∫ v, Wf (c₁ + 1 / 2) v) :=
        mul_le_mul hKm hI hI0 (div_nonneg (KG3_nonneg hc₁0 T N) (by positivity))

/-! ### Assembly at one modulus -/

/-- The bound of `sum_norm_DP_sq_le`. -/
def DPc (c₀ T : ℝ) (R N N₀ : ℕ) : ℝ :=
  (KG3 c₀ T N / (2 * π)) ^ 2 * (∫ v, Wf (c₀ + 1 / 2) v) * (LSb R N N₀ (T + 1) * ∫ v, Wf (c₀ + 3 / 2) v)

/-- The bound of `norm_DT_le`. -/
def BTc (c₁ T : ℝ) (N N₀ : ℕ) : ℝ :=
  KG3 c₁ T N / (2 * π) * (2 * (N₀ : ℝ) ^ (5 / 2 - c₁) * ∫ v, Wf (c₁ + 1 / 2) v)

lemma norm_add_sq_le' {x y : ℂ} {B : ℝ} (hy : ‖y‖ ≤ B) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * B ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + B := (norm_add_le x y).trans (by linarith)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖x‖ - B)]

/-- **`D = D_P + D_T` and the explicit bound**: for characters `χ ≠ 1` with `|t_χ| ≤ T`, `N₀ ≥ 1`, `0 < c₀ ≤ ½` and
`c₁ ≥ 5/2`, `Σ_χ |D(½ + it_χ, χ)|² ≤ 2·DPc + 2#R·BTc²`. -/
theorem sum_norm_afeD_sq_le_explicit {N : ℕ} [NeZero N] {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ ≤ 1 / 2) (hc₁ : 5 / 2 ≤ c₁) (Rs : Finset (DirichletCharacter ℂ N)) (hRs : ∀ χ ∈ Rs, χ ≠ 1)
    {T : ℝ} (hT : 0 ≤ T) (t : DirichletCharacter ℂ N → ℝ) (ht : ∀ χ ∈ Rs, |t χ| ≤ T) :
    ∑ χ ∈ Rs, ‖afeD χ (1 / 2 + t χ * I)‖ ^ 2 ≤
      2 * DPc c₀ T Rs.card N N₀ + 2 * (Rs.card * BTc c₁ T N N₀ ^ 2) := by
  have hpt : ∀ χ ∈ Rs, ‖afeD χ (1 / 2 + t χ * I)‖ ^ 2 ≤
      2 * ‖VerticalIntegral' (GG χ (Pd χ N₀) (1 / 2 + t χ * I)) c₀ / gammaFactor χ (1 / 2 + t χ * I) ^ 2‖ ^ 2 +
        2 * BTc c₁ T N N₀ ^ 2 := by
    intro χ hχ
    unfold afeD
    rw [afeJ_split (hRs χ hχ) N₀ (c₁ := c₁) hc₀ (by linarith) (by linarith) (t χ), add_div]
    exact norm_add_sq_le' (norm_DT_le (hRs χ hχ) hN₀ hc₁ hT (ht χ hχ))
  have hP := sum_norm_DP_sq_le hN₀ hc₀ hc₀' Rs hT t ht
  calc ∑ χ ∈ Rs, ‖afeD χ (1 / 2 + t χ * I)‖ ^ 2
      ≤ ∑ χ ∈ Rs, (2 * ‖VerticalIntegral' (GG χ (Pd χ N₀) (1 / 2 + t χ * I)) c₀ /
          gammaFactor χ (1 / 2 + t χ * I) ^ 2‖ ^ 2 + 2 * BTc c₁ T N N₀ ^ 2) := sum_le_sum hpt
    _ = 2 * ∑ χ ∈ Rs, ‖VerticalIntegral' (GG χ (Pd χ N₀) (1 / 2 + t χ * I)) c₀ /
          gammaFactor χ (1 / 2 + t χ * I) ^ 2‖ ^ 2 + 2 * (Rs.card * BTc c₁ T N N₀ ^ 2) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * DPc c₀ T Rs.card N N₀ + 2 * (Rs.card * BTc c₁ T N N₀ ^ 2) := by
        unfold DPc
        exact add_le_add (mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 2)) le_rfl

/-! ### The exponents -/

/-- `KG3(c, T) ≤ e^{2KR(c)}e^{c²}/c·(N(T + 2))^c`. -/
lemma KG3_le {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T) (N : ℕ) :
    KG3 c T N ≤ Real.exp (2 * KR c) * Real.exp (c ^ 2) / c * ((N : ℝ) * (T + 2)) ^ c := by
  unfold KG3
  rw [abs_of_nonneg hT]
  have e1 : Real.exp (KR c) ^ 2 = Real.exp (2 * KR c) := by
    rw [← Real.exp_nat_mul]; norm_num
  have e2 : ((1 + T) ^ (c / 2)) ^ 2 = (1 + T) ^ c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
  rw [mul_pow, e1, e2]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h2 : (1 + T) ^ c * (N : ℝ) ^ c ≤ ((N : ℝ) * (T + 2)) ^ c := by
    rw [← Real.mul_rpow (by linarith) hN0]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith) hc.le
  calc Real.exp (2 * KR c) * (1 + T) ^ c * Real.exp (c ^ 2) * (N : ℝ) ^ c / c
      = Real.exp (2 * KR c) * Real.exp (c ^ 2) / c * ((1 + T) ^ c * (N : ℝ) ^ c) := by ring
    _ ≤ _ := by gcongr

lemma natLog_two_add_one_le {n : ℕ} (hn : 1 ≤ n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log (2 * n)) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by exact_mod_cast Real.natLog_le_logb n 2
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hnr
  have h2 : Real.logb 2 n ≤ 2 * Real.log n := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hlogn (by linarith : (0 : ℝ) ≤ 2 * Real.log 2 - 1)]
  have h3 : Real.log n ≤ Real.log (2 * n) := Real.log_le_log (by linarith) (by linarith)
  push_cast
  linarith

lemma alg_bound {R X K e A B Lg : ℝ} (hR : R ≤ X) (hX : 0 ≤ X) (hL : 1 ≤ Lg) (hK0 : 0 ≤ K) (hK : K ≤ 2 * Lg)
    (he : 0 ≤ e) (hA0 : 0 ≤ A) (hA : A ≤ 8 * Lg * X) (hB0 : 0 ≤ B) (hB : B ≤ 2 * Lg ^ 2) :
    2 * R + 2 * K ^ 2 * (e * (A * B) * (2 * Lg ^ 3)) ≤ (2 + 256 * e) * X * Lg ^ 8 := by
  have hL0 : 0 ≤ Lg := by linarith
  have hK2 : K ^ 2 ≤ (2 * Lg) ^ 2 := pow_le_pow_left₀ hK0 hK 2
  have hAB : A * B ≤ (8 * Lg * X) * (2 * Lg ^ 2) := mul_le_mul hA hB hB0 (by positivity)
  have hL8 : 1 ≤ Lg ^ 8 := one_le_pow₀ hL
  have h1 : 2 * R ≤ 2 * X * Lg ^ 8 := by nlinarith
  have h2 : 2 * K ^ 2 * (e * (A * B) * (2 * Lg ^ 3)) ≤
      2 * (2 * Lg) ^ 2 * (e * ((8 * Lg * X) * (2 * Lg ^ 2)) * (2 * Lg ^ 3)) := by gcongr
  have e2 : 2 * (2 * Lg) ^ 2 * (e * ((8 * Lg * X) * (2 * Lg ^ 2)) * (2 * Lg ^ 3)) = 256 * e * X * Lg ^ 8 := by ring
  linarith

/-- `LSb(R, N, N₀, T + 1) ≤ (2 + 256e)(N(T + 2) + N₀)(1 + log 2N₀)⁸` for `R ≤ N`. -/
lemma LSb_le {R N N₀ : ℕ} (hR : R ≤ N) (hN₀ : 1 ≤ N₀) {T : ℝ} (hT : 0 ≤ T) :
    LSb R N N₀ (T + 1) ≤ (2 + 256 * Real.exp 1) * ((N : ℝ) * (T + 2) + N₀) * (1 + Real.log (2 * N₀)) ^ 8 := by
  have hN₀r : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  have hRr : (R : ℝ) ≤ N := by exact_mod_cast hR
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hl1 : 0 ≤ Real.log N₀ := Real.log_nonneg hN₀r
  have hl2 : 0 ≤ Real.log (2 * N₀) := Real.log_nonneg (by linarith)
  have hl12 : Real.log N₀ ≤ Real.log (2 * N₀) := Real.log_le_log (by linarith) (by linarith)
  have hNT : 0 ≤ (N : ℝ) * (T + 2) := by positivity
  unfold LSb
  refine alg_bound (by nlinarith) (by positivity) (by linarith) (Nat.cast_nonneg _)
    (natLog_two_add_one_le hN₀) (Real.exp_pos 1).le (by positivity) ?_ (by positivity) (by nlinarith)
  nlinarith [mul_nonneg hN0 hT, mul_le_mul_of_nonneg_left (by linarith : 1 + Real.log N₀ ≤ 1 + Real.log (2 * N₀))
    (by linarith : (0 : ℝ) ≤ 8 * N₀), mul_nonneg hNT hl2, mul_nonneg (by linarith : (0 : ℝ) ≤ N₀) hl2]

/-- **The second moment of `D` at one modulus**: for every `0 < ε ≤ 1` there is `C` with
`Σ_χ |D(½ + it_χ, χ)|² ≤ C(N(T + 2))^{1+ε}` for every set of characters `χ ≠ 1` mod `N` and points `|t_χ| ≤ T`; at
`δ = ε/8`, `c₀ = δ`, `c₁ = 5/δ`, `N₀ = ⌈(N(T + 2))^{1+δ}⌉`. -/
theorem sum_norm_afeD_sq_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (Rs : Finset (DirichletCharacter ℂ N)), (∀ χ ∈ Rs, χ ≠ 1) →
      ∀ T : ℝ, 0 ≤ T → ∀ t : DirichletCharacter ℂ N → ℝ, (∀ χ ∈ Rs, |t χ| ≤ T) →
        ∑ χ ∈ Rs, ‖afeD χ (1 / 2 + t χ * I)‖ ^ 2 ≤ C * ((N : ℝ) * (T + 2)) ^ (1 + ε) := by
  have hδ0 : 0 < ε / 8 := by positivity
  have hc₁5 : 5 / 2 ≤ 5 / (ε / 8) := by rw [le_div_iff₀ hδ0]; nlinarith
  have hc₁0 : 0 < 5 / (ε / 8) := by positivity
  have hδc : ε / 8 * (5 / (ε / 8)) = 5 := by field_simp
  obtain ⟨A₀, hA₀⟩ : ∃ x : ℝ, x = Real.exp (2 * KR (ε / 8)) * Real.exp ((ε / 8) ^ 2) / (ε / 8) := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ x : ℝ, x = Real.exp (2 * KR (5 / (ε / 8))) * Real.exp ((5 / (ε / 8)) ^ 2) /
      (5 / (ε / 8)) := ⟨_, rfl⟩
  obtain ⟨I₁, hI₁⟩ : ∃ x : ℝ, x = ∫ v, Wf (ε / 8 + 1 / 2) v := ⟨_, rfl⟩
  obtain ⟨I₂, hI₂⟩ : ∃ x : ℝ, x = ∫ v, Wf (ε / 8 + 3 / 2) v := ⟨_, rfl⟩
  obtain ⟨I₃, hI₃⟩ : ∃ x : ℝ, x = ∫ v, Wf (5 / (ε / 8) + 1 / 2) v := ⟨_, rfl⟩
  obtain ⟨CL, hCL⟩ : ∃ x : ℝ, x = (2 + 256 * Real.exp 1) * 3 * ((1 + 1 / (ε / 8 / 16)) ^ 8 * 4 ^ (ε / 8 / 2)) :=
    ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; positivity
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hI₁0 : 0 ≤ I₁ := by rw [hI₁]; exact (integral_Wf_pos (by linarith)).le
  have hI₂0 : 0 ≤ I₂ := by rw [hI₂]; exact (integral_Wf_pos (by linarith)).le
  have hI₃0 : 0 ≤ I₃ := by rw [hI₃]; exact (integral_Wf_pos (by linarith)).le
  have hCL0 : 0 ≤ CL := by rw [hCL]; positivity
  refine ⟨2 * ((A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂)) + 2 * (A₁ / (2 * π) * (2 * I₃)) ^ 2,
    fun N _ Rs hRs T hT t ht => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  obtain ⟨Q, hQ⟩ : ∃ x : ℝ, x = (N : ℝ) * (T + 2) := ⟨_, rfl⟩
  rw [← hQ]
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 < Q := by linarith
  have hNQ : (N : ℝ) ≤ Q := by rw [hQ]; nlinarith
  have hQδ1 : 1 ≤ Q ^ (1 + ε / 8) := Real.one_le_rpow hQ1 (by linarith)
  obtain ⟨N₀, hN₀def⟩ : ∃ n : ℕ, n = ⌈Q ^ (1 + ε / 8)⌉₊ := ⟨_, rfl⟩
  have hN₀ge : Q ^ (1 + ε / 8) ≤ N₀ := by rw [hN₀def]; exact Nat.le_ceil _
  have hN₀le : (N₀ : ℝ) ≤ 2 * Q ^ (1 + ε / 8) := by
    rw [hN₀def]
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ Q ^ (1 + ε / 8))
    linarith
  have hN₀1 : 1 ≤ N₀ := by exact_mod_cast (show (1 : ℝ) ≤ N₀ by linarith)
  have hRN : Rs.card ≤ N := by exact_mod_cast LinnikDensity.card_chars_le Rs
  have hmain := sum_norm_afeD_sq_le_explicit hN₀1 hδ0 (by linarith : ε / 8 ≤ 1 / 2) hc₁5 Rs hRs hT t ht
  refine hmain.trans ?_
  -- the polynomial part
  have hKP : KG3 (ε / 8) T N ≤ A₀ * Q ^ (ε / 8) := by rw [hA₀, hQ]; exact KG3_le hδ0 hT N
  have hKsq : (KG3 (ε / 8) T N / (2 * π)) ^ 2 ≤ (A₀ / (2 * π)) ^ 2 * Q ^ (ε / 4) := by
    have h0 := KG3_nonneg hδ0 T N
    have h1 : (KG3 (ε / 8) T N / (2 * π)) ^ 2 ≤ (A₀ * Q ^ (ε / 8) / (2 * π)) ^ 2 := by gcongr
    have h2 : (Q ^ (ε / 8)) ^ 2 = Q ^ (ε / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; congr 1; push_cast; ring
    calc _ ≤ _ := h1
      _ = (A₀ / (2 * π)) ^ 2 * (Q ^ (ε / 8)) ^ 2 := by ring
      _ = _ := by rw [h2]
  have hLS : LSb Rs.card N N₀ (T + 1) ≤ CL * Q ^ (1 + ε / 4) := by
    have h1 := LSb_le hRN hN₀1 hT
    rw [← hQ] at h1
    have hN₀r : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀1
    have hQQ : Q ≤ Q ^ (1 + ε / 8) := by
      calc Q = Q ^ (1 : ℝ) := (Real.rpow_one Q).symm
        _ ≤ Q ^ (1 + ε / 8) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
    have hsum : Q + N₀ ≤ 3 * Q ^ (1 + ε / 8) := by linarith
    have hlog := one_add_log_pow_le (M := 2 * N₀) (a := ε / 8 / 16) (by linarith) (by positivity) 8
    have e8 : ((8 : ℕ) : ℝ) * (ε / 8 / 16) = ε / 8 / 2 := by push_cast; ring
    rw [e8] at hlog
    have h2N : 2 * (N₀ : ℝ) ≤ 4 * Q ^ (2 : ℝ) := by
      have : Q ^ (1 + ε / 8) ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
      linarith
    have hpow : (2 * (N₀ : ℝ)) ^ (ε / 8 / 2) ≤ 4 ^ (ε / 8 / 2) * Q ^ (ε / 8) := by
      calc (2 * (N₀ : ℝ)) ^ (ε / 8 / 2) ≤ (4 * Q ^ (2 : ℝ)) ^ (ε / 8 / 2) :=
            Real.rpow_le_rpow (by positivity) h2N (by positivity)
        _ = 4 ^ (ε / 8 / 2) * (Q ^ (2 : ℝ)) ^ (ε / 8 / 2) := Real.mul_rpow (by norm_num) (by positivity)
        _ = 4 ^ (ε / 8 / 2) * Q ^ (ε / 8) := by
            rw [← Real.rpow_mul hQ0.le]; congr 2; ring
    have hL0 : 0 ≤ (1 + 1 / (ε / 8 / 16)) ^ 8 := by positivity
    have hlog' : (1 + Real.log (2 * N₀)) ^ 8 ≤ (1 + 1 / (ε / 8 / 16)) ^ 8 * (4 ^ (ε / 8 / 2) * Q ^ (ε / 8)) :=
      hlog.trans (mul_le_mul_of_nonneg_left hpow hL0)
    have hc : 0 ≤ 2 + 256 * Real.exp 1 := by positivity
    have hQN0 : 0 ≤ Q + N₀ := by positivity
    have hQe : Q ^ (1 + ε / 8) * Q ^ (ε / 8) = Q ^ (1 + ε / 4) := by
      rw [← Real.rpow_add hQ0]; congr 1; ring
    calc LSb Rs.card N N₀ (T + 1) ≤ (2 + 256 * Real.exp 1) * (Q + N₀) * (1 + Real.log (2 * N₀)) ^ 8 := h1
      _ ≤ (2 + 256 * Real.exp 1) * (3 * Q ^ (1 + ε / 8)) *
          ((1 + 1 / (ε / 8 / 16)) ^ 8 * (4 ^ (ε / 8 / 2) * Q ^ (ε / 8))) := by gcongr
      _ = (2 + 256 * Real.exp 1) * 3 * ((1 + 1 / (ε / 8 / 16)) ^ 8 * 4 ^ (ε / 8 / 2)) *
          (Q ^ (1 + ε / 8) * Q ^ (ε / 8)) := by ring
      _ = CL * Q ^ (1 + ε / 4) := by rw [hQe, hCL]
  have hDP : DPc (ε / 8) T Rs.card N N₀ ≤ (A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂) * Q ^ (1 + ε / 2) := by
    unfold DPc
    rw [← hI₁, ← hI₂]
    have hLS0 : 0 ≤ LSb Rs.card N N₀ (T + 1) := by
      unfold LSb
      have hl : 0 ≤ Real.log (2 * N₀) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀1
        linarith)
      have hl' : 0 ≤ Real.log N₀ := Real.log_nonneg (by exact_mod_cast hN₀1)
      have h3 : 0 ≤ (1 + Real.log (2 * N₀)) ^ 3 := pow_nonneg (by linarith) 3
      have : 0 ≤ (N : ℝ) * (2 * (T + 1) + 1) := by positivity
      positivity
    have hQe : Q ^ (ε / 4) * Q ^ (1 + ε / 4) = Q ^ (1 + ε / 2) := by
      rw [← Real.rpow_add hQ0]; congr 1; ring
    calc (KG3 (ε / 8) T N / (2 * π)) ^ 2 * I₁ * (LSb Rs.card N N₀ (T + 1) * I₂)
        ≤ ((A₀ / (2 * π)) ^ 2 * Q ^ (ε / 4)) * I₁ * ((CL * Q ^ (1 + ε / 4)) * I₂) := by gcongr
      _ = (A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂) * (Q ^ (ε / 4) * Q ^ (1 + ε / 4)) := by ring
      _ = _ := by rw [hQe]
  -- the tail part
  have hBT : BTc (5 / (ε / 8)) T N N₀ ≤ A₁ / (2 * π) * (2 * I₃) := by
    unfold BTc
    rw [← hI₃]
    have hK := KG3_le hc₁0 hT N
    rw [← hA₁, ← hQ] at hK
    have hK0 := KG3_nonneg hc₁0 T N
    have hN₀p : (N₀ : ℝ) ^ (5 / 2 - 5 / (ε / 8)) ≤ (Q ^ (1 + ε / 8)) ^ (5 / 2 - 5 / (ε / 8)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hN₀ge (by linarith)
    rw [← Real.rpow_mul hQ0.le] at hN₀p
    have hexp : Q ^ (5 / (ε / 8)) * Q ^ ((1 + ε / 8) * (5 / 2 - 5 / (ε / 8))) ≤ 1 := by
      rw [← Real.rpow_add hQ0]
      refine Real.rpow_le_one_of_one_le_of_nonpos hQ1 ?_
      have e : 5 / (ε / 8) + (1 + ε / 8) * (5 / 2 - 5 / (ε / 8)) =
          5 / 2 + 5 / 2 * (ε / 8) - ε / 8 * (5 / (ε / 8)) := by ring
      rw [e, hδc]
      linarith
    have hpos : 0 ≤ (N₀ : ℝ) ^ (5 / 2 - 5 / (ε / 8)) := by positivity
    calc KG3 (5 / (ε / 8)) T N / (2 * π) * (2 * (N₀ : ℝ) ^ (5 / 2 - 5 / (ε / 8)) * I₃)
        ≤ A₁ * Q ^ (5 / (ε / 8)) / (2 * π) * (2 * Q ^ ((1 + ε / 8) * (5 / 2 - 5 / (ε / 8))) * I₃) := by
          gcongr
      _ = A₁ / (2 * π) * (2 * I₃) * (Q ^ (5 / (ε / 8)) * Q ^ ((1 + ε / 8) * (5 / 2 - 5 / (ε / 8)))) := by
          ring
      _ ≤ A₁ / (2 * π) * (2 * I₃) * 1 := by
          gcongr
      _ = _ := mul_one _
  have hBT0 : 0 ≤ BTc (5 / (ε / 8)) T N N₀ := by
    unfold BTc
    have := KG3_nonneg hc₁0 T N
    have : 0 ≤ ∫ v, Wf (5 / (ε / 8) + 1 / 2) v := (integral_Wf_pos (by linarith)).le
    positivity
  -- assemble
  have hQ2 : Q ^ (1 + ε / 2) ≤ Q ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hQ3 : Q ≤ Q ^ (1 + ε) := by
    calc Q = Q ^ (1 : ℝ) := (Real.rpow_one Q).symm
      _ ≤ Q ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : (Rs.card : ℝ) ≤ Q := (LinnikDensity.card_chars_le Rs).trans hNQ
  have hBT2 : BTc (5 / (ε / 8)) T N N₀ ^ 2 ≤ (A₁ / (2 * π) * (2 * I₃)) ^ 2 := pow_le_pow_left₀ hBT0 hBT 2
  have hCP0 : 0 ≤ (A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂) := by positivity
  have hCT0 : 0 ≤ (A₁ / (2 * π) * (2 * I₃)) ^ 2 := sq_nonneg _
  have hR0 : (0 : ℝ) ≤ Rs.card := Nat.cast_nonneg _
  have hQe0 : 0 ≤ Q ^ (1 + ε) := by positivity
  calc 2 * DPc (ε / 8) T Rs.card N N₀ + 2 * (Rs.card * BTc (5 / (ε / 8)) T N N₀ ^ 2)
      ≤ 2 * ((A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂) * Q ^ (1 + ε)) +
        2 * (Q ^ (1 + ε) * (A₁ / (2 * π) * (2 * I₃)) ^ 2) := by
        gcongr
        · exact hDP.trans (mul_le_mul_of_nonneg_left hQ2 hCP0)
        · exact hR.trans hQ3
    _ = (2 * ((A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂)) + 2 * (A₁ / (2 * π) * (2 * I₃)) ^ 2) * Q ^ (1 + ε) := by
        ring

/-! ### The fourth moment at one modulus -/

/-- **The hybrid fourth moment at one modulus, for primitive characters**: for every `0 < ε ≤ 1` there is `C` with
`Σ_χ |L(½ + it_χ, χ)|⁴ ≤ C(N(T + 2))^{1+ε}` for every set of primitive characters `χ ≠ 1` mod `N` and points
`|t_χ| ≤ T`: `norm_LFunction_four_le`, and `sum_norm_afeD_sq_le` for the characters and for their inverses. -/
theorem fourth_moment_primitive {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (Rs : Finset (DirichletCharacter ℂ N)), (∀ χ ∈ Rs, χ.IsPrimitive ∧ χ ≠ 1) →
      ∀ T : ℝ, 0 ≤ T → ∀ t : DirichletCharacter ℂ N → ℝ, (∀ χ ∈ Rs, |t χ| ≤ T) →
        ∑ χ ∈ Rs, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C * ((N : ℝ) * (T + 2)) ^ (1 + ε) := by
  obtain ⟨C, hC⟩ := sum_norm_afeD_sq_le hε hε1
  refine ⟨4 * C, fun N _ Rs hRs T hT t ht => ?_⟩
  have h1 : ∀ χ ∈ Rs, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤
      2 * ‖afeD χ (1 / 2 + t χ * I)‖ ^ 2 + 2 * ‖afeD χ⁻¹ (1 / 2 + ((-t χ : ℝ) : ℂ) * I)‖ ^ 2 :=
    fun χ hχ => norm_LFunction_four_le (hRs χ hχ).1 (hRs χ hχ).2 (t χ)
  have hA := hC N Rs (fun χ hχ => (hRs χ hχ).2) T hT t ht
  have hB := hC N (Rs.image (·⁻¹))
    (fun ψ hψ => by
      obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hψ
      exact inv_ne_one.2 (hRs χ hχ).2) T hT (fun ψ => -t ψ⁻¹)
    (fun ψ hψ => by
      obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hψ
      simp only [inv_inv, abs_neg]; exact ht χ hχ)
  have hsum' : ∑ χ ∈ Rs, ‖afeD χ⁻¹ (1 / 2 + ((-t χ : ℝ) : ℂ) * I)‖ ^ 2 =
      ∑ ψ ∈ Rs.image (·⁻¹), ‖afeD ψ (1 / 2 + ((-t ψ⁻¹ : ℝ) : ℂ) * I)‖ ^ 2 := by
    rw [Finset.sum_image (fun χ _ ψ _ h => inv_injective h)]
    refine sum_congr rfl fun χ _ => ?_
    simp only [inv_inv]
  calc ∑ χ ∈ Rs, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4
      ≤ ∑ χ ∈ Rs, (2 * ‖afeD χ (1 / 2 + t χ * I)‖ ^ 2 +
          2 * ‖afeD χ⁻¹ (1 / 2 + ((-t χ : ℝ) : ℂ) * I)‖ ^ 2) := sum_le_sum h1
    _ = 2 * ∑ χ ∈ Rs, ‖afeD χ (1 / 2 + t χ * I)‖ ^ 2 +
          2 * ∑ χ ∈ Rs, ‖afeD χ⁻¹ (1 / 2 + ((-t χ : ℝ) : ℂ) * I)‖ ^ 2 := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ 2 * (C * ((N : ℝ) * (T + 2)) ^ (1 + ε)) + 2 * (C * ((N : ℝ) * (T + 2)) ^ (1 + ε)) := by
        rw [hsum']
        exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 2))
    _ = 4 * C * ((N : ℝ) * (T + 2)) ^ (1 + ε) := by ring

end LinnikFourth

namespace LinnikFourth

/-! ### Every character `χ ≠ 1` mod `q` -/

/-- The primitive character of `χ` as a character mod `N` when `N` is the conductor of `χ` (and `1` otherwise). -/
def toPrim {q : ℕ} (N : ℕ) (χ : DirichletCharacter ℂ q) : DirichletCharacter ℂ N :=
  if h : χ.conductor = N then h ▸ χ.primitiveCharacter else 1

lemma toPrim_self {q : ℕ} (χ : DirichletCharacter ℂ q) : toPrim χ.conductor χ = χ.primitiveCharacter := by
  simp [toPrim]

lemma toPrim_isPrimitive {q N : ℕ} {χ : DirichletCharacter ℂ q} (h : χ.conductor = N) :
    (toPrim N χ).IsPrimitive := by
  subst h; rw [toPrim_self]; exact χ.primitiveCharacter_isPrimitive

lemma changeLevel_toPrim {q N : ℕ} {χ : DirichletCharacter ℂ q} (h : χ.conductor = N) (hN : N ∣ q) :
    changeLevel hN (toPrim N χ) = χ := by
  subst h; rw [toPrim_self]; exact χ.changeLevel_primitiveCharacter

lemma toPrim_ne_one {q N : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (h : χ.conductor = N) (hN : N ∣ q) :
    toPrim N χ ≠ 1 := by
  intro h1
  apply hχ
  rw [← changeLevel_toPrim h hN, h1, changeLevel_one]

/-- `|L(½ + it, χ)| ≤ ∏_{p | q}(1 + p^{−1/2})·|L(½ + it, χ*)|` for `χ ≠ 1` mod `q` with primitive character `χ*`
mod the conductor `N` (Mathlib's `LFunction_changeLevel`, as in round 522's `LinnikSubconvex.critBoundχ`). -/
lemma norm_LFunction_le_toPrim {q N : ℕ} [NeZero q] [NeZero N] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (h : χ.conductor = N) (t : ℝ) :
    ‖LFunction χ (1 / 2 + t * I)‖ ≤
      (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)))) * ‖LFunction (toPrim N χ) (1 / 2 + t * I)‖ := by
  have hN : N ∣ q := h ▸ χ.conductor_dvd_level
  have hχ' : toPrim N χ ≠ 1 := toPrim_ne_one hχ h hN
  have hsre : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
  have hL : LFunction χ (1 / 2 + t * I) = LFunction (toPrim N χ) (1 / 2 + t * I) *
      ∏ p ∈ q.primeFactors, (1 - toPrim N χ p * (p : ℂ) ^ (-(1 / 2 + t * I))) := by
    have h' := LFunction_changeLevel hN (toPrim N χ) (s := 1 / 2 + t * I) (Or.inl hχ')
    rwa [changeLevel_toPrim h hN] at h'
  have hfac : ∀ p ∈ q.primeFactors, ‖1 - toPrim N χ p * (p : ℂ) ^ (-(1 / 2 + t * I))‖ ≤
      1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro p hp
    have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_natCast_cpow_of_pos hp0, Complex.neg_re, hsre]
    have := DirichletCharacter.norm_le_one (toPrim N χ) p
    have hp' : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    nlinarith
  rw [hL, norm_mul, norm_prod, mul_comm]
  exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hfac) (norm_nonneg _)

/-- `Σ_{N | q} N^{1+ε} ≤ ζ(1 + ε)q^{1+ε}`, `ζ(1 + ε) = Σ' n^{−(1+ε)}`: `N ↦ q/N` permutes the divisors. -/
lemma sum_divisors_rpow_le {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : q ≠ 0) :
    ∑ N ∈ q.divisors, (N : ℝ) ^ (1 + ε) ≤ (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε)) * (q : ℝ) ^ (1 + ε) := by
  rw [← Nat.sum_div_divisors q (fun N => (N : ℝ) ^ (1 + ε))]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + ε)) := Real.summable_one_div_nat_rpow.2 (by linarith)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hterm : ∀ d ∈ q.divisors, ((q / d : ℕ) : ℝ) ^ (1 + ε) = (q : ℝ) ^ (1 + ε) * (1 / (d : ℝ) ^ (1 + ε)) := by
    intro d hd
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    rw [Nat.cast_div hdq hd0.ne', Real.div_rpow hq0.le hd0.le]
    field_simp
  calc ∑ d ∈ q.divisors, ((q / d : ℕ) : ℝ) ^ (1 + ε)
      = (q : ℝ) ^ (1 + ε) * ∑ d ∈ q.divisors, 1 / (d : ℝ) ^ (1 + ε) := by
        rw [sum_congr rfl hterm, ← mul_sum]
    _ ≤ (q : ℝ) ^ (1 + ε) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε) := by
        gcongr
        exact hsum.sum_le_tsum q.divisors (fun i _ => by positivity)
    _ = _ := mul_comm _ _

/-- **The hybrid fourth moment over the characters mod `q`**: for every `0 < ε ≤ 1` there is `C` with
`Σ_χ |L(½ + it_χ, χ)|⁴ ≤ C(q(T + 2))^{1+ε}` for every set of characters `χ ≠ 1` mod `q` and points `|t_χ| ≤ T`.
Group the characters by conductor `N | q`; on each group `χ ↦ χ*` is injective (`changeLevel_toPrim`), so
`fourth_moment_primitive` at modulus `N` applies; then `norm_LFunction_le_toPrim`, `prod_primeFactors_le` and
`sum_divisors_rpow_le`. -/
theorem fourth_moment {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (Rs : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ Rs, χ ≠ 1) →
      ∀ T : ℝ, 0 ≤ T → ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ Rs, |t χ| ≤ T) →
        ∑ χ ∈ Rs, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C * ((q : ℝ) * (T + 2)) ^ (1 + ε) := by
  obtain ⟨C₀, hC₀⟩ := fourth_moment_primitive (half_pos hε) (by linarith)
  have hη0 : 0 < ε / 8 := by positivity
  obtain ⟨B, hB⟩ : ∃ x : ℝ, x = (2 : ℝ) ^ ⌈Real.exp (1 / (ε / 8))⌉₊ := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ x : ℝ, x = ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε / 2) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hZ0 : 0 ≤ Z := by rw [hZ]; exact tsum_nonneg fun n => by positivity
  set C₁ := max C₀ 0 with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  refine ⟨B ^ 4 * C₁ * Z, fun q _ Rs hRs T hT t ht => ?_⟩
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq0
  obtain ⟨P, hP⟩ : ∃ x : ℝ, x = ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ))) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; exact Finset.prod_nonneg fun p _ => by positivity
  have hPB : P ≤ B * (q : ℝ) ^ (ε / 8) := by rw [hP, hB]; exact LinnikSubconvex.prod_primeFactors_le hη0 hq0
  -- each conductor
  have hfib : ∀ N ∈ q.divisors, ∑ χ ∈ Rs with χ.conductor = N, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤
      P ^ 4 * (C₁ * ((N : ℝ) * (T + 2)) ^ (1 + ε / 2)) := by
    intro N hNd
    have hN : N ∣ q := Nat.dvd_of_mem_divisors hNd
    have : NeZero N := ⟨(Nat.pos_of_mem_divisors hNd).ne'⟩
    have h1 : ∀ χ ∈ Rs.filter (fun χ => χ.conductor = N), ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤
        P ^ 4 * ‖LFunction (toPrim N χ) (1 / 2 + t χ * I)‖ ^ 4 := by
      intro χ hχ
      obtain ⟨hχR, hcN⟩ := Finset.mem_filter.1 hχ
      have h := norm_LFunction_le_toPrim (hRs χ hχR) hcN (t χ)
      rw [← hP] at h
      calc ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ (P * ‖LFunction (toPrim N χ) (1 / 2 + t χ * I)‖) ^ 4 :=
            pow_le_pow_left₀ (norm_nonneg _) h 4
        _ = P ^ 4 * ‖LFunction (toPrim N χ) (1 / 2 + t χ * I)‖ ^ 4 := by ring
    have h2 := hC₀ N ((Rs.filter fun χ => χ.conductor = N).image (toPrim N))
      (fun ψ hψ => by
        obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hψ
        obtain ⟨hχR, hcN⟩ := Finset.mem_filter.1 hχ
        exact ⟨toPrim_isPrimitive hcN, toPrim_ne_one (hRs χ hχR) hcN hN⟩)
      T hT (fun ψ => t (changeLevel hN ψ))
      (fun ψ hψ => by
        obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hψ
        obtain ⟨hχR, hcN⟩ := Finset.mem_filter.1 hχ
        simp only [changeLevel_toPrim hcN hN]
        exact ht χ hχR)
    rw [Finset.sum_image (fun χ₁ h₁ χ₂ h₂ h => by
      rw [← changeLevel_toPrim (Finset.mem_filter.1 h₁).2 hN, ← changeLevel_toPrim (Finset.mem_filter.1 h₂).2 hN,
        h])] at h2
    have h3 : ∑ χ ∈ Rs with χ.conductor = N, ‖LFunction (toPrim N χ) (1 / 2 + t χ * I)‖ ^ 4 ≤
        C₀ * ((N : ℝ) * (T + 2)) ^ (1 + ε / 2) := by
      refine le_of_eq_of_le (sum_congr rfl fun χ hχ => ?_) h2
      rw [changeLevel_toPrim (Finset.mem_filter.1 hχ).2 hN]
    have hpow0 : 0 ≤ ((N : ℝ) * (T + 2)) ^ (1 + ε / 2) := by positivity
    calc ∑ χ ∈ Rs with χ.conductor = N, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4
        ≤ ∑ χ ∈ Rs with χ.conductor = N, P ^ 4 * ‖LFunction (toPrim N χ) (1 / 2 + t χ * I)‖ ^ 4 :=
          sum_le_sum h1
      _ = P ^ 4 * ∑ χ ∈ Rs with χ.conductor = N, ‖LFunction (toPrim N χ) (1 / 2 + t χ * I)‖ ^ 4 := by
          rw [mul_sum]
      _ ≤ P ^ 4 * (C₁ * ((N : ℝ) * (T + 2)) ^ (1 + ε / 2)) := by
          gcongr
          exact h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0)
  -- sum over the conductors
  have hmaps : ∀ χ ∈ Rs, χ.conductor ∈ q.divisors := fun χ _ =>
    Nat.mem_divisors.2 ⟨χ.conductor_dvd_level, hq0⟩
  have hT2 : (0 : ℝ) < T + 2 := by linarith
  have hdiv := sum_divisors_rpow_le (half_pos hε) hq0
  rw [← hZ] at hdiv
  have hsplit : ∀ N ∈ q.divisors, ((N : ℝ) * (T + 2)) ^ (1 + ε / 2) = (N : ℝ) ^ (1 + ε / 2) * (T + 2) ^ (1 + ε / 2) :=
    fun N _ => Real.mul_rpow (Nat.cast_nonneg N) hT2.le
  have hP4 : P ^ 4 ≤ B ^ 4 * (q : ℝ) ^ (ε / 2) := by
    calc P ^ 4 ≤ (B * (q : ℝ) ^ (ε / 8)) ^ 4 := pow_le_pow_left₀ hP0 hPB 4
      _ = B ^ 4 * ((q : ℝ) ^ (ε / 8)) ^ 4 := by ring
      _ = B ^ 4 * (q : ℝ) ^ (ε / 2) := by
          have e : ((q : ℝ) ^ (ε / 8)) ^ 4 = (q : ℝ) ^ (ε / 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
          rw [e]
  have hQ1 : 1 ≤ (q : ℝ) * (T + 2) := by nlinarith
  have hqQ : (q : ℝ) ^ (ε / 2) ≤ ((q : ℝ) * (T + 2)) ^ (ε / 2) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
  have hfin : ((q : ℝ) * (T + 2)) ^ (ε / 2) * ((q : ℝ) * (T + 2)) ^ (1 + ε / 2) =
      ((q : ℝ) * (T + 2)) ^ (1 + ε) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ N ∈ q.divisors, ∑ χ ∈ Rs with χ.conductor = N, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4
      ≤ ∑ N ∈ q.divisors, P ^ 4 * (C₁ * ((N : ℝ) * (T + 2)) ^ (1 + ε / 2)) := sum_le_sum hfib
    _ = P ^ 4 * C₁ * (T + 2) ^ (1 + ε / 2) * ∑ N ∈ q.divisors, (N : ℝ) ^ (1 + ε / 2) := by
        rw [mul_sum]
        refine sum_congr rfl fun N hN => ?_
        rw [hsplit N hN]; ring
    _ ≤ P ^ 4 * C₁ * (T + 2) ^ (1 + ε / 2) * (Z * (q : ℝ) ^ (1 + ε / 2)) := by gcongr
    _ = P ^ 4 * (C₁ * Z) * ((q : ℝ) * (T + 2)) ^ (1 + ε / 2) := by
        rw [Real.mul_rpow (by linarith) hT2.le]; ring
    _ ≤ (B ^ 4 * ((q : ℝ) * (T + 2)) ^ (ε / 2)) * (C₁ * Z) * ((q : ℝ) * (T + 2)) ^ (1 + ε / 2) := by
        gcongr
        exact hP4.trans (mul_le_mul_of_nonneg_left hqQ (by positivity))
    _ = B ^ 4 * C₁ * Z * (((q : ℝ) * (T + 2)) ^ (ε / 2) * ((q : ℝ) * (T + 2)) ^ (1 + ε / 2)) := by ring
    _ = B ^ 4 * C₁ * Z * ((q : ℝ) * (T + 2)) ^ (1 + ε) := by rw [hfin]

end LinnikFourth

#print axioms LinnikFourth.norm_LFunction_four_le
#print axioms LinnikFourth.sum_norm_Pd_sq_le
#print axioms LinnikFourth.afeJ_split
#print axioms LinnikFourth.sum_norm_afeD_sq_le
#print axioms LinnikFourth.fourth_moment_primitive
#print axioms LinnikFourth.fourth_moment
