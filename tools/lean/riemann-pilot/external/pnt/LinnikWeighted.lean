/-
# Round 526, part 3: the Halász–Montgomery inequality with a smooth weight, its kernel through the primitive
# character, and the product trick

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

* `hm_duality_W`: round 525's `LinnikPower.hm_duality` with the weight `W(n) = e^{−n/U} − e^{−2n/U}`. If `W ≥ c₀ > 0`
  on `S`, then `(Σ_{χ∈R}|F(χ, β_χ + iγ_χ)|)² ≤ c₀⁻¹Σ_n|a_n|²n^{−2σ}·Σ_{χ,χ′∈R}|H_U(χχ′⁻¹, z_{χχ′})|` with
  `H_U(ψ, z) = Σ_{n≥1}ψ(n)n^{−z}W(n)` and `z_{χχ′} = β_χ + β_χ′ − 2σ + i(γ_χ − γ_χ′)`. On the diagonal,
  `|H_U(ψ, z)| ≤ U` for `Re z ≥ 0` (`norm_tsum_hTerm_le`).
* `hTerm_tsum_eq`: `H_U(ψ, z) = (1/2π)∫ L(z + c + iv, ψ)kW_U(c + iv) dv` for `ψ ≠ 1`, `U ≥ 2`, `0 ≤ Re z ≤ 1` and
  `0 < c ≤ 2` (round 525's `LinnikOffDiag.kTerm_tsum_eq` at `U` and at `U/2`).
* `integral_dsum`: through the primitive character `ψ*` of `ψ`,
  `∫ L(z + c + iv, ψ)kW_U(c + iv) dv = Σ_T(−1)^{|T|}ψ*(d_T)d_T^{−z}∫ L(z + c + iv, ψ*)kW_{U/d_T}(c + iv) dv`, the sum
  over the sets `T` of primes dividing `q`, `d_T = ∏_{p∈T} p` (Mathlib's `LFunction_changeLevel`).
* `norm_hTerm_le_reflect`: part 2's `reflect` in each term, for any truncations `Z_T`:
  `|H_U(ψ, z)| ≤ (1/2π)Σ_T(∫|kW·Φ·Σ_{m ≤ Z_T}| + ∫|kW·Φ·Σ_{m > Z_T}|)` with `Λ = U/d_T`.
* `pv_mul`, `mass_mulCo_le`: the product of two Dirichlet polynomials is the polynomial with the convolved
  coefficients, and `Σ_k|c_k|² ≤ τΣ|b_n|²Σ|e_m|²` when `d(k) ≤ τ` on its support.
* `ls_pv_dyadic`: round 521's `large_values_chars_off` on the dyadic pieces of `[2, X]`, with Cauchy–Schwarz over the
  pieces.
* `huxley_core`, the product trick: if `|F(χ, u_χ)| ≥ V > 0` for every `χ ∈ Rs`, `F` on `[2, N]`, then for every
  polynomial `E` on `[1, K]`, `(Σ_χ|E(χ, u_χ)|)² ≤ V^{−2}|Rs|·LSX(NK)·τΣ|b_n|²Σ|e_m|²` with `d(k) ≤ τ` for `k ≤ NK`.
-/

import LinnikReflect

open Complex Real Finset MeasureTheory Set Filter Topology

noncomputable section

namespace LinnikReflect

open DirichletCharacter LinnikPower

variable {q : ℕ}

/-! ### The Halász–Montgomery inequality with the weight `e^{−n/U} − e^{−2n/U}` -/

/-- The `n`-th term of `H_U(ψ, z) = Σ_{n≥1} ψ(n)n^{−z}(e^{−n/U} − e^{−2n/U})`. -/
def hTerm (ψ : DirichletCharacter ℂ q) (U : ℝ) (z : ℂ) (n : ℕ) : ℂ := kTerm ψ U z n - kTerm ψ (U / 2) z n

/-- The weight `e^{−n/U} − e^{−2n/U}` for `n ≥ 1` (and `1` at `n = 0`). -/
def wW (U : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else Real.exp (-((n : ℝ) / U)) - Real.exp (-((n : ℝ) / (U / 2)))

lemma wW_pos {U : ℝ} (hU : 0 < U) (n : ℕ) : 0 < wW U n := by
  unfold wW
  split_ifs with hn
  · exact one_pos
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have : (n : ℝ) / U < (n : ℝ) / (U / 2) := by
      rw [div_lt_div_iff₀ hU (by positivity)]; nlinarith
    have := Real.exp_lt_exp.2 (neg_lt_neg this)
    linarith

lemma hTerm_eq (ψ : DirichletCharacter ℂ q) (U : ℝ) (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    hTerm ψ U z n = (wW U n : ℂ) * (ψ n * (n : ℂ) ^ (-z)) := by
  unfold hTerm kTerm wW
  simp only [hn, ite_false]
  push_cast
  ring

lemma norm_hTerm_le (ψ : DirichletCharacter ℂ q) {U : ℝ} (hU : 0 < U) {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    ‖hTerm ψ U z n‖ ≤ wt U n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hTerm, kTerm, wt]
  · rw [hTerm_eq ψ U z hn, norm_mul, Complex.norm_real]
    have hw := wW_pos hU n
    rw [Real.norm_of_nonneg hw.le]
    have h1 : wW U n ≤ wt U n := by
      unfold wW wt; simp only [hn, ite_false]
      have := Real.exp_pos (-((n : ℝ) / (U / 2)))
      linarith
    have h2 : ‖ψ n * (n : ℂ) ^ (-z)‖ ≤ 1 := by
      rw [norm_mul]
      have h3 := DirichletCharacter.norm_le_one ψ n
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
      have h4 : ‖(n : ℂ) ^ (-z)‖ ≤ 1 := by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by simp; linarith)
      calc ‖ψ n‖ * ‖(n : ℂ) ^ (-z)‖ ≤ 1 * 1 := mul_le_mul h3 h4 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc wW U n * ‖ψ n * (n : ℂ) ^ (-z)‖ ≤ wt U n * 1 := mul_le_mul h1 h2 (norm_nonneg _) (wt_nonneg U n)
      _ = wt U n := mul_one _

lemma summable_hTerm (ψ : DirichletCharacter ℂ q) {U : ℝ} (hU : 0 < U) {z : ℂ} (hz : 0 ≤ z.re) :
    Summable (hTerm ψ U z) :=
  Summable.of_norm_bounded (wt_summable_le hU).1 (norm_hTerm_le ψ hU hz)

/-- **The Halász–Montgomery inequality with the weight `W(n) = e^{−n/U} − e^{−2n/U}`**: if `W ≥ c₀ > 0` on `S`,
then `(Σ_{χ∈R} |F(χ, β_χ + iγ_χ)|)² ≤ c₀⁻¹·Σ_n |a_n|²n^{−2σ}·Σ_{χ,χ′∈R} |H_U(χχ′⁻¹, z_{χχ′})|` with
`z_{χχ′} = β_χ + β_χ′ − 2σ + i(γ_χ − γ_χ′)`. The proof is round 525's `LinnikPower.hm_duality` with this weight. -/
theorem hm_duality_W {R : Finset (DirichletCharacter ℂ q)} {S : Finset ℕ} (hS0 : 0 ∉ S) {U c₀ : ℝ} (hU : 0 < U)
    (hc₀ : 0 < c₀) (hSW : ∀ n ∈ S, c₀ ≤ wW U n) (a : ℕ → ℂ) {σ : ℝ} (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ R, σ ≤ β χ) :
    (∑ χ ∈ R, ‖pv S a χ ((β χ : ℂ) + γ χ * I)‖) ^ 2 ≤
      c₀⁻¹ * (∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) *
        ∑ χ ∈ R, ∑ χ' ∈ R, ‖∑' n : ℕ, hTerm (χ * χ'⁻¹) U
          (((β χ + β χ' - 2 * σ : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I) n‖ := by
  classical
  set u : DirichletCharacter ℂ q → ℂ := fun χ => ((β χ - σ : ℝ) : ℂ) + (γ χ : ℂ) * I with hu
  set D : DirichletCharacter ℂ q → ℂ := fun χ => pv S a χ ((β χ : ℂ) + γ χ * I) with hD
  set η : DirichletCharacter ℂ q → ℂ := fun χ => phase (D χ) with hη
  set Φ : ℕ → ℂ := fun n => ∑ χ ∈ R, η χ * χ n * (n : ℂ) ^ (-u χ) with hΦ
  set x : ℕ → ℂ := fun n => a n * (n : ℂ) ^ (-(σ : ℂ)) with hx
  have hηD : ∀ χ, η χ * D χ = (‖D χ‖ : ℂ) := fun χ => phase_mul (D χ)
  have h1 : ((∑ χ ∈ R, ‖D χ‖ : ℝ) : ℂ) = ∑ n ∈ S, x n * Φ n := by
    push_cast
    rw [← sum_congr rfl fun χ _ => hηD χ]
    simp only [hD, pv, hΦ, hx, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun n hn => sum_congr rfl fun χ _ => ?_
    have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
    rw [cpow_split hn0 σ (β χ) (γ χ)]
    simp only [hu]
    ring
  have hnx : ∀ n ∈ S, ‖x n‖ = ‖a n‖ * (n : ℝ) ^ (-σ) := by
    intro n hn
    have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
    rw [hx, norm_mul, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0)]
    simp
  set w : ℕ → ℝ := wW U with hw
  have hwpos : ∀ n, 0 < w n := fun n => wW_pos hU n
  have hcs : (∑ n ∈ S, ‖x n‖ * ‖Φ n‖) ^ 2 ≤ (∑ n ∈ S, ‖x n‖ ^ 2 / w n) * (∑ n ∈ S, w n * ‖Φ n‖ ^ 2) := by
    have h := sum_mul_sq_le_sq_mul_sq S (fun n => ‖x n‖ * (Real.sqrt (w n))⁻¹) (fun n => Real.sqrt (w n) * ‖Φ n‖)
    have e1 : ∀ n, ‖x n‖ * (Real.sqrt (w n))⁻¹ * (Real.sqrt (w n) * ‖Φ n‖) = ‖x n‖ * ‖Φ n‖ := fun n => by
      have : Real.sqrt (w n) ≠ 0 := (Real.sqrt_pos.2 (hwpos n)).ne'
      field_simp
    have e2 : ∀ n, (‖x n‖ * (Real.sqrt (w n))⁻¹) ^ 2 = ‖x n‖ ^ 2 / w n := fun n => by
      rw [mul_pow, inv_pow, Real.sq_sqrt (hwpos n).le, div_eq_mul_inv]
    have e3 : ∀ n, (Real.sqrt (w n) * ‖Φ n‖) ^ 2 = w n * ‖Φ n‖ ^ 2 := fun n => by
      rw [mul_pow, Real.sq_sqrt (hwpos n).le]
    simp only [e1, e2, e3] at h
    exact h
  have hG : ∑ n ∈ S, ‖x n‖ ^ 2 / w n ≤ c₀⁻¹ * ∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    rw [hnx n hn, div_eq_mul_inv]
    have h0 : (w n)⁻¹ ≤ c₀⁻¹ := inv_anti₀ hc₀ (hSW n hn)
    calc (‖a n‖ * (n : ℝ) ^ (-σ)) ^ 2 * (w n)⁻¹ ≤ (‖a n‖ * (n : ℝ) ^ (-σ)) ^ 2 * c₀⁻¹ := by gcongr
      _ = c₀⁻¹ * (‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) := by ring
  set z : DirichletCharacter ℂ q → DirichletCharacter ℂ q → ℂ :=
    fun χ χ' => ((β χ + β χ' - 2 * σ : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I with hz
  have hzre : ∀ χ ∈ R, ∀ χ' ∈ R, 0 ≤ (z χ χ').re := by
    intro χ hχ χ' hχ'
    simp only [hz, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
    linarith [hβ χ hχ, hβ χ' hχ']
  have hzu : ∀ χ χ', z χ χ' = u χ + (starRingEnd ℂ) (u χ') := by
    intro χ χ'
    simp only [hz, hu, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  set F : ℕ → ℂ := fun n => ∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') * hTerm (χ * χ'⁻¹) U (z χ χ') n
    with hF
  have hFeq : ∀ n, n ≠ 0 → F n = (w n : ℂ) * Φ n * (starRingEnd ℂ) (Φ n) := by
    intro n hn
    have hterm : ∀ χ χ', hTerm (χ * χ'⁻¹) U (z χ χ') n
        = (w n : ℂ) * (χ n * (n : ℂ) ^ (-u χ)) * (starRingEnd ℂ) (χ' n * (n : ℂ) ^ (-u χ')) := by
      intro χ χ'
      rw [hTerm_eq _ U _ hn]
      rw [MulChar.mul_apply, ← MulChar.star_apply', hzu, ← cpow_mul_conj_cpow hn, map_mul, Complex.star_def]
      ring
    have hΦexp : (w n : ℂ) * Φ n * (starRingEnd ℂ) (Φ n) = ∑ χ ∈ R, ∑ χ' ∈ R,
        (w n : ℂ) * (η χ * χ n * (n : ℂ) ^ (-u χ)) * (starRingEnd ℂ) (η χ' * χ' n * (n : ℂ) ^ (-u χ')) := by
      simp only [hΦ, map_sum]
      rw [mul_assoc, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun χ _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun χ' _ => ?_
      ring
    rw [hΦexp]
    simp only [hF]
    refine sum_congr rfl fun χ _ => sum_congr rfl fun χ' _ => ?_
    rw [hterm, map_mul, map_mul, map_mul]
    ring
  have hF0 : F 0 = 0 := by simp [hF, hTerm, kTerm]
  have hFre : ∀ n, (F n).re = (if n = 0 then 0 else w n * ‖Φ n‖ ^ 2) := by
    intro n
    split_ifs with hn
    · rw [hn, hF0]; simp
    · rw [hFeq n hn, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsumk : ∀ χ ∈ R, ∀ χ' ∈ R, Summable (hTerm (χ * χ'⁻¹) U (z χ χ')) :=
    fun χ hχ χ' hχ' => summable_hTerm _ hU (hzre χ hχ χ' hχ')
  have hηle : ∀ χ, ‖η χ‖ ≤ 1 := fun χ => norm_phase_le _
  have hFsum : Summable F := by
    simp only [hF]
    refine summable_sum fun χ hχ => summable_sum fun χ' hχ' => (hsumk χ hχ χ' hχ').mul_left _
  have hFbd : ∀ n, ‖F n‖ ≤ (R.card : ℝ) ^ 2 * wt U n := by
    intro n
    simp only [hF]
    calc ‖∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') * hTerm (χ * χ'⁻¹) U (z χ χ') n‖
        ≤ ∑ χ ∈ R, ∑ χ' ∈ R, ‖η χ * (starRingEnd ℂ) (η χ') * hTerm (χ * χ'⁻¹) U (z χ χ') n‖ :=
          (norm_sum_le _ _).trans (sum_le_sum fun χ _ => norm_sum_le _ _)
      _ ≤ ∑ _χ ∈ R, ∑ _χ' ∈ R, wt U n := by
          refine sum_le_sum fun χ hχ => sum_le_sum fun χ' hχ' => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj]
          have h1 := hηle χ
          have h2 := hηle χ'
          have h3 := norm_hTerm_le (χ * χ'⁻¹) hU (hzre χ hχ χ' hχ') n
          have h0 := norm_nonneg (hTerm (χ * χ'⁻¹) U (z χ χ') n)
          calc ‖η χ‖ * ‖η χ'‖ * ‖hTerm (χ * χ'⁻¹) U (z χ χ') n‖ ≤ 1 * 1 * wt U n := by gcongr
            _ = wt U n := by ring
      _ = (R.card : ℝ) ^ 2 * wt U n := by rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
  have hwt := wt_summable_le hU
  have hFresum : Summable fun n => (F n).re :=
    Summable.of_norm_bounded (hwt.1.mul_left ((R.card : ℝ) ^ 2))
      (fun n => (Real.norm_eq_abs _).trans_le ((Complex.abs_re_le_norm (F n)).trans (hFbd n)))
  have hFre0 : ∀ n, 0 ≤ (F n).re := fun n => by
    rw [hFre n]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (hwpos n).le (by positivity)
  have h6 : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ ∑' n, (F n).re := by
    have e : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 = ∑ n ∈ S, (F n).re := by
      refine sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
      rw [hFre n, ite_eq_right hn0]
    rw [e]
    exact hFresum.sum_le_tsum S (fun n _ => hFre0 n)
  have h7 : ∑' n, (F n).re ≤ ‖∑' n, F n‖ := by
    rw [← Complex.re_tsum hFsum]; exact Complex.re_le_norm _
  have h8 : ∑' n, F n = ∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') *
      ∑' n, hTerm (χ * χ'⁻¹) U (z χ χ') n := by
    simp only [hF]
    rw [Summable.tsum_finsetSum fun χ hχ => summable_sum fun χ' hχ' => (hsumk χ hχ χ' hχ').mul_left _]
    refine sum_congr rfl fun χ hχ => ?_
    rw [Summable.tsum_finsetSum fun χ' hχ' => (hsumk χ hχ χ' hχ').mul_left _]
    exact sum_congr rfl fun χ' _ => tsum_mul_left
  have h9 : ‖∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') * ∑' n, hTerm (χ * χ'⁻¹) U (z χ χ') n‖
      ≤ ∑ χ ∈ R, ∑ χ' ∈ R, ‖∑' n, hTerm (χ * χ'⁻¹) U (z χ χ') n‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun χ _ => (norm_sum_le _ _).trans (sum_le_sum fun χ' _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have h1 := hηle χ
    have h2 := hηle χ'
    have h0 := norm_nonneg (∑' n, hTerm (χ * χ'⁻¹) U (z χ χ') n)
    calc ‖η χ‖ * ‖η χ'‖ * ‖∑' n, hTerm (χ * χ'⁻¹) U (z χ χ') n‖
        ≤ 1 * 1 * ‖∑' n, hTerm (χ * χ'⁻¹) U (z χ χ') n‖ := by gcongr
      _ = _ := by ring
  have hDnn : 0 ≤ ∑ χ ∈ R, ‖D χ‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hmod : ∑ χ ∈ R, ‖D χ‖ ≤ ∑ n ∈ S, ‖x n‖ * ‖Φ n‖ := by
    have := congrArg norm h1
    rw [Complex.norm_real, Real.norm_of_nonneg hDnn] at this
    rw [this]
    exact (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => norm_mul _ _))
  set HH := ∑ χ ∈ R, ∑ χ' ∈ R, ‖∑' n, hTerm (χ * χ'⁻¹) U (z χ χ') n‖ with hHH
  have hW : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ HH := by
    calc ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ ∑' n, (F n).re := h6
      _ ≤ ‖∑' n, F n‖ := h7
      _ = _ := by rw [h8]
      _ ≤ HH := h9
  have hWnn : 0 ≤ ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 := sum_nonneg fun n _ => mul_nonneg (hwpos n).le (by positivity)
  have hGnn : 0 ≤ ∑ n ∈ S, ‖x n‖ ^ 2 / w n := sum_nonneg fun n _ => div_nonneg (by positivity) (hwpos n).le
  calc (∑ χ ∈ R, ‖pv S a χ ((β χ : ℂ) + γ χ * I)‖) ^ 2 = (∑ χ ∈ R, ‖D χ‖) ^ 2 := rfl
    _ ≤ (∑ n ∈ S, ‖x n‖ * ‖Φ n‖) ^ 2 := pow_le_pow_left₀ hDnn hmod 2
    _ ≤ (∑ n ∈ S, ‖x n‖ ^ 2 / w n) * (∑ n ∈ S, w n * ‖Φ n‖ ^ 2) := hcs
    _ ≤ (c₀⁻¹ * ∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) * HH := mul_le_mul hG hW hWnn (by positivity)

/-- The diagonal: `|H_U(ψ, z)| ≤ U` for `Re z ≥ 0`. -/
theorem norm_tsum_hTerm_le (ψ : DirichletCharacter ℂ q) {U : ℝ} (hU : 0 < U) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖∑' n, hTerm ψ U z n‖ ≤ U := by
  have hwt := wt_summable_le hU
  have hn := norm_hTerm_le ψ hU hz
  have hns : Summable fun n => ‖hTerm ψ U z n‖ := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hn hwt.1
  calc ‖∑' n, hTerm ψ U z n‖ ≤ ∑' n, ‖hTerm ψ U z n‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' n, wt U n := hns.tsum_le_tsum hn hwt.1
    _ ≤ U := hwt.2

/-! ### The weighted sum as an integral, and the reduction to the primitive character -/

/-- `|L(z + w, ψ)| ≤ A(1 + |Im w|)` on `c ≤ Re w ≤ 2`, for `0 ≤ Re z ≤ 1`, with
`A = max 3 (1/c)·(N + 1)(|Im z| + 2)`. -/
lemma norm_LFunction_shift_le {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) {c : ℝ} (hc : 0 < c) {w : ℂ} (hw1 : c ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖LFunction ψ (z + w)‖ ≤ max 3 (1 / c) * ((N : ℝ) + 1) * (|z.im| + 2) * (1 + |w.im|) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have him : |(z + w).im| ≤ |z.im| + |w.im| := by simp only [add_im]; exact abs_add_le _ _
  have hgrow : (|z.im| + |w.im| + 2) ≤ (|z.im| + 2) * (1 + |w.im|) := by
    nlinarith [abs_nonneg z.im, abs_nonneg w.im]
  rcases le_or_gt (1 / 2) (z + w).re with h | h
  · have h3 : (z + w).re ≤ 3 := by simp only [add_re]; linarith
    refine (Linnik.LFunction_growth hψ h h3).trans ?_
    calc 3 * ((N : ℝ) + 1) * (|(z + w).im| + 2) ≤ 3 * ((N : ℝ) + 1) * (|z.im| + |w.im| + 2) := by gcongr
      _ ≤ max 3 (1 / c) * ((N : ℝ) + 1) * ((|z.im| + 2) * (1 + |w.im|)) := by
          gcongr; exact le_max_left _ _
      _ = _ := by ring
  · have hl : c ≤ (z + w).re := by simp only [add_re]; linarith
    refine (LinnikSubconvex.norm_LFunction_strip_le hψ hc hl (by linarith)).trans ?_
    calc ((N : ℝ) + 1) / c * (1 + |(z + w).im|) ≤ ((N : ℝ) + 1) / c * (|z.im| + |w.im| + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 1 / c * ((N : ℝ) + 1) * (|z.im| + |w.im| + 2) := by ring
      _ ≤ max 3 (1 / c) * ((N : ℝ) + 1) * ((|z.im| + 2) * (1 + |w.im|)) := by
          gcongr; exact le_max_right _ _
      _ = _ := by ring

/-- `v ↦ L(z + c + iv, ψ)kW_Λ(c + iv)` is integrable for `ψ ≠ 1`, `Λ > 0`, `0 ≤ Re z ≤ 1`, `0 < c ≤ 2`. -/
lemma integrable_L_kW {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) {Λ : ℝ} (hΛ : 0 < Λ)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) :
    Integrable fun v : ℝ => LFunction ψ (z + (c + v * I)) * kW Λ (c + v * I) := by
  set A := max 3 (1 / c) * ((N : ℝ) + 1) * (|z.im| + 2) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hnp : ∀ v : ℝ, ∀ m : ℕ, ((c : ℂ) + v * I) ≠ -m := by
    intro v m h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hcont : Continuous fun v : ℝ => LFunction ψ (z + (c + v * I)) * kW Λ (c + v * I) := by
    rw [continuous_iff_continuousAt]
    intro v
    have h1 : ContinuousAt (fun v : ℝ => LFunction ψ (z + (c + v * I))) v :=
      ((differentiable_LFunction hψ).continuous.comp (by fun_prop)).continuousAt
    have h2 : ContinuousAt (fun v : ℝ => kW Λ (c + v * I)) v :=
      ContinuousAt.comp (g := kW Λ) (f := fun v : ℝ => (c : ℂ) + v * I)
        (differentiableAt_kW hΛ (hnp v)).continuousAt (by fun_prop)
    exact h1.mul h2
  refine integrable_line (G := fun w => LFunction ψ (z + w) * kW Λ w) hc (le_abs_self c) hcont
    (K := InghamDensity.KG * (3 * Λ ^ c) * A) fun v => ?_

  have hre : ((c : ℂ) + v * I).re = c := by simp
  have him : ((c : ℂ) + v * I).im = v := by simp
  have hG := norm_mul_Gamma_le (w := (c : ℂ) + v * I) (by rw [hre]; linarith) (by rw [hre]; exact hc2)
  rw [him] at hG
  have hL := norm_LFunction_shift_le hψ hz0 hz1 hc (w := (c : ℂ) + v * I) (by rw [hre]) (by rw [hre]; exact hc2)
  rw [him, ← hA] at hL
  have hk : ‖kW Λ ((c : ℂ) + v * I)‖ ≤ ‖Complex.Gamma ((c : ℂ) + v * I)‖ * (3 * Λ ^ c) := by
    unfold kW
    rw [norm_mul]
    have h3 := norm_cpow_sub_half_le hΛ (w := (c : ℂ) + v * I) (by rw [hre]; linarith)
    rw [hre] at h3
    gcongr
  have hv1 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
  have hKG := InghamDensity.KG_pos
  rw [norm_mul]
  have e5 : (1 + |v|) ^ 3 * (1 + |v|) * (1 + |v|) = (1 + |v|) ^ 5 := by ring
  calc ‖(c : ℂ) + v * I‖ * (‖LFunction ψ (z + (c + v * I))‖ * ‖kW Λ (c + v * I)‖) * (1 + |v|) ^ 3
      ≤ ‖(c : ℂ) + v * I‖ * ((A * (1 + |v|)) * (‖Complex.Gamma ((c : ℂ) + v * I)‖ * (3 * Λ ^ c))) *
          (1 + |v|) ^ 3 := by gcongr
    _ = (‖(c : ℂ) + v * I‖ * ‖Complex.Gamma ((c : ℂ) + v * I)‖ * (1 + |v|) ^ 4) * ((3 * Λ ^ c) * A) := by ring
    _ ≤ (‖(c : ℂ) + v * I‖ * ‖Complex.Gamma ((c : ℂ) + v * I)‖ * (1 + |v|) ^ 5) * ((3 * Λ ^ c) * A) := by
        have h45 : (1 + |v|) ^ 4 ≤ (1 + |v|) ^ 5 := pow_le_pow_right₀ hv1 (by norm_num)
        gcongr
    _ ≤ InghamDensity.KG * ((3 * Λ ^ c) * A) := by gcongr
    _ = InghamDensity.KG * (3 * Λ ^ c) * A := by ring

/-- `v ↦ L(z + c + iv, ψ)Γ(c + iv)Λ^{c+iv}` is integrable (round 525's integrand `offG`). -/
lemma integrable_offG {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) {Λ : ℝ} (hΛ : 0 < Λ)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) :
    Integrable fun v : ℝ => LinnikOffDiag.offG ψ Λ z (c + v * I) := by
  set A := max 3 (1 / c) * ((N : ℝ) + 1) * (|z.im| + 2) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hcont : Continuous fun v : ℝ => LinnikOffDiag.offG ψ Λ z (c + v * I) := by
    rw [continuous_iff_continuousAt]
    intro v
    exact ContinuousAt.comp (g := LinnikOffDiag.offG ψ Λ z) (f := fun v : ℝ => (c : ℂ) + v * I)
      (LinnikOffDiag.differentiableAt_offG hψ hΛ z (by simpa using hc)).continuousAt (by fun_prop)
  refine integrable_line (G := LinnikOffDiag.offG ψ Λ z) hc (le_abs_self c) hcont
    (K := InghamDensity.KG * Λ ^ c * A) fun v => ?_
  have hre : ((c : ℂ) + v * I).re = c := by simp
  have him : ((c : ℂ) + v * I).im = v := by simp
  have hG := norm_mul_Gamma_le (w := (c : ℂ) + v * I) (by rw [hre]; linarith) (by rw [hre]; exact hc2)
  rw [him] at hG
  have hL := norm_LFunction_shift_le hψ hz0 hz1 hc (w := (c : ℂ) + v * I) (by rw [hre]) (by rw [hre]; exact hc2)
  rw [him, ← hA] at hL
  have hΛw : ‖(Λ : ℂ) ^ ((c : ℂ) + v * I)‖ = Λ ^ c := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hΛ, hre]
  have hv1 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
  have hKG := InghamDensity.KG_pos
  unfold LinnikOffDiag.offG
  rw [norm_mul, norm_mul, hΛw]
  calc ‖(c : ℂ) + v * I‖ * (‖LFunction ψ (z + (c + v * I))‖ * ‖Complex.Gamma ((c : ℂ) + v * I)‖ * Λ ^ c) *
        (1 + |v|) ^ 3
      ≤ ‖(c : ℂ) + v * I‖ * ((A * (1 + |v|)) * ‖Complex.Gamma ((c : ℂ) + v * I)‖ * Λ ^ c) * (1 + |v|) ^ 3 := by
        gcongr
    _ = (‖(c : ℂ) + v * I‖ * ‖Complex.Gamma ((c : ℂ) + v * I)‖ * (1 + |v|) ^ 4) * (Λ ^ c * A) := by ring
    _ ≤ (‖(c : ℂ) + v * I‖ * ‖Complex.Gamma ((c : ℂ) + v * I)‖ * (1 + |v|) ^ 5) * (Λ ^ c * A) := by
        have h45 : (1 + |v|) ^ 4 ≤ (1 + |v|) ^ 5 := pow_le_pow_right₀ hv1 (by norm_num)
        gcongr
    _ ≤ InghamDensity.KG * (Λ ^ c * A) := by gcongr
    _ = InghamDensity.KG * Λ ^ c * A := by ring

/-- **The weighted sum as an integral**: for `ψ ≠ 1`, `U ≥ 2`, `0 ≤ Re z ≤ 1` and `0 < c ≤ 2`,
`Σ_{n≥1} ψ(n)n^{−z}(e^{−n/U} − e^{−2n/U}) = (1/2π)∫ L(z + c + iv, ψ)kW_U(c + iv) dv` (round 525's
`LinnikOffDiag.kTerm_tsum_eq` at `U` and at `U/2`). -/
theorem hTerm_tsum_eq {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {U : ℝ} (hU : 2 ≤ U) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) :
    ∑' n, hTerm ψ U z n = (1 / (2 * π) : ℂ) * ∫ v : ℝ, LFunction ψ (z + (c + v * I)) * kW U (c + v * I) := by
  have hU0 : 0 < U := by linarith
  have h1 : (1 : ℝ) ≤ U := by linarith
  have h2 : (1 : ℝ) ≤ U / 2 := by linarith
  have hs1 := summable_kTerm ψ hU0 hz0
  have hs2 := summable_kTerm ψ (by linarith : (0 : ℝ) < U / 2) hz0
  have e : ∑' n, hTerm ψ U z n = ∑' n, kTerm ψ U z n - ∑' n, kTerm ψ (U / 2) z n := by
    unfold hTerm; exact hs1.tsum_sub hs2
  rw [e, LinnikOffDiag.kTerm_tsum_eq hψ h1 hz0 hz1 hc hc2, LinnikOffDiag.kTerm_tsum_eq hψ h2 hz0 hz1 hc hc2,
    ← mul_sub, ← integral_sub (integrable_offG hψ hU0 hz0 hz1 hc hc2)
      (integrable_offG hψ (by linarith) hz0 hz1 hc hc2)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [LinnikOffDiag.offG, kW]
  ring

instance conductor_neZero {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) : NeZero ψ.conductor :=
  ⟨ψ.conductor_ne_zero⟩

/-! ### The Euler factor at the primes of `q`, expanded over subsets -/

lemma natCast_finset_prod_cpow (T : Finset ℕ) (s : ℂ) :
    (((∏ p ∈ T, p : ℕ) : ℂ)) ^ s = ∏ p ∈ T, ((p : ℕ) : ℂ) ^ s := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [prod_insert ha, prod_insert ha, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih]

/-- `∏_{p∈P}(1 − ψ(p)p^{−s}) = Σ_{T⊆P}(−1)^{|T|}ψ(d_T)d_T^{−s}`, `d_T = ∏_{p∈T} p`. -/
lemma euler_expand {f : ℕ} (ψ : DirichletCharacter ℂ f) (P : Finset ℕ) (s : ℂ) :
    ∏ p ∈ P, (1 - ψ p * (p : ℂ) ^ (-s)) =
      ∑ T ∈ P.powerset, (-1) ^ T.card * ψ (∏ p ∈ T, p : ℕ) * (((∏ p ∈ T, p : ℕ) : ℂ)) ^ (-s) := by
  have h := Finset.prod_add (fun p : ℕ => -(ψ p * (p : ℂ) ^ (-s))) (fun _ => (1 : ℂ)) P
  simp only [prod_const_one, mul_one] at h
  rw [show (∏ p ∈ P, (1 - ψ p * (p : ℂ) ^ (-s))) = ∏ p ∈ P, (-(ψ p * (p : ℂ) ^ (-s)) + 1) from
    prod_congr rfl fun p _ => by ring, h]
  refine sum_congr rfl fun T _ => ?_
  rw [prod_neg, prod_mul_distrib, natCast_finset_prod_cpow, Nat.cast_prod, map_prod]
  ring

/-- **`L(s, ψ)` through the primitive character**: for `ψ ≠ 1` mod `q`,
`L(s, ψ) = Σ_{T ⊆ primes of q}(−1)^{|T|}ψ*(d_T)d_T^{−s}L(s, ψ*)` (Mathlib's `LFunction_changeLevel`). -/
lemma LFunction_eq_dsum {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) (s : ℂ) :
    LFunction ψ s = ∑ T ∈ q.primeFactors.powerset, (-1) ^ T.card * ψ.primitiveCharacter (∏ p ∈ T, p : ℕ) *
      (((∏ p ∈ T, p : ℕ) : ℂ)) ^ (-s) * LFunction ψ.primitiveCharacter s := by
  have hψ' : ψ.primitiveCharacter ≠ 1 := by
    intro h
    apply hψ
    rw [← ψ.changeLevel_primitiveCharacter, h, changeLevel_one]
  have h := LFunction_changeLevel ψ.conductor_dvd_level ψ.primitiveCharacter (s := s) (Or.inl hψ')
  rw [ψ.changeLevel_primitiveCharacter] at h
  rw [h, euler_expand, mul_sum]
  exact sum_congr rfl fun T _ => by ring

/-- `x^w d^{−w} = (x/d)^w` for `x ≥ 0` and `d ≥ 1`. -/
lemma ofReal_div_natCast_cpow {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (w : ℂ) :
    (((x / d : ℝ)) : ℂ) ^ w = (x : ℂ) ^ w * (d : ℂ) ^ (-w) := by
  have harg : ((d : ℝ) : ℂ).arg ≠ π := by
    rw [Complex.ofReal_natCast, Complex.natCast_arg]; exact Real.pi_pos.ne
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx (inv_nonneg.2 (Nat.cast_nonneg d)),
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, Complex.ofReal_natCast]

/-- `d^{−w}·kW_U(w) = kW_{U/d}(w)` for `U ≥ 0`. -/
lemma kW_div {U : ℝ} (hU : 0 ≤ U) (d : ℕ) (w : ℂ) :
    (d : ℂ) ^ (-w) * kW U w = kW (U / d) w := by
  unfold kW
  have e2 : (U / d / 2 : ℝ) = U / 2 / d := by ring
  rw [ofReal_div_natCast_cpow hU, e2, ofReal_div_natCast_cpow (by linarith : (0 : ℝ) ≤ U / 2)]
  ring

/-- **The integral through the primitive character**: for `ψ ≠ 1` mod `q`, `U > 0`, `0 ≤ Re z ≤ 1`, `0 < c ≤ 2`,
`∫ L(z + c + iv, ψ)kW_U(c + iv) dv = Σ_T (−1)^{|T|}ψ*(d_T)d_T^{−z}∫ L(z + c + iv, ψ*)kW_{U/d_T}(c + iv) dv`. -/
theorem integral_dsum {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {U : ℝ} (hU : 0 < U) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) :
    (∫ v : ℝ, LFunction ψ (z + (c + v * I)) * kW U (c + v * I)) =
      ∑ T ∈ q.primeFactors.powerset, (-1) ^ T.card * ψ.primitiveCharacter (∏ p ∈ T, p : ℕ) *
        (((∏ p ∈ T, p : ℕ) : ℂ)) ^ (-z) *
          ∫ v : ℝ, LFunction ψ.primitiveCharacter (z + (c + v * I)) *
            kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c + v * I) := by
  have hψ' : ψ.primitiveCharacter ≠ 1 := by
    intro h
    apply hψ
    rw [← ψ.changeLevel_primitiveCharacter, h, changeLevel_one]
  have hd0 : ∀ T ∈ q.primeFactors.powerset, 0 < (∏ p ∈ T, p : ℕ) := fun T hT =>
    prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (mem_powerset.1 hT hp)).pos
  have hpt : ∀ v : ℝ, LFunction ψ (z + (c + v * I)) * kW U (c + v * I) =
      ∑ T ∈ q.primeFactors.powerset, (-1) ^ T.card * ψ.primitiveCharacter (∏ p ∈ T, p : ℕ) *
        (((∏ p ∈ T, p : ℕ) : ℂ)) ^ (-z) *
          (LFunction ψ.primitiveCharacter (z + (c + v * I)) * kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c + v * I)) := by
    intro v
    rw [LFunction_eq_dsum hψ, sum_mul]
    refine sum_congr rfl fun T hT => ?_
    have hd : ((∏ p ∈ T, p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hd0 T hT).ne'
    rw [← kW_div hU.le, neg_add, Complex.cpow_add _ _ hd]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum]
  · refine sum_congr rfl fun T _ => ?_
    exact integral_const_mul _ _
  · intro T hT
    exact (integrable_L_kW hψ' (div_pos hU (by exact_mod_cast hd0 T hT)) hz0 hz1 hc hc2).const_mul _

/-- **The reflected kernel bound for one pair**: for `ψ ≠ 1` mod `q`, `U ≥ 2`, `0 ≤ Re z ≤ 1` and lines
`c₂ < 0 < c₁` with `−1/2 ≤ c₂`, `c₁ ≤ 2`, `−5/16 ≤ Re z + c₂ < 0`, `Re z + c₁ ≤ 13/16`, and any truncations `Z_T`,
`|H_U(ψ, z)| ≤ (1/2π)Σ_T (∫|kW·Φ·Σ_{m ≤ Z_T}| + ∫|kW·Φ·Σ_{m > Z_T}|)` over `T ⊆ primes of q`, with `Λ = U/d_T` in
`kW`, `Φ` for the primitive character `ψ*` and the dual character `ψ⁻¹` (`hTerm_tsum_eq`, `integral_dsum`,
`reflect`). -/
theorem norm_hTerm_le_reflect {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {U : ℝ} (hU : 2 ≤ U)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) {c₁ c₂ : ℝ} (hc₂0 : c₂ < 0) (hc₁0 : 0 < c₁) (hc₂ : -1 / 2 ≤ c₂)
    (hc₁ : c₁ ≤ 2) (hs1 : -5 / 16 ≤ z.re + c₂) (hs3 : z.re + c₂ < 0) (hs2 : z.re + c₁ ≤ 13 / 16)
    (Z : Finset ℕ → ℕ) :
    ‖∑' n, hTerm ψ U z n‖ ≤ (1 / (2 * π)) * ∑ T ∈ q.primeFactors.powerset,
      ((∫ v : ℝ, ‖kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c₁ + v * I) * Phi ψ.primitiveCharacter q (z + (c₁ + v * I)) *
          dualS ψ⁻¹ (Z T) (z + (c₁ + v * I))‖) +
        ∫ v : ℝ, ‖kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c₂ + v * I) * Phi ψ.primitiveCharacter q (z + (c₂ + v * I)) *
          dualT ψ⁻¹ (Z T) (z + (c₂ + v * I))‖) := by
  have hU0 : 0 < U := by linarith
  have hψ' : ψ.primitiveCharacter ≠ 1 := by
    intro h
    apply hψ
    rw [← ψ.changeLevel_primitiveCharacter, h, changeLevel_one]
  have hprim := ψ.primitiveCharacter_isPrimitive
  have hd0 : ∀ T ∈ q.primeFactors.powerset, 0 < (∏ p ∈ T, p : ℕ) := fun T hT =>
    prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (mem_powerset.1 hT hp)).pos
  rw [hTerm_tsum_eq hψ hU hz0 hz1 hc₁0 hc₁, integral_dsum hψ hU0 hz0 hz1 hc₁0 hc₁, norm_mul]
  have h2π : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg pi_pos.le]
  rw [h2π]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun T hT => ?_)) (by positivity)
  have hΛ : 0 < U / ((∏ p ∈ T, p : ℕ) : ℝ) := div_pos hU0 (by exact_mod_cast hd0 T hT)
  have hR := reflect_aux ψ.conductor_dvd_level hprim hψ' hΛ hc₂0 hc₁0 hc₂ hc₁ hs1 hs3 hs2 (Z T)
  rw [ψ.changeLevel_primitiveCharacter] at hR
  obtain ⟨heq, -, -⟩ := hR
  rw [heq, norm_mul]
  have ha : ‖(-1) ^ T.card * ψ.primitiveCharacter (∏ p ∈ T, p : ℕ) * (((∏ p ∈ T, p : ℕ) : ℂ)) ^ (-z)‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast_cpow_of_pos (hd0 T hT)]
    have h1 := DirichletCharacter.norm_le_one ψ.primitiveCharacter (∏ p ∈ T, p : ℕ)
    have h2 : ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-z).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd0 T hT) (by simp; linarith)
    calc ‖ψ.primitiveCharacter (∏ p ∈ T, p : ℕ)‖ * ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-z).re ≤ 1 * 1 :=
          mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hb : ‖(∫ v : ℝ, kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c₁ + v * I) *
        Phi ψ.primitiveCharacter q (z + (c₁ + v * I)) * dualS ψ⁻¹ (Z T) (z + (c₁ + v * I))) +
      ∫ v : ℝ, kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c₂ + v * I) * Phi ψ.primitiveCharacter q (z + (c₂ + v * I)) *
        dualT ψ⁻¹ (Z T) (z + (c₂ + v * I))‖ ≤
      (∫ v : ℝ, ‖kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c₁ + v * I) *
        Phi ψ.primitiveCharacter q (z + (c₁ + v * I)) * dualS ψ⁻¹ (Z T) (z + (c₁ + v * I))‖) +
      ∫ v : ℝ, ‖kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c₂ + v * I) * Phi ψ.primitiveCharacter q (z + (c₂ + v * I)) *
        dualT ψ⁻¹ (Z T) (z + (c₂ + v * I))‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _))
  have h0 : 0 ≤ (∫ v : ℝ, ‖kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c₁ + v * I) *
        Phi ψ.primitiveCharacter q (z + (c₁ + v * I)) * dualS ψ⁻¹ (Z T) (z + (c₁ + v * I))‖) +
      ∫ v : ℝ, ‖kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c₂ + v * I) * Phi ψ.primitiveCharacter q (z + (c₂ + v * I)) *
        dualT ψ⁻¹ (Z T) (z + (c₂ + v * I))‖ :=
    add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  calc _ ≤ 1 * ((∫ v : ℝ, ‖kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c₁ + v * I) *
          Phi ψ.primitiveCharacter q (z + (c₁ + v * I)) * dualS ψ⁻¹ (Z T) (z + (c₁ + v * I))‖) +
        ∫ v : ℝ, ‖kW (U / ((∏ p ∈ T, p : ℕ) : ℝ)) (c₂ + v * I) * Phi ψ.primitiveCharacter q (z + (c₂ + v * I)) *
          dualT ψ⁻¹ (Z T) (z + (c₂ + v * I))‖) := mul_le_mul ha hb (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The two reflected integrands are integrable (`reflect_aux`). -/
theorem integrable_reflect {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {Λ : ℝ} (hΛ : 0 < Λ)
    {z : ℂ} {c₁ c₂ : ℝ} (hc₂0 : c₂ < 0) (hc₁0 : 0 < c₁) (hc₂ : -1 / 2 ≤ c₂)
    (hc₁ : c₁ ≤ 2) (hs1 : -5 / 16 ≤ z.re + c₂) (hs3 : z.re + c₂ < 0) (hs2 : z.re + c₁ ≤ 13 / 16) (Z : ℕ) :
    (Integrable fun v : ℝ => kW Λ (c₁ + v * I) * Phi ψ.primitiveCharacter q (z + (c₁ + v * I)) *
        dualS ψ⁻¹ Z (z + (c₁ + v * I))) ∧
      (Integrable fun v : ℝ => kW Λ (c₂ + v * I) * Phi ψ.primitiveCharacter q (z + (c₂ + v * I)) *
        dualT ψ⁻¹ Z (z + (c₂ + v * I))) := by
  have hψ' : ψ.primitiveCharacter ≠ 1 := by
    intro h
    apply hψ
    rw [← ψ.changeLevel_primitiveCharacter, h, changeLevel_one]
  have hR := reflect_aux ψ.conductor_dvd_level ψ.primitiveCharacter_isPrimitive hψ' hΛ hc₂0 hc₁0 hc₂ hc₁ hs1 hs3
    hs2 Z (q := q)
  rw [ψ.changeLevel_primitiveCharacter] at hR
  exact hR.2

/-! ### The product trick: products of two Dirichlet polynomials and the large sieve -/

/-- The support of a product of two Dirichlet polynomials: the products `nm`, `n ∈ S`, `m ∈ M`. -/
def mulSupp (S M : Finset ℕ) : Finset ℕ := (S ×ˢ M).image fun p => p.1 * p.2

/-- The coefficients of the product: `c_k = Σ_{n∈S, m∈M, nm = k} b_n e_m`. -/
def mulCo (S M : Finset ℕ) (b e : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ p ∈ (S ×ˢ M).filter (fun p => p.1 * p.2 = k), b p.1 * e p.2

/-- **The product of two Dirichlet polynomials** is the Dirichlet polynomial with the convolved coefficients. -/
theorem pv_mul (S M : Finset ℕ) (b e : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (s : ℂ) :
    pv S b χ s * pv M e χ s = pv (mulSupp S M) (mulCo S M b e) χ s := by
  classical
  unfold pv mulCo mulSupp
  rw [sum_mul_sum, ← sum_product (f := fun p : ℕ × ℕ =>
    b p.1 * χ p.1 * (p.1 : ℂ) ^ (-s) * (e p.2 * χ p.2 * (p.2 : ℂ) ^ (-s)))]
  have hterm : ∀ p : ℕ × ℕ, b p.1 * χ p.1 * (p.1 : ℂ) ^ (-s) * (e p.2 * χ p.2 * (p.2 : ℂ) ^ (-s)) =
      (b p.1 * e p.2) * (χ ((p.1 * p.2 : ℕ)) * (((p.1 * p.2 : ℕ)) : ℂ) ^ (-s)) := by
    intro p
    rw [Nat.cast_mul (α := ZMod q), map_mul, Nat.cast_mul (α := ℂ), Complex.natCast_mul_natCast_cpow]
    ring
  simp_rw [hterm]
  rw [← sum_fiberwise_of_maps_to (s := S ×ˢ M) (t := (S ×ˢ M).image fun p => p.1 * p.2)
    (g := fun p => p.1 * p.2) (fun p hp => mem_image_of_mem _ hp)]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_assoc, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [(mem_filter.1 hp).2]

/-- **The mass of the convolved coefficients**: `Σ_k |c_k|² ≤ τ·Σ|b_n|²·Σ|e_m|²` when `d(k) ≤ τ` on the support. -/
theorem mass_mulCo_le {S M : Finset ℕ} (hS0 : 0 ∉ S) (hM0 : 0 ∉ M) (b e : ℕ → ℂ) {τ : ℝ}
    (hτ : ∀ k ∈ mulSupp S M, (k.divisors.card : ℝ) ≤ τ) :
    ∑ k ∈ mulSupp S M, ‖mulCo S M b e k‖ ^ 2 ≤ τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * ∑ m ∈ M, ‖e m‖ ^ 2) := by
  classical
  set F : ℕ → Finset (ℕ × ℕ) := fun k => (S ×ˢ M).filter (fun p => p.1 * p.2 = k) with hF
  have hk : ∀ k ∈ mulSupp S M, ‖mulCo S M b e k‖ ^ 2 ≤ τ * ∑ p ∈ F k, ‖b p.1‖ ^ 2 * ‖e p.2‖ ^ 2 := by
    intro k hk
    have hcard : ((F k).card : ℝ) ≤ τ := by
      obtain ⟨p₀, hp₀, hk₀⟩ := mem_image.1 hk
      have hk0 : k ≠ 0 := by
        rw [← hk₀]
        obtain ⟨h1, h2⟩ := mem_product.1 hp₀
        exact mul_ne_zero (fun h => hS0 (h ▸ h1)) (fun h => hM0 (h ▸ h2))
      have hinj : (F k).card ≤ k.divisors.card := by
        refine card_le_card_of_injOn (fun p => p.1) (fun p hp => ?_) (fun p hp p' hp' h => ?_)
        · have hp := mem_filter.1 hp
          exact Nat.mem_divisors.2 ⟨⟨p.2, hp.2.symm⟩, hk0⟩
        · have h1 := (mem_filter.1 hp).2
          have h2 := (mem_filter.1 hp').2
          have hne : p.1 ≠ 0 := fun h0 => hS0 (h0 ▸ (mem_product.1 (mem_filter.1 hp).1).1)
          have e : p.1 = p'.1 := h
          have e2 : p.2 = p'.2 := by
            apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
            rw [h1, e, h2]
          exact Prod.ext e e2
      exact (by exact_mod_cast hinj : ((F k).card : ℝ) ≤ k.divisors.card).trans (hτ k hk)
    have h1 : ‖mulCo S M b e k‖ ≤ ∑ p ∈ F k, ‖b p.1‖ * ‖e p.2‖ :=
      (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun p _ => norm_mul _ _))
    have h2 := sq_sum_le_card_mul_sum_sq (s := F k) (f := fun p => ‖b p.1‖ * ‖e p.2‖)
    have h3 : 0 ≤ ∑ p ∈ F k, (‖b p.1‖ * ‖e p.2‖) ^ 2 := sum_nonneg fun _ _ => by positivity
    calc ‖mulCo S M b e k‖ ^ 2 ≤ (∑ p ∈ F k, ‖b p.1‖ * ‖e p.2‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (F k).card * ∑ p ∈ F k, (‖b p.1‖ * ‖e p.2‖) ^ 2 := h2
      _ ≤ τ * ∑ p ∈ F k, (‖b p.1‖ * ‖e p.2‖) ^ 2 := mul_le_mul_of_nonneg_right hcard h3
      _ = τ * ∑ p ∈ F k, ‖b p.1‖ ^ 2 * ‖e p.2‖ ^ 2 := by simp_rw [mul_pow]
  calc ∑ k ∈ mulSupp S M, ‖mulCo S M b e k‖ ^ 2 ≤ ∑ k ∈ mulSupp S M, τ * ∑ p ∈ F k, ‖b p.1‖ ^ 2 * ‖e p.2‖ ^ 2 :=
        sum_le_sum hk
    _ = τ * ∑ p ∈ S ×ˢ M, ‖b p.1‖ ^ 2 * ‖e p.2‖ ^ 2 := by
        rw [← mul_sum, hF]
        congr 1
        exact sum_fiberwise_of_maps_to (fun p hp => mem_image_of_mem _ hp) _
    _ = τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * ∑ m ∈ M, ‖e m‖ ^ 2) := by
        rw [sum_product, sum_mul_sum]

/-- A Dirichlet polynomial at `β + iγ` as round 521's `dp` at `γ` with the weights `j^{−β}`. -/
theorem pv_eq_dp (S : Finset ℕ) (hS0 : 0 ∉ S) (c : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (β γ : ℝ) :
    pv S c χ ((β : ℂ) + γ * I) = DirMean.dp S (fun j => c j * χ j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) γ := by
  unfold DirMean.dp pv
  refine sum_congr rfl fun j hj => ?_
  have hj1 : j ≠ 0 := fun h => hS0 (h ▸ hj)
  have hn0 : (j : ℂ) ≠ 0 := by exact_mod_cast hj1
  have hnr : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj1
  have hc : (j : ℂ) ^ (-((β : ℂ) + γ * I))
      = (((j : ℝ) ^ (-β) : ℝ) : ℂ) * Complex.exp (-(I * ((γ * Real.log j : ℝ) : ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero hn0, Real.rpow_def_of_pos hnr]
    have hlog : Complex.log (j : ℂ) = (Real.log j : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hnr.le]
    rw [hlog, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hc]; ring

/-- The dyadic large-sieve factor `L(X) = e(q(2T + 1) + 8X(1 + log X))(2 + log²(2X))(log₂X + 1)`. -/
def LSX (q : ℕ) (T : ℝ) (X : ℕ) : ℝ :=
  Real.exp 1 * ((q * (2 * T + 1) + 8 * X * (1 + Real.log X)) * (2 + Real.log (2 * X) ^ 2)) * (Nat.log 2 X + 1)

lemma LSX_nonneg (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (X : ℕ) : 0 ≤ LSX q T X := by
  unfold LSX
  have : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  positivity

/-- **The large sieve off the line, any support in `[2, X]`**: for distinct characters with `0 ≤ δ_χ ≤ 1/2` and
`|γ_χ| ≤ T`, `Σ_χ |Σ_{k∈S} c_kχ(k)k^{−δ_χ−iγ_χ}|² ≤ L(X)Σ_k|c_k|²` (round 521's `large_values_chars_off` on the
dyadic pieces `(2^j, 2^{j+1}]`, `j ≤ log₂ X`, and Cauchy–Schwarz over the pieces). -/
theorem ls_pv_dyadic {Sk : Finset ℕ} {X : ℕ} (hSk : Sk ⊆ Icc 2 X) (c : ℕ → ℂ) (q : ℕ) [NeZero q] {T : ℝ}
    (hT : 0 ≤ T) (Rs : Finset (DirichletCharacter ℂ q)) (δ γ : DirichletCharacter ℂ q → ℝ)
    (hδ : ∀ χ ∈ Rs, 0 ≤ δ χ ∧ δ χ ≤ 1 / 2) (hγ : ∀ χ ∈ Rs, |γ χ| ≤ T) :
    ∑ χ ∈ Rs, ‖pv Sk c χ ((δ χ : ℂ) + γ χ * I)‖ ^ 2 ≤ LSX q T X * ∑ k ∈ Sk, ‖c k‖ ^ 2 := by
  classical
  set J := Nat.log 2 X + 1 with hJ
  set g : ℕ → ℕ := fun k => Nat.log 2 (k - 1) with hg
  have hSk0 : 0 ∉ Sk := fun h => by have := (mem_Icc.1 (hSk h)).1; omega
  have hmaps : ∀ k ∈ Sk, g k ∈ range J := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_Icc.1 (hSk hk)
    rw [Finset.mem_range, hJ]
    have : Nat.log 2 (k - 1) ≤ Nat.log 2 X := Nat.log_mono_right (by omega)
    simp only [hg]; omega
  have hpiece : ∀ j ∈ range J, (Sk.filter fun k => g k = j) ⊆ Ioc (2 ^ j) (2 * 2 ^ j) := by
    intro j _ k hk
    obtain ⟨hk, hkj⟩ := mem_filter.1 hk
    obtain ⟨hk1, -⟩ := mem_Icc.1 (hSk hk)
    have h1 : 2 ^ Nat.log 2 (k - 1) ≤ k - 1 := Nat.pow_log_le_self 2 (by omega)
    have h2 : k - 1 < 2 ^ (Nat.log 2 (k - 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    simp only [hg] at hkj
    rw [hkj] at h1 h2
    rw [pow_succ] at h2
    rw [Finset.mem_Ioc]
    constructor <;> omega
  -- the polynomial as the sum of its pieces
  have hsplit : ∀ χ ∈ Rs, pv Sk c χ ((δ χ : ℂ) + γ χ * I) =
      ∑ j ∈ range J, pv (Sk.filter fun k => g k = j) c χ ((δ χ : ℂ) + γ χ * I) := by
    intro χ _
    unfold pv
    exact (sum_fiberwise_of_maps_to hmaps _).symm
  -- Cauchy–Schwarz over the pieces
  have hcs : ∀ χ ∈ Rs, ‖pv Sk c χ ((δ χ : ℂ) + γ χ * I)‖ ^ 2 ≤
      J * ∑ j ∈ range J, ‖pv (Sk.filter fun k => g k = j) c χ ((δ χ : ℂ) + γ χ * I)‖ ^ 2 := by
    intro χ hχ
    rw [hsplit χ hχ]
    have h1 := norm_sum_le (range J) fun j => pv (Sk.filter fun k => g k = j) c χ ((δ χ : ℂ) + γ χ * I)
    have h2 := sq_sum_le_card_mul_sum_sq (s := range J)
      (f := fun j => ‖pv (Sk.filter fun k => g k = j) c χ ((δ χ : ℂ) + γ χ * I)‖)
    rw [card_range] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  -- the large sieve on each piece
  have hX0 : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set L0 : ℝ := Real.exp 1 * ((q * (2 * T + 1) + 8 * X * (1 + Real.log X)) * (2 + Real.log (2 * X) ^ 2))
    with hL0
  have hL0nn : 0 ≤ L0 := by rw [hL0]; positivity
  have hls : ∀ j ∈ range J, ∑ χ ∈ Rs, ‖pv (Sk.filter fun k => g k = j) c χ ((δ χ : ℂ) + γ χ * I)‖ ^ 2 ≤
      L0 * ∑ k ∈ Sk.filter (fun k => g k = j), ‖c k‖ ^ 2 := by
    intro j hj
    rcases (Sk.filter fun k => g k = j).eq_empty_or_nonempty with he | hne
    · rw [he]; simp [pv]
    obtain ⟨k₀, hk₀⟩ := hne
    have hk₀X : k₀ ≤ X := (mem_Icc.1 (hSk (mem_filter.1 hk₀).1)).2
    have hjX : 2 ^ j < X := lt_of_lt_of_le (mem_Ioc.1 (hpiece j hj hk₀)).1 hk₀X
    have hP1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hS0' : 0 ∉ Sk.filter (fun k => g k = j) := fun h => hSk0 (mem_filter.1 h).1
    have h := LinnikHybrid.large_values_chars_off hP1 (hpiece j hj) c q (σ := 0) (lo := -T - 1 / 2)
      (hi := T + 1 / 2) (by linarith) Rs γ δ
      (fun χ hχ => ⟨by linarith [(abs_le.1 (hγ χ hχ)).1], by linarith [(abs_le.1 (hγ χ hχ)).2]⟩)
      (fun χ hχ => ⟨(hδ χ hχ).1, by linarith [(hδ χ hχ).2]⟩)
    simp only [neg_zero, Real.rpow_zero, one_pow, mul_one] at h
    have hconv : ∀ χ, pv (Sk.filter fun k => g k = j) c χ ((δ χ : ℂ) + γ χ * I) =
        DirMean.dp (Sk.filter fun k => g k = j) (fun k => c k * χ k * (((k : ℝ) ^ (-δ χ) : ℝ) : ℂ)) (γ χ) :=
      fun χ => pv_eq_dp _ hS0' c χ (δ χ) (γ χ)
    simp_rw [hconv]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => by positivity))
    -- the factor at `P = 2^j` is at most the factor at `X`
    have hPX : ((2 ^ j : ℕ) : ℝ) ≤ X := by exact_mod_cast hjX.le
    have hP0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by positivity)
    have hlog1 : Real.log ((2 ^ j : ℕ) : ℝ) ≤ Real.log X := Real.log_le_log hP0 hPX
    have hlog2 : Real.log (2 * ((2 ^ j : ℕ) : ℝ)) ≤ Real.log (2 * X) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlogP : 0 ≤ Real.log ((2 ^ j : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hP1' : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hP1
    have hlog2P : 0 ≤ Real.log (2 * ((2 ^ j : ℕ) : ℝ)) := Real.log_nonneg (by linarith)
    rw [hL0]
    have hT2 : (0 : ℝ) ≤ q * (T + 1 / 2 - (-T - 1 / 2)) := by nlinarith
    have e : (q : ℝ) * (T + 1 / 2 - (-T - 1 / 2)) = q * (2 * T + 1) := by ring
    rw [e] at hT2 ⊢
    gcongr
  calc ∑ χ ∈ Rs, ‖pv Sk c χ ((δ χ : ℂ) + γ χ * I)‖ ^ 2
      ≤ ∑ χ ∈ Rs, J * ∑ j ∈ range J, ‖pv (Sk.filter fun k => g k = j) c χ ((δ χ : ℂ) + γ χ * I)‖ ^ 2 :=
        sum_le_sum hcs
    _ = J * ∑ j ∈ range J, ∑ χ ∈ Rs, ‖pv (Sk.filter fun k => g k = j) c χ ((δ χ : ℂ) + γ χ * I)‖ ^ 2 := by
        rw [← mul_sum, sum_comm]
    _ ≤ J * ∑ j ∈ range J, L0 * ∑ k ∈ Sk.filter (fun k => g k = j), ‖c k‖ ^ 2 := by
        gcongr with j hj
        exact hls j hj
    _ = J * (L0 * ∑ k ∈ Sk, ‖c k‖ ^ 2) := by
        rw [← mul_sum, sum_fiberwise_of_maps_to hmaps]
    _ = LSX q T X * ∑ k ∈ Sk, ‖c k‖ ^ 2 := by
        rw [LSX, ← hL0, hJ]; push_cast; ring

/-- **The product trick against the large values**: if `|F(χ)| ≥ V > 0` at `u_χ = δ_χ + iγ_χ` for every `χ ∈ Rs`,
with `F` supported on `[2, N]`, then for any polynomial `E` on `[1, K]`,
`(Σ_χ |E(χ, u_χ)|)² ≤ V^{−2}|Rs|·L(NK)·τ·Σ|b_n|²·Σ|e_m|²` with `d(k) ≤ τ` for `k ≤ NK`:
`|E| ≤ |FE|/V`, `FE` is a polynomial on `[2, NK]` (`pv_mul`), then Cauchy–Schwarz, `ls_pv_dyadic` and
`mass_mulCo_le`. -/
theorem huxley_core {S M : Finset ℕ} {N K : ℕ} (hS : S ⊆ Icc 2 N) (hM : M ⊆ Icc 1 K) (b e : ℕ → ℂ) (q : ℕ)
    [NeZero q] {T : ℝ} (hT : 0 ≤ T) (Rs : Finset (DirichletCharacter ℂ q)) (δ γ : DirichletCharacter ℂ q → ℝ)
    (hδ : ∀ χ ∈ Rs, 0 ≤ δ χ ∧ δ χ ≤ 1 / 2) (hγ : ∀ χ ∈ Rs, |γ χ| ≤ T) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ χ ∈ Rs, V ≤ ‖pv S b χ ((δ χ : ℂ) + γ χ * I)‖) {τ : ℝ}
    (hτ : ∀ k, k ≤ N * K → (k.divisors.card : ℝ) ≤ τ) :
    (∑ χ ∈ Rs, ‖pv M e χ ((δ χ : ℂ) + γ χ * I)‖) ^ 2 ≤
      (V ^ 2)⁻¹ * (Rs.card * (LSX q T (N * K) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * ∑ m ∈ M, ‖e m‖ ^ 2)))) := by
  have hS0 : 0 ∉ S := fun h => by have := (mem_Icc.1 (hS h)).1; omega
  have hM0 : 0 ∉ M := fun h => by have := (mem_Icc.1 (hM h)).1; omega
  have hsupp : mulSupp S M ⊆ Icc 2 (N * K) := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hk
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    obtain ⟨h11, h12⟩ := mem_Icc.1 (hS h1)
    obtain ⟨h21, h22⟩ := mem_Icc.1 (hM h2)
    exact mem_Icc.2 ⟨by nlinarith, Nat.mul_le_mul h12 h22⟩
  set u : DirichletCharacter ℂ q → ℂ := fun χ => (δ χ : ℂ) + γ χ * I with hu
  have hpt : ∀ χ ∈ Rs, ‖pv M e χ (u χ)‖ ≤ V⁻¹ * ‖pv (mulSupp S M) (mulCo S M b e) χ (u χ)‖ := by
    intro χ hχ
    rw [← pv_mul, norm_mul, le_inv_mul_iff₀ hV]
    exact mul_le_mul_of_nonneg_right (hbig χ hχ) (norm_nonneg _)
  have h1 : ∑ χ ∈ Rs, ‖pv M e χ (u χ)‖ ≤ V⁻¹ * ∑ χ ∈ Rs, ‖pv (mulSupp S M) (mulCo S M b e) χ (u χ)‖ := by
    rw [mul_sum]; exact sum_le_sum hpt
  have h2 := sq_sum_le_card_mul_sum_sq (s := Rs) (f := fun χ => ‖pv (mulSupp S M) (mulCo S M b e) χ (u χ)‖)
  have h3 := ls_pv_dyadic hsupp (mulCo S M b e) q hT Rs δ γ hδ hγ
  have h4 := mass_mulCo_le hS0 hM0 b e (fun k hk => hτ k (mem_Icc.1 (hsupp hk)).2)
  have hLS := LSX_nonneg q hT (N * K)
  have hR0 : (0 : ℝ) ≤ Rs.card := Nat.cast_nonneg _
  have hs0 : 0 ≤ ∑ χ ∈ Rs, ‖pv M e χ (u χ)‖ := sum_nonneg fun _ _ => norm_nonneg _
  calc (∑ χ ∈ Rs, ‖pv M e χ (u χ)‖) ^ 2
      ≤ (V⁻¹ * ∑ χ ∈ Rs, ‖pv (mulSupp S M) (mulCo S M b e) χ (u χ)‖) ^ 2 := pow_le_pow_left₀ hs0 h1 2
    _ = (V ^ 2)⁻¹ * (∑ χ ∈ Rs, ‖pv (mulSupp S M) (mulCo S M b e) χ (u χ)‖) ^ 2 := by rw [mul_pow, inv_pow]
    _ ≤ (V ^ 2)⁻¹ * (Rs.card * ∑ χ ∈ Rs, ‖pv (mulSupp S M) (mulCo S M b e) χ (u χ)‖ ^ 2) := by gcongr
    _ ≤ (V ^ 2)⁻¹ * (Rs.card * (LSX q T (N * K) * ∑ k ∈ mulSupp S M, ‖mulCo S M b e k‖ ^ 2)) := by gcongr
    _ ≤ (V ^ 2)⁻¹ * (Rs.card * (LSX q T (N * K) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * ∑ m ∈ M, ‖e m‖ ^ 2)))) := by
        gcongr

end LinnikReflect

#print axioms LinnikReflect.hm_duality_W
#print axioms LinnikReflect.hTerm_tsum_eq
#print axioms LinnikReflect.integral_dsum
#print axioms LinnikReflect.norm_hTerm_le_reflect
#print axioms LinnikReflect.mass_mulCo_le
#print axioms LinnikReflect.ls_pv_dyadic
#print axioms LinnikReflect.huxley_core
