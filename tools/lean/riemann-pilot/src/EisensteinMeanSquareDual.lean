import EisensteinMeanSquareBlock

/-! # The mean square from the dual mean square (round 310)

S4 of round 291's plan, part 10, and the second conditional milestone: the companion paper's
Proposition 4.5 with its choice of parameters. Round 308's row/column form and round 309's block
bound are summed over the excluded ideal `𝔟`, the dyadic ranges of `N(f)` and the characters modulo
`4`.

* **The weights** (`weight_support`, `W0f_contDiff`, `exists_bump_one`, `exists_bump`): a weight
  vanishes outside some `[α, β]` with `0 < α ≤ β`; `W₀(x) = x^{−1/2}W(x)` is smooth; a smooth bump `V`
  equals `1` on `[α, β]` and has topological support in `[α/2, 2β]` (`exists_bump_one`, in this file
  since round 332), so at `α/2` it equals `1` on `[α/2, β]` with support in `[α/4, 2β]`.
* **Counting** (`idealCount_le`, `card_fsLe_le`, `four_pow_card_le`, `sum_idealsLe_inv_le`,
  `sum_fsLe_inv_le`, `sum_fsLe_four_pow_le`): `#{𝔞 : N𝔞 ≤ x} ≤ (2κ+5)x` for `x ≥ 1`, from round 287's
  ideal theorem; `4^{|𝔟|} ≤ C_δ·N(𝔟)^δ`; `Σ_{N𝔞 ≤ x} 1/N𝔞 ≤ 2(2κ+5)(⌊log₂⌊x⌋⌋ + 1)` by dyadic shells
  (round 314; in this file since round 332), hence the same over the squarefree `𝔟`.
* **The zero frequency** (`norm_zeroFreq_le`, `norm_zeroSum_le`, `zero_term_le`): at most
  `#𝒜·B²·2H/√3·|Φ̂(0)|` for `|W| ≤ B`, the paper's `≪ H‖W‖²_∞` term with the count of the sets of
  primes; since round 332 for any weights bounded by `B` (`norm_zeroSum_le`).
* **The rows of one `𝔟`** (`rowsOf`, `sum_rowsOf`, `goodRow`, `rowTerm_eq_zero`, `bTerm_eq_good`):
  a row contributes only if `μ` is prime to the primes of `V` (else `χ_V(μ) = 0`), `N(𝔟)N(f) ≤ βZ`
  (else a weight `W₀` vanishes) and `N(d_T μ) ≤ C·Z²/(H·N(𝔟)²)` for a `C` with `3R²β² ≤ 4C`
  (else a weight `W₀` or the dual weight `Φ̂` vanishes: the paper's restriction `N(k) ≤ 𝓗`;
  `dualW_eq_zero_of_le`, round 332).
* **`bTerm_bound`**: the good rows of level `j = ⌊log₂ N(f)⌋` form one block of round 309's
  `rowBlock_bound` at `F = 2^j`, whose column mean squares come from the dual mean square through
  `rows_colMeanSquare`; there are at most `⌊log₂⌊βZ⌋⌋ + 1` levels.
* **`famSum_meanSquare_le`**: for `N(z) ≤ H`, `Σ_z |A_Z(z)|²` is at most the zero frequency plus
  `(#characters mod 4)²·Σ_{N𝔟 ≤ βZ} (⌊log₂⌊βZ⌋⌋ + 1)·(the block bound of 𝔟)`, given the
  conclusions of round 306's `bilinear_dual_bound₂` and `dualMeanSquare_excl` (the dual mean square
  with the exclusion `𝔟`) as hypotheses.
* **`meanSquare_of_dualMeanSquare`**: `DualMeanSquare ϑ ⇒ MeanSquare ϑ` for `ϑ > 0`, at
  `H = Z^{1+ϑ}` with each of the five auxiliary exponents equal to `ε/5`. The block bound is at most
  `(2/√3·K·3^{ε/5}·K_c)·H·Z·Z^{2ε/5}·4^{|𝔟|}/N(𝔟)` (`blockBound_le`, `Amin_rpow_le`), and the two
  logarithms and `4^{|𝔟|}` cost `Z^{3ε/5}` (`log_floor_succ_le`).
* **`ne_zero_of_dualMeanSquare`**: with round 288's milestone, `DualMeanSquare ϑ` for `ϑ > 0` gives
  `ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` on `Re s > (11 + 5ϑ)/12`.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### The weights -/

/-- A weight vanishes outside some `[α, β]` with `0 < α ≤ β`. -/
theorem weight_support {W : ℝ → ℝ} (hW : HalfPlaneS0.Weight W) :
    ∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ ∀ x, x < α ∨ β < x → W x = 0 := by
  obtain ⟨R, -, hR⟩ := hW.exists_vanish_right
  by_cases hK : (tsupport W).Nonempty
  · obtain ⟨m, hm, hmin⟩ := hW.compact.exists_isMinOn hK continuous_id.continuousOn
    have hm0 : 0 < m := hW.pos hm
    refine ⟨m, max R m, hm0, le_max_right _ _, fun x hx => ?_⟩
    rcases hx with hx | hx
    · by_contra hne
      have hxs : x ∈ tsupport W := subset_tsupport W hne
      exact absurd (hmin hxs) (not_le.2 hx)
    · exact hR x (lt_of_le_of_lt (le_max_left _ _) hx)
  · refine ⟨1, 1, one_pos, le_rfl, fun x _ => image_eq_zero_of_notMem_tsupport fun h => hK ⟨x, h⟩⟩

theorem W0f_eq_zero {W : ℝ → ℝ} {α β : ℝ} (hW : ∀ x, x < α ∨ β < x → W x = 0) {x : ℝ}
    (hx : x < α ∨ β < x) : W0f W x = 0 := by
  unfold W0f; rw [hW x hx, zero_div]

/-- `W₀(x) = x^{−1/2}W(x)` is smooth when `W` is smooth and vanishes below some `α > 0`. -/
theorem W0f_contDiff {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W) {α β : ℝ} (hα : 0 < α)
    (hWs : ∀ x, x < α ∨ β < x → W x = 0) : ContDiff ℝ ∞ (W0f W) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y < α
  · have h0 : W0f W =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hy] with x hx
      exact W0f_eq_zero hWs (Or.inl hx)
    exact contDiffAt_const.congr_of_eventuallyEq h0
  · have hy0 : 0 < y := lt_of_lt_of_le hα (not_lt.1 hy)
    have hs : ContDiffAt ℝ ∞ Real.sqrt y := Real.contDiffAt_sqrt hy0.ne'
    exact hW.contDiffAt.div hs (Real.sqrt_pos.2 hy0).ne'

/-- **A bump** equal to `1` on `[α, β]` with topological support in `[α/2, 2β]`, for `0 < α ≤ β` (the
paper's `I_* = [u/2, 2v]`; round 320, in this file since round 332). -/
theorem exists_bump_one {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ V : ℝ → ℂ, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ Set.Ioi 0 ∧
      tsupport V ⊆ Set.Icc (α / 2) (2 * β) ∧ ∀ y, α ≤ y → y ≤ β → V y = 1 := by
  let f : ContDiffBump ((α + β) / 2) :=
    ⟨(β - α) / 2 + α / 8, (β - α) / 2 + α / 4, by linarith, by linarith⟩
  refine ⟨fun x => ((f x : ℝ) : ℂ), ofRealCLM.contDiff.comp f.contDiff, ?_, ?_, ?_, ?_⟩
  · exact f.hasCompactSupport.comp_left Complex.ofReal_zero
  · intro x hx
    have hx' : x ∈ tsupport f := tsupport_comp_subset Complex.ofReal_zero _ hx
    rw [f.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hx'
    have := neg_abs_le (x - (α + β) / 2)
    show 0 < x
    change |x - (α + β) / 2| ≤ (β - α) / 2 + α / 4 at hx'
    linarith
  · intro x hx
    have hx' : x ∈ tsupport f := tsupport_comp_subset Complex.ofReal_zero _ hx
    rw [f.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hx'
    change |x - (α + β) / 2| ≤ (β - α) / 2 + α / 4 at hx'
    have h1 := neg_abs_le (x - (α + β) / 2)
    have h2 := le_abs_self (x - (α + β) / 2)
    exact ⟨by linarith, by linarith⟩
  · intro y hy1 hy2
    have : f y = 1 := f.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, Real.dist_eq]
      change |y - (α + β) / 2| ≤ (β - α) / 2 + α / 8
      rw [abs_le]
      constructor <;> linarith)
    simp [this]

/-- **A bump** equal to `1` on `[α/2, β]` with topological support in `[α/4, 2β]`, for `0 < α ≤ β`:
`exists_bump_one` at `α/2` (round 332). -/
theorem exists_bump {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ V : ℝ → ℂ, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ Set.Ioi 0 ∧
      tsupport V ⊆ Set.Icc (α / 4) (2 * β) ∧ ∀ y, α / 2 ≤ y → y ≤ β → V y = 1 := by
  obtain ⟨V, h1, h2, h3, h4, h5⟩ := exists_bump_one (β := β) (half_pos hα) (by linarith)
  exact ⟨V, h1, h2, h3, by rwa [div_div, show (2 : ℝ) * 2 = 4 by norm_num] at h4, h5⟩

/-! ### Counting -/

theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x :=
  Real.sqrt_le_self_iff.2 (Or.inr hx)

/-- `#{𝔞 : N𝔞 ≤ x} ≤ (2κ + 5)·x` for `x ≥ 1`, from round 287's ideal theorem with a square-root
error (`abs_idealCount_sub_le`). -/
theorem idealCount_le {x : ℝ} (hx : 1 ≤ x) : (idealCount x : ℝ) ≤ (2 * kappa + 5) * x := by
  have h := abs_idealCount_sub_le (le_trans zero_le_one hx)
  have hk := kappa_pos
  have hs := sqrt_le_self_of_one_le hx
  have h1 := (abs_le.1 h).2
  nlinarith

open Classical in
theorem card_fsLe_le {x : ℝ} (hx : 1 ≤ x) : ((fsLe x).card : ℝ) ≤ (2 * kappa + 5) * x := by
  have hc : (fsLe x).card ≤ idealCount x := by
    unfold fsLe
    calc (((idealsLe x).filter fun I => (absNorm I).Coprime 6 ∧ Squarefree I).image primeSet).card
        ≤ ((idealsLe x).filter fun I => (absNorm I).Coprime 6 ∧ Squarefree I).card :=
          Finset.card_image_le
      _ ≤ (idealsLe x).card := Finset.card_filter_le _ _
      _ = idealCount x := card_idealsLe x
  exact le_trans (by exact_mod_cast hc) (idealCount_le hx)

theorem nI_eq_prod (T : Finset Pr) : nI T = ∏ P ∈ T, (absNorm P.1 : ℝ) := by
  unfold nI; rw [absNorm_idl, Nat.cast_prod]

/-- `Σ_{T⊆A} (−1)^{|T|}·2H/(√3·N(T)) = 2H/√3·∏_{P∈A} (1 − 1/N(P))`: the zero frequency's Möbius sum. -/
theorem sum_kap_empty (H : ℝ) (A : Finset Pr) :
    ∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) =
      ((2 * H / Real.sqrt 3 * ∏ P ∈ A, (1 - 1 / (absNorm P.1 : ℝ)) : ℝ) : ℂ) := by
  have hk : ∀ T : Finset Pr, kap H ∅ ∅ T = 2 * H / Real.sqrt 3 * (∏ P ∈ T, (-1 / (absNorm P.1 : ℝ))) *
      (-1) ^ T.card := by
    intro T
    unfold kap
    rw [nI_empty, mul_one, Real.sqrt_one, mul_one, nI_eq_prod]
    have : (∏ P ∈ T, (-1 / (absNorm P.1 : ℝ))) * (-1) ^ T.card = 1 / ∏ P ∈ T, (absNorm P.1 : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, div_mul_eq_mul_div, ← pow_add, ← two_mul,
        pow_mul]
      norm_num
    rw [mul_assoc, this]; ring
  have hp : ∏ P ∈ A, (1 - 1 / (absNorm P.1 : ℝ)) =
      ∑ T ∈ A.powerset, ∏ P ∈ T, (-1 / (absNorm P.1 : ℝ)) := by
    have := Finset.prod_add (fun P : Pr => -1 / (absNorm P.1 : ℝ)) (fun _ => (1 : ℝ)) A
    simp only [Finset.prod_const_one, mul_one] at this
    rw [← this]
    exact Finset.prod_congr rfl fun P _ => by ring
  rw [hp, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [hk]
  push_cast
  have h1 : ((-1 : ℂ) ^ T.card) * ((-1 : ℂ) ^ T.card) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (2 * (H : ℂ) / (Real.sqrt 3 : ℂ) *
    ∏ P ∈ T, (-1 / ((absNorm P.1 : ℕ) : ℂ))) * h1

theorem prod_one_sub_inv_mem (A : Finset Pr) :
    0 ≤ ∏ P ∈ A, (1 - 1 / (absNorm P.1 : ℝ)) ∧ ∏ P ∈ A, (1 - 1 / (absNorm P.1 : ℝ)) ≤ 1 := by
  have hf : ∀ P ∈ A, 0 ≤ 1 - 1 / (absNorm P.1 : ℝ) ∧ 1 - 1 / (absNorm P.1 : ℝ) ≤ 1 := by
    intro P _
    have h1 : (1 : ℝ) ≤ absNorm P.1 := by exact_mod_cast one_le_absNorm_Pr P
    have h2 : 0 < 1 / (absNorm P.1 : ℝ) := by positivity
    have h3 : 1 / (absNorm P.1 : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
    constructor <;> linarith
  exact ⟨Finset.prod_nonneg fun P hP => (hf P hP).1,
    Finset.prod_le_one₀ (fun P hP => (hf P hP).1) fun P hP => (hf P hP).2⟩

/-- **The zero frequency of one set of primes** (round 332):
`|Σ_{T⊆A} (−1)^{|T|}·2H/(√3N(T))·Φ̂(0)| ≤ 2H/√3·|Φ̂(0)|`, since the sum is
`2H/√3·Π_{P∈A}(1 − 1/N(P))·Φ̂(0)` (`sum_kap_empty`). -/
theorem norm_zeroFreq_le {H : ℝ} (hH : 0 ≤ H) (A : Finset Pr) :
    ‖∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0‖ ≤
      2 * H / Real.sqrt 3 * ‖dualG 0‖ := by
  obtain ⟨h0, h1⟩ := prod_one_sub_inv_mem A
  rw [← Finset.sum_mul, sum_kap_empty, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (by positivity) h0)]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) h1) (norm_nonneg _)

/-- **A zero frequency over a family of sets of primes** (round 332): with weights `|w(A)| ≤ B`,
`|Σ_{A∈𝒜} w(A)·Σ_{T⊆A} (−1)^{|T|}·2H/(√3N(T))·Φ̂(0)| ≤ #𝒜·B·2H/√3·|Φ̂(0)|`. `zero_term_le`,
`zero_Mq_le` and `zero_rowD_le` are its instances. -/
theorem norm_zeroSum_le {H B : ℝ} (hH : 0 ≤ H) (𝒜 : Finset (Finset Pr)) (w : Finset Pr → ℂ)
    (hw : ∀ A ∈ 𝒜, ‖w A‖ ≤ B) :
    ‖∑ A ∈ 𝒜, w A * ∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0‖ ≤
      𝒜.card * (B * (2 * H / Real.sqrt 3 * ‖dualG 0‖)) := by
  calc _ ≤ ∑ A ∈ 𝒜, ‖w A * ∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _A ∈ 𝒜, B * (2 * H / Real.sqrt 3 * ‖dualG 0‖) := Finset.sum_le_sum fun A hA => by
        rw [norm_mul]
        exact mul_le_mul (hw A hA) (norm_zeroFreq_le hH A) (norm_nonneg _)
          ((norm_nonneg _).trans (hw A hA))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The zero frequency** (the paper's `Z ≪ H‖W‖²_∞`, here with the count of the sets of primes):
`|Σ_A W(N(A)/Z)²·Σ_{T⊆A} (−1)^{|T|}·2H/(√3N(T))·Φ̂(0)| ≤ #𝒜·B²·2H/√3·|Φ̂(0)|` for `|W| ≤ B`. -/
theorem zero_term_le {W : ℝ → ℝ} {Bw : ℝ} (hBw : ∀ x, |W x| ≤ Bw) {Z H : ℝ} (hH : 0 ≤ H)
    (𝒜 : Finset (Finset Pr)) :
    ‖∑ A ∈ 𝒜, ((W (nI A / Z) ^ 2 : ℝ) : ℂ) *
        ∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0‖ ≤
      𝒜.card * (Bw ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖)) := by
  refine norm_zeroSum_le hH 𝒜 _ fun A _ => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hBw _) 2

/-- **The divisor bound for `4^{ω(𝔟)}`**: for `δ > 0` there is `C` with `4^{|b|} ≤ C·N(b)^δ`. The
primes with `N(P)^δ ≥ 4` contribute at most `N(b)^δ`; the others are finitely many. -/
theorem four_pow_card_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : Finset Pr, (4 : ℝ) ^ b.card ≤ C * nI b ^ δ := by
  set Y : ℝ := (4 : ℝ) ^ (1 / δ) with hY
  set S := primesLe Y with hS
  refine ⟨(4 : ℝ) ^ S.card, by positivity, fun b => ?_⟩
  have hsplit : b.card = (b ∩ S).card + (b \ S).card := (Finset.card_inter_add_card_sdiff b S).symm
  have h1 : (4 : ℝ) ^ (b ∩ S).card ≤ (4 : ℝ) ^ S.card :=
    pow_le_pow_right₀ (by norm_num) (Finset.card_le_card Finset.inter_subset_right)
  have hlarge : ∀ P ∈ b \ S, (4 : ℝ) ≤ (absNorm P.1 : ℝ) ^ δ := by
    intro P hP
    have hPS : P ∉ S := (Finset.mem_sdiff.1 hP).2
    rw [hS, mem_primesLe, not_le] at hPS
    have hgt : Y < (absNorm P.1 : ℝ) := by
      have := Nat.lt_floor_add_one Y
      have h2 : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ absNorm P.1 := by exact_mod_cast hPS
      push_cast at h2
      linarith
    have hY0 : 0 ≤ Y := by positivity
    calc (4 : ℝ) = Y ^ δ := by
          rw [hY, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one]
      _ ≤ (absNorm P.1 : ℝ) ^ δ := Real.rpow_le_rpow hY0 hgt.le hδ.le
  have h2 : (4 : ℝ) ^ (b \ S).card ≤ nI b ^ δ := by
    calc (4 : ℝ) ^ (b \ S).card = ∏ _P ∈ b \ S, (4 : ℝ) := by rw [Finset.prod_const]
      _ ≤ ∏ P ∈ b \ S, (absNorm P.1 : ℝ) ^ δ :=
          Finset.prod_le_prod₀ (fun _ _ => by norm_num) hlarge
      _ = nI (b \ S) ^ δ := by
          rw [nI_eq_prod, Real.finsetProd_rpow _ _ (fun P _ => by positivity)]
      _ ≤ nI b ^ δ := by
          refine Real.rpow_le_rpow (le_trans zero_le_one (one_le_nI _)) ?_ hδ.le
          unfold nI; exact_mod_cast absNorm_idl_mono Finset.sdiff_subset
  rw [hsplit, pow_add]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- `log₂ n + 1 ≤ (1/(η log 2) + 1)·n^η` for `n ≥ 1`, `η > 0`. -/
theorem natLog_succ_le {η : ℝ} (hη : 0 < η) {n : ℕ} (hn : 1 ≤ n) :
    ((Nat.log 2 n : ℕ) : ℝ) + 1 ≤ (1 / (η * Real.log 2) + 1) * (n : ℝ) ^ η := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  have h1 : Real.log n ≤ (n : ℝ) ^ η / η := Real.log_le_rpow_div hn0.le hη
  have h2 : (1 : ℝ) ≤ (n : ℝ) ^ η := Real.one_le_rpow (by exact_mod_cast hn) hη.le
  have h3 : (Nat.log 2 n : ℝ) ≤ (n : ℝ) ^ η / (η * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc (Nat.log 2 n : ℝ) * (η * Real.log 2) = η * ((Nat.log 2 n : ℝ) * Real.log 2) := by ring
      _ ≤ η * ((n : ℝ) ^ η / η) := mul_le_mul_of_nonneg_left (hlog.trans h1) hη.le
      _ = (n : ℝ) ^ η := by field_simp
  calc ((Nat.log 2 n : ℕ) : ℝ) + 1 ≤ (n : ℝ) ^ η / (η * Real.log 2) + (n : ℝ) ^ η := by linarith
    _ = (1 / (η * Real.log 2) + 1) * (n : ℝ) ^ η := by ring

/-! ### Dyadic shells -/

theorem primesLe_mono {Y Y' : ℝ} (h : Y ≤ Y') : primesLe Y ⊆ primesLe Y' := by
  intro P hP
  rw [mem_primesLe] at hP ⊢
  exact hP.trans (Nat.floor_mono h)

theorem absNorm_idl_ne_zero (b : Finset Pr) : absNorm (idl b) ≠ 0 := by
  have h := one_le_nI b
  unfold nI at h
  have : 1 ≤ absNorm (idl b) := by exact_mod_cast h
  omega

/-- `2^{⌊log₂ N(b)⌋} ≤ N(b) < 2·2^{⌊log₂ N(b)⌋}`. -/
theorem nI_log_bounds (b : Finset Pr) :
    (2 : ℝ) ^ Nat.log 2 (absNorm (idl b)) ≤ nI b ∧
      nI b < 2 * (2 : ℝ) ^ Nat.log 2 (absNorm (idl b)) := by
  have h1 := Nat.pow_log_le_self 2 (absNorm_idl_ne_zero b)
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (absNorm (idl b))
  unfold nI
  constructor
  · exact_mod_cast h1
  · rw [Nat.pow_succ] at h2
    have h3 : (absNorm (idl b) : ℝ) <
        ((2 ^ Nat.log 2 (absNorm (idl b)) * 2 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith

open Classical in
/-- **The harmonic sum over all ideals by dyadic shells** (round 314; in this file since round 332):
`Σ_{𝔞 : N𝔞 ≤ x} 1/N𝔞 ≤ 2(2κ+5)(⌊log₂⌊x⌋⌋ + 1)`. -/
theorem sum_idealsLe_inv_le (x : ℝ) :
    ∑ I ∈ idealsLe x, 1 / (absNorm I : ℝ) ≤
      2 * (2 * kappa + 5) * ((Nat.log 2 ⌊x⌋₊ : ℕ) + 1 : ℝ) := by
  set L := Nat.log 2 ⌊x⌋₊
  set lv : Ideal (𝓞 K) → ℕ := fun I => Nat.log 2 (absNorm I) with hlv
  have hmaps : ∀ I ∈ idealsLe x, lv I ∈ Finset.range (L + 1) := by
    intro I hI
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.log_mono_right (mem_idealsLe.1 hI).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hk := kappa_pos
  calc ∑ j ∈ Finset.range (L + 1), ∑ I ∈ idealsLe x with lv I = j, 1 / (absNorm I : ℝ)
      ≤ ∑ _j ∈ Finset.range (L + 1), 2 * (2 * kappa + 5) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hsub : (idealsLe x).filter (fun I => lv I = j) ⊆ idealsLe ((2 : ℝ) ^ (j + 1)) := by
          intro I hI
          rw [Finset.mem_filter] at hI
          rw [mem_idealsLe]
          have h0 := (mem_idealsLe.1 hI.1).1
          have h1 : absNorm I < 2 ^ (j + 1) := by
            rw [← hI.2]; exact Nat.lt_pow_succ_log_self (by norm_num) _
          have hf : ⌊(2 : ℝ) ^ (j + 1)⌋₊ = 2 ^ (j + 1) := by
            rw [show (2 : ℝ) ^ (j + 1) = ((2 ^ (j + 1) : ℕ) : ℝ) by push_cast; ring,
              Nat.floor_natCast]
          rw [hf]; exact ⟨h0, h1.le⟩
        have hterm : ∀ I ∈ (idealsLe x).filter (fun I => lv I = j),
            1 / (absNorm I : ℝ) ≤ 1 / (2 : ℝ) ^ j := by
          intro I hI
          rw [Finset.mem_filter] at hI
          have h0 := (mem_idealsLe.1 hI.1).1
          have h1 : 2 ^ j ≤ absNorm I := by
            rw [← hI.2]; exact Nat.pow_log_le_self 2 h0.ne'
          have h1' : (2 : ℝ) ^ j ≤ absNorm I := by exact_mod_cast h1
          exact one_div_le_one_div_of_le (by positivity) h1'
        calc ∑ I ∈ idealsLe x with lv I = j, 1 / (absNorm I : ℝ)
            ≤ ∑ _I ∈ (idealsLe x).filter (fun I => lv I = j), 1 / (2 : ℝ) ^ j :=
              Finset.sum_le_sum hterm
          _ = ((idealsLe x).filter (fun I => lv I = j)).card * (1 / (2 : ℝ) ^ j) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((2 * kappa + 5) * (2 : ℝ) ^ (j + 1)) * (1 / (2 : ℝ) ^ j) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc (((idealsLe x).filter (fun I => lv I = j)).card : ℝ)
                  ≤ (idealsLe ((2 : ℝ) ^ (j + 1))).card := by
                    exact_mod_cast Finset.card_le_card hsub
                _ = idealCount ((2 : ℝ) ^ (j + 1)) := by rw [card_idealsLe]
                _ ≤ _ := idealCount_le (one_le_pow₀ (by norm_num))
          _ = 2 * (2 * kappa + 5) := by
              rw [pow_succ]; field_simp
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

open Classical in
/-- **The harmonic sum over squarefree ideals**: `Σ_{𝔟 : N𝔟 ≤ x} 1/N𝔟 ≤ 2(2κ+5)(⌊log₂⌊x⌋⌋ + 1)`,
from `sum_idealsLe_inv_le`, since `𝔟 ↦ ∏_{P∈𝔟} P` is injective (round 332). -/
theorem sum_fsLe_inv_le (x : ℝ) :
    ∑ b ∈ fsLe x, 1 / nI b ≤ 2 * (2 * kappa + 5) * ((Nat.log 2 ⌊x⌋₊ : ℕ) + 1 : ℝ) := by
  calc ∑ b ∈ fsLe x, 1 / nI b = ∑ I ∈ (fsLe x).image idl, 1 / (absNorm I : ℝ) := by
        rw [Finset.sum_image fun A _ B _ h => by rw [← primeSet_idl A, h, primeSet_idl]]; rfl
    _ ≤ ∑ I ∈ idealsLe x, 1 / (absNorm I : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
        (fun I hI => by
          obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hI
          exact mem_idealsLe.2 ⟨Nat.pos_of_ne_zero (absNorm_idl_ne_zero A), mem_fsLe.1 hA⟩)
        (fun _ _ _ => by positivity)
    _ ≤ _ := sum_idealsLe_inv_le x

/-- **The sum of `4^{ω(𝔟)}/N𝔟`** over `N𝔟 ≤ x`, from `4^{|b|} ≤ C·N(b)^δ` and the shells. -/
theorem sum_fsLe_four_pow_le {δ : ℝ} (hδ : 0 < δ) {Cδ : ℝ} (hCδ : 0 < Cδ)
    (h4 : ∀ b : Finset Pr, (4 : ℝ) ^ b.card ≤ Cδ * nI b ^ δ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ b ∈ fsLe x, (4 : ℝ) ^ b.card / nI b ≤
      Cδ * x ^ δ * (2 * (2 * kappa + 5) * ((Nat.log 2 ⌊x⌋₊ : ℕ) + 1 : ℝ)) := by
  calc ∑ b ∈ fsLe x, (4 : ℝ) ^ b.card / nI b ≤ ∑ b ∈ fsLe x, Cδ * x ^ δ * (1 / nI b) := by
        refine Finset.sum_le_sum fun b hb => ?_
        have hb0 := nI_pos b
        have h1 : nI b ^ δ ≤ x ^ δ :=
          Real.rpow_le_rpow hb0.le (nI_le_of_mem_fsLe_real hx hb) hδ.le
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right ((h4 b).trans (mul_le_mul_of_nonneg_left h1 hCδ.le))
          hb0.le
    _ = Cδ * x ^ δ * ∑ b ∈ fsLe x, 1 / nI b := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_fsLe_inv_le x) (by positivity)

/-! ### The rows of a fixed `𝔟` -/

open Classical in
/-- The rows `(T, V, μ)` of a fixed `𝔟`: `T, V ⊆ U∖𝔟` disjoint and `μ ∈ E`. -/
def rowsOf (U b : Finset Pr) (E : Finset (𝓞 K)) : Finset Row :=
  ((U \ b).powerset ×ˢ ((U \ b).powerset ×ˢ E)).filter fun r => Disjoint r.1 r.2.1

open Classical in
theorem mem_rowsOf {U b : Finset Pr} {E : Finset (𝓞 K)} {r : Row} :
    r ∈ rowsOf U b E ↔ r.1 ⊆ U \ b ∧ r.2.1 ⊆ U \ (b ∪ r.1) ∧ r.2.2 ∈ E := by
  unfold rowsOf
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_powerset,
    Finset.mem_powerset]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, ?_, h3⟩
    rw [Finset.subset_sdiff] at h2 ⊢
    exact ⟨h2.1, Finset.disjoint_union_right.2 ⟨h2.2, h4.symm⟩⟩
  · rintro ⟨h1, h2, h3⟩
    rw [Finset.subset_sdiff, Finset.disjoint_union_right] at h2
    exact ⟨⟨h1, Finset.subset_sdiff.2 ⟨h2.1, h2.2.1⟩, h3⟩, h2.2.2.symm⟩

open Classical in
theorem sum_rowsOf (U b : Finset Pr) (E : Finset (𝓞 K)) (g : Row → ℂ) :
    ∑ T ∈ (U \ b).powerset, ∑ V ∈ (U \ (b ∪ T)).powerset, ∑ μ ∈ E, g (T, V, μ) =
      ∑ r ∈ rowsOf U b E, g r := by
  rw [Finset.sum_finset_product (rowsOf U b E) ((U \ b).powerset)
    (fun T => (U \ (b ∪ T)).powerset ×ˢ E) (fun r => by
      rw [mem_rowsOf, Finset.mem_powerset, Finset.mem_product, Finset.mem_powerset])]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_product]

/-- The level `⌊log₂ N(f)⌋` of a row. -/
def lev (r : Row) : ℕ := Nat.log 2 (absNorm (idl (rowF r)))

/-- A row's double sum over its columns. -/
def rowTerm (W : ℝ → ℝ) (Z H : ℝ) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
    (U b : Finset Pr) (r : Row) : ℂ :=
  ∑ M1 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset, ∑ M2 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset,
    rcTerm W Z H ξ1 ξ2 b r.1 r.2.1 r.2.2 M1 M2

/-- The rows that can contribute: `μ` prime to `V`, `N(k) ≤ H_c` and `N(𝔟)N(f) ≤ βZ`. -/
def goodRow (β Z Hc : ℝ) (b : Finset Pr) (r : Row) : Prop :=
  (∀ P ∈ r.2.1, ¬ πP P ∣ r.2.2) ∧ (absNorm (span {rowK r}) : ℝ) ≤ Hc ∧
    nI b * nI (rowF r) ≤ β * Z

theorem absNorm_rowK (r : Row) :
    (absNorm (span {rowK r}) : ℝ) = nI r.1 * (absNorm (span {r.2.2}) : ℝ) := by
  unfold rowK nI eS
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul, span_prod_πP, Nat.cast_mul]

theorem W0f_eq_zero_of_gt {W : ℝ → ℝ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {x : ℝ} (hx : β < x) :
    W0f W x = 0 := by
  unfold W0f; rw [hW x hx, zero_div]

section Vanish

variable (W : ℝ → ℝ) (Z H : ℝ) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
  (b T V : Finset Pr) (μ : 𝓞 K) (M1 M2 : Finset Pr)

theorem rcTerm_eq_zero_of_dvd {P : Pr} (hP : P ∈ V) (h : πP P ∣ μ) :
    rcTerm W Z H ξ1 ξ2 b T V μ M1 M2 = 0 := by
  unfold rcTerm; rw [chiS_eq_zero_of_dvd hP h]; simp

theorem rcTerm_eq_zero_of_W1 (h : W0f W (nI b * nI T * nI V * nI M1 / Z) = 0) :
    rcTerm W Z H ξ1 ξ2 b T V μ M1 M2 = 0 := by
  unfold rcTerm; rw [h]; simp

theorem rcTerm_eq_zero_of_W2 (h : W0f W (nI b * nI T * nI V * nI M2 / Z) = 0) :
    rcTerm W Z H ξ1 ξ2 b T V μ M1 M2 = 0 := by
  unfold rcTerm; rw [h]; simp

theorem rcTerm_eq_zero_of_dualW (h : dualW H (V ∪ M1) (V ∪ M2) T μ = 0) :
    rcTerm W Z H ξ1 ξ2 b T V μ M1 M2 = 0 := by
  unfold rcTerm; rw [h]; simp

end Vanish

/-- **The dual weight vanishes on large frequencies** (round 332): if both columns satisfy
`N(b)N(T)N(V)N(M_j) ≤ c` and `3R²c² ≤ 4H·N(μ)·N(b)²N(T)`, then `Φ̂` vanishes at the dual argument.
`rcTerm_eq_zero_of_large` and `rcDual_eq_zero_of_large_mu` are its instances. -/
theorem dualW_eq_zero_of_le {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {H c : ℝ}
    (b T V M1 M2 : Finset Pr) (μ : 𝓞 K) (hV1 : Disjoint V M1) (hV2 : Disjoint V M2)
    (e1 : nI b * nI T * nI V * nI M1 ≤ c) (e2 : nI b * nI T * nI V * nI M2 ≤ c)
    (hk : 3 * R ^ 2 * c ^ 2 ≤ 4 * H * (absNorm (span {μ}) : ℝ) * (nI b ^ 2 * nI T)) :
    dualW H (V ∪ M1) (V ∪ M2) T μ = 0 := by
  unfold dualW
  refine hR _ ?_
  have hb := nI_pos b; have hT := nI_pos T; have hV := nI_pos V
  have hm1 := nI_pos M1; have hm2 := nI_pos M2
  rw [Real.le_sqrt' hR0, nI_union hV1, nI_union hV2, le_div_iff₀ (by positivity)]
  have e3 : (nI b * nI T * nI V * nI M1) * (nI b * nI T * nI V * nI M2) ≤ c * c :=
    mul_le_mul e1 e2 (by positivity) (le_trans (by positivity) e1)
  have key : R ^ 2 * (3 * (nI V * nI M1 * (nI V * nI M2)) * nI T) * (nI b ^ 2 * nI T) ≤
      4 * H * (absNorm (span {μ}) : ℝ) * (nI b ^ 2 * nI T) := by
    calc R ^ 2 * (3 * (nI V * nI M1 * (nI V * nI M2)) * nI T) * (nI b ^ 2 * nI T)
        = 3 * R ^ 2 * ((nI b * nI T * nI V * nI M1) * (nI b * nI T * nI V * nI M2)) := by ring
      _ ≤ 3 * R ^ 2 * (c * c) := mul_le_mul_of_nonneg_left e3 (by positivity)
      _ = 3 * R ^ 2 * c ^ 2 := by ring
      _ ≤ _ := hk
  exact le_of_mul_le_mul_right key (by positivity)

/-- **The terms beyond the range of `k`** (the paper's restriction `N(k) ≤ 𝓗`): if
`N(d_T)N(μ) > C·Z²/(H·N(𝔟)²)` with `3R²β² ≤ 4C`, every term vanishes, by a weight `W₀` or by the
dual weight `Φ̂` (`dualW_eq_zero_of_le` at `c = βZ`). -/
theorem rcTerm_eq_zero_of_large {W : ℝ → ℝ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {Z H : ℝ}
    (hZ : 0 < Z) (hH : 0 < H) {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {CI : ℝ}
    (hCI : 3 * R ^ 2 * β ^ 2 ≤ 4 * CI) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
    (b T V : Finset Pr) (μ : 𝓞 K) {M1 M2 : Finset Pr} (hV1 : Disjoint V M1) (hV2 : Disjoint V M2)
    (hk : CI * Z ^ 2 / (H * nI b ^ 2) < nI T * (absNorm (span {μ}) : ℝ)) :
    rcTerm W Z H ξ1 ξ2 b T V μ M1 M2 = 0 := by
  by_cases h1 : W0f W (nI b * nI T * nI V * nI M1 / Z) = 0
  · exact rcTerm_eq_zero_of_W1 W Z H ξ1 ξ2 b T V μ M1 M2 h1
  by_cases h2 : W0f W (nI b * nI T * nI V * nI M2 / Z) = 0
  · exact rcTerm_eq_zero_of_W2 W Z H ξ1 ξ2 b T V μ M1 M2 h2
  have hb := nI_pos b
  refine rcTerm_eq_zero_of_dualW W Z H ξ1 ξ2 b T V μ M1 M2
    (dualW_eq_zero_of_le hR0 hR b T V M1 M2 μ hV1 hV2 (c := β * Z) ?_ ?_ ?_)
  · by_contra hc; exact h1 (W0f_eq_zero_of_gt hW (by rw [lt_div_iff₀ hZ]; linarith))
  · by_contra hc; exact h2 (W0f_eq_zero_of_gt hW (by rw [lt_div_iff₀ hZ]; linarith))
  · have ek : CI * Z ^ 2 < nI T * (absNorm (span {μ}) : ℝ) * (H * nI b ^ 2) := by
      rwa [div_lt_iff₀ (by positivity)] at hk
    nlinarith [sq_nonneg Z]

/-- **The rows that cannot contribute vanish**: a row of `rowsOf` that is not good has zero double
column sum. -/
theorem rowTerm_eq_zero {W : ℝ → ℝ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {Z H : ℝ}
    (hZ : 0 < Z) (hH : 0 < H) {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {CI : ℝ}
    (hCI : 3 * R ^ 2 * β ^ 2 ≤ 4 * CI) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
    {U b : Finset Pr} {r : Row} (hr : r.2.1 ⊆ U \ (b ∪ r.1))
    (hng : ¬ goodRow β Z (CI * Z ^ 2 / (H * nI b ^ 2)) b r) :
    rowTerm W Z H ξ1 ξ2 U b r = 0 := by
  have hTV : Disjoint r.1 r.2.1 := by
    have := (Finset.subset_sdiff.1 hr).2
    rw [Finset.disjoint_union_right] at this
    exact this.2.symm
  unfold rowTerm
  refine Finset.sum_eq_zero fun M1 hM1 => Finset.sum_eq_zero fun M2 hM2 => ?_
  have hV1 : Disjoint r.2.1 M1 := disjoint_of_mem_powerset_sdiff hM1
  have hV2 : Disjoint r.2.1 M2 := disjoint_of_mem_powerset_sdiff hM2
  by_cases hA' : ∃ P ∈ r.2.1, πP P ∣ r.2.2
  · obtain ⟨P, hP, hd⟩ := hA'
    exact rcTerm_eq_zero_of_dvd W Z H ξ1 ξ2 b r.1 r.2.1 r.2.2 M1 M2 hP hd
  have hA : ∀ P ∈ r.2.1, ¬ πP P ∣ r.2.2 := fun P hP hd => hA' ⟨P, hP, hd⟩
  by_cases hB : (absNorm (span {rowK r}) : ℝ) ≤ CI * Z ^ 2 / (H * nI b ^ 2)
  swap
  · rw [not_le, absNorm_rowK] at hB
    exact rcTerm_eq_zero_of_large hW hZ hH hR0 hR hCI ξ1 ξ2 b r.1 r.2.1 r.2.2 hV1 hV2 hB
  have hC : β * Z < nI b * nI (rowF r) := by
    by_contra hc; exact hng ⟨hA, hB, not_lt.1 hc⟩
  refine rcTerm_eq_zero_of_W1 W Z H ξ1 ξ2 b r.1 r.2.1 r.2.2 M1 M2 (W0f_eq_zero_of_gt hW ?_)
  rw [rowF, nI_union hTV] at hC
  rw [lt_div_iff₀ hZ]
  have hb := nI_pos b
  have hT := nI_pos r.1
  have hV := nI_pos r.2.1
  have hm := one_le_nI M1
  calc β * Z < nI b * (nI r.1 * nI r.2.1) := hC
    _ = nI b * nI r.1 * nI r.2.1 * 1 := by ring
    _ ≤ nI b * nI r.1 * nI r.2.1 * nI M1 := mul_le_mul_of_nonneg_left hm (by positivity)

open Classical in
/-- **The sum of a fixed `𝔟` over its good rows**: the rows of round 308's sum are `rowsOf`, and the
rows that are not good contribute nothing (`rowTerm_eq_zero`). -/
theorem bTerm_eq_good {W : ℝ → ℝ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {Z H : ℝ}
    (hZ : 0 < Z) (hH : 0 < H) {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {CI : ℝ}
    (hCI : 3 * R ^ 2 * β ^ 2 ≤ 4 * CI) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
    (U b : Finset Pr) (E : Finset (𝓞 K)) :
    ∑ T ∈ (U \ b).powerset, ∑ V ∈ (U \ (b ∪ T)).powerset, ∑ μ ∈ E,
        ∑ M1 ∈ ((U \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U \ (b ∪ T)) \ V).powerset,
          rcTerm W Z H ξ1 ξ2 b T V μ M1 M2 =
      ∑ r ∈ (rowsOf U b E).filter (goodRow β Z (CI * Z ^ 2 / (H * nI b ^ 2)) b),
        rowTerm W Z H ξ1 ξ2 U b r := by
  rw [show (∑ T ∈ (U \ b).powerset, ∑ V ∈ (U \ (b ∪ T)).powerset, ∑ μ ∈ E,
        ∑ M1 ∈ ((U \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U \ (b ∪ T)) \ V).powerset,
          rcTerm W Z H ξ1 ξ2 b T V μ M1 M2) = ∑ r ∈ rowsOf U b E, rowTerm W Z H ξ1 ξ2 U b r
      from sum_rowsOf U b E (rowTerm W Z H ξ1 ξ2 U b)]
  refine (Finset.sum_filter_of_ne fun r hr hne => ?_).symm
  by_contra hng
  exact hne (rowTerm_eq_zero hW hZ hH hR0 hR hCI ξ1 ξ2 (mem_rowsOf.1 hr).2.1 hng)

open Classical in
/-- No row is good when `N(𝔟) > βZ`. -/
theorem good_eq_empty {β Z Hc : ℝ} {b : Finset Pr} (hb : β * Z < nI b) (U : Finset Pr)
    (E : Finset (𝓞 K)) : (rowsOf U b E).filter (goodRow β Z Hc b) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro r _ hg
  unfold goodRow at hg
  have h1 := one_le_nI (rowF r)
  have h2 := nI_pos b
  have : nI b ≤ nI b * nI (rowF r) := le_mul_of_one_le_right h2.le h1
  linarith [hg.2.2]

open Classical in
/-- **The bound for a fixed `𝔟`** (the paper's dyadic decomposition in `N(f)` and Lemma B.2 on each
range): the good rows of level `j = ⌊log₂ N(f)⌋ ≤ ⌊log₂⌊βZ⌋⌋` form one block of round 309's
`rowBlock_bound` at `F = 2^j`, whose column mean squares come from the dual mean square (`hexcl`,
through `rows_colMeanSquare`), so the sum is at most `(⌊log₂⌊βZ⌋⌋ + 1)` times the block bound
`2HN(𝔟)/(√3Z)·K·A_min^{−σ}·4^{|𝔟|}K_c Z^{ε₁}(Z/N(𝔟))²` with `A_min = HN(𝔟)²/(3Z²)`. -/
theorem bTerm_bound (W : ℝ → ℝ) {α β : ℝ} (hβ : 0 ≤ β) (hW : ∀ x, β < x → W x = 0)
    {Z H : ℝ} (hZ : 1 ≤ Z) (hH : 0 < H) {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0)
    {CI : ℝ} (hCI : 3 * R ^ 2 * β ^ 2 ≤ 4 * CI)
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U b : Finset Pr) (E : Finset (𝓞 K))
    (hE : ∀ μ ∈ E, μ ≠ 0) (hU : primesLe (2 * β * Z) ⊆ U)
    (V : ℝ → ℂ) (hVs : tsupport V ⊆ Set.Icc (α / 4) (2 * β)) (J : ℕ)
    {Kb σ Kc ε1 : ℝ} (hKc : 0 ≤ Kc)
    (hK : ∀ {ι κ : Type} (T : Finset ι) (C : Finset κ) (a b : ι → κ → ℂ) (x : κ → ℝ),
      (∀ n ∈ C, 0 < x n) → ∀ M : ℝ, 0 ≤ M →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, a r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, b r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      ∀ ρ : ι → ℝ, (∀ r ∈ T, 1 ≤ ρ r ∧ ρ r ≤ 2) →
      ∀ w : ι → ℂ, (∀ r ∈ T, ‖w r‖ ≤ 1) → ∀ (Ar : ι → ℝ) (Amin : ℝ), 0 < Amin →
      (∀ r ∈ T, Amin ≤ Ar r) →
      ‖∑ r ∈ T, w r * ∑ n1 ∈ C, ∑ n2 ∈ C, a r n1 * conj (b r n2) *
          ((((W0f W (ρ r * x n1)) : ℝ) : ℂ) * conj (((W0f W (ρ r * x n2)) : ℝ) : ℂ) *
            dualG (Real.sqrt (Ar r / (x n1 * x n2))))‖ ≤ Kb * Amin ^ (-σ) * M)
    (hexcl : ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ F : ℝ, 1 ≤ F →
      ∀ W' : ℝ → ℂ, ContDiff ℝ ∞ W' → (∀ x, x < α / 4 ∨ 2 * β < x → W' x = 0) → ∀ N : ℝ,
      (∀ j ≤ J, ∀ x, ‖iteratedDeriv j W' x‖ ≤ N) →
      ∀ (Fs : Finset (Ideal (𝓞 K))) (Ks : Finset (𝓞 K)),
        (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
          (absNorm f : ℝ) < 2 * F) →
        (∀ k ∈ Ks, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ CI * Z ^ 2 / (H * nI b ^ 2)) →
        ∑ f ∈ Fs, ∑ k ∈ Ks, ‖colSum ξ W' (Z / (nI b * F)) (idl b) k (pgen f)‖ ^ 2 ≤
          4 ^ b.card * (Kc * N ^ 2 * Z ^ ε1 * (Z / nI b) ^ 2)) :
    ‖∑ T ∈ (U \ b).powerset, ∑ V' ∈ (U \ (b ∪ T)).powerset, ∑ μ ∈ E,
        ∑ M1 ∈ ((U \ (b ∪ T)) \ V').powerset, ∑ M2 ∈ ((U \ (b ∪ T)) \ V').powerset,
          rcTerm W Z H ξ1 ξ2 b T V' μ M1 M2‖ ≤
      ((Nat.log 2 ⌊β * Z⌋₊ : ℕ) + 1 : ℝ) *
        (2 * H * nI b / (Real.sqrt 3 * Z) * (Kb * (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-σ) *
          (4 ^ b.card * (Kc * Z ^ ε1 * (Z / nI b) ^ 2)))) := by
  have hZ0 : 0 < Z := by linarith
  have hb0 := nI_pos b
  rw [bTerm_eq_good hW hZ0 hH hR0 hR hCI ξ1 ξ2 U b E]
  set Hc := CI * Z ^ 2 / (H * nI b ^ 2) with hHc
  set Amin := H * nI b ^ 2 / (3 * Z ^ 2) with hAmin
  set Mb : ℝ := 4 ^ b.card * (Kc * Z ^ ε1 * (Z / nI b) ^ 2) with hMb
  set L := Nat.log 2 ⌊β * Z⌋₊ with hL
  set G := (rowsOf U b E).filter (goodRow β Z Hc b) with hG
  have hmaps : ∀ r ∈ G, lev r ∈ Finset.range (L + 1) := by
    intro r hr
    rw [hG, Finset.mem_filter] at hr
    obtain ⟨-, hg⟩ := hr
    unfold goodRow at hg
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine Nat.log_mono_right (Nat.le_floor ?_)
    have h2 : nI (rowF r) ≤ β * Z :=
      le_trans (le_mul_of_one_le_left (nI_pos _).le (one_le_nI b)) hg.2.2
    unfold nI at h2; exact_mod_cast h2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hAminpos : 0 < Amin := by positivity
  have hMbnn : 0 ≤ Mb := by positivity
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ Finset.range (L + 1), ‖∑ r ∈ G with lev r = j, rowTerm W Z H ξ1 ξ2 U b r‖
      ≤ ∑ _j ∈ Finset.range (L + 1),
          2 * H * nI b / (Real.sqrt 3 * Z) * (Kb * Amin ^ (-σ) * Mb) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hF : (0 : ℝ) < 2 ^ j := by positivity
        have hF1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        have hfacts : ∀ r ∈ G.filter (fun r => lev r = j), r.2.1 ⊆ U \ (b ∪ r.1) ∧
            Disjoint r.1 r.2.1 ∧ (∀ P ∈ r.2.1, ¬ πP P ∣ r.2.2) ∧ r.2.2 ≠ 0 ∧
            (2 : ℝ) ^ j ≤ nI (rowF r) ∧ nI (rowF r) < 2 * 2 ^ j ∧
            (absNorm (span {rowK r}) : ℝ) ≤ Hc := by
          intro r hr
          rw [Finset.mem_filter, hG, Finset.mem_filter] at hr
          obtain ⟨⟨hrow, hgood⟩, hlev⟩ := hr
          unfold goodRow at hgood
          obtain ⟨-, hV, hμ⟩ := mem_rowsOf.1 hrow
          have hTV : Disjoint r.1 r.2.1 := by
            have := (Finset.subset_sdiff.1 hV).2
            rw [Finset.disjoint_union_right] at this
            exact this.2.symm
          have hb := nI_log_bounds (rowF r)
          rw [show Nat.log 2 (absNorm (idl (rowF r))) = j from hlev] at hb
          exact ⟨hV, hTV, hgood.1, hE _ hμ, hb.1, hb.2, hgood.2.1⟩
        have hX : 0 < Z / (nI b * 2 ^ j) := by positivity
        have hUX : primesLe (2 * β * (Z / (nI b * 2 ^ j))) ⊆ U := by
          refine (primesLe_mono ?_).trans hU
          have : Z / (nI b * 2 ^ j) ≤ Z :=
            div_le_self hZ0.le (one_le_mul_of_one_le_of_one_le (one_le_nI b) hF1)
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hβ) (by norm_num)
        have hcol : ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
            ∀ U' : ℝ → ℂ, ContDiff ℝ ∞ U' → tsupport U' ⊆ tsupport V → ∀ N : ℝ,
            (∀ j' ≤ J, ∀ y, ‖iteratedDeriv j' U' y‖ ≤ N) →
            ∑ r ∈ G.filter (fun r => lev r = j),
              ‖∑ n ∈ (U \ b).powerset, conj (colA ξ (rowK r) (rowFe r) n) *
                U' (nI n / (Z / (nI b * 2 ^ j)))‖ ^ 2 ≤ Mb * N ^ 2 := fun ξ =>
          rows_colMeanSquare ξ J Kc ε1 Z (nI b) (2 ^ j) Hc rfl hX hUX (hexcl ξ (2 ^ j) hF1) V hVs
            (G.filter (fun r => lev r = j)) fun r hr =>
              let h := hfacts r hr
              ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
        have hrows : ∀ r ∈ G.filter (fun r => lev r = j), r.2.1 ⊆ U \ (b ∪ r.1) ∧
            1 ≤ nI (rowF r) / 2 ^ j ∧ nI (rowF r) / 2 ^ j ≤ 2 ∧
            Amin ≤ ARow H (Z / (nI b * 2 ^ j)) r := by
          intro r hr
          obtain ⟨hV, hTV, -, hμ, h1, h2, -⟩ := hfacts r hr
          refine ⟨hV, (one_le_div hF).2 h1, (div_le_iff₀ hF).2 (by linarith), ?_⟩
          exact ARow_ge hH.le hZ0 hF b r hTV hμ h2
        have := rowBlock_bound W hZ0 hF hH.le ξ1 ξ2 (G.filter (fun r => lev r = j)) hAminpos
          hMbnn hrows V J hK (hcol ξ1) (hcol ξ2)
        exact this
    _ = ((L : ℝ) + 1) * (2 * H * nI b / (Real.sqrt 3 * Z) * (Kb * Amin ^ (-σ) * Mb)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

theorem norm_sum_le_of_subset {α : Type*} {s t : Finset α} (h : t ⊆ s) (f : α → ℂ) (g : α → ℝ)
    (h0 : ∀ x ∈ s, x ∉ t → f x = 0) (hg : ∀ x ∈ t, ‖f x‖ ≤ g x) :
    ‖∑ x ∈ s, f x‖ ≤ ∑ x ∈ t, g x := by
  rw [← Finset.sum_subset h h0]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum hg)

theorem norm_double_sum_le {ι : Type*} [Fintype ι] (c X : ι → ι → ℂ) {S : ℝ}
    (hc : ∀ i j, ‖c i j‖ ≤ 1) (hX : ∀ i j, ‖X i j‖ ≤ S) :
    ‖∑ i, ∑ j, c i j * X i j‖ ≤ (Fintype.card ι : ℝ) ^ 2 * S := by
  calc ‖∑ i, ∑ j, c i j * X i j‖ ≤ ∑ i, ∑ j, ‖c i j * X i j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : ι, ∑ _j : ι, S := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hc i j)).trans (hX i j)
    _ = (Fintype.card ι : ℝ) ^ 2 * S := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

open Classical in
/-- **The mean square at one scale** (the paper's Proposition 4.5 before its choice of parameters):
for `N(z) ≤ H`, `Σ_z |A_Z(z)|²` is at most the zero frequency `#𝒜·B²·2H/√3·|Φ̂(0)|` plus
`(#characters mod 4)²·Σ_{𝔟 : N𝔟 ≤ βZ} (⌊log₂⌊βZ⌋⌋ + 1)·(the block bound of 𝔟)`; the hypotheses `hK`
and `hexcl` are the conclusions of round 306's `bilinear_dual_bound₂` and `dualMeanSquare_excl` (the
dual mean square with the exclusion `𝔟`). -/
theorem famSum_meanSquare_le (W : ℝ → ℝ) {α β : ℝ} (hβ : 0 ≤ β) (hW : ∀ x, β < x → W x = 0)
    {Bw : ℝ} (hBw : ∀ x, |W x| ≤ Bw)
    {Z H : ℝ} (hZ : 1 ≤ Z) (hH : 0 < H) {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0)
    {CI : ℝ} (hCI : 3 * R ^ 2 * β ^ 2 ≤ 4 * CI)
    (V : ℝ → ℂ) (hVs : tsupport V ⊆ Set.Icc (α / 4) (2 * β)) (J : ℕ)
    {Kb σ Kc ε1 : ℝ} (hKc : 0 ≤ Kc)
    (hK : ∀ {ι κ : Type} (T : Finset ι) (C : Finset κ) (a b : ι → κ → ℂ) (x : κ → ℝ),
      (∀ n ∈ C, 0 < x n) → ∀ M : ℝ, 0 ≤ M →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, a r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, b r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      ∀ ρ : ι → ℝ, (∀ r ∈ T, 1 ≤ ρ r ∧ ρ r ≤ 2) →
      ∀ w : ι → ℂ, (∀ r ∈ T, ‖w r‖ ≤ 1) → ∀ (Ar : ι → ℝ) (Amin : ℝ), 0 < Amin →
      (∀ r ∈ T, Amin ≤ Ar r) →
      ‖∑ r ∈ T, w r * ∑ n1 ∈ C, ∑ n2 ∈ C, a r n1 * conj (b r n2) *
          ((((W0f W (ρ r * x n1)) : ℝ) : ℂ) * conj (((W0f W (ρ r * x n2)) : ℝ) : ℂ) *
            dualG (Real.sqrt (Ar r / (x n1 * x n2))))‖ ≤ Kb * Amin ^ (-σ) * M)
    (hexcl : ∀ b : Finset Pr, ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ F : ℝ, 1 ≤ F →
      ∀ W' : ℝ → ℂ, ContDiff ℝ ∞ W' → (∀ x, x < α / 4 ∨ 2 * β < x → W' x = 0) → ∀ N : ℝ,
      (∀ j ≤ J, ∀ x, ‖iteratedDeriv j W' x‖ ≤ N) →
      ∀ (Fs : Finset (Ideal (𝓞 K))) (Ks : Finset (𝓞 K)),
        (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
          (absNorm f : ℝ) < 2 * F) →
        (∀ k ∈ Ks, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ CI * Z ^ 2 / (H * nI b ^ 2)) →
        ∑ f ∈ Fs, ∑ k ∈ Ks, ‖colSum ξ W' (Z / (nI b * F)) (idl b) k (pgen f)‖ ^ 2 ≤
          4 ^ b.card * (Kc * N ^ 2 * Z ^ ε1 * (Z / nI b) ^ 2))
    (T : Finset (𝓞 K)) (hT : ∀ z ∈ T, (absNorm (span {z}) : ℝ) ≤ H) :
    ∑ z ∈ T, ‖famSum W Z z‖ ^ 2 ≤
      (fsLe (⌈β * Z⌉₊ : ℝ)).card * (Bw ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖)) +
        (Fintype.card (MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) : ℝ) ^ 2 *
          ∑ b ∈ fsLe (β * Z), ((Nat.log 2 ⌊β * Z⌋₊ : ℕ) + 1 : ℝ) *
            (2 * H * nI b / (Real.sqrt 3 * Z) * (Kb * (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-σ) *
              (4 ^ b.card * (Kc * Z ^ ε1 * (Z / nI b) ^ 2)))) := by
  have hZ0 : 0 < Z := by linarith
  set Y : ℝ := 3 * R ^ 2 * (⌈β * Z⌉₊ : ℝ) ^ 2 / (4 * H) with hYdef
  have hY : 3 * R ^ 2 * (⌈β * Z⌉₊ : ℝ) ^ 2 ≤ 4 * H * Y := by
    have : 4 * H * Y = 3 * R ^ 2 * (⌈β * Z⌉₊ : ℝ) ^ 2 := by
      rw [hYdef]; field_simp
    rw [this]
  set U := primesLe (max (⌈β * Z⌉₊ : ℝ) (2 * β * Z)) with hUdef
  have hU1 : primesLe (⌈β * Z⌉₊ : ℝ) ⊆ U := primesLe_mono (le_max_left _ _)
  have hU2 : primesLe (2 * β * Z) ⊆ U := primesLe_mono (le_max_right _ _)
  have hfsU : fsLe (β * Z) ⊆ U.powerset := by
    intro b hb
    rw [Finset.mem_powerset]
    exact (subset_primesLe hb).trans (primesLe_mono ((Nat.le_ceil _).trans (le_max_left _ _)))
  have hmaj := sum_sq_le_majorant H hH (famSum W Z) (norm_famSum_le hW hZ0) T hT
  refine hmaj.trans ((Complex.re_le_norm _).trans ?_)
  rw [meanSquare_rowcol hW hZ0 hH hR0 hR hY U hU1]
  refine (norm_add_le _ _).trans (add_le_add (zero_term_le hBw hH.le _) ?_)
  refine norm_double_sum_le _ _ (fun ξ1 ξ2 => norm_pairCoeff_le pairPsiCls
    (fun c1 c2 => norm_pairPsiCls_le _ _) ξ1⁻¹ ξ2) fun ξ1 ξ2 => ?_
  refine norm_sum_le_of_subset hfsU _ _ (fun b _ hb => ?_) (fun b _ => ?_)
  · have hlt : β * Z < nI b := by
      rw [mem_fsLe, not_le] at hb
      unfold nI; exact Nat.lt_of_floor_lt hb
    rw [bTerm_eq_good hW hZ0 hH hR0 hR hCI ξ1 ξ2 U b _, good_eq_empty hlt, Finset.sum_empty]
  · exact bTerm_bound W hβ hW hZ hH hR0 hR hCI ξ1 ξ2 U b _
      (fun μ hμ => (Finset.mem_erase.1 hμ).1) hU2 V hVs J hKc hK (hexcl b)

/-! ### The choice of parameters -/

/-- `A_min^{−e} ≤ 3^e·Z^e` for `A_min = H·N(𝔟)²/(3Z²)` and `Z ≤ H`. -/
theorem Amin_rpow_le {e : ℝ} (he : 0 ≤ e) {Z H : ℝ} (hZ : 1 ≤ Z) (hZH : Z ≤ H) (b : Finset Pr) :
    (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-e) ≤ 3 ^ e * Z ^ e := by
  have hZ0 : 0 < Z := by linarith
  have hH : 0 < H := by linarith
  have hb := one_le_nI b
  have hb0 := nI_pos b
  have hA : 0 < H * nI b ^ 2 / (3 * Z ^ 2) := by positivity
  rw [Real.rpow_neg hA.le, ← Real.inv_rpow hA.le, ← Real.mul_rpow (by norm_num) hZ0.le]
  refine Real.rpow_le_rpow (by positivity) ?_ he
  rw [inv_div, div_le_iff₀ (by positivity)]
  have h1 : Z ≤ H * nI b ^ 2 := by
    have : 1 ≤ nI b ^ 2 := one_le_pow₀ hb
    nlinarith
  nlinarith

/-- `⌊log₂⌊βZ⌋⌋ + 1 ≤ (1/(e log 2) + 1)·(β+1)^e·Z^e` for `e > 0`, `β ≥ 0`, `Z ≥ 1`. -/
theorem log_floor_succ_le {e : ℝ} (he : 0 < e) {β Z : ℝ} (hβ : 0 ≤ β) (hZ : 1 ≤ Z) :
    ((Nat.log 2 ⌊β * Z⌋₊ : ℕ) : ℝ) + 1 ≤ (1 / (e * Real.log 2) + 1) * (β + 1) ^ e * Z ^ e := by
  have hZ0 : 0 ≤ Z := by linarith
  have h1 := natLog_succ_le he (n := ⌊β * Z⌋₊ + 1) (by omega)
  have h2 : ((Nat.log 2 ⌊β * Z⌋₊ : ℕ) : ℝ) ≤ ((Nat.log 2 (⌊β * Z⌋₊ + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.log_mono_right (Nat.le_succ _)
  have h3 : ((⌊β * Z⌋₊ + 1 : ℕ) : ℝ) ≤ (β + 1) * Z := by
    push_cast
    have := Nat.floor_le (mul_nonneg hβ hZ0)
    nlinarith
  have h4 : ((⌊β * Z⌋₊ + 1 : ℕ) : ℝ) ^ e ≤ ((β + 1) * Z) ^ e :=
    Real.rpow_le_rpow (by positivity) h3 he.le
  rw [Real.mul_rpow (by linarith) hZ0] at h4
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hc : 0 ≤ 1 / (e * Real.log 2) + 1 := by positivity
  calc ((Nat.log 2 ⌊β * Z⌋₊ : ℕ) : ℝ) + 1 ≤ ((Nat.log 2 (⌊β * Z⌋₊ + 1) : ℕ) : ℝ) + 1 := by
        linarith
    _ ≤ (1 / (e * Real.log 2) + 1) * ((⌊β * Z⌋₊ + 1 : ℕ) : ℝ) ^ e := h1
    _ ≤ (1 / (e * Real.log 2) + 1) * ((β + 1) ^ e * Z ^ e) := mul_le_mul_of_nonneg_left h4 hc
    _ = _ := by ring

/-- **The block bound of one `𝔟`**, simplified:
`2HN(𝔟)/(√3Z)·K·A_min^{−e}·4^{|𝔟|}K_c Z^e(Z/N(𝔟))² ≤ (2/√3·K′·3^e·K_c)·HZ·(Z^e)²·4^{|𝔟|}/N(𝔟)`. -/
theorem blockBound_le {e : ℝ} (he : 0 ≤ e) {Z H : ℝ} (hZ : 1 ≤ Z) (hZH : Z ≤ H)
    {Kb Kb' Kc : ℝ} (hKb : Kb ≤ Kb') (hKb' : 0 ≤ Kb') (hKc : 0 ≤ Kc) (b : Finset Pr) :
    2 * H * nI b / (Real.sqrt 3 * Z) * (Kb * (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-e) *
      (4 ^ b.card * (Kc * Z ^ e * (Z / nI b) ^ 2))) ≤
    (2 / Real.sqrt 3 * Kb' * 3 ^ e * Kc) * (H * Z * (Z ^ e) ^ 2) * ((4 : ℝ) ^ b.card / nI b) := by
  have hZ0 : 0 < Z := by linarith
  have hH : 0 < H := by linarith
  have hb := nI_pos b
  have hA := Amin_rpow_le he hZ hZH b
  have hA0 : 0 ≤ (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-e) := Real.rpow_nonneg (by positivity) _
  have hPe : 0 ≤ Z ^ e := Real.rpow_nonneg hZ0.le _
  have e1 : 2 * H * nI b / (Real.sqrt 3 * Z) * (Kb' * (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-e) *
      (4 ^ b.card * (Kc * Z ^ e * (Z / nI b) ^ 2))) =
      (2 / Real.sqrt 3 * Kb' * Kc) * (H * Z * Z ^ e) * ((4 : ℝ) ^ b.card / nI b) *
        (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-e) := by
    field_simp
  calc 2 * H * nI b / (Real.sqrt 3 * Z) * (Kb * (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-e) *
        (4 ^ b.card * (Kc * Z ^ e * (Z / nI b) ^ 2)))
      ≤ 2 * H * nI b / (Real.sqrt 3 * Z) * (Kb' * (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-e) *
        (4 ^ b.card * (Kc * Z ^ e * (Z / nI b) ^ 2))) := by
        gcongr
    _ = (2 / Real.sqrt 3 * Kb' * Kc) * (H * Z * Z ^ e) * ((4 : ℝ) ^ b.card / nI b) *
        (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-e) := e1
    _ ≤ (2 / Real.sqrt 3 * Kb' * Kc) * (H * Z * Z ^ e) * ((4 : ℝ) ^ b.card / nI b) *
        (3 ^ e * Z ^ e) := mul_le_mul_of_nonneg_left hA (by positivity)
    _ = _ := by ring

open Classical in
/-- **The second conditional milestone: the dual mean square gives the family's mean square** (the
companion paper's Proposition 4.5 with its choice of parameters `H = Z^{1+ϑ}`, `e = ε/5`):
`DualMeanSquare ϑ ⇒ MeanSquare ϑ` for `ϑ > 0`. -/
theorem meanSquare_of_dualMeanSquare {ϑ : ℝ} (hϑ : 0 < ϑ) (hDM : DualMeanSquare ϑ) :
    MeanSquare ϑ := by
  intro W hW ε hε
  obtain ⟨α, β, hα, hαβ, hWs⟩ := weight_support hW
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hWβ : ∀ x, β < x → W x = 0 := fun x hx => hWs x (Or.inr hx)
  obtain ⟨Bw, hBw'⟩ := hW.smooth.continuous.bounded_above_of_compact_support hW.compact
  have hBw : ∀ x, |W x| ≤ Bw := fun x => by have := hBw' x; rwa [Real.norm_eq_abs] at this
  have hBw0 : 0 ≤ Bw := le_trans (abs_nonneg _) (hBw 0)
  set e := ε / 5 with he_def
  have he : 0 < e := by positivity
  obtain ⟨V, hV, hVc, hVp, hVs, hV1⟩ := exists_bump hα hαβ
  obtain ⟨R, hR0, hR⟩ := exists_dualG_eq_zero
  obtain ⟨J, hJ⟩ := dualMeanSquare_excl hDM e he
  set CI := max 1 (3 * R ^ 2 * β ^ 2 / 4) with hCI_def
  have hCI1 : 1 ≤ CI := le_max_left _ _
  have hCI : 3 * R ^ 2 * β ^ 2 ≤ 4 * CI := by
    have := le_max_right 1 (3 * R ^ 2 * β ^ 2 / 4); linarith
  obtain ⟨Kc, hKc⟩ := hJ (α / 4) (2 * β) (by positivity) CI hCI1
  have hW0 : ContDiff ℝ ∞ (fun y => ((W0f W y : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp (W0f_contDiff hW.smooth hα hWs)
  have hW0s : ∀ y, y < α ∨ β < y → (fun y => ((W0f W y : ℝ) : ℂ)) y = 0 := fun y hy => by
    simp only [W0f_eq_zero hWs hy, ofReal_zero]
  obtain ⟨Kb, hKb⟩ := MellinSep.bilinear_dual_bound₂ (fun y => ((W0f W y : ℝ) : ℂ)) hW0 hα hW0s
    V hV hVc hVp (ρ0 := 1) (ρ1 := 2) one_pos (fun y h1 h2 => hV1 y h1 (by rwa [div_one] at h2))
    J dualG dualG_contDiff dualG_bounded hR he
  obtain ⟨Cδ, hCδ, h4⟩ := four_pow_card_le he
  have hk := kappa_pos
  set Kb' := max Kb 0 with hKb'
  set Kc' := max Kc 0 with hKc'
  have hKb'0 : 0 ≤ Kb' := le_max_right _ _
  have hKc'0 : 0 ≤ Kc' := le_max_right _ _
  set nξ : ℝ := (Fintype.card (MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) : ℝ) with hnξ
  set cL := (1 / (e * Real.log 2) + 1) * (β + 1) ^ e with hcL
  set c2 := 2 / Real.sqrt 3 * Kb' * 3 ^ e * Kc' with hc2
  have hc20 : 0 ≤ c2 := by positivity
  set C0 := (2 * kappa + 5) * (β + 1) * (Bw ^ 2 * (2 / Real.sqrt 3 * ‖dualG 0‖)) with hC0
  set C1 := nξ ^ 2 * (cL ^ 2 * c2 * Cδ * β ^ e * (2 * (2 * kappa + 5))) with hC1
  refine ⟨C0 + C1, fun Z hZ T hT => ?_⟩
  have hZ0 : 0 < Z := by linarith
  set H := Z ^ (1 + ϑ) with hHdef
  have hH : 0 < H := Real.rpow_pos_of_pos hZ0 _
  have hZH : Z ≤ H := by
    calc Z = Z ^ (1 : ℝ) := (Real.rpow_one Z).symm
      _ ≤ Z ^ (1 + ϑ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hexcl : ∀ b : Finset Pr, ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ F : ℝ, 1 ≤ F →
      ∀ W' : ℝ → ℂ, ContDiff ℝ ∞ W' → (∀ x, x < α / 4 ∨ 2 * β < x → W' x = 0) → ∀ N : ℝ,
      (∀ j ≤ J, ∀ x, ‖iteratedDeriv j W' x‖ ≤ N) →
      ∀ (Fs : Finset (Ideal (𝓞 K))) (Ks : Finset (𝓞 K)),
        (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
          (absNorm f : ℝ) < 2 * F) →
        (∀ k ∈ Ks, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ CI * Z ^ 2 / (H * nI b ^ 2)) →
        ∑ f ∈ Fs, ∑ k ∈ Ks, ‖colSum ξ W' (Z / (nI b * F)) (idl b) k (pgen f)‖ ^ 2 ≤
          4 ^ b.card * (Kc' * N ^ 2 * Z ^ e * (Z / nI b) ^ 2) := by
    intro b ξ F hF W' hW' hW's N hN Fs Ks hFs hKs
    have hb := nI_pos b
    have hHc : 0 < CI * Z ^ 2 / (H * nI b ^ 2) := by positivity
    have h := hKc ξ W' hW' hW's N hN Z (nI b) F (CI * Z ^ 2 / (H * nI b ^ 2)) hZ (one_le_nI b) hF
      hHc le_rfl (idl b) (idl_coprime6 b) (idl_squarefree b) Fs Ks hFs hKs
    rw [primeSet_idl] at h
    refine h.trans ?_
    have hN2 : 0 ≤ N ^ 2 * Z ^ e * (Z / nI b) ^ 2 := by positivity
    have : Kc * N ^ 2 * Z ^ e * (Z / nI b) ^ 2 ≤ Kc' * N ^ 2 * Z ^ e * (Z / nI b) ^ 2 := by
      have := mul_le_mul_of_nonneg_right (le_max_left Kc 0) hN2
      calc Kc * N ^ 2 * Z ^ e * (Z / nI b) ^ 2 = Kc * (N ^ 2 * Z ^ e * (Z / nI b) ^ 2) := by ring
        _ ≤ Kc' * (N ^ 2 * Z ^ e * (Z / nI b) ^ 2) := this
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hmain := famSum_meanSquare_le W hβ.le hWβ hBw hZ hH hR0 hR hCI V hVs J hKc'0 hKb hexcl T
    (fun z hz => (hT z hz).2)
  refine hmain.trans ?_
  -- the arithmetic of the exponents
  set P := Z ^ e with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hZ he.le
  have hP0 : 0 ≤ P := by linarith
  have hZpow : Z ^ (2 + ϑ + ε) = H * Z * P ^ 5 := by
    rw [show 2 + ϑ + ε = (1 + ϑ) + 1 + e * ((5 : ℕ) : ℝ) by rw [he_def]; push_cast; ring,
      Real.rpow_add hZ0, Real.rpow_add hZ0, Real.rpow_one, Real.rpow_mul_natCast hZ0.le]
  rw [hZpow]
  -- the zero frequency
  have hM1 : (1 : ℝ) ≤ (⌈β * Z⌉₊ : ℝ) := by
    have : 0 < ⌈β * Z⌉₊ := Nat.ceil_pos.2 (by positivity)
    exact_mod_cast this
  have hMle : (⌈β * Z⌉₊ : ℝ) ≤ (β + 1) * Z := by
    have := Nat.ceil_lt_add_one (R := ℝ) (mul_nonneg hβ.le hZ0.le)
    nlinarith
  have hzero : ((fsLe (⌈β * Z⌉₊ : ℝ)).card : ℝ) * (Bw ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖)) ≤
      C0 * (H * Z * P ^ 5) := by
    have hc := card_fsLe_le hM1
    have hP5 : 1 ≤ P ^ 5 := one_le_pow₀ hP1
    have hB : 0 ≤ Bw ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖) := by positivity
    calc ((fsLe (⌈β * Z⌉₊ : ℝ)).card : ℝ) * (Bw ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖))
        ≤ ((2 * kappa + 5) * ((β + 1) * Z)) * (Bw ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖)) :=
          mul_le_mul_of_nonneg_right (hc.trans (mul_le_mul_of_nonneg_left hMle (by positivity)))
            hB
      _ = C0 * (H * Z) := by rw [hC0]; ring
      _ ≤ C0 * (H * Z * P ^ 5) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hP5) (by positivity)
  -- the dual sum
  set Lp : ℝ := ((Nat.log 2 ⌊β * Z⌋₊ : ℕ) : ℝ) + 1 with hLp
  have hLp0 : 0 ≤ Lp := by positivity
  have hLle : Lp ≤ cL * P := log_floor_succ_le he hβ.le hZ
  have hsum := sum_fsLe_four_pow_le he hCδ h4 (x := β * Z) (by positivity)
  rw [Real.mul_rpow hβ.le hZ0.le] at hsum
  have hoff : nξ ^ 2 * ∑ b ∈ fsLe (β * Z), Lp *
        (2 * H * nI b / (Real.sqrt 3 * Z) * (Kb * (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-e) *
          (4 ^ b.card * (Kc' * P * (Z / nI b) ^ 2)))) ≤ C1 * (H * Z * P ^ 5) := by
    calc nξ ^ 2 * ∑ b ∈ fsLe (β * Z), Lp *
          (2 * H * nI b / (Real.sqrt 3 * Z) * (Kb * (H * nI b ^ 2 / (3 * Z ^ 2)) ^ (-e) *
            (4 ^ b.card * (Kc' * P * (Z / nI b) ^ 2))))
        ≤ nξ ^ 2 * ∑ b ∈ fsLe (β * Z), Lp *
            (c2 * (H * Z * P ^ 2) * ((4 : ℝ) ^ b.card / nI b)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left (blockBound_le he.le hZ hZH (le_max_left Kb 0)
            hKb'0 hKc'0 b) hLp0
      _ = nξ ^ 2 * (Lp * (c2 * (H * Z * P ^ 2)) *
            ∑ b ∈ fsLe (β * Z), (4 : ℝ) ^ b.card / nI b) := by
          rw [Finset.mul_sum (s := fsLe (β * Z)) (a := Lp * (c2 * (H * Z * P ^ 2)))]
          congr 1
          exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ nξ ^ 2 * (Lp * (c2 * (H * Z * P ^ 2)) *
            (Cδ * (β ^ e * P) * (2 * (2 * kappa + 5) * Lp))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (sq_nonneg _)
      _ = nξ ^ 2 * (Lp ^ 2 * (c2 * Cδ * β ^ e * (2 * (2 * kappa + 5)) * (H * Z * P ^ 3))) := by
          ring
      _ ≤ nξ ^ 2 * ((cL * P) ^ 2 * (c2 * Cδ * β ^ e * (2 * (2 * kappa + 5)) * (H * Z * P ^ 3))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hLp0 hLle 2)
            (by positivity)) (sq_nonneg _)
      _ = C1 * (H * Z * P ^ 5) := by rw [hC1]; ring
  calc _ ≤ C0 * (H * Z * P ^ 5) + C1 * (H * Z * P ^ 5) := add_le_add hzero hoff
    _ = (C0 + C1) * (H * Z * P ^ 5) := by ring


/-- **The composed conditional milestone**: the dual mean square at `ϑ > 0` gives `ζ(s) ≠ 0` and
`L(s, χ₋₃) ≠ 0` on `Re s > (11 + 5ϑ)/12` (round 288's `ne_zero_of_meanSquare` after
`meanSquare_of_dualMeanSquare`). -/
theorem ne_zero_of_dualMeanSquare {ϑ : ℝ} (hϑ : 0 < ϑ) (h : DualMeanSquare ϑ) {s : ℂ}
    (hs : (11 + 5 * ϑ) / 12 < s.re) :
    riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction PsiOmega.chi3 s ≠ 0 :=
  ne_zero_of_meanSquare hϑ.le (meanSquare_of_dualMeanSquare hϑ h) hs

end Eis

end

#print axioms Eis.weight_support
#print axioms Eis.W0f_eq_zero
#print axioms Eis.W0f_contDiff
#print axioms Eis.exists_bump_one
#print axioms Eis.exists_bump
#print axioms Eis.sqrt_le_self_of_one_le
#print axioms Eis.idealCount_le
#print axioms Eis.card_fsLe_le
#print axioms Eis.nI_eq_prod
#print axioms Eis.sum_kap_empty
#print axioms Eis.prod_one_sub_inv_mem
#print axioms Eis.norm_zeroFreq_le
#print axioms Eis.norm_zeroSum_le
#print axioms Eis.zero_term_le
#print axioms Eis.four_pow_card_le
#print axioms Eis.natLog_succ_le
#print axioms Eis.primesLe_mono
#print axioms Eis.absNorm_idl_ne_zero
#print axioms Eis.nI_log_bounds
#print axioms Eis.sum_idealsLe_inv_le
#print axioms Eis.sum_fsLe_inv_le
#print axioms Eis.sum_fsLe_four_pow_le
#print axioms Eis.mem_rowsOf
#print axioms Eis.sum_rowsOf
#print axioms Eis.absNorm_rowK
#print axioms Eis.W0f_eq_zero_of_gt
#print axioms Eis.rcTerm_eq_zero_of_dvd
#print axioms Eis.rcTerm_eq_zero_of_W1
#print axioms Eis.rcTerm_eq_zero_of_W2
#print axioms Eis.rcTerm_eq_zero_of_dualW
#print axioms Eis.dualW_eq_zero_of_le
#print axioms Eis.rcTerm_eq_zero_of_large
#print axioms Eis.rowTerm_eq_zero
#print axioms Eis.bTerm_eq_good
#print axioms Eis.good_eq_empty
#print axioms Eis.bTerm_bound
#print axioms Eis.norm_sum_le_of_subset
#print axioms Eis.norm_double_sum_le
#print axioms Eis.famSum_meanSquare_le
#print axioms Eis.Amin_rpow_le
#print axioms Eis.log_floor_succ_le
#print axioms Eis.blockBound_le
#print axioms Eis.meanSquare_of_dualMeanSquare
#print axioms Eis.ne_zero_of_dualMeanSquare
