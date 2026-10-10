import EisensteinQuadSieveSigma3

/-! # The quadratic large sieve, part 4e: the error terms over disjoint pairs (round 352)

S5e of round 312's plan, S5e-4e as staged in round 351: the error terms of `Σ_3` and `Σ_4`
over the disjoint pairs of columns, through round 348's Mellin form of the lattice error and
round 350's bilinear bound.

* **The bilinear bound under a Mellin integral** (`mellin_bilin`): for an integrable `C`, row
  coefficients `ρ_t(d)` on a finite set of rows with `|ρ_t(d)| ≤ w(d)` and column multipliers
  `u_t(B)` with `|u_t(B)| ≤ U(B)`, both continuous in `t`, the sum over disjoint pairs
  `Σ a(B₁)b(B₂)∫C(t)Σ_d ρ_t(d)u_t(B₁)u_t(B₂)ρ_{B₁}(d)ρ_{B₂}(d)dt` has modulus at most
  `‖C‖₁·Δ·√(Σ_B 2^{|B|}U(B)²|a(B)|²)·√(Σ_B 2^{|B|}U(B)²|b(B)|²)` when `FBound w X Δ`
  (round 350's `bilin_disj_le_c` for each `t`).
* **`Σ_4`'s error** (`err4`, `err4_mellin`, `err4_bilin`): the error of round 350's
  `sig4_eq_main_add` for the pair `(G ∪ B₁, G ∪ B₂)` is a Mellin integral of product form, with
  `ρ_t(d) = (N(d)/M)^{s/2}∏_{Q∈G}(1 − N(Q)^s)` on the squarefree rows prime to `G` and
  `u_t(B) = ∏_{Q∈B}(1 − N(Q)^s)`, `s = ε − 2πit` (`sM`, `eulS`). For `K ≤ M` its sum over the
  disjoint pairs is at most `C₀·Π_G·Δ·√(Σ 2^{|B|}Π_B²|a|²)·√(Σ 2^{|B|}Π_B²|b|²)` with
  `Π_S = ∏_{Q∈S}(1 + N(Q)^ε)` and `FBound (sqfW K) X Δ`.
* **`Σ_3`'s error** (`err3T`, `err3`, `err3T_mellin`, `err3_bilin`): for each `T ⊆ G` the
  error piece of round 351's `sig3_eq_main_add` factors the same way, since
  `1/√N(B₁ ∪ B₂)` and `√κ_T` split over `B₁` and `B₂` (`sqrt_kappa_split`, `cpow_mul4`), with
  `u_t(B) = N(B)^{−1/2−s/2}ρ_B(π_T)∏_{Q∈B}(1 − N(Q)^s)`. Its sum over the disjoint pairs is at
  most `2^{|G|}(2M/√3)C₀(4M/3)^{ε/2}K₁^{ε/2}·Δ·√(Σ 2^{|B|}N(B)⁻¹Π_B²|a|²)·√(…)` with
  `FBound (sqfW K₁) X Δ`; the factor `N(B)⁻¹` is what columns in shells turn into `M/N`.
-/

open Complex MeasureTheory Set NumberField Ideal
open scoped Classical

noncomputable section

namespace Eis

theorem integrable_mul_bdd {C g : ℝ → ℂ} (hC : Integrable C) (hg : Continuous g) {B : ℝ}
    (hB : ∀ t, ‖g t‖ ≤ B) : Integrable fun t => C t * g t := by
  refine (hC.norm.mul_const B).mono' (hC.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)

/-- **The bilinear bound under a Mellin integral**: for an integrable `C`, row coefficients
`ρ_t(d)` on a finite set of rows with `|ρ_t(d)| ≤ w(d)` and column multipliers `u_t(B)` with
`|u_t(B)| ≤ U(B)`, both continuous in `t`,
`|Σ_{B₁,B₂ disjoint} a(B₁)b(B₂)∫C(t)Σ_d ρ_t(d)u_t(B₁)u_t(B₂)ρ_{B₁}(d)ρ_{B₂}(d)dt|
  ≤ ‖C‖₁·Δ·√(Σ_B 2^{|B|}U(B)²|a(B)|²)·√(Σ_B 2^{|B|}U(B)²|b(B)|²)`. -/
theorem mellin_bilin {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) {X Δ : ℝ}
    (hΔ : 0 ≤ Δ) (h : FBound w X Δ) (𝒩 : Finset (Finset Pr)) (h𝒩 : ∀ A ∈ 𝒩, nI A ≤ X)
    (a b : Finset Pr → ℂ) {C : ℝ → ℂ} (hC : Integrable C) (R : Finset (𝓞 K))
    (ρ : ℝ → 𝓞 K → ℂ) (hρc : ∀ d, Continuous fun t => ρ t d)
    (hρ : ∀ t, ∀ d ∈ R, ‖ρ t d‖ ≤ w d)
    (u : ℝ → Finset Pr → ℂ) (huc : ∀ B, Continuous fun t => u t B) (U : Finset Pr → ℝ)
    (hu : ∀ t B, ‖u t B‖ ≤ U B) :
    ‖∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, if Disjoint B1 B2 then a B1 * b B2 *
        ∫ t, C t * ∑ d ∈ R, ρ t d * (u t B1 * u t B2 * (q2 B1 d * q2 B2 d)) else 0‖ ≤
      (∫ t, ‖C t‖) * (Δ * (Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * (U B ^ 2 * ‖a B‖ ^ 2)) *
        Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * (U B ^ 2 * ‖b B‖ ^ 2)))) := by
  set g : Finset Pr → Finset Pr → ℝ → ℂ := fun B1 B2 t =>
    ∑ d ∈ R, ρ t d * (u t B1 * u t B2 * (q2 B1 d * q2 B2 d)) with hg
  have hU0 : ∀ B, 0 ≤ U B := fun B => (norm_nonneg _).trans (hu 0 B)
  have hgc : ∀ B1 B2, Continuous (g B1 B2) := fun B1 B2 =>
    continuous_finsetSum _ fun d _ =>
      (hρc d).mul (((huc B1).mul (huc B2)).mul continuous_const)
  have hgb : ∀ B1 B2 t, ‖g B1 B2 t‖ ≤ ∑ d ∈ R, w d * (U B1 * U B2) := fun B1 B2 t => by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have h1 := norm_q2_le B1 d
    have h2 := norm_q2_le B2 d
    have hq : ‖q2 B1 d‖ * ‖q2 B2 d‖ ≤ 1 := by
      nlinarith [norm_nonneg (q2 B1 d), norm_nonneg (q2 B2 d)]
    have huu : ‖u t B1‖ * ‖u t B2‖ ≤ U B1 * U B2 :=
      mul_le_mul (hu t B1) (hu t B2) (norm_nonneg _) (hU0 B1)
    have h3 : ‖u t B1‖ * ‖u t B2‖ * (‖q2 B1 d‖ * ‖q2 B2 d‖) ≤ U B1 * U B2 := by
      calc ‖u t B1‖ * ‖u t B2‖ * (‖q2 B1 d‖ * ‖q2 B2 d‖) ≤ ‖u t B1‖ * ‖u t B2‖ * 1 :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ ≤ U B1 * U B2 := by rw [mul_one]; exact huu
    exact mul_le_mul (hρ t d hd) h3 (by positivity) (hw0 d)
  have hint : ∀ B1 B2, Integrable fun t => C t * g B1 B2 t := fun B1 B2 =>
    integrable_mul_bdd hC (hgc B1 B2) (hgb B1 B2)
  -- the sum of integrals as one integral
  have hsum : (∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, if Disjoint B1 B2 then a B1 * b B2 *
      ∫ t, C t * g B1 B2 t else 0) =
      ∫ t, ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, if Disjoint B1 B2 then a B1 * b B2 * (C t * g B1 B2 t) else 0 := by
    have hi : ∀ B1 B2, Integrable fun t =>
        if Disjoint B1 B2 then a B1 * b B2 * (C t * g B1 B2 t) else 0 := by
      intro B1 B2
      split_ifs
      · exact (hint B1 B2).const_mul _
      · exact integrable_zero _ _ _
    rw [integral_finsetSum _ fun B1 _ => integrable_finsetSum _ fun B2 _ => hi B1 B2]
    refine Finset.sum_congr rfl fun B1 _ => ?_
    rw [integral_finsetSum _ fun B2 _ => hi B1 B2]
    refine Finset.sum_congr rfl fun B2 _ => ?_
    split_ifs
    · rw [integral_const_mul]
    · rw [integral_zero]
  show ‖∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, if Disjoint B1 B2 then a B1 * b B2 *
      ∫ t, C t * g B1 B2 t else 0‖ ≤ _
  rw [hsum]
  -- the pointwise bound
  set Bd : ℝ := Δ * (Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * (U B ^ 2 * ‖a B‖ ^ 2)) *
    Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * (U B ^ 2 * ‖b B‖ ^ 2))) with hBd
  have hpt : ∀ t, ‖∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩,
      (if Disjoint B1 B2 then a B1 * b B2 * (C t * g B1 B2 t) else 0)‖ ≤ ‖C t‖ * Bd := by
    intro t
    set α : Finset Pr → ℂ := fun B => a B * u t B with hα
    set β : Finset Pr → ℂ := fun B => b B * u t B with hβ
    set c : 𝓞 K → ℂ := fun m => if m ∈ R then ρ t m else 0 with hc
    have hcw : ∀ m, ‖c m‖ ≤ w m := fun m => by
      simp only [hc]
      split_ifs with hm
      · exact hρ t m hm
      · rw [norm_zero]; exact hw0 m
    set Zf : 𝓞 K → ℂ := fun m => ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩,
      (if Disjoint B1 B2 then α B1 * β B2 * (q2 B1 m * q2 B2 m) else 0) with hZf
    have htsum : ∑' m : 𝓞 K, c m * Zf m = ∑ m ∈ R, c m * Zf m :=
      tsum_eq_sum fun m hm => by simp only [hc, hm, ite_false, zero_mul]
    have hre : (∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩,
        (if Disjoint B1 B2 then a B1 * b B2 * (C t * g B1 B2 t) else 0)) =
        C t * ∑' m : 𝓞 K, c m * Zf m := by
      rw [htsum]
      calc (∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩,
            (if Disjoint B1 B2 then a B1 * b B2 * (C t * g B1 B2 t) else 0))
          = ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, ∑ d ∈ R, C t * (ρ t d *
              (if Disjoint B1 B2 then α B1 * β B2 * (q2 B1 d * q2 B2 d) else 0)) := by
            refine Finset.sum_congr rfl fun B1 _ => Finset.sum_congr rfl fun B2 _ => ?_
            split_ifs
            · simp only [hg, hα, hβ, Finset.mul_sum]
              refine Finset.sum_congr rfl fun d _ => ?_
              ring
            · simp
        _ = ∑ d ∈ R, ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, C t * (ρ t d *
              (if Disjoint B1 B2 then α B1 * β B2 * (q2 B1 d * q2 B2 d) else 0)) := by
            exact (Finset.sum_congr rfl fun B1 _ => Finset.sum_comm).trans Finset.sum_comm
        _ = C t * ∑ d ∈ R, c d * Zf d := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun d hd => ?_
            simp only [hc, hZf, hd, ite_true, Finset.mul_sum]
    rw [hre, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (bilin_disj_le_c hw0 hw hΔ h 𝒩 h𝒩 α β c hcw).trans ?_
    have hmono : ∀ γ : Finset Pr → ℂ, ∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * ‖γ B * u t B‖ ^ 2 ≤
        ∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * (U B ^ 2 * ‖γ B‖ ^ 2) := fun γ =>
      Finset.sum_le_sum fun B _ => by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [norm_mul, mul_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hu t B) 2) (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt (hmono a))
      (Real.sqrt_le_sqrt (hmono b)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hΔ
  calc ‖∫ t, ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩,
        (if Disjoint B1 B2 then a B1 * b B2 * (C t * g B1 B2 t) else 0)‖
      ≤ ∫ t, ‖C t‖ * Bd :=
        norm_integral_le_of_norm_le (hC.norm.mul_const Bd) (Filter.Eventually.of_forall hpt)
    _ = (∫ t, ‖C t‖) * Bd := integral_mul_const _ _

/-- The Mellin exponent `s = ε − 2πit`. -/
def sM (ε t : ℝ) : ℂ := (ε : ℂ) - ((2 * Real.pi * t : ℝ) : ℂ) * I

theorem continuous_sM (ε : ℝ) : Continuous (sM ε) := by unfold sM; fun_prop

theorem sM_re (ε t : ℝ) : (sM ε t).re = ε := by simp [sM]

theorem continuous_cpow_sM {β : ℝ} (hβ : 0 < β) (ε : ℝ) :
    Continuous fun t => (β : ℂ) ^ sM ε t :=
  (continuous_sM ε).const_cpow (Or.inl (by exact_mod_cast hβ.ne'))

theorem norm_cpow_sM {β : ℝ} (hβ : 0 < β) (ε t : ℝ) : ‖(β : ℂ) ^ sM ε t‖ = β ^ ε := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hβ, sM_re]

/-- The Euler factor `∏_{Q∈S}(1 − N(Q)^s)` on `Re s = ε`. -/
def eulS (ε : ℝ) (S : Finset Pr) (t : ℝ) : ℂ :=
  ∏ Q ∈ S, (1 - ((absNorm Q.1 : ℝ) : ℂ) ^ sM ε t)

theorem continuous_eulS (ε : ℝ) (S : Finset Pr) : Continuous (eulS ε S) := by
  unfold eulS
  exact continuous_finsetProd _ fun Q _ =>
    continuous_const.sub (continuous_cpow_sM (absNorm_Pr_pos Q) ε)

theorem norm_eulS_le (ε : ℝ) (S : Finset Pr) (t : ℝ) :
    ‖eulS ε S t‖ ≤ ∏ Q ∈ S, (1 + (absNorm Q.1 : ℝ) ^ ε) :=
  norm_prod_one_sub_le S t

theorem eulS_union {ε : ℝ} {A B : Finset Pr} (h : Disjoint A B) (t : ℝ) :
    eulS ε (A ∪ B) t = eulS ε A t * eulS ε B t := by
  unfold eulS; rw [Finset.prod_union h]

theorem eulS_bound_nonneg (ε : ℝ) (S : Finset Pr) : 0 ≤ ∏ Q ∈ S, (1 + (absNorm Q.1 : ℝ) ^ ε) :=
  Finset.prod_nonneg fun Q _ => by positivity

/-- **Weights scale**: `FBound w X Δ` gives `FBound (c·w) X (c·Δ)` for `c ≥ 0`. -/
theorem FBound.const_mul {w : 𝓞 K → ℝ} {X Δ c : ℝ} (hc : 0 ≤ c) (h : FBound w X Δ) :
    FBound (fun m => c * w m) X (c * Δ) := by
  intro 𝒩 α h𝒩
  have := h 𝒩 α h𝒩
  calc ∑' m : 𝓞 K, c * w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2
      = c * ∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 := by
        rw [← tsum_mul_left]; exact tsum_congr fun m => by ring
    _ ≤ c * (Δ * ∑ A ∈ 𝒩, ‖α A‖ ^ 2) := mul_le_mul_of_nonneg_left this hc
    _ = c * Δ * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 := by ring

theorem summable_sqfW (Y : ℝ) : Summable (sqfW Y) := by
  refine summable_of_ne_finset_zero (s := eltsLe Y) fun m hm => ?_
  unfold sqfW
  rw [mem_eltsLe] at hm
  exact ite_eq_right fun h => hm h.2

/-- The error of `Σ_4` for a pair (round 350's `sig4_eq_main_add`). -/
def err4 (M Kt : ℝ) (G D : Finset Pr) : ℂ :=
  ∑ d ∈ eltsLe Kt, (if Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d then
    q2 D d * ∑ T ∈ (G ∪ D).powerset, (-1 : ℂ) ^ T.card *
      latErr PhiOnR (Real.sqrt ((absNorm (span {d}) : ℝ) / M) * nI T) else 0)

/-- The row coefficient of `Σ_4`'s error under the Mellin integral. -/
def rho4 (ε M : ℝ) (G : Finset Pr) (t : ℝ) (d : 𝓞 K) : ℂ :=
  if Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d then
    ((Real.sqrt ((absNorm (span {d}) : ℝ) / M) : ℝ) : ℂ) ^ sM ε t * eulS ε G t else 0

theorem rho4_of {ε M : ℝ} {G : Finset Pr} {t : ℝ} {d : 𝓞 K}
    (hd : Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d) :
    rho4 ε M G t d = ((Real.sqrt ((absNorm (span {d}) : ℝ) / M) : ℝ) : ℂ) ^ sM ε t * eulS ε G t :=
  ite_eq_left hd

theorem rho4_of_not {ε M : ℝ} {G : Finset Pr} {t : ℝ} {d : 𝓞 K}
    (hd : ¬ (Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d)) : rho4 ε M G t d = 0 :=
  ite_eq_right hd

theorem absNorm_sqf_pos {d : 𝓞 K} (hd : Squarefree (span {d})) :
    (0 : ℝ) < absNorm (span {d}) := by
  refine Nat.cast_pos.2 (Nat.pos_of_ne_zero ?_)
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact sqf_ne_zero hd

theorem continuous_rho4 (ε M : ℝ) (hM : 0 < M) (G : Finset Pr) (d : 𝓞 K) :
    Continuous fun t => rho4 ε M G t d := by
  by_cases hd : Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d
  · simp_rw [rho4_of hd]
    exact (continuous_cpow_sM (Real.sqrt_pos.2 (div_pos (absNorm_sqf_pos hd.1) hM)) ε).mul
      (continuous_eulS ε G)
  · simp_rw [rho4_of_not hd]
    exact continuous_const

theorem norm_rho4_le {ε M Kt : ℝ} (hε : 0 < ε) (hM : 0 < M) (hK : Kt ≤ M) (G : Finset Pr)
    (t : ℝ) {d : 𝓞 K} (hdK : d ∈ eltsLe Kt) :
    ‖rho4 ε M G t d‖ ≤ (∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) * sqfW Kt d := by
  unfold rho4 sqfW
  have hN := mem_eltsLe.1 hdK
  by_cases hd : Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d
  · rw [ite_eq_left hd, ite_eq_left ⟨hd.1, hN⟩, mul_one, norm_mul]
    have hβ : 0 < Real.sqrt ((absNorm (span {d}) : ℝ) / M) :=
      Real.sqrt_pos.2 (div_pos (absNorm_sqf_pos hd.1) hM)
    rw [norm_cpow_sM hβ]
    have h1 : Real.sqrt ((absNorm (span {d}) : ℝ) / M) ^ ε ≤ 1 := by
      refine Real.rpow_le_one (Real.sqrt_nonneg _) ?_ hε.le
      rw [Real.sqrt_le_one, div_le_one hM]
      linarith
    calc Real.sqrt ((absNorm (span {d}) : ℝ) / M) ^ ε * ‖eulS ε G t‖
        ≤ 1 * ∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε) :=
          mul_le_mul h1 (norm_eulS_le ε G t) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [ite_eq_right hd, norm_zero]
    exact mul_nonneg (eulS_bound_nonneg ε G) (by split_ifs <;> norm_num)

/-- **`Σ_4`'s error for a pair as a Mellin integral of product form**: for `C` representing the
Möbius sums of the lattice error (round 348's `latErr_moebius`) and disjoint `G, B₁, B₂`,
`err₄(G, B₁ ∪ B₂) = ∫C(t)Σ_d ρ_t(d)·u_t(B₁)u_t(B₂)·ρ_{B₁}(d)ρ_{B₂}(d)dt`, with
`u_t(B) = ∏_{Q∈B}(1 − N(Q)^s)`. -/
theorem err4_mellin {ε M Kt : ℝ} (hM : 0 < M) {C : ℝ → ℂ} (hC : Integrable C)
    (hCrep : ∀ β : ℝ, 0 < β → ∀ S : Finset Pr,
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * latErr PhiOnR (β * nI T) =
        ∫ t : ℝ, C t * ((β : ℂ) ^ sM ε t * eulS ε S t))
    {G B1 B2 : Finset Pr} (h12 : Disjoint B1 B2) (hG1 : Disjoint G B1) (hG2 : Disjoint G B2) :
    err4 M Kt G (B1 ∪ B2) = ∫ t, C t * ∑ d ∈ eltsLe Kt, rho4 ε M G t d *
      (eulS ε B1 t * eulS ε B2 t * (q2 B1 d * q2 B2 d)) := by
  have hGD : Disjoint G (B1 ∪ B2) := Finset.disjoint_union_right.2 ⟨hG1, hG2⟩
  set Y : 𝓞 K → ℝ → ℂ := fun d t => rho4 ε M G t d *
    (eulS ε B1 t * eulS ε B2 t * (q2 B1 d * q2 B2 d)) with hY
  have hYc : ∀ d, Continuous (Y d) := fun d =>
    (continuous_rho4 ε M hM G d).mul (((continuous_eulS ε B1).mul (continuous_eulS ε B2)).mul
      continuous_const)
  have hYb : ∀ d, ∃ B, ∀ t, ‖Y d t‖ ≤ B := by
    intro d
    refine ⟨(if Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d then
      Real.sqrt ((absNorm (span {d}) : ℝ) / M) ^ ε else 0) *
        (∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) * ((∏ Q ∈ B1, (1 + (absNorm Q.1 : ℝ) ^ ε)) *
          (∏ Q ∈ B2, (1 + (absNorm Q.1 : ℝ) ^ ε))), fun t => ?_⟩
    simp only [hY]
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have hq : ‖q2 B1 d‖ * ‖q2 B2 d‖ ≤ 1 := by
      have h1 := norm_q2_le B1 d
      have h2 := norm_q2_le B2 d
      nlinarith [norm_nonneg (q2 B1 d), norm_nonneg (q2 B2 d)]
    have he1 := norm_eulS_le ε B1 t
    have he2 := norm_eulS_le ε B2 t
    have hr : ‖rho4 ε M G t d‖ ≤ (if Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d then
        Real.sqrt ((absNorm (span {d}) : ℝ) / M) ^ ε else 0) *
          (∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) := by
      unfold rho4
      split_ifs with hd
      · rw [norm_mul, norm_cpow_sM (Real.sqrt_pos.2 (div_pos (absNorm_sqf_pos hd.1) hM))]
        exact mul_le_mul_of_nonneg_left (norm_eulS_le ε G t) (by positivity)
      · simp
    have hp1 := eulS_bound_nonneg ε B1
    have hp2 := eulS_bound_nonneg ε B2
    have hee : ‖eulS ε B1 t‖ * ‖eulS ε B2 t‖ * (‖q2 B1 d‖ * ‖q2 B2 d‖) ≤
        (∏ Q ∈ B1, (1 + (absNorm Q.1 : ℝ) ^ ε)) * (∏ Q ∈ B2, (1 + (absNorm Q.1 : ℝ) ^ ε)) := by
      calc ‖eulS ε B1 t‖ * ‖eulS ε B2 t‖ * (‖q2 B1 d‖ * ‖q2 B2 d‖)
          ≤ ‖eulS ε B1 t‖ * ‖eulS ε B2 t‖ * 1 := mul_le_mul_of_nonneg_left hq (by positivity)
        _ ≤ _ := by rw [mul_one]; exact mul_le_mul he1 he2 (norm_nonneg _) hp1
    exact mul_le_mul hr hee (by positivity) (by
      refine mul_nonneg ?_ (eulS_bound_nonneg ε G)
      split_ifs <;> positivity)
  have hint : ∀ d, Integrable fun t => C t * Y d t := fun d => by
    obtain ⟨B, hB⟩ := hYb d
    exact integrable_mul_bdd hC (hYc d) hB
  -- each row as an integral
  have hrow : ∀ d ∈ eltsLe Kt, (if Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d then
      q2 (B1 ∪ B2) d * ∑ T ∈ (G ∪ (B1 ∪ B2)).powerset, (-1 : ℂ) ^ T.card *
        latErr PhiOnR (Real.sqrt ((absNorm (span {d}) : ℝ) / M) * nI T) else 0) =
      ∫ t, C t * Y d t := by
    intro d _
    by_cases hd : Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d
    · have hβ : 0 < Real.sqrt ((absNorm (span {d}) : ℝ) / M) :=
        Real.sqrt_pos.2 (div_pos (absNorm_sqf_pos hd.1) hM)
      rw [ite_eq_left hd, hCrep _ hβ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hY]
      rw [rho4_of hd, eulS_union hGD, eulS_union h12, q2_union h12]
      ring
    · rw [ite_eq_right hd]
      simp only [hY, rho4_of_not hd, zero_mul, mul_zero, integral_zero]
  unfold err4
  rw [Finset.sum_congr rfl hrow, ← integral_finsetSum _ fun d _ => hint d]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [hY, Finset.mul_sum]

/-- **The bilinear bound for `Σ_4`'s error**: for every `ε > 0` there is `C₀` such that for
`0 < M`, `K ≤ M`, `FBound (sqfW K) X Δ`, a family of column sets of norm at most `X` disjoint from
`G` and any coefficients,
`|Σ_{B₁,B₂ disjoint} a(B₁)b(B₂)err₄(G, B₁ ∪ B₂)|
  ≤ C₀·Π_G·Δ·√(Σ_B 2^{|B|}Π_B²|a(B)|²)·√(Σ_B 2^{|B|}Π_B²|b(B)|²)`,
`Π_S = ∏_{Q∈S}(1 + N(Q)^ε)`. -/
theorem err4_bilin {ε : ℝ} (hε : 0 < ε) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (M Kt X Δ : ℝ) (G : Finset Pr) (𝒩 : Finset (Finset Pr))
      (a b : Finset Pr → ℂ), 0 < M → Kt ≤ M → 0 ≤ Δ → FBound (sqfW Kt) X Δ →
      (∀ B ∈ 𝒩, nI B ≤ X) → (∀ B ∈ 𝒩, Disjoint G B) →
      ‖∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, if Disjoint B1 B2 then a B1 * b B2 * err4 M Kt G (B1 ∪ B2) else 0‖ ≤
        C0 * ((∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) * Δ *
          (Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card *
              ((∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * ‖a B‖ ^ 2)) *
            Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card *
              ((∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * ‖b B‖ ^ 2)))) := by
  obtain ⟨C, hC, hCrep⟩ := latErr_moebius PhiOnR hε
  refine ⟨∫ t, ‖C t‖, integral_nonneg fun t => norm_nonneg _,
    fun M Kt X Δ G 𝒩 a b hM hK hΔ hF h𝒩 hG => ?_⟩
  have hCrep' : ∀ β : ℝ, 0 < β → ∀ S : Finset Pr,
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * latErr PhiOnR (β * nI T) =
        ∫ t : ℝ, C t * ((β : ℂ) ^ sM ε t * eulS ε S t) := fun β hβ S => hCrep β hβ S
  set Λ : ℝ := ∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε) with hΛ
  have hΛ0 : 0 ≤ Λ := eulS_bound_nonneg ε G
  have hrep : ∀ B1 ∈ 𝒩, ∀ B2 ∈ 𝒩, (if Disjoint B1 B2 then a B1 * b B2 *
      err4 M Kt G (B1 ∪ B2) else 0) = (if Disjoint B1 B2 then a B1 * b B2 *
      ∫ t, C t * ∑ d ∈ eltsLe Kt, rho4 ε M G t d *
        (eulS ε B1 t * eulS ε B2 t * (q2 B1 d * q2 B2 d)) else 0) := by
    intro B1 hB1 B2 hB2
    split_ifs with h12
    · rw [err4_mellin hM hC hCrep' h12 (hG B1 hB1) (hG B2 hB2)]
    · rfl
  rw [Finset.sum_congr rfl fun B1 hB1 => Finset.sum_congr rfl fun B2 hB2 => hrep B1 hB1 B2 hB2]
  have hb := mellin_bilin (w := fun m => Λ * sqfW Kt m) (fun m => mul_nonneg hΛ0 (sqfW_nonneg _ _))
    ((summable_sqfW Kt).mul_left Λ) (mul_nonneg hΛ0 hΔ) (hF.const_mul hΛ0) 𝒩 h𝒩 a b hC
    (eltsLe Kt) (fun t d => rho4 ε M G t d) (continuous_rho4 ε M hM G)
    (fun t d hd => norm_rho4_le hε hM hK G t hd) (fun t B => eulS ε B t) (continuous_eulS ε)
    (fun B => ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) (fun t B => norm_eulS_le ε B t)
  refine hb.trans (le_of_eq ?_)
  ring

/-- The `T`-th piece of `Σ_3`'s error for a pair (round 351's `sig3_eq_main_add`), without the
sign: `2M/(√3√N(D)N(T))·ρ_D(π_T)·Σ_d ρ_D(d)Σ_{T'⊆D}(−1)^{|T'|}r_G(√(κ_T N(d))N(T'))`. -/
def err3T (M K₁ : ℝ) (T D : Finset Pr) : ℂ :=
  (((2 * M / (Real.sqrt 3 * Real.sqrt (nI D) * nI T)) : ℝ) : ℂ) * q2 D (∏ P ∈ T, πP P) *
    ∑ d ∈ eltsLe K₁, (if Squarefree (span {d}) then
      q2 D d * ∑ T' ∈ D.powerset, (-1 : ℂ) ^ T'.card *
        latErr dualR (Real.sqrt (4 * M / (3 * nI D * nI T) * (absNorm (span {d}) : ℝ)) * nI T')
      else 0)

/-- `Σ_3`'s error for a pair. -/
def err3 (M K₁ : ℝ) (G D : Finset Pr) : ℂ :=
  ∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * err3T M K₁ T D

/-- The row coefficient of `Σ_3`'s error under the Mellin integral. -/
def rho3 (ε M : ℝ) (T : Finset Pr) (t : ℝ) (d : 𝓞 K) : ℂ :=
  if Squarefree (span {d}) then
    ((Real.sqrt (4 * M / (3 * nI T)) : ℝ) : ℂ) ^ sM ε t *
      ((Real.sqrt (absNorm (span {d}) : ℝ) : ℝ) : ℂ) ^ sM ε t else 0

/-- The column multiplier of `Σ_3`'s error under the Mellin integral. -/
def u3 (ε : ℝ) (T : Finset Pr) (t : ℝ) (B : Finset Pr) : ℂ :=
  (((Real.sqrt (nI B))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (nI B))⁻¹ : ℝ) : ℂ) ^ sM ε t *
    q2 B (∏ P ∈ T, πP P) * eulS ε B t

theorem rho3_of {ε M : ℝ} {T : Finset Pr} {t : ℝ} {d : 𝓞 K} (hd : Squarefree (span {d})) :
    rho3 ε M T t d = ((Real.sqrt (4 * M / (3 * nI T)) : ℝ) : ℂ) ^ sM ε t *
      ((Real.sqrt (absNorm (span {d}) : ℝ) : ℝ) : ℂ) ^ sM ε t :=
  ite_eq_left hd

theorem rho3_of_not {ε M : ℝ} {T : Finset Pr} {t : ℝ} {d : 𝓞 K} (hd : ¬ Squarefree (span {d})) :
    rho3 ε M T t d = 0 :=
  ite_eq_right hd

theorem continuous_rho3 (ε : ℝ) {M : ℝ} (hM : 0 < M) (T : Finset Pr) (d : 𝓞 K) :
    Continuous fun t => rho3 ε M T t d := by
  by_cases hd : Squarefree (span {d})
  · simp_rw [rho3_of hd]
    exact (continuous_cpow_sM (Real.sqrt_pos.2 (by have := nI_pos T; positivity)) ε).mul
      (continuous_cpow_sM (Real.sqrt_pos.2 (absNorm_sqf_pos hd)) ε)
  · simp_rw [rho3_of_not hd]
    exact continuous_const

theorem continuous_u3 (ε : ℝ) (T B : Finset Pr) : Continuous fun t => u3 ε T t B := by
  unfold u3
  have hB : 0 < (Real.sqrt (nI B))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (nI_pos B))
  exact ((continuous_const.mul (continuous_cpow_sM hB ε)).mul continuous_const).mul
    (continuous_eulS ε B)

theorem norm_rho3_le {ε M K₁ : ℝ} (hε : 0 < ε) (hM : 0 < M) (T : Finset Pr) (t : ℝ)
    {d : 𝓞 K} (hdK : d ∈ eltsLe K₁) :
    ‖rho3 ε M T t d‖ ≤ (Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) * sqfW K₁ d := by
  have hN := mem_eltsLe.1 hdK
  by_cases hd : Squarefree (span {d})
  · rw [rho3_of hd]
    unfold sqfW
    rw [ite_eq_left ⟨hd, hN⟩, mul_one, norm_mul]
    have hT := one_le_nI T
    have h1 : 0 < Real.sqrt (4 * M / (3 * nI T)) :=
      Real.sqrt_pos.2 (by have := nI_pos T; positivity)
    rw [norm_cpow_sM h1, norm_cpow_sM (Real.sqrt_pos.2 (absNorm_sqf_pos hd))]
    refine mul_le_mul (Real.rpow_le_rpow h1.le (Real.sqrt_le_sqrt ?_) hε.le)
      (Real.rpow_le_rpow (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hN) hε.le)
      (by positivity) (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · rw [rho3_of_not hd, norm_zero]
    exact mul_nonneg (by positivity) (sqfW_nonneg _ _)

theorem norm_u3_le {ε : ℝ} (hε : 0 < ε) (T : Finset Pr) (t : ℝ) (B : Finset Pr) :
    ‖u3 ε T t B‖ ≤ (Real.sqrt (nI B))⁻¹ * ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε) := by
  unfold u3
  have hB0 : 0 < Real.sqrt (nI B) := Real.sqrt_pos.2 (nI_pos B)
  have hB : 0 < (Real.sqrt (nI B))⁻¹ := inv_pos.2 hB0
  have hB1 : (Real.sqrt (nI B))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hB0, Real.one_le_sqrt]
    exact one_le_nI B
  rw [norm_mul, norm_mul, norm_mul, norm_cpow_sM hB, Complex.norm_real,
    Real.norm_of_nonneg hB.le]
  have h1 : (Real.sqrt (nI B))⁻¹ ^ ε ≤ 1 := Real.rpow_le_one hB.le hB1 hε.le
  have h2 := norm_q2_le B (∏ P ∈ T, πP P)
  have h3 := norm_eulS_le ε B t
  have h4 := eulS_bound_nonneg ε B
  calc (Real.sqrt (nI B))⁻¹ * (Real.sqrt (nI B))⁻¹ ^ ε * ‖q2 B (∏ P ∈ T, πP P)‖ * ‖eulS ε B t‖
      ≤ (Real.sqrt (nI B))⁻¹ * 1 * 1 * ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε) := by
        gcongr
    _ = _ := by ring

/-- `√(4M/(3N(B₁)N(B₂)N(T))·n) = √(4M/(3N(T)))·N(B₁)^{−1/2}·N(B₂)^{−1/2}·√n`. -/
theorem sqrt_kappa_split {M x y z n : ℝ} (hM : 0 < M) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.sqrt (4 * M / (3 * (x * y) * z) * n) =
      Real.sqrt (4 * M / (3 * z)) * (Real.sqrt x)⁻¹ * (Real.sqrt y)⁻¹ * Real.sqrt n := by
  rw [show 4 * M / (3 * (x * y) * z) * n = 4 * M / (3 * z) * x⁻¹ * y⁻¹ * n by
      field_simp]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_inv, Real.sqrt_inv]

theorem cpow_mul4 {a b c n : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hn : 0 ≤ n) (r : ℂ) :
    ((a * b * c * n : ℝ) : ℂ) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ r * (c : ℂ) ^ r * (n : ℂ) ^ r := by
  rw [Complex.ofReal_mul (a * b * c) n, Complex.mul_cpow_ofReal_nonneg (by positivity) hn,
    Complex.ofReal_mul (a * b) c, Complex.mul_cpow_ofReal_nonneg (by positivity) hc,
    Complex.ofReal_mul a b, Complex.mul_cpow_ofReal_nonneg ha hb]

/-- **`Σ_3`'s error piece for a pair as a Mellin integral of product form**: for `C`
representing the Möbius sums of the dual lattice error and disjoint `B₁, B₂`,
`err₃,T(B₁ ∪ B₂) = 2M/(√3N(T))·∫C(t)Σ_d ρ_t(d)u_t(B₁)u_t(B₂)ρ_{B₁}(d)ρ_{B₂}(d)dt`. -/
theorem err3T_mellin {ε M K₁ : ℝ} (hM : 0 < M) {C : ℝ → ℂ} (hC : Integrable C)
    (hCrep : ∀ β : ℝ, 0 < β → ∀ S : Finset Pr,
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * latErr dualR (β * nI T) =
        ∫ t : ℝ, C t * ((β : ℂ) ^ sM ε t * eulS ε S t))
    (T : Finset Pr) {B1 B2 : Finset Pr} (h12 : Disjoint B1 B2) :
    err3T M K₁ T (B1 ∪ B2) = (((2 * M / (Real.sqrt 3 * nI T)) : ℝ) : ℂ) *
      ∫ t, C t * ∑ d ∈ eltsLe K₁, rho3 ε M T t d *
        (u3 ε T t B1 * u3 ε T t B2 * (q2 B1 d * q2 B2 d)) := by
  set Y : 𝓞 K → ℝ → ℂ := fun d t => rho3 ε M T t d *
    (u3 ε T t B1 * u3 ε T t B2 * (q2 B1 d * q2 B2 d)) with hY
  have hTp := nI_pos T
  have hYc : ∀ d, Continuous (Y d) := fun d =>
    (continuous_rho3 ε hM T d).mul (((continuous_u3 ε T B1).mul (continuous_u3 ε T B2)).mul
      continuous_const)
  have hrb : ∀ d t, ‖rho3 ε M T t d‖ ≤ (if Squarefree (span {d}) then
      Real.sqrt (4 * M / (3 * nI T)) ^ ε * Real.sqrt (absNorm (span {d}) : ℝ) ^ ε else 0) := by
    intro d t
    by_cases hd : Squarefree (span {d})
    · rw [rho3_of hd, ite_eq_left hd, norm_mul,
        norm_cpow_sM (Real.sqrt_pos.2 (by positivity)),
        norm_cpow_sM (Real.sqrt_pos.2 (absNorm_sqf_pos hd))]
    · rw [rho3_of_not hd, ite_eq_right hd, norm_zero]
  have hub : ∀ B t, ‖u3 ε T t B‖ ≤ (Real.sqrt (nI B))⁻¹ * (Real.sqrt (nI B))⁻¹ ^ ε *
      ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε) := by
    intro B t
    unfold u3
    have hB : 0 < (Real.sqrt (nI B))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (nI_pos B))
    rw [norm_mul, norm_mul, norm_mul, norm_cpow_sM hB, Complex.norm_real,
      Real.norm_of_nonneg hB.le]
    have h2 := norm_q2_le B (∏ P ∈ T, πP P)
    have h3 := norm_eulS_le ε B t
    calc (Real.sqrt (nI B))⁻¹ * (Real.sqrt (nI B))⁻¹ ^ ε * ‖q2 B (∏ P ∈ T, πP P)‖ *
          ‖eulS ε B t‖
        ≤ (Real.sqrt (nI B))⁻¹ * (Real.sqrt (nI B))⁻¹ ^ ε * 1 *
            ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε) := by gcongr
      _ = _ := by ring
  have hYb : ∀ d t, ‖Y d t‖ ≤ (if Squarefree (span {d}) then
      Real.sqrt (4 * M / (3 * nI T)) ^ ε * Real.sqrt (absNorm (span {d}) : ℝ) ^ ε else 0) *
      (((Real.sqrt (nI B1))⁻¹ * (Real.sqrt (nI B1))⁻¹ ^ ε *
          ∏ Q ∈ B1, (1 + (absNorm Q.1 : ℝ) ^ ε)) *
        ((Real.sqrt (nI B2))⁻¹ * (Real.sqrt (nI B2))⁻¹ ^ ε *
          ∏ Q ∈ B2, (1 + (absNorm Q.1 : ℝ) ^ ε))) := by
    intro d t
    simp only [hY]
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have hq : ‖q2 B1 d‖ * ‖q2 B2 d‖ ≤ 1 := by
      have h1 := norm_q2_le B1 d
      have h2 := norm_q2_le B2 d
      nlinarith [norm_nonneg (q2 B1 d), norm_nonneg (q2 B2 d)]
    have hU1 := hub B1 t
    have hU2 := hub B2 t
    have hR := hrb d t
    have hU10 : 0 ≤ (Real.sqrt (nI B1))⁻¹ * (Real.sqrt (nI B1))⁻¹ ^ ε *
        ∏ Q ∈ B1, (1 + (absNorm Q.1 : ℝ) ^ ε) :=
      mul_nonneg (by positivity) (eulS_bound_nonneg ε B1)
    have hR0 : 0 ≤ (if Squarefree (span {d}) then
        Real.sqrt (4 * M / (3 * nI T)) ^ ε * Real.sqrt (absNorm (span {d}) : ℝ) ^ ε else 0) := by
      split_ifs <;> positivity
    calc ‖rho3 ε M T t d‖ * (‖u3 ε T t B1‖ * ‖u3 ε T t B2‖ * (‖q2 B1 d‖ * ‖q2 B2 d‖))
        ≤ ‖rho3 ε M T t d‖ * (‖u3 ε T t B1‖ * ‖u3 ε T t B2‖ * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by positivity)) (norm_nonneg _)
      _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul hR (mul_le_mul hU1 hU2 (norm_nonneg _) hU10) (by positivity) hR0
  have hint : ∀ d, Integrable fun t => C t * Y d t := fun d =>
    integrable_mul_bdd hC (hYc d) (hYb d)
  -- each row as an integral
  have hD : nI (B1 ∪ B2) = nI B1 * nI B2 := nI_union h12
  have hcoef : 2 * M / (Real.sqrt 3 * Real.sqrt (nI (B1 ∪ B2)) * nI T) =
      2 * M / (Real.sqrt 3 * nI T) * (Real.sqrt (nI B1))⁻¹ * (Real.sqrt (nI B2))⁻¹ := by
    rw [hD, Real.sqrt_mul (nI_pos B1).le]
    have h1 := Real.sqrt_pos.2 (nI_pos B1)
    have h2 := Real.sqrt_pos.2 (nI_pos B2)
    have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    field_simp
  have hrow : ∀ d ∈ eltsLe K₁,
      (((2 * M / (Real.sqrt 3 * Real.sqrt (nI (B1 ∪ B2)) * nI T)) : ℝ) : ℂ) *
        q2 (B1 ∪ B2) (∏ P ∈ T, πP P) * (if Squarefree (span {d}) then
          q2 (B1 ∪ B2) d * ∑ T' ∈ (B1 ∪ B2).powerset, (-1 : ℂ) ^ T'.card *
            latErr dualR (Real.sqrt (4 * M / (3 * nI (B1 ∪ B2) * nI T) *
              (absNorm (span {d}) : ℝ)) * nI T')
          else 0) =
      (((2 * M / (Real.sqrt 3 * nI T)) : ℝ) : ℂ) * ∫ t, C t * Y d t := by
    intro d _
    by_cases hd : Squarefree (span {d})
    · have hN := absNorm_sqf_pos hd
      have hβ : 0 < Real.sqrt (4 * M / (3 * nI (B1 ∪ B2) * nI T) * (absNorm (span {d}) : ℝ)) :=
        Real.sqrt_pos.2 (by have := nI_pos (B1 ∪ B2); positivity)
      rw [ite_eq_left hd, hCrep _ hβ, ← integral_const_mul, ← integral_const_mul,
        ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hY]
      rw [rho3_of hd]
      unfold u3
      rw [hD, sqrt_kappa_split hM (nI_pos B1) (nI_pos B2) hTp,
        cpow_mul4 (Real.sqrt_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _))
          (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _),
        eulS_union h12, q2_union h12, q2_union h12, ← hD, hcoef]
      push_cast
      ring
    · rw [ite_eq_right hd]
      simp only [hY, rho3_of_not hd, zero_mul, mul_zero, integral_zero]
  unfold err3T
  rw [Finset.mul_sum, Finset.sum_congr rfl hrow, ← Finset.mul_sum,
    ← integral_finsetSum _ fun d _ => hint d]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [hY, Finset.mul_sum]

/-- **The bilinear bound for `Σ_3`'s error**: for every `ε > 0` there is `C₀` such that for
`0 < M`, `FBound (sqfW K₁) X Δ`, a family of column sets of norm at most `X` and any coefficients,
`|Σ_{B₁,B₂ disjoint} a(B₁)b(B₂)err₃(G, B₁ ∪ B₂)|
  ≤ 2^{|G|}·(2M/√3)·C₀·(4M/3)^{ε/2}K₁^{ε/2}·Δ·√(Σ_B 2^{|B|}N(B)⁻¹Π_B²|a(B)|²)·√(…b…)`. -/
theorem err3_bilin {ε : ℝ} (hε : 0 < ε) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (M K₁ X Δ : ℝ) (G : Finset Pr) (𝒩 : Finset (Finset Pr))
      (a b : Finset Pr → ℂ), 0 < M → 0 ≤ Δ → FBound (sqfW K₁) X Δ →
      (∀ B ∈ 𝒩, nI B ≤ X) →
      ‖∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, if Disjoint B1 B2 then a B1 * b B2 * err3 M K₁ G (B1 ∪ B2) else 0‖ ≤
        (2 : ℝ) ^ G.card * (2 * M / Real.sqrt 3) * C0 *
          ((Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) * Δ *
            (Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * (((Real.sqrt (nI B))⁻¹ *
                ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * ‖a B‖ ^ 2)) *
              Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * (((Real.sqrt (nI B))⁻¹ *
                ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * ‖b B‖ ^ 2)))) := by
  obtain ⟨C, hC, hCrep⟩ := latErr_moebius dualR hε
  refine ⟨∫ t, ‖C t‖, integral_nonneg fun t => norm_nonneg _,
    fun M K₁ X Δ G 𝒩 a b hM hΔ hF h𝒩 => ?_⟩
  have hCrep' : ∀ β : ℝ, 0 < β → ∀ S : Finset Pr,
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * latErr dualR (β * nI T) =
        ∫ t : ℝ, C t * ((β : ℂ) ^ sM ε t * eulS ε S t) := fun β hβ S => hCrep β hβ S
  set Λ : ℝ := Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set Bd : ℝ := (∫ t, ‖C t‖) * (Λ * Δ *
    (Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * (((Real.sqrt (nI B))⁻¹ *
        ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * ‖a B‖ ^ 2)) *
      Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * (((Real.sqrt (nI B))⁻¹ *
        ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * ‖b B‖ ^ 2)))) with hBd
  have hI : 0 ≤ ∫ t, ‖C t‖ := integral_nonneg fun t => norm_nonneg _
  have hBd0 : 0 ≤ Bd := by positivity
  -- one piece
  have hT : ∀ T ∈ G.powerset, ‖∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩,
      (if Disjoint B1 B2 then a B1 * b B2 * err3T M K₁ T (B1 ∪ B2) else 0)‖ ≤
      2 * M / Real.sqrt 3 * Bd := by
    intro T _
    have hTp := nI_pos T
    have hk : ∀ B1 ∈ 𝒩, ∀ B2 ∈ 𝒩, (if Disjoint B1 B2 then a B1 * b B2 *
        err3T M K₁ T (B1 ∪ B2) else 0) =
        (((2 * M / (Real.sqrt 3 * nI T)) : ℝ) : ℂ) * (if Disjoint B1 B2 then a B1 * b B2 *
          ∫ t, C t * ∑ d ∈ eltsLe K₁, rho3 ε M T t d *
            (u3 ε T t B1 * u3 ε T t B2 * (q2 B1 d * q2 B2 d)) else 0) := by
      intro B1 _ B2 _
      split_ifs with h12
      · rw [err3T_mellin hM hC hCrep' T h12]; ring
      · rw [mul_zero]
    rw [Finset.sum_congr rfl fun B1 hB1 => Finset.sum_congr rfl fun B2 hB2 => hk B1 hB1 B2 hB2]
    simp_rw [← Finset.mul_sum]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hb := mellin_bilin (w := fun m => Λ * sqfW K₁ m)
      (fun m => mul_nonneg hΛ0 (sqfW_nonneg _ _)) ((summable_sqfW K₁).mul_left Λ)
      (mul_nonneg hΛ0 hΔ) (hF.const_mul hΛ0) 𝒩 h𝒩 a b hC (eltsLe K₁)
      (fun t d => rho3 ε M T t d) (continuous_rho3 ε hM T)
      (fun t d hd => norm_rho3_le hε hM T t hd) (fun t B => u3 ε T t B) (continuous_u3 ε T)
      (fun B => (Real.sqrt (nI B))⁻¹ * ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε))
      (fun t B => norm_u3_le hε T t B)
    have hle : 2 * M / (Real.sqrt 3 * nI T) ≤ 2 * M / Real.sqrt 3 := by
      have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
      rw [div_le_div_iff₀ (by positivity) h3]
      have := one_le_nI T
      nlinarith [mul_nonneg (mul_nonneg hM.le h3.le) (sub_nonneg.2 this)]
    exact mul_le_mul hle (hb.trans (le_of_eq (by rw [hBd]))) (norm_nonneg _)
      (by positivity)
  -- the sum over `T`
  have hswap : (∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩,
      (if Disjoint B1 B2 then a B1 * b B2 * err3 M K₁ G (B1 ∪ B2) else 0)) =
      ∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩,
        (if Disjoint B1 B2 then a B1 * b B2 * err3T M K₁ T (B1 ∪ B2) else 0) := by
    unfold err3
    symm
    calc ∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩,
          (if Disjoint B1 B2 then a B1 * b B2 * err3T M K₁ T (B1 ∪ B2) else 0)
        = ∑ T ∈ G.powerset, ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, (-1 : ℂ) ^ T.card *
          (if Disjoint B1 B2 then a B1 * b B2 * err3T M K₁ T (B1 ∪ B2) else 0) := by
          simp_rw [Finset.mul_sum]
      _ = ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, ∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card *
          (if Disjoint B1 B2 then a B1 * b B2 * err3T M K₁ T (B1 ∪ B2) else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun B1 _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun B1 _ => Finset.sum_congr rfl fun B2 _ => ?_
          split_ifs
          · rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun T _ => by ring
          · simp
  rw [hswap]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum
    (g := fun _ => 2 * M / Real.sqrt 3 * Bd) fun T hT' => ?_).trans (le_of_eq ?_))
  · rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hT T hT'
  · rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, hBd]
    push_cast
    ring

end Eis

end

#print axioms Eis.integrable_mul_bdd
#print axioms Eis.mellin_bilin
#print axioms Eis.continuous_sM
#print axioms Eis.sM_re
#print axioms Eis.continuous_cpow_sM
#print axioms Eis.norm_cpow_sM
#print axioms Eis.continuous_eulS
#print axioms Eis.norm_eulS_le
#print axioms Eis.eulS_union
#print axioms Eis.eulS_bound_nonneg
#print axioms Eis.FBound.const_mul
#print axioms Eis.summable_sqfW
#print axioms Eis.rho4_of
#print axioms Eis.rho4_of_not
#print axioms Eis.absNorm_sqf_pos
#print axioms Eis.continuous_rho4
#print axioms Eis.norm_rho4_le
#print axioms Eis.err4_mellin
#print axioms Eis.err4_bilin
#print axioms Eis.rho3_of
#print axioms Eis.rho3_of_not
#print axioms Eis.continuous_rho3
#print axioms Eis.continuous_u3
#print axioms Eis.norm_rho3_le
#print axioms Eis.norm_u3_le
#print axioms Eis.sqrt_kappa_split
#print axioms Eis.cpow_mul4
#print axioms Eis.err3T_mellin
#print axioms Eis.err3_bilin
