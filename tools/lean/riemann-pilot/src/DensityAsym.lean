import Mathlib
import DensityCore

/-! # Zero density from detection (round 235)

With `X = ⌊U^{2σ−1}⌋` and `N = ⌊U^{3−2σ+2δ}⌋` (so `XN ≤ U^{2+2δ}`), `card_detect_le` gives
`≪ (log U)^{10}·(U^{1−(2σ−1)²} + U^{(2+2δ)(2−2σ)}) ≤ (log U)^{10} U^{4(1+δ)(1−σ)}` detected zeros
with `U ≤ |γ| ≤ 2U` (`window_count`). `DetectHyp δ` says every zero with `β ≥ σ ≥ ¾` in such a
window is detected, once `U ≥ U₀`. `density_of_detect`: `DetectHyp δ` gives `DensityXi (4(1+δ)) 11`
(dyadic windows above `U₀`; below `σ = ¾` the bound is trivial since then `T^{4(1−σ)} ≥ T`).
-/

open Real Finset

noncomputable section

namespace ShortWeil

open Pilot1ca Pilot1bt DirMean Kaiser

/-- `X = ⌊U^{2σ−1}⌋`. -/
def Xp (σ U : ℝ) : ℕ := ⌊U ^ (2 * σ - 1)⌋₊

/-- `N = ⌊U^{3−2σ+2δ}⌋`. -/
def Np (δ σ U : ℝ) : ℕ := ⌊U ^ (3 - 2 * σ + 2 * δ)⌋₊

/-- **Detection**: above `U₀`, every zero with `β ≥ σ ≥ ¾` and `U ≤ |γ| ≤ 2U` has `|D(ρ)| ≥ ½`. -/
def DetectHyp (δ : ℝ) : Prop :=
  ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ σ U : ℝ, 3 / 4 ≤ σ → σ ≤ 1 → U₀ ≤ U →
    ∀ i : ZeroIdx (sqF Xi), U ≤ |(tau i).re| → |(tau i).re| ≤ 2 * U → σ ≤ βs i →
      1 / 2 ≤ ‖DPval (Xp σ U) (Np δ σ U) (βs i) (γs i)‖

theorem half_le_log {U : ℝ} (hU : 2 ≤ U) : 1 / 2 ≤ Real.log U := by
  have h := Real.log_two_gt_d9
  have := Real.log_le_log (by norm_num) hU
  linarith

theorem natLog_le (N : ℕ) (hN : 1 ≤ N) : (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
  have h := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have hr : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast h
  have hl := Real.log_le_log (by positivity) hr
  rw [Real.log_pow] at hl
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  exact hl

/-- `Kloc(2U + 1) ≤ Kc·log U` for `U ≥ 2`. -/
def Kc : ℝ := 13 * (5 + kLam) + 10

theorem Kloc_le {U : ℝ} (hU : 2 ≤ U) : Kloc (2 * U + 1) ≤ Kc * Real.log U := by
  have hl := half_le_log hU
  have h3 : Real.log (2 * U + 1 + 2) ≤ 3 * Real.log U := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    have : U ^ (3 : ℝ) = U ^ 3 := by norm_cast
    have h4 : 4 ≤ U ^ 2 := by nlinarith
    rw [this]; nlinarith [mul_le_mul_of_nonneg_right h4 (by linarith : 0 ≤ U)]
  unfold Kloc Kc
  have hk := kLam_nonneg
  have h1 : 13 * (5 + kLam) * (1 / 2) ≤ 13 * (5 + kLam) * Real.log U :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  nlinarith

/-- The window constant. -/
def Cwin : ℝ := 800 * 125 * 7 ^ 6 * Kc * 3

/-- **One window**: `≤ Cwin (log U)^{10} U^{4(1+δ)(1−σ)}` detected zeros with `|γ| ≤ 2U`. -/
theorem window_count {δ σ U : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1)
    (hU : 2 ≤ U) (Z : Finset (ZeroIdx (sqF Xi)))
    (hZ : ∀ i ∈ Z, |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i
      ∧ 1 / 2 ≤ ‖DPval (Xp σ U) (Np δ σ U) (βs i) (γs i)‖) :
    (Z.card : ℝ) ≤ Cwin * Real.log U ^ 10 * U ^ (4 * (1 + δ) * (1 - σ)) := by
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hl := half_le_log hU
  set y1 := U ^ (2 * σ - 1) with hy1def
  set y2 := U ^ (3 - 2 * σ + 2 * δ) with hy2def
  set X := Xp σ U with hXdef
  set N := Np δ σ U with hNdef
  have hy1 : 1 ≤ y1 := Real.one_le_rpow hU1 (by linarith)
  have hy2 : 1 ≤ y2 := Real.one_le_rpow hU1 (by linarith)
  have hX1 : 1 ≤ X := (Nat.one_le_floor_iff _).2 hy1
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff _).2 hy2
  have hXle : (X : ℝ) ≤ y1 := Nat.floor_le (by linarith)
  have hXge : y1 / 2 ≤ X := by
    have h := Nat.lt_floor_add_one y1
    have : (1 : ℝ) ≤ X := by exact_mod_cast hX1
    change y1 < (X : ℝ) + 1 at h
    linarith
  have hNle : (N : ℝ) ≤ y2 := Nat.floor_le (by linarith)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hy12 : y1 * y2 = U ^ (2 + 2 * δ) := by
    rw [hy1def, hy2def, ← Real.rpow_add hU0]; congr 1; ring
  have hXN : (X : ℝ) * N ≤ U ^ (2 + 2 * δ) := by
    rw [← hy12]; exact mul_le_mul hXle hNle hN0.le (by linarith)
  have hmain := card_detect_le (by linarith : 1 / 2 ≤ σ) hσ1 hU hX1 hN1 Z hZ
  -- the factors
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hK : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 5 * Real.log U := by
    have h1 := natLog_le N hN1
    have h2 : Real.log N ≤ 2 * Real.log U := by
      calc Real.log N ≤ Real.log y2 := Real.log_le_log hN0 hNle
        _ = (3 - 2 * σ + 2 * δ) * Real.log U := Real.log_rpow hU0 _
        _ ≤ 2 * Real.log U := by nlinarith
    have h3 : Real.log N / Real.log 2 ≤ 3 * Real.log U := by
      rw [div_le_iff₀ (by linarith)]
      have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have hlU : 0 ≤ Real.log U := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hl2.le hlU]
    push_cast
    linarith
  have hL : 1 + Real.log (2 * X * N) ≤ 7 * Real.log U := by
    have h1 : Real.log (2 * X * N) ≤ Real.log 2 + (2 + 2 * δ) * Real.log U := by
      rw [mul_assoc, Real.log_mul (by norm_num) (by positivity), ← Real.log_rpow hU0]
      gcongr
    have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    nlinarith
  have hX1r : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hL0 : 0 ≤ 1 + Real.log (2 * X * N) := by
    have h := mul_le_mul hX1r hN1r zero_le_one (by linarith)
    have : (1 : ℝ) ≤ 2 * X * N := by nlinarith
    have := Real.log_nonneg this
    linarith
  have hKl := Kloc_le hU
  have hKl0 : 0 ≤ Kloc (2 * U + 1) := Kloc_nonneg (by linarith)
  set E := 4 * (1 + δ) * (1 - σ) with hE
  have hT1 : U * (X : ℝ) ^ (1 - 2 * σ) ≤ 2 * U ^ E := by
    have h1 : (X : ℝ) ^ (1 - 2 * σ) ≤ (y1 / 2) ^ (1 - 2 * σ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hXge (by linarith)
    have h2 : (y1 / 2) ^ (1 - 2 * σ) = y1 ^ (1 - 2 * σ) * 2 ^ (2 * σ - 1) := by
      rw [Real.div_rpow (by linarith) (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
      congr 2; ring
    have h3 : (2 : ℝ) ^ (2 * σ - 1) ≤ 2 := by
      calc (2 : ℝ) ^ (2 * σ - 1) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h4 : U * y1 ^ (1 - 2 * σ) = U ^ (4 * σ * (1 - σ)) := by
      rw [hy1def, ← Real.rpow_mul hU0.le]
      rw [show U * U ^ ((2 * σ - 1) * (1 - 2 * σ)) = U ^ (1 + (2 * σ - 1) * (1 - 2 * σ)) by
        rw [Real.rpow_add hU0, Real.rpow_one]]
      congr 1; ring
    have h5 : U ^ (4 * σ * (1 - σ)) ≤ U ^ E :=
      Real.rpow_le_rpow_of_exponent_le hU1 (by rw [hE]; nlinarith)
    have hy1p : 0 ≤ y1 ^ (1 - 2 * σ) := by positivity
    calc U * (X : ℝ) ^ (1 - 2 * σ) ≤ U * (y1 ^ (1 - 2 * σ) * 2 ^ (2 * σ - 1)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hU0.le
      _ ≤ U * (y1 ^ (1 - 2 * σ) * 2) := by gcongr
      _ = 2 * (U * y1 ^ (1 - 2 * σ)) := by ring
      _ = 2 * U ^ (4 * σ * (1 - σ)) := by rw [h4]
      _ ≤ 2 * U ^ E := by gcongr
  have hT2 : ((X : ℝ) * N) ^ (2 - 2 * σ) ≤ U ^ E := by
    calc ((X : ℝ) * N) ^ (2 - 2 * σ) ≤ (U ^ (2 + 2 * δ)) ^ (2 - 2 * σ) :=
          Real.rpow_le_rpow (by positivity) hXN (by linarith)
      _ = U ^ E := by rw [← Real.rpow_mul hU0.le, hE]; congr 1; ring
  have hsum : U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ) ≤ 3 * U ^ E := by linarith
  have hsum0 : 0 ≤ U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ) := by positivity
  have hlU : 0 ≤ Real.log U := by linarith
  refine hmain.trans ?_
  calc 800 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3 * (1 + Real.log (2 * X * N)) ^ 6 * Kloc (2 * U + 1)
        * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ))
      ≤ 800 * (5 * Real.log U) ^ 3 * (7 * Real.log U) ^ 6 * (Kc * Real.log U) * (3 * U ^ E) := by
        have hKc0 : 0 ≤ Kc := by unfold Kc; have := kLam_nonneg; positivity
        gcongr
    _ = Cwin * Real.log U ^ 10 * U ^ E := by unfold Cwin; ring

theorem Kc_nonneg : 0 ≤ Kc := by unfold Kc; have := kLam_nonneg; positivity

theorem log_le_pow11 {T : ℝ} (hT : 2 ≤ T) : Real.log T ≤ 2 ^ 10 * Real.log T ^ 11 := by
  have hl := half_le_log hT
  have h1 : 1 ≤ (2 * Real.log T) ^ 10 := one_le_pow₀ (by linarith)
  calc Real.log T = Real.log T * 1 := (mul_one _).symm
    _ ≤ Real.log T * (2 * Real.log T) ^ 10 := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = 2 ^ 10 * Real.log T ^ 11 := by ring

theorem one_le_pow11 {T : ℝ} (hT : 2 ≤ T) : 1 ≤ 2 ^ 11 * Real.log T ^ 11 := by
  have hl := half_le_log hT
  have h1 : 1 ≤ (2 * Real.log T) ^ 11 := one_le_pow₀ (by linarith)
  calc (1 : ℝ) ≤ (2 * Real.log T) ^ 11 := h1
    _ = 2 ^ 11 * Real.log T ^ 11 := by ring

/-- **Zero density from detection**: `N(σ, T) ≤ C T^{4(1+δ)(1−σ)}(log T)^{11}`. -/
theorem density_of_detect {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hD : DetectHyp δ) :
    DensityXi (4 * (1 + δ)) 11 := by
  classical
  obtain ⟨U₀, hU₀, hdet⟩ := hD
  set A := 4 * (1 + δ) with hA
  set C0 : ℝ := ((finite_re_le U₀).toFinset.card : ℝ) with hC0
  have hC00 : 0 ≤ C0 := Nat.cast_nonneg _
  set Ca : ℝ := 2 * Kc * 2 ^ 10 with hCa
  set Cb : ℝ := C0 * 2 ^ 11 + 4 * Cwin with hCb
  have hCw : 0 ≤ Cwin := by unfold Cwin; have := Kc_nonneg; positivity
  have hCa0 : 0 ≤ Ca := by have := Kc_nonneg; positivity
  refine ⟨max Ca Cb, le_max_of_le_left hCa0, fun T hT w hw0 hw1 => ?_⟩
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlT := half_le_log hT
  set e := A * (1 / 2 - w) with he
  have he0 : 0 ≤ e := by rw [he, hA]; nlinarith
  have hTe : 1 ≤ T ^ e := Real.one_le_rpow hT1 he0
  have hlog11 : 0 ≤ Real.log T ^ 11 := by positivity
  have e11 : Real.log T ^ (11 : ℝ) = Real.log T ^ (11 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
  rw [NX_eq_card, e11]
  set S := (finite_re_le T).toFinset.filter fun i => w ≤ |(tau i).im| with hS
  by_cases hw : w < 1 / 4
  · -- below `σ = ¾`: the trivial bound
    have h1 : (S.card : ℝ) ≤ (T + 1) * Kloc T :=
      (Nat.cast_le.2 (card_filter_le _ _)).trans (card_re_le hT0.le)
    have h2 : Kloc T ≤ Kc * Real.log T :=
      (Kloc_mono (by linarith) (by linarith : T ≤ 2 * T + 1)).trans (Kloc_le hT)
    have h3 : T ≤ T ^ e := by
      calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
        _ ≤ T ^ e := Real.rpow_le_rpow_of_exponent_le hT1 (by rw [he, hA]; nlinarith)
    have h4 := log_le_pow11 hT
    have hKc := Kc_nonneg
    calc (S.card : ℝ) ≤ (T + 1) * Kloc T := h1
      _ ≤ (2 * T) * (Kc * Real.log T) := by
          gcongr
          · exact Kloc_nonneg hT0.le
          · linarith
      _ ≤ (2 * T ^ e) * (Kc * (2 ^ 10 * Real.log T ^ 11)) := by gcongr
      _ = Ca * T ^ e * Real.log T ^ 11 := by rw [hCa]; ring
      _ ≤ max Ca Cb * T ^ e * Real.log T ^ 11 := by gcongr; exact le_max_left _ _
  · -- dyadic windows
    push Not at hw
    set σ := 1 / 2 + w with hσ
    have hσ34 : 3 / 4 ≤ σ := by rw [hσ]; linarith
    have hσ1 : σ ≤ 1 := by rw [hσ]; linarith
    have he' : e = A * (1 - σ) := by rw [he, hσ]; ring
    set mm : ZeroIdx (sqF Xi) → ℕ := fun i => ⌊|(tau i).re| / U₀⌋₊ with hmm
    set kk : ZeroIdx (sqF Xi) → ℕ := fun i => Nat.log 2 (mm i) with hkk
    set L := Nat.log 2 ⌊T / U₀⌋₊ + 1 with hL
    set Slow := S.filter fun i => |(tau i).re| ≤ U₀ with hSlow
    set Z : ℕ → Finset (ZeroIdx (sqF Xi)) := fun k => S.filter fun i => U₀ < |(tau i).re| ∧ kk i = k
      with hZ
    have hU₀0 : 0 < U₀ := by linarith
    have hcover : S ⊆ Slow ∪ (range L).biUnion Z := by
      intro i hi
      by_cases hlow : |(tau i).re| ≤ U₀
      · exact mem_union_left _ (mem_filter.2 ⟨hi, hlow⟩)
      · push Not at hlow
        refine mem_union_right _ (mem_biUnion.2 ⟨kk i, mem_range.2 ?_, mem_filter.2 ⟨hi, hlow, rfl⟩⟩)
        have hiT : |(tau i).re| ≤ T := by
          have := (mem_filter.1 hi).1; simpa using this
        have hmT : mm i ≤ ⌊T / U₀⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_right hiT hU₀0.le)
        exact Nat.lt_succ_of_le (Nat.log_mono_right hmT)
    have hlowc : (Slow.card : ℝ) ≤ C0 := by
      rw [hC0]
      exact_mod_cast card_le_card fun i hi => by
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]; exact (mem_filter.1 hi).2
    -- each window
    have hwin : ∀ k ∈ range L, ((Z k).card : ℝ) ≤ Cwin * Real.log T ^ 10 * T ^ e := by
      intro k _
      rcases (Z k).eq_empty_or_nonempty with hZe | ⟨i1, hi1⟩
      · rw [hZe, card_empty, Nat.cast_zero]; positivity
      set U := (2 : ℝ) ^ k * U₀ with hUdef
      have hUU₀ : U₀ ≤ U := by
        rw [hUdef]; exact le_mul_of_one_le_left hU₀0.le (one_le_pow₀ (by norm_num))
      have hU2 : 2 ≤ U := hU₀.trans hUU₀
      -- the window of an element
      have hwinU : ∀ i ∈ Z k, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U := by
        intro i hi
        obtain ⟨_, hlow, hk⟩ := mem_filter.1 hi
        have hm1 : 1 ≤ mm i := by
          simp only [hmm]; rw [Nat.one_le_floor_iff, le_div_iff₀ hU₀0]; linarith
        have hmne : mm i ≠ 0 := by omega
        have h1 := Nat.pow_log_le_self 2 hmne
        have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (mm i)
        simp only [hkk] at hk
        rw [hk] at h1 h2
        have hr1 : ((2 ^ k : ℕ) : ℝ) ≤ mm i := by exact_mod_cast h1
        have hr2 : (mm i : ℝ) + 1 ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h2
        have hf1 := Nat.floor_le (div_nonneg (abs_nonneg (tau i).re) hU₀0.le)
        have hf2 := Nat.lt_floor_add_one (|(tau i).re| / U₀)
        simp only [hmm] at hr1 hr2
        push_cast at hr1 hr2
        rw [pow_succ] at hr2
        constructor
        · rw [hUdef]; rw [le_div_iff₀ hU₀0] at hf1; nlinarith
        · rw [hUdef]; rw [div_lt_iff₀ hU₀0] at hf2; nlinarith
      have hc := window_count hδ0 hδ1 hσ34 hσ1 hU2 (Z k) fun i hi => by
        obtain ⟨hlo, hhi⟩ := hwinU i hi
        have hβ : σ ≤ βs i := by
          have := (mem_filter.1 (mem_filter.1 hi).1).2; unfold βs; rw [hσ]; linarith
        exact ⟨hhi, hβ, hdet σ U hσ34 hσ1 hUU₀ i hlo hhi hβ⟩
      have hUT : U ≤ T := by
        have := (hwinU i1 hi1).1
        have hiT : |(tau i1).re| ≤ T := by
          have := (mem_filter.1 (mem_filter.1 hi1).1).1; simpa using this
        linarith
      have hlU : Real.log U ≤ Real.log T := Real.log_le_log (by linarith) hUT
      have hlU0 : 0 ≤ Real.log U := by linarith [half_le_log hU2]
      calc ((Z k).card : ℝ) ≤ Cwin * Real.log U ^ 10 * U ^ (4 * (1 + δ) * (1 - σ)) := hc
        _ ≤ Cwin * Real.log T ^ 10 * T ^ e := by
            rw [he', hA]
            gcongr
    -- the number of windows
    have hLle : (L : ℝ) ≤ 4 * Real.log T := by
      have h1 : (Nat.log 2 ⌊T / U₀⌋₊ : ℝ) ≤ Real.log T / Real.log 2 := by
        rcases Nat.eq_zero_or_pos ⌊T / U₀⌋₊ with h0 | hpos
        · rw [h0, Nat.log_zero_right, Nat.cast_zero]
          exact div_nonneg (by linarith) (Real.log_nonneg (by norm_num))
        · refine (natLog_le _ hpos).trans ?_
          apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
          apply Real.log_le_log (by exact_mod_cast hpos)
          calc (⌊T / U₀⌋₊ : ℝ) ≤ T / U₀ := Nat.floor_le (by positivity)
            _ ≤ T := div_le_self hT0.le (by linarith)
      have h2 : Real.log T / Real.log 2 ≤ 3 / 2 * Real.log T := by
        rw [div_le_iff₀ (Real.log_pos (by norm_num))]
        have := Real.log_two_gt_d9
        nlinarith
      rw [hL]; push_cast; linarith
    have hsum : ((range L).biUnion Z).card ≤ ∑ k ∈ range L, (Z k).card := card_biUnion_le
    calc (S.card : ℝ) ≤ ((Slow ∪ (range L).biUnion Z).card : ℝ) := by exact_mod_cast card_le_card hcover
      _ ≤ Slow.card + ((range L).biUnion Z).card := by exact_mod_cast card_union_le _ _
      _ ≤ C0 + ∑ k ∈ range L, ((Z k).card : ℝ) := by
          gcongr
          exact_mod_cast hsum
      _ ≤ C0 + ∑ _k ∈ range L, Cwin * Real.log T ^ 10 * T ^ e := by gcongr with k hk; exact hwin k hk
      _ = C0 + L * (Cwin * Real.log T ^ 10 * T ^ e) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ C0 * (2 ^ 11 * Real.log T ^ 11 * T ^ e) + (4 * Real.log T) * (Cwin * Real.log T ^ 10 * T ^ e) := by
          gcongr
          · have := one_le_pow11 hT
            calc C0 = C0 * 1 * 1 := by ring
              _ ≤ C0 * (2 ^ 11 * Real.log T ^ 11) * T ^ e := by gcongr
              _ = C0 * (2 ^ 11 * Real.log T ^ 11 * T ^ e) := by ring
      _ = Cb * T ^ e * Real.log T ^ 11 := by rw [hCb]; ring
      _ ≤ max Ca Cb * T ^ e * Real.log T ^ 11 := by gcongr; exact le_max_right _ _

end ShortWeil

#print axioms ShortWeil.density_of_detect

#print axioms ShortWeil.window_count
