/-
# Round 518, part 2: Ingham's zero-density exponent `2 + 4c` from `|ζ(1/2 + it)| ≪ |t|^c`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. If `|ζ(1/2 + it)| ≤ C|t|^c` for `|t| ≥ 2` (`CrossCriteria.ZetaCritBound c`) with `0 < c ≤ 1`, then
`N(σ, T) ≤ C' T^{(2+4c)(1−σ)}(log T)^{12}` for `1/2 ≤ σ ≤ 1` and `T ≥ 2`: `ShortWeil.DensityXi (2 + 4c) 12`
(`densityXi_of_zetaCrit`). Hence:
* `inghamFromC`: `CrossCriteria.InghamFromC c` for every `c ≥ 0`;
* `densityXi_17_6`: with round 517's `c = 5/24 + ε`, `N(σ, T) ≪ T^{(17/6 + ε)(1−σ)}(log T)^{12}` for every `ε > 0`;
* `short_primes_11_17`: a prime in `(y, y + y^θ]` for every `θ > 11/17` and all large `y` (round 235's
  `DetectEM.short_primes` has `θ > 3/4`);
* `densityXi_Theta`, `short_primes_Theta`: at round 469's `Θ`, the exponent `1 + 2Θ + ε` and every
  `θ > 2Θ/(1 + 2Θ)`;
* `densityHypothesis_of_lindelof`: `CrossCriteria.Lindelof` implies `CrossCriteria.DensityHypothesis`.

The count in a window `U ≤ |γ| ≤ 2U` (`window_count_c`), with `X = ⌊U⌋`, `Y = U^{1+2c}` and
`N = ⌊22 Y log Y/X⌋ + 1`: by part 1's `trichotomy` every zero with `β ≥ σ` falls in one of three classes, and each
class is counted over the two parity classes of the unit windows of `|γ|` (`card_le_of_classes`, with
`ZeroLocal.card_local_le` for the multiplicity of a window).
* `|P₁|, |P₂| ≥ 1/4` (`class_count_b`): `DensityCore`'s chain with coefficients `|b_j| ≤ d(j)` (dyadic blocks,
  `DirMean.large_values_off'`, `DivSq.sum_card_divisors_sq_le`), at most
  `16K³·32e(1 + log 2XN)⁶(U X^{1−2σ} + (XN)^{2−2σ})` per parity class, `K = ⌊log₂ N⌋ + 1`.
* `|I| ≥ U/4` (`class3_count`): on the line, `|G(w)|(1 + |v|)³ ≤ A·|M_X(1/2 + i(γ + v))|` with
  `A = KG·C_Z(1 + 2U)^{1+c}Y^{1/2−σ}/δ` for `σ ≥ 1/2 + δ` (`Gfun_left_le`; `Zr_crit_bound` gives
  `|Z(1/2 + it)| ≤ C_Z(1 + |t|)^{1+c}` from `ZetaCritBound c`); summed over a parity class with
  `m ≤ λ/2 + m²/(2λ)` at `λ = U/(2A)`, and the mean value `Σ_r |M_X(1/2 + it_r)|² ≤ MV(X)(U + X + 1 + V)` over
  1-separated points (`mean_value_moll`, from `DirMean.large_values_off'` at `β = 1/2`), at most
  `4A²·MV(X)(U + X + 1)/U²` per parity class.
Both are at most `Cw (log U)^{11} U^{(2+4c)(1−σ)}` (`window_bound`). Dyadic windows above `U₀ = 8` and the trivial
bound below `σ = 1 − 1/(2 + 4c)` give `densityXi_of_zetaCrit`.
-/
import InghamDetect
import DensityAsym
import DetectCore
import ShortKV

open Complex Real Filter Topology MeasureTheory

noncomputable section

namespace InghamDensity

open ShortWeil PsiOmega Pilot1ca Pilot1bt DirMean Finset

/-! ### Windows and parity classes -/

/-- Representatives in windows `[n, n + 1)` with `n` two apart have 1-separated ordinates. -/
theorem sep_of_windows (C : Finset ℕ) (rep : ℕ → ZeroIdx (sqF Xi))
    (hC : ∀ n ∈ C, ∀ m ∈ C, n ≠ m → n + 2 ≤ m ∨ m + 2 ≤ n)
    (hwin : ∀ n ∈ C, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1) :
    ∀ n ∈ C, ∀ m ∈ C, n ≠ m → 1 ≤ |γs (rep n) - γs (rep m)| := by
  intro n hn m hm hnm
  have h1 := hwin n hn
  have h2 := hwin m hm
  have e1 : |γs (rep n)| = |(tau (rep n)).re| := abs_γs _
  have e2 : |γs (rep m)| = |(tau (rep m)).re| := abs_γs _
  refine le_trans ?_ (abs_abs_sub_abs_le_abs_sub (γs (rep n)) (γs (rep m)))
  rw [e1, e2]
  rcases hC n hn m hm hnm with h | h
  · have : ((n + 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast h
    push_cast at this
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · have : ((m + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast h
    push_cast at this
    rw [abs_of_nonneg (by linarith)]; linarith

/-- **Window reduction.** If every parity class of window representatives (of zeros with property `P`) has at
most `B` elements, then `|Z| ≤ 2B·Kloc(2U + 1)`. -/
theorem card_le_of_classes {U : ℝ} (hU : 0 ≤ U) (P : ZeroIdx (sqF Xi) → Prop)
    (Z : Finset (ZeroIdx (sqF Xi))) (hZ : ∀ i ∈ Z, |(tau i).re| ≤ 2 * U ∧ P i) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (C : Finset ℕ) (rep : ℕ → ZeroIdx (sqF Xi)),
      (∀ n ∈ C, ∀ m ∈ C, n ≠ m → n + 2 ≤ m ∨ m + 2 ≤ n) →
      (∀ n ∈ C, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1) →
      (∀ n ∈ C, |(tau (rep n)).re| ≤ 2 * U ∧ P (rep n)) → (C.card : ℝ) ≤ B) :
    (Z.card : ℝ) ≤ 2 * B * Kloc (2 * U + 1) := by
  classical
  have hKl : 0 ≤ Kloc (2 * U + 1) := Kloc_nonneg (by linarith)
  rcases Z.eq_empty_or_nonempty with hZe | ⟨i0, hi0⟩
  · rw [hZe, card_empty, Nat.cast_zero]; positivity
  have : Nonempty (ZeroIdx (sqF Xi)) := ⟨i0⟩
  set nn : ZeroIdx (sqF Xi) → ℕ := fun i => ⌊|(tau i).re|⌋₊ with hnn
  set NI := Z.image nn with hNI
  have hfib : ∀ n ∈ NI, ((Z.filter fun i => nn i = n).card : ℝ) ≤ Kloc (2 * U + 1) := by
    intro n hn
    obtain ⟨i1, hi1, rfl⟩ := mem_image.1 hn
    have hn0 : (0 : ℝ) ≤ nn i1 := Nat.cast_nonneg _
    have hnU : (nn i1 : ℝ) ≤ 2 * U + 1 :=
      (Nat.floor_le (abs_nonneg _)).trans (by linarith [(hZ i1 hi1).1])
    refine (card_local_le hn0 _ fun i hi => ?_).trans (Kloc_mono hn0 hnU)
    obtain ⟨_, hik⟩ := mem_filter.1 hi
    have h1 := Nat.floor_le (abs_nonneg (tau i).re)
    have h2 := Nat.lt_floor_add_one |(tau i).re|
    simp only [hnn] at hik
    rw [hik] at h1 h2
    rw [abs_le]; constructor <;> linarith
  have hZN : (Z.card : ℝ) ≤ NI.card * Kloc (2 * U + 1) := by
    rw [card_eq_sum_card_image nn Z]
    push_cast
    calc ∑ n ∈ NI, ((Z.filter fun i => nn i = n).card : ℝ) ≤ ∑ _n ∈ NI, Kloc (2 * U + 1) :=
          sum_le_sum hfib
      _ = NI.card * Kloc (2 * U + 1) := by rw [sum_const, nsmul_eq_mul]
  have hrep : ∀ n ∈ NI, ∃ i ∈ Z, nn i = n := fun n hn => by
    obtain ⟨i, hi, h⟩ := mem_image.1 hn; exact ⟨i, hi, h⟩
  choose! rep hrepZ hrepn using hrep
  have hwin : ∀ n ∈ NI, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1 := by
    intro n hn
    have h := hrepn n hn
    have h1 := Nat.floor_le (abs_nonneg (tau (rep n)).re)
    have h2 := Nat.lt_floor_add_one |(tau (rep n)).re|
    simp only [hnn] at h
    rw [h] at h1 h2
    exact ⟨h1, h2⟩
  have hclass : ∀ p : ℕ, ((NI.filter fun n => n % 2 = p).card : ℝ) ≤ B := by
    intro p
    exact hB _ rep
      (fun n hn m hm hnm => by
        have := (mem_filter.1 hn).2; have := (mem_filter.1 hm).2; omega)
      (fun n hn => hwin n (mem_filter.1 hn).1) (fun n hn => hZ _ (hrepZ n (mem_filter.1 hn).1))
  have hsplit : (NI.card : ℝ) ≤ (NI.filter fun n => n % 2 = 0).card + (NI.filter fun n => n % 2 = 1).card := by
    have h := card_filter_add_card_filter_not (s := NI) (fun n => n % 2 = 0)
    have e : NI.filter (fun n => ¬ n % 2 = 0) = NI.filter (fun n => n % 2 = 1) :=
      filter_congr fun n _ => by omega
    rw [e] at h
    exact_mod_cast h.symm.le
  calc (Z.card : ℝ) ≤ NI.card * Kloc (2 * U + 1) := hZN
    _ ≤ (B + B) * Kloc (2 * U + 1) := by
        gcongr; exact hsplit.trans (add_le_add (hclass 0) (hclass 1))
    _ = 2 * B * Kloc (2 * U + 1) := by ring

/-- A parity class of windows below `2U` has at most `2U + 1` elements. -/
theorem card_class_le {U : ℝ} (hU : 0 ≤ U) (C : Finset ℕ) (rep : ℕ → ZeroIdx (sqF Xi))
    (hwin : ∀ n ∈ C, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1)
    (hU2 : ∀ n ∈ C, |(tau (rep n)).re| ≤ 2 * U) : (C.card : ℝ) ≤ 2 * U + 1 := by
  have hsub : C ⊆ range (⌊2 * U⌋₊ + 1) := by
    intro n hn
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.le_floor ((hwin n hn).1.trans (hU2 n hn))
  have := card_le_card hsub
  rw [card_range] at this
  have h2 : ((⌊2 * U⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * U + 1 := by
    push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * U)]
  exact (Nat.cast_le.2 this).trans h2

/-! ### Large values of `Σ b_j j^{−ρ}` with `|b_j| ≤ d(j)` (DensityCore's chain, general coefficients) -/

/-- The coefficient mass of a block. -/
theorem block_mass_le_b (b : ℕ → ℂ) (hb : ∀ j, ‖b j‖ ≤ (j.divisors.card : ℝ)) {P : ℕ} (hP : 1 ≤ P)
    {S : Finset ℕ} (hS : S ⊆ Ioc P (2 * P)) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑ j ∈ S, ‖b j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2
      ≤ 2 * (P : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * P)) ^ 3 := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have h1 : ∀ j ∈ S, ‖b j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2
      ≤ ((j.divisors.card : ℕ) : ℝ) ^ 2 * ((P : ℝ) ^ (-σ)) ^ 2 := by
    intro j hj
    obtain ⟨hj1, _⟩ := mem_Ioc.1 (hS hj)
    have hPj : (P : ℝ) ≤ j := by exact_mod_cast hj1.le
    have hjs : (j : ℝ) ^ (-σ) ≤ (P : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos hP0 hPj (by linarith)
    gcongr
    exact hb j
  have h2 : ∑ j ∈ S, ((j.divisors.card : ℕ) : ℝ) ^ 2 ≤ ∑ j ∈ Ioc 0 (2 * P), ((j.divisors.card : ℕ) : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (fun j hj => by
      obtain ⟨h1, h2⟩ := mem_Ioc.1 (hS hj); exact mem_Ioc.2 ⟨by omega, h2⟩) fun _ _ _ => by positivity
  have h3 := DivSq.sum_card_divisors_sq_le (2 * P)
  push_cast at h3
  have hpow : ((P : ℝ) ^ (-σ)) ^ 2 * (2 * P) = 2 * (P : ℝ) ^ (1 - 2 * σ) := by
    rw [show (1 : ℝ) - 2 * σ = 1 + (-σ * 2) by ring, Real.rpow_add hP0, Real.rpow_one,
      ← Real.rpow_natCast ((P : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hP0.le]
    push_cast; ring
  calc ∑ j ∈ S, ‖b j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2
      ≤ ∑ j ∈ S, ((j.divisors.card : ℕ) : ℝ) ^ 2 * ((P : ℝ) ^ (-σ)) ^ 2 := sum_le_sum h1
    _ = (∑ j ∈ S, ((j.divisors.card : ℕ) : ℝ) ^ 2) * ((P : ℝ) ^ (-σ)) ^ 2 := by rw [sum_mul]
    _ ≤ (2 * P * (1 + Real.log (2 * P)) ^ 3) * ((P : ℝ) ^ (-σ)) ^ 2 := by gcongr; exact h2.trans h3
    _ = 2 * (P : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * P)) ^ 3 := by rw [← hpow]; ring

/-- The `k`-th dyadic block of `Pv b`. -/
def Fkb (b : ℕ → ℂ) (X N k : ℕ) (β γ : ℝ) : ℂ :=
  dp ((Ioc X (X * N)).filter (fun j => blk X j = k)) (fun j => b j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) γ

theorem Pv_eq_blocks (b : ℕ → ℂ) (X N : ℕ) (hX : 1 ≤ X) (β γ : ℝ) :
    Pv b X N β γ = ∑ k ∈ range (Nat.log 2 N + 1), Fkb b X N k β γ := by
  unfold Pv Fkb
  exact dp_blocks X N hX _ γ

/-- **One block**: `c₀²·#{large values} ≤ 32e(1 + log 2XN)⁶(U X^{1−2σ} + (XN)^{2−2σ})`. -/
theorem block_count_b (b : ℕ → ℂ) (hb : ∀ j, ‖b j‖ ≤ (j.divisors.card : ℝ)) {σ U : ℝ} (hσ : 1 / 2 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : 2 ≤ U) {X N k : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hk : k < Nat.log 2 N + 1)
    {ι : Type*} (Rs : Finset ι) (x β : ι → ℝ)
    (hsep : ∀ r ∈ Rs, ∀ s ∈ Rs, r ≠ s → 1 ≤ |x r - x s|) (hx : ∀ r ∈ Rs, |x r| ≤ 2 * U)
    (hβ : ∀ r ∈ Rs, σ ≤ β r ∧ β r ≤ σ + 1 / 2) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hbig : ∀ r ∈ Rs, c₀ ≤ ‖Fkb b X N k (β r) (x r)‖) :
    (Rs.card : ℝ) * c₀ ^ 2 ≤ 32 * Real.exp 1 * (1 + Real.log (2 * X * N)) ^ 6
      * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) := by
  set P := 2 ^ k * X with hPdef
  have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hPN : P ≤ X * N := by
    rw [hPdef, mul_comm X N]; exact Nat.mul_le_mul_right X (pow_blk_le hk hN)
  have hXP : X ≤ P := by rw [hPdef]; exact Nat.le_mul_of_pos_left X (by positivity)
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hPNr : (P : ℝ) ≤ X * N := by exact_mod_cast hPN
  have hXPr : (X : ℝ) ≤ P := by exact_mod_cast hXP
  set ℓ := Real.log (2 * X * N) with hℓ
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by nlinarith [mul_le_mul hXr hNr zero_le_one (by linarith)])
  have hlP : Real.log P ≤ ℓ := Real.log_le_log hP0 (by nlinarith)
  have hl2P : Real.log (2 * P) ≤ ℓ := Real.log_le_log (by positivity) (by nlinarith)
  have hlP0 : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast hP)
  have hl2P0 : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by nlinarith [(by exact_mod_cast hP : (1 : ℝ) ≤ P)])
  have hLV := large_values_off' hP (block_sub (N := N) (k := k) hX) b (σ := σ)
    (lo := -2 * U - 1) (hi := 2 * U + 1) (by linarith) Rs x β hsep
    (fun r hr => by have := abs_le.1 (hx r hr); constructor <;> linarith) hβ
  have hmass := block_mass_le_b b hb hP (block_sub (N := N) (k := k) hX) (by linarith : 0 ≤ σ)
  have hlow : (Rs.card : ℝ) * c₀ ^ 2 ≤ ∑ r ∈ Rs, ‖Fkb b X N k (β r) (x r)‖ ^ 2 := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun r hr => pow_le_pow_left₀ hc₀.le (hbig r hr) 2
  have hL : (2 * U + 1 - (-2 * U - 1) + 8 * P * (1 + Real.log P)) ≤ 8 * (U + P) * (1 + ℓ) := by
    nlinarith
  have hL2 : 2 + Real.log (2 * P) ^ 2 ≤ 2 * (1 + ℓ) ^ 2 := by nlinarith
  have hsplit : (P : ℝ) ^ (1 - 2 * σ) * (U + P) ≤ U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ) := by
    have h1 : (P : ℝ) ^ (1 - 2 * σ) ≤ (X : ℝ) ^ (1 - 2 * σ) :=
      Real.rpow_le_rpow_of_nonpos hX0 hXPr (by linarith)
    have h2 : (P : ℝ) ^ (1 - 2 * σ) * P = (P : ℝ) ^ (2 - 2 * σ) := by
      rw [show (2 : ℝ) - 2 * σ = (1 - 2 * σ) + 1 by ring, Real.rpow_add hP0, Real.rpow_one]
    have h3 : (P : ℝ) ^ (2 - 2 * σ) ≤ ((X : ℝ) * N) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow hP0.le hPNr (by linarith)
    have hU0 : 0 ≤ U := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hU0]
  have hmass0 : 0 ≤ ∑ j ∈ (Ioc X (X * N)).filter (fun j => blk X j = k),
      ‖b j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2 := sum_nonneg fun _ _ => by positivity
  have hPs : 0 ≤ (P : ℝ) ^ (1 - 2 * σ) := by positivity
  calc (Rs.card : ℝ) * c₀ ^ 2 ≤ ∑ r ∈ Rs, ‖Fkb b X N k (β r) (x r)‖ ^ 2 := hlow
    _ ≤ Real.exp 1 * ((2 * U + 1 - (-2 * U - 1) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2))
          * ∑ j ∈ (Ioc X (X * N)).filter (fun j => blk X j = k),
              ‖b j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2 := hLV
    _ ≤ Real.exp 1 * ((8 * (U + P) * (1 + ℓ)) * (2 * (1 + ℓ) ^ 2))
          * (2 * (P : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * P)) ^ 3) := by
        gcongr
    _ ≤ Real.exp 1 * ((8 * (U + P) * (1 + ℓ)) * (2 * (1 + ℓ) ^ 2))
          * (2 * (P : ℝ) ^ (1 - 2 * σ) * (1 + ℓ) ^ 3) := by gcongr
    _ = 32 * Real.exp 1 * (1 + ℓ) ^ 6 * ((P : ℝ) ^ (1 - 2 * σ) * (U + P)) := by ring
    _ ≤ 32 * Real.exp 1 * (1 + ℓ) ^ 6 * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) := by
        gcongr

/-- **One parity class** with `|Pv b(ρ)| ≥ c₁`: `|C| ≤ K³/c₁² · 32e(1 + log 2XN)⁶(U X^{1−2σ} + (XN)^{2−2σ})`. -/
theorem class_count_b (b : ℕ → ℂ) (hb : ∀ j, ‖b j‖ ≤ (j.divisors.card : ℝ)) {σ U : ℝ} (hσ : 1 / 2 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : 2 ≤ U) {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (C : Finset ℕ) (rep : ℕ → ZeroIdx (sqF Xi))
    (hC : ∀ n ∈ C, ∀ m ∈ C, n ≠ m → n + 2 ≤ m ∨ m + 2 ≤ n)
    (hwin : ∀ n ∈ C, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1)
    (hdet : ∀ n ∈ C, |(tau (rep n)).re| ≤ 2 * U ∧ (σ ≤ βs (rep n)
      ∧ c₁ ≤ ‖Pv b X N (βs (rep n)) (γs (rep n))‖)) :
    (C.card : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3 / c₁ ^ 2 * (32 * Real.exp 1
      * (1 + Real.log (2 * X * N)) ^ 6 * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ))) := by
  classical
  set K := Nat.log 2 N + 1 with hK
  set B := 32 * Real.exp 1 * (1 + Real.log (2 * X * N)) ^ 6
      * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) with hB
  have hK0 : (0 : ℝ) < K := by positivity
  set xs : ℕ → ℝ := fun n => γs (rep n)
  set bs : ℕ → ℝ := fun n => βs (rep n)
  have hsep := sep_of_windows C rep hC hwin
  have hx : ∀ n ∈ C, |xs n| ≤ 2 * U := fun n hn => by
    simp only [xs]; rw [abs_γs]; exact (hdet n hn).1
  have hβ : ∀ n ∈ C, σ ≤ bs n ∧ bs n ≤ σ + 1 / 2 := fun n hn =>
    ⟨(hdet n hn).2.1, by have := βs_lt_one (rep n); simp only [bs]; linarith⟩
  have hlarge : ∀ n ∈ C, ∃ k ∈ range K, c₁ / K ≤ ‖Fkb b X N k (bs n) (xs n)‖ := by
    intro n hn
    by_contra hcon
    push Not at hcon
    have h1 := (hdet n hn).2.2
    rw [Pv_eq_blocks b X N hX] at h1
    have h2 : ∑ k ∈ range K, ‖Fkb b X N k (bs n) (xs n)‖ < ∑ _k ∈ range K, c₁ / (K : ℝ) :=
      sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ fun k hk => hcon k hk
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    have h3 : (K : ℝ) * (c₁ / K) = c₁ := by field_simp
    linarith [(norm_sum_le (range K) fun k => Fkb b X N k (bs n) (xs n)).trans_lt (h3 ▸ h2)]
  set Ck : ℕ → Finset ℕ := fun k => C.filter fun n => c₁ / (K : ℝ) ≤ ‖Fkb b X N k (bs n) (xs n)‖
  have hsub : C ⊆ (range K).biUnion Ck := by
    intro n hn
    obtain ⟨k, hk, hbig⟩ := hlarge n hn
    exact mem_biUnion.2 ⟨k, hk, mem_filter.2 ⟨hn, hbig⟩⟩
  have hCk : ∀ k ∈ range K, ((Ck k).card : ℝ) ≤ (K : ℝ) ^ 2 / c₁ ^ 2 * B := by
    intro k hk
    have hc0 : (0 : ℝ) < c₁ / K := by positivity
    have h := block_count_b b hb hσ hσ1 hU hX hN (mem_range.1 hk) (Ck k) xs bs
      (fun n hn m hm hnm => hsep n (mem_filter.1 hn).1 m (mem_filter.1 hm).1 hnm)
      (fun n hn => hx n (mem_filter.1 hn).1) (fun n hn => hβ n (mem_filter.1 hn).1) hc0
      (fun n hn => (mem_filter.1 hn).2)
    rw [div_pow, ← le_div_iff₀ (by positivity)] at h
    calc ((Ck k).card : ℝ) ≤ B / (c₁ ^ 2 / (K : ℝ) ^ 2) := h
      _ = (K : ℝ) ^ 2 / c₁ ^ 2 * B := by field_simp
  calc (C.card : ℝ) ≤ ((range K).biUnion Ck).card := by exact_mod_cast card_le_card hsub
    _ ≤ ∑ k ∈ range K, ((Ck k).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _k ∈ range K, (K : ℝ) ^ 2 / c₁ ^ 2 * B := sum_le_sum hCk
    _ = (K : ℝ) ^ 3 / c₁ ^ 2 * B := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-! ### The integral piece: `|ζ(½ + it)| ≪ |t|^c` and the mean value of `M_X` on the line -/

/-- `ZetaCritBound c` gives `|Z(½ + it)| ≤ C_Z (1 + |t|)^{1+c}` for every `t`, with `C_Z ≥ 1`. -/
theorem Zr_crit_bound {c : ℝ} (hc : 0 ≤ c) (h : CrossCriteria.ZetaCritBound c) :
    ∃ CZ : ℝ, 1 ≤ CZ ∧ ∀ t : ℝ, ‖Zr (1 / 2 + t * I)‖ ≤ CZ * (1 + |t|) ^ (1 + c) := by
  obtain ⟨C, hC⟩ := h
  have hcont : Continuous fun t : ℝ => Zr (1 / 2 + t * I) :=
    differentiable_Zr.continuous.comp (by fun_prop)
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max (max C₀ C) 1, le_max_right _ _, fun t => ?_⟩
  have h1 : 1 ≤ (1 + |t|) ^ (1 + c) := Real.one_le_rpow (by linarith [abs_nonneg t]) (by linarith)
  have hM0 : 0 ≤ max (max C₀ C) 1 := le_max_of_le_right zero_le_one
  rcases lt_or_ge |t| 2 with ht | ht
  · have hmem : t ∈ Set.Icc (-2 : ℝ) 2 := by
      obtain ⟨h1, h2⟩ := abs_lt.1 ht; exact ⟨h1.le, h2.le⟩
    calc ‖Zr (1 / 2 + t * I)‖ ≤ C₀ := hC₀ t hmem
      _ ≤ max (max C₀ C) 1 := le_max_of_le_left (le_max_left _ _)
      _ ≤ max (max C₀ C) 1 * (1 + |t|) ^ (1 + c) := le_mul_of_one_le_right hM0 h1
  · have hs1 : (1 / 2 + t * I : ℂ) ≠ 1 := fun h => by
      have := congrArg Complex.re h; norm_num at this
    rw [Zr_of_ne hs1, norm_mul]
    have hz := hC t ht
    have ht0 : 0 < |t| := by linarith
    have hC0 : 0 ≤ C := by
      have hp : 0 < |t| ^ c := Real.rpow_pos_of_pos ht0 c
      by_contra hneg
      push Not at hneg
      have : C * |t| ^ c < 0 := mul_neg_of_neg_of_pos hneg hp
      linarith [norm_nonneg (riemannZeta (1 / 2 + t * I))]
    have hsub : ‖(1 / 2 + t * I : ℂ) - 1‖ ≤ 1 + |t| := by
      calc ‖(1 / 2 + t * I : ℂ) - 1‖ ≤ |((1 / 2 + t * I : ℂ) - 1).re| + |((1 / 2 + t * I : ℂ) - 1).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = 1 / 2 + |t| := by norm_num [abs_of_neg]
        _ ≤ 1 + |t| := by linarith
    have htc : |t| ^ c ≤ (1 + |t|) ^ c := Real.rpow_le_rpow (abs_nonneg t) (by linarith) hc
    calc ‖(1 / 2 + t * I : ℂ) - 1‖ * ‖riemannZeta (1 / 2 + t * I)‖
        ≤ (1 + |t|) * (C * (1 + |t|) ^ c) :=
          mul_le_mul hsub (hz.trans (mul_le_mul_of_nonneg_left htc hC0)) (norm_nonneg _) (by positivity)
      _ = C * (1 + |t|) ^ (1 + c) := by
          rw [Real.rpow_add (by positivity), Real.rpow_one]; ring
      _ ≤ max (max C₀ C) 1 * (1 + |t|) ^ (1 + c) := by
          gcongr; exact le_max_of_le_left (le_max_right _ _)

/-- The weight `(1 + |v|)^{−3}`. -/
def wt (v : ℝ) : ℝ := ((1 + |v|) ^ 3)⁻¹

theorem wt_pos (v : ℝ) : 0 < wt v := by unfold wt; positivity

theorem continuous_wt : Continuous wt := by
  unfold wt
  exact (by fun_prop : Continuous fun v : ℝ => (1 + |v|) ^ 3).inv₀ fun v => by positivity

theorem wt_mul_le (v : ℝ) : wt v * (1 + |v|) ≤ (1 + v ^ 2)⁻¹ := by
  unfold wt
  have h1 : 0 < 1 + |v| := by positivity
  have h2 : 1 + v ^ 2 ≤ (1 + |v|) ^ 2 := by nlinarith [abs_nonneg v, sq_abs v]
  rw [inv_mul_eq_div, div_le_iff₀ (by positivity), mul_comm, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  calc (1 + |v|) * (1 + v ^ 2) ≤ (1 + |v|) * (1 + |v|) ^ 2 := by gcongr
    _ = (1 + |v|) ^ 3 := by ring

theorem wt_le (v : ℝ) : wt v ≤ (1 + v ^ 2)⁻¹ :=
  le_trans (le_mul_of_one_le_right (wt_pos v).le (by linarith [abs_nonneg v])) (wt_mul_le v)

/-- A continuous real `f` with `|f| ≤ K(1 + v²)⁻¹` is integrable. -/
theorem integrable_real_of_le {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ}
    (hK : ∀ v, |f v| ≤ K * (1 + v ^ 2)⁻¹) : Integrable f :=
  Integrable.mono' (integrable_inv_one_add_sq.const_mul K) hf.aestronglyMeasurable
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hK v)

/-- The point `½ + it`. -/
theorem continuous_moll_line (X : ℕ) (γ : ℝ) :
    Continuous fun v : ℝ => ‖moll X (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ :=
  ((differentiable_moll X).continuous.comp (by fun_prop)).norm

/-- **On the line `Re w = ½ − β`**: `|G(w)|(1 + |v|)³ ≤ A·|M_X(½ + i(γ + v))|` with
`A = KG C_Z (1 + 2U)^{1+c} Y^{½−σ}/δ`, for a zero `ρ = β + iγ`, `σ ≤ β < 1`, `½ + δ ≤ σ`, `|γ| ≤ 2U`. -/
theorem Gfun_left_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {CZ : ℝ} (hCZ0 : 0 ≤ CZ)
    (hCZ : ∀ t : ℝ, ‖Zr (1 / 2 + t * I)‖ ≤ CZ * (1 + |t|) ^ (1 + c)) (X : ℕ)
    {σ δ U Y β γ : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hσβ : σ ≤ β) (hβ1 : β < 1) (hU : 0 ≤ U)
    (hγ : |γ| ≤ 2 * U) (hY : 1 ≤ Y) (hz : Zr ((β : ℂ) + γ * I) = 0) (v : ℝ) :
    ‖Gfun X Y ((β : ℂ) + γ * I) (((1 / 2 - ((β : ℂ) + γ * I).re : ℝ) : ℂ) + v * I)‖ * (1 + |v|) ^ 3
      ≤ KG * CZ * (1 + 2 * U) ^ (1 + c) * Y ^ (1 / 2 - σ) / δ
        * ‖moll X (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ := by
  have hre : ((β : ℂ) + γ * I).re = β := by simp
  rw [hre]
  set w : ℂ := ((1 / 2 - β : ℝ) : ℂ) + v * I with hw
  have hwre : w.re = 1 / 2 - β := by simp [hw]
  have hwim : w.im = v := by simp [hw]
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwre; simp at hwre; linarith
  have hsum : (β : ℂ) + γ * I + w = 1 / 2 + ((γ + v : ℝ) : ℂ) * I := by
    rw [hw]; push_cast; ring
  rw [Gfun_eq_left X Y hz hw0, hsum, norm_mul, norm_mul, norm_mul, norm_div]
  -- the four factors
  have hZ : ‖Zr (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ ≤ CZ * (1 + 2 * U) ^ (1 + c) * (1 + |v|) ^ 2 := by
    refine (hCZ (γ + v)).trans ?_
    have hb : 1 + |γ + v| ≤ (1 + 2 * U) * (1 + |v|) := by
      have := abs_add_le γ v
      nlinarith [abs_nonneg γ, abs_nonneg v]
    have hp : (1 + |γ + v|) ^ (1 + c) ≤ ((1 + 2 * U) * (1 + |v|)) ^ (1 + c) :=
      Real.rpow_le_rpow (by positivity) hb (by linarith)
    rw [Real.mul_rpow (by positivity) (by positivity)] at hp
    have hv2 : (1 + |v|) ^ (1 + c) ≤ (1 + |v|) ^ 2 := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) (by push_cast; linarith)
    calc CZ * (1 + |γ + v|) ^ (1 + c) ≤ CZ * ((1 + 2 * U) ^ (1 + c) * (1 + |v|) ^ (1 + c)) := by gcongr
      _ ≤ CZ * ((1 + 2 * U) ^ (1 + c) * (1 + |v|) ^ 2) := by gcongr
      _ = CZ * (1 + 2 * U) ^ (1 + c) * (1 + |v|) ^ 2 := by ring
  have hG := norm_Gamma_le' (z := w + 1) (by simp [hwre]; linarith) (by simp [hwre]; linarith)
  have hGim : (w + 1).im = v := by simp [hwim]
  rw [hGim] at hG
  have hwn : δ ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    rw [hwre, abs_of_neg (by linarith)] at this
    linarith
  have hYw : ‖(Y : ℂ) ^ w‖ ≤ Y ^ (1 / 2 - σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), hwre]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  have hwpos : 0 < ‖w‖ := by linarith
  set m := ‖moll X (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ with hm
  set g := ‖Complex.Gamma (w + 1)‖ with hg
  have hm0 : 0 ≤ m := norm_nonneg _
  have hg0 : 0 ≤ g := norm_nonneg _
  have hdiv : g / ‖w‖ ≤ g / δ := div_le_div_of_nonneg_left hg0 hδ hwn
  calc m * ‖Zr (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ * (g / ‖w‖) * ‖(Y : ℂ) ^ w‖ * (1 + |v|) ^ 3
      ≤ m * (CZ * (1 + 2 * U) ^ (1 + c) * (1 + |v|) ^ 2) * (g / δ) * Y ^ (1 / 2 - σ) * (1 + |v|) ^ 3 := by
        gcongr
    _ = CZ * (1 + 2 * U) ^ (1 + c) * Y ^ (1 / 2 - σ) / δ * m * (g * (1 + |v|) ^ 5) := by ring
    _ ≤ CZ * (1 + 2 * U) ^ (1 + c) * Y ^ (1 / 2 - σ) / δ * m * KG := by gcongr
    _ = KG * CZ * (1 + 2 * U) ^ (1 + c) * Y ^ (1 / 2 - σ) / δ * m := by ring

/-- The `k`-th dyadic block of `M_X(½ + it) − 1`. -/
def Fm (X k : ℕ) (t : ℝ) : ℂ :=
  dp ((Ioc 1 (1 * X)).filter (fun j => blk 1 j = k))
    (fun j => ((ArithmeticFunction.moebius j : ℤ) : ℂ) * (((j : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) t

theorem moll_half_eq {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    moll X (1 / 2 + (t : ℂ) * I) = 1 + ∑ k ∈ range (Nat.log 2 X + 1), Fm X k t := by
  have hsplit : Ioc 0 X = insert 1 (Ioc 1 X) := by
    ext m; simp only [mem_Ioc, mem_insert]; omega
  unfold moll
  rw [hsplit, sum_insert (by simp)]
  have h1 : ((ArithmeticFunction.moebius 1 : ℤ) : ℂ) * ((1 : ℕ) : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)) = 1 := by
    simp
  rw [h1]
  congr 1
  have hdp : ∑ m ∈ Ioc 1 X, ((ArithmeticFunction.moebius m : ℤ) : ℂ) * (m : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))
      = dp (Ioc 1 (1 * X))
          (fun j => ((ArithmeticFunction.moebius j : ℤ) : ℂ) * (((j : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) t := by
    rw [one_mul]
    unfold dp
    refine sum_congr rfl fun m hm => ?_
    have hm0 : 0 < m := by have := (mem_Ioc.1 hm).1; omega
    have e : (1 / 2 + (t : ℂ) * I) = (((1 / 2 : ℝ) : ℂ) + t * I) := by push_cast; ring
    rw [e, natCast_cpow_neg m hm0 (1 / 2) t]
    ring
  rw [hdp, dp_blocks 1 X le_rfl]
  rfl

theorem norm_moll_half_sq_le {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    ‖moll X (1 / 2 + (t : ℂ) * I)‖ ^ 2
      ≤ 2 + 2 * ((Nat.log 2 X + 1 : ℕ) : ℝ) * ∑ k ∈ range (Nat.log 2 X + 1), ‖Fm X k t‖ ^ 2 := by
  rw [moll_half_eq hX]
  set K := Nat.log 2 X + 1 with hK
  set S := ∑ k ∈ range K, ‖Fm X k t‖ with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => norm_nonneg _
  have h1 : ‖(1 : ℂ) + ∑ k ∈ range K, Fm X k t‖ ≤ 1 + S :=
    (norm_add_le _ _).trans (by rw [norm_one]; gcongr; exact norm_sum_le _ _)
  have h2 : S ^ 2 ≤ K * ∑ k ∈ range K, ‖Fm X k t‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range K) (f := fun k => ‖Fm X k t‖)
    simpa [hS] using this
  calc ‖(1 : ℂ) + ∑ k ∈ range K, Fm X k t‖ ^ 2 ≤ (1 + S) ^ 2 := by gcongr
    _ ≤ 2 + 2 * S ^ 2 := by nlinarith [sq_nonneg (S - 1)]
    _ ≤ 2 + 2 * (K * ∑ k ∈ range K, ‖Fm X k t‖ ^ 2) := by gcongr
    _ = 2 + 2 * (K : ℝ) * ∑ k ∈ range K, ‖Fm X k t‖ ^ 2 := by ring

/-- The mean-value constant. -/
def MV (X : ℕ) : ℝ :=
  4 + 16 * Real.exp 1 * ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 2 * (1 + Real.log X) * (2 + Real.log (2 * X) ^ 2)

/-- **The mean value of `M_X` on the critical line** over 1-separated points `|t_r| ≤ 2U + V`, at most `2U + 1`
of them: `Σ_r |M_X(½ + it_r)|² ≤ MV(X)(U + X + 1 + V)`. -/
theorem mean_value_moll {X : ℕ} (hX : 1 ≤ X) {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) {ι : Type*}
    (R : Finset ι) (t : ι → ℝ) (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |t r - t s|)
    (ht : ∀ r ∈ R, |t r| ≤ 2 * U + V) (hR : (R.card : ℝ) ≤ 2 * U + 1) :
    ∑ r ∈ R, ‖moll X (1 / 2 + (t r : ℂ) * I)‖ ^ 2 ≤ MV X * (U + X + 1 + V) := by
  set K := Nat.log 2 X + 1 with hK
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hl2X : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  set E := Real.exp 1 * ((4 * U + 2 * V + 2 + 8 * X * (1 + Real.log X)) * (2 + Real.log (2 * X) ^ 2)) with hE
  have hblock : ∀ k ∈ range K, ∑ r ∈ R, ‖Fm X k (t r)‖ ^ 2 ≤ E := by
    intro k hk
    have hk' := mem_range.1 hk
    have hP : 1 ≤ 2 ^ k * 1 := by rw [mul_one]; exact Nat.one_le_two_pow
    have hPX : 2 ^ k ≤ X := pow_blk_le hk' hX
    have hLV := large_values_off' hP (block_sub (X := 1) (N := X) (k := k) le_rfl)
      (fun j => ((ArithmeticFunction.moebius j : ℤ) : ℂ)) (σ := 1 / 2)
      (lo := -(2 * U + V + 1)) (hi := 2 * U + V + 1) (by linarith) R t (fun _ => 1 / 2) hsep
      (fun r hr => by have := abs_le.1 (ht r hr); constructor <;> linarith) (fun r hr => by norm_num)
    set S := (Ioc 1 (1 * X)).filter (fun j => blk 1 j = k) with hSdef
    have hSsub : S ⊆ Ioc (2 ^ k * 1) (2 * (2 ^ k * 1)) := block_sub le_rfl
    set P : ℕ := 2 ^ k * 1 with hPdef
    have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
    have hPXr : (P : ℝ) ≤ X := by rw [hPdef, mul_one]; exact_mod_cast hPX
    -- the coefficient mass is at most 1
    have hmass : ∑ j ∈ S, ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ 1 := by
      have hterm : ∀ j ∈ S, ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2
          ≤ 1 / P := by
        intro j hj
        obtain ⟨hj1, _⟩ := mem_Ioc.1 (hSsub hj)
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
        have hPj : (P : ℝ) ≤ j := by exact_mod_cast hj1.le
        have hμ : ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2 ≤ 1 := by
          rw [Complex.norm_intCast]
          have : |((ArithmeticFunction.moebius j : ℤ) : ℝ)| ≤ 1 := by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          nlinarith [abs_nonneg ((ArithmeticFunction.moebius j : ℤ) : ℝ)]
        have hj2 : ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / j := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hj0.le]
          norm_num
          rw [Real.rpow_neg_one]
        rw [hj2]
        calc ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2 * (1 / (j : ℝ)) ≤ 1 * (1 / P) := by
              gcongr
          _ = 1 / P := one_mul _
      have hcard : (S.card : ℝ) ≤ P := by
        have := card_le_card hSsub
        rw [Nat.card_Ioc] at this
        have e : 2 * P - P = P := by omega
        rw [e] at this
        exact_mod_cast this
      calc ∑ j ∈ S, ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2
          ≤ ∑ _j ∈ S, 1 / (P : ℝ) := sum_le_sum hterm
        _ = S.card * (1 / P) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ P * (1 / P) := by gcongr
        _ = 1 := by field_simp
    have hlP : Real.log P ≤ Real.log X := Real.log_le_log hP0 hPXr
    have hlP0 : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast hP)
    have hl2P : Real.log (2 * P) ≤ Real.log (2 * X) := Real.log_le_log (by positivity) (by linarith)
    have hl2P0 : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ P := by exact_mod_cast hP
      linarith)
    have hF : ∀ r, Fm X k (t r) = dp S (fun j => ((ArithmeticFunction.moebius j : ℤ) : ℂ)
        * (((j : ℝ) ^ (-(fun _ : ι => (1 / 2 : ℝ)) r) : ℝ) : ℂ)) (t r) := fun r => rfl
    simp_rw [hF]
    refine hLV.trans ?_
    have hmass0 : 0 ≤ ∑ j ∈ S, ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2
        * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := sum_nonneg fun _ _ => by positivity
    calc Real.exp 1 * ((2 * U + V + 1 - -(2 * U + V + 1) + 8 * P * (1 + Real.log P))
          * (2 + Real.log (2 * P) ^ 2)) * ∑ j ∈ S, ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2
            * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2
        ≤ Real.exp 1 * ((4 * U + 2 * V + 2 + 8 * X * (1 + Real.log X)) * (2 + Real.log (2 * X) ^ 2)) * 1 := by
          gcongr
          · linarith
    _ = E := by rw [hE, mul_one]
  -- sum over the points
  have hpt := fun r => norm_moll_half_sq_le hX (t r)
  calc ∑ r ∈ R, ‖moll X (1 / 2 + (t r : ℂ) * I)‖ ^ 2
      ≤ ∑ r ∈ R, (2 + 2 * (K : ℝ) * ∑ k ∈ range K, ‖Fm X k (t r)‖ ^ 2) := sum_le_sum fun r _ => hpt r
    _ = 2 * R.card + 2 * (K : ℝ) * ∑ k ∈ range K, ∑ r ∈ R, ‖Fm X k (t r)‖ ^ 2 := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, sum_comm]; ring
    _ ≤ 2 * (2 * U + 1) + 2 * (K : ℝ) * ∑ _k ∈ range K, E := by
        gcongr with k hk
        · exact hblock k hk
    _ = 2 * (2 * U + 1) + 2 * (K : ℝ) ^ 2 * E := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ MV X * (U + X + 1 + V) := by
        unfold MV
        rw [hE]
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
        have hb : 4 * U + 2 * V + 2 + 8 * X * (1 + Real.log X) ≤ 8 * (1 + Real.log X) * (U + X + 1 + V) := by
          nlinarith
        have hL0 : 0 ≤ 2 + Real.log (2 * X) ^ 2 := by positivity
        have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
        have h3 : 2 * (K : ℝ) ^ 2 * (Real.exp 1 * ((4 * U + 2 * V + 2 + 8 * X * (1 + Real.log X))
            * (2 + Real.log (2 * X) ^ 2)))
            ≤ 2 * (K : ℝ) ^ 2 * (Real.exp 1 * ((8 * (1 + Real.log X) * (U + X + 1 + V))
            * (2 + Real.log (2 * X) ^ 2))) := by gcongr
        nlinarith

/-- **The integral class.** For a parity class of window representatives whose zeros `ρ` have `σ ≤ β` and
`|I(ρ)| ≥ U/4`: `|C| ≤ 4A² MV(X)(U + X + 1)/U²` with `A = KG C_Z (1 + 2U)^{1+c} Y^{½−σ}/δ`. The steps: the bound
on the line for each zero; the sum over the class; `m ≤ λ/2 + m²/(2λ)` at `λ = U/(2A)`; the mean value of `M_X`. -/
theorem class3_count {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {CZ : ℝ} (hCZ1 : 1 ≤ CZ)
    (hCZ : ∀ t : ℝ, ‖Zr (1 / 2 + t * I)‖ ≤ CZ * (1 + |t|) ^ (1 + c)) {X : ℕ} (hX : 1 ≤ X)
    {σ δ U Y : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hU : 2 ≤ U) (hY : 1 ≤ Y)
    (C : Finset ℕ) (rep : ℕ → ZeroIdx (sqF Xi))
    (hC : ∀ n ∈ C, ∀ m ∈ C, n ≠ m → n + 2 ≤ m ∨ m + 2 ≤ n)
    (hwin : ∀ n ∈ C, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1)
    (hdet : ∀ n ∈ C, |(tau (rep n)).re| ≤ 2 * U ∧
      (σ ≤ βs (rep n) ∧ U / 4 ≤ ‖Iv X Y ((βs (rep n) : ℂ) + γs (rep n) * I)‖)) :
    (C.card : ℝ) ≤ 4 * (KG * CZ * (1 + 2 * U) ^ (1 + c) * Y ^ (1 / 2 - σ) / δ) ^ 2 * MV X
      * (U + X + 1) / U ^ 2 := by
  classical
  set A := KG * CZ * (1 + 2 * U) ^ (1 + c) * Y ^ (1 / 2 - σ) / δ with hA
  have hA0 : 0 < A := by have := KG_pos; have : (0 : ℝ) < CZ := by linarith
                         positivity
  have hU0 : 0 < U := by linarith
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  set m : ℕ → ℝ → ℝ := fun n v => ‖moll X (1 / 2 + ((γs (rep n) + v : ℝ) : ℂ) * I)‖ with hm
  have hmc : ∀ n, Continuous (m n) := fun n => continuous_moll_line X (γs (rep n))
  have hmX : ∀ n v, m n v ≤ X := fun n v => norm_moll_le_X X (by simp)
  have hm0 : ∀ n v, 0 ≤ m n v := fun n v => norm_nonneg _
  have hint : ∀ n, Integrable fun v => m n v * wt v := by
    intro n
    refine integrable_real_of_le ((hmc n).mul continuous_wt) (K := X) fun v => ?_
    rw [abs_of_nonneg (mul_nonneg (hm0 n v) (wt_pos v).le)]
    exact mul_le_mul (hmX n v) (wt_le v) (wt_pos v).le (by positivity)
  -- (i) each zero
  have hIv : ∀ n ∈ C, U / 4 ≤ A / (2 * π) * ∫ v, m n v * wt v := by
    intro n hn
    obtain ⟨hre, hσβ, hI⟩ := hdet n hn
    have hβ1 : βs (rep n) < 1 := βs_lt_one (rep n)
    have hγ : |γs (rep n)| ≤ 2 * U := by rw [abs_γs]; exact hre
    have hρ1 : ((βs (rep n) : ℂ) + γs (rep n) * I) ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hz : Zr ((βs (rep n) : ℂ) + γs (rep n) * I) = 0 :=
      Zr_zero_of_zeta (DetectCore.zeta_βsγs (rep n)) hρ1
    refine hI.trans ?_
    unfold Iv
    rw [norm_mul]
    have hc2 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hc2]
    have hle : ‖∫ v : ℝ, Gfun X Y ((βs (rep n) : ℂ) + γs (rep n) * I)
        (((1 / 2 - ((βs (rep n) : ℂ) + γs (rep n) * I).re : ℝ) : ℂ) + v * I)‖
        ≤ ∫ v, A * (m n v * wt v) := by
      refine norm_integral_le_of_norm_le ((hint n).const_mul A) (Eventually.of_forall fun v => ?_)
      have h := Gfun_left_le hc0 hc1 (by linarith) hCZ X hδ hσδ hσβ hβ1 hU0.le hγ hY hz v
      have hp : 0 < (1 + |v|) ^ 3 := by positivity
      change _ ≤ A * (‖moll X (1 / 2 + ((γs (rep n) + v : ℝ) : ℂ) * I)‖ * ((1 + |v|) ^ 3)⁻¹)
      rw [← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ hp]
      exact h
    rw [integral_const_mul] at hle
    calc 1 / (2 * π) * ‖∫ v : ℝ, Gfun X Y ((βs (rep n) : ℂ) + γs (rep n) * I)
          (((1 / 2 - ((βs (rep n) : ℂ) + γs (rep n) * I).re : ℝ) : ℂ) + v * I)‖
        ≤ 1 / (2 * π) * (A * ∫ v, m n v * wt v) := by gcongr
      _ = A / (2 * π) * ∫ v, m n v * wt v := by ring
  -- (ii) the sum over the class
  have hsum1 : (C.card : ℝ) * (U / 4) ≤ A / (2 * π) * ∫ v, ∑ n ∈ C, m n v * wt v := by
    rw [integral_finsetSum C fun n _ => hint n, mul_sum, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hIv
  -- (iii) pointwise: `m ≤ λ/2 + m²/(2λ)` at `λ = U/(2A)`, and the mean value
  have hR := card_class_le hU0.le C rep hwin fun n hn => (hdet n hn).1
  have hsep := sep_of_windows C rep hC hwin
  set K' := (C.card : ℝ) * U / (4 * A) + A / U * MV X * (U + X + 1) with hK'
  have hpt : ∀ v : ℝ, ∑ n ∈ C, m n v * wt v ≤ K' * (1 + v ^ 2)⁻¹ := by
    intro v
    have hamgm : ∀ n, m n v ≤ U / (4 * A) + A / U * m n v ^ 2 := by
      intro n
      have h := sq_nonneg (m n v - U / (2 * A))
      have e : U / (4 * A) + A / U * m n v ^ 2 - m n v = A / U * (m n v - U / (2 * A)) ^ 2 := by
        field_simp; ring
      have : 0 ≤ A / U * (m n v - U / (2 * A)) ^ 2 := by positivity
      linarith
    have hmv := mean_value_moll hX hU0.le (abs_nonneg v) C (fun n => γs (rep n) + v)
      (fun n hn k hk hnk => by
        have := hsep n hn k hk hnk
        rwa [show γs (rep n) + v - (γs (rep k) + v) = γs (rep n) - γs (rep k) by ring])
      (fun n hn => by
        have h1 := abs_add_le (γs (rep n)) v
        have h2 : |γs (rep n)| ≤ 2 * U := by rw [abs_γs]; exact (hdet n hn).1
        linarith) hR
    have hsumm : ∑ n ∈ C, m n v ≤ C.card * (U / (4 * A)) + A / U * (MV X * (U + X + 1 + |v|)) := by
      calc ∑ n ∈ C, m n v ≤ ∑ n ∈ C, (U / (4 * A) + A / U * m n v ^ 2) := sum_le_sum fun n _ => hamgm n
        _ = C.card * (U / (4 * A)) + A / U * ∑ n ∈ C, m n v ^ 2 := by
            rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
        _ ≤ C.card * (U / (4 * A)) + A / U * (MV X * (U + X + 1 + |v|)) := by
            gcongr
    have hMV0 : 0 ≤ MV X := by unfold MV; have := Real.log_nonneg hXr; positivity
    have hw1 := wt_le v
    have hw2 := wt_mul_le v
    have hwp := (wt_pos v).le
    have hb : U + X + 1 + |v| ≤ (U + X + 1) * (1 + |v|) := by nlinarith [abs_nonneg v]
    calc ∑ n ∈ C, m n v * wt v = wt v * ∑ n ∈ C, m n v := by rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
      _ ≤ wt v * (C.card * (U / (4 * A)) + A / U * (MV X * (U + X + 1 + |v|))) := by gcongr
      _ = C.card * (U / (4 * A)) * wt v + A / U * MV X * (wt v * (U + X + 1 + |v|)) := by ring
      _ ≤ C.card * (U / (4 * A)) * (1 + v ^ 2)⁻¹ + A / U * MV X * ((U + X + 1) * (1 + v ^ 2)⁻¹) := by
          have hq : wt v * (U + X + 1 + |v|) ≤ (U + X + 1) * (1 + v ^ 2)⁻¹ := by
            calc wt v * (U + X + 1 + |v|) ≤ wt v * ((U + X + 1) * (1 + |v|)) := by gcongr
              _ = (U + X + 1) * (wt v * (1 + |v|)) := by ring
              _ ≤ (U + X + 1) * (1 + v ^ 2)⁻¹ := by gcongr
          have hcoef : 0 ≤ A / U * MV X := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left hw1 (by positivity))
            (mul_le_mul_of_nonneg_left hq hcoef)
      _ = K' * (1 + v ^ 2)⁻¹ := by rw [hK']; ring
  -- (iv) integrate
  have hint_sum : Integrable fun v => ∑ n ∈ C, m n v * wt v := integrable_finsetSum C fun n _ => hint n
  have hI2 : ∫ v, ∑ n ∈ C, m n v * wt v ≤ K' * π := by
    calc ∫ v, ∑ n ∈ C, m n v * wt v ≤ ∫ v, K' * (1 + v ^ 2)⁻¹ :=
          integral_mono hint_sum (integrable_inv_one_add_sq.const_mul K') hpt
      _ = K' * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hpi : 0 < π := Real.pi_pos
  have hfin : (C.card : ℝ) * (U / 4) ≤ A / 2 * K' := by
    calc (C.card : ℝ) * (U / 4) ≤ A / (2 * π) * ∫ v, ∑ n ∈ C, m n v * wt v := hsum1
      _ ≤ A / (2 * π) * (K' * π) := by gcongr
      _ = A / 2 * K' := by field_simp
  rw [hK'] at hfin
  have hU2 : 0 < U ^ 2 := by positivity
  rw [le_div_iff₀ hU2]
  have e : A / 2 * ((C.card : ℝ) * U / (4 * A) + A / U * MV X * (U + X + 1))
      = (C.card : ℝ) * U / 8 + A ^ 2 * MV X * (U + X + 1) / (2 * U) := by
    field_simp; ring
  rw [e] at hfin
  have h8 : (C.card : ℝ) * U / 8 ≤ A ^ 2 * MV X * (U + X + 1) / (2 * U) := by linarith
  rw [div_le_div_iff₀ (by norm_num) (by positivity)] at h8
  nlinarith

/-! ### One window -/

/-- **The three classes in one window.** Every zero with `U ≤ |γ| ≤ 2U` and `β ≥ σ ≥ ½ + δ` falls in one of
the three classes of `trichotomy`; each class is counted by `card_le_of_classes`, with `class_count_b` (twice)
and `class3_count`. -/
theorem window_classes {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {CZ : ℝ} (hCZ1 : 1 ≤ CZ)
    (hCZ : ∀ t : ℝ, ‖Zr (1 / 2 + t * I)‖ ≤ CZ * (1 + |t|) ^ (1 + c))
    {σ δ U Y : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hσ1 : σ ≤ 1) (hU : 2 ≤ U) (hY : 8 ≤ Y) (hUY : U ≤ Y)
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ))
    (Z : Finset (ZeroIdx (sqF Xi)))
    (hZ : ∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) :
    (Z.card : ℝ) ≤ 2 * Kloc (2 * U + 1) * (2 * (((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * X * N)) ^ 6
        * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ))))
      + 4 * (KG * CZ * (1 + 2 * U) ^ (1 + c) * Y ^ (1 / 2 - σ) / δ) ^ 2 * MV X * (U + X + 1) / U ^ 2) := by
  classical
  have hU0 : 0 ≤ U := by linarith
  have hY0 : 0 < Y := by linarith
  set B1 := ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2 * (32 * Real.exp 1
      * (1 + Real.log (2 * X * N)) ^ 6 * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ))) with hB1
  set B3 := 4 * (KG * CZ * (1 + 2 * U) ^ (1 + c) * Y ^ (1 / 2 - σ) / δ) ^ 2 * MV X * (U + X + 1) / U ^ 2
    with hB3
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB10 : 0 ≤ B1 := by
    have : 0 ≤ 1 + Real.log (2 * X * N) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * X * N by nlinarith)
      linarith
    positivity
  have hB30 : 0 ≤ B3 := by
    have : 0 ≤ MV X := by unfold MV; have := Real.log_nonneg hXr; positivity
    positivity
  -- the trichotomy for each zero
  have htri : ∀ i ∈ Z, 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖ ∨ 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖
      ∨ U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖ := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hZ i hi
    exact trichotomy hX hN hY hU hUY hM (by linarith) (βs_lt_one i) (by rw [abs_γs]; exact h1)
      (by rw [abs_γs]; exact h2) (DetectCore.zeta_βsγs i)
  set Z1 := Z.filter fun i => 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖
  set Z2 := Z.filter fun i => 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖
  set Z3 := Z.filter fun i => U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖
  have hcover : Z ⊆ Z1 ∪ Z2 ∪ Z3 := by
    intro i hi
    rcases htri i hi with h | h | h
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_right _ (mem_filter.2 ⟨hi, h⟩)
  have hb1 : ∀ j, ‖b1 X Y j‖ ≤ (j.divisors.card : ℝ) := norm_b1_le X hY0
  have hb2 : ∀ j, ‖b2 X Y j‖ ≤ (j.divisors.card : ℝ) := norm_b2_le X hY0
  have hσ2 : 1 / 2 ≤ σ := by linarith
  have hc1' : 1 ≤ 2 * U + 1 := by linarith
  have hZ1 : (Z1.card : ℝ) ≤ 2 * B1 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖) Z1
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB10 fun C rep hC hwin hdet =>
        class_count_b (b1 X Y) hb1 hσ2 hσ1 hU hX hN (by norm_num) C rep hC hwin hdet
  have hZ2 : (Z2.card : ℝ) ≤ 2 * B1 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖) Z2
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB10 fun C rep hC hwin hdet =>
        class_count_b (b2 X Y) hb2 hσ2 hσ1 hU hX hN (by norm_num) C rep hC hwin hdet
  have hZ3 : (Z3.card : ℝ) ≤ 2 * B3 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖) Z3
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB30 fun C rep hC hwin hdet =>
        class3_count hc0 hc1 hCZ1 hCZ hX hδ hσδ hU (by linarith) C rep hC hwin hdet
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2 ∪ Z3).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card + Z3.card := by
        have h1 := card_union_le (Z1 ∪ Z2) Z3
        have h2 := card_union_le Z1 Z2
        exact_mod_cast h1.trans (by omega)
    _ ≤ 2 * B1 * Kloc (2 * U + 1) + 2 * B1 * Kloc (2 * U + 1) + 2 * B3 * Kloc (2 * U + 1) := by
        linarith
    _ = 2 * Kloc (2 * U + 1) * (2 * B1 + B3) := by ring

/-! ### The parameters `X = ⌊U⌋`, `Y = U^{1+2c}`, `XN ≈ 22 Y log Y` -/

def Xw (U : ℝ) : ℕ := ⌊U⌋₊

def Yw (c U : ℝ) : ℝ := U ^ (1 + 2 * c)

def Nw (c U : ℝ) : ℕ := ⌊22 * Yw c U * Real.log (Yw c U) / (Xw U : ℝ)⌋₊ + 1

theorem log_ge_two {U : ℝ} (hU : 8 ≤ U) : 2 ≤ Real.log U := by
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  have := Real.log_le_log (by norm_num) hU
  linarith

theorem Xw_one {U : ℝ} (hU : 8 ≤ U) : 1 ≤ Xw U := (Nat.one_le_floor_iff _).2 (by linarith)

theorem Xw_le {U : ℝ} (hU : 8 ≤ U) : (Xw U : ℝ) ≤ U := Nat.floor_le (by linarith)

theorem Xw_half {U : ℝ} (hU : 8 ≤ U) : U / 2 ≤ Xw U := by
  have h := Nat.lt_floor_add_one U
  have : (1 : ℝ) ≤ Xw U := by exact_mod_cast Xw_one hU
  change U < (Xw U : ℝ) + 1 at h
  linarith

theorem Yw_ge {c U : ℝ} (hc0 : 0 ≤ c) (hU : 8 ≤ U) : U ≤ Yw c U := by
  unfold Yw
  calc U = U ^ (1 : ℝ) := (Real.rpow_one U).symm
    _ ≤ U ^ (1 + 2 * c) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem log_Yw {c U : ℝ} (hU : 8 ≤ U) : Real.log (Yw c U) = (1 + 2 * c) * Real.log U := by
  unfold Yw; rw [Real.log_rpow (by linarith)]

theorem log_Yw_ge_one {c U : ℝ} (hc0 : 0 ≤ c) (hU : 8 ≤ U) : 1 ≤ Real.log (Yw c U) := by
  have := log_ge_two hU
  have := Real.log_le_log (by linarith) (Yw_ge hc0 hU)
  linarith

theorem XN_ge {c U : ℝ} (hU : 8 ≤ U) :
    22 * Yw c U * Real.log (Yw c U) ≤ ((Xw U * Nw c U : ℕ) : ℝ) := by
  have hX : (0 : ℝ) < Xw U := by exact_mod_cast Xw_one hU
  set q := 22 * Yw c U * Real.log (Yw c U) / (Xw U : ℝ) with hq
  have h := Nat.lt_floor_add_one q
  have e : 22 * Yw c U * Real.log (Yw c U) = Xw U * q := by rw [hq]; field_simp
  rw [e]
  unfold Nw
  rw [← hq]
  push_cast
  gcongr

theorem XN_le {c U : ℝ} (hc0 : 0 ≤ c) (hU : 8 ≤ U) :
    ((Xw U * Nw c U : ℕ) : ℝ) ≤ 23 * Yw c U * Real.log (Yw c U) := by
  have hX : (0 : ℝ) < Xw U := by exact_mod_cast Xw_one hU
  have hY := Yw_ge hc0 hU
  have hlY := log_Yw_ge_one hc0 hU
  set q := 22 * Yw c U * Real.log (Yw c U) / (Xw U : ℝ) with hq
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) hX.le
  have h := Nat.floor_le hq0
  have hXU := Xw_le hU
  unfold Nw
  rw [← hq]
  push_cast
  calc (Xw U : ℝ) * (⌊q⌋₊ + 1) ≤ Xw U * (q + 1) := by gcongr
    _ = 22 * Yw c U * Real.log (Yw c U) + Xw U := by rw [hq]; field_simp
    _ ≤ 22 * Yw c U * Real.log (Yw c U) + Yw c U * Real.log (Yw c U) := by
        gcongr; nlinarith
    _ = 23 * Yw c U * Real.log (Yw c U) := by ring

theorem Nw_one {c U : ℝ} : 1 ≤ Nw c U := by unfold Nw; omega

theorem Yw_le {c U : ℝ} (hc1 : c ≤ 1) (hU : 8 ≤ U) : Yw c U ≤ U ^ 3 := by
  unfold Yw
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)

/-! ### The window bound -/

/-- `Nat.log₂ N + 1 ≤ 13 log U`. -/
theorem bound_K {c U : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hU : 8 ≤ U) :
    ((Nat.log 2 (Nw c U) + 1 : ℕ) : ℝ) ≤ 13 * Real.log U := by
  have hL := log_ge_two hU
  have hU0 : 0 < U := by linarith
  have hN1 : 1 ≤ Nw c U := Nw_one
  have hX1 : (1 : ℝ) ≤ Xw U := by exact_mod_cast Xw_one hU
  have hY := Yw_ge hc0 hU
  have hY3 := Yw_le hc1 hU
  have hlY : Real.log (Yw c U) ≤ Yw c U := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hNle : (Nw c U : ℝ) ≤ U ^ 8 := by
    have h1 : (Nw c U : ℝ) ≤ ((Xw U * Nw c U : ℕ) : ℝ) := by
      push_cast; nlinarith [(by exact_mod_cast hN1 : (1 : ℝ) ≤ Nw c U)]
    have h2 := XN_le hc0 hU
    have h3 : 23 * Yw c U * Real.log (Yw c U) ≤ 23 * (U ^ 3) * U ^ 3 := by
      have hlY0 := log_Yw_ge_one hc0 hU
      gcongr
      linarith
    have h4 : 23 * (U ^ 3) * U ^ 3 ≤ U ^ 8 := by
      have : (23 : ℝ) ≤ U ^ 2 := by nlinarith
      calc 23 * U ^ 3 * U ^ 3 ≤ U ^ 2 * U ^ 3 * U ^ 3 := by gcongr
        _ = U ^ 8 := by ring
    linarith
  have hlN : Real.log (Nw c U) ≤ 8 * Real.log U := by
    have := Real.log_le_log (by exact_mod_cast (show 0 < Nw c U by omega)) hNle
    rwa [Real.log_pow] at this
  have h1 := natLog_le (Nw c U) hN1
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h2 : Real.log (Nw c U) / Real.log 2 ≤ 12 * Real.log U := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  push_cast
  linarith

/-- `1 + log(2XN) ≤ 9 log U`. -/
theorem bound_ell {c U : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hU : 8 ≤ U) :
    1 + Real.log (2 * (Xw U : ℝ) * (Nw c U)) ≤ 9 * Real.log U := by
  have hL := log_ge_two hU
  have hY := Yw_ge hc0 hU
  have hY3 := Yw_le hc1 hU
  have hlY : Real.log (Yw c U) ≤ Yw c U := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hX1 : (1 : ℝ) ≤ Xw U := by exact_mod_cast Xw_one hU
  have hN1 : (1 : ℝ) ≤ Nw c U := by exact_mod_cast (Nw_one (c := c) (U := U))
  have h2 := XN_le hc0 hU
  push_cast at h2
  have hle : 2 * (Xw U : ℝ) * (Nw c U) ≤ U ^ 8 := by
    have hlY0 := log_Yw_ge_one hc0 hU
    have h3 : 23 * Yw c U * Real.log (Yw c U) ≤ 23 * (U ^ 3) * U ^ 3 := by
      gcongr
      linarith
    have : (46 : ℝ) ≤ U ^ 2 := by nlinarith
    calc 2 * (Xw U : ℝ) * (Nw c U) = 2 * ((Xw U : ℝ) * (Nw c U)) := by ring
      _ ≤ 2 * (23 * (U ^ 3) * U ^ 3) := by linarith
      _ = 46 * U ^ 6 := by ring
      _ ≤ U ^ 2 * U ^ 6 := by gcongr
      _ = U ^ 8 := by ring
  have hpos : 0 < 2 * (Xw U : ℝ) * (Nw c U) := by positivity
  have := Real.log_le_log hpos hle
  rw [Real.log_pow] at this
  push_cast at this
  linarith

/-- `MV(X) ≤ 800 (log U)⁵`. -/
theorem bound_MV {U : ℝ} (hU : 8 ≤ U) : MV (Xw U) ≤ 800 * Real.log U ^ 5 := by
  have hL := log_ge_two hU
  have hX1 : 1 ≤ Xw U := Xw_one hU
  have hX1r : (1 : ℝ) ≤ Xw U := by exact_mod_cast hX1
  have hXU := Xw_le hU
  have hlX : Real.log (Xw U) ≤ Real.log U := Real.log_le_log (by linarith) hXU
  have hlX0 : 0 ≤ Real.log (Xw U) := Real.log_nonneg hX1r
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2' : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
  have hK : ((Nat.log 2 (Xw U) + 1 : ℕ) : ℝ) ≤ 2 * Real.log U := by
    have h1 := natLog_le (Xw U) hX1
    have h2 : Real.log (Xw U) / Real.log 2 ≤ 3 / 2 * Real.log U := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    push_cast; linarith
  have hK0 : (0 : ℝ) ≤ ((Nat.log 2 (Xw U) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hl2X : Real.log (2 * Xw U) ≤ 3 / 2 * Real.log U := by
    rw [Real.log_mul (by norm_num) (by linarith)]; linarith
  have hl2X0 : 0 ≤ Real.log (2 * Xw U) := Real.log_nonneg (by linarith)
  have he : Real.exp 1 ≤ 2.72 := by have := Real.exp_one_lt_d9; linarith
  have hA : 1 + Real.log (Xw U) ≤ 3 / 2 * Real.log U := by linarith
  have hB : 2 + Real.log (2 * Xw U) ^ 2 ≤ 3 * Real.log U ^ 2 := by nlinarith
  unfold MV
  have hL5 : 32 ≤ Real.log U ^ 5 := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ Real.log U ^ 5 := by gcongr
  calc 4 + 16 * Real.exp 1 * ((Nat.log 2 (Xw U) + 1 : ℕ) : ℝ) ^ 2 * (1 + Real.log (Xw U))
        * (2 + Real.log (2 * Xw U) ^ 2)
      ≤ 4 + 16 * 2.72 * (2 * Real.log U) ^ 2 * (3 / 2 * Real.log U) * (3 * Real.log U ^ 2) := by
        gcongr
    _ = 4 + 783.36 * Real.log U ^ 5 := by ring
    _ ≤ 800 * Real.log U ^ 5 := by linarith

/-- `U X^{1−2σ} + (XN)^{2−2σ} ≤ 71 log U · U^{(2+4c)(1−σ)}`. -/
theorem bound_S1 {c σ U : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hU : 8 ≤ U) :
    U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw c U)) ^ (2 - 2 * σ)
      ≤ 71 * Real.log U * U ^ ((2 + 4 * c) * (1 - σ)) := by
  have hL := log_ge_two hU
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  set E := (2 + 4 * c) * (1 - σ) with hE
  have hUE : 1 ≤ U ^ E := Real.one_le_rpow hU1 (by rw [hE]; nlinarith)
  -- the first term
  have hT1 : U * ((Xw U : ℝ)) ^ (1 - 2 * σ) ≤ 2 * U ^ E := by
    have hXh := Xw_half hU
    have h1 : ((Xw U : ℝ)) ^ (1 - 2 * σ) ≤ (U / 2) ^ (1 - 2 * σ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hXh (by linarith)
    have h2 : (U / 2) ^ (1 - 2 * σ) = U ^ (1 - 2 * σ) * 2 ^ (2 * σ - 1) := by
      rw [Real.div_rpow (by linarith) (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
      congr 2; ring
    have h3 : (2 : ℝ) ^ (2 * σ - 1) ≤ 2 := by
      calc (2 : ℝ) ^ (2 * σ - 1) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h4 : U * U ^ (1 - 2 * σ) = U ^ (2 - 2 * σ) := by
      rw [show (2 : ℝ) - 2 * σ = 1 + (1 - 2 * σ) by ring, Real.rpow_add hU0, Real.rpow_one]
    have h5 : U ^ (2 - 2 * σ) ≤ U ^ E := Real.rpow_le_rpow_of_exponent_le hU1 (by rw [hE]; nlinarith)
    have hp : 0 ≤ U ^ (1 - 2 * σ) := by positivity
    calc U * ((Xw U : ℝ)) ^ (1 - 2 * σ) ≤ U * (U ^ (1 - 2 * σ) * 2 ^ (2 * σ - 1)) := by
          rw [← h2]; gcongr
      _ ≤ U * (U ^ (1 - 2 * σ) * 2) := by gcongr
      _ = 2 * (U * U ^ (1 - 2 * σ)) := by ring
      _ = 2 * U ^ (2 - 2 * σ) := by rw [h4]
      _ ≤ 2 * U ^ E := by gcongr
  -- the second term
  have hT2 : ((Xw U : ℝ) * (Nw c U)) ^ (2 - 2 * σ) ≤ 69 * Real.log U * U ^ E := by
    have hXN := XN_le hc0 hU
    push_cast at hXN
    have hlY1 := log_Yw_ge_one hc0 hU
    have hY0 : 0 < Yw c U := by unfold Yw; positivity
    have hb : 1 ≤ 23 * Real.log (Yw c U) := by linarith
    have h1 : ((Xw U : ℝ) * (Nw c U)) ^ (2 - 2 * σ) ≤ (23 * Real.log (Yw c U) * Yw c U) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have h2 : (23 * Real.log (Yw c U) * Yw c U) ^ (2 - 2 * σ)
        = (23 * Real.log (Yw c U)) ^ (2 - 2 * σ) * (Yw c U) ^ (2 - 2 * σ) :=
      Real.mul_rpow (by linarith) hY0.le
    have h3 : (23 * Real.log (Yw c U)) ^ (2 - 2 * σ) ≤ 23 * Real.log (Yw c U) := by
      calc (23 * Real.log (Yw c U)) ^ (2 - 2 * σ) ≤ (23 * Real.log (Yw c U)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hb (by linarith)
        _ = 23 * Real.log (Yw c U) := Real.rpow_one _
    have h4 : 23 * Real.log (Yw c U) ≤ 69 * Real.log U := by
      rw [log_Yw hU]; nlinarith
    have h5 : (Yw c U) ^ (2 - 2 * σ) = U ^ E := by
      unfold Yw; rw [← Real.rpow_mul hU0.le, hE]; congr 1; ring
    calc ((Xw U : ℝ) * (Nw c U)) ^ (2 - 2 * σ) ≤ (23 * Real.log (Yw c U)) ^ (2 - 2 * σ) * (Yw c U) ^ (2 - 2 * σ) := by
          rw [← h2]; exact h1
      _ ≤ 69 * Real.log U * U ^ E := by
          rw [h5]; gcongr; exact h3.trans h4
  have hlU : 2 * U ^ E ≤ 2 * Real.log U * U ^ E := by
    have : 0 ≤ U ^ E := by positivity
    nlinarith
  linarith

/-- `A = KG C_Z (1 + 2U)^{1+c} Y^{½−σ}/δ` satisfies `A² ≤ 81 (KG C_Z/δ)² U^{(2+4c)(1−σ)+1}`. -/
theorem bound_A {c CZ δ σ U : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hCZ1 : 1 ≤ CZ) (hδ : 0 < δ) (hU : 8 ≤ U) :
    (KG * CZ * (1 + 2 * U) ^ (1 + c) * (Yw c U) ^ (1 / 2 - σ) / δ) ^ 2
      ≤ 81 * (KG * CZ / δ) ^ 2 * U ^ ((2 + 4 * c) * (1 - σ) + 1) := by
  have hU0 : 0 < U := by linarith
  have hKG := KG_pos
  have h1 : (1 + 2 * U) ^ (1 + c) ≤ 9 * U ^ (1 + c) := by
    calc (1 + 2 * U) ^ (1 + c) ≤ (3 * U) ^ (1 + c) := Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = (3 : ℝ) ^ (1 + c) * U ^ (1 + c) := Real.mul_rpow (by norm_num) hU0.le
      _ ≤ 9 * U ^ (1 + c) := by
          gcongr
          calc (3 : ℝ) ^ (1 + c) ≤ 3 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 9 := by norm_num
  have h2 : (Yw c U) ^ (1 / 2 - σ) = U ^ ((1 + 2 * c) * (1 / 2 - σ)) := by
    unfold Yw; rw [← Real.rpow_mul hU0.le]
  have h3 : U ^ (1 + c) * U ^ ((1 + 2 * c) * (1 / 2 - σ)) = U ^ (((2 + 4 * c) * (1 - σ) + 1) / 2) := by
    rw [← Real.rpow_add hU0]; congr 1; ring
  have h4 : (U ^ (((2 + 4 * c) * (1 - σ) + 1) / 2)) ^ 2 = U ^ ((2 + 4 * c) * (1 - σ) + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; congr 1; push_cast; ring
  have hA : KG * CZ * (1 + 2 * U) ^ (1 + c) * (Yw c U) ^ (1 / 2 - σ) / δ
      ≤ 9 * (KG * CZ / δ) * U ^ (((2 + 4 * c) * (1 - σ) + 1) / 2) := by
    rw [h2, ← h3]
    have : 0 ≤ U ^ ((1 + 2 * c) * (1 / 2 - σ)) := by positivity
    calc KG * CZ * (1 + 2 * U) ^ (1 + c) * U ^ ((1 + 2 * c) * (1 / 2 - σ)) / δ
        ≤ KG * CZ * (9 * U ^ (1 + c)) * U ^ ((1 + 2 * c) * (1 / 2 - σ)) / δ := by gcongr
      _ = 9 * (KG * CZ / δ) * (U ^ (1 + c) * U ^ ((1 + 2 * c) * (1 / 2 - σ))) := by ring
  have hA0 : 0 ≤ KG * CZ * (1 + 2 * U) ^ (1 + c) * (Yw c U) ^ (1 / 2 - σ) / δ := by
    unfold Yw; have : (0 : ℝ) ≤ CZ := by linarith
    positivity
  calc (KG * CZ * (1 + 2 * U) ^ (1 + c) * (Yw c U) ^ (1 / 2 - σ) / δ) ^ 2
      ≤ (9 * (KG * CZ / δ) * U ^ (((2 + 4 * c) * (1 - σ) + 1) / 2)) ^ 2 := by gcongr
    _ = 81 * (KG * CZ / δ) ^ 2 * (U ^ (((2 + 4 * c) * (1 - σ) + 1) / 2)) ^ 2 := by ring
    _ = 81 * (KG * CZ / δ) ^ 2 * U ^ ((2 + 4 * c) * (1 - σ) + 1) := by rw [h4]

/-- The class-3 term: `4A² MV(X)(U + X + 1)/U² ≤ 777600 (KG C_Z/δ)² (log U)⁵ U^{(2+4c)(1−σ)}`. -/
theorem bound_B3 {c CZ δ σ U : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hCZ1 : 1 ≤ CZ) (hδ : 0 < δ) (hU : 8 ≤ U) :
    4 * (KG * CZ * (1 + 2 * U) ^ (1 + c) * (Yw c U) ^ (1 / 2 - σ) / δ) ^ 2 * MV (Xw U) * (U + (Xw U) + 1) / U ^ 2
      ≤ 777600 * (KG * CZ / δ) ^ 2 * Real.log U ^ 5 * U ^ ((2 + 4 * c) * (1 - σ)) := by
  have hU0 : 0 < U := by linarith
  have hL := log_ge_two hU
  have hA := bound_A (σ := σ) hc0 hc1 hCZ1 hδ hU
  have hMV := bound_MV hU
  have hMV0 : 0 ≤ MV (Xw U) := by
    unfold MV; have := Real.log_nonneg (by exact_mod_cast Xw_one hU : (1 : ℝ) ≤ Xw U); positivity
  have hXU := Xw_le hU
  have h3U : U + (Xw U : ℝ) + 1 ≤ 3 * U := by linarith
  have hsum0 : 0 ≤ U + (Xw U : ℝ) + 1 := by positivity
  have hE : U ^ ((2 + 4 * c) * (1 - σ) + 1) = U ^ ((2 + 4 * c) * (1 - σ)) * U := by
    rw [Real.rpow_add hU0, Real.rpow_one]
  rw [div_le_iff₀ (by positivity)]
  calc 4 * (KG * CZ * (1 + 2 * U) ^ (1 + c) * (Yw c U) ^ (1 / 2 - σ) / δ) ^ 2 * MV (Xw U) * (U + (Xw U) + 1)
      ≤ 4 * (81 * (KG * CZ / δ) ^ 2 * U ^ ((2 + 4 * c) * (1 - σ) + 1)) * (800 * Real.log U ^ 5) * (3 * U) := by
        gcongr
    _ = 777600 * (KG * CZ / δ) ^ 2 * Real.log U ^ 5 * U ^ ((2 + 4 * c) * (1 - σ)) * U ^ 2 := by
        rw [hE]; ring

/-- The window constant. -/
def Cw (CZ δ : ℝ) : ℝ := 2 * Kc * (2 * (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71) + 777600 * (KG * CZ / δ) ^ 2)

theorem Cw_nonneg (CZ δ : ℝ) : 0 ≤ Cw CZ δ := by unfold Cw; have := Kc_nonneg; positivity

/-- **The window bound**: the right side of `window_classes` at `X = ⌊U⌋`, `Y = U^{1+2c}`, `N = ⌊22Y log Y/X⌋ + 1` is
at most `Cw (log U)^{11} U^{(2+4c)(1−σ)}`. -/
theorem window_bound {c CZ δ σ U : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hCZ1 : 1 ≤ CZ) (hδ : 0 < δ)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hU : 8 ≤ U) :
    2 * Kloc (2 * U + 1) * (2 * (((Nat.log 2 (Nw c U) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw c U))) ^ 6
        * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw c U)) ^ (2 - 2 * σ))))
      + 4 * (KG * CZ * (1 + 2 * U) ^ (1 + c) * (Yw c U) ^ (1 / 2 - σ) / δ) ^ 2 * MV (Xw U)
        * (U + (Xw U) + 1) / U ^ 2)
    ≤ Cw CZ δ * Real.log U ^ 11 * U ^ ((2 + 4 * c) * (1 - σ)) := by
  set L := Real.log U with hLdef
  set E := (2 + 4 * c) * (1 - σ) with hE
  have hL := log_ge_two hU
  have hL1 : 1 ≤ L := by linarith
  have hUE : 0 ≤ U ^ E := by positivity
  have hK := bound_K hc0 hc1 hU
  have hl := bound_ell hc0 hc1 hU
  have hS := bound_S1 hc0 hc1 hσ hσ1 hU
  have hB3 := bound_B3 (σ := σ) hc0 hc1 hCZ1 hδ hU
  have hKl := Kloc_le (U := U) (by linarith)
  have hKl0 : 0 ≤ Kloc (2 * U + 1) := Kloc_nonneg (by linarith)
  have he : 32 * Real.exp 1 ≤ 96 := by have := Real.exp_one_lt_d9; linarith
  have hK0 : (0 : ℝ) ≤ ((Nat.log 2 (Nw c U) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hX1 : (1 : ℝ) ≤ Xw U := by exact_mod_cast Xw_one hU
  have hN1 : (1 : ℝ) ≤ Nw c U := by exact_mod_cast (Nw_one (c := c) (U := U))
  have hl0 : 0 ≤ 1 + Real.log (2 * (Xw U : ℝ) * (Nw c U)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (Xw U : ℝ) * (Nw c U) by nlinarith)
    linarith
  have hS0 : 0 ≤ U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw c U)) ^ (2 - 2 * σ) := by positivity
  have e16 : ∀ x : ℝ, x / (1 / 4) ^ 2 = 16 * x := fun x => by norm_num [div_eq_mul_inv]; ring
  have hT1 : ((Nat.log 2 (Nw c U) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw c U))) ^ 6
        * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw c U)) ^ (2 - 2 * σ)))
      ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * L ^ 10 * U ^ E := by
    rw [e16]
    calc 16 * ((Nat.log 2 (Nw c U) + 1 : ℕ) : ℝ) ^ 3
          * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw c U))) ^ 6
            * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw c U)) ^ (2 - 2 * σ)))
        ≤ 16 * (13 * L) ^ 3 * (96 * (9 * L) ^ 6 * (71 * L * U ^ E)) := by gcongr
      _ = 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * L ^ 10 * U ^ E := by ring
  have hB3' : 4 * (KG * CZ * (1 + 2 * U) ^ (1 + c) * (Yw c U) ^ (1 / 2 - σ) / δ) ^ 2 * MV (Xw U)
        * (U + (Xw U) + 1) / U ^ 2 ≤ 777600 * (KG * CZ / δ) ^ 2 * L ^ 10 * U ^ E := by
    refine hB3.trans ?_
    have h510 : L ^ 5 ≤ L ^ 10 := pow_le_pow_right₀ hL1 (by norm_num)
    gcongr
  have hKlL : Kloc (2 * U + 1) ≤ Kc * L := hKl
  have hKcL : 0 ≤ 2 * (Kc * L) := by have := Kc_nonneg; positivity
  have hsum0 : 0 ≤ 2 * (((Nat.log 2 (Nw c U) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw c U))) ^ 6
        * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw c U)) ^ (2 - 2 * σ))))
      + 4 * (KG * CZ * (1 + 2 * U) ^ (1 + c) * (Yw c U) ^ (1 / 2 - σ) / δ) ^ 2 * MV (Xw U)
        * (U + (Xw U) + 1) / U ^ 2 := by
    have : 0 ≤ MV (Xw U) := by unfold MV; have := Real.log_nonneg hX1; positivity
    positivity
  calc 2 * Kloc (2 * U + 1) * (2 * (((Nat.log 2 (Nw c U) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw c U))) ^ 6
        * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw c U)) ^ (2 - 2 * σ))))
      + 4 * (KG * CZ * (1 + 2 * U) ^ (1 + c) * (Yw c U) ^ (1 / 2 - σ) / δ) ^ 2 * MV (Xw U)
        * (U + (Xw U) + 1) / U ^ 2)
      ≤ 2 * (Kc * L) * (2 * (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * L ^ 10 * U ^ E)
          + 777600 * (KG * CZ / δ) ^ 2 * L ^ 10 * U ^ E) := by
        gcongr
    _ = Cw CZ δ * L ^ 11 * U ^ E := by unfold Cw; ring

/-- **One window, unconditionally given the critical-line bound**: at most `Cw (log U)^{11} U^{(2+4c)(1−σ)}`
zeros with `U ≤ |γ| ≤ 2U` and `β ≥ σ ≥ ½ + δ`, for `U ≥ 8`. -/
theorem window_count_c {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {CZ : ℝ} (hCZ1 : 1 ≤ CZ)
    (hCZ : ∀ t : ℝ, ‖Zr (1 / 2 + t * I)‖ ≤ CZ * (1 + |t|) ^ (1 + c)) {σ δ U : ℝ} (hδ : 0 < δ)
    (hσδ : 1 / 2 + δ ≤ σ) (hσ1 : σ ≤ 1) (hU : 8 ≤ U) (Z : Finset (ZeroIdx (sqF Xi)))
    (hZ : ∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) :
    (Z.card : ℝ) ≤ Cw CZ δ * Real.log U ^ 11 * U ^ ((2 + 4 * c) * (1 - σ)) := by
  have hY := Yw_ge hc0 hU
  refine (window_classes hc0 hc1 hCZ1 hCZ hδ hσδ hσ1 (by linarith) (by linarith) hY (Xw_one hU) Nw_one
    (XN_ge hU) Z hZ).trans ?_
  exact window_bound hc0 hc1 hCZ1 hδ (by linarith) hσ1 hU

/-! ### Zero density -/

theorem log_le_pow12 {T : ℝ} (hT : 2 ≤ T) : Real.log T ≤ 2 ^ 11 * Real.log T ^ 12 := by
  have hl := half_le_log hT
  have h1 : 1 ≤ (2 * Real.log T) ^ 11 := one_le_pow₀ (by linarith)
  calc Real.log T = Real.log T * 1 := (mul_one _).symm
    _ ≤ Real.log T * (2 * Real.log T) ^ 11 := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = 2 ^ 11 * Real.log T ^ 12 := by ring

theorem one_le_pow12 {T : ℝ} (hT : 2 ≤ T) : 1 ≤ 2 ^ 12 * Real.log T ^ 12 := by
  have hl := half_le_log hT
  have h1 : 1 ≤ (2 * Real.log T) ^ 12 := one_le_pow₀ (by linarith)
  calc (1 : ℝ) ≤ (2 * Real.log T) ^ 12 := h1
    _ = 2 ^ 12 * Real.log T ^ 12 := by ring

/-- **Ingham's exponent from a pointwise bound on the critical line.** `ZetaCritBound c` with `0 < c ≤ 1` gives
`N(σ, T) ≤ C T^{(2+4c)(1−σ)}(log T)^{12}`: dyadic windows above `U₀ = 8` (`window_count_c`, with `δ = ½ − 1/(2+4c)`),
and the trivial bound below `σ = 1 − 1/(2+4c)`, where `T^{(2+4c)(1−σ)} ≥ T`. -/
theorem densityXi_of_zetaCrit {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (h : CrossCriteria.ZetaCritBound c) :
    DensityXi (2 + 4 * c) 12 := by
  classical
  obtain ⟨CZ, hCZ1, hCZ⟩ := Zr_crit_bound hc0.le h
  set A := 2 + 4 * c with hA
  set δ := 1 / 2 - 1 / A with hδdef
  have hA2 : 2 < A := by rw [hA]; linarith
  have hAδ : A * (1 / 2 - δ) = 1 := by rw [hδdef]; field_simp; ring
  have hδ : 0 < δ := by
    rw [hδdef]
    have : 1 / A < 1 / 2 := by rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  set U₀ : ℝ := 8 with hU₀
  set C0 : ℝ := ((finite_re_le U₀).toFinset.card : ℝ) with hC0
  have hC00 : 0 ≤ C0 := Nat.cast_nonneg _
  set Ca : ℝ := 2 * Kc * 2 ^ 11 with hCa
  set Cb : ℝ := C0 * 2 ^ 12 + 4 * Cw CZ δ with hCb
  have hCw := Cw_nonneg CZ δ
  have hCa0 : 0 ≤ Ca := by have := Kc_nonneg; positivity
  refine ⟨max Ca Cb, le_max_of_le_left hCa0, fun T hT w hw0 hw1 => ?_⟩
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlT := half_le_log hT
  set e := A * (1 / 2 - w) with he
  have he0 : 0 ≤ e := by rw [he]; nlinarith
  have hTe : 1 ≤ T ^ e := Real.one_le_rpow hT1 he0
  have hlog12 : 0 ≤ Real.log T ^ 12 := by positivity
  have e12 : Real.log T ^ (12 : ℝ) = Real.log T ^ (12 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
  rw [NX_eq_card, e12]
  set S := (finite_re_le T).toFinset.filter fun i => w ≤ |(tau i).im| with hS
  by_cases hw : w < δ
  · -- below `σ = 1 − 1/A`: the trivial bound
    have h1 : (S.card : ℝ) ≤ (T + 1) * Kloc T :=
      (Nat.cast_le.2 (card_filter_le _ _)).trans (card_re_le hT0.le)
    have h2 : Kloc T ≤ Kc * Real.log T :=
      (Kloc_mono (by linarith) (by linarith : T ≤ 2 * T + 1)).trans (Kloc_le hT)
    have h3 : T ≤ T ^ e := by
      calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
        _ ≤ T ^ e := Real.rpow_le_rpow_of_exponent_le hT1 (by rw [he]; nlinarith)
    have h4 := log_le_pow12 hT
    have hKc := Kc_nonneg
    calc (S.card : ℝ) ≤ (T + 1) * Kloc T := h1
      _ ≤ (2 * T) * (Kc * Real.log T) := by
          gcongr
          · exact Kloc_nonneg hT0.le
          · linarith
      _ ≤ (2 * T ^ e) * (Kc * (2 ^ 11 * Real.log T ^ 12)) := by gcongr
      _ = Ca * T ^ e * Real.log T ^ 12 := by rw [hCa]; ring
      _ ≤ max Ca Cb * T ^ e * Real.log T ^ 12 := by gcongr; exact le_max_left _ _
  · -- dyadic windows
    push Not at hw
    set σ := 1 / 2 + w with hσ
    have hσδ : 1 / 2 + δ ≤ σ := by rw [hσ]; linarith
    have hσ1 : σ ≤ 1 := by rw [hσ]; linarith
    have he' : e = A * (1 - σ) := by rw [he, hσ]; ring
    set mm : ZeroIdx (sqF Xi) → ℕ := fun i => ⌊|(tau i).re| / U₀⌋₊ with hmm
    set kk : ZeroIdx (sqF Xi) → ℕ := fun i => Nat.log 2 (mm i) with hkk
    set L := Nat.log 2 ⌊T / U₀⌋₊ + 1 with hL
    set Slow := S.filter fun i => |(tau i).re| ≤ U₀ with hSlow
    set Z : ℕ → Finset (ZeroIdx (sqF Xi)) := fun k => S.filter fun i => U₀ < |(tau i).re| ∧ kk i = k
      with hZ
    have hU₀0 : 0 < U₀ := by rw [hU₀]; norm_num
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
    have hwin : ∀ k ∈ range L, ((Z k).card : ℝ) ≤ Cw CZ δ * Real.log T ^ 11 * T ^ e := by
      intro k _
      rcases (Z k).eq_empty_or_nonempty with hZe | ⟨i1, hi1⟩
      · rw [hZe, card_empty, Nat.cast_zero]; positivity
      set U := (2 : ℝ) ^ k * U₀ with hUdef
      have hUU₀ : U₀ ≤ U := by
        rw [hUdef]; exact le_mul_of_one_le_left hU₀0.le (one_le_pow₀ (by norm_num))
      have hU8 : 8 ≤ U := by rw [hU₀] at hUU₀; exact hUU₀
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
      have hc := window_count_c hc0.le hc1 hCZ1 hCZ hδ hσδ hσ1 hU8 (Z k) fun i hi => by
        obtain ⟨hlo, hhi⟩ := hwinU i hi
        have hβ : σ ≤ βs i := by
          have := (mem_filter.1 (mem_filter.1 hi).1).2; unfold βs; rw [hσ]; linarith
        exact ⟨hlo, hhi, hβ⟩
      have hUT : U ≤ T := by
        have := (hwinU i1 hi1).1
        have hiT : |(tau i1).re| ≤ T := by
          have := (mem_filter.1 (mem_filter.1 hi1).1).1; simpa using this
        linarith
      have hlU : Real.log U ≤ Real.log T := Real.log_le_log (by linarith) hUT
      have hlU0 : 0 ≤ Real.log U := by linarith [log_ge_two hU8]
      calc ((Z k).card : ℝ) ≤ Cw CZ δ * Real.log U ^ 11 * U ^ ((2 + 4 * c) * (1 - σ)) := hc
        _ ≤ Cw CZ δ * Real.log T ^ 11 * T ^ e := by
            rw [he', hA]
            gcongr
    have hLle : (L : ℝ) ≤ 4 * Real.log T := by
      have h1 : (Nat.log 2 ⌊T / U₀⌋₊ : ℝ) ≤ Real.log T / Real.log 2 := by
        rcases Nat.eq_zero_or_pos ⌊T / U₀⌋₊ with h0 | hpos
        · rw [h0, Nat.log_zero_right, Nat.cast_zero]
          exact div_nonneg (by linarith) (Real.log_nonneg (by norm_num))
        · refine (natLog_le _ hpos).trans ?_
          apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
          apply Real.log_le_log (by exact_mod_cast hpos)
          calc (⌊T / U₀⌋₊ : ℝ) ≤ T / U₀ := Nat.floor_le (by positivity)
            _ ≤ T := div_le_self hT0.le (by rw [hU₀]; norm_num)
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
      _ ≤ C0 + ∑ _k ∈ range L, Cw CZ δ * Real.log T ^ 11 * T ^ e := by gcongr with k hk; exact hwin k hk
      _ = C0 + L * (Cw CZ δ * Real.log T ^ 11 * T ^ e) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ C0 * (2 ^ 12 * Real.log T ^ 12 * T ^ e)
            + (4 * Real.log T) * (Cw CZ δ * Real.log T ^ 11 * T ^ e) := by
          have h1 := one_le_pow12 hT
          have h2 : (1 : ℝ) ≤ 2 ^ 12 * Real.log T ^ 12 * T ^ e := one_le_mul_of_one_le_of_one_le h1 hTe
          have hlT0 : 0 ≤ Real.log T := by linarith
          have hW0 : 0 ≤ Cw CZ δ * Real.log T ^ 11 * T ^ e :=
            mul_nonneg (mul_nonneg hCw (pow_nonneg hlT0 11)) (by linarith)
          refine add_le_add ?_ (mul_le_mul_of_nonneg_right hLle hW0)
          calc C0 = C0 * 1 := by ring
            _ ≤ C0 * (2 ^ 12 * Real.log T ^ 12 * T ^ e) := mul_le_mul_of_nonneg_left h2 hC00
      _ = Cb * T ^ e * Real.log T ^ 12 := by rw [hCb]; ring
      _ ≤ max Ca Cb * T ^ e * Real.log T ^ 12 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)) hlog12

/-! ### Corollaries -/

/-- `DensityXi` is monotone in the exponent. -/
theorem densityXi_mono {A A' B : ℝ} (hA : A ≤ A') (h : DensityXi A B) : DensityXi A' B := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun T hT w hw0 hw1 => (hC T hT w hw0 hw1).trans ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have h1 : T ^ (A * (1 / 2 - w)) ≤ T ^ (A' * (1 / 2 - w)) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
  have hlog : 0 ≤ Real.log T ^ B := Real.rpow_nonneg (Real.log_nonneg hT1) B
  gcongr

/-- **`CrossCriteria.InghamFromC c` for every `c ≥ 0`**: `ZetaCritBound c` gives `DensityXi (2 + 4c + ε)` for every
`ε > 0` (`densityXi_of_zetaCrit` at `c + ε/4` when `c + ε/4 ≤ 1`; otherwise the target exponent exceeds `6`, and
round 517's convexity bound at `c = ½` gives the exponent `4`). -/
theorem inghamFromC {c : ℝ} (hc : 0 ≤ c) : CrossCriteria.InghamFromC c := by
  intro h ε hε
  refine ⟨12, ?_⟩
  rcases le_or_gt (c + ε / 4) 1 with h1 | h1
  · have hc' : CrossCriteria.ZetaCritBound (c + ε / 4) := Subconvexity.zetaCritBound_mono (by linarith) h
    have hd := densityXi_of_zetaCrit (c := c + ε / 4) (by linarith) h1 hc'
    have e : 2 + 4 * (c + ε / 4) = 2 + 4 * c + ε := by ring
    rwa [e] at hd
  · have hd := densityXi_of_zetaCrit (c := 1 / 4 + 1 / 4) (by norm_num) (by norm_num)
      (Subconvexity.convexityBound (1 / 4) (by norm_num))
    exact densityXi_mono (by linarith) hd

/-- **Zero density at round 517's exponent**: `N(σ, T) ≪ T^{(17/6 + ε)(1−σ)}(log T)^{12}` for every `ε > 0`. -/
theorem densityXi_17_6 {ε : ℝ} (hε : 0 < ε) : DensityXi (17 / 6 + ε) 12 := by
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have h := Subconvexity.zetaCritBound_five_24 (ε := ε' / 4) (by linarith)
  have hd := densityXi_of_zetaCrit (c := 5 / 24 + ε' / 4) (by positivity) (by linarith) h
  have e : 2 + 4 * (5 / 24 + ε' / 4) = 17 / 6 + ε' := by ring
  rw [e] at hd
  exact densityXi_mono (by linarith) hd

/-- **Zero density at round 469's `Θ`**: `N(σ, T) ≪ T^{(1 + 2Θ + ε)(1−σ)}(log T)^{12}` for every `ε > 0`. -/
theorem densityXi_Theta {ε : ℝ} (hε : 0 < ε) : DensityXi (1 + 2 * PsiExponent.Theta + ε) 12 := by
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hT1 := PsiExponent.half_le_Theta
  have hT2 := PsiExponent.Theta_le
  have h := Subconvexity.zetaCritBound_Theta (ε := ε' / 4) (by linarith)
  have hd := densityXi_of_zetaCrit (c := (2 * PsiExponent.Theta - 1) / 4 + ε' / 4) (by linarith)
    (by linarith) h
  have e : 2 + 4 * ((2 * PsiExponent.Theta - 1) / 4 + ε' / 4) = 1 + 2 * PsiExponent.Theta + ε' := by ring
  rw [e] at hd
  exact densityXi_mono (by linarith) hd

/-- **Lindelöf implies the density hypothesis.** -/
theorem densityHypothesis_of_lindelof (h : CrossCriteria.Lindelof) : CrossCriteria.DensityHypothesis := by
  intro ε hε
  obtain ⟨B, hB⟩ := inghamFromC (c := ε / 8) (by positivity) (h (ε / 8) (by positivity)) (ε / 2) (by positivity)
  refine ⟨B, ?_⟩
  have e : 2 + 4 * (ε / 8) + ε / 2 = 2 + ε := by ring
  rwa [e] at hB

/-- Short intervals from a density exponent `A₀ + ε` for every `ε > 0`: a prime in `(y, y + y^θ]` for every
`θ > max(½, 1 − 1/A₀)` and all large `y` (round 235's `short_primes_KV_of_density`). -/
theorem short_primes_of_density_eps {A₀ : ℝ} (hA₀ : 0 < A₀)
    (hd : ∀ ε > 0, ∃ B : ℝ, DensityXi (A₀ + ε) B) {θ : ℝ} (h1 : 1 / 2 < θ) (h2 : 1 - 1 / A₀ < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ := by
  rcases lt_or_ge θ 1 with hθ1 | hθ1
  · have h1θ : 0 < 1 - θ := by linarith
    have hinv : A₀ < 1 / (1 - θ) := by
      rw [lt_div_iff₀ h1θ]
      have h3 : 1 - θ < 1 / A₀ := by linarith
      rw [lt_div_iff₀ hA₀] at h3
      linarith
    set A := (A₀ + 1 / (1 - θ)) / 2 with hA
    have hAA₀ : A₀ < A := by rw [hA]; linarith
    have hA1 : A < 1 / (1 - θ) := by rw [hA]; linarith
    obtain ⟨B, hB⟩ := hd (A - A₀) (by linarith)
    rw [show A₀ + (A - A₀) = A by ring] at hB
    refine ShortKV.short_primes_KV_of_density (by linarith) hB h1 ?_
    have h4 : A * (1 - θ) < 1 := by rwa [lt_div_iff₀ h1θ] at hA1
    have h5 : 1 - θ < 1 / A := by rw [lt_div_iff₀ (by linarith)]; linarith
    linarith
  · obtain ⟨B, hB⟩ := hd 1 one_pos
    refine ShortKV.short_primes_KV_of_density (by linarith) hB h1 ?_
    have : 0 < 1 / (A₀ + 1) := by positivity
    linarith

/-- **Primes in short intervals for every `θ > 11/17`**: from `densityXi_17_6`. -/
theorem short_primes_11_17 {θ : ℝ} (hθ : 11 / 17 < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ :=
  short_primes_of_density_eps (A₀ := 17 / 6) (by norm_num) (fun ε hε => ⟨12, densityXi_17_6 hε⟩)
    (by linarith) (by norm_num; linarith)

/-- **Primes in short intervals at `Θ`**: for every `θ > 2Θ/(1 + 2Θ)`. -/
theorem short_primes_Theta {θ : ℝ} (hθ : 2 * PsiExponent.Theta / (1 + 2 * PsiExponent.Theta) < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ := by
  have hT1 := PsiExponent.half_le_Theta
  have hA : 0 < 1 + 2 * PsiExponent.Theta := by linarith
  have e : 1 - 1 / (1 + 2 * PsiExponent.Theta) = 2 * PsiExponent.Theta / (1 + 2 * PsiExponent.Theta) := by
    field_simp; ring
  have hhalf : 1 / 2 ≤ 2 * PsiExponent.Theta / (1 + 2 * PsiExponent.Theta) := by
    rw [le_div_iff₀ hA]; linarith
  exact short_primes_of_density_eps hA (fun ε hε => ⟨12, densityXi_Theta hε⟩) (by linarith) (by rw [e]; exact hθ)

end InghamDensity

#print axioms InghamDensity.card_le_of_classes
#print axioms InghamDensity.class_count_b
#print axioms InghamDensity.Zr_crit_bound
#print axioms InghamDensity.mean_value_moll
#print axioms InghamDensity.class3_count
#print axioms InghamDensity.window_count_c
#print axioms InghamDensity.densityXi_of_zetaCrit
#print axioms InghamDensity.inghamFromC
#print axioms InghamDensity.densityXi_17_6
#print axioms InghamDensity.densityXi_Theta
#print axioms InghamDensity.densityHypothesis_of_lindelof
#print axioms InghamDensity.short_primes_11_17
#print axioms InghamDensity.short_primes_Theta
