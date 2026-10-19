import SieveRough
import SieveBrun

open Real Filter Finset
open scoped Chebyshev

namespace SieveRanges

/-- The primes of `[A, A²)`. -/
noncomputable def rng (A : ℝ) : Finset ℕ :=
  (Finset.range ⌈A ^ 2⌉₊).filter (fun p => p.Prime ∧ A ≤ p)

theorem mem_rng {A : ℝ} {p : ℕ} : p ∈ rng A ↔ p.Prime ∧ A ≤ p ∧ (p : ℝ) < A ^ 2 := by
  rw [rng, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
  tauto

/-- **The prime sums of the ranges are uniformly bounded.** -/
theorem rng_sum_le : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ A : ℝ, 1 ≤ A → ∑ p ∈ rng A, 1 / (p : ℝ) ≤ C₀ := by
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 (SieveRough.theta_near (ε := 1 / 10) (by norm_num))
  set t₀ := max T₁ (Real.exp 1) with ht₀
  have he : (1 : ℝ) < Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have ht₀1 : 1 < t₀ := lt_of_lt_of_le he (le_max_right _ _)
  refine ⟨max 3 (t₀ ^ 2 + 1), le_max_of_le_left (by norm_num), fun A hA => ?_⟩
  have hterm : ∀ p ∈ rng A, 0 ≤ 1 / (p : ℝ) := fun p _ => by positivity
  by_cases hbig : t₀ ≤ A
  · refine le_trans ?_ (le_max_left _ _)
    have hAe : Real.exp 1 ≤ A := le_trans (le_max_right _ _) hbig
    have hA1 : 1 < A := lt_of_lt_of_le he hAe
    have hlogA : 1 ≤ Real.log A := by rw [Real.le_log_iff_exp_le (by linarith)]; exact hAe
    -- the range lies in `{⌈A⌉} ∪ (A, A²]`
    have hsub : rng A ⊆ insert ⌈A⌉₊ ((Ioc ⌊A⌋₊ ⌊A ^ 2⌋₊).filter Nat.Prime) := by
      intro p hp
      obtain ⟨hpp, hAp, hpA⟩ := mem_rng.1 hp
      rcases eq_or_lt_of_le hAp with h | h
      · rw [Finset.mem_insert]; left
        rw [h, Nat.ceil_natCast]
      · rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_Ioc]; right
        refine ⟨⟨?_, Nat.le_floor hpA.le⟩, hpp⟩
        exact Nat.floor_lt (by linarith) |>.2 h
    have h1 := SieveRough.sum_inv_le (a := A) (b := A ^ 2) (ε := 1 / 10) hAe (by nlinarith) (by norm_num)
      (fun t ht => hT₁ t (le_trans (le_max_left _ _) (le_trans hbig ht.1)))
    have hlog : Real.log (Real.log (A ^ 2)) - Real.log (Real.log A) = Real.log 2 := by
      rw [Real.log_pow, show ((2 : ℕ) : ℝ) * Real.log A = 2 * Real.log A by norm_num,
        Real.log_mul (by norm_num) (by linarith)]
      ring
    rw [hlog] at h1
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hb1 : (1 / 10) / Real.log A ≤ 1 / 10 := div_le_self (by norm_num) hlogA
    have hb2 : 3 * (1 / 10) / Real.log A ^ 2 ≤ 3 / 10 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hceil : 1 / (⌈A⌉₊ : ℝ) ≤ 1 := by
      rw [div_le_one (by have := Nat.le_ceil A; linarith)]
      have := Nat.le_ceil A; linarith
    calc ∑ p ∈ rng A, 1 / (p : ℝ) ≤ ∑ p ∈ insert ⌈A⌉₊ ((Ioc ⌊A⌋₊ ⌊A ^ 2⌋₊).filter Nat.Prime), 1 / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
      _ ≤ 1 / (⌈A⌉₊ : ℝ) + ∑ p ∈ (Ioc ⌊A⌋₊ ⌊A ^ 2⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
          by_cases hm : ⌈A⌉₊ ∈ (Ioc ⌊A⌋₊ ⌊A ^ 2⌋₊).filter Nat.Prime
          · rw [Finset.insert_eq_of_mem hm]
            have : (0 : ℝ) ≤ 1 / (⌈A⌉₊ : ℝ) := by positivity
            linarith
          · rw [Finset.sum_insert hm]
      _ ≤ 3 := by nlinarith
  · push Not at hbig
    refine le_trans ?_ (le_max_right _ _)
    have hcard : ((rng A).card : ℝ) ≤ t₀ ^ 2 + 1 := by
      have h1 : (rng A).card ≤ ⌈A ^ 2⌉₊ := by
        rw [rng]; exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
      have h2 : (⌈A ^ 2⌉₊ : ℝ) < A ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
      have h3 : A ^ 2 ≤ t₀ ^ 2 := by nlinarith
      have : ((rng A).card : ℝ) ≤ ⌈A ^ 2⌉₊ := by exact_mod_cast h1
      linarith
    calc ∑ p ∈ rng A, 1 / (p : ℝ) ≤ ∑ _p ∈ rng A, (1 : ℝ) := Finset.sum_le_sum fun p hp => by
          have := (mem_rng.1 hp).1.two_le
          rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ p)
      _ = (rng A).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ t₀ ^ 2 + 1 := hcard

/-! ### The ranges below `w` -/

theorem sq_rpow_half {w : ℝ} (hw : 0 ≤ w) (j : ℕ) : (w ^ ((1 / 2 : ℝ) ^ (j + 1))) ^ 2 = w ^ ((1 / 2 : ℝ) ^ j) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hw]
  congr 1
  rw [pow_succ]; ring

theorem rpow_half_anti {w : ℝ} (hw : 1 ≤ w) {i j : ℕ} (hij : i ≤ j) :
    w ^ ((1 / 2 : ℝ) ^ j) ≤ w ^ ((1 / 2 : ℝ) ^ i) :=
  Real.rpow_le_rpow_of_exponent_le hw (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij)

theorem lt_of_mem_rng {w : ℝ} (hw : 1 ≤ w) {j p : ℕ} (hp : p ∈ rng (w ^ ((1 / 2 : ℝ) ^ (j + 1)))) :
    (p : ℝ) < w ^ ((1 / 2 : ℝ) ^ j) := by
  have := (mem_rng.1 hp).2.2
  rwa [sq_rpow_half (by linarith)] at this

theorem lt_w_of_mem_rng {w : ℝ} (hw : 1 ≤ w) {j p : ℕ} (hp : p ∈ rng (w ^ ((1 / 2 : ℝ) ^ (j + 1)))) :
    (p : ℝ) < w := by
  have h := lt_of_mem_rng hw hp
  have h2 := rpow_half_anti hw (Nat.zero_le j)
  simp only [pow_zero, Real.rpow_one] at h2
  linarith

/-- The ranges cover the primes below `w`, once `w^{2^{−J}} ≤ 2`. -/
theorem cover {w : ℝ} {J : ℕ} (hJ : w ^ ((1 / 2 : ℝ) ^ J) ≤ 2) {p : ℕ} (hp : p.Prime)
    (hpw : (p : ℝ) < w) : ∃ j < J, p ∈ rng (w ^ ((1 / 2 : ℝ) ^ (j + 1))) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hJ1 : 1 ≤ J := by
    by_contra h
    push Not at h
    interval_cases J
    simp at hJ
    linarith
  have hex : ∃ j, w ^ ((1 / 2 : ℝ) ^ (j + 1)) ≤ p := ⟨J - 1, by rw [Nat.sub_add_cancel hJ1]; linarith⟩
  classical
  set j₀ := Nat.find hex with hj₀
  have hlow : w ^ ((1 / 2 : ℝ) ^ (j₀ + 1)) ≤ p := Nat.find_spec hex
  have hj₀J : j₀ < J := by
    have := Nat.find_min' hex (show w ^ ((1 / 2 : ℝ) ^ (J - 1 + 1)) ≤ p by
      rw [Nat.sub_add_cancel hJ1]; linarith)
    omega
  refine ⟨j₀, hj₀J, mem_rng.2 ⟨hp, hlow, ?_⟩⟩
  rw [sq_rpow_half (by linarith)]
  rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
  · rw [h0]; simpa using hpw
  · obtain ⟨j', hj'⟩ : ∃ j', j₀ = j' + 1 := ⟨j₀ - 1, by omega⟩
    have hmin := Nat.find_min hex (show j' < j₀ by omega)
    push Not at hmin
    rw [hj']; exact hmin

/-- The ranges are disjoint. -/
theorem rng_disjoint {w : ℝ} (hw : 1 ≤ w) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (rng (w ^ ((1 / 2 : ℝ) ^ (i + 1)))) (rng (w ^ ((1 / 2 : ℝ) ^ (j + 1)))) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rcases lt_or_gt_of_ne hij with h | h
  · have h1 := lt_of_mem_rng hw hpj
    have h2 := (mem_rng.1 hpi).2.1
    have h3 := rpow_half_anti hw (show i + 1 ≤ j by omega)
    linarith
  · have h1 := lt_of_mem_rng hw hpi
    have h2 := (mem_rng.1 hpj).2.1
    have h3 := rpow_half_anti hw (show j + 1 ≤ i by omega)
    linarith

end SieveRanges
