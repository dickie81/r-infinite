import Mathlib
import KaiserZeroWeight
import ShortPrimes

/-! # Local zero counts (round 235)

Round 164's zero weight `Σ_τ V_τ(x) ≤ (5 + kLam + ½ log(|x| + 2))/π` (`Kaiser.tsum_Vz_le`) counts
zeros locally: each `τ` with `||Re τ| − x| ≤ 1` has `V_τ(x) ≥ 2/(13π)`. So
* `card_local_le`: at most `(13/2)(5 + kLam + ½ log(x + 2))` zeros of `Ξ` have `||Re τ| − x| ≤ 1`;
* `card_re_le`: `#{τ : |Re τ| ≤ T} ≤ (T + 1)·(13/2)(5 + kLam + ½ log(T + 2))`.
-/

open Real Finset

noncomputable section

namespace ShortWeil

open Pilot1ca Pilot1bt Kaiser

/-- `Kloc(x) = (13/2)(5 + kLam + ½ log(x + 2))`. -/
def Kloc (x : ℝ) : ℝ := 13 / 2 * (5 + kLam + Real.log (x + 2) / 2)

theorem kLam_nonneg : 0 ≤ kLam := tsum_nonneg fun _ => norm_nonneg _

theorem Vz_ge {x : ℝ} {τ : ℂ} (hτ : |τ.im| < 1 / 2) (h : |(|τ.re| - x)| ≤ 1) :
    2 / (13 * π) ≤ Vz τ x := by
  obtain ⟨hs1, hs2⟩ := abs_lt.1 hτ
  have key : ∀ y z : ℝ, 1 / 2 ≤ y → y ≤ 3 / 2 → |z| ≤ 1 → 2 / (13 * π) ≤ pk y z := by
    intro y z hy1 hy2 hz
    unfold pk
    have hz2 : z ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg z]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 2 * (z ^ 2 + y ^ 2) ≤ 13 * y := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 pi_pos.le]
  unfold Vz
  rcases le_total 0 τ.re with hr | hr
  · rw [abs_of_nonneg hr] at h
    have h1 := key (1 + τ.im) (x - τ.re) (by linarith) (by linarith) (by rw [abs_sub_comm]; exact h)
    have h2 := pk_nonneg (by linarith : 0 ≤ 1 - τ.im) (x + τ.re)
    linarith
  · rw [abs_of_nonpos hr] at h
    have h1 := key (1 - τ.im) (x + τ.re) (by linarith) (by linarith)
      (by rw [show x + τ.re = -(-τ.re - x) by ring, abs_neg]; exact h)
    have h2 := pk_nonneg (by linarith : 0 ≤ 1 + τ.im) (x - τ.re)
    linarith

theorem summable_Vz (x : ℝ) : Summable fun i : ZeroIdx (sqF Xi) => Vz (tau i) x := (hasSum_Vz x).summable

/-- **The local count.** -/
theorem card_local_le {x : ℝ} (hx : 0 ≤ x) (F : Finset (ZeroIdx (sqF Xi)))
    (hF : ∀ i ∈ F, |(|(tau i).re| - x)| ≤ 1) : (F.card : ℝ) ≤ Kloc x := by
  have h1 : (F.card : ℝ) * (2 / (13 * π)) ≤ ∑ i ∈ F, Vz (tau i) x := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi => Vz_ge (tau_im i) (hF i hi)
  have h2 : ∑ i ∈ F, Vz (tau i) x ≤ ∑' i, Vz (tau i) x :=
    (summable_Vz x).sum_le_tsum F fun i _ => Vz_nonneg (tau_im i) x
  have h3 := tsum_Vz_le x
  rw [abs_of_nonneg hx] at h3
  have hc : (0 : ℝ) < 2 / (13 * π) := by positivity
  have : (F.card : ℝ) * (2 / (13 * π)) ≤ (5 + kLam + Real.log (x + 2) / 2) / π := by linarith
  unfold Kloc
  rw [show (F.card : ℝ) * (2 / (13 * π)) = (F.card : ℝ) * 2 / 13 / π by ring,
    div_le_div_iff_of_pos_right pi_pos] at this
  linarith

theorem Kloc_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : Kloc x ≤ Kloc y := by
  unfold Kloc
  have := Real.log_le_log (by linarith) (by linarith : x + 2 ≤ y + 2)
  nlinarith

/-- **`#{τ : |Re τ| ≤ T} ≤ (T + 1)·Kloc(T)`.** -/
theorem card_re_le {T : ℝ} (hT : 0 ≤ T) :
    ((finite_re_le T).toFinset.card : ℝ) ≤ (T + 1) * Kloc T := by
  set F := (finite_re_le T).toFinset with hF
  set n : ZeroIdx (sqF Xi) → ℕ := fun i => ⌊|(tau i).re|⌋₊ with hn
  have hmaps : ∀ i ∈ F, n i ∈ Finset.range (⌊T⌋₊ + 1) := by
    intro i hi
    have : |(tau i).re| ≤ T := by simpa [hF] using hi
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.floor_le_floor this))
  have hfib : ∀ k ∈ Finset.range (⌊T⌋₊ + 1), ((F.filter fun i => n i = k).card : ℝ) ≤ Kloc T := by
    intro k hk
    have hkT : (k : ℝ) ≤ T := by
      have := Finset.mem_range.1 hk
      exact (Nat.cast_le.2 (Nat.lt_succ_iff.1 this)).trans (Nat.floor_le hT)
    refine (card_local_le (Nat.cast_nonneg k) _ fun i hi => ?_).trans (Kloc_mono (Nat.cast_nonneg k) hkT)
    obtain ⟨_, hik⟩ := Finset.mem_filter.1 hi
    have h1 := Nat.floor_le (abs_nonneg (tau i).re)
    have h2 := Nat.lt_floor_add_one |(tau i).re|
    simp only [hn] at hik
    rw [hik] at h1 h2
    rw [abs_le]; constructor <;> linarith
  calc (F.card : ℝ) = ∑ k ∈ Finset.range (⌊T⌋₊ + 1), ((F.filter fun i => n i = k).card : ℝ) := by
        rw [← Nat.cast_sum, card_eq_sum_card_fiberwise hmaps]
    _ ≤ ∑ _k ∈ Finset.range (⌊T⌋₊ + 1), Kloc T := sum_le_sum hfib
    _ = (⌊T⌋₊ + 1) * Kloc T := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ (T + 1) * Kloc T := by
        have hK : 0 ≤ Kloc T := by
          unfold Kloc; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2)
          have := kLam_nonneg; positivity
        gcongr; exact Nat.floor_le hT

end ShortWeil

#print axioms ShortWeil.card_local_le
#print axioms ShortWeil.card_re_le
