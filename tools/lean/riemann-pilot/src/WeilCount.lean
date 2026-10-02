import Mathlib
import XiLogDeriv

/-! # A sharper zero count (round 156, part 3)

`summable_ord_div` (round 18) gives `Σ ord(u)/|u| < ∞` for an entire `F` of growth exponent `α < 1`.
The same dyadic argument gives `Σ ord(u)/|u|^β < ∞` for every `β > α`. For `F(w) = Ξ(√w)`
(`α = 3/4`, from `xiGrowth`) this is `Σ_ρ |t_ρ|^{−7/4} < ∞` (`β = 7/8`), the convergence the
explicit formula's zero sum needs for test functions decaying like `1/t²`.
-/

open Real Filter Topology Complex Set

noncomputable section

namespace Pilot1ca

theorem two_pow_rpow (c : ℝ) (j : ℕ) : ((2 : ℝ) ^ j) ^ c = ((2 : ℝ) ^ c) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast ((2 : ℝ) ^ c), ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), mul_comm]

/-- **`Σ ord(u)/|u|^β < ∞`** for `β > α`. -/
theorem summable_ord_div_rpow {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) {C A α β : ℝ}
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hα0 : 0 ≤ α) (hαβ : α < β)
    (hgrowth : ∀ w, ‖F w‖ ≤ C * Real.exp (A * ‖w‖ ^ α)) :
    Summable (fun u : ℂ => (ordN F u : ℝ) / ‖u‖ ^ β) := by
  have hβ : 0 < β := by linarith
  obtain ⟨m, hm, hmz⟩ := exists_zero_free_ball hF hF0
  set K := |Real.log C - Real.log ‖F 0‖|
  set A₁ := A * Real.exp 1 ^ α
  have hK : 0 ≤ K := abs_nonneg _
  have hA₁ : 0 ≤ A₁ := by positivity
  set term : ℕ → ℝ := fun j => (K + A₁ * (2 ^ (j + 1) * m) ^ α) / (2 ^ j * m) ^ β
  set q1 : ℝ := ((2 : ℝ) ^ β)⁻¹
  set q2 : ℝ := (2 : ℝ) ^ α / (2 : ℝ) ^ β
  have h2β : 1 < (2 : ℝ) ^ β := Real.one_lt_rpow (by norm_num) hβ
  have hq1 : q1 < 1 := inv_lt_one_of_one_lt₀ h2β
  have hq2 : q2 < 1 := by
    rw [div_lt_one (by positivity)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hαβ
  have hterm : ∀ j : ℕ, term j = K / m ^ β * q1 ^ j + A₁ * 2 ^ α * m ^ α / m ^ β * q2 ^ j := by
    intro j
    simp only [term, q1, q2]
    rw [Real.mul_rpow (by positivity) hm.le, Real.mul_rpow (by positivity) hm.le, pow_succ,
      Real.mul_rpow (by positivity) (by norm_num), two_pow_rpow, two_pow_rpow, inv_pow, div_pow]
    have h1 : (0 : ℝ) < ((2 : ℝ) ^ β) ^ j := by positivity
    have h2 : (0 : ℝ) < m ^ β := by positivity
    field_simp
  have hsum : Summable term := by
    have h1 := (summable_geometric_of_lt_one (by positivity) hq1).mul_left (K / m ^ β)
    have h2 := (summable_geometric_of_lt_one (by positivity) hq2).mul_left
      (A₁ * 2 ^ α * m ^ α / m ^ β)
    exact (h1.add h2).congr fun j => (hterm j).symm
  have hterm0 : ∀ j, 0 ≤ term j := fun j => by simp only [term]; positivity
  refine summable_of_sum_le (c := ∑' j, term j) (fun u => by positivity) (fun S => ?_)
  set S' := S.filter (fun u => ordN F u ≠ 0)
  have hS' : ∑ u ∈ S, (ordN F u : ℝ) / ‖u‖ ^ β = ∑ u ∈ S', (ordN F u : ℝ) / ‖u‖ ^ β := by
    rw [Finset.sum_filter_of_ne]
    intro u _ h h0; rw [h0] at h; simp at h
  rw [hS']
  have hbig : ∀ u ∈ S', m ≤ ‖u‖ := by
    intro u hu
    have hz := (ordN_ne_zero_iff hF hF0 u).1 (Finset.mem_filter.1 hu).2
    by_contra h; exact hmz u (lt_of_not_ge h) hz
  set J : ℂ → ℕ := fun u => Nat.log 2 ⌊‖u‖ / m⌋₊
  have hJ : ∀ u ∈ S', (2 : ℝ) ^ J u * m ≤ ‖u‖ ∧ ‖u‖ < 2 ^ (J u + 1) * m := by
    intro u hu
    have hx : 1 ≤ ‖u‖ / m := by rw [le_div_iff₀ hm]; linarith [hbig u hu]
    have hn : ⌊‖u‖ / m⌋₊ ≠ 0 := by
      have := Nat.floor_pos.2 hx; omega
    have h1 : 2 ^ J u ≤ ⌊‖u‖ / m⌋₊ := Nat.pow_log_le_self 2 hn
    have h2 : ⌊‖u‖ / m⌋₊ < 2 ^ (J u + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    constructor
    · have : ((2 ^ J u : ℕ) : ℝ) ≤ ‖u‖ / m :=
        le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
      rw [le_div_iff₀ hm] at this; exact_mod_cast this
    · have h3 : ‖u‖ / m < ((2 ^ (J u + 1) : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one (‖u‖ / m)
        have h4 : ((⌊‖u‖ / m⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ (J u + 1) : ℕ) : ℝ) := by
          exact_mod_cast h2
        linarith
      rw [div_lt_iff₀ hm] at h3; exact_mod_cast h3
  rw [← Finset.sum_fiberwise_of_maps_to (g := J) (t := S'.image J)
    (fun u hu => Finset.mem_image_of_mem J hu)]
  calc ∑ j ∈ S'.image J, ∑ u ∈ S' with J u = j, (ordN F u : ℝ) / ‖u‖ ^ β
      ≤ ∑ j ∈ S'.image J, term j := by
        apply Finset.sum_le_sum
        intro j _
        have hfib : ∀ u ∈ S'.filter (fun u => J u = j),
            (ordN F u : ℝ) / ‖u‖ ^ β ≤ (ordN F u : ℝ) / (2 ^ j * m) ^ β := by
          intro u hu
          obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
          have := (hJ u hu1).1
          rw [hu2] at this
          exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (Real.rpow_le_rpow (by positivity) this hβ.le)
        refine (Finset.sum_le_sum hfib).trans ?_
        rw [← Finset.sum_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply zero_count' hF hF0 hC hA hα0 hgrowth (by positivity)
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
        have := (hJ u hu1).2
        rw [hu2] at this
        exact this.le
    _ ≤ ∑' j, term j := hsum.sum_le_tsum _ (fun j _ => hterm0 j)

/-- Over the zero family of `F(w) = Ξ(√w)`: `Σ_i |u_i|^{−7/8} < ∞`. -/
theorem summable_Xi_zeros_rpow :
    Summable (fun i : ZeroIdx (sqF Xi) => (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹) := by
  obtain ⟨C, A, hC, hA, hg⟩ := xiGrowth
  have hF := sqF_differentiable differentiable_Xi Xi_even
  have hF0 : sqF Xi 0 ≠ 0 := by rw [sqF_zero]; exact Xi_zero_ne_zero
  have hgF : ∀ w, ‖sqF Xi w‖ ≤ C * Real.exp (A * ‖w‖ ^ (3 / 4 : ℝ)) := by
    intro w
    refine (hg _).trans ?_
    have hn : ‖w ^ ((2 : ℂ)⁻¹)‖ = ‖w‖ ^ (2⁻¹ : ℝ) := by
      rw [show ((2 : ℂ)⁻¹) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
    rw [hn, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hs := summable_ord_div_rpow hF hF0 hC hA (by norm_num) (by norm_num : (3 / 4 : ℝ) < 7 / 8) hgF
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  refine ⟨fun u => (hasSum_fintype _).summable, ?_⟩
  refine hs.congr fun u => ?_
  rw [tsum_fintype]
  show _ = ∑ _b : Fin (ordN (sqF Xi) u), (‖u‖ ^ (7 / 8 : ℝ))⁻¹
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]

end Pilot1ca

#print axioms Pilot1ca.summable_ord_div_rpow
#print axioms Pilot1ca.summable_Xi_zeros_rpow
