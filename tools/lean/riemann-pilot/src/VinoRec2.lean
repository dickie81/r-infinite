/-
# Sharpening, step S2b: VMVT with geometric decay from the start (round 214)

Plain statements.
* `step_real2`: if `J_s(Q) ≤ C·Q^E` for all `Q ≥ 1`, then `J_{k+s}(P) ≤ C'·P^{E'}` for all
  `P ≥ 1`, with `E' = μ/k = 2(k+s) − k(k+1)/2 + (1−1/k)(E − 2s + k(k+1)/2)` — the good-part
  exponent only. The bad part (`one_step2`, round 214) is fed back by strong induction on `P`:
  it costs `C'·P^{E'}/2` once `P^{1/k} ≥ T₀` with `T₀^D ≥ 8(2(k+2))^{2(k−1)}(k−1)^{2(k+s)}2^{E'}`,
  `D = E' − 2(k−1)`; below `P₀ = ⌈T₀⌉^k` the trivial bound `J ≤ P^{2(k+s)}` is used.
* `vmvt2`: `J_{k+mk,k}(P) ≤ C_m·P^{2(k+mk) − k(k+1)/2 + η_m}` with `η_m = (1−1/k)^m·k(k−1)/2`
  (no second branch; round 202 had `max(…, k(k+1)/2 − 2(s+1)/k)`), taking `T₀ = (4k)^{20}`.
* `Cv2_le`: `C_m ≤ (8(k+2))^{40k²(m+1) + g(m)}` with `g` from round 207.
-/
import VinoBad
import VinoConst2

open Finset

namespace VinoRec2

open Vinogradov VinoIter VinoHolder VinoSplit VinoRec VinoBad

set_option maxHeartbeats 3200000 in
/-- **One step with the bad part fed back.** -/
theorem step_real2 {k s : ℕ} (hk : 2 ≤ k) (hs : 1 ≤ s) {C E T0 : ℝ} (hC : 0 < C) (hE : 0 ≤ E)
    (hJ : ∀ Q : ℕ, 1 ≤ Q → (J s k Q : ℝ) ≤ C * (Q : ℝ) ^ E)
    (hT0 : 1 ≤ T0)
    (hDpos : 0 < μ k s E / k - 2 * ((k : ℝ) - 1))
    (hKb : 8 * (2 * ((k : ℝ) + 2)) ^ (2 * (k - 1)) * (((k - 1 : ℕ) : ℝ)) ^ (2 * (k + s)) *
      (2 : ℝ) ^ (μ k s E / k) ≤ T0 ^ (μ k s E / k - 2 * ((k : ℝ) - 1))) :
    ∀ P : ℕ, 1 ≤ P → (J (k + s) k P : ℝ) ≤
      max (((⌈T0⌉₊ ^ k : ℕ) : ℝ) ^ (2 * (k + s))) (2 * Kmain k s C E) *
        (P : ℝ) ^ (μ k s E / k) := by
  set E' := μ k s E / k with hE'
  set D := E' - 2 * ((k : ℝ) - 1) with hDdef
  set P0 := ⌈T0⌉₊ ^ k with hP0
  set C' := max (((P0 : ℕ) : ℝ) ^ (2 * (k + s))) (2 * Kmain k s C E) with hC'
  have hKm : 0 ≤ Kmain k s C E := by unfold Kmain; positivity
  have hE'0 : 0 ≤ E' := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have : 0 ≤ μ k s E := by
      unfold μ; exact add_nonneg (by positivity) (mul_nonneg (by linarith) hE)
    rw [hE']; positivity
  have hC'0 : 0 ≤ C' := le_trans (by positivity) (le_max_left _ _)
  intro P
  induction P using Nat.strong_induction_on with
  | _ P ih =>
  intro hP
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  rcases le_or_gt P P0 with hsmall | hbig
  · -- trivial range
    have h1 : (J (k + s) k P : ℝ) ≤ (P : ℝ) ^ (2 * (k + s)) := by exact_mod_cast J_le _ _ _
    have h2 : (P : ℝ) ^ (2 * (k + s)) ≤ ((P0 : ℕ) : ℝ) ^ (2 * (k + s)) :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hsmall) _
    have h3 : (1 : ℝ) ≤ (P : ℝ) ^ E' := Real.one_le_rpow hPr hE'0
    calc (J (k + s) k P : ℝ) ≤ ((P0 : ℕ) : ℝ) ^ (2 * (k + s)) := h1.trans h2
      _ ≤ C' := le_max_left _ _
      _ = C' * 1 := (mul_one _).symm
      _ ≤ C' * (P : ℝ) ^ E' := mul_le_mul_of_nonneg_left h3 hC'0
  -- large range
  obtain ⟨p, hp, hkp, hPp, htp, hpt⟩ := exists_good_prime (by omega : 1 ≤ k) hP
  set t : ℝ := (P : ℝ) ^ ((k : ℝ)⁻¹) with ht
  have hk0 : k ≠ 0 := by omega
  have hx : (P : ℝ) = t ^ k := (Real.rpow_inv_natCast_pow (by positivity) hk0).symm
  have ht1 : 1 ≤ t := Real.one_le_rpow hPr (by positivity)
  have ht0 : 0 < t := by linarith
  have htT : T0 ≤ t := by
    have hc : (⌈T0⌉₊ : ℝ) < t := by
      by_contra hcon
      push Not at hcon
      have : (P : ℝ) ≤ ((⌈T0⌉₊ : ℕ) : ℝ) ^ k := by
        rw [hx]; exact pow_le_pow_left₀ ht0.le hcon k
      have : P ≤ P0 := by rw [hP0]; exact_mod_cast this
      omega
    exact (Nat.le_ceil T0).trans hc.le
  have hpc : (p : ℝ) ≤ (2 * ((k : ℝ) + 2)) * t := hpt
  set Q := P / p + 1 with hQdef
  have hQ1 : 1 ≤ Q := by rw [hQdef]; exact Nat.le_add_left 1 _
  have hQP : Q < P := by
    have hp3 : 3 ≤ p := by omega
    have hP2 : 2 ≤ P := by
      have : 1 ≤ P0 := Nat.one_le_pow _ _ (Nat.lt_of_lt_of_le zero_lt_one (by
        have : (1 : ℝ) ≤ (⌈T0⌉₊ : ℝ) := le_trans hT0 (Nat.le_ceil T0)
        exact_mod_cast this))
      omega
    have : P / p ≤ P / 3 := Nat.div_le_div_left hp3 (by norm_num)
    rw [hQdef]; omega
  have hQ : (Q : ℝ) ≤ 2 * t ^ (k - 1) := q_bound hk ht1 hx htp
  have hos : (J (k + s) k P : ℝ) ≤
      4 * ((p.choose (k - 1) : ℕ) : ℝ) ^ 2 * ((((k - 1 : ℕ) : ℝ)) ^ (2 * (k + s)) *
        (J (k + s) k Q : ℝ)) +
      16 * ((k + s : ℕ) : ℝ) ^ (2 * k) * ((p : ℝ) ^ (2 * s - 1) * ((p : ℝ) *
        ((P : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2)) * (J s k Q : ℝ)))) := by
    have := one_step2 hp (by omega) hkp hPp hs
    rw [← hQdef] at this
    exact_mod_cast this
  have hmain := main_part hk hs hC hE hJ hQ1 ht0 hx hQ hpc
  have htE : t ^ (μ k s E) = (P : ℝ) ^ E' := by
    rw [ht, ← Real.rpow_mul (by positivity), hE']
    congr 1
    field_simp
  rw [htE] at hmain
  -- the bad part
  have hIH := ih Q hQP hQ1
  have hch : ((p.choose (k - 1) : ℕ) : ℝ) ≤ (2 * ((k : ℝ) + 2)) ^ (k - 1) * t ^ (k - 1) := by
    have : p.choose (k - 1) ≤ p ^ (k - 1) := Nat.choose_le_pow p (k - 1)
    calc ((p.choose (k - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ (k - 1) := by exact_mod_cast this
      _ ≤ ((2 * ((k : ℝ) + 2)) * t) ^ (k - 1) := pow_le_pow_left₀ (by positivity) hpc _
      _ = _ := by rw [mul_pow]
  have hQE : (Q : ℝ) ^ E' ≤ (2 : ℝ) ^ E' * t ^ (((k : ℝ) - 1) * E') := by
    have h2 : (Q : ℝ) ^ E' ≤ (2 * t ^ (k - 1)) ^ E' := Real.rpow_le_rpow (by positivity) hQ hE'0
    have h3 : (2 * t ^ (k - 1) : ℝ) ^ E' = (2 : ℝ) ^ E' * t ^ (((k : ℝ) - 1) * E') := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      congr 2
      rw [Nat.cast_sub (by omega)]; simp
    rwa [h3] at h2
  have htD : T0 ^ D ≤ t ^ D := Real.rpow_le_rpow (by linarith) htT hDpos.le
  have hsplit : t ^ ((2 * (k - 1) : ℕ) : ℝ) * t ^ (((k : ℝ) - 1) * E') * t ^ D =
      (P : ℝ) ^ E' := by
    rw [← Real.rpow_add ht0, ← Real.rpow_add ht0, ← htE, hE']
    congr 1
    rw [hDdef, hE']
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    field_simp
    ring
  have hbad : 4 * ((p.choose (k - 1) : ℕ) : ℝ) ^ 2 * ((((k - 1 : ℕ) : ℝ)) ^ (2 * (k + s)) *
        (J (k + s) k Q : ℝ)) ≤ C' / 2 * (P : ℝ) ^ E' := by
    set Kb := 8 * (2 * ((k : ℝ) + 2)) ^ (2 * (k - 1)) * (((k - 1 : ℕ) : ℝ)) ^ (2 * (k + s)) *
      (2 : ℝ) ^ E' with hKbdef
    have hKb0 : 0 ≤ Kb := by positivity
    have hch2 : ((p.choose (k - 1) : ℕ) : ℝ) ^ 2 ≤
        (2 * ((k : ℝ) + 2)) ^ (2 * (k - 1)) * t ^ ((2 * (k - 1) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      calc ((p.choose (k - 1) : ℕ) : ℝ) ^ 2 ≤ ((2 * ((k : ℝ) + 2)) ^ (k - 1) * t ^ (k - 1)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hch 2
        _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
    have hJQ' : (J (k + s) k Q : ℝ) ≤ C' * ((2 : ℝ) ^ E' * t ^ (((k : ℝ) - 1) * E')) :=
      hIH.trans (mul_le_mul_of_nonneg_left hQE hC'0)
    have hpos1 : (0 : ℝ) ≤ (((k - 1 : ℕ) : ℝ)) ^ (2 * (k + s)) := by positivity
    calc 4 * ((p.choose (k - 1) : ℕ) : ℝ) ^ 2 * ((((k - 1 : ℕ) : ℝ)) ^ (2 * (k + s)) *
          (J (k + s) k Q : ℝ))
        ≤ 4 * ((2 * ((k : ℝ) + 2)) ^ (2 * (k - 1)) * t ^ ((2 * (k - 1) : ℕ) : ℝ)) *
          ((((k - 1 : ℕ) : ℝ)) ^ (2 * (k + s)) *
            (C' * ((2 : ℝ) ^ E' * t ^ (((k : ℝ) - 1) * E')))) := by gcongr
      _ = Kb / 2 * C' * (t ^ ((2 * (k - 1) : ℕ) : ℝ) * t ^ (((k : ℝ) - 1) * E')) := by
          rw [hKbdef]; ring
      _ ≤ T0 ^ D / 2 * C' * (t ^ ((2 * (k - 1) : ℕ) : ℝ) * t ^ (((k : ℝ) - 1) * E')) := by
          gcongr
      _ ≤ t ^ D / 2 * C' * (t ^ ((2 * (k - 1) : ℕ) : ℝ) * t ^ (((k : ℝ) - 1) * E')) := by
          gcongr
      _ = C' / 2 * (t ^ ((2 * (k - 1) : ℕ) : ℝ) * t ^ (((k : ℝ) - 1) * E') * t ^ D) := by ring
      _ = C' / 2 * (P : ℝ) ^ E' := by rw [hsplit]
  have hKmC : Kmain k s C E ≤ C' / 2 := by
    have := le_max_right (((P0 : ℕ) : ℝ) ^ (2 * (k + s))) (2 * Kmain k s C E)
    rw [← hC'] at this; linarith
  have hPE : (0 : ℝ) ≤ (P : ℝ) ^ E' := by positivity
  calc (J (k + s) k P : ℝ) ≤ _ := hos
    _ ≤ C' / 2 * (P : ℝ) ^ E' + Kmain k s C E * (P : ℝ) ^ E' := add_le_add hbad hmain
    _ ≤ C' / 2 * (P : ℝ) ^ E' + C' / 2 * (P : ℝ) ^ E' := by gcongr
    _ = C' * (P : ℝ) ^ E' := by ring

/-! ## The iteration -/

/-- `η_m = (1 − 1/k)^m · k(k−1)/2`. -/
noncomputable def eta2 (k m : ℕ) : ℝ := (1 - 1 / (k : ℝ)) ^ m * ((k : ℝ) * ((k : ℝ) - 1) / 2)

/-- The exponent `2s − k(k+1)/2 + η_m`, `s = k + mk`. -/
noncomputable def expo2 (k m : ℕ) : ℝ :=
  2 * ((k + m * k : ℕ) : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eta2 k m

/-- `T₀ = (4k)^{20}`. -/
noncomputable def T0 (k : ℕ) : ℝ := (4 * (k : ℝ)) ^ 20

/-- The constants. -/
noncomputable def Cv2 (k : ℕ) : ℕ → ℝ
  | 0 => k.factorial
  | m + 1 => max ((((⌈T0 k⌉₊ ^ k : ℕ) : ℝ)) ^ (2 * (k + (k + m * k))))
      (2 * Kmain k (k + m * k) (Cv2 k m) (expo2 k m))

lemma eta2_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) : eta2 k m ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 0 ≤ 1 - 1 / (k : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have h2 : 1 - 1 / (k : ℝ) ≤ 1 := by have : 0 ≤ 1 / (k : ℝ) := by positivity
                                      linarith
  unfold eta2
  have := pow_le_one₀ h1 h2 (n := m)
  have h3 : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by nlinarith
  nlinarith

/-- Bernoulli: `η_m ≥ k(k−1)/2 − m(k−1)/2`. -/
lemma eta2_ge {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (k : ℝ) * ((k : ℝ) - 1) / 2 - (m : ℝ) * ((k : ℝ) - 1) / 2 ≤ eta2 k m := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / (k : ℝ)) by
    have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith) m
  have e : 1 + -(1 / (k : ℝ)) = 1 - 1 / (k : ℝ) := by ring
  rw [e] at hb
  unfold eta2
  have h3 : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by nlinarith
  have := mul_le_mul_of_nonneg_right hb h3
  have e2 : (1 + (m : ℝ) * -(1 / (k : ℝ))) * ((k : ℝ) * ((k : ℝ) - 1) / 2) =
      (k : ℝ) * ((k : ℝ) - 1) / 2 - (m : ℝ) * ((k : ℝ) - 1) / 2 := by
    field_simp; ring
  linarith

lemma expo2_eq {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    μ k (k + m * k) (expo2 k m) / k = expo2 k (m + 1) := by
  have hk0 : (k : ℝ) ≠ 0 := by have : (2 : ℝ) ≤ k := by exact_mod_cast hk
                               positivity
  have hsucc : eta2 k (m + 1) = (1 - 1 / (k : ℝ)) * eta2 k m := by
    unfold eta2; rw [pow_succ]; ring
  unfold μ expo2
  rw [hsucc]
  generalize eta2 k m = η
  rw [Nat.cast_add, Nn_cast]
  push_cast
  field_simp
  ring

lemma expo2_nonneg {k : ℕ} (hk : 2 ≤ k) (m : ℕ) : 0 ≤ expo2 k m := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have := eta2_ge hk m
  unfold expo2
  push_cast
  have hm : (0 : ℝ) ≤ m := by positivity
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **VMVT with geometric decay from the start.** -/
theorem vmvt2 {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    0 < Cv2 k m ∧ ∀ P : ℕ, 1 ≤ P → (J (k + m * k) k P : ℝ) ≤ Cv2 k m * (P : ℝ) ^ (expo2 k m) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  induction m with
  | zero =>
    refine ⟨by simp [Cv2]; positivity, fun P hP => ?_⟩
    have h := J_le_diag (le_refl k) P
    simp only [zero_mul, add_zero, Cv2]
    have he : expo2 k 0 = (k : ℝ) := by simp [expo2, eta2]; ring
    rw [he, Real.rpow_natCast]
    exact_mod_cast h
  | succ m ih =>
    obtain ⟨hC, hJ⟩ := ih
    set s := k + m * k with hsdef
    have hs : 1 ≤ s := by omega
    have hE := expo2_nonneg hk m
    have heq := expo2_eq hk m
    rw [← hsdef] at heq
    have hT0 : 1 ≤ T0 k := by unfold T0; exact one_le_pow₀ (by linarith)
    -- the margin `D = E' − 2(k−1)`
    set E' := expo2 k (m + 1) with hE'
    have hEge : 2 * ((k : ℝ) * ((m : ℝ) + 2)) - (k : ℝ) - ((m : ℝ) + 1) * ((k : ℝ) - 1) / 2 ≤ E' := by
      have := eta2_ge hk (m + 1)
      rw [hE']; unfold expo2
      push_cast at this ⊢
      nlinarith
    have hEle : E' ≤ 2 * ((k : ℝ) * ((m : ℝ) + 2)) := by
      have := eta2_le hk (m + 1)
      rw [hE']; unfold expo2
      push_cast
      nlinarith
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hDpos : 0 < E' - 2 * ((k : ℝ) - 1) := by nlinarith
    have hKb : 8 * (2 * ((k : ℝ) + 2)) ^ (2 * (k - 1)) * (((k - 1 : ℕ) : ℝ)) ^ (2 * (k + s)) *
        (2 : ℝ) ^ E' ≤ T0 k ^ (E' - 2 * ((k : ℝ) - 1)) := by
      set B : ℝ := 4 * (k : ℝ) with hB
      have hB8 : (8 : ℝ) ≤ B := by rw [hB]; linarith
      have hB1 : (1 : ℝ) ≤ B := by linarith
      have hB0 : (0 : ℝ) ≤ B := by linarith
      have h1 : (8 : ℝ) ≤ B ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
      have h2 : (2 * ((k : ℝ) + 2)) ^ (2 * (k - 1)) ≤ B ^ ((2 * (k - 1) : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; exact pow_le_pow_left₀ (by positivity) (by rw [hB]; linarith) _
      have h3 : (((k - 1 : ℕ) : ℝ)) ^ (2 * (k + s)) ≤ B ^ ((2 * (k + s) : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        apply pow_le_pow_left₀ (by positivity)
        have : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
        rw [hB]; linarith
      have h4 : (2 : ℝ) ^ E' ≤ B ^ E' := Real.rpow_le_rpow (by norm_num) (by linarith)
        (expo2_nonneg hk (m + 1))
      have hprod : 8 * (2 * ((k : ℝ) + 2)) ^ (2 * (k - 1)) * (((k - 1 : ℕ) : ℝ)) ^ (2 * (k + s)) *
          (2 : ℝ) ^ E' ≤ B ^ ((2 : ℝ) + ((2 * (k - 1) : ℕ) : ℝ) + ((2 * (k + s) : ℕ) : ℝ) + E') := by
        rw [Real.rpow_add (by linarith), Real.rpow_add (by linarith), Real.rpow_add (by linarith)]
        gcongr
      refine hprod.trans ?_
      have hT : T0 k ^ (E' - 2 * ((k : ℝ) - 1)) = B ^ (20 * (E' - 2 * ((k : ℝ) - 1))) := by
        rw [T0, ← hB, ← Real.rpow_natCast, ← Real.rpow_mul hB0]; norm_num
      rw [hT]
      apply Real.rpow_le_rpow_of_exponent_le hB1
      have hsr : (s : ℝ) = (k : ℝ) * ((m : ℝ) + 1) := by rw [hsdef]; push_cast; ring
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
      rw [hsr]
      nlinarith
    have hstep := step_real2 hk hs hC hE hJ hT0 (by rw [heq]; exact hDpos) (by rw [heq]; exact hKb)
    have hCv : Cv2 k (m + 1) = max ((((⌈T0 k⌉₊ ^ k : ℕ) : ℝ)) ^ (2 * (k + s)))
        (2 * Kmain k s (Cv2 k m) (expo2 k m)) := rfl
    refine ⟨?_, fun P hP => ?_⟩
    · rw [hCv]
      have : 0 < Kmain k s (Cv2 k m) (expo2 k m) := by unfold Kmain; positivity
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hlen : k + (m + 1) * k = k + s := by rw [hsdef]; ring
    rw [hlen, hCv, ← heq]
    exact hstep P hP

/-! ## Explicit constants -/

lemma Cv2_ge_one {k : ℕ} (hk : 2 ≤ k) (m : ℕ) : 1 ≤ Cv2 k m := by
  cases m with
  | zero =>
    simp only [Cv2]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  | succ m =>
    simp only [Cv2]
    refine le_trans ?_ (le_max_left _ _)
    apply one_le_pow₀
    have : 1 ≤ ⌈T0 k⌉₊ ^ k := Nat.one_le_pow _ _ (by
      have h1 : (1 : ℝ) ≤ T0 k := by
        unfold T0; exact one_le_pow₀ (by have : (2 : ℝ) ≤ k := by exact_mod_cast hk
                                         linarith)
      have := Nat.le_ceil (T0 k)
      have h2 : (1 : ℝ) ≤ ⌈T0 k⌉₊ := le_trans h1 this
      exact_mod_cast h2)
    exact_mod_cast this

lemma expo2_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) : expo2 k m ≤ 2 * ((k + m * k : ℕ) : ℝ) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have := eta2_le hk m
  unfold expo2
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **Explicit constants.** `C_m ≤ (8(k+2))^{40k²(m+1) + g(m)}`. -/
theorem Cv2_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    Cv2 k m ≤ (8 * ((k : ℝ) + 2)) ^ (40 * k ^ 2 * (m + 1) + gexp k m) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set Q : ℝ := 8 * ((k : ℝ) + 2) with hQ
  have hQ1 : (1 : ℝ) ≤ Q := by rw [hQ]; nlinarith
  have hkQ : (k : ℝ) ≤ Q := by rw [hQ]; nlinarith
  induction m with
  | zero =>
    simp only [Cv2, gexp]
    calc (k.factorial : ℝ) ≤ ((k ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow k
      _ = (k : ℝ) ^ k := by push_cast; ring
      _ ≤ Q ^ k := pow_le_pow_left₀ (by positivity) hkQ _
      _ ≤ Q ^ (40 * k ^ 2 * (0 + 1) + k) := pow_le_pow_right₀ hQ1 (by omega)
  | succ m ih =>
    set s := k + m * k with hsdef
    have hC1 := Cv2_ge_one hk m
    show max ((((⌈T0 k⌉₊ ^ k : ℕ) : ℝ)) ^ (2 * (k + s)))
      (2 * Kmain k s (Cv2 k m) (expo2 k m)) ≤ Q ^ (40 * k ^ 2 * (m + 1 + 1) + gexp k (m + 1))
    have hs : (s : ℝ) = (k : ℝ) * ((m : ℝ) + 1) := by rw [hsdef]; push_cast; ring
    apply max_le
    · -- the trivial range
      have hceil : ⌈T0 k⌉₊ = (4 * k) ^ 20 := by
        unfold T0
        rw [show (4 * (k : ℝ)) ^ 20 = (((4 * k) ^ 20 : ℕ) : ℝ) by push_cast; ring]
        exact Nat.ceil_natCast _
      rw [hceil]
      have h4 : ((((4 * k) ^ 20) ^ k : ℕ) : ℝ) ≤ Q ^ (20 * k) := by
        push_cast
        rw [← pow_mul, show 20 * k = 20 * k from rfl]
        exact pow_le_pow_left₀ (by positivity) (by rw [hQ]; linarith) _
      have hks : 2 * (k + s) ≤ 2 * k * (m + 2) := by rw [hsdef]; ring_nf; omega
      calc ((((4 * k) ^ 20) ^ k : ℕ) : ℝ) ^ (2 * (k + s)) ≤ (Q ^ (20 * k)) ^ (2 * (k + s)) :=
            pow_le_pow_left₀ (by positivity) h4 _
        _ = Q ^ (20 * k * (2 * (k + s))) := by rw [← pow_mul]
        _ ≤ Q ^ (40 * k ^ 2 * (m + 1 + 1) + gexp k (m + 1)) := by
            apply pow_le_pow_right₀ hQ1
            have : 20 * k * (2 * (k + s)) ≤ 40 * k ^ 2 * (m + 1 + 1) := by
              calc 20 * k * (2 * (k + s)) ≤ 20 * k * (2 * k * (m + 2)) :=
                    Nat.mul_le_mul_left _ hks
                _ = 40 * k ^ 2 * (m + 1 + 1) := by ring
            omega
    · -- the main part: `2·K_main ≤ C_m·Q^{inc+1}`
      have hks : ((k + s : ℕ) : ℝ) ≤ Q ^ (m + 2) := by
        have e : ((k + s : ℕ) : ℝ) = (k : ℝ) * ((m : ℝ) + 2) := by push_cast; rw [hs]; ring
        rw [e, pow_succ]
        rw [mul_comm]
        apply mul_le_mul _ hkQ (by positivity) (by positivity)
        calc (m : ℝ) + 2 ≤ 2 ^ (m + 1) := by
              exact_mod_cast add_two_le_two_pow m
          _ ≤ Q ^ (m + 1) := pow_le_pow_left₀ (by norm_num) (by linarith) _
      have hfac : (k.factorial : ℝ) ≤ Q ^ k := by
        calc (k.factorial : ℝ) ≤ ((k ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow k
          _ = (k : ℝ) ^ k := by push_cast; ring
          _ ≤ Q ^ k := pow_le_pow_left₀ (by positivity) hkQ _
      have hc : 2 * ((k : ℝ) + 2) ≤ Q := by rw [hQ]; nlinarith
      have hNn : Nn k s ≤ 2 * k * (m + 1) + k ^ 2 := by
        unfold Nn
        have : k * (k - 1) / 2 ≤ k ^ 2 := (Nat.div_le_self _ _).trans (by
          rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
        rw [hsdef]; nlinarith
      have hE := expo2_le hk m
      have hEnn := expo2_nonneg hk m
      have h2E : (2 : ℝ) ^ expo2 k m ≤ Q ^ (2 * k * (m + 1)) := by
        calc (2 : ℝ) ^ expo2 k m ≤ Q ^ expo2 k m :=
              Real.rpow_le_rpow (by norm_num) (by linarith) hEnn
          _ ≤ Q ^ ((2 * k * (m + 1) : ℕ) : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_le hQ1
              rw [← hsdef] at hE
              push_cast
              rw [hs] at hE; linarith
          _ = Q ^ (2 * k * (m + 1)) := Real.rpow_natCast _ _
      have hmain : Kmain k s (Cv2 k m) (expo2 k m) ≤
          Cv2 k m * Q ^ (1 + 2 * k * (m + 2) + k + (2 * k * (m + 1) + k ^ 2) + 2 * k * (m + 1)) := by
        unfold Kmain
        have hA : (16 : ℝ) ≤ Q := by rw [hQ]; linarith
        have hB : ((k + s : ℕ) : ℝ) ^ (2 * k) ≤ Q ^ (2 * k * (m + 2)) := by
          rw [pow_mul' Q]; exact pow_le_pow_left₀ (by positivity) hks _
        have hD : (2 * ((k : ℝ) + 2)) ^ Nn k s ≤ Q ^ (2 * k * (m + 1) + k ^ 2) :=
          (pow_le_pow_left₀ (by positivity) hc _).trans (pow_le_pow_right₀ hQ1 hNn)
        have hC0 : 0 ≤ Cv2 k m := by linarith
        calc 16 * ((k + s : ℕ) : ℝ) ^ (2 * k) *
              ((k.factorial : ℝ) * (2 * ((k : ℝ) + 2)) ^ Nn k s) * Cv2 k m * (2 : ℝ) ^ expo2 k m
            ≤ Q * Q ^ (2 * k * (m + 2)) * (Q ^ k * Q ^ (2 * k * (m + 1) + k ^ 2)) *
              Cv2 k m * Q ^ (2 * k * (m + 1)) := by gcongr
          _ = _ := by ring
      have hg : gexp k (m + 1) = gexp k m + (1 + 2 * k * (m + 2) + k + (2 * k * (m + 1) + k ^ 2) +
          2 * k * (m + 1)) + 1 := by
        simp only [gexp]; ring
      set inc := 1 + 2 * k * (m + 2) + k + (2 * k * (m + 1) + k ^ 2) + 2 * k * (m + 1)
      have hQg : Cv2 k m * Q ^ inc ≤ Q ^ (40 * k ^ 2 * (m + 1) + gexp k m) * Q ^ inc :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      have hQ2 : (2 : ℝ) ≤ Q := by linarith
      have hfin : Q ^ (40 * k ^ 2 * (m + 1) + gexp k m) * Q ^ inc * Q ≤
          Q ^ (40 * k ^ 2 * (m + 1 + 1) + gexp k (m + 1)) := by
        rw [← pow_add, ← pow_succ]
        apply pow_le_pow_right₀ hQ1
        rw [hg]; ring_nf; omega
      have hP : 0 ≤ Q ^ (40 * k ^ 2 * (m + 1) + gexp k m) * Q ^ inc := by positivity
      calc 2 * Kmain k s (Cv2 k m) (expo2 k m) ≤ 2 * (Cv2 k m * Q ^ inc) := by linarith
        _ ≤ 2 * (Q ^ (40 * k ^ 2 * (m + 1) + gexp k m) * Q ^ inc) := by linarith
        _ ≤ Q ^ (40 * k ^ 2 * (m + 1) + gexp k m) * Q ^ inc * Q := by nlinarith
        _ ≤ _ := hfin

end VinoRec2
