/-
# Vinogradov's mean value theorem with explicit constants (round 207)

Plain statements.
* `Cvm k m` is the constant produced by `m` Karatsuba steps: `C_0 = k!` and
  `C_{m+1} = K_bad + K_main(C_m)`, exactly as in the proof of `vmvt_iter` (round 202).
* `vmvt_explicit`: `J_{k+mk,k}(P) ≤ C_m·P^{expo k m}` for all `P ≥ 1`, with this explicit `C_m`.
* `Cvm_le`: `C_m ≤ Q^{g(m)}` with `Q = 8(k+2)`, `g(0) = k` and
  `g(m+1) = g(m) + 6k(m+1) + k² + 3k + 2`, so `g(m) ≈ 3k·m²`.

Layer II needs the constant to grow slowly enough that its `(2ℓ²)`-th root, with `ℓ = k(m+1)`,
tends to 1. Here `log C_m / ℓ² ≈ 3·log Q / k → 0`.
-/
import VinoRec

open Finset

namespace VinoRec

open Vinogradov

/-- The explicit VMVT constant after `m` steps. -/
noncomputable def Cvm (k : ℕ) : ℕ → ℝ
  | 0 => k.factorial
  | m + 1 => Kbad k (k + m * k) + Kmain k (k + m * k) (Cvm k m) (expo k m)

/-- **VMVT with explicit constant.** -/
theorem vmvt_explicit {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    0 < Cvm k m ∧ ∀ P : ℕ, 1 ≤ P → (J (k + m * k) k P : ℝ) ≤ Cvm k m * (P : ℝ) ^ (expo k m) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  induction m with
  | zero =>
    refine ⟨by simp [Cvm]; positivity, fun P hP => ?_⟩
    have h := J_le_diag (le_refl k) P
    simp only [zero_mul, add_zero, Cvm]
    have he : expo k 0 = (k : ℝ) := by simp [expo, eta]; ring
    rw [he, Real.rpow_natCast]
    exact_mod_cast h
  | succ m ih =>
    obtain ⟨hC, hJ⟩ := ih
    set s := k + m * k with hsdef
    have hs : 1 ≤ s := by omega
    have hstep := step_real hk hs hC (expo_nonneg hk m) hJ
    have hCv : Cvm k (m + 1) = Kbad k s + Kmain k s (Cvm k m) (expo k m) := rfl
    refine ⟨?_, fun P hP => ?_⟩
    · rw [hCv]
      have : 0 < Kmain k s (Cvm k m) (expo k m) := by unfold Kmain; positivity
      have : 0 ≤ Kbad k s := by unfold Kbad; positivity
      linarith
    have hlen : k + (m + 1) * k = k + s := by rw [hsdef]; ring
    rw [hlen, hCv]
    have hexp := expo_step hk m
    rw [← hexp]
    exact hstep P hP

/-- `η_m ≤ k(k+1)/2`. -/
lemma eta_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) : eta k m ≤ (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 0 ≤ 1 - 1 / (k : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have h2 : 1 - 1 / (k : ℝ) ≤ 1 := sub_le_self _ (by positivity)
  induction m with
  | zero => simp only [eta]; nlinarith
  | succ m ih =>
    rw [eta]
    apply max_le
    · have := eta_nonneg hk m
      nlinarith
    · have : 0 ≤ 2 * (((k + m * k : ℕ) : ℝ) + 1) / k := by positivity
      linarith

/-- The VMVT exponent is at most `2s`. -/
lemma expo_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) : expo k m ≤ 2 * ((k + m * k : ℕ) : ℝ) := by
  unfold expo; have := eta_le hk m; linarith

lemma add_two_le_two_pow (m : ℕ) : m + 2 ≤ 2 ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; omega

/-- The growth exponent `g`. -/
def gexp (k : ℕ) : ℕ → ℕ
  | 0 => k
  | m + 1 => gexp k m + 6 * k * (m + 1) + k ^ 2 + 3 * k + 2

lemma Cvm_ge_one {k : ℕ} (hk : 2 ≤ k) (m : ℕ) : 1 ≤ Cvm k m := by
  induction m with
  | zero => simp only [Cvm]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  | succ m ih =>
    show 1 ≤ Kbad k (k + m * k) + Kmain k (k + m * k) (Cvm k m) (expo k m)
    have hb : 0 ≤ Kbad k (k + m * k) := by unfold Kbad; positivity
    have hm : 1 ≤ Kmain k (k + m * k) (Cvm k m) (expo k m) := by
      unfold Kmain
      have h1 : (1 : ℝ) ≤ ((k + (k + m * k) : ℕ) : ℝ) ^ (2 * k) :=
        one_le_pow₀ (by exact_mod_cast (show 1 ≤ k + (k + m * k) by omega))
      have h2 : (1 : ℝ) ≤ (k.factorial : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
      have h3 : (1 : ℝ) ≤ (2 * ((k : ℝ) + 2)) ^ Nn k (k + m * k) := one_le_pow₀ (by
        have : (0 : ℝ) ≤ k := by positivity
        linarith)
      have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ expo k m := Real.one_le_rpow (by norm_num) (expo_nonneg hk m)
      have h5 : (1 : ℝ) ≤ (k.factorial : ℝ) * (2 * ((k : ℝ) + 2)) ^ Nn k (k + m * k) :=
        one_le_mul_of_one_le_of_one_le h2 h3
      calc (1 : ℝ) ≤ 16 * 1 * 1 * 1 * 1 := by norm_num
        _ ≤ _ := by gcongr
    linarith

set_option maxHeartbeats 1600000 in
/-- **Explicit growth of the VMVT constant.** `C_m ≤ (8(k+2))^{g(m)}`. -/
theorem Cvm_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    Cvm k m ≤ (8 * ((k : ℝ) + 2)) ^ gexp k m := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set Q : ℝ := 8 * ((k : ℝ) + 2) with hQ
  have hQ1 : (1 : ℝ) ≤ Q := by rw [hQ]; nlinarith
  have hQ32 : (32 : ℝ) ≤ Q := by rw [hQ]; nlinarith
  have hkQ : (k : ℝ) ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  induction m with
  | zero =>
    simp only [Cvm, gexp]
    calc (k.factorial : ℝ) ≤ ((k ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow k
      _ = (k : ℝ) ^ k := by push_cast; ring
      _ ≤ Q ^ k := pow_le_pow_left₀ (by positivity) hkQ _
  | succ m ih =>
    set s := k + m * k with hsdef
    have hC1 := Cvm_ge_one hk m
    show Kbad k s + Kmain k s (Cvm k m) (expo k m) ≤ Q ^ gexp k (m + 1)
    have hs : (s : ℝ) = (k : ℝ) * ((m : ℝ) + 1) := by rw [hsdef]; push_cast; ring
    -- bounds on the pieces, all as powers of Q
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
    have hE := expo_le hk m
    have hEnn := expo_nonneg hk m
    have h2E : (2 : ℝ) ^ expo k m ≤ Q ^ (2 * k * (m + 1)) := by
      calc (2 : ℝ) ^ expo k m ≤ Q ^ expo k m := Real.rpow_le_rpow (by norm_num) (by linarith) hEnn
        _ ≤ Q ^ ((2 * k * (m + 1) : ℕ) : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le hQ1
            rw [← hsdef] at hE
            push_cast
            rw [hs] at hE; linarith
        _ = Q ^ (2 * k * (m + 1)) := Real.rpow_natCast _ _
    have hmain : Kmain k s (Cvm k m) (expo k m) ≤
        Cvm k m * Q ^ (1 + 2 * k * (m + 2) + k + (2 * k * (m + 1) + k ^ 2) + 2 * k * (m + 1)) := by
      unfold Kmain
      have hA : (16 : ℝ) ≤ Q := by linarith
      have hB : ((k + s : ℕ) : ℝ) ^ (2 * k) ≤ Q ^ (2 * k * (m + 2)) := by
        rw [pow_mul' Q]; exact pow_le_pow_left₀ (by positivity) hks _
      have hD : (2 * ((k : ℝ) + 2)) ^ Nn k s ≤ Q ^ (2 * k * (m + 1) + k ^ 2) :=
        (pow_le_pow_left₀ (by positivity) hc _).trans (pow_le_pow_right₀ hQ1 hNn)
      calc 16 * ((k + s : ℕ) : ℝ) ^ (2 * k) * ((k.factorial : ℝ) * (2 * ((k : ℝ) + 2)) ^ Nn k s) *
            Cvm k m * (2 : ℝ) ^ expo k m
          ≤ Q * Q ^ (2 * k * (m + 2)) * (Q ^ k * Q ^ (2 * k * (m + 1) + k ^ 2)) *
            Cvm k m * Q ^ (2 * k * (m + 1)) := by gcongr
        _ = _ := by ring
    have hbad : Kbad k s ≤ Cvm k m * Q ^ (1 + 2 * k * (m + 2) + k + (2 * k * (m + 1) + k ^ 2) +
        2 * k * (m + 1)) := by
      unfold Kbad
      have hk2 : ((k - 1 : ℕ) : ℝ) * 2 ≤ Q := by
        have : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
        linarith
      have hb1 : (2 * ((k : ℝ) + 2)) ^ (k - 1) ≤ Q ^ k :=
        (pow_le_pow_left₀ (by positivity) hc _).trans (pow_le_pow_right₀ hQ1 (Nat.sub_le _ _))
      have hb2 : (((k - 1 : ℕ) : ℝ) * 2) ^ (k + s) ≤ Q ^ (k + s) := pow_le_pow_left₀ (by positivity) hk2 _
      have hks' : k + s ≤ k * (m + 2) := by rw [hsdef]; ring_nf; omega
      calc 2 * ((2 * ((k : ℝ) + 2)) ^ (k - 1) * (((k - 1 : ℕ) : ℝ) * 2) ^ (k + s)) ^ 2
          ≤ Q * (Q ^ k * Q ^ (k * (m + 2))) ^ 2 := by
            gcongr
            · linarith
            · exact hb2.trans (pow_le_pow_right₀ hQ1 hks')
        _ = 1 * Q ^ (1 + 2 * k + 2 * k * (m + 2)) := by
            rw [← pow_add, ← pow_mul, pow_add, pow_add, pow_one]; ring_nf
        _ ≤ Cvm k m * Q ^ (1 + 2 * k * (m + 2) + k + (2 * k * (m + 1) + k ^ 2) + 2 * k * (m + 1)) := by
            apply mul_le_mul hC1 (pow_le_pow_right₀ hQ1 (by nlinarith)) (by positivity) (by linarith)
    have hg : gexp k (m + 1) = gexp k m + (1 + 2 * k * (m + 2) + k + (2 * k * (m + 1) + k ^ 2) +
        2 * k * (m + 1)) + 1 := by
      simp only [gexp]; ring
    rw [hg, pow_succ, pow_add]
    set inc := 1 + 2 * k * (m + 2) + k + (2 * k * (m + 1) + k ^ 2) + 2 * k * (m + 1)
    have hQg : Cvm k m * Q ^ inc ≤ Q ^ gexp k m * Q ^ inc :=
      mul_le_mul_of_nonneg_right ih (by positivity)
    have hP : 0 ≤ Q ^ gexp k m * Q ^ inc := by positivity
    calc Kbad k s + Kmain k s (Cvm k m) (expo k m) ≤ 2 * (Cvm k m * Q ^ inc) := by linarith
      _ ≤ 2 * (Q ^ gexp k m * Q ^ inc) := by linarith
      _ ≤ Q ^ gexp k m * Q ^ inc * Q := by nlinarith

end VinoRec
