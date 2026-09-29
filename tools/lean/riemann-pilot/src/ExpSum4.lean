/-
# Layer II, step (F): the block bound (round 206)

Plain statement (`block_bound`). Suppose:
* the mean value satisfies `J_{ℓ,K}(M) ≤ C·M^{2ℓ − K(K+1)/2 + η}`;
* `2M² ≤ N`;
* a good coordinate `r ≤ K` satisfies `|t|·ℓ·M^r ≤ π·r·N^r`.

Then
  `|Σ_{N<n≤2N} n^{−it}| ≤ N·(C²·3^K·ℓ^{2K}·M^{2η}·W)^{1/(2ℓ²)} + 2|t|N(M²/N)^{K+1} + 2M²`,
with the explicit saving
  `W = 1/(ℓM^r) + 2πr(2N)^r(1 + log(ℓM^r)) / (|t|ℓ²M^{2r})`.

Everything is explicit, so the choice of parameters becomes real analysis (step G).
Assembled from `stepE` (round 205), `bilinear_bound`, `oneD_bound` and `oneD_trivial`
(round 204).
-/
import ExpSum3

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder

lemma oneD_three (α : ℝ) (L : ℕ) (hL : 1 ≤ L) :
    ∑ z ∈ Icc (-(L : ℤ)) L, ‖inner α z L‖ ≤ 3 * (L : ℝ) ^ 2 := by
  refine (oneD_trivial α L L).trans ?_
  have : (1 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith

lemma prod_three_L (K M ℓ : ℕ) :
    ∏ j : Fin K, (3 * ((Lbox K M ℓ j : ℕ) : ℝ) ^ 2) =
      3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (K * (K + 1)) := by
  simp only [Lbox, Nat.cast_mul, Nat.cast_pow, mul_pow, Finset.prod_mul_distrib, prod_const,
    card_univ, Fintype.card_fin, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  have hs : ∑ j : Fin K, (j.val + 1) * 2 = K * (K + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (i + 1) * 2), ← Finset.sum_mul,
      Finset.sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one, add_mul,
      Finset.sum_range_id_mul_two]
    rcases K with _ | K
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  rw [hs]; ring

/-- The explicit saving factor of the good coordinate. -/
noncomputable def Wsave (t : ℝ) (N M ℓ r : ℕ) : ℝ :=
  1 / ((ℓ : ℝ) * (M : ℝ) ^ r) +
    2 * Real.pi * r * (2 * (N : ℝ)) ^ r * (1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ r)) /
      (|t| * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * r))

/-- The per-`n` saving `Φ`. -/
noncomputable def Phi (t C η : ℝ) (N M K ℓ r : ℕ) : ℝ :=
  (C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (2 * η) * Wsave t N M ℓ r) ^
    (((2 * ℓ ^ 2 : ℕ) : ℝ)⁻¹)

set_option maxHeartbeats 1600000 in
/-- **Per-`n` bound.** `|Σ_{a,b≤M} e(Σ_j α_j(n)(ab)^{j+1})| ≤ M²·Φ`. -/
theorem Bn_bound {t : ℝ} (ht : t ≠ 0) {N n M K ℓ r : ℕ} {C η : ℝ} (hC : 0 < C)
    (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ) (hr1 : 1 ≤ r) (hrK : r ≤ K)
    (hJ : (J ℓ K M : ℝ) ≤ C * (M : ℝ) ^ (2 * (ℓ : ℝ) - (K : ℝ) * ((K : ℝ) + 1) / 2 + η))
    (hn1 : N < n) (hn2 : n ≤ 2 * N)
    (hgood : |t| * ℓ * (M : ℝ) ^ r ≤ Real.pi * r * (N : ℝ) ^ r) :
    ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b)‖ ≤
      (M : ℝ) ^ 2 * Phi t C η N M K ℓ r := by
  have hπ := Real.pi_pos
  have htp : 0 < |t| := abs_pos.mpr ht
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hnN : (N : ℝ) < n := by exact_mod_cast hn1
  have hn2r : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn2
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  set j0 : Fin K := ⟨r - 1, by omega⟩ with hj0
  have hj0r : j0.val + 1 = r := by simp [hj0]; omega
  set α := alphaVec t n K with hα
  set L := Lbox K M ℓ j0 with hLdef
  have hLr : (L : ℝ) = ℓ * (M : ℝ) ^ r := by
    simp [hLdef, Lbox, hj0r]
  have hL1 : 1 ≤ L := by
    have : (1 : ℝ) ≤ L := by rw [hLr]; nlinarith [one_le_pow₀ hMr (n := r)]
    exact_mod_cast this
  have habsα : |α j0| = |t| / (2 * Real.pi * r * (n : ℝ) ^ r) := by
    have hj0r' : ((j0 : ℕ) : ℝ) + 1 = r := by exact_mod_cast hj0r
    simp only [hα, alphaVec, hj0r, hj0r']
    rw [abs_div, abs_of_pos (show (0 : ℝ) < (r : ℝ) * (n : ℝ) ^ r by positivity), abs_mul,
      abs_div, abs_pow, abs_neg, abs_one, one_pow, mul_one,
      abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)]
    field_simp
  have hα0 : α j0 ≠ 0 := by
    intro h; rw [h, abs_zero] at habsα
    have : 0 < |t| / (2 * Real.pi * r * (n : ℝ) ^ r) := by positivity
    linarith
  have hαL : |α j0| * L ≤ 1 / 2 := by
    rw [habsα, hLr, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (N : ℝ) ^ r ≤ (n : ℝ) ^ r := pow_le_pow_left₀ hN0 hnN.le _
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ Real.pi * r)]
  have hinvα : 1 / |α j0| ≤ 2 * Real.pi * r * (2 * (N : ℝ)) ^ r / |t| := by
    rw [habsα, one_div_div]
    apply div_le_div_of_nonneg_right _ htp.le
    apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnpos.le hn2r _) (by positivity)
  -- the good coordinate
  have hZ0 := oneD_bound (α j0) hα0 L L hαL
  have hWg : (L + (1 / |α j0|) * (1 + Real.log L)) ≤ (L : ℝ) ^ 2 * Wsave t N M ℓ r := by
    have hlog : 0 ≤ 1 + Real.log L := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ L by exact_mod_cast hL1); linarith
    have key : (L : ℝ) ^ 2 * Wsave t N M ℓ r =
        L + 2 * Real.pi * r * (2 * (N : ℝ)) ^ r / |t| * (1 + Real.log L) := by
      rw [hLr]; unfold Wsave
      have : (0 : ℝ) < (ℓ : ℝ) * (M : ℝ) ^ r := by positivity
      field_simp; ring
    rw [key]
    have := mul_le_mul_of_nonneg_right hinvα hlog
    linarith
  -- product of the box factors
  set g : Fin K → ℝ := fun j => if j = j0 then (L : ℝ) ^ 2 * Wsave t N M ℓ r
    else 3 * ((Lbox K M ℓ j : ℕ) : ℝ) ^ 2 with hg
  have hprod : ∏ j, ∑ zj ∈ Icc (-(Lbox K M ℓ j : ℤ)) (Lbox K M ℓ j),
      ‖inner (α j) zj (Lbox K M ℓ j)‖ ≤ ∏ j, g j := by
    apply Finset.prod_le_prod₀
    · intro j _; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    · intro j _
      simp only [hg]
      split_ifs with h
      · subst h; exact hZ0.trans hWg
      · have hLj : 1 ≤ Lbox K M ℓ j := by
          unfold Lbox
          exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
        exact oneD_three _ _ hLj
  have hW0 : 0 ≤ Wsave t N M ℓ r := by
    have hlogL : 0 ≤ 1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ r) := by
      have : (1 : ℝ) ≤ (ℓ : ℝ) * (M : ℝ) ^ r := by rw [← hLr]; exact_mod_cast hL1
      have := Real.log_nonneg this; linarith
    unfold Wsave
    exact add_nonneg (by positivity) (div_nonneg (mul_nonneg (by positivity) hlogL) (by positivity))
  have hgprod : ∏ j, g j ≤ Wsave t N M ℓ r * (3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (K * (K + 1))) := by
    rw [← prod_three_L, ← Finset.mul_prod_erase univ g (mem_univ j0),
      ← Finset.mul_prod_erase univ (fun j => 3 * ((Lbox K M ℓ j : ℕ) : ℝ) ^ 2) (mem_univ j0)]
    have hrest : ∏ j ∈ univ.erase j0, g j =
        ∏ j ∈ univ.erase j0, 3 * ((Lbox K M ℓ j : ℕ) : ℝ) ^ 2 := by
      apply prod_congr rfl; intro j hj
      simp only [hg, ite_eq_right_iff.mpr (fun h => absurd h (ne_of_mem_erase hj))]
    rw [hrest]
    have hg0 : g j0 = (L : ℝ) ^ 2 * Wsave t N M ℓ r := by simp [hg]
    rw [hg0, ← hLdef]
    have hP : 0 ≤ ∏ j ∈ univ.erase j0, 3 * ((Lbox K M ℓ j : ℕ) : ℝ) ^ 2 := by positivity
    have : (L : ℝ) ^ 2 * Wsave t N M ℓ r ≤ Wsave t N M ℓ r * (3 * (L : ℝ) ^ 2) := by
      nlinarith [sq_nonneg (L : ℝ)]
    calc (L : ℝ) ^ 2 * Wsave t N M ℓ r * ∏ j ∈ univ.erase j0, 3 * ((Lbox K M ℓ j : ℕ) : ℝ) ^ 2
        ≤ Wsave t N M ℓ r * (3 * (L : ℝ) ^ 2) *
            ∏ j ∈ univ.erase j0, 3 * ((Lbox K M ℓ j : ℕ) : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right this hP
      _ = _ := by ring
  -- combine with the bilinear bound
  have hbil := bilinear_bound α hℓ (M := M)
  set B := ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T α (A K a) (A K b)‖ with hB
  set e : ℝ := 2 * (ℓ : ℝ) - (K : ℝ) * ((K : ℝ) + 1) / 2 + η
  have hJ0 : (0 : ℝ) ≤ J ℓ K M := Nat.cast_nonneg _
  have hMpos : (0 : ℝ) < M := by linarith
  have hQ : B ^ (2 * ℓ ^ 2) ≤ (M : ℝ) ^ ((4 * ℓ ^ 2 : ℕ) : ℝ) *
      (C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (2 * η) * Wsave t N M ℓ r) := by
    refine hbil.trans ?_
    have h1 : (J ℓ K M : ℝ) ^ 2 ≤ (C * (M : ℝ) ^ e) ^ 2 := pow_le_pow_left₀ hJ0 hJ 2
    have hM4 : (0 : ℝ) ≤ (M : ℝ) ^ (4 * ℓ * (ℓ - 1)) := by positivity
    have hP0 : 0 ≤ ∏ j, ∑ zj ∈ Icc (-(Lbox K M ℓ j : ℤ)) (Lbox K M ℓ j),
        ‖inner (α j) zj (Lbox K M ℓ j)‖ :=
      Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc (M : ℝ) ^ (4 * ℓ * (ℓ - 1)) * (J ℓ K M : ℝ) ^ 2 *
          ∏ j, ∑ zj ∈ Icc (-(Lbox K M ℓ j : ℤ)) (Lbox K M ℓ j), ‖inner (α j) zj (Lbox K M ℓ j)‖
        ≤ (M : ℝ) ^ (4 * ℓ * (ℓ - 1)) * (C * (M : ℝ) ^ e) ^ 2 *
            (Wsave t N M ℓ r * (3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (K * (K + 1)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hM4) (hprod.trans hgprod) hP0 (by positivity)
      _ = _ := by
          have hMe : ((M : ℝ) ^ e) ^ 2 = (M : ℝ) ^ (2 * e) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hMpos.le]; ring_nf
          rw [mul_pow, hMe, ← Real.rpow_natCast (M : ℝ) (4 * ℓ * (ℓ - 1)),
            ← Real.rpow_natCast (M : ℝ) (K * (K + 1))]
          have hexp : ((4 * ℓ * (ℓ - 1) : ℕ) : ℝ) + 2 * e + ((K * (K + 1) : ℕ) : ℝ) =
              ((4 * ℓ ^ 2 : ℕ) : ℝ) + 2 * η := by
            simp only [e]
            push_cast [Nat.cast_sub hℓ]
            ring
          have hcomb : (M : ℝ) ^ ((4 * ℓ * (ℓ - 1) : ℕ) : ℝ) * (M : ℝ) ^ (2 * e) *
              (M : ℝ) ^ ((K * (K + 1) : ℕ) : ℝ) =
              (M : ℝ) ^ ((4 * ℓ ^ 2 : ℕ) : ℝ) * (M : ℝ) ^ (2 * η) := by
            rw [← Real.rpow_add hMpos, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos, hexp]
          calc _ = C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) * Wsave t N M ℓ r *
                ((M : ℝ) ^ ((4 * ℓ * (ℓ - 1) : ℕ) : ℝ) * (M : ℝ) ^ (2 * e) *
                  (M : ℝ) ^ ((K * (K + 1) : ℕ) : ℝ)) := by ring
            _ = _ := by rw [hcomb]; ring
  -- take the (2ℓ²)-th root
  have hk0 : 2 * ℓ ^ 2 ≠ 0 := by positivity
  have hB0 : 0 ≤ B := norm_nonneg _
  have hQ0 : 0 ≤ C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (2 * η) * Wsave t N M ℓ r := by
    positivity
  have hroot := Real.rpow_le_rpow (by positivity) hQ (by positivity :
    (0 : ℝ) ≤ (((2 * ℓ ^ 2 : ℕ) : ℝ))⁻¹)
  rw [Real.pow_rpow_inv_natCast hB0 hk0, Real.mul_rpow (by positivity) hQ0,
    ← Real.rpow_mul hMpos.le] at hroot
  have hexp2 : ((4 * ℓ ^ 2 : ℕ) : ℝ) * (((2 * ℓ ^ 2 : ℕ) : ℝ))⁻¹ = 2 := by
    push_cast
    have : (ℓ : ℝ) ≠ 0 := by positivity
    field_simp; ring
  rw [hexp2, Real.rpow_two] at hroot
  exact hroot

/-- **Step (F), the block bound.** -/
theorem block_bound {t : ℝ} (ht : t ≠ 0) {N M K ℓ r : ℕ} {C η : ℝ} (hC : 0 < C)
    (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ) (hr1 : 1 ≤ r) (hrK : r ≤ K) (hMN : 2 * M ^ 2 ≤ N)
    (hJ : (J ℓ K M : ℝ) ≤ C * (M : ℝ) ^ (2 * (ℓ : ℝ) - (K : ℝ) * ((K : ℝ) + 1) / 2 + η))
    (hgood : |t| * ℓ * (M : ℝ) ^ r ≤ Real.pi * r * (N : ℝ) ^ r) :
    ‖∑ n ∈ Ioc N (2 * N), phaseF t n‖ ≤
      N * Phi t C η N M K ℓ r + 2 * |t| * N * ((M : ℝ) ^ 2 / N) ^ (K + 1) +
        2 * (M : ℝ) ^ 2 := by
  have hNM : N ≤ 2 * N := by omega
  have hE := stepE t N (2 * N) M K hNM hM hMN
  have hMpos : (0 : ℝ) < (M : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    positivity
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by have := Nat.one_le_pow 2 M hM; omega
    exact_mod_cast this
  have hterm : ∀ n ∈ Ioc N (2 * N),
      ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b)‖ +
        2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / n) ^ (K + 1) ≤
      (M : ℝ) ^ 2 * Phi t C η N M K ℓ r + 2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / N) ^ (K + 1) := by
    intro n hn
    have hn' := mem_Ioc.mp hn
    refine add_le_add (Bn_bound ht hC hM hℓ hr1 hrK hJ hn'.1 hn'.2 hgood) ?_
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn'.1.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hMpos.le hNpos hnN) _
  have hsum := sum_le_sum hterm
  rw [sum_const, Nat.card_Ioc, show 2 * N - N = N by omega, nsmul_eq_mul] at hsum
  refine hE.trans ?_
  have : 1 / (M : ℝ) ^ 2 * ∑ n ∈ Ioc N (2 * N),
      (‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b)‖ +
        2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / n) ^ (K + 1)) ≤
      1 / (M : ℝ) ^ 2 * (N * ((M : ℝ) ^ 2 * Phi t C η N M K ℓ r +
        2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / N) ^ (K + 1))) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have e : 1 / (M : ℝ) ^ 2 * (N * ((M : ℝ) ^ 2 * Phi t C η N M K ℓ r +
        2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / N) ^ (K + 1))) =
      N * Phi t C η N M K ℓ r + 2 * |t| * N * ((M : ℝ) ^ 2 / N) ^ (K + 1) := by
    field_simp
  linarith

end ExpSum
