/-
# Sharpening, step S1a: many good coordinates (round 213)

Plain statement (`block_bound_multi`). This is the block bound of rounds 206/208, but every
coordinate `j ∈ G` that satisfies the no-wrap condition `|t|·ℓ·M^{j+1} ≤ π(j+1)N^{j+1}`
contributes its own saving factor `W_{j+1}`:
  `|Σ_{N<n≤N'} n^{−it}| ≤ N·Φ_G + 2|t|N(M²/N)^{K+1} + 2M²`,
  `Φ_G = (C²·3^K·ℓ^{2K}·M^{2η}·Π_{j∈G} W_{j+1})^{1/(2ℓ²)}`.

With one coordinate the saving is `N^{−O(r)/ℓ²}`. With a window of about `K` coordinates it is
`N^{−O(K²)/ℓ²}`, which the classical proofs of the Korobov–Vinogradov bound exploit.
-/
import ExpSum6

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder

lemma wsave_nonneg (t : ℝ) (N : ℕ) {M ℓ : ℕ} (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ) (r : ℕ) :
    0 ≤ Wsave t N M ℓ r := by
  have hlogL : 0 ≤ 1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ r) := by
    have h1 : (1 : ℝ) ≤ (ℓ : ℝ) * (M : ℝ) ^ r := by
      have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
      have : (1 : ℝ) ≤ (M : ℝ) ^ r := one_le_pow₀ (by exact_mod_cast hM)
      nlinarith
    have := Real.log_nonneg h1; linarith
  unfold Wsave
  exact add_nonneg (by positivity) (div_nonneg (mul_nonneg (by positivity) hlogL) (by positivity))

/-- **One good coordinate.** -/
lemma coord_good {t : ℝ} (ht : t ≠ 0) {N n M K ℓ : ℕ} (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ)
    (hn1 : N < n) (hn2 : n ≤ 2 * N) (j : Fin K)
    (hgood : |t| * ℓ * (M : ℝ) ^ (j.val + 1) ≤ Real.pi * (j.val + 1 : ℕ) * (N : ℝ) ^ (j.val + 1)) :
    ∑ z ∈ Icc (-(Lbox K M ℓ j : ℤ)) (Lbox K M ℓ j), ‖inner (alphaVec t n K j) z (Lbox K M ℓ j)‖ ≤
      ((Lbox K M ℓ j : ℕ) : ℝ) ^ 2 * Wsave t N M ℓ (j.val + 1) := by
  set r := j.val + 1 with hr
  have hπ := Real.pi_pos
  have htp : 0 < |t| := abs_pos.mpr ht
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hrr : (1 : ℝ) ≤ r := by rw [hr]; exact_mod_cast (show 1 ≤ j.val + 1 by omega)
  have hnN : (N : ℝ) < n := by exact_mod_cast hn1
  have hn2r : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn2
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  set L := Lbox K M ℓ j with hLdef
  have hLr : (L : ℝ) = ℓ * (M : ℝ) ^ r := by simp [hLdef, Lbox, hr]
  have hL1 : 1 ≤ L := by
    have : (1 : ℝ) ≤ L := by
      rw [hLr]
      have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
      nlinarith [one_le_pow₀ hMr (n := r)]
    exact_mod_cast this
  have habsα : |alphaVec t n K j| = |t| / (2 * Real.pi * r * (n : ℝ) ^ r) := by
    have hj0r' : ((j : ℕ) : ℝ) + 1 = r := by rw [hr]; push_cast; ring
    simp only [alphaVec, hj0r']
    rw [abs_div, abs_of_pos (show (0 : ℝ) < (r : ℝ) * (n : ℝ) ^ (j.val + 1) by positivity), abs_mul,
      abs_div, abs_pow, abs_neg, abs_one, one_pow, mul_one,
      abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)]
    rw [← hr]
    field_simp
  have hα0 : alphaVec t n K j ≠ 0 := by
    intro h; rw [h, abs_zero] at habsα
    have : 0 < |t| / (2 * Real.pi * r * (n : ℝ) ^ r) := by positivity
    linarith
  have hgood' : |t| * ℓ * (M : ℝ) ^ r ≤ Real.pi * r * (N : ℝ) ^ r := by
    simpa using hgood
  have hαL : |alphaVec t n K j| * L ≤ 1 / 2 := by
    rw [habsα, hLr, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (N : ℝ) ^ r ≤ (n : ℝ) ^ r := pow_le_pow_left₀ hN0 hnN.le _
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ Real.pi * r)]
  have hinvα : 1 / |alphaVec t n K j| ≤ 2 * Real.pi * r * (2 * (N : ℝ)) ^ r / |t| := by
    rw [habsα, one_div_div]
    apply div_le_div_of_nonneg_right _ htp.le
    apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnpos.le hn2r _) (by positivity)
  have hZ0 := oneD_bound (alphaVec t n K j) hα0 L L hαL
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

/-- The multi-coordinate saving. -/
noncomputable def WG (t : ℝ) (N M K ℓ : ℕ) (G : Finset (Fin K)) : ℝ :=
  ∏ j ∈ G, Wsave t N M ℓ (j.val + 1)

/-- The per-`n` saving with a set of good coordinates. -/
noncomputable def PhiG (t C η : ℝ) (N M K ℓ : ℕ) (G : Finset (Fin K)) : ℝ :=
  (C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (2 * η) * WG t N M K ℓ G) ^
    (((2 * ℓ ^ 2 : ℕ) : ℝ)⁻¹)

lemma WG_nonneg (t : ℝ) (N : ℕ) {M K ℓ : ℕ} (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ) (G : Finset (Fin K)) :
    0 ≤ WG t N M K ℓ G :=
  Finset.prod_nonneg fun _ _ => wsave_nonneg t N hM hℓ _

set_option maxHeartbeats 1600000 in
/-- **Per-`n` bound, many good coordinates.** -/
theorem Bn_bound_multi {t : ℝ} (ht : t ≠ 0) {N n M K ℓ : ℕ} {C η : ℝ} (hC : 0 < C)
    (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ) (G : Finset (Fin K))
    (hJ : (J ℓ K M : ℝ) ≤ C * (M : ℝ) ^ (2 * (ℓ : ℝ) - (K : ℝ) * ((K : ℝ) + 1) / 2 + η))
    (hn1 : N < n) (hn2 : n ≤ 2 * N)
    (hgood : ∀ j ∈ G, |t| * ℓ * (M : ℝ) ^ (j.val + 1) ≤
      Real.pi * (j.val + 1 : ℕ) * (N : ℝ) ^ (j.val + 1)) :
    ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b)‖ ≤
      (M : ℝ) ^ 2 * PhiG t C η N M K ℓ G := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  set α := alphaVec t n K with hα
  set W : Fin K → ℝ := fun j => if j ∈ G then Wsave t N M ℓ (j.val + 1) else 1 with hWdef
  have hW0 : ∀ j, 0 ≤ W j := by
    intro j; simp only [hWdef]; split_ifs
    · exact wsave_nonneg t N hM hℓ _
    · norm_num
  have hprod : ∏ j, ∑ zj ∈ Icc (-(Lbox K M ℓ j : ℤ)) (Lbox K M ℓ j),
      ‖inner (α j) zj (Lbox K M ℓ j)‖ ≤ ∏ j, (W j * (3 * ((Lbox K M ℓ j : ℕ) : ℝ) ^ 2)) := by
    apply Finset.prod_le_prod₀
    · intro j _; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    · intro j _
      have hLj : 1 ≤ Lbox K M ℓ j := by
        unfold Lbox
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
      simp only [hWdef]
      split_ifs with h
      · refine (coord_good ht hM hℓ hn1 hn2 j (hgood j h)).trans ?_
        have := wsave_nonneg t N hM hℓ (j.val + 1)
        nlinarith [sq_nonneg ((Lbox K M ℓ j : ℕ) : ℝ)]
      · rw [one_mul]; exact oneD_three _ _ hLj
  have hWprod : ∏ j, W j = WG t N M K ℓ G := by
    simp only [hWdef, WG]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  have hgprod : ∏ j, (W j * (3 * ((Lbox K M ℓ j : ℕ) : ℝ) ^ 2)) =
      WG t N M K ℓ G * (3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (K * (K + 1))) := by
    rw [Finset.prod_mul_distrib, hWprod, prod_three_L]
  have hWG0 := WG_nonneg t N hM hℓ G
  have hbil := bilinear_bound α hℓ (M := M)
  set B := ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T α (A K a) (A K b)‖ with hB
  set e : ℝ := 2 * (ℓ : ℝ) - (K : ℝ) * ((K : ℝ) + 1) / 2 + η
  have hJ0 : (0 : ℝ) ≤ J ℓ K M := Nat.cast_nonneg _
  have hMpos : (0 : ℝ) < M := by linarith
  have hQ : B ^ (2 * ℓ ^ 2) ≤ (M : ℝ) ^ ((4 * ℓ ^ 2 : ℕ) : ℝ) *
      (C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (2 * η) * WG t N M K ℓ G) := by
    refine hbil.trans ?_
    have h1 : (J ℓ K M : ℝ) ^ 2 ≤ (C * (M : ℝ) ^ e) ^ 2 := pow_le_pow_left₀ hJ0 hJ 2
    have hM4 : (0 : ℝ) ≤ (M : ℝ) ^ (4 * ℓ * (ℓ - 1)) := by positivity
    have hP0 : 0 ≤ ∏ j, ∑ zj ∈ Icc (-(Lbox K M ℓ j : ℤ)) (Lbox K M ℓ j),
        ‖inner (α j) zj (Lbox K M ℓ j)‖ :=
      Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc (M : ℝ) ^ (4 * ℓ * (ℓ - 1)) * (J ℓ K M : ℝ) ^ 2 *
          ∏ j, ∑ zj ∈ Icc (-(Lbox K M ℓ j : ℤ)) (Lbox K M ℓ j), ‖inner (α j) zj (Lbox K M ℓ j)‖
        ≤ (M : ℝ) ^ (4 * ℓ * (ℓ - 1)) * (C * (M : ℝ) ^ e) ^ 2 *
            (WG t N M K ℓ G * (3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (K * (K + 1)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hM4) (hprod.trans hgprod.le) hP0 (by positivity)
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
          calc _ = C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) * WG t N M K ℓ G *
                ((M : ℝ) ^ ((4 * ℓ * (ℓ - 1) : ℕ) : ℝ) * (M : ℝ) ^ (2 * e) *
                  (M : ℝ) ^ ((K * (K + 1) : ℕ) : ℝ)) := by ring
            _ = _ := by rw [hcomb]; ring
  have hk0 : 2 * ℓ ^ 2 ≠ 0 := by positivity
  have hB0 : 0 ≤ B := norm_nonneg _
  have hQ0 : 0 ≤ C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (2 * η) * WG t N M K ℓ G := by
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

/-- **Partial blocks, many good coordinates.** -/
theorem block_bound_multi {t : ℝ} (ht : t ≠ 0) {N N' M K ℓ : ℕ} {C η : ℝ} (hC : 0 < C)
    (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ) (G : Finset (Fin K)) (hMN : 2 * M ^ 2 ≤ N)
    (hN1 : N ≤ N') (hN2 : N' ≤ 2 * N)
    (hJ : (J ℓ K M : ℝ) ≤ C * (M : ℝ) ^ (2 * (ℓ : ℝ) - (K : ℝ) * ((K : ℝ) + 1) / 2 + η))
    (hgood : ∀ j ∈ G, |t| * ℓ * (M : ℝ) ^ (j.val + 1) ≤
      Real.pi * (j.val + 1 : ℕ) * (N : ℝ) ^ (j.val + 1)) :
    ‖∑ n ∈ Ioc N N', phaseF t n‖ ≤
      N * PhiG t C η N M K ℓ G + 2 * |t| * N * ((M : ℝ) ^ 2 / N) ^ (K + 1) +
        2 * (M : ℝ) ^ 2 := by
  have hE := stepE t N N' M K hN1 hM hMN
  have hMpos : (0 : ℝ) < (M : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    positivity
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by have := Nat.one_le_pow 2 M hM; omega
    exact_mod_cast this
  set Y := (M : ℝ) ^ 2 * PhiG t C η N M K ℓ G +
    2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / N) ^ (K + 1) with hY
  have hterm : ∀ n ∈ Ioc N N',
      ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b)‖ +
        2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / n) ^ (K + 1) ≤ Y := by
    intro n hn
    have hn' := mem_Ioc.mp hn
    refine add_le_add (Bn_bound_multi ht hC hM hℓ G hJ hn'.1 (hn'.2.trans hN2) hgood) ?_
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn'.1.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hMpos.le hNpos hnN) _
  have hY0 : 0 ≤ Y := by
    have hPhi : 0 ≤ PhiG t C η N M K ℓ G := by
      unfold PhiG
      exact Real.rpow_nonneg (mul_nonneg (by positivity) (WG_nonneg t N hM hℓ G)) _
    positivity
  have hsum := sum_le_sum hterm
  rw [sum_const, Nat.card_Ioc, nsmul_eq_mul] at hsum
  have hcard : ((N' - N : ℕ) : ℝ) ≤ N := by exact_mod_cast (show N' - N ≤ N by omega)
  refine hE.trans ?_
  have h1 : 1 / (M : ℝ) ^ 2 * ∑ n ∈ Ioc N N',
      (‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b)‖ +
        2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / n) ^ (K + 1)) ≤ 1 / (M : ℝ) ^ 2 * (N * Y) :=
    mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_right hcard hY0)) (by positivity)
  have e : 1 / (M : ℝ) ^ 2 * (N * Y) =
      N * PhiG t C η N M K ℓ G + 2 * |t| * N * ((M : ℝ) ^ 2 / N) ^ (K + 1) := by
    simp only [Y]; field_simp
  linarith

end ExpSum
