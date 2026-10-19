/-
# Round 583: large values at several points per character

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. Let `S ⊆ (P, 2P]`, `c_j ∈ ℂ` and `q ≥ 1`, and write `D_χ(t) = Σ_{j∈S} c_jχ(j)j^{−it}` (`DirMean.dp`).
Take finitely many points `(χ_i, x_i)` with `x_i ∈ [lo + ½, hi − ½]`, where any two points of the same character are
at distance at least `1`. Then `Σ_i |D_{χ_i}(x_i)|² ≤ (q(hi − lo) + 8P(1 + log P))(2 + log²(2P))Σ|c_j|²`
(`large_values_points`). That is the bound of `LinnikHybrid.large_values_chars`, which is the case of one point per
character (`large_values_chars_of_points`). A count of zeros detects several zeros of one character, at ordinates
at least `1` apart (`frontier/linnik/SIEVE-ROUTE.md` §9, milestone M1). With SIEVE-ROUTE.md §10 (round 586),
M1 is not needed for the uniform curve (round 587).

* `large_values_points`: group the points by their character. For each character, `DirMean.gallagher` (Gallagher's
  lemma for a `1`-separated set) bounds the sum over its points by the integral of `|D_χ|² + 2|D_χ||D_χ′|` over
  `[lo, hi]`. Then, as in `large_values_chars`, `mean_value_chars` for `D` and for its derivative, whose
  coefficients are `−i c_j log j`.
-/
import LinnikHybrid

open Real Complex MeasureTheory Set Finset

noncomputable section

namespace LinnikPoints

open DirMean LinnikHybrid

/-- **Large values at several points per character**: for points `(χ_i, x_i)`, `i ∈ Rs`, with
`x_i ∈ [lo + ½, hi − ½]` and any two points of one character at distance at least `1`,
`Σ_i |Σ_{j∈S} c_jχ_i(j)j^{−ix_i}|² ≤ (q(hi − lo) + 8P(1 + log P))(2 + log²(2P))Σ|c_j|²`. -/
theorem large_values_points {ι : Type*} {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ)
    (q : ℕ) [NeZero q] {lo hi : ℝ} (hab : lo ≤ hi) (Rs : Finset ι) (ch : ι → DirichletCharacter ℂ q)
    (x : ι → ℝ) (hR : ∀ i ∈ Rs, lo + 1 / 2 ≤ x i ∧ x i ≤ hi - 1 / 2)
    (hsep : ∀ i ∈ Rs, ∀ j ∈ Rs, i ≠ j → ch i = ch j → 1 ≤ |x i - x j|) :
    ∑ i ∈ Rs, ‖dp S (fun j => c j * ch i j) (x i)‖ ^ 2
      ≤ (q * (hi - lo) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
  classical
  set c' : ℕ → ℂ := fun j => c j * (-(I * (Real.log j : ℂ))) with hc'
  set L := q * (hi - lo) + 8 * P * (1 + Real.log P) with hL
  have hderiv : ∀ χ : DirichletCharacter ℂ q, ∀ t, HasDerivAt (dp S (fun j => c j * χ j))
      (dp S (fun j => c' j * χ j) t) t := fun χ t => by
    have h := hasDerivAt_dp S (fun j => c j * χ j) t
    have e : (fun j => c' j * χ j) = (fun j => c j * χ j * (-(I * (Real.log j : ℂ)))) := by
      funext j; simp only [hc']; ring
    rw [e]; exact h
  set g : DirichletCharacter ℂ q → ℝ → ℝ := fun χ t => ‖dp S (fun j => c j * χ j) t‖ ^ 2
      + 2 * ‖dp S (fun j => c j * χ j) t‖ * ‖dp S (fun j => c' j * χ j) t‖ with hg
  have hgc : ∀ χ, Continuous (g χ) := fun χ => by
    simp only [hg]
    have h1 := continuous_dp S (fun j => c j * χ j)
    have h2 := continuous_dp S (fun j => c' j * χ j)
    fun_prop
  have hg0 : ∀ χ t, 0 ≤ g χ t := fun χ t => by simp only [hg]; positivity
  -- the points of one character, by Gallagher's lemma for a `1`-separated set
  have hfib : ∀ χ : DirichletCharacter ℂ q,
      ∑ i ∈ Rs with ch i = χ, ‖dp S (fun j => c j * χ j) (x i)‖ ^ 2 ≤ ∫ t in lo..hi, g χ t := by
    intro χ
    have hinj : Set.InjOn x ↑(Rs.filter fun i => ch i = χ) := by
      intro i hi j hj hij
      by_contra hne
      have hi' := Finset.mem_filter.1 hi
      have hj' := Finset.mem_filter.1 hj
      have h1 := hsep i hi'.1 j hj'.1 hne (hi'.2.trans hj'.2.symm)
      rw [hij, sub_self, abs_zero] at h1
      norm_num at h1
    rw [← Finset.sum_image (f := fun t => ‖dp S (fun j => c j * χ j) t‖ ^ 2) hinj]
    have hG := DirMean.gallagher (hderiv χ) (continuous_dp S (fun j => c' j * χ j))
      ((Rs.filter fun i => ch i = χ).image x)
      (fun a ha b hb hne => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb
        have hi' := Finset.mem_filter.1 hi
        have hj' := Finset.mem_filter.1 hj
        exact hsep i hi'.1 j hj'.1 (fun h => hne (h ▸ rfl)) (hi'.2.trans hj'.2.symm))
      (fun a ha => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
        exact hR i (Finset.mem_filter.1 hi).1)
      hab
    simpa only [hg] using hG
  have hInt0 : ∀ χ, 0 ≤ ∫ t in lo..hi, g χ t := fun χ =>
    intervalIntegral.integral_nonneg hab fun t _ => hg0 χ t
  have hle2 : ∀ χ, ∫ t in lo..hi, g χ t ≤ 2 * (∫ t in lo..hi, ‖dp S (fun j => c j * χ j) t‖ ^ 2)
      + ∫ t in lo..hi, ‖dp S (fun j => c' j * χ j) t‖ ^ 2 := by
    intro χ
    have i2 : IntervalIntegrable (fun t => 2 * ‖dp S (fun j => c j * χ j) t‖ ^ 2) MeasureTheory.volume lo hi :=
      (continuous_const.mul ((continuous_dp S _).norm.pow 2)).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun t => ‖dp S (fun j => c' j * χ j) t‖ ^ 2) MeasureTheory.volume lo hi :=
      ((continuous_dp S _).norm.pow 2).intervalIntegrable _ _
    have := intervalIntegral.integral_mono_on hab ((hgc χ).intervalIntegrable _ _) (i2.add i3)
      fun t _ => by
        simp only [hg]
        nlinarith [sq_nonneg (‖dp S (fun j => c j * χ j) t‖ - ‖dp S (fun j => c' j * χ j) t‖)]
    rwa [intervalIntegral.integral_add i2 i3, intervalIntegral.integral_const_mul] at this
  have hm : ∑ χ : DirichletCharacter ℂ q, ∫ t in lo..hi, ‖dp S (fun j => c j * χ j) t‖ ^ 2
      ≤ L * ∑ j ∈ S, ‖c j‖ ^ 2 := mean_value_chars hS c q hab
  have hm' : ∑ χ : DirichletCharacter ℂ q, ∫ t in lo..hi, ‖dp S (fun j => c' j * χ j) t‖ ^ 2
      ≤ L * ∑ j ∈ S, ‖c' j‖ ^ 2 := mean_value_chars hS c' q hab
  have hc'le : ∑ j ∈ S, ‖c' j‖ ^ 2 ≤ Real.log (2 * P) ^ 2 * ∑ j ∈ S, ‖c j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.1 (hS hj)
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hlj : 0 ≤ Real.log j := Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega))
    have hlj2 : Real.log j ≤ Real.log (2 * P) := Real.log_le_log hj0 (by exact_mod_cast hj2)
    simp only [hc', norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlj, mul_pow]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlj hlj2 2) (by positivity)
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log P := Real.log_natCast_nonneg P
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [hL]; nlinarith [sub_nonneg.2 hab]
  calc ∑ i ∈ Rs, ‖dp S (fun j => c j * ch i j) (x i)‖ ^ 2
      = ∑ χ : DirichletCharacter ℂ q, ∑ i ∈ Rs with ch i = χ, ‖dp S (fun j => c j * ch i j) (x i)‖ ^ 2 :=
        (Finset.sum_fiberwise Rs ch _).symm
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ i ∈ Rs with ch i = χ, ‖dp S (fun j => c j * χ j) (x i)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.1 hi).2]
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ∫ t in lo..hi, g χ t := Finset.sum_le_sum fun χ _ => hfib χ
    _ ≤ ∑ χ : DirichletCharacter ℂ q, (2 * (∫ t in lo..hi, ‖dp S (fun j => c j * χ j) t‖ ^ 2)
          + ∫ t in lo..hi, ‖dp S (fun j => c' j * χ j) t‖ ^ 2) := Finset.sum_le_sum fun χ _ => hle2 χ
    _ = 2 * (∑ χ : DirichletCharacter ℂ q, ∫ t in lo..hi, ‖dp S (fun j => c j * χ j) t‖ ^ 2)
          + ∑ χ : DirichletCharacter ℂ q, ∫ t in lo..hi, ‖dp S (fun j => c' j * χ j) t‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * (L * ∑ j ∈ S, ‖c j‖ ^ 2) + L * ∑ j ∈ S, ‖c' j‖ ^ 2 := by linarith
    _ ≤ 2 * (L * ∑ j ∈ S, ‖c j‖ ^ 2) + L * (Real.log (2 * P) ^ 2 * ∑ j ∈ S, ‖c j‖ ^ 2) := by
        have := mul_le_mul_of_nonneg_left hc'le hL0; linarith
    _ = L * (2 + Real.log (2 * P) ^ 2) * ∑ j ∈ S, ‖c j‖ ^ 2 := by ring

/-- `LinnikHybrid.large_values_chars` is the case of one point per character. -/
theorem large_values_chars_of_points {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ)
    (q : ℕ) [NeZero q] {lo hi : ℝ} (hab : lo ≤ hi) (Rs : Finset (DirichletCharacter ℂ q))
    (x : DirichletCharacter ℂ q → ℝ) (hR : ∀ χ ∈ Rs, lo + 1 / 2 ≤ x χ ∧ x χ ≤ hi - 1 / 2) :
    ∑ χ ∈ Rs, ‖dp S (fun j => c j * χ j) (x χ)‖ ^ 2
      ≤ (q * (hi - lo) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2) * ∑ j ∈ S, ‖c j‖ ^ 2 :=
  large_values_points hS c q hab Rs id x hR fun _ _ _ _ hne heq => absurd heq hne

end LinnikPoints
