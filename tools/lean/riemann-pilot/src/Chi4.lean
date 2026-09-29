import Mathlib
import DirichletOmega
import XiBounds

/-! # `L(s, χ₄)`: positivity on `(0, ∞)`, a zero with `Re ρ ≥ ½`, and the race mod 4 (round 223)

Round 222's race theorem (`DirichletOmega.race_four`) had two hypotheses. Both are proved here.

**No real zero.** With `S(x) = Σ_{n ≤ x} χ₄(n) ∈ {0, 1}` (`sum_c4`), partial summation gives
`L(s, χ₄) = s∫_1^∞ S(x)x^{−s−1}dx` on `Re s > 1` (`PsiOmega.integral_summ`). The right side is a
Mellin transform holomorphic on `Re s > 0` (`I4_differentiableAt`), so the identity holds there
(`LFunction_chi4_eq`). Since `S ≥ 0` and `S = 1` on `[1, 3)`:
* `LFunction_chi4_real_ge`: `L(σ, χ₄) ≥ 1 − 3^{−σ} > 0` for real `σ > 0`;
* `norm_LFunction_chi4_le`: `‖L(s, χ₄)‖ ≤ ‖s‖/Re s` on `Re s > 0`.

**A zero exists.**
* `χ₄` is primitive (`chi4_isPrimitive`) and real (`chi4_inv`), so Mathlib's functional equation
  gives `Λ*(1 − s) = εΛ*(s)` for `Λ*(s) = 4^{s/2}Λ(s, χ₄)` (`Lam_one_sub`).
* On `Re s ≥ ½`, `‖Λ*(s)‖ ≤ n^{3n}` for `n ≥ ‖s‖ + 3` (`norm_Lam_le`), from `‖Γ(w)‖ ≤ Γ(Re w)`
  and the bound on `L`.
* `f(z) = Λ*(½ + iz)Λ*(½ − iz)` is even and entire, `f(0) = Λ*(½)² ≠ 0`, and
  `‖f(z)‖ ≤ C·exp(48‖z‖^{3/2})` (`norm_fL_le`).
* If `L(s, χ₄)` had no zero with `Re ρ ≥ ½`, `f` would have no zeros, and Hadamard's factorisation
  (`hadamardW_even`) would make it constant. But `f(−i(σ − ½)) = εΛ*(σ)²`, and
  `‖Λ*(2k + 1)‖ ≥ (4/π)^k/3` (`norm_Lam_odd_ge`). Hence `exists_zero_chi4`.

`race_four_half`: the `log p`-weighted race mod 4 changes lead infinitely often, by more than
`c·x^θ` each way, for every `θ < ½`. No hypotheses.

No bearing on RH. -/

open Real Complex MeasureTheory Filter Topology Set ArithmeticFunction

noncomputable section

namespace PsiOmega

open LandauLaplace DirichletCharacter Pilot1ca Pilot1bt

/-- `χ₄(n)` as a real number. -/
def c4 (n : ℕ) : ℝ := ((ZMod.χ₄ n : ℤ) : ℝ)

theorem c4_ofReal (n : ℕ) : (c4 n : ℂ) = chi4 n := by rw [chi4_nat, c4]; push_cast; rfl

/-- `Σ_{k ≤ n} χ₄(k)` is `1` if `n ≡ 1, 2 (mod 4)` and `0` otherwise. -/
theorem sum_c4 (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, c4 k = if n % 4 = 1 ∨ n % 4 = 2 then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, c4, ZMod.χ₄_nat_eq_if_mod_four]
    have h4 := Nat.mod_lt n (show 0 < 4 by norm_num)
    have e1 : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
    have e2 : (n + 1) % 2 = (n % 4 + 1) % 2 := by omega
    rw [e1, e2]
    interval_cases n % 4 <;> norm_num

theorem summ_c4_nonneg (x : ℝ) : 0 ≤ summ c4 x := by
  unfold summ; rw [sum_c4]; split_ifs <;> norm_num

theorem summ_c4_le_one (x : ℝ) : summ c4 x ≤ 1 := by
  unfold summ; rw [sum_c4]; split_ifs <;> norm_num

theorem summ_c4_eq_one {x : ℝ} (h1 : 1 ≤ x) (h3 : x < 3) : summ c4 x = 1 := by
  unfold summ
  have hf1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hf3 : ⌊x⌋₊ < 3 := (Nat.floor_lt (by linarith)).2 (by exact_mod_cast h3)
  rw [sum_c4]
  interval_cases h : ⌊x⌋₊ <;> norm_num

theorem linBound_c4 : LinBound c4 1 := fun x hx => by
  rw [abs_of_nonneg (summ_c4_nonneg x), one_mul]
  rcases lt_or_ge x 1 with h | h
  · have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.2 h
    unfold summ; rw [this]; simpa using hx
  · exact (summ_c4_le_one x).trans h

/-- `I(s) = ∫_1^∞ S(x)x^{−s−1}dx`, `S(x) = Σ_{n ≤ x} χ₄(n)`. -/
def I4 (s : ℂ) : ℂ := ∫ x in Ioi (1 : ℝ), (summ c4 x : ℂ) * (x : ℂ) ^ (-(s + 1))

theorem I4_eq_mellin (s : ℂ) :
    I4 s = mellin (fun x : ℝ => (Ioi (1 : ℝ)).indicator (fun x => (summ c4 x : ℂ)) x) (-s) := by
  unfold I4 mellin
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_indicator (s := Ioi 0) measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases h1 : x ∈ Ioi (1 : ℝ)
  · have h0 : x ∈ Ioi (0 : ℝ) := show (0 : ℝ) < x from lt_trans one_pos h1
    simp only [indicator_of_mem h1, indicator_of_mem h0, smul_eq_mul]
    rw [mul_comm]; congr 2; ring
  · simp only [indicator_of_notMem h1]
    by_cases h0 : x ∈ Ioi (0 : ℝ)
    · simp [indicator_of_mem h0, indicator_of_notMem h1]
    · simp [indicator_of_notMem h0]

theorem I4_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ I4 s := by
  set g : ℝ → ℂ := fun x => (Ioi (1 : ℝ)).indicator (fun x => (summ c4 x : ℂ)) x
  have hgm : Measurable g :=
    (Complex.continuous_ofReal.measurable.comp (measurable_summ c4)).indicator measurableSet_Ioi
  have hgb : ∀ x, ‖g x‖ ≤ 1 := fun x => by
    by_cases h : x ∈ Ioi (1 : ℝ)
    · simp only [g, indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (summ_c4_nonneg x)]
      exact summ_c4_le_one x
    · simp [g, indicator_of_notMem h]
  have hloc : LocallyIntegrableOn g (Ioi 0) :=
    ((locallyIntegrable_const (1 : ℂ)).mono hgm.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hgb x)).locallyIntegrableOn _
  have htop : g =O[atTop] (· ^ (-(0 : ℝ))) :=
    Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun x => by
      simpa [Real.rpow_zero] using hgb x)
  have hbot : g =O[𝓝[>] 0] (· ^ (-((-s).re - 1))) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have : x ∉ Ioi (1 : ℝ) := fun h => by linarith [hx.2, show 1 < x from h]
    simp [g, indicator_of_notMem this]
  have hd : DifferentiableAt ℂ (mellin g) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow hloc htop (by simp; linarith) hbot (by linarith)
  have e : I4 = fun s => mellin g (-s) := funext I4_eq_mellin
  rw [e]
  exact hd.comp s differentiableAt_id.neg

theorem LSeriesSummable_c4 {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n => (c4 n : ℂ)) s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n _ => by
    rw [c4_ofReal, sub_self, Real.rpow_zero, mul_one, chi4_nat]
    have := norm_le_one chi4 n; rwa [chi4_nat] at this⟩

/-- **`L(s, χ₄) = s·∫_1^∞ S(x)x^{−s−1}dx` for `Re s > 0`.** -/
theorem LFunction_chi4_eq {s : ℂ} (hs : 0 < s.re) : LFunction chi4 s = s * I4 s := by
  set U : Set ℂ := {s | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : Convex ℝ U := convex_halfSpace_re_gt 0
  have hL : DifferentiableOn ℂ (LFunction chi4) U :=
    (differentiable_LFunction chi4_ne_one).differentiableOn
  have hR : DifferentiableOn ℂ (fun s => s * I4 s) U := fun z hz =>
    (differentiableAt_id.mul (I4_differentiableAt hz)).differentiableWithinAt
  refine eqOn_convex hUo hUc hL hR (z0 := 2) (show (0 : ℝ) < (2 : ℂ).re by norm_num) ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hz; linarith
  have hsum := LSeriesSummable_c4 hz
  have h := integral_summ linBound_c4 hz hsum
  rw [show (fun n => (c4 n : ℂ)) = fun n : ℕ => chi4 n from funext c4_ofReal] at h
  rw [show (fun n : ℕ => chi4 (n : ZMod 4)) = fun n : ℕ => chi4 n from rfl] at h
  rw [LFunction_eq_LSeries chi4 hz]
  unfold I4; rw [h]; field_simp

/-- `∫_1^∞ x^{−σ−1}dx = 1/σ`. -/
theorem integral_rpow_Ioi_one {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) = 1 / σ := by
  rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow, show -σ - 1 + 1 = -σ by ring]
  field_simp

/-- **`|L(s, χ₄)| ≤ |s|/σ`** for `σ = Re s > 0`. -/
theorem norm_LFunction_chi4_le {s : ℂ} (hs : 0 < s.re) : ‖LFunction chi4 s‖ ≤ ‖s‖ / s.re := by
  rw [LFunction_chi4_eq hs, norm_mul, div_eq_mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← integral_rpow_Ioi_one hs]
  refine norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt (by linarith) one_pos))
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_))
  have hx0 : 0 < x := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (summ_c4_nonneg x),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have : (-(s + 1)).re = -s.re - 1 := by simp; ring
  rw [this]
  have hp : 0 ≤ x ^ (-s.re - 1) := by positivity
  nlinarith [summ_c4_le_one x]

/-- **`L(σ, χ₄) ≥ 1 − 3^{−σ}`** for real `σ > 0`; in particular `L(σ, χ₄) > 0`. -/
theorem LFunction_chi4_real_ge {σ : ℝ} (hσ : 0 < σ) :
    1 - (3 : ℝ) ^ (-σ) ≤ (LFunction chi4 σ).re ∧ (LFunction chi4 σ).im = 0 := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  set h : ℝ → ℝ := fun x => summ c4 x * x ^ (-σ - 1)
  have hI : I4 σ = ((∫ x in Ioi (1 : ℝ), h x : ℝ) : ℂ) := by
    unfold I4
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 1 < x) => ?_
    simp only [h]; push_cast
    rw [Complex.ofReal_cpow (by linarith)]; congr 2; push_cast; ring
  rw [LFunction_chi4_eq hs, hI, ← Complex.ofReal_mul, ofReal_re, ofReal_im]
  refine ⟨?_, rfl⟩
  have hint : IntegrableOn (fun x : ℝ => x ^ (-σ - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hhint : IntegrableOn h (Ioi 1) := by
    refine hint.mono' ((measurable_summ c4).mul (by fun_prop)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_))
    have hp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg (by linarith) _
    simp only [h, Real.norm_eq_abs, abs_mul, abs_of_nonneg (summ_c4_nonneg x), abs_of_nonneg hp]
    nlinarith [summ_c4_le_one x]
  -- `h ≥ x^{−σ−1}` on `(1, 3)` and `h ≥ 0`
  have hlow : ∫ x in Ioo (1 : ℝ) 3, x ^ (-σ - 1) ≤ ∫ x in Ioi (1 : ℝ), h x := by
    calc ∫ x in Ioo (1 : ℝ) 3, x ^ (-σ - 1) = ∫ x in Ioo (1 : ℝ) 3, h x :=
          setIntegral_congr_fun measurableSet_Ioo fun x hx => by
            simp only [h, summ_c4_eq_one hx.1.le hx.2, one_mul]
      _ ≤ ∫ x in Ioi (1 : ℝ), h x :=
          setIntegral_mono_set hhint ((ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun x (hx : 1 < x) =>
              mul_nonneg (summ_c4_nonneg x) (Real.rpow_nonneg (by linarith) _)))
            (Eventually.of_forall Ioo_subset_Ioi_self)
  have hval : ∫ x in Ioo (1 : ℝ) 3, x ^ (-σ - 1) = (1 - (3 : ℝ) ^ (-σ)) / σ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
      integral_rpow (Or.inr ⟨by linarith, by norm_num [Set.mem_uIcc]⟩)]
    rw [show -σ - 1 + 1 = -σ by ring, Real.one_rpow]
    field_simp; ring
  rw [hval] at hlow
  have := mul_le_mul_of_nonneg_left hlow hσ.le
  rw [mul_div_cancel₀ _ hσ.ne'] at this
  exact this

theorem LFunction_chi4_pos {σ : ℝ} (hσ : 0 < σ) : LFunction chi4 σ ≠ 0 := fun h => by
  have := (LFunction_chi4_real_ge hσ).1
  rw [h, zero_re] at this
  have : (3 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith


/-! ## The functional equation -/

theorem chi4_odd : chi4.Odd := by
  show chi4 (-1) = -1
  have e : (-1 : ZMod 4) = ((3 : ℕ) : ZMod 4) := by decide
  rw [e, chi4_nat, ZMod.χ₄_nat_eq_if_mod_four]; norm_num

theorem chi4_inv : chi4⁻¹ = chi4 := (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).inv

theorem chi4_isPrimitive : chi4.IsPrimitive := by
  rw [isPrimitive_def]
  have hd := conductor_dvd_level chi4
  have hc0 := conductor_ne_zero chi4
  have hle : conductor chi4 ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 1 ≤ conductor chi4 := Nat.pos_of_ne_zero hc0
  interval_cases h : conductor chi4
  · exact absurd (eq_one_iff_conductor_eq_one.2 h) chi4_ne_one
  · exfalso
    have hf := factorsThrough_conductor chi4
    rw [h] at hf
    have e := congrArg (fun χ : DirichletCharacter ℂ 4 => χ ((3 : ℤ) : ZMod 4)) hf.eq_changeLevel
    rw [changeLevel_eq_cast_of_dvd' _ _ (by norm_num : IsCoprime (3 : ℤ) (4 : ℕ))] at e
    have h3 : ((3 : ℤ) : ZMod 2) = 1 := by decide
    rw [h3, map_one] at e
    have : chi4 ((3 : ℤ) : ZMod 4) = -1 := by
      rw [show ((3 : ℤ) : ZMod 4) = ((3 : ℕ) : ZMod 4) by decide, chi4_nat,
        ZMod.χ₄_nat_eq_if_mod_four]; norm_num
    rw [this] at e; norm_num at e
  · exact absurd hd (by decide)
  · rfl

/-- `Λ*(s) = 4^{s/2}Λ(s, χ₄)`, with `Λ*(1 − s) = εΛ*(s)`. -/
def Lam (s : ℂ) : ℂ := (4 : ℂ) ^ (s / 2) * completedLFunction chi4 s

theorem differentiable_Lam : Differentiable ℂ Lam :=
  ((differentiable_id.div_const 2).const_cpow (Or.inl (by norm_num : (4 : ℂ) ≠ 0))).mul
    (differentiable_completedLFunction (N := 4) chi4_ne_one)

theorem Lam_one_sub (s : ℂ) : Lam (1 - s) = rootNumber chi4 * Lam s := by
  unfold Lam
  rw [chi4_isPrimitive.completedLFunction_one_sub, chi4_inv]
  push_cast
  have e : (4 : ℂ) ^ ((1 - s) / 2) * (4 : ℂ) ^ (s - 1 / 2) = (4 : ℂ) ^ (s / 2) := by
    rw [← cpow_add _ _ (by norm_num : (4 : ℂ) ≠ 0)]; congr 1; ring
  linear_combination (rootNumber chi4 * completedLFunction chi4 s) * e

/-- For `Re s > −1`, `Λ(s, χ₄) = Γ_ℝ(s + 1)L(s, χ₄)`. -/
theorem completed_eq {s : ℂ} (hs : -1 < s.re) :
    completedLFunction chi4 s = Gammaℝ (s + 1) * LFunction chi4 s := by
  have hΓ : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  rw [LFunction_eq_completed_div_gammaFactor (N := 4) chi4 s (Or.inr (by norm_num)),
    chi4_odd.gammaFactor_def]
  field_simp

/-! ## Growth -/

theorem norm_cGamma_le {w : ℂ} (hw : 0 < w.re) : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq
    (setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem rGamma_le {x : ℝ} (hx : 3 / 4 ≤ x) {n : ℕ} (hn : x + 2 ≤ n + 1) :
    Real.Gamma x ≤ n.factorial := by
  have hx0 : 0 < x := by linarith
  have h2 : Real.Gamma (x + 2) = (x + 1) * x * Real.Gamma x := by
    rw [show x + 2 = (x + 1) + 1 by ring, Real.Gamma_add_one (by linarith),
      Real.Gamma_add_one hx0.ne']; ring
  have hmono : Real.Gamma (x + 2) ≤ Real.Gamma (n + 1) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (show (2 : ℝ) ≤ x + 2 by linarith)
      (show (2 : ℝ) ≤ n + 1 by linarith) hn
  rw [Real.Gamma_nat_eq_factorial] at hmono
  have hG := Real.Gamma_pos_of_pos hx0
  have hxx : 1 ≤ (x + 1) * x := by nlinarith
  nlinarith

theorem norm_Gammaℝ_le {w : ℂ} (hw : 0 < w.re) : ‖Gammaℝ w‖ ≤ Real.Gamma (w.re / 2) := by
  rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have h1 : π ^ (-w / 2).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
      (by simp; linarith)
  have h2 := norm_cGamma_le (w := w / 2) (by simp; linarith)
  have e : (w / 2).re = w.re / 2 := by simp
  rw [e] at h2
  calc π ^ (-w / 2).re * ‖Complex.Gamma (w / 2)‖ ≤ 1 * Real.Gamma (w.re / 2) :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **`‖Λ*(w)‖ ≤ n^{3n}`** for `Re w ≥ ½` and `‖w‖ + 3 ≤ n`. -/
theorem norm_Lam_le {w : ℂ} (hw : 1 / 2 ≤ w.re) {n : ℕ} (hn : ‖w‖ + 3 ≤ n) :
    ‖Lam w‖ ≤ (n : ℝ) ^ (3 * n) := by
  have hre := Complex.re_le_norm w
  have hn2 : (2 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  rw [Lam, completed_eq (by linarith), norm_mul, norm_mul]
  have h4 : ‖(4 : ℂ) ^ (w / 2)‖ ≤ (n : ℝ) ^ n := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    have e : (w / 2).re = w.re / 2 := by simp
    rw [e]
    calc (4 : ℝ) ^ (w.re / 2) ≤ 4 ^ ((n : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 ^ (n : ℝ) := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; ring_nf
      _ ≤ (n : ℝ) ^ (n : ℝ) := Real.rpow_le_rpow (by norm_num) hn2 (by positivity)
      _ = (n : ℝ) ^ n := Real.rpow_natCast _ _
  have hΓ : ‖Gammaℝ (w + 1)‖ ≤ (n : ℝ) ^ n := by
    refine (norm_Gammaℝ_le (by simp; linarith)).trans ?_
    have e : (w + 1).re = w.re + 1 := by simp
    rw [e]
    refine (rGamma_le (n := n) (by linarith) (by linarith)).trans ?_
    exact_mod_cast Nat.factorial_le_pow n
  have hL : ‖LFunction chi4 w‖ ≤ (n : ℝ) ^ n := by
    refine (norm_LFunction_chi4_le (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : (2 : ℝ) * n ≤ (n : ℝ) ^ n := by
      have hn2' : 2 ≤ n := by exact_mod_cast hn2
      have h1 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ n := pow_le_pow_right₀ (by linarith) hn2'
      nlinarith
    nlinarith
  calc ‖(4 : ℂ) ^ (w / 2)‖ * (‖Gammaℝ (w + 1)‖ * ‖LFunction chi4 w‖)
      ≤ (n : ℝ) ^ n * ((n : ℝ) ^ n * (n : ℝ) ^ n) := by gcongr
    _ = (n : ℝ) ^ (3 * n) := by ring

/-- `(x + 5)√(x + 5) ≤ 4x√x + 64` for `x ≥ 0`. -/
theorem shift_five {x : ℝ} (hx : 0 ≤ x) :
    (x + 5) * Real.sqrt (x + 5) ≤ 4 * (x * Real.sqrt x) + 64 := by
  have hu0 := Real.sqrt_nonneg x
  have hv0 := Real.sqrt_nonneg (x + 5)
  rcases le_total 5 x with h | h
  · have hvu : Real.sqrt (x + 5) ≤ 3 / 2 * Real.sqrt x := by
      rw [show 3 / 2 * Real.sqrt x = Real.sqrt ((3 / 2) ^ 2 * x) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have : (x + 5) * Real.sqrt (x + 5) ≤ 2 * x * (3 / 2 * Real.sqrt x) :=
      mul_le_mul (by linarith) hvu hv0 (by linarith)
    nlinarith [mul_nonneg hx hu0]
  · have hv : Real.sqrt (x + 5) ≤ 4 := by
      rw [show (4 : ℝ) = Real.sqrt 16 by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have : (x + 5) * Real.sqrt (x + 5) ≤ 10 * 4 := mul_le_mul (by linarith) hv hv0 (by norm_num)
    nlinarith [mul_nonneg hx hu0]

/-! ## The even function `f(z) = Λ*(½ + iz)Λ*(½ − iz)` -/

/-- `f(z) = Λ*(½ + iz)Λ*(½ − iz)`. -/
def fL (z : ℂ) : ℂ := Lam (1 / 2 + I * z) * Lam (1 / 2 - I * z)

theorem fL_even (z : ℂ) : fL (-z) = fL z := by
  unfold fL; rw [mul_comm]; congr 2 <;> ring

theorem fL_eq (z : ℂ) : fL z = rootNumber chi4 * Lam (1 / 2 + I * z) ^ 2 := by
  unfold fL
  rw [show 1 / 2 - I * z = 1 - (1 / 2 + I * z) by ring, Lam_one_sub]; ring

theorem differentiable_fL : Differentiable ℂ fL :=
  (differentiable_Lam.comp ((differentiable_const _).add (differentiable_const _ |>.mul
    differentiable_id))).mul
  (differentiable_Lam.comp ((differentiable_const _).sub (differentiable_const _ |>.mul
    differentiable_id)))

theorem Lam_half_ne : Lam (1 / 2) ≠ 0 := by
  unfold Lam
  rw [completed_eq (by norm_num)]
  refine mul_ne_zero (by simp) (mul_ne_zero (Gammaℝ_ne_zero_of_re_pos (by norm_num)) ?_)
  have := LFunction_chi4_pos (σ := 1 / 2) (by norm_num)
  simpa using this

theorem fL_zero_ne : fL 0 ≠ 0 := by
  unfold fL; simp only [mul_zero, add_zero, sub_zero]
  exact mul_ne_zero Lam_half_ne Lam_half_ne

theorem rootNumber_ne : rootNumber chi4 ≠ 0 := fun h => by
  have := fL_eq 0; rw [h, zero_mul] at this; exact fL_zero_ne this

/-- **The order of `f`**: `‖f(z)‖ ≤ (‖ε‖ + 1)e^{768}·exp(48‖z‖^{3/2})`. -/
theorem norm_fL_le (z : ℂ) :
    ‖fL z‖ ≤ (‖rootNumber chi4‖ + 1) * Real.exp 768 * Real.exp (48 * ‖z‖ ^ (3 / 2 : ℝ)) := by
  set x := ‖z‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg z
  -- a point `w = ½ ± iz` with `Re w ≥ ½` and `‖f z‖ = ‖ε‖‖Λ*(w)‖²`
  obtain ⟨w, hw, hwn, hfw⟩ : ∃ w : ℂ, 1 / 2 ≤ w.re ∧ ‖w‖ ≤ 1 / 2 + x ∧
      fL z = rootNumber chi4 * Lam w ^ 2 := by
    have hn1 : ‖1 / 2 + I * z‖ ≤ 1 / 2 + x := (norm_add_le _ _).trans (by simp [hx])
    have hn2 : ‖1 / 2 + I * -z‖ ≤ 1 / 2 + x := (norm_add_le _ _).trans (by simp [hx])
    rcases le_total (1 / 2) (1 / 2 + I * z).re with h | h
    · exact ⟨_, h, hn1, fL_eq z⟩
    · refine ⟨1 / 2 + I * -z, ?_, hn2, by rw [← fL_eq, fL_even]⟩
      simp only [add_re, mul_re, I_re, I_im, neg_re, neg_im] at h ⊢; norm_num at h ⊢; linarith
  set N : ℕ := ⌈x⌉₊ + 4
  have hNx : (N : ℝ) ≤ x + 5 := by
    have := Nat.ceil_lt_add_one hx0; simp only [N]; push_cast; linarith
  have hxN : x + 4 ≤ (N : ℝ) := by
    have := Nat.le_ceil x; simp only [N]; push_cast; linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hL := norm_Lam_le hw (n := N) (by linarith)
  have hL2 : ‖Lam w‖ ^ 2 ≤ Real.exp (12 * ((N : ℝ) * Real.sqrt N)) := by
    calc ‖Lam w‖ ^ 2 ≤ ((N : ℝ) ^ (3 * N)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hL 2
      _ = Real.exp ((6 * N : ℝ) * Real.log N) := by
          rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hN0]; push_cast; ring_nf
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          have hl := log_le_two_sqrt hN0
          nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hNs : (N : ℝ) * Real.sqrt N ≤ 4 * (x * Real.sqrt x) + 64 :=
    le_trans (mul_le_mul hNx (Real.sqrt_le_sqrt hNx) (Real.sqrt_nonneg _) (by linarith))
      (shift_five hx0)
  have hx32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hx0 (by norm_num), Real.rpow_one]
  rw [hx32, hfw, norm_mul, norm_pow]
  calc ‖rootNumber chi4‖ * ‖Lam w‖ ^ 2 ≤ (‖rootNumber chi4‖ + 1) * Real.exp (12 * ((N : ℝ) * Real.sqrt N)) :=
        mul_le_mul (by linarith) hL2 (by positivity) (by positivity)
    _ ≤ (‖rootNumber chi4‖ + 1) * Real.exp (12 * (4 * (x * Real.sqrt x) + 64)) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-! ## Growth along the reals, and the zero -/

/-- **`‖Λ*(2k + 1)‖ ≥ (4/π)^k/3`.** -/
theorem norm_Lam_odd_ge (k : ℕ) : (4 / π) ^ k / 3 ≤ ‖Lam ((2 * k + 1 : ℝ) : ℂ)‖ := by
  set σ : ℝ := 2 * k + 1
  have hσ1 : 1 ≤ σ := by simp only [σ]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hπ := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  unfold Lam
  rw [completed_eq (by simp; linarith), norm_mul, norm_mul]
  have h4 : ‖(4 : ℂ) ^ ((σ : ℂ) / 2)‖ = 2 * 4 ^ k := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    have e : ((σ : ℂ) / 2).re = σ / 2 := by simp
    rw [e, show σ / 2 = (k : ℝ) + 1 / 2 by simp only [σ]; ring, Real.rpow_add (by norm_num),
      Real.rpow_natCast, show (4 : ℝ) ^ (1 / 2 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
    ring
  have hΓ : π⁻¹ ^ (k + 1) ≤ ‖Gammaℝ ((σ : ℂ) + 1)‖ := by
    rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have e1 : ((σ : ℂ) + 1) / 2 = ((k : ℕ) : ℂ) + 1 := by
      simp only [σ]; push_cast; ring
    have e2 : (-((σ : ℂ) + 1) / 2).re = -((k : ℝ) + 1) := by simp [σ]; ring
    rw [e1, e2, Complex.Gamma_nat_eq_factorial, Complex.norm_natCast,
      Real.rpow_neg Real.pi_pos.le, show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, inv_pow]
    have : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
    have : 0 ≤ (π ^ (k + 1))⁻¹ := by positivity
    nlinarith
  have hL : 2 / 3 ≤ ‖LFunction chi4 σ‖ := by
    have h := (LFunction_chi4_real_ge (σ := σ) (by linarith)).1
    have h3 : (3 : ℝ) ^ (-σ) ≤ 1 / 3 := by
      rw [Real.rpow_neg (by norm_num), one_div]
      have h33 : (3 : ℝ) ≤ 3 ^ σ := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hσ1
      exact inv_anti₀ (by norm_num) h33
    exact le_trans (by linarith) (h.trans (Complex.re_le_norm _))
  rw [h4]
  have hpk : (4 / π) ^ k / 3 = 4 ^ k * (π⁻¹ ^ (k + 1)) * (π / 3) := by
    have hπ0 := Real.pi_ne_zero
    rw [inv_pow, pow_succ, div_pow]; field_simp
  rw [hpk]
  have hpos : 0 ≤ 4 ^ k * π⁻¹ ^ (k + 1) := by positivity
  calc 4 ^ k * π⁻¹ ^ (k + 1) * (π / 3) ≤ 4 ^ k * π⁻¹ ^ (k + 1) * (4 / 3) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos
    _ = 2 * 4 ^ k * (π⁻¹ ^ (k + 1) * (2 / 3)) := by ring
    _ ≤ 2 * 4 ^ k * (‖Gammaℝ ((σ : ℂ) + 1)‖ * ‖LFunction chi4 σ‖) := by gcongr

/-- **`L(s, χ₄)` has a zero with `½ ≤ Re ρ < 1`.** If not, `f` has no zeros, so by Hadamard
(`hadamardW_even`) `f` is constant, i.e. `‖Λ*(σ)‖` is constant on the reals; but
`‖Λ*(2k + 1)‖ ≥ (4/π)^k/3`. -/
theorem exists_zero_chi4 : ∃ ρ : ℂ, LFunction chi4 ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
  by_contra hno
  push Not at hno
  -- `L(ρ) = 0` forces `Re ρ < ½` (as `Re ρ < 1` always)
  have hlt : ∀ ρ, LFunction chi4 ρ = 0 → ρ.re < 1 / 2 := fun ρ h => by
    by_contra h'; push Not at h'
    have h1 : ρ.re < 1 := by
      by_contra h''; exact LFunction_ne_zero_of_one_le_re chi4 (.inl chi4_ne_one) (not_lt.1 h'') h
    exact absurd h1 (not_lt.2 (hno ρ h h'))
  -- so `Λ*` has no zeros
  have hLam : ∀ w, Lam w ≠ 0 := by
    intro w hw
    have hw' : Lam (1 - w) = 0 := by rw [Lam_one_sub, hw, mul_zero]
    have key : ∀ v, Lam v = 0 → 1 / 2 ≤ v.re → False := fun v hv hre => by
      unfold Lam at hv
      rw [completed_eq (by linarith)] at hv
      rcases mul_eq_zero.1 hv with h | h
      · rw [cpow_eq_zero_iff] at h; norm_num at h
      · rcases mul_eq_zero.1 h with h | h
        · exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith) h
        · linarith [hlt v h]
    rcases le_total (1 / 2) w.re with h | h
    · exact key w hw h
    · exact key (1 - w) hw' (by simp; linarith)
  have hfne : ∀ z, fL z ≠ 0 := fun z => mul_ne_zero (hLam _) (hLam _)
  -- Hadamard: `f` is constant
  have H := hadamardW_even differentiable_fL fL_even fL_zero_ne (C := (‖rootNumber chi4‖ + 1) * Real.exp 768)
    (A := 48) (β := 3 / 2) (by nlinarith [norm_nonneg (rootNumber chi4), Real.add_one_le_exp (768 : ℝ)])
    (by norm_num) (by norm_num) (by norm_num) norm_fL_le
  have : IsEmpty (ZeroIdx (sqF fL)) := ⟨fun i => by
    have h := (ordN_ne_zero_iff (sqF_differentiable differentiable_fL fL_even)
      (by rw [sqF_zero]; exact fL_zero_ne) i.1).1 (Nat.pos_iff_ne_zero.1 (Fin.pos i.2))
    exact hfne _ h⟩
  have hconst : ∀ z, fL z = fL 0 := fun z => by
    have := (H.prod z).unique hasProd_empty
    rwa [div_eq_one_iff_eq fL_zero_ne] at this
  -- but `‖Λ*(2k + 1)‖` is unbounded
  set K := ‖fL 0‖ / ‖rootNumber chi4‖
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (3 * (K + 1)) (show 1 < 4 / π by
    rw [lt_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four])
  have hge := norm_Lam_odd_ge k
  set σ : ℝ := 2 * k + 1
  have hz : fL (-I * ((σ : ℂ) - 1 / 2)) = rootNumber chi4 * Lam σ ^ 2 := by
    rw [fL_eq]; congr 2
    rw [show I * (-I * ((σ : ℂ) - 1 / 2)) = -(I * I) * ((σ : ℂ) - 1 / 2) by ring, I_mul_I]; ring
  rw [hconst] at hz
  have hn : ‖Lam σ‖ ^ 2 = K := by
    simp only [K]; rw [hz, norm_mul, norm_pow]
    field_simp [norm_ne_zero_iff.2 rootNumber_ne]
  have hK0 : 0 ≤ K := by positivity
  have h1 : ‖Lam σ‖ ≤ K + 1 := by nlinarith [norm_nonneg (Lam σ)]
  have h2 : (4 / π) ^ k / 3 ≤ K + 1 := hge.trans h1
  linarith

/-! ## The race mod 4, unconditionally -/

/-- **The prime race mod 4 changes lead infinitely often (Littlewood 1914, `ψ`-form).** For every
`0 < θ < ½`, `c` and `X`, there are `x, x' > X` with `ψ(x; 4, 1) − ψ(x; 4, 3) > c·x^θ` and
`ψ(x'; 4, 1) − ψ(x'; 4, 3) < −c·x'^θ`. -/
theorem race_four_half {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 1 / 2) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < psiAP 4 1 x - psiAP 4 3 x) ∧
      (∃ x, X < x ∧ psiAP 4 1 x - psiAP 4 3 x < -(c * x ^ θ)) := by
  obtain ⟨ρ, hρ, hre, -⟩ := exists_zero_chi4
  exact race_four hρ hθ (by linarith) (fun σ hσ _ => LFunction_chi4_pos (by linarith)) c X

end PsiOmega

#print axioms PsiOmega.exists_zero_chi4
#print axioms PsiOmega.race_four_half

#print axioms PsiOmega.LFunction_chi4_eq
#print axioms PsiOmega.LFunction_chi4_real_ge
