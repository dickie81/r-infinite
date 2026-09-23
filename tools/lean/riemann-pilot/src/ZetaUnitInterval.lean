import Mathlib

/-! # `ζ(σ) ≠ 0` for `0 < σ < 1`, from Mathlib's theta-kernel definition of `ζ`

Mathlib defines `ζ` through the completed function `Λ(s) = P.Λ(s/2)/2`, where `P` is the FE-pair
of the theta kernel `θ(x) = Σ_{n∈ℤ} e^{−πn²x}` (`HurwitzZeta.evenKernel 0`), with `f₀ = g₀ = 1`,
`k = ½`, `ε = 1`:
`P.Λ(t) = ∫₀^∞ x^{t−1} h(x) dx − 1/t − 1/(½ − t)`,
`h = θ − 1` on `(1, ∞)` and `h = θ − x^{−½}` on `(0, 1)`.

For `0 < t < ½` both correction terms are integrals, `1/t = ∫₀¹ x^{t−1}` and
`1/(½ − t) = ∫₁^∞ x^{t−1}x^{−½}`, so `P.Λ(t) = ∫₀^∞ x^{t−1}(h − m)` with `m = 1` on `(0, 1)` and
`m = x^{−½}` on `(1, ∞)`. The integrand is negative:
* on `(1, ∞)`, `θ − 1 < x^{−½}`;
* on `(0, 1)`, `θ(x) − x^{−½} = x^{−½}(θ(1/x) − 1) < 1`, by the functional equation.

Both are the single bound `√y (θ(y) − 1) < 1` for `y ≥ 1`. That follows from
`θ(y) − 1 ≤ 2q/(1 − q)`, `q = e^{−πy}` (since `n² ≥ |n|`), together with `√y q ≤ e^{(1−π)y} ≤ e^{−2}`.
Hence `Λ(σ)` is a negative real, and `ζ(σ) = Λ(σ)/Γ_ℝ(σ) ≠ 0` (`Γ_ℝ(σ) ≠ 0`).
-/

open Real Complex MeasureTheory Set Filter HurwitzZeta

noncomputable section

namespace ZetaUnitInterval

/-- `θ(y) − 1 = Σ_{n ≠ 0} e^{−πn²y}`. -/
theorem hasSum_theta_sub_one {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => if n = 0 then 0 else rexp (-π * (n : ℝ) ^ 2 * y)) (evenKernel 0 y - 1) := by
  have h := hasSum_int_evenKernel₀ 0 hy
  simp only [add_zero, Int.cast_eq_zero, QuotientAddGroup.mk_zero, ite_true] at h
  exact h

theorem theta_sub_one_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ evenKernel 0 y - 1 :=
  (hasSum_theta_sub_one hy).nonneg fun n => by split_ifs <;> positivity

/-- `θ(y) − 1 ≤ 2q/(1 − q)` with `q = e^{−πy}`. -/
theorem theta_sub_one_le {y : ℝ} (hy : 0 < y) :
    evenKernel 0 y - 1 ≤ rexp (-π * y) / (1 - rexp (-π * y)) + rexp (-π * y) / (1 - rexp (-π * y)) := by
  set q := rexp (-π * y) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
  have hgeo : HasSum (fun n : ℕ => q ^ (n + 1)) (q / (1 - q)) := by
    have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left q
    convert this using 1
    · funext n; ring
    · rw [div_eq_mul_inv]
  set b : ℤ → ℝ := fun n => if n = 0 then 0 else q ^ n.natAbs with hb
  have hbpos : HasSum (fun n : ℕ => b n) (q / (1 - q)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, hb, Nat.cast_zero, ite_true, sub_zero]
    convert hgeo using 1
    funext n
    rw [Int.natAbs_natCast]
    simp only [show ((n + 1 : ℕ) : ℤ) ≠ 0 by omega, ↓reduceIte]
  have hbneg : HasSum (fun n : ℕ => b (-(n + 1))) (q / (1 - q)) := by
    convert hgeo using 1
    funext n
    simp only [hb]
    simp only [show (-((n : ℤ) + 1)) ≠ 0 by omega, ↓reduceIte]
    congr 1
  have hbsum := hbpos.of_nat_of_neg_add_one hbneg
  refine hasSum_le (fun n => ?_) (hasSum_theta_sub_one hy) hbsum
  simp only [hb]
  split_ifs with h0
  · exact le_rfl
  · rw [hq, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hn : (1 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.2 h0
    have hsq : (n : ℝ) ^ 2 = (n.natAbs : ℝ) ^ 2 := by
      rw [← Int.cast_natCast n.natAbs, ← Int.cast_pow, ← Int.cast_pow, Int.natAbs_sq]
    rw [hsq]
    set k : ℝ := (n.natAbs : ℝ)
    have hk : k ≤ k ^ 2 := by nlinarith
    have hpy : 0 < π * y := mul_pos Real.pi_pos hy
    have := mul_le_mul_of_nonneg_left hk hpy.le
    nlinarith

/-- **The key bound**: `√y (θ(y) − 1) < 1` for `y ≥ 1`. -/
theorem theta_bound {y : ℝ} (hy : 1 ≤ y) : y ^ (1 / 2 : ℝ) * (evenKernel 0 y - 1) < 1 := by
  have hy0 : 0 < y := by linarith
  set q := rexp (-π * y) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hpi := Real.pi_gt_three
  -- `q ≤ e^{−3} < 1/2`
  have hq_half : q < 1 / 2 := by
    have h1 : q ≤ rexp (-3) := Real.exp_le_exp.2 (by nlinarith)
    have h2 : rexp (-3) < 1 / 2 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      have := Real.add_one_le_exp 3; linarith
    linarith
  -- `√y · q ≤ e^{y} e^{−πy} ≤ e^{−2} < 1/7`
  have hsqrt : y ^ (1 / 2 : ℝ) ≤ y := by
    have := Real.rpow_le_rpow_of_exponent_le hy (by norm_num : (1 / 2 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  have hyexp : y ≤ rexp y := by linarith [Real.add_one_le_exp y]
  have hsq_q : y ^ (1 / 2 : ℝ) * q < 1 / 7 := by
    have h1 : y ^ (1 / 2 : ℝ) * q ≤ rexp y * q :=
      mul_le_mul_of_nonneg_right (hsqrt.trans hyexp) hq0.le
    have h2 : rexp y * q = rexp (y - π * y) := by rw [hq, ← Real.exp_add]; ring_nf
    have h3 : rexp (y - π * y) ≤ rexp (-2) := Real.exp_le_exp.2 (by nlinarith)
    have h4 : rexp (-2) < 1 / 7 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      have he := Real.exp_one_gt_d9
      have : rexp 2 = rexp 1 * rexp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith
    linarith
  have hle := theta_sub_one_le hy0
  rw [← hq] at hle
  have hsq0 : 0 ≤ y ^ (1 / 2 : ℝ) := by positivity
  have hden : 1 / 2 < 1 - q := by linarith
  calc y ^ (1 / 2 : ℝ) * (evenKernel 0 y - 1)
      ≤ y ^ (1 / 2 : ℝ) * (q / (1 - q) + q / (1 - q)) := mul_le_mul_of_nonneg_left hle hsq0
    _ = 2 * (y ^ (1 / 2 : ℝ) * q) / (1 - q) := by ring
    _ < 1 := by
      rw [div_lt_one (by linarith)]
      linarith

/-! ## The two pointwise bounds -/

theorem upper_piece {x : ℝ} (hx : 1 < x) : evenKernel 0 x - 1 < x ^ (-(1 / 2 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have h := theta_bound hx.le
  have hp : 0 < x ^ (1 / 2 : ℝ) := by positivity
  rw [Real.rpow_neg hx0.le, ← one_div, lt_div_iff₀ hp, mul_comm]
  exact h

/-- `θ(x) − x^{−½} = x^{−½}(θ(1/x) − 1)` (functional equation). -/
theorem lower_piece_eq {x : ℝ} (hx0 : 0 < x) :
    evenKernel 0 x - x ^ (-(1 / 2 : ℝ)) = (1 / x) ^ (1 / 2 : ℝ) * (evenKernel 0 (1 / x) - 1) := by
  have hfe := evenKernel_functional_equation 0 x
  rw [← evenKernel_eq_cosKernel_of_zero] at hfe
  rw [hfe, Real.rpow_neg hx0.le, Real.div_rpow zero_le_one hx0.le, Real.one_rpow]
  ring

theorem lower_piece {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : evenKernel 0 x - x ^ (-(1 / 2 : ℝ)) < 1 := by
  rw [lower_piece_eq hx0]
  exact theta_bound (by rw [le_div_iff₀ hx0]; linarith)

theorem lower_piece_nonneg {x : ℝ} (hx0 : 0 < x) : 0 ≤ evenKernel 0 x - x ^ (-(1 / 2 : ℝ)) := by
  rw [lower_piece_eq hx0]
  exact mul_nonneg (by positivity) (theta_sub_one_nonneg (by positivity))

/-! ## Mathlib's `f_modif` for the theta kernel, as a real function -/

/-- The real version of `(hurwitzEvenFEPair 0).f_modif`. -/
def hmod (x : ℝ) : ℝ :=
  (Ioi 1).indicator (fun x => evenKernel 0 x - 1) x
    + (Ioo 0 1).indicator (fun x => evenKernel 0 x - x ^ (-(1 / 2 : ℝ))) x

/-- The comparison function: `1` on `(0, 1)`, `x^{−½}` on `(1, ∞)`. -/
def mcmp (x : ℝ) : ℝ :=
  (Ioi 1).indicator (fun x => x ^ (-(1 / 2 : ℝ))) x + (Ioo 0 1).indicator (fun _ => (1 : ℝ)) x

theorem f_modif_eq (x : ℝ) : (hurwitzEvenFEPair 0).f_modif x = ((hmod x : ℝ) : ℂ) := by
  simp only [WeakFEPair.f_modif, hurwitzEvenFEPair, hmod, Pi.add_apply, Set.indicator_apply,
    Function.comp_apply, ite_true]
  split_ifs <;> push_cast <;> ring

theorem hmod_le_mcmp {x : ℝ} (hx : 0 < x) : hmod x ≤ mcmp x := by
  unfold hmod mcmp
  rcases lt_trichotomy x 1 with h | h | h
  · simp only [Set.indicator_apply, mem_Ioi, mem_Ioo, show ¬ 1 < x by linarith, hx, h, and_self,
      ite_true, ite_false, zero_add]
    exact (lower_piece hx h).le
  · subst h; simp
  · simp only [Set.indicator_apply, mem_Ioi, mem_Ioo, h, show ¬ x < 1 by linarith, and_false,
      ite_true, ite_false, add_zero]
    exact (upper_piece h).le

theorem hmod_lt_mcmp {x : ℝ} (hx : 1 < x) : hmod x < mcmp x := by
  unfold hmod mcmp
  simp only [Set.indicator_apply, mem_Ioi, mem_Ioo, hx, show ¬ x < 1 by linarith, and_false,
    ite_true, ite_false, add_zero]
  exact upper_piece hx

/-! ## The integrals -/

theorem Lambda0_eq (t : ℝ) :
    (hurwitzEvenFEPair 0).Λ₀ t = ((∫ x in Ioi 0, x ^ (t - 1) * hmod x : ℝ) : ℂ) := by
  unfold WeakFEPair.Λ₀ mellin
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [f_modif_eq, smul_eq_mul]
  rw [ofReal_mul, ofReal_cpow (le_of_lt hx)]
  push_cast; ring_nf

theorem integrable_F (t : ℝ) : IntegrableOn (fun x => x ^ (t - 1) * hmod x) (Ioi 0) := by
  have hc := ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin (t : ℂ)).1
  have h2 : IntegrableOn (fun x : ℝ => ((x ^ (t - 1) * hmod x : ℝ) : ℂ)) (Ioi 0) := by
    refine hc.congr_fun (fun x hx => ?_) measurableSet_Ioi
    show (x : ℂ) ^ ((t : ℂ) - 1) • (hurwitzEvenFEPair 0).f_modif x = _
    rw [f_modif_eq, smul_eq_mul, ofReal_mul, ofReal_cpow (le_of_lt hx)]
    push_cast; ring_nf
  simpa using h2.re

theorem integrable_G {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    IntegrableOn (fun x => x ^ (t - 1) * mcmp x) (Ioi 0) := by
  have hA : IntegrableOn (fun x : ℝ => x ^ (t - 1) * x ^ (-(1 / 2 : ℝ))) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by linarith : t - 3 / 2 < -1) one_pos).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    rw [← Real.rpow_add (by simp at hx; linarith)]; ring_nf
  have hB : IntegrableOn (fun x : ℝ => x ^ (t - 1)) (Ioo 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < t - 1)).1.mono_set
      Ioo_subset_Ioc_self
  have hsum := ((hA.integrable_indicator measurableSet_Ioi).add
    (hB.integrable_indicator measurableSet_Ioo)).integrableOn (s := Ioi 0)
  refine hsum.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, mcmp, Set.indicator_apply]
  split_ifs <;> ring

theorem integral_G {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    ∫ x in Ioi 0, x ^ (t - 1) * mcmp x = 1 / t + 1 / (1 / 2 - t) := by
  have hA : IntegrableOn (fun x : ℝ => x ^ (t - 1) * x ^ (-(1 / 2 : ℝ))) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by linarith : t - 3 / 2 < -1) one_pos).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    rw [← Real.rpow_add (by simp at hx; linarith)]; ring_nf
  have hB : IntegrableOn (fun x : ℝ => x ^ (t - 1)) (Ioo 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < t - 1)).1.mono_set
      Ioo_subset_Ioc_self
  have hsplit : (fun x => x ^ (t - 1) * mcmp x)
      = fun x => (Ioi 1).indicator (fun x : ℝ => x ^ (t - 1) * x ^ (-(1 / 2 : ℝ))) x
          + (Ioo 0 1).indicator (fun x : ℝ => x ^ (t - 1)) x := by
    funext x; simp only [mcmp, Set.indicator_apply]; split_ifs <;> ring
  rw [hsplit, integral_add ((hA.integrable_indicator measurableSet_Ioi).integrableOn)
    ((hB.integrable_indicator measurableSet_Ioo).integrableOn),
    setIntegral_indicator measurableSet_Ioi, setIntegral_indicator measurableSet_Ioo,
    Ioi_inter_Ioi, show max (0 : ℝ) 1 = 1 by norm_num,
    Set.inter_eq_right.2 Ioo_subset_Ioi_self]
  have h1 : ∫ x in Ioi (1 : ℝ), x ^ (t - 1) * x ^ (-(1 / 2 : ℝ)) = 1 / (1 / 2 - t) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x : ℝ => x ^ (t - 3 / 2))
      (fun x hx => by rw [← Real.rpow_add (by simp at hx; linarith)]; ring_nf),
      integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show t - 3 / 2 + 1 = -(1 / 2 - t) by ring, neg_div_neg_eq]
  have h2 : ∫ x in Ioo (0 : ℝ) 1, x ^ (t - 1) = 1 / t := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith)), Real.one_rpow, Real.zero_rpow (by linarith),
      sub_zero, sub_add_cancel]
  rw [h1, h2]; ring

theorem integral_F_lt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    ∫ x in Ioi 0, x ^ (t - 1) * hmod x < 1 / t + 1 / (1 / 2 - t) := by
  rw [← integral_G ht0 ht1]
  have hF := integrable_F t
  have hG := integrable_G ht0 ht1
  have hpos : 0 < ∫ x in Ioi 0, (x ^ (t - 1) * mcmp x - x ^ (t - 1) * hmod x) := by
    rw [integral_pos_iff_support_of_nonneg_ae]
    · refine lt_of_lt_of_le ?_ (measure_mono (s := Ioi (1 : ℝ)) fun x hx => ?_)
      · rw [Measure.restrict_apply measurableSet_Ioi, Ioi_inter_Ioi,
          show max (1 : ℝ) 0 = 1 by norm_num, Real.volume_Ioi]
        exact WithTop.top_pos
      · have hx1 : (1 : ℝ) < x := hx
        have := hmod_lt_mcmp hx1
        have hp : 0 < x ^ (t - 1) := Real.rpow_pos_of_pos (by linarith) _
        simp only [Function.mem_support]
        nlinarith
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
      have := hmod_le_mcmp (show 0 < x from hx)
      have hp : 0 < x ^ (t - 1) := Real.rpow_pos_of_pos hx _
      simp only [Pi.zero_apply]
      nlinarith
    · exact hG.sub hF
  rw [integral_sub hG hF] at hpos
  linarith

/-! ## The theorem -/

/-- **`Λ(σ) < 0` for `0 < σ < 1`** (Mathlib's `completedRiemannZeta`). -/
theorem completedRiemannZeta_re_neg {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    completedRiemannZeta σ = ((∫ x in Ioi 0, x ^ (σ / 2 - 1) * hmod x : ℝ) - 1 / (σ / 2)
      - 1 / (1 / 2 - σ / 2) : ℝ) / 2 ∧
      (∫ x in Ioi 0, x ^ (σ / 2 - 1) * hmod x : ℝ) - 1 / (σ / 2) - 1 / (1 / 2 - σ / 2) < 0 := by
  refine ⟨?_, by linarith [integral_F_lt (t := σ / 2) (by linarith) (by linarith)]⟩
  rw [completedRiemannZeta, completedHurwitzZetaEven, WeakFEPair.Λ,
    show (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) by push_cast; ring, Lambda0_eq]
  simp only [hurwitzEvenFEPair, ite_true, smul_eq_mul, mul_one, one_div]
  push_cast; ring

/-- **`ζ(σ) ≠ 0` for `0 < σ < 1`.** -/
theorem riemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  obtain ⟨heq, hneg⟩ := completedRiemannZeta_re_neg h0 h1
  rw [riemannZeta_def_of_ne_zero (by exact_mod_cast h0.ne')]
  refine div_ne_zero ?_ (Gammaℝ_ne_zero_of_re_pos (by simpa using h0))
  rw [heq]
  refine div_ne_zero ?_ two_ne_zero
  exact_mod_cast hneg.ne

end ZetaUnitInterval

#print axioms ZetaUnitInterval.theta_bound
#print axioms ZetaUnitInterval.integral_F_lt
#print axioms ZetaUnitInterval.riemannZeta_ne_zero_of_mem_Ioo
