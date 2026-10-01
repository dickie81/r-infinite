import WeilChiDensity
import ArchShift
import StrictPositivity
import ZeroLocal
import SixteenPi
import KaiserNine

/-! # `GoodChar.half` from `hS`; kernel identities; sharper local constants (round 246)

`hS` at `σ = ½` is `GoodChar.half`, so the `χ` criteria need no separate central-value hypothesis (`goodChar_of_hS`, `grh_iff_twins'`, `weil_criterion_chi'`); `GRH'` (GRH off the real axis) and `grh_half_iff`; `Q_χ ≥ 0` under `GoodChar` and `GRH'`, with no real-zero hypothesis beyond `GoodChar.half`; the archimedean kernels `kerK = archKer ¼`, `archKer ¼ + archKer ¾ = 1/sinh(u/2)`; the local zero count `card_local_le_sharp` with `5/2` in place of `13/2`; `lam_nine` in `SixteenPi`'s `fBalExp` form.
-/

open Real Complex MeasureTheory Filter Topology Set

noncomputable section

/-! ## (A), (B) -/

namespace ChiHalf

open PsiOmega DirichletCharacter Pilot1ca Pilot1bt PilotWeil

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- `GoodChar` from its first three fields and `hS`: the field `half` is `hS (1/2)`. -/
theorem goodChar_of_hS (h1 : χ ≠ 1) (hq : χ.IsQuadratic) (hp : χ.IsPrimitive)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) : GoodChar χ :=
  ⟨h1, hq, hp, by simpa using hS (1 / 2) (by norm_num) (by norm_num)⟩

/-- `grh_iff_twins` with no central-value hypothesis. -/
theorem grh_iff_twins' (h1 : χ ≠ 1) (hq : χ.IsQuadratic) (hp : χ.IsPrimitive)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) :
    GRH χ ↔ ∀ l : ℝ, 0 ≤ l → 0 ≤ QC χ (l + 1) (twin (box 1) l) :=
  grh_iff_twins (goodChar_of_hS h1 hq hp hS) hS

/-- `weil_criterion_chi` with no central-value hypothesis. -/
theorem weil_criterion_chi' (h1 : χ ≠ 1) (hq : χ.IsQuadratic) (hp : χ.IsPrimitive)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) :
    (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ QC χ a g) ↔ GRH χ :=
  weil_criterion_chi (goodChar_of_hS h1 hq hp hS) hS

/-- GRH for the non-real zeros only. -/
def GRH' (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.im ≠ 0 → s.re = 1 / 2

/-- **The decomposition**: `GRH ∧ L(½) ≠ 0 ⟺ GRH' ∧ hS`. -/
theorem grh_half_iff :
    (GRH χ ∧ LFunction χ (1 / 2) ≠ 0) ↔
      (GRH' χ ∧ ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) := by
  constructor
  · rintro ⟨hG, hh⟩
    refine ⟨fun s hs h0 h1 _ => hG s hs h0 h1, fun σ h0 h1 hz => ?_⟩
    have hσ : σ = 1 / 2 := by
      have := hG (σ : ℂ) hz (by simpa using h0) (by simpa using h1)
      simpa using this
    subst hσ
    exact hh (by simpa using hz)
  · rintro ⟨h', hS⟩
    refine ⟨fun s hs h0 h1 => ?_, by simpa using hS (1 / 2) (by norm_num) (by norm_num)⟩
    by_cases him : s.im = 0
    · have e : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [e] at hs
      exact absurd hs (hS s.re h0 h1)
    · exact h' s hs h0 h1 him

/-- `ĝ(iy)` is real for every real probe `g` and real `y`. -/
theorem ghatC_mul_I_im (g : ℝ → ℝ) (a y : ℝ) : (ghatC g a ((y : ℂ) * I)).im = 0 := by
  have h : ∀ u : ℝ, ((g u : ℝ) : ℂ) * cexp (I * ((y : ℂ) * I) * u)
      = ((g u * Real.exp (-(y * u)) : ℝ) : ℂ) := by
    intro u
    have e : I * ((y : ℂ) * I) * (u : ℂ) = ((-(y * u) : ℝ) : ℂ) := by
      push_cast; linear_combination ((y : ℂ) * u) * Complex.I_sq
    rw [e, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  unfold ghatC
  simp_rw [h]
  rw [intervalIntegral.integral_ofReal]
  exact Complex.ofReal_im _

/-- **Real zeros are invisible to the `ĝ²` form**: under GRH for the non-real zeros only,
`Q_χ(g) ≥ 0` for every probe with a strip test — whatever the real zeros in `(0, 1)` other than `½` are (`hG : GoodChar χ` excludes `½`). -/
theorem QC_nonneg_of_GRH' (hG : GoodChar χ) (h' : GRH' χ) {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g)
    (ha : 0 < a) {K : ℝ} (hK : StripTest (fun z => ghatC g a z ^ 2) K) : 0 ≤ QC χ a g := by
  have h := (QC_hasSum hG hp ha hK).mapL Complex.reCLM
  simp only [Complex.reCLM_apply, ofReal_re] at h
  refine h.nonneg fun i => ?_
  by_cases hi : (tauC i).im = 0
  · have e : tauC i = ((tauC i).re : ℂ) := Complex.ext (by simp) (by simp [hi])
    rw [e, hsq_ofReal hp ha.le]
    simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (by norm_num) (hsq_nonneg _)
  · obtain ⟨hz, h0, h1⟩ := zero_of_tau hG i
    have hre : (1 / 2 + I * tauC i).re = 1 / 2 - (tauC i).im := by simp; ring
    have him : (1 / 2 + I * tauC i).im = (tauC i).re := by simp
    have hre0 : (tauC i).re = 0 := by
      by_contra hne
      have := h' _ hz h0 h1 (by rw [him]; exact hne)
      rw [hre] at this
      exact hi (by linarith)
    have e : tauC i = (((tauC i).im : ℝ) : ℂ) * I := Complex.ext (by simp [hre0]) (by simp)
    rw [e]
    set z := ghatC g a (((tauC i).im : ℝ) * I) with hzdef
    have hz0 : z.im = 0 := ghatC_mul_I_im g a _
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
    rw [hz', show (2 : ℂ) * (z.re : ℂ) ^ 2 = ((2 * z.re ^ 2 : ℝ) : ℂ) by push_cast; ring, ofReal_re]
    positivity

/-- **The twin criterion without `hS` would decide the Siegel question.** If
`Q_χ(twin) ≥ 0 ⟹ GRH` held for some `GoodChar χ` without the real-zero hypothesis, then GRH for the
non-real zeros would already exclude every real zero off `½`. -/
theorem grh_of_twin_criterion (hG : GoodChar χ)
    (hcrit : (∀ l : ℝ, 0 ≤ l → 0 ≤ QC χ (l + 1) (twin (box 1) l)) → GRH χ) (h' : GRH' χ) :
    GRH χ := by
  refine hcrit fun l hl => ?_
  obtain ⟨K, hK⟩ := striptest_twin_box hl
  exact QC_nonneg_of_GRH' hG h' (twin_probe (box_probe 1) hl) (by linarith) hK

/-- The same for the criterion over every strip-test probe (`ProbeS`), not over every `Probe`. -/
theorem grh_of_probe_criterion (hG : GoodChar χ)
    (hcrit : (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → ProbeS a g → 0 ≤ QC χ a g) → GRH χ) (h' : GRH' χ) :
    GRH χ :=
  hcrit fun _ _ ha hg => QC_nonneg_of_GRH' hG h' hg.1 ha hg.2.choose_spec

end ChiHalf

/-! ## (C) the archimedean kernels -/

namespace ArchKerQuarter

open Pilot1ca

theorem kerK_eq_archKer (u : ℝ) : kerK u = archKer (1 / 4) u := by
  unfold kerK archKer
  rw [show (1 - 2 * (1 / 4 : ℝ)) * u = u / 2 by ring]

theorem archIntegrand_eq_Q (g : ℝ → ℝ) (u : ℝ) : archIntegrand g u = archIntegrandQ (1 / 4) g u := by
  unfold archIntegrand archIntegrandQ archKer
  rw [show (1 - 2 * (1 / 4 : ℝ)) * u = u / 2 by ring]

/-- **The `Γ_ℂ` kernel**: `K_{1/4}(u) + K_{3/4}(u) = 1/sinh(u/2)`. -/
theorem archKer_quarter_add {u : ℝ} (hu : 0 < u) :
    archKer (1 / 4) u + archKer (3 / 4) u = 1 / Real.sinh (u / 2) := by
  unfold archKer
  have hs : Real.sinh u = 2 * Real.sinh (u / 2) * Real.cosh (u / 2) := by
    have := Real.sinh_two_mul (u / 2)
    rwa [show 2 * (u / 2) = u by ring] at this
  have h2 : 0 < Real.sinh (u / 2) := Real.sinh_pos_iff.2 (by linarith)
  have hc : 0 < Real.cosh (u / 2) := Real.cosh_pos _
  rw [show (1 - 2 * (1 / 4 : ℝ)) * u = u / 2 by ring, show (1 - 2 * (3 / 4 : ℝ)) * u = -(u / 2) by ring,
    ← add_div]
  have hcosh : Real.exp (u / 2) + Real.exp (-(u / 2)) = 2 * Real.cosh (u / 2) := by
    rw [Real.cosh_eq]; ring
  rw [hcosh, hs, div_eq_div_iff (mul_pos (mul_pos two_pos h2) hc).ne' h2.ne']
  ring

end ArchKerQuarter

/-! ## (D) the local zero weight -/

namespace LocalSharp

open Pilot1ca Pilot1bt Kaiser ShortWeil

theorem Vz_ge_sharp {x : ℝ} {τ : ℂ} (hτ : |τ.im| < 1 / 2) (h : |(|τ.re| - x)| ≤ 1) :
    2 / (5 * π) ≤ Vz τ x := by
  obtain ⟨hs1, hs2⟩ := abs_lt.1 hτ
  have key : ∀ y z : ℝ, 1 / 2 ≤ y → y ≤ 3 / 2 → |z| ≤ 1 → 2 / (5 * π) ≤ pk y z := by
    intro y z hy1 hy2 hz
    unfold pk
    have hz2 : z ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg z]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 2 * (z ^ 2 + y ^ 2) ≤ 5 * y := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y - 1 / 2) (by linarith : (0 : ℝ) ≤ 2 - y)]
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

/-- The sharp constant is attained in the limit: at `y = ½`, `z = 1`, `pk y z = 2/(5π)`. -/
theorem pk_half_one : pk (1 / 2) 1 = 2 / (5 * π) := by
  unfold pk; rw [div_eq_div_iff (by positivity) (by positivity)]; ring

/-- **The local count with `5/2` in place of `13/2`.** -/
theorem card_local_le_sharp {x : ℝ} (hx : 0 ≤ x) (F : Finset (ZeroIdx (sqF Xi)))
    (hF : ∀ i ∈ F, |(|(tau i).re| - x)| ≤ 1) :
    (F.card : ℝ) ≤ 5 / 2 * (5 + kLam + Real.log (x + 2) / 2) := by
  have h1 : (F.card : ℝ) * (2 / (5 * π)) ≤ ∑ i ∈ F, Vz (tau i) x := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => Vz_ge_sharp (tau_im i) (hF i hi)
  have h2 : ∑ i ∈ F, Vz (tau i) x ≤ ∑' i, Vz (tau i) x :=
    (summable_Vz x).sum_le_tsum F fun i _ => Vz_nonneg (tau_im i) x
  have h3 := tsum_Vz_le x
  rw [abs_of_nonneg hx] at h3
  have : (F.card : ℝ) * (2 / (5 * π)) ≤ (5 + kLam + Real.log (x + 2) / 2) / π := by linarith
  rw [show (F.card : ℝ) * (2 / (5 * π)) = (F.card : ℝ) * 2 / 5 / π by ring,
    div_le_div_iff_of_pos_right pi_pos] at this
  linarith

end LocalSharp

/-! ## (E) `4π` -/

namespace PatE

open Pilot1ca

theorem fBalExp_two : fBalExp 2 = 4 * π := by unfold fBalExp; ring

/-- `lam_nine` with its double-exponential coefficient written as SixteenPi's maximal exponent. -/
theorem lam_nine_fBal :
    ∃ K, 0 ≤ K ∧ ∀ a, 4 ≤ a → lam a ≤ K * (a + 1) * Real.exp (9 * a - fBalExp 2 * Real.exp (2 * a)) := by
  rw [fBalExp_two]; exact Kaiser.lam_nine

/-- SixteenPi's time at the wall is `1/(4·fBalExp 2·e^{2a})`. -/
theorem tau_at_wall_fBal (a : ℝ) :
    tauWall (2 * π * Real.exp (2 * a)) 2 = 1 / (4 * fBalExp 2 * Real.exp (2 * a)) := by
  rw [tau_at_wall', fBalExp_two]; ring

end PatE

#print axioms ChiHalf.goodChar_of_hS
#print axioms ChiHalf.grh_iff_twins'
#print axioms ChiHalf.weil_criterion_chi'
#print axioms ChiHalf.grh_half_iff
#print axioms ChiHalf.ghatC_mul_I_im
#print axioms ChiHalf.QC_nonneg_of_GRH'
#print axioms ChiHalf.grh_of_twin_criterion
#print axioms ChiHalf.grh_of_probe_criterion
#print axioms ArchKerQuarter.kerK_eq_archKer
#print axioms ArchKerQuarter.archIntegrand_eq_Q
#print axioms ArchKerQuarter.archKer_quarter_add
#print axioms LocalSharp.Vz_ge_sharp
#print axioms LocalSharp.pk_half_one
#print axioms LocalSharp.card_local_le_sharp
#print axioms PatE.fBalExp_two
#print axioms PatE.lam_nine_fBal
#print axioms PatE.tau_at_wall_fBal
