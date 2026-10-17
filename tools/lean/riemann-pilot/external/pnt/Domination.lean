import WeilIndexInfinite
import WeilCount
import ParityGap
import StripConv
import PhiDExp
import KaiserNine
import Landau

/-! # Domination corollaries (round 249)

Rounds 230–231's negative-direction counts from round 232's; `ESupp → RSupp` so the `FourierInv` lemmas need only the weaker class; the λ₁ bounds of rounds 163, 164 and 234 (`lam_prefactor`, `lam_kaiser`, `lam_prefactor_KV`) as corollaries of round 220's `lam_nine`; `apply_localW` with the redundant hypotheses dropped.
-/

open Real Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace Domination

open Pilot1ca Pilot1bt PilotWeil

/-! ### S1. Rounds 230–231 are corollaries of round 232 (`negDirections_offline`). -/

/-- `negDirections_of_quadruples`, verbatim statement, from `negDirections_offline`. -/
theorem negDirections_of_quadruples' (R F : Finset (Σ w : NontrivialZero, Fin (zeroMult w)))
    (_hF : ∀ i, (zetaZeroFamily i).re ≠ 1 / 2 → i ∈ F)
    (hRoff : ∀ r ∈ R, (zetaZeroFamily r).re ≠ 1 / 2)
    (_hR : ∀ i, (zetaZeroFamily i).re ≠ 1 / 2 → ∃ r ∈ R, Orb (tz i) (tz r))
    (hdist : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ¬Orb (tz s) (tz r)) :
    ∃ a : ℝ, 0 < a ∧ ∃ V : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ V = R.card ∧
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a z ^ 2) K) ∧
      ∀ v ∈ V, v ≠ 0 → weilQ a v < 0 :=
  negDirections_offline R hRoff hdist

/-- `negDirections_above`, verbatim statement, from `negDirections_offline`. -/
theorem negDirections_above' (v₀ : ℝ) (hv₀ : 0 ≤ v₀)
    (R F : Finset (Σ w : NontrivialZero, Fin (zeroMult w)))
    (_hF : ∀ i, v₀ < |(zetaZeroFamily i).re - 1 / 2| → i ∈ F)
    (hRtop : ∀ r ∈ R, v₀ < |(zetaZeroFamily r).re - 1 / 2|)
    (_hR : ∀ i, v₀ < |(zetaZeroFamily i).re - 1 / 2| → ∃ r ∈ R, Orb (tz i) (tz r))
    (hdist : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ¬Orb (tz s) (tz r)) :
    ∃ a : ℝ, 0 < a ∧ ∃ V : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ V = R.card ∧
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a z ^ 2) K) ∧
      ∀ v ∈ V, v ≠ 0 → weilQ a v < 0 :=
  negDirections_offline R (fun r hr h => by
    have := hRtop r hr; rw [h, sub_self, abs_zero] at this; linarith) hdist

/-- `negIndex_eq_quadruples` without its finiteness hypothesis `hF` (strictly stronger). -/
theorem negIndex_eq_quadruples' (R : Finset (Σ w : NontrivialZero, Fin (zeroMult w)))
    (hRoff : ∀ r ∈ R, (zetaZeroFamily r).re ≠ 1 / 2)
    (hR : ∀ i, (zetaZeroFamily i).re ≠ 1 / 2 → ∃ r ∈ R, Orb (tz i) (tz r))
    (hdist : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ¬Orb (tz s) (tz r)) :
    (∀ (a : ℝ), 0 < a → ∀ (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V],
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a z ^ 2) K) →
      (∀ v ∈ V, v ≠ 0 → weilQ a v < 0) → Module.finrank ℝ V ≤ R.card) ∧
    ∃ a : ℝ, 0 < a ∧ ∃ V : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ V = R.card ∧
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a z ^ 2) K) ∧
      ∀ v ∈ V, v ≠ 0 → weilQ a v < 0 := by
  refine ⟨fun a ha V _ hV hneg => ?_, negDirections_offline R hRoff hdist⟩
  refine finrank_le_quadruples_zeta V ha (fun v hv => (hV v hv).1) (fun v hv => (hV v hv).2) hneg R
    fun i => ?_
  by_cases hi : (zetaZeroFamily i).re = 1 / 2
  · exact Or.inl hi
  · obtain ⟨r, hr, ho⟩ := hR i hi
    exact Or.inr ⟨r, hr, ho⟩

/-! ### S2. `Hadamard.summable_ord_div` is the `β = 1` case of `WeilCount.summable_ord_div_rpow`. -/

theorem summable_ord_div' {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) {C A α : ℝ}
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hgrowth : ∀ w, ‖F w‖ ≤ C * Real.exp (A * ‖w‖ ^ α)) :
    Summable (fun u : ℂ => (ordN F u : ℝ) / ‖u‖) := by
  simpa [Real.rpow_one] using summable_ord_div_rpow hF hF0 hC hA hα0 hα1 hgrowth

/-! ### S3. FourierInv A1–A4 (even `ESupp`) from ParityGap G1 (any parity, `RSupp`). -/

variable {a : ℝ} {g : ℝ → ℝ}

theorem _root_.Pilot1ca.ESupp.toR (hp : ESupp a g) : RSupp a g := ⟨hp.supp, hp.memL2⟩

theorem fourier_autocorr' (hp : ESupp a g) (ha : 0 < a) (r : ℝ) :
    ∫ x, (autocorr g x : ℂ) * Complex.exp (Complex.I * r * x) = ghatC g a r ^ 2 := by
  rw [fourier_autocorr_gen hp.toR ha r, ghatC_even hp.even, sq]

theorem PhiH_eq_PhiG (hp : ESupp a g) (ha : 0 ≤ a) : PhiH g a = PhiG g a := by
  funext ξ
  simp only [PhiH, PhiG, gN]
  rw [ghatC_real hp ha, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem fourier_autocorr_eq' (hp : ESupp a g) (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (autocorr g x : ℂ)) ξ = (PhiH g a ξ : ℂ) := by
  rw [PhiH_eq_PhiG hp ha.le]; exact fourier_autocorr_eq_gen hp.toR ha ξ

theorem tendsto_gauss_PhiH' (hp : ESupp a g) (ha : 0 < a) :
    Tendsto (fun c : ℝ => ∫ x, Real.exp (-c⁻¹ * x ^ 2) * PhiH g a x) atTop (𝓝 (autocorr g 0)) := by
  rw [PhiH_eq_PhiG hp ha.le]; exact tendsto_gauss_PhiG hp.toR ha

theorem integrable_PhiH' (hp : ESupp a g) (ha : 0 < a) : Integrable (PhiH g a) := by
  rw [PhiH_eq_PhiG hp ha.le]; exact integrable_PhiG hp.toR ha

theorem autocorr_eq_inv' (hp : ESupp a g) (ha : 0 < a) (u : ℝ) :
    autocorr g u = ∫ v, PhiH g a v * Real.cos (2 * π * v * u) := by
  rw [PhiH_eq_PhiG hp ha.le]; exact autocorr_eq_inv_gen hp.toR ha u

/-! ### S4. `StripConv.tendstoLocallyUniformlyOn_ratio` (49-line ε–η proof) from Mathlib. -/

theorem tendstoLocallyUniformlyOn_ratio' {G : ℕ → ℂ → ℂ} {F : ℂ → ℂ} (hF : Continuous F)
    (hF0 : F 0 ≠ 0) (hconv : TendstoLocallyUniformlyOn G F atTop stripSet) :
    TendstoLocallyUniformlyOn (fun n z => G n z / G n 0) (fun z => F z / F 0) atTop stripSet := by
  have h0 : Tendsto (fun n => G n 0) atTop (𝓝 (F 0)) := hconv.tendsto_at zero_mem_stripSet
  have hinv : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => (G n 0)⁻¹) (fun _ => (F 0)⁻¹) atTop stripSet :=
    ((h0.inv₀ hF0).tendstoUniformlyOn_const stripSet).tendstoLocallyUniformlyOn
  have := hconv.mul₀ hinv hF.continuousOn continuousOn_const
  have e1 : (fun n z => G n z / G n 0) = G * fun n (_ : ℂ) => (G n 0)⁻¹ := by
    funext n z; simp [div_eq_mul_inv]
  have e2 : (fun z => F z / F 0) = F * fun _ : ℂ => (F 0)⁻¹ := by
    funext z; simp [div_eq_mul_inv]
  rw [e1, e2]; exact this

/-! ### S5. `WeilDischarge.weilExplicit_combo` is `PhiDExp.weilExplicit_combo_gen` at `b = a/8`. -/

theorem weilExplicit_combo' {a : ℝ} (ha : 1 ≤ a) (p q : ℝ) :
    WeilExplicit rhoXi
      (fun z => ghatC (fun t => p * twin (PhiA (a / 8)) (a / 4) t
        + q * twin (PhiA (a / 8)) (3 * a / 4) t) a z ^ 2)
      (hsq (fun t => p * twin (PhiA (a / 8)) (a / 4) t + q * twin (PhiA (a / 8)) (3 * a / 4) t) a) :=
  weilExplicit_combo_gen (by positivity) (by positivity) (by linarith) (by linarith) p q

/-! ### S6. As Lean statements, the Kaiser `λ₁` bounds of rounds 16x, 164 and 234 follow from `lam_nine`. -/

/-- The statement of `KaiserKV.lam_prefactor_KV` (round 234), from round 220's `lam_nine` (`c = 1`). -/
theorem lam_prefactor_KV' : ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ a : ℝ, 4 ≤ a →
    lam a ≤ K * (a + 1) *
      Real.exp (10 * a - c * a ^ ((1 : ℝ) / 3) / Real.log a ^ ((1 : ℝ) / 3) - 4 * π * Real.exp (2 * a)) := by
  obtain ⟨K, hK, h⟩ := Kaiser.lam_nine
  refine ⟨K, 1, hK, one_pos, fun a ha => (h a ha).trans ?_⟩
  have ha0 : 0 < a := by linarith
  have hlog : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le ha0]; linarith [Real.exp_one_lt_d9]
  have h1 : 1 ≤ Real.log a ^ ((1 : ℝ) / 3) := Real.one_le_rpow hlog (by norm_num)
  have h2 : a ^ ((1 : ℝ) / 3) ≤ a := by
    calc a ^ ((1 : ℝ) / 3) ≤ a ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = a := Real.rpow_one a
  have h3 : 1 * a ^ ((1 : ℝ) / 3) / Real.log a ^ ((1 : ℝ) / 3) ≤ a := by
    rw [one_mul, div_le_iff₀ (by linarith)]
    nlinarith [Real.rpow_nonneg ha0.le ((1 : ℝ) / 3)]
  have hK1 : 0 ≤ K * (a + 1) := by positivity
  gcongr
  linarith

/-- The statement of `KaiserPrefactor.lam_prefactor` (round 164), from `lam_nine`. -/
theorem lam_prefactor' :
    ∃ K, 0 ≤ K ∧ ∀ a, 4 ≤ a → lam a ≤ K * (a + 1) * Real.exp (10 * a - 4 * π * Real.exp (2 * a)) := by
  obtain ⟨K, hK, h⟩ := Kaiser.lam_nine
  refine ⟨K, hK, fun a ha => (h a ha).trans ?_⟩
  have ha1 : 0 ≤ a + 1 := by linarith
  have : 0 ≤ K * (a + 1) := mul_nonneg hK ha1
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) this

/-- The statement of `KaiserBulk.lam_kaiser`, from `lam_nine`. -/
theorem lam_kaiser' :
    ∃ K, 0 ≤ K ∧ ∀ a, 4 ≤ a → lam a ≤ K * Real.exp (20 * a - 4 * π * Real.exp (2 * a)) := by
  obtain ⟨K, hK, h⟩ := Kaiser.lam_nine
  refine ⟨K, hK, fun a ha => (h a ha).trans ?_⟩
  have ha1 : a + 1 ≤ Real.exp (11 * a) := by
    have := Real.add_one_le_exp (11 * a); linarith
  calc K * (a + 1) * Real.exp (9 * a - 4 * π * Real.exp (2 * a))
      ≤ K * Real.exp (11 * a) * Real.exp (9 * a - 4 * π * Real.exp (2 * a)) := by gcongr
    _ = K * Real.exp (20 * a - 4 * π * Real.exp (2 * a)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

end Domination

/-! ### S7. `Landau.apply_localW` from `Landau.disc_factsW` (the disc facts are proved twice). -/

namespace Landau
open Complex Real

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ

theorem apply_localW' {w : ℝ → ℝ} {Cw K : ℝ} (hw : WidthOK w Cw) (hK : 0 < K) (hG : GrowthW w K) {T δ : ℝ}
    (hT : 4 ≤ |T|) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    radW w T * -(ζ' ((1 + δ : ℝ) + T * I) / ζ ((1 + δ : ℝ) + T * I)).re ≤
        Kc * Real.log (Bnd K δ T) ∧
    ∀ β : ℝ, ζ (β + T * I) = 0 → 1 + δ - β ≤ radW w T / 2 →
      radW w T * -(ζ' ((1 + δ : ℝ) + T * I) / ζ ((1 + δ : ℝ) + T * I)).re ≤
        Kc * Real.log (Bnd K δ T) - radW w T / (1 + δ - β) := by
  obtain ⟨hpole, hbound, hB⟩ := disc_factsW hw hK hG hT hδ hδ2
  have hre : (((1 + δ : ℝ) : ℂ) + T * I).re = 1 + δ := by simp
  have him : (((1 + δ : ℝ) : ℂ) + T * I).im = T := by simp
  have hloc := local_bound (by rw [hre]; linarith) (radW_pos hw T hT) hB hpole hbound
  refine ⟨hloc.1, fun β hβ hd => ?_⟩
  have := hloc.2 β (by rw [him]; exact hβ) (by rw [hre]; exact hd)
  rwa [hre] at this

end Landau

#print axioms Domination.negDirections_of_quadruples'
#print axioms Domination.negDirections_above'
#print axioms Domination.negIndex_eq_quadruples'
#print axioms Domination.summable_ord_div'
#print axioms Domination.fourier_autocorr'
#print axioms Domination.fourier_autocorr_eq'
#print axioms Domination.tendsto_gauss_PhiH'
#print axioms Domination.integrable_PhiH'
#print axioms Domination.autocorr_eq_inv'
#print axioms Domination.tendstoLocallyUniformlyOn_ratio'
#print axioms Domination.weilExplicit_combo'
#print axioms Domination.lam_prefactor_KV'
#print axioms Domination.lam_prefactor'
#print axioms Domination.lam_kaiser'
#print axioms Landau.apply_localW'
