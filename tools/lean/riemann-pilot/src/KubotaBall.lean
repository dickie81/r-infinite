import KubotaUnfold
import Roadmap

/-! # Hyperbolic balls and their averages (round 418)

S5f-10 of round 360's plan, part 1 (S5f-10a). Round 360 planned Lax–Milgram for the energy form, to bound the
resolvent by `|Im λ|⁻¹` off the real axis. This round prepares a different operator: the average over a
hyperbolic ball of fixed radius. Ball averages commute with the action, the powers `v^s` are eigenfunctions
with an explicit eigenvalue `ĥ(s)`, `ĥ` is entire, and `Im ĥ(s) > 0` just above the real axis.

* **The point-pair invariant** (`ppi` and `PInv`, definitions; **`pinv_actP`**, with `PInv.comp`,
  `PInv.congr`, `pinv_transl`, `pinv_diag`, `inv_identity` and `pinv_E`):
  `(|z − z'|² + (v − v')²)/(vv')` is invariant under every `g` of determinant `1`, through round 383's
  decomposition of `g` into translations, `(a, 0; 0, a⁻¹)` and `E = (0, −1; 1, 0)`.
* **Balls and averages** (`hball` and `bavg`, definitions; **`bavg_comp_actP`**, with `measurable_ppi`,
  `measurableSet_hball` and `mem_hball_actP`): `g` maps balls to balls, and
  `∫_{B_R(p)} f∘g dμ = ∫_{B_R(gp)} f dμ` (round 383's `integral_actP`).
* **The eigenvalue** (`hhat`, a definition; **`bavg_cpow`**, with `measurable_cpow_snd`):
  `∫_{B_R(z, v)} v'^s dμ = ĥ_R(s)·v^s` for `v > 0`, with `ĥ_R(s) = ∫_{B_R(0, 1)} v^s dμ`.
* **As a one-variable integral** (**`hhat_eq_integral`**, with `mem_hball_one`, `hball_one_subset`,
  `volume_hball_one_lt_top` and `rpow_le_of_mem_Icc`): `ĥ_R(s) = ∫_0^∞ π·max(Rv − (v − 1)², 0)·v^{s−3} dv`
  for `R ≥ 0`, by Fubini with the area of a disc (Mathlib's `Complex.volume_closedBall`).
* **The radius `r`** (**`hhat_eq_interval`**, with `ballQ_exp`, `cpow_ofReal_exp` and `hhat_eq_line`):
  for `R = 2cosh r − 2` and `r ≥ 0`, `ĥ(s) = ∫_{−r}^{r} 2π(cosh r − cosh u)·e^{(s−1)u} du`
  (the substitution `v = e^u`, Mathlib's `integral_comp_exp`).
* **Holomorphy** (**`differentiable_hhat`**, with `hhat_eq_ghatC`): `ĥ` is entire, being round 4's
  `ghatC` at `−i(s − 1)` (round 6's `ghatC_differentiable`).
* **Positivity** (`imK`, a definition; **`im_hhat_pos`**, **`im_hhat_ge`** and **`hhat_real_pos`**, with
  `im_hhat_eq` and `imK_pos`): `Im ĥ(σ + it) = ∫_0^r 4π(cosh r − cosh u)·sinh((σ − 1)u)·sin(tu) du`. It is
  positive for `σ > 1` and `0 < t < π/r`, and at least `t·K(r, σ)` with `K(r, σ) > 0` for `σ > 1` and
  `0 ≤ t ≤ π/(2r)` (Jordan's inequality, Mathlib's `Real.mul_le_sin`). On the real axis `ĥ(σ)` is real and
  positive.
-/

open MeasureTheory Set
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Eis

/-! ### The point-pair invariant -/

/-- The point-pair invariant `(|z − z'|² + (v − v')²)/(vv')`, which is `2cosh d − 2` for the hyperbolic
distance `d`. -/
def ppi (p q : ℂ × ℝ) : ℝ := (Complex.normSq (p.1 - q.1) + (p.2 - q.2) ^ 2) / (p.2 * q.2)

/-- `f` preserves the point-pair invariant on upper half-space. -/
def PInv (f : ℂ × ℝ → ℂ × ℝ) : Prop := ∀ p ∈ UHS, ∀ q ∈ UHS, ppi (f p) (f q) = ppi p q

theorem PInv.comp {f g : ℂ × ℝ → ℂ × ℝ} (hf : PInv f) (hg : PInv g) (hgU : ∀ p ∈ UHS, g p ∈ UHS) :
    PInv (f ∘ g) := fun p hp q hq => by
  simp only [Function.comp]
  rw [hf _ (hgU p hp) _ (hgU q hq), hg p hp q hq]

theorem PInv.congr {f g : ℂ × ℝ → ℂ × ℝ} (hf : PInv f) (h : ∀ p ∈ UHS, f p = g p) : PInv g :=
  fun p hp q hq => by rw [← h p hp, ← h q hq]; exact hf p hp q hq

theorem pinv_transl (x : ℂ) : PInv (actP !![1, x; 0, 1]) := fun p _ q _ => by
  simp only [actP, uhsAct_transl, ppi]
  ring_nf

theorem pinv_diag {a : ℂ} (ha : a ≠ 0) : PInv (actP !![a, 0; 0, a⁻¹]) := fun p _ q _ => by
  simp only [actP, uhsAct_diag ha, ppi]
  have hn : 0 < Complex.normSq a := Complex.normSq_pos.2 ha
  rw [← mul_sub, Complex.normSq_mul, map_pow, ← mul_sub,
    show Complex.normSq a ^ 2 * Complex.normSq (p.1 - q.1) + (Complex.normSq a * (p.2 - q.2)) ^ 2 =
      Complex.normSq a ^ 2 * (Complex.normSq (p.1 - q.1) + (p.2 - q.2) ^ 2) by ring,
    show Complex.normSq a * p.2 * (Complex.normSq a * q.2) = Complex.normSq a ^ 2 * (p.2 * q.2) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hn.ne')]

/-- The identity behind the inversion: with `N = n + v²`, `M = m + u²` and `r = Re(z·conj w)`,
`(n/N² + m/M² − 2r/(NM)) + (v/N − u/M)² = (n + m − 2r + (v − u)²)/(NM)`. -/
theorem inv_identity {n m r v u : ℝ} (hN : 0 < n + v ^ 2) (hM : 0 < m + u ^ 2) :
    n / (n + v ^ 2) ^ 2 + m / (m + u ^ 2) ^ 2 - 2 * (r / ((n + v ^ 2) * (m + u ^ 2))) +
        (v / (n + v ^ 2) - u / (m + u ^ 2)) ^ 2 =
      (n + m - 2 * r + (v - u) ^ 2) / ((n + v ^ 2) * (m + u ^ 2)) := by
  field_simp
  ring

theorem pinv_E : PInv (actP !![0, -1; 1, 0]) := fun p hp q hq => by
  have hv : (0 : ℝ) < p.2 := hp
  have hw : (0 : ℝ) < q.2 := hq
  have hN : 0 < Complex.normSq p.1 + p.2 ^ 2 := by have := Complex.normSq_nonneg p.1; positivity
  have hM : 0 < Complex.normSq q.1 + q.2 ^ 2 := by have := Complex.normSq_nonneg q.1; positivity
  simp only [actP, uhsAct_inv, ppi]
  have e1 : -conj p.1 / ((Complex.normSq p.1 + p.2 ^ 2 : ℝ) : ℂ) -
      -conj q.1 / ((Complex.normSq q.1 + q.2 ^ 2 : ℝ) : ℂ) =
      -conj (p.1 / ((Complex.normSq p.1 + p.2 ^ 2 : ℝ) : ℂ) -
        q.1 / ((Complex.normSq q.1 + q.2 ^ 2 : ℝ) : ℂ)) := by
    rw [map_sub, map_div₀, map_div₀, Complex.conj_ofReal, Complex.conj_ofReal]; ring
  have e2 : (p.1 / ((Complex.normSq p.1 + p.2 ^ 2 : ℝ) : ℂ) *
      conj (q.1 / ((Complex.normSq q.1 + q.2 ^ 2 : ℝ) : ℂ))).re =
      (p.1 * conj q.1).re / ((Complex.normSq p.1 + p.2 ^ 2) * (Complex.normSq q.1 + q.2 ^ 2)) := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, ← Complex.ofReal_mul, Complex.div_ofReal_re]
  rw [e1, Complex.normSq_neg, Complex.normSq_conj, Complex.normSq_sub, Complex.normSq_div,
    Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_ofReal, e2, Complex.normSq_sub,
    ← sq, ← sq, inv_identity hN hM, div_mul_div_comm, div_div_div_cancel_right₀ (by positivity)]

/-- **The point-pair invariant is invariant under `SL_2(ℂ)`**, through the decomposition of round
383's `uinv_actP`. -/
theorem pinv_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) : PInv (actP g) := by
  have hdet := det_two_eq_one g hg
  have hmul : ∀ {g h : Matrix (Fin 2) (Fin 2) ℂ}, g.det = 1 → h.det = 1 → PInv (actP g) →
      PInv (actP h) → PInv (actP (g * h)) := fun hg hh hug huh =>
    (hug.comp huh fun p hp => actP_mem hh hp).congr fun _ hp => (actP_mul hg hh hp).symm
  by_cases hc : g 1 0 = 0
  · have ha : g 0 0 ≠ 0 := fun h => by rw [h, hc] at hdet; simp at hdet
    have e : g = !![g 0 0, 0; 0, (g 0 0)⁻¹] * !![1, g 0 1 / g 0 0; 0, 1] := by
      have hd : g 1 1 = (g 0 0)⁻¹ := by
        rw [hc, mul_zero, sub_zero] at hdet; exact eq_inv_of_mul_eq_one_right hdet
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, hc, hd]
      field_simp
    rw [e]
    exact hmul (det_diag ha) (det_transl _) (pinv_diag ha) (pinv_transl _)
  · have e : g = !![1, g 0 0 / g 1 0; 0, 1] * !![0, -1; 1, 0] * !![g 1 0, 0; 0, (g 1 0)⁻¹] *
        !![1, g 1 1 / g 1 0; 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> field_simp
      linear_combination -hdet
    rw [e]
    have h1 : (!![1, g 0 0 / g 1 0; 0, 1] * !![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
      rw [Matrix.det_mul, det_transl, det_E, one_mul]
    have h2 : (!![1, g 0 0 / g 1 0; 0, 1] * !![0, -1; 1, 0] * !![g 1 0, 0; 0, (g 1 0)⁻¹] :
        Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
      rw [Matrix.det_mul, h1, det_diag hc, one_mul]
    exact hmul h2 (det_transl _)
      (hmul h1 (det_diag hc) (hmul (det_transl _) det_E (pinv_transl _) pinv_E) (pinv_diag hc))
      (pinv_transl _)

/-! ### Balls and ball averages -/

/-- The ball `{q : (|z − z'|² + (v − v')²)/(vv') ≤ R}` about `p` in upper half-space. -/
def hball (R : ℝ) (p : ℂ × ℝ) : Set (ℂ × ℝ) := {q | q ∈ UHS ∧ ppi p q ≤ R}

theorem measurable_ppi (p : ℂ × ℝ) : Measurable (ppi p) := by
  unfold ppi; fun_prop

theorem measurableSet_hball (R : ℝ) (p : ℂ × ℝ) : MeasurableSet (hball R p) :=
  measurableSet_UHS.inter (measurableSet_le (measurable_ppi p) measurable_const)

/-- `g` maps balls to balls. -/
theorem mem_hball_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {R : ℝ} {p q : ℂ × ℝ}
    (hp : p ∈ UHS) (hq : q ∈ UHS) : actP g q ∈ hball R (actP g p) ↔ q ∈ hball R p := by
  simp only [hball, mem_ofPred_eq, pinv_actP hg p hp q hq, actP_mem hg hq, hq, true_and]

/-- The average over the ball: `∫_{B_R(p)} f dμ`. -/
def bavg (R : ℝ) (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ := ∫ q in hball R p, f q ∂uhsMeasure

/-- **Ball averages commute with the action**: `∫_{B_R(p)} f ∘ g = ∫_{B_R(gp)} f` for `g` of determinant
`1` (round 383's `integral_actP`). -/
theorem bavg_comp_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {R : ℝ} {f : ℂ × ℝ → ℂ}
    (hf : Measurable f) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    bavg R (fun q => f (actP g q)) p = bavg R f (actP g p) := by
  unfold bavg
  rw [← integral_indicator (measurableSet_hball R p), ← integral_indicator (measurableSet_hball R _)]
  have hF : AEStronglyMeasurable ((hball R (actP g p)).indicator f) uhsMeasure :=
    (hf.indicator (measurableSet_hball R _)).aestronglyMeasurable
  rw [← integral_actP hg hF]
  refine integral_congr_ae ?_
  filter_upwards [ae_UHS] with q hq
  by_cases hb : q ∈ hball R p
  · rw [indicator_of_mem hb, indicator_of_mem ((mem_hball_actP hg hp hq).2 hb)]
  · rw [indicator_of_notMem hb, indicator_of_notMem fun h => hb ((mem_hball_actP hg hp hq).1 h)]

/-- The ball transform `ĥ_R(s) = ∫_{B_R(0, 1)} v^s dμ`. -/
def hhat (R : ℝ) (s : ℂ) : ℂ := bavg R (fun q => ((q.2 : ℝ) : ℂ) ^ s) (0, 1)

theorem measurable_cpow_snd (s : ℂ) : Measurable fun q : ℂ × ℝ => ((q.2 : ℝ) : ℂ) ^ s := by
  fun_prop

/-- **Powers are eigenfunctions**: `∫_{B_R(z, v)} v'^s dμ = ĥ_R(s)·v^s`. -/
theorem bavg_cpow (R : ℝ) (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    bavg R (fun q => ((q.2 : ℝ) : ℂ) ^ s) p = hhat R s * ((p.2 : ℝ) : ℂ) ^ s := by
  have hv : (0 : ℝ) < p.2 := hp
  set a : ℂ := ((Real.sqrt p.2 : ℝ) : ℂ) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact_mod_cast (Real.sqrt_pos.2 hv).ne'
  have hna : Complex.normSq a = p.2 := by
    rw [ha, Complex.normSq_ofReal, Real.mul_self_sqrt hv.le]
  set g : Matrix (Fin 2) (Fin 2) ℂ := !![1, p.1; 0, 1] * !![a, 0; 0, a⁻¹] with hgdef
  have hg : g.det = 1 := by rw [hgdef, Matrix.det_mul, det_transl, det_diag ha0, one_mul]
  have h01 : ((0 : ℂ), (1 : ℝ)) ∈ UHS := (zero_lt_one : (0 : ℝ) < 1)
  have hgp : actP g (0, 1) = p := by
    rw [hgdef, actP_mul (det_transl _) (det_diag ha0) h01]
    simp only [actP, uhsAct_diag ha0, uhsAct_transl, mul_zero, zero_add, hna, mul_one]
  have hcomp : ∀ q ∈ UHS, ((actP g q).2 : ℂ) ^ s = ((p.2 : ℝ) : ℂ) ^ s * ((q.2 : ℝ) : ℂ) ^ s := by
    intro q hq
    have hq' : (0 : ℝ) < q.2 := hq
    rw [hgdef, actP_mul (det_transl _) (det_diag ha0) hq]
    simp only [actP, uhsAct_diag ha0, uhsAct_transl, hna]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hv.le hq'.le]
  rw [← hgp, ← bavg_comp_actP hg (measurable_cpow_snd s) h01, hgp, hhat, bavg, bavg,
    ← integral_mul_const]
  refine setIntegral_congr_fun (measurableSet_hball R _) fun q hq => ?_
  rw [hcomp q hq.1, mul_comm]

/-! ### The ball about `(0, 1)` -/

theorem mem_hball_one {R : ℝ} {z : ℂ} {v : ℝ} :
    (z, v) ∈ hball R (0, 1) ↔ 0 < v ∧ Complex.normSq z ≤ R * v - (v - 1) ^ 2 := by
  simp only [hball, mem_ofPred_eq, UHS, ppi, zero_sub, Complex.normSq_neg, one_mul]
  constructor
  · rintro ⟨hv, h⟩
    refine ⟨hv, ?_⟩
    rw [div_le_iff₀ hv] at h
    nlinarith
  · rintro ⟨hv, h⟩
    refine ⟨hv, ?_⟩
    rw [div_le_iff₀ hv]
    nlinarith

/-- The ball about `(0, 1)` lies in `|z| ≤ R + 2`, `1/(R + 2) ≤ v ≤ R + 2`. -/
theorem hball_one_subset {R : ℝ} (hR : 0 ≤ R) :
    hball R (0, 1) ⊆ Metric.closedBall (0 : ℂ) (R + 2) ×ˢ Icc (1 / (R + 2)) (R + 2) := by
  rintro ⟨z, v⟩ h
  obtain ⟨hv, hz⟩ := mem_hball_one.1 h
  have hn := Complex.normSq_nonneg z
  have hvR : v ≤ R + 2 := by nlinarith
  have hv1 : 1 ≤ (R + 2) * v := by nlinarith
  refine ⟨?_, ?_, hvR⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖z‖ ^ 2 ≤ (R + 2) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).1 h1
  · rw [div_le_iff₀ (by linarith)]; linarith

theorem volume_hball_one_lt_top {R : ℝ} (hR : 0 ≤ R) : volume (hball R (0, 1)) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (hball_one_subset hR)) ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top (measure_closedBall_lt_top) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

/-- `v^x ≤ (R + 2)^{|x|}` on `1/(R + 2) ≤ v ≤ R + 2`. -/
theorem rpow_le_of_mem_Icc {R v x : ℝ} (hR : 0 ≤ R) (hv : v ∈ Icc (1 / (R + 2)) (R + 2)) :
    v ^ x ≤ (R + 2) ^ |x| := by
  have hR2 : 0 < R + 2 := by linarith
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv.1
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact Real.rpow_le_rpow hv0.le hv.2 hx
  · rw [abs_of_neg hx]
    have h1 : v ^ x = (1 / v) ^ (-x) := by
      rw [Real.div_rpow zero_le_one hv0.le, Real.one_rpow, Real.rpow_neg hv0.le, one_div, inv_inv]
    rw [h1]
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    rw [div_le_iff₀ hv0]
    have := hv.1
    rw [div_le_iff₀ hR2] at this
    linarith

/-- **The ball transform as a one-variable integral**: for `R ≥ 0`,
`ĥ_R(s) = ∫_{v>0} π·max(Rv − (v − 1)², 0)·v^{−3}·v^s dv`, by Fubini with the area `πρ` of the disc
`|z|² ≤ ρ`. -/
theorem hhat_eq_integral {R : ℝ} (hR : 0 ≤ R) (s : ℂ) :
    hhat R s = ∫ v in Ioi (0 : ℝ),
      ((Real.pi * max (R * v - (v - 1) ^ 2) 0 * v ^ (-3 : ℤ) : ℝ) : ℂ) * ((v : ℝ) : ℂ) ^ s := by
  set G : ℂ × ℝ → ℂ := fun q => ((q.2 ^ (-3 : ℤ) : ℝ) : ℂ) * ((q.2 : ℝ) : ℂ) ^ s with hG
  have hGm : Measurable G := by rw [hG]; fun_prop
  -- step 1: to Lebesgue measure on `ℂ × ℝ`
  have h1 : hhat R s = ∫ q, (hball R (0, 1)).indicator G q := by
    rw [hhat, bavg, ← integral_indicator (measurableSet_hball R _), uhsMeasure,
      integral_withDensity_eq_integral_toReal_smul measurable_uhsW
        (Filter.Eventually.of_forall fun q => ENNReal.ofReal_lt_top),
      ← integral_indicator measurableSet_UHS]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    by_cases hq : q ∈ hball R (0, 1)
    · have hq' : q ∈ UHS := hq.1
      have hv : (0 : ℝ) < q.2 := hq'
      rw [indicator_of_mem hq', indicator_of_mem hq, indicator_of_mem hq, uhsW,
        ENNReal.toReal_ofReal (by positivity), hG, Complex.real_smul]
    · rw [indicator_of_notMem hq]
      by_cases hq' : q ∈ UHS
      · rw [indicator_of_mem hq', indicator_of_notMem hq, smul_zero]
      · rw [indicator_of_notMem hq']
  -- step 2: integrability
  have hint : Integrable ((hball R (0, 1)).indicator G) (volume : Measure (ℂ × ℝ)) := by
    rw [integrable_indicator_iff (measurableSet_hball R _)]
    refine Measure.integrableOn_of_bounded (M := (R + 2) ^ |s.re - 3|) (volume_hball_one_lt_top hR).ne
      hGm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' (measurableSet_hball R _)]
    refine Filter.Eventually.of_forall fun q hq => ?_
    have hv : (0 : ℝ) < q.2 := hq.1
    have hIcc := (Set.mem_prod.1 (hball_one_subset hR hq)).2
    rw [hG, norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hv,
      Real.norm_eq_abs, abs_of_pos (by positivity), ← Real.rpow_intCast,
      ← Real.rpow_add hv]
    calc q.2 ^ ((((-3 : ℤ) : ℝ)) + s.re) = q.2 ^ (s.re - 3) := by push_cast; ring_nf
      _ ≤ (R + 2) ^ |s.re - 3| := rpow_le_of_mem_Icc hR hIcc
  -- step 3: Fubini, integrating `z` first
  rw [h1, Measure.volume_eq_prod, integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact hint),
    ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  beta_reduce
  by_cases hv : 0 < v
  · rw [indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv)]
    have hslice : (fun z : ℂ => (hball R (0, 1)).indicator G (z, v)) =
        {z : ℂ | Complex.normSq z ≤ R * v - (v - 1) ^ 2}.indicator
          (fun _ => ((v ^ (-3 : ℤ) : ℝ) : ℂ) * ((v : ℝ) : ℂ) ^ s) := by
      funext z
      by_cases hz : Complex.normSq z ≤ R * v - (v - 1) ^ 2
      · rw [indicator_of_mem (mem_hball_one.2 ⟨hv, hz⟩), indicator_of_mem (show z ∈ _ from hz)]
      · rw [indicator_of_notMem (fun h => hz (mem_hball_one.1 h).2),
          indicator_of_notMem (show z ∉ _ from hz)]
    have hmeas : MeasurableSet {z : ℂ | Complex.normSq z ≤ R * v - (v - 1) ^ 2} :=
      measurableSet_le (by fun_prop) measurable_const
    have hvol : volume.real {z : ℂ | Complex.normSq z ≤ R * v - (v - 1) ^ 2} =
        Real.pi * max (R * v - (v - 1) ^ 2) 0 := by
      rw [measureReal_def]
      set ρ := R * v - (v - 1) ^ 2
      rcases le_or_gt 0 ρ with hρ | hρ
      · have hset : {z : ℂ | Complex.normSq z ≤ ρ} = Metric.closedBall 0 (Real.sqrt ρ) := by
          ext z
          rw [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, Complex.normSq_eq_norm_sq,
            Real.le_sqrt (norm_nonneg _) hρ]
        rw [hset, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt hρ, max_eq_left hρ]
        simp [mul_comm]
      · have hset : {z : ℂ | Complex.normSq z ≤ ρ} = ∅ := by
          ext z
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
          exact lt_of_lt_of_le hρ (Complex.normSq_nonneg z)
        rw [hset, measure_empty, ENNReal.toReal_zero, max_eq_right hρ.le, mul_zero]
    rw [hslice, integral_indicator_const _ hmeas, hvol, Complex.real_smul]
    push_cast
    ring
  · rw [indicator_of_notMem (show v ∉ Ioi (0 : ℝ) from hv)]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun z => ?_)
    show (hball R (0, 1)).indicator G (z, v) = 0
    rw [indicator_of_notMem fun h => hv (mem_hball_one.1 h).1]

/-! ### The ball of radius `r`: `R = 2cosh r − 2` -/

/-- `(2cosh r − 2)e^u − (e^u − 1)² = 2e^u(cosh r − cosh u)`. -/
theorem ballQ_exp (r u : ℝ) :
    (2 * Real.cosh r - 2) * Real.exp u - (Real.exp u - 1) ^ 2 =
      2 * Real.exp u * (Real.cosh r - Real.cosh u) := by
  have h : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [Real.cosh_eq u]
  linear_combination h

theorem cpow_ofReal_exp (u : ℝ) (s : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ s = Complex.exp (u * s) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]

/-- **The ball transform on the line**: substituting `v = e^u`,
`ĥ(s) = ∫_ℝ 2π·max(cosh r − cosh u, 0)·e^{(s − 1)u} du` for `R = 2cosh r − 2`. -/
theorem hhat_eq_line (r : ℝ) (s : ℂ) :
    hhat (2 * Real.cosh r - 2) s = ∫ u : ℝ,
      ((2 * Real.pi * max (Real.cosh r - Real.cosh u) 0 : ℝ) : ℂ) * Complex.exp ((s - 1) * u) := by
  have hR : 0 ≤ 2 * Real.cosh r - 2 := by linarith [Real.one_le_cosh r]
  rw [hhat_eq_integral hR, ← integral_comp_exp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  beta_reduce
  have hmax : max (2 * Real.exp u * (Real.cosh r - Real.cosh u)) 0 =
      2 * Real.exp u * max (Real.cosh r - Real.cosh u) 0 := by
    rw [mul_max_of_nonneg _ _ (by positivity), mul_zero]
  have e : Complex.exp u * Complex.exp u * Complex.exp (-3 * u) * Complex.exp (u * s) =
      Complex.exp ((s - 1) * u) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [ballQ_exp, hmax, cpow_ofReal_exp, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_zpow,
    Complex.ofReal_exp, ← Complex.exp_int_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * ((max (Real.cosh r - Real.cosh u) 0 : ℝ) : ℂ)) * e

/-- **The ball transform on `[−r, r]`**: `ĥ(s) = ∫_{−r}^{r} 2π(cosh r − cosh u)e^{(s − 1)u} du`. -/
theorem hhat_eq_interval {r : ℝ} (hr : 0 ≤ r) (s : ℂ) :
    hhat (2 * Real.cosh r - 2) s = ∫ u in (-r)..r,
      ((2 * Real.pi * (Real.cosh r - Real.cosh u) : ℝ) : ℂ) * Complex.exp ((s - 1) * u) := by
  rw [hhat_eq_line, intervalIntegral.integral_of_le (by linarith),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (-r) r)]
  · refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have hc : Real.cosh u ≤ Real.cosh r := by
      rw [Real.cosh_le_cosh, abs_of_nonneg hr]
      exact abs_le.2 ⟨by linarith [hu.1], hu.2⟩
    rw [max_eq_left (by linarith)]
  · intro u hu
    have hc : Real.cosh r ≤ Real.cosh u := by
      rw [Real.cosh_le_cosh, abs_of_nonneg hr]
      rcases le_or_gt u (-r) with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have : r < u := by
          by_contra h'
          exact hu ⟨h, not_lt.1 h'⟩
        rw [abs_of_pos (by linarith)]; exact this.le
    rw [max_eq_right (by linarith), mul_zero, Complex.ofReal_zero, zero_mul]

/-- `ĥ(s) = ĝ(−i(s − 1))` for `g(u) = 2π(cosh r − cosh u)` on `[−r, r]`, in round 4's `ghatC`. -/
theorem hhat_eq_ghatC {r : ℝ} (hr : 0 ≤ r) (s : ℂ) :
    hhat (2 * Real.cosh r - 2) s =
      Pilot1ca.ghatC (fun u => 2 * Real.pi * (Real.cosh r - Real.cosh u)) r
        (-Complex.I * (s - 1)) := by
  rw [hhat_eq_interval hr, Pilot1ca.ghatC]
  refine intervalIntegral.integral_congr fun u _ => ?_
  have e : Complex.I * (-Complex.I * (s - 1)) * u = (s - 1) * u := by
    ring_nf; rw [Complex.I_sq]; ring
  simp only [e]

/-- **`ĥ` is entire** (round 6's `ghatC_differentiable`). -/
theorem differentiable_hhat {r : ℝ} (hr : 0 ≤ r) : Differentiable ℂ (hhat (2 * Real.cosh r - 2)) := by
  have h := Pilot1ca.ghatC_differentiable (g := fun u => 2 * Real.pi * (Real.cosh r - Real.cosh u))
    (a := r) ((by fun_prop : Continuous fun u : ℝ =>
      2 * Real.pi * (Real.cosh r - Real.cosh u)).intervalIntegrable _ _)
  have e : hhat (2 * Real.cosh r - 2) = fun s =>
      Pilot1ca.ghatC (fun u => 2 * Real.pi * (Real.cosh r - Real.cosh u)) r
        (-Complex.I * (s - 1)) := funext (hhat_eq_ghatC hr)
  rw [e]
  exact h.comp (by fun_prop)

/-- **The imaginary part, symmetrized**:
`Im ĥ(σ + it) = ∫_0^r 4π(cosh r − cosh u)·sinh((σ − 1)u)·sin(tu) du`. -/
theorem im_hhat_eq {r : ℝ} (hr : 0 ≤ r) (s : ℂ) :
    (hhat (2 * Real.cosh r - 2) s).im = ∫ u in (0 : ℝ)..r,
      4 * Real.pi * (Real.cosh r - Real.cosh u) * Real.sinh ((s.re - 1) * u) * Real.sin (s.im * u) := by
  set H : ℝ → ℝ := fun u => 2 * Real.pi * (Real.cosh r - Real.cosh u) *
    (Real.exp ((s.re - 1) * u) * Real.sin (s.im * u)) with hH
  have hHc : Continuous H := by rw [hH]; fun_prop
  have hint : IntervalIntegrable (fun u : ℝ =>
      ((2 * Real.pi * (Real.cosh r - Real.cosh u) : ℝ) : ℂ) * Complex.exp ((s - 1) * u))
      volume (-r) r := (by fun_prop : Continuous fun u : ℝ =>
        ((2 * Real.pi * (Real.cosh r - Real.cosh u) : ℝ) : ℂ) *
          Complex.exp ((s - 1) * u)).intervalIntegrable _ _
  rw [hhat_eq_interval hr, ← RCLike.im_to_complex, ← intervalIntegral.intervalIntegral_im hint]
  have h1 : (∫ u in (-r)..r, RCLike.im (((2 * Real.pi * (Real.cosh r - Real.cosh u) : ℝ) : ℂ) *
      Complex.exp ((s - 1) * u))) = ∫ u in (-r)..r, H u := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hH, RCLike.im_to_complex, Complex.exp_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, add_zero, zero_add]
  rw [h1, ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hHc.intervalIntegrable _ _) (hHc.intervalIntegrable _ _)]
  have h2 : (∫ u in (-r)..0, H u) = ∫ u in (0 : ℝ)..r, H (-u) := by
    rw [intervalIntegral.integral_comp_neg, neg_zero]
  rw [h2, ← intervalIntegral.integral_add (f := fun u => H (-u)) (g := H)
    ((hHc.comp continuous_neg).intervalIntegrable _ _) (hHc.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [hH, Real.cosh_neg, mul_neg, Real.sin_neg, Real.sinh_eq]
  ring

/-- **`Im ĥ > 0` off the real axis**: for `σ > 1` and `0 < t < π/r`, `Im ĥ(σ + it) > 0`. -/
theorem im_hhat_pos {r : ℝ} (hr : 0 < r) {s : ℂ} (hσ : 1 < s.re) (ht : 0 < s.im)
    (htr : s.im * r < Real.pi) : 0 < (hhat (2 * Real.cosh r - 2) s).im := by
  rw [im_hhat_eq hr.le]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun u : ℝ => 4 * Real.pi * (Real.cosh r - Real.cosh u) *
      Real.sinh ((s.re - 1) * u) * Real.sin (s.im * u)).intervalIntegrable _ _) (fun u hu => ?_) hr
  have hc : Real.cosh u < Real.cosh r := by
    rw [Real.cosh_lt_cosh, abs_of_pos hr, abs_of_pos hu.1]; exact hu.2
  have hsh : 0 < Real.sinh ((s.re - 1) * u) := Real.sinh_pos_iff.2 (mul_pos (by linarith) hu.1)
  have hsin : 0 < Real.sin (s.im * u) := by
    refine Real.sin_pos_of_pos_of_lt_pi (mul_pos ht hu.1) ?_
    calc s.im * u < s.im * r := mul_lt_mul_of_pos_left hu.2 ht
      _ < Real.pi := htr
  have := Real.pi_pos
  have : 0 < Real.cosh r - Real.cosh u := by linarith
  positivity

/-- The constant of the linear lower bound: `∫_0^r 4π(cosh r − cosh u)·sinh((σ − 1)u)·(2u/π) du`. -/
def imK (r σ : ℝ) : ℝ := ∫ u in (0 : ℝ)..r,
  4 * Real.pi * (Real.cosh r - Real.cosh u) * Real.sinh ((σ - 1) * u) * (2 / Real.pi * u)

theorem imK_pos {r σ : ℝ} (hr : 0 < r) (hσ : 1 < σ) : 0 < imK r σ := by
  unfold imK
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun u : ℝ => 4 * Real.pi * (Real.cosh r - Real.cosh u) *
      Real.sinh ((σ - 1) * u) * (2 / Real.pi * u)).intervalIntegrable _ _) (fun u hu => ?_) hr
  have hc : Real.cosh u < Real.cosh r := by
    rw [Real.cosh_lt_cosh, abs_of_pos hr, abs_of_pos hu.1]; exact hu.2
  have hsh : 0 < Real.sinh ((σ - 1) * u) := Real.sinh_pos_iff.2 (mul_pos (by linarith) hu.1)
  have := Real.pi_pos
  have : 0 < Real.cosh r - Real.cosh u := by linarith
  have := hu.1
  positivity

/-- **The linear lower bound**: `Im ĥ(σ + it) ≥ t·K(r, σ)` for `σ > 1` and `0 ≤ t ≤ π/(2r)`
(Jordan's inequality `sin x ≥ 2x/π`). -/
theorem im_hhat_ge {r : ℝ} (hr : 0 < r) {s : ℂ} (hσ : 1 < s.re) (ht : 0 ≤ s.im)
    (htr : s.im * r ≤ Real.pi / 2) : s.im * imK r s.re ≤ (hhat (2 * Real.cosh r - 2) s).im := by
  rw [im_hhat_eq hr.le, imK, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hr.le
    ((by fun_prop : Continuous fun u : ℝ => s.im * (4 * Real.pi * (Real.cosh r - Real.cosh u) *
      Real.sinh ((s.re - 1) * u) * (2 / Real.pi * u))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u : ℝ => 4 * Real.pi * (Real.cosh r - Real.cosh u) *
      Real.sinh ((s.re - 1) * u) * Real.sin (s.im * u)).intervalIntegrable _ _) (fun u hu => ?_)
  have hc : Real.cosh u ≤ Real.cosh r := by
    rw [Real.cosh_le_cosh, abs_of_pos hr, abs_of_nonneg hu.1]; exact hu.2
  have hsh : 0 ≤ Real.sinh ((s.re - 1) * u) :=
    Real.sinh_nonneg_iff.2 (mul_nonneg (by linarith) hu.1)
  have hsin : 2 / Real.pi * (s.im * u) ≤ Real.sin (s.im * u) := by
    refine Real.mul_le_sin (mul_nonneg ht hu.1) ?_
    calc s.im * u ≤ s.im * r := mul_le_mul_of_nonneg_left hu.2 ht
      _ ≤ Real.pi / 2 := htr
  have hA : 0 ≤ 4 * Real.pi * (Real.cosh r - Real.cosh u) * Real.sinh ((s.re - 1) * u) := by
    have := Real.pi_pos
    have : 0 ≤ Real.cosh r - Real.cosh u := by linarith
    positivity
  calc s.im * (4 * Real.pi * (Real.cosh r - Real.cosh u) * Real.sinh ((s.re - 1) * u) *
        (2 / Real.pi * u))
      = 4 * Real.pi * (Real.cosh r - Real.cosh u) * Real.sinh ((s.re - 1) * u) *
        (2 / Real.pi * (s.im * u)) := by ring
    _ ≤ 4 * Real.pi * (Real.cosh r - Real.cosh u) * Real.sinh ((s.re - 1) * u) *
        Real.sin (s.im * u) := mul_le_mul_of_nonneg_left hsin hA

/-- **On the real axis**: `ĥ(σ)` is real and positive. -/
theorem hhat_real_pos {r : ℝ} (hr : 0 < r) (σ : ℝ) :
    (hhat (2 * Real.cosh r - 2) σ).im = 0 ∧ 0 < (hhat (2 * Real.cosh r - 2) σ).re := by
  refine ⟨by rw [im_hhat_eq hr.le]; simp, ?_⟩
  have hint : IntervalIntegrable (fun u : ℝ =>
      ((2 * Real.pi * (Real.cosh r - Real.cosh u) : ℝ) : ℂ) * Complex.exp (((σ : ℂ) - 1) * u))
      volume (-r) r := (by fun_prop : Continuous fun u : ℝ =>
        ((2 * Real.pi * (Real.cosh r - Real.cosh u) : ℝ) : ℂ) *
          Complex.exp (((σ : ℂ) - 1) * u)).intervalIntegrable _ _
  rw [hhat_eq_interval hr.le, ← RCLike.re_to_complex, ← intervalIntegral.intervalIntegral_re hint]
  have h1 : (∫ u in (-r)..r, RCLike.re (((2 * Real.pi * (Real.cosh r - Real.cosh u) : ℝ) : ℂ) *
      Complex.exp (((σ : ℂ) - 1) * u))) = ∫ u in (-r)..r,
        2 * Real.pi * (Real.cosh r - Real.cosh u) * Real.exp ((σ - 1) * u) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    have e : ((σ : ℂ) - 1) * (u : ℂ) = (((σ - 1) * u : ℝ) : ℂ) := by push_cast; ring
    simp only [RCLike.re_to_complex, e, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h1]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun u : ℝ => 2 * Real.pi * (Real.cosh r - Real.cosh u) *
      Real.exp ((σ - 1) * u)).intervalIntegrable _ _) (fun u hu => ?_) (by linarith)
  have hc : Real.cosh u < Real.cosh r := by
    rw [Real.cosh_lt_cosh, abs_of_pos hr]; exact abs_lt.2 hu
  have := Real.pi_pos
  have : 0 < Real.cosh r - Real.cosh u := by linarith
  positivity

end Eis

end

#print axioms Eis.PInv.comp
#print axioms Eis.PInv.congr
#print axioms Eis.pinv_transl
#print axioms Eis.pinv_diag
#print axioms Eis.inv_identity
#print axioms Eis.pinv_E
#print axioms Eis.pinv_actP
#print axioms Eis.measurable_ppi
#print axioms Eis.measurableSet_hball
#print axioms Eis.mem_hball_actP
#print axioms Eis.bavg_comp_actP
#print axioms Eis.measurable_cpow_snd
#print axioms Eis.bavg_cpow
#print axioms Eis.mem_hball_one
#print axioms Eis.hball_one_subset
#print axioms Eis.volume_hball_one_lt_top
#print axioms Eis.rpow_le_of_mem_Icc
#print axioms Eis.hhat_eq_integral
#print axioms Eis.ballQ_exp
#print axioms Eis.cpow_ofReal_exp
#print axioms Eis.hhat_eq_line
#print axioms Eis.hhat_eq_interval
#print axioms Eis.hhat_eq_ghatC
#print axioms Eis.differentiable_hhat
#print axioms Eis.im_hhat_eq
#print axioms Eis.im_hhat_pos
#print axioms Eis.imK_pos
#print axioms Eis.im_hhat_ge
#print axioms Eis.hhat_real_pos
