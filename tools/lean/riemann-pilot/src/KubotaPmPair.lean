import KubotaPoincare
import KubotaThetaPair
import KubotaDerivative

/-! # The pairing of `P_m(ψ)` with `ũ_s` (round 430)

S5f-10 of round 360's plan, part 13 (S5f-10f, third part). Round 429's next step planned the pairing of round
429's twisted pseudo-Eisenstein series `P_m(ψ)` with `ũ_s` for `Re s > 2`, for `ψ` bounded and vanishing
outside `[α, β]` with `α > 0`. This round proves it, with `m = δ₃x`, `ν = ρ_G dμ` as in round 423, and
`H = Y + β + 1/α`:

* **The band series** (`bandF`, `bandD`, `bandL` and `bandL'`, definitions; **`hasDerivAt_bandL`**,
  **`differentiable_bandL`** and **`differentiable_inner_bandL`**, with `measurable_bandF`,
  `measurable_bandD`, `bandF_eq_zero_of_lt`, `bandD_eq_zero_of_lt`, `norm_bandF_le`, `norm_bandD_le`,
  `bandF_taylor`, `memLp_pseis_bandF` and `memLp_pseis_bandD`): for `0 < Y ≤ H`, `s ↦ E(1[Y ≤ v ≤ H]v^s)` is
  complex-differentiable into `L²(ν)` at every `s`, with derivative `E(1[Y ≤ v ≤ H]·log v·v^s)`, by round
  424's method; so its pairings are entire.
* **Bounds on `3P × [α, β]`** (`hBd`, a definition; **`tsum_height_rpow_le_unif`** and
  **`norm_pseis_le_hBd`**, with `norm_le_six_of_mem_fundP3`): for `|z| ≤ 6`, `0 < α ≤ v ≤ β` and `σ > 2`, the
  heights of the bottom rows satisfy `Σ (v/Q)^σ ≤ hBd σ α β` (round 387's `height_le_lattice`), so a
  pseudo-Eisenstein series of a profile with `|f(v)| ≤ v^σ` is bounded by `hBd σ α β` on `3P × [α, β]`.
* **Integrals over `3P × [α, β]`** (**`integral_fundP3_conj_mul`** and **`lintegral_rhoT3_pm_ne_top`**, with
  `zpow_neg_three_le`, `uhsMeasure_fundP3_Icc_lt_top_of_pos` and `integrableOn_fundP3_of_bdd`): for `ψ`
  vanishing outside `[α, β]` and `F` bounded on `3P × [α, β]`, Fubini,
  `∫_{3P×(0,∞)} conj ψ(v)·F dz dv/v³ = ∫_0^∞ v^{−3}·conj ψ(v)·∫_{3P} F(z, v) dz dv`, and the finiteness that
  round 429's unfolding asks for.
* **The pairing for `Re s > 2`** (**`height_le_band`**, **`eisHigh_eq_band`** and **`inner_pmSer_uL`**, with
  `le_band` and `eisLow_eq_band`): on `3P × [α, β]` every height is at most `H`, so there
  `h_s = E(1[Y ≤ v ≤ H]v^s)`, and for `Im ĥ(s) ≠ 0`,
  `⟨P_m(ψ), ũ_s⟩ = ∫_0^∞ v^{−3}·conj ψ(v)·∫_{3P} ĕ(−mz/9)E(z, v; s) dz dv − ⟨P_m(ψ), E(1[Y ≤ v ≤ H]v^s)⟩`.
* **The Bessel form** (`jPsi`, a definition; **`inner_pmSer_uL_bessel`**, with `integrableOn_Ioi_conj_mul` and
  `continuousOn_zpow_besselK`): for `x ≠ 0`, round 428's coefficient gives
  `⟨P_m(ψ), ũ_s⟩ = (2π/Γ(s))(2π|m|/9)^{s−1}·D_m(s)·J_ψ(s) + I_m·M_ψ(2 − s) − ⟨P_m(ψ), E(1[Y ≤ v ≤ H]v^s)⟩`,
  with `J_ψ(s) = ∫_0^∞ conj ψ(v)·v^{−2}·K_{s−1}(4π|m|v/9) dv`, `D_m(s)` round 428's Dirichlet series,
  `I_m = ∫_{3P} ĕ(−mz/9) dz` and round 427's `M_ψ`.
-/

open MeasureTheory Set Filter NumberField Complex Ideal Asymptotics
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### The band profile -/

/-- The band profile `1[Y ≤ v ≤ H]·v^s`. -/
def bandF (s : ℂ) (Y H : ℝ) (v : ℝ) : ℂ := if Y ≤ v ∧ v ≤ H then ((v : ℝ) : ℂ) ^ s else 0

/-- Its derivative in `s`, `1[Y ≤ v ≤ H]·log v·v^s`. -/
def bandD (s : ℂ) (Y H : ℝ) (v : ℝ) : ℂ :=
  if Y ≤ v ∧ v ≤ H then ((Real.log v : ℝ) : ℂ) * ((v : ℝ) : ℂ) ^ s else 0

theorem measurable_bandF (s : ℂ) (Y H : ℝ) : Measurable (bandF s Y H) :=
  Measurable.ite ((measurableSet_le measurable_const measurable_id).inter
    (measurableSet_le measurable_id measurable_const)) (Complex.measurable_ofReal.pow_const s)
    measurable_const

theorem measurable_bandD (s : ℂ) (Y H : ℝ) : Measurable (bandD s Y H) :=
  Measurable.ite ((measurableSet_le measurable_const measurable_id).inter
    (measurableSet_le measurable_id measurable_const))
    ((Complex.measurable_ofReal.comp Real.measurable_log).mul (Complex.measurable_ofReal.pow_const s))
    measurable_const

theorem bandF_eq_zero_of_lt (s : ℂ) {Y H v : ℝ} (hv : v < Y) : bandF s Y H v = 0 := by
  unfold bandF
  simp only [show ¬ (Y ≤ v ∧ v ≤ H) from fun h => not_le.2 hv h.1, ↓reduceIte]

theorem bandD_eq_zero_of_lt (s : ℂ) {Y H v : ℝ} (hv : v < Y) : bandD s Y H v = 0 := by
  unfold bandD
  simp only [show ¬ (Y ≤ v ∧ v ≤ H) from fun h => not_le.2 hv h.1, ↓reduceIte]

/-- `|1[Y ≤ v ≤ H]v^s| ≤ Y^σ + H^σ`. -/
theorem norm_bandF_le (s : ℂ) {Y H : ℝ} (hY : 0 < Y) (hYH : Y ≤ H) (v : ℝ) :
    ‖bandF s Y H v‖ ≤ Y ^ s.re + H ^ s.re := by
  unfold bandF
  split_ifs with h
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hY h.1)]
    exact rpow_le_add_of_mem_Icc hY ⟨h.1, h.2⟩
  · rw [norm_zero]
    have := Real.rpow_nonneg hY.le s.re
    have := Real.rpow_nonneg (hY.le.trans hYH) s.re
    linarith

/-- `|1[Y ≤ v ≤ H]·log v·v^s| ≤ (|log Y| + |log H|)(Y^σ + H^σ)`. -/
theorem norm_bandD_le (s : ℂ) {Y H : ℝ} (hY : 0 < Y) (hYH : Y ≤ H) (v : ℝ) :
    ‖bandD s Y H v‖ ≤ (|Real.log Y| + |Real.log H|) * (Y ^ s.re + H ^ s.re) := by
  have hb0 : 0 ≤ Y ^ s.re + H ^ s.re := by
    have := Real.rpow_nonneg hY.le s.re
    have := Real.rpow_nonneg (hY.le.trans hYH) s.re
    linarith
  unfold bandD
  split_ifs with h
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hY h.1)]
    exact mul_le_mul (abs_log_le_of_mem_Icc hY ⟨h.1, h.2⟩) (rpow_le_add_of_mem_Icc hY ⟨h.1, h.2⟩)
      (Real.rpow_nonneg (hY.le.trans h.1) _) (by positivity)
  · rw [norm_zero]
    positivity

/-- **Taylor's bound for the band profile, uniform in `v`**:
`|f_{s+h}(v) − f_s(v) − h·f′_s(v)| ≤ (Y^σ + H^σ)·(|h|L)²` with `L = |log Y| + |log H|`, when `|h|L ≤ 1`. -/
theorem bandF_taylor (s : ℂ) {Y H : ℝ} (hY : 0 < Y) (hYH : Y ≤ H) {h : ℂ}
    (hh : ‖h‖ * (|Real.log Y| + |Real.log H|) ≤ 1) (v : ℝ) :
    ‖bandF (s + h) Y H v - bandF s Y H v - h * bandD s Y H v‖ ≤
      (Y ^ s.re + H ^ s.re) * (‖h‖ * (|Real.log Y| + |Real.log H|)) ^ 2 := by
  unfold bandF bandD
  split_ifs with hv
  · have hv0 : 0 < v := lt_of_lt_of_le hY hv.1
    have hlog := abs_log_le_of_mem_Icc hY ⟨hv.1, hv.2⟩
    have hhl : ‖h * (Real.log v : ℂ)‖ ≤ ‖h‖ * (|Real.log Y| + |Real.log H|) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
    refine (norm_cpow_taylor_le hv0 s h (hhl.trans hh)).trans ?_
    exact mul_le_mul (rpow_le_add_of_mem_Icc hY ⟨hv.1, hv.2⟩)
      (pow_le_pow_left₀ (norm_nonneg _) hhl 2) (by positivity) (by
        have := Real.rpow_nonneg hY.le s.re
        have := Real.rpow_nonneg (hY.le.trans hYH) s.re
        linarith)
  · simp only [sub_zero, mul_zero, norm_zero]
    have := Real.rpow_nonneg hY.le s.re
    have := Real.rpow_nonneg (hY.le.trans hYH) s.re
    positivity

theorem memLp_pseis_bandF (s : ℂ) {Y H : ℝ} (hY : 0 < Y) (hYH : Y ≤ H) :
    MemLp (pseis (bandF s Y H)) 2 (muR rhoG) :=
  memLp_pseis_of_vanish (measurable_bandF s Y H) hY (by
      have := Real.rpow_nonneg hY.le s.re
      have := Real.rpow_nonneg (hY.le.trans hYH) s.re
      linarith)
    (fun v _ hv => bandF_eq_zero_of_lt s hv) (fun v _ => norm_bandF_le s hY hYH v)

theorem memLp_pseis_bandD (s : ℂ) {Y H : ℝ} (hY : 0 < Y) (hYH : Y ≤ H) :
    MemLp (pseis (bandD s Y H)) 2 (muR rhoG) :=
  memLp_pseis_of_vanish (measurable_bandD s Y H) hY (by
      have := Real.rpow_nonneg hY.le s.re
      have := Real.rpow_nonneg (hY.le.trans hYH) s.re
      positivity)
    (fun v _ hv => bandD_eq_zero_of_lt s hv) (fun v _ => norm_bandD_le s hY hYH v)

/-- `E(1[Y ≤ v ≤ H]v^s)` in `L²(ν)`. -/
def bandL {Y H : ℝ} (hY : 0 < Y) (hYH : Y ≤ H) (s : ℂ) : Lp ℂ 2 (muR rhoG) :=
  (memLp_pseis_bandF s hY hYH).toLp (pseis (bandF s Y H))

/-- Its derivative `E(1[Y ≤ v ≤ H]·log v·v^s)` in `L²(ν)`. -/
def bandL' {Y H : ℝ} (hY : 0 < Y) (hYH : Y ≤ H) (s : ℂ) : Lp ℂ 2 (muR rhoG) :=
  (memLp_pseis_bandD s hY hYH).toLp (pseis (bandD s Y H))

/-- **`s ↦ E(1[Y ≤ v ≤ H]v^s)` is complex-differentiable into `L²(ν)` at every `s`**, with derivative
`E(1[Y ≤ v ≤ H]·log v·v^s)`, by round 424's method. -/
theorem hasDerivAt_bandL {Y H : ℝ} (hY : 0 < Y) (hYH : Y ≤ H) (s₀ : ℂ) :
    HasDerivAt (bandL hY hYH) (bandL' hY hYH s₀) s₀ := by
  set L := |Real.log Y| + |Real.log H|
  set Mb := fun t : ℂ => Y ^ t.re + H ^ t.re
  have hMb : ∀ t : ℂ, 0 ≤ Mb t := fun t => by
    have := Real.rpow_nonneg hY.le t.re
    have := Real.rpow_nonneg (hY.le.trans hYH) t.re
    simp only [Mb]
    linarith
  set P := (psC Y ^ (1 / 2 : ℝ)).toReal
  have hL : 0 ≤ L := by positivity
  have hP : 0 ≤ P := ENNReal.toReal_nonneg
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  set K := P * (Mb s₀ * L ^ 2)
  have hK : 0 ≤ K := by have := hMb s₀; positivity
  set ε := min (1 / (L + 1)) (c / (K + 1))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  filter_upwards [Metric.ball_mem_nhds s₀ hε] with s hs
  rw [Metric.mem_ball, dist_eq_norm] at hs
  set h := s - s₀ with hh_def
  have hs' : s = s₀ + h := by rw [hh_def]; ring
  have h1 : ‖h‖ * L ≤ 1 := by
    have : ‖h‖ ≤ 1 / (L + 1) := hs.le.trans (min_le_left _ _)
    calc ‖h‖ * L ≤ 1 / (L + 1) * L := mul_le_mul_of_nonneg_right this hL
      _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; linarith
  have h2 : K * ‖h‖ ≤ c := by
    have : ‖h‖ ≤ c / (K + 1) := hs.le.trans (min_le_right _ _)
    calc K * ‖h‖ ≤ K * (c / (K + 1)) := mul_le_mul_of_nonneg_left this hK
      _ ≤ c := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
  set rem : ℝ → ℂ := fun v => bandF s Y H v - bandF s₀ Y H v - h * bandD s₀ Y H v with hrem
  have hrem_m : Measurable rem :=
    ((measurable_bandF s Y H).sub (measurable_bandF s₀ Y H)).sub
      (measurable_const.mul (measurable_bandD s₀ Y H))
  have hrem0 : ∀ v, 0 < v → v < Y → rem v = 0 := fun v _ hv => by
    simp only [hrem, bandF_eq_zero_of_lt _ hv, bandD_eq_zero_of_lt _ hv, sub_zero, mul_zero]
  have hremb : ∀ v, 0 < v → ‖rem v‖ ≤ Mb s₀ * (‖h‖ * L) ^ 2 := fun v _ => by
    have := bandF_taylor s₀ hY hYH h1 v
    rwa [← hs'] at this
  have hD : 0 ≤ Mb s₀ * (‖h‖ * L) ^ 2 := by have := hMb s₀; positivity
  have hpw : ∀ (f : ℝ → ℂ) (D : ℝ), 0 ≤ D → (∀ v, 0 < v → v < Y → f v = 0) →
      (∀ v, 0 < v → ‖f v‖ ≤ D) → ∀ v, 0 < v → ‖f v‖ ≤ D * (Y ^ 3)⁻¹ * v ^ (3 : ℝ) :=
    fun f D hD0 h0 hb v hv => norm_le_pow_of_vanish hY hD0 h0 hb hv
  have hI : ∀ t : ℂ, ∀ v, 0 < v → ‖bandF t Y H v‖ ≤ Mb t * (Y ^ 3)⁻¹ * v ^ (3 : ℝ) :=
    fun t => hpw _ _ (hMb t) (fun v _ hv => bandF_eq_zero_of_lt t hv)
      (fun v _ => norm_bandF_le t hY hYH v)
  have hDr : ∀ v, 0 < v → ‖h * bandD s₀ Y H v‖ ≤ ‖h‖ * (L * Mb s₀) * (Y ^ 3)⁻¹ * v ^ (3 : ℝ) :=
    hpw _ _ (by have := hMb s₀; positivity)
      (fun v _ hv => by rw [bandD_eq_zero_of_lt s₀ hv, mul_zero])
      (fun v _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_bandD_le s₀ hY hYH v) (norm_nonneg _))
  have hsub : ∀ v, 0 < v → ‖bandF s Y H v - bandF s₀ Y H v‖ ≤
      (Mb s * (Y ^ 3)⁻¹ + Mb s₀ * (Y ^ 3)⁻¹) * v ^ (3 : ℝ) := fun v hv => by
    refine (norm_sub_le _ _).trans ?_
    have := add_le_add (hI s v hv) (hI s₀ v hv)
    linarith
  have hae : (fun p => pseis (bandF s Y H) p - pseis (bandF s₀ Y H) p - h * pseis (bandD s₀ Y H) p)
      =ᵐ[muR rhoG] pseis rem := by
    filter_upwards [ae_muR_UHS rhoG] with p hp
    rw [← pseis_const_mul, ← pseis_sub (by norm_num : (2 : ℝ) < 3) (hI s) (hI s₀) hp,
      ← pseis_sub (by norm_num : (2 : ℝ) < 3) hsub hDr hp]
  have hnorm : ‖bandL hY hYH s - bandL hY hYH s₀ - h • bandL' hY hYH s₀‖ ≤
      P * (Mb s₀ * (‖h‖ * L) ^ 2) := by
    rw [bandL, bandL, bandL', ← MemLp.toLp_const_smul, ← MemLp.toLp_sub, ← MemLp.toLp_sub,
      Lp.norm_toLp]
    have he : eLpNorm (pseis (bandF s Y H) - pseis (bandF s₀ Y H) - h • pseis (bandD s₀ Y H)) 2
        (muR rhoG) = eLpNorm (pseis rem) 2 (muR rhoG) := eLpNorm_congr_ae hae
    rw [he]
    have hb := eLpNorm_pseis_le hrem_m hY hD hrem0 hremb
    have hfin : psC Y ^ (1 / 2 : ℝ) * ENNReal.ofReal (Mb s₀ * (‖h‖ * L) ^ 2) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (psC_lt_top Y).ne)
        ENNReal.ofReal_ne_top
    refine (ENNReal.toReal_mono hfin hb).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD]
  calc ‖bandL hY hYH s - bandL hY hYH s₀ - (s - s₀) • bandL' hY hYH s₀‖
      ≤ P * (Mb s₀ * (‖h‖ * L) ^ 2) := hnorm
    _ = K * ‖h‖ * ‖h‖ := by ring
    _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- **`s ↦ E(1[Y ≤ v ≤ H]v^s)` is entire**, into `L²(ν)`. -/
theorem differentiable_bandL {Y H : ℝ} (hY : 0 < Y) (hYH : Y ≤ H) : Differentiable ℂ (bandL hY hYH) :=
  fun s => (hasDerivAt_bandL hY hYH s).differentiableAt

/-- **Pairings with `E(1[Y ≤ v ≤ H]v^s)` are entire.** -/
theorem differentiable_inner_bandL (y : Lp ℂ 2 (muR rhoG)) {Y H : ℝ} (hY : 0 < Y) (hYH : Y ≤ H) :
    Differentiable ℂ fun s => inner ℂ y (bandL hY hYH s) := fun s =>
  ((innerSL ℂ y).differentiableAt).comp s (differentiable_bandL hY hYH s)

/-! ### Bounds on `3P × [α, β]` -/

theorem norm_le_six_of_mem_fundP3 {z : ℂ} (hz : z ∈ fundP3) : ‖z‖ ≤ 6 := by
  have h := norm_le_two_of_mem_fundP (show z / 3 ∈ fundP from hz)
  rw [norm_div, show ‖(3 : ℂ)‖ = 3 by norm_num, div_le_iff₀ (by norm_num)] at h
  linarith

open Classical in
/-- **The heights, uniformly on a compact set**: for `|z| ≤ 6` and `α ≤ v ≤ β` with `α > 0`,
`Σ_{(c, d)} (v/Q)^σ ≤ (9(2β² + 146)/α)^σ·(Σ_x (1 + |σx|)^{−σ})²` for `σ > 2` (round 387's
`height_le_lattice`). -/
theorem tsum_height_rpow_le_unif {σ : ℝ} (hσ : 2 < σ) {α β : ℝ} (hα : 0 < α) {p : ℂ × ℝ}
    (hz : ‖p.1‖ ≤ 6) (hαv : α ≤ p.2) (hvβ : p.2 ≤ β) :
    ∑' cd : 𝓞 K × 𝓞 K, (if BRow cd then (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) ^ σ else 0) ≤
      (9 * (2 * β ^ 2 + 146) / α) ^ σ * (∑' x : 𝓞 K, (1 + ‖σO x‖) ^ (-σ)) ^ 2 := by
  have hv : 0 < p.2 := lt_of_lt_of_le hα hαv
  have hp : p ∈ UHS := hv
  set C := 9 * p.2 / (p.2 ^ 2 / (2 * p.2 ^ 2 + 4 * Complex.normSq p.1 + 2))
  set Lb := 9 * (2 * β ^ 2 + 146) / α
  have hC : 0 < C := div_pos (by positivity) (div_pos (pow_pos hv 2)
    (by nlinarith [Complex.normSq_nonneg p.1]))
  have hCL : C ≤ Lb := by
    have hn : Complex.normSq p.1 ≤ 36 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg p.1]
    have e : C = 9 * (2 * p.2 ^ 2 + 4 * Complex.normSq p.1 + 2) / p.2 := by
      simp only [C]
      field_simp
    rw [e, div_le_div_iff₀ hv hα]
    have hβ : p.2 ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hv.le hvβ 2
    nlinarith [Complex.normSq_nonneg p.1, mul_le_mul_of_nonneg_left hαv
      (by nlinarith [Complex.normSq_nonneg p.1] : (0 : ℝ) ≤ 9 * (2 * p.2 ^ 2 + 4 * Complex.normSq p.1 + 2)),
      mul_le_mul_of_nonneg_left hvβ (by positivity : (0 : ℝ) ≤ 9 * (2 * β ^ 2 + 146)), hβ]
  have hS := summable_O_rpow hσ
  have hS2 : Summable fun z : 𝓞 K × 𝓞 K => (1 + ‖σO z.1‖) ^ (-σ) * (1 + ‖σO z.2‖) ^ (-σ) :=
    Summable.mul_of_nonneg hS hS (fun _ => by positivity) (fun _ => by positivity)
  calc ∑' cd : 𝓞 K × 𝓞 K, (if BRow cd then (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) ^ σ else 0)
      ≤ ∑' cd : 𝓞 K × 𝓞 K, Lb ^ σ * ((1 + ‖σO cd.1‖) ^ (-σ) * (1 + ‖σO cd.2‖) ^ (-σ)) := by
        refine Summable.tsum_le_tsum (fun cd => ?_) (summable_height_rpow hσ hp) (hS2.mul_left _)
        split_ifs with h
        · have hle := height_le_lattice h hp
          have h0 : 0 ≤ p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 :=
            (div_pos hv (uhsDen_pos_of_BRow h hp)).le
          calc (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) ^ σ
              ≤ (Lb * ((1 + ‖σO cd.1‖) * (1 + ‖σO cd.2‖))⁻¹) ^ σ :=
                Real.rpow_le_rpow h0 (hle.trans (mul_le_mul_of_nonneg_right hCL (by positivity)))
                  (by linarith)
            _ = Lb ^ σ * ((1 + ‖σO cd.1‖) ^ (-σ) * (1 + ‖σO cd.2‖) ^ (-σ)) := by
                rw [Real.mul_rpow (hC.le.trans hCL) (by positivity), Real.inv_rpow (by positivity),
                  ← Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) (by positivity)]
        · positivity
    _ = Lb ^ σ * (∑' x : 𝓞 K, (1 + ‖σO x‖) ^ (-σ)) ^ 2 := by
        have hSn : Summable fun x : 𝓞 K => ‖(1 + ‖σO x‖) ^ (-σ)‖ :=
          hS.congr fun x => (Real.norm_of_nonneg (by positivity)).symm
        rw [tsum_mul_left, sq, tsum_mul_tsum_of_summable_norm hSn hSn]

/-- The bound of `tsum_height_rpow_le_unif`. -/
def hBd (σ α β : ℝ) : ℝ := (9 * (2 * β ^ 2 + 146) / α) ^ σ * (∑' x : 𝓞 K, (1 + ‖σO x‖) ^ (-σ)) ^ 2

/-- **A pseudo-Eisenstein series of a profile `|f(v)| ≤ v^σ` is bounded on `3P × [α, β]`** by `hBd σ α β`. -/
theorem norm_pseis_le_hBd {f : ℝ → ℂ} {σ : ℝ} (hσ : 2 < σ) (hf : ∀ v, 0 < v → ‖f v‖ ≤ v ^ σ)
    {α β : ℝ} (hα : 0 < α) {p : ℂ × ℝ} (hz : p.1 ∈ fundP3) (hαv : α ≤ p.2) (hvβ : p.2 ≤ β) :
    ‖pseis f p‖ ≤ hBd σ α β := by
  have hp : p ∈ UHS := show 0 < p.2 from lt_of_lt_of_le hα hαv
  have hf1 : ∀ v, 0 < v → ‖f v‖ ≤ 1 * v ^ σ := fun v hv => by rw [one_mul]; exact hf v hv
  refine (tsum_of_norm_bounded (summable_height_rpow hσ hp).hasSum fun cd => ?_).trans
    (tsum_height_rpow_le_unif hσ hα (norm_le_six_of_mem_fundP3 hz) hαv hvβ)
  have := norm_psTerm_le hf1 hp cd
  rwa [one_mul] at this

/-! ### Integrals over `3P × [α, β]` -/

theorem zpow_neg_three_le {α v : ℝ} (hα : 0 < α) (hv : α ≤ v) : v ^ (-3 : ℤ) ≤ α ^ (-3 : ℤ) := by
  have e : ∀ x : ℝ, x ^ (-3 : ℤ) = (x ^ 3)⁻¹ := fun x => by
    rw [zpow_neg]
    norm_cast
  rw [e, e]
  exact inv_anti₀ (pow_pos hα 3) (pow_le_pow_left₀ hα.le hv 3)

/-- `μ(3P × [α, β]) < ∞` for `α > 0`. -/
theorem uhsMeasure_fundP3_Icc_lt_top_of_pos {α β : ℝ} (hα : 0 < α) :
    uhsMeasure (fundP3 ×ˢ Icc α β) < ⊤ := by
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  rw [uhsMeasure, withDensity_apply _ hT]
  calc ∫⁻ p in fundP3 ×ˢ Icc α β, uhsW p ∂(volume.restrict UHS)
      ≤ ∫⁻ _ in fundP3 ×ˢ Icc α β, ENNReal.ofReal (α ^ (-3 : ℤ)) ∂(volume.restrict UHS) := by
        refine setLIntegral_mono measurable_const fun p hp => ?_
        unfold uhsW
        exact ENNReal.ofReal_le_ofReal (zpow_neg_three_le hα hp.2.1)
    _ = ENNReal.ofReal (α ^ (-3 : ℤ)) * (volume.restrict UHS) (fundP3 ×ˢ Icc α β) :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (α ^ (-3 : ℤ)) * volume (fundP3 ×ˢ Icc α β) := by
        gcongr
        exact Measure.restrict_le_self
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [Measure.volume_eq_prod, Measure.prod_prod, volume_fundP3, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **Integrable on `3P × (0, ∞)`**: a function bounded on `3P × [α, β]`, times `ψ(v)` vanishing outside
`[α, β]`. -/
theorem integrableOn_fundP3_of_bdd {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) {G : ℂ × ℝ → ℂ}
    (hG : Measurable G) {B : ℝ} (hB : ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → ‖G p‖ ≤ B) :
    IntegrableOn (fun p : ℂ × ℝ => conj (ψ p.2) * G p) (Prod.fst ⁻¹' fundP3) uhsMeasure := by
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  have hm : Measurable fun p : ℂ × ℝ => conj (ψ p.2) * G p :=
    (Complex.continuous_conj.measurable.comp (hψ.comp measurable_snd)).mul hG
  have h1 : IntegrableOn (fun p : ℂ × ℝ => conj (ψ p.2) * G p) (fundP3 ×ˢ Icc α β) uhsMeasure := by
    refine Measure.integrableOn_of_bounded (M := M * B) (uhsMeasure_fundP3_Icc_lt_top_of_pos hα).ne
      hm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hT]
    refine Eventually.of_forall fun p hp => ?_
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hM _) (hB p hp.1 hp.2) (norm_nonneg _) hM0
  refine h1.of_forall_sdiff_eq_zero (measurableSet_fundP3.preimage measurable_fst) fun p hp => ?_
  have h2 : p.2 ∉ Icc α β := fun h => hp.2 ⟨hp.1, h⟩
  rw [hψ0 _ h2, map_zero, zero_mul]

/-- **Fubini on `3P × (0, ∞)`**: for `ψ` vanishing outside `[α, β]` and `F` bounded on `3P × [α, β]`,
`∫_{3P×(0,∞)} conj ψ(v)·F dz dv/v³ = ∫_0^∞ v^{−3}·conj ψ(v)·∫_{3P} F(z, v) dz dv`. -/
theorem integral_fundP3_conj_mul {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) {F : ℂ × ℝ → ℂ}
    (hF : Measurable F) {B : ℝ} (hB : ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → ‖F p‖ ≤ B) :
    ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * F p ∂uhsMeasure =
      ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * ∫ z in fundP3, F (z, v) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hB0 : ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → 0 ≤ B := fun p h1 h2 =>
    (norm_nonneg _).trans (hB p h1 h2)
  set T : Set (ℂ × ℝ) := fundP3 ×ˢ Icc α β with hTdef
  set H : ℂ × ℝ → ℂ := fun q => ((q.2 ^ (-3 : ℤ) : ℝ) : ℂ) * (conj (ψ q.2) * F q) with hHdef
  have hT : MeasurableSet T := measurableSet_fundP3.prod measurableSet_Icc
  have hHm : Measurable H := by
    have : Measurable fun q : ℂ × ℝ => ((q.2 ^ (-3 : ℤ) : ℝ) : ℂ) := by fun_prop
    exact this.mul ((Complex.continuous_conj.measurable.comp (hψ.comp measurable_snd)).mul hF)
  have hstep1 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * F p ∂uhsMeasure = ∫ q, T.indicator H q := by
    rw [← integral_indicator (measurableSet_fundP3.preimage measurable_fst), uhsMeasure,
      integral_withDensity_eq_integral_toReal_smul measurable_uhsW
        (Eventually.of_forall fun q => ENNReal.ofReal_lt_top),
      ← integral_indicator measurableSet_UHS]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    by_cases hq : q ∈ T
    · have hv : 0 < q.2 := lt_of_lt_of_le hα hq.2.1
      have hq' : q ∈ UHS := hv
      rw [indicator_of_mem hq', indicator_of_mem (show q ∈ Prod.fst ⁻¹' fundP3 from hq.1),
        indicator_of_mem hq, uhsW, ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    · rw [indicator_of_notMem hq]
      by_cases hq' : q ∈ UHS
      · rw [indicator_of_mem hq']
        by_cases h3 : q.1 ∈ fundP3
        · have h4 : q.2 ∉ Icc α β := fun h => hq ⟨h3, h⟩
          rw [indicator_of_mem (show q ∈ Prod.fst ⁻¹' fundP3 from h3), hψ0 _ h4, map_zero, zero_mul,
            smul_zero]
        · rw [indicator_of_notMem (show q ∉ Prod.fst ⁻¹' fundP3 from h3), smul_zero]
      · rw [indicator_of_notMem hq']
  have hint : Integrable (T.indicator H) (volume : Measure (ℂ × ℝ)) := by
    rw [integrable_indicator_iff hT]
    have hvolT : volume T ≠ ⊤ := by
      rw [hTdef, Measure.volume_eq_prod, Measure.prod_prod, volume_fundP3, Real.volume_Icc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    refine Measure.integrableOn_of_bounded (M := α ^ (-3 : ℤ) * (M * |B|)) hvolT
      hHm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hT]
    refine Eventually.of_forall fun q hq => ?_
    have hv : 0 < q.2 := lt_of_lt_of_le hα hq.2.1
    simp only [hHdef]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    exact mul_le_mul (zpow_neg_three_le hα hq.2.1)
      (mul_le_mul (hM _) ((hB q hq.1 hq.2).trans (le_abs_self B)) (norm_nonneg _) hM0)
      (by positivity) (by positivity)
  have hslice : ∀ v : ℝ, ∫ z, T.indicator H (z, v) = (Ioi (0 : ℝ)).indicator
      (fun v => ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * ∫ z in fundP3, F (z, v)) v := by
    intro v
    by_cases hv : v ∈ Icc α β
    · have hv0 : 0 < v := lt_of_lt_of_le hα hv.1
      rw [indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv0)]
      have e : (fun z => T.indicator H (z, v)) = fundP3.indicator (fun z => H (z, v)) := by
        funext z
        by_cases hz : z ∈ fundP3
        · rw [indicator_of_mem (show (z, v) ∈ T from ⟨hz, hv⟩), indicator_of_mem hz]
        · rw [indicator_of_notMem (show (z, v) ∉ T from fun h => hz h.1), indicator_of_notMem hz]
      rw [e, integral_indicator measurableSet_fundP3]
      simp only [hHdef]
      rw [integral_const_mul, integral_const_mul]
      ring
    · have e : (fun z => T.indicator H (z, v)) = fun _ => 0 := by
        funext z
        rw [indicator_of_notMem (show (z, v) ∉ T from fun h => hv h.2)]
      rw [e, integral_zero]
      by_cases hv0 : v ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hv0, hψ0 v hv, map_zero, mul_zero, zero_mul]
      · rw [indicator_of_notMem hv0]
  rw [hstep1, Measure.volume_eq_prod,
    integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact hint)]
  simp_rw [hslice]
  rw [integral_indicator measurableSet_Ioi]

/-- **The finiteness for the unfolding of `P_m(ψ)`**, for `ψ` vanishing outside `[α, β]` and `G` bounded on
`3P × [α, β]`. -/
theorem lintegral_rhoT3_pm_ne_top (m : 𝓞 K) {ψ : ℝ → ℂ} {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) {G : ℂ × ℝ → ℂ} {B : ℝ}
    (hB : ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → ‖G p‖ ≤ B) :
    ∫⁻ p, rhoT3 p * ‖conj (ψ p.2 * ebr (σO m * p.1 / 9)) * G p‖ₑ ∂uhsMeasure ≠ ⊤ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  refine ne_top_of_le_ne_top (b := ∫⁻ p, (fundP3 ×ˢ Icc α β).indicator
      (fun _ => ENNReal.ofReal (M * |B|)) p ∂uhsMeasure) ?_ (lintegral_mono fun p => ?_)
  · rw [lintegral_indicator_const hT]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (uhsMeasure_fundP3_Icc_lt_top_of_pos hα).ne
  · by_cases hp : p ∈ fundP3 ×ˢ Icc α β
    · rw [indicator_of_mem hp]
      calc rhoT3 p * ‖conj (ψ p.2 * ebr (σO m * p.1 / 9)) * G p‖ₑ
          ≤ 1 * ‖conj (ψ p.2 * ebr (σO m * p.1 / 9)) * G p‖ₑ := by
            gcongr
            exact rhoT3_le_one p
        _ = ENNReal.ofReal ‖conj (ψ p.2 * ebr (σO m * p.1 / 9)) * G p‖ := by rw [one_mul, ofReal_norm]
        _ ≤ ENNReal.ofReal (M * |B|) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [norm_mul, Complex.norm_conj, norm_mul, norm_ebr, mul_one]
            exact mul_le_mul (hM _) ((hB p hp.1 hp.2).trans (le_abs_self B)) (norm_nonneg _) hM0
    · rw [indicator_of_notMem hp]
      by_cases h3 : p.1 ∈ fundP3
      · have h4 : p.2 ∉ Icc α β := fun h => hp ⟨h3, h⟩
        rw [hψ0 _ h4, zero_mul, map_zero, zero_mul, enorm_zero, mul_zero]
      · have h0 : rhoT3 p = 0 := by
          unfold rhoT3
          rw [indicator_of_notMem h3]
        rw [h0, zero_mul]

/-! ### The pairing for `Re s > 2` -/

theorem le_band {Y α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) : Y ≤ Y + β + 1 / α := by
  have : 0 < 1 / α := by positivity
  linarith

/-- **Every height on `3P × [α, β]` is at most `Y + β + 1/α`**: `v` for the row `(0, 1)`, at most `1/v` for
the others (round 427's `height_le_inv`). -/
theorem height_le_band {cd : 𝓞 K × 𝓞 K} (hb : BRow cd) {Y α β : ℝ} (hY : 0 < Y) (hα : 0 < α)
    {p : ℂ × ℝ} (hαv : α ≤ p.2) (hvβ : p.2 ≤ β) :
    p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 ≤ Y + β + 1 / α := by
  have hv : 0 < p.2 := lt_of_lt_of_le hα hαv
  have h1α : 0 < 1 / α := by positivity
  by_cases hc : cd.1 = 0
  · have hcd : cd = (0, 1) := by
      obtain ⟨c, d⟩ := cd
      simp only at hc
      subst hc
      rw [bRow_zero_iff.1 hb]
    rw [hcd]
    have hD : uhsDen (σO 0) (σO 1) p.1 p.2 = 1 := by
      unfold uhsDen
      simp
    simp only
    rw [hD, div_one]
    linarith
  · have h1 := height_le_inv hc cd.2 p.1 hv
    have h2 : 1 / p.2 ≤ 1 / α := one_div_le_one_div_of_le hα hαv
    linarith

/-- **`h_s` on `3P × [α, β]` is a band series**: `h_s = E(1[Y ≤ v ≤ Y + β + 1/α]v^s)` there. -/
theorem eisHigh_eq_band (s : ℂ) {Y α β : ℝ} (hY : 0 < Y) (hα : 0 < α) {p : ℂ × ℝ} (hαv : α ≤ p.2)
    (hvβ : p.2 ≤ β) : eisHigh s Y p = pseis (bandF s Y (Y + β + 1 / α)) p := by
  unfold eisHigh pseis
  refine tsum_congr fun cd => ?_
  unfold psTerm
  split_ifs with hb
  · congr 1
    have hH := height_le_band hb hY hα hαv hvβ
    unfold highF bandF
    by_cases hlt : p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 < Y
    · have hn : ¬ (Y ≤ p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 ∧
          p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 ≤ Y + β + 1 / α) := fun h => not_le.2 hlt h.1
      simp only [hlt, hn, ↓reduceIte]
    · have hy : Y ≤ p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 ∧
          p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 ≤ Y + β + 1 / α := ⟨not_lt.1 hlt, hH⟩
      simp only [hlt, hy, and_self, ↓reduceIte]
  · rfl

/-- **`E_s − h_s = E_s − E(1[Y ≤ v ≤ H]v^s)` on `3P × [α, β]`**, `H = Y + β + 1/α`, for `Re s > 2`. -/
theorem eisLow_eq_band {s : ℂ} (hs : 2 < s.re) {Y α β : ℝ} (hY : 0 < Y) (hα : 0 < α) {p : ℂ × ℝ}
    (hαv : α ≤ p.2) (hvβ : p.2 ≤ β) :
    eisLow s Y p = eis1 s p - pseis (bandF s Y (Y + β + 1 / α)) p := by
  have hp : p ∈ UHS := show 0 < p.2 from lt_of_lt_of_le hα hαv
  rw [eis1_eq_eisLow_add_eisHigh hs Y hp, eisHigh_eq_band s hY hα hαv hvβ]
  ring

/-- **The pairing of `P_m(ψ)` with `ũ_s` for `Re s > 2`**: for `m = δ₃x`, `R ≥ 0`, `Y > 0`, `ψ` measurable and
bounded, vanishing outside `[α, β]` with `0 < α ≤ β`, and `Im ĥ(s) ≠ 0`,
`⟨P_m(ψ), ũ_s⟩ = ∫_0^∞ v^{−3}·conj ψ(v)·∫_{3P} ĕ(−mz/9)E(z, v; s) dz dv − ⟨P_m(ψ), E(1[Y ≤ v ≤ H]v^s)⟩`
with `H = Y + β + 1/α`. -/
theorem inner_pmSer_uL (x : 𝓞 K) {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ}
    (hψ : Measurable ψ) (hψ2 : MemLp (pmSer (δ3 * x) ψ) 2 (muR rhoG)) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) {s : ℂ}
    (hs : 2 < s.re) (him : (hhat R s).im ≠ 0) :
    inner ℂ (hψ2.toLp (pmSer (δ3 * x) ψ)) (uL R hR Y hY s) =
      (∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) *
        ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * eis1 s (z, v)) -
      inner ℂ (hψ2.toLp (pmSer (δ3 * x) ψ)) (bandL hY (le_band hα hαβ) s) := by
  set H := Y + β + 1 / α
  set m := δ3 * x with hm
  have hσ : 2 < s.re := hs
  set Bd := hBd s.re α β
  have hbL : ∀ v, 0 < v → ‖lowF s Y v‖ ≤ v ^ s.re := fun v hv => by
    have := norm_lowF_le s Y hv
    rwa [one_mul] at this
  have hbB : ∀ v, 0 < v → ‖bandF s Y H v‖ ≤ v ^ s.re := fun v hv => by
    unfold bandF
    split_ifs
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
    · rw [norm_zero]
      exact Real.rpow_nonneg hv.le _
  have hbE : ∀ v, 0 < v → ‖((v : ℝ) : ℂ) ^ s‖ ≤ v ^ s.re := fun v hv => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have bL : ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → ‖eisLow s Y p‖ ≤ Bd :=
    fun p h1 h2 => norm_pseis_le_hBd hσ hbL hα h1 h2.1 h2.2
  have bB : ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → ‖pseis (bandF s Y H) p‖ ≤ Bd :=
    fun p h1 h2 => norm_pseis_le_hBd hσ hbB hα h1 h2.1 h2.2
  have bE : ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → ‖eis1 s p‖ ≤ Bd :=
    fun p h1 h2 => by rw [eis1_eq_pseis]; exact norm_pseis_le_hBd hσ hbE hα h1 h2.1 h2.2
  rw [uL_eq_eisLow hR hY hs him,
    inner_toLp_pmSer hψ hψ2 (isAut_eisLow s Y) (measurable_eisLow s Y) (memLp_eisLow hs hY.le)
      (lintegral_rhoT3_pm_ne_top m hM hψ0 hα bL),
    bandL, inner_toLp_pmSer hψ hψ2 (isAut_pseis _) (measurable_pseis (measurable_bandF s Y H))
      (memLp_pseis_bandF s hY (le_band hα hαβ)) (lintegral_rhoT3_pm_ne_top m hM hψ0 hα bB)]
  -- the character
  have hme : Measurable fun p : ℂ × ℝ => conj (ebr (σO m * p.1 / 9)) :=
    Complex.continuous_conj.measurable.comp
      (measurable_ebr.comp ((measurable_const.mul measurable_fst).div_const 9))
  set FE : ℂ × ℝ → ℂ := fun p => conj (ebr (σO m * p.1 / 9)) * eis1 s p with hFE
  set FB : ℂ × ℝ → ℂ := fun p => conj (ebr (σO m * p.1 / 9)) * pseis (bandF s Y H) p with hFB
  have hE1m : Measurable (eis1 s) := by
    rw [eis1_eq_pseis]
    exact measurable_pseis (Complex.measurable_ofReal.pow_const s)
  have hFEm : Measurable FE := hme.mul hE1m
  have hFBm : Measurable FB := hme.mul (measurable_pseis (measurable_bandF s Y H))
  have bFE : ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → ‖FE p‖ ≤ Bd := fun p h1 h2 => by
    simp only [hFE]
    rw [norm_mul, Complex.norm_conj, norm_ebr, one_mul]
    exact bE p h1 h2
  have bFB : ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → ‖FB p‖ ≤ Bd := fun p h1 h2 => by
    simp only [hFB]
    rw [norm_mul, Complex.norm_conj, norm_ebr, one_mul]
    exact bB p h1 h2
  have h1 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO m * p.1 / 9)) * eisLow s Y p ∂uhsMeasure =
      ∫ p in Prod.fst ⁻¹' fundP3, (conj (ψ p.2) * FE p - conj (ψ p.2) * FB p) ∂uhsMeasure := by
    refine setIntegral_congr_fun (measurableSet_fundP3.preimage measurable_fst) fun p _ => ?_
    simp only [hFE, hFB]
    by_cases hv : p.2 ∈ Icc α β
    · rw [eisLow_eq_band hs hY hα hv.1 hv.2, map_mul]
      ring
    · simp [hψ0 _ hv]
  have h2 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO m * p.1 / 9)) *
      pseis (bandF s Y H) p ∂uhsMeasure =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * FB p ∂uhsMeasure := by
    refine setIntegral_congr_fun (measurableSet_fundP3.preimage measurable_fst) fun p _ => ?_
    simp only [hFB]
    rw [map_mul]
    ring
  rw [h1, h2, integral_sub (integrableOn_fundP3_of_bdd hψ hM hψ0 hα hFEm bFE)
      (integrableOn_fundP3_of_bdd hψ hM hψ0 hα hFBm bFB),
    integral_fundP3_conj_mul hψ hM hψ0 hα hFEm bFE]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [hFE]
  congr 1
  refine setIntegral_congr_fun measurableSet_fundP3 fun z _ => ?_
  rw [conj_ebr, hm]
  congr 2
  ring

/-! ### The Bessel form -/

/-- **Integrable on `(0, ∞)`**: `conj ψ(v)·g(v)` for `ψ` measurable and bounded, vanishing outside `[α, β]`
with `α > 0`, and `g` continuous on `(0, ∞)`. -/
theorem integrableOn_Ioi_conj_mul {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0)) :
    IntegrableOn (fun v => conj (ψ v) * g v) (Ioi 0) := by
  have hsub : Icc α β ⊆ Ioi 0 := fun v hv => lt_of_lt_of_le hα hv.1
  have hgc : ContinuousOn g (Icc α β) := hg.mono hsub
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  have h1 : IntegrableOn (fun v => conj (ψ v) * g v) (Icc α β) := by
    refine Integrable.mono' (integrable_const (M * B))
      ((Complex.continuous_conj.measurable.comp hψ).aestronglyMeasurable.mul
        (hgc.aestronglyMeasurable measurableSet_Icc)) ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun v hv => ?_
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hM _) (hB v hv) (norm_nonneg _) hM0
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun v hv => ?_
  rw [hψ0 _ hv.2, map_zero, zero_mul]

/-- `J_ψ(s) = ∫_0^∞ conj ψ(v)·v^{−2}·K_{s−1}(a·v) dv`. -/
def jPsi (a : ℝ) (ψ : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ v in Ioi 0, conj (ψ v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (s - 1) (a * v))

/-- `v ↦ v^{−2}·K_ν(a·v)` is continuous on `(0, ∞)` for `a > 0` (round 373's `continuousAt_besselK`). -/
theorem continuousOn_zpow_besselK (ν : ℂ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun v : ℝ => ((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK ν (a * v)) (Ioi 0) := by
  intro v hv
  have hv' : (0 : ℝ) < v := hv
  have h1 : ContinuousAt (fun v : ℝ => ((v ^ (-2 : ℤ) : ℝ) : ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_zpow₀ v (-2) (Or.inl hv'.ne'))
  have h2 : ContinuousAt (fun v : ℝ => besselK ν (a * v)) v :=
    (continuousAt_besselK ν (mul_pos ha hv')).comp (continuousAt_const.mul continuousAt_id)
  exact (h1.mul h2).continuousWithinAt

/-- **The Bessel form of the pairing**: for `m = δ₃x` with `x ≠ 0`, `R ≥ 0`, `Y > 0`, `ψ` measurable and
bounded, vanishing outside `[α, β]` with `0 < α ≤ β`, `Re s > 2` and `Im ĥ(s) ≠ 0`,
`⟨P_m(ψ), ũ_s⟩ = (2π/Γ(s))(2π|m|/9)^{s−1}·D_m(s)·J_ψ(s) + I_m·M_ψ(2 − s) − ⟨P_m(ψ), E(1[Y ≤ v ≤ H]v^s)⟩` with
`J_ψ = jPsi (4π|m|/9) ψ`, `D_m(s)` round 428's Dirichlet series, `H = Y + β + 1/α`, `I_m = ∫_{3P} ĕ(−mz/9) dz`
and round 427's `M_ψ`. -/
theorem inner_pmSer_uL_bessel {x : 𝓞 K} (hx : x ≠ 0) {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y)
    {ψ : ℝ → ℂ} (hψ : Measurable ψ) (hψ2 : MemLp (pmSer (δ3 * x) ψ) 2 (muR rhoG)) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) {s : ℂ}
    (hs : 2 < s.re) (him : (hhat R s).im ≠ 0) :
    inner ℂ (hψ2.toLp (pmSer (δ3 * x) ψ)) (uL R hR Y hY s) =
      2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO (δ3 * x) / 9‖ : ℝ) : ℂ) ^ (s - 1) *
          (∑' c : 𝓞 K, cuspSm (δ3 * x) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)) *
          jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ψ s +
        (∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z))) * mellinPsi ψ (2 - s) -
        inner ℂ (hψ2.toLp (pmSer (δ3 * x) ψ)) (bandL hY (le_band hα hαβ) s) := by
  have hξ : σO (δ3 * x) / 9 ≠ 0 :=
    div_ne_zero (σO_ne_zero (mul_ne_zero δ3_ne_zero hx)) (by norm_num)
  have ha : 0 < 4 * Real.pi * ‖σO (δ3 * x) / 9‖ := by
    have := norm_pos_iff.2 hξ
    positivity
  have hcont1 : ContinuousOn (fun v : ℝ => ((v : ℝ) : ℂ) ^ (-1 - (2 - s))) (Ioi 0) := fun v hv =>
    (continuousAt_ofReal_cpow_const v _ (Or.inr (show (0 : ℝ) < v from hv).ne')).continuousWithinAt
  have hi1 := integrableOn_Ioi_conj_mul hψ hM hψ0 hα hcont1
  have hi2 := integrableOn_Ioi_conj_mul hψ hM hψ0 hα (continuousOn_zpow_besselK (s - 1) ha)
  rw [inner_pmSer_uL x hR hY hψ hψ2 hM hψ0 hα hαβ hs him]
  congr 1
  have he : ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) *
      ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * eis1 s (z, v) =
      ∫ v in Ioi 0, ((∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z))) *
          (conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - (2 - s))) +
        2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO (δ3 * x) / 9‖ : ℝ) : ℂ) ^ (s - 1) *
          (∑' c : 𝓞 K, cuspSm (δ3 * x) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)) *
          (conj (ψ v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) *
            besselK (s - 1) (4 * Real.pi * ‖σO (δ3 * x) / 9‖ * v)))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    rw [integral_ebr_eis1_fundP3 hx hs hv']
    have e1 : ((v ^ (-3 : ℤ) : ℝ) : ℂ) * ((v : ℝ) : ℂ) ^ s = ((v : ℝ) : ℂ) ^ (-1 - (2 - s)) := by
      have := cpow_neg_one_sub hv' (2 - s)
      rwa [sub_sub_cancel] at this
    have e2 : ((v ^ (-3 : ℤ) : ℝ) : ℂ) * ((v : ℝ) : ℂ) = ((v ^ (-2 : ℤ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [show (-2 : ℤ) = -3 + 1 by norm_num, zpow_add₀ hv'.ne', zpow_one]
    rw [← e1, ← e2]
    ring
  rw [he, integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul]
  unfold jPsi mellinPsi
  ring

end Eis

end

#print axioms Eis.measurable_bandF
#print axioms Eis.measurable_bandD
#print axioms Eis.bandF_eq_zero_of_lt
#print axioms Eis.bandD_eq_zero_of_lt
#print axioms Eis.norm_bandF_le
#print axioms Eis.norm_bandD_le
#print axioms Eis.bandF_taylor
#print axioms Eis.memLp_pseis_bandF
#print axioms Eis.memLp_pseis_bandD
#print axioms Eis.hasDerivAt_bandL
#print axioms Eis.differentiable_bandL
#print axioms Eis.differentiable_inner_bandL
#print axioms Eis.norm_le_six_of_mem_fundP3
#print axioms Eis.tsum_height_rpow_le_unif
#print axioms Eis.norm_pseis_le_hBd
#print axioms Eis.zpow_neg_three_le
#print axioms Eis.uhsMeasure_fundP3_Icc_lt_top_of_pos
#print axioms Eis.integrableOn_fundP3_of_bdd
#print axioms Eis.integral_fundP3_conj_mul
#print axioms Eis.lintegral_rhoT3_pm_ne_top
#print axioms Eis.le_band
#print axioms Eis.height_le_band
#print axioms Eis.eisHigh_eq_band
#print axioms Eis.eisLow_eq_band
#print axioms Eis.inner_pmSer_uL
#print axioms Eis.integrableOn_Ioi_conj_mul
#print axioms Eis.continuousOn_zpow_besselK
#print axioms Eis.inner_pmSer_uL_bessel
