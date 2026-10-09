import Mathlib
import ChiGround
import FirstFailure

/-! # Continuity and the first positivity failure for every u-space form (round 331)

FirstFailure.lean (round 161) proves for `ζ` that if Weil positivity ever fails, it fails *first* at a
definite support `a₁`. Its inputs are `λ₁ > 0` at small support (round 121, SmallPositivity.lean),
continuity of `λ₁` (round 148, SimpleCont.lean) and monotonicity (round 47, `lam_antitone`). Here
the three are proved for every u-space form `UData` (ChiGround.lean, round 330), and the
structure theorem follows for each.

* **Continuity** (`UData.continuousOn_lam`). Right-continuity by compactness and lower
  semicontinuity along shrinking supports (`UData.lsc`, `UData.lam_right`), as in SimpleCont.lean;
  left-continuity by dilation (`UData.lam_left`, through ParityCont's `left_cont_of_dil`), with the
  `q`-energy continuous under dilation for every `q ≥ ¼` (`tendsto_archEQ_dil`). Monotonicity:
  `UData.lam_antitone`.
* **Positivity at small support** (`UData.lam_pos_small`): `λ ≥ log 2 − ¼` on some `(0, a₀]`. Below
  `log 2` only `n = 1` enters the prime sum (`UData.Q_eq_small`), and
  `E_q(g) ≥ ∫_{u>2a} K_q ≥ log 2 − log a − a − 4` (`archEQ_ge_far`, `farQ_ge`: SmallPositivity's closed
  form `farField_eq` for `K`, and `K − K_q ≤ 2e^{−u/2}` for `q ≤ ¾`). `a₀` depends on `c − 2f(1)`.
* **The first failure** (`UData.first_failure`): if `λ < 0` at some support, there is a first support
  `a₁` with `λ > 0` before it, `λ(a₁) = 0` and `λ ≤ 0` after it; `Q ≥ 0` on every probe at `a₁`; and a
  ground state `g*` at `a₁` with `Q(g*) = 0` and `B(g*, ψ) = 0` for every probe `ψ`.
* **The χ column**: `continuousOn_lamC`, `lamC_pos_small` and `first_failureC`, the first failure of
  `Q_χ` when GRH fails for a good character with no real zero in `(0, 1)`.
* **The Davenport–Heilbronn instance** (`first_failureDH`, `continuousOn_lamDH`). `λ_dh < 0` from
  `12/5` on (`lamDH_neg`), so the first failure of `Q_dh` exists, at some `a₁ ≤ 12/5`, with no
  hypothesis.

For `χ` the first failure is a reformulation of `¬GRH(χ)`, as FirstFailure.lean's is of `¬RH`: GRH(χ)
follows from ruling out a normalised probe `g*` that is a zero of a positive semidefinite `Q_χ` and
lies in the kernel of its bilinear form. For `dh` such a `g*` exists (`first_failureDH`).
-/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## Dilation of the `q`-energy -/

/-- `G^q_s(v) = (f(0) − f(v))·K_q(v/s)`, so that `A_q(o_s)(u) = G^q_s(su)`. -/
def GsQ (q : ℝ) (o : ℝ → ℝ) (s v : ℝ) : ℝ := (autocorr o 0 - autocorr o v) * archKer q (v / s)

theorem archIntegrandQ_dil (q : ℝ) {s : ℝ} (hs : 0 < s) (o : ℝ → ℝ) (u : ℝ) :
    archIntegrandQ q (dil s o) u = GsQ q o s (s * u) := by
  unfold archIntegrandQ GsQ
  rw [autocorr_dil hs, autocorr_dil hs, mul_zero, mul_div_cancel_left₀ _ hs.ne']

/-- `K_q ≤ K` for `q ≥ ¼`. -/
theorem archKer_le_kerK {q : ℝ} (hq : 1 / 4 ≤ q) {u : ℝ} (hu : 0 < u) : archKer q u ≤ kerK u := by
  unfold archKer kerK
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) (Real.sinh_pos_iff.2 hu).le

theorem GsQ_nonneg (q : ℝ) {o : ℝ → ℝ} (ho : MemLp o 2 volume) {s v : ℝ} (hs : 0 < s) (hv : 0 < v) :
    0 ≤ GsQ q o s v :=
  mul_nonneg (autocorr_sub_nonneg ho v) (archKer_pos q (div_pos hv hs)).le

theorem GsQ_le_Gs {q : ℝ} (hq : 1 / 4 ≤ q) {o : ℝ → ℝ} (ho : MemLp o 2 volume) {s v : ℝ} (hs : 0 < s)
    (hv : 0 < v) : GsQ q o s v ≤ Gs o s v :=
  mul_le_mul_of_nonneg_left (archKer_le_kerK hq (div_pos hv hs)) (autocorr_sub_nonneg ho v)

theorem measurable_GsQ (q : ℝ) {o : ℝ → ℝ} (ho : MemLp o 2 volume) (s : ℝ) : Measurable (GsQ q o s) := by
  have hK : Measurable (archKer q) := by unfold archKer; fun_prop
  unfold GsQ
  exact (measurable_const.sub (continuous_autocorr ho).measurable).mul
    (hK.comp (measurable_id.div_const s))

theorem archEQ_dil (q : ℝ) {o : ℝ → ℝ} {s : ℝ} (hs : 0 < s) :
    archEQ q (dil s o) = s⁻¹ * ∫ v in Ioi 0, GsQ q o s v := by
  unfold archEQ
  simp_rw [archIntegrandQ_dil q hs o]
  rw [integral_comp_mul_left_Ioi (GsQ q o s) 0 hs, mul_zero, smul_eq_mul]

/-- **The `q`-energy is continuous under dilation** at `s = 1⁺` (ParityCont's `tendsto_archE_dilS`
for `K_q`, `q ≥ ¼`, dominated by the same `D`). -/
theorem tendsto_archEQ_dil {q : ℝ} (hq : 1 / 4 ≤ q) {a : ℝ} {o : ℝ → ℝ} (hp : Probe a o) :
    Tendsto (fun s => archEQ q (dil s o)) (𝓝[Icc 1 2] 1) (𝓝 (archEQ q o)) := by
  have hev : ∀ᶠ s in 𝓝[Icc 1 2] (1 : ℝ), s ∈ Icc (1 : ℝ) 2 := self_mem_nhdsWithin
  have hI : Tendsto (fun s => ∫ v in Ioi 0, GsQ q o s v) (𝓝[Icc 1 2] 1)
      (𝓝 (∫ v in Ioi 0, GsQ q o 1 v)) := by
    refine tendsto_integral_filter_of_dominated_convergence (domD o)
      (Eventually.of_forall fun s => (measurable_GsQ q hp.memL2 s).aestronglyMeasurable)
      (hev.mono fun s hs => (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_))
      (integrableOn_domD hp.toS)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_))
    · have hs0 : 0 < s := by linarith [hs.1]
      rw [Real.norm_eq_abs, abs_of_nonneg (GsQ_nonneg q hp.memL2 hs0 hv)]
      exact (GsQ_le_Gs hq hp.memL2 hs0 hv).trans (Gs_le_domD hp.memL2 hs.1 hs.2 hv)
    · have hv0 : (0 : ℝ) < v := hv
      have hc : ContinuousAt (fun s => GsQ q o s v) 1 := by
        unfold GsQ archKer
        refine continuousAt_const.mul (ContinuousAt.div
          (Real.continuous_exp.continuousAt.comp
            (continuousAt_const.mul (continuousAt_const.div continuousAt_id one_ne_zero))) ?_ ?_)
        · exact (Real.continuous_sinh.continuousAt).comp
            (continuousAt_const.div continuousAt_id one_ne_zero)
        · simp only [div_one]; exact (Real.sinh_pos_iff.2 hv0).ne'
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hGs1 : (∫ v in Ioi 0, GsQ q o 1 v) = archEQ q o := by
    unfold archEQ GsQ archIntegrandQ; simp only [div_one]
  have hinv : Tendsto (fun s : ℝ => s⁻¹) (𝓝[Icc 1 2] 1) (𝓝 1) := by
    have := (tendsto_inv₀ (one_ne_zero' ℝ)).mono_left (nhdsWithin_le_nhds (s := Icc (1 : ℝ) 2))
    rw [inv_one] at this; exact this
  have := hinv.mul hI
  rw [one_mul, hGs1] at this
  refine this.congr' (hev.mono fun s hs => ?_)
  dsimp only
  rw [archEQ_dil q (by linarith [hs.1])]

/-- Dilation maps probes at support `a` to probes at support `a/s`, for `1 ≤ s ≤ 2`. -/
theorem probe_dilS {a : ℝ} {o : ℝ → ℝ} (hp : Probe a o) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    Probe (a / s) (dil s o) :=
  ⟨fun u => by unfold dil; rw [show s * -u = -(s * u) by ring, hp.even],
    dil_supp (by linarith) hp.supp, memLp_dilS (by linarith) hp.memL2, arch_dil hp.toS hs1 hs2⟩

/-! ## The far field of `K_q` -/

/-- `K − 2e^{−u/2} ≤ K_q` for `q ≤ ¾` (`K − K_{3/4} = sech(u/2)`). -/
theorem kerK_sub_le_archKer {q : ℝ} (hq : q ≤ 3 / 4) {u : ℝ} (hu : 0 < u) :
    kerK u - 2 * Real.exp (-(u / 2)) ≤ archKer q u := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
  have h1 : archKer (3 / 4) u ≤ archKer q u := by
    unfold archKer
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hs.le
  have h2 : kerK u - 2 * Real.exp (-(u / 2)) ≤ archKer (3 / 4) u := by
    unfold kerK archKer
    rw [show (1 - 2 * (3 / 4 : ℝ)) * u = -(u / 2) by ring, sub_le_iff_le_add, div_le_iff₀ hs,
      add_mul, div_mul_cancel₀ _ hs.ne', Real.sinh_eq]
    have e1 : Real.exp (-(u / 2)) * Real.exp u = Real.exp (u / 2) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(u / 2)) * Real.exp (-u) = Real.exp (-(3 * u / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp (-(3 * u / 2)) ≤ Real.exp (-(u / 2)) := Real.exp_le_exp.2 (by linarith)
    nlinarith [e1, e2, e3]
  linarith

theorem integrableOn_kerK_Ioi {c : ℝ} (hc : 0 < c) : IntegrableOn kerK (Ioi c) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun _ hx => hasDerivAt_farPrim (lt_of_lt_of_le hc hx))
    (fun _ hx => (kerK_pos (lt_trans hc hx)).le) tendsto_farPrim

/-- **`∫_{u > 2a} K ≥ log 2 − log a − a`**, from SmallPositivity's closed form (`farField_eq`). -/
theorem farField_ge_log {a : ℝ} (ha : 0 < a) :
    Real.log 2 - Real.log a - a ≤ ∫ u in Ioi (2 * a), kerK u := by
  rw [farField_eq ha]
  have hE : 1 < Real.exp a := Real.one_lt_exp_iff.mpr ha
  have hEa : Real.exp a - 1 ≤ a * Real.exp a := by
    have h := Real.add_one_le_exp (-a)
    have : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos a, Real.exp_pos (-a)]
  have hratio : 2 / (a * Real.exp a) ≤ (Real.exp a + 1) / (Real.exp a - 1) := by
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [Real.exp_pos a]
  have hlogr : Real.log (2 / (a * Real.exp a)) ≤ Real.log ((Real.exp a + 1) / (Real.exp a - 1)) :=
    Real.log_le_log (by positivity) hratio
  have hneg : -Real.log ((Real.exp a - 1) / (Real.exp a + 1))
      = Real.log ((Real.exp a + 1) / (Real.exp a - 1)) := by
    rw [← Real.log_inv, inv_div]
  have hsplit : Real.log (2 / (a * Real.exp a)) = Real.log 2 - Real.log a - a := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_mul ha.ne' (Real.exp_pos a).ne',
      Real.log_exp]; ring
  have hat : Real.arctan (Real.sinh a) < π / 2 := Real.arctan_lt_pi_div_two _
  rw [hneg]
  linarith

/-- **The far field of `K_q`**: `∫_{u > 2a} K_q ≥ log 2 − log a − a − 4` for `¼ ≤ q ≤ ¾`. -/
theorem farQ_ge {q : ℝ} (hq1 : 1 / 4 ≤ q) (hq : q ≤ 3 / 4) {a : ℝ} (ha : 0 < a) :
    Real.log 2 - Real.log a - a - 4 ≤ ∫ u in Ioi (2 * a), archKer q u := by
  have h2a : 0 < 2 * a := by linarith
  have hK := integrableOn_kerK_Ioi h2a
  have e : (fun u : ℝ => 2 * Real.exp (-(u / 2))) = fun u => 2 * Real.exp (-(1 / 2) * u) := by
    funext u; congr 2; ring
  have hE : IntegrableOn (fun u : ℝ => 2 * Real.exp (-(u / 2))) (Ioi (2 * a)) := by
    rw [e]; exact (exp_neg_integrableOn_Ioi (2 * a) (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2
  have hKq : IntegrableOn (archKer q) (Ioi (2 * a)) := by
    refine hK.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
    · exact (by unfold archKer; fun_prop : Measurable (archKer q)).aestronglyMeasurable
    · have hu0 : 0 < u := lt_trans h2a hu
      rw [Real.norm_eq_abs, abs_of_pos (archKer_pos q hu0)]
      exact archKer_le_kerK hq1 hu0
  have hmono : ∫ u in Ioi (2 * a), (kerK u - 2 * Real.exp (-(u / 2)))
      ≤ ∫ u in Ioi (2 * a), archKer q u :=
    setIntegral_mono_on (hK.sub hE) hKq measurableSet_Ioi
      fun u hu => kerK_sub_le_archKer hq (lt_trans h2a hu)
  rw [integral_sub hK hE] at hmono
  have hEval : ∫ u in Ioi (2 * a), 2 * Real.exp (-(u / 2)) = 4 * Real.exp (-a) := by
    rw [e, integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0),
      show -(1 / 2 : ℝ) * (2 * a) = -a by ring]
    ring
  have hFar := farField_ge_log ha
  have hexp : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

/-- **`E_q(g) ≥ ∫_{u > 2a} K_q`** for a normalised probe at support `a`: past `2a` the autocorrelation
vanishes. -/
theorem archEQ_ge_far {q : ℝ} (hq : 1 / 4 ≤ q) {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) : ∫ u in Ioi (2 * a), archKer q u ≤ archEQ q g := by
  have hI := archIntegrandQ_integrable hp hq
  have h1 : ∫ u in Ioi (2 * a), archKer q u = ∫ u in Ioi (2 * a), archIntegrandQ q g u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : 2 * a < u := hu
    unfold archIntegrandQ
    rw [autocorr_zero, hn, autocorr_eq_zero hp.supp (by rw [abs_of_pos (by linarith)]; exact hu')]
    ring
  rw [h1]
  unfold archEQ
  exact setIntegral_mono_set hI
    ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun u hu => archIntegrandQ_nonneg q hp.memL2 hu))
    (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ 2 * a)).eventuallyLE

namespace UData

variable (U : UData) {a : ℝ} {g h : ℝ → ℝ}

theorem lam_nonempty (ha : 0 < a) : {x | ∃ h, Probe a h ∧ normSq h = 1 ∧ U.Q h = x}.Nonempty :=
  ⟨_, box a, box_probe a, normSq_box ha, rfl⟩

/-- **`λ` is non-increasing in the support.** -/
theorem lam_antitone {b : ℝ} (ha : 0 < a) (hab : a ≤ b) : U.lam b ≤ U.lam a := by
  show U.lam b ≤ sInf {x | ∃ h, Probe a h ∧ normSq h = 1 ∧ U.Q h = x}
  refine le_csInf (U.lam_nonempty ha) ?_
  rintro x ⟨g, hp, hn, rfl⟩
  exact U.lam_le (hp.mono hab) hn

/-! ### Right-continuity: compactness -/

/-- **Lower semicontinuity along shrinking supports** (SimpleCont's `lsc_even` for `Q`): normalised
probes at supports `b_n ↓ a` whose energies converge to `L` give a normalised probe at `a` with
`Q ≤ L`. -/
theorem lsc (ha : 0 < a) {a₁ : ℝ} {b : ℕ → ℝ} (hb : ∀ n, a ≤ b n) (hb1 : ∀ n, b n ≤ a₁)
    (hbt : Tendsto b atTop (𝓝 a)) {h : ℕ → ℝ → ℝ} (hp : ∀ n, Probe (b n) (h n))
    (hn : ∀ n, normSq (h n) = 1) {L : ℝ} (hq : Tendsto (fun n => U.Q (h n)) atTop (𝓝 L)) :
    ∃ G, Probe a G ∧ normSq G = 1 ∧ U.Q G ≤ L := by
  have ha₁ : 0 < a₁ := ha.trans_le ((hb 0).trans (hb1 0))
  have hp1 : ∀ n, Probe a₁ (h n) := fun n => (hp n).mono (hb1 n)
  obtain ⟨M, hM⟩ := hq.bddAbove_range
  have hQM : ∀ n, U.Q (h n) ≤ M := fun n => hM ⟨n, rfl⟩
  -- the `q`-energies are bounded above, and so are the energies `E`
  have hC3 : ∀ n, archEQ U.q (h n) ≤ M + U.M a₁ := by
    intro n
    have e := U.Q_eq_nonArch (hp1 n).supp
    have := U.nonArch_ge (hp1 n) (hn n)
    linarith [hQM n]
  have hC : ∀ n, archE (h n) ≤ Real.exp (2 * a₁) * (M + U.M a₁) + tailDH a₁ := by
    intro n
    have h1 := U.archE_le ha₁ (hp1 n)
    rw [hn n, one_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left (hC3 n) (Real.exp_pos (2 * a₁)).le
    linarith
  obtain ⟨φ, hφ, G, hG, hlim⟩ := exists_convergent_subseq ha₁ hp1 (B := 1) (fun n => (hn n).le) hC
  set G' := symCut a G with hG'def
  have hG' : MemLp G' 2 volume := memLp_symCut a hG
  have hmem : ∀ j, MemLp (h (φ j)) 2 volume := fun j => (hp (φ j)).memL2
  -- cut to `[−a, a]`: the shell estimate
  have hlim' : Tendsto (fun j => normSq (fun t => h (φ j) t - G' t)) atTop (𝓝 0) := by
    have hsh := tendsto_shellSq hG (hbt.comp hφ.tendsto_atTop)
    have hup : Tendsto (fun j => 6 * normSq (fun t => h (φ j) t - G t) + 4 * shellSq G a (b (φ j)))
        atTop (𝓝 0) := by
      have := (hlim.const_mul 6).add (hsh.const_mul 4)
      rw [mul_zero, mul_zero, add_zero] at this
      exact this
    exact squeeze_zero (fun j => integral_nonneg fun t => sq_nonneg _)
      (fun j => normSq_sub_symCut_shell (hp (φ j)) hG) hup
  have hnorm : Tendsto (fun j => normSq (h (φ j))) atTop (𝓝 (normSq G')) := by
    simp_rw [normSq_eq_mul]
    exact tendsto_integral_mul hmem hmem hG' hG' hlim' hlim'
  have hnormG : normSq G' = 1 :=
    tendsto_nhds_unique hnorm (tendsto_const_nhds.congr fun j => (hn (φ j)).symm)
  have hauto : ∀ u, Tendsto (fun j => autocorr (h (φ j)) u) atTop (𝓝 (autocorr G' u)) := by
    intro u
    have hsh : ∀ j, normSq (fun t => h (φ j) (t + u) - G' (t + u))
        = normSq (fun t => h (φ j) t - G' t) :=
      fun j => normSq_shift (fun t => h (φ j) t - G' t) u
    unfold autocorr
    exact tendsto_integral_mul hmem (fun j => memLp_shift (hmem j) u) hG' (memLp_shift hG' u)
      hlim' (hlim'.congr fun j => (hsh j).symm)
  have hsuppG' : ∀ u, a < |u| → G' u = 0 := symCut_supp a G
  have haa₁ : a ≤ a₁ := (hb 0).trans (hb1 0)
  have hsuppG1 : ∀ u, a₁ < |u| → G' u = 0 := fun u hu => hsuppG' u (by linarith)
  have hnonArch : Tendsto (fun j => U.nonArch a₁ (h (φ j))) atTop (𝓝 (U.nonArch a₁ G')) := by
    unfold UData.nonArch
    exact (hnorm.const_mul _).sub
      ((tendsto_finsetSum _ fun n _ => (hauto _).const_mul _).const_mul 2)
  have hA : Tendsto (fun j => archEQ U.q (h (φ j))) atTop (𝓝 (L - U.nonArch a₁ G')) := by
    have e : ∀ j, archEQ U.q (h (φ j)) = U.Q (h (φ j)) - U.nonArch a₁ (h (φ j)) := by
      intro j; rw [U.Q_eq_nonArch (hp1 (φ j)).supp]; ring
    simp_rw [e]
    exact (hq.comp hφ.tendsto_atTop).sub hnonArch
  -- Fatou on the `q`-integrand
  obtain ⟨hint, hle⟩ := fatou_real measurableSet_Ioi
    (f := fun j => archIntegrandQ U.q (h (φ j))) (F := archIntegrandQ U.q G')
    (fun j => archIntegrandQ_integrable (hp (φ j)) U.quarter_le)
    (fun j u hu => archIntegrandQ_nonneg U.q (hmem j) hu)
    (fun u _ => by
      unfold archIntegrandQ
      exact ((hauto 0).sub (hauto u)).mul_const _) hA
  have hPG : Probe a G' := ⟨symCut_even a G, hsuppG', hG', U.arch_of_archQU ha hsuppG' hG' hint⟩
  refine ⟨G', hPG, hnormG, ?_⟩
  rw [U.Q_eq_nonArch hsuppG1]
  unfold archEQ
  linarith

/-- **Right-continuity of `λ`.** -/
theorem lam_right (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b, a ≤ b → b < a + δ → U.lam a - ε < U.lam b := by
  by_contra H
  push Not at H
  choose b hab hbδ hbl using fun n : ℕ => H (1 / ((n : ℝ) + 1)) (by positivity)
  set a₁ := a + 1 with ha₁
  have hb1 : ∀ n, b n ≤ a₁ := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith [hbδ n]
  have hb0 : ∀ n, 0 < b n := fun n => ha.trans_le (hab n)
  have hbt : Tendsto b atTop (𝓝 a) := by
    have hu : Tendsto (fun n : ℕ => a + 1 / ((n : ℝ) + 1)) atTop (𝓝 a) := by
      have := (tendsto_const_nhds (x := a)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu hab fun n => (hbδ n).le
  have hnear : ∀ n, ∃ g, Probe (b n) g ∧ normSq g = 1 ∧ U.Q g < U.lam (b n) + ε / 2 := by
    intro n
    obtain ⟨x, ⟨g, hp, hn, rfl⟩, hx⟩ :=
      exists_lt_of_csInf_lt (U.lam_nonempty (hb0 n)) (by linarith : U.lam (b n) < U.lam (b n) + ε / 2)
    exact ⟨g, hp, hn, hx⟩
  choose g hgp hgn hgq using hnear
  have hqI : ∀ n, U.Q (g n) ∈ Icc (-U.M a₁) (U.lam a - ε / 2) := fun n =>
    ⟨by have := U.Q_ge ((hgp n).mono (hb1 n)); rwa [hgn n, mul_one] at this,
      by linarith [hgq n, hbl n]⟩
  obtain ⟨L, hLI, φ, hφ, hqφ⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_Icc (-U.M a₁) (U.lam a - ε / 2)) hqI
  rw [closure_Icc] at hLI
  obtain ⟨G, hPG, hnG, hQG⟩ := U.lsc ha (fun n => hab (φ n)) (fun n => hb1 (φ n))
    (hbt.comp hφ.tendsto_atTop) (fun n => hgp (φ n)) (fun n => hgn (φ n)) hqφ
  have := U.lam_le hPG hnG
  linarith [hLI.2]

/-! ### Left-continuity: dilation -/

/-- **`Q` is continuous under dilation** at `s = 1⁺`. -/
theorem tendsto_Q_dil (ha : 0 < a) {o : ℝ → ℝ} (hp : Probe a o) :
    Tendsto (fun s => U.Q (dil s o)) (𝓝[Icc 1 2] 1) (𝓝 (U.Q o)) := by
  have hev : ∀ᶠ s in 𝓝[Icc 1 2] (1 : ℝ), s ∈ Icc (1 : ℝ) 2 := self_mem_nhdsWithin
  have hc : Continuous fun s : ℝ => ∑ n ∈ Finset.range (primeCut a),
      U.f n / Real.sqrt n * autocorr o (s * Real.log n) :=
    continuous_finsetSum _ fun n _ => continuous_const.mul
      ((continuous_autocorr hp.memL2).comp (continuous_id.mul continuous_const))
  have h1 := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Icc (1 : ℝ) 2))
  simp only [one_mul] at h1
  have hlim := ((tendsto_const_nhds (x := U.c * normSq o)).add
    (tendsto_archEQ_dil U.quarter_le hp)).sub (h1.const_mul 2)
  rw [U.Q_eq_range hp.supp]
  refine hlim.congr' (hev.mono fun s hs => ?_)
  have hs0 : 0 < s := by linarith [hs.1]
  dsimp only
  rw [U.Q_eq_range (a := a) (fun u hu => dil_supp hs0 hp.supp u
    (lt_of_le_of_lt (div_le_self ha.le hs.1) hu)), normSq_dilS hs0]
  simp_rw [autocorr_dil hs0]

/-- **Left-continuity of `λ`** (dilation). -/
theorem lam_left (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b, a - δ < b → b ≤ a → U.lam b < U.lam a + ε := by
  obtain ⟨x, ⟨o, hp, hn, rfl⟩, hx⟩ :=
    exists_lt_of_csInf_lt (U.lam_nonempty ha) (by linarith : U.lam a < U.lam a + ε / 2)
  exact left_cont_of_dil (Pr := Probe) (Q := fun _ => U.Q) ha hε hn hx (U.tendsto_Q_dil ha hp)
    (fun s h1 h2 => probe_dilS hp h1 h2) (fun _ _ _ _ _ => rfl) (fun b g _ hg hgn => U.lam_le hg hgn)

/-- **`λ` is continuous on `(0, ∞)`.** -/
theorem continuousOn_lam : ContinuousOn U.lam (Ioi 0) :=
  continuousOn_of_right_left (fun _ ha _ hε => U.lam_right ha hε) (fun _ ha _ hε => U.lam_left ha hε)
    (fun _ _ ha hab => U.lam_antitone ha hab)

/-! ### Positivity at small support -/

theorem le_three_quarters : U.q ≤ 3 / 4 := by
  rcases U.hq with h | h
  · rw [h]; norm_num
  · rw [h]

/-- Below `log 2` only `n = 1` enters the prime sum: `Q(g) = (c − 2f(1))‖g‖² + E_q(g)`. -/
theorem Q_eq_small (h2a : 2 * a < Real.log 2) (hp : Probe a g) :
    U.Q g = (U.c - 2 * U.f 1) * normSq g + archEQ U.q g := by
  have hS : ∑' n : ℕ, U.f n / Real.sqrt n * autocorr g (Real.log n) = U.f 1 * normSq g := by
    rw [tsum_eq_single 1]
    · simp [autocorr_zero]
    · intro n hn
      rcases lt_or_ge n 2 with h | h
      · interval_cases n <;> simp_all
      · have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h)
        have hpos : 0 < Real.log n := lt_of_lt_of_le (Real.log_pos (by norm_num)) hl
        rw [autocorr_eq_zero hp.supp (by rw [abs_of_pos hpos]; linarith), mul_zero]
  unfold UData.Q; rw [hS]; ring

/-- **`Q(g) ≥ c − 2f(1) + log 2 − log a − a − 4`** on normalised probes at support `a`, `2a < log 2`. -/
theorem Q_ge_small (ha : 0 < a) (h2a : 2 * a < Real.log 2) (hp : Probe a g) (hn : normSq g = 1) :
    U.c - 2 * U.f 1 + (Real.log 2 - Real.log a - a - 4) ≤ U.Q g := by
  rw [U.Q_eq_small h2a hp, hn, mul_one]
  have h1 := archEQ_ge_far U.quarter_le ha.le hp hn
  have h2 := farQ_ge U.quarter_le U.le_three_quarters ha
  linarith

/-- **`λ ≥ log 2 − ¼` at small support**, for every u-space form. -/
theorem lam_pos_small : ∃ a₀, 0 < a₀ ∧ ∀ a, 0 < a → a ≤ a₀ → Real.log 2 - 1 / 4 ≤ U.lam a := by
  set C := |U.c - 2 * U.f 1| + 4 with hC
  refine ⟨min (1 / 4) (Real.exp (-C)), lt_min (by norm_num) (Real.exp_pos _), fun a ha ha₀ => ?_⟩
  have ha4 : a ≤ 1 / 4 := ha₀.trans (min_le_left _ _)
  have hlog : Real.log a ≤ -C := by
    have := Real.log_le_log ha (ha₀.trans (min_le_right _ _))
    rwa [Real.log_exp] at this
  have h2a : 2 * a < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this; linarith
  show Real.log 2 - 1 / 4 ≤ sInf {x | ∃ h, Probe a h ∧ normSq h = 1 ∧ U.Q h = x}
  refine le_csInf (U.lam_nonempty ha) ?_
  rintro x ⟨g, hp, hn, rfl⟩
  have := U.Q_ge_small ha h2a hp hn
  have := neg_abs_le (U.c - 2 * U.f 1)
  linarith

/-! ### The first positivity failure -/

/-- **The first positivity failure for a u-space form** (FirstFailure.lean's `first_failure`). If
`λ < 0` at some support, there is a first support `a₁` at which positivity is lost: `λ > 0` before
it, `λ(a₁) = 0`, `λ ≤ 0` after it and `< 0` somewhere; `Q ≥ 0` on every probe at `a₁`; and a ground
state `g*` at `a₁` with `Q(g*) = 0` and `B(g*, ψ) = 0` for every probe `ψ`. -/
theorem first_failure (hneg : ∃ a, 0 < a ∧ U.lam a < 0) :
    ∃ a₁, 0 < a₁ ∧ (∀ a, 0 < a → a < a₁ → 0 < U.lam a) ∧ U.lam a₁ = 0 ∧
      (∀ a, a₁ ≤ a → U.lam a ≤ 0) ∧ (∃ a₀, a₁ ≤ a₀ ∧ U.lam a₀ < 0) ∧
      (∀ ψ, Probe a₁ ψ → 0 ≤ U.Q ψ) ∧
      ∃ g, U.IsGroundState a₁ g ∧ U.Q g = 0 ∧ ∀ ψ, Probe a₁ ψ → U.bil a₁ g ψ = 0 := by
  obtain ⟨a₀, ha₀, hl₀⟩ := hneg
  obtain ⟨as, has, hsmall⟩ := U.lam_pos_small
  have hl2 : (0 : ℝ) < Real.log 2 - 1 / 4 := by
    have := Real.log_two_gt_d9; norm_num at this; linarith
  set T : Set ℝ := {a | 0 < a ∧ U.lam a ≤ 0}
  have hT : T.Nonempty := ⟨a₀, ha₀, hl₀.le⟩
  have hTb : BddBelow T := ⟨0, fun _ h => h.1.le⟩
  set a₁ := sInf T
  -- every failing support exceeds the small-support threshold
  have hbig : ∀ a ∈ T, as < a := fun a h => by
    by_contra hc
    push Not at hc
    have := hsmall a h.1 hc
    linarith [h.2]
  have hge : as ≤ a₁ := le_csInf hT fun a h => (hbig a h).le
  have ha₁ : 0 < a₁ := has.trans_le hge
  have hbefore : ∀ a, 0 < a → a < a₁ → 0 < U.lam a := fun a ha hlt => by
    by_contra hc
    push Not at hc
    exact absurd (csInf_le hTb ⟨ha, hc⟩) (not_le.2 hlt)
  have hafter : ∀ a, a₁ < a → U.lam a ≤ 0 := fun a hlt => by
    obtain ⟨b, hb, hba⟩ := exists_lt_of_csInf_lt hT hlt
    exact (U.lam_antitone hb.1 hba.le).trans hb.2
  have hc : ContinuousAt U.lam a₁ := U.continuousOn_lam.continuousAt (Ioi_mem_nhds ha₁)
  have hle : U.lam a₁ ≤ 0 :=
    le_of_tendsto (x := 𝓝[>] a₁) (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun a (h : a ∈ Ioi a₁) => hafter a h)
  have hge0 : 0 ≤ U.lam a₁ :=
    ge_of_tendsto (x := 𝓝[<] a₁) (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (Filter.mem_of_superset (Ioo_mem_nhdsLT ha₁) fun a h => (hbefore a h.1 h.2).le)
  have hzero : U.lam a₁ = 0 := le_antisymm hle hge0
  obtain ⟨g, hg⟩ := U.exists_groundState ha₁
  have hgq : U.Q g = 0 := hg.2.2.trans hzero
  refine ⟨a₁, ha₁, hbefore, hzero, fun a h => ?_, ⟨a₀, csInf_le hTb ⟨ha₀, hl₀.le⟩, hl₀⟩,
    fun ψ hψ => ?_, g, hg, hgq, fun ψ hψ => ?_⟩
  · rcases h.lt_or_eq with h | h
    · exact hafter a h
    · rw [← h]; exact hle
  · have := U.lam_mul_le hψ
    rw [hzero, zero_mul] at this
    exact this
  · have := U.euler_lagrange_mem (U.isGroundState_iff.1 hg).1 hψ
    rw [hzero, zero_mul] at this
    exact this

end UData

/-! ## The χ column -/

section Chi

open DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- **`λ_χ` is continuous on `(0, ∞)`.** -/
theorem continuousOn_lamC (χ : DirichletCharacter ℂ N) : ContinuousOn (lamC χ) (Ioi 0) :=
  (chiU χ).continuousOn_lam

/-- **`λ_χ ≥ log 2 − ¼` at small support.** -/
theorem lamC_pos_small (χ : DirichletCharacter ℂ N) :
    ∃ a₀, 0 < a₀ ∧ ∀ a, 0 < a → a ≤ a₀ → Real.log 2 - 1 / 4 ≤ lamC χ a :=
  (chiU χ).lam_pos_small

/-- **The first positivity failure for `L(s, χ)`** (the χ column of `first_failure`,
FirstFailure.lean). If GRH fails for a good character with no real zero in `(0, 1)`, there is a
first support `a₁` at which Weil positivity is lost, with a ground state `g*` of `Q_χ` there that is
an exact null vector in the kernel of the bilinear form. -/
theorem first_failureC (hG : GoodChar χ) (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0)
    (h : ¬ GRH χ) :
    ∃ a₁, 0 < a₁ ∧ (∀ a, 0 < a → a < a₁ → 0 < lamC χ a) ∧ lamC χ a₁ = 0 ∧
      (∀ a, a₁ ≤ a → lamC χ a ≤ 0) ∧ (∃ a₀, a₁ ≤ a₀ ∧ lamC χ a₀ < 0) ∧
      (∀ ψ, Probe a₁ ψ → 0 ≤ QCu χ ψ) ∧
      ∃ g, IsGroundStateC χ a₁ g ∧ QCu χ g = 0 ∧ ∀ ψ, Probe a₁ ψ → (chiU χ).bil a₁ g ψ = 0 := by
  obtain ⟨a, ha, hneg⟩ := exists_lamC_neg_of_not_GRH hG hS h
  exact (chiU χ).first_failure ⟨a, ha, hneg a le_rfl⟩

end Chi

/-! ## The Davenport–Heilbronn instance -/

/-- **The first positivity failure of `Q_dh`, unconditionally.** `λ_dh < 0` from `12/5` on
(`lamDH_neg`, round 261's certificate), so `λ_dh` has a first zero `a₁ ≤ 12/5`: `Q_dh ≥ 0` on every
probe at `a₁`, with a ground state `g*` there that is an exact null vector in the kernel of `B_dh`. -/
theorem first_failureDH :
    ∃ a₁, 0 < a₁ ∧ a₁ ≤ 12 / 5 ∧ (∀ a, 0 < a → a < a₁ → 0 < lamDH a) ∧ lamDH a₁ = 0 ∧
      (∀ a, a₁ ≤ a → lamDH a ≤ 0) ∧ (∀ ψ, Probe a₁ ψ → 0 ≤ QDHu ψ) ∧
      ∃ g, IsGroundStateDH a₁ g ∧ QDHu g = 0 ∧ ∀ ψ, Probe a₁ ψ → bilDH a₁ g ψ = 0 := by
  obtain ⟨a₁, ha₁, hbefore, hzero, hafter, -, hpsd, g, hg, hgq, hker⟩ :=
    dhU.first_failure ⟨12 / 5, by norm_num, lamDH_neg le_rfl⟩
  have hle : a₁ ≤ 12 / 5 := by
    by_contra hc
    push Not at hc
    have h1 := hbefore (12 / 5) (by norm_num) hc
    have h2 := lamDH_neg (b := 12 / 5) le_rfl
    exact absurd h1 (not_lt.2 h2.le)
  exact ⟨a₁, ha₁, hle, hbefore, hzero, hafter, hpsd, g, hg, hgq, hker⟩

/-- **`λ_dh` is continuous on `(0, ∞)`.** -/
theorem continuousOn_lamDH : ContinuousOn lamDH (Ioi 0) := dhU.continuousOn_lam

end PsiOmega

#print axioms PsiOmega.UData.continuousOn_lam
#print axioms PsiOmega.UData.lam_pos_small
#print axioms PsiOmega.UData.first_failure
#print axioms PsiOmega.continuousOn_lamC
#print axioms PsiOmega.first_failureC
#print axioms PsiOmega.first_failureDH
#print axioms PsiOmega.continuousOn_lamDH
