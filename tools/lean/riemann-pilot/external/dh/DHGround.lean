import Mathlib
import DHForm
import DHColumn
import StructureD
import GroundChain
import SimpleStructure
import GroundStateExists

/-! # The dh column, part 3: the ground-state stack of `QDHu`

The ground-state theory of Weil's form `weilQ` for `ζ`, ported to the Davenport–Heilbronn form
`QDHu` (DHBridge.lean:72), which has no pole term. Each declaration cites the ζ declaration it is
the dh column of.

**Stage 1 (existence).** `groundSpaceDH`, `IsGroundStateDH`, and `exists_groundStateDH`, the port of
`exists_groundState` (GroundStateExists.lean:485) through `exists_min_weilQc`
(GroundStateExists.lean:355). Compactness (`exists_convergent_subseq`, Compactness.lean:233) needs a
bound on the archimedean energy at `q = ¼`; `QDHu` controls it at `q = ¾`. The transfer:
`K_{1/4}(u) = e^u K_{3/4}(u)` (`archIntegrand_eq_exp_mul`), so on `(0, 2a]` the `¼`-integrand is at
most `e^{2a}` times the `¾`-integrand; beyond `2a` the autocorrelation of a probe at support `a`
vanishes, so there the `¼`-integrand is `‖g‖²K_{1/4}(u)` (not `0`), integrable on `(2a, ∞)`
(`archIntegrand_le_dom`, `archE_le_DH`: `E(g) ≤ e^{2a}E_{3/4}(g) + ‖g‖²T(a)`). Fatou is applied to
the `¾`-integrand, and the same domination makes the limit a probe (`arch_of_archQ`).

**Stage 2 (Euler–Lagrange).** `bilDH`, written through `xcorr` like `bil0` and equal to the
polarisation of `QDHu` (`bilDH_polar`); `euler_lagrangeDH_mem`: `B_dh(w, ψ) = λ_dh⟨w, ψ⟩`.

**Stage 3 (swap closure, simple ground states).** `split_mem_groundSpaceDH` (no pole hypothesis),
`zero_swap_falseDH`, `zeros_real_or_imagDH`, `zeros_real_or_imagDH'`, `green_mem_groundSpaceDH`;
`dhRHcross_of_eventually_simple` and its refutation `not_simple_hypConvDH`.

**Stage 4 (Theorem D).** `Gpole_annihilatesDH` (no pole hypothesis on `v`), `G_mem_partnerDH`,
`finiteDimensional_groundL2DH`, the chain filtration (`chainSpaceDH`, `chain_stepDH`, `gdimDH`),
`theoremDDH`, the top-of-chain ground state `topGSDH` with `topGSDH_cross`, and
`not_hypConvDH_top`: `HypConvDH` fails for the top-of-chain ground states at every sequence of
positive supports.
-/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## Stage 1: the ground-state space and existence -/

/-- **The ground-state space of `QDHu`** at support `a`: probes with `Q_dh(g) = λ_dh(a)‖g‖²`
(the dh column of `groundSpace`, Uniqueness.lean:332). A submodule of `ℝ → ℝ`. -/
abbrev groundSpaceDH (a : ℝ) : Submodule ℝ (ℝ → ℝ) := (QDHu_form a).space

/-- **A ground state of `QDHu`** at support `a`: a normalised probe at the ground energy (the dh
column of `IsGroundState`, Roadmap.lean:63, in the energy form of `isGroundState_iff`). -/
def IsGroundStateDH (a : ℝ) (g : ℝ → ℝ) : Prop :=
  Probe a g ∧ normSq g = 1 ∧ QDHu g = lamDH a

/-- The ground states are exactly the unit vectors of `groundSpaceDH`. -/
theorem isGroundStateDH_iff {a : ℝ} {g : ℝ → ℝ} :
    IsGroundStateDH a g ↔ g ∈ groundSpaceDH a ∧ normSq g = 1 := by
  constructor
  · rintro ⟨hp, hn, hq⟩
    refine ⟨⟨hp, ?_⟩, hn⟩
    show QDHu g = (QDHu_form a).inf * normSq g
    rw [hn, mul_one]; exact hq
  · rintro ⟨⟨hp, hq⟩, hn⟩
    refine ⟨hp, hn, ?_⟩
    rw [hq, hn, mul_one]; rfl

/-- The ground states are exactly the normalised minimisers (the form of `IsGroundState`,
Roadmap.lean:63; `isGroundState_iff`, Uniqueness.lean:335). -/
theorem isGroundStateDH_iff_min {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} :
    IsGroundStateDH a g ↔
      Probe a g ∧ normSq g = 1 ∧ ∀ h, Probe a h → normSq h = 1 → QDHu g ≤ QDHu h := by
  rw [isGroundStateDH_iff]; exact ((QDHu_form a).isMin_iff ha).symm

/-! ### `E_{1/4}` from `E_{3/4}` on probes -/

/-- `K_{1/4}(u) = e^u K_{3/4}(u)`: the `¼`-integrand is `e^u` times the `¾`-integrand. -/
theorem archIntegrand_eq_exp_mul (g : ℝ → ℝ) (u : ℝ) :
    archIntegrand g u = Real.exp u * archIntegrandQ (3 / 4) g u := by
  unfold archIntegrand archIntegrandQ archKer
  have e : Real.exp (u / 2) = Real.exp u * Real.exp ((1 - 2 * (3 / 4)) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]; ring

/-- `K_{1/4}` is integrable on `(2a, ∞)`: `u·K_{1/4}(u) ≤ 16e^{−u/4}` (`u_archK_le`). -/
theorem integrableOn_archKer_quarter {a : ℝ} (ha : 0 < a) :
    IntegrableOn (archKer (1 / 4)) (Ioi (2 * a)) := by
  have hm : AEStronglyMeasurable (archKer (1 / 4)) (volume.restrict (Ioi (2 * a))) := by
    have : Measurable (archKer (1 / 4)) := by
      unfold archKer
      exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).div
        Real.measurable_sinh
    exact this.aestronglyMeasurable
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi (2 * a)
    (by norm_num : (0 : ℝ) < 1 / 4)).const_mul (16 / (2 * a))) hm
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
  have h2a : 2 * a < u := hu
  have hu0 : 0 < u := by linarith
  have e : archKer (1 / 4) u = Real.exp (u / 2) / Real.sinh u := by
    unfold archKer; congr 2; ring
  have hk := archKer_pos (1 / 4) hu0
  rw [e] at hk ⊢
  rw [Real.norm_eq_abs, abs_of_pos hk,
    show 16 / (2 * a) * Real.exp (-(1 / 4) * u) = (16 * Real.exp (-(1 / 4) * u)) / (2 * a) by ring,
    le_div_iff₀ (by positivity)]
  calc Real.exp (u / 2) / Real.sinh u * (2 * a) ≤ Real.exp (u / 2) / Real.sinh u * u :=
        mul_le_mul_of_nonneg_left h2a.le hk.le
    _ = u * (Real.exp (u / 2) / Real.sinh u) := by ring
    _ ≤ _ := u_archK_le hu0

/-- `∫_{u > 2a} K_{1/4}(u) du`, written as an integral over `u > 0`. -/
def tailDH (a : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), (Ioi (2 * a)).indicator (archKer (1 / 4)) u

theorem integrableOn_tail {a : ℝ} (ha : 0 < a) :
    IntegrableOn ((Ioi (2 * a)).indicator (archKer (1 / 4))) (Ioi (0 : ℝ)) :=
  ((integrableOn_archKer_quarter ha).integrable_indicator measurableSet_Ioi).integrableOn

/-- **The pointwise domination**: `[f(0) − f(u)]K_{1/4}(u) ≤ e^{2a}[f(0) − f(u)]K_{3/4}(u)
+ ‖g‖²·1_{u > 2a}K_{1/4}(u)` for `g` supported in `[−a, a]`. -/
theorem archIntegrand_le_dom {a : ℝ} {g : ℝ → ℝ} (hsupp : ∀ u, a < |u| → g u = 0)
    (hg : MemLp g 2 volume) {u : ℝ} (hu : 0 < u) :
    archIntegrand g u ≤ Real.exp (2 * a) * archIntegrandQ (3 / 4) g u
      + normSq g * (Ioi (2 * a)).indicator (archKer (1 / 4)) u := by
  have hQ := archIntegrandQ_nonneg (3 / 4) hg hu
  rw [archIntegrand_eq_exp_mul]
  by_cases h : 2 * a < u
  · have h0 : autocorr g u = 0 := autocorr_eq_zero hsupp (h.trans_le (le_abs_self u))
    have hi : (Ioi (2 * a)).indicator (archKer (1 / 4)) u = archKer (1 / 4) u := by
      simp only [Set.indicator_apply, Set.mem_Ioi, h, ite_true]
    have e : Real.exp u * archIntegrandQ (3 / 4) g u = normSq g * archKer (1 / 4) u := by
      unfold archIntegrandQ archKer
      rw [h0, sub_zero, autocorr_zero]
      have : Real.exp ((1 - 2 * (1 / 4)) * u) = Real.exp u * Real.exp ((1 - 2 * (3 / 4)) * u) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]; ring
    rw [hi, e]
    have := mul_nonneg (Real.exp_pos (2 * a)).le hQ
    linarith
  · have hi : (Ioi (2 * a)).indicator (archKer (1 / 4)) u = 0 := by
      simp only [Set.indicator_apply, Set.mem_Ioi, h, ite_false]
    rw [hi, mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (not_lt.1 h)) hQ

/-- **`E(g) ≤ e^{2a}E_{3/4}(g) + ‖g‖²·T(a)`** on probes at support `a`. -/
theorem archE_le_DH {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) :
    archE g ≤ Real.exp (2 * a) * archEQ (3 / 4) g + normSq g * tailDH a := by
  have hQ := archIntegrandQ_integrable hp (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)
  have hK := integrableOn_tail ha
  calc archE g = ∫ u in Ioi 0, archIntegrand g u := rfl
    _ ≤ ∫ u in Ioi 0, (Real.exp (2 * a) * archIntegrandQ (3 / 4) g u
          + normSq g * (Ioi (2 * a)).indicator (archKer (1 / 4)) u) :=
        setIntegral_mono_on hp.arch ((hQ.const_mul _).add (hK.const_mul _)) measurableSet_Ioi
          fun u hu => archIntegrand_le_dom hp.supp hp.memL2 hu
    _ = _ := by
        rw [integral_add (hQ.const_mul _) (hK.const_mul _), integral_const_mul, integral_const_mul]
        rfl

/-- **The archimedean condition of a probe from the `¾`-integrand**, for `g` supported in
`[−a, a]`. -/
theorem arch_of_archQ {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hsupp : ∀ u, a < |u| → g u = 0)
    (hg : MemLp g 2 volume) (hQ : IntegrableOn (archIntegrandQ (3 / 4) g) (Ioi 0)) :
    IntegrableOn (archIntegrand g) (Ioi 0) := by
  have hK := integrableOn_tail ha
  have hm : AEStronglyMeasurable (archIntegrand g) (volume.restrict (Ioi 0)) := by
    have : archIntegrand g = fun u => Real.exp u * archIntegrandQ (3 / 4) g u :=
      funext (archIntegrand_eq_exp_mul g)
    rw [this]
    exact Real.continuous_exp.aestronglyMeasurable.mul hQ.aestronglyMeasurable
  refine Integrable.mono' ((hQ.const_mul (Real.exp (2 * a))).add (hK.const_mul (normSq g))) hm
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg hg hu)]
  exact archIntegrand_le_dom hsupp hg hu

/-! ### The minimiser -/

/-- The non-archimedean part of `QDHu` at support `a`: the constant and the finite prime sum (the dh
column of `nonArch`, GroundStateExists.lean:326, with no pole term). -/
def nonArchDH (a : ℝ) (g : ℝ → ℝ) : ℝ :=
  constDH * normSq g
    - 2 * ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr g (Real.log n)

theorem QDHu_eq_nonArch {a : ℝ} {g : ℝ → ℝ} (hsupp : ∀ u, a < |u| → g u = 0) :
    QDHu g = nonArchDH a g + archEQ (3 / 4) g := by
  rw [QDHu_eq_range hsupp]; unfold nonArchDH; ring

theorem nonArchDH_ge {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) :
    -MDH a ≤ nonArchDH a g := by
  have hP := abs_primeDH_le hp
  rw [hn, mul_one] at hP
  have h1 := neg_abs_le constDH
  have h2 := le_abs_self
    (∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr g (Real.log n))
  unfold nonArchDH MDH; rw [hn, mul_one]; linarith

/-- **A minimiser of `QDHu` exists at every support `a > 0`** (the dh column of `exists_min_weilQc`,
GroundStateExists.lean:355, at pole weight `0` with `E_{3/4}` in place of `E`). -/
theorem exists_min_QDHu {a : ℝ} (ha : 0 < a) : ∃ g, Probe a g ∧ normSq g = 1 ∧
    ∀ h, Probe a h → normSq h = 1 → QDHu g ≤ QDHu h := by
  set Sv : Set ℝ := {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ QDHu h = q} with hSv
  have hne : Sv.Nonempty := ⟨_, box a, box_probe a, normSq_box ha, rfl⟩
  have hbdd : BddBelow Sv := (QDHu_form a).bdd
  obtain ⟨q, hqa, hq, hqS⟩ := exists_seq_tendsto_sInf hne hbdd
  choose h hp hn hQ using hqS
  set lam := sInf Sv with hlam
  -- the non-archimedean part is bounded below, so `E_{3/4}` is bounded above
  have hC3 : ∀ j, archEQ (3 / 4) (h j) ≤ q 0 + MDH a := by
    intro j
    have e := QDHu_eq_nonArch (hp j).supp
    have := nonArchDH_ge (hp j) (hn j)
    have hqj : q j ≤ q 0 := hqa (Nat.zero_le j)
    rw [hQ j] at e
    linarith
  -- and so is `E = E_{1/4}`, which the compactness theorem takes
  have hC : ∀ j, archE (h j) ≤ Real.exp (2 * a) * (q 0 + MDH a) + tailDH a := by
    intro j
    have h1 := archE_le_DH ha (hp j)
    rw [hn j, one_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left (hC3 j) (Real.exp_pos (2 * a)).le
    linarith
  obtain ⟨φ, hφ, G, hG, hlim⟩ := exists_convergent_subseq ha hp (B := 1) (fun j => (hn j).le) hC
  set G' := symCut a G with hG'def
  have hG' : MemLp G' 2 volume := memLp_symCut a hG
  have hlim' : Tendsto (fun j => normSq (fun t => h (φ j) t - G' t)) atTop (𝓝 0) :=
    squeeze_zero (fun j => integral_nonneg fun t => sq_nonneg _)
      (fun j => normSq_sub_symCut_le (hp (φ j)) hG) hlim
  have hmem : ∀ j, MemLp (h (φ j)) 2 volume := fun j => (hp (φ j)).memL2
  -- continuity of the non-archimedean terms
  have hnorm : Tendsto (fun j => normSq (h (φ j))) atTop (𝓝 (normSq G')) := by
    simp_rw [normSq_eq_mul]
    exact tendsto_integral_mul hmem hmem hG' hG' hlim' hlim'
  have hnormG : normSq G' = 1 := by
    have h1 : Tendsto (fun j => normSq (h (φ j))) atTop (𝓝 1) := by
      simp only [hn]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hnorm h1
  have hauto : ∀ u, Tendsto (fun j => autocorr (h (φ j)) u) atTop (𝓝 (autocorr G' u)) := by
    intro u
    have hsh : ∀ j, normSq (fun t => h (φ j) (t + u) - G' (t + u))
        = normSq (fun t => h (φ j) t - G' t) :=
      fun j => normSq_shift (fun t => h (φ j) t - G' t) u
    unfold autocorr
    exact tendsto_integral_mul hmem (fun j => memLp_shift (hmem j) u) hG' (memLp_shift hG' u)
      hlim' (hlim'.congr fun j => (hsh j).symm)
  have hsuppG' : ∀ u, a < |u| → G' u = 0 := symCut_supp a G
  have hnonArch : Tendsto (fun j => nonArchDH a (h (φ j))) atTop (𝓝 (nonArchDH a G')) := by
    unfold nonArchDH
    exact (hnorm.const_mul _).sub
      ((tendsto_finsetSum _ fun n _ => (hauto _).const_mul _).const_mul 2)
  -- the `¾`-energies converge to `λ − nonArch(G')`
  have hqφ : Tendsto (fun j => q (φ j)) atTop (𝓝 lam) := hq.comp hφ.tendsto_atTop
  have hA : Tendsto (fun j => archEQ (3 / 4) (h (φ j))) atTop (𝓝 (lam - nonArchDH a G')) := by
    have e : ∀ j, archEQ (3 / 4) (h (φ j)) = q (φ j) - nonArchDH a (h (φ j)) := by
      intro j; rw [← hQ (φ j), QDHu_eq_nonArch (hp (φ j)).supp]; ring
    simp_rw [e]
    exact hqφ.sub hnonArch
  -- Fatou on the `¾`-integrand
  obtain ⟨hint, hle⟩ := fatou_real measurableSet_Ioi
    (f := fun j => archIntegrandQ (3 / 4) (h (φ j))) (F := archIntegrandQ (3 / 4) G')
    (fun j => archIntegrandQ_integrable (hp (φ j)) (by norm_num))
    (fun j u hu => archIntegrandQ_nonneg (3 / 4) (hmem j) hu)
    (fun u _ => by
      unfold archIntegrandQ
      exact ((hauto 0).sub (hauto u)).mul_const _) hA
  have hPG : Probe a G' := ⟨symCut_even a G, hsuppG', hG', arch_of_archQ ha hsuppG' hG' hint⟩
  refine ⟨G', hPG, hnormG, fun h' hp' hn' => ?_⟩
  have hQG : QDHu G' ≤ lam := by
    rw [QDHu_eq_nonArch hsuppG']; unfold archEQ; linarith
  exact hQG.trans (csInf_le hbdd ⟨h', hp', hn', rfl⟩)

/-- **A ground state of `QDHu` exists at every support `a > 0`** (the dh column of
`exists_groundState`, GroundStateExists.lean:485). -/
theorem exists_groundStateDH {a : ℝ} (ha : 0 < a) : ∃ g, IsGroundStateDH a g := by
  obtain ⟨g, hp, hn, hmin⟩ := exists_min_QDHu ha
  exact ⟨g, (isGroundStateDH_iff_min ha).2 ⟨hp, hn, hmin⟩⟩

/-- Ground states at every support of a sequence `a_n > 0` (the dh column of `exists_groundStates`,
GroundStateExists.lean:455). -/
theorem exists_groundStatesDH {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) :
    ∃ g : ℕ → ℝ → ℝ, ∀ n, IsGroundStateDH (a n) (g n) :=
  ⟨fun n => (exists_groundStateDH (ha n)).choose,
    fun n => (exists_groundStateDH (ha n)).choose_spec⟩


/-! ## Stage 2: the bilinear form and the Euler–Lagrange equation -/

/-- **The bilinear form of `QDHu`** at support `a`:
`B_dh(φ, ψ) = c·x(0) + ∫_0^∞ (x(0) − x(u))K_{3/4}(u) du − 2Σ_{n < N(a)} c(n)n^{−1/2} x(log n)`,
`x = xcorr φ ψ` (the dh column of `bil0`, StrictPositivity.lean:92; the term `2ĝ(i/2)ĥ(i/2)` of
`euler_lagrange_mem`, UniquenessQ.lean:83, is absent). It is the polarisation of `QDHu`
(`bilDH_polar`). -/
def bilDH (a : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  constDH * xcorr φ ψ 0 + (∫ u in Ioi 0, archXQ (3 / 4) φ ψ u)
    - 2 * ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * xcorr φ ψ (Real.log n)

/-- `B_dh` is symmetric (the dh column of `bil0_comm`, UniquenessQ.lean:29). -/
theorem bilDH_comm (a : ℝ) (φ ψ : ℝ → ℝ) : bilDH a φ ψ = bilDH a ψ φ := by
  unfold bilDH archXQ; simp only [xcorr_comm φ ψ]

/-- `Q_dh(φ + sψ) = Q_dh(φ) + 2sB_dh(φ, ψ) + s²Q_dh(ψ)` on probes (the dh column of
`weilQ0_add_smul`, StrictPositivity.lean:99). -/
theorem QDHu_add_smul {a : ℝ} {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : Probe a ψ) (s : ℝ) :
    QDHu (fun t => φ t + s * ψ t) = QDHu φ + 2 * s * bilDH a φ ψ + s ^ 2 * QDHu ψ := by
  have hA := archEQ_add_smul hφ hψ (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4) s
  have hS : ∑ n ∈ Finset.range (primeCut a),
        fDH n / Real.sqrt n * autocorr (fun t => φ t + s * ψ t) (Real.log n)
      = ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr φ (Real.log n)
        + 2 * s * ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * xcorr φ ψ (Real.log n)
        + s ^ 2 * ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr ψ (Real.log n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [autocorr_add_smul hφ.memL2 hψ.memL2]; ring
  rw [QDHu_eq_range (probe_add_smul hφ hψ s).supp, QDHu_eq_range hφ.supp, QDHu_eq_range hψ.supp,
    normSq_add_smul hφ.memL2 hψ.memL2, hA, hS]
  unfold bilDH; ring

/-- **`B_dh` is the polarisation of `QDHu`**: `B_dh(φ, ψ) = (Q_dh(φ + ψ) − Q_dh(φ − ψ))/4`, the
bilinear form whose diagonal the parallelogram law `QDHu_add_sub` (DHForm.lean:76) makes
quadratic. -/
theorem bilDH_polar {a : ℝ} {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : Probe a ψ) :
    bilDH a φ ψ = (QDHu (fun t => φ t + ψ t) - QDHu (fun t => φ t - ψ t)) / 4 := by
  have e1 := QDHu_add_smul hφ hψ 1
  have e2 := QDHu_add_smul hφ hψ (-1)
  have f1 : (fun t => φ t + 1 * ψ t) = fun t => φ t + ψ t := by funext t; ring
  have f2 : (fun t => φ t + -1 * ψ t) = fun t => φ t - ψ t := by funext t; ring
  rw [f1] at e1
  rw [f2] at e2
  rw [e1, e2]; ring

/-- `Q_dh(f) = B_dh(f, f)` (the dh column of `weilQ0_eq_bil0`, Commute.lean:148). -/
theorem QDHu_eq_bilDH {a : ℝ} {f : ℝ → ℝ} (hf : Probe a f) : QDHu f = bilDH a f f := by
  have e := QDHu_add_smul hf hf 1
  have e2 : (fun t => f t + 1 * f t) = fun t => (2 : ℝ) * f t := by funext t; ring
  rw [e2, QDHu_smul] at e
  linarith

/-- **Euler–Lagrange for any element of the ground space of `QDHu`**: `B_dh(w, ψ) = λ_dh⟨w, ψ⟩`
for every probe `ψ` at support `a` (the dh column of `euler_lagrange_mem`, UniquenessQ.lean:82,
whose pole term `2ŵ(i/2)ψ̂(i/2)` is absent). -/
theorem euler_lagrangeDH_mem {a : ℝ} {w ψ : ℝ → ℝ} (hw : w ∈ groundSpaceDH a) (hψ : Probe a ψ) :
    bilDH a w ψ = lamDH a * xcorr w ψ 0 := by
  have hq : QDHu w = lamDH a * normSq w := hw.2
  apply sub_eq_zero.1
  refine quad_zero (c := QDHu ψ - lamDH a * normSq ψ) fun s => ?_
  have h := lamDH_mul_le (probe_add_smul hw.1 hψ s)
  rw [QDHu_add_smul hw.1 hψ, normSq_add_smul hw.1.memL2 hψ.memL2, hq] at h
  nlinarith [h]

/-- **Euler–Lagrange at a ground state**, inner-product form: `B_dh(g, ψ) = λ_dh(a)∫gψ`. -/
theorem euler_lagrangeDH {a : ℝ} {g ψ : ℝ → ℝ} (hg : IsGroundStateDH a g) (hψ : Probe a ψ) :
    bilDH a g ψ = lamDH a * ∫ t, g t * ψ t := by
  rw [← xcorr_zero_eq]; exact euler_lagrangeDH_mem (isGroundStateDH_iff.1 hg).1 hψ

/-! ## Stage 3: the swap closure and simple ground states -/

/-- A ground state of `QDHu` is **simple** when the ground-state space is spanned by it (the dh
column of `SimpleGround`, ZeroSwap.lean:98). -/
def SimpleGroundDH (a : ℝ) (g : ℝ → ℝ) : Prop :=
  IsGroundStateDH a g ∧ ∀ h ∈ groundSpaceDH a, ∃ c : ℝ, h =ᵐ[volume] fun t => c * g t

/-- **Splitting a ground-space element** (the dh column of `split_mem_groundSpace`,
ZeroSwap.lean:158): probes `u, v` whose autocorrelations add up to those of `g ∈ V_dh` lie in
`V_dh`. The pole hypothesis `ĝ_u(i/2)² + ĝ_v(i/2)² = ĝ(i/2)²` drops out: `QDHu` has no pole term. -/
theorem split_mem_groundSpaceDH {a : ℝ} {g u v : ℝ → ℝ} (hg : g ∈ groundSpaceDH a)
    (hu : Probe a u) (hv : Probe a v) (hac : ∀ x, autocorr u x + autocorr v x = autocorr g x) :
    u ∈ groundSpaceDH a ∧ v ∈ groundSpaceDH a := by
  have hp : Probe a g := hg.1
  have hN : normSq u + normSq v = normSq g := by
    rw [normSq_eq_autocorr, normSq_eq_autocorr, normSq_eq_autocorr]; exact hac 0
  have hq : (1 / 4 : ℝ) ≤ 3 / 4 := by norm_num
  have hA : archEQ (3 / 4) u + archEQ (3 / 4) v = archEQ (3 / 4) g := by
    unfold archEQ
    rw [← integral_add (archIntegrandQ_integrable hu hq) (archIntegrandQ_integrable hv hq)]
    congr 1; funext x
    unfold archIntegrandQ
    linear_combination (archKer (3 / 4) x) * (hac 0 - hac x)
  have hS : ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr u (Real.log n)
      + ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr v (Real.log n)
      = ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr g (Real.log n) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    linear_combination (fDH n / Real.sqrt n) * hac (Real.log n)
  have hQ : QDHu u + QDHu v = QDHu g := by
    rw [QDHu_eq_range hu.supp, QDHu_eq_range hv.supp, QDHu_eq_range hp.supp]
    linear_combination constDH * hN + hA - 2 * hS
  have ru := lamDH_mul_le hu
  have rv := lamDH_mul_le hv
  have hgq : QDHu g = lamDH a * normSq g := hg.2
  have hsplit : lamDH a * normSq g = lamDH a * normSq u + lamDH a * normSq v := by
    rw [← hN]; ring
  exact ⟨⟨hu, show QDHu u = lamDH a * normSq u by linarith⟩,
    ⟨hv, show QDHu v = lamDH a * normSq v by linarith⟩⟩

/-- **The zero-swap lemma for `QDHu`, core** (the dh column of `zero_swap_false`,
ZeroSwap.lean:187). A simple ground state admits no realised swap of a zero with non-real square. -/
theorem zero_swap_falseDH {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hs : SimpleGroundDH a g) {σ : ℂ}
    (hσ : σ.im ≠ 0) (hR : SwapRealization a g σ) : False := by
  obtain ⟨hgs, hsimp⟩ := hs
  obtain ⟨u, v, hu, hv, hB, hac⟩ := hR
  obtain ⟨⟨-, eu⟩, ⟨-, ev⟩⟩ := split_mem_groundSpaceDH (isGroundStateDH_iff.1 hgs).1 hu hv hac
  obtain ⟨α, hα⟩ := hsimp u ⟨hu, eu⟩
  obtain ⟨β, hβ⟩ := hsimp v ⟨hv, ev⟩
  set c : ℂ := (α : ℂ) + Complex.I * β
  set B : ℂ → ℂ := fun z => (z ^ 2 - (starRingEnd ℂ) σ) / (z ^ 2 - σ)
  have key : ∀ t : ℝ, ghatC g a t ≠ 0 → c = B t := by
    intro t ht
    have h := hB t (sq_ne_of_im hσ t)
    rw [ghatC_congr_ae hα, ghatC_smul, ghatC_congr_ae hβ, ghatC_smul] at h
    apply mul_left_cancel₀ ht
    rw [← h]; simp only [c]; ring
  obtain ⟨t₁, t₂, h₁, ht₂, hsq⟩ := exists_two_real_ghatC_ne ha hgs.1 hgs.2.1
  have c1 := key t₁ h₁
  have c2 := key t₂ ht₂
  have hd1 : ((t₁ : ℂ)) ^ 2 - σ ≠ 0 := sub_ne_zero.2 (sq_ne_of_im hσ t₁)
  have hd2 : ((t₂ : ℂ)) ^ 2 - σ ≠ 0 := sub_ne_zero.2 (sq_ne_of_im hσ t₂)
  have heq : B t₁ = B t₂ := c1.symm.trans c2
  simp only [B] at heq
  rw [div_eq_div_iff hd1 hd2] at heq
  have hprod : (((t₂ ^ 2 - t₁ ^ 2 : ℝ)) : ℂ) * (σ - (starRingEnd ℂ) σ) = 0 := by
    push_cast; linear_combination heq
  rcases mul_eq_zero.1 hprod with h | h
  · rw [Complex.ofReal_eq_zero] at h; linarith
  · rw [Complex.sub_conj] at h
    apply hσ
    have := congrArg Complex.im h
    simp at this
    exact this

/-- **Zeros of a simple ground state of `QDHu` lie on `ℝ ∪ iℝ`**, given the swap realisation for
every zero off the cross (the dh column of `zeros_real_or_imag`, ZeroSwap.lean:225). -/
theorem zeros_real_or_imagDH {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hs : SimpleGroundDH a g)
    (hPW : ∀ w : ℂ, ghatC g a w = 0 → (w ^ 2).im ≠ 0 → SwapRealization a g (w ^ 2)) :
    ∀ w : ℂ, ghatC g a w = 0 → w.re = 0 ∨ w.im = 0 := by
  intro w hw
  by_contra hne
  push Not at hne
  have him : (w ^ 2).im ≠ 0 := by
    rw [sq, Complex.mul_im]
    have := mul_ne_zero hne.1 hne.2
    intro h; apply this; linarith
  exact zero_swap_falseDH ha hs him (hPW w hw him)

/-- **Zeros of a simple ground state of `QDHu` lie on `ℝ ∪ iℝ`**, no further input
(the dh column of `zeros_real_or_imag'`, SwapRealize.lean:405; `swapRealization_of_zero`,
SwapRealize.lean:391, holds for every probe). -/
theorem zeros_real_or_imagDH' {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hs : SimpleGroundDH a g) :
    ∀ w : ℂ, ghatC g a w = 0 → w.re = 0 ∨ w.im = 0 :=
  zeros_real_or_imagDH ha hs fun _ hw hσ => swapRealization_of_zero ha hs.1.1 hw hσ

/-- **The chain for `dh` with eventual simplicity** (the dh column of `rh_of_eventually_simple`,
SwapRealize.lean:412, and of `rh_of_simple_ground_states`, HurwitzCross.lean:86): eventually simple
ground states of `QDHu` satisfying `HypConvDH` give the cross form `DHRHcross`. -/
theorem dhRHcross_of_eventually_simple {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundStateDH (a n) (g n))
    (hsimple : ∀ᶠ n in atTop, SimpleGroundDH (a n) (g n)) (hconv : HypConvDH a g) : DHRHcross :=
  dhRHcross_of_cross (fun n => (probe_integrable (hgs n).1).intervalIntegrable)
    (hsimple.mono fun n hs => zeros_real_or_imagDH' (ha n) hs) hconv

/-- **The refutation**: no sequence of eventually simple ground states of `QDHu` satisfies
`HypConvDH` (`dh_offline_nonreal_zero`, DHOffCross.lean, through `not_hypConvDH_of_cross`). -/
theorem not_simple_hypConvDH {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundStateDH (a n) (g n))
    (hsimple : ∀ᶠ n in atTop, SimpleGroundDH (a n) (g n)) : ¬ HypConvDH a g :=
  not_hypConvDH_of_cross (fun n => (probe_integrable (hgs n).1).intervalIntegrable)
    (hsimple.mono fun n hs => zeros_real_or_imagDH' (ha n) hs)

/-! ### The swap closure of the ground space -/

/-- The swapped pair of a ground-space element lies in the ground space (the dh column of
`swap_pair_mem`, SimpleStructure.lean:25). -/
theorem swap_pair_memDH {g : ℝ → ℝ} {a : ℝ} {w : ℂ} (ha : 0 < a) (hg : g ∈ groundSpaceDH a)
    (hw : ghatC g a w = 0) (hσ : (w ^ 2).im ≠ 0) :
    uSw g a w ∈ groundSpaceDH a ∧ vSw g a w ∈ groundSpaceDH a := by
  have hp : Probe a g := hg.1
  have hw0 : w ≠ 0 := by rintro rfl; apply hσ; simp
  have hac := swap_autocorr hp ha hw hw0 hσ
  have hac' : ∀ s, autocorr (vSw g a w) s + autocorr (uSw g a w) s = autocorr g s :=
    fun s => by rw [add_comm]; exact hac s
  have hu : Probe a (uSw g a w) := ⟨uSw_even hp hw, uSw_supp hp hw, memLp_uSw hp hw,
    arch_dom (memLp_uSw hp hw) (memLp_vSw hp hw) hac hp.arch⟩
  have hv : Probe a (vSw g a w) := ⟨vSw_even hp hw, vSw_supp hp hw, memLp_vSw hp hw,
    arch_dom (memLp_vSw hp hw) (memLp_uSw hp hw) hac' hp.arch⟩
  exact split_mem_groundSpaceDH hg hu hv hac

/-- **Swap closure** (the dh column of `green_mem_groundSpace`, SimpleStructure.lean:43): if
`g ∈ V_dh` and `ĝ(w) = 0` with `w²` non-real, the real and imaginary parts of the Green solution
`h = (∂² + w²)⁻¹ g` lie in `V_dh`. -/
theorem green_mem_groundSpaceDH {g : ℝ → ℝ} {a : ℝ} {w : ℂ} (ha : 0 < a)
    (hg : g ∈ groundSpaceDH a) (hw : ghatC g a w = 0) (hσ : (w ^ 2).im ≠ 0) :
    (fun x => (hSw g a w x).re) ∈ groundSpaceDH a ∧
      (fun x => (hSw g a w x).im) ∈ groundSpaceDH a := by
  obtain ⟨hu, hv⟩ := swap_pair_memDH ha hg hw hσ
  set s := (w ^ 2).im
  have hc : ∀ x, ((starRingEnd ℂ) (w ^ 2) - w ^ 2) * hSw g a w x
      = ((2 * s * (hSw g a w x).im : ℝ) : ℂ)
        + ((-2 * s * (hSw g a w x).re : ℝ) : ℂ) * Complex.I := by
    intro x
    have e1 : ((starRingEnd ℂ) (w ^ 2) - w ^ 2).re = 0 := by
      simp only [Complex.sub_re, Complex.conj_re, sub_self]
    have e2 : ((starRingEnd ℂ) (w ^ 2) - w ^ 2).im = -2 * s := by
      simp only [Complex.sub_im, Complex.conj_im, s]; ring
    apply Complex.ext
    · rw [Complex.mul_re, e1, e2]; simp
    · rw [Complex.mul_im, e1, e2]; simp
  have hre : (fun x => (hSw g a w x).re) = fun x => (-(2 * s)⁻¹) * vSw g a w x := by
    funext x
    have : vSw g a w x = -2 * s * (hSw g a w x).re := by
      rw [vSw_eq]; simp only; rw [hc x]; simp
    rw [this]; field_simp
  have him : (fun x => (hSw g a w x).im)
      = fun x => (2 * s)⁻¹ * (uSw g a w x + (-1) * g x) := by
    funext x
    have : uSw g a w x = g x + 2 * s * (hSw g a w x).im := by
      rw [uSw_eq]; simp only; rw [hc x]; simp
    rw [this]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [hre]; exact (groundSpaceDH a).smul_mem _ hv
  · rw [him]
    have := (groundSpaceDH a).add_mem hu ((groundSpaceDH a).smul_mem (-1) hg)
    exact (groundSpaceDH a).smul_mem _ (by convert this using 1)


/-! ## Stage 4: Theorem D for `QDHu`

The port of StructureD.lean. The Green operator `Gpole` of the pole (DegenerateFlat.lean:32) is a
fact about probes, not about the form: `Gpole_probe`, `Gpole_hat`, `xcorr_G_swap` are reused. What
changes is that `QDHu` has no pole term, so `Gpole_annihilatesDH` needs no pole hypothesis on `v`. -/

/-- **`Q_dh − λ_dh` pairs `G v` with every pole-free probe to zero**, for `v` in the ground space
(the dh column of `Gpole_annihilates`, DegenerateFlat.lean:511, whose hypothesis `v̂(i/2) = 0` only
killed the pole term `2v̂(i/2)(Gm)^(i/2)` and drops out). -/
theorem Gpole_annihilatesDH {a : ℝ} (ha : 0 ≤ a) {v m : ℝ → ℝ} (hv : v ∈ groundSpaceDH a)
    (hm : Probe a m) (hmpole : poleR m a = 0) :
    bilDH a (Gpole v a) m - lamDH a * xcorr (Gpole v a) m 0 = 0 := by
  have el := euler_lagrangeDH_mem hv (Gpole_probe hm ha hmpole)
  have hsw : bilDH a (Gpole v a) m = bilDH a v (Gpole m a) := by
    unfold bilDH archXQ
    simp only [xcorr_G_swap ha hv.1 hm hmpole]
  rw [hsw, xcorr_G_swap ha hv.1 hm hmpole, el, sub_self]

/-- `Q_λ(φ + rψ) = Q_λ(φ) + 2r B_λ(φ, ψ) + r² Q_λ(ψ)` for `Q_λ = Q_dh − λ_dh‖·‖²` (the dh column of
`Qlam_add_smul`, DegenerateFlat.lean:519). -/
theorem QlamDH_add_smul {a : ℝ} {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : Probe a ψ) (r : ℝ) :
    QDHu (fun t => φ t + r * ψ t) - lamDH a * normSq (fun t => φ t + r * ψ t)
      = (QDHu φ - lamDH a * normSq φ) + 2 * r * (bilDH a φ ψ - lamDH a * xcorr φ ψ 0)
        + r ^ 2 * (QDHu ψ - lamDH a * normSq ψ) := by
  rw [QDHu_add_smul hφ hψ, normSq_add_smul hφ.memL2 hψ.memL2]; ring

theorem QlamDH_nonneg {a : ℝ} {f : ℝ → ℝ} (hf : Probe a f) : 0 ≤ QDHu f - lamDH a * normSq f := by
  have := lamDH_mul_le hf; linarith

/-- If `w` is pole-free in the ground space and `G w` is pole-free, `G w` is in the ground space
(the dh column of
`G_mem_pole_free`, DegenerateFlat.lean:545). -/
theorem G_mem_pole_freeDH {a : ℝ} (ha : 0 ≤ a) {w : ℝ → ℝ} (hw : w ∈ groundSpaceDH a)
    (hwp : poleR w a = 0) (hGp : poleR (Gpole w a) a = 0) : Gpole w a ∈ groundSpaceDH a := by
  have hP := Gpole_probe hw.1 ha hwp
  refine ⟨hP, ?_⟩
  have key := Gpole_annihilatesDH ha hw hP hGp
  show QDHu (Gpole w a) = lamDH a * normSq (Gpole w a)
  rw [QDHu_eq_bilDH hP, normSq_eq_xcorr hP.memL2]
  linarith

/-- **Rank-one step** (the dh column of `G_mem_partner`, DegenerateFlat.lean:559). If `w` is
pole-free in the ground space and some ground-space element `k` has `k̂(i/2) ≠ 0`, then `G w` is in
the ground space. -/
theorem G_mem_partnerDH {a : ℝ} (ha : 0 ≤ a) {w k : ℝ → ℝ} (hw : w ∈ groundSpaceDH a)
    (hwp : poleR w a = 0) (hk : k ∈ groundSpaceDH a) (hkp : poleR k a ≠ 0) :
    Gpole w a ∈ groundSpaceDH a := by
  set H := Gpole w a
  have hP : Probe a H := Gpole_probe hw.1 ha hwp
  set s := -(poleR H a / poleR k a)
  set f : ℝ → ℝ := fun t => H t + s * k t
  have hf : Probe a f := probe_add_smul hP hk.1 s
  have hfp : poleR f a = 0 := by
    simp only [f]
    rw [poleR_add hP.memL2 (hk.1.memL2.const_mul s) a, poleR_smul]
    simp only [s]; field_simp; ring
  have hB : bilDH a H f - lamDH a * xcorr H f 0 = 0 := Gpole_annihilatesDH ha hw hf hfp
  have hexp := QlamDH_add_smul hP hf (-1)
  have hfun : (fun t => H t + (-1) * f t) = fun t => (-s) * k t := by
    funext t; simp only [f]; ring
  rw [hfun, QDHu_smul, normSq_smul, hB] at hexp
  have hk0 : QDHu k - lamDH a * normSq k = 0 := by
    have : QDHu k = lamDH a * normSq k := hk.2
    rw [this]; ring
  have e0 : (-s) ^ 2 * QDHu k - lamDH a * ((-s) ^ 2 * normSq k) = 0 := by
    linear_combination (-s) ^ 2 * hk0
  have n1 := QlamDH_nonneg hP
  have n2 := QlamDH_nonneg hf
  exact ⟨hP, show QDHu H = lamDH a * normSq H by nlinarith⟩

/-! ### The ground space in `L²` -/

/-- The ground space of `QDHu` mapped into `L²` (the dh column of `iotaGS`, StructureD.lean:32). -/
abbrev iotaGSDH (a : ℝ) : groundSpaceDH a →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) := iotaOf QDHu_form a

theorem norm_iotaGSDH_sq {a : ℝ} (x : groundSpaceDH a) : ‖iotaGSDH a x‖ ^ 2 = normSq x.1 := by
  show ‖x.2.1.memL2.toLp x.1‖ ^ 2 = _
  rw [L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [x.2.1.memL2.coeFn_toLp] with t ht
  rw [ht]

theorem MDH_nonneg (a : ℝ) : 0 ≤ MDH a := by
  unfold MDH
  have : 0 ≤ ∑ n ∈ Finset.range (primeCut a), |fDH n / Real.sqrt n| :=
    Finset.sum_nonneg fun n _ => abs_nonneg _
  positivity

theorem tailDH_nonneg (a : ℝ) : 0 ≤ tailDH a := by
  unfold tailDH
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  simp only [Set.indicator_apply]
  split_ifs
  · exact (archKer_pos (1 / 4) hu).le
  · exact le_rfl

theorem nonArchDH_ge' {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) :
    -(MDH a * normSq g) ≤ nonArchDH a g := by
  have hP := abs_primeDH_le hp
  have hN := normSq_nonneg g
  have hc : -(|constDH| * normSq g) ≤ constDH * normSq g := by
    rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le _) hN
  have h2 := le_abs_self
    (∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr g (Real.log n))
  unfold nonArchDH MDH
  nlinarith

/-- The archimedean energy of a ground-space element is controlled by its norm (the dh column of
`archE_le_of_mem`, StructureD.lean:42, through `archE_le_DH`). -/
theorem archE_le_of_memDH {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : g ∈ groundSpaceDH a) :
    archE g ≤ (Real.exp (2 * a) * (|lamDH a| + MDH a) + tailDH a) * normSq g := by
  have hq : QDHu g = lamDH a * normSq g := hg.2
  have hN := normSq_nonneg g
  have h1 := archE_le_DH ha hg.1
  have e := QDHu_eq_nonArch (a := a) hg.1.supp
  have hA : archEQ (3 / 4) g ≤ (|lamDH a| + MDH a) * normSq g := by
    have hl : lamDH a * normSq g ≤ |lamDH a| * normSq g :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hN
    have := nonArchDH_ge' hg.1
    rw [hq] at e
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left hA (Real.exp_pos (2 * a)).le
  nlinarith

/-- **The ground space of `QDHu` is finite-dimensional** (its image in `L²`; the dh column of
`finiteDimensional_groundL2`, StructureD.lean:56). -/
theorem finiteDimensional_groundL2DH {a : ℝ} (ha : 0 < a) :
    FiniteDimensional ℝ (LinearMap.range (iotaGSDH a)) := by
  by_contra hfin
  obtain ⟨R, f, hR, hfR, hsep⟩ :=
    exists_seq_norm_le_one_le_norm_sub (𝕜 := ℝ) (E := LinearMap.range (iotaGSDH a)) hfin
  have hx : ∀ n, ∃ x : groundSpaceDH a, iotaGSDH a x = (f n : Lp ℝ 2 volume) :=
    fun n => LinearMap.mem_range.1 (f n).2
  choose x hxf using hx
  set h : ℕ → ℝ → ℝ := fun n => (x n).1
  have hp : ∀ n, Probe a (h n) := fun n => (x n).2.1
  have hN : ∀ n, normSq (h n) ≤ R ^ 2 := by
    intro n
    rw [← norm_iotaGSDH_sq, hxf n, Submodule.norm_coe]
    exact pow_le_pow_left₀ (norm_nonneg _) (hfR n) 2
  set K := Real.exp (2 * a) * (|lamDH a| + MDH a) + tailDH a
  have hK : 0 ≤ K := by
    have := MDH_nonneg a
    have := tailDH_nonneg a
    positivity
  have hC : ∀ n, archE (h n) ≤ K * R ^ 2 :=
    fun n => (archE_le_of_memDH ha (x n).2).trans (mul_le_mul_of_nonneg_left (hN n) hK)
  obtain ⟨φ, hφ, G, hG, hlim⟩ := exists_convergent_subseq ha hp hN hC
  have hconv := tendsto_toLp (fun j => (hp (φ j)).memL2) hG hlim
  have hcau := hconv.cauchySeq
  obtain ⟨N, hN'⟩ := Metric.cauchySeq_iff'.1 hcau 1 one_pos
  have hd := hN' (N + 1) (by omega)
  have hsep' := hsep (show φ (N + 1) ≠ φ N from (hφ (Nat.lt_succ_self N)).ne')
  have e1 : ((hp (φ (N + 1))).memL2.toLp (h (φ (N + 1)))) = (f (φ (N + 1)) : Lp ℝ 2 volume) :=
    hxf _
  have e2 : ((hp (φ N)).memL2.toLp (h (φ N))) = (f (φ N) : Lp ℝ 2 volume) := hxf _
  rw [dist_eq_norm, e1, e2, ← Submodule.coe_sub, Submodule.norm_coe] at hd
  linarith

/-! ### `QDHu` as a ground-state family

Everything from the Green chains to Theorem D and the top-of-chain ground state is
`GroundChain.lean`'s, at the instance `dhGD` (round 274; rounds 268's stage 4 was a renamed copy of
`StructureD`). -/

/-- **The Davenport–Heilbronn form as a ground-state family.** -/
def dhGD : GroundData where
  Q := fun _ => QDHu
  form := QDHu_form
  partner := fun ha hw hwp hk hkp => G_mem_partnerDH ha hw hwp hk hkp
  poleFree := fun ha hw hwp hGp => G_mem_pole_freeDH ha hw hwp hGp
  green := fun ha hg hw hσ => green_mem_groundSpaceDH ha hg hw hσ
  fd := fun ha => finiteDimensional_groundL2DH ha
  nonzero := fun ha => by
    obtain ⟨g, hg⟩ := exists_groundStateDH ha
    exact ⟨g, (isGroundStateDH_iff.1 hg).1, (isGroundStateDH_iff.1 hg).2⟩

/-- `f` starts a Green chain of length `j` in `V_dh` (the dh column of `IsChain`). -/
abbrev IsChainDH (a : ℝ) (j : ℕ) (f : ℝ → ℝ) : Prop := dhGD.IsChain a j f

/-- The dimension of the ground space of `QDHu` (the dh column of `gdim`). -/
abbrev gdimDH (a : ℝ) : ℕ := dhGD.gdim a

/-- The chain as vectors of `V_dh`. -/
abbrev chainVecDH {a : ℝ} {j : ℕ} {w : ℝ → ℝ} (hc : IsChainDH a j w) (i : Fin (j + 1)) :
    groundSpaceDH a :=
  dhGD.chainVec hc i

/-- **Round 48's Theorem D for `QDHu`** (the dh column of `theoremD`). With `m = dim V_dh`
(finite), there is a nonzero `w` whose Green chain `w, Gw, …, G^{m−1}w` lies in `V_dh` (all but the
last pole-free), is linearly independent, and spans it a.e.; every zero `ω` of `ĥ`, `h = G^{m−1}w`,
has `ω² ∈ ℝ`. -/
theorem theoremDDH {a : ℝ} (ha : 0 < a) :
    ∃ w, IsChainDH a (gdimDH a - 1) w ∧ 0 < normSq w ∧
      (∃ hc : IsChainDH a (gdimDH a - 1) w,
        LinearIndependent ℝ (fun i => (iotaGSDH a).rangeRestrict (chainVecDH hc i))) ∧
      (∀ v ∈ groundSpaceDH a, ∃ c : Fin (gdimDH a - 1 + 1) → ℝ,
        v =ᵐ[volume] fun x => ∑ i, c i * Gi a i w x) ∧
      ∀ ω : ℂ, ghatC (Gi a (gdimDH a - 1) w) a ω = 0 → (ω ^ 2).im = 0 :=
  dhGD.theoremD ha

/-! ### The top-of-chain ground state -/

/-- A nonzero `w` with a full-length Green chain in `V_dh`. -/
abbrev chainBaseDH (a : ℝ) : ℝ → ℝ := dhGD.chainBase a

/-- **The top-of-chain ground state of `QDHu`**: `G^{m−1}w`, normalised (the dh column of `topGS`). -/
abbrev topGSDH (a : ℝ) : ℝ → ℝ := dhGD.topGS a

/-- The top of the chain is a ground state of `QDHu` (the dh column of `topGS_isGroundState`). -/
theorem topGSDH_isGroundState {a : ℝ} (ha : 0 < a) : IsGroundStateDH a (topGSDH a) :=
  isGroundStateDH_iff.2 (dhGD.topGS_mem ha)

/-- **Every zero of the top-of-chain ground state's transform lies on `ℝ ∪ iℝ`**, at every support
`a > 0`, with no simplicity assumption (the dh column of `topGS_cross`). -/
theorem topGSDH_cross {a : ℝ} (ha : 0 < a) (z : ℂ) (hz : ghatC (topGSDH a) a z = 0) :
    z.re = 0 ∨ z.im = 0 :=
  dhGD.topGS_cross ha z hz

/-- **The chain for `dh` with simplicity removed** (the dh column of `rh_of_hypConv_top`,
StructureD.lean:192): `HypConvDH` for the top-of-chain ground states gives `DHRHcross`. -/
theorem dhRHcross_of_hypConv_top {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hconv : HypConvDH a fun n => topGSDH (a n)) : DHRHcross :=
  dhRHcross_of_cross (fun n => (probe_integrable (topGSDH_isGroundState (ha n)).1).intervalIntegrable)
    (Eventually.of_forall fun n z hz => topGSDH_cross (ha n) z hz) hconv

/-- **`HypConvDH` fails for the top-of-chain ground states of `QDHu`**, at every sequence of positive
supports (`dh_offline_nonreal_zero`, DHOffCross.lean, through `not_hypConvDH_of_cross`); like the
target statement, it assumes no `a_n → ∞`. -/
theorem not_hypConvDH_top {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) :
    ¬ HypConvDH a (fun n => topGSDH (a n)) :=
  not_hypConvDH_of_cross
    (fun n => (probe_integrable (topGSDH_isGroundState (ha n)).1).intervalIntegrable)
    (Eventually.of_forall fun n z hz => topGSDH_cross (ha n) z hz)

/-- If the ground states `g n` of `QDHu` are eventually simple, they agree with the top-of-chain
ground states up to scalars, so `HypConvDH` transfers (the dh column of `hypConv_top_of_simple`,
StructureD.lean:199). -/
theorem hypConvDH_top_of_simple {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hsimple : ∀ᶠ n in atTop, SimpleGroundDH (a n) (g n)) (hconv : HypConvDH a g) :
    HypConvDH a fun n => topGSDH (a n) := by
  have heq : ∀ᶠ n in atTop, ∀ z : ℂ,
      ghatC (topGSDH (a n)) (a n) z / ghatC (topGSDH (a n)) (a n) 0
        = ghatC (g n) (a n) z / ghatC (g n) (a n) 0 := by
    filter_upwards [hsimple] with n hs z
    obtain ⟨c, hcg⟩ := hs.2 _ (isGroundStateDH_iff.1 (topGSDH_isGroundState (ha n))).1
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := normSq_congr_ae hcg
      rw [(topGSDH_isGroundState (ha n)).2.1] at this
      simp [Pilot1ca.normSq] at this
    rw [ghatC_congr_ae hcg, ghatC_congr_ae hcg, ghatC_smul, ghatC_smul,
      mul_div_mul_left _ _ (by exact_mod_cast hc0)]
  intro u hu x
  obtain ⟨t, ht, hev⟩ := hconv u hu x
  refine ⟨t, ht, ?_⟩
  filter_upwards [hev, heq] with n hn he y hy
  rw [he y]; exact hn y hy

end PsiOmega

#print axioms PsiOmega.isGroundStateDH_iff
#print axioms PsiOmega.archE_le_DH
#print axioms PsiOmega.arch_of_archQ
#print axioms PsiOmega.exists_min_QDHu
#print axioms PsiOmega.exists_groundStateDH
#print axioms PsiOmega.exists_groundStatesDH
#print axioms PsiOmega.QDHu_add_smul
#print axioms PsiOmega.bilDH_polar
#print axioms PsiOmega.euler_lagrangeDH_mem
#print axioms PsiOmega.euler_lagrangeDH
#print axioms PsiOmega.split_mem_groundSpaceDH
#print axioms PsiOmega.zero_swap_falseDH
#print axioms PsiOmega.zeros_real_or_imagDH
#print axioms PsiOmega.zeros_real_or_imagDH'
#print axioms PsiOmega.dhRHcross_of_eventually_simple
#print axioms PsiOmega.not_simple_hypConvDH
#print axioms PsiOmega.swap_pair_memDH
#print axioms PsiOmega.green_mem_groundSpaceDH
#print axioms PsiOmega.Gpole_annihilatesDH
#print axioms PsiOmega.G_mem_partnerDH
#print axioms PsiOmega.finiteDimensional_groundL2DH
#print axioms PsiOmega.theoremDDH
#print axioms PsiOmega.topGSDH_isGroundState
#print axioms PsiOmega.topGSDH_cross
#print axioms PsiOmega.dhRHcross_of_hypConv_top
#print axioms PsiOmega.not_hypConvDH_top
#print axioms PsiOmega.hypConvDH_top_of_simple
