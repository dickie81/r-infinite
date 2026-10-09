import Mathlib
import GroundIndex
import FirstFailure
import SimpleCover

/-! # The ground space as a negative block of Weil's form (round 252)

A ground state minimises the full Weil form `Q` (`IsGroundState`, Roadmap.lean), so when `λ₁(a) < 0`
the ground space is a space on which `Q = λ₁‖·‖² < 0`. Its Green chain `w, Gw, …, G^{m−1}w`
(round 54, StructureD.lean) supplies the regularity Weil's explicit formula needs: `Ĝf = −f̂/(z² + ¼)`
(`Gpole_hat`, round 53) makes every Green image a strip-test probe (`striptest_Gpole`), so the chain
above its base is a `(gdim a − 1)`-dimensional negative-definite space of strip-test probes
(`exists_ground_block`). Round 229's count then reads `gdim a − 1 ≤ #quadruples` wherever `λ₁ < 0`
(`gdim_sub_one_le_quadruples`), and round 251's join gives `gdim ≤ ⌊(M − 1)/2⌋ + 1` under (a) with
an eventual bound `M` (`gdim_le_of_lam_neg`).

If RH fails, `λ₁(a n) < 0` eventually along `a n → ∞` (`exists_lam_neg_of_not_RH`, round 161, and
`lam_antitone`, round 47), so the bound descends, `M ↦ ⌊(M − 1)/2⌋ + 1 < M` for `M ≥ 3`, until
round 56's `rh_of_dim_le_two` closes:

* `rh_of_dim_bounded`: **(a) and any eventual bound on the ground-space dimension give RH**, along
  supports `a n → ∞`; round 56's `M ≤ 2` becomes every `M`.
* `rh_or_gdim_tendsto`: **(a) alone, along `a n → ∞`, gives RH or `gdim (a n) → ∞`**.

Bearing on RH: as for the other (a)-chains, (a) is the open input. What changes is the second input:
eventual simplicity (round 46), `dim ≤ 2` (round 56) and the parity gap (round 137) were each sufficient with (a);
now any bound on the dimension is, and without one, (a) forces `gdim → ∞` unless RH holds.
-/

open Real Complex MeasureTheory Filter Set

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-! ## The transform of a Green image is a strip test function -/

/-- On the strip `|Im z| ≤ 1` with `|Re z| ≥ 1`, `|z² + ¼| ≥ (1 + Re² z)/8`. -/
theorem norm_sq_add_quarter_ge {z : ℂ} (hz : z ∈ PilotWeil.strip (-1) 1) (hre : 1 ≤ |z.re|) :
    (1 + z.re ^ 2) / 8 ≤ ‖z ^ 2 - (Complex.I / 2) ^ 2‖ := by
  have e : (Complex.I / 2) ^ 2 = -(1 / 4 : ℂ) := by rw [div_pow, Complex.I_sq]; norm_num
  have h1 : (z ^ 2 - (Complex.I / 2) ^ 2).re = z.re ^ 2 - z.im ^ 2 + 1 / 4 := by
    rw [e, sub_neg_eq_add, Complex.add_re, pow_two, Complex.mul_re]
    norm_num; ring
  have h2 : (z ^ 2 - (Complex.I / 2) ^ 2).re ≤ ‖z ^ 2 - (Complex.I / 2) ^ 2‖ := Complex.re_le_norm _
  have him : z.im ^ 2 ≤ 1 := by obtain ⟨h1', h2'⟩ := hz; nlinarith
  have hx : 1 ≤ z.re ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg z.re]
  linarith

/-- **The transform of a Green image is a strip test function**: `Ĝf = −f̂/(z² + ¼)` off `±i/2`, with
`f̂` bounded on the strip, and `Ĝf` continuous near `±i/2`. -/
theorem striptest_Gpole {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hp : Probe a f) (hpole : poleR f a = 0) :
    ∃ K, StripTest (fun z => ghatC (Gpole f a) a z ^ 2) K := by
  have hGp := Gpole_probe hp ha.le hpole
  have hint : IntervalIntegrable (Gpole f a) volume (-a) a := memLp_intervalIntegrable hGp.memL2 _ _
  have hd := ghatC_differentiable hint
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn
    hd.continuous.continuousOn
  set I₁ := ∫ u in (-a)..a, |f u| with hI₁def
  have hI₁ : 0 ≤ I₁ := intervalIntegral.integral_nonneg (by linarith) fun u _ => abs_nonneg _
  refine ⟨max (2 * B ^ 2) (64 * (Real.exp a * I₁) ^ 2), striptest_sq hd fun z hz => ?_⟩
  rcases le_or_gt |z.re| 1 with hre | hre
  · have hzb : z ∈ Metric.closedBall (0 : ℂ) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have him : |z.im| ≤ 1 := abs_le.2 ⟨hz.1, hz.2⟩
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 2 := by linarith
    have h1 := hB z hzb
    have h2 : 1 + z.re ^ 2 ≤ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg z.re]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans h1
    calc ‖ghatC (Gpole f a) a z‖ ^ 2 * (1 + z.re ^ 2) ≤ B ^ 2 * 2 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2 (by positivity) (by positivity)
      _ = 2 * B ^ 2 := by ring
      _ ≤ max (2 * B ^ 2) (64 * (Real.exp a * I₁) ^ 2) := le_max_left _ _
  · have hden := norm_sq_add_quarter_ge hz hre.le
    have hpos : 0 < (1 + z.re ^ 2) / 8 := by positivity
    have hz2 : z ^ 2 ≠ (Complex.I / 2) ^ 2 := by
      intro h
      rw [h, sub_self, norm_zero] at hden
      linarith
    have hid : ghatC (Gpole f a) a z = -(ghatC f a z / (z ^ 2 - (Complex.I / 2) ^ 2)) :=
      Gpole_hat hp ha.le hpole hz2
    have hnum : ‖ghatC f a z‖ ≤ Real.exp a * I₁ :=
      norm_ghatC_strip_le ha.le (memLp_intervalIntegrable hp.memL2 _ _) (abs_le.2 ⟨hz.1, hz.2⟩)
    have h1 : ‖ghatC (Gpole f a) a z‖ ≤ Real.exp a * I₁ / ((1 + z.re ^ 2) / 8) := by
      rw [hid, norm_neg, norm_div]
      exact div_le_div₀ (by positivity) hnum hpos hden
    have hq : 0 < 1 + z.re ^ 2 := by positivity
    calc ‖ghatC (Gpole f a) a z‖ ^ 2 * (1 + z.re ^ 2)
        ≤ (Real.exp a * I₁ / ((1 + z.re ^ 2) / 8)) ^ 2 * (1 + z.re ^ 2) := by
          gcongr
      _ = 64 * (Real.exp a * I₁) ^ 2 / (1 + z.re ^ 2) := by field_simp; ring
      _ ≤ 64 * (Real.exp a * I₁) ^ 2 := by
          apply div_le_self (by positivity); linarith [sq_nonneg z.re]
      _ ≤ max (2 * B ^ 2) (64 * (Real.exp a * I₁) ^ 2) := le_max_right _ _

/-! ## Finite sums -/

theorem memLp_sum_smul {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, MemLp (f i) 2 volume) (c : ι → ℝ) :
    MemLp (∑ i ∈ s, c i • f i) 2 volume := memLp_finsetSum' s fun i hi => (hf i hi).const_smul (c i)

theorem Gpole_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, MemLp (f i) 2 volume) (c : ι → ℝ) (a : ℝ) :
    Gpole (∑ i ∈ s, c i • f i) a = ∑ i ∈ s, c i • Gpole (f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => funext x; simp [Gpole]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      Gpole_add' ((hf i (Finset.mem_insert_self _ _)).const_smul (c i))
        (memLp_sum_smul s (fun j hj => hf j (Finset.mem_insert_of_mem hj)) c),
      Gpole_smul', ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

theorem poleR_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, MemLp (f i) 2 volume) (c : ι → ℝ) (a : ℝ) :
    poleR (∑ i ∈ s, c i • f i) a = ∑ i ∈ s, c i * poleR (f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [poleR]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h1 := poleR_add ((hf i (Finset.mem_insert_self _ _)).const_smul (c i))
      (memLp_sum_smul s (fun j hj => hf j (Finset.mem_insert_of_mem hj)) c) a
    have h2 : poleR (c i • f i) a = c i * poleR (f i) a := poleR_smul _ _ _
    rw [show poleR (c i • f i + ∑ j ∈ s, c j • f j) a
        = poleR (fun t => (c i • f i) t + (∑ j ∈ s, c j • f j) t) a from rfl, h1, h2,
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

/-! ## The negative block -/

/-- **A ground space with `λ₁ < 0` carries a negative block of `Q` of codimension one**: the Green
images `Gw, …, G^{m−1}w` of a full chain span a `(gdim a − 1)`-dimensional space of strip-test
probes on which `Q = λ₁‖·‖² < 0`. -/
theorem exists_ground_block {a : ℝ} (ha : 0 < a) (hlam : lam a < 0) :
    ∃ V : Submodule ℝ (ℝ → ℝ), FiniteDimensional ℝ V ∧ Module.finrank ℝ V = gdim a - 1 ∧
      (∀ v ∈ V, Probe a v) ∧ (∀ v ∈ V, ∃ K, StripTest (fun z => ghatC v a z ^ 2) K) ∧
      ∀ v ∈ V, v ≠ 0 → weilQ a v < 0 := by
  classical
  obtain ⟨hc, hpos⟩ := chainBase_spec ha
  set w := chainBase a with hw
  set m := gdim a with hm
  have hli0 := chain_linearIndependent ha hc hpos
  have hli1 : LinearIndependent ℝ
      (fun i : Fin (m - 1) => (iotaGS a).rangeRestrict (chainVec hc i.succ)) :=
    hli0.comp Fin.succ (Fin.succ_injective _)
  have hli2 : LinearIndependent ℝ (fun i : Fin (m - 1) => chainVec hc i.succ) :=
    LinearIndependent.of_comp (iotaGS a).rangeRestrict hli1
  have hli3 : LinearIndependent ℝ (fun i : Fin (m - 1) => ((chainVec hc i.succ : groundSpace a) : ℝ → ℝ)) :=
    hli2.map' (groundSpace a).subtype (Submodule.ker_subtype _)
  set V : Submodule ℝ (ℝ → ℝ) :=
    Submodule.span ℝ (Set.range fun i : Fin (m - 1) => ((chainVec hc i.succ : groundSpace a) : ℝ → ℝ))
    with hV
  have hle : V ≤ groundSpace a :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun i => (chainVec hc i.succ).2)
  have hfd : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hrank : Module.finrank ℝ V = m - 1 := by
    rw [hV, finrank_span_eq_card hli3, Fintype.card_fin]
  have hmem : ∀ i : Fin (m - 1), Gi a i w ∈ groundSpace a :=
    fun i => hc.1 i (by omega)
  have hpole : ∀ i : Fin (m - 1), poleR (Gi a i w) a = 0 := fun i => hc.2 i i.2
  refine ⟨V, hfd, hrank, fun v hv => (hle hv).1, fun v hv => ?_, fun v hv hv0 => ?_⟩
  · -- strip test: `v = G u` for the pole-free ground-space element `u`
    obtain ⟨c, hcv⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
    set u : ℝ → ℝ := ∑ i : Fin (m - 1), c i • Gi a i w with hu
    have hu_mem : u ∈ groundSpace a :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)
    have hu_pole : poleR u a = 0 := by
      rw [hu, poleR_sum _ (fun i _ => (hmem i).1.memL2)]
      exact Finset.sum_eq_zero fun i _ => by rw [hpole i, mul_zero]
    have hvu : v = Gpole u a := by
      rw [← hcv, hu, Gpole_sum _ (fun i _ => (hmem i).1.memL2)]
      refine Finset.sum_congr rfl fun i _ => ?_
      show c i • (chainVec hc i.succ : ℝ → ℝ) = c i • Gpole (Gi a i w) a
      rw [← Gi_succ]; rfl
    rw [hvu]
    exact striptest_Gpole ha hu_mem.1 hu_pole
  · -- negativity: `Q v = λ₁‖v‖²` with `‖v‖ > 0` by independence in `L²`
    obtain ⟨c, hcv⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
    set y : groundSpace a := ∑ i : Fin (m - 1), c i • chainVec hc i.succ with hy
    have hyv : (y : ℝ → ℝ) = v := by
      rw [← hcv, hy, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
    have hQ : weilQ a v = lam a * normSq v := (hle hv).2
    have hne : iotaGS a y ≠ 0 := by
      intro h0
      have h2 : (iotaGS a).rangeRestrict y = 0 := by apply Subtype.ext; exact h0
      have h3 : ∑ i : Fin (m - 1), c i • (iotaGS a).rangeRestrict (chainVec hc i.succ) = 0 := by
        rw [← h2, hy, map_sum]; simp only [map_smul]
      have hc0 := Fintype.linearIndependent_iff.1 hli1 c h3
      apply hv0
      rw [← hcv]
      exact Finset.sum_eq_zero fun i _ => by rw [hc0 i, zero_smul]
    have hN : 0 < normSq v := by
      rw [← hyv, ← norm_iotaGS_sq]
      exact pow_pos (norm_pos_iff.2 hne) 2
    rw [hQ]
    exact mul_neg_of_neg_of_pos hlam hN

/-- **`gdim − 1` is at most the number of off-line quadruples** wherever `λ₁ < 0`: round 229's count
applied to the ground block. -/
theorem gdim_sub_one_le_quadruples {a : ℝ} (ha : 0 < a) (hlam : lam a < 0)
    (R : Finset (Σ w : NontrivialZero, Fin (zeroMult w)))
    (hR : ∀ i, (zetaZeroFamily i).re = 1 / 2 ∨ ∃ r ∈ R,
      let t := (zetaZeroFamily i - 1 / 2) / Complex.I
      let w := (zetaZeroFamily r - 1 / 2) / Complex.I
      t = w ∨ t = -w ∨ t = (starRingEnd ℂ) w ∨ t = -(starRingEnd ℂ) w) :
    gdim a - 1 ≤ R.card := by
  obtain ⟨V, hfd, hrank, hV, hS, hneg⟩ := exists_ground_block ha hlam
  rw [← hrank]
  exact finrank_le_quadruples_zeta V ha hV hS hneg R hR

/-- **Under the join, `λ₁ < 0` forces `gdim ≤ ⌊(M − 1)/2⌋ + 1`.** -/
theorem gdim_le_of_lam_neg {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {M : ℕ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ M)
    (hconv : HypConv a g) (n : ℕ) (hn : lam (a n) < 0) : gdim (a n) ≤ (M - 1) / 2 + 1 := by
  obtain ⟨V, hfd, hrank, hV, hS, hneg⟩ := exists_ground_block (ha n) hn
  have := finrank_le_ground_index ha hgs hdim hconv (ha n) V hV hS hneg
  omega

/-- **RH from (a) and any eventual dimension bound**, along supports `a n → ∞`: if RH fails,
`λ₁(a n) < 0` eventually (`exists_lam_neg_of_not_RH`, `lam_antitone`), so the bound `M` descends to
`⌊(M − 1)/2⌋ + 1 < M` until `M ≤ 2`, where `rh_of_dim_le_two` closes. -/
theorem rh_of_dim_bounded {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {M : ℕ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ M)
    (hconv : HypConv a g) (hlim : Tendsto a atTop atTop) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨a₀, ha₀, hneg⟩ := exists_lam_neg_of_not_RH hRH
  have hlam : ∀ᶠ n in atTop, lam (a n) < 0 :=
    (hlim.eventually_ge_atTop a₀).mono fun n hn => (lam_antitone ha₀ hn).trans_lt hneg
  have key : ∀ M : ℕ, (∀ᶠ n in atTop, gdim (a n) ≤ M) → False := by
    intro M
    induction M using Nat.strong_induction_on with
    | _ M ih =>
      intro hdim
      by_cases hM : M ≤ 2
      · exact hRH (rh_of_dim_le_two ha hgs (hdim.mono fun n hn => hn.trans hM) hconv)
      · refine ih ((M - 1) / 2 + 1) (by omega) ?_
        filter_upwards [hlam] with n hn
        exact gdim_le_of_lam_neg ha hgs hdim hconv n hn
  exact key M hdim

/-- (a) passes to subsequences. -/
theorem hypConv_comp {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (h : HypConv a g) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : HypConv (a ∘ φ) (g ∘ φ) := fun u hu x => by
  obtain ⟨t, ht, hev⟩ := h u hu x
  exact ⟨t, ht, hφ.tendsto_atTop.eventually hev⟩

/-- **The dichotomy**: along supports `a n → ∞`, (a) gives RH or `gdim (a n) → ∞`. -/
theorem rh_or_gdim_tendsto {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hconv : HypConv a g)
    (hlim : Tendsto a atTop atTop) :
    RiemannHypothesis ∨ Tendsto (fun n => gdim (a n)) atTop atTop := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  right
  rw [Filter.tendsto_atTop]
  intro M
  by_contra h
  rw [Filter.not_eventually] at h
  obtain ⟨φ, hφ, hφM⟩ := Filter.extraction_of_frequently_atTop h
  exact hRH (rh_of_dim_bounded (a := a ∘ φ) (g := g ∘ φ) (M := M) (fun n => ha _)
    (fun n => hgs _) (Eventually.of_forall fun n => (not_le.1 (hφM n)).le)
    (hypConv_comp hconv hφ) (hlim.comp hφ.tendsto_atTop))

end Pilot1ca

#print axioms Pilot1ca.striptest_Gpole
#print axioms Pilot1ca.exists_ground_block
#print axioms Pilot1ca.gdim_sub_one_le_quadruples
#print axioms Pilot1ca.gdim_le_of_lam_neg
#print axioms Pilot1ca.rh_of_dim_bounded
#print axioms Pilot1ca.rh_or_gdim_tendsto
