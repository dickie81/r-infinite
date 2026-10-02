import Mathlib
import Roadmap

/-! # Step (iii): Theorem 1bu(ii)'s limit shape, and the chain to `RiemannHypothesis`

Theorem 1bu(ii): with Hadamard's factorisations `ĝ₁(r) = ĝ₁(0)Π_τ(1 − r²/τ²)` and
`Ξ(r) = Ξ(0)Π_γ(1 − r²/γ²)` over zero pairs, Hypothesis D (the two zero multisets agree below `T_D`)
and `ε(δ) = Σ_{|τ|≥T_D}|τ|⁻² + Σ_{γ≥T_D}γ⁻² → 0`, the ground state's transform converges to `Ξ`
locally uniformly.

Here the factorisations are written in the variable `w = τ⁻²` (`HadamardW`: the factor is `1 − z²w`,
so a padding entry `w = 0` is the factor `1`). The comparison is over a *pairing* of the two zero
lists on one index type, and the error is `θ = Σ‖w_i − v_i‖`. Hypothesis D with tails `ε` is the
special case where the pairing matches the zeros below `T_D` exactly, so those entries contribute `0`
and `θ ≤ ε`. But `θ → 0` also allows zeros displaced by a summable amount — the dodging
tolerance — which exact D does not.

* `norm_tprod_sub_tprod_le`: `‖Π(1 + x_i) − Π(1 + y_i)‖ ≤ exp(Σ‖x‖ + Σ‖y‖)·Σ‖x_i − y_i‖`.
* `hadamard_compare`: `‖f(z)/f(0) − g(z)/g(0)‖ ≤ ‖z‖²·exp(‖z‖²(Σ‖w‖ + Σ‖v‖))·Σ‖w_i − v_i‖`.
* `tendstoLocallyUniformly_of_pairing`: 1bu(ii)'s convergence `ĝ_n/ĝ_n(0) → Ξ/Ξ(0)`.
* `rh_of_pairing_and_realRooted`: with real-rootedness at every support (item 6), Mathlib's
  `RiemannHypothesis`. Named input: Hadamard's factorisations. -/

open Real Filter Topology Complex

noncomputable section

namespace Pilot1ca

/-! ## Products -/

theorem norm_prod_one_add_le {ι : Type*} (t : Finset ι) (y : ι → ℂ) :
    ‖∏ i ∈ t, (1 + y i)‖ ≤ Real.exp (∑ i ∈ t, ‖y i‖) := by
  rw [Real.exp_sum]
  refine (Finset.norm_prod_le _ _).trans ?_
  gcongr with i _
  calc ‖1 + y i‖ ≤ 1 + ‖y i‖ := by simpa using norm_add_le (1 : ℂ) (y i)
    _ ≤ Real.exp ‖y i‖ := by linarith [Real.add_one_le_exp ‖y i‖]

theorem norm_prod_sub_prod_le {ι : Type*} (t : Finset ι) (x y : ι → ℂ) :
    ‖∏ i ∈ t, (1 + x i) - ∏ i ∈ t, (1 + y i)‖
      ≤ Real.exp (∑ i ∈ t, (‖x i‖ + ‖y i‖)) * ∑ i ∈ t, ‖x i - y i‖ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj IH =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj,
      Real.exp_add]
    set P := ∏ i ∈ t, (1 + x i)
    set Q := ∏ i ∈ t, (1 + y i)
    set E := Real.exp (∑ i ∈ t, (‖x i‖ + ‖y i‖))
    set D := ∑ i ∈ t, ‖x i - y i‖
    have hE : 0 ≤ E := Real.exp_nonneg _
    have hQ : ‖Q‖ ≤ E := by
      refine (norm_prod_one_add_le t y).trans (Real.exp_le_exp.2 ?_)
      exact Finset.sum_le_sum fun i _ => by linarith [norm_nonneg (x i)]
    have e : (1 + x j) * P - (1 + y j) * Q = (1 + x j) * (P - Q) + (x j - y j) * Q := by ring
    have h1 : ‖1 + x j‖ ≤ Real.exp (‖x j‖ + ‖y j‖) := by
      calc ‖1 + x j‖ ≤ 1 + ‖x j‖ := by simpa using norm_add_le (1 : ℂ) (x j)
        _ ≤ Real.exp ‖x j‖ := by linarith [Real.add_one_le_exp ‖x j‖]
        _ ≤ _ := Real.exp_le_exp.2 (by linarith [norm_nonneg (y j)])
    have h2 : 1 ≤ Real.exp (‖x j‖ + ‖y j‖) :=
      Real.one_le_exp (by positivity)
    rw [e]
    calc ‖(1 + x j) * (P - Q) + (x j - y j) * Q‖
        ≤ ‖1 + x j‖ * ‖P - Q‖ + ‖x j - y j‖ * ‖Q‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ Real.exp (‖x j‖ + ‖y j‖) * (E * D) + ‖x j - y j‖ * (Real.exp (‖x j‖ + ‖y j‖) * E) := by
          gcongr
          exact hQ.trans (le_mul_of_one_le_left hE h2)
      _ = Real.exp (‖x j‖ + ‖y j‖) * E * (‖x j - y j‖ + D) := by ring

/-- **`‖Π(1 + x_i) − Π(1 + y_i)‖ ≤ exp(Σ‖x‖ + Σ‖y‖)·Σ‖x_i − y_i‖`** for absolutely summable `x, y`. -/
theorem norm_tprod_sub_tprod_le {ι : Type*} {x y : ι → ℂ} (hx : Summable fun i => ‖x i‖)
    (hy : Summable fun i => ‖y i‖) :
    ‖(∏' i, (1 + x i)) - ∏' i, (1 + y i)‖
      ≤ Real.exp ((∑' i, ‖x i‖) + ∑' i, ‖y i‖) * ∑' i, ‖x i - y i‖ := by
  have hxy : Summable fun i => ‖x i - y i‖ :=
    (hx.add hy).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_sub_le _ _)
  have hpx := (multipliable_one_add_of_summable hx).hasProd
  have hpy := (multipliable_one_add_of_summable hy).hasProd
  have ht : Tendsto (fun t : Finset ι => ‖∏ i ∈ t, (1 + x i) - ∏ i ∈ t, (1 + y i)‖) atTop
      (𝓝 ‖(∏' i, (1 + x i)) - ∏' i, (1 + y i)‖) := (hpx.sub hpy).norm
  refine le_of_tendsto' ht fun t => (norm_prod_sub_prod_le t x y).trans ?_
  gcongr
  · rw [Finset.sum_add_distrib]
    exact add_le_add (hx.sum_le_tsum t fun i _ => norm_nonneg _)
      (hy.sum_le_tsum t fun i _ => norm_nonneg _)
  · exact hxy.sum_le_tsum t fun i _ => norm_nonneg _

/-! ## Hadamard's factorisation (the named input) and the comparison -/

/-- **Hadamard's factorisation of an even entire function over its zero pairs**, in the variable
`w = τ⁻²` (named input): `f(0) ≠ 0`, `Σ‖w_i‖ < ∞`, and `f(z) = f(0)Π_i(1 − z²w_i)` for every `z`.
Entries `w_i = 0` are padding (factor `1`). -/
structure HadamardW {ι : Type*} (f : ℂ → ℂ) (w : ι → ℂ) : Prop where
  f0 : f 0 ≠ 0
  summ : Summable fun i => ‖w i‖
  prod : ∀ z, HasProd (fun i => 1 - z ^ 2 * w i) (f z / f 0)

theorem HadamardW.eq_tprod {ι : Type*} {f : ℂ → ℂ} {w : ι → ℂ} (h : HadamardW f w) (z : ℂ) :
    f z / f 0 = ∏' i, (1 + -(z ^ 2 * w i)) := by
  rw [(h.prod z).tprod_eq.symm]
  congr 1

theorem summable_scaled {ι : Type*} {w : ι → ℂ} (hw : Summable fun i => ‖w i‖) (z : ℂ) :
    Summable fun i => ‖-(z ^ 2 * w i)‖ := by
  simpa [norm_neg, norm_mul, norm_pow] using hw.mul_left (‖z‖ ^ 2)

/-- **The comparison of two factorisations over one pairing**:
`‖f(z)/f(0) − g(z)/g(0)‖ ≤ ‖z‖²·exp(‖z‖²(Σ‖w‖ + Σ‖v‖))·Σ‖w_i − v_i‖`. -/
theorem hadamard_compare {ι : Type*} {f g : ℂ → ℂ} {w v : ι → ℂ} (hf : HadamardW f w)
    (hg : HadamardW g v) (z : ℂ) :
    ‖f z / f 0 - g z / g 0‖
      ≤ ‖z‖ ^ 2 * Real.exp (‖z‖ ^ 2 * ((∑' i, ‖w i‖) + ∑' i, ‖v i‖)) * ∑' i, ‖w i - v i‖ := by
  rw [hf.eq_tprod, hg.eq_tprod]
  refine (norm_tprod_sub_tprod_le (summable_scaled hf.summ z) (summable_scaled hg.summ z)).trans ?_
  have e1 : ∀ u : ι → ℂ, (∑' i, ‖-(z ^ 2 * u i)‖) = ‖z‖ ^ 2 * ∑' i, ‖u i‖ := by
    intro u
    rw [← tsum_mul_left]; congr 1; funext i; simp [norm_pow]
  have e2 : (∑' i, ‖-(z ^ 2 * w i) - -(z ^ 2 * v i)‖) = ‖z‖ ^ 2 * ∑' i, ‖w i - v i‖ := by
    rw [← tsum_mul_left]; congr 1; funext i
    rw [show -(z ^ 2 * w i) - -(z ^ 2 * v i) = -(z ^ 2 * (w i - v i)) by ring]
    simp [norm_pow]
  rw [e1, e1, e2, mul_add]
  apply le_of_eq; ring

/-! ## 1bu(ii): the convergence to `Ξ` -/

/-- **Theorem 1bu(ii), the limit shape.** For each support `n`, let `F n` (the ground state's
transform) and `Ξ` have Hadamard factorisations over one pairing `w n`, `v n` of their zero lists.
Suppose the sums `Σ‖w n‖` are bounded and the pairing error `θ n = Σ‖w n i − v n i‖` tends to `0`.
(Under D, this is the tails' `ε(δ) → 0`.) Then `F n / F n(0) → Ξ/Ξ(0)` locally uniformly. -/
theorem tendstoLocallyUniformly_of_pairing {ι : ℕ → Type*} {F : ℕ → ℂ → ℂ}
    {w v : ∀ n, ι n → ℂ} (hF : ∀ n, HadamardW (F n) (w n)) (hX : ∀ n, HadamardW Xi (v n))
    {B : ℝ} (hB : ∀ n, (∑' i, ‖w n i‖) ≤ B) {θ : ℕ → ℝ}
    (hθ : ∀ n, (∑' i, ‖w n i - v n i‖) ≤ θ n) (hθ0 : Tendsto θ atTop (𝓝 0)) :
    TendstoLocallyUniformly (fun n z => F n z / F n 0) (fun z => Xi z / Xi 0) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hR' : ∀ z ∈ K, ‖z‖ ≤ max R 0 := fun z hz => by
    have := hR hz; rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set R0 := max R 0
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  -- the bound `R0² e^{R0²(2B + θ + 1)} θ n → 0`
  set c := R0 ^ 2 * Real.exp (R0 ^ 2 * (2 * B + 1 + 1))
  have hc : 0 ≤ c := by positivity
  have hlim : Tendsto (fun n => c * θ n) atTop (𝓝 0) := by simpa using hθ0.const_mul c
  have hev1 := hlim.eventually (gt_mem_nhds hη)
  have hev2 := hθ0.eventually (gt_mem_nhds one_pos)
  filter_upwards [hev1, hev2] with n h1 h2 z hz
  have hzR := hR' z hz
  have hsw : 0 ≤ ∑' i, ‖w n i‖ := tsum_nonneg fun _ => norm_nonneg _
  have hsv : (∑' i, ‖v n i‖) ≤ B + θ n := by
    have hs : Summable fun i => ‖w n i - v n i‖ :=
      ((hF n).summ.add (hX n).summ).of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun i => norm_sub_le _ _)
    calc (∑' i, ‖v n i‖) ≤ ∑' i, (‖w n i‖ + ‖w n i - v n i‖) :=
          (hX n).summ.tsum_le_tsum (fun i => by
            have := norm_sub_norm_le (v n i) (w n i)
            rw [norm_sub_rev (v n i)] at this; linarith) ((hF n).summ.add hs)
      _ = (∑' i, ‖w n i‖) + ∑' i, ‖w n i - v n i‖ := (hF n).summ.tsum_add hs
      _ ≤ B + θ n := add_le_add (hB n) (hθ n)
  have hθn : 0 ≤ θ n := le_trans (tsum_nonneg fun _ => norm_nonneg _) (hθ n)
  have hcmp := hadamard_compare (hF n) (hX n) z
  rw [dist_comm, dist_eq_norm]
  calc ‖F n z / F n 0 - Xi z / Xi 0‖
      ≤ ‖z‖ ^ 2 * Real.exp (‖z‖ ^ 2 * ((∑' i, ‖w n i‖) + ∑' i, ‖v n i‖)) * ∑' i, ‖w n i - v n i‖ :=
        hcmp
    _ ≤ R0 ^ 2 * Real.exp (R0 ^ 2 * (2 * B + 1 + 1)) * θ n := by
        have hz2 : ‖z‖ ^ 2 ≤ R0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzR 2
        have hsum : (∑' i, ‖w n i‖) + ∑' i, ‖v n i‖ ≤ 2 * B + 1 + 1 := by
          linarith [hB n]
        have hs0 : 0 ≤ (∑' i, ‖w n i‖) + ∑' i, ‖v n i‖ :=
          add_nonneg hsw (tsum_nonneg fun _ => norm_nonneg _)
        gcongr
        exact hθ n
    _ < η := h1

/-! ## The chain to `RiemannHypothesis` -/

/-- **1bu(ii) + item 6, assembled**: ground states at supports `2a n` whose transforms are real-rooted
(item 1(b)) and paired with `Ξ`'s zeros as above give Mathlib's `RiemannHypothesis`.
Named input: Hadamard's factorisations (`HadamardW`), for each `ĝ_n` and for `Ξ`. The pairing
hypothesis is D in its quantitative form: every zero matched within a summable error that tends
to `0`. -/
theorem rh_of_pairing_and_realRooted {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) MeasureTheory.volume (-(a n)) (a n))
    (hRR : ∀ n, RealRooted (a n) (g n))
    {ι : ℕ → Type*} {w v : ∀ n, ι n → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : ∀ n, HadamardW Xi (v n))
    {B : ℝ} (hB : ∀ n, (∑' i, ‖w n i‖) ≤ B) {θ : ℕ → ℝ}
    (hθ : ∀ n, (∑' i, ‖w n i - v n i‖) ≤ θ n) (hθ0 : Tendsto θ atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hconv := tendstoLocallyUniformly_of_pairing hF hX hB hθ hθ0
  have hX0 : Xi 0 ≠ 0 := (hX 0).f0
  -- the limit `Ξ/Ξ(0)` has only real zeros
  have hreal : ∀ z, Xi z / Xi 0 = 0 → z.im = 0 :=
    hurwitz_real (F := fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0)
      (fun n => (ghatC_differentiable (hint n)).div_const _)
      (differentiable_Xi.div_const _) hconv
      ⟨(2 - 1 / 2) / I, by rw [Xi_at_ordinate]; exact div_ne_zero xi_two_ne_zero hX0⟩
      (fun n z h => hRR n z ((div_eq_zero_iff.1 h).resolve_right (hF n).f0))
  intro s hz htriv _
  apply re_eq_half_of_Xi_real
  apply hreal
  rw [Xi_at_ordinate, xi_eq_zero_of_nontrivial ⟨hz, htriv⟩, zero_div]

/-! ## The paper's form: exact Hypothesis D with tails `ε → 0` -/

theorem HadamardW.comp_equiv {ι κ : Type*} {f : ℂ → ℂ} {w : ι → ℂ} (h : HadamardW f w)
    (e : κ ≃ ι) : HadamardW f (w ∘ e) :=
  ⟨h.f0, (e.summable_iff (f := fun i => ‖w i‖)).2 h.summ,
    fun z => (e.hasProd_iff (f := fun i => 1 - z ^ 2 * w i)).2 (h.prod z)⟩

theorem HadamardW.pad {ι : Type*} {f : ℂ → ℂ} {w : ι → ℂ} (h : HadamardW f w) (β : Type*) :
    HadamardW f (Sum.elim w (fun _ : β => (0 : ℂ))) := by
  refine ⟨h.f0, ?_, fun z => ?_⟩
  · have h0 : HasSum ((fun x => ‖Sum.elim w (fun _ : β => (0 : ℂ)) x‖) ∘ Sum.inr) 0 := by
      have : ((fun x => ‖Sum.elim w (fun _ : β => (0 : ℂ)) x‖) ∘ Sum.inr) = fun _ => (0 : ℝ) := by
        funext b; simp
      rw [this]; exact hasSum_zero
    exact (HasSum.sum (f := fun x => ‖Sum.elim w (fun _ : β => (0 : ℂ)) x‖)
      (show HasSum (fun i => ‖w i‖) _ from h.summ.hasSum) h0).summable
  · have h1 : HasProd ((fun x => 1 - z ^ 2 * Sum.elim w (fun _ : β => (0 : ℂ)) x) ∘ Sum.inr) 1 := by
      have : ((fun x => 1 - z ^ 2 * Sum.elim w (fun _ : β => (0 : ℂ)) x) ∘ Sum.inr)
          = fun _ => (1 : ℂ) := by funext b; simp
      rw [this]; exact hasProd_one
    have := HasProd.sum (f := fun x => 1 - z ^ 2 * Sum.elim w (fun _ : β => (0 : ℂ)) x)
      (show HasProd (fun i => 1 - z ^ 2 * w i) _ from h.prod z) h1
    rwa [mul_one] at this

/-- **Hypothesis D in family form** (Theorem 1bu(ii)) at the threshold `t = T_D⁻²`: the zeros with
`|τ| < T_D` (that is, `‖w‖ > t`) of the two lists correspond one-to-one with equal values. -/
def DFamW {ι κ : Type*} (w : ι → ℂ) (v : κ → ℂ) (t : ℝ) : Prop :=
  ∃ e : {i // t < ‖w i‖} ≃ {j // t < ‖v j‖}, ∀ i, v (e i) = w i

/-- 1bu(ii)'s `ε(δ) = Σ_{|τ|≥T_D}|τ|⁻² + Σ_{|γ|≥T_D}|γ|⁻²`. -/
def tailEps {ι κ : Type*} (w : ι → ℂ) (v : κ → ℂ) (t : ℝ) : ℝ :=
  (∑' i : {i // ¬ t < ‖w i‖}, ‖w i‖) + ∑' j : {j // ¬ t < ‖v j‖}, ‖v j‖

/-- **Exact D gives a pairing with error at most `ε`.** Match the zeros below `T_D` by `D`, and pair
each tail zero with a padding entry. -/
theorem pairing_of_D {ι κ : Type*} {f g : ℂ → ℂ} {w : ι → ℂ} {v : κ → ℂ} {t : ℝ}
    (hf : HadamardW f w) (hg : HadamardW g v) (hD : DFamW w v t) :
    ∃ (P : Type (max u_1 u_2)) (w' v' : P → ℂ), HadamardW f w' ∧ HadamardW g v' ∧
      (∑' x, ‖w' x‖) = ∑' i, ‖w i‖ ∧ (∑' x, ‖w' x - v' x‖) ≤ tailEps w v t := by
  set Sw := {i // t < ‖w i‖}
  set Swc := {i // ¬ t < ‖w i‖}
  set Svc := {j // ¬ t < ‖v j‖}
  obtain ⟨e, he⟩ := hD
  -- `P = Sw ⊕ (Swc ⊕ Svc)`
  let E1 : Sw ⊕ (Swc ⊕ Svc) ≃ ι ⊕ Svc :=
    (Equiv.sumAssoc Sw Swc Svc).symm.trans
      (Equiv.sumCongr (Equiv.sumCompl fun i => t < ‖w i‖) (Equiv.refl _))
  let E2 : Sw ⊕ (Swc ⊕ Svc) ≃ κ ⊕ Swc :=
    ((Equiv.sumCongr (Equiv.refl Sw) (Equiv.sumComm Swc Svc)).trans
      (Equiv.sumAssoc Sw Svc Swc).symm).trans
      (Equiv.sumCongr ((Equiv.sumCongr e (Equiv.refl _)).trans
        (Equiv.sumCompl fun j => t < ‖v j‖)) (Equiv.refl _))
  let w' := (Sum.elim w (fun _ : Svc => (0 : ℂ))) ∘ E1
  let v' := (Sum.elim v (fun _ : Swc => (0 : ℂ))) ∘ E2
  have hw' : HadamardW f w' := (hf.pad Svc).comp_equiv E1
  have hv' : HadamardW g v' := (hg.pad Swc).comp_equiv E2
  refine ⟨_, w', v', hw', hv', ?_, ?_⟩
  · -- `Σ‖w'‖ = Σ‖w‖`
    have h1 : (∑' x, ‖w' x‖) = ∑' y : ι ⊕ Svc, ‖Sum.elim w (fun _ : Svc => (0 : ℂ)) y‖ :=
      E1.tsum_eq (fun y => ‖Sum.elim w (fun _ : Svc => (0 : ℂ)) y‖)
    rw [h1, Summable.tsum_sum (f := fun y => ‖Sum.elim w (fun _ : Svc => (0 : ℂ)) y‖)
      (show Summable fun i => ‖w i‖ from hf.summ)
      (show Summable fun _ : Svc => ‖(0 : ℂ)‖ by simp)]
    simp
  · -- the pairing error
    have hws : Summable fun i : Swc => ‖w i‖ := hf.summ.subtype _
    have hvs : Summable fun j : Svc => ‖v j‖ := hg.summ.subtype _
    set bnd : Sw ⊕ (Swc ⊕ Svc) → ℝ :=
      Sum.elim (fun _ => 0) (Sum.elim (fun i => ‖w i‖) (fun j => ‖v j‖)) with hbnd
    have hbs : HasSum bnd (0 + ((∑' i : Swc, ‖w i‖) + ∑' j : Svc, ‖v j‖)) :=
      HasSum.sum (f := bnd) (show HasSum (fun _ : Sw => (0 : ℝ)) 0 from hasSum_zero)
        (HasSum.sum (f := bnd ∘ Sum.inr) (show HasSum (fun i : Swc => ‖w i‖) _ from hws.hasSum)
          (show HasSum (fun j : Svc => ‖v j‖) _ from hvs.hasSum))
    have hpt : ∀ x, ‖w' x - v' x‖ ≤ bnd x := by
      rintro (i | i | j)
      · simp [w', v', E1, E2, bnd]
        exact sub_eq_zero.2 (he i).symm
      · simp [w', v', E1, E2, bnd]
        exact le_rfl
      · simp [w', v', E1, E2, bnd]
        exact le_rfl
    have hsum : Summable fun x => ‖w' x - v' x‖ :=
      (hw'.summ.add hv'.summ).of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => norm_sub_le _ _)
    calc (∑' x, ‖w' x - v' x‖) ≤ ∑' x, bnd x := hsum.tsum_le_tsum hpt hbs.summable
      _ = tailEps w v t := by rw [hbs.tsum_eq, zero_add]; rfl

/-- **Theorem 1bu(ii) + item 6 in the paper's own terms**: ground states at supports `2a n` whose
transforms are real-rooted (item 1(b)), satisfying Hypothesis D exactly below `T_D(n)` (item 1(a),
the threshold `t n = T_D(n)⁻²`), with `Σ_τ τ⁻²` bounded and `ε(δ_n) → 0`, give Mathlib's
`RiemannHypothesis`. Named input: Hadamard's factorisations of each `ĝ_n` and of `Ξ`. -/
theorem rh_of_D_and_realRooted {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) MeasureTheory.volume (-(a n)) (a n))
    (hRR : ∀ n, RealRooted (a n) (g n))
    {ι : ℕ → Type} {κ : Type} {w : ∀ n, ι n → ℂ} {v : κ → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : HadamardW Xi v)
    {B : ℝ} (hB : ∀ n, (∑' i, ‖w n i‖) ≤ B) {t : ℕ → ℝ} (hD : ∀ n, DFamW (w n) v (t n))
    (hε : Tendsto (fun n => tailEps (w n) v (t n)) atTop (𝓝 0)) : RiemannHypothesis := by
  choose P w' v' hw' hv' hsw hθ using fun n => pairing_of_D (hF n) hX (hD n)
  exact rh_of_pairing_and_realRooted hint hRR hw' hv' (fun n => (hsw n).le.trans (hB n)) hθ hε

end Pilot1ca

#print axioms Pilot1ca.norm_prod_sub_prod_le
#print axioms Pilot1ca.norm_tprod_sub_tprod_le
#print axioms Pilot1ca.hadamard_compare
#print axioms Pilot1ca.tendstoLocallyUniformly_of_pairing
#print axioms Pilot1ca.rh_of_pairing_and_realRooted
#print axioms Pilot1ca.pairing_of_D
#print axioms Pilot1ca.rh_of_D_and_realRooted
