import Mathlib
import XiBounds

/-! # Dodging D and the curvature sum rule

Two changes to the chain of `rh_of_D_and_realRooted_final`:

* **Approximate D.** The paper's own census finds D only "to the dodging tolerance, not exactly"
  (Theorem 1bu(ii)): the ground state's zeros sit near the zeta zeros, not on them. Exact D is
  replaced by a *dodging* hypothesis: every zero of `Ξ` below `T_D(n)` is matched with its own zero
  of `ĝ_n`, with total displacement `Σ|τ⁻² − γ⁻²| ≤ η_n → 0`. Nothing is assumed about the other
  zeros of `ĝ_n`.
* **The curvature sum rule.** For a real-rooted `ĝ` of an even integrable `g`,
  `Σ_τ τ⁻² = ∫u²g / (2∫g)` (`ghat_sum_rule`). The uniform bound `Σ τ⁻² ≤ B` and the tails `ε → 0`
  are replaced by one scalar condition: the curvature `κ_n = ∫u²g_n / (2∫g_n)` of the ground states
  converges to `Ξ`'s, `Re Σ_ρ-pairs γ⁻²` (the `z²` coefficient of `Ξ(z)/Ξ(0)`, `0.023105`). Under this,
  "and no other zero below `T_D`" is a consequence, not a hypothesis.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## A. Pairings from a matching -/

/-- **A matching gives a pairing.** Match the entries `p` of `w` to the entries `q` of `v` by `e`, and
pair each unmatched entry with padding: the pairing error is the matched displacement plus the two
unmatched sums. (`pairing_of_D` is the case of exact matching below a threshold.) -/
theorem pairing_of_matching {ι κ : Type*} {f g : ℂ → ℂ} {w : ι → ℂ} {v : κ → ℂ}
    (hf : HadamardW f w) (hg : HadamardW g v) (p : ι → Prop) (q : κ → Prop)
    (e : {i // p i} ≃ {j // q j}) :
    ∃ (P : Type (max u_1 u_2)) (w' v' : P → ℂ), HadamardW f w' ∧ HadamardW g v' ∧
      (∑' x, ‖w' x‖) = ∑' i, ‖w i‖ ∧
      (∑' x, ‖w' x - v' x‖) ≤ (∑' i : {i // p i}, ‖w i - v (e i)‖) +
        ((∑' i : {i // ¬ p i}, ‖w i‖) + ∑' j : {j // ¬ q j}, ‖v j‖) := by
  classical
  let Sw := {i // p i}
  let Swc := {i // ¬ p i}
  let Svc := {j // ¬ q j}
  let E1 : Sw ⊕ (Swc ⊕ Svc) ≃ ι ⊕ Svc :=
    (Equiv.sumAssoc Sw Swc Svc).symm.trans
      (Equiv.sumCongr (Equiv.sumCompl p) (Equiv.refl _))
  let E2 : Sw ⊕ (Swc ⊕ Svc) ≃ κ ⊕ Swc :=
    ((Equiv.sumCongr (Equiv.refl Sw) (Equiv.sumComm Swc Svc)).trans
      (Equiv.sumAssoc Sw Svc Swc).symm).trans
      (Equiv.sumCongr ((Equiv.sumCongr e (Equiv.refl _)).trans
        (Equiv.sumCompl q)) (Equiv.refl _))
  let w' := (Sum.elim w (fun _ : Svc => (0 : ℂ))) ∘ E1
  let v' := (Sum.elim v (fun _ : Swc => (0 : ℂ))) ∘ E2
  have hw' : HadamardW f w' := (hf.pad Svc).comp_equiv E1
  have hv' : HadamardW g v' := (hg.pad Swc).comp_equiv E2
  refine ⟨_, w', v', hw', hv', ?_, ?_⟩
  · have h1 : (∑' x, ‖w' x‖) = ∑' y : ι ⊕ Svc, ‖Sum.elim w (fun _ : Svc => (0 : ℂ)) y‖ :=
      E1.tsum_eq (fun y => ‖Sum.elim w (fun _ : Svc => (0 : ℂ)) y‖)
    rw [h1, Summable.tsum_sum (f := fun y => ‖Sum.elim w (fun _ : Svc => (0 : ℂ)) y‖)
      (show Summable fun i => ‖w i‖ from hf.summ)
      (show Summable fun _ : Svc => ‖(0 : ℂ)‖ by simp)]
    simp
  · have hws : Summable fun i : Swc => ‖w i‖ := hf.summ.subtype _
    have hvs : Summable fun j : Svc => ‖v j‖ := hg.summ.subtype _
    have hms : Summable fun i : Sw => ‖w i - v (e i)‖ := by
      have h1 : Summable fun i : Sw => ‖w i‖ := hf.summ.subtype _
      have h2 : Summable fun i : Sw => ‖v (e i)‖ :=
        (e.summable_iff (f := fun j : {j // q j} => ‖v j‖)).2 (hg.summ.subtype _)
      exact (h1.add h2).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _)
    set bnd : Sw ⊕ (Swc ⊕ Svc) → ℝ :=
      Sum.elim (fun i => ‖w i - v (e i)‖) (Sum.elim (fun i => ‖w i‖) (fun j => ‖v j‖)) with hbnd
    have hbs : HasSum bnd ((∑' i : Sw, ‖w i - v (e i)‖) +
        ((∑' i : Swc, ‖w i‖) + ∑' j : Svc, ‖v j‖)) :=
      HasSum.sum (f := bnd) (show HasSum (fun i : Sw => ‖w i - v (e i)‖) _ from hms.hasSum)
        (HasSum.sum (f := bnd ∘ Sum.inr) (show HasSum (fun i : Swc => ‖w i‖) _ from hws.hasSum)
          (show HasSum (fun j : Svc => ‖v j‖) _ from hvs.hasSum))
    have hpt : ∀ x, ‖w' x - v' x‖ ≤ bnd x := by
      rintro (i | i | j)
      · simp [w', v', E1, E2, bnd]; try exact le_rfl
      · simp [w', v', E1, E2, bnd]; try exact le_rfl
      · simp [w', v', E1, E2, bnd]; try exact le_rfl
    have hsum : Summable fun x => ‖w' x - v' x‖ :=
      (hw'.summ.add hv'.summ).of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => norm_sub_le _ _)
    calc (∑' x, ‖w' x - v' x‖) ≤ ∑' x, bnd x := hsum.tsum_le_tsum hpt hbs.summable
      _ = _ := hbs.tsum_eq

/-- The part of a summable list above a threshold `t → 0` exhausts it. -/
theorem tendsto_tsum_above {κ : Type*} {v : κ → ℂ} {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ∑' j : {j // t n < ‖v j‖}, ‖v j‖) atTop (𝓝 (∑' j, ‖v j‖)) ∨
      ¬ Summable (fun j => ‖v j‖) := by
  by_cases hv : Summable fun j => ‖v j‖
  swap
  · exact Or.inr hv
  left
  have e : ∀ n, (∑' j : {j // t n < ‖v j‖}, ‖v j‖)
      = ∑' j, ({j | t n < ‖v j‖} : Set κ).indicator (fun j => ‖v j‖) j :=
    fun n => tsum_subtype ({j | t n < ‖v j‖} : Set κ) (fun j => ‖v j‖)
  simp_rw [e]
  refine tendsto_tsum_of_dominated_convergence hv (fun j => ?_) (Eventually.of_forall fun n j => ?_)
  · by_cases hj : ‖v j‖ = 0
    · have : ∀ n, ({j | t n < ‖v j‖} : Set κ).indicator (fun j => ‖v j‖) j = ‖v j‖ := by
        intro n; simp [Set.indicator_apply, hj]
      simp only [this]; exact tendsto_const_nhds
    · have hpos : 0 < ‖v j‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hj)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [ht.eventually (gt_mem_nhds hpos)] with n hn
      simp [hn]
  · rw [Real.norm_eq_abs, Set.indicator_apply]
    split_ifs <;> simp

/-- **The chain with dodging D and the curvature condition.** Ground states whose transforms are
real-rooted, such that below `T_D(n)` (`t n = T_D(n)⁻²`, `t → 0`) every zero of `Ξ` is matched with its
own zero of `ĝ_n` within total displacement `η_n → 0`, and whose curvature `Σ_τ τ⁻²` converges to
`Ξ`'s `Re Σ γ⁻²`, give Mathlib's `RiemannHypothesis`. -/
theorem rh_of_dodging_and_curvature {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) MeasureTheory.volume (-(a n)) (a n))
    (hRR : ∀ n, RealRooted (a n) (g n))
    {ι : ℕ → Type} {κ : Type} {w : ∀ n, ι n → ℂ} {v : κ → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : HadamardW Xi v)
    {t η : ℕ → ℝ}
    (hD : ∀ n, ∃ (p : ι n → Prop) (e : {i // p i} ≃ {j // t n < ‖v j‖}),
      (∑' i : {i // p i}, ‖w n i - v (e i)‖) ≤ η n)
    (hη : Tendsto η atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0))
    (hκ : Tendsto (fun n => ∑' i, ‖w n i‖) atTop (𝓝 (∑' j, v j).re)) :
    RiemannHypothesis := by
  choose p e he using hD
  set K := ∑' j, ‖v j‖ with hK
  set K' := (∑' j, v j).re with hK'
  have hKK : K' ≤ K := (Complex.re_le_norm _).trans (norm_tsum_le_tsum_norm hX.summ)
  set Sv : ℕ → ℝ := fun n => ∑' j : {j // t n < ‖v j‖}, ‖v j‖ with hSv
  have hSvK : Tendsto Sv atTop (𝓝 K) :=
    (tendsto_tsum_above (v := v) ht).resolve_right (not_not.2 hX.summ)
  -- the pairings and their errors
  choose P w' v' hw' hv' hsw hcost using fun n => pairing_of_matching (hF n) hX (p n) _ (e n)
  set θ : ℕ → ℝ := fun n => η n + (((∑' i, ‖w n i‖) - Sv n + η n) + (K - Sv n)) with hθ
  have hθb : ∀ n, (∑' x, ‖w' n x - v' n x‖) ≤ θ n := by
    intro n
    have hsp : Summable fun i : {i // p n i} => ‖w n i‖ := (hF n).summ.subtype _
    have hmatch : Summable fun i : {i // p n i} => ‖w n i - v (e n i)‖ := by
      have h2 : Summable fun i : {i // p n i} => ‖v (e n i)‖ :=
        ((e n).summable_iff (f := fun j : {j // t n < ‖v j‖} => ‖v j‖)).2 (hX.summ.subtype _)
      exact (hsp.add h2).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _)
    -- `Sv ≤ Σ_p ‖w‖ + η`
    have hSvle : Sv n ≤ (∑' i : {i // p n i}, ‖w n i‖) + η n := by
      have h1 : Sv n = ∑' i : {i // p n i}, ‖v (e n i)‖ :=
        ((e n).tsum_eq (fun j : {j // t n < ‖v j‖} => ‖v j‖)).symm
      rw [h1]
      calc (∑' i : {i // p n i}, ‖v (e n i)‖)
          ≤ ∑' i : {i // p n i}, (‖w n i‖ + ‖w n i - v (e n i)‖) :=
            ((e n).summable_iff (f := fun j : {j // t n < ‖v j‖} => ‖v j‖)).2
              (hX.summ.subtype _) |>.tsum_le_tsum (fun i => by
                have := norm_sub_norm_le (v (e n i)) (w n i)
                rw [norm_sub_rev (v (e n i))] at this; linarith) (hsp.add hmatch)
        _ = (∑' i : {i // p n i}, ‖w n i‖) + ∑' i : {i // p n i}, ‖w n i - v (e n i)‖ :=
            hsp.tsum_add hmatch
        _ ≤ _ := add_le_add le_rfl (he n)
    -- the unmatched sums
    have hsplitW : (∑' i : {i // p n i}, ‖w n i‖) + (∑' i : {i // ¬ p n i}, ‖w n i‖)
        = ∑' i, ‖w n i‖ :=
      (hF n).summ.tsum_subtype_add_tsum_subtype_compl {i | p n i}
    have hsplitV : Sv n + (∑' j : {j // ¬ t n < ‖v j‖}, ‖v j‖) = K :=
      hX.summ.tsum_subtype_add_tsum_subtype_compl {j | t n < ‖v j‖}
    refine (hcost n).trans ?_
    simp only [hθ]
    linarith [he n]
  have hθ0' : Tendsto θ atTop (𝓝 (0 + ((K' - K + 0) + (K - K)))) :=
    hη.add (((hκ.sub hSvK).add hη).add (tendsto_const_nhds.sub hSvK))
  have hθnn : ∀ n, 0 ≤ θ n := fun n =>
    (tsum_nonneg fun _ => norm_nonneg _).trans (hθb n)
  have hge : 0 ≤ 0 + ((K' - K + 0) + (K - K)) := ge_of_tendsto' hθ0' hθnn
  have hθ0 : Tendsto θ atTop (𝓝 0) := by
    have : 0 + ((K' - K + 0) + (K - K)) = 0 := by linarith
    rwa [this] at hθ0'
  obtain ⟨B, hB⟩ := hκ.bddAbove_range
  exact rh_of_pairing_and_realRooted hint hRR hw' (fun n => hv' n)
    (fun n => (hsw n).le.trans (hB ⟨n, rfl⟩)) hθb hθ0

/-! ## B. The curvature sum rule -/

theorem norm_prod_one_add_sub_one_le {ι : Type*} (t : Finset ι) (x : ι → ℂ) :
    ‖∏ i ∈ t, (1 + x i) - 1‖ ≤ ∏ i ∈ t, (1 + ‖x i‖) - 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj IH =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    set P := ∏ i ∈ t, (1 + x i)
    set Q := ∏ i ∈ t, (1 + ‖x i‖)
    have hP : ‖P‖ ≤ Q := by
      refine (Finset.norm_prod_le _ _).trans
        (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_)
      simpa using norm_add_le (1 : ℂ) (x i)
    have e : (1 + x j) * P - 1 = (P - 1) + x j * P := by ring
    rw [e]
    calc ‖(P - 1) + x j * P‖ ≤ ‖P - 1‖ + ‖x j‖ * ‖P‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ (Q - 1) + ‖x j‖ * Q := by gcongr
      _ = (1 + ‖x j‖) * Q - 1 := by ring

/-- `‖Π(1 + x_i) − 1 − Σx_i‖ ≤ Π(1 + ‖x_i‖) − 1 − Σ‖x_i‖` over a finite set. -/
theorem norm_prod_one_add_sub_sum_le {ι : Type*} (t : Finset ι) (x : ι → ℂ) :
    ‖∏ i ∈ t, (1 + x i) - 1 - ∑ i ∈ t, x i‖ ≤ ∏ i ∈ t, (1 + ‖x i‖) - 1 - ∑ i ∈ t, ‖x i‖ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj IH =>
    have h1 := norm_prod_one_add_sub_one_le t x
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    set P := ∏ i ∈ t, (1 + x i)
    set Q := ∏ i ∈ t, (1 + ‖x i‖)
    set S := ∑ i ∈ t, x i
    set T := ∑ i ∈ t, ‖x i‖
    have e : (1 + x j) * P - 1 - (x j + S) = (P - 1 - S) + x j * (P - 1) := by ring
    rw [e]
    calc ‖(P - 1 - S) + x j * (P - 1)‖ ≤ ‖P - 1 - S‖ + ‖x j‖ * ‖P - 1‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ (Q - 1 - T) + ‖x j‖ * (Q - 1) := by gcongr
      _ = (1 + ‖x j‖) * Q - 1 - (‖x j‖ + T) := by ring

theorem prod_one_add_norm_le_exp {ι : Type*} (t : Finset ι) (x : ι → ℂ) :
    ∏ i ∈ t, (1 + ‖x i‖) ≤ Real.exp (∑ i ∈ t, ‖x i‖) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun i _ => by positivity)
    fun i _ => by linarith [Real.add_one_le_exp ‖x i‖]

theorem exp_sub_one_sub_mono {s S : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S) :
    Real.exp s - 1 - s ≤ Real.exp S - 1 - S := by
  have h1 : Real.exp S = Real.exp s * Real.exp (S - s) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 := Real.add_one_le_exp (S - s)
  have h3 : 1 ≤ Real.exp s := Real.one_le_exp hs
  nlinarith [mul_nonneg (Real.exp_pos s).le (show 0 ≤ Real.exp (S - s) - (S - s + 1) by linarith),
    mul_nonneg (show 0 ≤ Real.exp s - 1 by linarith) (show 0 ≤ S - s by linarith)]

/-- **`‖Π'(1 + x_i) − 1 − Σ'x_i‖ ≤ e^S − 1 − S`**, `S = Σ'‖x_i‖`. -/
theorem norm_tprod_one_add_sub_tsum_le {ι : Type*} {x : ι → ℂ} (hx : Summable fun i => ‖x i‖) :
    ‖(∏' i, (1 + x i)) - 1 - ∑' i, x i‖ ≤ Real.exp (∑' i, ‖x i‖) - 1 - ∑' i, ‖x i‖ := by
  have hpx := (multipliable_one_add_of_summable hx).hasProd
  have hsx := hx.of_norm.hasSum
  have ht : Tendsto (fun t : Finset ι => ‖∏ i ∈ t, (1 + x i) - 1 - ∑ i ∈ t, x i‖) atTop
      (𝓝 ‖(∏' i, (1 + x i)) - 1 - ∑' i, x i‖) :=
    ((hpx.sub tendsto_const_nhds).sub hsx).norm
  refine le_of_tendsto' ht fun t => (norm_prod_one_add_sub_sum_le t x).trans ?_
  have hs0 : 0 ≤ ∑ i ∈ t, ‖x i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsS : ∑ i ∈ t, ‖x i‖ ≤ ∑' i, ‖x i‖ := hx.sum_le_tsum t fun i _ => norm_nonneg _
  linarith [prod_one_add_norm_le_exp t x, exp_sub_one_sub_mono hs0 hsS]

/-- **The second-order expansion of a Hadamard product**: `f(z)/f(0) = 1 − z²Σw + O(‖z‖⁴)`,
explicitly `≤ (‖z‖²Σ‖w‖)²` once `‖z‖²Σ‖w‖ ≤ 1`. -/
theorem HadamardW.expansion {ι : Type*} {f : ℂ → ℂ} {w : ι → ℂ} (h : HadamardW f w) (z : ℂ)
    (hz : ‖z‖ ^ 2 * ∑' i, ‖w i‖ ≤ 1) :
    ‖f z / f 0 - (1 - z ^ 2 * ∑' i, w i)‖ ≤ (‖z‖ ^ 2 * ∑' i, ‖w i‖) ^ 2 := by
  have hs := summable_scaled h.summ z
  have e1 : (∑' i, ‖-(z ^ 2 * w i)‖) = ‖z‖ ^ 2 * ∑' i, ‖w i‖ := by
    rw [← tsum_mul_left]; congr 1; funext i; simp [norm_pow]
  have e2 : (∑' i, -(z ^ 2 * w i)) = -(z ^ 2 * ∑' i, w i) := by
    rw [tsum_neg, tsum_mul_left]
  have key := norm_tprod_one_add_sub_tsum_le hs
  rw [e1, e2] at key
  rw [h.eq_tprod]
  have hS0 : 0 ≤ ‖z‖ ^ 2 * ∑' i, ‖w i‖ :=
    mul_nonneg (by positivity) (tsum_nonneg fun _ => norm_nonneg _)
  have hexp := Real.abs_exp_sub_one_sub_id_le (x := ‖z‖ ^ 2 * ∑' i, ‖w i‖)
    (by rw [abs_of_nonneg hS0]; exact hz)
  have e3 : (∏' i, (1 + -(z ^ 2 * w i))) - (1 - z ^ 2 * ∑' i, w i)
      = (∏' i, (1 + -(z ^ 2 * w i))) - 1 - -(z ^ 2 * ∑' i, w i) := by ring
  rw [e3]
  exact key.trans ((le_abs_self _).trans hexp)

theorem ghatC_zero (g : ℝ → ℝ) (a : ℝ) : ghatC g a 0 = ((∫ u in (-a)..a, g u : ℝ) : ℂ) := by
  unfold ghatC
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  exact intervalIntegral.integral_ofReal

/-- The odd moment of an even function vanishes. -/
theorem integral_mul_even_eq_zero {g : ℝ → ℝ} (heven : ∀ u, g (-u) = g u) (a : ℝ) :
    ∫ u in (-a)..a, u * g u = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) (f := fun u => u * g u)
  simp only [neg_neg, heven, neg_mul, intervalIntegral.integral_neg] at h
  linarith

theorem sum_range_three (y : ℂ) :
    ∑ m ∈ Finset.range 3, y ^ m / (m.factorial : ℂ) = 1 + y + y ^ 2 / 2 := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The second-order expansion of `ĝ`**: for even integrable `g` on `[−a, a]` and real `x` with
`|x|a ≤ 1`, `‖ĝ(x) − ∫g + (x²/2)∫u²g‖ ≤ |x|³a³∫|g|`. -/
theorem ghat_expansion {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hg : IntervalIntegrable g volume (-a) a)
    (heven : ∀ u, g (-u) = g u) (x : ℝ) (hx : |x| * a ≤ 1) :
    ‖ghatC g a x - ((∫ u in (-a)..a, g u : ℝ) : ℂ)
        + ((x : ℂ) ^ 2 / 2) * ((∫ u in (-a)..a, u ^ 2 * g u : ℝ) : ℂ)‖
      ≤ |x| ^ 3 * a ^ 3 * ∫ u in (-a)..a, |g u| := by
  have hle : -a ≤ a := by linarith
  have hgC : IntervalIntegrable (fun u => ((g u : ℝ) : ℂ)) volume (-a) a :=
    ⟨hg.1.ofReal, hg.2.ofReal⟩
  set R : ℝ → ℂ := fun u => Complex.exp (I * x * u) - (1 + I * x * u + (I * x * u) ^ 2 / 2)
    with hR
  have hRc : Continuous R := by simp only [hR]; fun_prop
  have hRi : IntervalIntegrable (fun u => ((g u : ℝ) : ℂ) * R u) volume (-a) a :=
    hgC.mul_continuousOn hRc.continuousOn
  have hr1 : IntervalIntegrable (fun u => u * g u) volume (-a) a :=
    hg.continuousOn_mul continuousOn_id
  have hr2 : IntervalIntegrable (fun u => u ^ 2 * g u) volume (-a) a :=
    hg.continuousOn_mul (continuous_pow 2).continuousOn
  have hc1 : IntervalIntegrable (fun u => ((u * g u : ℝ) : ℂ)) volume (-a) a :=
    ⟨hr1.1.ofReal, hr1.2.ofReal⟩
  have hc2 : IntervalIntegrable (fun u => ((u ^ 2 * g u : ℝ) : ℂ)) volume (-a) a :=
    ⟨hr2.1.ofReal, hr2.2.ofReal⟩
  have hfun : (fun u : ℝ => ((g u : ℝ) : ℂ) * Complex.exp (I * x * u))
      = fun u => (((g u : ℝ) : ℂ) * R u + ((g u : ℝ) : ℂ))
          + ((I * x) * ((u * g u : ℝ) : ℂ) - ((x : ℂ) ^ 2 / 2) * ((u ^ 2 * g u : ℝ) : ℂ)) := by
    funext u
    simp only [hR]
    push_cast
    linear_combination ((g u : ℂ) * (x : ℂ) ^ 2 * (u : ℂ) ^ 2 / 2) * I_sq
  have hI : ghatC g a x = (∫ u in (-a)..a, ((g u : ℝ) : ℂ) * R u)
      + ((∫ u in (-a)..a, g u : ℝ) : ℂ)
      + ((I * x) * ((∫ u in (-a)..a, u * g u : ℝ) : ℂ)
        - ((x : ℂ) ^ 2 / 2) * ((∫ u in (-a)..a, u ^ 2 * g u : ℝ) : ℂ)) := by
    unfold ghatC
    rw [hfun, intervalIntegral.integral_add (hRi.add hgC) ((hc1.const_mul _).sub (hc2.const_mul _)),
      intervalIntegral.integral_add hRi hgC,
      intervalIntegral.integral_sub (hc1.const_mul _) (hc2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal]
  rw [hI, integral_mul_even_eq_zero heven]
  have e : (∫ u in (-a)..a, ((g u : ℝ) : ℂ) * R u) + ((∫ u in (-a)..a, g u : ℝ) : ℂ)
      + ((I * x) * (((0 : ℝ)) : ℂ) - ((x : ℂ) ^ 2 / 2) * ((∫ u in (-a)..a, u ^ 2 * g u : ℝ) : ℂ))
      - ((∫ u in (-a)..a, g u : ℝ) : ℂ)
      + ((x : ℂ) ^ 2 / 2) * ((∫ u in (-a)..a, u ^ 2 * g u : ℝ) : ℂ)
      = ∫ u in (-a)..a, ((g u : ℝ) : ℂ) * R u := by push_cast; ring
  rw [e]
  have hb : IntervalIntegrable (fun u => |g u| * (|x| ^ 3 * a ^ 3)) volume (-a) a :=
    hg.abs.mul_const _
  refine (intervalIntegral.norm_integral_le_of_norm_le hle
    (Eventually.of_forall fun u hu => ?_) hb).trans ?_
  · have hua : |u| ≤ a := abs_le.2 ⟨hu.1.le, hu.2⟩
    have hy : ‖I * (x : ℂ) * (u : ℂ)‖ = |x| * |u| := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    have hxu : |x| * |u| ≤ |x| * a := mul_le_mul_of_nonneg_left hua (abs_nonneg x)
    have hy1 : ‖I * (x : ℂ) * (u : ℂ)‖ ≤ 1 := by rw [hy]; linarith
    have hexp := Complex.exp_bound hy1 (n := 3) (by norm_num)
    rw [sum_range_three] at hexp
    have hc : ((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      norm_num [Nat.factorial]
    have hRu : ‖R u‖ ≤ |x| ^ 3 * a ^ 3 := by
      calc ‖R u‖ ≤ ‖I * (x : ℂ) * (u : ℂ)‖ ^ 3 * (((Nat.succ 3 : ℕ) : ℝ)
            * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹) := hexp
        _ ≤ ‖I * (x : ℂ) * (u : ℂ)‖ ^ 3 * 1 := by gcongr
        _ ≤ (|x| * a) ^ 3 := by
            rw [mul_one, hy]
            exact pow_le_pow_left₀ (by positivity) hxu 3
        _ = |x| ^ 3 * a ^ 3 := by ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hRu (abs_nonneg _)
  · rw [intervalIntegral.integral_mul_const]
    apply le_of_eq; ring

/-- For a real-rooted `ĝ`, the zeros of `sqF ĝ` are positive reals: `u⁻¹ = ‖u⁻¹‖`. -/
theorem inv_zero_eq_norm {g : ℝ → ℝ} {a : ℝ} (hg : IntervalIntegrable g volume (-a) a)
    (heven : ∀ u, g (-u) = g u) (h0 : ghatC g a 0 ≠ 0) (hRR : RealRooted a g)
    (i : ZeroIdx (sqF (ghatC g a))) : (i.1⁻¹ : ℂ) = ((‖i.1⁻¹‖ : ℝ) : ℂ) := by
  have hF := sqF_differentiable (ghatC_differentiable hg) (fun z => ghatC_even heven a z)
  have hF0 : sqF (ghatC g a) 0 ≠ 0 := by rwa [sqF_zero]
  have hz : sqF (ghatC g a) i.1 = 0 :=
    (ordN_ne_zero_iff hF hF0 i.1).1 (Nat.pos_iff_ne_zero.1 i.2.pos)
  have him : (i.1 ^ ((2 : ℂ)⁻¹)).im = 0 := hRR _ hz
  obtain ⟨s, hs⟩ : ∃ s : ℝ, i.1 ^ ((2 : ℂ)⁻¹) = s :=
    ⟨(i.1 ^ ((2 : ℂ)⁻¹)).re, Complex.ext (by simp) (by simp [him])⟩
  have hu : i.1 = ((s ^ 2 : ℝ) : ℂ) := by
    rw [← sqrt_sq' i.1, hs]; push_cast; ring
  rw [hu, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (sq_nonneg s))]

/-- **The curvature sum rule**: for even integrable `g` with `∫g ≠ 0`,
`Σ_τ τ⁻² = ∫u²g / (2∫g)`, the sum over the zero pairs of `ĝ` taken in `w = τ⁻²` (in general complex;
see `ghat_curvature` for the real-rooted case). -/
theorem ghat_sum_rule {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hg : IntervalIntegrable g volume (-a) a)
    (heven : ∀ u, g (-u) = g u) (h0 : ghatC g a 0 ≠ 0) :
    ∑' i : ZeroIdx (sqF (ghatC g a)), i.1⁻¹
      = (((∫ u in (-a)..a, u ^ 2 * g u) / (2 * ∫ u in (-a)..a, g u) : ℝ) : ℂ) := by
  have hH := hadamardW_ghat ha hg heven h0
  set W := ∑' i : ZeroIdx (sqF (ghatC g a)), ‖i.1⁻¹‖ with hW
  set Sw := ∑' i : ZeroIdx (sqF (ghatC g a)), i.1⁻¹ with hSw
  set G0 := ∫ u in (-a)..a, g u with hG0d
  set G2 := ∫ u in (-a)..a, u ^ 2 * g u with hG2d
  set A := ∫ u in (-a)..a, |g u| with hAd
  have hg0 : ghatC g a 0 = (G0 : ℂ) := ghatC_zero g a
  have hG0 : (G0 : ℂ) ≠ 0 := hg0 ▸ h0
  have hG0' : G0 ≠ 0 := by exact_mod_cast hG0
  set κ : ℂ := ((G2 / (2 * G0) : ℝ) : ℂ) with hκ
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => norm_nonneg _
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg (by linarith) fun u _ => abs_nonneg _
  set M := a ^ 3 * A / |G0| with hM
  have hM0 : 0 ≤ M := by positivity
  set x0 := 1 / (W + a + 1) with hx0d
  have hx0 : 0 < x0 := by positivity
  have hbound : ∀ x : ℝ, 0 < x → x ≤ x0 → ‖Sw - κ‖ ≤ x * (W ^ 2 + M) := by
    intro x hx hxx0
    have hsum1 : x * (W + a + 1) ≤ 1 := by
      calc x * (W + a + 1) ≤ x0 * (W + a + 1) := by gcongr
        _ = 1 := by rw [hx0d]; field_simp
    have hxW : x * W ≤ 1 := by nlinarith
    have hxa : x * a ≤ 1 := by nlinarith
    have hx1 : x ≤ 1 := by nlinarith
    have hz : ‖(x : ℂ)‖ ^ 2 * W ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]; nlinarith
    have e1 := hH.expansion (x : ℂ) hz
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at e1
    have e2 := ghat_expansion ha hg heven x (by rw [abs_of_pos hx]; exact hxa)
    rw [abs_of_pos hx] at e2
    have e3 : ‖ghatC g a x / ghatC g a 0 - (1 - (x : ℂ) ^ 2 * κ)‖ ≤ x ^ 3 * M := by
      have : ghatC g a x / ghatC g a 0 - (1 - (x : ℂ) ^ 2 * κ)
          = (ghatC g a x - (G0 : ℂ) + ((x : ℂ) ^ 2 / 2) * (G2 : ℂ)) / (G0 : ℂ) := by
        rw [hg0, hκ]; push_cast; field_simp; ring
      rw [this, norm_div, Complex.norm_real, Real.norm_eq_abs,
        div_le_iff₀ (abs_pos.2 hG0')]
      calc _ ≤ x ^ 3 * a ^ 3 * A := e2
        _ = x ^ 3 * M * |G0| := by rw [hM]; field_simp
    have e4 : ‖(x : ℂ) ^ 2 * (Sw - κ)‖ ≤ (x ^ 2 * W) ^ 2 + x ^ 3 * M := by
      have : (x : ℂ) ^ 2 * (Sw - κ)
          = (ghatC g a x / ghatC g a 0 - (1 - (x : ℂ) ^ 2 * Sw))
            - (ghatC g a x / ghatC g a 0 - (1 - (x : ℂ) ^ 2 * κ)) := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (by linarith)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at e4
    have hx2 : 0 < x ^ 2 := by positivity
    have hd : ‖Sw - κ‖ ≤ x ^ 2 * W ^ 2 + x * M := by
      refine le_of_mul_le_mul_left ?_ hx2
      calc x ^ 2 * ‖Sw - κ‖ ≤ (x ^ 2 * W) ^ 2 + x ^ 3 * M := e4
        _ = x ^ 2 * (x ^ 2 * W ^ 2 + x * M) := by ring
    have h1 : x ^ 2 * W ^ 2 ≤ x * W ^ 2 :=
      mul_le_mul_of_nonneg_right (show x ^ 2 ≤ x by nlinarith) (sq_nonneg W)
    have h2 : x * (W ^ 2 + M) = x * W ^ 2 + x * M := by ring
    linarith
  have hd0 : ‖Sw - κ‖ ≤ 0 := by
    have ht : Tendsto (fun x : ℝ => x * (W ^ 2 + M)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun x : ℝ => x * (W ^ 2 + M)) (𝓝 0) (𝓝 (0 * (W ^ 2 + M))) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hx0] with x hx
    exact hbound x hx.1 hx.2.le
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hd0)

/-- **The curvature sum rule, real-rooted**: `Σ_τ τ⁻² = ∫u²g / (2∫g)` as a sum of positive terms. -/
theorem ghat_curvature {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hg : IntervalIntegrable g volume (-a) a)
    (heven : ∀ u, g (-u) = g u) (h0 : ghatC g a 0 ≠ 0) (hRR : RealRooted a g) :
    ∑' i : ZeroIdx (sqF (ghatC g a)), ‖i.1⁻¹‖
      = (∫ u in (-a)..a, u ^ 2 * g u) / (2 * ∫ u in (-a)..a, g u) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, ← ghat_sum_rule ha hg heven h0]
  congr 1; funext i
  exact (inv_zero_eq_norm hg heven h0 hRR i).symm

/-- `Ξ`'s curvature: `Σ'_j v_j` is the `z²` coefficient of `Ξ(z)/Ξ(0)`
(numerically `−Ξ''(0)/(2Ξ(0)) = 0.023105`, Theorem 1bu(ii)). -/
theorem xi_expansion (z : ℂ)
    (hz : ‖z‖ ^ 2 * ∑' j : ZeroIdx (sqF Xi), ‖j.1⁻¹‖ ≤ 1) :
    ‖Xi z / Xi 0 - (1 - z ^ 2 * ∑' j : ZeroIdx (sqF Xi), j.1⁻¹)‖
      ≤ (‖z‖ ^ 2 * ∑' j : ZeroIdx (sqF Xi), ‖j.1⁻¹‖) ^ 2 :=
  (hadamardW_Xi xiGrowth Xi_zero_ne_zero).expansion z hz

/-! ## C. The chain in its final form -/

/-- **Roadmap item 1 ⇒ `RiemannHypothesis`, with dodging D and the curvature condition.**
For even integrable ground states `g_n` on `[−a_n, a_n]` with `∫g_n ≠ 0`:
* `ĝ_n` real-rooted (item 1(b));
* dodging D (item 1(a), to tolerance): below `T_D(n)` (`t n = T_D(n)⁻²`, `t → 0`), every zero of `Ξ`
  is matched with its own zero of `ĝ_n`, the matched `|τ⁻² − γ⁻²|` summing to `η_n → 0`;
* the curvature `κ_n = ∫u²g_n / (2∫g_n)` converges to `Ξ`'s, `Re Σ_j γ_j⁻²`.
No bound on `Σ τ⁻²`, no tail condition, and nothing about `ĝ_n`'s unmatched zeros is assumed. -/
theorem rh_of_dodging_and_curvature_final {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (heven : ∀ n u, g n (-u) = g n u) (hg0 : ∀ n, (∫ u in (-(a n))..(a n), g n u) ≠ 0)
    (hRR : ∀ n, RealRooted (a n) (g n))
    {t η : ℕ → ℝ}
    (hD : ∀ n, ∃ (p : ZeroIdx (sqF (ghatC (g n) (a n))) → Prop)
      (e : {i // p i} ≃ {j : ZeroIdx (sqF Xi) // t n < ‖j.1⁻¹‖}),
      (∑' i : {i // p i}, ‖i.1.1⁻¹ - (e i).1.1⁻¹‖) ≤ η n)
    (hη : Tendsto η atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0))
    (hκ : Tendsto (fun n => (∫ u in (-(a n))..(a n), u ^ 2 * g n u)
        / (2 * ∫ u in (-(a n))..(a n), g n u))
      atTop (𝓝 (∑' j : ZeroIdx (sqF Xi), j.1⁻¹).re)) :
    RiemannHypothesis := by
  have h0 : ∀ n, ghatC (g n) (a n) 0 ≠ 0 := fun n => by
    rw [ghatC_zero]; exact_mod_cast hg0 n
  exact rh_of_dodging_and_curvature hint hRR
    (w := fun n (i : ZeroIdx (sqF (ghatC (g n) (a n)))) => i.1⁻¹)
    (v := fun j : ZeroIdx (sqF Xi) => j.1⁻¹)
    (fun n => hadamardW_ghat (ha n) (hint n) (heven n) (h0 n))
    (hadamardW_Xi xiGrowth Xi_zero_ne_zero) hD hη ht
    (hκ.congr fun n => (ghat_curvature (ha n) (hint n) (heven n) (h0 n) (hRR n)).symm)

end Pilot1ca

#print axioms Pilot1ca.pairing_of_matching
#print axioms Pilot1ca.tendsto_tsum_above
#print axioms Pilot1ca.rh_of_dodging_and_curvature
#print axioms Pilot1ca.HadamardW.expansion
#print axioms Pilot1ca.ghat_expansion
#print axioms Pilot1ca.ghat_sum_rule
#print axioms Pilot1ca.ghat_curvature
#print axioms Pilot1ca.xi_expansion
#print axioms Pilot1ca.rh_of_dodging_and_curvature_final
