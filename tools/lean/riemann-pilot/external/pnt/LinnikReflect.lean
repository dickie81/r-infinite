/-
# Round 526, part 2: the reflection of the smoothed character sum

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

For `ψ` primitive mod `f`, `f | q`, and `χ` the character mod `q` induced by `ψ`, the reflection factor is
`Φ(s) = f^{1/2−s}ε(ψ)·γ_{ψ⁻¹}(1 − s)/γ_ψ(s)·eulerQ(s)⁻¹` (part 1), so that `L(s, ψ) = Φ(s)L(1 − s, χ⁻¹)` for
`Re s < 1` (`LFunction_eq_Phi`). The kernel `kW_Λ(w) = Γ(w)(Λ^w − (Λ/2)^w)` is the Mellin transform of the weight
`e^{−x/Λ} − e^{−2x/Λ}`.

* `norm_Phi_le`: `|Φ(s)| ≤ f^{1/2−Re s}·CG(1 + |Im s|)^{1/2−Re s}·EQ(q)` on `−5/16 ≤ Re s ≤ 13/16`, with
  `EQ(q) = ∏_{p | q}(1 − p^{−3/16})⁻¹`.
* `LFunction_sub_dualS`: `L(1 − s, χ) − Σ_{m ≤ Z}χ(m)m^{s−1} = Σ_{m > Z}χ(m)m^{s−1}` for `Re s < 0`.
* `kW_isBigO`: `kW_Λ` is bounded near `0`, where `Γ` has its pole and `Λ^w − (Λ/2)^w` vanishes.
* `strip_bound`, `integrable_line`, `decay_strip`: the bounds that move a contour across the strip.
* `reflect`: for `ψ ≠ 1`, `Λ > 0`, lines `c₂ < 0 < c₁` with `−1/2 ≤ c₂`, `c₁ ≤ 2`, `−5/16 ≤ Re z + c₂ < 0` and
  `Re z + c₁ ≤ 13/16`, and any truncation `Z`,
  `∫ L(z + c₁ + iv, ψ)kW_Λ(c₁ + iv) dv = ∫ kW_Λ(c₁ + iv)Φ(z + c₁ + iv)Σ_{m ≤ Z}χ⁻¹(m)m^{z+c₁+iv−1} dv
  + ∫ kW_Λ(c₂ + iv)Φ(z + c₂ + iv)Σ_{m > Z}χ⁻¹(m)m^{z+c₂+iv−1} dv`. On `Re w = c₁` the functional equation splits
  `L(1 − z − w, χ⁻¹)` into its first `Z` terms and the rest, and the rest is moved to `Re w = c₂` (round 524's
  `LinnikGamma.verticalIntegral_sub_eq`, with residue `0` because `kW_Λ` is bounded at `0`), where it is the tail of
  the dual series. `reflect_aux` adds the integrability of both integrands on the right.
-/

import LinnikGammaRatio

open Complex Real Finset MeasureTheory Set Filter Topology

noncomputable section

namespace LinnikReflect

open DirichletCharacter

/-! ### The pieces of the reflected integrand -/

/-- The reflection factor `Φ(s) = f^{1/2−s}ε(ψ)·γ_{ψ⁻¹}(1 − s)/γ_ψ(s)·eulerQ(s)⁻¹`. -/
def Phi {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f) (q : ℕ) (s : ℂ) : ℂ :=
  (f : ℂ) ^ (1 / 2 - s) * rootNumber ψ * gr ψ s * (eulerQ ψ q s)⁻¹

/-- The kernel `Γ(w)(Λ^w − (Λ/2)^w)`, the Mellin transform of `e^{−x/Λ} − e^{−2x/Λ}` up to the factor `x^{−w}`. -/
def kW (Λ : ℝ) (w : ℂ) : ℂ := Complex.Gamma w * ((Λ : ℂ) ^ w - ((Λ / 2 : ℝ) : ℂ) ^ w)

/-- The finite dual sum `Σ_{1 ≤ m ≤ Z} χ(m)m^{s−1}`. -/
def dualS {q : ℕ} (χ : DirichletCharacter ℂ q) (Z : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 Z, χ m * (m : ℂ) ^ (s - 1)

/-- The dual tail `Σ_{m > Z} χ(m)m^{s−1}`. -/
def dualT {q : ℕ} (χ : DirichletCharacter ℂ q) (Z : ℕ) (s : ℂ) : ℂ :=
  ∑' m : ℕ, if Z < m then χ m * (m : ℂ) ^ (s - 1) else 0

/-- The constant `∏_{p | q}(1 − p^{−3/16})⁻¹` bounding `eulerQ(s)⁻¹` on `Re s ≤ 13/16`. -/
def EQ (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-(3 / 16 : ℝ)))⁻¹

lemma EQ_pos (q : ℕ) : 0 < EQ q := by
  unfold EQ
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have : (p : ℝ) ^ (-(3 / 16 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have : 0 < 1 - (p : ℝ) ^ (-(3 / 16 : ℝ)) := by linarith
  positivity

/-- **The functional equation with `Φ`**: `L(s, ψ) = Φ(s)L(1 − s, χ⁻¹)` for `Re s < 1`. -/
theorem LFunction_eq_Phi {f q : ℕ} [NeZero f] [NeZero q] (hfq : f ∣ q) {ψ : DirichletCharacter ℂ f}
    (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) {s : ℂ} (hs : s.re < 1) :
    LFunction ψ s = Phi ψ q s * LFunction (changeLevel hfq ψ)⁻¹ (1 - s) := by
  rw [LFunction_eq_reflect hfq hprim hψ hs]; rfl

/-- **The bound on `Φ`**: `|Φ(s)| ≤ f^{1/2−Re s}·CG(1 + |Im s|)^{1/2−Re s}·EQ(q)` on `−5/16 ≤ Re s ≤ 13/16`. -/
theorem norm_Phi_le {f : ℕ} [NeZero f] {ψ : DirichletCharacter ℂ f} (hprim : ψ.IsPrimitive) (q : ℕ) {s : ℂ}
    (hs1 : -5 / 16 ≤ s.re) (hs2 : s.re ≤ 13 / 16) :
    ‖Phi ψ q s‖ ≤ (f : ℝ) ^ (1 / 2 - s.re) * (CG * (1 + |s.im|) ^ (1 / 2 - s.re)) * EQ q := by
  unfold Phi
  rw [norm_mul, norm_mul, norm_mul, LinnikFE.norm_rootNumber hprim, mul_one]
  have hf : ‖(f : ℂ) ^ (1 / 2 - s)‖ ≤ (f : ℝ) ^ (1 / 2 - s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne f))]; simp
  have hg := norm_gr_le ψ hs1 hs2
  have hE := norm_eulerQ_inv_le ψ q (θ := 3 / 16) (by norm_num) (s := s) (by linarith)
  have hE' : ‖(eulerQ ψ q s)⁻¹‖ ≤ EQ q := by unfold EQ; simpa using hE
  have hCG := CG_pos
  exact mul_le_mul (mul_le_mul hf hg (norm_nonneg _) (by positivity)) hE' (norm_nonneg _) (by positivity)

/-- `|w|·|Γ(w)|·(1 + |Im w|)⁵ ≤ KG` on `−1/2 ≤ Re w ≤ 2` (round 518's `norm_Gamma_le'` at `w + 1`). -/
lemma norm_mul_Gamma_le {w : ℂ} (h1 : -1 / 2 ≤ w.re) (h2 : w.re ≤ 2) :
    ‖w‖ * ‖Complex.Gamma w‖ * (1 + |w.im|) ^ 5 ≤ InghamDensity.KG := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp; exact InghamDensity.KG_pos.le
  · have h := InghamDensity.norm_Gamma_le' (z := w + 1) (by simp; linarith) (by simp; linarith)
    have him : (w + 1).im = w.im := by simp
    rw [him, Complex.Gamma_add_one w hw, norm_mul] at h
    exact h

/-- `|Λ^w − (Λ/2)^w| ≤ 3Λ^{Re w}` for `Λ > 0`, `Re w ≥ −1`. -/
lemma norm_cpow_sub_half_le {Λ : ℝ} (hΛ : 0 < Λ) {w : ℂ} (hw : -1 ≤ w.re) :
    ‖(Λ : ℂ) ^ w - ((Λ / 2 : ℝ) : ℂ) ^ w‖ ≤ 3 * Λ ^ w.re := by
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hΛ, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Real.div_rpow hΛ.le (by norm_num)]
  have h2 : (1 : ℝ) / 2 ^ w.re ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = 2 * 2 ^ (-1 : ℝ) := by norm_num
      _ ≤ 2 * 2 ^ w.re := by gcongr; norm_num
  have hΛp : 0 < Λ ^ w.re := by positivity
  calc Λ ^ w.re + Λ ^ w.re / 2 ^ w.re = Λ ^ w.re * (1 + 1 / 2 ^ w.re) := by ring
    _ ≤ Λ ^ w.re * (1 + 2) := by gcongr
    _ = 3 * Λ ^ w.re := by ring

/-- `kW Λ` is differentiable at every `w ∉ {0, −1, −2, …}`. -/
lemma differentiableAt_kW {Λ : ℝ} (hΛ : 0 < Λ) {w : ℂ} (hw : ∀ m : ℕ, w ≠ -m) : DifferentiableAt ℂ (kW Λ) w := by
  unfold kW
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (Λ : ℂ) ^ w) w :=
    differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 hΛ.ne'))
  have h2 : DifferentiableAt ℂ (fun w : ℂ => ((Λ / 2 : ℝ) : ℂ) ^ w) w :=
    differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 (by positivity)))
  exact (Complex.differentiableAt_Gamma _ hw).mul (h1.sub h2)

/-- `kW Λ` is bounded near `0`: `Γ(w)(Λ^w − (Λ/2)^w) = Γ(w + 1)·slope`, and the slope of `Λ^w − (Λ/2)^w` at `0`
converges. -/
lemma kW_isBigO {Λ : ℝ} (hΛ : 0 < Λ) : (kW Λ) =O[𝓝[≠] 0] (1 : ℂ → ℂ) := by
  set g : ℂ → ℂ := fun w => (Λ : ℂ) ^ w - ((Λ / 2 : ℝ) : ℂ) ^ w with hg
  have hgd : Differentiable ℂ g := by
    intro w
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (Λ : ℂ) ^ w) w :=
      differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 hΛ.ne'))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => ((Λ / 2 : ℝ) : ℂ) ^ w) w :=
      differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 (by positivity)))
    exact h1.sub h2
  have hg0 : g 0 = 0 := by simp [hg]
  have hslope : Tendsto (fun w => slope g 0 w) (𝓝[≠] 0) (𝓝 (deriv g 0)) := (hgd 0).hasDerivAt.tendsto_slope
  have hG1 : Tendsto (fun w : ℂ => Complex.Gamma (w + 1)) (𝓝[≠] 0) (𝓝 (Complex.Gamma (0 + 1))) := by
    have hc : ContinuousAt (fun w : ℂ => Complex.Gamma (w + 1)) 0 := by
      have hd : DifferentiableAt ℂ Complex.Gamma (0 + 1) := by
        refine Complex.differentiableAt_Gamma _ fun m h => ?_
        have := congrArg Complex.re h
        simp at this
        linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      exact (hd.comp (0 : ℂ) (differentiableAt_id.add_const 1)).continuousAt
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hT := (hG1.mul hslope).isBigO_one ℂ
  refine hT.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw0 : w ≠ 0 := hw
  unfold kW
  rw [slope_def_field, hg0, sub_zero, sub_zero, Complex.Gamma_add_one w hw0]
  simp only [hg]
  field_simp

/-- `Φ` is differentiable at every `s` with `Re s < 1`. -/
lemma differentiableAt_Phi {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f) (q : ℕ) {s : ℂ} (hs : s.re < 1) :
    DifferentiableAt ℂ (Phi ψ q) s := by
  unfold Phi
  have hf0 : (f : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne f)
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (f : ℂ) ^ (1 / 2 - s)) s :=
    (differentiableAt_const _ |>.sub differentiableAt_id).const_cpow (Or.inl hf0)
  -- the Archimedean ratio
  have h2 : DifferentiableAt ℂ (gr ψ) s := by
    unfold gr
    have key : ∀ a : ℝ, 0 ≤ a →
        DifferentiableAt ℂ (fun s : ℂ => Complex.Gammaℝ (1 - s + a) * (Complex.Gammaℝ (s + a))⁻¹) s := by
      intro a ha
      have hA : DifferentiableAt ℂ (fun s : ℂ => Complex.Gammaℝ (1 - s + a)) s := by
        have hre : 0 < (1 - s + (a : ℂ)).re := by simp; linarith
        have hG : DifferentiableAt ℂ Complex.Gammaℝ (1 - s + a) := by
          have e : Complex.Gammaℝ = fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2) * Complex.Gamma (u / 2) := by
            funext u; exact Complex.Gammaℝ_def u
          rw [e]
          refine DifferentiableAt.mul ?_ ?_
          · exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
              (Or.inl (ofReal_ne_zero.2 Real.pi_ne_zero))
          · refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp _ (differentiableAt_id.div_const 2)
            have h1 := congrArg Complex.re h
            have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
            simp at h1
            linarith
        exact hG.comp s ((differentiableAt_const _ |>.sub differentiableAt_id).add_const _)
      have hB : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gammaℝ (s + a))⁻¹) s := by
        have h := Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const (a : ℂ))
        exact h s
      exact hA.mul hB
    rcases ψ.even_or_odd with h | h
    · have h' : ψ⁻¹.Even := (LinnikFE.even_inv_iff ψ).2 h
      have e : (fun s => gammaFactor ψ⁻¹ (1 - s) * (gammaFactor ψ s)⁻¹) =
          fun s : ℂ => Complex.Gammaℝ (1 - s + ((0 : ℝ) : ℂ)) * (Complex.Gammaℝ (s + ((0 : ℝ) : ℂ)))⁻¹ := by
        funext s; rw [h'.gammaFactor_def, h.gammaFactor_def]; simp
      rw [e]; exact key 0 le_rfl
    · have h' : ψ⁻¹.Odd := (LinnikFE.odd_inv_iff ψ).2 h
      have e : (fun s => gammaFactor ψ⁻¹ (1 - s) * (gammaFactor ψ s)⁻¹) =
          fun s : ℂ => Complex.Gammaℝ (1 - s + ((1 : ℝ) : ℂ)) * (Complex.Gammaℝ (s + ((1 : ℝ) : ℂ)))⁻¹ := by
        funext s; rw [h'.gammaFactor_def, h.gammaFactor_def]; push_cast; ring_nf
      rw [e]; exact key 1 zero_le_one
  -- the Euler factor
  have h3 : DifferentiableAt ℂ (eulerQ ψ q) s := by
    unfold eulerQ
    have : (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - ψ⁻¹ p * (p : ℂ) ^ (-(1 - s)))) =
        fun s : ℂ => ∏ p ∈ q.primeFactors, (fun s : ℂ => (1 - ψ⁻¹ p * (p : ℂ) ^ (-(1 - s)))) s := rfl
    rw [this]
    refine DifferentiableAt.fun_finsetProd fun p hp => ?_
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact (differentiableAt_const _).sub ((differentiableAt_const _).mul
      ((differentiableAt_const _ |>.sub differentiableAt_id).neg.const_cpow (Or.inl hp0)))
  have h4 : DifferentiableAt ℂ (fun s => (eulerQ ψ q s)⁻¹) s := h3.inv (eulerQ_ne_zero ψ q hs)
  exact ((h1.mul (differentiableAt_const _)).mul h2).mul h4

/-! ### The dual sums -/

/-- `|dualS χ Z s| ≤ Z` for `Re s ≤ 1`. -/
lemma norm_dualS_le {q : ℕ} (χ : DirichletCharacter ℂ q) (Z : ℕ) {s : ℂ} (hs : s.re ≤ 1) :
    ‖dualS χ Z s‖ ≤ Z := by
  unfold dualS
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m ∈ Finset.Icc 1 Z, ‖χ m * (m : ℂ) ^ (s - 1)‖ ≤ ∑ m ∈ Finset.Icc 1 Z, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos hm1]
        have h1 := DirichletCharacter.norm_le_one χ m
        have h2 : (m : ℝ) ^ (s - 1).re ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm1) (by simp; linarith)
        calc ‖χ m‖ * (m : ℝ) ^ (s - 1).re ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
          _ = 1 := one_mul 1
    _ = Z := by simp

/-- **The tail of the dual series**: `L(1 − s, χ) − Σ_{m ≤ Z} χ(m)m^{s−1} = Σ_{m > Z} χ(m)m^{s−1}` for `Re s < 0`. -/
lemma LFunction_sub_dualS {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Z : ℕ) {s : ℂ} (hs : s.re < 0) :
    LFunction χ (1 - s) - dualS χ Z s = dualT χ Z s := by
  have hre : 1 < (1 - s).re := by simp; linarith
  rw [LFunction_eq_LSeries χ hre]
  unfold LSeries dualS dualT
  set a : ℕ → ℂ := fun n => LSeries.term (fun n => χ n) (1 - s) n with ha
  have hsum : Summable a := ZMod.LSeriesSummable_of_one_lt_re (fun n => χ n) hre
  have hterm : ∀ n : ℕ, n ≠ 0 → a n = χ n * (n : ℂ) ^ (s - 1) := by
    intro n hn
    rw [ha]; dsimp only; rw [LSeries.term_of_ne_zero hn]
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [show s - 1 = -(1 - s) by ring, Complex.cpow_neg, div_eq_mul_inv]
  set f₁ : ℕ → ℂ := fun n => if n ∈ Finset.Icc 1 Z then a n else 0 with hf₁
  set f₂ : ℕ → ℂ := fun n => if Z < n then a n else 0 with hf₂
  have hsplit : ∀ n, a n = f₁ n + f₂ n := by
    intro n
    simp only [hf₁, hf₂, Finset.mem_Icc]
    by_cases h0 : n = 0
    · subst h0
      have : a 0 = 0 := by rw [ha]; simp
      simp [this]
    · by_cases h : n ≤ Z
      · rw [ite_eq_left ⟨by omega, h⟩, ite_eq_right (by omega)]; ring
      · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; ring
  have hs₁ : Summable f₁ := summable_of_ne_finset_zero (s := Finset.Icc 1 Z) fun n hn => by
    simp only [hf₁]; rw [ite_eq_right hn]
  have hs₂ : Summable f₂ := by
    refine Summable.of_norm_bounded hsum.norm fun n => ?_
    simp only [hf₂]
    split_ifs
    · exact le_rfl
    · simp
  have htsum : ∑' n, a n = ∑' n, f₁ n + ∑' n, f₂ n := by
    rw [← hs₁.tsum_add hs₂]; exact tsum_congr hsplit
  have ht₁ : ∑' n, f₁ n = ∑ m ∈ Finset.Icc 1 Z, χ m * (m : ℂ) ^ (s - 1) := by
    rw [tsum_eq_sum (s := Finset.Icc 1 Z) fun n hn => by simp only [hf₁]; rw [ite_eq_right hn]]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [hf₁]; rw [ite_eq_left hm]
    exact hterm m (by have := (Finset.mem_Icc.1 hm).1; omega)
  have ht₂ : ∑' n, f₂ n = ∑' m : ℕ, if Z < m then χ m * (m : ℂ) ^ (s - 1) else 0 := by
    apply tsum_congr
    intro n
    simp only [hf₂]
    split_ifs with h
    · exact hterm n (by omega)
    · rfl
  rw [show (∑' n, LSeries.term (fun n => χ n) (1 - s) n) = ∑' n, a n from rfl, htsum, ht₁, ht₂]
  ring

/-! ### The bounds on the strip -/

/-- `|L(1 − s, χ)| ≤ 6(q + 1)(|Im s| + 2)` on `−5/16 ≤ Re s ≤ 13/16`, for `χ ≠ 1`. -/
lemma norm_LFunction_one_sub_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hs1 : -5 / 16 ≤ s.re) (hs2 : s.re ≤ 13 / 16) :
    ‖LFunction χ (1 - s)‖ ≤ 6 * ((q : ℝ) + 1) * (|s.im| + 2) := by
  have him : |(1 - s).im| = |s.im| := by simp
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rcases le_or_gt (1 / 2) (1 - s).re with h | h
  · have h3 : (1 - s).re ≤ 3 := by simp; linarith
    refine (Linnik.LFunction_growth hχ h h3).trans ?_
    rw [him]
    have : (0 : ℝ) ≤ (q + 1) * (|s.im| + 2) := by positivity
    nlinarith
  · have hl : 3 / 16 ≤ (1 - s).re := by simp; linarith
    refine (LinnikSubconvex.norm_LFunction_strip_le hχ (by norm_num : (0 : ℝ) < 3 / 16) hl (by linarith)).trans ?_
    rw [him]
    have : (0 : ℝ) ≤ (q + 1) := by positivity
    have : ((q : ℝ) + 1) / (3 / 16) = 16 / 3 * ((q : ℝ) + 1) := by ring
    rw [this]
    nlinarith [abs_nonneg s.im]

/-- `|Φ(z + w)| ≤ f·CG·EQ(q)·(1 + |Im z|)(1 + |Im w|)` when `−5/16 ≤ Re(z + w) ≤ 13/16`. -/
lemma norm_Phi_le' {f : ℕ} [NeZero f] {ψ : DirichletCharacter ℂ f} (hprim : ψ.IsPrimitive) (q : ℕ) {z w : ℂ}
    (h1 : -5 / 16 ≤ (z + w).re) (h2 : (z + w).re ≤ 13 / 16) :
    ‖Phi ψ q (z + w)‖ ≤ (f : ℝ) * CG * EQ q * ((1 + |z.im|) * (1 + |w.im|)) := by
  have hP := norm_Phi_le hprim q h1 h2
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne f)
  set e := 1 / 2 - (z + w).re with he
  have he1 : e ≤ 1 := by rw [he]; linarith
  have hfe : (f : ℝ) ^ e ≤ f := by
    rcases le_or_gt e 0 with h | h
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hf1 h).trans hf1
    · calc (f : ℝ) ^ e ≤ (f : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hf1 he1
        _ = f := Real.rpow_one _
  have him : 1 + |(z + w).im| ≤ (1 + |z.im|) * (1 + |w.im|) := by
    have := abs_add_le z.im w.im
    simp only [add_im]
    nlinarith [abs_nonneg z.im, abs_nonneg w.im]
  have hb1 : (1 : ℝ) ≤ 1 + |(z + w).im| := by linarith [abs_nonneg (z + w).im]
  have hbe : (1 + |(z + w).im|) ^ e ≤ (1 + |z.im|) * (1 + |w.im|) := by
    rcases le_or_gt e 0 with h | h
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hb1 h).trans (by nlinarith [abs_nonneg z.im, abs_nonneg w.im])
    · calc (1 + |(z + w).im|) ^ e ≤ (1 + |(z + w).im|) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 he1
        _ = 1 + |(z + w).im| := Real.rpow_one _
        _ ≤ _ := him
  have hCG := CG_pos
  have hEQ := EQ_pos q
  calc ‖Phi ψ q (z + w)‖ ≤ (f : ℝ) ^ e * (CG * (1 + |(z + w).im|) ^ e) * EQ q := hP
    _ ≤ (f : ℝ) * (CG * ((1 + |z.im|) * (1 + |w.im|))) * EQ q := by gcongr
    _ = (f : ℝ) * CG * EQ q * ((1 + |z.im|) * (1 + |w.im|)) := by ring

/-! ### The strip bound and integrability -/

/-- `Λ^x ≤ Λ^{c₁} + Λ^{c₂}` for `c₂ ≤ x ≤ c₁`, `Λ > 0`. -/
lemma rpow_le_add_ends {Λ x c₁ c₂ : ℝ} (hΛ : 0 < Λ) (h1 : c₂ ≤ x) (h2 : x ≤ c₁) :
    Λ ^ x ≤ Λ ^ c₁ + Λ ^ c₂ := by
  rcases le_or_gt 1 Λ with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h h2
    have : 0 ≤ Λ ^ c₂ := by positivity
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hΛ h.le h1
    have : 0 ≤ Λ ^ c₁ := by positivity
    linarith

/-- **The strip bound**: if `|F(w)| ≤ B(1 + |Im w|)` on `c₂ ≤ Re w ≤ c₁`, then there
`|w|·|kW(w)Φ(z + w)F(w)|·(1 + |Im w|)³ ≤ KG·3(Λ^{c₁} + Λ^{c₂})·f·CG·EQ(q)(1 + |Im z|)·B`. -/
lemma strip_bound {f q : ℕ} [NeZero f] {ψ : DirichletCharacter ℂ f} (hprim : ψ.IsPrimitive) {Λ : ℝ}
    (hΛ : 0 < Λ) {z : ℂ} {c₁ c₂ : ℝ} (hc₂ : -1 / 2 ≤ c₂) (hc₁ : c₁ ≤ 2) (hs1 : -5 / 16 ≤ z.re + c₂)
    (hs2 : z.re + c₁ ≤ 13 / 16) (F : ℂ → ℂ) {B : ℝ}
    (hF : ∀ w : ℂ, c₂ ≤ w.re → w.re ≤ c₁ → ‖F w‖ ≤ B * (1 + |w.im|)) :
    ∀ w : ℂ, c₂ ≤ w.re → w.re ≤ c₁ →
      ‖w‖ * ‖kW Λ w * Phi ψ q (z + w) * F w‖ * (1 + |w.im|) ^ 3 ≤
        InghamDensity.KG * (3 * (Λ ^ c₁ + Λ ^ c₂) * ((f : ℝ) * CG * EQ q * (1 + |z.im|)) * B) := by
  intro w hw1 hw2
  have hG := norm_mul_Gamma_le (w := w) (by linarith) (by linarith)
  have hk : ‖kW Λ w‖ ≤ ‖Complex.Gamma w‖ * (3 * (Λ ^ c₁ + Λ ^ c₂)) := by
    unfold kW
    rw [norm_mul]
    have h3 := norm_cpow_sub_half_le hΛ (w := w) (by linarith)
    have h4 := rpow_le_add_ends hΛ hw1 hw2
    gcongr
    linarith
  have hre : (z + w).re = z.re + w.re := by simp
  have hP := norm_Phi_le' hprim q (z := z) (w := w) (by rw [hre]; linarith) (by rw [hre]; linarith)
  have hFw := hF w hw1 hw2
  have hB : 0 ≤ B := by
    have := (norm_nonneg (F w)).trans hFw
    have h1 : 0 < 1 + |w.im| := by positivity
    by_contra h; push Not at h
    nlinarith
  have hCG := CG_pos
  have hEQ := EQ_pos q
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have hKG := InghamDensity.KG_pos
  set ΛM := 3 * (Λ ^ c₁ + Λ ^ c₂) with hΛM
  have hΛM0 : 0 ≤ ΛM := by rw [hΛM]; positivity
  set P := (f : ℝ) * CG * EQ q * (1 + |z.im|) with hPdef
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hP' : ‖Phi ψ q (z + w)‖ ≤ P * (1 + |w.im|) := by
    rw [hPdef]; refine hP.trans (le_of_eq ?_); ring
  rw [norm_mul, norm_mul]
  have e1 : (1 + |w.im|) ^ 3 * (1 + |w.im|) * (1 + |w.im|) = (1 + |w.im|) ^ 5 := by ring
  calc ‖w‖ * (‖kW Λ w‖ * ‖Phi ψ q (z + w)‖ * ‖F w‖) * (1 + |w.im|) ^ 3
      ≤ ‖w‖ * ((‖Complex.Gamma w‖ * ΛM) * (P * (1 + |w.im|)) * (B * (1 + |w.im|))) * (1 + |w.im|) ^ 3 := by
        gcongr
    _ = (‖w‖ * ‖Complex.Gamma w‖ * (1 + |w.im|) ^ 5) * (ΛM * P * B) := by rw [← e1]; ring
    _ ≤ InghamDensity.KG * (ΛM * P * B) := by gcongr
    _ = InghamDensity.KG * (3 * (Λ ^ c₁ + Λ ^ c₂) * ((f : ℝ) * CG * EQ q * (1 + |z.im|)) * B) := by
        rw [hΛM, hPdef]

/-- **Integrability on a vertical line away from `0`** from a bound `|w|·|G(w)|·(1 + |Im w|)³ ≤ K`. -/
lemma integrable_line {G : ℂ → ℂ} {c μ K : ℝ} (hμ : 0 < μ) (hc : μ ≤ |c|)
    (hcont : Continuous fun v : ℝ => G (c + v * I))
    (hb : ∀ v : ℝ, ‖(c : ℂ) + v * I‖ * ‖G (c + v * I)‖ * (1 + |v|) ^ 3 ≤ K) :
    Integrable fun v : ℝ => G (c + v * I) := by
  have hK : 0 ≤ K := (by positivity : (0 : ℝ) ≤ ‖(c : ℂ) + (0 : ℝ) * I‖ * ‖G (c + (0 : ℝ) * I)‖ *
    (1 + |(0 : ℝ)|) ^ 3).trans (hb 0)
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (K / μ)) hcont.aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have hn : μ ≤ ‖(c : ℂ) + v * I‖ := by
    refine hc.trans ?_
    have := Complex.abs_re_le_norm ((c : ℂ) + v * I)
    simpa using this
  have h1 : 1 + v ^ 2 ≤ (1 + |v|) ^ 3 := by
    have h11 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    nlinarith [abs_nonneg v, sq_abs v, pow_le_pow_right₀ h11 (by norm_num : 2 ≤ 3)]
  have hv : 0 < 1 + v ^ 2 := by positivity
  have hb' := hb v
  rw [show K / μ * (1 + v ^ 2)⁻¹ = K / (μ * (1 + v ^ 2)) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  calc ‖G (c + v * I)‖ * (μ * (1 + v ^ 2)) ≤ ‖G (c + v * I)‖ * (‖(c : ℂ) + v * I‖ * (1 + |v|) ^ 3) := by
        gcongr
    _ = ‖(c : ℂ) + v * I‖ * ‖G (c + v * I)‖ * (1 + |v|) ^ 3 := by ring
    _ ≤ K := hb'

/-- **Uniform decay on the strip** from a bound `|w|·|G(w)|·(1 + |Im w|)³ ≤ K` there. -/
lemma decay_strip {G : ℂ → ℂ} {c₁ c₂ K : ℝ}
    (hb : ∀ w : ℂ, c₂ ≤ w.re → w.re ≤ c₁ → ‖w‖ * ‖G w‖ * (1 + |w.im|) ^ 3 ≤ K) :
    ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc c₂ c₁, ∀ y : ℝ, T₀ ≤ |y| → ‖G (x + y * I)‖ ≤ η := by
  intro η hη
  refine ⟨max 1 (K / η), fun x hx y hy => ?_⟩
  have hb' := hb (x + y * I) (by simpa using hx.1) (by simpa using hx.2)
  have him : ((x : ℂ) + y * I).im = y := by simp
  rw [him] at hb'
  have hy1 : 1 ≤ |y| := (le_max_left _ _).trans hy
  have hyK : K / η ≤ |y| := (le_max_right _ _).trans hy
  have hn : |y| ≤ ‖(x : ℂ) + y * I‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) + y * I)
    simpa using this
  have h3 : |y| ≤ (1 + |y|) ^ 3 := by
    have h11 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
    calc |y| ≤ 1 + |y| := by linarith
      _ ≤ (1 + |y|) ^ 3 := le_self_pow₀ h11 (by norm_num)
  have hG0 := norm_nonneg (G (x + y * I))
  have hKη : K ≤ η * |y| := by rwa [div_le_iff₀ hη, mul_comm] at hyK
  have hyy : |y| * |y| ≤ ‖(x : ℂ) + y * I‖ * (1 + |y|) ^ 3 := mul_le_mul hn h3 (abs_nonneg y) (norm_nonneg _)
  have : ‖G (x + y * I)‖ * (|y| * |y|) ≤ η * |y| * |y| := by
    calc ‖G (x + y * I)‖ * (|y| * |y|) ≤ ‖G (x + y * I)‖ * (‖(x : ℂ) + y * I‖ * (1 + |y|) ^ 3) := by gcongr
      _ = ‖(x : ℂ) + y * I‖ * ‖G (x + y * I)‖ * (1 + |y|) ^ 3 := by ring
      _ ≤ K := hb'
      _ ≤ η * |y| := hKη
      _ ≤ η * |y| * |y| := le_mul_of_one_le_right (by positivity) hy1
  have hy0 : 0 < |y| * |y| := by positivity
  nlinarith

/-- **The reflection of the smoothed character sum**, with the integrability of both reflected integrands. For `ψ`
primitive mod `f`, `ψ ≠ 1`, `f | q`, `χ` the character mod `q` induced by `ψ`, `Λ > 0`, and lines `c₂ < 0 < c₁` with
`−1/2 ≤ c₂`, `c₁ ≤ 2`, `−5/16 ≤ Re z + c₂ < 0` and `Re z + c₁ ≤ 13/16`, writing `w = c₁ + iv` on the left,
`∫ L(z + w, ψ)kW(w) dv = ∫_{(c₁)} kW(w)Φ(z + w)Σ_{m ≤ Z}χ⁻¹(m)m^{z+w−1} dv + ∫_{(c₂)} kW(w)Φ(z + w)Σ_{m > Z}χ⁻¹(m)m^{z+w−1} dv`,
and both integrands on the right are integrable.
On `Re w = c₁` the functional equation (`LFunction_eq_Phi`) splits `L(1 − z − w, χ⁻¹)` into the first `Z` terms and the
rest; the rest is moved to `Re w = c₂` (round 524's `LinnikGamma.verticalIntegral_sub_eq` with residue `0`: `kW` is
bounded at `0`, `kW_isBigO`), where it is the tail of the series (`LFunction_sub_dualS`). -/
theorem reflect_aux {f q : ℕ} [NeZero f] [NeZero q] (hfq : f ∣ q) {ψ : DirichletCharacter ℂ f}
    (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) {Λ : ℝ} (hΛ : 0 < Λ) {z : ℂ} {c₁ c₂ : ℝ}
    (hc₂0 : c₂ < 0) (hc₁0 : 0 < c₁) (hc₂ : -1 / 2 ≤ c₂) (hc₁ : c₁ ≤ 2) (hs1 : -5 / 16 ≤ z.re + c₂)
    (hs3 : z.re + c₂ < 0) (hs2 : z.re + c₁ ≤ 13 / 16) (Z : ℕ) :
    ((∫ v : ℝ, LFunction ψ (z + (c₁ + v * I)) * kW Λ (c₁ + v * I)) =
      (∫ v : ℝ, kW Λ (c₁ + v * I) * Phi ψ q (z + (c₁ + v * I)) *
          dualS (changeLevel hfq ψ)⁻¹ Z (z + (c₁ + v * I))) +
      ∫ v : ℝ, kW Λ (c₂ + v * I) * Phi ψ q (z + (c₂ + v * I)) *
          dualT (changeLevel hfq ψ)⁻¹ Z (z + (c₂ + v * I))) ∧
    (Integrable fun v : ℝ => kW Λ (c₁ + v * I) * Phi ψ q (z + (c₁ + v * I)) *
          dualS (changeLevel hfq ψ)⁻¹ Z (z + (c₁ + v * I))) ∧
    (Integrable fun v : ℝ => kW Λ (c₂ + v * I) * Phi ψ q (z + (c₂ + v * I)) *
          dualT (changeLevel hfq ψ)⁻¹ Z (z + (c₂ + v * I))) := by
  set χ := changeLevel hfq ψ with hχdef
  have hχ1 : χ ≠ 1 := fun h => hψ ((changeLevel_eq_one_iff hfq).1 h)
  have hχi : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ1
  set G1 : ℂ → ℂ := fun w => kW Λ w * Phi ψ q (z + w) * dualS χ⁻¹ Z (z + w) with hG1
  set GR : ℂ → ℂ := fun w => kW Λ w * Phi ψ q (z + w) * (LFunction χ⁻¹ (1 - (z + w)) - dualS χ⁻¹ Z (z + w))
    with hGR
  have hre : ∀ w : ℂ, (z + w).re = z.re + w.re := fun w => by simp
  have him : ∀ w : ℂ, (z + w).im = z.im + w.im := fun w => by simp
  -- the third factors on the strip
  have hS : ∀ w : ℂ, c₂ ≤ w.re → w.re ≤ c₁ → ‖dualS χ⁻¹ Z (z + w)‖ ≤ (Z : ℝ) * (1 + |w.im|) := by
    intro w _ hw2
    refine (norm_dualS_le χ⁻¹ Z (s := z + w) (by rw [hre]; linarith)).trans ?_
    exact le_mul_of_one_le_right (Nat.cast_nonneg Z) (by linarith [abs_nonneg w.im])
  have hL : ∀ w : ℂ, c₂ ≤ w.re → w.re ≤ c₁ →
      ‖LFunction χ⁻¹ (1 - (z + w)) - dualS χ⁻¹ Z (z + w)‖ ≤
        (6 * ((q : ℝ) + 1) * (|z.im| + 2) + Z) * (1 + |w.im|) := by
    intro w hw1 hw2
    have h1 := norm_LFunction_one_sub_strip hχi (s := z + w) (by rw [hre]; linarith) (by rw [hre]; linarith)
    have h2 := hS w hw1 hw2
    rw [him] at h1
    have h3 : |z.im + w.im| + 2 ≤ (|z.im| + 2) * (1 + |w.im|) := by
      have := abs_add_le z.im w.im
      nlinarith [abs_nonneg z.im, abs_nonneg w.im]
    have hq0 : (0 : ℝ) ≤ 6 * ((q : ℝ) + 1) := by positivity
    calc ‖LFunction χ⁻¹ (1 - (z + w)) - dualS χ⁻¹ Z (z + w)‖
        ≤ ‖LFunction χ⁻¹ (1 - (z + w))‖ + ‖dualS χ⁻¹ Z (z + w)‖ := norm_sub_le _ _
      _ ≤ 6 * ((q : ℝ) + 1) * ((|z.im| + 2) * (1 + |w.im|)) + (Z : ℝ) * (1 + |w.im|) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h3 hq0)
      _ = (6 * ((q : ℝ) + 1) * (|z.im| + 2) + Z) * (1 + |w.im|) := by ring
  have hbR := strip_bound hprim (q := q) hΛ (z := z) hc₂ hc₁ hs1 hs2
    (fun w => LFunction χ⁻¹ (1 - (z + w)) - dualS χ⁻¹ Z (z + w)) hL
  have hb1 := strip_bound hprim (q := q) hΛ (z := z) hc₂ hc₁ hs1 hs2 (fun w => dualS χ⁻¹ Z (z + w)) hS
  -- differentiability
  have hdS : ∀ s : ℂ, DifferentiableAt ℂ (dualS χ⁻¹ Z) s := by
    intro s
    unfold dualS
    have : (fun s : ℂ => ∑ m ∈ Finset.Icc 1 Z, χ⁻¹ m * (m : ℂ) ^ (s - 1)) =
        fun s : ℂ => ∑ m ∈ Finset.Icc 1 Z, (fun s : ℂ => χ⁻¹ m * (m : ℂ) ^ (s - 1)) s := rfl
    rw [this]
    refine DifferentiableAt.fun_sum fun m hm => ?_
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (Finset.mem_Icc.1 hm).1; omega)
    exact (differentiableAt_const _).mul ((differentiableAt_id.sub_const 1).const_cpow (Or.inl hm0))
  have hdF : ∀ w : ℂ, (z + w).re < 1 →
      DifferentiableAt ℂ (fun w => Phi ψ q (z + w)) w ∧ DifferentiableAt ℂ (fun w => dualS χ⁻¹ Z (z + w)) w ∧
        DifferentiableAt ℂ (fun w => LFunction χ⁻¹ (1 - (z + w))) w := by
    intro w hw
    refine ⟨(differentiableAt_Phi ψ q hw).comp w (differentiableAt_id.const_add z),
      (hdS (z + w)).comp w (differentiableAt_id.const_add z), ?_⟩
    exact (differentiable_LFunction hχi (1 - (z + w))).comp w
      ((differentiableAt_id.const_add z).const_sub 1)
  have hdR : ∀ w : ℂ, (∀ m : ℕ, w ≠ -m) → (z + w).re < 1 → DifferentiableAt ℂ GR w := by
    intro w hw hw1
    obtain ⟨h1, h2, h3⟩ := hdF w hw1
    exact ((differentiableAt_kW hΛ hw).mul h1).mul (h3.sub h2)
  have hd1 : ∀ w : ℂ, (∀ m : ℕ, w ≠ -m) → (z + w).re < 1 → DifferentiableAt ℂ G1 w := by
    intro w hw hw1
    obtain ⟨h1, h2, _⟩ := hdF w hw1
    exact ((differentiableAt_kW hΛ hw).mul h1).mul h2
  -- points of the strip other than `0` are not poles of `Γ`
  have hnp : ∀ w : ℂ, c₂ ≤ w.re → w ≠ 0 → ∀ m : ℕ, w ≠ -m := by
    intro w hw h0 m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · exact h0 (by simpa using hm)
    · have := congrArg Complex.re hm
      simp at this
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      linarith
  have hline : ∀ c : ℝ, c ≠ 0 → c₂ ≤ c → ∀ v : ℝ, ∀ m : ℕ, ((c : ℂ) + v * I) ≠ -m := by
    intro c hc0 hc v
    apply hnp _ (by simpa using hc)
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hc0 this
  have hcontR : ∀ c : ℝ, c ≠ 0 → c₂ ≤ c → c ≤ c₁ → Continuous fun v : ℝ => GR (c + v * I) := by
    intro c hc0 hc1 hc2
    rw [continuous_iff_continuousAt]
    intro v
    exact ContinuousAt.comp (g := GR) (f := fun v : ℝ => (c : ℂ) + v * I)
      (hdR _ (hline c hc0 hc1 v) (by rw [hre]; simp; linarith)).continuousAt (by fun_prop)
  have hcont1 : Continuous fun v : ℝ => G1 (c₁ + v * I) := by
    rw [continuous_iff_continuousAt]
    intro v
    exact ContinuousAt.comp (g := G1) (f := fun v : ℝ => (c₁ : ℂ) + v * I)
      (hd1 _ (hline c₁ hc₁0.ne' (by linarith) v) (by rw [hre]; simp; linarith)).continuousAt (by fun_prop)
  -- integrability on the two lines
  have hlineb : ∀ (G : ℂ → ℂ) (K c : ℝ), c₂ ≤ c → c ≤ c₁ →
      (∀ w : ℂ, c₂ ≤ w.re → w.re ≤ c₁ → ‖w‖ * ‖G w‖ * (1 + |w.im|) ^ 3 ≤ K) →
      ∀ v : ℝ, ‖(c : ℂ) + v * I‖ * ‖G (c + v * I)‖ * (1 + |v|) ^ 3 ≤ K := by
    intro G K c h1 h2 hb v
    have := hb (c + v * I) (by simpa using h1) (by simpa using h2)
    have hi : ((c : ℂ) + v * I).im = v := by simp
    rwa [hi] at this
  have hintR1 : Integrable fun v : ℝ => GR (c₁ + v * I) :=
    integrable_line hc₁0 (le_abs_self c₁) (hcontR c₁ hc₁0.ne' (by linarith) le_rfl)
      (hlineb GR _ c₁ (by linarith) le_rfl hbR)
  have hintR2 : Integrable fun v : ℝ => GR (c₂ + v * I) :=
    integrable_line (neg_pos.2 hc₂0) (neg_le_abs c₂) (hcontR c₂ hc₂0.ne le_rfl (by linarith))
      (hlineb GR _ c₂ le_rfl (by linarith) hbR)
  have hint1 : Integrable fun v : ℝ => G1 (c₁ + v * I) :=
    integrable_line hc₁0 (le_abs_self c₁) hcont1 (hlineb G1 _ c₁ (by linarith) le_rfl hb1)
  -- the shift of the remainder
  have hhol : HolomorphicOn GR ((Icc c₂ c₁ ×ℂ univ) \ {0}) := by
    intro w hw
    have hw1 : c₂ ≤ w.re := hw.1.1.1
    have hw2 : w.re ≤ c₁ := hw.1.1.2
    have hw0 : w ≠ 0 := hw.2
    exact (hdR w (hnp w hw1 hw0) (by rw [hre]; linarith)).differentiableWithinAt
  have hres : (GR - fun w ↦ (0 : ℂ) / (w - 0)) =O[𝓝[≠] 0] (1 : ℂ → ℂ) := by
    have e : (GR - fun w ↦ (0 : ℂ) / (w - 0)) =
        fun w => kW Λ w * (Phi ψ q (z + w) * (LFunction χ⁻¹ (1 - (z + w)) - dualS χ⁻¹ Z (z + w))) := by
      funext w; simp only [Pi.sub_apply, zero_div, sub_zero, hGR]; ring
    rw [e]
    have hz0 : (z + 0).re < 1 := by rw [hre]; simp; linarith
    obtain ⟨h1, h2, h3⟩ := hdF 0 hz0
    have hc : ContinuousAt (fun w => Phi ψ q (z + w) * (LFunction χ⁻¹ (1 - (z + w)) - dualS χ⁻¹ Z (z + w))) 0 :=
      (h1.mul (h3.sub h2)).continuousAt
    have hF := (hc.tendsto.isBigO_one ℂ).mono (nhdsWithin_le_nhds (s := {0}ᶜ))
    have hk := kW_isBigO hΛ
    have := hk.mul hF
    refine this.congr' (Eventually.of_forall fun _ => rfl) (Eventually.of_forall fun _ => ?_)
    simp
  have hdecay := decay_strip (G := GR) hbR
  have hshift := LinnikGamma.verticalIntegral_sub_eq hc₂0 hc₁0 0 hhol hres hintR1 hintR2 hdecay
  rw [mul_zero, sub_eq_zero] at hshift
  simp only [VerticalIntegral] at hshift
  have hRR : ∫ v : ℝ, GR (c₁ + v * I) = ∫ v : ℝ, GR (c₂ + v * I) := smul_right_injective ℂ I_ne_zero hshift
  -- assemble
  have hpt : ∀ v : ℝ, LFunction ψ (z + (c₁ + v * I)) * kW Λ (c₁ + v * I) = G1 (c₁ + v * I) + GR (c₁ + v * I) := by
    intro v
    have hlt : (z + ((c₁ : ℂ) + v * I)).re < 1 := by rw [hre]; simp; linarith
    rw [LFunction_eq_Phi hfq hprim hψ hlt]
    simp only [hG1, hGR]
    ring
  have hT : ∀ v : ℝ, GR (c₂ + v * I) =
      kW Λ (c₂ + v * I) * Phi ψ q (z + (c₂ + v * I)) * dualT χ⁻¹ Z (z + (c₂ + v * I)) := by
    intro v
    have hlt : (z + ((c₂ : ℂ) + v * I)).re < 0 := by rw [hre]; simp; linarith
    simp only [hGR]
    rw [LFunction_sub_dualS χ⁻¹ Z hlt]
  refine ⟨?_, hint1, hintR2.congr (Eventually.of_forall hT)⟩
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hint1 hintR1, hRR,
    integral_congr_ae (Eventually.of_forall hT)]

/-- **The reflection of the smoothed character sum** (the identity of `reflect_aux`). -/
theorem reflect {f q : ℕ} [NeZero f] [NeZero q] (hfq : f ∣ q) {ψ : DirichletCharacter ℂ f}
    (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) {Λ : ℝ} (hΛ : 0 < Λ) {z : ℂ} {c₁ c₂ : ℝ}
    (hc₂0 : c₂ < 0) (hc₁0 : 0 < c₁) (hc₂ : -1 / 2 ≤ c₂) (hc₁ : c₁ ≤ 2) (hs1 : -5 / 16 ≤ z.re + c₂)
    (hs3 : z.re + c₂ < 0) (hs2 : z.re + c₁ ≤ 13 / 16) (Z : ℕ) :
    (∫ v : ℝ, LFunction ψ (z + (c₁ + v * I)) * kW Λ (c₁ + v * I)) =
      (∫ v : ℝ, kW Λ (c₁ + v * I) * Phi ψ q (z + (c₁ + v * I)) *
          dualS (changeLevel hfq ψ)⁻¹ Z (z + (c₁ + v * I))) +
      ∫ v : ℝ, kW Λ (c₂ + v * I) * Phi ψ q (z + (c₂ + v * I)) *
          dualT (changeLevel hfq ψ)⁻¹ Z (z + (c₂ + v * I)) :=
  (reflect_aux hfq hprim hψ hΛ hc₂0 hc₁0 hc₂ hc₁ hs1 hs3 hs2 Z).1

end LinnikReflect

#print axioms LinnikReflect.LFunction_eq_Phi
#print axioms LinnikReflect.norm_Phi_le
#print axioms LinnikReflect.kW_isBigO
#print axioms LinnikReflect.reflect_aux
#print axioms LinnikReflect.reflect
