/-
# Rung 3, closed: the growth bound for ζ and the zero-free region it gives (rounds 212–214)

Plain statements.
* `zeta_bound_large`: given `GrowthSum a` with `1/2 ≤ a ≤ 1`, there is `B` with `|ζ(σ+it)| ≤ B·log|t|` whenever
  `log|t| ≥ 25` and `1 − (log|t|)^{−a} ≤ σ ≤ 2`.
  Proof: PNT+'s `Zeta0EqZeta` writes `ζ(s) = Σ_{n≤X} n^{−s} − X^{1−s}/(1−s) − X^{−s}/2 + R`,
  with `|R| ≤ 2|t|X^{−σ}/σ` (`ZetaBnd_aux1`). Take `X = ⌊|t|^{5/4}⌋`. Then the sum is at most
  `B·log|t|` by the layer-II growth bound (`GrowthSum`), and the other three terms are at most
  `1`, `1/2` and `5`, since `σ ≥ 4/5`.
* `zeta_bound_compact`: ζ is bounded on `0 ≤ σ ≤ 2`, `3 ≤ |t| ≤ T` (compactness; `s ≠ 1`).
* `polylogGrowth_of`: any layer-II growth bound `GrowthSum a` (`1/2 ≤ a ≤ 1`) gives
  `PolylogGrowth a K`.
* `polylogGrowth_kv`: `PolylogGrowth a K` holds for every `4/5 ≤ a ≤ 1` (round 213; `6/7` in
  round 212).
* `polylogGrowth_sharp`: `PolylogGrowth a K` for every `2/3 < a ≤ 1` (round 214).
* `zeroFree_kv`: ζ has no zeros in `σ ≥ 1 − A/(log|t|)^{n₁}` for every `n₁ > 2/3`.
* `rung3_kv`: `ψ(x) − x = O(x·exp(−c(log x)^{1/(1+n₁)}))` for every `n₁ > 2/3`, i.e. every
  exponent below `3/5` (the Korobov–Vinogradov exponent, without its `log log` refinement).

Every input is proved. There are no hypotheses and no RH-conditional steps.
-/
import Landau
import VinoFam

open Complex Set Filter MeasureTheory

namespace KVBridge

lemma sum_range_eq_Ioc (N : ℕ) (s : ℂ) (hs : s ≠ 0) :
    ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s = ∑ n ∈ Finset.Ioc 0 N, 1 / (n : ℂ) ^ s := by
  have h : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [h, Finset.sum_insert (by simp), Nat.cast_zero, Complex.zero_cpow hs, div_zero, zero_add]

lemma zeta_split {N : ℕ} (hN : 1 ≤ N) {σ t : ℝ} (hσ : 0 < σ) (ht : t ≠ 0) :
    riemannZeta (σ + t * I) = ∑ n ∈ Finset.Ioc 0 N, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I) +
      (-(N : ℂ) ^ (1 - ((σ : ℂ) + t * I))) / (1 - ((σ : ℂ) + t * I)) +
      (-(N : ℂ) ^ (-((σ : ℂ) + t * I))) / 2 +
      ((σ : ℂ) + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ : ℂ) + t * I) + 1) := by
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; exact ht this
  have hs0 : (σ : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [← Zeta0EqZeta (N := N) (by omega) (by simp; exact hσ) hs1, riemannZeta0, sum_range_eq_Ioc N _ hs0]

lemma pos_of_log_ge {t : ℝ} {c : ℝ} (hc : 0 < c) (hL : c ≤ Real.log |t|) : 0 < |t| := by
  rcases (abs_nonneg t).lt_or_eq with h | h
  · exact h
  · rw [← h, Real.log_zero] at hL; linarith

/-- The Dirichlet-polynomial growth bound of layer II, at exponent `a`. -/
def GrowthSum (a : ℝ) : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∀ t σ : ℝ, 1 ≤ Real.log |t| → 1 - Real.log |t| ^ (-a) ≤ σ →
    ∀ X : ℕ, (X : ℝ) ≤ |t| ^ ((5 : ℝ) / 4) →
      ‖∑ n ∈ Finset.Ioc 0 X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ B * Real.log |t|

/-- **ζ from its truncated sum.** For `log|t| ≥ 25` and `4/5 ≤ σ ≤ 2`, with `X = ⌊|t|^{5/4}⌋`,
`|ζ(σ+it)| ≤ |Σ_{n≤X} n^{−σ−it}| + 13/2`. -/
theorem zeta_le_sum {t σ : ℝ} (hL : 25 ≤ Real.log |t|) (hσ45 : 4 / 5 ≤ σ) (hσ2 : σ ≤ 2) :
    ‖riemannZeta (σ + t * I)‖ ≤
      ‖∑ n ∈ Finset.Ioc 0 ⌊|t| ^ ((5 : ℝ) / 4)⌋₊, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ + 13 / 2 := by
  set L := Real.log |t| with hLdef
  have htpos : 0 < |t| := pos_of_log_ge (by norm_num) hL
  have htexp : |t| = Real.exp L := (Real.exp_log htpos).symm
  have ht2 : 2 ≤ |t| := by
    rw [htexp]; have := Real.add_one_le_exp L; linarith
  have ht1 : 1 ≤ |t| := by linarith
  have ht0 : t ≠ 0 := abs_pos.mp htpos
  have hσ0 : 0 < σ := by linarith
  -- the truncation point
  set Y := |t| ^ ((5 : ℝ) / 4) with hYdef
  have hY1 : 1 ≤ Y := Real.one_le_rpow ht1 (by norm_num)
  set X := ⌊Y⌋₊ with hXdef
  have hX1 : 1 ≤ X := Nat.le_floor (by exact_mod_cast hY1)
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hXY : (X : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hYX : Y ≤ 2 * X := by have := Nat.lt_floor_add_one Y; linarith
  have hX0 : (0 : ℝ) < X := by linarith
  rw [zeta_split hX1 hσ0 ht0]
  -- the four terms
  have hT2 : ‖(-(X : ℂ) ^ (1 - ((σ : ℂ) + t * I))) / (1 - ((σ : ℂ) + t * I))‖ ≤ 1 := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos (by omega)]
    have hre : (1 - ((σ : ℂ) + t * I)).re = 1 - σ := by simp
    rw [hre]
    have hden : |t| ≤ ‖1 - ((σ : ℂ) + t * I)‖ := by
      have := Complex.abs_im_le_norm (1 - ((σ : ℂ) + t * I))
      simpa using this
    have hnum : (X : ℝ) ^ (1 - σ) ≤ |t| := by
      calc (X : ℝ) ^ (1 - σ) ≤ (X : ℝ) ^ ((1 : ℝ) / 5) :=
            Real.rpow_le_rpow_of_exponent_le hXr (by linarith)
        _ ≤ Y ^ ((1 : ℝ) / 5) := Real.rpow_le_rpow hX0.le hXY (by norm_num)
        _ = |t| ^ ((1 : ℝ) / 4) := by
            rw [hYdef, ← Real.rpow_mul htpos.le]; norm_num
        _ ≤ |t| ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
        _ = |t| := Real.rpow_one _
    rw [div_le_one (by linarith)]
    linarith
  have hT3 : ‖(-(X : ℂ) ^ (-((σ : ℂ) + t * I))) / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos (by omega)]
    have hre : (-((σ : ℂ) + t * I)).re = -σ := by simp
    rw [hre]
    have : (X : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hXr (by linarith)
    simp only [Complex.norm_ofNat]
    linarith
  have hT4 := ZetaBnd_aux1 X hX1 (σ := σ) (t := t) ⟨hσ0, hσ2⟩ ht2
  have hXσ : (X : ℝ) ^ (-σ) ≤ 2 / |t| := by
    have hY2 : (0 : ℝ) < Y / 2 := by linarith
    calc (X : ℝ) ^ (-σ) ≤ (X : ℝ) ^ (-(4 / 5 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hXr (by linarith)
      _ ≤ (Y / 2) ^ (-(4 / 5 : ℝ)) := Real.rpow_le_rpow_of_nonpos hY2 (by linarith) (by norm_num)
      _ = |t| ^ (-(1 : ℝ)) * (2 : ℝ) ^ ((4 : ℝ) / 5) := by
          rw [Real.div_rpow (by linarith) (by norm_num), hYdef, ← Real.rpow_mul htpos.le,
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
      _ ≤ |t| ^ (-(1 : ℝ)) * 2 := by
          gcongr
          calc (2 : ℝ) ^ ((4 : ℝ) / 5) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
      _ = 2 / |t| := by rw [Real.rpow_neg_one]; ring
  have hT4' : 2 * |t| * (X : ℝ) ^ (-σ) / σ ≤ 5 := by
    rw [div_le_iff₀ hσ0]
    have : |t| * (X : ℝ) ^ (-σ) ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hXσ htpos.le
      rwa [mul_div_cancel₀ _ htpos.ne'] at this
    nlinarith
  calc _ ≤ ‖∑ n ∈ Finset.Ioc 0 X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ +
        ‖(-(X : ℂ) ^ (1 - ((σ : ℂ) + t * I))) / (1 - ((σ : ℂ) + t * I))‖ +
        ‖(-(X : ℂ) ^ (-((σ : ℂ) + t * I))) / 2‖ +
        ‖((σ : ℂ) + t * I) * ∫ x in Ioi (X : ℝ), (⌊x⌋ + 1 / 2 - x) /
          (x : ℂ) ^ (((σ : ℂ) + t * I) + 1)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
        exact add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ‖∑ n ∈ Finset.Ioc 0 X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ + 1 + 1 / 2 + 5 := by
        refine add_le_add (add_le_add (add_le_add le_rfl hT2) hT3) (hT4.trans hT4')
    _ = _ := by ring

/-- **ζ on the thin strip, for large `|t|`.** -/
theorem zeta_bound_large {a : ℝ} (ha1 : 1 / 2 ≤ a) (_ha2 : a ≤ 1) (hS : GrowthSum a) :
    ∃ B : ℝ, 0 < B ∧ ∀ t σ : ℝ, 25 ≤ Real.log |t| → 1 - Real.log |t| ^ (-a) ≤ σ → σ ≤ 2 →
      ‖riemannZeta (σ + t * I)‖ ≤ B * Real.log |t| := by
  obtain ⟨B, hB0, hB⟩ := hS
  refine ⟨B + 7, by linarith, fun t σ hL hσ hσ2 => ?_⟩
  set L := Real.log |t| with hLdef
  have hL0 : 0 < L := by linarith
  -- `(log|t|)^{−a} ≤ 1/5`
  have hLa : 5 ≤ L ^ a := by
    have h1 : L ^ ((1 : ℝ) / 2) ≤ L ^ a :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (25 : ℝ) ^ ((1 : ℝ) / 2) ≤ L ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by norm_num) hL (by norm_num)
    have h3 : (25 : ℝ) ^ ((1 : ℝ) / 2) = 5 := by
      rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have hδ : L ^ (-a) ≤ 1 / 5 := by
    rw [Real.rpow_neg hL0.le, one_div]
    exact inv_anti₀ (by norm_num) hLa
  have hT1 := hB t σ (by linarith) hσ _ (Nat.floor_le (Real.rpow_nonneg (abs_nonneg t) _))
  calc _ ≤ _ := zeta_le_sum hL (by linarith) hσ2
    _ ≤ B * L + 13 / 2 := by linarith
    _ ≤ (B + 7) * L := by nlinarith

/-- **ζ on a compact piece.** -/
theorem zeta_bound_compact (T : ℝ) :
    ∃ M : ℝ, ∀ t σ : ℝ, 3 ≤ |t| → |t| ≤ T → 0 ≤ σ → σ ≤ 2 →
      ‖riemannZeta (σ + t * I)‖ ≤ M := by
  set S : Set (ℝ × ℝ) := Icc 0 2 ×ˢ (Icc (-T) (-3) ∪ Icc 3 T) with hSdef
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_Icc.union isCompact_Icc)
  have hg : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) := by fun_prop
  have hcont : ContinuousOn (fun p : ℝ × ℝ => riemannZeta ((p.1 : ℂ) + p.2 * I)) S := by
    intro p hp
    have hp2 : p.2 ≠ 0 := by
      rcases hp.2 with h | h
      · have := h.2; intro h0; rw [h0] at this; linarith
      · have := h.1; intro h0; rw [h0] at this; linarith
    have hne : (p.1 : ℂ) + p.2 * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; exact hp2 this
    show ContinuousWithinAt (riemannZeta ∘ fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) S p
    have hζ : ContinuousAt riemannZeta ((fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * I) p) :=
      (differentiableAt_riemannZeta hne).continuousAt
    exact (ContinuousAt.comp (x := p) (f := fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * I) hζ hg.continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨M, fun t σ ht3 htT hσ0 hσ2 => hM (σ, t) ⟨⟨hσ0, hσ2⟩, ?_⟩⟩
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht3 htT
    exact Or.inr ⟨ht3, htT⟩
  · rw [abs_of_neg h] at ht3 htT
    exact Or.inl ⟨by linarith, by linarith⟩

/-- **Any layer-II growth bound gives the growth hypothesis of Landau's lemma.** -/
theorem polylogGrowth_of {a : ℝ} (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 1) (hS : GrowthSum a) :
    ∃ K : ℝ, 0 < K ∧ Landau.PolylogGrowth a K := by
  obtain ⟨B, hB0, hB⟩ := zeta_bound_large ha1 ha2 hS
  obtain ⟨M, hM⟩ := zeta_bound_compact (Real.exp 25)
  refine ⟨max B (max M 1), by positivity, ?_⟩
  intro t ht3 σ hσ hσ2
  set K := max B (max M 1) with hKdef
  have hK1 : 1 ≤ K := le_trans (le_max_right M 1) (le_max_right B _)
  set L := Real.log |t| with hLdef
  have htpos : 0 < |t| := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le htpos]
    have := Real.exp_one_lt_d9; linarith
  have hLK : L ≤ L ^ K := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ K := Real.rpow_le_rpow_of_exponent_le hL1 hK1
  have h1LK : 1 ≤ L ^ K := Real.one_le_rpow hL1 (by linarith)
  rcases le_or_gt 25 L with hbig | hsmall
  · calc ‖riemannZeta (σ + t * I)‖ ≤ B * L := hB t σ hbig hσ hσ2
      _ ≤ K * L := by gcongr; exact le_max_left _ _
      _ ≤ K * L ^ K := by gcongr
  · have htT : |t| ≤ Real.exp 25 := by
      rw [← Real.exp_log htpos]; exact Real.exp_le_exp.mpr hsmall.le
    have hσ0 : 0 ≤ σ := by
      have : L ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
      linarith
    calc ‖riemannZeta (σ + t * I)‖ ≤ M := hM t σ ht3 htT hσ0 hσ2
      _ ≤ K := le_trans (le_max_left M 1) (le_max_right B _)
      _ = K * 1 := (mul_one K).symm
      _ ≤ K * L ^ K := by gcongr

/-- **The growth hypothesis holds for every `4/5 ≤ a ≤ 1`** (weak VMVT, many coordinates). -/
theorem polylogGrowth_kv {a : ℝ} (ha1 : 4 / 5 ≤ a) (ha2 : a ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ Landau.PolylogGrowth a K :=
  polylogGrowth_of (by linarith) ha2 (ExpSum.growth_weak ha1 ha2)

/-- **The growth hypothesis holds for every `2/3 < a ≤ 1`** (round 214: many coordinates plus
VMVT at `s ≍ k² log k`). -/
theorem polylogGrowth_sharp {a : ℝ} (ha1 : 2 / 3 < a) (ha2 : a ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ Landau.PolylogGrowth a K :=
  polylogGrowth_of (by linarith) ha2 (VinoFam.growth_sharp ha1 ha2)

lemma mid_exponent {n₁ : ℝ} (hn : 2 / 3 < n₁) :
    2 / 3 < (2 / 3 + min n₁ 1) / 2 ∧ (2 / 3 + min n₁ 1) / 2 ≤ 1 ∧ (2 / 3 + min n₁ 1) / 2 < n₁ := by
  have h1 : min n₁ 1 ≤ 1 := min_le_right _ _
  have h2 : min n₁ 1 ≤ n₁ := min_le_left _ _
  have h3 : 2 / 3 < min n₁ 1 := lt_min hn (by norm_num)
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **Zero-free region** of width `(log|t|)^{−n₁}` for every `n₁ > 2/3`. -/
theorem zeroFree_kv {n₁ : ℝ} (hn : 2 / 3 < n₁) : ZetaZeroFreeGenProp n₁ := by
  obtain ⟨h1, h2, h3⟩ := mid_exponent hn
  obtain ⟨K, hK, hG⟩ := polylogGrowth_sharp h1 h2
  exact Landau.zeroFree_of_growth (by linarith) hK hG h3

/-- **Rung 3**: `ψ(x) − x = O(x·exp(−c(log x)^{1/(1+n₁)}))` for every `n₁ > 2/3`, i.e. every
exponent below `3/5`. -/
theorem rung3_kv {n₁ : ℝ} (hn : 2 / 3 < n₁) :
    ∃ c > 0, (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop]
      (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁)))) := by
  obtain ⟨h1, h2, h3⟩ := mid_exponent hn
  obtain ⟨K, hK, hG⟩ := polylogGrowth_sharp h1 h2
  exact Landau.rung3_of_growth (by linarith) h2 hK hG h3

end KVBridge
