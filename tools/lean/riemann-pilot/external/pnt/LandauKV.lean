/-
# The last bit, step R3: the Korobov–Vinogradov zero-free region (round 215)

Plain statement (`zeroFree_KV`). There is `A > 0` such that
  `ζ(σ + it) ≠ 0` for `|t| ≥ e³` and `σ ≥ 1 − A/((log|t|)^{2/3}(log log|t|)^{1/3})`.

Route.
* `growthW_kv`: `|ζ(σ+it)| ≤ K(log|t|)^K` on `σ ≥ 1 − w(log|t|)`, where
  `w(L) = c₂(log(L+2)/(L+2))^{2/3}`. For `log|t| ≥ 25` this is `growth_kv` (round 215) through
  the truncated sum (`zeta_le_sum`), since `w(L) ≤ c₂(log L/L)^{2/3}`; below, compactness.
* `wkv_ok`: `w` is an admissible width (`LandauW.WidthOK`).
* `LandauW.zero_gap_explicitW` then keeps zeros `≍ w(log t)/log log t` away from `σ = 1`.
-/
import LandauW

open Nat Filter Topology Set Function Complex Real ComplexConjugate MeasureTheory

local notation "ζ" => riemannZeta

namespace LandauKV

open Landau LandauW

/-- **ζ from its truncated sum.** For `log|t| ≥ 25` and `4/5 ≤ σ ≤ 2`, with `X = ⌊|t|^{5/4}⌋`,
`|ζ(σ+it)| ≤ |Σ_{n≤X} n^{−σ−it}| + 13/2`. -/
theorem zeta_le_sum {t σ : ℝ} (hL : 25 ≤ Real.log |t|) (hσ45 : 4 / 5 ≤ σ) (hσ2 : σ ≤ 2) :
    ‖riemannZeta (σ + t * I)‖ ≤
      ‖∑ n ∈ Finset.Ioc 0 ⌊|t| ^ ((5 : ℝ) / 4)⌋₊, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ + 13 / 2 := by
  set L := Real.log |t| with hLdef
  have htpos : 0 < |t| := KVBridge.pos_of_log_ge (by norm_num) hL
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
  rw [KVBridge.zeta_split hX1 hσ0 ht0]
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

/-- `f(x) = log x / x`. -/
noncomputable def fl (x : ℝ) : ℝ := Real.log x / x

/-- The Korobov–Vinogradov width. -/
noncomputable def wkv (L : ℝ) : ℝ := VinoKV.c2 * fl (L + 2) ^ ((2 : ℝ) / 3)

lemma c2_pos : 0 < VinoKV.c2 := by rw [VinoKV.c2]; norm_num
lemma c2_le : VinoKV.c2 ≤ 1 / 5 := by rw [VinoKV.c2]; norm_num

lemma fl_anti {x y : ℝ} (hx : Real.exp 1 ≤ x) (hxy : x ≤ y) : fl y ≤ fl x :=
  Real.log_div_self_antitoneOn hx (hx.trans hxy) hxy

lemma e_le_three : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith

lemma fl_pos {x : ℝ} (hx : 1 < x) : 0 < fl x := div_pos (Real.log_pos hx) (by linarith)

lemma fl_le_one {x : ℝ} (hx : 0 < x) : fl x ≤ 1 := by
  rw [fl, div_le_one hx]
  exact (Real.log_le_sub_one_of_pos hx).trans (by linarith)

/-- **The width is admissible.** -/
theorem wkv_ok : WidthOK wkv (-Real.log VinoKV.c2 + 1) := by
  have hc := c2_pos
  have hc1 : VinoKV.c2 ≤ 1 := c2_le.trans (by norm_num)
  have hlc : 0 ≤ -Real.log VinoKV.c2 := by
    have := Real.log_nonpos hc.le hc1; linarith
  refine ⟨fun L hL => ?_, fun L hL => ?_, fun L L' hL hLL => ?_, fun L hL => ?_, by linarith⟩
  · unfold wkv; have := fl_pos (show 1 < L + 2 by linarith); positivity
  · unfold wkv
    have h1 := fl_le_one (show 0 < L + 2 by linarith)
    have h0 := (fl_pos (show 1 < L + 2 by linarith)).le
    have : fl (L + 2) ^ ((2 : ℝ) / 3) ≤ 1 := Real.rpow_le_one h0 h1 (by norm_num)
    nlinarith
  · unfold wkv
    have he : Real.exp 1 ≤ L + 2 := e_le_three.trans (by linarith)
    have h := fl_anti he (show L + 2 ≤ L' + 2 by linarith)
    have h0 := (fl_pos (show 1 < L' + 2 by linarith)).le
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 h (by norm_num)) hc.le
  · unfold wkv
    have hf := fl_pos (show 1 < L + 2 by linarith)
    rw [Real.log_mul hc.ne' (by positivity), Real.log_rpow hf, fl,
      Real.log_div (by have := Real.log_pos (show (1 : ℝ) < L + 2 by linarith); linarith)
        (by linarith)]
    have hll : 0 ≤ Real.log (Real.log (L + 2)) := by
      apply Real.log_nonneg
      rw [Real.le_log_iff_exp_le (by linarith)]; exact e_le_three.trans (by linarith)
    have h3 : Real.log (L + 2) ≤ Real.log 3 + Real.log L := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) (by linarith)
    have hl3 : Real.log 3 ≤ 3 / 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 2 by norm_num)
      linarith
    have hlL : 0 ≤ Real.log L := Real.log_nonneg hL
    nlinarith

/-- **ζ grows at most polylogarithmically on the Korobov–Vinogradov region.** -/
theorem growthW_kv : ∃ K : ℝ, 0 < K ∧ GrowthW wkv K := by
  obtain ⟨B, hB0, hB⟩ := VinoKV.growth_kv
  obtain ⟨M, hM⟩ := KVBridge.zeta_bound_compact (Real.exp 25)
  refine ⟨max (B + 7) (max M 2), by positivity, ?_⟩
  intro t ht3 σ hσ hσ2
  set K := max (B + 7) (max M 2) with hKdef
  have hK2 : 2 ≤ K := le_trans (le_max_right M 2) (le_max_right _ _)
  set L := Real.log |t| with hLdef
  have htpos : 0 < |t| := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le htpos]; linarith [e_le_three]
  have hLK2 : L ^ (2 : ℕ) ≤ L ^ K := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hL1 (by push_cast; linarith)
  have h1LK : 1 ≤ L ^ K := Real.one_le_rpow hL1 (by linarith)
  have hw1 := wkv_ok.le1 L hL1
  rcases le_or_gt 25 L with hbig | hsmall
  · -- the Korobov–Vinogradov range
    have hwδ : wkv L ≤ VinoKV.δkv L := by
      unfold wkv VinoKV.δkv
      have he : Real.exp 1 ≤ L := e_le_three.trans (by linarith)
      have h := fl_anti he (show L ≤ L + 2 by linarith)
      have h0 := (fl_pos (show 1 < L + 2 by linarith)).le
      have := Real.rpow_le_rpow h0 h (show (0 : ℝ) ≤ 2 / 3 by norm_num)
      exact mul_le_mul_of_nonneg_left (by simpa [fl] using this) c2_pos.le
    have hδ15 : VinoKV.δkv L ≤ 1 / 5 := by
      unfold VinoKV.δkv
      have h1 := fl_le_one (show 0 < L by linarith)
      have h0 := (fl_pos (show 1 < L by linarith)).le
      have : (Real.log L / L) ^ ((2 : ℝ) / 3) ≤ 1 :=
        Real.rpow_le_one (by simpa [fl] using h0) (by simpa [fl] using h1) (by norm_num)
      have := c2_le
      nlinarith [c2_pos]
    have hσ' : 1 - VinoKV.δkv L ≤ σ := by linarith
    have hs := zeta_le_sum hbig (by linarith) hσ2
    have hsum := hB t σ (by linarith) hσ' ⌊|t| ^ ((5 : ℝ) / 4)⌋₊
      (Nat.floor_le (by positivity))
    calc ‖ζ (σ + t * I)‖ ≤ B * L ^ 2 + 13 / 2 := by linarith
      _ ≤ (B + 7) * L ^ 2 := by nlinarith
      _ ≤ K * L ^ K := by
          apply mul_le_mul (le_max_left _ _) hLK2 (by positivity) (by positivity)
  · -- the compact range
    have htT : |t| ≤ Real.exp 25 := by
      rw [← Real.exp_log htpos]; exact Real.exp_le_exp.mpr hsmall.le
    calc ‖ζ (σ + t * I)‖ ≤ M := hM t σ ht3 htT (by linarith) hσ2
      _ ≤ K := le_trans (le_max_left M 2) (le_max_right _ _)
      _ = K * 1 := (mul_one K).symm
      _ ≤ K * L ^ K := by gcongr

/-- **The Korobov–Vinogradov zero-free region.** -/
theorem zeroFree_KV : ∃ A : ℝ, 0 < A ∧ ∀ σ t : ℝ, Real.exp 3 ≤ |t| →
    1 - A / (Real.log |t| ^ ((2 : ℝ) / 3) * Real.log (Real.log |t|) ^ ((1 : ℝ) / 3)) ≤ σ →
    ζ (σ + t * I) ≠ 0 := by
  obtain ⟨K, hK, hG⟩ := growthW_kv
  obtain ⟨N, hN, hgap⟩ := zero_gap_explicitW wkv_ok hK hG
  have hc := c2_pos
  refine ⟨VinoKV.c2 / (48 * N) * (3 / 13) / 2, by positivity, fun σ t ht hσ hz => ?_⟩
  have he3 : (4 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ); linarith
  have ht4 : 4 ≤ |t| := he3.trans ht
  have htpos : 0 < |t| := by linarith
  set ℓ := Real.log |t| with hℓdef
  have hℓ3 : 3 ≤ ℓ := by rw [hℓdef, Real.le_log_iff_exp_le htpos]; exact ht
  have hlogℓ : 1 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact e_le_three.trans hℓ3
  set x := Real.log ℓ with hxdef
  have hx0 : 0 < x := by linarith
  set E := 1 / (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3)) with hEdef
  have hE0 : 0 < E := by positivity
  have hg := hgap σ t hz ht4
  -- lower bound for the shift
  have hdlt : VinoKV.c2 / (48 * N) * E ≤ dltW wkv N t := by
    set L := Lg (2 * t) with hLdef
    have ht2 : 4 ≤ |2 * t| := by rw [abs_mul]; norm_num; linarith
    have hL1 : 1 < L := Lg_gt_one ht2
    have hL2 : L ≤ 2 * ℓ := Lg_two_le ht4
    -- the width
    have hw1 : wkv (2 * ℓ) ≤ wkv L := wkv_ok.anti _ _ hL1.le hL2
    have hw2 : VinoKV.c2 * (x / (4 * ℓ)) ^ ((2 : ℝ) / 3) ≤ wkv (2 * ℓ) := by
      unfold wkv
      apply mul_le_mul_of_nonneg_left _ hc.le
      have he : Real.exp 1 ≤ 2 * ℓ + 2 := e_le_three.trans (by linarith)
      have hf := fl_anti he (show 2 * ℓ + 2 ≤ 4 * ℓ by linarith)
      have hf4 : x / (4 * ℓ) ≤ fl (4 * ℓ) := by
        rw [fl]; apply div_le_div_of_nonneg_right _ (by linarith)
        exact Real.log_le_log (by linarith) (by linarith)
      exact Real.rpow_le_rpow (by positivity) (hf4.trans hf) (by norm_num)
    -- the denominator
    have hden : N * (1 + Real.log L) ≤ 3 * N * x := by
      have h1 : Real.log L ≤ Real.log 2 + x := by
        rw [hxdef, ← Real.log_mul (by norm_num) (by linarith)]
        exact Real.log_le_log (by linarith) hL2
      have h2 := Real.log_two_lt_d9
      nlinarith
    -- the algebra
    have hrp : (x / (4 * ℓ)) ^ ((2 : ℝ) / 3) / x ≥ E / 4 := by
      have hsplit : x = x ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_add hx0]; norm_num
      have h4 : (4 : ℝ) ^ ((2 : ℝ) / 3) ≤ 4 := by
        calc (4 : ℝ) ^ ((2 : ℝ) / 3) ≤ 4 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := Real.rpow_one 4
      rw [Real.div_rpow hx0.le (by positivity), Real.mul_rpow (by norm_num) (by linarith), hEdef]
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hx0]
      have hℓp : 0 < ℓ ^ ((2 : ℝ) / 3) := by positivity
      have hx1 : 0 < x ^ ((1 : ℝ) / 3) := by positivity
      have hx2 : 0 < x ^ ((2 : ℝ) / 3) := by positivity
      have h4p : 0 < (4 : ℝ) ^ ((2 : ℝ) / 3) := by positivity
      have hq : 1 ≤ 4 / (4 : ℝ) ^ ((2 : ℝ) / 3) := by rw [le_div_iff₀ h4p]; linarith
      have lhs : 1 / (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3)) * x =
          x ^ ((2 : ℝ) / 3) / ℓ ^ ((2 : ℝ) / 3) := by
        rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (by positivity) (by positivity)]
        nth_rewrite 1 [hsplit]; ring
      rw [lhs, div_mul_eq_mul_div, div_le_div_iff₀ hℓp (by positivity)]
      have hxx : 0 ≤ x ^ ((2 : ℝ) / 3) * ℓ ^ ((2 : ℝ) / 3) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 hxx]
    unfold dltW radW
    rw [← hLdef]
    have hwL : VinoKV.c2 * (x / (4 * ℓ)) ^ ((2 : ℝ) / 3) ≤ wkv L := hw2.trans hw1
    have hNpos : 0 < N := by linarith
    have hdpos : 0 < N * (1 + Real.log L) := by
      have := Real.log_pos hL1; positivity
    calc VinoKV.c2 / (48 * N) * E
        ≤ VinoKV.c2 / (12 * N) * ((x / (4 * ℓ)) ^ ((2 : ℝ) / 3) / x) := by
          rw [show VinoKV.c2 / (48 * N) * E = VinoKV.c2 / (12 * N) * (E / 4) by ring]
          exact mul_le_mul_of_nonneg_left hrp (by positivity)
      _ = 1 / 4 * (VinoKV.c2 * (x / (4 * ℓ)) ^ ((2 : ℝ) / 3)) / (3 * N * x) := by
          field_simp; ring
      _ ≤ 1 / 4 * wkv L / (3 * N * x) := by gcongr
      _ ≤ 1 / 4 * wkv L / (N * (1 + Real.log L)) := by
          apply div_le_div_of_nonneg_left _ hdpos hden
          have := wkv_ok.pos L hL1.le; positivity
  have hA : VinoKV.c2 / (48 * N) * (3 / 13) / 2 /
      (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3)) = VinoKV.c2 / (48 * N) * (3 / 13) / 2 * E := by
    rw [hEdef]; ring
  rw [hA] at hσ
  have hpos : 0 < VinoKV.c2 / (48 * N) * E := by
    have : 0 < N := by linarith
    positivity
  nlinarith

end LandauKV
