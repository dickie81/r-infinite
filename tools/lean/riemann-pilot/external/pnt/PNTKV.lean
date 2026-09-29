/-
# Round 216c: the prime number theorem with the Korobov–Vinogradov error term

`ψ(x) = x + O(x·exp(−c (log x)^{3/5} (log log x)^{−1/5}))`.

Inputs: round 216a's `ζ'/ζ` bound on `σ ≥ 1 − A·u(|t|)`, `u(T) = 1/((log T)^{2/3}(log(log T+3))^{1/3})`;
round 215's zero-free region; PNT+'s `ZetaNoZerosInBox`; and round 216b's `GenPNTW`, applied with
depth `D(T) = A·u(T)`, `log T(x) = G(log x)`, `G(L) = L^{3/5}/(log L)^{1/5}`, `ε(x) = e^{−(A/2) G}`.
-/
import MediumPNTW
import LogDerivKV

set_option lang.lemmaCmd true

open Set Function Filter Complex Real Topology

open scoped Chebyshev

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

namespace PNTKV

open LogDerivKV MediumPNTW

/-! ### The depth `A·u(T)` -/

lemma uKV_anti {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) : uKV b ≤ uKV a := by
  have hla : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith [LandauKV.e_le_three]
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hxa := log_add3_ge_one (show 0 ≤ Real.log a by linarith)
  have hxab : Real.log (Real.log a + 3) ≤ Real.log (Real.log b + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  unfold uKV
  apply one_div_le_one_div_of_le (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (by linarith) _))
  apply mul_le_mul (Real.rpow_le_rpow (by linarith) hlab (by norm_num))
    (Real.rpow_le_rpow (by linarith) hxab (by norm_num)) (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg (by linarith) _)

lemma depthOK {A : ℝ} (hA : 0 < A) (hA2 : A ≤ 1 / 2) : DepthOK (fun T ↦ A * uKV T) where
  pos T hT := mul_pos hA (uKV_pos (by linarith))
  half T hT := by
    have := uKV_le_one hT.le
    have := (uKV_pos (by linarith : (1 : ℝ) < T)).le
    nlinarith
  anti T₁ T₂ h1 h2 := mul_le_mul_of_nonneg_left (uKV_anti h1.le h2) hA.le

/-- `ζ ≠ 0` on the boxes `[1 − A u(T), 2] × [−T, T]`, for a suitable `A`. -/
lemma zeroFree_boxes : ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, 0 < A → A ≤ A₀ → ∀ T : ℝ, 3 ≤ T →
    ∀ s ∈ Icc (1 - A * uKV T) 2 ×ℂ Icc (-T) T, ζ s ≠ 0 := by
  obtain ⟨Az, hAz, hz⟩ := LandauKV.zeroFree_KV
  obtain ⟨σb, hσb, hbox⟩ := ZetaNoZerosInBox 21
  refine ⟨min Az (1 - σb), lt_min hAz (by linarith), fun A hA hA0 T hT s hs => ?_⟩
  have hre := (Complex.mem_reProdIm.mp hs).1
  have him := (Complex.mem_reProdIm.mp hs).2
  have hu1 := uKV_le_one hT
  have hu0 := (uKV_pos (by linarith : (1 : ℝ) < T)).le
  rw [← re_add_im s]
  by_cases ht : |s.im| ≤ 21
  · apply hbox _ ht
    have : A * uKV T ≤ 1 - σb :=
      calc A * uKV T ≤ A * 1 := mul_le_mul_of_nonneg_left hu1 hA.le
        _ ≤ 1 - σb := by rw [mul_one]; exact hA0.trans (min_le_right _ _)
    linarith [hre.1]
  · push Not at ht
    have hTt : |s.im| ≤ T := abs_le.mpr ⟨him.1, him.2⟩
    have he3 : Real.exp 3 ≤ |s.im| := by
      have : Real.exp 3 < 21 := by
        have := Real.exp_one_lt_d9
        have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [h3]
        have : Real.exp 1 ^ 3 < (2.72 : ℝ) ^ 3 :=
          pow_lt_pow_left₀ (by linarith) (Real.exp_pos 1).le (by norm_num)
        linarith [show (2.72 : ℝ) ^ 3 < 21 by norm_num]
      linarith
    apply hz _ _ he3
    set ℓ := Real.log |s.im| with hℓ
    have hℓ3 : 3 ≤ ℓ := by rw [hℓ, Real.le_log_iff_exp_le (by linarith)]; exact he3
    have hlℓ : 0 < Real.log ℓ := Real.log_pos (by linarith)
    have hle : Real.log ℓ ≤ Real.log (ℓ + 3) := Real.log_le_log (by linarith) (by linarith)
    have hu : uKV |s.im| ≤ 1 / (ℓ ^ ((2 : ℝ) / 3) * Real.log ℓ ^ ((1 : ℝ) / 3)) := by
      unfold uKV; rw [← hℓ]
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlℓ.le hle (by norm_num)) (by positivity)
    have hanti := uKV_anti (show 3 ≤ |s.im| by linarith) hTt
    have hAAz : A ≤ Az := hA0.trans (min_le_left _ _)
    have hq : 0 ≤ 1 / (ℓ ^ ((2 : ℝ) / 3) * Real.log ℓ ^ ((1 : ℝ) / 3)) := by positivity
    have h1 : A * uKV T ≤ Az * (1 / (ℓ ^ ((2 : ℝ) / 3) * Real.log ℓ ^ ((1 : ℝ) / 3))) :=
      mul_le_mul hAAz (hanti.trans hu) hu0 hAz.le
    rw [mul_one_div] at h1
    linarith [hre.1]

/-! ### The cutoff scale `G(L) = L^{3/5}/(log L)^{1/5}` -/

noncomputable def G (L : ℝ) : ℝ := L ^ ((3 : ℝ) / 5) / Real.log L ^ ((1 : ℝ) / 5)

lemma G_nonneg {L : ℝ} (hL : 1 ≤ L) : 0 ≤ G L := by
  unfold G; have := Real.log_nonneg hL; positivity

/-- `log L = o(G L)`. -/
lemma logL_le {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ L in atTop, Real.log L ≤ δ * G L := by
  have h := (isLittleO_log_rpow_rpow_atTop ((6 : ℝ) / 5) (show (0 : ℝ) < 3 / 5 by norm_num)).bound hδ
  filter_upwards [h, eventually_gt_atTop (Real.exp 1)] with L hL hLe
  have hL0 : 0 < L := lt_trans (Real.exp_pos 1) hLe
  have hl1 : 1 < Real.log L := by rw [Real.lt_log_iff_exp_lt hL0]; exact hLe
  have hl0 : 0 < Real.log L := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hL
  have e : Real.log L ^ ((6 : ℝ) / 5) = Real.log L * Real.log L ^ ((1 : ℝ) / 5) := by
    rw [show (6 : ℝ) / 5 = 1 + 1 / 5 by norm_num, Real.rpow_add hl0, Real.rpow_one]
  rw [e] at hL
  unfold G
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  exact hL

/-- `G L = o(L)`. -/
lemma G_le {κ : ℝ} (hκ : 0 < κ) : ∀ᶠ L in atTop, G L ≤ κ * L := by
  have h := (tendsto_rpow_atTop (show (0 : ℝ) < 2 / 5 by norm_num)).eventually_ge_atTop (1 / κ)
  filter_upwards [h, eventually_gt_atTop (Real.exp 1)] with L hL hLe
  have hL0 : 0 < L := lt_trans (Real.exp_pos 1) hLe
  have hl1 : 1 < Real.log L := by rw [Real.lt_log_iff_exp_lt hL0]; exact hLe
  have hg : G L ≤ L ^ ((3 : ℝ) / 5) := by
    unfold G
    apply div_le_self (by positivity)
    exact Real.one_le_rpow hl1.le (by norm_num)
  have hsplit : L = L ^ ((3 : ℝ) / 5) * L ^ ((2 : ℝ) / 5) := by
    rw [← Real.rpow_add hL0]; norm_num
  have h3 : 0 < L ^ ((3 : ℝ) / 5) := by positivity
  have : L ^ ((3 : ℝ) / 5) ≤ κ * L := by
    nth_rewrite 2 [hsplit]
    have : 1 ≤ κ * L ^ ((2 : ℝ) / 5) := by
      rw [div_le_iff₀ hκ] at hL; linarith
    nlinarith
  linarith

lemma G_tendsto : Tendsto G atTop atTop := by
  apply tendsto_atTop_mono' atTop _ Real.tendsto_log_atTop
  filter_upwards [logL_le one_pos] with L hL
  linarith

/-- `G ≤ L·u(e^G)`: the contour depth at `T = e^{G}` beats `G/L`. -/
lemma G_le_depth : ∀ᶠ L in atTop, G L ≤ L * uKV (Real.exp (G L)) := by
  filter_upwards [G_le (show (0 : ℝ) < 1 / 2 by norm_num), eventually_ge_atTop (6 : ℝ),
    logL_le one_pos, Real.tendsto_log_atTop.eventually_gt_atTop 1] with L hGL hL6 hlogG hl1
  have hL0 : 0 < L := by linarith
  set lam := Real.log L with hlam
  have hG1 : 1 < G L := by linarith
  have hG0 : 0 < G L := by linarith
  unfold uKV
  rw [Real.log_exp]
  have hx := log_add3_ge_one hG0.le
  have hxl : Real.log (G L + 3) ≤ lam := Real.log_le_log (by linarith) (by linarith)
  -- `G^{2/3}·G = L/λ^{1/3}`
  have h53 : G L ^ ((2 : ℝ) / 3) * G L = L / lam ^ ((1 : ℝ) / 3) := by
    have e1 : G L ^ ((2 : ℝ) / 3) * G L = G L ^ ((5 : ℝ) / 3) := by
      rw [show (5 : ℝ) / 3 = 2 / 3 + 1 by norm_num, Real.rpow_add hG0, Real.rpow_one]
    rw [e1]; unfold G
    rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hL0.le,
      ← Real.rpow_mul (by linarith)]
    norm_num; rfl
  have hprod : G L ^ ((2 : ℝ) / 3) * Real.log (G L + 3) ^ ((1 : ℝ) / 3) * G L ≤ L := by
    have hxr : Real.log (G L + 3) ^ ((1 : ℝ) / 3) ≤ lam ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by linarith) hxl (by norm_num)
    have hl3 : 0 < lam ^ ((1 : ℝ) / 3) := by positivity
    calc G L ^ ((2 : ℝ) / 3) * Real.log (G L + 3) ^ ((1 : ℝ) / 3) * G L
        = (G L ^ ((2 : ℝ) / 3) * G L) * Real.log (G L + 3) ^ ((1 : ℝ) / 3) := by ring
      _ ≤ (L / lam ^ ((1 : ℝ) / 3)) * lam ^ ((1 : ℝ) / 3) := by
          rw [h53]; exact mul_le_mul_of_nonneg_left hxr (by positivity)
      _ = L := by field_simp
  have hpos : 0 < G L ^ ((2 : ℝ) / 3) * Real.log (G L + 3) ^ ((1 : ℝ) / 3) := by positivity
  rw [mul_one_div, le_div_iff₀ hpos]
  linarith

/-! ### The theorem -/

/-- **The prime number theorem with the Korobov–Vinogradov error term.** -/
theorem PNT_KV : ∃ c > 0, (ψ - id) =O[atTop] fun x : ℝ ↦
    x * Real.exp (-c * (Real.log x ^ ((3 : ℝ) / 5) / Real.log (Real.log x) ^ ((1 : ℝ) / 5))) := by
  obtain ⟨Ab, hAb, hAb2, Cb, hCb, hbnd⟩ := logDerivBnd_KV
  obtain ⟨A₀, hA₀, hzf⟩ := zeroFree_boxes
  set A := min Ab A₀ with hAdef
  have hA : 0 < A := lt_min hAb hA₀
  have hA2 : A ≤ 1 / 2 := (min_le_left _ _).trans hAb2
  have hD := depthOK hA hA2
  set D : ℝ → ℝ := fun T ↦ A * uKV T with hDdef
  -- the `ζ'/ζ` bound on the depth-`D` region
  have hb : LogDerivZetaHasBoundW D 3 Cb := by
    intro σ t ht hσ
    have hu := (uKV_pos (by linarith : (1 : ℝ) < |t|)).le
    have h := hbnd σ t ht (le_trans (by
      have := mul_le_mul_of_nonneg_right (min_le_left Ab A₀) hu
      simp only [hDdef]; linarith) (mem_Ici.mp hσ))
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact h
  have holo : ∀ T : ℝ, 3 ≤ T → HolomorphicOn (fun s : ℂ ↦ ζ' s / ζ s)
      ((Icc (1 - D T) 2 ×ℂ Icc (-T) T) \ {1}) := fun T hT ↦
    LogDerivZetaHoloOn (Set.notMem_sdiff_of_mem rfl)
      (fun s hs ↦ hzf A hA (min_le_right _ _) T hT s hs.1)
  set c₁ := A / 2 with hc₁
  set c := A / 4 with hc
  set Gx : ℝ → ℝ := fun x ↦ G (Real.log x) with hGx
  have hGt : Tendsto Gx atTop atTop := G_tendsto.comp Real.tendsto_log_atTop
  have ev : ∀ {p : ℝ → Prop}, (∀ᶠ L in atTop, p L) → ∀ᶠ x in atTop, p (Real.log x) :=
    fun h ↦ Real.tendsto_log_atTop.eventually h
  have hG0 : ∀ᶠ x in atTop, 0 ≤ Gx x := by
    filter_upwards [ev (eventually_ge_atTop 1)] with x hx using G_nonneg hx
  refine ⟨c, by positivity, ?_⟩
  have key := GenPNTW hD (show (0 : ℝ) < 3 by norm_num) hCb hb holo
    (fun x ↦ Real.exp (Gx x)) (fun x ↦ Real.exp (-c₁ * Gx x)) (fun x ↦ Real.exp (-c * Gx x))
    (tendsto_exp_atTop.comp hGt)
    (Eventually.of_forall fun x ↦ Real.exp_pos _)
    (by
      have : Tendsto (fun x ↦ -c₁ * Gx x) atTop atBot :=
        hGt.const_mul_atTop_of_neg (by simp only [hc₁]; linarith)
      exact Real.tendsto_exp_atBot.comp this)
    (by
      filter_upwards [ev (G_le (show (0 : ℝ) < 1 / 2 by norm_num)), ev (eventually_ge_atTop 2),
        eventually_gt_atTop 0, hG0] with x hGL hL2 hx0 hg0
      have : 1 < Real.log x - c₁ * Gx x := by
        simp only [hGx]; nlinarith
      calc (2 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
        _ < Real.exp (Real.log x - c₁ * Gx x) := Real.exp_lt_exp.mpr this
        _ = x * Real.exp (-c₁ * Gx x) := by
            rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hx0]; ring_nf)
    (by
      have hu : Tendsto (fun x ↦ Gx x ^ ((2 : ℝ) / 3)) atTop atTop :=
        (tendsto_rpow_atTop (by norm_num)).comp hGt
      have h0 : Tendsto (fun x ↦ A * (Gx x ^ ((2 : ℝ) / 3))⁻¹) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp hu).const_mul A
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
      · filter_upwards [hGt.eventually_gt_atTop 2] with x hx
        exact (hD.pos _ (by
          have := Real.add_one_lt_exp (show Gx x ≠ 0 by linarith)
          linarith)).le
      · filter_upwards [hGt.eventually_gt_atTop 2] with x hx
        simp only [hDdef]
        apply mul_le_mul_of_nonneg_left _ hA.le
        unfold uKV
        rw [Real.log_exp, one_div]
        apply inv_anti₀ (by positivity)
        have := log_add3_ge_one (show 0 ≤ Gx x by linarith)
        have : 1 ≤ Real.log (Gx x + 3) ^ ((1 : ℝ) / 3) := Real.one_le_rpow this (by norm_num)
        have : 0 ≤ Gx x ^ ((2 : ℝ) / 3) := by positivity
        nlinarith)
    (by -- `ε log x ≤ F`
      filter_upwards [ev (logL_le (show 0 < A / 4 by positivity)), eventually_gt_atTop 1]
        with x hx hx1
      have hl : 0 < Real.log x := Real.log_pos hx1
      calc Real.exp (-c₁ * Gx x) * Real.log x
          = Real.exp (-c₁ * Gx x) * Real.exp (Real.log (Real.log x)) := by rw [Real.exp_log hl]
        _ ≤ Real.exp (-c₁ * Gx x) * Real.exp (A / 4 * Gx x) := by gcongr
        _ = Real.exp (-c * Gx x) := by rw [← Real.exp_add]; congr 1; simp only [hc₁, hc]; ring)
    (by -- `log x/(ε T) ≤ F`
      filter_upwards [ev (logL_le (show 0 < A / 4 by positivity)), eventually_gt_atTop 1, hG0]
        with x hx hx1 hg0
      have hl : 0 < Real.log x := Real.log_pos hx1
      rw [div_le_iff₀ (by positivity)]
      calc Real.log x = Real.exp (Real.log (Real.log x)) := (Real.exp_log hl).symm
        _ ≤ Real.exp (A / 4 * Gx x) := by gcongr
        _ ≤ Real.exp (-c * Gx x) * (Real.exp (-c₁ * Gx x) * Real.exp (Gx x)) := by
            rw [← Real.exp_add, ← Real.exp_add]; gcongr
            simp only [hc₁, hc]; nlinarith)
    (by -- `x^{−D(T)}/ε ≤ F`
      filter_upwards [ev G_le_depth, eventually_gt_atTop 1, hG0] with x hx hx1 hg0
      have hx0 : 0 < x := by linarith
      rw [div_le_iff₀ (by positivity), Real.rpow_def_of_pos hx0, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simp only [hDdef]
      have : A * Gx x ≤ Real.log x * (A * uKV (Real.exp (Gx x))) := by
        have := mul_le_mul_of_nonneg_left hx hA.le; simp only [hGx]; nlinarith
      simp only [hc₁, hc]; nlinarith)
    (by -- `x^{σ₂−1}/ε ≤ F`
      intro σ₂ hσ₂
      filter_upwards [ev (G_le (show 0 < (1 - σ₂) / A by
          have : 0 < 1 - σ₂ := by linarith
          positivity)), eventually_gt_atTop 1, hG0] with x hx hx1 hg0
      have hx0 : 0 < x := by linarith
      rw [div_le_iff₀ (by positivity), Real.rpow_def_of_pos hx0, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : A * Gx x ≤ (1 - σ₂) * Real.log x := by
        have := mul_le_mul_of_nonneg_left hx hA.le
        simp only [hGx]; rw [← mul_assoc, mul_div_cancel₀ _ hA.ne'] at this; linarith
      simp only [hc₁, hc]; nlinarith)
  simpa [hGx, G, neg_mul] using key

end PNTKV
