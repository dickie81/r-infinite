/-
# R4a: the log-derivative bound on the Korobov–Vinogradov region (round 216)

Plain statement (`logDerivBnd_KV`). With `u(T) = 1/((log T)^{2/3}(log(log T + 3))^{1/3})`,
there are `A ∈ (0, 1/2]` and `C > 0` such that
  `|ζ'/ζ(σ+it)| ≤ C (log|t|)³` for `|t| > 3` and `σ ≥ 1 − A·u(|t|)`.

This is round 193's L4 (`Landau.logDerivBnd_of_growth`) for the width `wkv` of round 215: the
disc facts and the local bound at a point are the same; the zero gap is `zero_gap_explicitW`, and
the power-form inverse bounds are replaced by `1/ρ ≤ (24/c₂)·log|t|` and
`1/dlt ≤ O(log²|t|)`, with `dlt ≥ c₂ u/(48N)`.
-/
import LandauKV

open Nat Filter Topology Set Function Complex Real ComplexConjugate MeasureTheory

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ

namespace LogDerivKV

open Landau LandauW LandauKV

theorem disc_factsW {w : ℝ → ℝ} {Cw K : ℝ} (hw : WidthOK w Cw) (hK : 0 < K) (hG : GrowthW w K) {T δ : ℝ}
    (hT : 4 ≤ |T|) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    (∀ z : ℂ, ‖z‖ < 2 → (((1 + δ : ℝ) : ℂ) + T * I) + radW w T * z ≠ 1) ∧
    (∀ z : ℂ, ‖z‖ ≤ 3 / 4 → ‖ζ ((((1 + δ : ℝ) : ℂ) + T * I) + radW w T * z)‖ ≤
      Bnd K δ T * ‖ζ (((1 + δ : ℝ) : ℂ) + T * I)‖) ∧ 1 < Bnd K δ T := by
  set s₀ : ℂ := ((1 + δ : ℝ) : ℂ) + T * I with hs₀def
  have hre : s₀.re = 1 + δ := by simp [hs₀def]
  have him : s₀.im = T := by simp [hs₀def]
  set ρ := radW w T with hρdef
  have hρ := radW_pos hw T hT
  have hρ4 := radW_le hw hT
  have hL := Lg_gt_one hT
  have hζδ : 1 ≤ ‖ζ ((1 + δ : ℝ) : ℂ)‖ * ‖ζ s₀‖ := by
    have h := inv_norm_zeta_le (s := s₀) (by rw [hre]; linarith)
    rw [hre] at h
    have hz : 0 < ‖ζ s₀‖ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; linarith))
    rw [div_le_iff₀ hz] at h; linarith
  have hB : 1 < Bnd K δ T := by
    unfold Bnd; have : 0 ≤ K * Lg T ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by positivity
    linarith
  refine ⟨fun z hz h => ?_, fun z hz => ?_, hB⟩
  · have := congrArg Complex.im h
    simp only [add_im, him, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, one_im] at this
    have hzi : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have : |T| ≤ ρ * |z.im| := by
      rw [show T = -(ρ * z.im) by linarith, abs_neg, abs_mul, abs_of_pos hρ]
    nlinarith [abs_nonneg z.im]
  · set s := s₀ + ρ * z with hsdef
    have hsre : s.re = 1 + δ + ρ * z.re := by simp [hsdef, hre]
    have hsim : s.im = T + ρ * z.im := by simp [hsdef, him]
    have hzr : |z.re| ≤ 3 / 4 := (Complex.abs_re_le_norm z).trans hz
    have hzi : |z.im| ≤ 3 / 4 := (Complex.abs_im_le_norm z).trans hz
    have hρzi : |ρ * z.im| ≤ 3 / 16 := by
      rw [abs_mul, abs_of_pos hρ]; nlinarith [abs_nonneg z.im]
    have hρzr : |ρ * z.re| ≤ 3 / 4 * ρ := by
      rw [abs_mul, abs_of_pos hρ]; nlinarith [abs_nonneg z.re]
    have hims : 3 ≤ |s.im| := by
      rw [hsim]; have := abs_sub_abs_le_abs_sub T (-(ρ * z.im))
      rw [abs_neg, sub_neg_eq_add] at this; linarith
    have hims2 : |s.im| ≤ |T| + 1 := by
      rw [hsim]; have := abs_add_le T (ρ * z.im); linarith
    have hlog_pos : 0 < Real.log |s.im| := Real.log_pos (by linarith)
    have hlog_le : Real.log |s.im| ≤ Lg T := Real.log_le_log (by linarith) hims2
    have hlog1 : 1 ≤ Real.log |s.im| := by
      rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
    have hpow : w (Lg T) ≤ w (Real.log |s.im|) := hw.anti _ _ hlog1 hlog_le
    have hlower : 1 - w (Real.log |s.im|) ≤ s.re := by
      rw [hsre]
      have : w (Lg T) = 4 * ρ := by rw [hρdef, radW]; ring
      have := abs_le.mp hρzr
      linarith
    have hupper : s.re ≤ 2 := by
      rw [hsre]; have := abs_le.mp hρzr; linarith
    have hgs := hG s.im hims s.re hlower hupper
    rw [Complex.re_add_im] at hgs
    have hKpow : K * Real.log |s.im| ^ K ≤ K * Lg T ^ K :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog_pos.le hlog_le hK.le) hK.le
    have hζs0 : 0 ≤ ‖ζ s₀‖ := norm_nonneg _
    calc ‖ζ s‖ ≤ K * Lg T ^ K := hgs.trans hKpow
      _ ≤ K * Lg T ^ K * (‖ζ ((1 + δ : ℝ) : ℂ)‖ * ‖ζ s₀‖) := by
          have : 0 ≤ K * Lg T ^ K := by positivity
          nlinarith
      _ ≤ Bnd K δ T * ‖ζ s₀‖ := by
          unfold Bnd; nlinarith [mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Lg T) K))
            (norm_nonneg (ζ ((1 + δ : ℝ) : ℂ))), hζs0]

lemma dltW_anti {w : ℝ → ℝ} {Cw : ℝ} (hw : WidthOK w Cw) {N : ℝ} (hN : 0 < N) {T U : ℝ}
    (hT : 4 ≤ |T|) (h : |T| ≤ |U|) : dltW w N U ≤ dltW w N T := by
  have hT2 : 4 ≤ |2 * T| := by rw [abs_mul]; norm_num; linarith
  have hTU : |2 * T| ≤ |2 * U| := by rw [abs_mul, abs_mul]; norm_num; linarith
  unfold dltW
  have hr := radW_anti hw hT2 hTU
  have hrpos := radW_pos hw (2 * U) (by linarith)
  have hL1 := Lg_gt_one hT2
  have hlog : Real.log (Lg (2 * T)) ≤ Real.log (Lg (2 * U)) :=
    Real.log_le_log (by linarith) (Lg_mono hT2 hTU)
  have hlnn : 0 ≤ Real.log (Lg (2 * T)) := Real.log_nonneg hL1.le
  apply div_le_div₀ (radW_pos hw (2 * T) hT2).le hr (by positivity)
  nlinarith

lemma dltW_pos {w : ℝ → ℝ} {Cw : ℝ} (hw : WidthOK w Cw) {N : ℝ} (hN : 0 < N) {T : ℝ}
    (hT : 2 ≤ |T|) : 0 < dltW w N T := by
  have hT2 : 4 ≤ |2 * T| := by rw [abs_mul]; norm_num; linarith
  unfold dltW
  have := radW_pos hw (2 * T) hT2
  have := Real.log_nonneg (Lg_gt_one hT2).le
  positivity

set_option maxHeartbeats 1600000 in
/-- **The local bound inside the disc**, for any admissible width. -/
theorem near_boundW {w : ℝ → ℝ} {Cw K N c1 t σ Q1 Q2 E : ℝ} (hw : WidthOK w Cw) (hK : 0 < K)
    (hG : GrowthW w K) (hN : 4 ≤ N)
    (hgap : ∀ β t : ℝ, ζ (β + t * I) = 0 → 4 ≤ |t| → 3 * dltW w N t / 13 ≤ 1 - β)
    (ht : 5 ≤ |t|) (hζ : ζ (σ + t * I) ≠ 0) (hlo1 : 1 - σ ≤ radW w t / 8)
    (hlo2 : 1 - σ ≤ 3 * dltW w N (|t| + 1) / 26) (hhi : σ < 1 + radW w t / 8)
    (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (hE : 0 ≤ E)
    (hinvρ : 1 / radW w t ≤ Q1 * Real.log |t|)
    (hinvg : 1 / (3 * dltW w N (|t| + 1) / 26) ≤ Q2 * Real.log |t| ^ 2)
    (hlB : Real.log (Bnd K (radW w t / 8) t) ≤ E * Real.log |t|) :
    ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      E * (Q1 * Kc + 1 / Real.log ((3 / 4) / (1 / 2)) * Q2) * Real.log |t| ^ 3 := by
  have ht4 : 4 ≤ |t| := by linarith
  have ht3 : 3 ≤ |t| := by linarith
  set ℓ := Real.log |t| with hℓdef
  have hℓ : 1 ≤ ℓ := ell_ge_one ht3
  set ρ := radW w t with hρdef
  have hρ : 0 < ρ := radW_pos hw t ht4
  have hρ4 : ρ ≤ 1 / 4 := radW_le hw ht4
  set δ := ρ / 8 with hδdef
  set s₀ : ℂ := ((1 + δ : ℝ) : ℂ) + t * I with hs₀def
  obtain ⟨hpole, hbound, hB1⟩ := disc_factsW hw hK hG (T := t) (δ := δ) ht4 (by positivity)
    (by linarith)
  set z : ℂ := (((σ - 1 - δ) / ρ : ℝ) : ℂ) with hzdef
  have hsz : s₀ + (ρ : ℂ) * z = σ + t * I := by
    apply Complex.ext
    · simp only [hs₀def, hzdef, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, sub_zero]
      field_simp; ring
    · simp [hs₀def, hzdef]
  have hz : ‖z‖ ≤ 1 / 4 := by
    rw [hzdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hρ, div_le_iff₀ hρ,
      abs_le]
    constructor <;> linarith
  have hNpos : 0 < N := by linarith
  set g := 3 * dltW w N (|t| + 1) / 26 with hgdef
  have hdpos : 0 < dltW w N (|t| + 1) := dltW_pos hw hNpos (by
    rw [abs_of_pos (by positivity : (0 : ℝ) < |t| + 1)]; linarith)
  have hg : 0 < g := by rw [hgdef]; linarith
  have hgap' : ∀ v : ℂ, ‖v‖ ≤ 1 / 2 → ζ (s₀ + ρ * v) = 0 →
      g ≤ ‖(s₀ + ρ * z) - (s₀ + ρ * v)‖ := by
    intro v hv hv0
    set u := s₀ + (ρ : ℂ) * v with hudef
    have hure : u.re = 1 + δ + ρ * v.re := by simp [hudef, hs₀def]
    have huim : u.im = t + ρ * v.im := by simp [hudef, hs₀def]
    have hvi : |v.im| ≤ 1 / 2 := (Complex.abs_im_le_norm v).trans hv
    have hρvi : |ρ * v.im| ≤ 1 / 8 := by
      rw [abs_mul, abs_of_pos hρ]; nlinarith [abs_nonneg v.im]
    have hu4 : 4 ≤ |u.im| := by
      rw [huim]; have := abs_sub_abs_le_abs_sub t (-(ρ * v.im))
      rw [abs_neg, sub_neg_eq_add] at this; linarith
    have hu5 : |u.im| ≤ |t| + 1 := by
      rw [huim]; have := abs_add_le t (ρ * v.im); linarith
    have hz0 : ζ (u.re + u.im * I) = 0 := by rw [Complex.re_add_im]; exact hv0
    have h1 := hgap u.re u.im hz0 hu4
    have h2 := dltW_anti hw hNpos (T := u.im) (U := |t| + 1) hu4
      (by rw [abs_of_pos (by positivity : (0 : ℝ) < |t| + 1)]; exact hu5)
    rw [hsz]
    have hre : ((σ : ℂ) + t * I - u).re = σ - u.re := by simp
    have := Complex.abs_re_le_norm ((σ : ℂ) + t * I - u)
    rw [hre] at this
    have hσu : g ≤ σ - u.re := by rw [hgdef] at hlo2 ⊢; linarith
    exact hσu.trans ((le_abs_self _).trans this)
  have hs₀ : 1 < s₀.re := by simp [hs₀def]; positivity
  have main := local_bound_point hs₀ hρ hB1 hg hz (by rw [hsz]; exact hζ) hpole hbound hgap'
  rw [hsz] at main
  set L := ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ with hLdef
  set lB := Real.log (Bnd K δ t) with hlBdef
  set cL := 1 / Real.log ((3 / 4) / (1 / 2)) with hcLdef
  have hcL : 0 < cL := by
    rw [hcLdef]; have : 0 < Real.log ((3 / 4 : ℝ) / (1 / 2)) := Real.log_pos (by norm_num)
    positivity
  have hKc : 0 ≤ Kc := by unfold Kc; positivity
  have hlBpos : 0 < lB := Real.log_pos hB1
  have hL1 : L ≤ Kc * lB * (1 / ρ) + cL * lB * (1 / g) := by
    have h2 : L ≤ (Kc * lB + ρ / g * (cL * lB)) / ρ := by
      rw [le_div_iff₀ hρ]; linarith [main]
    have e : (Kc * lB + ρ / g * (cL * lB)) / ρ = Kc * lB * (1 / ρ) + cL * lB * (1 / g) := by
      field_simp
    linarith
  have hE0 : 0 ≤ E * ℓ := by positivity
  have t1 : Kc * lB * (1 / ρ) ≤ Kc * (E * ℓ) * (Q1 * ℓ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlB hKc) hinvρ (by positivity) (by positivity)
  have t2 : cL * lB * (1 / g) ≤ cL * (E * ℓ) * (Q2 * ℓ ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlB hcL.le) hinvg (by positivity) (by positivity)
  have hℓ23 : ℓ ^ 2 ≤ ℓ ^ 3 := pow_le_pow_right₀ hℓ (by norm_num)
  have hKE : 0 ≤ Kc * E * Q1 := by positivity
  calc L ≤ Kc * (E * ℓ) * (Q1 * ℓ) + cL * (E * ℓ) * (Q2 * ℓ ^ 2) := by linarith
    _ = (Kc * E * Q1) * ℓ ^ 2 + E * (cL * Q2) * ℓ ^ 3 := by ring
    _ ≤ (Kc * E * Q1) * ℓ ^ 3 + E * (cL * Q2) * ℓ ^ 3 := by nlinarith
    _ = E * (Q1 * Kc + cL * Q2) * ℓ ^ 3 := by ring

/-! ## The Korobov–Vinogradov width: explicit inequalities -/

/-- `u(T) = 1/((log T)^{2/3}(log(log T + 3))^{1/3})`. -/
noncomputable def uKV (T : ℝ) : ℝ :=
  1 / (Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T + 3) ^ ((1 : ℝ) / 3))

lemma log_add3_ge_one {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : 1 ≤ Real.log (ℓ + 3) := by
  rw [Real.le_log_iff_exp_le (by linarith)]; linarith [e_le_three]

lemma uKV_pos {T : ℝ} (hT : 1 < T) : 0 < uKV T := by
  unfold uKV
  have := Real.log_pos hT
  have := log_add3_ge_one (show 0 ≤ Real.log T by linarith)
  have : 0 < Real.log (Real.log T + 3) := by linarith
  positivity

lemma uKV_le_one {T : ℝ} (hT : 3 ≤ T) : uKV T ≤ 1 := by
  have hℓ : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith [e_le_three]
  have hx := log_add3_ge_one (show 0 ≤ Real.log T by linarith)
  unfold uKV
  rw [div_le_one (by positivity)]
  have h1 : 1 ≤ Real.log T ^ ((2 : ℝ) / 3) := Real.one_le_rpow hℓ (by norm_num)
  have h2 : 1 ≤ Real.log (Real.log T + 3) ^ ((1 : ℝ) / 3) := Real.one_le_rpow hx (by norm_num)
  nlinarith

/-- `(x/(4ℓ))^{2/3} ≥ ¼·x/(ℓ^{2/3} x^{1/3})`, the shape of both lower bounds. -/
lemma shape_lower {ℓ x : ℝ} (hℓ : 1 ≤ ℓ) (hx : 1 ≤ x) :
    x / (4 * (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3))) ≤ (x / (4 * ℓ)) ^ ((2 : ℝ) / 3) := by
  have hx0 : 0 < x := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hsplit : x = x ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add hx0]; norm_num
  have h4 : (4 : ℝ) ^ ((2 : ℝ) / 3) ≤ 4 := by
    calc (4 : ℝ) ^ ((2 : ℝ) / 3) ≤ 4 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := Real.rpow_one 4
  have hℓp : 0 < ℓ ^ ((2 : ℝ) / 3) := by positivity
  have hx1 : 0 < x ^ ((1 : ℝ) / 3) := by positivity
  have hx2 : 0 < x ^ ((2 : ℝ) / 3) := by positivity
  have h4p : 0 < (4 : ℝ) ^ ((2 : ℝ) / 3) := by positivity
  rw [Real.div_rpow hx0.le (by positivity), Real.mul_rpow (by norm_num) hℓ0.le]
  have lhs : x / (4 * (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3))) =
      x ^ ((2 : ℝ) / 3) / (4 * ℓ ^ ((2 : ℝ) / 3)) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    nth_rewrite 1 [hsplit]; ring
  rw [lhs, div_le_div_iff₀ (by positivity) (by positivity)]
  have hxx : 0 ≤ x ^ ((2 : ℝ) / 3) * ℓ ^ ((2 : ℝ) / 3) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h4 hxx]

lemma wkv_lower {L ℓ : ℝ} (hL : 1 ≤ L) (hℓ : 1 ≤ ℓ) (hLℓ : L ≤ 2 * ℓ) :
    VinoKV.c2 * (Real.log (ℓ + 3) / (4 * ℓ)) ^ ((2 : ℝ) / 3) ≤ wkv L := by
  have hw1 : wkv (2 * ℓ) ≤ wkv L := wkv_ok.anti _ _ hL hLℓ
  refine le_trans ?_ hw1
  unfold wkv
  apply mul_le_mul_of_nonneg_left _ c2_pos.le
  have he : Real.exp 1 ≤ 2 * ℓ + 2 := e_le_three.trans (by linarith)
  have hf := fl_anti he (show 2 * ℓ + 2 ≤ 4 * ℓ by linarith)
  have hf4 : Real.log (ℓ + 3) / (4 * ℓ) ≤ fl (4 * ℓ) := by
    rw [fl]; apply div_le_div_of_nonneg_right _ (by linarith)
    exact Real.log_le_log (by linarith) (by linarith)
  have hx := log_add3_ge_one (show 0 ≤ ℓ by linarith)
  exact Real.rpow_le_rpow (by positivity) (hf4.trans hf) (by norm_num)

lemma radW_lower_u {t : ℝ} (ht : 4 ≤ |t|) : VinoKV.c2 / 16 * uKV |t| ≤ radW wkv t := by
  set ℓ := Real.log |t| with hℓdef
  have hℓ : 1 ≤ ℓ := ell_ge_one (by linarith)
  set x := Real.log (ℓ + 3) with hxdef
  have hx := log_add3_ge_one (show 0 ≤ ℓ by linarith)
  have hL1 := Lg_gt_one ht
  have hw := wkv_lower hL1.le hℓ (Lg_le_two_ell ht)
  have hs := shape_lower hℓ hx
  have hu : uKV |t| ≤ x / (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3)) := by
    unfold uKV; rw [← hℓdef, ← hxdef]
    apply div_le_div_of_nonneg_right hx (by positivity)
  unfold radW
  have hc := c2_pos
  have e : x / (4 * (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3))) =
      x / (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3)) / 4 := by ring
  rw [e] at hs
  nlinarith

lemma dltW_lower_u {N t : ℝ} (hN : 0 < N) (ht : 3 ≤ |t|) :
    VinoKV.c2 / (48 * N) * uKV |t| ≤ dltW wkv N (|t| + 1) := by
  set ℓ := Real.log |t| with hℓdef
  have hℓ : 1 ≤ ℓ := ell_ge_one ht
  set x := Real.log (ℓ + 3) with hxdef
  have hx := log_add3_ge_one (show 0 ≤ ℓ by linarith)
  have hx0 : 0 < x := by linarith
  have hU : 4 ≤ |2 * (|t| + 1)| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < |t| + 1)]; norm_num; linarith
  have hL1 := Lg_gt_one hU
  have hLle : Lg (2 * (|t| + 1)) ≤ 2 * ℓ := by
    unfold Lg; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < |t| + 1), abs_two]
    exact two_log_bound ht
  have hw := wkv_lower hL1.le hℓ hLle
  have hs := shape_lower hℓ hx
  have hden : 1 + Real.log (Lg (2 * (|t| + 1))) ≤ 3 * x := by
    have h1 : Real.log (Lg (2 * (|t| + 1))) ≤ Real.log 2 + Real.log ℓ := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) hLle
    have h2 : Real.log ℓ ≤ x := Real.log_le_log (by linarith) (by linarith)
    have h3 := Real.log_two_lt_d9
    have h4 : (1.38 : ℝ) ≤ x := by
      have : Real.log 4 ≤ x := Real.log_le_log (by norm_num) (by linarith)
      have h44 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_gt_d9
      linarith
    linarith
  have hlnn : 0 ≤ Real.log (Lg (2 * (|t| + 1))) := Real.log_nonneg hL1.le
  have hc := c2_pos
  have hu : uKV |t| = 1 / (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3)) := by
    unfold uKV; rw [← hℓdef, ← hxdef]
  unfold dltW radW
  rw [le_div_iff₀ (by positivity), hu]
  have hq : 0 < ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) := by positivity
  have hwpos : 0 ≤ wkv (Lg (2 * (|t| + 1))) := (wkv_ok.pos _ hL1.le).le
  -- reduce to `hs` and `hw`
  have key : VinoKV.c2 / (48 * N) * (1 / (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3))) *
      (N * (1 + Real.log (Lg (2 * (|t| + 1))))) ≤
      VinoKV.c2 * (x / (4 * (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3)))) / 4 := by
    rw [show VinoKV.c2 / (48 * N) * (1 / (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3))) *
        (N * (1 + Real.log (Lg (2 * (|t| + 1))))) =
        VinoKV.c2 / (48 * (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3))) *
        (1 + Real.log (Lg (2 * (|t| + 1)))) by field_simp]
    rw [show VinoKV.c2 * (x / (4 * (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3)))) / 4 =
        VinoKV.c2 / (48 * (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3))) * (3 * x) by field_simp; ring]
    exact mul_le_mul_of_nonneg_left hden (by positivity)
  have hsx : VinoKV.c2 * (x / (4 * (ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3)))) ≤
      VinoKV.c2 * (x / (4 * ℓ)) ^ ((2 : ℝ) / 3) := by
    exact mul_le_mul_of_nonneg_left hs hc.le
  linarith

lemma inv_radW_le {t : ℝ} (ht : 4 ≤ |t|) :
    1 / radW wkv t ≤ 24 / VinoKV.c2 * Real.log |t| := by
  set ℓ := Real.log |t| with hℓdef
  have hL1 := Lg_gt_one ht
  set L := Lg t with hLdef
  have hL2 : L ≤ 2 * ℓ := Lg_le_two_ell ht
  have hc := c2_pos
  have hf1 := fl_le_one (show 0 < L + 2 by linarith)
  have hf0 := fl_pos (show 1 < L + 2 by linarith)
  have hfl : 1 / (L + 2) ≤ fl (L + 2) := by
    rw [fl]; apply div_le_div_of_nonneg_right _ (by linarith)
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith [e_le_three]
  have hpow : fl (L + 2) ≤ fl (L + 2) ^ ((2 : ℝ) / 3) := by
    calc fl (L + 2) = fl (L + 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ fl (L + 2) ^ ((2 : ℝ) / 3) :=
          Real.rpow_le_rpow_of_exponent_ge hf0 hf1 (by norm_num)
  have hw : VinoKV.c2 / (L + 2) ≤ wkv L := by
    unfold wkv
    calc VinoKV.c2 / (L + 2) = VinoKV.c2 * (1 / (L + 2)) := by ring
      _ ≤ VinoKV.c2 * fl (L + 2) ^ ((2 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left (hfl.trans hpow) hc.le
  unfold radW
  rw [← hLdef]
  have hwpos : 0 < wkv L := wkv_ok.pos L hL1.le
  rw [div_le_iff₀ (by positivity)]
  have : 1 ≤ 1 / 4 * (VinoKV.c2 / (L + 2)) * (24 / VinoKV.c2 * ℓ) := by
    rw [show 1 / 4 * (VinoKV.c2 / (L + 2)) * (24 / VinoKV.c2 * ℓ) = 6 * ℓ / (L + 2) by
      field_simp; ring]
    rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : 1 / 4 * (VinoKV.c2 / (L + 2)) * (24 / VinoKV.c2 * ℓ) ≤
      24 / VinoKV.c2 * ℓ * (1 / 4 * wkv L) := by
    have : 0 ≤ 24 / VinoKV.c2 * ℓ := by
      have := ell_ge_one (t := t) (by linarith); positivity
    nlinarith
  linarith

lemma logBnd_le_kv {K c1 t : ℝ} (hK : 0 < K) (hc1 : 0 < c1)
    (hnear : ∀ σ : ℝ, σ ∈ Set.Ioc 1 2 → ‖ζ σ‖ ≤ c1 / (σ - 1)) (ht : 4 ≤ |t|) :
    Real.log (Bnd K (radW wkv t / 8) t) ≤
      (Real.log (2 + 192 * K * c1 / VinoKV.c2) + 2 * K + 1) * Real.log |t| := by
  set ℓ := Real.log |t| with hℓdef
  have hℓ : 1 ≤ ℓ := ell_ge_one (by linarith)
  have hL := Lg_gt_one ht
  have hρ := radW_pos wkv_ok t ht
  have hρ4 := radW_le wkv_ok ht
  have hc := c2_pos
  have hinv := inv_radW_le ht
  rw [← hℓdef] at hinv
  have hζ : ‖ζ ((1 + radW wkv t / 8 : ℝ) : ℂ)‖ ≤ 8 * c1 * (24 / VinoKV.c2 * ℓ) := by
    have h := hnear (1 + radW wkv t / 8) ⟨by linarith, by linarith⟩
    have e : c1 / (1 + radW wkv t / 8 - 1) = 8 * c1 * (1 / radW wkv t) := by
      rw [show 1 + radW wkv t / 8 - 1 = radW wkv t / 8 by ring]; field_simp
    rw [e] at h
    exact h.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
  have hLK : Lg t ^ K ≤ (2 * ℓ) ^ K := Real.rpow_le_rpow (by linarith) (Lg_le_two_ell ht) hK.le
  have h2K : 1 ≤ (2 * ℓ) ^ K := Real.one_le_rpow (by linarith) hK.le
  set D := 2 + 192 * K * c1 / VinoKV.c2 with hD
  have hD1 : 1 ≤ D := by rw [hD]; have : 0 ≤ 192 * K * c1 / VinoKV.c2 := by positivity
                         linarith
  have hB : Bnd K (radW wkv t / 8) t ≤ D * (2 * ℓ) ^ K * ℓ := by
    unfold Bnd
    have hLKp : 0 ≤ Lg t ^ K := Real.rpow_nonneg (by linarith) K
    calc 2 + K * Lg t ^ K * ‖ζ ((1 + radW wkv t / 8 : ℝ) : ℂ)‖
        ≤ 2 + K * (2 * ℓ) ^ K * (8 * c1 * (24 / VinoKV.c2 * ℓ)) := by gcongr
      _ = 2 + 192 * K * c1 / VinoKV.c2 * ((2 * ℓ) ^ K * ℓ) := by field_simp; ring
      _ ≤ 2 * ((2 * ℓ) ^ K * ℓ) + 192 * K * c1 / VinoKV.c2 * ((2 * ℓ) ^ K * ℓ) := by
          nlinarith
      _ = D * (2 * ℓ) ^ K * ℓ := by rw [hD]; ring
  have hBpos : 0 < Bnd K (radW wkv t / 8) t := by unfold Bnd; positivity
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD1
  calc Real.log (Bnd K (radW wkv t / 8) t) ≤ Real.log (D * (2 * ℓ) ^ K * ℓ) :=
        Real.log_le_log hBpos hB
    _ = Real.log D + K * Real.log (2 * ℓ) + Real.log ℓ := by
        rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by positivity) (by positivity),
          Real.log_rpow (by linarith)]
    _ ≤ Real.log D + K * (2 * ℓ) + ℓ := by
        have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * ℓ by linarith)
        have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ℓ by linarith)
        nlinarith
    _ ≤ (Real.log D + 2 * K + 1) * ℓ := by nlinarith

set_option maxHeartbeats 3200000 in
/-- **R4a: `ζ'/ζ = O((log|t|)³)` on the Korobov–Vinogradov region.** -/
theorem logDerivBnd_KV : ∃ A : ℝ, 0 < A ∧ A ≤ 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧
    ∀ σ t : ℝ, 3 < |t| → 1 - A * uKV |t| ≤ σ →
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * Real.log |t| ^ 3 := by
  obtain ⟨K, hK, hG⟩ := growthW_kv
  obtain ⟨N, hN, hgap⟩ := zero_gap_explicitW wkv_ok hK hG
  obtain ⟨C3, hC3⟩ := LogDerivZetaBdd_of_Re_ge_three_halves
  obtain ⟨Cs, hCs, hstrip⟩ := LogDerivZetaUniformLogSquaredBoundStripSpec
  obtain ⟨C0, hC0, hshift⟩ := ShiftZeroBound
  obtain ⟨c1, hc1, hnear⟩ := ZetaNear1BndExact
  have hNpos : 0 < N := by linarith
  have hc := c2_pos
  have hF := FinIoo
  set A := min (min (1 / 2) (F / 2)) (min (VinoKV.c2 / 128)
    (3 / 26 * (VinoKV.c2 / (48 * N)))) with hAdef
  have hApos : 0 < A := by
    simp only [hAdef, lt_min_iff]
    refine ⟨⟨by norm_num, by linarith [hF.1]⟩, by positivity, by positivity⟩
  have hA1 : A ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hAF : A ≤ F / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hAr : A ≤ VinoKV.c2 / 128 := (min_le_right _ _).trans (min_le_left _ _)
  have hAd : A ≤ 3 / 26 * (VinoKV.c2 / (48 * N)) := (min_le_right _ _).trans (min_le_right _ _)
  set E := Real.log (2 + 192 * K * c1 / VinoKV.c2) + 2 * K + 1 with hEdef
  have hE : 0 ≤ E := by
    have : 0 ≤ Real.log (2 + 192 * K * c1 / VinoKV.c2) := Real.log_nonneg (by
      have : 0 ≤ 192 * K * c1 / VinoKV.c2 := by positivity
      linarith)
    linarith
  set Q1 := 24 / VinoKV.c2 with hQ1
  set Q2 := 26 / 3 * (48 * N / VinoKV.c2) * 3 with hQ2
  set cL := 1 / Real.log ((3 / 4) / (1 / 2)) with hcLdef
  have hcL : 0 < cL := by
    rw [hcLdef]; have : 0 < Real.log ((3 / 4 : ℝ) / (1 / 2)) := Real.log_pos (by norm_num)
    positivity
  have hKc : 0 ≤ Kc := by unfold Kc; positivity
  set En := E * (Q1 * Kc + cL * Q2) with hEndef
  have hEn : 0 ≤ En := by positivity
  have hC3n : 0 ≤ max C3 0 := le_max_right _ _
  refine ⟨A, hApos, hA1, max C3 0 + Cs + (8 * Q1 + C0) + En + 1, by positivity,
    fun σ t ht hσ => ?_⟩
  have ht3 : 3 ≤ |t| := ht.le
  set ℓ := Real.log |t| with hℓdef
  have hℓ : 1 ≤ ℓ := ell_ge_one ht3
  have hℓ3 : 1 ≤ ℓ ^ 3 := one_le_pow₀ hℓ
  have hℓ23 : ℓ ^ 2 ≤ ℓ ^ 3 := pow_le_pow_right₀ hℓ (by norm_num)
  have hℓ13 : ℓ ≤ ℓ ^ 3 := by nlinarith
  have hu1 : uKV |t| ≤ 1 := uKV_le_one ht3
  have hu0 : 0 < uKV |t| := uKV_pos (by linarith)
  set C := max C3 0 + Cs + (8 * Q1 + C0) + En + 1 with hCdef
  have fin : ∀ P : ℝ, P ≤ C → ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ P * ℓ ^ 3 →
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * ℓ ^ 3 := fun P hP h =>
    h.trans (mul_le_mul_of_nonneg_right hP (by positivity))
  have hQ1n : 0 ≤ Q1 := by positivity
  by_cases h32 : 3 / 2 ≤ σ
  · refine fin (max C3 0) (by linarith) ?_
    have h := hC3 (σ + t * I) (by simp; exact h32)
    have : max C3 0 ≤ max C3 0 * ℓ ^ 3 := le_mul_of_one_le_right hC3n hℓ3
    exact h.trans ((le_max_left _ _).trans this)
  rw [not_le] at h32
  by_cases ht5 : |t| < 5
  · refine fin Cs (by linarith) ?_
    have hℓ2 : ℓ < 2 := by
      rw [hℓdef, Real.log_lt_iff_lt_exp (by linarith)]
      have := Real.exp_one_gt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    have hlo : 1 - F / ℓ ≤ σ := by
      have h1 : A * uKV |t| ≤ A := by nlinarith
      have h2 : F / 2 ≤ F / ℓ := div_le_div_of_nonneg_left hF.1.le (by linarith) hℓ2.le
      linarith
    have h := hstrip t ht3 σ ⟨hlo, h32.le⟩
    exact h.trans (mul_le_mul_of_nonneg_left hℓ23 hCs.le)
  rw [not_lt] at ht5
  have ht4 : 4 ≤ |t| := by linarith
  set ρ := radW wkv t with hρdef
  have hρ : 0 < ρ := radW_pos wkv_ok t ht4
  have hρ4 : ρ ≤ 1 / 4 := radW_le wkv_ok ht4
  have hinvρ : 1 / ρ ≤ Q1 * ℓ := inv_radW_le ht4
  by_cases hin : σ < 1 + ρ / 8
  · refine fin En (by linarith) ?_
    have hlo1 : 1 - σ ≤ ρ / 8 := by
      have hrl := radW_lower_u ht4
      have : A * uKV |t| ≤ VinoKV.c2 / 128 * uKV |t| := mul_le_mul_of_nonneg_right hAr hu0.le
      linarith
    have hdl := dltW_lower_u hNpos ht3 (N := N)
    have hlo2 : 1 - σ ≤ 3 * dltW wkv N (|t| + 1) / 26 := by
      have : A * uKV |t| ≤ 3 / 26 * (VinoKV.c2 / (48 * N)) * uKV |t| :=
        mul_le_mul_of_nonneg_right hAd hu0.le
      linarith
    have hζ : ζ (σ + t * I) ≠ 0 := by
      intro hz
      have h1 := hgap σ t hz ht4
      have h2 := dltW_anti wkv_ok hNpos (T := t) (U := |t| + 1) ht4
        (by rw [abs_of_pos (by positivity : (0 : ℝ) < |t| + 1)]; linarith)
      have h3 := dltW_pos wkv_ok hNpos (T := t) (by linarith)
      linarith
    have hinvg : 1 / (3 * dltW wkv N (|t| + 1) / 26) ≤ Q2 * ℓ ^ 2 := by
      have hdpos : 0 < dltW wkv N (|t| + 1) := dltW_pos wkv_ok hNpos (by
        rw [abs_of_pos (by positivity : (0 : ℝ) < |t| + 1)]; linarith)
      have hlow : 0 < VinoKV.c2 / (48 * N) * uKV |t| := by positivity
      have h1 : 1 / dltW wkv N (|t| + 1) ≤ 1 / (VinoKV.c2 / (48 * N) * uKV |t|) :=
        one_div_le_one_div_of_le hlow hdl
      -- `1/u ≤ 3ℓ²`
      set x := Real.log (ℓ + 3) with hxdef
      have hx := log_add3_ge_one (show 0 ≤ ℓ by linarith)
      have hx3 : x ≤ 3 * ℓ := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ℓ + 3 by linarith); linarith
      have hℓp : ℓ ^ ((2 : ℝ) / 3) ≤ ℓ := by
        calc ℓ ^ ((2 : ℝ) / 3) ≤ ℓ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hℓ (by norm_num)
          _ = ℓ := Real.rpow_one ℓ
      have hxp : x ^ ((1 : ℝ) / 3) ≤ x := by
        calc x ^ ((1 : ℝ) / 3) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
          _ = x := Real.rpow_one x
      have hinvu : 1 / uKV |t| ≤ 3 * ℓ ^ 2 := by
        unfold uKV; rw [← hℓdef, ← hxdef, one_div_one_div]
        have h0 : 0 ≤ ℓ ^ ((2 : ℝ) / 3) := by positivity
        have h0' : 0 ≤ x ^ ((1 : ℝ) / 3) := by positivity
        calc ℓ ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) ≤ ℓ * (3 * ℓ) :=
              mul_le_mul hℓp (hxp.trans hx3) h0' (by linarith)
          _ = 3 * ℓ ^ 2 := by ring
      have e1 : 1 / (3 * dltW wkv N (|t| + 1) / 26) = 26 / 3 * (1 / dltW wkv N (|t| + 1)) := by
        field_simp
      have e2 : 1 / (VinoKV.c2 / (48 * N) * uKV |t|) = 48 * N / VinoKV.c2 * (1 / uKV |t|) := by
        field_simp
      rw [e1, hQ2]
      calc 26 / 3 * (1 / dltW wkv N (|t| + 1))
          ≤ 26 / 3 * (48 * N / VinoKV.c2 * (1 / uKV |t|)) := by rw [← e2]; gcongr
        _ ≤ 26 / 3 * (48 * N / VinoKV.c2 * (3 * ℓ ^ 2)) := by gcongr
        _ = _ := by ring
    have hlB := logBnd_le_kv hK hc1 hnear ht4 (t := t)
    exact near_boundW (c1 := c1) wkv_ok hK hG hN hgap ht5 hζ hlo1 hlo2 hin hQ1n (by positivity) hE hinvρ
      hinvg hlB
  · rw [not_lt] at hin
    refine fin (8 * Q1 + C0) (by linarith) ?_
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    have h := norm_logDeriv_le (s := (σ : ℂ) + t * I) (by rw [hre]; linarith)
    rw [hre] at h
    have hs := hshift (σ - 1) ⟨by linarith, by linarith⟩
    have e : (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
    rw [e] at hs
    have hinv : 1 / (σ - 1) ≤ 8 * Q1 * ℓ := by
      have h1 : 1 / (σ - 1) ≤ 1 / (ρ / 8) := one_div_le_one_div_of_le (by positivity) (by linarith)
      have e2 : 1 / (ρ / 8) = 8 * (1 / ρ) := by field_simp
      nlinarith
    calc ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ 8 * Q1 * ℓ + C0 := by linarith
      _ ≤ (8 * Q1 + C0) * ℓ ^ 3 := by nlinarith

end LogDerivKV
