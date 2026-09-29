/-
# The last bit, step R1: growth on the Korobov–Vinogradov region (round 215)

Plain statement (`growth_kv`). There are `c₀ > 0` and `B` such that, with `L = log|t|`,
  `|Σ_{1≤n≤X} n^{−σ−it}| ≤ B·L²`
whenever `L ≥ 5`, `σ ≥ 1 − c₀(log L / L)^{2/3}` and `X ≤ |t|^{5/4}`.

What changed from round 214. The window of good coordinates saves about `u^{K²/3}`, so the VMVT
excess only has to satisfy `η ≤ K²/8192`, not `η ≤ 1/32`. By `vmvt2` that holds after
`m = 12K` steps, so `ℓ = K(12K+1) ≤ 13K²` with no `log K`, and the per-block saving is
`N^{−c/λ²}` with no logarithmic loss (`big_block_kv`). With the trivial range `log N ≤ Λ`,
`Λ = 20L(log L/L)^{1/3}`, the initial segment costs `e^{Λδ}(2+Λ) ≤ L(2+Λ)`.
-/
import VinoFam

open Finset Complex

namespace VinoKV

open Vinogradov VinoRec VinoRec2 ExpSum VinoFam

lemma eta_kv {K : ℕ} (hK : 2 ≤ K) : eta2 K (12 * K) ≤ (K : ℝ) ^ 2 / 8192 := by
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have h0 : 0 ≤ 1 - 1 / (K : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hpow : (1 - 1 / (K : ℝ)) ^ (12 * K) ≤ 1 / 4096 := by
    rw [show 12 * K = K * 12 by ring, pow_mul]
    calc ((1 - 1 / (K : ℝ)) ^ K) ^ 12 ≤ (1 / 2) ^ 12 :=
          pow_le_pow_left₀ (pow_nonneg h0 _) (half_pow hK) _
      _ = 1 / 4096 := by norm_num
  have hc : 0 ≤ (K : ℝ) * ((K : ℝ) - 1) / 2 := by nlinarith
  unfold eta2
  calc (1 - 1 / (K : ℝ)) ^ (12 * K) * ((K : ℝ) * ((K : ℝ) - 1) / 2)
      ≤ 1 / 4096 * ((K : ℝ) * ((K : ℝ) - 1) / 2) := mul_le_mul_of_nonneg_right hpow hc
    _ ≤ (K : ℝ) ^ 2 / 8192 := by nlinarith

/-- The saving constant. -/
noncomputable def c2 : ℝ := 1 / 5000000

set_option maxHeartbeats 3200000 in
/-- **A block with no logarithmic loss.** -/
theorem big_block_kv {t σ δ : ℝ} {N N' : ℕ}
    (hL : 5 ≤ Real.log |t|) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hσ : 1 - δ ≤ σ)
    (hν20 : 20 ≤ Real.log N)
    (hℓc : 13 * Real.log |t| ^ 2 ≤ Real.exp (Real.log N / 5))
    (hsav : δ * (20 * Real.log |t| / Real.log N) ^ 2 ≤ c2)
    (hN5 : Real.log N ≤ 5 / 4 * Real.log |t|) (hN1 : N ≤ N') (hN2 : N' ≤ 2 * N) :
    ‖∑ n ∈ Ioc N N', 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ 2 ^ (300 + 2) := by
  set L := Real.log |t| with hLdef
  set ν := Real.log N with hνdef
  have hL0 : 0 < L := by linarith
  have hν0 : 0 < ν := by linarith
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [hνdef, h, Nat.cast_zero, Real.log_zero] at hν20; linarith
    · exact h
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNexp : (N : ℝ) = Real.exp ν := (Real.exp_log hNr).symm
  have htpos : 0 < |t| := by
    rcases (abs_nonneg t).lt_or_eq with h | h
    · exact h
    · rw [hLdef, ← h, Real.log_zero] at hL; linarith
  have htexp : |t| = Real.exp L := (Real.exp_log htpos).symm
  set τ := 20 * L / ν with hτdef
  have hτ16 : 16 ≤ τ := by rw [hτdef, le_div_iff₀ hν0]; linarith
  have hτL : τ ≤ L := by rw [hτdef, div_le_iff₀ hν0]; nlinarith
  set R := ⌊τ⌋₊ with hRdef
  have hRle : (R : ℝ) ≤ τ := Nat.floor_le (by linarith)
  have hRlt : τ < R + 1 := Nat.lt_floor_add_one τ
  have hR16 : 16 ≤ R := Nat.le_floor (by exact_mod_cast hτ16)
  set u := Real.exp (ν / 20) with hudef
  have hu : 2 ≤ u := by
    have h2 := Real.log_two_lt_d9
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ u := Real.exp_le_exp.mpr (by linarith)
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hN : (N : ℝ) = u ^ 20 := by rw [hudef, exp_pow', hNexp]; congr 1; push_cast; ring
  have ht1 : u ^ R ≤ |t| := by
    rw [hudef, exp_pow', htexp, Real.exp_le_exp]
    have hτν : τ * ν = 20 * L := by rw [hτdef]; field_simp
    have := mul_le_mul_of_nonneg_right hRle hν0.le
    linarith
  have ht2 : |t| ≤ u ^ (R + 1) := by
    rw [hudef, exp_pow', htexp, Real.exp_le_exp]
    have hτν : τ * ν = 20 * L := by rw [hτdef]; field_simp
    have := mul_le_mul_of_nonneg_right hRlt.le hν0.le
    push_cast; linarith
  set K := R / 4 + 6 with hKdef
  have hKR : R + 21 ≤ 4 * K := by omega
  have hK10 : 10 ≤ K := by omega
  have hK2 : 2 ≤ K := by omega
  have hKτ : (K : ℝ) ≤ τ := by
    have h4 : 4 * K ≤ R + 24 := by omega
    have h4r : 4 * (K : ℝ) ≤ R + 24 := by exact_mod_cast h4
    linarith
  set m := 12 * K with hm
  set ℓ := K + m * K with hℓdef
  have hKℓ : K ≤ ℓ := by omega
  have hℓ13 : (ℓ : ℝ) ≤ 13 * (K : ℝ) ^ 2 := by
    rw [hℓdef, hm]; push_cast
    have : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    nlinarith
  have hK0r : (0 : ℝ) ≤ K := by positivity
  have hℓτ : (ℓ : ℝ) ≤ 13 * τ ^ 2 := hℓ13.trans (by nlinarith)
  have hℓu : (ℓ : ℝ) ≤ u ^ 4 := by
    rw [hudef, exp_pow']
    calc (ℓ : ℝ) ≤ 13 * τ ^ 2 := hℓτ
      _ ≤ 13 * L ^ 2 := by nlinarith
      _ ≤ Real.exp (ν / 5) := hℓc
      _ = Real.exp (((4 : ℕ) : ℝ) * ν / 20) := by congr 1; push_cast; ring
  obtain ⟨G, hG, hG1, hGR⟩ := window hR16 hKR
  obtain ⟨hC, hJ⟩ := vmvt2 hK2 m
  set H : ℝ := (K : ℝ) ^ 2 / 8192 with hH
  have hη := eta_kv hK2
  have hJ' : ∀ P : ℕ, 1 ≤ P → (J ℓ K P : ℝ) ≤
      Cv2 K m * (P : ℝ) ^ (2 * (ℓ : ℝ) - (K : ℝ) * ((K : ℝ) + 1) / 2 + eta2 K m) := by
    intro P hP
    have h := hJ P hP
    convert h using 3
    all_goals first | rfl | (unfold VinoRec2.expo2; push_cast; ring)
  have hQ := const_bound_m hK10 (show K ≤ m by omega)
  have hbs := fun m' (hm1 : N ≤ m') (hm2 : m' ≤ N') =>
    block_saving_multiH (t := t) (N' := m') G hu hN hm1 (by omega) (by omega) hKℓ hℓu ht1 ht2
      hKR hG hC (by positivity : (0 : ℝ) ≤ H) hη hJ' hQ
  set sv : ℝ := ((G.card : ℝ) * R / 6 - 16 * H) / (2 * (ℓ : ℝ) ^ 2) with hsv
  have hℓpos : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast (show 1 ≤ ℓ by omega)
    linarith
  -- the saving beats the loss
  have hsave : 20 * (1 - σ) ≤ sv := by
    have hRr : (16 : ℝ) ≤ R := by exact_mod_cast hR16
    have hK58 : (K : ℝ) ≤ 5 / 8 * R := by
      have h4 : 4 * K ≤ R + 24 := by omega
      have h4r : 4 * (K : ℝ) ≤ R + 24 := by exact_mod_cast h4
      linarith
    have h16H : 16 * H ≤ R ^ 2 / 1300 := by
      rw [hH]; nlinarith
    have hnum : R ^ 2 / 600 ≤ (G.card : ℝ) * R / 6 - 16 * H := by nlinarith
    have hsv0 : R ^ 2 / (1200 * (ℓ : ℝ) ^ 2) ≤ sv := by
      rw [hsv, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (ℓ : ℝ)]
    have hδτ : δ * τ ^ 2 ≤ c2 := hsav
    have hRτ : (15 / 16) * τ ≤ R := by linarith
    have hkey : 24000 * δ * (ℓ : ℝ) ^ 2 ≤ R ^ 2 := by
      have hℓ2 : (ℓ : ℝ) ^ 2 ≤ 169 * τ ^ 2 * τ ^ 2 := by
        have := pow_le_pow_left₀ hℓpos.le hℓτ 2
        nlinarith
      have hτ0 : 0 ≤ τ ^ 2 := by positivity
      calc 24000 * δ * (ℓ : ℝ) ^ 2 ≤ 24000 * δ * (169 * τ ^ 2 * τ ^ 2) := by gcongr
        _ = 24000 * 169 * (δ * τ ^ 2) * τ ^ 2 := by ring
        _ ≤ 24000 * 169 * c2 * τ ^ 2 := by gcongr
        _ ≤ R ^ 2 := by rw [c2]; nlinarith
    rcases le_or_gt (1 - σ) 0 with h | h
    · have : 0 ≤ sv := le_trans (by positivity) hsv0
      linarith
    have : 20 * (1 - σ) * (1200 * (ℓ : ℝ) ^ 2) ≤ R ^ 2 := by nlinarith
    calc 20 * (1 - σ) ≤ R ^ 2 / (1200 * (ℓ : ℝ) ^ 2) := by
          rw [le_div_iff₀ (by positivity)]; linarith
      _ ≤ sv := hsv0
  -- weights
  have hσ0 : 0 ≤ σ := by linarith
  rw [sum_congr rfl (fun n hn => cpow_phase n (by have := (mem_Ioc.mp hn).1; omega) σ t)]
  set Bv : ℝ := 2 ^ (300 + 2) * N / u ^ sv with hBv
  have hrpos : 0 < u ^ sv := Real.rpow_pos_of_pos hu0 _
  have hab := abel_bound (fun n => phaseF t n) (fun n => (n : ℝ) ^ (-σ)) N N' Bv
    (by rw [hBv]; positivity) (fun m' hm1 hm2 => hbs m' hm1 hm2)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (fun n hn1 _ => Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < n by omega))
      (by push_cast; linarith) (by linarith))
  refine hab.trans ?_
  have h1 : ((N + 1 : ℕ) : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hNr (by push_cast; linarith) (by linarith)
  have h2 : (N : ℝ) ^ (-σ) * N ≤ u ^ sv := by
    have e : (N : ℝ) ^ (-σ) * N = u ^ (20 * (1 - σ)) := by
      calc (N : ℝ) ^ (-σ) * N = (N : ℝ) ^ (-σ) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (N : ℝ) ^ (-σ + 1) := (Real.rpow_add hNr _ _).symm
        _ = (u ^ 20 : ℝ) ^ (-σ + 1) := by rw [hN]
        _ = u ^ (20 * (1 - σ)) := by
            rw [← Real.rpow_natCast u 20, ← Real.rpow_mul hu0.le]; push_cast; ring_nf
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hu1 hsave
  have hB0' : 0 ≤ Bv := by rw [hBv]; positivity
  calc ((N + 1 : ℕ) : ℝ) ^ (-σ) * Bv ≤ (N : ℝ) ^ (-σ) * Bv := mul_le_mul_of_nonneg_right h1 hB0'
    _ = 2 ^ (300 + 2) * ((N : ℝ) ^ (-σ) * N) / u ^ sv := by rw [hBv]; ring
    _ ≤ 2 ^ (300 + 2) * u ^ sv / u ^ sv := by gcongr
    _ = 2 ^ (300 + 2) := by field_simp

/-- The Korobov–Vinogradov width `c₂(log L/L)^{2/3}`. -/
noncomputable def δkv (L : ℝ) : ℝ := c2 * (Real.log L / L) ^ ((2 : ℝ) / 3)

set_option maxHeartbeats 1600000 in
/-- **Step R1: growth on the Korobov–Vinogradov region.** -/
theorem growth_kv :
    ∃ B : ℝ, 0 < B ∧ ∀ t σ : ℝ, 5 ≤ Real.log |t| → 1 - δkv (Real.log |t|) ≤ σ →
      ∀ X : ℕ, (X : ℝ) ≤ |t| ^ ((5 : ℝ) / 4) →
        ‖∑ n ∈ Ioc 0 X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ B * Real.log |t| ^ 2 := by
  have hc2 : (0 : ℝ) < c2 := by rw [c2]; norm_num
  refine ⟨2 * (2 + 20) + 3 * 2 ^ (300 + 2), by positivity, ?_⟩
  intro t σ hL hσ X hX
  set L := Real.log |t| with hLdef
  have hL0 : 0 < L := by linarith
  have htpos : 0 < |t| := by
    rcases (abs_nonneg t).lt_or_eq with h | h
    · exact h
    · rw [hLdef, ← h, Real.log_zero] at hL; linarith
  -- `w = (log L / L)^{1/3}`
  have hlogL : 1 < Real.log L := by
    rw [Real.lt_log_iff_exp_lt hL0]
    have := Real.exp_one_lt_d9; linarith
  have hlogLL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  set x := Real.log L / L with hxdef
  have hx0 : 0 < x := div_pos (by linarith) hL0
  have hx1 : x ≤ 1 := by rw [hxdef, div_le_one hL0]; exact hlogLL
  set w := x ^ ((1 : ℝ) / 3) with hwdef
  have hw0 : 0 < w := Real.rpow_pos_of_pos hx0 _
  have hw1 : w ≤ 1 := Real.rpow_le_one hx0.le hx1 (by norm_num)
  have hw2 : w ^ 2 = x ^ ((2 : ℝ) / 3) := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hw3 : w ^ 3 = x := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  set δ := δkv L with hδdef
  have hδw : δ = c2 * w ^ 2 := by rw [hδdef, δkv, hw2]
  have hδ0 : 0 ≤ δ := by rw [hδw]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδw, c2]; nlinarith [pow_le_one₀ hw0.le hw1 (n := 2)]
  set Λ := 20 * L * w with hΛdef
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛδ : Λ * δ ≤ Real.log L := by
    have e : Λ * δ = 20 * c2 * (L * w ^ 3) := by rw [hΛdef, hδw]; ring
    rw [e, hw3, hxdef, mul_div_cancel₀ _ hL0.ne', c2]
    have : 0 < Real.log L := by linarith
    nlinarith
  -- `L^{2/3} ≤ L w` and `Λ ≥ 20`, `13 L² ≤ e^{ν/5}` for `ν ≥ Λ`
  have hLw3 : (L * w) ^ 3 = L ^ 2 * Real.log L := by
    rw [mul_pow, hw3, hxdef]; field_simp
  have hLw : 1 ≤ L * w := by
    by_contra hc; push Not at hc
    have : (L * w) ^ 3 < 1 := by
      have h0 : 0 ≤ L * w := by positivity
      calc (L * w) ^ 3 < 1 ^ 3 := pow_lt_pow_left₀ hc h0 (by norm_num)
        _ = 1 := by norm_num
    rw [hLw3] at this; nlinarith
  have hΛ20 : 20 ≤ Λ := by rw [hΛdef]; nlinarith
  have hℓcond : ∀ ν, Λ ≤ ν → 13 * L ^ 2 ≤ Real.exp (ν / 5) := by
    intro ν hν
    -- `log(13 L²) ≤ 4 L w ≤ Λ/5`
    have hy : L ^ ((2 : ℝ) / 3) ≤ L * w := by
      have h1 : (L ^ ((2 : ℝ) / 3)) ^ 3 = L ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
      have h2 : L ^ 2 ≤ (L * w) ^ 3 := by rw [hLw3]; nlinarith
      rw [← h1] at h2
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h2
    have hlog23 : Real.log L ≤ 3 / 2 * L ^ ((2 : ℝ) / 3) := by
      have := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 2 / 3 by norm_num)
      linarith
    have h13 : Real.log 13 ≤ L ^ ((2 : ℝ) / 3) := by
      have h5 : (5 : ℝ) ^ ((2 : ℝ) / 3) ≤ L ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow (by norm_num) hL (by norm_num)
      have h53 : (2.6 : ℝ) ≤ (5 : ℝ) ^ ((2 : ℝ) / 3) := by
        have hc : ((2.6 : ℝ) ^ (3 : ℕ)) ≤ ((5 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) := by
          rw [← Real.rpow_natCast ((5 : ℝ) ^ ((2 : ℝ) / 3)), ← Real.rpow_mul (by norm_num)]
          norm_num
        exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hc
      have hl13 : Real.log 13 ≤ 2.6 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have := Real.exp_one_gt_d9
        have h1 : (2.7182818283 : ℝ) ^ (26 : ℕ) ≤ Real.exp 1 ^ (26 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) this.le _
        rw [← Real.exp_nat_mul] at h1
        have h2 : Real.exp ((26 : ℕ) * 1) = Real.exp 2.6 ^ (10 : ℕ) := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [h2] at h1
        by_contra hc; push Not at hc
        have : Real.exp 2.6 ^ (10 : ℕ) < (13 : ℝ) ^ (10 : ℕ) :=
          pow_lt_pow_left₀ hc (Real.exp_pos _).le (by norm_num)
        norm_num at h1 this; linarith
      linarith
    rw [← Real.exp_log (show (0 : ℝ) < 13 * L ^ 2 by positivity), Real.exp_le_exp,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have : 4 * (L * w) ≤ ν / 5 := by rw [hΛdef] at hν; linarith
    push_cast
    nlinarith
  -- the initial segment
  set N0 := ⌈Real.exp Λ⌉₊ with hN0def
  have hN0ge : Real.exp Λ ≤ N0 := Nat.le_ceil _
  have hN0lt : (N0 : ℝ) < Real.exp Λ + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hN0le : (N0 : ℝ) ≤ 2 * Real.exp Λ := by
    have := Real.one_le_exp hΛ0; linarith
  have hN01 : 1 ≤ N0 := by
    have : (1 : ℝ) ≤ N0 := le_trans (Real.one_le_exp hΛ0) hN0ge
    exact_mod_cast this
  set Y := min X N0 with hYdef
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le Y) (min_le_left X N0)]
  have hL1 : 1 ≤ L := by linarith
  have hsmall : ‖∑ n ∈ Ioc 0 Y, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ 2 * (2 + 20) * L ^ 2 := by
    have hYle : (Y : ℝ) ≤ 2 * Real.exp Λ := by
      have : (Y : ℝ) ≤ N0 := by exact_mod_cast min_le_right X N0
      linarith
    refine (small_part Y hYle hΛ0 hδ0 hδ1 hσ).trans ?_
    have h1 : Real.exp (Λ * δ) ≤ L := by
      calc Real.exp (Λ * δ) ≤ Real.exp (Real.log L) := Real.exp_le_exp.mpr hΛδ
        _ = L := Real.exp_log hL0
    have h2 : 2 + Λ ≤ (2 + 20) * L := by rw [hΛdef]; nlinarith
    calc 2 * Real.exp (Λ * δ) * (2 + Λ) ≤ 2 * L * ((2 + 20) * L) := by gcongr
      _ = 2 * (2 + 20) * L ^ 2 := by ring
  have hbig : ‖∑ n ∈ Ioc Y X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ 3 * 2 ^ (300 + 2) * L ^ 2 := by
    rcases le_or_gt X N0 with hXN | hXN
    · have : Y = X := min_eq_left hXN
      rw [this, Finset.Ioc_self, Finset.sum_empty, norm_zero]; positivity
    have hY : Y = N0 := min_eq_right hXN.le
    rw [hY]
    have hX0 : X ≠ 0 := by omega
    have hXr : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX0
    have hlogX : Real.log X ≤ 5 / 4 * L := by
      have := Real.log_le_log hXr hX
      rwa [Real.log_rpow htpos] at this
    have hblocks := dyadic (fun n => 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)) N0 X (2 ^ (300 + 2))
      (by positivity)
      (fun N N' hN0N hNN' hN'2 hN'X => by
        have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
        have hΛν : Λ ≤ Real.log N := by
          have := Real.log_le_log (Real.exp_pos _)
            (hN0ge.trans (show (N0 : ℝ) ≤ N by exact_mod_cast hN0N))
          rwa [Real.log_exp] at this
        have hν0 : 0 < Real.log N := by linarith
        refine big_block_kv hL hδ0 hδ1 hσ (by linarith) (hℓcond _ hΛν) ?_ ?_ hNN' hN'2
        · -- `δ (20L/ν)² ≤ δ (20L/Λ)² = c₂`
          have h1 : 20 * L / Real.log N ≤ 20 * L / Λ :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hΛν
          have h2 : (20 * L / Real.log N) ^ 2 ≤ (20 * L / Λ) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h1 2
          have h3 : δ * (20 * L / Λ) ^ 2 = c2 := by
            rw [hδw, hΛdef]; field_simp
          calc δ * (20 * L / Real.log N) ^ 2 ≤ δ * (20 * L / Λ) ^ 2 :=
                mul_le_mul_of_nonneg_left h2 hδ0
            _ = c2 := h3
        · have hNX : (N : ℝ) ≤ X := by exact_mod_cast (hNN'.trans hN'X)
          exact (Real.log_le_log hNr hNX).trans hlogX)
      (Nat.log 2 X + 1) X le_rfl (by
        have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
        calc X ≤ 2 ^ (Nat.log 2 X + 1) := this.le
          _ ≤ 2 ^ (Nat.log 2 X + 1) * N0 := Nat.le_mul_of_pos_right _ hN01)
    refine hblocks.trans ?_
    have hlog2 : (Nat.log 2 X : ℝ) * Real.log 2 ≤ Real.log X := by
      have h := Nat.pow_log_le_self 2 hX0
      have h' : ((2 ^ Nat.log 2 X : ℕ) : ℝ) ≤ X := by exact_mod_cast h
      have := Real.log_le_log (by positivity) h'
      rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at this
    have hl2 := Real.log_two_gt_d9
    have hj : (Nat.log 2 X : ℝ) ≤ 2 * L := by
      have : (Nat.log 2 X : ℝ) * 0.6931471803 ≤ 5 / 4 * L := by
        have : (Nat.log 2 X : ℝ) * 0.6931471803 ≤ (Nat.log 2 X : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
        linarith
      nlinarith
    have hQ : (0 : ℝ) ≤ 2 ^ (300 + 2) := by positivity
    have hj3 : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 3 * L ^ 2 := by push_cast; nlinarith
    calc ((Nat.log 2 X + 1 : ℕ) : ℝ) * 2 ^ (300 + 2) ≤ 3 * L ^ 2 * 2 ^ (300 + 2) :=
          mul_le_mul_of_nonneg_right hj3 hQ
      _ = 3 * 2 ^ (300 + 2) * L ^ 2 := by ring
  calc ‖∑ n ∈ Ioc 0 Y, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I) +
        ∑ n ∈ Ioc Y X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖
      ≤ ‖∑ n ∈ Ioc 0 Y, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ +
          ‖∑ n ∈ Ioc Y X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ := norm_add_le _ _
    _ ≤ 2 * (2 + 20) * L ^ 2 + 3 * 2 ^ (300 + 2) * L ^ 2 := add_le_add hsmall hbig
    _ = (2 * (2 + 20) + 3 * 2 ^ (300 + 2)) * L ^ 2 := by ring

end VinoKV
