/-
# Sharpening, step S1c: growth from any VMVT family (round 213)

Plain statement (`growth_gen`). Suppose VMVT holds along a family `ℓ = ℓ(K)` for `K ≥ K₀`
(`K₀ ≤ 10`), with `K ≤ ℓ ≤ B₀K^q`, `η ≤ 1/32` and constants absorbed as in round 213
(`VMVTFamily`). Then for every `a` with `(2q−2)/(2q−1) ≤ a ≤ 1` there is `B` with
  `|Σ_{1≤n≤X} n^{−σ−it}| ≤ B·log|t|`
whenever `log|t| ≥ 1`, `σ ≥ 1 − (log|t|)^{−a}` and `X ≤ |t|^{5/4}`.

Instance (`growth_weak`): the weak VMVT of rounds 194–209 (`ℓ = K + 2K³`, `q = 3`) gives every
`a ≥ 4/5`, improving `6/7` from round 211.
-/
import ExpSum9
import ExpSum7

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder VinoRec

/-- A family of VMVT inputs, one for each `K ≥ K₀`. -/
def VMVTFamily (K0 Q0 : ℕ) (q B0 : ℝ) (ℓf : ℕ → ℕ) : Prop :=
  ∀ K, K0 ≤ K → K ≤ ℓf K ∧ (ℓf K : ℝ) ≤ B0 * (K : ℝ) ^ q ∧
    ∃ C η : ℝ, 0 < C ∧ η ≤ 1 / 32 ∧
      (∀ P : ℕ, 1 ≤ P →
        (J (ℓf K) K P : ℝ) ≤ C * (P : ℝ) ^ (2 * (ℓf K : ℝ) - (K : ℝ) * ((K : ℝ) + 1) / 2 + η)) ∧
      C ^ 2 * 3 ^ K * (ℓf K : ℝ) ^ (2 * K) * 2 ^ (K * (5 * K + 8)) ≤
        (2 : ℝ) ^ (2 * Q0 * ℓf K ^ 2)

/-- The threshold constant. -/
noncomputable def Aconst (q B0 : ℝ) : ℝ := 2400 * B0 + 5 * Real.log B0 + 10 * q + 20

set_option maxHeartbeats 1600000 in
/-- **A block far from the origin, from any VMVT family.** -/
theorem big_block_gen {a q B0 t σ : ℝ} {K0 Q0 : ℕ} {ℓf : ℕ → ℕ}
    (hF : VMVTFamily K0 Q0 q B0 ℓf) (hK0 : K0 ≤ 10) (hq : 2 ≤ q) (hB0 : 1 ≤ B0)
    (ha0 : 0 < a) (ha1 : a ≤ 1) {N N' : ℕ}
    (hL : 1 ≤ Real.log |t|) (hσ : 1 - Real.log |t| ^ (-a) ≤ σ)
    (hΛ : Aconst q B0 * Real.log |t| ^ (1 - a / (2 * q - 2)) ≤ Real.log N)
    (hN5 : Real.log N ≤ 5 / 4 * Real.log |t|) (_hN1 : N ≤ N') (hN2 : N' ≤ 2 * N) :
    ‖∑ n ∈ Ioc N N', 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ 2 ^ (Q0 + 2) := by
  set L := Real.log |t| with hLdef
  set ν := Real.log N with hνdef
  set A := Aconst q B0 with hAdef
  set b := 1 - a / (2 * q - 2) with hbdef
  have hq2 : (2 : ℝ) ≤ 2 * q - 2 := by linarith
  have hb1 : b ≤ 1 := by rw [hbdef]; have : 0 ≤ a / (2 * q - 2) := by positivity
                         linarith
  have hb12 : 1 / 2 ≤ b := by
    rw [hbdef]
    have : a / (2 * q - 2) ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hL0 : 0 < L := by linarith
  have hlogB : 0 ≤ Real.log B0 := Real.log_nonneg hB0
  have hA20 : 20 ≤ A := by rw [hAdef, Aconst]; nlinarith
  have hAB : 2400 * B0 ≤ A := by rw [hAdef, Aconst]; nlinarith
  have hLb : 1 ≤ L ^ b := Real.one_le_rpow hL (by linarith)
  have hν20 : 20 ≤ ν := by nlinarith
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
  -- `τ = 20L/ν`, `R = ⌊τ⌋`
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
  have hτν : τ * ν = 20 * L := by rw [hτdef]; field_simp
  have ht1 : u ^ R ≤ |t| := by
    rw [hudef, exp_pow', htexp, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_right hRle hν0.le
    linarith
  have ht2 : |t| ≤ u ^ (R + 1) := by
    rw [hudef, exp_pow', htexp, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_right hRlt.le hν0.le
    push_cast; linarith
  set K := R / 4 + 6 with hKdef
  have hKR : R + 21 ≤ 4 * K := by omega
  have hK10 : 10 ≤ K := by omega
  have hKτ : (K : ℝ) ≤ τ := by
    have h4 : 4 * K ≤ R + 24 := by omega
    have h4r : 4 * (K : ℝ) ≤ R + 24 := by exact_mod_cast h4
    linarith
  obtain ⟨hKℓ, hℓB, C, η, hC, hη, hJ, hQ⟩ := hF K (by omega)
  set ℓ := ℓf K with hℓdef
  have hK0r : (0 : ℝ) ≤ K := by positivity
  have hℓτ : (ℓ : ℝ) ≤ B0 * τ ^ q :=
    hℓB.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hK0r hKτ (by linarith)) (by linarith))
  -- `ℓ ≤ u⁴`
  have hℓu : (ℓ : ℝ) ≤ u ^ 4 := by
    have hlogL : Real.log L ≤ 2 * L ^ b := by
      have h := Real.log_le_rpow_div hL0.le (show 0 < b by linarith)
      refine h.trans ?_
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ L ^ b := by linarith
      nlinarith
    have hτq : τ ^ q ≤ L ^ q := Real.rpow_le_rpow (by linarith) hτL (by linarith)
    have hBL : B0 * L ^ q = Real.exp (Real.log B0 + q * Real.log L) := by
      rw [Real.exp_add, Real.exp_log (by linarith), Real.rpow_def_of_pos hL0, mul_comm (Real.log L)]
    calc (ℓ : ℝ) ≤ B0 * τ ^ q := hℓτ
      _ ≤ B0 * L ^ q := mul_le_mul_of_nonneg_left hτq (by linarith)
      _ = Real.exp (Real.log B0 + q * Real.log L) := hBL
      _ ≤ u ^ 4 := by
          rw [hudef, exp_pow', Real.exp_le_exp]
          have h1 : A * L ^ b ≤ ν := hΛ
          have h2 : (5 * Real.log B0 + 10 * q) * L ^ b ≤ A * L ^ b := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            rw [hAdef, Aconst]; nlinarith
          have h3 : 5 * Real.log B0 ≤ 5 * Real.log B0 * L ^ b := by nlinarith
          have h4 : q * Real.log L ≤ 2 * q * L ^ b := by nlinarith
          push_cast
          nlinarith
  obtain ⟨G, hG, hG1, hGR⟩ := window hR16 hKR
  have hbs := fun m (hm1 : N ≤ m) (hm2 : m ≤ N') =>
    block_saving_multi (t := t) (N' := m) G hu hN hm1 (by omega) (by omega) hKℓ hℓu ht1 ht2 hKR
      hG hC hη hJ hQ
  set sv : ℝ := ((G.card : ℝ) * R / 6 - 1 / 2) / (2 * (ℓ : ℝ) ^ 2) with hsv
  -- the saving beats the loss
  have hℓpos : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast (show 1 ≤ ℓ by omega)
    linarith
  have hsave : 20 * (1 - σ) ≤ sv := by
    have hsv0 : R ^ 2 / (600 * (ℓ : ℝ) ^ 2) ≤ sv := by
      rw [hsv, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (ℓ : ℝ)]
    have hδ : 1 - σ ≤ L ^ (-a) := by linarith
    have hLa0 : 0 ≤ L ^ (-a) := Real.rpow_nonneg hL0.le _
    -- `τ ≤ (20/A) L^{a/(2q−2)}`
    have hτb : τ ≤ 20 / A * L ^ (a / (2 * q - 2)) := by
      have hLL : L = L ^ b * L ^ (a / (2 * q - 2)) := by
        rw [← Real.rpow_add hL0, hbdef]; ring_nf; exact (Real.rpow_one L).symm
      rw [hτdef, div_le_iff₀ hν0]
      calc 20 * L = 20 * (L ^ b * L ^ (a / (2 * q - 2))) := by rw [← hLL]
        _ ≤ 20 / A * L ^ (a / (2 * q - 2)) * (A * L ^ b) := by
            field_simp; ring_nf; exact le_rfl
        _ ≤ 20 / A * L ^ (a / (2 * q - 2)) * ν := by
            apply mul_le_mul_of_nonneg_left hΛ (by positivity)
    have hτpow : τ ^ (2 * q - 2) ≤ (20 / A) ^ 2 * L ^ a := by
      have h1 : τ ^ (2 * q - 2) ≤ (20 / A * L ^ (a / (2 * q - 2))) ^ (2 * q - 2) :=
        Real.rpow_le_rpow (by linarith) hτb (by linarith)
      have h2 : (20 / A * L ^ (a / (2 * q - 2))) ^ (2 * q - 2) =
          (20 / A) ^ (2 * q - 2) * L ^ a := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hL0.le _), ← Real.rpow_mul hL0.le,
          div_mul_cancel₀ a (by linarith : (2 * q - 2) ≠ 0)]
      have h3 : (20 / A) ^ (2 * q - 2) ≤ (20 / A) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by positivity) (by rw [div_le_one (by linarith)]; linarith) hq2
      rw [Real.rpow_two] at h3
      calc τ ^ (2 * q - 2) ≤ _ := h1
        _ = _ := h2
        _ ≤ (20 / A) ^ 2 * L ^ a := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hL0.le _)
    have hℓ2 : (ℓ : ℝ) ^ 2 ≤ B0 ^ 2 * (τ ^ (2 * q - 2) * τ ^ 2) := by
      have e : τ ^ (2 * q - 2) * τ ^ 2 = (τ ^ q) ^ 2 := by
        rw [← Real.rpow_natCast (τ ^ q) 2, ← Real.rpow_mul (by linarith), ← Real.rpow_two,
          ← Real.rpow_add (by linarith)]; ring_nf
      rw [e, ← mul_pow]
      exact pow_le_pow_left₀ hℓpos.le hℓτ 2
    have hRτ : (15 / 16) * τ ≤ R := by linarith
    have hkey : 12000 * L ^ (-a) * (ℓ : ℝ) ^ 2 ≤ R ^ 2 := by
      have hLaa : L ^ (-a) * L ^ a = 1 := by
        rw [← Real.rpow_add hL0]; simp
      have hA2 : 12000 * B0 ^ 2 * (20 / A) ^ 2 ≤ 225 / 256 := by
        rw [div_pow, mul_div_assoc']
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have hτ0 : 0 ≤ τ ^ 2 := by positivity
      calc 12000 * L ^ (-a) * (ℓ : ℝ) ^ 2
          ≤ 12000 * L ^ (-a) * (B0 ^ 2 * (τ ^ (2 * q - 2) * τ ^ 2)) := by gcongr
        _ ≤ 12000 * L ^ (-a) * (B0 ^ 2 * ((20 / A) ^ 2 * L ^ a * τ ^ 2)) := by gcongr
        _ = 12000 * B0 ^ 2 * (20 / A) ^ 2 * τ ^ 2 * (L ^ (-a) * L ^ a) := by ring
        _ ≤ 225 / 256 * τ ^ 2 * 1 := by rw [hLaa]; gcongr
        _ ≤ R ^ 2 := by nlinarith
    rcases le_or_gt (1 - σ) 0 with h | h
    · have : 0 ≤ sv := le_trans (by positivity) hsv0
      linarith
    have : 20 * (1 - σ) * (600 * (ℓ : ℝ) ^ 2) ≤ R ^ 2 := by nlinarith
    calc 20 * (1 - σ) ≤ R ^ 2 / (600 * (ℓ : ℝ) ^ 2) := by
          rw [le_div_iff₀ (by positivity)]; linarith
      _ ≤ sv := hsv0
  -- weights
  have hσ0 : 0 ≤ σ := by
    have : L ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
    linarith
  rw [sum_congr rfl (fun n hn => cpow_phase n (by have := (mem_Ioc.mp hn).1; omega) σ t)]
  set Bv : ℝ := 2 ^ (Q0 + 2) * N / u ^ sv with hBv
  have hrpos : 0 < u ^ sv := Real.rpow_pos_of_pos hu0 _
  have hab := abel_bound (fun n => phaseF t n) (fun n => (n : ℝ) ^ (-σ)) N N' Bv
    (by rw [hBv]; positivity) (fun m hm1 hm2 => hbs m hm1 hm2)
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
    _ = 2 ^ (Q0 + 2) * ((N : ℝ) ^ (-σ) * N) / u ^ sv := by rw [hBv]; ring
    _ ≤ 2 ^ (Q0 + 2) * u ^ sv / u ^ sv := by gcongr
    _ = 2 ^ (Q0 + 2) := by field_simp

/-- **Step S1c: growth from any VMVT family.** -/
theorem growth_gen {a q B0 : ℝ} {K0 Q0 : ℕ} {ℓf : ℕ → ℕ}
    (hF : VMVTFamily K0 Q0 q B0 ℓf) (hK0 : K0 ≤ 10) (hq : 2 ≤ q) (hB0 : 1 ≤ B0)
    (ha1 : (2 * q - 2) / (2 * q - 1) ≤ a) (ha2 : a ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ t σ : ℝ, 1 ≤ Real.log |t| → 1 - Real.log |t| ^ (-a) ≤ σ →
      ∀ X : ℕ, (X : ℝ) ≤ |t| ^ ((5 : ℝ) / 4) →
        ‖∑ n ∈ Ioc 0 X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ B * Real.log |t| := by
  set A := Aconst q B0 with hAdef
  have hlogB : 0 ≤ Real.log B0 := Real.log_nonneg hB0
  have hA20 : 20 ≤ A := by rw [hAdef, Aconst]; nlinarith
  have hq1 : (0 : ℝ) < 2 * q - 1 := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (by apply div_pos <;> linarith) ha1
  refine ⟨2 * Real.exp A * (2 + A) + 3 * 2 ^ (Q0 + 2), by positivity, ?_⟩
  intro t σ hL hσ X hX
  set L := Real.log |t| with hLdef
  have hL0 : 0 < L := by linarith
  have htpos : 0 < |t| := by
    rcases (abs_nonneg t).lt_or_eq with h | h
    · exact h
    · rw [hLdef, ← h, Real.log_zero] at hL; linarith
  set δ := L ^ (-a) with hδdef
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hL0.le _
  have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  set b := 1 - a / (2 * q - 2) with hbdef
  have hb1 : b ≤ 1 := by
    rw [hbdef]; have : 0 ≤ a / (2 * q - 2) := div_nonneg ha0.le (by linarith)
    linarith
  have hb0 : 0 ≤ b := by
    rw [hbdef]
    have : a / (2 * q - 2) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  set Λ := A * L ^ b with hΛdef
  have hP1 : 1 ≤ L ^ b := Real.one_le_rpow hL hb0
  have hPL : L ^ b ≤ L := by
    calc L ^ b ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL hb1
      _ = L := Real.rpow_one L
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛδ : Λ * δ ≤ A := by
    have e : Λ * δ = A * L ^ (b + -a) := by
      rw [hΛdef, hδdef, Real.rpow_add hL0]; ring
    rw [e]
    have hba : b + -a ≤ 0 := by
      rw [hbdef]
      have h1 : (2 * q - 2) / (2 * q - 1) * (2 * q - 1) = 2 * q - 2 := by field_simp
      have h2 : a * (2 * q - 1) ≥ 2 * q - 2 := by
        have := mul_le_mul_of_nonneg_right ha1 hq1.le; linarith
      have hq2 : (0 : ℝ) < 2 * q - 2 := by linarith
      have : 1 - a ≤ a / (2 * q - 2) := by rw [le_div_iff₀ hq2]; nlinarith
      linarith
    have : L ^ (b + -a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL hba
    nlinarith
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
  have hsmall : ‖∑ n ∈ Ioc 0 Y, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤
      2 * Real.exp A * (2 + A) * L := by
    have hYle : (Y : ℝ) ≤ 2 * Real.exp Λ := by
      have : (Y : ℝ) ≤ N0 := by exact_mod_cast min_le_right X N0
      linarith
    refine (small_part Y hYle hΛ0 hδ0 hδ1 (by linarith)).trans ?_
    have h1 : Real.exp (Λ * δ) ≤ Real.exp A := Real.exp_le_exp.mpr hΛδ
    have h2 : 2 + Λ ≤ (2 + A) * L := by nlinarith
    calc 2 * Real.exp (Λ * δ) * (2 + Λ) ≤ 2 * Real.exp A * ((2 + A) * L) := by gcongr
      _ = 2 * Real.exp A * (2 + A) * L := by ring
  have hbig : ‖∑ n ∈ Ioc Y X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ 3 * 2 ^ (Q0 + 2) * L := by
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
    have hblocks := dyadic (fun n => 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)) N0 X (2 ^ (Q0 + 2))
      (by positivity)
      (fun N N' hN0N hNN' hN'2 hN'X => by
        have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
        refine big_block_gen hF hK0 hq hB0 ha0 ha2 hL hσ ?_ ?_ hNN' hN'2
        · have := Real.log_le_log (Real.exp_pos _)
            (hN0ge.trans (show (N0 : ℝ) ≤ N by exact_mod_cast hN0N))
          rwa [Real.log_exp] at this
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
    have hQ : (0 : ℝ) ≤ 2 ^ (Q0 + 2) := by positivity
    push_cast
    nlinarith
  calc ‖∑ n ∈ Ioc 0 Y, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I) +
        ∑ n ∈ Ioc Y X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖
      ≤ ‖∑ n ∈ Ioc 0 Y, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ +
          ‖∑ n ∈ Ioc Y X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ := norm_add_le _ _
    _ ≤ 2 * Real.exp A * (2 + A) * L + 3 * 2 ^ (Q0 + 2) * L := add_le_add hsmall hbig
    _ = (2 * Real.exp A * (2 + A) + 3 * 2 ^ (Q0 + 2)) * L := by ring

/-- **The weak VMVT is a family with `q = 3`.** -/
theorem weakFamily : VMVTFamily 10 25 3 3 (fun K => K + 2 * K ^ 2 * K) := by
  intro K hK
  have hK2 : 2 ≤ K := by omega
  refine ⟨by nlinarith, ?_, Cvm K (2 * K ^ 2), eta K (2 * K ^ 2),
    (vmvt_explicit hK2 (2 * K ^ 2)).1, eta_two_sq32 hK, ?_, const_bound2 hK2⟩
  · have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    nlinarith [pow_le_pow_right₀ hKr (show 1 ≤ 3 by norm_num)]
  · intro P hP
    have h := (vmvt_explicit hK2 (2 * K ^ 2)).2 P hP
    have e : K + 2 * K ^ 2 * K = K + 2 * K ^ 2 * K := rfl
    convert h using 3
    simp only [expo]

/-- **S1: growth for every `a ≥ 4/5` from the weak VMVT.** -/
theorem growth_weak {a : ℝ} (ha1 : 4 / 5 ≤ a) (ha2 : a ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ t σ : ℝ, 1 ≤ Real.log |t| → 1 - Real.log |t| ^ (-a) ≤ σ →
      ∀ X : ℕ, (X : ℝ) ≤ |t| ^ ((5 : ℝ) / 4) →
        ‖∑ n ∈ Ioc 0 X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ B * Real.log |t| :=
  growth_gen weakFamily le_rfl (by norm_num) (by norm_num) (by norm_num; linarith) ha2

end ExpSum
