import SieveLeaves

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves
open SieveCert (V DEN H U1 U2 cand dec inKK ne3 counted4 surelyEval cell inside allowed lim)

namespace SieveQ

open Classical

/-! ### The exponents -/

/-- The sieve's floor exponent, `a₀ = L·V/DEN`. -/
noncomputable def a0 : ℝ := 2333 / 1000 * ((V : ℝ) / DEN)

/-- Proposition 6's exponent, `b₀ = L(DEN − U2)/DEN`. -/
noncomputable def b0 : ℝ := 2333 / 1000 * (((DEN - U2 : ℕ) : ℝ) / DEN)

theorem DEN_pos : (0 : ℝ) < DEN := SieveCert.DEN_pos'

theorem a0_pos : 0 < a0 := by
  have : (0 : ℝ) < V := by exact_mod_cast SieveCert.V_pos
  unfold a0
  have := DEN_pos
  positivity

theorem a0_b0 : a0 + b0 < 599 / 1000 * (2333 / 1000) := by
  have h : ((V + (DEN - U2) : ℕ) : ℝ) * 1000 < 599 * DEN := by
    exact_mod_cast (show (V + (DEN - U2)) * 1000 < 599 * DEN by decide)
  have hD := DEN_pos
  unfold a0 b0
  rw [← mul_add, ← add_div]
  rw [Nat.cast_add] at h
  have : ((V : ℝ) + ((DEN - U2 : ℕ) : ℝ)) / DEN < 599 / 1000 := by
    rw [div_lt_iff₀ hD]
    linarith
  nlinarith

theorem b0_gt : 515 / 1000 * (2333 / 1000) < b0 := by
  have h : (515 : ℝ) * DEN < 1000 * ((DEN - U2 : ℕ) : ℝ) := by
    exact_mod_cast (show 515 * DEN < 1000 * (DEN - U2) by decide)
  have hD := DEN_pos
  unfold b0
  have : (515 / 1000 : ℝ) < ((DEN - U2 : ℕ) : ℝ) / DEN := by
    rw [lt_div_iff₀ hD]
    linarith
  nlinarith

theorem b0_lt : b0 < 2333 / 1000 - 1 := by
  have h1 : (1000 : ℝ) * DEN < 2333 * U2 := by exact_mod_cast (show 1000 * DEN < 2333 * U2 by decide)
  have h2 : ((DEN - U2 : ℕ) : ℝ) = DEN - U2 := Nat.cast_sub SieveCert.U2_le_DEN
  have hD := DEN_pos
  unfold b0
  rw [h2, mul_div_assoc', div_lt_iff₀ hD]
  linarith

/-! ### The parameters at `x = q^L` -/

/-- The parameters of the decomposition at `x = q^L`. -/
noncomputable def parQ (q : ℕ) : Par where
  x := (q : ℝ) ^ (2333 / 1000 : ℝ)
  z₀ := ⌈(q : ℝ) ^ a0⌉₊
  ztop := Nat.sqrt (N2 q) + 1
  Xp := ⌊(q : ℝ) ^ b0⌋₊
  N₁ := N1 q
  N₂ := N2 q

theorem xpow (q : ℕ) (s : ℝ) : ((q : ℝ) ^ (2333 / 1000 : ℝ)) ^ s = (q : ℝ) ^ (2333 / 1000 * s) :=
  (Real.rpow_mul (Nat.cast_nonneg q) _ _).symm

theorem ev_rpow {c : ℝ} (hc : 0 < c) (B : ℝ) : ∀ᶠ q : ℕ in atTop, B ≤ (q : ℝ) ^ c :=
  ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B

/-- `q^a = q^b · q^{a − b}`. -/
theorem rpow_split {q : ℝ} (hq : 0 < q) (a b : ℝ) : q ^ a = q ^ b * q ^ (a - b) := by
  rw [← Real.rpow_add hq]
  congr 1
  ring

/-- If `q^{a−b} ≥ 3` and `q^b ≥ 1`, then `q^a ≥ q^b + 2`. -/
theorem rpow_gap {q : ℝ} (hq : 0 < q) {a b : ℝ} (h3 : 3 ≤ q ^ (a - b)) (h1 : 1 ≤ q ^ b) : q ^ b + 2 ≤ q ^ a := by
  rw [rpow_split hq a b]
  nlinarith

/-! ### `q` large -/

/-- The facts about `q` that the decomposition and its leaves use, as powers of `q`. -/
structure LargeQ (q : ℕ) : Prop where
  q3 : 3 ≤ q
  h14 : 2 ≤ (q : ℝ) ^ (2333 / 1000 * (14 / (DEN : ℝ)))
  hhalf : 4 ≤ (q : ℝ) ^ (2333 / 1000 / 2 : ℝ)
  hz : 3 ≤ (q : ℝ) ^ (2333 / 1000 / 2 - a0)
  hX : 3 ≤ (q : ℝ) ^ (2333 / 1000 - b0 * (3 / 2))
  hDEN : 3 ≤ (q : ℝ) ^ (2333 / 1000 / (DEN : ℝ))
  h401 : 3 ≤ (q : ℝ) ^ (2333 / 1000 * ((U1 : ℝ) / DEN) - 401 / 1000 * (2333 / 1000))
  h485 : 2 ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) - 2333 / 1000 * ((U2 : ℝ) / DEN))
  hb : 3 ≤ (q : ℝ) ^ (b0 - 2333 / 1000 / 2)

theorem largeQ_ev : ∀ᶠ q : ℕ in atTop, LargeQ q := by
  have hD := DEN_pos
  have e1 : (0 : ℝ) < 2333 / 1000 * (14 / (DEN : ℝ)) := by positivity
  have e2 : (0 : ℝ) < 2333 / 1000 / 2 := by norm_num
  have e3 : (0 : ℝ) < 2333 / 1000 / 2 - a0 := by
    have h : (2 : ℝ) * V < DEN := by exact_mod_cast (show 2 * V < DEN by decide)
    have : (V : ℝ) / DEN < 1 / 2 := by rw [div_lt_iff₀ hD]; linarith
    unfold a0
    nlinarith
  have e4 : (0 : ℝ) < 2333 / 1000 - b0 * (3 / 2) := by
    have h : (3 : ℝ) * ((DEN - U2 : ℕ) : ℝ) < 2 * DEN := by
      exact_mod_cast (show 3 * (DEN - U2) < 2 * DEN by decide)
    have : ((DEN - U2 : ℕ) : ℝ) / DEN < 2 / 3 := by rw [div_lt_iff₀ hD]; linarith
    unfold b0
    nlinarith
  have e5 : (0 : ℝ) < 2333 / 1000 / (DEN : ℝ) := by positivity
  have e6 : (0 : ℝ) < 2333 / 1000 * ((U1 : ℝ) / DEN) - 401 / 1000 * (2333 / 1000) := by
    have h : (401 : ℝ) * DEN < 1000 * U1 := by exact_mod_cast (show 401 * DEN < 1000 * U1 by decide)
    have : (401 / 1000 : ℝ) < (U1 : ℝ) / DEN := by rw [lt_div_iff₀ hD]; linarith
    nlinarith
  have e7 : (0 : ℝ) < 485 / 1000 * (2333 / 1000) - 2333 / 1000 * ((U2 : ℝ) / DEN) := by
    have h : (1000 : ℝ) * U2 < 485 * DEN := by exact_mod_cast (show 1000 * U2 < 485 * DEN by decide)
    have : (U2 : ℝ) / DEN < 485 / 1000 := by rw [div_lt_iff₀ hD]; linarith
    nlinarith
  have e8 : (0 : ℝ) < b0 - 2333 / 1000 / 2 := by
    have h : (DEN : ℝ) < 2 * ((DEN - U2 : ℕ) : ℝ) := by
      exact_mod_cast (show DEN < 2 * (DEN - U2) by decide)
    have : (1 / 2 : ℝ) < ((DEN - U2 : ℕ) : ℝ) / DEN := by rw [lt_div_iff₀ hD]; linarith
    unfold b0
    nlinarith
  filter_upwards [eventually_ge_atTop 3, ev_rpow e1 2, ev_rpow e2 4, ev_rpow e3 3, ev_rpow e4 3, ev_rpow e5 3,
    ev_rpow e6 3, ev_rpow e7 2, ev_rpow e8 3] with q h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem sqrt_x (q : ℕ) : Real.sqrt ((q : ℝ) ^ (2333 / 1000 : ℝ)) = (q : ℝ) ^ (2333 / 1000 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1
  ring

theorem N2_ge (q : ℕ) (hq : 1 ≤ q) : (q : ℝ) ^ (2333 / 1000 : ℝ) ≤ (N2 q : ℝ) := by
  have hy : (1 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.one_le_rpow (by exact_mod_cast hq) (by norm_num)
  have := Nat.sub_one_lt_floor (2 * (q : ℝ) ^ (2333 / 1000 : ℝ))
  unfold N2
  linarith

theorem N2_le (q : ℕ) : (N2 q : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) := Nat.floor_le (by positivity)

/-- **The decomposition's hypotheses hold for large `q`.** -/
theorem good_of_large {q : ℕ} (hL : LargeQ q) : (parQ q).Good := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hL.q3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hD := DEN_pos
  have hy1 : 1 < (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.one_lt_rpow (by linarith) (by norm_num)
  have hN₂y := N2_ge q (by have := hL.q3; omega)
  have hN₂le := N2_le q
  have hsy := sqrt_x q
  refine ⟨hy1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((q : ℝ) ^ (2333 / 1000 : ℝ)) ^ ((V : ℝ) / DEN) ≤ (⌈(q : ℝ) ^ a0⌉₊ : ℝ)
    rw [xpow]
    exact Nat.le_ceil _
  · show ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ) ≤ ((q : ℝ) ^ (2333 / 1000 : ℝ)) ^ (((V : ℝ) + SieveCert.n * H) / DEN)
    have hexp : ((V : ℝ) + SieveCert.n * H) / DEN = 1 / 2 + 14 / DEN := by
      have h : (2 : ℝ) * ((V : ℝ) + SieveCert.n * H) = DEN + 28 := by
        exact_mod_cast (show 2 * (V + SieveCert.n * H) = DEN + 28 by decide)
      field_simp
      linarith
    have h5 : ((q : ℝ) ^ (2333 / 1000 : ℝ)) ^ (((V : ℝ) + SieveCert.n * H) / DEN) =
        (q : ℝ) ^ (2333 / 1000 / 2 : ℝ) * (q : ℝ) ^ (2333 / 1000 * (14 / (DEN : ℝ))) := by
      rw [hexp, xpow, ← Real.rpow_add hq0]
      congr 1
      ring
    have h1 : (Nat.sqrt (N2 q) : ℝ) ≤ Real.sqrt (N2 q) := Real.nat_sqrt_le_real_sqrt
    have h2 : Real.sqrt (N2 q) ≤ Real.sqrt (2 * (q : ℝ) ^ (2333 / 1000 : ℝ)) := Real.sqrt_le_sqrt hN₂le
    have h3 : Real.sqrt (2 * (q : ℝ) ^ (2333 / 1000 : ℝ)) =
        Real.sqrt 2 * (q : ℝ) ^ (2333 / 1000 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), hsy]
    have h4 : Real.sqrt 2 < 3 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hh := hL.hhalf
    have h14 := hL.h14
    rw [h5]
    push_cast
    nlinarith
  · show ⌈(q : ℝ) ^ a0⌉₊ ≤ Nat.sqrt (N2 q) + 1
    have h1 : (⌈(q : ℝ) ^ a0⌉₊ : ℝ) < (q : ℝ) ^ a0 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 := rpow_gap hq0 hL.hz (Real.one_le_rpow hq1 a0_pos.le)
    have h3 : Real.sqrt (N2 q) ≤ Nat.sqrt (N2 q) + 1 := Real.real_sqrt_le_nat_sqrt_succ
    have h4 : (q : ℝ) ^ (2333 / 1000 / 2 : ℝ) ≤ Real.sqrt (N2 q) := by
      rw [← hsy]
      exact Real.sqrt_le_sqrt hN₂y
    have : (⌈(q : ℝ) ^ a0⌉₊ : ℝ) < ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this.le
  · show Nat.sqrt (N2 q) + 1 ≤ N2 q + 1
    exact Nat.add_le_add_right (Nat.sqrt_le_self _) 1
  · show (⌊(q : ℝ) ^ b0⌋₊ : ℝ) * Real.sqrt (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ (N1 q : ℝ)
    have hw : (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ (q : ℝ) ^ b0 := Nat.floor_le (by positivity)
    have hsq : Real.sqrt (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ (q : ℝ) ^ (b0 / 2) := by
      calc Real.sqrt (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ Real.sqrt ((q : ℝ) ^ b0) := Real.sqrt_le_sqrt hw
        _ = (q : ℝ) ^ (b0 / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]
          congr 1
          ring
    have hprod : (⌊(q : ℝ) ^ b0⌋₊ : ℝ) * Real.sqrt (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ (q : ℝ) ^ (b0 * (3 / 2)) := by
      calc (⌊(q : ℝ) ^ b0⌋₊ : ℝ) * Real.sqrt (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ (q : ℝ) ^ b0 * (q : ℝ) ^ (b0 / 2) :=
            mul_le_mul hw hsq (Real.sqrt_nonneg _) (by positivity)
        _ = (q : ℝ) ^ (b0 * (3 / 2)) := by
          rw [← Real.rpow_add hq0]
          congr 1
          ring
    have hgap := rpow_gap hq0 hL.hX (Real.one_le_rpow hq1 (by nlinarith [b0_gt]))
    have hN₁ : (q : ℝ) ^ (2333 / 1000 : ℝ) - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
    linarith
  · show (N2 q : ℝ) < ((q : ℝ) ^ (2333 / 1000 : ℝ)) ^ (((DEN : ℝ) + 1) / DEN)
    have h1 : ((q : ℝ) ^ (2333 / 1000 : ℝ)) ^ (((DEN : ℝ) + 1) / DEN) =
        (q : ℝ) ^ (2333 / 1000 : ℝ) * (q : ℝ) ^ (2333 / 1000 / (DEN : ℝ)) := by
      rw [xpow, ← Real.rpow_add hq0]
      congr 1
      field_simp
    have h2 := hL.hDEN
    have h3 : 0 < (q : ℝ) ^ (2333 / 1000 : ℝ) := by positivity
    rw [h1]
    nlinarith

/-! ### The families' atoms: thresholds, nonzero coefficients, lengths -/

theorem thrOK_append {q k : ℕ} {s₁ s₂ : List (Atom k)} (h₁ : ThrOK q s₁) (h₂ : ThrOK q s₂) :
    ThrOK q (s₁ ++ s₂) := by
  intro A hA
  rcases List.mem_append.1 hA with h | h
  · exact h₁ A h
  · exact h₂ A h

theorem thrOK_extS {q k' : ℕ} {spec : List (Atom (k' + 1))} {z : ℝ} (h : ThrOK q spec) (hz1 : 1 ≤ z)
    (hz2 : z ≤ (q : ℝ) ^ (2333 / 1000 + 1 : ℝ)) (hq : 1 ≤ q) : ThrOK q (extS z spec) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) := Real.one_le_rpow (by exact_mod_cast hq) (by norm_num)
  intro A hA
  simp only [extS, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with ⟨A', hA', rfl⟩ | rfl | rfl
  · rw [Atom.lift_thr]
    exact h A' hA'
  · exact ⟨le_rfl, hq1⟩
  · exact ⟨hz1, hz2⟩

theorem thrOK_cellA {q k : ℕ} (hq : 1 ≤ q) (t : Fin k) {c : ℕ} (hc : c < SieveCert.n) :
    ThrOK q (cellA t ((q : ℝ) ^ (2333 / 1000 : ℝ)) c) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hD := DEN_pos
  have hy1 : (1 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.one_le_rpow hq1 (by norm_num)
  have hyL : (q : ℝ) ^ (2333 / 1000 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  have hle : ((SieveCert.e c : ℝ) + H) / DEN ≤ 1 := by
    have h1 := SieveCert.e_add_H_le hc
    have h2 : (2 : ℝ) * ((V : ℝ) + SieveCert.n * H) = DEN + 28 := by
      exact_mod_cast (show 2 * (V + SieveCert.n * H) = DEN + 28 by decide)
    have h3 : (28 : ℝ) ≤ DEN := by exact_mod_cast (show 28 ≤ DEN by decide)
    rw [div_le_one hD]
    linarith
  have he0 : (0 : ℝ) ≤ (SieveCert.e c : ℝ) / DEN := by positivity
  have hle' : (SieveCert.e c : ℝ) / DEN ≤ 1 := le_trans (div_le_div_of_nonneg_right (by
    have : (0 : ℝ) ≤ H := Nat.cast_nonneg _
    linarith) hD.le) hle
  intro A hA
  simp only [cellA, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl
  · exact ⟨Real.one_le_rpow hy1 he0,
      le_trans (le_of_le_of_eq (Real.rpow_le_rpow_of_exponent_le hy1 hle') (Real.rpow_one _)) hyL⟩
  · exact ⟨Real.one_le_rpow hy1 (by positivity),
      le_trans (le_of_le_of_eq (Real.rpow_le_rpow_of_exponent_le hy1 hle) (Real.rpow_one _)) hyL⟩

theorem thrOK_single {q k : ℕ} {A : Atom k} (h1 : 1 ≤ A.thr) (h2 : A.thr ≤ (q : ℝ) ^ (2333 / 1000 + 1 : ℝ)) :
    ThrOK q [A] := by
  intro A' hA'
  rw [List.mem_singleton] at hA'
  subst hA'
  exact ⟨h1, h2⟩

/-- The thresholds `z₀`, `z_top` and `X'` lie in `[1, q^{L+1}]`. -/
theorem thr_bounds {q : ℕ} (hL : LargeQ q) :
    (1 ≤ ((parQ q).z₀ : ℝ) ∧ ((parQ q).z₀ : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 + 1 : ℝ)) ∧
    (1 ≤ ((parQ q).ztop : ℝ) ∧ ((parQ q).ztop : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 + 1 : ℝ)) ∧
    (1 ≤ ((parQ q).Xp : ℝ) ∧ ((parQ q).Xp : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 + 1 : ℝ)) := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hL.q3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hsplit : (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) = (q : ℝ) ^ (2333 / 1000 : ℝ) * q := by
    rw [Real.rpow_add hq0, Real.rpow_one]
  have hy1 : (1 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.one_le_rpow hq1 (by norm_num)
  have ha1 : (1 : ℝ) ≤ (q : ℝ) ^ a0 := Real.one_le_rpow hq1 a0_pos.le
  have hb1 : (1 : ℝ) ≤ (q : ℝ) ^ b0 := Real.one_le_rpow hq1 (by nlinarith [b0_gt])
  have haL : (q : ℝ) ^ a0 ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by
    have := hL.hz
    have e3 : (0 : ℝ) < 2333 / 1000 / 2 - a0 := by
      by_contra hc
      have : (q : ℝ) ^ (2333 / 1000 / 2 - a0) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
      linarith
    linarith)
  have hbL : (q : ℝ) ^ b0 ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by nlinarith [b0_lt])
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ha1.trans (Nat.le_ceil _)
  · have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (q : ℝ) ^ a0 by positivity)
    show (⌈(q : ℝ) ^ a0⌉₊ : ℝ) ≤ _
    rw [hsplit]
    nlinarith
  · show (1 : ℝ) ≤ ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ)
    push_cast
    have : (0 : ℝ) ≤ Nat.sqrt (N2 q) := Nat.cast_nonneg _
    linarith
  · show ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ) ≤ _
    have h1 : Nat.sqrt (N2 q) + 1 ≤ N2 q + 1 := Nat.add_le_add_right (Nat.sqrt_le_self _) 1
    have h2 : ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ) ≤ (N2 q : ℝ) + 1 := by exact_mod_cast h1
    have h3 := N2_le q
    rw [hsplit]
    nlinarith
  · show (1 : ℝ) ≤ (⌊(q : ℝ) ^ b0⌋₊ : ℝ)
    exact_mod_cast Nat.le_floor (by exact_mod_cast hb1)
  · show (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ _
    have := Nat.floor_le (show (0 : ℝ) ≤ (q : ℝ) ^ b0 by positivity)
    rw [hsplit]
    nlinarith

/-! ### The windows' thresholds for large `q` -/

/-- `x = q^L`. -/
noncomputable abbrev xq (q : ℕ) : ℝ := (q : ℝ) ^ (2333 / 1000 : ℝ)

/-- The lower window's ends `P₁ = ⌊x^{u₁}⌋`, `P₂ = ⌊x^{u₂}⌋`, and the upper window's `W₁ = ⌊x^{1−u₁}⌋`. -/
noncomputable abbrev P1 (q : ℕ) : ℕ := ⌊xq q ^ ((U1 : ℝ) / DEN)⌋₊
noncomputable abbrev P2 (q : ℕ) : ℕ := ⌊xq q ^ ((U2 : ℝ) / DEN)⌋₊
noncomputable abbrev W1 (q : ℕ) : ℕ := ⌊xq q ^ (((DEN - U1 : ℕ) : ℝ) / DEN)⌋₊

theorem Xp_eq (q : ℕ) : (parQ q).Xp = ⌊xq q ^ (((DEN - U2 : ℕ) : ℝ) / DEN)⌋₊ := by
  show ⌊(q : ℝ) ^ b0⌋₊ = _
  rw [xq, xpow]
  rfl

theorem P1_ok {q : ℕ} (hL : LargeQ q) : (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P1 q := by
  have hq0 : (0 : ℝ) < q := by have := hL.q3; positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  have h := rpow_gap hq0 hL.h401 (Real.one_le_rpow hq1 (by norm_num))
  have h2 := Nat.sub_one_lt_floor (xq q ^ ((U1 : ℝ) / DEN))
  rw [xq, xpow] at h2
  unfold P1
  rw [xq, xpow]
  linarith

theorem P2_ok {q : ℕ} (hL : LargeQ q) : (P2 q : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  have hD := DEN_pos
  have h : (1000 : ℝ) * U2 < 485 * DEN := by exact_mod_cast (show 1000 * U2 < 485 * DEN by decide)
  have hu : (U2 : ℝ) / DEN ≤ 485 / 1000 := by rw [div_le_iff₀ hD]; linarith
  unfold P2
  rw [xq, xpow]
  exact (Nat.floor_le (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hq1 (by nlinarith))

theorem W1_le {q : ℕ} (hL : LargeQ q) : W1 q ≤ N1 q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  have hy1 : (1 : ℝ) ≤ xq q := Real.one_le_rpow hq1 (by norm_num)
  have hD := DEN_pos
  have hle : ((DEN - U1 : ℕ) : ℝ) / DEN ≤ 1 := by
    rw [div_le_one hD]
    exact_mod_cast Nat.sub_le DEN U1
  unfold W1 N1
  exact Nat.floor_le_floor (le_of_le_of_eq (Real.rpow_le_rpow_of_exponent_le hy1 hle) (Real.rpow_one _))

theorem W1_pos {q : ℕ} (hL : LargeQ q) : 1 ≤ W1 q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  have hy1 : (1 : ℝ) ≤ xq q := Real.one_le_rpow hq1 (by norm_num)
  exact Nat.le_floor (by exact_mod_cast Real.one_le_rpow hy1 (by positivity))

theorem W1_div {q : ℕ} (hL : LargeQ q) : (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ ((N1 q / W1 q : ℕ) : ℝ) := by
  have hq0 : (0 : ℝ) < q := by have := hL.q3; positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  have hD := DEN_pos
  have hgap := rpow_gap hq0 hL.h401 (Real.one_le_rpow hq1 (by norm_num))
  set w := xq q ^ (((DEN - U1 : ℕ) : ℝ) / DEN) with hw
  have hw1 : (1 : ℝ) ≤ w := Real.one_le_rpow (Real.one_le_rpow hq1 (by norm_num)) (by positivity)
  have hW : (W1 q : ℝ) ≤ w := Nat.floor_le (by positivity)
  have hW0 : (0 : ℝ) < W1 q := by exact_mod_cast W1_pos hL
  have hyw : xq q / w = (q : ℝ) ^ (2333 / 1000 * ((U1 : ℝ) / DEN)) := by
    rw [hw, xq, xpow, ← Real.rpow_sub hq0]
    congr 1
    rw [Nat.cast_sub SieveCert.U1_le_DEN]
    field_simp
    ring
  -- `N₁/W₁ ≥ (x − 1)/w ≥ x/w − 1`
  have hN₁ : xq q - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
  have hdiv : (N1 q : ℝ) / W1 q < ((N1 q / W1 q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hW0]
    have h := Nat.lt_div_mul_add (a := N1 q) (show 0 < W1 q from W1_pos hL)
    have : ((N1 q : ℕ) : ℝ) < ((N1 q / W1 q * W1 q + W1 q : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  have h1 : xq q / w - 1 ≤ (N1 q : ℝ) / W1 q := by
    have : (xq q - 1) / w ≤ (N1 q : ℝ) / W1 q := by
      calc (xq q - 1) / w ≤ (N1 q : ℝ) / w := div_le_div_of_nonneg_right hN₁.le (by linarith)
        _ ≤ (N1 q : ℝ) / W1 q := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hW0 hW
    have h2 : xq q / w - 1 ≤ (xq q - 1) / w := by
      rw [sub_div]
      have : 1 / w ≤ 1 := by rw [div_le_one (by linarith)]; exact hw1
      linarith
    linarith
  rw [hyw] at h1
  linarith

theorem W0_div {q : ℕ} (hL : LargeQ q) :
    ((N2 q / ((parQ q).Xp + 1) : ℕ) : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) := by
  have hq0 : (0 : ℝ) < q := by have := hL.q3; positivity
  have h1 : ((N2 q / ((parQ q).Xp + 1) : ℕ) : ℝ) ≤ (N2 q : ℝ) / (((parQ q).Xp + 1 : ℕ) : ℝ) := Nat.cast_div_le
  have h2 : (q : ℝ) ^ b0 < (((parQ q).Xp + 1 : ℕ) : ℝ) := by
    show (q : ℝ) ^ b0 < ((⌊(q : ℝ) ^ b0⌋₊ + 1 : ℕ) : ℝ)
    push_cast
    exact Nat.lt_floor_add_one _
  have hb0 : (0 : ℝ) < (q : ℝ) ^ b0 := by positivity
  have h3 : (N2 q : ℝ) / (((parQ q).Xp + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) / (q : ℝ) ^ b0 :=
    div_le_div₀ (by positivity) (N2_le q) hb0 h2.le
  have h4 : 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) / (q : ℝ) ^ b0 =
      2 * (q : ℝ) ^ (2333 / 1000 * ((U2 : ℝ) / DEN)) := by
    rw [mul_div_assoc, ← Real.rpow_sub hq0]
    congr 2
    unfold b0
    rw [Nat.cast_sub SieveCert.U2_le_DEN]
    have := DEN_pos
    field_simp
    ring
  have h5 := hL.h485
  have h6 : 2 * (q : ℝ) ^ (2333 / 1000 * ((U2 : ℝ) / DEN)) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) := by
    rw [rpow_split hq0 (485 / 1000 * (2333 / 1000)) (2333 / 1000 * ((U2 : ℝ) / DEN))]
    have : (0 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 * ((U2 : ℝ) / DEN)) := by positivity
    nlinarith
  linarith

theorem ztop_le_Xp {q : ℕ} (hL : LargeQ q) : (parQ q).ztop ≤ (parQ q).Xp + 1 := by
  have hq0 : (0 : ℝ) < q := by have := hL.q3; positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  show Nat.sqrt (N2 q) + 1 ≤ ⌊(q : ℝ) ^ b0⌋₊ + 1
  refine Nat.add_le_add_right (Nat.le_floor ?_) 1
  have h1 : (Nat.sqrt (N2 q) : ℝ) ≤ Real.sqrt (N2 q) := Real.nat_sqrt_le_real_sqrt
  have h2 : Real.sqrt (N2 q) ≤ Real.sqrt (2 * (q : ℝ) ^ (2333 / 1000 : ℝ)) := Real.sqrt_le_sqrt (N2_le q)
  have h3 : Real.sqrt (2 * (q : ℝ) ^ (2333 / 1000 : ℝ)) = Real.sqrt 2 * (q : ℝ) ^ (2333 / 1000 / 2 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), sqrt_x]
  have h4 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h5 : (q : ℝ) ^ b0 = (q : ℝ) ^ (2333 / 1000 / 2 : ℝ) * (q : ℝ) ^ (b0 - 2333 / 1000 / 2) :=
    rpow_split hq0 _ _
  have h6 := hL.hb
  have h7 : (0 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 / 2 : ℝ) := by positivity
  nlinarith

/-! ### Each family of the tree: thresholds, coefficients, length -/

section Families

variable {q : ℕ} (hL : LargeQ q)
include hL

theorem q1 : 1 ≤ q := by have := hL.q3; omega

theorem thrOK_S1 : ThrOK q (parQ q).S1 := by
  obtain ⟨⟨hz1, hz2⟩, ⟨ht1, ht2⟩, -⟩ := thr_bounds hL
  intro A hA
  simp only [Par.S1, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl
  · exact ⟨hz1, hz2⟩
  · exact ⟨ht1, ht2⟩

theorem thrOK_S1c {i : ℕ} (hi : i < SieveCert.n) : ThrOK q ((parQ q).S1c i) :=
  thrOK_append (thrOK_S1 hL) (thrOK_cellA (q1 hL) 0 hi)

theorem thrOK_S2 {i : ℕ} (hi : i < SieveCert.n) : ThrOK q ((parQ q).S2 i) :=
  thrOK_extS (thrOK_S1c hL hi) (thr_bounds hL).1.1 (thr_bounds hL).1.2 (q1 hL)

theorem thrOK_S2c {i j : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) : ThrOK q ((parQ q).S2c i j) :=
  thrOK_append (thrOK_S2 hL hi) (thrOK_cellA (q1 hL) 1 hj)

theorem thrOK_S2le {i j : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) : ThrOK q ((parQ q).S2le i j) :=
  thrOK_append (thrOK_S2c hL hi hj) (thrOK_single (thr_bounds hL).2.2.1 (thr_bounds hL).2.2.2)

theorem thrOK_S2gt {i j : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) : ThrOK q ((parQ q).S2gt i j) :=
  thrOK_append (thrOK_S2c hL hi hj) (thrOK_single (thr_bounds hL).2.2.1 (thr_bounds hL).2.2.2)

theorem thrOK_S3 {i j : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) : ThrOK q ((parQ q).S3 i j) :=
  thrOK_extS (thrOK_S2le hL hi hj) (thr_bounds hL).1.1 (thr_bounds hL).1.2 (q1 hL)

theorem thrOK_S3c {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n) :
    ThrOK q ((parQ q).S3c i j k) :=
  thrOK_append (thrOK_S3 hL hi hj) (thrOK_cellA (q1 hL) 2 hk)

theorem thrOK_S3le {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n) :
    ThrOK q ((parQ q).S3le i j k) :=
  thrOK_append (thrOK_S3c hL hi hj hk) (thrOK_single (thr_bounds hL).2.2.1 (thr_bounds hL).2.2.2)

theorem thrOK_S3gt {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n) :
    ThrOK q ((parQ q).S3gt i j k) :=
  thrOK_append (thrOK_S3c hL hi hj hk) (thrOK_single (thr_bounds hL).2.2.1 (thr_bounds hL).2.2.2)

theorem thrOK_S4 {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n) :
    ThrOK q ((parQ q).S4 i j k) :=
  thrOK_extS (thrOK_S3le hL hi hj hk) (thr_bounds hL).1.1 (thr_bounds hL).1.2 (q1 hL)

theorem thrOK_S4c {i j k l : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n)
    (hl : l < SieveCert.n) : ThrOK q ((parQ q).S4c i j k l) :=
  thrOK_append (thrOK_S4 hL hi hj hk) (thrOK_cellA (q1 hL) 3 hl)

end Families

theorem nz_lift {k : ℕ} (A : Atom k) (h : NZ A) : NZ A.lift := by
  cases A with
  | ge t b => trivial
  | lt t b => trivial
  | ltVar s t => exact fun h' => (show s ≠ t from h) (Fin.castSucc_injective _ h')
  | prodLe T b => exact (Finset.map_nonempty).2 (show T.Nonempty from h)
  | prodGt T b => exact (Finset.map_nonempty).2 (show T.Nonempty from h)

theorem nz_append {k : ℕ} {s₁ s₂ : List (Atom k)} (h₁ : ∀ A ∈ s₁, NZ A) (h₂ : ∀ A ∈ s₂, NZ A) :
    ∀ A ∈ s₁ ++ s₂, NZ A := by
  intro A hA
  rcases List.mem_append.1 hA with h | h
  · exact h₁ A h
  · exact h₂ A h

theorem nz_extS {k' : ℕ} {spec : List (Atom (k' + 1))} {z : ℝ} (h : ∀ A ∈ spec, NZ A) :
    ∀ A ∈ extS z spec, NZ A := by
  intro A hA
  simp only [extS, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with ⟨A', hA', rfl⟩ | rfl | rfl
  · exact nz_lift A' (h A' hA')
  · exact (Fin.castSucc_lt_last _).ne
  · trivial

theorem nz_cellA {k : ℕ} (t : Fin k) (x : ℝ) (c : ℕ) : ∀ A ∈ cellA t x c, NZ A := by
  intro A hA
  simp only [cellA, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl <;> trivial

theorem nz_prodLe {k' : ℕ} (b : ℝ) : ∀ A ∈ [Atom.prodLe (Finset.univ : Finset (Fin (k' + 1))) b], NZ A := by
  intro A hA
  rw [List.mem_singleton] at hA
  subst hA
  exact Finset.univ_nonempty

theorem nz_S1c (q i : ℕ) : ∀ A ∈ (parQ q).S1c i, NZ A :=
  nz_append (by intro A hA; simp only [Par.S1, List.mem_cons, List.mem_nil_iff, or_false] at hA
                rcases hA with rfl | rfl <;> trivial) (nz_cellA _ _ _)

theorem nz_S2le (q i j : ℕ) : ∀ A ∈ (parQ q).S2le i j, NZ A :=
  nz_append (nz_append (nz_extS (nz_S1c q i)) (nz_cellA _ _ _)) (nz_prodLe _)

theorem nz_S3le (q i j k : ℕ) : ∀ A ∈ (parQ q).S3le i j k, NZ A :=
  nz_append (nz_append (nz_extS (nz_S2le q i j)) (nz_cellA _ _ _)) (nz_prodLe _)

theorem len_S1c (q i : ℕ) : ((parQ q).S1c i).length ≤ 18 := by
  simp [Par.S1c, Par.S1, cellA]
theorem len_S2c (q i j : ℕ) : ((parQ q).S2c i j).length ≤ 18 := by
  simp [Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
theorem len_S2le (q i j : ℕ) : ((parQ q).S2le i j).length ≤ 18 := by
  simp [Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
theorem len_S2gt (q i j : ℕ) : ((parQ q).S2gt i j).length ≤ 18 := by
  simp [Par.S2gt, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
theorem len_S3c (q i j k : ℕ) : ((parQ q).S3c i j k).length ≤ 18 := by
  simp [Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
theorem len_S3le (q i j k : ℕ) : ((parQ q).S3le i j k).length ≤ 18 := by
  simp [Par.S3le, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
theorem len_S3gt (q i j k : ℕ) : ((parQ q).S3gt i j k).length ≤ 18 := by
  simp [Par.S3gt, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
theorem len_S4c (q i j k l : ℕ) : ((parQ q).S4c i j k l).length ≤ 18 := by
  simp [Par.S4c, Par.S4, Par.S3le, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]

/-! ### The estimates at one `q` -/

/-- The lower window's estimate at `q`, with error `E`. -/
def TLat (q : ℕ) (a : ZMod q) (k' : ℕ) (E : ℝ) : Prop :=
  ∀ (spec : List (Atom (k' + 1))) (S : Finset (Fin (k' + 1))) (P₁ P₂ : ℕ), spec.length ≤ 18 → ThrOK q spec →
    (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
    (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      StrictAnti rt ∧ (∀ i, (q : ℝ) ^ a0 ≤ rt i) ∧ P₁ < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ P₂) →
    |famI (gA q a) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) -
        famI (gB q) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec)| ≤ E

/-- The upper window's estimate at `q`, with error `E`. -/
def TUat (q : ℕ) (a : ZMod q) (k' : ℕ) (E : ℝ) : Prop :=
  ∀ (spec : List (Atom (k' + 1))) (W₀ W₁ : ℕ), spec.length ≤ 18 → ThrOK q spec →
    (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      StrictAnti rt ∧ (∀ i, (q : ℝ) ^ a0 ≤ rt i) ∧ W₀ < ∏ i, rt i ∧ ∏ i, rt i ≤ W₁) →
    W₁ ≤ N1 q → (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ ((N1 q / W₁ : ℕ) : ℝ) →
    ((N2 q / (W₀ + 1) : ℕ) : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
    |famI (gA q a) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) -
        famI (gB q) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec)| ≤ E

/-- Proposition 6's estimate at `q`, with error `E`. -/
def P6at (q : ℕ) (a : ZMod q) (j : ℕ) (E : ℝ) : Prop :=
  ∀ (spec : List (Atom j)), spec.length ≤ 18 → ThrOK q spec → (∀ A ∈ spec, NZ A) →
    (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      (∀ i, ⌈(q : ℝ) ^ a0⌉₊ ≤ rt i) ∧ ∏ i, rt i ≤ ⌊(q : ℝ) ^ b0⌋₊) →
    |famJ (gA q a) (N1 q) (N2 q) ⌈(q : ℝ) ^ a0⌉₊ (famSet j (N2 q) spec) -
        famJ (gB q) (N1 q) (N2 q) ⌈(q : ℝ) ^ a0⌉₊ (famSet j (N2 q) spec)| ≤ E

theorem TLat.mono {q : ℕ} {a : ZMod q} {k' : ℕ} {E E' : ℝ} (h : TLat q a k' E) (hE : E ≤ E') : TLat q a k' E' :=
  fun spec S P₁ P₂ h1 h2 h3 h4 h5 => (h spec S P₁ P₂ h1 h2 h3 h4 h5).trans hE

theorem TUat.mono {q : ℕ} {a : ZMod q} {k' : ℕ} {E E' : ℝ} (h : TUat q a k' E) (hE : E ≤ E') : TUat q a k' E' :=
  fun spec W₀ W₁ h1 h2 h3 h4 h5 h6 => (h spec W₀ W₁ h1 h2 h3 h4 h5 h6).trans hE

theorem P6at.mono {q : ℕ} {a : ZMod q} {j : ℕ} {E E' : ℝ} (h : P6at q a j E) (hE : E ≤ E') : P6at q a j E' :=
  fun spec h1 h2 h3 h4 => (h spec h1 h2 h3 h4).trans hE

/-- **A box surely evaluable** is estimated by the lower window, or by the upper window when its set is all the
primes; a proper set in the upper window is impossible below `X'`. -/
theorem box_leaf {q : ℕ} (hL : LargeQ q) {a : ZMod q} {k' : ℕ} {E : ℝ} (hE : 0 ≤ E) (hTL : TLat q a k' E)
    (hTU : TUat q a k' E) {spec : List (Atom (k' + 1))} (hlen : spec.length ≤ 18) (hthr : ThrOK q spec)
    (c : Fin (k' + 1) → ℕ)
    (hsem : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      StrictAnti rt ∧ (∀ i, (parQ q).z₀ ≤ rt i) ∧ (∀ t, InC (xq q) (c t) (rt t)) ∧
        ∏ t ∈ Finset.univ.erase (Fin.last k'), rt t ≤ (parQ q).Xp)
    (hsE : surelyEval (List.ofFn fun t => cell (c t)) = true) :
    |famI (gA q a) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) -
        famI (gB q) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec)| ≤ E := by
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by norm_num)
  have ha0 : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (parQ q).z₀ ≤ rt i) → ∀ i, (q : ℝ) ^ a0 ≤ rt i :=
    fun rt h i => (Nat.le_ceil _).trans (by exact_mod_cast h i)
  obtain ⟨T, hT⟩ := exists_inside _ hsE
  simp only [inside, cell, Bool.or_eq_true, Bool.and_eq_true] at hT
  rcases hT with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;> replace hlo := of_decide_eq_true hlo <;>
    replace hhi := of_decide_eq_true hhi
  · refine hTL spec T (P1 q) (P2 q) hlen hthr (P1_ok hL) (P2_ok hL) fun rt hp hs => ?_
    obtain ⟨hsa, hz₀, hc, -⟩ := hsem rt hp hs
    exact ⟨hsa, ha0 rt hz₀, window_lo hq1 hc hlo, window_hi hq1 hc hhi⟩
  · by_cases hTu : T = Finset.univ
    · subst hTu
      refine hTU spec (parQ q).Xp (W1 q) hlen hthr (fun rt hp hs => ?_) (W1_le hL) (W1_div hL) (W0_div hL)
      obtain ⟨hsa, hz₀, hc, -⟩ := hsem rt hp hs
      refine ⟨hsa, ha0 rt hz₀, ?_, window_hi hq1 hc hhi⟩
      rw [Xp_eq]
      exact window_lo hq1 hc hlo
    · have hempty : ∀ rt ∈ famSet (k' + 1) (N2 q) spec, False := by
        intro rt hrt
        rw [mem_famSet] at hrt
        obtain ⟨hsa, -, hc, hX⟩ := hsem rt (fun i => (hrt.1 i).2) hrt.2
        have h1 := window_lo hq1 hc hlo
        have h2 := prod_proper_le hsa (fun t => (hrt.1 t).2.one_lt.le) hTu
        rw [← Xp_eq] at h1
        omega
      rw [famI_eq_zero _ _ _ _ (fun rt hrt => (hempty rt hrt).elim),
        famI_eq_zero _ _ _ _ (fun rt hrt => (hempty rt hrt).elim), sub_zero, abs_zero]
      exact hE

/-! ### The leaves -/

theorem mem_famSet_sum {k : ℕ} {spec : List (Atom k)} {rt : Fin k → ℕ} (hp : ∀ i, (rt i).Prime)
    (hs : ∀ A ∈ spec, A.sem rt) : rt ∈ famSet k (∑ i, rt i) spec :=
  mem_famSet.2 ⟨fun i => ⟨Finset.single_le_sum (fun j _ => Nat.zero_le (rt j)) (Finset.mem_univ i), hp i⟩, hs⟩

theorem prod_erase_last {k' : ℕ} (rt : Fin (k' + 1) → ℕ) (h : ∀ i, 0 < rt i) :
    ∏ t ∈ Finset.univ.erase (Fin.last k'), rt t = ∏ i : Fin k', rt i.castSucc := by
  have h1 := Finset.prod_erase_mul (Finset.univ : Finset (Fin (k' + 1))) rt (Finset.mem_univ (Fin.last k'))
  rw [Fin.prod_univ_castSucc] at h1
  exact Nat.eq_of_mul_eq_mul_right (h _) h1

theorem J0_eq (P : Par) (g : ℕ → ℝ) : P.J0 g = famJ g P.N₁ P.N₂ P.z₀ (famSet 0 P.N₂ []) := by
  have h : famSet 0 P.N₂ [] = {fun i => Fin.elim0 i} := by
    ext x
    simp only [mem_famSet, IsEmpty.forall_iff, true_and, List.not_mem_nil, implies_true, Finset.mem_singleton]
    exact ⟨fun _ => funext fun i => Fin.elim0 i, fun _ => trivial⟩
  rw [h, famJ, Finset.sum_singleton]
  unfold Par.J0
  simp

section Leaves

variable {q : ℕ} (hL : LargeQ q) {a : ZMod q} {E : ℝ}
include hL

omit hL in
theorem ha0_of {k : ℕ} {rt : Fin k → ℕ} (h : ∀ i, (parQ q).z₀ ≤ rt i) : ∀ i, (q : ℝ) ^ a0 ≤ rt i :=
  fun i => (Nat.le_ceil _).trans (by exact_mod_cast h i)

theorem lf_j0 (hP : P6at q a 0 E) : |(parQ q).J0 (gA q a) - (parQ q).J0 (gB q)| ≤ E := by
  rw [J0_eq, J0_eq]
  refine hP [] (by simp) (fun A hA => absurd hA List.not_mem_nil) (fun A hA => absurd hA List.not_mem_nil)
    fun rt _ _ => ⟨fun i => Fin.elim0 i, ?_⟩
  rw [Finset.univ_eq_empty, Finset.prod_empty]
  exact (thr_bounds hL).2.2.1 |> fun h => by exact_mod_cast h

theorem lf_e1 (hT : TLat q a 0 E) {i : ℕ} (hi : i < SieveCert.n) (hW : Par.inW i) :
    |(parQ q).I (gA q a) ((parQ q).S1c i) - (parQ q).I (gB q) ((parQ q).S1c i)| ≤ E := by
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by norm_num)
  refine hT _ Finset.univ (P1 q) (P2 q) (len_S1c q i) (thrOK_S1c hL hi) (P1_ok hL) (P2_ok hL) fun rt hp hs => ?_
  have hrt := mem_famSet_sum hp hs
  have hc := (parQ q).chain_S1c i rt hrt
  have hC : InC (xq q) i (rt 0) := inC_of_mem hrt (t := 0) fun A hA => List.mem_append_right _ hA
  have hC' : ∀ t, InC (xq q) ((fun _ : Fin 1 => i) t) (rt t) := fun t => by rw [Fin.fin_one_eq_zero t]; exact hC
  refine ⟨hc.1, ha0_of hc.2.1, window_lo hq1 hC' ?_, window_hi hq1 hC' ?_⟩
  · simpa using hW.1
  · simpa using hW.2

theorem lf_p1 (hP : P6at q a 1 E) {i : ℕ} (hi : i < SieveCert.n) :
    |(parQ q).J (gA q a) ((parQ q).S1c i) - (parQ q).J (gB q) ((parQ q).S1c i)| ≤ E := by
  refine hP _ (len_S1c q i) (thrOK_S1c hL hi) (nz_S1c q i) fun rt hp hs => ?_
  have hc := (parQ q).chain_S1c i rt (mem_famSet_sum hp hs)
  refine ⟨hc.2.1, ?_⟩
  rw [Fin.prod_univ_one]
  have := hc.2.2 0
  have := ztop_le_Xp hL
  show rt 0 ≤ (parQ q).Xp
  omega

theorem lf_e2 (hT : TUat q a 1 E) {i j : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hd : dec i j = true) :
    |(parQ q).I (gA q a) ((parQ q).S2gt i j) - (parQ q).I (gB q) ((parQ q).S2gt i j)| ≤ E := by
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by norm_num)
  have hall := SieveCert.allowed_of_dec hd
  simp only [allowed, Bool.and_eq_true, decide_eq_true_eq] at hall
  refine hT _ (parQ q).Xp (W1 q) (len_S2gt q i j) (thrOK_S2gt hL hi hj) (fun rt hp hs => ?_) (W1_le hL)
    (W1_div hL) (W0_div hL)
  have hrt := mem_famSet_sum hp hs
  obtain ⟨hc, hCi, hCj⟩ := (parQ q).facts_S2c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
  have hC : ∀ t, InC (xq q) (![i, j] t) (rt t) := by
    intro t
    fin_cases t
    · exact hCi
    · exact hCj
  have hgt : ((parQ q).Xp : ℝ) < ∏ t ∈ Finset.univ, (rt t : ℝ) :=
    sem_of_mem hrt (A := Atom.prodGt Finset.univ (parQ q).Xp) (List.mem_append_right _ (List.mem_singleton_self _))
  refine ⟨hc.1, ha0_of hc.2.1, by exact_mod_cast hgt, ?_⟩
  have := window_hi hq1 hC (T := Finset.univ) (B := DEN - U1) (by simpa [Fin.sum_univ_two, SieveCert.lim] using hall.1)
  simpa using this

theorem lf_p2 (hP : P6at q a 2 E) {i j : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) :
    |(parQ q).J (gA q a) ((parQ q).S2le i j) - (parQ q).J (gB q) ((parQ q).S2le i j)| ≤ E := by
  refine hP _ (len_S2le q i j) (thrOK_S2le hL hi hj) (nz_S2le q i j) fun rt hp hs => ?_
  have hrt := mem_famSet_sum hp hs
  obtain ⟨hc, -, -, hX⟩ := (parQ q).facts_S2le hrt
  refine ⟨hc.2.1, ?_⟩
  rw [Fin.prod_univ_two]
  exact_mod_cast hX

theorem lf_e2' (hE : 0 ≤ E) (hTL : TLat q a 1 E) (hTU : TUat q a 1 E) {i j : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hs : Par.sE2 i j = true) :
    |(parQ q).I (gA q a) ((parQ q).S2c i j) - (parQ q).I (gB q) ((parQ q).S2c i j)| ≤ E := by
  refine box_leaf hL hE hTL hTU (len_S2c q i j) (thrOK_S2c hL hi hj) ![i, j] (fun rt hp hs' => ?_) ?_
  · obtain ⟨hc, hCi, hCj⟩ := (parQ q).facts_S2c (mem_famSet_sum hp hs')
    refine ⟨hc.1, hc.2.1, fun t => ?_, ?_⟩
    · fin_cases t
      · exact hCi
      · exact hCj
    · rw [prod_erase_last rt fun t => (hp t).pos, Fin.prod_univ_one]
      have := hc.2.2 0
      have := ztop_le_Xp hL
      show rt 0 ≤ (parQ q).Xp
      omega
  · simpa [List.ofFn_succ, Par.sE2] using hs

theorem lf_e3 (hT : TUat q a 2 E) {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hd : dec i j = true) (hkk : inKK i j k = true) (hn3 : ne3 i j k = true) :
    |(parQ q).I (gA q a) ((parQ q).S3gt i j k) - (parQ q).I (gB q) ((parQ q).S3gt i j k)| ≤ E := by
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by norm_num)
  have hall := SieveCert.allowed_of_dec hd
  simp only [allowed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hall
  have hrow := hall.2 k hk
  simp only [hkk, hn3, Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hrow
  refine hT _ (parQ q).Xp (W1 q) (len_S3gt q i j k) (thrOK_S3gt hL hi hj hk) (fun rt hp hs => ?_) (W1_le hL)
    (W1_div hL) (W0_div hL)
  have hrt := mem_famSet_sum hp hs
  obtain ⟨hc, hCi, hCj, hCk, -⟩ := (parQ q).facts_S3c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
  have hC : ∀ t, InC (xq q) (![i, j, k] t) (rt t) := by
    intro t
    fin_cases t
    · exact hCi
    · exact hCj
    · exact hCk
  have hgt : ((parQ q).Xp : ℝ) < ∏ t ∈ Finset.univ, (rt t : ℝ) :=
    sem_of_mem hrt (A := Atom.prodGt Finset.univ (parQ q).Xp) (List.mem_append_right _ (List.mem_singleton_self _))
  refine ⟨hc.1, ha0_of hc.2.1, by exact_mod_cast hgt, ?_⟩
  have := window_hi hq1 hC (T := Finset.univ) (B := DEN - U1) (by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    simpa [SieveCert.lim] using hrow)
  simpa using this

theorem lf_p3 (hP : P6at q a 3 E) {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) :
    |(parQ q).J (gA q a) ((parQ q).S3le i j k) - (parQ q).J (gB q) ((parQ q).S3le i j k)| ≤ E := by
  refine hP _ (len_S3le q i j k) (thrOK_S3le hL hi hj hk) (nz_S3le q i j k) fun rt hp hs => ?_
  have hrt := mem_famSet_sum hp hs
  obtain ⟨hc, -, -, -, -, hX⟩ := (parQ q).facts_S3le hrt
  refine ⟨hc.2.1, ?_⟩
  rw [Fin.prod_univ_three]
  exact_mod_cast hX

theorem lf_e3' (hE : 0 ≤ E) (hTL : TLat q a 2 E) (hTU : TUat q a 2 E) {i j k : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hk : k < SieveCert.n) (hn3 : ne3 i j k = false) :
    |(parQ q).I (gA q a) ((parQ q).S3c i j k) - (parQ q).I (gB q) ((parQ q).S3c i j k)| ≤ E := by
  refine box_leaf hL hE hTL hTU (len_S3c q i j k) (thrOK_S3c hL hi hj hk) ![i, j, k] (fun rt hp hs' => ?_) ?_
  · obtain ⟨hc, hCi, hCj, hCk, hX⟩ := (parQ q).facts_S3c (mem_famSet_sum hp hs')
    refine ⟨hc.1, hc.2.1, fun t => ?_, ?_⟩
    · fin_cases t
      · exact hCi
      · exact hCj
      · exact hCk
    · rw [prod_erase_last rt fun t => (hp t).pos, Fin.prod_univ_two]
      exact_mod_cast hX
  · simpa [List.ofFn_succ, ne3] using hn3

theorem lf_e4 (hE : 0 ≤ E) (hTL : TLat q a 3 E) (hTU : TUat q a 3 E) {i j k l : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hs : Par.sE4 i j k l = true) :
    |(parQ q).I (gA q a) ((parQ q).S4c i j k l) - (parQ q).I (gB q) ((parQ q).S4c i j k l)| ≤ E := by
  refine box_leaf hL hE hTL hTU (len_S4c q i j k l) (thrOK_S4c hL hi hj hk hl) ![i, j, k, l]
    (fun rt hp hs' => ?_) ?_
  · obtain ⟨hc, hCi, hCj, hCk, hCl, -, hX⟩ := (parQ q).facts_S4c (mem_famSet_sum hp hs')
    refine ⟨hc.1, hc.2.1, fun t => ?_, ?_⟩
    · fin_cases t
      · exact hCi
      · exact hCj
      · exact hCk
      · exact hCl
    · rw [prod_erase_last rt fun t => (hp t).pos, Fin.prod_univ_three]
      exact_mod_cast hX
  · simpa [List.ofFn_succ, Par.sE4] using hs

end Leaves

/-- The leaves' error at `q`: `ηq^L/(φ(q) log q) + q^{L−δ}/φ(q)`. -/
noncomputable def Err (η δ : ℝ) (q : ℕ) : ℝ :=
  η * (q : ℝ) ^ (2333 / 1000 : ℝ) / (q.totient * Real.log q) + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ)

theorem Err_nonneg {η : ℝ} (hη : 0 < η) (δ : ℝ) (q : ℕ) (hq : 1 ≤ q) : 0 ≤ Err η δ q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  unfold Err
  positivity

theorem Err_ge {η : ℝ} (hη : 0 < η) {δ d : ℝ} (hδd : δ ≤ d) (q : ℕ) (hq : 1 ≤ q) :
    (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - d : ℝ) ≤ Err η δ q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  have h1 : (q : ℝ) ^ (2333 / 1000 - d : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 - δ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have h2 : 0 ≤ η * (q : ℝ) ^ (2333 / 1000 : ℝ) / (q.totient * Real.log q) := by positivity
  unfold Err
  have : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  nlinarith

theorem Err_ge' {η : ℝ} {δ d : ℝ} (hδd : δ ≤ d) (q : ℕ) (hq : 1 ≤ q) :
    η * (q : ℝ) ^ (2333 / 1000 : ℝ) / (q.totient * Real.log q) + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - d : ℝ)
      ≤ Err η δ q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) ^ (2333 / 1000 - d : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 - δ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  unfold Err
  have : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  nlinarith

/-- **The leaves, for large `q`.** For `η > 0` there are `δ > 0` and `q₀` such that for `q ≥ q₀` and `a` a unit
mod `q`, `q` is large and every leaf of the tree at `x = q^L` is within `Err η δ q`. -/
theorem leaves_ev {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      LargeQ q ∧ (parQ q).Leaves (gA q a) (gB q) (Err η δ q) := by
  obtain ⟨d1, hd1, q1, h1⟩ := TL_spec a0 a0_pos 0
  obtain ⟨d2, hd2, q2, h2⟩ := TL_spec a0 a0_pos 1
  obtain ⟨d3, hd3, q3, h3⟩ := TL_spec a0 a0_pos 2
  obtain ⟨d4, hd4, q4, h4⟩ := TL_spec a0 a0_pos 3
  obtain ⟨d5, hd5, q5, h5⟩ := TU_spec a0 a0_pos 1
  obtain ⟨d6, hd6, q6, h6⟩ := TU_spec a0 a0_pos 2
  obtain ⟨d7, hd7, q7, h7⟩ := TU_spec a0 a0_pos 3
  obtain ⟨d8, hd8, q8, h8⟩ := P6_spec a0 b0 a0_pos a0_b0 b0_gt b0_lt 0 hη
  obtain ⟨d9, hd9, q9, h9⟩ := P6_spec a0 b0 a0_pos a0_b0 b0_gt b0_lt 1 hη
  obtain ⟨d10, hd10, q10, h10⟩ := P6_spec a0 b0 a0_pos a0_b0 b0_gt b0_lt 2 hη
  obtain ⟨d11, hd11, q11, h11⟩ := P6_spec a0 b0 a0_pos a0_b0 b0_gt b0_lt 3 hη
  obtain ⟨qL, hqL⟩ := Filter.eventually_atTop.1 largeQ_ev
  set δ := min d1 (min d2 (min d3 (min d4 (min d5 (min d6 (min d7 (min d8 (min d9 (min d10 d11))))))))) with hδ
  have hδ0 : 0 < δ := by
    simp only [hδ, lt_min_iff]
    exact ⟨hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11⟩
  have hle : ∀ d ∈ [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], δ ≤ d := by
    intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hδ, min_le_iff]
  refine ⟨δ, hδ0, q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + qL, fun q _ hq a ha => ?_⟩
  have hLq : LargeQ q := hqL q (by omega)
  have hq1 : 1 ≤ q := by have := hLq.q3; omega
  have hE0 := Err_nonneg hη δ q hq1
  have tl0 : TLat q a 0 (Err η δ q) := TLat.mono (h1 q (by omega) a ha) (Err_ge hη (hle d1 (by simp)) q hq1)
  have tl1 : TLat q a 1 (Err η δ q) := TLat.mono (h2 q (by omega) a ha) (Err_ge hη (hle d2 (by simp)) q hq1)
  have tl2 : TLat q a 2 (Err η δ q) := TLat.mono (h3 q (by omega) a ha) (Err_ge hη (hle d3 (by simp)) q hq1)
  have tl3 : TLat q a 3 (Err η δ q) := TLat.mono (h4 q (by omega) a ha) (Err_ge hη (hle d4 (by simp)) q hq1)
  have tu1 : TUat q a 1 (Err η δ q) := TUat.mono (h5 q (by omega) a ha) (Err_ge hη (hle d5 (by simp)) q hq1)
  have tu2 : TUat q a 2 (Err η δ q) := TUat.mono (h6 q (by omega) a ha) (Err_ge hη (hle d6 (by simp)) q hq1)
  have tu3 : TUat q a 3 (Err η δ q) := TUat.mono (h7 q (by omega) a ha) (Err_ge hη (hle d7 (by simp)) q hq1)
  have p0 : P6at q a 0 (Err η δ q) := P6at.mono (h8 q (by omega) a ha) (Err_ge' (η := η) (hle d8 (by simp)) q hq1)
  have p1 : P6at q a 1 (Err η δ q) := P6at.mono (h9 q (by omega) a ha) (Err_ge' (η := η) (hle d9 (by simp)) q hq1)
  have p2 : P6at q a 2 (Err η δ q) := P6at.mono (h10 q (by omega) a ha) (Err_ge' (η := η) (hle d10 (by simp)) q hq1)
  have p3 : P6at q a 3 (Err η δ q) := P6at.mono (h11 q (by omega) a ha) (Err_ge' (η := η) (hle d11 (by simp)) q hq1)
  refine ⟨hLq, ⟨lf_j0 hLq p0, fun i hi hW => lf_e1 hLq tl0 hi hW, fun i hi _ => lf_p1 hLq p1 hi,
    fun i hi j hj _ hd => lf_e2 hLq tu1 hi hj hd, fun i hi j hj _ _ => lf_p2 hLq p2 hi hj,
    fun i hi _ j hj _ hs => lf_e2' hLq hE0 tl1 tu1 hi hj hs,
    fun i hi j hj _ hd k hk hkk hn3 => lf_e3 hLq tu2 hi hj hk hd hkk hn3,
    fun i hi j hj _ _ k hk _ _ => lf_p3 hLq p3 hi hj hk,
    fun i hi j hj _ _ k hk _ hn3 => lf_e3' hLq hE0 tl2 tu2 hi hj hk hn3,
    fun i hi j hj _ _ k hk _ _ l hl _ hs => lf_e4 hLq hE0 tl3 tu3 hi hj hk (by omega) hs⟩⟩

end SieveQ
