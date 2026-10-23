/-
# Round 526, part 4: the dual sums as polynomials at the points of the first character, and the kernel of a pair

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

For a pair `χ ≠ χ′` with `z = (a + a′) + i(g − g′)` (`a = δ_χ`, `g = γ_χ`, `a′ = δ_χ′`, `g′ = γ_χ′`), part 2's
reflection is used on the lines `c₁ = 3/4 − 2a` and `c₂ = −1/4 − 2a`, where `Re(z + c₁) = 3/4 + a′ − a` and
`Re(z + c₂) = −1/4 + a′ − a`.

* `dual_term`, `sum_dual_eq_conj_pv`, `dualS_eq_conj_pv`: on the line `κ − 2a`,
  `(χχ′⁻¹)⁻¹(m)m^{z+κ−2a+iv−1} = conj(dualCo(m)·χ(m)m^{−(a+ig)})`, so a dual sum over any set of positive integers is the
  conjugate of a Dirichlet polynomial at the point `u_χ = a + ig` of `χ`, with coefficients
  `dualCo(m) = conj(χ′(m)m^{κ−1+a′+i(v−g′)})` that do not depend on `χ`.
* `mass_dualCo_one`: on `κ = 3/4`, `Σ_{m ≤ Z}|dualCo(m)|² ≤ Z^{1/2+2a′}/(1/2 + 2a′)` for `0 ≤ a′ < 1/4`.
* `tailBlock`, `dualT_split`, `mass_dualCo_block`: the tail beyond `Z = A − 1` splits into the blocks
  `B_j = [A2^j, A2^{j+1})`, `j < J`, and the rest from `A2^J` on; on `κ = −1/4`,
  `Σ_{m∈B_j}|dualCo(m)|² ≤ (A2^j)^{−3/2+2a′}`.
* `norm_far_tail_le`: `|Σ_{m ≥ M}ψ(m)m^{s−1}| ≤ M^{−1/16}ζ(9/8)` for `Re s ≤ −3/16` and `M ≥ 1`.
* `pair_kernel_one`, `pair_kernel_two`: for `0 ≤ a, a′ ≤ η ≤ 1/16`, `Λ⁻¹ ≤ M`, `1 ≤ M` and the analytic conductor
  `Δ = f(1 + |g − g′|) ≤ D` (`f` the conductor of `χχ′⁻¹`),
  `|kW_Λ(c₁ + iv)||Φ(z + c₁ + iv)| ≤ K₀Λ^{3/4}Δ^{−1/4}(1 + |v|)^{−4}` and
  `|kW_Λ(c₂ + iv)||Φ(z + c₂ + iv)| ≤ K₀Λ^{−1/4}Δ^{3/4}(1 + |v|)^{−4}` with `K₀ = 12·KG·CG·EQ(q)M^{2η}D^η`.
-/

import LinnikWeighted
import SquarefreeCount

open Complex Real Finset MeasureTheory Filter Topology

noncomputable section

namespace LinnikReflect

open DirichletCharacter LinnikPower

variable {q : ℕ}

/-! ### The dual sums as conjugated Dirichlet polynomials at the points of the first character -/

/-- The dual coefficient `conj(χ′(m)m^{κ−1+a′+i(v−g′)})`. -/
def dualCo (χ' : DirichletCharacter ℂ q) (κ a' g' v : ℝ) (m : ℕ) : ℂ :=
  (starRingEnd ℂ) (χ' m * (m : ℂ) ^ (((κ - 1 + a' : ℝ) : ℂ) + ((v - g' : ℝ) : ℂ) * I))

lemma natCast_arg_ne_pi (m : ℕ) : (m : ℂ).arg ≠ π := by
  rw [Complex.natCast_arg]; exact Real.pi_pos.ne

/-- One term of a dual sum: with `z = (a + a′) + i(g − g′)` and the line `κ − 2a`,
`(χχ′⁻¹)⁻¹(m)m^{z + κ − 2a + iv − 1} = conj(dualCo(m)·χ(m)m^{−(a+ig)})`. -/
lemma dual_term (χ χ' : DirichletCharacter ℂ q) {m : ℕ} (hm : m ≠ 0) (a a' g g' κ v : ℝ) :
    (χ * χ'⁻¹)⁻¹ m * (m : ℂ) ^ ((((a + a' : ℝ) : ℂ) + ((g - g' : ℝ) : ℂ) * I) + (((κ - 2 * a : ℝ) : ℂ) + v * I) - 1) =
      (starRingEnd ℂ) (dualCo χ' κ a' g' v m * (χ m * (m : ℂ) ^ (-((a : ℂ) + g * I)))) := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hχc : (starRingEnd ℂ) (χ m) = χ⁻¹ m := by rw [← MulChar.star_apply']; rfl
  unfold dualCo
  rw [map_mul, Complex.conj_conj, map_mul, hχc]
  have hc : (starRingEnd ℂ) ((m : ℂ) ^ (-((a : ℂ) + g * I))) = (m : ℂ) ^ (-((a : ℂ) - g * I)) := by
    have h := Complex.cpow_conj (m : ℂ) (-((a : ℂ) + g * I)) (natCast_arg_ne_pi m)
    rw [Complex.conj_natCast] at h
    rw [← h]
    congr 1
    simp [map_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hc]
  have hinv : (χ * χ'⁻¹)⁻¹ = χ⁻¹ * χ' := by rw [mul_inv, inv_inv]
  rw [hinv, MulChar.mul_apply]
  have hexp : (m : ℂ) ^ ((((a + a' : ℝ) : ℂ) + ((g - g' : ℝ) : ℂ) * I) + (((κ - 2 * a : ℝ) : ℂ) + v * I) - 1) =
      (m : ℂ) ^ (((κ - 1 + a' : ℝ) : ℂ) + ((v - g' : ℝ) : ℂ) * I) * (m : ℂ) ^ (-((a : ℂ) - g * I)) := by
    rw [← Complex.cpow_add _ _ hm0]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- **A dual sum over any set of positive integers** is the conjugate of a Dirichlet polynomial at
`u = a + ig`, with coefficients `dualCo` independent of the first character. -/
lemma sum_dual_eq_conj_pv (χ χ' : DirichletCharacter ℂ q) {B : Finset ℕ} (hB0 : 0 ∉ B) (a a' g g' κ v : ℝ) :
    ∑ m ∈ B, (χ * χ'⁻¹)⁻¹ m * (m : ℂ) ^ ((((a + a' : ℝ) : ℂ) + ((g - g' : ℝ) : ℂ) * I) +
        (((κ - 2 * a : ℝ) : ℂ) + v * I) - 1) =
      (starRingEnd ℂ) (pv B (dualCo χ' κ a' g' v) χ ((a : ℂ) + g * I)) := by
  unfold pv
  rw [map_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [dual_term χ χ' (fun h => hB0 (h ▸ hm)), mul_assoc]

/-- The finite dual sum as a conjugated Dirichlet polynomial. -/
lemma dualS_eq_conj_pv (χ χ' : DirichletCharacter ℂ q) (Z : ℕ) (a a' g g' κ v : ℝ) :
    dualS (χ * χ'⁻¹)⁻¹ Z ((((a + a' : ℝ) : ℂ) + ((g - g' : ℝ) : ℂ) * I) + (((κ - 2 * a : ℝ) : ℂ) + v * I)) =
      (starRingEnd ℂ) (pv (Icc 1 Z) (dualCo χ' κ a' g' v) χ ((a : ℂ) + g * I)) := by
  unfold dualS
  exact sum_dual_eq_conj_pv χ χ' (fun h => by simp at h) a a' g g' κ v

lemma norm_dualCo_le (χ' : DirichletCharacter ℂ q) (κ a' g' v : ℝ) {m : ℕ} (hm : m ≠ 0) :
    ‖dualCo χ' κ a' g' v m‖ ≤ (m : ℝ) ^ (κ - 1 + a') := by
  unfold dualCo
  rw [Complex.norm_conj, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm)]
  have h1 := DirichletCharacter.norm_le_one χ' m
  have hre : (((κ - 1 + a' : ℝ) : ℂ) + ((v - g' : ℝ) : ℂ) * I).re = κ - 1 + a' := by simp
  rw [hre]
  calc ‖χ' m‖ * (m : ℝ) ^ (κ - 1 + a') ≤ 1 * (m : ℝ) ^ (κ - 1 + a') :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := one_mul _

/-- **The mass of the finite dual coefficients** on the line `κ = 3/4`:
`Σ_{m ≤ Z}|dualCo(m)|² ≤ Z^{1/2+2a′}/(1/2 + 2a′)` for `0 ≤ a′ < 1/4` (`SquarefreeCount.sum_rpow_neg_le`). -/
lemma mass_dualCo_one (χ' : DirichletCharacter ℂ q) {a' : ℝ} (ha0 : 0 ≤ a') (ha1 : a' < 1 / 4) (g' v : ℝ)
    (Z : ℕ) :
    ∑ m ∈ Icc 1 Z, ‖dualCo χ' (3 / 4) a' g' v m‖ ^ 2 ≤ (Z : ℝ) ^ (1 / 2 + 2 * a') / (1 / 2 + 2 * a') := by
  have hI : Icc 1 Z = Ioc 0 Z := by ext m; simp only [mem_Icc, mem_Ioc]; omega
  have h := SquarefreeCount.sum_rpow_neg_le (β := 1 / 2 - 2 * a') (by linarith) (by linarith) Z
  rw [show 1 - (1 / 2 - 2 * a') = 1 / 2 + 2 * a' by ring] at h
  refine le_trans (sum_le_sum fun m hm => ?_) (hI ▸ h)
  have hm0 : m ≠ 0 := by have := (mem_Icc.1 hm).1; omega
  have h1 := norm_dualCo_le χ' (3 / 4) a' g' v hm0
  calc ‖dualCo χ' (3 / 4) a' g' v m‖ ^ 2 ≤ ((m : ℝ) ^ (3 / 4 - 1 + a')) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (m : ℝ) ^ (-(1 / 2 - 2 * a')) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]; congr 1; push_cast; ring

/-! ### The dual tail in dyadic blocks -/

/-- The `j`-th block `{A ≤ m < A2^J : ⌊log₂⌊m/A⌋⌋ = j}` of the dual tail beyond `Z = A − 1`. -/
def tailBlock (A J j : ℕ) : Finset ℕ := (Ico A (A * 2 ^ J)).filter fun m => Nat.log 2 (m / A) = j

lemma mem_tailBlock {A J j m : ℕ} (hA : 1 ≤ A) (hm : m ∈ tailBlock A J j) : A * 2 ^ j ≤ m ∧ m < A * 2 ^ (j + 1) := by
  obtain ⟨hm, hj⟩ := mem_filter.1 hm
  obtain ⟨hm1, -⟩ := mem_Ico.1 hm
  have hq1 : 1 ≤ m / A := (Nat.one_le_div_iff (by omega)).2 hm1
  have h1 : 2 ^ Nat.log 2 (m / A) ≤ m / A := Nat.pow_log_le_self 2 (by omega)
  have h2 : m / A < 2 ^ (Nat.log 2 (m / A) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  rw [hj] at h1 h2
  constructor
  · calc A * 2 ^ j ≤ A * (m / A) := Nat.mul_le_mul_left A h1
      _ ≤ m := Nat.mul_div_le m A
  · have h3 : m < A * (m / A + 1) := by
      have := Nat.lt_div_mul_add (a := m) (b := A) (by omega)
      linarith [mul_comm (m / A) A]
    calc m < A * (m / A + 1) := h3
      _ ≤ A * 2 ^ (j + 1) := Nat.mul_le_mul_left A (by omega)

lemma tailBlock_card_le {A J j : ℕ} (hA : 1 ≤ A) : ((tailBlock A J j).card : ℝ) ≤ (A * 2 ^ j : ℕ) := by
  have hsub : tailBlock A J j ⊆ Ico (A * 2 ^ j) (A * 2 ^ (j + 1)) := fun m hm =>
    mem_Ico.2 (mem_tailBlock hA hm)
  have h := Finset.card_le_card hsub
  rw [Nat.card_Ico] at h
  have e : A * 2 ^ (j + 1) - A * 2 ^ j = A * 2 ^ j := by
    rw [pow_succ, ← mul_assoc, mul_two, Nat.add_sub_cancel]
  rw [e] at h
  exact_mod_cast h

lemma tailBlock_sub {A J j : ℕ} (hA : 1 ≤ A) : tailBlock A J j ⊆ Icc 1 (A * 2 ^ (j + 1)) := fun m hm => by
  have h := mem_tailBlock hA hm
  have : 1 ≤ A * 2 ^ j := Nat.one_le_iff_ne_zero.2 (by positivity)
  exact mem_Icc.2 ⟨by omega, by omega⟩

/-- **The mass of a tail block** on the line `κ = −1/4`: `Σ_{m∈B_j}|dualCo(m)|² ≤ (A2^j)^{−3/2+2a′}`. -/
lemma mass_dualCo_block (χ' : DirichletCharacter ℂ q) {a' : ℝ} (ha1 : a' ≤ 1 / 4) (g' v : ℝ)
    {A J j : ℕ} (hA : 1 ≤ A) :
    ∑ m ∈ tailBlock A J j, ‖dualCo χ' (-1 / 4) a' g' v m‖ ^ 2 ≤ ((A * 2 ^ j : ℕ) : ℝ) ^ (-3 / 2 + 2 * a') := by
  set X : ℝ := ((A * 2 ^ j : ℕ) : ℝ) with hX
  have hX1 : 1 ≤ X := by rw [hX]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hterm : ∀ m ∈ tailBlock A J j, ‖dualCo χ' (-1 / 4) a' g' v m‖ ^ 2 ≤ X ^ (-5 / 2 + 2 * a') := by
    intro m hm
    obtain ⟨h1, -⟩ := mem_tailBlock hA hm
    have hm1 : X ≤ m := by rw [hX]; exact_mod_cast h1
    have hm0 : m ≠ 0 := by intro h; rw [h] at hm1; simp at hm1; linarith
    have hn := norm_dualCo_le χ' (-1 / 4) a' g' v hm0
    calc ‖dualCo χ' (-1 / 4) a' g' v m‖ ^ 2 ≤ ((m : ℝ) ^ (-1 / 4 - 1 + a')) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = (m : ℝ) ^ (-5 / 2 + 2 * a') := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]; congr 1; push_cast; ring
      _ ≤ X ^ (-5 / 2 + 2 * a') := Real.rpow_le_rpow_of_nonpos (by linarith) hm1 (by linarith)
  calc ∑ m ∈ tailBlock A J j, ‖dualCo χ' (-1 / 4) a' g' v m‖ ^ 2 ≤ ∑ _m ∈ tailBlock A J j, X ^ (-5 / 2 + 2 * a') :=
        sum_le_sum hterm
    _ = (tailBlock A J j).card * X ^ (-5 / 2 + 2 * a') := by rw [sum_const, nsmul_eq_mul]
    _ ≤ X * X ^ (-5 / 2 + 2 * a') := by gcongr; exact tailBlock_card_le hA
    _ = X ^ (-3 / 2 + 2 * a') := by
        conv_rhs => rw [show (-3 / 2 + 2 * a') = 1 + (-5 / 2 + 2 * a') by ring, Real.rpow_add (by linarith),
          Real.rpow_one]

/-- **The dual tail in blocks**: for `Re s < 0` and `A = Z + 1`,
`Σ_{m > Z}ψ(m)m^{s−1} = Σ_{j<J}Σ_{m∈B_j}ψ(m)m^{s−1} + Σ_{m ≥ A2^J}ψ(m)m^{s−1}`. -/
lemma dualT_split (ψ : DirichletCharacter ℂ q) (Z J : ℕ) {s : ℂ} (hs : s.re < 0) :
    dualT ψ Z s = ∑ j ∈ range J, ∑ m ∈ tailBlock (Z + 1) J j, ψ m * (m : ℂ) ^ (s - 1) +
      ∑' m : ℕ, if (Z + 1) * 2 ^ J ≤ m then ψ m * (m : ℂ) ^ (s - 1) else 0 := by
  classical
  set A := Z + 1 with hA
  set f : ℕ → ℂ := fun m => ψ m * (m : ℂ) ^ (s - 1) with hf
  have hA1 : 1 ≤ A := by omega
  have hA2 : A ≤ A * 2 ^ J := Nat.le_mul_of_pos_right A (by positivity)
  -- summability of the terms
  have hnorm : ∀ m : ℕ, ‖f m‖ ≤ ((m : ℝ) ^ (1 - s.re))⁻¹ := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · have hs1 : s - 1 ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      simp only [hf, Nat.cast_zero, Complex.zero_cpow hs1, mul_zero, norm_zero]
      positivity
    · rw [hf, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm)]
      have h1 := DirichletCharacter.norm_le_one ψ m
      have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
      have h2 : (m : ℝ) ^ (s - 1).re = ((m : ℝ) ^ (1 - s.re))⁻¹ := by
        rw [← Real.rpow_neg hm0.le]; congr 1; simp
      rw [h2]
      calc ‖ψ m‖ * ((m : ℝ) ^ (1 - s.re))⁻¹ ≤ 1 * ((m : ℝ) ^ (1 - s.re))⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := one_mul _
  have hfs : Summable f :=
    Summable.of_norm_bounded (Real.summable_nat_rpow_inv.2 (by linarith : (1 : ℝ) < 1 - s.re)) hnorm
  -- split the indicator
  have hsplit : ∀ m : ℕ, (if Z < m then f m else 0) =
      (if m ∈ Ico A (A * 2 ^ J) then f m else 0) + (if A * 2 ^ J ≤ m then f m else 0) := by
    intro m
    by_cases h1 : m < A
    · rw [ite_eq_right (by omega), ite_eq_right (fun h => by simp [mem_Ico] at h; omega),
        ite_eq_right (by omega)]; ring
    · by_cases h2 : m < A * 2 ^ J
      · rw [ite_eq_left (by omega), ite_eq_left (mem_Ico.2 ⟨by omega, h2⟩), ite_eq_right (by omega)]; ring
      · rw [ite_eq_left (by omega), ite_eq_right (fun h => by simp [mem_Ico] at h; omega),
          ite_eq_left (by omega)]; ring
  have hs1 : Summable fun m : ℕ => if m ∈ Ico A (A * 2 ^ J) then f m else 0 :=
    summable_of_ne_finset_zero (s := Ico A (A * 2 ^ J)) fun m hm => ite_eq_right hm
  have hs2 : Summable fun m : ℕ => if A * 2 ^ J ≤ m then f m else 0 := by
    refine Summable.of_norm_bounded hfs.norm fun m => ?_
    split_ifs
    · exact le_rfl
    · simp
  unfold dualT
  rw [show (fun m : ℕ => if Z < m then ψ m * (m : ℂ) ^ (s - 1) else 0) =
      fun m : ℕ => (if m ∈ Ico A (A * 2 ^ J) then f m else 0) + (if A * 2 ^ J ≤ m then f m else 0) from
      funext hsplit, hs1.tsum_add hs2]
  congr 1
  rw [tsum_eq_sum (s := Ico A (A * 2 ^ J)) fun m hm => ite_eq_right hm]
  rw [sum_congr rfl fun m hm => ite_eq_left hm]
  have hmaps : ∀ m ∈ Ico A (A * 2 ^ J), Nat.log 2 (m / A) ∈ range J := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := mem_Ico.1 hm
    rw [Finset.mem_range]
    have hq1 : 1 ≤ m / A := (Nat.one_le_div_iff (by omega)).2 hm1
    have hq2 : m / A < 2 ^ J := (Nat.div_lt_iff_lt_mul (by omega)).2 (by rw [mul_comm]; exact hm2)
    exact Nat.log_lt_of_lt_pow (by omega) hq2
  exact (sum_fiberwise_of_maps_to hmaps f).symm

/-- **The far tail is small**: for `Re s ≤ −3/16` and `M ≥ 1`, `|Σ_{m ≥ M}ψ(m)m^{s−1}| ≤ M^{−1/16}ζ(9/8)` with
`ζ(9/8) = Σ_{m≥1} m^{−9/8}`. -/
lemma norm_far_tail_le (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re ≤ -3 / 16) {M : ℕ} (hM : 1 ≤ M) :
    ‖∑' m : ℕ, if M ≤ m then ψ m * (m : ℂ) ^ (s - 1) else 0‖ ≤
      (M : ℝ) ^ (-(1 / 16 : ℝ)) * ∑' m : ℕ, ((m : ℝ) ^ (9 / 8 : ℝ))⁻¹ := by
  have hz : Summable fun m : ℕ => ((m : ℝ) ^ (9 / 8 : ℝ))⁻¹ := Real.summable_nat_rpow_inv.2 (by norm_num)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hb : ∀ m : ℕ, ‖if M ≤ m then ψ m * (m : ℂ) ^ (s - 1) else 0‖ ≤
      (M : ℝ) ^ (-(1 / 16 : ℝ)) * ((m : ℝ) ^ (9 / 8 : ℝ))⁻¹ := by
    intro m
    split_ifs with h
    · have hm0 : m ≠ 0 := by omega
      have hm1 : (M : ℝ) ≤ m := by exact_mod_cast h
      have hmpos : (0 : ℝ) < m := by linarith
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm0)]
      have h1 := DirichletCharacter.norm_le_one ψ m
      have h2 : (m : ℝ) ^ (s - 1).re ≤ (m : ℝ) ^ (-(19 / 16 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp; linarith)
      have h3 : (m : ℝ) ^ (-(19 / 16 : ℝ)) = (m : ℝ) ^ (-(1 / 16 : ℝ)) * ((m : ℝ) ^ (9 / 8 : ℝ))⁻¹ := by
        rw [← Real.rpow_neg hmpos.le, ← Real.rpow_add hmpos]; norm_num
      have h4 : (m : ℝ) ^ (-(1 / 16 : ℝ)) ≤ (M : ℝ) ^ (-(1 / 16 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hm1 (by norm_num)
      calc ‖ψ m‖ * (m : ℝ) ^ (s - 1).re ≤ 1 * ((m : ℝ) ^ (-(1 / 16 : ℝ)) * ((m : ℝ) ^ (9 / 8 : ℝ))⁻¹) := by
            rw [← h3]; exact mul_le_mul h1 h2 (by positivity) zero_le_one
        _ ≤ (M : ℝ) ^ (-(1 / 16 : ℝ)) * ((m : ℝ) ^ (9 / 8 : ℝ))⁻¹ := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_right h4 (by positivity)
    · simp only [norm_zero]; positivity
  have hs : Summable fun m : ℕ => (M : ℝ) ^ (-(1 / 16 : ℝ)) * ((m : ℝ) ^ (9 / 8 : ℝ))⁻¹ := hz.mul_left _
  calc ‖∑' m : ℕ, if M ≤ m then ψ m * (m : ℂ) ^ (s - 1) else 0‖
      ≤ ∑' m : ℕ, ‖if M ≤ m then ψ m * (m : ℂ) ^ (s - 1) else 0‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs)
    _ ≤ ∑' m : ℕ, (M : ℝ) ^ (-(1 / 16 : ℝ)) * ((m : ℝ) ^ (9 / 8 : ℝ))⁻¹ :=
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs).tsum_le_tsum hb hs
    _ = _ := tsum_mul_left

/-! ### The reflected kernels on the two lines, for one pair -/

/-- `(1 + |x + y|)^e ≤ (1 + |x|)^e(1 + |y|)` for `|e| ≤ 1`. -/
lemma one_add_abs_add_rpow_le (x y : ℝ) {e : ℝ} (he1 : -1 ≤ e) (he2 : e ≤ 1) :
    (1 + |x + y|) ^ e ≤ (1 + |x|) ^ e * (1 + |y|) := by
  have hx : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hy : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hxy : 1 ≤ 1 + |x + y| := by linarith [abs_nonneg (x + y)]
  rcases le_or_gt 0 e with he | he
  · have h1 : 1 + |x + y| ≤ (1 + |x|) * (1 + |y|) := by
      nlinarith [abs_add_le x y, abs_nonneg x, abs_nonneg y]
    calc (1 + |x + y|) ^ e ≤ ((1 + |x|) * (1 + |y|)) ^ e := Real.rpow_le_rpow (by linarith) h1 he
      _ = (1 + |x|) ^ e * (1 + |y|) ^ e := Real.mul_rpow (by linarith) (by linarith)
      _ ≤ (1 + |x|) ^ e * (1 + |y|) := by
          gcongr
          calc (1 + |y|) ^ e ≤ (1 + |y|) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy he2
            _ = 1 + |y| := Real.rpow_one _
  · have h0 : |x| ≤ |x + y| + |y| := by
      calc |x| = |(x + y) + (-y)| := by ring_nf
        _ ≤ |x + y| + |-y| := abs_add_le _ _
        _ = |x + y| + |y| := by rw [abs_neg]
    have h1 : 1 + |x| ≤ (1 + |x + y|) * (1 + |y|) := by nlinarith [abs_nonneg (x + y), abs_nonneg y]
    have h2 : (1 + |x|) / (1 + |y|) ≤ 1 + |x + y| := by rw [div_le_iff₀ (by linarith)]; linarith
    calc (1 + |x + y|) ^ e ≤ ((1 + |x|) / (1 + |y|)) ^ e :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h2 he.le
      _ = (1 + |x|) ^ e * (1 + |y|) ^ (-e) := by
          rw [Real.div_rpow (by linarith) (by linarith), Real.rpow_neg (by linarith), div_eq_mul_inv]
      _ ≤ (1 + |x|) ^ e * (1 + |y|) := by
          gcongr
          calc (1 + |y|) ^ (-e) ≤ (1 + |y|) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
            _ = 1 + |y| := Real.rpow_one _

/-- `|Φ(z + c + iv)| ≤ CG·EQ(q)·(f(1 + |Im z|))^e·(1 + |v|)` with `e = 1/2 − Re z − c`, on
`−5/16 ≤ Re z + c ≤ 13/16`. -/
lemma norm_Phi_line_le {f : ℕ} [NeZero f] {ψ : DirichletCharacter ℂ f} (hprim : ψ.IsPrimitive) (q : ℕ) {z : ℂ}
    {c : ℝ} (h1 : -5 / 16 ≤ z.re + c) (h2 : z.re + c ≤ 13 / 16) (v : ℝ) :
    ‖Phi ψ q (z + (c + v * I))‖ ≤ CG * EQ q * ((f : ℝ) * (1 + |z.im|)) ^ (1 / 2 - (z.re + c)) * (1 + |v|) := by
  have hre : (z + (c + v * I)).re = z.re + c := by simp
  have him : (z + (c + v * I)).im = z.im + v := by simp
  have hP := norm_Phi_le hprim q (s := z + (c + v * I)) (by rw [hre]; exact h1) (by rw [hre]; exact h2)
  rw [hre, him] at hP
  set e := 1 / 2 - (z.re + c) with he
  have hf0 : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne f)
  have hb := one_add_abs_add_rpow_le z.im v (e := e) (by rw [he]; linarith) (by rw [he]; linarith)
  have hCG := CG_pos
  have hEQ := EQ_pos q
  calc ‖Phi ψ q (z + (c + v * I))‖ ≤ (f : ℝ) ^ e * (CG * (1 + |z.im + v|) ^ e) * EQ q := hP
    _ ≤ (f : ℝ) ^ e * (CG * ((1 + |z.im|) ^ e * (1 + |v|))) * EQ q := by gcongr
    _ = CG * EQ q * ((f : ℝ) ^ e * (1 + |z.im|) ^ e) * (1 + |v|) := by ring
    _ = CG * EQ q * ((f : ℝ) * (1 + |z.im|)) ^ e * (1 + |v|) := by
        rw [Real.mul_rpow hf0.le (by positivity)]

/-- `|kW_Λ(c + iv)| ≤ 12·KG·Λ^c(1 + |v|)^{−5}` for `|c| ≥ 1/4`, `−1/2 ≤ c ≤ 2`. -/
lemma norm_kW_line_le {Λ : ℝ} (hΛ : 0 < Λ) {c : ℝ} (hc0 : 1 / 4 ≤ |c|) (hc1 : -1 / 2 ≤ c) (hc2 : c ≤ 2)
    (v : ℝ) : ‖kW Λ (c + v * I)‖ ≤ 12 * InghamDensity.KG * Λ ^ c * ((1 + |v|) ^ 5)⁻¹ := by
  have hre : ((c : ℂ) + v * I).re = c := by simp
  have him : ((c : ℂ) + v * I).im = v := by simp
  have hG := norm_mul_Gamma_le (w := (c : ℂ) + v * I) (by rw [hre]; exact hc1) (by rw [hre]; exact hc2)
  rw [him] at hG
  have hw : 1 / 4 ≤ ‖(c : ℂ) + v * I‖ := by
    have := Complex.abs_re_le_norm ((c : ℂ) + v * I)
    rw [hre] at this
    linarith
  have h3 := norm_cpow_sub_half_le hΛ (w := (c : ℂ) + v * I) (by rw [hre]; linarith)
  rw [hre] at h3
  have hv5 : 0 < (1 + |v|) ^ 5 := by positivity
  have hKG := InghamDensity.KG_pos
  have hΓ : ‖Complex.Gamma ((c : ℂ) + v * I)‖ ≤ 4 * InghamDensity.KG * ((1 + |v|) ^ 5)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hv5]
    have h0 : 0 ≤ ‖Complex.Gamma ((c : ℂ) + v * I)‖ * (1 + |v|) ^ 5 := by positivity
    nlinarith
  unfold kW
  rw [norm_mul]
  calc ‖Complex.Gamma ((c : ℂ) + v * I)‖ * ‖(Λ : ℂ) ^ ((c : ℂ) + v * I) - ((Λ / 2 : ℝ) : ℂ) ^ ((c : ℂ) + v * I)‖
      ≤ (4 * InghamDensity.KG * ((1 + |v|) ^ 5)⁻¹) * (3 * Λ ^ c) :=
        mul_le_mul hΓ h3 (norm_nonneg _) (by positivity)
    _ = 12 * InghamDensity.KG * Λ ^ c * ((1 + |v|) ^ 5)⁻¹ := by ring

/-- `Λ^{−a} ≤ M^η` for `0 ≤ a ≤ η`, `M ≥ 1` and `Λ⁻¹ ≤ M`. -/
lemma rpow_neg_le_slack {Λ a η M : ℝ} (hΛ : 0 < Λ) (ha : 0 ≤ a) (haη : a ≤ η) (hM : 1 ≤ M) (hΛM : Λ⁻¹ ≤ M) :
    Λ ^ (-a) ≤ M ^ η := by
  have hη : 0 ≤ η := ha.trans haη
  rcases le_or_gt 1 Λ with h | h
  · exact (Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)).trans (Real.one_le_rpow hM hη)
  · have hi : 1 ≤ Λ⁻¹ := by rw [le_inv_comm₀ one_pos hΛ, inv_one]; exact h.le
    rw [Real.rpow_neg hΛ.le, ← Real.inv_rpow hΛ.le]
    calc Λ⁻¹ ^ a ≤ Λ⁻¹ ^ η := Real.rpow_le_rpow_of_exponent_le hi haη
      _ ≤ M ^ η := Real.rpow_le_rpow (by positivity) hΛM hη

/-- `X^{e₀+t} ≤ X^{e₀}·Y^η` for `1 ≤ X ≤ Y`, `t ≤ η`, `0 ≤ η`. -/
lemma rpow_add_le_slack {X Y e₀ t η : ℝ} (hX : 1 ≤ X) (hXY : X ≤ Y) (ht : t ≤ η) (hη : 0 ≤ η) :
    X ^ (e₀ + t) ≤ X ^ e₀ * Y ^ η := by
  rw [Real.rpow_add (by linarith)]
  gcongr
  calc X ^ t ≤ X ^ η := Real.rpow_le_rpow_of_exponent_le hX ht
    _ ≤ Y ^ η := Real.rpow_le_rpow (by linarith) hXY hη

/-- **The kernel on the first line** `c₁ = 3/4 − 2a`, for one pair: with `z = (a + a′) + i(g − g′)`, `0 ≤ a, a′ ≤ η ≤ 1/16`,
`Λ⁻¹ ≤ M`, `1 ≤ M` and `Δ = f(1 + |g − g′|) ≤ D`,
`|kW_Λ(c₁ + iv)||Φ(z + c₁ + iv)| ≤ 12·KG·CG·EQ(q)M^{2η}D^η·Λ^{3/4}Δ^{−1/4}(1 + |v|)^{−4}`. -/
theorem pair_kernel_one {f : ℕ} [NeZero f] {ψ : DirichletCharacter ℂ f} (hprim : ψ.IsPrimitive) (q : ℕ)
    {Λ : ℝ} (hΛ : 0 < Λ) {a a' η : ℝ} (ha : 0 ≤ a) (haη : a ≤ η) (ha' : 0 ≤ a') (ha'η : a' ≤ η)
    (hη : η ≤ 1 / 16) (g g' v : ℝ) {M D : ℝ} (hM : 1 ≤ M) (hΛM : Λ⁻¹ ≤ M)
    (hD : (f : ℝ) * (1 + |g - g'|) ≤ D) :
    ‖kW Λ (((3 / 4 - 2 * a : ℝ) : ℂ) + v * I)‖ *
        ‖Phi ψ q ((((a + a' : ℝ) : ℂ) + ((g - g' : ℝ) : ℂ) * I) + (((3 / 4 - 2 * a : ℝ) : ℂ) + v * I))‖ ≤
      12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η * Λ ^ (3 / 4 : ℝ) *
        ((f : ℝ) * (1 + |g - g'|)) ^ (-1 / 4 : ℝ) * ((1 + |v|) ^ 4)⁻¹ := by
  set z : ℂ := ((a + a' : ℝ) : ℂ) + ((g - g' : ℝ) : ℂ) * I with hz
  have hzre : z.re = a + a' := by simp [hz]
  have hzim : z.im = g - g' := by simp [hz]
  have hk := norm_kW_line_le hΛ (c := 3 / 4 - 2 * a) (by rw [abs_of_pos (by linarith)]; linarith)
    (by linarith) (by linarith) v
  have hP := norm_Phi_line_le hprim q (z := z) (c := 3 / 4 - 2 * a) (by rw [hzre]; linarith)
    (by rw [hzre]; linarith) v
  rw [hzre, hzim] at hP
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne f)
  have hΔ1 : 1 ≤ (f : ℝ) * (1 + |g - g'|) := by nlinarith [abs_nonneg (g - g')]
  -- the exponent of `Λ`
  have hΛe : Λ ^ (3 / 4 - 2 * a) ≤ Λ ^ (3 / 4 : ℝ) * M ^ (2 * η) := by
    rw [show (3 / 4 - 2 * a) = 3 / 4 + -(2 * a) by ring, Real.rpow_add hΛ]
    gcongr
    exact rpow_neg_le_slack hΛ (by linarith) (by linarith) hM hΛM
  -- the exponent of `Δ`
  have hΔe : ((f : ℝ) * (1 + |g - g'|)) ^ (1 / 2 - (a + a' + (3 / 4 - 2 * a))) ≤
      ((f : ℝ) * (1 + |g - g'|)) ^ (-1 / 4 : ℝ) * D ^ η := by
    rw [show 1 / 2 - (a + a' + (3 / 4 - 2 * a)) = -1 / 4 + (a - a') by ring]
    exact rpow_add_le_slack hΔ1 hD (by linarith) (by linarith)
  have hKG := InghamDensity.KG_pos
  have hCG := CG_pos
  have hEQ := EQ_pos q
  have hv : 0 < 1 + |v| := by positivity
  have e5 : ((1 + |v|) ^ 5)⁻¹ * (1 + |v|) = ((1 + |v|) ^ 4)⁻¹ := by
    field_simp
  calc ‖kW Λ (((3 / 4 - 2 * a : ℝ) : ℂ) + v * I)‖ * ‖Phi ψ q (z + (((3 / 4 - 2 * a : ℝ) : ℂ) + v * I))‖
      ≤ (12 * InghamDensity.KG * Λ ^ (3 / 4 - 2 * a) * ((1 + |v|) ^ 5)⁻¹) *
          (CG * EQ q * ((f : ℝ) * (1 + |g - g'|)) ^ (1 / 2 - (a + a' + (3 / 4 - 2 * a))) * (1 + |v|)) :=
        mul_le_mul hk hP (norm_nonneg _) (by positivity)
    _ ≤ (12 * InghamDensity.KG * (Λ ^ (3 / 4 : ℝ) * M ^ (2 * η)) * ((1 + |v|) ^ 5)⁻¹) *
          (CG * EQ q * (((f : ℝ) * (1 + |g - g'|)) ^ (-1 / 4 : ℝ) * D ^ η) * (1 + |v|)) := by
        gcongr
    _ = 12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η * Λ ^ (3 / 4 : ℝ) *
          ((f : ℝ) * (1 + |g - g'|)) ^ (-1 / 4 : ℝ) * (((1 + |v|) ^ 5)⁻¹ * (1 + |v|)) := by ring
    _ = _ := by rw [e5]

/-- **The kernel on the second line** `c₂ = −1/4 − 2a`, for one pair:
`|kW_Λ(c₂ + iv)||Φ(z + c₂ + iv)| ≤ 12·KG·CG·EQ(q)M^{2η}D^η·Λ^{−1/4}Δ^{3/4}(1 + |v|)^{−4}`. -/
theorem pair_kernel_two {f : ℕ} [NeZero f] {ψ : DirichletCharacter ℂ f} (hprim : ψ.IsPrimitive) (q : ℕ)
    {Λ : ℝ} (hΛ : 0 < Λ) {a a' η : ℝ} (ha : 0 ≤ a) (haη : a ≤ η) (ha' : 0 ≤ a') (ha'η : a' ≤ η)
    (hη : η ≤ 1 / 16) (g g' v : ℝ) {M D : ℝ} (hM : 1 ≤ M) (hΛM : Λ⁻¹ ≤ M)
    (hD : (f : ℝ) * (1 + |g - g'|) ≤ D) :
    ‖kW Λ (((-1 / 4 - 2 * a : ℝ) : ℂ) + v * I)‖ *
        ‖Phi ψ q ((((a + a' : ℝ) : ℂ) + ((g - g' : ℝ) : ℂ) * I) + (((-1 / 4 - 2 * a : ℝ) : ℂ) + v * I))‖ ≤
      12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η * Λ ^ (-1 / 4 : ℝ) *
        ((f : ℝ) * (1 + |g - g'|)) ^ (3 / 4 : ℝ) * ((1 + |v|) ^ 4)⁻¹ := by
  set z : ℂ := ((a + a' : ℝ) : ℂ) + ((g - g' : ℝ) : ℂ) * I with hz
  have hzre : z.re = a + a' := by simp [hz]
  have hzim : z.im = g - g' := by simp [hz]
  have hk := norm_kW_line_le hΛ (c := -1 / 4 - 2 * a) (by rw [abs_of_neg (by linarith)]; linarith)
    (by linarith) (by linarith) v
  have hP := norm_Phi_line_le hprim q (z := z) (c := -1 / 4 - 2 * a) (by rw [hzre]; linarith)
    (by rw [hzre]; linarith) v
  rw [hzre, hzim] at hP
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne f)
  have hΔ1 : 1 ≤ (f : ℝ) * (1 + |g - g'|) := by nlinarith [abs_nonneg (g - g')]
  have hΛe : Λ ^ (-1 / 4 - 2 * a) ≤ Λ ^ (-1 / 4 : ℝ) * M ^ (2 * η) := by
    rw [show (-1 / 4 - 2 * a) = -1 / 4 + -(2 * a) by ring, Real.rpow_add hΛ]
    gcongr
    exact rpow_neg_le_slack hΛ (by linarith) (by linarith) hM hΛM
  have hΔe : ((f : ℝ) * (1 + |g - g'|)) ^ (1 / 2 - (a + a' + (-1 / 4 - 2 * a))) ≤
      ((f : ℝ) * (1 + |g - g'|)) ^ (3 / 4 : ℝ) * D ^ η := by
    rw [show 1 / 2 - (a + a' + (-1 / 4 - 2 * a)) = 3 / 4 + (a - a') by ring]
    exact rpow_add_le_slack hΔ1 hD (by linarith) (by linarith)
  have hKG := InghamDensity.KG_pos
  have hCG := CG_pos
  have hEQ := EQ_pos q
  have hv : 0 < 1 + |v| := by positivity
  have e5 : ((1 + |v|) ^ 5)⁻¹ * (1 + |v|) = ((1 + |v|) ^ 4)⁻¹ := by
    field_simp
  calc ‖kW Λ (((-1 / 4 - 2 * a : ℝ) : ℂ) + v * I)‖ * ‖Phi ψ q (z + (((-1 / 4 - 2 * a : ℝ) : ℂ) + v * I))‖
      ≤ (12 * InghamDensity.KG * Λ ^ (-1 / 4 - 2 * a) * ((1 + |v|) ^ 5)⁻¹) *
          (CG * EQ q * ((f : ℝ) * (1 + |g - g'|)) ^ (1 / 2 - (a + a' + (-1 / 4 - 2 * a))) * (1 + |v|)) :=
        mul_le_mul hk hP (norm_nonneg _) (by positivity)
    _ ≤ (12 * InghamDensity.KG * (Λ ^ (-1 / 4 : ℝ) * M ^ (2 * η)) * ((1 + |v|) ^ 5)⁻¹) *
          (CG * EQ q * (((f : ℝ) * (1 + |g - g'|)) ^ (3 / 4 : ℝ) * D ^ η) * (1 + |v|)) := by
        gcongr
    _ = 12 * InghamDensity.KG * CG * EQ q * M ^ (2 * η) * D ^ η * Λ ^ (-1 / 4 : ℝ) *
          ((f : ℝ) * (1 + |g - g'|)) ^ (3 / 4 : ℝ) * (((1 + |v|) ^ 5)⁻¹ * (1 + |v|)) := by ring
    _ = _ := by rw [e5]

end LinnikReflect

#print axioms LinnikReflect.sum_dual_eq_conj_pv
#print axioms LinnikReflect.mass_dualCo_one
#print axioms LinnikReflect.mass_dualCo_block
#print axioms LinnikReflect.dualT_split
#print axioms LinnikReflect.norm_far_tail_le
#print axioms LinnikReflect.pair_kernel_one
#print axioms LinnikReflect.pair_kernel_two
