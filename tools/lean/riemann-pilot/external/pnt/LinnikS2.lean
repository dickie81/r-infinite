import LinnikSplit

/-!
# Round 540: the closed form of `S₂`, and the socket for prime moduli

Built on Mathlib, `LinnikMoment`, `LinnikLines` and `LinnikSplit`; no PrimeNumberTheoremAnd file is imported.

* `sum_what_mul`: Parseval for the residue sums, `Σ_k ŵ(−ck)ŵ(k) = qΣ_a w(a)w(ac)`.
* `S2part_eq`, `sum_xy_eq`: the three families of degenerate lines of round 539 are one sum, and substituting
  `x = −cy` turns it into `Σ_{c≠0}|R(c)|²Σ_{y≠0}ŵ(−cy)ŵ(y)`.
* `sum_w_RR`: `Σ_{a,c} w(a)w(ac)|R(c)|² = Σ_{χ,χ′∈W}|G(χ,χ′)|²` for real weights with `w(0) = 0`.
* `S2_closed`: `S₂ = 3(q − 1)ŵ(0)(qΣ_{χ,χ′∈W}|G(χ,χ′)|² − ŵ(0)²(q − 1)|W|)`. With the diagonal `N_c` this is
  `q⁻²S₂ = 3N_c(1 − 1/q)(‖E‖_F² + |W|N_c²/q)`, the term `3N_c‖E‖_F²` of `tr(G³) = |W|N_c³ + 3N_c‖E‖_F² + tr(E³)`
  up to factors `1 + O(1/q)`.
* `large_values_socket`: under the hypotheses of round 538's `large_values_lines`, if `‖E‖_F² ≤ A` (`offFrob`,
  the off-diagonal Frobenius norm of the Gram matrix) and `Re q⁻²S₃ ≤ B`, then
  `(|W|V² − N_cβ)³ ≤ β³(3N_c(A + |W|N_c²/q) + B)`. Chen–Gupta–Li bound the corresponding terms in their
  Proposition 6.1 (`S₂`) and §§7–11 (`S₃`); a bound for `S₃` below their first term at low energy is the open step
  of `frontier/linnik/SEVEN-THIRDS.md` §15.
-/

open Finset

noncomputable section

namespace LinnikS2

open LinnikLines LinnikSplit

variable {q : ℕ} [hq : Fact q.Prime] [DecidableEq (DirichletCharacter ℂ q)]

omit [DecidableEq (DirichletCharacter ℂ q)] in
/-- Parseval for the residue sums: `Σ_k ŵ(−ck)ŵ(k) = q Σ_a w(a)w(ac)`. -/
lemma sum_what_mul (w : ZMod q → ℂ) (c : ZMod q) :
    ∑ k, what w (-(c * k)) * what w k = q * ∑ a, w a * w (a * c) := by
  have hs : ∀ d : ZMod q, ∑ k, ZMod.stdAddChar (k * d) = if d = 0 then (q : ℂ) else 0 := by
    intro d
    have h := AddChar.sum_mulShift d (ZMod.isPrimitive_stdAddChar q)
    rw [ZMod.card] at h
    simpa only [Nat.cast_ite, Nat.cast_zero] using h
  calc ∑ k, what w (-(c * k)) * what w k
      = ∑ k, ∑ a, ∑ b, w a * w b * ZMod.stdAddChar (k * (a * c - b)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [what, what, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [show w a * ZMod.stdAddChar (-(a * -(c * k))) * (w b * ZMod.stdAddChar (-(b * k))) =
          w a * w b * (ZMod.stdAddChar (-(a * -(c * k))) * ZMod.stdAddChar (-(b * k))) by ring,
          ← AddChar.map_add_eq_mul]
        congr 2; ring
    _ = ∑ a, ∑ b, w a * w b * ∑ k, ZMod.stdAddChar (k * (a * c - b)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
    _ = q * ∑ a, w a * w (a * c) := by
        simp only [hs, sub_eq_zero, mul_ite, mul_zero]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, ite_true]
        ring

omit [DecidableEq (DirichletCharacter ℂ q)] in
/-- The three families of `S₂` are one sum. -/
lemma S2part_eq (W : Finset (DirichletCharacter ℂ q)) (ŵ : ZMod q → ℂ) :
    S2part W ŵ = 3 * ((q : ℂ) - 1) * ŵ 0 *
      ∑ x ∈ univ.erase 0, ∑ y ∈ univ.erase 0, ŵ x * ŵ y * RR W (-x * y⁻¹) := by
  set Φ := ∑ x ∈ univ.erase (0 : ZMod q), ∑ y ∈ univ.erase 0, ŵ x * ŵ y * RR W (-x * y⁻¹) with hΦ
  have f1 : ∑ k₂ ∈ univ.erase (0 : ZMod q), ∑ k₃ ∈ univ.erase 0, ŵ 0 * ŵ k₂ * ŵ k₃ * RR W (-k₂ * k₃⁻¹) = ŵ 0 * Φ := by
    rw [hΦ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  have f2 : ∑ k₁ ∈ univ.erase (0 : ZMod q), ∑ k₃ ∈ univ.erase 0, ŵ k₁ * ŵ 0 * ŵ k₃ * RR W (-k₁ * k₃⁻¹) = ŵ 0 * Φ := by
    rw [hΦ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  have f3 : ∑ k₁ ∈ univ.erase (0 : ZMod q), ∑ k₂ ∈ univ.erase 0, ŵ k₁ * ŵ k₂ * ŵ 0 * RR W (-k₁ * k₂⁻¹) = ŵ 0 * Φ := by
    rw [hΦ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  rw [S2part, f1, f2, f3]
  ring

omit [DecidableEq (DirichletCharacter ℂ q)] in
/-- Substituting `x = −cy`: `Σ_{x,y≠0} ŵ(x)ŵ(y)|R(−x/y)|² = Σ_{c≠0}|R(c)|² Σ_{y≠0} ŵ(−cy)ŵ(y)`. -/
lemma sum_xy_eq (W : Finset (DirichletCharacter ℂ q)) (ŵ : ZMod q → ℂ) :
    ∑ x ∈ univ.erase 0, ∑ y ∈ univ.erase 0, ŵ x * ŵ y * RR W (-x * y⁻¹) =
      ∑ c ∈ univ.erase 0, RR W c * ∑ y ∈ univ.erase 0, ŵ (-(c * y)) * ŵ y := by
  rw [Finset.sum_comm]
  have hy : ∀ y ∈ univ.erase (0 : ZMod q), ∑ x ∈ univ.erase 0, ŵ x * ŵ y * RR W (-x * y⁻¹) =
      ∑ c ∈ univ.erase 0, RR W c * (ŵ (-(c * y)) * ŵ y) := by
    intro y hy
    have hy0 : y ≠ 0 := Finset.ne_of_mem_erase hy
    refine Finset.sum_nbij' (fun x => -x * y⁻¹) (fun c => -(c * y)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
      exact Finset.mem_erase.2 ⟨mul_ne_zero (neg_ne_zero.2 hx0) (inv_ne_zero hy0), Finset.mem_univ _⟩
    · intro c hc
      have hc0 : c ≠ 0 := Finset.ne_of_mem_erase hc
      exact Finset.mem_erase.2 ⟨neg_ne_zero.2 (mul_ne_zero hc0 hy0), Finset.mem_univ _⟩
    · intro x _
      rw [show -(-x * y⁻¹ * y) = x * (y⁻¹ * y) by ring, inv_mul_cancel₀ hy0, mul_one]
    · intro c _
      rw [show -(-(c * y)) * y⁻¹ = c * (y * y⁻¹) by ring, mul_inv_cancel₀ hy0, mul_one]
    · intro x _
      rw [show -(-x * y⁻¹ * y) = x * (y⁻¹ * y) by ring, inv_mul_cancel₀ hy0, mul_one]
      ring
  rw [Finset.sum_congr rfl hy, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]

omit [DecidableEq (DirichletCharacter ℂ q)] in
/-- Moving two outer sums past two inner ones. -/
lemma swap22 {α β : Type*} {s : Finset α} {t : Finset β} (F : α → α → β → β → ℂ) :
    ∑ x ∈ s, ∑ y ∈ s, ∑ a ∈ t, ∑ b ∈ t, F x y a b = ∑ a ∈ t, ∑ b ∈ t, ∑ x ∈ s, ∑ y ∈ s, F x y a b := by
  calc ∑ x ∈ s, ∑ y ∈ s, ∑ a ∈ t, ∑ b ∈ t, F x y a b = ∑ x ∈ s, ∑ a ∈ t, ∑ y ∈ s, ∑ b ∈ t, F x y a b :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ a ∈ t, ∑ x ∈ s, ∑ y ∈ s, ∑ b ∈ t, F x y a b := Finset.sum_comm
    _ = ∑ a ∈ t, ∑ x ∈ s, ∑ b ∈ t, ∑ y ∈ s, F x y a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ a ∈ t, ∑ b ∈ t, ∑ x ∈ s, ∑ y ∈ s, F x y a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm

omit [DecidableEq (DirichletCharacter ℂ q)] in
/-- `Σ_{a,c} w(a)w(ac)|R(c)|² = Σ_{χ,χ′∈W} |G(χ,χ′)|²` for real weights. -/
lemma sum_w_RR (W : Finset (DirichletCharacter ℂ q)) (w : ZMod q → ℂ) (h0 : w 0 = 0)
    (hw : ∀ a, star (w a) = w a) :
    ∑ c, RR W c * ∑ a, w a * w (a * c) = ∑ χ ∈ W, ∑ χ' ∈ W, gramZ w χ χ' * star (gramZ w χ χ') := by
  have hRR : ∀ z : ZMod q, RR W z⁻¹ = RR W z := by
    intro z; rw [RR, RR, Rsum_inv, star_star, mul_comm]
  -- the right side as a double sum over residues
  have hB : ∑ χ ∈ W, ∑ χ' ∈ W, gramZ w χ χ' * star (gramZ w χ χ') =
      ∑ a, ∑ b, w a * w b * RR W (a * b⁻¹) := by
    calc ∑ χ ∈ W, ∑ χ' ∈ W, gramZ w χ χ' * star (gramZ w χ χ')
        = ∑ χ ∈ W, ∑ χ' ∈ W, ∑ a, ∑ b, w a * w b * (χ (a * b⁻¹) * star (χ' (a * b⁻¹))) := by
          refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun χ' _ => ?_
          rw [gramZ, star_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          simp only [star_mul', hw, star_apply_eq, map_mul, inv_inv]
          ring
      _ = ∑ a, ∑ b, ∑ χ ∈ W, ∑ χ' ∈ W, w a * w b * (χ (a * b⁻¹) * star (χ' (a * b⁻¹))) := swap22 _
      _ = ∑ a, ∑ b, w a * w b * ((∑ χ ∈ W, χ (a * b⁻¹)) * ∑ χ' ∈ W, star (χ' (a * b⁻¹))) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun χ _ => by rw [Finset.mul_sum]
      _ = ∑ a, ∑ b, w a * w b * RR W (a * b⁻¹) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [RR, Rsum, star_sum]
  -- the left side, with b = a c for a ≠ 0
  have hA : ∑ c, RR W c * ∑ a, w a * w (a * c) = ∑ a, ∑ b, w a * w b * RR W (a * b⁻¹) := by
    calc ∑ c, RR W c * ∑ a, w a * w (a * c) = ∑ a, w a * ∑ c, w (a * c) * RR W c := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
      _ = ∑ a, ∑ b, w a * w b * RR W (a * b⁻¹) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          by_cases ha : a = 0
          · subst ha; simp [h0]
          · have e := (Equiv.sum_comp (Equiv.mulLeft₀ a ha) (fun b => w a * w b * RR W (a * b⁻¹))).symm
            simp only [Equiv.mulLeft₀_apply] at e
            rw [e, Finset.mul_sum]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [show a * (a * c)⁻¹ = c⁻¹ by rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ ha, one_mul], hRR]
            ring
  rw [hA, hB]


/-- **The closed form of `S₂`**: for real residue weights with `w(0) = 0`,
`S₂ = 3(q − 1)ŵ(0)(q Σ_{χ,χ′∈W}|G(χ,χ′)|² − ŵ(0)²(q − 1)|W|)`. -/
theorem S2_closed (W : Finset (DirichletCharacter ℂ q)) (w : ZMod q → ℂ) (h0 : w 0 = 0)
    (hw : ∀ a, star (w a) = w a) :
    S2part W (what w) = 3 * ((q : ℂ) - 1) * what w 0 *
      (q * ∑ χ ∈ W, ∑ χ' ∈ W, gramZ w χ χ' * star (gramZ w χ χ') - what w 0 ^ 2 * ((q : ℂ) - 1) * W.card) := by
  rw [S2part_eq, sum_xy_eq]
  congr 1
  have hRR0 : RR W 0 = 0 := by simp [RR, Rsum_zero]
  have hy : ∀ c : ZMod q, ∑ y ∈ univ.erase 0, what w (-(c * y)) * what w y =
      q * ∑ a, w a * w (a * c) - what w 0 ^ 2 := by
    intro c
    rw [← sum_what_mul w c, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
    simp only [mul_zero, neg_zero]
    ring
  simp only [hy, mul_sub]
  rw [Finset.sum_sub_distrib]
  have e1 : ∑ c ∈ univ.erase (0 : ZMod q), RR W c * (q * ∑ a, w a * w (a * c)) =
      q * ∑ χ ∈ W, ∑ χ' ∈ W, gramZ w χ χ' * star (gramZ w χ χ') := by
    rw [← sum_w_RR W w h0 hw, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)), hRR0, zero_mul,
      zero_add, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have e2 : ∑ c ∈ univ.erase (0 : ZMod q), RR W c * what w 0 ^ 2 = what w 0 ^ 2 * (((q : ℂ) - 1) * W.card) := by
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    have h := sum_R_star_R W
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))] at h
    simp only [Rsum_zero, star_zero, mul_zero, zero_add] at h
    simpa only [RR] using h
  rw [e1, e2]
  ring

/-- The off-diagonal Frobenius norm `‖E‖_F² = Σ_{χ≠χ′∈W} |G(χ,χ′)|²` of the Gram matrix on `S`. -/
def offFrob (W : Finset (DirichletCharacter ℂ q)) (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ χ ∈ W, ∑ χ' ∈ W, if χ = χ' then 0 else ‖LinnikMoment.gram S c χ χ'‖ ^ 2

/-- **The socket for prime moduli at one point per character.** Under the hypotheses of round 538's
`large_values_lines`, if `‖E‖_F² ≤ A` (Chen–Gupta–Li's `S₂` bound) and `Re q⁻²S₃ ≤ B` (their `S₃` bound), then
`(|W|V² − N_cβ)³ ≤ β³(3N_c(A + |W|N_c²/q) + B)`. -/
theorem large_values_socket (W : Finset (DirichletCharacter ℂ q)) (S : Finset ℕ) (b c : ℕ → ℂ)
    (hS : ∀ n ∈ S, IsUnit (n : ZMod q)) {V : ℝ}
    (hV : ∀ χ ∈ W, V ^ 2 ≤ ‖∑ n ∈ S, c n * χ n * b n‖ ^ 2)
    (hge : (∑ n ∈ S, ‖c n‖ ^ 2) * (∑ n ∈ S, ‖b n‖ ^ 2) ≤ W.card * V ^ 2) {A B : ℝ}
    (hA : offFrob W S c ≤ A) (hB : ((q : ℂ)⁻¹ ^ 2 * S3part W (what (resW S c))).re ≤ B) :
    (W.card * V ^ 2 - (∑ n ∈ S, ‖c n‖ ^ 2) * (∑ n ∈ S, ‖b n‖ ^ 2)) ^ 3 ≤
      (∑ n ∈ S, ‖b n‖ ^ 2) ^ 3 *
        (3 * (∑ n ∈ S, ‖c n‖ ^ 2) * (A + W.card * (∑ n ∈ S, ‖c n‖ ^ 2) ^ 2 / q) + B) := by
  set Nc := ∑ n ∈ S, ‖c n‖ ^ 2 with hNc
  set β := ∑ n ∈ S, ‖b n‖ ^ 2 with hβ
  have key := large_values_split W S b c hS hV hge
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.out.pos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.out.one_lt.le
  have hNc0 : 0 ≤ Nc := Finset.sum_nonneg fun _ _ => by positivity
  have hβ0 : 0 ≤ β := Finset.sum_nonneg fun _ _ => by positivity
  -- the Frobenius norm of the Gram matrix: diagonal plus off-diagonal
  have hfrob : ∑ χ ∈ W, ∑ χ' ∈ W, gramZ (resW S c) χ χ' * star (gramZ (resW S c) χ χ') =
      ((W.card * Nc ^ 2 + offFrob W S c : ℝ) : ℂ) := by
    have e : ∀ χ χ' : DirichletCharacter ℂ q, gramZ (resW S c) χ χ' * star (gramZ (resW S c) χ χ') =
        (((if χ = χ' then Nc ^ 2 else 0) + (if χ = χ' then 0 else ‖LinnikMoment.gram S c χ χ'‖ ^ 2) : ℝ) : ℂ) := by
      intro χ χ'
      rw [← gram_eq_gramZ, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      split_ifs with h
      · subst h; rw [gram_self S c hS, ← hNc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hNc0]; simp
      · simp
    have e' : ∑ χ ∈ W, ∑ χ' ∈ W, gramZ (resW S c) χ χ' * star (gramZ (resW S c) χ χ') =
        ((∑ χ ∈ W, ∑ χ' ∈ W, ((if χ = χ' then Nc ^ 2 else 0) +
          (if χ = χ' then 0 else ‖LinnikMoment.gram S c χ χ'‖ ^ 2)) : ℝ) : ℂ) := by
      simp only [e]; push_cast; rfl
    rw [e']
    congr 1
    simp only [Finset.sum_add_distrib, offFrob]
    congr 1
    rw [Finset.sum_congr rfl fun χ hχ => Finset.sum_ite_eq W χ (fun _ => Nc ^ 2)]
    simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
  have hw0 := resW_zero S c hS
  have hwr : ∀ a : ZMod q, star (resW S c a) = resW S c a := by
    intro a; simp only [resW, star_sum, Complex.star_def, Complex.conj_ofReal]
  rw [S2_closed W (resW S c) hw0 hwr, what_resW_zero, ← hNc, hfrob] at key
  -- `q⁻²S₂` in real form
  have hS2 : ((q : ℂ)⁻¹ ^ 2 * (3 * ((q : ℂ) - 1) * (Nc : ℂ) * (q * ((W.card * Nc ^ 2 + offFrob W S c : ℝ) : ℂ) -
      (Nc : ℂ) ^ 2 * ((q : ℂ) - 1) * W.card) + S3part W (what (resW S c)))).re =
      3 * Nc * (1 - 1 / q) * (offFrob W S c + W.card * Nc ^ 2 / q) +
        ((q : ℂ)⁻¹ ^ 2 * S3part W (what (resW S c))).re := by
    have e : (q : ℂ)⁻¹ ^ 2 * (3 * ((q : ℂ) - 1) * (Nc : ℂ) * (q * ((W.card * Nc ^ 2 + offFrob W S c : ℝ) : ℂ) -
        (Nc : ℂ) ^ 2 * ((q : ℂ) - 1) * W.card) + S3part W (what (resW S c))) =
        ((3 * Nc * (1 - 1 / q) * (offFrob W S c + W.card * Nc ^ 2 / q) : ℝ) : ℂ) +
          (q : ℂ)⁻¹ ^ 2 * S3part W (what (resW S c)) := by
      have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
      push_cast
      field_simp
      ring
    rw [e, Complex.add_re, Complex.ofReal_re]
  rw [hS2] at key
  have hoff0 : 0 ≤ offFrob W S c := by
    unfold offFrob
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  have hfac : 0 ≤ 1 - 1 / (q : ℝ) ∧ 1 - 1 / (q : ℝ) ≤ 1 := by
    constructor
    · rw [sub_nonneg, div_le_one hq0]; exact hq1
    · have : 0 ≤ 1 / (q : ℝ) := by positivity
      linarith
  have hmain : 3 * Nc * (1 - 1 / q) * (offFrob W S c + W.card * Nc ^ 2 / q) ≤
      3 * Nc * (A + W.card * Nc ^ 2 / q) := by
    have h1 : offFrob W S c + W.card * Nc ^ 2 / q ≤ A + W.card * Nc ^ 2 / q := by linarith
    have h2 : 0 ≤ offFrob W S c + W.card * Nc ^ 2 / q := by positivity
    calc 3 * Nc * (1 - 1 / q) * (offFrob W S c + W.card * Nc ^ 2 / q)
        ≤ 3 * Nc * 1 * (offFrob W S c + W.card * Nc ^ 2 / q) := by gcongr; exact hfac.2
      _ ≤ 3 * Nc * (A + W.card * Nc ^ 2 / q) := by rw [mul_one]; gcongr
  calc (W.card * V ^ 2 - Nc * β) ^ 3
      ≤ β ^ 3 * (3 * Nc * (1 - 1 / q) * (offFrob W S c + W.card * Nc ^ 2 / q) +
          ((q : ℂ)⁻¹ ^ 2 * S3part W (what (resW S c))).re) := key
    _ ≤ β ^ 3 * (3 * Nc * (A + W.card * Nc ^ 2 / q) + B) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

end LinnikS2
