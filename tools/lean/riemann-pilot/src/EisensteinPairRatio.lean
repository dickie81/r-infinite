import EisensteinSecondPoisson

/-! # The paired factor through the ratio class, and Lemma 7.2 in one character (round 322)

S5c-5, part 1, in round 316's plan. Round 321's `Mq_rowcol` expands the twisted paired factor in
pairs `(ξ_a, ξ_b)` of characters modulo `4`, and its row factor `ā_{ξ_a}(w)a_{ξ_b}(w)` does not cancel
when `ξ_a ≠ ξ_b`. The companion paper expands `ξ_1(z)G(z^{-1})` in single characters
("`\xi_1(z)G(z^{-1})=\sum_{\xi'}c_{\xi'}\xi'(z)`"), through its (4.7),
"`\chi_a(-1)\overline{G(a)}G(b)\mathcal R(a,b)=G(ba^{-1})`". This file proves the pilot's form of (4.7)
and that expansion.

* **`Γ_quad` modulo `4`** (`gamQ`, `gaussTr_P2_coords`, `gamQ_coords`, `gamQ_congr`): round 297's
  `Γ_quad(c) = ½·Σ_{y mod 2} e(−cy²/4)` is `Φ(a, b)/2` for `c = a + bω`, so it depends only on `c mod 4`.
* **Squares** (`P2_mul_sq`, **`gamQ_mul_sq`**): `Γ_quad(cs²) = Γ_quad(c)` for `s` prime to `2`, since
  `P₂(cs², y) = P₂(c, sy)` and `y ↦ sy` permutes the residues modulo `2`. The paper: "Thus
  `Γ_quad(c)` depends only on `c mod 4𝒪` and is invariant under multiplication by a square in
  `(𝒪/4𝒪)^×`".
* `γ₃(n) = Γ_quad(n)` for `n = ∏_{P∈S} π_P` (`gamF_three_eq_gamQ`, from round 304's `gamF_three_eq`).
* **The ratio class** (`lift4`, `chi4Cls`, `pairG`, **`pairPsi_eq_pairG`**): for disjoint `C₁, C₂` and
  `w` with `cls4 C₁·w = cls4 C₂`, round 304's paired factor is `Ψ(C₁, C₂) = χ_w(4)·Γ_quad(w)`. Here
  `χ_w(4)` is `σ(u)` for the cube root of unity `u ≡ w (mod 2)` (round 304's `prod_chi6_four`), and
  `Γ_quad(c₁c₂) = Γ_quad(c₁²w) = Γ_quad(w)`.
* **Functions of one class** (`classCoeff`, `fun_eq_sum_mulChar`, `norm_classCoeff_le`): a function
  `h` of one unit class is `Σ_ξ ĉ(ξ)·ξ`, with `|ĉ| ≤ B` when `|h| ≤ B`.
* **The single expansion** (`pairH`, **`pairTerm_expandD`**, `pair_char_formD`, **`Mq_rowcolD`**):
  `pairH ξ₁ z = ξ₁(z)·χ_z(4)Γ_quad(z)` is the paper's `ξ_1(z)G(z^{-1})`: its `G(c)` is
  "`\overline{\chi_c(4)}\Gamma_{\rm quad}(c)`", and `Γ_quad(z⁻¹) = Γ_quad(z)` by `gamQ_mul_sq`. Round 321's
  identities hold with `Σ_ξ ĉ(ξ)·(…)(ξ, ξ)` in place of the sum over pairs, and `|ĉ| ≤ 2`
  (`norm_classCoeff_pairH_le`).
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-! ### `Γ_quad` modulo `4` -/

/-- The paper's `Γ_quad(c) = ½·Σ_{y mod 2} e(-cy²/4)` (round 297's `quad_gauss`). -/
def gamQ (c : 𝓞 K) : ℂ := gaussTr 2 (P2 c) 0 / 2

/-- `Σ_{y mod 2} P₂(c, y) = Φ(a, b)` for `c = a + bω` (the second half of round 297's
`quad_gauss_coords`). -/
theorem gaussTr_P2_coords (a b : ℤ) :
    gaussTr 2 (P2 ((a : 𝓞 K) + (b : 𝓞 K) * ω)) 0 = quadPhi a b := by
  rw [gaussTr_two _ (P2_periodic _),
    P2_coord _ 0 0 0 (by simp), P2_coord _ 1 a b (by ring),
    P2_coord _ ω (b - a) (-a)
      (by push_cast; linear_combination (a : 𝓞 K) * ω_sq_add + (b : 𝓞 K) * ω_cube),
    P2_coord _ (1 + ω) (-b) (a - b)
      (by push_cast; linear_combination ((a : 𝓞 K) + 2 * b) * ω_sq_add + (b : 𝓞 K) * ω_cube)]
  rw [neg_zero, zpow_zero, neg_neg, neg_sub]
  rfl

theorem gamQ_coords (a b : ℤ) : gamQ ((a : 𝓞 K) + (b : 𝓞 K) * ω) = quadPhi a b / 2 := by
  rw [gamQ, gaussTr_P2_coords]

/-- `Γ_quad` depends only on the class modulo `4`. -/
theorem gamQ_congr {c c' : 𝓞 K} (h : c - c' ∈ span {(4 : 𝓞 K)}) : gamQ c = gamQ c' := by
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨a, b, hab⟩ := exists_coords c'
  obtain ⟨a', b', hab'⟩ := exists_coords d
  have hc : c = ((a + 4 * a' : ℤ) : 𝓞 K) + ((b + 4 * b' : ℤ) : 𝓞 K) * ω := by
    have : c = c' + d * 4 := by rw [hd]; ring
    rw [this, hab, hab']; push_cast; ring
  rw [hc, hab, gamQ_coords, gamQ_coords, quadPhi_add_four]

theorem P2_mul_sq (c s μ : 𝓞 K) : P2 (c * s * s) μ = P2 c (s * μ) := by
  unfold P2 Rq
  rw [show c * s * s * μ * μ = c * (s * μ) * (s * μ) by ring]

theorem not_isUnit_two : ¬ IsUnit (2 : 𝓞 K) := fun h =>
  span_two_isMaximal.ne_top (Ideal.span_singleton_eq_top.2 h)

/-- **`Γ_quad` is invariant under squares prime to `2`**: `Γ_quad(cs²) = Γ_quad(c)`, since
`P₂(cs², y) = P₂(c, sy)` and `y ↦ sy` permutes the residues modulo `2`. -/
theorem gamQ_mul_sq (c s : 𝓞 K) (hs : IsCoprime s 2) : gamQ (c * s * s) = gamQ c := by
  unfold gamQ
  congr 1
  have hper : ∀ z u : 𝓞 K, P2 c (s * (z + 2 * u)) = P2 c (s * z) := fun z u => by
    rw [show s * (z + 2 * u) = s * z + 2 * (s * u) by ring, P2_periodic]
  have e1 : gaussTr 2 (P2 (c * s * s)) 0 = gaussTr 2 (fun μ => P2 c (s * μ)) 0 := by
    congr 1; funext μ; exact P2_mul_sq c s μ
  rw [e1, gaussTr_two _ hper, gaussTr_two _ (P2_periodic c)]
  obtain ⟨⟨q, v⟩, hq⟩ := rep2_bijective.2 s
  simp only at hq
  have hred : ∀ μ, P2 c (s * μ) = P2 c (rep2 q * μ) := fun μ => by
    rw [← hq, show (rep2 q + 2 * v) * μ = rep2 q * μ + 2 * (v * μ) by ring, P2_periodic]
  simp only [hred]
  have hP : ∀ x y z : 𝓞 K, x = y + 2 * z → P2 c x = P2 c y := fun x y z h => by
    rw [h, P2_periodic]
  obtain ⟨i, j⟩ := q
  fin_cases i <;> fin_cases j <;>
    simp only [rep2, Nat.cast_zero, Nat.cast_one, zero_mul, add_zero, zero_add, one_mul, mul_zero,
      mul_one] at hq ⊢
  · exfalso
    rw [← hq] at hs
    exact not_isUnit_two (isCoprime_self.1 (IsCoprime.of_mul_left_left hs))
  · rw [hP (ω * ω) (1 + ω) (-1 - ω) (by linear_combination ω_sq_add),
      hP (ω * (1 + ω)) 1 (-1) (by linear_combination ω_sq_add)]
    ring
  · rw [hP ((1 + ω) * ω) 1 (-1) (by linear_combination ω_sq_add),
      hP ((1 + ω) * (1 + ω)) ω 0 (by linear_combination ω_sq_add)]
    ring

/-- `γ₃(n) = Γ_quad(n)` for `n = ∏_{P∈S} π_P` (round 304's `gamF_three_eq`). -/
theorem gamF_three_eq_gamQ (S : Finset Pr) :
    gamF πP S (fun P => chiF πP h6Pr P ^ 3) = gamQ (∏ P ∈ S, πP P) := by
  obtain ⟨a, b, hab⟩ := exists_coords (∏ P ∈ S, πP P)
  rw [gamF_three_eq πP h6Pr S (hcopPr S) a b hab, hab, gamQ_coords]

/-! ### The paired factor as a function of the ratio class -/

/-- A representative of a class modulo `4`. -/
def lift4 (z : 𝓞 K ⧸ span {(4 : 𝓞 K)}) : 𝓞 K := (Ideal.Quotient.mk_surjective z).choose

theorem mk_lift4 (z : 𝓞 K ⧸ span {(4 : 𝓞 K)}) :
    Ideal.Quotient.mk (span {(4 : 𝓞 K)}) (lift4 z) = z :=
  (Ideal.Quotient.mk_surjective z).choose_spec

open Classical in
/-- The paper's `χ_z(4)` on classes modulo `4`: `σ(u)` for the cube root of unity `u ≡ z (mod 2)`
(round 304's `prod_chi6_four`), and `0` when there is none. -/
def chi4Cls (z : 𝓞 K ⧸ span {(4 : 𝓞 K)}) : ℂ :=
  if h : ∃ u : 𝓞 K, u ^ 3 = 1 ∧ Ideal.Quotient.mk (span {(2 : 𝓞 K)}) u =
      Ideal.Quotient.mk (span {(2 : 𝓞 K)}) (lift4 z) then σO h.choose else 0

/-- `χ_z(4)·Γ_quad(z)` on classes modulo `4`. -/
def pairG (z : 𝓞 K ⧸ span {(4 : 𝓞 K)}) : ℂ := chi4Cls z * gamQ (lift4 z)

theorem span_four_le_two {x : 𝓞 K} (hx : x ∈ span {(4 : 𝓞 K)}) : x ∈ span {(2 : 𝓞 K)} := by
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  exact Ideal.mem_span_singleton'.2 ⟨2 * d, by ring⟩

/-- **The paired factor through the ratio class** (the companion paper's (4.7),
"`χ_a(-1)\overline{G(a)}G(b)\mathcal R(a,b)=G(ba^{-1})`", in round 304's form): for disjoint `C₁, C₂`
and `w` with `cls4 C₁·w = cls4 C₂`, `Ψ(C₁, C₂) = χ_w(4)·Γ_quad(w)`. By round 304,
`Ψ(C₁, C₂) = χ_{c₁}(4)⁻¹χ_{c₂}(4)·γ₃(c₁c₂)`; `χ_c(4)` is a character of `c mod 2`, and
`γ₃(c₁c₂) = Γ_quad(c₁c₂) = Γ_quad(c₁²w) = Γ_quad(w)`. -/
theorem pairPsi_eq_pairG {C1 C2 : Finset Pr} (hd : Disjoint C1 C2)
    {w : 𝓞 K ⧸ span {(4 : 𝓞 K)}} (hw : cls4 C1 * w = cls4 C2) : pairPsi C1 C2 = pairG w := by
  set c1 := ∏ P ∈ C1, πP P with hc1
  set c2 := ∏ P ∈ C2, πP P with hc2
  set w' := lift4 w with hw'def
  have hw' : c1 * w' - c2 ∈ span {(4 : 𝓞 K)} := by
    rw [← Ideal.Quotient.eq, map_mul, hw'def, mk_lift4]; exact hw
  obtain ⟨u1, hu13, hu12, hu1⟩ := prod_chi6_four πP h6Pr C1 (fun P _ => (πP_spec P).1)
  obtain ⟨u2, hu23, hu22, hu2⟩ := prod_chi6_four πP h6Pr C2 (fun P _ => (πP_spec P).1)
  have hmk : Ideal.Quotient.mk (span {(2 : 𝓞 K)}) (u1 ^ 2 * u2) =
      Ideal.Quotient.mk (span {(2 : 𝓞 K)}) w' := by
    have e2 : Ideal.Quotient.mk (span {(2 : 𝓞 K)}) c2 =
        Ideal.Quotient.mk (span {(2 : 𝓞 K)}) (c1 * w') :=
      (Ideal.Quotient.eq.2 (span_four_le_two hw')).symm
    have e3 : Ideal.Quotient.mk (span {(2 : 𝓞 K)}) (u1 ^ 3) = 1 := by rw [hu13, map_one]
    rw [map_mul, map_pow, hu12, hu22, e2, map_mul, ← hu12, ← mul_assoc, ← pow_succ, ← map_pow, e3,
      one_mul]
  have hu3 : (u1 ^ 2 * u2) ^ 3 = 1 := by
    rw [mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hu13, hu23, one_pow, one_mul]
  have hex : ∃ u : 𝓞 K, u ^ 3 = 1 ∧ Ideal.Quotient.mk (span {(2 : 𝓞 K)}) u =
      Ideal.Quotient.mk (span {(2 : 𝓞 K)}) (lift4 w) := ⟨u1 ^ 2 * u2, hu3, hmk⟩
  have hchi : chi4Cls w = σO u1 ^ 2 * σO u2 := by
    unfold chi4Cls
    rw [dite_eq_left hex]
    obtain ⟨h3, hm⟩ := hex.choose_spec
    have : hex.choose = u1 ^ 2 * u2 :=
      cube_eq_of_mk_eq (span {(2 : 𝓞 K)}) three_not_mem_span_two h3 hu3 (hm.trans hmk.symm)
    rw [this, map_mul, map_pow]
  have hgam : gamF πP (C1 ∪ C2) (fun P => chiF πP h6Pr P ^ 3) = gamQ w' := by
    rw [gamF_three_eq_gamQ, Finset.prod_union hd]
    have hc : c1 * c2 - w' * c1 * c1 ∈ span {(4 : 𝓞 K)} := by
      have : c1 * c2 - w' * c1 * c1 = -(c1 * (c1 * w' - c2)) := by ring
      rw [this]; exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ hw')
    rw [gamQ_congr hc, gamQ_mul_sq w' c1
      (IsCoprime.prod_left fun P _ => isCoprime_two (πP P) (h6Pr P))]
  have hσ : σO u1 * σO u1 ^ 2 = 1 := by rw [← pow_succ', ← map_pow, hu13, map_one]
  have hinv : (σO u1)⁻¹ = σO u1 ^ 2 := inv_eq_of_mul_eq_one_right hσ
  unfold pairPsi pairG
  rw [hu1, hu2, hgam, hchi, hinv]

/-! ### Functions of one unit class through characters -/

section UnitExpand

variable {M : Type*} [CommMonoid M] [Finite M]

/-- The coefficients of a function of one unit class: `ĉ(ξ) = N⁻¹·Σ_c h(c)·ξ(c⁻¹)`. -/
def classCoeff [Fintype (MulChar M ℂ)] [Fintype Mˣ] (h : M → ℂ) (ξ : MulChar M ℂ) : ℂ :=
  (Fintype.card (MulChar M ℂ) : ℂ)⁻¹ * ∑ c : Mˣ, h c * ξ ((c⁻¹ : Mˣ) : M)

/-- **A function of one unit class is a sum of characters**: `h(x) = Σ_ξ ĉ(ξ)·ξ(x)` for a unit `x`. -/
theorem fun_eq_sum_mulChar [Fintype (MulChar M ℂ)] [Fintype Mˣ] (h : M → ℂ) (x : Mˣ) :
    h x = ∑ ξ : MulChar M ℂ, classCoeff h ξ * ξ x := by
  classical
  have h1 : h x = ∑ c : Mˣ, h c * (if (x : M) = c then (1 : ℂ) else 0) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro c _ hc
      rw [ite_eq_right (fun e => hc (Units.val_inj.1 e).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [h1]
  simp_rw [indicator_eq_sum_mulChar]
  unfold classCoeff
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun c _ => by ring

/-- `‖ĉ(ξ)‖ ≤ B` when `‖h‖ ≤ B` on unit classes. -/
theorem norm_classCoeff_le [Fintype (MulChar M ℂ)] [Fintype Mˣ] (h : M → ℂ) {B : ℝ}
    (hB : ∀ c : Mˣ, ‖h c‖ ≤ B) (ξ : MulChar M ℂ) : ‖classCoeff h ξ‖ ≤ B := by
  have : NeZero ((Monoid.exponent Mˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Fintype.card (MulChar M ℂ) = Fintype.card Mˣ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity M ℂ
  have hN : (0 : ℝ) < Fintype.card (MulChar M ℂ) := Nat.cast_pos.2 Fintype.card_pos
  have hv : ∀ c : Mˣ, ‖ξ ((c : Mˣ) : M)‖ = 1 := norm_mulChar_unit ξ
  unfold classCoeff
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (Fintype.card (MulChar M ℂ) : ℝ)⁻¹ * ‖∑ c : Mˣ, h c * ξ ((c⁻¹ : Mˣ) : M)‖
      ≤ (Fintype.card (MulChar M ℂ) : ℝ)⁻¹ * ∑ _c : Mˣ, B := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul, hv, mul_one]
        exact hB c
    _ = B := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hcard]
        field_simp

end UnitExpand

/-! ### The diagonal expansion of the twisted pair -/

/-- `ξ₁(z)·χ_z(4)Γ_quad(z)` on classes modulo `4`: the companion paper's `ξ_1(z)G(z^{-1})` of its
Lemma 7.2, with its `G(c) = \overline{\chi_c(4)}\Gamma_{\rm quad}(c)` at `c = z⁻¹`. -/
def pairH (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (z : 𝓞 K ⧸ span {(4 : 𝓞 K)}) : ℂ :=
  ξ1 z * pairG z

theorem norm_gamQ_le (c : 𝓞 K) : ‖gamQ c‖ ≤ 2 := by
  obtain ⟨a, b, rfl⟩ := exists_coords c
  have h1 : ∀ n : ℤ, ‖(I : ℂ) ^ n‖ = 1 := fun n => by rw [norm_zpow, Complex.norm_I, one_zpow]
  have h4 : ‖1 + I ^ (-b) + I ^ a + I ^ (b - a)‖ ≤ 4 := by
    calc ‖1 + I ^ (-b) + I ^ a + I ^ (b - a)‖
        ≤ ‖(1 : ℂ)‖ + ‖I ^ (-b)‖ + ‖I ^ a‖ + ‖I ^ (b - a)‖ := norm_add₄_le
      _ = 4 := by rw [h1, h1, h1, norm_one]; norm_num
  rw [gamQ_coords, quadPhi, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  linarith

theorem norm_chi4Cls_le (z : 𝓞 K ⧸ span {(4 : 𝓞 K)}) : ‖chi4Cls z‖ ≤ 1 := by
  classical
  unfold chi4Cls
  split_ifs with h
  · have h3 : ‖σO h.choose‖ ^ 3 = 1 := by
      rw [← norm_pow, ← map_pow, h.choose_spec.1, map_one, norm_one]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h3)
  · rw [norm_zero]; exact zero_le_one

theorem norm_pairH_le (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (z : 𝓞 K ⧸ span {(4 : 𝓞 K)}) :
    ‖pairH ξ1 z‖ ≤ 2 := by
  unfold pairH pairG
  rw [norm_mul, norm_mul]
  calc ‖ξ1 z‖ * (‖chi4Cls z‖ * ‖gamQ (lift4 z)‖) ≤ 1 * (1 * 2) :=
        mul_le_mul (norm_xi_le ξ1 z) (mul_le_mul (norm_chi4Cls_le z) (norm_gamQ_le _)
          (norm_nonneg _) zero_le_one) (by positivity) zero_le_one
    _ = 2 := by ring

/-- `|ĉ(ξ)| ≤ 2` for the coefficients of `pairH ξ₁`. -/
theorem norm_classCoeff_pairH_le (ξ1 ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) :
    ‖classCoeff (pairH ξ1) ξ‖ ≤ 2 :=
  norm_classCoeff_le _ (fun _ => norm_pairH_le ξ1 _) ξ

theorem xi_units_inv (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (x : (𝓞 K ⧸ span {(4 : 𝓞 K)})ˣ) :
    ξ ((x⁻¹ : (𝓞 K ⧸ span {(4 : 𝓞 K)})ˣ) : 𝓞 K ⧸ span {(4 : 𝓞 K)}) =
      (ξ (x : 𝓞 K ⧸ span {(4 : 𝓞 K)}))⁻¹ := map_units_inv ξ x

/-- **The twisted pair coefficients in one character** (the companion paper's
"`\mu(z_1)\mu(z_2)\xi_1(z_1)\overline{\xi_1(z_2)} \gamma(\overline{\chi_{z_1}}\chi_{z_2}) =\sum_{\xi'}c_{\xi'}a_{\xi'}(z_1)\overline{a_{\xi'}(z_2)}`",
in round 308's orientation): for disjoint `C₁, C₂`,
`ξ̄₁(C₁)ξ₁(C₂)·ā(C₁)a(C₂)Ψ(C₁, C₂) = Σ_ξ ĉ(ξ)·ā_ξ(C₁)a_ξ(C₂)`, with `ĉ` the coefficients of
`pairH ξ₁`. -/
theorem pairTerm_expandD (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {C1 C2 : Finset Pr}
    (hd : Disjoint C1 C2) :
    conj (ξ1 (cls4 C1)) * ξ1 (cls4 C2) *
        (conj (aF πP h6Pr C1) * aF πP h6Pr C2 * pairPsi C1 C2) =
      ∑ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        classCoeff (pairH ξ1) ξ * (conj (aXi ξ (idl C1)) * aXi ξ (idl C2)) := by
  set x := (isUnit_cls4 C1).unit
  set y := (isUnit_cls4 C2).unit
  have hx : (x : 𝓞 K ⧸ span {(4 : 𝓞 K)}) = cls4 C1 := IsUnit.unit_spec _
  have hy : (y : 𝓞 K ⧸ span {(4 : 𝓞 K)}) = cls4 C2 := IsUnit.unit_spec _
  have hz : cls4 C1 * ((x⁻¹ * y : (𝓞 K ⧸ span {(4 : 𝓞 K)})ˣ) : 𝓞 K ⧸ span {(4 : 𝓞 K)}) =
      cls4 C2 := by
    rw [← hx, ← hy, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  have hξ : ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
      ξ ((x⁻¹ * y : (𝓞 K ⧸ span {(4 : 𝓞 K)})ˣ) : 𝓞 K ⧸ span {(4 : 𝓞 K)}) =
        conj (ξ (cls4 C1)) * ξ (cls4 C2) := by
    intro ξ
    rw [Units.val_mul, map_mul, xi_units_inv, hx, hy, conj_xi_cls4, MulChar.inv_apply_eq_inv']
  rw [pairPsi_eq_pairG hd hz]
  have hexp := fun_eq_sum_mulChar (pairH ξ1) (x⁻¹ * y)
  have hP : conj (ξ1 (cls4 C1)) * ξ1 (cls4 C2) *
      (conj (aF πP h6Pr C1) * aF πP h6Pr C2 *
        pairG ((x⁻¹ * y : (𝓞 K ⧸ span {(4 : 𝓞 K)})ˣ) : 𝓞 K ⧸ span {(4 : 𝓞 K)})) =
      conj (aF πP h6Pr C1) * aF πP h6Pr C2 *
        pairH ξ1 ((x⁻¹ * y : (𝓞 K ⧸ span {(4 : 𝓞 K)})ˣ) : 𝓞 K ⧸ span {(4 : 𝓞 K)}) := by
    unfold pairH; rw [hξ]; ring
  rw [hP, hexp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [hξ, aXi_idl, aXi_idl, map_mul]
  ring

open Classical in
/-- **One pair of twisted Möbius columns after Poisson summation, in one character modulo `4`**
(`pair_char_formTw` with `pairTerm_expandD` in place of the double expansion). -/
theorem pair_char_formD (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (H : ℝ) (hH : 0 < H)
    {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {M Y : ℝ}
    (hY : 3 * R ^ 2 * M ^ 2 ≤ 4 * H * Y) {A1 A2 : Finset Pr} (h1 : nI A1 ≤ M) (h2 : nI A2 ≤ M) :
    conj (ξ1 (cls4 (A1 \ A2))) * ξ1 (cls4 (A2 \ A1)) *
      ((-1 : ℂ) ^ A1.card * (-1) ^ A2.card *
        ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ))) =
    (if A1 = A2 then ∑ T ∈ A1.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 else 0) +
      ∑ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, classCoeff (pairH ξ1) ξ *
        ∑ T ∈ (A1 ∩ A2).powerset, tauXi H ((eltsLe Y).erase 0) ξ ξ (A1 \ A2) (A2 \ A1) T := by
  rw [pairSum_clean H hH A1 A2, Finset.mul_sum]
  have hd : Disjoint (A1 \ A2) (A2 \ A1) := disjoint_sdiff_sdiff
  have hM0 : 0 ≤ M := le_trans zero_le_one ((one_le_nI A1).trans h1)
  have hsplit : ∀ T ∈ (A1 ∩ A2).powerset,
      conj (ξ1 (cls4 (A1 \ A2))) * ξ1 (cls4 (A2 \ A1)) *
        ((-1 : ℂ) ^ T.card * (kap H (A1 \ A2) (A2 \ A1) T : ℂ) *
          (conj (aF πP h6Pr (A1 \ A2)) * aF πP h6Pr (A2 \ A1) * pairPsi (A1 \ A2) (A2 \ A1)) *
          (chiS (A1 \ A2) (∏ P ∈ T, πP P) * conj (chiS (A2 \ A1) (∏ P ∈ T, πP P))) *
          ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
            dualW H (A1 \ A2) (A2 \ A1) T μ) =
      (if A1 = A2 then (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 else 0) +
        ∑ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, classCoeff (pairH ξ1) ξ *
          tauXi H ((eltsLe Y).erase 0) ξ ξ (A1 \ A2) (A2 \ A1) T := by
    intro T hT
    have hTs : T ⊆ A1 ∩ A2 := Finset.mem_powerset.1 hT
    have hYT : 3 * R ^ 2 * (nI (A1 \ A2) * nI (A2 \ A1) * nI T) ≤ 4 * H * Y := by
      have hle := nI_pair_le hTs
      have hMM : nI A1 * nI A2 ≤ M ^ 2 := by
        rw [sq]; exact mul_le_mul h1 h2 (le_trans zero_le_one (one_le_nI A2)) hM0
      nlinarith [sq_nonneg R]
    rw [tsum_mu_eq H hH hR0 hR _ _ _ hYT, mul_add, mul_add]
    congr 1
    · by_cases he : A1 = A2
      · have he' := sdiff_eq_empty_both.2 he
        rw [ite_eq_left he, ite_eq_left he', he'.1, he'.2]
        simp only [cls4_empty, map_one, aF_empty, pairPsi_empty, chiS_empty]
        ring
      · have hn : ¬(A1 \ A2 = ∅ ∧ A2 \ A1 = ∅) := fun h => he (sdiff_eq_empty_both.1 h)
        rw [ite_eq_right he, ite_eq_right hn, mul_zero, mul_zero]
    · have e : ∀ (x y s k P F S : ℂ), x * y * (s * k * P * F * S) = (x * y * P) * (s * k * F * S) :=
        fun x y s k P F S => by ring
      rw [e, pairTerm_expandD ξ1 hd, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      unfold tauXi eS
      ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  · split_ifs with he
    · subst he; rw [Finset.inter_self]
    · exact Finset.sum_eq_zero fun T _ => rfl
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.mul_sum]

open Classical in
/-- **The second mean square in row/column form, in one character modulo `4`** (the companion
paper's Lemma 7.2 before its regrouping, with its single expansion
"`\xi_1(z)G(z^{-1})=\sum_{\xi'}c_{\xi'}\xi'(z)`"): `Mq_rowcol` with `Σ_ξ ĉ(ξ)·Σ rcQ(ξ, ξ)` in place of
the sum over pairs of characters, `ĉ` the coefficients of `pairH ξ₁`. -/
theorem Mq_rowcolD (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U : ℝ → ℂ} {β L : ℝ} (hβ : 0 ≤ β)
    (hL : 0 < L) (hU : ∀ x, 2 * β < x → U x = 0) (b T V : Finset Pr) {Y : ℝ} (hY : 0 < Y)
    {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {Y2 : ℝ}
    (hY2 : 3 * R ^ 2 * (2 * β * ellS L b T V) ^ 2 ≤ 4 * Y * Y2) {U0 : Finset Pr}
    (hU0 : primesLe (2 * β * ellS L b T V) ⊆ U0) :
    ∑' y : 𝓞 K, Pcol ξ1 U β L b T V y * conj (Pcol ξ1 U β L b T V y) *
        Majorant.Phi (σO y / (Real.sqrt Y : ℂ)) =
      ∑ A ∈ fsLe (2 * β * ellS L b T V),
          wQ U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) A A *
            ∑ T2 ∈ A.powerset, (-1 : ℂ) ^ T2.card * (kap Y ∅ ∅ T2 : ℂ) * dualG 0 +
        ∑ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, classCoeff (pairH ξ1) ξ *
          ∑ b2 ∈ U0.powerset, ∑ T2 ∈ (U0 \ b2).powerset, ∑ V2 ∈ (U0 \ (b2 ∪ T2)).powerset,
            ∑ μ ∈ (eltsLe Y2).erase 0,
              ∑ M1 ∈ ((U0 \ (b2 ∪ T2)) \ V2).powerset, ∑ M2 ∈ ((U0 \ (b2 ∪ T2)) \ V2).powerset,
                rcQ U (ellS L b T V) Y (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) ξ ξ b2 T2 V2 μ M1 M2 := by
  set ℓ := ellS L b T V with hℓdef
  set c := eS b ^ 4 * eS T ^ 5 * eS V ^ 6 with hcdef
  set 𝒜 := fsLe (2 * β * ℓ) with h𝒜def
  have hℓ : 0 < ℓ := ellS_pos hL b T V
  have hΛ : 0 ≤ 2 * β * ℓ := by positivity
  rw [Mq_expand ξ1 U β L b T V hY]
  have hpair : ∀ A1 ∈ 𝒜, ∀ A2 ∈ 𝒜,
      alphaQ ξ1 U ℓ c A1 * conj (alphaQ ξ1 U ℓ c A2) *
        ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt Y : ℂ)) =
      (if A1 = A2 then wQ U ℓ c A1 A1 *
          ∑ T2 ∈ A1.powerset, (-1 : ℂ) ^ T2.card * (kap Y ∅ ∅ T2 : ℂ) * dualG 0 else 0) +
        ∑ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, classCoeff (pairH ξ1) ξ *
          (wQ U ℓ c A1 A2 * ∑ T2 ∈ (A1 ∩ A2).powerset,
            tauXi Y ((eltsLe Y2).erase 0) ξ ξ (A1 \ A2) (A2 \ A1) T2) := by
    intro A1 hA1 A2 hA2
    rw [alphaQ_pair]
    have e : ∀ (w x s S : ℂ), w * (x * s) * S = w * (x * (s * S)) := fun w x s S => by ring
    rw [e, pair_char_formD ξ1 Y hY hR0 hR hY2 (nI_le_of_mem_fsLe_real hΛ hA1)
      (nI_le_of_mem_fsLe_real hΛ hA2), mul_add]
    congr 1
    · split_ifs with he
      · subst he; rfl
      · rw [mul_zero]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      ring
  rw [Finset.sum_congr rfl fun A1 hA1 => Finset.sum_congr rfl fun A2 hA2 => hpair A1 hA1 A2 hA2]
  simp only [Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun A1 hA1 => ?_
    rw [Finset.sum_ite_eq, ite_eq_left hA1]
  · rw [Finset.sum_congr rfl fun A1 _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    simp_rw [← Finset.mul_sum]
    congr 1
    refine xi_chainQ U hℓ c _ ξ ξ U0 𝒜 (fun A hA => (subset_primesLe hA).trans hU0) ?_
    intro A _ hA
    refine hU _ ?_
    have := lt_nI_of_not_mem_fsLe hA
    rw [lt_div_iff₀ hℓ]; linarith

end Eis

end

#print axioms Eis.gaussTr_P2_coords
#print axioms Eis.gamQ_coords
#print axioms Eis.gamQ_congr
#print axioms Eis.P2_mul_sq
#print axioms Eis.not_isUnit_two
#print axioms Eis.gamQ_mul_sq
#print axioms Eis.gamF_three_eq_gamQ
#print axioms Eis.mk_lift4
#print axioms Eis.span_four_le_two
#print axioms Eis.pairPsi_eq_pairG
#print axioms Eis.fun_eq_sum_mulChar
#print axioms Eis.norm_classCoeff_le
#print axioms Eis.norm_gamQ_le
#print axioms Eis.norm_chi4Cls_le
#print axioms Eis.norm_pairH_le
#print axioms Eis.norm_classCoeff_pairH_le
#print axioms Eis.xi_units_inv
#print axioms Eis.pairTerm_expandD
#print axioms Eis.pair_char_formD
#print axioms Eis.Mq_rowcolD
