/-
# Round 609: curves of counts glued from pieces, and their windows checked at the corners

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

`SieveTypeIIGen.typeII_gen` takes a curve `g` with `CurveCounts g` and `WindowOK g L m₁ m₂`. A curve made of many
constant pieces `A_i(1 − σ)` (a staircase above a density curve) is glued here piece by piece.

*  `RangeCounts g lo hi`: the counts of `g` on `lo ≤ σ ≤ hi` (`CurveCounts` restricted to a range).
*  `rangeCounts_of_density`: a density estimate `C(qT)^{A(1−σ)}(log qT)^{10}` on `[lo, hi]` gives
  `RangeCounts (fun σ => A(1 − σ)) lo hi`.
*  `rangeCounts_trivial`: at most `q ≤ qT` characters: `RangeCounts (fun _ => 1) lo hi` for `lo ≥ 1/2`.
*  `rangeCounts_glue`: `RangeCounts g lo mid` and `RangeCounts g' mid hi` give
  `RangeCounts (fun σ => if σ < mid then g σ else g' σ) lo hi`.
*  `curveCounts_of_range`: `RangeCounts g (1/2) 1` is `CurveCounts g`.
*  `WindowPiece g L m₁ m₂ lo hi`: the two inequalities of `WindowOK` for `lo ≤ β ≤ hi`; `windowPiece_glue` glues two
  pieces across an `if`; `windowOK_of_piece`: a piece on `[1/2, 11/12]` is `WindowOK`.
*  `windowPiece_affine` (and its forms `windowPiece_const` for `A(1 − β)` and `windowPiece_one` for `1`): for
  `g β = p − Aβ` on `[lo, hi]` (`A(1 − β)` is `p = A`; the trivial piece `1` is `p = 1`, `A = 0`), with `lo ≤ hi` and
  `m₁ ≤ m₂`, the inequalities at the corners `β ∈ {lo, hi}`, `m ∈ {m₁, 1, m₂}` (each where it lies in the range of its
  inequality) and `w ∈ {0, 4·10⁻⁶}` give the piece: on each range of `m` the exponent is affine in `w`, in `β` and in
  `m` separately, so it is at most its values at the corners of the box.

The file imports `SieveTypeIIGen.lean`.
-/
import SieveTypeIIGen

open Complex Real Finset

noncomputable section

namespace SieveCurveGlue

open DirichletCharacter SieveTypeIIGen

open scoped Classical in
/-- **The counts of a curve on a range**: there is `C ≥ 0` such that for every `q ≥ 1`, `lo ≤ σ ≤ hi` and `T ≥ 2` at
most `C(qT)^{g(σ)}(1 + log qT)^{10}` characters mod `q` have a zero with `Re s ≥ σ` and `|Im s| ≤ T`. -/
def RangeCounts (g : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), lo ≤ σ → σ ≤ hi → 2 ≤ T →
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
        C * ((q : ℝ) * T) ^ g σ * (1 + Real.log ((q : ℝ) * T)) ^ 10

theorem curveCounts_of_range {g : ℝ → ℝ} (h : RangeCounts g (1 / 2) 1) : CurveCounts g := h

open scoped Classical in
/-- A density estimate on `[lo, hi]` with the exponent `A(1 − σ)` and `(log qT)^{10}` gives the counts of
`σ ↦ A(1 − σ)` there. -/
theorem rangeCounts_of_density {A lo hi : ℝ}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), lo ≤ σ → σ ≤ hi → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ (A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ)) :
    RangeCounts (fun σ => A * (1 - σ)) lo hi := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : 2 ≤ (q : ℝ) * T := by nlinarith
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by linarith)
  have hlog : Real.log ((q : ℝ) * T) ^ (10 : ℝ) ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ hl (by linarith) 10
  have hP : 0 ≤ ((q : ℝ) * T) ^ (A * (1 - σ)) := Real.rpow_nonneg (by linarith) _
  calc _ ≤ C * ((q : ℝ) * T) ^ (A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := hC q σ T hσ hσ1 hT
    _ ≤ C * ((q : ℝ) * T) ^ (A * (1 - σ)) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by gcongr

open scoped Classical in
/-- The trivial count: at most `q ≤ qT = (qT)^1` characters, on any range. -/
theorem rangeCounts_trivial (lo hi : ℝ) : RangeCounts (fun _ => 1) lo hi := by
  refine ⟨1, zero_le_one, fun q _ σ T _ _ hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  have hl1 : 1 ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := one_le_pow₀ (by linarith)
  have hc := LinnikDensity.card_chars_le (q := q) (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
    ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)
  rw [Real.rpow_one]
  calc _ ≤ (q : ℝ) := hc
    _ ≤ 1 * ((q : ℝ) * T) * 1 := by nlinarith
    _ ≤ 1 * ((q : ℝ) * T) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by gcongr

open scoped Classical in
/-- **Gluing two ranges**: counts for `g` on `[lo, mid]` and for `g'` on `[mid, hi]` give counts for the curve that is
`g` below `mid` and `g'` from `mid` on, on `[lo, hi]`. -/
theorem rangeCounts_glue {g g' : ℝ → ℝ} {lo mid hi : ℝ} (h₁ : RangeCounts g lo mid) (h₂ : RangeCounts g' mid hi) :
    RangeCounts (fun σ => if σ < mid then g σ else g' σ) lo hi := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  have hl1 : 0 ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := by positivity
  by_cases hm : σ < mid
  · simp only [hm, ite_true]
    have hP : 0 ≤ ((q : ℝ) * T) ^ g σ := Real.rpow_nonneg (by nlinarith) _
    calc _ ≤ C₁ * ((q : ℝ) * T) ^ g σ * (1 + Real.log ((q : ℝ) * T)) ^ 10 := hC₁ q σ T hσ hm.le hT
      _ ≤ max C₁ C₂ * ((q : ℝ) * T) ^ g σ * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          gcongr; exact le_max_left _ _
  · simp only [hm, ite_false]
    have hP : 0 ≤ ((q : ℝ) * T) ^ g' σ := Real.rpow_nonneg (by nlinarith) _
    calc _ ≤ C₂ * ((q : ℝ) * T) ^ g' σ * (1 + Real.log ((q : ℝ) * T)) ^ 10 :=
          hC₂ q σ T (not_lt.1 hm) hσ1 hT
      _ ≤ max C₁ C₂ * ((q : ℝ) * T) ^ g' σ * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          gcongr; exact le_max_right _ _

/-- **The window's inequalities on a range of `β`**: `WindowOK g L m₁ m₂` restricted to `lo ≤ β ≤ hi`. -/
def WindowPiece (g : ℝ → ℝ) (L m₁ m₂ lo hi : ℝ) : Prop :=
  ∀ β m w : ℝ, lo ≤ β → β ≤ hi → m₁ ≤ m → m ≤ m₂ → 0 ≤ w → w ≤ 4 / 10 ^ 6 →
    (m ≤ 1 → (L - m) * (β + w) + g β / 2 + (1 + m) / 2 ≤ L - 1 / 25000) ∧
    (1 ≤ m → (L - m) * (β + w) + g β / 2 + m ≤ L - 1 / 25000)

theorem windowOK_of_piece {g : ℝ → ℝ} {L m₁ m₂ : ℝ} (h : WindowPiece g L m₁ m₂ (1 / 2) (11 / 12)) :
    WindowOK g L m₁ m₂ := h

/-- Gluing two pieces across `mid`. -/
theorem windowPiece_glue {g g' : ℝ → ℝ} {L m₁ m₂ lo mid hi : ℝ} (h₁ : WindowPiece g L m₁ m₂ lo mid)
    (h₂ : WindowPiece g' L m₁ m₂ mid hi) :
    WindowPiece (fun β => if β < mid then g β else g' β) L m₁ m₂ lo hi := by
  intro β m w hβ hβ1 hm hm1 hw hw1
  by_cases hb : β < mid
  · simp only [hb, ite_true]; exact h₁ β m w hβ hb.le hm hm1 hw hw1
  · simp only [hb, ite_false]; exact h₂ β m w (not_lt.1 hb) hβ1 hm hm1 hw hw1

/-- **A piece with an affine exponent `g β = p − Aβ`** (`A(1 − β)` is `p = A`; the trivial piece is `p = 1`, `A = 0`):
for `lo ≤ hi` and `m₁ ≤ m₂`, the corner inequalities give the piece. For the inequality with `m ≤ 1` the corners are
`β ∈ {lo, hi}`, `m ∈ {m₁, 1, m₂}` where the corner is at most `1`, `w ∈ {0, 4·10⁻⁶}`; for the one with `m ≥ 1` the
corners `m` are those at least `1`. On each range of `m` the exponent is affine in `w`, in `β` and in `m` separately,
so it is at most its values at the corners of the box. -/
theorem windowPiece_affine {p A L m₁ m₂ lo hi : ℝ} (hlo : lo ≤ hi) (hm : m₁ ≤ m₂)
    (hL1 : ∀ β m w, (β = lo ∨ β = hi) → ((m = m₁ ∧ m₁ ≤ 1) ∨ (m = 1 ∧ m₁ ≤ 1 ∧ 1 ≤ m₂) ∨ (m = m₂ ∧ m₂ ≤ 1)) →
      (w = 0 ∨ w = 4 / 10 ^ 6) → (L - m) * (β + w) + (p - A * β) / 2 + (1 + m) / 2 ≤ L - 1 / 25000)
    (hL2 : ∀ β m w, (β = lo ∨ β = hi) → ((m = m₁ ∧ 1 ≤ m₁) ∨ (m = 1 ∧ m₁ ≤ 1 ∧ 1 ≤ m₂) ∨ (m = m₂ ∧ 1 ≤ m₂)) →
      (w = 0 ∨ w = 4 / 10 ^ 6) → (L - m) * (β + w) + (p - A * β) / 2 + m ≤ L - 1 / 25000) :
    WindowPiece (fun β => p - A * β) L m₁ m₂ lo hi := by
  intro β m w hβ hβ1 hm1 hm2 hw hw1
  -- `F(β, m, w) = (L − m)(β + w) + (p − Aβ)/2 + t(m)` is affine in `w`, in `β`, and in `m` for each affine `t`;
  -- a function affine in each variable separately is at most its maximum over the corners of a box.
  have key : ∀ (t₀ t₁ : ℝ) (ma mb : ℝ), ma ≤ m → m ≤ mb →
      (∀ β' m' w', (β' = lo ∨ β' = hi) → (m' = ma ∨ m' = mb) → (w' = 0 ∨ w' = 4 / 10 ^ 6) →
        (L - m') * (β' + w') + (p - A * β') / 2 + (t₀ + t₁ * m') ≤ L - 1 / 25000) →
      (L - m) * (β + w) + (p - A * β) / 2 + (t₀ + t₁ * m) ≤ L - 1 / 25000 := by
    intro t₀ t₁ ma mb hma hmb hc
    -- interpolate in `w`, then in `β`, then in `m`
    have hw' : ∀ β' m', (β' = lo ∨ β' = hi) → (m' = ma ∨ m' = mb) →
        (L - m') * (β' + w) + (p - A * β') / 2 + (t₀ + t₁ * m') ≤ L - 1 / 25000 := by
      intro β' m' hb' hm'
      have h0 := hc β' m' 0 hb' hm' (Or.inl rfl)
      have h1 := hc β' m' (4 / 10 ^ 6) hb' hm' (Or.inr rfl)
      -- affine in `w`: the value at `w` is a convex combination of the values at `0` and `4/10^6`
      have hθ : (L - m') * (β' + w) + (p - A * β') / 2 + (t₀ + t₁ * m') =
          (1 - w / (4 / 10 ^ 6)) * ((L - m') * (β' + 0) + (p - A * β') / 2 + (t₀ + t₁ * m')) +
          (w / (4 / 10 ^ 6)) * ((L - m') * (β' + 4 / 10 ^ 6) + (p - A * β') / 2 + (t₀ + t₁ * m')) := by
        field_simp; ring
      have hθ0 : 0 ≤ w / (4 / 10 ^ 6) := by positivity
      have hθ1 : w / (4 / 10 ^ 6) ≤ 1 := by rw [div_le_one (by norm_num)]; exact hw1
      rw [hθ]
      nlinarith [mul_le_mul_of_nonneg_left h0 (by linarith : 0 ≤ 1 - w / (4 / 10 ^ 6)),
        mul_le_mul_of_nonneg_left h1 hθ0]
    have hβ' : ∀ m', (m' = ma ∨ m' = mb) →
        (L - m') * (β + w) + (p - A * β) / 2 + (t₀ + t₁ * m') ≤ L - 1 / 25000 := by
      intro m' hm'
      have h0 := hw' lo m' (Or.inl rfl) hm'
      have h1 := hw' hi m' (Or.inr rfl) hm'
      rcases eq_or_lt_of_le hlo with heq | hlt
      · subst heq
        have : β = lo := le_antisymm hβ1 hβ
        subst this; exact h0
      · have hθ : (L - m') * (β + w) + (p - A * β) / 2 + (t₀ + t₁ * m') =
            ((hi - β) / (hi - lo)) * ((L - m') * (lo + w) + (p - A * lo) / 2 + (t₀ + t₁ * m')) +
            ((β - lo) / (hi - lo)) * ((L - m') * (hi + w) + (p - A * hi) / 2 + (t₀ + t₁ * m')) := by
          field_simp; ring
        have hθ0 : 0 ≤ (hi - β) / (hi - lo) := div_nonneg (by linarith) (by linarith)
        have hθ1 : 0 ≤ (β - lo) / (hi - lo) := div_nonneg (by linarith) (by linarith)
        have hsum : (hi - β) / (hi - lo) + (β - lo) / (hi - lo) = 1 := by
          field_simp; ring
        rw [hθ]
        nlinarith [mul_le_mul_of_nonneg_left h0 hθ0, mul_le_mul_of_nonneg_left h1 hθ1]
    have h0 := hβ' ma (Or.inl rfl)
    have h1 := hβ' mb (Or.inr rfl)
    rcases eq_or_lt_of_le (hma.trans hmb) with heq | hlt
    · have : m = ma := le_antisymm (heq ▸ hmb) hma
      subst this; exact h0
    · have hθ : (L - m) * (β + w) + (p - A * β) / 2 + (t₀ + t₁ * m) =
          ((mb - m) / (mb - ma)) * ((L - ma) * (β + w) + (p - A * β) / 2 + (t₀ + t₁ * ma)) +
          ((m - ma) / (mb - ma)) * ((L - mb) * (β + w) + (p - A * β) / 2 + (t₀ + t₁ * mb)) := by
        field_simp; ring
      have hθ0 : 0 ≤ (mb - m) / (mb - ma) := div_nonneg (by linarith) (by linarith)
      have hθ1 : 0 ≤ (m - ma) / (mb - ma) := div_nonneg (by linarith) (by linarith)
      rw [hθ]
      nlinarith [mul_le_mul_of_nonneg_left h0 hθ0, mul_le_mul_of_nonneg_left h1 hθ1]
  constructor
  · intro hm1'
    -- `m ∈ [m₁, min 1 m₂]`; corners `m₁` and `min 1 m₂`
    have hmin : m ≤ min 1 m₂ := le_min hm1' hm2
    have := key (1 / 2) (1 / 2) m₁ (min 1 m₂) hm1 hmin (by
      intro β' m' w' hb' hm' hw'
      rcases hm' with rfl | rfl
      · have := hL1 β' m' w' hb' (Or.inl ⟨rfl, hm1.trans hm1'⟩) hw'; linarith
      · rcases le_total 1 m₂ with h12 | h12
        · rw [min_eq_left h12]
          have := hL1 β' 1 w' hb' (Or.inr (Or.inl ⟨rfl, hm1.trans hm1', h12⟩)) hw'; linarith
        · rw [min_eq_right h12]
          have := hL1 β' m₂ w' hb' (Or.inr (Or.inr ⟨rfl, h12⟩)) hw'; linarith)
    linarith
  · intro hm1'
    have hmax : max m₁ 1 ≤ m := max_le hm1 hm1'
    have := key 0 1 (max m₁ 1) m₂ hmax hm2 (by
      intro β' m' w' hb' hm' hw'
      rcases hm' with rfl | rfl
      · rcases le_total 1 m₁ with h11 | h11
        · rw [max_eq_left h11]
          have := hL2 β' m₁ w' hb' (Or.inl ⟨rfl, h11⟩) hw'; linarith
        · rw [max_eq_right h11]
          have := hL2 β' 1 w' hb' (Or.inr (Or.inl ⟨rfl, h11, hm1'.trans hm2⟩)) hw'; linarith
      · have := hL2 β' m' w' hb' (Or.inr (Or.inr ⟨rfl, hm1'.trans hm2⟩)) hw'; linarith)
    linarith

/-- `WindowPiece` for a curve equal to another pointwise. -/
theorem windowPiece_congr {g g' : ℝ → ℝ} {L m₁ m₂ lo hi : ℝ} (hg : ∀ β, g β = g' β)
    (h : WindowPiece g L m₁ m₂ lo hi) : WindowPiece g' L m₁ m₂ lo hi := by
  have : g' = g := funext fun β => (hg β).symm
  rw [this]; exact h

/-- The piece `g β = A(1 − β)`: `windowPiece_affine` at `p = A`. -/
theorem windowPiece_const {A L m₁ m₂ lo hi : ℝ} (hlo : lo ≤ hi) (hm : m₁ ≤ m₂)
    (hL1 : ∀ β m w, (β = lo ∨ β = hi) → ((m = m₁ ∧ m₁ ≤ 1) ∨ (m = 1 ∧ m₁ ≤ 1 ∧ 1 ≤ m₂) ∨ (m = m₂ ∧ m₂ ≤ 1)) →
      (w = 0 ∨ w = 4 / 10 ^ 6) → (L - m) * (β + w) + (A - A * β) / 2 + (1 + m) / 2 ≤ L - 1 / 25000)
    (hL2 : ∀ β m w, (β = lo ∨ β = hi) → ((m = m₁ ∧ 1 ≤ m₁) ∨ (m = 1 ∧ m₁ ≤ 1 ∧ 1 ≤ m₂) ∨ (m = m₂ ∧ 1 ≤ m₂)) →
      (w = 0 ∨ w = 4 / 10 ^ 6) → (L - m) * (β + w) + (A - A * β) / 2 + m ≤ L - 1 / 25000) :
    WindowPiece (fun β => A * (1 - β)) L m₁ m₂ lo hi :=
  windowPiece_congr (fun β => by ring) (windowPiece_affine hlo hm hL1 hL2)

/-- The trivial piece `g β = 1`: `windowPiece_affine` at `p = 1`, `A = 0`. -/
theorem windowPiece_one {L m₁ m₂ lo hi : ℝ} (hlo : lo ≤ hi) (hm : m₁ ≤ m₂)
    (hL1 : ∀ β m w, (β = lo ∨ β = hi) → ((m = m₁ ∧ m₁ ≤ 1) ∨ (m = 1 ∧ m₁ ≤ 1 ∧ 1 ≤ m₂) ∨ (m = m₂ ∧ m₂ ≤ 1)) →
      (w = 0 ∨ w = 4 / 10 ^ 6) → (L - m) * (β + w) + (1 - 0 * β) / 2 + (1 + m) / 2 ≤ L - 1 / 25000)
    (hL2 : ∀ β m w, (β = lo ∨ β = hi) → ((m = m₁ ∧ 1 ≤ m₁) ∨ (m = 1 ∧ m₁ ≤ 1 ∧ 1 ≤ m₂) ∨ (m = m₂ ∧ 1 ≤ m₂)) →
      (w = 0 ∨ w = 4 / 10 ^ 6) → (L - m) * (β + w) + (1 - 0 * β) / 2 + m ≤ L - 1 / 25000) :
    WindowPiece (fun _ => (1 : ℝ)) L m₁ m₂ lo hi :=
  windowPiece_congr (fun β => by ring) (windowPiece_affine hlo hm hL1 hL2)

end SieveCurveGlue
