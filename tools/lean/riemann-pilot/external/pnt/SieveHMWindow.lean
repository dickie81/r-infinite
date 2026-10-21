/-
# Round 621: the window condition with the Halász–Montgomery branch

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

`WindowOKHM g L m₁ m₂ d e`: for every `β`, `m`, `w` of the window, either `WindowOK`'s inequality (the orthogonality
branch) or, for `m ≤ 1`, the Halász–Montgomery branch: both
`(L − m)(β + w) + g β/2 + m/2 + m/2 ≤ L − 1/25000` (the `|R|Λ` term) and
`(L − m)(β + w) + g β/2 + m/2 + (g β + b)/2 ≤ L − 1/25000` with `b = 5/12 + m/12 + d(1 − m) + 2e` (the `|R|²B` term).
Pieces (`WindowPieceHM`) glue as `WindowPiece` does; a piece that holds by orthogonality lifts; an affine piece holds
by the Halász–Montgomery branch if both its bilinear inequalities hold at the corners of the box.
`windowPieceHM_congr` and `windowPieceHM_const_split` (the piece `A(1 − β)`, as `windowPiece_const`) let an affine
piece stand for a curve's step written `A(1 − σ)`.

The file imports `SieveCurveGlue.lean`.
-/
import SieveCurveGlue

namespace SieveCurveGlue

/-- The Halász–Montgomery branch's exponent bound at `(β, m, w)` for a curve value `gβ`: the larger of the two
bilinear terms. -/
def hmBound (L d e gβ β m w : ℝ) : Prop :=
  (L - m) * (β + w) + gβ / 2 + m / 2 + m / 2 ≤ L - 1 / 25000 ∧
  (L - m) * (β + w) + gβ / 2 + m / 2 + (gβ + (5 / 12 + m / 12 + d * (1 - m) + 2 * e)) / 2 ≤ L - 1 / 25000

/-- **The window's exponents with the Halász–Montgomery branch**: for `1/2 ≤ β ≤ 11/12`, `m₁ ≤ m ≤ m₂`,
`0 ≤ w ≤ 4·10⁻⁶`: either `WindowOK`'s inequality for that `m`, or `m ≤ 1` and `hmBound`. -/
def WindowOKHM (g : ℝ → ℝ) (L m₁ m₂ d e : ℝ) : Prop :=
  ∀ β m w : ℝ, 1 / 2 ≤ β → β ≤ 11 / 12 → m₁ ≤ m → m ≤ m₂ → 0 ≤ w → w ≤ 4 / 10 ^ 6 →
    ((m ≤ 1 → (L - m) * (β + w) + g β / 2 + (1 + m) / 2 ≤ L - 1 / 25000) ∧
      (1 ≤ m → (L - m) * (β + w) + g β / 2 + m ≤ L - 1 / 25000)) ∨
    (m ≤ 1 ∧ hmBound L d e (g β) β m w)

/-- The same on a range `lo ≤ β ≤ hi`. -/
def WindowPieceHM (g : ℝ → ℝ) (L m₁ m₂ d e lo hi : ℝ) : Prop :=
  ∀ β m w : ℝ, lo ≤ β → β ≤ hi → m₁ ≤ m → m ≤ m₂ → 0 ≤ w → w ≤ 4 / 10 ^ 6 →
    ((m ≤ 1 → (L - m) * (β + w) + g β / 2 + (1 + m) / 2 ≤ L - 1 / 25000) ∧
      (1 ≤ m → (L - m) * (β + w) + g β / 2 + m ≤ L - 1 / 25000)) ∨
    (m ≤ 1 ∧ hmBound L d e (g β) β m w)

/-- A piece on `[1/2, 11/12]` (`h`) is the window condition. -/
theorem windowOKHM_of_piece {g : ℝ → ℝ} {L m₁ m₂ d e : ℝ} (h : WindowPieceHM g L m₁ m₂ d e (1 / 2) (11 / 12)) :
    WindowOKHM g L m₁ m₂ d e := h

/-- A piece that holds by orthogonality holds. -/
theorem windowPieceHM_of_piece {g : ℝ → ℝ} {L m₁ m₂ d e lo hi : ℝ} (h : WindowPiece g L m₁ m₂ lo hi) :
    WindowPieceHM g L m₁ m₂ d e lo hi :=
  fun β m w hβ hβ1 hm hm1 hw hw1 => Or.inl (h β m w hβ hβ1 hm hm1 hw hw1)

/-- Gluing two pieces across `mid`, as `windowPiece_glue`. -/
theorem windowPieceHM_glue {g g' : ℝ → ℝ} {L m₁ m₂ d e lo mid hi : ℝ} (h₁ : WindowPieceHM g L m₁ m₂ d e lo mid)
    (h₂ : WindowPieceHM g' L m₁ m₂ d e mid hi) :
    WindowPieceHM (fun β => if β < mid then g β else g' β) L m₁ m₂ d e lo hi := by
  intro β m w hβ hβ1 hm hm1 hw hw1
  by_cases hb : β < mid
  · simp only [hb, ite_true]; exact h₁ β m w hβ hb.le hm hm1 hw hw1
  · simp only [hb, ite_false]; exact h₂ β m w (not_lt.1 hb) hβ1 hm hm1 hw hw1

/-- **A function affine in each of `w`, `β`, `m` separately is at most its maximum over the corners of a box**:
`F(β, m, w) = (L − m)(β + w) + (p − Aβ)/2 + (t₀ + t₁m)` on `[lo, hi] × [ma, mb] × [0, 4·10⁻⁶]`
(the `key` of `SieveCurveGlue.windowPiece_affine`, as a lemma): `lo ≤ hi` (`hlo`), the point in the box (`hβ`,
`hβ1`, `hma`, `hmb`, `hw`, `hw1`) and the bound at the corners (`hc`). -/
theorem affine_corner_bound {p A L lo hi ma mb t₀ t₁ β m w : ℝ} (hlo : lo ≤ hi) (hβ : lo ≤ β) (hβ1 : β ≤ hi)
    (hma : ma ≤ m) (hmb : m ≤ mb) (hw : 0 ≤ w) (hw1 : w ≤ 4 / 10 ^ 6)
    (hc : ∀ β' m' w', (β' = lo ∨ β' = hi) → (m' = ma ∨ m' = mb) → (w' = 0 ∨ w' = 4 / 10 ^ 6) →
      (L - m') * (β' + w') + (p - A * β') / 2 + (t₀ + t₁ * m') ≤ L - 1 / 25000) :
    (L - m) * (β + w) + (p - A * β) / 2 + (t₀ + t₁ * m) ≤ L - 1 / 25000 := by
  -- interpolate in `w`, then in `β`, then in `m`
  have hw' : ∀ β' m', (β' = lo ∨ β' = hi) → (m' = ma ∨ m' = mb) →
      (L - m') * (β' + w) + (p - A * β') / 2 + (t₀ + t₁ * m') ≤ L - 1 / 25000 := by
    intro β' m' hb' hm'
    have h0 := hc β' m' 0 hb' hm' (Or.inl rfl)
    have h1 := hc β' m' (4 / 10 ^ 6) hb' hm' (Or.inr rfl)
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

/-- **An affine piece by the Halász–Montgomery branch**, for `lo ≤ hi` (`hlo`) and a window with `m₂ ≤ 1` (`hm2`):
if both bilinear inequalities hold at the eight corners `β ∈ {lo, hi}`, `m ∈ {m₁, m₂}`, `w ∈ {0, 4·10⁻⁶}` (`h1`,
`h2`), the piece holds. The first is
`affine_corner_bound` with `t(m) = m`; the second with `p, A` doubled (its `(p − Aβ)` appears twice) and
`t(m) = (5/12 + d + 2e)/2 + ((13/12 − d)/2)m`. -/
theorem windowPieceHM_affine {p A L m₁ m₂ d e lo hi : ℝ} (hlo : lo ≤ hi) (hm2 : m₂ ≤ 1)
    (h1 : ∀ β m w, (β = lo ∨ β = hi) → (m = m₁ ∨ m = m₂) → (w = 0 ∨ w = 4 / 10 ^ 6) →
      (L - m) * (β + w) + (p - A * β) / 2 + m / 2 + m / 2 ≤ L - 1 / 25000)
    (h2 : ∀ β m w, (β = lo ∨ β = hi) → (m = m₁ ∨ m = m₂) → (w = 0 ∨ w = 4 / 10 ^ 6) →
      (L - m) * (β + w) + (p - A * β) / 2 + m / 2 +
        ((p - A * β) + (5 / 12 + m / 12 + d * (1 - m) + 2 * e)) / 2 ≤ L - 1 / 25000) :
    WindowPieceHM (fun β => p - A * β) L m₁ m₂ d e lo hi := by
  intro β m w hβ hβ1 hm1 hm2' hw hw1
  refine Or.inr ⟨hm2'.trans hm2, ?_, ?_⟩
  · have := affine_corner_bound (p := p) (A := A) (L := L) (t₀ := 0) (t₁ := 1) hlo hβ hβ1 hm1 hm2' hw hw1
      (fun β' m' w' hb' hm' hw' => by have := h1 β' m' w' hb' hm' hw'; linarith)
    linarith
  · have := affine_corner_bound (p := 2 * p) (A := 2 * A) (L := L) (t₀ := (5 / 12 + d + 2 * e) / 2)
      (t₁ := (13 / 12 - d) / 2) hlo hβ hβ1 hm1 hm2' hw hw1
      (fun β' m' w' hb' hm' hw' => by have := h2 β' m' w' hb' hm' hw'; linarith)
    linarith

/-- **An affine piece by the Halász–Montgomery branch below `m = 1` and by orthogonality above it**, for
`lo ≤ hi` (`hlo`): the two bilinear inequalities at the corners `m ∈ {m₁, 1}` (`h1`, `h2`) give the branch for
`m ≤ 1`, and orthogonality's inequality for `m ≥ 1` (whose exponent `(L − m)(β + w) + gβ/2 + m` is the first of the
two) at the corners `m ∈ {1, m₂}` (`h3`) gives it for `m ≥ 1` (a range of `m` with no point gives nothing to show). -/
theorem windowPieceHM_affine_split {p A L m₁ m₂ d e lo hi : ℝ} (hlo : lo ≤ hi)
    (h1 : ∀ β m w, (β = lo ∨ β = hi) → (m = m₁ ∨ m = 1) → (w = 0 ∨ w = 4 / 10 ^ 6) →
      (L - m) * (β + w) + (p - A * β) / 2 + m / 2 + m / 2 ≤ L - 1 / 25000)
    (h2 : ∀ β m w, (β = lo ∨ β = hi) → (m = m₁ ∨ m = 1) → (w = 0 ∨ w = 4 / 10 ^ 6) →
      (L - m) * (β + w) + (p - A * β) / 2 + m / 2 +
        ((p - A * β) + (5 / 12 + m / 12 + d * (1 - m) + 2 * e)) / 2 ≤ L - 1 / 25000)
    (h3 : ∀ β m w, (β = lo ∨ β = hi) → (m = 1 ∨ m = m₂) → (w = 0 ∨ w = 4 / 10 ^ 6) →
      (L - m) * (β + w) + (p - A * β) / 2 + m ≤ L - 1 / 25000) :
    WindowPieceHM (fun β => p - A * β) L m₁ m₂ d e lo hi := by
  intro β m w hβ hβ1 hm hm' hw hw1
  by_cases hle : m ≤ 1
  · refine Or.inr ⟨hle, ?_, ?_⟩
    · have := affine_corner_bound (p := p) (A := A) (L := L) (t₀ := 0) (t₁ := 1) hlo hβ hβ1 hm hle hw hw1
        (fun β' m' w' hb' hm'' hw' => by have := h1 β' m' w' hb' hm'' hw'; linarith)
      linarith
    · have := affine_corner_bound (p := 2 * p) (A := 2 * A) (L := L) (t₀ := (5 / 12 + d + 2 * e) / 2)
        (t₁ := (13 / 12 - d) / 2) hlo hβ hβ1 hm hle hw hw1
        (fun β' m' w' hb' hm'' hw' => by have := h2 β' m' w' hb' hm'' hw'; linarith)
      linarith
  · have hlt : 1 < m := not_le.1 hle
    refine Or.inl ⟨fun h => absurd h hle, fun _ => ?_⟩
    have := affine_corner_bound (p := p) (A := A) (L := L) (t₀ := 0) (t₁ := 1) hlo hβ hβ1 hlt.le hm' hw hw1
      (fun β' m' w' hb' hm'' hw' => by have := h3 β' m' w' hb' hm'' hw'; linarith)
    linarith

/-- `WindowPieceHM` for a curve equal to another pointwise (as `windowPiece_congr`): `g β = g' β` for every `β`
(`hg`) and the piece for `g` (`h`). -/
theorem windowPieceHM_congr {g g' : ℝ → ℝ} {L m₁ m₂ d e lo hi : ℝ} (hg : ∀ β, g β = g' β)
    (h : WindowPieceHM g L m₁ m₂ d e lo hi) : WindowPieceHM g' L m₁ m₂ d e lo hi := by
  have : g' = g := funext fun β => (hg β).symm
  rw [this]; exact h

/-- The piece `g β = A(1 − β)` by `windowPieceHM_affine_split` at `p = A` (as `windowPiece_const`), for `lo ≤ hi`
(`hlo`) and the corner inequalities `h1`, `h2` (`m ∈ {m₁, 1}`) and `h3` (`m ∈ {1, m₂}`). -/
theorem windowPieceHM_const_split {A L m₁ m₂ d e lo hi : ℝ} (hlo : lo ≤ hi)
    (h1 : ∀ β m w, (β = lo ∨ β = hi) → (m = m₁ ∨ m = 1) → (w = 0 ∨ w = 4 / 10 ^ 6) →
      (L - m) * (β + w) + (A - A * β) / 2 + m / 2 + m / 2 ≤ L - 1 / 25000)
    (h2 : ∀ β m w, (β = lo ∨ β = hi) → (m = m₁ ∨ m = 1) → (w = 0 ∨ w = 4 / 10 ^ 6) →
      (L - m) * (β + w) + (A - A * β) / 2 + m / 2 +
        ((A - A * β) + (5 / 12 + m / 12 + d * (1 - m) + 2 * e)) / 2 ≤ L - 1 / 25000)
    (h3 : ∀ β m w, (β = lo ∨ β = hi) → (m = 1 ∨ m = m₂) → (w = 0 ∨ w = 4 / 10 ^ 6) →
      (L - m) * (β + w) + (A - A * β) / 2 + m ≤ L - 1 / 25000) :
    WindowPieceHM (fun β => A * (1 - β)) L m₁ m₂ d e lo hi :=
  windowPieceHM_congr (fun β => by ring) (windowPieceHM_affine_split hlo h1 h2 h3)

end SieveCurveGlue

#print axioms SieveCurveGlue.affine_corner_bound
#print axioms SieveCurveGlue.windowPieceHM_affine
#print axioms SieveCurveGlue.windowPieceHM_affine_split
#print axioms SieveCurveGlue.windowPieceHM_const_split
