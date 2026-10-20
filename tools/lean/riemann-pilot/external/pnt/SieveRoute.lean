/-
# Round 607: the parameters of the sieve route, and its Type II input

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

The sieve route of `frontier/linnik/SIEVE-ROUTE.md` §13 runs at `x = q^L` with a Type II window `[w₁L, w₂L]`. `Route`
holds `L`, `w₁` and `w₂`, and `RouteOK` the facts about them that the route's proofs use. `TypeIIAt` is the Type II
estimate the route takes as its input: Proposition 3′ at `L` on the window, the conclusion of
`SieveTypeII.typeII_step` with `L`, `w₁` and `w₂` in place of `2333/1000`, `401/1000` and `485/1000`.

* `route2333`, `routeOK2333`, `typeII2333`: the first goal's parameters, `L = 2333/1000` on `[401/1000, 485/1000]`,
  and `SieveTypeII.typeII_step` as `TypeIIAt`.

The file imports `SieveTypeII.lean`.
-/
import SieveTypeII

open Complex

noncomputable section

namespace SieveRoute

/-- **The sieve route's parameters**: the exponent `L` of `x = q^L`, and the Type II window `[w₁, w₂]` as fractions
of `L`. -/
class Route where
  /-- The exponent. -/
  L : ℝ
  /-- The Type II window's left end, a fraction of `L`. -/
  w₁ : ℝ
  /-- The Type II window's right end, a fraction of `L`. -/
  w₂ : ℝ

export Route (L w₁ w₂)

variable [Route]

/-- **The facts about the parameters** that the route's proofs use. -/
class RouteOK : Prop where
  two_lt_L : 2 < L
  w₁_pos : 0 < w₁
  w₁_lt_w₂ : w₁ < w₂
  w₂_lt_one : w₂ < 1
  L_le : L ≤ 5 / 2

open scoped Classical ContDiff in
/-- **Proposition 3′ at `L` on the window `[w₁L, w₂L]`, pointwise in the heights**: the conclusion of
`SieveTypeII.typeII_step` with `L`, `w₁` and `w₂` in place of `2333/1000`, `401/1000` and `485/1000`. -/
def TypeIIAt : Prop :=
  ∀ {f0 : ℝ → ℝ}, ContDiff ℝ ∞ f0 → Function.support f0 ⊆ Set.Icc (1 / 2) 2 → ∀ (K₀ : ℕ) {e₁ η : ℝ}, 0 < e₁ →
    0 < η → η ≤ 1 / 100000 →
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (w₁ * L) ≤ P → (P : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ L / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ (L - 1 / 50000) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P)

variable [RouteOK]

theorem two_lt_L : 2 < L := RouteOK.two_lt_L
theorem L_pos : 0 < L := by linarith [two_lt_L]
theorem w₁_pos : 0 < w₁ := RouteOK.w₁_pos
theorem w₁_lt_w₂ : w₁ < w₂ := RouteOK.w₁_lt_w₂
theorem w₂_lt_one : w₂ < 1 := RouteOK.w₂_lt_one
theorem L_le : L ≤ 5 / 2 := RouteOK.L_le
theorem w₁L_pos : 0 < w₁ * L := mul_pos w₁_pos L_pos
theorem w₂L_lt_L : w₂ * L < L := by nlinarith [w₂_lt_one, L_pos]

/-- Closes the numeric side goals about `L`, `w₁` and `w₂` that the route's proofs meet: `norm_num`, or `nlinarith`
with the facts of `RouteOK`. -/
macro "route_num" : tactic =>
  `(tactic| first
    | (norm_num; done)
    | nlinarith [SieveRoute.L_pos, SieveRoute.w₁_pos, SieveRoute.w₁_lt_w₂, SieveRoute.w₂_lt_one, SieveRoute.L_le,
        SieveRoute.two_lt_L, SieveRoute.w₁L_pos, SieveRoute.w₂L_lt_L])

end SieveRoute

namespace SieveRoute

/-- **The first goal's parameters**: `L = 2333/1000` on the window `[401/1000, 485/1000]`. -/
@[instance_reducible] def route2333 : Route := ⟨2333 / 1000, 401 / 1000, 485 / 1000⟩

theorem routeOK2333 : @RouteOK route2333 :=
  @RouteOK.mk route2333 (show (2 : ℝ) < 2333 / 1000 by norm_num) (show (0 : ℝ) < 401 / 1000 by norm_num)
    (show (401 / 1000 : ℝ) < 485 / 1000 by norm_num) (show (485 / 1000 : ℝ) < 1 by norm_num)
    (show (2333 / 1000 : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeII.typeII_step` as `TypeIIAt`** at the first goal's parameters. -/
theorem typeII2333 : @TypeIIAt route2333 := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeII.typeII_step hf0 hsupp K₀ he₁ hη hη1

end SieveRoute

#print axioms SieveRoute.routeOK2333
#print axioms SieveRoute.typeII2333
