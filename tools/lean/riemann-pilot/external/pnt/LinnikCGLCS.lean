/-
# Round 660: the two Cauchy–Schwarz steps of their §11 (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

This file proves the two Cauchy–Schwarz steps with which Chen–Gupta–Li's proof of Proposition 11.1 opens, on each
dyadic block of round 657's `prop72`.

Their text. From Proposition 7.2, "Applications of the Cauchy-Schwarz inequality and the second moment bound for R
(cf. Lemma 9.1) give" (text layer lines 5567–5568, spaces restored) `S₃ ⪅ (N²/(q²M₂))S₃,₁^{1/2}S₃,₂^{1/2} + |W|`,
with `S₃,₁` and `S₃,₂` defined at lines 5575–5607. Then "Using the Cauchy-Schwarz inequality again, we have that
(11.1) S₃,₂ ≤ S₃,₃^{1/2}S₃,₄^{1/2}," (lines 5608–5611; spaces restored, the subscripts and exponents transcribed),
with `S₃,₃` and `S₃,₄` defined at lines 5613–5654.

The stack's quantities, for a finite set `B` of triples (in use, round 657's block `blk M k`), `L = NM₂/q` and
`X` for their `(qT)^ϵ`:
* `S₃,₁ = ∫_{[1/2,2]}Σ_{b₁}|R(v, b₁)|² dv`, which round 658's `lemma91` evaluates exactly as `(3/2)φ(q)|R|`;
* `Y(v, b₁) = Σ_{b₂}Σ_{m⃗∈B}R̃(c₁, b₁⁻¹b₂)R̃(c₂, b₂)(b₁m₁ − b₂m₂ + m₃, q)`, with `c₁ = (m₁v + m₃)/(m₂v)` and
  `c₂ = (m₁v + m₃)/m₂`, and `S₃,₂ = ∫_{[1/2,2]}Σ_{b₁}Y² dv`;
* `P(v, b₁) = Σ_{b₂}Σ_{m⃗∈B}R̃(c₁, b₁⁻¹b₂)²(…, q)`, `Q(v, b₁) = Σ_{b₂}Σ_{m⃗∈B}R̃(c₂, b₂)²(…, q)`,
  `S₃,₃ = ∫_{[1/2,2]}Σ_{b₁}P² dv` and `S₃,₄ = ∫_{[1/2,2]}Σ_{b₁}Q² dv`.
Their sums run over `|m_i| ∼ M_i`; the stack's run over the block. Their first step is stated with `⪅` and their
(11.1) with `≤`; the stack's are exact inequalities.

Plain statements, with `q ≥ 1` and `L ≥ 0`.
* `sum_blk`: the triple sum of `prop72` restricted to the block `k` is the sum over `blk M k`.
* `cs_vb`: for nonnegative measurable `A`, `Y` bounded on `[1/2, 2]`,
  `∫_{[1/2,2]}Σ_bAY ≤ √(∫_{[1/2,2]}Σ_bA²)√(∫_{[1/2,2]}Σ_bY²)`, the sums over the units.
* `sum_It_eq`: `Σ_{m⃗∈B}Ĩ_{M₂}(m⃗) = ∫_{[1/2,2]}Σ_{b₁}|R(v, b₁)|Y(v, b₁) dv`.
* `sum_It_sq_le`: `(Σ_{m⃗∈B}Ĩ_{M₂}(m⃗))² ≤ S₃,₁S₃,₂`.
* `Yb_sq_le`: `Y(v, b₁)² ≤ P(v, b₁)Q(v, b₁)`, by Cauchy–Schwarz over `(b₂, m⃗)` with the gcd weight.
* `S32_le`: `S₃,₂ ≤ √S₃,₃·√S₃,₄`.

* `blk`, `sum_blk`: the dyadic block as a finite set.
* `gw`, `gw_nonneg`, `gw_le`, `c₁`, `c₂`, `Yb`, `Pb`, `Qb`: the weight, the centres and the inner sums.
* `Cb`, `Rt_sq_le`, `measurable_Yb`, `measurable_Pb`, `measurable_Qb`, `Yb_nonneg`, `Pb_nonneg`, `Qb_nonneg`,
  `Yb_le`, `Pb_le`, `Qb_le`: measurability and bounds.
* `cs_vb`: Cauchy–Schwarz in `(v, b)`.
* `S31`, `S32`, `S33`, `S34`, `sum_It_eq`, `sum_It_sq_le`, `Yb_sq_le`, `S32_le`: their two steps.

The next step is to put `S₃,₃` and `S₃,₄` in the form of their Proposition 8.1. For `S₃,₃` their change of variables
`u = v⁻¹` turns `(m₁v + m₃)/(m₂v)` into `(m₁ + m₃u)/m₂`, which is the form Proposition 8.1 needs. The paper prints the
denominator as `m₂u` (text layer lines 5672–5673). On page 48 pdfminer finds the numerator `m₁ + m₃u` at
x = 281.3–332.3 over a rule at y = 256.5 spanning the same x, and the denominator `m₂u` at x = 296.0–317.7 below it
(`scratchpad/r660/p48_frac.txt`; the rule is line 184 of `scratchpad/r660/p48.txt`).

The file imports `LinnikCGLMom4.lean`.
-/

import LinnikCGLMom4

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLCS

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLS23 LinnikCGLTrace LinnikCGLDiag
  LinnikCGLTrunc LinnikCGLProd LinnikCGLRFact LinnikCGLRam LinnikCGLP71 LinnikCGLSym LinnikCGLRt LinnikCGLP72
  LinnikCGLMom LinnikCGLMom4

/-! ### The dyadic block as a finite set -/

/-- The triples of the dyadic block `k` of round 657's `prop72`: `0 < |m_i| ≤ M`, `⌊log₂|m₂|⌋ = k` and
`|m₁|, |m₃| ≤ |m₂|`. -/
def blk (M k : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (boxM M ×ˢ boxM M ×ˢ boxM M).filter fun m => Nat.log 2 m.2.1.natAbs = k ∧ |m.1| ≤ |m.2.1| ∧ |m.2.2| ≤ |m.2.1|

lemma sum_blk (M k : ℕ) (f : ℤ → ℤ → ℤ → ℝ) :
    ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M,
      (if Nat.log 2 m₂.natAbs = k ∧ |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then f m₁ m₂ m₃ else 0) =
    ∑ m ∈ blk M k, f m.1 m.2.1 m.2.2 := by
  unfold blk
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [Finset.sum_product]

/-! ### The quantities of their §11 -/

/-- The gcd weight `(b₁m₁ − b₂m₂ + m₃, q)`. -/
def gw {q : ℕ} (b₁ b₂ : (ZMod q)ˣ) (m : ℤ × ℤ × ℤ) : ℝ :=
  (Nat.gcd ((b₁ : ZMod q) * (m.1 : ZMod q) - (b₂ : ZMod q) * (m.2.1 : ZMod q) + (m.2.2 : ZMod q)).val q : ℝ)

lemma gw_nonneg {q : ℕ} (b₁ b₂ : (ZMod q)ˣ) (m : ℤ × ℤ × ℤ) : 0 ≤ gw b₁ b₂ m := Nat.cast_nonneg _

lemma gw_le {q : ℕ} [NeZero q] (b₁ b₂ : (ZMod q)ˣ) (m : ℤ × ℤ × ℤ) : gw b₁ b₂ m ≤ q := by
  unfold gw; exact_mod_cast Nat.gcd_le_right _ (Nat.pos_of_ne_zero (NeZero.ne q))

/-- The two centres: `c₁ = (m₁v + m₃)/(m₂v)` and `c₂ = (m₁v + m₃)/m₂`. -/
def c₁ (m : ℤ × ℤ × ℤ) (v : ℝ) : ℝ := (m.1 * v + m.2.2) / (m.2.1 * v)
def c₂ (m : ℤ × ℤ × ℤ) (v : ℝ) : ℝ := (m.1 * v + m.2.2) / m.2.1

/-- Their inner sum `Σ_{b₂}Σ_{m⃗}R̃(c₁, b₁⁻¹b₂)R̃(c₂, b₂)(b₁m₁ − b₂m₂ + m₃, q)`. -/
def Yb {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (X M₂ : ℝ) (B : Finset (ℤ × ℤ × ℤ)) (v : ℝ) (b₁ : (ZMod q)ˣ) : ℝ :=
  ∑ b₂ : (ZMod q)ˣ, ∑ m ∈ B, Rt N R χ t X M₂ (c₁ m v) ((b₁⁻¹ * b₂ : (ZMod q)ˣ) : ZMod q) *
    Rt N R χ t X M₂ (c₂ m v) (b₂ : ZMod q) * gw b₁ b₂ m

/-- `Σ_{b₂}Σ_{m⃗}R̃(c₁, b₁⁻¹b₂)²(b₁m₁ − b₂m₂ + m₃, q)`. -/
def Pb {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (X M₂ : ℝ) (B : Finset (ℤ × ℤ × ℤ)) (v : ℝ) (b₁ : (ZMod q)ˣ) : ℝ :=
  ∑ b₂ : (ZMod q)ˣ, ∑ m ∈ B, Rt N R χ t X M₂ (c₁ m v) ((b₁⁻¹ * b₂ : (ZMod q)ˣ) : ZMod q) ^ 2 * gw b₁ b₂ m

/-- `Σ_{b₂}Σ_{m⃗}R̃(c₂, b₂)²(b₁m₁ − b₂m₂ + m₃, q)`. -/
def Qb {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (X M₂ : ℝ) (B : Finset (ℤ × ℤ × ℤ)) (v : ℝ) (b₁ : (ZMod q)ˣ) : ℝ :=
  ∑ b₂ : (ZMod q)ˣ, ∑ m ∈ B, Rt N R χ t X M₂ (c₂ m v) (b₂ : ZMod q) ^ 2 * gw b₁ b₂ m

/-- The common bound `φ(q)|B|·(3/2)L|R|²·q` of `Y`, `P` and `Q`, for `L = NM₂/q ≥ 0`. -/
def Cb {ι : Type*} (q : ℕ) [NeZero q] (N M₂ : ℝ) (R : Finset ι) (B : Finset (ℤ × ℤ × ℤ)) : ℝ :=
  Fintype.card (ZMod q)ˣ * (B.card * (3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2 * q))

lemma Rt_sq_le {ι : Type*} {q : ℕ} {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {X M₂ : ℝ} (hL : 0 ≤ N * M₂ / q) (u : ℝ) (a : ZMod q) :
    Rt N R χ t X M₂ u a ^ 2 ≤ 3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2 := by
  have h := Rt_le R χ t (X := X) hL u a
  have h0 := Rt_nonneg N R χ t X M₂ u a
  calc Rt N R χ t X M₂ u a ^ 2 ≤ (Real.sqrt (3 / 2 * (N * M₂ / q)) * R.card) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by positivity)]

/-! ### Measurability and bounds -/

section bounds

variable {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
  {X M₂ : ℝ} (B : Finset (ℤ × ℤ × ℤ))

lemma measurable_Yb (b₁ : (ZMod q)ˣ) : Measurable fun v => Yb N R χ t X M₂ B v b₁ := by
  unfold Yb c₁ c₂
  refine Finset.measurable_sum _ fun b₂ _ => Finset.measurable_sum _ fun m _ => ?_
  exact (((measurable_Rt N R χ t X M₂ _).comp (by fun_prop)).mul ((measurable_Rt N R χ t X M₂ _).comp
    (by fun_prop))).mul measurable_const

lemma measurable_Pb (b₁ : (ZMod q)ˣ) : Measurable fun v => Pb N R χ t X M₂ B v b₁ := by
  unfold Pb c₁
  refine Finset.measurable_sum _ fun b₂ _ => Finset.measurable_sum _ fun m _ => ?_
  exact (((measurable_Rt N R χ t X M₂ _).comp (by fun_prop)).pow_const 2).mul measurable_const

lemma measurable_Qb (b₁ : (ZMod q)ˣ) : Measurable fun v => Qb N R χ t X M₂ B v b₁ := by
  unfold Qb c₂
  refine Finset.measurable_sum _ fun b₂ _ => Finset.measurable_sum _ fun m _ => ?_
  exact (((measurable_Rt N R χ t X M₂ _).comp (by fun_prop)).pow_const 2).mul measurable_const

lemma Yb_nonneg (v : ℝ) (b₁ : (ZMod q)ˣ) : 0 ≤ Yb N R χ t X M₂ B v b₁ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (Rt_nonneg _ _ _ _ _ _ _ _) (Rt_nonneg _ _ _ _ _ _ _ _)) (gw_nonneg _ _ _)

lemma Pb_nonneg (v : ℝ) (b₁ : (ZMod q)ˣ) : 0 ≤ Pb N R χ t X M₂ B v b₁ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (gw_nonneg _ _ _)

lemma Qb_nonneg (v : ℝ) (b₁ : (ZMod q)ˣ) : 0 ≤ Qb N R χ t X M₂ B v b₁ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (gw_nonneg _ _ _)

lemma Yb_le (hL : 0 ≤ N * M₂ / q) (v : ℝ) (b₁ : (ZMod q)ˣ) : Yb N R χ t X M₂ B v b₁ ≤ Cb q N M₂ R B := by
  unfold Yb Cb
  calc ∑ b₂ : (ZMod q)ˣ, ∑ m ∈ B, Rt N R χ t X M₂ (c₁ m v) ((b₁⁻¹ * b₂ : (ZMod q)ˣ) : ZMod q) *
        Rt N R χ t X M₂ (c₂ m v) (b₂ : ZMod q) * gw b₁ b₂ m
      ≤ ∑ _b₂ : (ZMod q)ˣ, ∑ _m ∈ B, 3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2 * q := by
        refine Finset.sum_le_sum fun b₂ _ => Finset.sum_le_sum fun m _ => ?_
        have h1 := Rt_nonneg N R χ t X M₂ (c₁ m v) ((b₁⁻¹ * b₂ : (ZMod q)ˣ) : ZMod q)
        have h2 := Rt_nonneg N R χ t X M₂ (c₂ m v) (b₂ : ZMod q)
        have hp : Rt N R χ t X M₂ (c₁ m v) ((b₁⁻¹ * b₂ : (ZMod q)ˣ) : ZMod q) *
            Rt N R χ t X M₂ (c₂ m v) (b₂ : ZMod q) ≤ 3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2 := by
          have := Rt_sq_le R χ t (X := X) hL (c₁ m v) ((b₁⁻¹ * b₂ : (ZMod q)ˣ) : ZMod q)
          have := Rt_sq_le R χ t (X := X) hL (c₂ m v) (b₂ : ZMod q)
          nlinarith [sq_nonneg (Rt N R χ t X M₂ (c₁ m v) ((b₁⁻¹ * b₂ : (ZMod q)ˣ) : ZMod q) -
            Rt N R χ t X M₂ (c₂ m v) (b₂ : ZMod q))]
        exact mul_le_mul hp (gw_le b₁ b₂ m) (gw_nonneg _ _ _) (by positivity)
    _ = Fintype.card (ZMod q)ˣ * (B.card * (3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2 * q)) := by simp

lemma Pb_le (hL : 0 ≤ N * M₂ / q) (v : ℝ) (b₁ : (ZMod q)ˣ) : Pb N R χ t X M₂ B v b₁ ≤ Cb q N M₂ R B := by
  unfold Pb Cb
  calc ∑ b₂ : (ZMod q)ˣ, ∑ m ∈ B, Rt N R χ t X M₂ (c₁ m v) ((b₁⁻¹ * b₂ : (ZMod q)ˣ) : ZMod q) ^ 2 * gw b₁ b₂ m
      ≤ ∑ _b₂ : (ZMod q)ˣ, ∑ _m ∈ B, 3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2 * q :=
        Finset.sum_le_sum fun b₂ _ => Finset.sum_le_sum fun m _ =>
          mul_le_mul (Rt_sq_le R χ t (X := X) hL _ _) (gw_le b₁ b₂ m) (gw_nonneg _ _ _) (by positivity)
    _ = Fintype.card (ZMod q)ˣ * (B.card * (3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2 * q)) := by simp

lemma Qb_le (hL : 0 ≤ N * M₂ / q) (v : ℝ) (b₁ : (ZMod q)ˣ) : Qb N R χ t X M₂ B v b₁ ≤ Cb q N M₂ R B := by
  unfold Qb Cb
  calc ∑ b₂ : (ZMod q)ˣ, ∑ m ∈ B, Rt N R χ t X M₂ (c₂ m v) (b₂ : ZMod q) ^ 2 * gw b₁ b₂ m
      ≤ ∑ _b₂ : (ZMod q)ˣ, ∑ _m ∈ B, 3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2 * q :=
        Finset.sum_le_sum fun b₂ _ => Finset.sum_le_sum fun m _ =>
          mul_le_mul (Rt_sq_le R χ t (X := X) hL _ _) (gw_le b₁ b₂ m) (gw_nonneg _ _ _) (by positivity)
    _ = Fintype.card (ZMod q)ˣ * (B.card * (3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2 * q)) := by simp

end bounds

/-! ### Cauchy–Schwarz in `(v, b₁)` -/

/-- **Cauchy–Schwarz in `(v, b)`** over `[1/2, 2]` and the units, for nonnegative measurable functions bounded on
`[1/2, 2]`: `∫Σ_bAY ≤ √(∫Σ_bA²)√(∫Σ_bY²)`. -/
lemma cs_vb {q : ℕ} [NeZero q] {A Y : ℝ → (ZMod q)ˣ → ℝ} (hA0 : ∀ v b, 0 ≤ A v b) (hY0 : ∀ v b, 0 ≤ Y v b)
    (hAm : ∀ b, Measurable fun v => A v b) (hYm : ∀ b, Measurable fun v => Y v b) {CA CY : ℝ}
    (hAb : ∀ v ∈ Icc (1 / 2 : ℝ) 2, ∀ b, A v b ≤ CA) (hYb : ∀ v ∈ Icc (1 / 2 : ℝ) 2, ∀ b, Y v b ≤ CY) :
    ∫ v in Icc (1 / 2 : ℝ) 2, ∑ b, A v b * Y v b ≤
      Real.sqrt (∫ v in Icc (1 / 2 : ℝ) 2, ∑ b, A v b ^ 2) * Real.sqrt (∫ v in Icc (1 / 2 : ℝ) 2, ∑ b, Y v b ^ 2) := by
  set f : ℝ → ℝ := fun v => Real.sqrt (∑ b, A v b ^ 2) with hf
  set g : ℝ → ℝ := fun v => Real.sqrt (∑ b, Y v b ^ 2) with hg
  have hfm : Measurable f := (Finset.measurable_sum _ fun b _ => (hAm b).pow_const 2).sqrt
  have hgm : Measurable g := (Finset.measurable_sum _ fun b _ => (hYm b).pow_const 2).sqrt
  have hfb : ∀ v ∈ Icc (1 / 2 : ℝ) 2, f v ≤ Real.sqrt (Fintype.card (ZMod q)ˣ * CA ^ 2) := fun v hv =>
    Real.sqrt_le_sqrt (by
      calc ∑ b, A v b ^ 2 ≤ ∑ _b : (ZMod q)ˣ, CA ^ 2 :=
            Finset.sum_le_sum fun b _ => pow_le_pow_left₀ (hA0 v b) (hAb v hv b) 2
        _ = Fintype.card (ZMod q)ˣ * CA ^ 2 := by simp)
  have hgb : ∀ v ∈ Icc (1 / 2 : ℝ) 2, g v ≤ Real.sqrt (Fintype.card (ZMod q)ˣ * CY ^ 2) := fun v hv =>
    Real.sqrt_le_sqrt (by
      calc ∑ b, Y v b ^ 2 ≤ ∑ _b : (ZMod q)ˣ, CY ^ 2 :=
            Finset.sum_le_sum fun b _ => pow_le_pow_left₀ (hY0 v b) (hYb v hv b) 2
        _ = Fintype.card (ZMod q)ˣ * CY ^ 2 := by simp)
  have hcs := cs_Icc (fun v => Real.sqrt_nonneg _) (fun v => Real.sqrt_nonneg _) hfm hgm hfb hgb
  have hf2 : ∀ v, f v ^ 2 = ∑ b, A v b ^ 2 := fun v => Real.sq_sqrt (Finset.sum_nonneg fun b _ => sq_nonneg _)
  have hg2 : ∀ v, g v ^ 2 = ∑ b, Y v b ^ 2 := fun v => Real.sq_sqrt (Finset.sum_nonneg fun b _ => sq_nonneg _)
  rw [setIntegral_congr_fun measurableSet_Icc (fun x _ => hf2 x),
    setIntegral_congr_fun measurableSet_Icc (fun x _ => hg2 x)] at hcs
  have hpt : ∀ v, ∑ b, A v b * Y v b ≤ f v * g v := by
    intro v
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun b _ => sq_nonneg _)]
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hint : IntegrableOn (fun v => ∑ b, A v b * Y v b) (Icc (1 / 2 : ℝ) 2) := by
    refine integrableOn_Icc_of_le (Finset.measurable_sum _ fun b _ => (hAm b).mul (hYm b))
      (C := Fintype.card (ZMod q)ˣ * (CA * CY)) fun v hv => ?_
    rw [abs_of_nonneg (Finset.sum_nonneg fun b _ => mul_nonneg (hA0 v b) (hY0 v b))]
    calc ∑ b, A v b * Y v b ≤ ∑ _b : (ZMod q)ˣ, CA * CY :=
          Finset.sum_le_sum fun b _ => mul_le_mul (hAb v hv b) (hYb v hv b) (hY0 v b)
            ((hA0 v b).trans (hAb v hv b))
      _ = Fintype.card (ZMod q)ˣ * (CA * CY) := by simp
  have hint2 : IntegrableOn (fun v => f v * g v) (Icc (1 / 2 : ℝ) 2) := by
    refine integrableOn_Icc_of_le (hfm.mul hgm) (C := Real.sqrt (Fintype.card (ZMod q)ˣ * CA ^ 2) *
      Real.sqrt (Fintype.card (ZMod q)ˣ * CY ^ 2)) fun v hv => ?_
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact mul_le_mul (hfb v hv) (hgb v hv) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact (setIntegral_mono_on hint hint2 measurableSet_Icc fun v _ => hpt v).trans hcs

/-! ### Their two Cauchy–Schwarz steps -/

section steps

variable {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
  {X M₂ : ℝ} (B : Finset (ℤ × ℤ × ℤ))

/-- Their `S₃,₁ = ∫_{[1/2,2]}Σ_{b₁}|R(v, b₁)|² dv`. -/
def S31 : ℝ := ∫ v in Icc (1 / 2 : ℝ) 2, ∑ b₁ : (ZMod q)ˣ, ‖Rf R χ t v b₁‖ ^ 2

/-- Their `S₃,₂ = ∫_{[1/2,2]}Σ_{b₁}Y(v, b₁)² dv`. -/
def S32 : ℝ := ∫ v in Icc (1 / 2 : ℝ) 2, ∑ b₁ : (ZMod q)ˣ, Yb N R χ t X M₂ B v b₁ ^ 2

/-- Their `S₃,₃ = ∫_{[1/2,2]}Σ_{b₁}P(v, b₁)² dv`. -/
def S33 : ℝ := ∫ v in Icc (1 / 2 : ℝ) 2, ∑ b₁ : (ZMod q)ˣ, Pb N R χ t X M₂ B v b₁ ^ 2

/-- Their `S₃,₄ = ∫_{[1/2,2]}Σ_{b₁}Q(v, b₁)² dv`. -/
def S34 : ℝ := ∫ v in Icc (1 / 2 : ℝ) 2, ∑ b₁ : (ZMod q)ˣ, Qb N R χ t X M₂ B v b₁ ^ 2

/-- `Σ_{m⃗∈B}Ĩ_{M₂}(m⃗) = ∫_{[1/2,2]}Σ_{b₁}|R(v, b₁)|Y(v, b₁) dv`. -/
lemma sum_It_eq (hL : 0 ≤ N * M₂ / q) :
    ∑ m ∈ B, It N R χ t X M₂ m.1 m.2.1 m.2.2 =
      ∫ v in Icc (1 / 2 : ℝ) 2, ∑ b₁ : (ZMod q)ˣ, ‖Rf R χ t v b₁‖ * Yb N R χ t X M₂ B v b₁ := by
  unfold It
  rw [← integral_finsetSum _ fun m _ => integrableOn_Itg R χ t hL _ _ _]
  refine setIntegral_congr_fun measurableSet_Icc fun v _ => ?_
  unfold Itg Yb c₁ c₂ gw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **Their first Cauchy–Schwarz step**: `(Σ_{m⃗∈B}Ĩ_{M₂}(m⃗))² ≤ S₃,₁S₃,₂`. -/
theorem sum_It_sq_le (hL : 0 ≤ N * M₂ / q) :
    (∑ m ∈ B, It N R χ t X M₂ m.1 m.2.1 m.2.2) ^ 2 ≤ S31 R χ t * S32 R χ t (X := X) (M₂ := M₂) B (N := N) := by
  rw [sum_It_eq R χ t B hL]
  have hA0 : ∀ v (b : (ZMod q)ˣ), 0 ≤ ‖Rf R χ t v (b : ZMod q)‖ := fun _ _ => norm_nonneg _
  have hAm : ∀ b : (ZMod q)ˣ, Measurable fun v => ‖Rf R χ t v (b : ZMod q)‖ := fun b =>
    (measurable_Rf R χ t (b : ZMod q)).norm
  have hAb : ∀ v ∈ Icc (1 / 2 : ℝ) 2, ∀ b : (ZMod q)ˣ, ‖Rf R χ t v (b : ZMod q)‖ ≤ R.card := fun v hv b =>
    norm_Rf_le R χ t (by linarith [hv.1]) _
  have hY0 : ∀ v b, 0 ≤ Yb N R χ t X M₂ B v b := fun v b => Yb_nonneg R χ t B v b
  have hYm : ∀ b, Measurable fun v => Yb N R χ t X M₂ B v b := fun b => measurable_Yb R χ t B b
  have hYb : ∀ v ∈ Icc (1 / 2 : ℝ) 2, ∀ b, Yb N R χ t X M₂ B v b ≤ Cb q N M₂ R B := fun v _ b =>
    Yb_le R χ t B hL v b
  have h := cs_vb hA0 hY0 hAm hYm hAb hYb
  have h0 : 0 ≤ ∫ v in Icc (1 / 2 : ℝ) 2, ∑ b₁ : (ZMod q)ˣ, ‖Rf R χ t v b₁‖ * Yb N R χ t X M₂ B v b₁ :=
    setIntegral_nonneg measurableSet_Icc fun v _ =>
      Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (Yb_nonneg R χ t B v b)
  have hS1 : 0 ≤ S31 R χ t (q := q) := setIntegral_nonneg measurableSet_Icc fun v _ =>
    Finset.sum_nonneg fun b _ => sq_nonneg _
  have hS2 : 0 ≤ S32 R χ t (X := X) (M₂ := M₂) B (N := N) := setIntegral_nonneg measurableSet_Icc fun v _ =>
    Finset.sum_nonneg fun b _ => sq_nonneg _
  calc (∫ v in Icc (1 / 2 : ℝ) 2, ∑ b₁ : (ZMod q)ˣ, ‖Rf R χ t v b₁‖ * Yb N R χ t X M₂ B v b₁) ^ 2
      ≤ (Real.sqrt (S31 R χ t) * Real.sqrt (S32 R χ t (X := X) (M₂ := M₂) B (N := N))) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = S31 R χ t * S32 R χ t (X := X) (M₂ := M₂) B (N := N) := by
        rw [mul_pow, Real.sq_sqrt hS1, Real.sq_sqrt hS2]

/-- `Y(v, b₁)² ≤ P(v, b₁)Q(v, b₁)`, by Cauchy–Schwarz over `(b₂, m⃗)` with the weight `(b₁m₁ − b₂m₂ + m₃, q)`. -/
lemma Yb_sq_le (v : ℝ) (b₁ : (ZMod q)ˣ) :
    Yb N R χ t X M₂ B v b₁ ^ 2 ≤ Pb N R χ t X M₂ B v b₁ * Qb N R χ t X M₂ B v b₁ := by
  unfold Yb Pb Qb
  simp only [← Finset.sum_product']
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => mul_nonneg (sq_nonneg _) (gw_nonneg _ _ _))
    (fun p _ => mul_nonneg (sq_nonneg _) (gw_nonneg _ _ _)) fun p _ => le_of_eq ?_
  ring

/-- **Their second Cauchy–Schwarz step, (11.1)**: `S₃,₂ ≤ S₃,₃^{1/2}S₃,₄^{1/2}`. -/
theorem S32_le (hL : 0 ≤ N * M₂ / q) :
    S32 R χ t (X := X) (M₂ := M₂) B (N := N) ≤
      Real.sqrt (S33 R χ t (X := X) (M₂ := M₂) B (N := N)) * Real.sqrt (S34 R χ t (X := X) (M₂ := M₂) B (N := N)) := by
  set C := Cb q N M₂ R B with hC
  have hP0 : ∀ v b, 0 ≤ Pb N R χ t X M₂ B v b := fun v b => Pb_nonneg R χ t B v b
  have hQ0 : ∀ v b, 0 ≤ Qb N R χ t X M₂ B v b := fun v b => Qb_nonneg R χ t B v b
  have hY0 : ∀ v b, 0 ≤ Yb N R χ t X M₂ B v b := fun v b => Yb_nonneg R χ t B v b
  have hPle : ∀ v b, Pb N R χ t X M₂ B v b ≤ C := fun v b => Pb_le R χ t B hL v b
  have hQle : ∀ v b, Qb N R χ t X M₂ B v b ≤ C := fun v b => Qb_le R χ t B hL v b
  have hYle : ∀ v b, Yb N R χ t X M₂ B v b ≤ C := fun v b => Yb_le R χ t B hL v b
  have hPm : ∀ b, Measurable fun v => Pb N R χ t X M₂ B v b := fun b => measurable_Pb R χ t B b
  have hQm : ∀ b, Measurable fun v => Qb N R χ t X M₂ B v b := fun b => measurable_Qb R χ t B b
  have hYm : ∀ b, Measurable fun v => Yb N R χ t X M₂ B v b := fun b => measurable_Yb R χ t B b
  have h := cs_vb (A := fun v b => Pb N R χ t X M₂ B v b) (Y := fun v b => Qb N R χ t X M₂ B v b)
    hP0 hQ0 hPm hQm (CA := C) (CY := C) (fun v _ b => hPle v b) (fun v _ b => hQle v b)
  refine le_trans ?_ h
  have hint1 : IntegrableOn (fun v => ∑ b₁ : (ZMod q)ˣ, Yb N R χ t X M₂ B v b₁ ^ 2) (Icc (1 / 2 : ℝ) 2) := by
    refine integrableOn_Icc_of_le (Finset.measurable_sum _ fun b _ => (hYm b).pow_const 2)
      (C := Fintype.card (ZMod q)ˣ * C ^ 2) fun v _ => ?_
    rw [abs_of_nonneg (Finset.sum_nonneg fun b _ => sq_nonneg _)]
    calc ∑ b₁ : (ZMod q)ˣ, Yb N R χ t X M₂ B v b₁ ^ 2 ≤ ∑ _b₁ : (ZMod q)ˣ, C ^ 2 :=
          Finset.sum_le_sum fun b _ => pow_le_pow_left₀ (hY0 v b) (hYle v b) 2
      _ = Fintype.card (ZMod q)ˣ * C ^ 2 := by simp
  have hint2 : IntegrableOn (fun v => ∑ b₁ : (ZMod q)ˣ, Pb N R χ t X M₂ B v b₁ * Qb N R χ t X M₂ B v b₁)
      (Icc (1 / 2 : ℝ) 2) := by
    refine integrableOn_Icc_of_le (Finset.measurable_sum _ fun b _ => (hPm b).mul (hQm b))
      (C := Fintype.card (ZMod q)ˣ * (C * C)) fun v _ => ?_
    rw [abs_of_nonneg (Finset.sum_nonneg fun b _ => mul_nonneg (hP0 v b) (hQ0 v b))]
    calc ∑ b₁ : (ZMod q)ˣ, Pb N R χ t X M₂ B v b₁ * Qb N R χ t X M₂ B v b₁ ≤ ∑ _b₁ : (ZMod q)ˣ, C * C :=
          Finset.sum_le_sum fun b _ => mul_le_mul (hPle v b) (hQle v b) (hQ0 v b) ((hP0 v b).trans (hPle v b))
      _ = Fintype.card (ZMod q)ˣ * (C * C) := by simp
  exact setIntegral_mono_on hint1 hint2 measurableSet_Icc fun v _ =>
    Finset.sum_le_sum fun b _ => Yb_sq_le R χ t B v b

end steps

end LinnikCGLCS

#print axioms LinnikCGLCS.sum_blk
#print axioms LinnikCGLCS.cs_vb
#print axioms LinnikCGLCS.sum_It_eq
#print axioms LinnikCGLCS.sum_It_sq_le
#print axioms LinnikCGLCS.S32_le
