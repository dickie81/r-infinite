/-
# Round 662: their `J(f⃗)`, their Proposition 8.1 as a displayed hypothesis, and `S₃,₃`, `S₃,₄` in its form (the
CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their §8 opens: "For parameters satisfying 0 < M ≤ (qT)^ϖ with 0 < ϖ < 1 and given a sequence of compactly supported
smooth functions f⃗ = {f_b}_{1≤b≤q, (b,q)=1}, we define J(f⃗) := sup_{0<M_i<M, 1≤i≤3} ∫_ℝ Σ_{1≤a≤q, (a,q)=1}
(Σ_{1≤b≤q, (b,q)=1} Σ_{|m₁|∼M₁, m₂∼M₂, |m₃|≪M₃} f_b((m₁u+m₃)/m₂)(am₁+bm₂+m₃,q))² du, which is an average of sums of
affine transformations with GCD twists." (text layer lines 2436–2462), and states: "Proposition 8.1. Suppose that
f⃗ = {f_b}_{1≤b≤q, (b,q)=1} is a sequence of smooth functions such that each f_b(u) is non-negative and supported on
|u| ≪ 1 and Σ_{1≤b≤q, (b,q)=1} |f̂_b(ξ)| ⪅_j (T/|ξ|)^j ϕ(q) sup_{b,u} f_b(u) for all j ∈ ℕ. Then
J(f⃗) ⪅ ϕ(q)M⁶(∫_ℝ Σ_{1≤b≤q, (b,q)=1} f_b(u) du)² + ϕ(q)²M⁴ ∫_ℝ Σ_{1≤b≤q, (b,q)=1} f_b(u)² du." (lines 2464–2486).
In both, spaces are restored and the arrows, the sums and their ranges, the integrals and their ranges, the hat, the
large parentheses, the fractions, the subscripts and the exponents transcribed; the text layer's `R` and `N` are the
PDF's blackboard `ℝ` and `ℕ` (`MSBM10` glyphs on page 26, `scratchpad/r662/probe/p26_all.txt`). Their notation:
"A∼B signifies the stronger condition B < A≤2B" (lines 278–279).

The stack's form.
* `setJ M₁ M₂ M₃ κ` is their range `M₁ < |m₁| ≤ 2M₁`, `M₂ < m₂ ≤ 2M₂`, with `|m₃| ≤ κM₃` for their `|m₃| ≪ M₃`; `gJ`
  is their inner double sum and `Jint` their integral, before the supremum over `(M₁, M₂, M₃)`. The gcd is that of
  `q` and the least nonnegative representative, as in round 653.
* `CGLP81` is their Proposition 8.1 with its implicit constants made explicit: the exponent `ϖ`, the support bound
  `A`, the constant `κ` of `|m₃| ≪ M₃` and decay constants `D j`. For each `ε > 0` it gives `C` and `Q₀` with
  `Jint ≤ C(qT)^ε(φ(q)M⁶(∫Σ_bf_b)² + φ(q)²M⁴∫Σ_bf_b²)` whenever `qT ≥ Q₀`, `T ≥ 1`, `0 < M_i < M ≤ (qT)^ϖ`, each
  `f_b` is smooth, nonnegative and `0` for `|u| > A`, and `Σ_b|f̂_b(ξ)| ≤ D_j(T/|ξ|)^jφ(q)f_{b₀}(u₀)` for every `j`
  and `ξ ≠ 0`, at some point `(b₀, u₀)`. Read with the paper's conventions, their Proposition 8.1 implies `CGLP81`:
  this decay condition, with `f_{b₀}(u₀) ≤ sup f` and a constant in place of their `⪅_j`, implies theirs (at `j = 0`
  and `ξ = 0` by continuity, each `f̂_b` being continuous), and `Jint` at any `0 < M_i < M` is at most their supremum.
  `CGLP81` is not proved here.

`S₃,₃` and `S₃,₄` in its form. Their §11 bounds both by Proposition 8.1 (lines 5655–5851). Round 660's
`S₃,₄ = ∫_{[1/2,2]}Σ_{b₁}Q(v, b₁)² dv` has `Q(v, b₁) = Σ_{b₂}Σ_{m⃗∈B}R̃(c₂, b₂)²(b₁m₁ − b₂m₂ + m₃, q)` with
`c₂ = (m₁v + m₃)/m₂`, over round 657's dyadic block `B = blk M k`. On `B` and `v ∈ [1/2, 2]`, `|c₂| ≤ 3`. Take any
nonnegative `f` with `f_{−b}(c) ≥ R̃(c, b)²` on `[−3, 3]`, and put `b = −b₂`, so that the weight is their
`(b₁m₁ + bm₂ + m₃, q)`. Then:
* the triples with `m₂ < 0` are the negatives of those with `m₂ > 0`, with the same `c₂` and gcd: a factor `2`;
* `m₁` is split dyadically, `2^j ≤ |m₁| < 2^{j+1}`, which is `|m₁| ∼ 2^j − 1/2`, for `j ≤ k`; likewise `m₂ ∼ 2^k − 1/2`,
  and `|m₃| ≤ |m₂| ≤ 2(2^k − 1/2)`, so `κ = 2`;
* so `Q(v, b₁)` is at most twice the sum over `j ≤ k` of their inner sums at `a = b₁`, and Cauchy–Schwarz over the
  `k + 1` values of `j` puts a factor `k + 1` in the square.
That gives `S₃,₄ ≤ 4(k + 1)Σ_{j≤k}Jint(f, 2^j − 1/2, 2^k − 1/2, 2^k − 1/2, 2)` (`S34_le_Jint`). For `S₃,₃` their change
of variables `u = v⁻¹` (`|dv| = u⁻²du ≤ 4du` on `[1/2, 2]`) turns `c₁ = (m₁v + m₃)/(m₂v)` into `(m₁ + m₃u)/m₂`, as
round 660 records. With `b₂ = b₁b`, the weight `(b₁m₁ − b₁bm₂ + m₃, q)` equals `(b₁⁻¹m₃ − bm₂ + m₁, q)`, since `b₁` is
a unit ("Note that (b₁m₁−b₁b₂m₂+m₃,q) = (m₁−b₂m₂+b₁⁻¹m₃,q) when (b₁,q) = 1", lines 5700–5701, spaces restored, the
subscripts and the exponent transcribed). Then `b₁ ↦ b₁⁻¹` and the swap `(m₁, m₂, m₃) ↦ (m₃, m₂, m₁)`, which maps the
block to itself, turn the sum into round 660's `Q` at `(u, b₁⁻¹)`. So `S₃,₃ ≤ 4S₃,₄` (`S33_le_S34`).

Plain statements, with `q ≥ 1`.
* `gcd_val_unit_mul`, `gcd_val_neg`: `(ux, q) = (x, q)` for a unit `u`, and `(−x, q) = (x, q)`, in `ℤ/qℤ`.
* `integrable_Jsum`: for `f` continuous and `0` beyond `A`, `0 ≤ M₁` and `0 < M₂`, the integrand of `Jint` is
  integrable on `ℝ`.
* `S34_le_Jint`: for `L = 2^kN/q ≥ 0` and `f` nonnegative, continuous, `0` beyond `A` and with
  `R̃(c, b)² ≤ f_{−b}(c)` for `|c| ≤ 3`, round 660's `S₃,₄` on `blk M k` is at most
  `4(k + 1)Σ_{j≤k}Jint(f, 2^j − 1/2, 2^k − 1/2, 2^k − 1/2, 2)`.
* `S33_le_S34`: for `L ≥ 0` and a finite set `B` of triples closed under the swap, `S₃,₃ ≤ 4S₃,₄`; `blk M k` is
  closed under it (`swap_mem_blk`).

* `gcd_val_unit_mul`, `gcd_val_neg`: the gcd under units.
* `setJ`, `mem_setJ`, `gJw`, `gJ`, `Jint`, `CGLP81`: their `J(f⃗)` and their Proposition 8.1.
* `integrable_Jsum`, `neg_mem_boxM`, `neg_mem_blk`, `swap_mem_blk`, `blk_abs`, `mem_setJ_of_blk`, `Jset`, `Qb_le_gJ`,
  `S34_le_Jint`: `S₃,₄`.
* `Pb_inv_eq`, `S33_le_S34`: `S₃,₃`.

The file imports `LinnikCGLCS.lean`.
-/

import LinnikCGLCS

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLJ

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLS23 LinnikCGLTrace LinnikCGLDiag
  LinnikCGLTrunc LinnikCGLProd LinnikCGLRFact LinnikCGLRam LinnikCGLP71 LinnikCGLSym LinnikCGLRt LinnikCGLP72
  LinnikCGLMom LinnikCGLMom4 LinnikCGLCS

/-! ### The gcd under units -/

/-- `(ux, q) = (x, q)` for a unit `u` of `ℤ/qℤ`: multiplication by `u` keeps the additive order. -/
lemma gcd_val_unit_mul {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) (x : ZMod q) :
    Nat.gcd ((u : ZMod q) * x).val q = Nat.gcd x.val q := by
  have hq : q ≠ 0 := NeZero.ne q
  have key : ∀ y : ZMod q, addOrderOf y = q / q.gcd y.val := fun y => by
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    exact ZMod.addOrderOf_coe _ hq
  have hinj : Function.Injective (AddMonoidHom.mulLeft (u : ZMod q)) := fun a b h => by
    have h' : (u : ZMod q) * a = (u : ZMod q) * b := h
    simpa using congrArg (fun z => ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * z) h'
  have h1 := addOrderOf_injective (AddMonoidHom.mulLeft (u : ZMod q)) hinj x
  have h1' : addOrderOf ((u : ZMod q) * x) = addOrderOf x := h1
  rw [key, key] at h1'
  rw [Nat.gcd_comm, Nat.gcd_comm x.val]
  calc q.gcd ((u : ZMod q) * x).val = q / (q / q.gcd ((u : ZMod q) * x).val) :=
        (Nat.div_div_self (Nat.gcd_dvd_left _ _) hq).symm
    _ = q / (q / q.gcd x.val) := by rw [h1']
    _ = q.gcd x.val := Nat.div_div_self (Nat.gcd_dvd_left _ _) hq

/-- `(−x, q) = (x, q)`. -/
lemma gcd_val_neg {q : ℕ} [NeZero q] (x : ZMod q) : Nat.gcd (-x).val q = Nat.gcd x.val q := by
  have h := gcd_val_unit_mul (-1 : (ZMod q)ˣ) x
  rwa [Units.val_neg, Units.val_one, neg_one_mul] at h

/-! ### Their `J(f⃗)` and their Proposition 8.1 -/

/-- Their range `M₁ < |m₁| ≤ 2M₁`, `M₂ < m₂ ≤ 2M₂` and `|m₃| ≤ κM₃` (their `|m₃| ≪ M₃`), as a finite set. -/
def setJ (M₁ M₂ M₃ κ : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-⌈2 * M₁⌉) ⌈2 * M₁⌉) ×ˢ (Finset.Icc (-⌈2 * M₂⌉) ⌈2 * M₂⌉) ×ˢ
      (Finset.Icc (-⌈κ * M₃⌉) ⌈κ * M₃⌉)).filter fun m =>
    M₁ < |(m.1 : ℝ)| ∧ |(m.1 : ℝ)| ≤ 2 * M₁ ∧ M₂ < (m.2.1 : ℝ) ∧ (m.2.1 : ℝ) ≤ 2 * M₂ ∧ |(m.2.2 : ℝ)| ≤ κ * M₃

lemma mem_setJ {M₁ M₂ M₃ κ : ℝ} (m : ℤ × ℤ × ℤ) :
    m ∈ setJ M₁ M₂ M₃ κ ↔ M₁ < |(m.1 : ℝ)| ∧ |(m.1 : ℝ)| ≤ 2 * M₁ ∧ M₂ < (m.2.1 : ℝ) ∧
      (m.2.1 : ℝ) ≤ 2 * M₂ ∧ |(m.2.2 : ℝ)| ≤ κ * M₃ := by
  unfold setJ
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have c1 := Int.le_ceil (2 * M₁)
    have c2 := Int.le_ceil (2 * M₂)
    have c3 := Int.le_ceil (κ * M₃)
    have a1 := abs_le.mp h2
    have a3 := abs_le.mp h5
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, h1, h2, h3, h4, h5⟩
    · have : -((⌈2 * M₁⌉ : ℤ) : ℝ) ≤ (m.1 : ℝ) := by linarith
      exact_mod_cast this
    · have : (m.1 : ℝ) ≤ ((⌈2 * M₁⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    · have : -((⌈2 * M₂⌉ : ℤ) : ℝ) ≤ (m.2.1 : ℝ) := by linarith
      exact_mod_cast this
    · have : (m.2.1 : ℝ) ≤ ((⌈2 * M₂⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    · have : -((⌈κ * M₃⌉ : ℤ) : ℝ) ≤ (m.2.2 : ℝ) := by linarith
      exact_mod_cast this
    · have : (m.2.2 : ℝ) ≤ ((⌈κ * M₃⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this

/-- Their gcd `(am₁ + bm₂ + m₃, q)`. -/
def gJw {q : ℕ} (a b : (ZMod q)ˣ) (m : ℤ × ℤ × ℤ) : ℝ :=
  (Nat.gcd ((a : ZMod q) * (m.1 : ZMod q) + (b : ZMod q) * (m.2.1 : ZMod q) + (m.2.2 : ZMod q)).val q : ℝ)

lemma gJw_nonneg {q : ℕ} (a b : (ZMod q)ˣ) (m : ℤ × ℤ × ℤ) : 0 ≤ gJw a b m := Nat.cast_nonneg _

/-- Their inner double sum `Σ_bΣ_{m⃗∈S}f_b((m₁u + m₃)/m₂)(am₁ + bm₂ + m₃, q)`. -/
def gJ {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (S : Finset (ℤ × ℤ × ℤ)) (a : (ZMod q)ˣ) (u : ℝ) : ℝ :=
  ∑ b : (ZMod q)ˣ, ∑ m ∈ S, f b ((m.1 * u + m.2.2) / m.2.1) * gJw a b m

/-- Their `J(f⃗)` before the supremum: `∫_ℝΣ_a(Σ_bΣ_{m⃗}f_b((m₁u + m₃)/m₂)(am₁ + bm₂ + m₃, q))² du`. -/
def Jint {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₁ M₂ M₃ κ : ℝ) : ℝ :=
  ∫ u, ∑ a : (ZMod q)ˣ, gJ f (setJ M₁ M₂ M₃ κ) a u ^ 2

/-- **Their Proposition 8.1, as a displayed hypothesis** (not proved here): for `0 < ϖ < 1`, a support bound `A`, the
constant `κ` of their `|m₃| ≪ M₃`, decay constants `D j` and every `ε > 0`, there are `C` and `Q₀` such that, for
`qT ≥ Q₀`, `T ≥ 1`, `0 < M ≤ (qT)^ϖ` and functions `f_b` that are smooth, nonnegative and `0` for `|u| > A`, with
`Σ_b|f̂_b(ξ)| ≤ D_j(T/|ξ|)^jφ(q)f_{b₀}(u₀)` for every `j` and `ξ ≠ 0`, every `0 < M₁, M₂, M₃ < M` has
`Jint ≤ C(qT)^ε(φ(q)M⁶(∫Σ_bf_b)² + φ(q)²M⁴∫Σ_bf_b²)`. -/
def CGLP81 : Prop :=
  ∀ ϖ : ℝ, 0 < ϖ → ϖ < 1 → ∀ (A κ : ℝ) (D : ℕ → ℝ) (ε : ℝ), 0 < ε → ∃ C Q₀ : ℝ,
    ∀ (q : ℕ) [NeZero q] (T M : ℝ) (f : (ZMod q)ˣ → ℝ → ℝ) (b₀ : (ZMod q)ˣ) (u₀ : ℝ),
    Q₀ ≤ (q : ℝ) * T → 1 ≤ T → 0 < M → M ≤ ((q : ℝ) * T) ^ ϖ →
    (∀ b, ContDiff ℝ ∞ (f b)) → (∀ b u, 0 ≤ f b u) → (∀ b u, A < |u| → f b u = 0) →
    (∀ (j : ℕ) (ξ : ℝ), ξ ≠ 0 →
      ∑ b, ‖𝓕 (fun u : ℝ => (f b u : ℂ)) ξ‖ ≤ D j * (T / |ξ|) ^ j * q.totient * f b₀ u₀) →
    ∀ M₁ M₂ M₃ : ℝ, 0 < M₁ → M₁ < M → 0 < M₂ → M₂ < M → 0 < M₃ → M₃ < M →
      Jint f M₁ M₂ M₃ κ ≤ C * ((q : ℝ) * T) ^ ε * ((q.totient : ℝ) * M ^ 6 * (∫ u, ∑ b, f b u) ^ 2 +
        (q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, f b u ^ 2)

/-! ### The integrand of `Jint` is integrable -/

/-- For `f` continuous and `0` beyond `A`, `0 ≤ M₁` and `0 < M₂`, the integrand of `Jint` is continuous with
compact support, hence integrable. -/
lemma integrable_Jsum {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfc : ∀ b, Continuous (f b)) {A : ℝ}
    (hfA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ M₃ κ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 < M₂) :
    Integrable fun u => ∑ a : (ZMod q)ˣ, gJ f (setJ M₁ M₂ M₃ κ) a u ^ 2 := by
  have hcont : ∀ a, Continuous fun u => gJ f (setJ M₁ M₂ M₃ κ) a u := fun a => by
    unfold gJ
    refine continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun m _ => ?_
    exact ((hfc b).comp (by fun_prop)).mul continuous_const
  refine Continuous.integrable_of_hasCompactSupport (continuous_finsetSum _ fun a _ => (hcont a).pow 2) ?_
  set K := 2 * M₂ * |A| + |κ * M₃| + 1 with hK
  refine HasCompactSupport.intro (isCompact_Icc (a := -K) (b := K)) fun u hu => ?_
  have hu' : K < |u| := by
    by_contra h
    push Not at h
    exact hu (abs_le.mp h)
  refine Finset.sum_eq_zero fun a _ => ?_
  have h0 : gJ f (setJ M₁ M₂ M₃ κ) a u = 0 := by
    unfold gJ
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun m hm => ?_
    obtain ⟨h1, -, h3, h4, h5⟩ := (mem_setJ m).1 hm
    have hm2 : (0 : ℝ) < m.2.1 := by linarith
    have hm1 : (1 : ℝ) ≤ |(m.1 : ℝ)| := by
      have hne : m.1 ≠ 0 := by
        rintro h
        rw [h, Int.cast_zero, abs_zero] at h1
        linarith
      have := Int.one_le_abs hne
      have : ((1 : ℤ) : ℝ) ≤ ((|m.1| : ℤ) : ℝ) := by exact_mod_cast this
      simpa [Int.cast_abs] using this
    have hκ : |(m.2.2 : ℝ)| ≤ |κ * M₃| := h5.trans (le_abs_self _)
    have hnum : 2 * M₂ * |A| + 1 < |(m.1 : ℝ) * u + m.2.2| := by
      have e1 : |(m.1 : ℝ) * u| = |(m.1 : ℝ)| * |u| := abs_mul _ _
      have e2 : |(m.1 : ℝ) * u| - |(m.2.2 : ℝ)| ≤ |(m.1 : ℝ) * u + m.2.2| := by
        have := abs_add_le (m.1 * u + m.2.2 : ℝ) (-(m.2.2 : ℝ))
        rw [add_neg_cancel_right, abs_neg] at this
        linarith
      have e3 : |u| ≤ |(m.1 : ℝ)| * |u| := le_mul_of_one_le_left (abs_nonneg _) hm1
      linarith
    have hA : |A| < |((m.1 : ℝ) * u + m.2.2) / m.2.1| := by
      rw [abs_div, abs_of_pos hm2, lt_div_iff₀ hm2]
      have hA0 := abs_nonneg A
      nlinarith
    rw [hfA b _ ((le_abs_self A).trans_lt hA), zero_mul]
  rw [h0]
  ring

/-! ### `S₃,₄` in the form of their `J` -/

lemma neg_mem_boxM {M : ℕ} {m : ℤ} (h : m ∈ boxM M) : -m ∈ boxM M := by
  unfold boxM at h ⊢
  rw [Finset.mem_erase, Finset.mem_Icc] at h ⊢
  omega

/-- The block is closed under `m ↦ −m`. -/
lemma neg_mem_blk {M k : ℕ} {m : ℤ × ℤ × ℤ} (hm : m ∈ blk M k) : -m ∈ blk M k := by
  unfold blk at hm ⊢
  simp only [Finset.mem_filter, Finset.mem_product] at hm ⊢
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hm
  simp only [Prod.fst_neg, Prod.snd_neg, abs_neg, Int.natAbs_neg]
  exact ⟨⟨neg_mem_boxM h1, neg_mem_boxM h2, neg_mem_boxM h3⟩, h4, h5, h6⟩

/-- The block is closed under the swap `(m₁, m₂, m₃) ↦ (m₃, m₂, m₁)`. -/
lemma swap_mem_blk {M k : ℕ} {m : ℤ × ℤ × ℤ} (hm : m ∈ blk M k) : (m.2.2, m.2.1, m.1) ∈ blk M k := by
  unfold blk at hm ⊢
  simp only [Finset.mem_filter, Finset.mem_product] at hm ⊢
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hm
  exact ⟨⟨h3, h2, h1⟩, h4, h6, h5⟩

/-- On the block, `m₁, m₂ ≠ 0`, `|m₁|, |m₃| ≤ |m₂|` and `2^k ≤ |m₂| < 2^{k+1}`. -/
lemma blk_abs {M k : ℕ} {m : ℤ × ℤ × ℤ} (hm : m ∈ blk M k) :
    m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ |m.1| ≤ |m.2.1| ∧ |m.2.2| ≤ |m.2.1| ∧ 2 ^ k ≤ m.2.1.natAbs ∧ m.2.1.natAbs < 2 ^ (k + 1) := by
  unfold blk at hm
  simp only [Finset.mem_filter, Finset.mem_product] at hm
  obtain ⟨⟨h1, h2, -⟩, h4, h5, h6⟩ := hm
  obtain ⟨hne1, -⟩ := mem_boxM h1
  obtain ⟨hne2, -⟩ := mem_boxM h2
  have hn : m.2.1.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hne2
  refine ⟨hne1, hne2, h5, h6, ?_, ?_⟩
  · have := Nat.pow_log_le_self 2 hn
    rwa [h4] at this
  · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m.2.1.natAbs
    rwa [h4] at this

/-- A triple of the block with `m₂ > 0` lies in their range at `M₁ = 2^j − 1/2`, `j = ⌊log₂|m₁|⌋ ≤ k`,
`M₂ = M₃ = 2^k − 1/2` and `κ = 2`. -/
lemma mem_setJ_of_blk {M k : ℕ} {m : ℤ × ℤ × ℤ} (hm : m ∈ blk M k) (hpos : 0 < m.2.1) :
    Nat.log 2 m.1.natAbs < k + 1 ∧
      m ∈ setJ (2 ^ Nat.log 2 m.1.natAbs - 1 / 2) (2 ^ k - 1 / 2) (2 ^ k - 1 / 2) 2 := by
  obtain ⟨hne1, -, h12, h32, hk1, hk2⟩ := blk_abs hm
  have hn1 : m.1.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hne1
  set j := Nat.log 2 m.1.natAbs with hj
  have hj1 : 2 ^ j ≤ m.1.natAbs := Nat.pow_log_le_self 2 hn1
  have hj2 : m.1.natAbs < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h12n : m.1.natAbs ≤ m.2.1.natAbs := by
    have : (m.1.natAbs : ℤ) ≤ (m.2.1.natAbs : ℤ) := by rw [Int.natCast_natAbs, Int.natCast_natAbs]; exact h12
    exact_mod_cast this
  refine ⟨Nat.log_lt_of_lt_pow hn1 (lt_of_le_of_lt h12n hk2), ?_⟩
  have habs1 : |(m.1 : ℝ)| = (m.1.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have habs2 : (m.2.1 : ℝ) = (m.2.1.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
  have habs3 : |(m.2.2 : ℝ)| ≤ (m.2.1.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact_mod_cast h32
  have e1 : ((2 ^ j : ℕ) : ℝ) ≤ (m.1.natAbs : ℝ) := by exact_mod_cast hj1
  have e2 : (m.1.natAbs : ℝ) + 1 ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hj2
  have e3 : ((2 ^ k : ℕ) : ℝ) ≤ (m.2.1.natAbs : ℝ) := by exact_mod_cast hk1
  have e4 : (m.2.1.natAbs : ℝ) + 1 ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hk2
  push_cast at e1 e2 e3 e4
  rw [pow_succ] at e2 e4
  rw [mem_setJ, habs1, habs2]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Their range at `M₁ = 2^j − 1/2`, `M₂ = M₃ = 2^k − 1/2` and `κ = 2`. -/
def Jset (k j : ℕ) : Finset (ℤ × ℤ × ℤ) := setJ (2 ^ j - 1 / 2) (2 ^ k - 1 / 2) (2 ^ k - 1 / 2) 2

/-- **The inner sum of `S₃,₄` against their `J`-sums**: for `v ∈ [1/2, 2]` and nonnegative `f` with
`R̃(c, b)² ≤ f_{−b}(c)` for `|c| ≤ 3`, `Q(v, b₁) ≤ 2Σ_{j≤k}gJ(f, Jset k j, b₁, v)`. -/
lemma Qb_le_gJ {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {X : ℝ} {M k : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} (hf0 : ∀ b u, 0 ≤ f b u)
    (hfR : ∀ (b : (ZMod q)ˣ) (c : ℝ), |c| ≤ 3 → Rt N R χ t X (2 ^ k) c (b : ZMod q) ^ 2 ≤ f (-b) c)
    {v : ℝ} (hv : v ∈ Icc (1 / 2 : ℝ) 2) (b₁ : (ZMod q)ˣ) :
    Qb N R χ t X (2 ^ k) (blk M k) v b₁ ≤ 2 * ∑ j ∈ Finset.range (k + 1), gJ f (Jset k j) b₁ v := by
  set B := blk M k with hB
  set F : (ZMod q)ˣ → ℤ × ℤ × ℤ → ℝ := fun b m => f b (c₂ m v) * gJw b₁ b m with hF
  have hF0 : ∀ b m, 0 ≤ F b m := fun b m => mul_nonneg (hf0 _ _) (gJw_nonneg _ _ _)
  -- the centre is in `[−3, 3]`
  have hc : ∀ m ∈ B, |c₂ m v| ≤ 3 := fun m hm => by
    obtain ⟨-, hne2, h12, h32, -, -⟩ := blk_abs hm
    have hm2 : (0 : ℝ) < |(m.2.1 : ℝ)| := abs_pos.2 (by exact_mod_cast hne2)
    have r12 : |(m.1 : ℝ)| ≤ |(m.2.1 : ℝ)| := by rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast h12
    have r32 : |(m.2.2 : ℝ)| ≤ |(m.2.1 : ℝ)| := by rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast h32
    unfold c₂
    rw [abs_div, div_le_iff₀ hm2]
    calc |(m.1 : ℝ) * v + m.2.2| ≤ |(m.1 : ℝ)| * v + |(m.2.2 : ℝ)| := by
          have := abs_add_le ((m.1 : ℝ) * v) (m.2.2 : ℝ)
          rw [abs_mul, abs_of_pos (by linarith [hv.1] : (0 : ℝ) < v)] at this
          exact this
      _ ≤ |(m.2.1 : ℝ)| * 2 + |(m.2.1 : ℝ)| := by nlinarith [hv.2, abs_nonneg (m.1 : ℝ)]
      _ = 3 * |(m.2.1 : ℝ)| := by ring
  -- `R̃² ≤ f_{−b₂}` and `b₂ = −b`
  have step1 : Qb N R χ t X (2 ^ k) B v b₁ ≤ ∑ b : (ZMod q)ˣ, ∑ m ∈ B, F b m := by
    unfold Qb
    calc ∑ b₂ : (ZMod q)ˣ, ∑ m ∈ B, Rt N R χ t X (2 ^ k) (c₂ m v) (b₂ : ZMod q) ^ 2 * gw b₁ b₂ m
        ≤ ∑ b₂ : (ZMod q)ˣ, ∑ m ∈ B, F (-b₂) m := by
          refine Finset.sum_le_sum fun b₂ _ => Finset.sum_le_sum fun m hm => ?_
          have hw : gw b₁ b₂ m = gJw b₁ (-b₂) m := by
            unfold gw gJw
            rw [Units.val_neg]
            congr 3
            ring
          rw [hw]
          exact mul_le_mul_of_nonneg_right (hfR b₂ _ (hc m hm)) (gJw_nonneg _ _ _)
      _ = ∑ b : (ZMod q)ˣ, ∑ m ∈ B, F b m :=
          Fintype.sum_equiv (Equiv.neg (ZMod q)ˣ) _ _ fun b₂ => rfl
  -- the negatives: a factor `2`
  have step2 : ∀ b, ∑ m ∈ B, F b m = 2 * ∑ m ∈ B.filter (fun m => 0 < m.2.1), F b m := by
    intro b
    rw [← Finset.sum_filter_add_sum_filter_not B (fun m => 0 < m.2.1)]
    have hneg : ∑ m ∈ B.filter (fun m => ¬0 < m.2.1), F b m = ∑ m ∈ B.filter (fun m => 0 < m.2.1), F b m := by
      refine Finset.sum_nbij' (fun m => -m) (fun m => -m) ?_ ?_ (fun m _ => neg_neg m) (fun m _ => neg_neg m) ?_
      · intro m hm
        rw [Finset.mem_filter] at hm ⊢
        refine ⟨neg_mem_blk hm.1, ?_⟩
        have := (blk_abs hm.1).2.1
        simp only [Prod.snd_neg, Prod.fst_neg]
        omega
      · intro m hm
        rw [Finset.mem_filter] at hm ⊢
        refine ⟨neg_mem_blk hm.1, ?_⟩
        simp only [Prod.snd_neg, Prod.fst_neg]
        omega
      · intro m _
        have hc2 : c₂ (-m) v = c₂ m v := by
          unfold c₂
          simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
          rw [show -(m.1 : ℝ) * v + -(m.2.2 : ℝ) = -((m.1 : ℝ) * v + m.2.2) by ring, neg_div_neg_eq]
        have hw : gJw b₁ b (-m) = gJw b₁ b m := by
          unfold gJw
          simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
          rw [show (b₁ : ZMod q) * -(m.1 : ZMod q) + (b : ZMod q) * -(m.2.1 : ZMod q) + -(m.2.2 : ZMod q) =
            -((b₁ : ZMod q) * (m.1 : ZMod q) + (b : ZMod q) * (m.2.1 : ZMod q) + (m.2.2 : ZMod q)) by ring,
            gcd_val_neg]
        simp only [hF, hc2, hw]
    rw [hneg]
    ring
  -- the dyadic split of `m₁`
  have step3 : ∀ b, ∑ m ∈ B.filter (fun m => 0 < m.2.1), F b m ≤
      ∑ j ∈ Finset.range (k + 1), ∑ m ∈ Jset k j, F b m := by
    intro b
    calc ∑ m ∈ B.filter (fun m => 0 < m.2.1), F b m
        ≤ ∑ m ∈ B.filter (fun m => 0 < m.2.1), ∑ j ∈ Finset.range (k + 1),
            (if m ∈ Jset k j then F b m else 0) := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [Finset.mem_filter] at hm
          obtain ⟨hjk, hmJ⟩ := mem_setJ_of_blk hm.1 hm.2
          have hle := Finset.single_le_sum (f := fun j => if m ∈ Jset k j then F b m else 0)
            (fun j _ => by split_ifs; exacts [hF0 b m, le_rfl]) (Finset.mem_range.2 hjk)
          have hmJ' : m ∈ Jset k (Nat.log 2 m.1.natAbs) := hmJ
          simp only [hmJ', ite_true] at hle
          exact hle
      _ = ∑ j ∈ Finset.range (k + 1), ∑ m ∈ B.filter (fun m => 0 < m.2.1),
            (if m ∈ Jset k j then F b m else 0) := Finset.sum_comm
      _ = ∑ j ∈ Finset.range (k + 1), ∑ m ∈ (B.filter (fun m => 0 < m.2.1)).filter (· ∈ Jset k j), F b m :=
          Finset.sum_congr rfl fun j _ => (Finset.sum_filter _ _).symm
      _ ≤ ∑ j ∈ Finset.range (k + 1), ∑ m ∈ Jset k j, F b m := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hF0 b m
          intro m hm
          exact (Finset.mem_filter.1 hm).2
  calc Qb N R χ t X (2 ^ k) B v b₁ ≤ ∑ b : (ZMod q)ˣ, ∑ m ∈ B, F b m := step1
    _ = ∑ b : (ZMod q)ˣ, 2 * ∑ m ∈ B.filter (fun m => 0 < m.2.1), F b m :=
        Finset.sum_congr rfl fun b _ => step2 b
    _ ≤ ∑ b : (ZMod q)ˣ, 2 * ∑ j ∈ Finset.range (k + 1), ∑ m ∈ Jset k j, F b m :=
        Finset.sum_le_sum fun b _ => by linarith [step3 b]
    _ = 2 * ∑ j ∈ Finset.range (k + 1), gJ f (Jset k j) b₁ v := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        rfl

/-- **`S₃,₄` against their `J`**: for `L = 2^kN/q ≥ 0` and `f` nonnegative, continuous, `0` beyond `A`, with
`R̃(c, b)² ≤ f_{−b}(c)` for `|c| ≤ 3`, `S₃,₄ ≤ 4(k + 1)Σ_{j≤k}Jint(f, 2^j − 1/2, 2^k − 1/2, 2^k − 1/2, 2)`. -/
theorem S34_le_Jint {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {X : ℝ} {M k : ℕ} (hL : 0 ≤ N * 2 ^ k / q) {f : (ZMod q)ˣ → ℝ → ℝ} (hf0 : ∀ b u, 0 ≤ f b u)
    (hfc : ∀ b, Continuous (f b)) {A : ℝ} (hfA : ∀ b u, A < |u| → f b u = 0)
    (hfR : ∀ (b : (ZMod q)ˣ) (c : ℝ), |c| ≤ 3 → Rt N R χ t X (2 ^ k) c (b : ZMod q) ^ 2 ≤ f (-b) c) :
    S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤
      4 * (k + 1) * ∑ j ∈ Finset.range (k + 1), Jint f (2 ^ j - 1 / 2) (2 ^ k - 1 / 2) (2 ^ k - 1 / 2) 2 := by
  have hJint : ∀ j, Jint f (2 ^ j - 1 / 2) (2 ^ k - 1 / 2) (2 ^ k - 1 / 2) 2 =
      ∫ u, ∑ a : (ZMod q)ˣ, gJ f (Jset k j) a u ^ 2 := fun j => rfl
  simp only [hJint]
  have hcont : ∀ j a, Continuous fun u => gJ f (Jset k j) a u := fun j a => by
    unfold gJ
    refine continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun m _ => ?_
    exact ((hfc b).comp (by fun_prop)).mul continuous_const
  have hGc : ∀ j, Continuous fun u => ∑ a : (ZMod q)ˣ, gJ f (Jset k j) a u ^ 2 := fun j =>
    continuous_finsetSum _ fun a _ => (hcont j a).pow 2
  have hpos2 : ∀ j : ℕ, (0 : ℝ) ≤ 2 ^ j - 1 / 2 := fun j => by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    linarith
  have hpos2k : (0 : ℝ) < 2 ^ k - 1 / 2 := by
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    linarith
  have hGi : ∀ j, Integrable fun u => ∑ a : (ZMod q)ˣ, gJ f (Jset k j) a u ^ 2 := fun j =>
    integrable_Jsum hfc hfA (hpos2 j) hpos2k
  -- pointwise
  have hpt : ∀ v ∈ Icc (1 / 2 : ℝ) 2, ∑ b₁ : (ZMod q)ˣ, Qb N R χ t X (2 ^ k) (blk M k) v b₁ ^ 2 ≤
      4 * (k + 1) * ∑ j ∈ Finset.range (k + 1), ∑ a : (ZMod q)ˣ, gJ f (Jset k j) a v ^ 2 := by
    intro v hv
    have h1 : ∀ b₁ : (ZMod q)ˣ, Qb N R χ t X (2 ^ k) (blk M k) v b₁ ^ 2 ≤
        4 * (k + 1) * ∑ j ∈ Finset.range (k + 1), gJ f (Jset k j) b₁ v ^ 2 := by
      intro b₁
      have hQ := Qb_le_gJ R χ t (M := M) hf0 hfR hv b₁
      have hQ0 := Qb_nonneg R χ t (blk M k) (N := N) (X := X) (M₂ := 2 ^ k) v b₁
      have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 1)) (f := fun j => gJ f (Jset k j) b₁ v)
      rw [Finset.card_range] at hcs
      calc Qb N R χ t X (2 ^ k) (blk M k) v b₁ ^ 2
          ≤ (2 * ∑ j ∈ Finset.range (k + 1), gJ f (Jset k j) b₁ v) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
        _ = 4 * (∑ j ∈ Finset.range (k + 1), gJ f (Jset k j) b₁ v) ^ 2 := by ring
        _ ≤ 4 * (((k + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (k + 1), gJ f (Jset k j) b₁ v ^ 2) := by
            linarith [hcs]
        _ = 4 * (k + 1) * ∑ j ∈ Finset.range (k + 1), gJ f (Jset k j) b₁ v ^ 2 := by push_cast; ring
    calc ∑ b₁ : (ZMod q)ˣ, Qb N R χ t X (2 ^ k) (blk M k) v b₁ ^ 2
        ≤ ∑ b₁ : (ZMod q)ˣ, 4 * (k + 1) * ∑ j ∈ Finset.range (k + 1), gJ f (Jset k j) b₁ v ^ 2 :=
          Finset.sum_le_sum fun b₁ _ => h1 b₁
      _ = 4 * (k + 1) * ∑ j ∈ Finset.range (k + 1), ∑ a : (ZMod q)ˣ, gJ f (Jset k j) a v ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
  -- integrate
  have hLHS : IntegrableOn (fun v => ∑ b₁ : (ZMod q)ˣ, Qb N R χ t X (2 ^ k) (blk M k) v b₁ ^ 2)
      (Icc (1 / 2 : ℝ) 2) := by
    refine integrableOn_Icc_of_le (Finset.measurable_sum _ fun b _ => (measurable_Qb R χ t (blk M k) b).pow_const 2)
      (C := Fintype.card (ZMod q)ˣ * Cb q N (2 ^ k) R (blk M k) ^ 2) fun v _ => ?_
    rw [abs_of_nonneg (Finset.sum_nonneg fun b _ => sq_nonneg _)]
    calc ∑ b₁ : (ZMod q)ˣ, Qb N R χ t X (2 ^ k) (blk M k) v b₁ ^ 2 ≤
          ∑ _b₁ : (ZMod q)ˣ, Cb q N (2 ^ k) R (blk M k) ^ 2 :=
          Finset.sum_le_sum fun b _ =>
            pow_le_pow_left₀ (Qb_nonneg R χ t (blk M k) v b) (Qb_le R χ t (blk M k) hL v b) 2
      _ = Fintype.card (ZMod q)ˣ * Cb q N (2 ^ k) R (blk M k) ^ 2 := by simp
  have hRHS : IntegrableOn (fun v => 4 * (k + 1) * ∑ j ∈ Finset.range (k + 1),
      ∑ a : (ZMod q)ˣ, gJ f (Jset k j) a v ^ 2) (Icc (1 / 2 : ℝ) 2) :=
    (continuous_const.mul (continuous_finsetSum _ fun j _ => hGc j)).integrableOn_Icc
  unfold S34
  calc ∫ v in Icc (1 / 2 : ℝ) 2, ∑ b₁ : (ZMod q)ˣ, Qb N R χ t X (2 ^ k) (blk M k) v b₁ ^ 2
      ≤ ∫ v in Icc (1 / 2 : ℝ) 2, 4 * (k + 1) * ∑ j ∈ Finset.range (k + 1),
          ∑ a : (ZMod q)ˣ, gJ f (Jset k j) a v ^ 2 :=
        setIntegral_mono_on hLHS hRHS measurableSet_Icc hpt
    _ = 4 * (k + 1) * ∑ j ∈ Finset.range (k + 1), ∫ v in Icc (1 / 2 : ℝ) 2,
          ∑ a : (ZMod q)ˣ, gJ f (Jset k j) a v ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun j _ => (hGc j).integrableOn_Icc]
    _ ≤ 4 * (k + 1) * ∑ j ∈ Finset.range (k + 1), ∫ u, ∑ a : (ZMod q)ˣ, gJ f (Jset k j) a u ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
        exact setIntegral_le_integral (hGi j) (Eventually.of_forall fun u =>
          Finset.sum_nonneg fun a _ => sq_nonneg _)

/-! ### `S₃,₃` against `S₃,₄`: their change of variables `u = v⁻¹` -/

/-- **Their change of variables in the inner sum**: for `u > 0` and `B` closed under the swap,
`P(u⁻¹, b₁) = Q(u, b₁⁻¹)`. -/
lemma Pb_inv_eq {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {X M₂ : ℝ} {B : Finset (ℤ × ℤ × ℤ)} (hB : ∀ m ∈ B, (m.2.2, m.2.1, m.1) ∈ B) {u : ℝ} (hu : 0 < u)
    (b₁ : (ZMod q)ˣ) :
    Pb N R χ t X M₂ B u⁻¹ b₁ = Qb N R χ t X M₂ B u b₁⁻¹ := by
  unfold Pb Qb
  -- `b₂ = b₁b`
  rw [← Fintype.sum_equiv (Equiv.mulLeft b₁) _ _ fun b => rfl]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
  -- the swap
  refine Finset.sum_nbij' (fun m => (m.2.2, m.2.1, m.1)) (fun m => (m.2.2, m.2.1, m.1)) (fun m hm => hB m hm)
    (fun m hm => hB m hm) (fun m _ => rfl) (fun m _ => rfl) fun m _ => ?_
  have hc : c₁ m u⁻¹ = c₂ (m.2.2, m.2.1, m.1) u := by
    unfold c₁ c₂
    simp only
    have hu0 : u ≠ 0 := hu.ne'
    by_cases hm2 : (m.2.1 : ℝ) = 0
    · rw [hm2]; simp
    · field_simp
      ring
  have hw : gw b₁ (b₁ * b) m = gw b₁⁻¹ b (m.2.2, m.2.1, m.1) := by
    unfold gw
    simp only [Units.val_mul]
    have e : (b₁ : ZMod q) * (m.1 : ZMod q) - (b₁ : ZMod q) * (b : ZMod q) * (m.2.1 : ZMod q) + (m.2.2 : ZMod q) =
        (b₁ : ZMod q) * ((((b₁⁻¹ : (ZMod q)ˣ) : ZMod q)) * (m.2.2 : ZMod q) - (b : ZMod q) * (m.2.1 : ZMod q) +
          (m.1 : ZMod q)) := by
      have h1 : (b₁ : ZMod q) * ((b₁⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := Units.mul_inv b₁
      linear_combination (-(m.2.2 : ZMod q)) * h1
    rw [e, gcd_val_unit_mul]
  rw [hc, hw]

/-- **`S₃,₃ ≤ 4S₃,₄`** for `L ≥ 0` and `B` closed under the swap `(m₁, m₂, m₃) ↦ (m₃, m₂, m₁)`: their change of
variables `u = v⁻¹`, with `|dv/du| = u⁻² ≤ 4` on `[1/2, 2]`. -/
theorem S33_le_S34 {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {X M₂ : ℝ} (hL : 0 ≤ N * M₂ / q) {B : Finset (ℤ × ℤ × ℤ)}
    (hB : ∀ m ∈ B, (m.2.2, m.2.1, m.1) ∈ B) :
    S33 R χ t (X := X) (M₂ := M₂) B (N := N) ≤ 4 * S34 R χ t (X := X) (M₂ := M₂) B (N := N) := by
  set s := Icc (1 / 2 : ℝ) 2 with hs
  set F : ℝ → ℝ := fun v => ∑ b₁ : (ZMod q)ˣ, Pb N R χ t X M₂ B v b₁ ^ 2 with hF
  set G : ℝ → ℝ := fun u => ∑ b₁ : (ZMod q)ˣ, Qb N R χ t X M₂ B u b₁ ^ 2 with hG
  have himage : (fun u : ℝ => u⁻¹) '' s = s := by
    ext v
    simp only [hs, mem_image, mem_Icc]
    constructor
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      have hu : 0 < u := by linarith
      refine ⟨?_, ?_⟩
      · rw [le_inv_comm₀ (by norm_num) hu]; linarith
      · rw [inv_le_comm₀ hu (by norm_num)]; linarith
    · rintro ⟨h1, h2⟩
      have hv : 0 < v := by linarith
      refine ⟨v⁻¹, ⟨?_, ?_⟩, inv_inv v⟩
      · rw [le_inv_comm₀ (by norm_num) hv]; linarith
      · rw [inv_le_comm₀ hv (by norm_num)]; linarith
  have hderiv : ∀ u ∈ s, HasDerivWithinAt (fun u : ℝ => u⁻¹) (-(u ^ 2)⁻¹) s u := fun u hu =>
    (hasDerivAt_inv (by linarith [hu.1] : u ≠ 0)).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => u⁻¹) s := inv_injective.injOn
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj F
  rw [himage] at hcv
  have hFG : ∀ u ∈ s, F u⁻¹ = G u := fun u hu => by
    have hu : 0 < u := by linarith [hu.1]
    simp only [hF, hG]
    calc ∑ b₁ : (ZMod q)ˣ, Pb N R χ t X M₂ B u⁻¹ b₁ ^ 2 = ∑ b₁ : (ZMod q)ˣ, Qb N R χ t X M₂ B u b₁⁻¹ ^ 2 :=
          Finset.sum_congr rfl fun b₁ _ => by rw [Pb_inv_eq R χ t hB hu b₁]
      _ = ∑ a : (ZMod q)ˣ, Qb N R χ t X M₂ B u a ^ 2 :=
          Fintype.sum_equiv (Equiv.inv (ZMod q)ˣ) _ _ fun b₁ => rfl
  have hGm : Measurable G := Finset.measurable_sum _ fun b _ => (measurable_Qb R χ t B b).pow_const 2
  have hG0 : ∀ u, 0 ≤ G u := fun u => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hGb : ∀ u, G u ≤ Fintype.card (ZMod q)ˣ * Cb q N M₂ R B ^ 2 := fun u => by
    calc G u ≤ ∑ _b₁ : (ZMod q)ˣ, Cb q N M₂ R B ^ 2 :=
          Finset.sum_le_sum fun b _ => pow_le_pow_left₀ (Qb_nonneg R χ t B u b) (Qb_le R χ t B hL u b) 2
      _ = Fintype.card (ZMod q)ˣ * Cb q N M₂ R B ^ 2 := by simp
  have h4 : ∀ u ∈ s, |-(u ^ 2)⁻¹| ≤ 4 := fun u hu => by
    have hu1 : (1 / 2 : ℝ) ≤ u := hu.1
    rw [abs_neg, abs_of_pos (by positivity)]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hFm : Measurable fun u : ℝ => F u⁻¹ :=
    Finset.measurable_sum _ fun b _ => ((measurable_Pb R χ t B b).comp measurable_inv).pow_const 2
  have hint1 : IntegrableOn (fun u => |-(u ^ 2)⁻¹| • F u⁻¹) s := by
    refine integrableOn_Icc_of_le ((by fun_prop : Measurable fun u : ℝ => |-(u ^ 2)⁻¹|).smul hFm)
      (C := 4 * (Fintype.card (ZMod q)ˣ * Cb q N M₂ R B ^ 2)) fun u hu => ?_
    rw [smul_eq_mul, hFG u hu, abs_mul, abs_abs, abs_of_nonneg (hG0 u)]
    exact mul_le_mul (h4 u hu) (hGb u) (hG0 u) (by norm_num)
  have hint2 : IntegrableOn (fun u => 4 * G u) s := by
    refine integrableOn_Icc_of_le (measurable_const.mul hGm)
      (C := 4 * (Fintype.card (ZMod q)ˣ * Cb q N M₂ R B ^ 2)) fun u _ => ?_
    rw [abs_of_nonneg (by linarith [hG0 u])]
    linarith [hGb u]
  unfold S33 S34
  change ∫ v in s, F v ≤ 4 * ∫ u in s, G u
  rw [hcv, ← integral_const_mul]
  refine setIntegral_mono_on hint1 hint2 measurableSet_Icc fun u hu => ?_
  rw [smul_eq_mul, hFG u hu]
  exact mul_le_mul_of_nonneg_right (h4 u hu) (hG0 u)

end LinnikCGLJ

#print axioms LinnikCGLJ.gcd_val_unit_mul
#print axioms LinnikCGLJ.integrable_Jsum
#print axioms LinnikCGLJ.S34_le_Jint
#print axioms LinnikCGLJ.S33_le_S34
