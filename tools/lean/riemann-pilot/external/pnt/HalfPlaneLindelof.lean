/-
# Round 470: a Lindelöf bound in a zero-free half-plane

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. If `ζ(s) ≠ 0` on `Re s > θ`, with `0 ≤ θ < 1`, then for every `σ₀ > θ` and every `ε > 0`
there are `T` and `C` with `|ζ(σ + it)| ≤ C|t|^ε` and `1/|ζ(σ + it)| ≤ C|t|^ε` for `σ ≥ σ₀` and `|t| ≥ T`
(`zeta_bound_of_zeroFree`). With no hypothesis at `θ = 11/12` (`zeta_bound_eleven_twelfths`, from round 466's
half-plane), and at `θ = Θ`, round 469's supremum of the real parts of the zeros (`zeta_bound_Theta`).

* `norm_le_interp`: a localized three-lines bound, by the maximum modulus principle on a rectangle with
  the weight `exp((z − it₀)² − (b − z)c₁ − (z − a)c₂)`.
* `logDeriv_le_interp`: a bound `|ζ′/ζ(σ + it)| ≤ C₁ log|t|` on `σ ≥ a` (in the main theorem, round 337's
  `logDeriv_le_of_zeroFree`), interpolated against a bound `B` on `Re s ≥ 3/2` (PNT+'s
  `LogDerivZetaBdd_of_Re_ge_three_halves`) on the rectangle `[a, 3/2] × [t − |t|/2, t + |t|/2]`.
* `hasDerivAt_log_norm`: the derivative of `u ↦ log|f(u)|` is `Re(f′/f)`.
* `norm_zeta_le_three_halves`, `inv_norm_zeta_le_three_halves`: `|ζ(s)|` and `1/|ζ(s)|` are at most
  `ζ(3/2)` on `Re s ≥ 3/2`.
* `zeta_bound_of_zeroFree`: the mean value inequality for `log|ζ(u + it)|` on `[σ, 3/2]`, with the
  interpolated bound `C(log|t|)^κ`, `κ < 1`.
-/
import PsiExponent

open Complex Set Filter Topology

namespace HalfPlaneLindelof

/-- The modulus of the weight: for `z = x + iy`, `|exp((z − it₀)² − (b − z)c₁ − (z − a)c₂)|` is
`exp(x² − (y − t₀)² − (b − x)c₁ − (x − a)c₂)`. -/
theorem norm_exp_weight (z : ℂ) (t₀ c₁ c₂ a b : ℝ) :
    ‖Complex.exp ((z - t₀ * I) ^ 2 - (b - z) * c₁ - (z - a) * c₂)‖ =
      Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2 - (b - z.re) * c₁ - (z.re - a) * c₂) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [sq, Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **Interpolation on a rectangle**, a localized form of Hadamard's three lines: a bound `A` on the closed
rectangle `[a, b] × [t₀ − W, t₀ + W]` and a bound `B` on its right edge give
`|F(σ + it₀)| ≤ e^{b² − σ²} A^{(b−σ)/(b−a)} B^{(σ−a)/(b−a)}`, once `log(A/B) ≤ W²`. -/
theorem norm_le_interp {F : ℂ → ℂ} {a b t₀ W A B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hW0 : 0 < W)
    (hB : 0 < B) (hBA : B ≤ A)
    (hF : DifferentiableOn ℂ F (Icc a b ×ℂ Icc (t₀ - W) (t₀ + W)))
    (hall : ∀ z ∈ Icc a b ×ℂ Icc (t₀ - W) (t₀ + W), ‖F z‖ ≤ A)
    (hright : ∀ y ∈ Icc (t₀ - W) (t₀ + W), ‖F (b + y * I)‖ ≤ B)
    (hW : Real.log (A / B) ≤ W ^ 2) {σ : ℝ} (hσ : σ ∈ Icc a b) :
    ‖F (σ + t₀ * I)‖ ≤
      Real.exp (b ^ 2 - σ ^ 2) * A ^ ((b - σ) / (b - a)) * B ^ ((σ - a) / (b - a)) := by
  have hA : 0 < A := hB.trans_le hBA
  have hba : 0 < b - a := by linarith
  set c₁ : ℝ := Real.log A / (b - a) with hc₁
  set c₂ : ℝ := Real.log B / (b - a) with hc₂
  set U : Set ℂ := Ioo a b ×ℂ Ioo (t₀ - W) (t₀ + W) with hU
  have hcl : closure U = Icc a b ×ℂ Icc (t₀ - W) (t₀ + W) := by
    rw [hU, closure_reProdIm, closure_Ioo hab.ne, closure_Ioo (by linarith)]
  set H : ℂ → ℂ := fun z => F z * Complex.exp ((z - t₀ * I) ^ 2 - (b - z) * c₁ - (z - a) * c₂) with hH
  have hHn : ∀ z, ‖H z‖ = ‖F z‖ *
      Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2 - (b - z.re) * c₁ - (z.re - a) * c₂) := by
    intro z; rw [hH, norm_mul, norm_exp_weight]
  have hlogAB : Real.log B ≤ Real.log A := Real.log_le_log hB hBA
  have hlogdiv : Real.log (A / B) = Real.log A - Real.log B := Real.log_div hA.ne' hB.ne'
  -- the bound on the frontier
  have hfr : ∀ z ∈ frontier U, ‖H z‖ ≤ Real.exp (b ^ 2) := by
    intro z hz
    rw [hU, frontier_reProdIm, closure_Ioo hab.ne, closure_Ioo (by linarith), frontier_Ioo hab,
      frontier_Ioo (by linarith)] at hz
    rcases hz with ⟨hre, him⟩ | ⟨hre, him⟩
    · -- top or bottom edge
      have hre' : z.re ∈ Icc a b := hre
      have him' : z.im = t₀ - W ∨ z.im = t₀ + W := him
      have hz' : z ∈ Icc a b ×ℂ Icc (t₀ - W) (t₀ + W) := by
        refine ⟨hre', ?_⟩
        show z.im ∈ Icc (t₀ - W) (t₀ + W)
        rcases him' with h | h <;> rw [h] <;> constructor <;> linarith
      have hyW : (z.im - t₀) ^ 2 = W ^ 2 := by
        rcases him' with h | h <;> rw [h] <;> ring
      rw [hHn, hyW]
      have hFz := hall z hz'
      obtain ⟨hx1, hx2⟩ := hre'
      have hl0 : 0 ≤ (z.re - a) / (b - a) := div_nonneg (by linarith) hba.le
      have hl1 : (z.re - a) / (b - a) ≤ 1 := (div_le_one hba).2 (by linarith)
      have key : z.re ^ 2 - W ^ 2 - (b - z.re) * c₁ - (z.re - a) * c₂ ≤ b ^ 2 - Real.log A := by
        have e : z.re ^ 2 - W ^ 2 - (b - z.re) * c₁ - (z.re - a) * c₂ =
            z.re ^ 2 - W ^ 2 - Real.log A + ((z.re - a) / (b - a)) * (Real.log A - Real.log B) := by
          rw [hc₁, hc₂]; field_simp; ring
        rw [e]
        have h1 : ((z.re - a) / (b - a)) * (Real.log A - Real.log B) ≤ Real.log A - Real.log B := by
          have := sub_nonneg.2 hlogAB
          calc ((z.re - a) / (b - a)) * (Real.log A - Real.log B) ≤ 1 * (Real.log A - Real.log B) :=
                mul_le_mul_of_nonneg_right hl1 this
            _ = Real.log A - Real.log B := one_mul _
        have h2 : z.re ^ 2 ≤ b ^ 2 := by nlinarith
        linarith [hW, hlogdiv]
      calc ‖F z‖ * Real.exp (z.re ^ 2 - W ^ 2 - (b - z.re) * c₁ - (z.re - a) * c₂)
          ≤ A * Real.exp (b ^ 2 - Real.log A) :=
            mul_le_mul hFz (Real.exp_le_exp.2 key) (Real.exp_pos _).le hA.le
        _ = Real.exp (b ^ 2) := by
            rw [Real.exp_sub, Real.exp_log hA]; field_simp
    · -- left or right edge
      have hre' : z.re = a ∨ z.re = b := hre
      have him' : z.im ∈ Icc (t₀ - W) (t₀ + W) := him
      rw [hHn]
      rcases hre' with hza | hzb
      · -- left edge
        have hz' : z ∈ Icc a b ×ℂ Icc (t₀ - W) (t₀ + W) := by
          refine ⟨?_, him'⟩
          show z.re ∈ Icc a b
          rw [hza]; exact ⟨le_rfl, hab.le⟩
        rw [hza]
        have key : a ^ 2 - (z.im - t₀) ^ 2 - (b - a) * c₁ - (a - a) * c₂ ≤ b ^ 2 - Real.log A := by
          have e : (b - a) * c₁ = Real.log A := by rw [hc₁]; field_simp
          have : a ^ 2 ≤ b ^ 2 := by nlinarith
          nlinarith [sq_nonneg (z.im - t₀)]
        calc ‖F z‖ * Real.exp (a ^ 2 - (z.im - t₀) ^ 2 - (b - a) * c₁ - (a - a) * c₂)
            ≤ A * Real.exp (b ^ 2 - Real.log A) :=
              mul_le_mul (hall z hz') (Real.exp_le_exp.2 key) (Real.exp_pos _).le hA.le
          _ = Real.exp (b ^ 2) := by rw [Real.exp_sub, Real.exp_log hA]; field_simp
      · -- right edge
        have hzeq : z = (b : ℂ) + z.im * I := by
          conv_lhs => rw [← Complex.re_add_im z]
          rw [hzb]
        rw [hzb]
        have key : b ^ 2 - (z.im - t₀) ^ 2 - (b - b) * c₁ - (b - a) * c₂ ≤ b ^ 2 - Real.log B := by
          have e : (b - a) * c₂ = Real.log B := by rw [hc₂]; field_simp
          nlinarith [sq_nonneg (z.im - t₀)]
        have hFb : ‖F z‖ ≤ B := by rw [hzeq]; exact hright _ him'
        calc ‖F z‖ * Real.exp (b ^ 2 - (z.im - t₀) ^ 2 - (b - b) * c₁ - (b - a) * c₂)
            ≤ B * Real.exp (b ^ 2 - Real.log B) :=
              mul_le_mul hFb (Real.exp_le_exp.2 key) (Real.exp_pos _).le hB.le
          _ = Real.exp (b ^ 2) := by rw [Real.exp_sub, Real.exp_log hB]; field_simp
  -- maximum modulus
  have hbd : Bornology.IsBounded U :=
    ((isCompact_Icc.reProdIm isCompact_Icc).isBounded).subset (hcl ▸ subset_closure)
  have hdiff : DiffContOnCl ℂ H U := by
    apply DifferentiableOn.diffContOnCl
    rw [hcl]
    refine hF.mul ?_
    intro z _
    apply DifferentiableAt.differentiableWithinAt
    fun_prop
  have hre : ((σ : ℂ) + t₀ * I).re = σ := by simp
  have him : ((σ : ℂ) + t₀ * I).im = t₀ := by simp
  have hmem : (σ : ℂ) + t₀ * I ∈ closure U := by
    rw [hcl]
    refine ⟨?_, ?_⟩
    · show ((σ : ℂ) + t₀ * I).re ∈ Icc a b
      rw [hre]; exact hσ
    · show ((σ : ℂ) + t₀ * I).im ∈ Icc (t₀ - W) (t₀ + W)
      rw [him]; constructor <;> linarith
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hbd hdiff hfr hmem
  rw [hHn] at hmax
  rw [hre, him, sub_self, sq (0 : ℝ), mul_zero, sub_zero] at hmax
  have hpos := Real.exp_pos (σ ^ 2 - (b - σ) * c₁ - (σ - a) * c₂)
  rw [← le_div_iff₀ hpos, ← Real.exp_sub] at hmax
  refine hmax.trans (le_of_eq ?_)
  rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB, ← Real.exp_add, ← Real.exp_add, hc₁, hc₂]
  congr 1
  field_simp
  ring

/-- **The derivative of `log |f|`**: for `f : ℝ → ℂ` with `f(u) ≠ 0`, `u ↦ log|f(u)|` has derivative
`Re(f′(u)/f(u))` at `u`. -/
theorem hasDerivAt_log_norm {f : ℝ → ℂ} {f' : ℂ} {u : ℝ} (hf : HasDerivAt f f' u) (h0 : f u ≠ 0) :
    HasDerivAt (fun x => Real.log ‖f x‖) (f' / f u).re u := by
  have hn : ‖f u‖ ^ 2 ≠ 0 := by positivity
  have h1 := (hf.norm_sq.log hn).div_const 2
  have hfun : (fun x => Real.log (‖f x‖ ^ 2) / 2) = fun x => Real.log ‖f x‖ := by
    funext x; rw [Real.log_pow]; push_cast; ring
  rw [hfun] at h1
  convert h1 using 1
  rw [Complex.inner, Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.normSq_eq_norm_sq]
  field_simp
  ring

open LSeries in
/-- `|ζ(s)| ≤ ζ(3/2)` on `Re s ≥ 3/2`. -/
theorem norm_zeta_le_three_halves {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ := by
  have hs1 : 1 < s.re := by linarith
  have hsum := Landau.norm_term_one_summable (σ := 3 / 2) (by norm_num)
  have hζs : riemannZeta s = ∑' n, term (fun _ => (1 : ℂ)) s n := by
    rw [← LSeries_one_eq_riemannZeta hs1]; rfl
  have hle : ∀ n, ‖term (fun _ => (1 : ℂ)) s n‖ ≤ ‖term (fun _ => (1 : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖ := by
    intro n
    rw [norm_term_eq, norm_term_eq]
    split_ifs with hn
    · rfl
    · simp only [ofReal_re, norm_one]
      have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hn)
      gcongr
  have hsums : Summable (fun n => ‖term (fun _ => (1 : ℂ)) s n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum
  have hζ32 : riemannZeta ((3 / 2 : ℝ) : ℂ) = ∑' n, term (fun _ => (1 : ℂ)) ((3 / 2 : ℝ) : ℂ) n := by
    rw [← LSeries_one_eq_riemannZeta (by norm_num)]; rfl
  have h2 : ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ = ∑' n, ‖term (fun _ => (1 : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖ := by
    rw [hζ32, show (fun n => term (fun _ => (1 : ℂ)) ((3 / 2 : ℝ) : ℂ) n) =
      fun n => ((‖term (fun _ => (1 : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖ : ℝ) : ℂ) from
      funext Landau.term_one_eq_ofReal, ← ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
  calc ‖riemannZeta s‖ = ‖∑' n, term (fun _ => (1 : ℂ)) s n‖ := by rw [hζs]
    _ ≤ ∑' n, ‖term (fun _ => (1 : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsums
    _ ≤ ∑' n, ‖term (fun _ => (1 : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖ := hsums.tsum_le_tsum hle hsum
    _ = ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ := h2.symm

/-- `1/|ζ(s)| ≤ ζ(3/2)` on `Re s ≥ 3/2`. -/
theorem inv_norm_zeta_le_three_halves {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖riemannZeta s‖⁻¹ ≤ ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ := by
  have h := Landau.inv_norm_zeta_le (s := s) (by linarith)
  rw [one_div] at h
  exact h.trans (norm_zeta_le_three_halves (s := (s.re : ℂ)) (by simpa using hs))

/-- `y^κ ≤ δy` for large `y`, when `κ < 1` and `δ > 0`. -/
theorem rpow_le_mul_self {κ δ : ℝ} (hκ : κ < 1) (hδ : 0 < δ) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ y : ℝ, Y ≤ y → y ^ κ ≤ δ * y := by
  have h := (tendsto_rpow_neg_atTop (y := 1 - κ) (by linarith)).eventually (gt_mem_nhds hδ)
  obtain ⟨Y, hY⟩ := eventually_atTop.1 h
  refine ⟨max Y 1, by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hyY := hY y (le_trans (le_max_left _ _) hy)
  have e : y ^ (-(1 - κ)) * y = y ^ κ := by
    rw [← Real.rpow_add_one hy0.ne']; congr 1; ring
  rw [← e]
  exact mul_le_mul_of_nonneg_right hyY.le hy0.le

/-- **The interpolated bound on `ζ′/ζ`**: from `|ζ′/ζ(σ + it)| ≤ C₁ log|t|` on `σ ≥ a`, `|t| > 3`, and
`|ζ′/ζ| ≤ B` on `Re s ≥ 3/2`: for `|t| > 6` with `B + (3/2)C₁|t| ≤ (|t|/2)²` and `u ∈ [a, 3/2]`,
`|ζ′/ζ(u + it)| ≤ e^{9/4 − u²}·A^{(3/2−u)/(3/2−a)}·B^{(u−a)/(3/2−a)}` with `A = max(B, C₁ log(3|t|/2))`. -/
theorem logDeriv_le_interp {θ a C₁ B t u : ℝ} (hθa : θ < a) (ha0 : 0 ≤ a) (ha32 : a < 3 / 2)
    (hC₁ : 0 < C₁) (hB : 1 ≤ B)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0)
    (hlog : ∀ σ t : ℝ, 3 < |t| → a ≤ σ →
      ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C₁ * Real.log |t|)
    (hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ B)
    (ht6 : 6 < |t|) (htW : B + C₁ * (3 * |t| / 2) ≤ (|t| / 2) ^ 2) (hu : u ∈ Icc a (3 / 2)) :
    ‖deriv riemannZeta (u + t * I) / riemannZeta (u + t * I)‖ ≤
      Real.exp ((3 / 2) ^ 2 - u ^ 2) * max B (C₁ * Real.log (3 * |t| / 2)) ^ ((3 / 2 - u) / (3 / 2 - a)) *
        B ^ ((u - a) / (3 / 2 - a)) := by
  set A := max B (C₁ * Real.log (3 * |t| / 2)) with hAdef
  have hW0 : 0 < |t| / 2 := by linarith
  have hB0 : 0 < B := by linarith
  set R : Set ℂ := Icc a (3 / 2) ×ℂ Icc (t - |t| / 2) (t + |t| / 2) with hR
  have him : ∀ z ∈ R, |t| / 2 ≤ |z.im| ∧ |z.im| ≤ 3 * |t| / 2 := by
    intro z hz
    have h2 : z.im ∈ Icc (t - |t| / 2) (t + |t| / 2) := hz.2
    have hd : |z.im - t| ≤ |t| / 2 := abs_sub_le_iff.2 ⟨by linarith [h2.2], by linarith [h2.1]⟩
    have h3 := abs_sub_abs_le_abs_sub t z.im
    have h4 := abs_sub_abs_le_abs_sub z.im t
    rw [abs_sub_comm] at h3
    constructor <;> linarith
  have hre : ∀ z ∈ R, a ≤ z.re := fun z hz => hz.1.1
  have hne1 : (1 : ℂ) ∉ R := by
    intro h
    have := (him 1 h).1
    simp only [Complex.one_im, abs_zero] at this
    linarith
  have hnz : ∀ z ∈ R, riemannZeta z ≠ 0 := fun z hz => hzf z (lt_of_lt_of_le hθa (hre z hz))
  have hF : DifferentiableOn ℂ (fun z => deriv riemannZeta z / riemannZeta z) R :=
    LogDerivZetaHoloOn hne1 hnz
  have hall : ∀ z ∈ R, ‖deriv riemannZeta z / riemannZeta z‖ ≤ A := by
    intro z hz
    obtain ⟨h1, h2⟩ := him z hz
    have hz3 : 3 < |z.im| := by linarith
    have h := hlog z.re z.im hz3 (hre z hz)
    rw [Complex.re_add_im] at h
    refine h.trans (le_trans ?_ (le_max_right _ _))
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) h2) hC₁.le
  have hWlog : Real.log (A / B) ≤ (|t| / 2) ^ 2 := by
    have hApos : 0 < A / B := div_pos (lt_of_lt_of_le hB0 (le_max_left _ _)) hB0
    have h1 : Real.log (A / B) ≤ A / B - 1 := Real.log_le_sub_one_of_pos hApos
    have h2 : A / B ≤ A := div_le_self (by linarith [le_max_left B (C₁ * Real.log (3 * |t| / 2))]) hB
    have hlg : Real.log (3 * |t| / 2) ≤ 3 * |t| / 2 :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have h3 : A ≤ B + C₁ * (3 * |t| / 2) := by
      rw [hAdef]
      apply max_le (by nlinarith)
      nlinarith
    linarith
  exact norm_le_interp ha0 ha32 hW0 hB0 (le_max_left _ _) hF hall
    (fun y _ => hright _ (by simp)) hWlog hu

/-- **A Lindelöf bound in a zero-free half-plane.** If `ζ(s) ≠ 0` on `Re s > θ`, `0 ≤ θ < 1`, then for every
`σ₀ > θ` and `ε > 0` there are `T` and `C` with `|ζ(σ + it)| ≤ C|t|^ε` and `1/|ζ(σ + it)| ≤ C|t|^ε` whenever
`σ ≥ σ₀` and `|t| ≥ T`. -/
theorem zeta_bound_of_zeroFree {θ σ₀ ε : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hθσ₀ : θ < σ₀) (hε : 0 < ε)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    ∃ T C : ℝ, ∀ σ t : ℝ, σ₀ ≤ σ → T ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε ∧ ‖riemannZeta (σ + t * I)‖⁻¹ ≤ C * |t| ^ ε := by
  set σ₁ : ℝ := min σ₀ (5 / 4) with hσ₁
  have hθσ₁ : θ < σ₁ := lt_min hθσ₀ (by linarith)
  have hσ₁σ₀ : σ₁ ≤ σ₀ := min_le_left _ _
  have hσ₁54 : σ₁ ≤ 5 / 4 := min_le_right _ _
  set a : ℝ := (θ + σ₁) / 2 with ha
  have hθa : θ < a := by linarith
  have haσ₁ : a < σ₁ := by linarith
  have ha32 : a < 3 / 2 := by linarith
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨C₁, hC₁, hlog⟩ := HalfPlanePNT.logDeriv_le_of_zeroFree hθ0 hθa ha32 hzf
  obtain ⟨C₂, hC₂⟩ := LogDerivZetaBdd_of_Re_ge_three_halves
  set B : ℝ := max C₂ 1 with hBdef
  have hB : 1 ≤ B := le_max_right _ _
  have hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ B :=
    fun s hs => (hC₂ s hs).trans (le_max_left _ _)
  set κ : ℝ := (3 / 2 - σ₁) / (3 / 2 - a) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) (by linarith)
  have hκ1 : κ < 1 := (div_lt_one (by linarith)).2 (by linarith)
  set K : ℝ := Real.exp ((3 / 2) ^ 2) * B * (3 / 2) with hK
  have hK0 : 0 < K := by positivity
  set δ : ℝ := ε / (K * C₁ + 1) with hδ
  have hKC : 0 < K * C₁ + 1 := by positivity
  have hδ0 : 0 < δ := div_pos hε hKC
  have hKδ : K * δ * C₁ ≤ ε := by
    rw [hδ, show K * (ε / (K * C₁ + 1)) * C₁ = ε * (K * C₁ / (K * C₁ + 1)) by ring]
    have : K * C₁ / (K * C₁ + 1) ≤ 1 := (div_le_one hKC).2 (by linarith)
    exact mul_le_of_le_one_right hε.le this
  obtain ⟨Y, hY0, hY⟩ := rpow_le_mul_self hκ1 hδ0
  set Z : ℝ := ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ with hZ
  set M : ℝ := Real.log Z + K * δ * (B + C₁ * Real.log (3 / 2)) with hM
  set T : ℝ := max (max 7 (4 * B + 6 * C₁ + 1)) (Real.exp (Y / C₁)) with hT
  refine ⟨T, max (Real.exp M) Z, fun σ t hσ ht => ?_⟩
  have ht7 : 7 ≤ |t| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htB : 4 * B + 6 * C₁ + 1 ≤ |t| := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htY : Real.exp (Y / C₁) ≤ |t| := le_trans (le_max_right _ _) ht
  have ht0 : 0 < |t| := by linarith
  have ht1 : 1 ≤ |t| ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hCZ : Z ≤ max (Real.exp M) Z := le_max_right _ _
  have hCM : Real.exp M ≤ max (Real.exp M) Z := le_max_left _ _
  have hC0 : 0 ≤ max (Real.exp M) Z := le_trans (Real.exp_pos M).le hCM
  by_cases h32 : 3 / 2 ≤ σ
  · -- right of `Re s = 3/2`
    have hre : 3 / 2 ≤ ((σ : ℂ) + t * I).re := by simpa using h32
    constructor
    · calc ‖riemannZeta (σ + t * I)‖ ≤ Z := norm_zeta_le_three_halves hre
        _ ≤ max (Real.exp M) Z := hCZ
        _ ≤ max (Real.exp M) Z * |t| ^ ε := le_mul_of_one_le_right hC0 ht1
    · calc ‖riemannZeta (σ + t * I)‖⁻¹ ≤ Z := inv_norm_zeta_le_three_halves hre
        _ ≤ max (Real.exp M) Z := hCZ
        _ ≤ max (Real.exp M) Z * |t| ^ ε := le_mul_of_one_le_right hC0 ht1
  · push Not at h32
    have hσa : a < σ := by linarith
    have hσθ : θ < σ := by linarith
    -- the interpolated bound at every `u ∈ [σ, 3/2]`
    set A : ℝ := max B (C₁ * Real.log (3 * |t| / 2)) with hA
    have hA1 : 1 ≤ A := le_trans hB (le_max_left _ _)
    have htW : B + C₁ * (3 * |t| / 2) ≤ (|t| / 2) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left htB (abs_nonneg t)
      have h2 : B ≤ B * |t| := le_mul_of_one_le_right (by linarith) (by linarith)
      linarith
    have hbound : ∀ u ∈ Icc σ (3 / 2),
        ‖deriv riemannZeta (u + t * I) / riemannZeta (u + t * I)‖ ≤ Real.exp ((3 / 2) ^ 2) * A ^ κ * B := by
      intro u hu
      have hua : u ∈ Icc a (3 / 2) := ⟨by linarith [hu.1], hu.2⟩
      have h := logDeriv_le_interp hθa ha0 ha32 hC₁ hB hzf hlog hright (by linarith) htW hua
      refine h.trans ?_
      have e1 : Real.exp ((3 / 2) ^ 2 - u ^ 2) ≤ Real.exp ((3 / 2) ^ 2) :=
        Real.exp_le_exp.2 (by linarith [sq_nonneg u])
      have e2 : A ^ ((3 / 2 - u) / (3 / 2 - a)) ≤ A ^ κ := by
        apply Real.rpow_le_rpow_of_exponent_le hA1
        rw [hκ]
        exact div_le_div_of_nonneg_right (by linarith [hu.1]) (by linarith)
      have e3 : B ^ ((u - a) / (3 / 2 - a)) ≤ B := by
        calc B ^ ((u - a) / (3 / 2 - a)) ≤ B ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hB ((div_le_one (by linarith)).2 (by linarith [hu.2]))
          _ = B := Real.rpow_one B
      have p1 : 0 ≤ A ^ ((3 / 2 - u) / (3 / 2 - a)) := Real.rpow_nonneg (by linarith) _
      have p2 : 0 ≤ B ^ ((u - a) / (3 / 2 - a)) := Real.rpow_nonneg (by linarith) _
      exact mul_le_mul (mul_le_mul e1 e2 p1 (Real.exp_pos _).le) e3 p2
        (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _))
    -- the mean value inequality for `log|ζ(u + it)|` on `[σ, 3/2]`
    set g : ℝ → ℝ := fun u => Real.log ‖riemannZeta (u + t * I)‖ with hg
    have hderiv : ∀ u ∈ Icc σ (3 / 2), HasDerivWithinAt g
        ((deriv riemannZeta (u + t * I) / riemannZeta (u + t * I)).re) (Icc σ (3 / 2)) u := by
      intro u hu
      have hne : ((u : ℂ) + t * I) ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        rw [this] at ht0
        simp at ht0
      have hz : riemannZeta ((u : ℂ) + t * I) ≠ 0 := hzf _ (by simp; linarith [hu.1])
      have hd : HasDerivAt (fun x : ℂ => riemannZeta (x + t * I)) (deriv riemannZeta (u + t * I)) u :=
        ((differentiableAt_riemannZeta hne).hasDerivAt).comp_add_const _ _
      exact (hasDerivAt_log_norm hd.comp_ofReal hz).hasDerivWithinAt
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
      (fun u hu => (Complex.abs_re_le_norm _).trans (hbound u hu)) (convex_Icc σ (3 / 2))
      (left_mem_Icc.2 h32.le) (right_mem_Icc.2 h32.le)
    -- the endpoint `u = 3/2`
    have hre32 : 3 / 2 ≤ (((3 / 2 : ℝ) : ℂ) + t * I).re := by simp
    have hz32 : 0 < ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I)‖ :=
      norm_pos_iff.2 (riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num))
    have hg32 : |g (3 / 2)| ≤ Real.log Z := by
      have u1 := norm_zeta_le_three_halves hre32
      have u2 := inv_norm_zeta_le_three_halves hre32
      have hZ0 : 0 < Z := lt_of_lt_of_le hz32 u1
      rw [abs_le]
      constructor
      · have := Real.log_le_log (inv_pos.2 hz32) u2
        rw [Real.log_inv] at this
        simp only [hg]
        linarith
      · exact Real.log_le_log hz32 u1
    -- the size of the interpolated bound
    have hlog32 : Real.log (3 * |t| / 2) = Real.log (3 / 2) + Real.log |t| := by
      rw [show 3 * |t| / 2 = (3 / 2) * |t| by ring, Real.log_mul (by norm_num) ht0.ne']
    have hlogt : Y / C₁ ≤ Real.log |t| := by
      rw [← Real.log_exp (Y / C₁)]; exact Real.log_le_log (Real.exp_pos _) htY
    have hlogt0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
    have hlog3 : 0 ≤ Real.log (3 * |t| / 2) := Real.log_nonneg (by linarith)
    have hAy : A ≤ B + C₁ * Real.log (3 * |t| / 2) := by
      rw [hA]
      exact max_le (le_add_of_nonneg_right (mul_nonneg hC₁.le hlog3)) (le_add_of_nonneg_left (by linarith))
    have hYy : Y ≤ B + C₁ * Real.log (3 * |t| / 2) := by
      have h1 := mul_le_mul_of_nonneg_left hlogt hC₁.le
      have h2 : C₁ * (Y / C₁) = Y := by field_simp
      have h3 := mul_le_mul_of_nonneg_left (Real.log_le_log ht0 (by linarith : |t| ≤ 3 * |t| / 2)) hC₁.le
      linarith
    have hAκ : A ^ κ ≤ δ * (B + C₁ * Real.log (3 * |t| / 2)) :=
      (Real.rpow_le_rpow (by linarith) hAy hκ0).trans (hY _ hYy)
    have hAκ0 : 0 ≤ A ^ κ := Real.rpow_nonneg (by linarith) _
    have hL : |g σ| ≤ M + ε * Real.log |t| := by
      have h1 : |g σ| ≤ |g (3 / 2)| + |g (3 / 2) - g σ| := by
        have := abs_sub (g (3 / 2)) (g (3 / 2) - g σ)
        rwa [sub_sub_cancel] at this
      have h2 : |g (3 / 2) - g σ| ≤ K * A ^ κ := by
        have hm := hmvt
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 / 2 - σ)] at hm
        have hE : 0 ≤ Real.exp ((3 / 2) ^ 2) * A ^ κ * B :=
          mul_nonneg (mul_nonneg (Real.exp_pos _).le hAκ0) (by linarith)
        have h4 : Real.exp ((3 / 2) ^ 2) * A ^ κ * B * (3 / 2 - σ) ≤
            Real.exp ((3 / 2) ^ 2) * A ^ κ * B * (3 / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hE
        have h5 : Real.exp ((3 / 2) ^ 2) * A ^ κ * B * (3 / 2) = K * A ^ κ := by rw [hK]; ring
        linarith
      have h3 : K * A ^ κ ≤ K * δ * (B + C₁ * Real.log (3 / 2)) + ε * Real.log |t| := by
        have h4 := mul_le_mul_of_nonneg_left hAκ hK0.le
        rw [hlog32] at h4
        have h5 : K * δ * C₁ * Real.log |t| ≤ ε * Real.log |t| := mul_le_mul_of_nonneg_right hKδ hlogt0
        have h6 : K * (δ * (B + C₁ * (Real.log (3 / 2) + Real.log |t|))) =
            K * δ * (B + C₁ * Real.log (3 / 2)) + K * δ * C₁ * Real.log |t| := by ring
        linarith
      rw [hM]
      linarith
    have hzσ : 0 < ‖riemannZeta (σ + t * I)‖ := norm_pos_iff.2 (hzf _ (by simp; linarith))
    have hpow : |t| ^ ε = Real.exp (ε * Real.log |t|) := by
      rw [Real.rpow_def_of_pos ht0, mul_comm]
    have hgσ : g σ = Real.log ‖riemannZeta (σ + t * I)‖ := rfl
    rw [hgσ] at hL
    constructor
    · calc ‖riemannZeta (σ + t * I)‖ = Real.exp (Real.log ‖riemannZeta (σ + t * I)‖) :=
            (Real.exp_log hzσ).symm
        _ ≤ Real.exp (M + ε * Real.log |t|) := Real.exp_le_exp.2 (le_of_abs_le hL)
        _ = Real.exp M * |t| ^ ε := by rw [Real.exp_add, hpow]
        _ ≤ max (Real.exp M) Z * |t| ^ ε := by gcongr
    · calc ‖riemannZeta (σ + t * I)‖⁻¹ = Real.exp (-Real.log ‖riemannZeta (σ + t * I)‖) := by
            rw [Real.exp_neg, Real.exp_log hzσ]
        _ ≤ Real.exp (M + ε * Real.log |t|) := Real.exp_le_exp.2 (by linarith [neg_abs_le (Real.log ‖riemannZeta (σ + t * I)‖), neg_le_abs (Real.log ‖riemannZeta (σ + t * I)‖)])
        _ = Real.exp M * |t| ^ ε := by rw [Real.exp_add, hpow]
        _ ≤ max (Real.exp M) Z * |t| ^ ε := by gcongr

/-- **The Lindelöf bound on `Re s > 11/12`**, with no hypothesis: round 466's half-plane in
`zeta_bound_of_zeroFree`. -/
theorem zeta_bound_eleven_twelfths {σ₀ ε : ℝ} (hσ₀ : 11 / 12 < σ₀) (hε : 0 < ε) :
    ∃ T C : ℝ, ∀ σ t : ℝ, σ₀ ≤ σ → T ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε ∧ ‖riemannZeta (σ + t * I)‖⁻¹ ≤ C * |t| ^ ε :=
  zeta_bound_of_zeroFree (by norm_num) (by norm_num) hσ₀ hε
    (fun _ hs => (Eis.ne_zero_of_re_gt_eleven_twelfths hs).1)

/-- **The Lindelöf bound on `Re s > Θ`**, with round 469's `Θ`, the supremum of the real parts of the
nontrivial zeros. -/
theorem zeta_bound_Theta {σ₀ ε : ℝ} (hσ₀ : PsiExponent.Theta < σ₀) (hε : 0 < ε) :
    ∃ T C : ℝ, ∀ σ t : ℝ, σ₀ ≤ σ → T ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε ∧ ‖riemannZeta (σ + t * I)‖⁻¹ ≤ C * |t| ^ ε :=
  zeta_bound_of_zeroFree (by linarith [PsiExponent.half_le_Theta])
    (by linarith [PsiExponent.Theta_le]) hσ₀ hε (fun _ hs => PsiExponent.zeta_ne_zero_of_Theta_lt hs)

end HalfPlaneLindelof

#print axioms HalfPlaneLindelof.norm_le_interp
#print axioms HalfPlaneLindelof.hasDerivAt_log_norm
#print axioms HalfPlaneLindelof.logDeriv_le_interp
#print axioms HalfPlaneLindelof.zeta_bound_of_zeroFree
#print axioms HalfPlaneLindelof.zeta_bound_eleven_twelfths
#print axioms HalfPlaneLindelof.zeta_bound_Theta
