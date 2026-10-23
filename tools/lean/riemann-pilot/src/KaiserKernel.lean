import Mathlib

/-! # Kaiser kernels (round 163, part 1)

Two entire functions of `w`:

* `kc w = Σ wⁿ/(2n)!`, so that `kc (s²) = cosh s` for every `s`;
* `ks w = Σ wⁿ/(2n+1)!`, so that `s · ks (s²) = sinh s`.

They give `cos(β√v)`, `cosh(β√(−v))` and `sin(ζ)/ζ` as entire functions of `v` and `ζ²`, with no
branch of the square root. The file proves entireness, the identities, and the bounds the Kaiser
trial needs (round 163, `frontier/kaiser/PROOF.md`, Step 1).
-/

open Complex Filter Topology

noncomputable section

namespace Kaiser

/-- `kc w = Σ wⁿ/(2n)!`. -/
def kc (w : ℂ) : ℂ := ∑' n : ℕ, w ^ n / ((2 * n).factorial : ℂ)

/-- `ks w = Σ wⁿ/(2n+1)!`. -/
def ks (w : ℂ) : ℂ := ∑' n : ℕ, w ^ n / ((2 * n + 1).factorial : ℂ)

theorem factorial_le_two_mul (n j : ℕ) : (n.factorial : ℝ) ≤ (2 * n + j).factorial := by
  exact_mod_cast Nat.factorial_le (by omega)

/-- Majorant: `‖wⁿ/(2n+j)!‖ ≤ Rⁿ/n!` on `‖w‖ ≤ R`. -/
theorem term_le {j n : ℕ} {w : ℂ} {R : ℝ} (hw : ‖w‖ ≤ R) :
    ‖w ^ n / ((2 * n + j).factorial : ℂ)‖ ≤ R ^ n / n.factorial := by
  rw [norm_div, norm_pow, Complex.norm_natCast]
  have h0 : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 : (n.factorial : ℝ) ≤ (2 * n + j).factorial := factorial_le_two_mul n j
  calc ‖w‖ ^ n / ((2 * n + j).factorial : ℝ) ≤ R ^ n / ((2 * n + j).factorial : ℝ) := by
        gcongr
    _ ≤ R ^ n / n.factorial := by
        have : 0 ≤ R ^ n := pow_nonneg ((norm_nonneg w).trans hw) n
        gcongr

theorem differentiable_ser (j : ℕ) :
    Differentiable ℂ (fun w : ℂ => ∑' n : ℕ, w ^ n / ((2 * n + j).factorial : ℂ)) := by
  intro w₀
  have hU : IsOpen (Metric.ball (0 : ℂ) (‖w₀‖ + 1)) := Metric.isOpen_ball
  have hd := differentiableOn_tsum_of_summable_norm (U := Metric.ball (0 : ℂ) (‖w₀‖ + 1))
    (F := fun n (w : ℂ) => w ^ n / ((2 * n + j).factorial : ℂ))
    (u := fun n => (‖w₀‖ + 1) ^ n / n.factorial) (Real.summable_pow_div_factorial _)
    (fun n => (by fun_prop : Differentiable ℂ fun w : ℂ => w ^ n / ((2 * n + j).factorial : ℂ)).differentiableOn)
    hU (fun n w hw => term_le (le_of_lt (by simpa using hw)))
  exact (hd w₀ (by simp)).differentiableAt (hU.mem_nhds (by simp))

theorem differentiable_kc : Differentiable ℂ kc := by
  unfold kc; simpa using differentiable_ser 0

theorem differentiable_ks : Differentiable ℂ ks := differentiable_ser 1

/-- `kc (s²) = cosh s`. -/
theorem kc_sq (s : ℂ) : kc (s ^ 2) = Complex.cosh s := by
  rw [Complex.cosh_eq_tsum, kc]
  congr 1; funext n; rw [← pow_mul]

/-- `s · ks (s²) = sinh s`. -/
theorem ks_sq (s : ℂ) : s * ks (s ^ 2) = Complex.sinh s := by
  rw [Complex.sinh_eq_tsum, ks, ← tsum_mul_left]
  congr 1; funext n; rw [← pow_mul, pow_succ]; ring

theorem kc_zero : kc 0 = 1 := by simpa using kc_sq 0

theorem ks_zero : ks 0 = 1 := by
  rw [ks, tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]; simp

/-- Every complex number has a square root. -/
theorem exists_sq_eq (w : ℂ) : ∃ s : ℂ, s ^ 2 = w :=
  ⟨w ^ (2⁻¹ : ℂ), by simp⟩

/-- `‖cosh s‖ ≤ exp |Re s|`. -/
theorem norm_cosh_le (s : ℂ) : ‖Complex.cosh s‖ ≤ Real.exp |s.re| := by
  rw [Complex.cosh, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, div_le_iff₀ (by norm_num)]
  calc ‖Complex.exp s + Complex.exp (-s)‖ ≤ ‖Complex.exp s‖ + ‖Complex.exp (-s)‖ := norm_add_le _ _
    _ = Real.exp s.re + Real.exp (-s.re) := by rw [Complex.norm_exp, Complex.norm_exp, neg_re]
    _ ≤ Real.exp |s.re| + Real.exp |s.re| := by
        gcongr
        · exact le_abs_self _
        · exact neg_le_abs _
    _ = Real.exp |s.re| * 2 := by ring

/-- `‖kc w‖ ≤ exp |Re s|` whenever `s² = w`. -/
theorem norm_kc_le {w s : ℂ} (hs : s ^ 2 = w) : ‖kc w‖ ≤ Real.exp |s.re| := by
  rw [← hs, kc_sq]; exact norm_cosh_le s

/-- **The square-root lemma.** If `s² = z² − L²` with `L` real, then `(Im s)² ≤ (Im z)² + L²`. -/
theorem im_sq_le {s z : ℂ} {L : ℝ} (hs : s ^ 2 = z ^ 2 - (L : ℂ) ^ 2) :
    s.im ^ 2 ≤ z.im ^ 2 + L ^ 2 := by
  have hre := congrArg Complex.re hs
  have him := congrArg Complex.im hs
  simp only [sq, mul_re, mul_im, sub_re, sub_im, ofReal_re, ofReal_im] at hre him
  by_contra h
  push Not at h
  have hp : z.re ^ 2 < s.re ^ 2 := by nlinarith [sq_nonneg L]
  have hq : z.im ^ 2 ≤ s.im ^ 2 := by nlinarith [sq_nonneg L]
  have : z.re ^ 2 * z.im ^ 2 < s.re ^ 2 * s.im ^ 2 := by
    have hs2 : 0 < s.im ^ 2 := by nlinarith [sq_nonneg z.im, sq_nonneg L]
    calc z.re ^ 2 * z.im ^ 2 ≤ z.re ^ 2 * s.im ^ 2 := by gcongr
      _ < s.re ^ 2 * s.im ^ 2 := by gcongr
  have hpq : s.re * s.im = z.re * z.im := by linarith
  have h2 : (s.re * s.im) ^ 2 = (z.re * z.im) ^ 2 := by rw [hpq]
  nlinarith [h2]

/-! ## The Kaiser factor `K(z) = cos(β√(z² − L²))` -/

/-- `kK β L z = kc(−β²(z² − L²)) = cos(β√(z² − L²))`. -/
def kK (β L : ℝ) (z : ℂ) : ℂ := kc (-(β : ℂ) ^ 2 * (z ^ 2 - (L : ℂ) ^ 2))

theorem differentiable_kK (β L : ℝ) : Differentiable ℂ (kK β L) := by
  unfold kK; exact differentiable_kc.comp (by fun_prop)

/-- **Exponential type.** `‖K(z)‖ ≤ exp(β(|Im z| + L))` for `β, L ≥ 0`. -/
theorem norm_kK_le {β L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L) (z : ℂ) :
    ‖kK β L z‖ ≤ Real.exp (β * (|z.im| + L)) := by
  obtain ⟨s, hs⟩ := exists_sq_eq (z ^ 2 - (L : ℂ) ^ 2)
  have hw : (I * β * s) ^ 2 = -(β : ℂ) ^ 2 * (z ^ 2 - (L : ℂ) ^ 2) := by
    rw [← hs]; ring_nf; rw [I_sq]; ring
  refine (norm_kc_le hw).trans (Real.exp_le_exp.2 ?_)
  have hre : (I * β * s).re = -(β * s.im) := by simp [mul_re, mul_im]
  rw [hre, abs_neg, abs_mul, abs_of_nonneg hβ]
  gcongr
  have h1 := im_sq_le hs
  have h2 : s.im ^ 2 ≤ (|z.im| + L) ^ 2 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
  exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2 |> fun h => by
    rcases abs_cases s.im with ⟨h', _⟩ | ⟨h', _⟩ <;>
      [linarith [(abs_le_of_sq_le_sq' h2 (by positivity)).2];
       linarith [(abs_le_of_sq_le_sq' h2 (by positivity)).1]]

/-- On the real line beyond `L`, `K(x) = cos(β√(x² − L²))`, so `‖K(x)‖ ≤ 1`. -/
theorem kK_real_ge {β L x : ℝ} (hx : L ^ 2 ≤ x ^ 2) :
    kK β L x = (Real.cos (β * Real.sqrt (x ^ 2 - L ^ 2)) : ℂ) := by
  set r := Real.sqrt (x ^ 2 - L ^ 2)
  have hr : r ^ 2 = x ^ 2 - L ^ 2 := Real.sq_sqrt (by linarith)
  have hw : (I * (β * r : ℝ)) ^ 2 = -(β : ℂ) ^ 2 * ((x : ℂ) ^ 2 - (L : ℂ) ^ 2) := by
    have : ((r : ℂ)) ^ 2 = (x : ℂ) ^ 2 - (L : ℂ) ^ 2 := by exact_mod_cast hr
    push_cast; ring_nf; rw [I_sq, this]; ring
  rw [kK, ← hw, kc_sq, mul_comm I, Complex.cosh_mul_I, ← Complex.ofReal_cos]

theorem norm_kK_real_ge {β L x : ℝ} (hx : L ^ 2 ≤ x ^ 2) : ‖kK β L x‖ ≤ 1 := by
  rw [kK_real_ge hx, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _

/-- Inside `(−L, L)`, `K(x) = cosh(β√(L² − x²))`. -/
theorem kK_real_le {β L x : ℝ} (hx : x ^ 2 ≤ L ^ 2) :
    kK β L x = (Real.cosh (β * Real.sqrt (L ^ 2 - x ^ 2)) : ℂ) := by
  set r := Real.sqrt (L ^ 2 - x ^ 2)
  have hr : r ^ 2 = L ^ 2 - x ^ 2 := Real.sq_sqrt (by linarith)
  have hw : ((β * r : ℝ) : ℂ) ^ 2 = -(β : ℂ) ^ 2 * ((x : ℂ) ^ 2 - (L : ℂ) ^ 2) := by
    have : ((r : ℂ)) ^ 2 = (L : ℂ) ^ 2 - (x : ℂ) ^ 2 := by exact_mod_cast hr
    push_cast; rw [mul_pow, this]; ring
  rw [kK, ← hw, kc_sq, ← Complex.ofReal_cosh]

/-! ## The sinc factor `sinc ζ = sin ζ / ζ` as an entire function -/

/-- `sincE ζ = ks(−ζ²) = sin ζ / ζ`. -/
def sincE (ζ : ℂ) : ℂ := ks (-ζ ^ 2)

theorem differentiable_sincE : Differentiable ℂ sincE := by
  unfold sincE; exact differentiable_ks.comp (by fun_prop)

theorem mul_sincE (ζ : ℂ) : ζ * sincE ζ = Complex.sin ζ := by
  have h := ks_sq (ζ * I)
  have e : (ζ * I) ^ 2 = -ζ ^ 2 := by ring_nf; rw [I_sq]; ring
  rw [e, Complex.sinh_mul_I] at h
  have hI : I ≠ 0 := I_ne_zero
  apply mul_left_cancel₀ hI
  rw [sincE]; linear_combination h

theorem sincE_real (x : ℝ) (hx : x ≠ 0) : sincE x = ((Real.sin x / x : ℝ) : ℂ) := by
  have h := mul_sincE (x : ℂ)
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  push_cast
  rw [eq_div_iff hx', mul_comm, h]

theorem sincE_zero : sincE 0 = 1 := by simp [sincE, ks_zero]

/-- `‖sincE ζ‖ ≤ 6 exp |Im ζ| / (1 + ‖ζ‖)`. -/
theorem norm_sincE_le (ζ : ℂ) : ‖sincE ζ‖ ≤ 6 * Real.exp |ζ.im| / (1 + ‖ζ‖) := by
  have he : 1 ≤ Real.exp |ζ.im| := Real.one_le_exp (abs_nonneg _)
  rcases le_or_gt ‖ζ‖ 1 with h1 | h1
  · -- series bound: ‖ks(−ζ²)‖ ≤ Σ 1/(2n+1)! ≤ Σ 1/n! = e < 3/2 · 2
    have hb : ‖sincE ζ‖ ≤ Real.exp 1 := by
      unfold sincE ks
      have hs : Summable (fun n : ℕ => (1 : ℝ) ^ n / n.factorial) := Real.summable_pow_div_factorial 1
      have hle : ∀ n : ℕ, ‖(-ζ ^ 2) ^ n / ((2 * n + 1).factorial : ℂ)‖ ≤ (1 : ℝ) ^ n / n.factorial :=
        fun n => term_le (by rw [norm_neg, norm_pow]; nlinarith [norm_nonneg ζ])
      calc ‖∑' n : ℕ, (-ζ ^ 2) ^ n / ((2 * n + 1).factorial : ℂ)‖
          ≤ ∑' n : ℕ, (1 : ℝ) ^ n / n.factorial := tsum_of_norm_bounded hs.hasSum hle
        _ = Real.exp 1 := by
          rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have e3 : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    calc ‖sincE ζ‖ ≤ 3 := hb.trans e3
      _ ≤ 6 * Real.exp |ζ.im| / (1 + ‖ζ‖) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith [norm_nonneg ζ]
  · have hz : ζ ≠ 0 := by intro h; rw [h, norm_zero] at h1; linarith
    have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hz
    have hsin : ‖Complex.sin ζ‖ ≤ Real.exp |ζ.im| := by
      rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2, div_le_iff₀ (by norm_num)]
      calc ‖Complex.exp (-ζ * I) - Complex.exp (ζ * I)‖
          ≤ ‖Complex.exp (-ζ * I)‖ + ‖Complex.exp (ζ * I)‖ := norm_sub_le _ _
        _ = Real.exp ζ.im + Real.exp (-ζ.im) := by
          rw [Complex.norm_exp, Complex.norm_exp]; simp [mul_re]
        _ ≤ Real.exp |ζ.im| + Real.exp |ζ.im| := by
          gcongr
          · exact le_abs_self _
          · exact neg_le_abs _
        _ = Real.exp |ζ.im| * 2 := by ring
    have : ‖sincE ζ‖ = ‖Complex.sin ζ‖ / ‖ζ‖ := by
      rw [← mul_sincE ζ, norm_mul, mul_div_cancel_left₀ _ hn.ne']
    rw [this, div_le_div_iff₀ hn (by positivity)]
    nlinarith [norm_nonneg ζ]

/-- On the real line `‖sincE x‖ ≤ 1`. -/
theorem norm_sincE_real_le_one (x : ℝ) : ‖sincE x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [sincE_zero]
  rw [sincE_real x hx, Complex.norm_real, Real.norm_eq_abs, abs_div]
  rw [div_le_one (abs_pos.2 hx)]; exact Real.abs_sin_le_abs

/-- On the real line `‖sincE x‖ ≤ 1/|x|`. -/
theorem norm_sincE_real_le_inv {x : ℝ} (hx : x ≠ 0) : ‖sincE x‖ ≤ 1 / |x| := by
  rw [sincE_real x hx, Complex.norm_real, Real.norm_eq_abs, abs_div]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one x) (abs_nonneg x)

end Kaiser

#print axioms Kaiser.differentiable_kc
#print axioms Kaiser.kc_sq
#print axioms Kaiser.ks_sq
#print axioms Kaiser.im_sq_le
#print axioms Kaiser.norm_kK_le
#print axioms Kaiser.kK_real_ge
#print axioms Kaiser.kK_real_le
#print axioms Kaiser.mul_sincE
#print axioms Kaiser.norm_sincE_le
