import EisensteinQuadSieveLemma14
import MellinSeparation

/-! # The quadratic large sieve, part 4b: sums over arguments prime to a set of primes (round 348)

S5e of round 312's plan, the second piece of round 343's S5e-4 as revised in round 348: the sum
`Σ_{e : π_Q ∤ e ∀Q∈S} P(β·N(e))` of a Schwartz profile `P` over the arguments prime to a finite set
`S` of primes, with its main term and a Mellin form of its error. Goldmakher and Louvel's single
explicit formula for their `Σ_4(𝔪, ≤K; h, X, χ)` serves both of Heath-Brown's sums; this is its
inner sum, over the square part.

* **Schwartz constructions** (`onReal`, `radS`): a Schwartz function on `ℂ` restricted to `ℝ`, and
  `z ↦ P(|z|²)` on `ℂ` for `P` Schwartz on `ℝ`.
* **Mellin inversion for a Schwartz profile** (`schwartz_exp_comp_S`, `mellin_of_schwartz`):
  round 302's `schwartz_exp_comp` and `mellin_of_dual` with rapid decay in place of vanishing on
  `[R, ∞)`: `G(√y) = ∫ c(t)·y^{−σ+2πit} dt` for `y > 0`, `σ > 0`, `c` Schwartz.
* **The lattice sum** `L_P(x) = Σ_e P(x·N(e))` (`latS`) by Poisson summation
  (`latS_poisson`): `L_P(x) = (2/(√3x))·Σ_μ Ĝ(√(4N(μ)/(3x)))`, where `Ĝ(ρ) = 𝓕(P(|·|²))(ρ)` is
  radial (`fourier_radS_eq`, `dualP`) and `Ĝ(0) = π∫_0^∞P` (`dualP_zero`).
* **The error** `r_P(x) = L_P(x) − (2π/(√3x))∫_0^∞P` (`latErr`) is the nonzero frequencies
  (`latErr_eq`), and **a Mellin integral on `Re s = ε`** (`latErr_mellin`):
  `r_P(x) = ∫ C(t)·x^{ε−2πit} dt` with `C` integrable, for every `ε > 0`. The coefficient is the
  Mellin coefficient of `Ĝ(√y)` on `Re = −(1+ε)` times the lattice's Dirichlet series at
  `1 + ε − 2πit`, which converges (`summable_absNorm_elt_rpow`).
* **The Möbius sums are Euler products** (`latErr_moebius`):
  `Σ_{T⊆S}(−1)^{|T|}·r_P(β·N(T)) = ∫ C(t)·β^{s}·∏_{P∈S}(1 − N(P)^{s}) dt`, `s = ε − 2πit`, with
  `|∏(1 − N(P)^s)| ≤ ∏(1 + N(P)^ε)` (`norm_prod_one_sub_le`).
* **The explicit formula** (`excl_eq_latS`, `excl_eq_main_add`):
  `Σ_{e : π_Q ∤ e ∀Q∈S} P(β·N(e)) = (2π/(√3β))·(∫_0^∞P)·∏_{Q∈S}(1 − N(Q)⁻¹)
    + Σ_{T⊆S}(−1)^{|T|}·r_P(β·N(T))`.
-/

open Complex MeasureTheory Set NumberField Ideal
open scoped FourierTransform SchwartzMap Nat ContDiff ComplexConjugate RealInnerProductSpace Classical
open MellinSep

noncomputable section

namespace Eis

/-- A Schwartz function on `ℂ` restricted to the real line. -/
def onReal (F : 𝓢(ℂ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℝ (Complex.ofRealCLM.hasTemperateGrowth)
    Complex.isometry_ofReal.antilipschitzWith F

theorem onReal_apply (F : 𝓢(ℂ, ℂ)) (x : ℝ) : onReal F x = F (x : ℂ) := rfl

/-- `z ↦ P(|z|²)` as a Schwartz function on `ℂ`. -/
def radS (P : 𝓢(ℝ, ℂ)) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLM ℝ (Function.hasTemperateGrowth_norm_sq ℂ) ⟨1, 1, fun z => by
    rw [one_mul, pow_one, Real.norm_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (‖z‖ - 1), norm_nonneg z]⟩ P

theorem radS_apply (P : 𝓢(ℝ, ℂ)) (z : ℂ) : radS P z = P (‖z‖ ^ 2) := rfl

/-- **Schwartz in logarithmic coordinates, for a Schwartz `G`**: `v ↦ e^{σv}·G(e^{av})` is a
Schwartz function for `σ, a > 0`. -/
theorem schwartz_exp_comp_S (G : 𝓢(ℝ, ℂ)) {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    ∃ h : 𝓢(ℝ, ℂ), ∀ v, h v = Real.exp (σ * v) • G (Real.exp (a * v)) := by
  set f : ℝ → ℂ := fun v => Real.exp (σ * v) • G (Real.exp (a * v)) with hf
  have he1 : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (σ * v)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have he2 : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (a * v)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hG : ContDiff ℝ ∞ (G : ℝ → ℂ) := G.smooth ⊤
  have hGe : ContDiff ℝ ∞ (fun v : ℝ => G (Real.exp (a * v))) := hG.comp he2
  have hfs : ContDiff ℝ ∞ f := he1.smul hGe
  -- the decay of `G` and its derivatives, at every order
  choose C _ hC using fun (p : ℕ × ℕ) => G.decay p.1 p.2
  set KA : ℕ → ℕ → ℝ := fun A m => ∑ i ∈ Finset.range (m + 1), |C (A, i)| with hKA
  have hKA : ∀ A m i, i ≤ m → |C (A, i)| ≤ KA A m := fun A m i hi =>
    Finset.single_le_sum (f := fun i => |C (A, i)|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hKA0 : ∀ A m, 0 ≤ KA A m := fun A m => Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- `‖D^i G(x)‖ ≤ KA A m · x^{-A}` for `x ≥ 1`, `i ≤ m`
  have hGx : ∀ A m i, i ≤ m → ∀ x : ℝ, 0 < x →
      ‖iteratedFDeriv ℝ i G x‖ ≤ KA A m / x ^ A := by
    intro A m i hi x hx
    have h := hC (A, i) x
    rw [Real.norm_of_nonneg hx.le] at h
    rw [le_div_iff₀ (pow_pos hx A), mul_comm]
    exact h.trans ((le_abs_self _).trans (hKA A m i hi))
  -- Leibniz: the `n`-th derivative of `f` at `v`
  have hLeib : ∀ n v, ‖iteratedFDeriv ℝ n f v‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (σ ^ i * Real.exp (σ * v)) *
        ‖iteratedFDeriv ℝ (n - i) (fun v : ℝ => G (Real.exp (a * v))) v‖ := by
    intro n v
    refine (norm_iteratedFDeriv_smul_le he1 hGe v (nat_le_infty n)).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv (f := fun v : ℝ => Real.exp (σ * v)),
      iteratedDeriv_exp_const_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hexpder : ∀ j v, ‖iteratedFDeriv ℝ j (fun v : ℝ => Real.exp (a * v)) v‖ =
      a ^ j * Real.exp (a * v) := by
    intro j v
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  -- the regime `v ≤ 0`
  have hneg : ∀ n, ∃ M, ∀ v, v ≤ 0 → ‖iteratedFDeriv ℝ n f v‖ ≤ M * Real.exp (σ * v) := by
    intro n
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * σ ^ i *
      ((n - i) ! * KA 0 (n - i) * a ^ (n - i)), fun v hv => ?_⟩
    have hx1 : Real.exp (a * v) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    refine (hLeib n v).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h2 : ‖iteratedFDeriv ℝ (n - i) (fun v : ℝ => G (Real.exp (a * v))) v‖ ≤
        (n - i) ! * KA 0 (n - i) * a ^ (n - i) := by
      refine norm_iteratedFDeriv_comp_le (g := G) (f := fun v : ℝ => Real.exp (a * v)) hG he2
        (nat_le_infty (n - i)) v (fun j hj => ?_) (fun j _ _ => ?_)
      · have := hGx 0 (n - i) j hj _ (Real.exp_pos (a * v))
        simpa using this
      · rw [hexpder]
        exact mul_le_of_le_one_right (by positivity) hx1
    calc (n.choose i : ℝ) * (σ ^ i * Real.exp (σ * v)) *
          ‖iteratedFDeriv ℝ (n - i) (fun v : ℝ => G (Real.exp (a * v))) v‖
        ≤ (n.choose i : ℝ) * (σ ^ i * Real.exp (σ * v)) *
          ((n - i) ! * KA 0 (n - i) * a ^ (n - i)) := by gcongr
      _ = _ := by ring
  -- the regime `v ≥ 0`, with the decay order `A`
  have hpos : ∀ n, ∃ M, ∀ v, 0 ≤ v → ‖iteratedFDeriv ℝ n f v‖ ≤ M * Real.exp (-v) := by
    intro n
    set A : ℕ := ⌈(σ + a * n + 1) / a⌉₊ with hA
    have hAa : σ + a * n + 1 ≤ a * A := by
      have := Nat.le_ceil ((σ + a * n + 1) / a)
      rw [div_le_iff₀ ha] at this; linarith
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * σ ^ i *
      ((n - i) ! * KA A n * a ^ (n - i)), fun v hv => ?_⟩
    set x := Real.exp (a * v) with hx
    have hx1 : 1 ≤ x := Real.one_le_exp (by positivity)
    have hx0 : 0 < x := Real.exp_pos _
    refine (hLeib n v).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h2 : ‖iteratedFDeriv ℝ (n - i) (fun v : ℝ => G (Real.exp (a * v))) v‖ ≤
        (n - i) ! * (KA A n / x ^ A) * (a * x) ^ (n - i) := by
      refine norm_iteratedFDeriv_comp_le (g := G) (f := fun v : ℝ => Real.exp (a * v)) hG he2
        (nat_le_infty (n - i)) v (fun j hj => ?_) (fun j hj1 _ => ?_)
      · exact hGx A n j (hj.trans (Nat.sub_le n i)) x hx0
      · rw [hexpder, mul_pow]
        gcongr
        calc x = x ^ 1 := (pow_one x).symm
          _ ≤ x ^ j := pow_le_pow_right₀ hx1 hj1
    -- `e^{σv}·x^{n-i}/x^A ≤ e^{-v}`
    have hkey : Real.exp (σ * v) * (x ^ (n - i) / x ^ A) ≤ Real.exp (-v) := by
      have h1 : x ^ (n - i) ≤ x ^ n := pow_le_pow_right₀ hx1 (Nat.sub_le n i)
      have h3 : Real.exp (σ * v) * (x ^ n / x ^ A) = Real.exp ((σ + a * n - a * A) * v) := by
        rw [hx, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add]
        congr 1; ring
      calc Real.exp (σ * v) * (x ^ (n - i) / x ^ A)
          ≤ Real.exp (σ * v) * (x ^ n / x ^ A) := by gcongr
        _ = Real.exp ((σ + a * n - a * A) * v) := h3
        _ ≤ Real.exp (-v) := Real.exp_le_exp.2 (by nlinarith)
    calc (n.choose i : ℝ) * (σ ^ i * Real.exp (σ * v)) *
          ‖iteratedFDeriv ℝ (n - i) (fun v : ℝ => G (Real.exp (a * v))) v‖
        ≤ (n.choose i : ℝ) * (σ ^ i * Real.exp (σ * v)) *
          ((n - i) ! * (KA A n / x ^ A) * (a * x) ^ (n - i)) := by gcongr
      _ = (n.choose i : ℝ) * σ ^ i * ((n - i) ! * KA A n * a ^ (n - i)) *
          (Real.exp (σ * v) * (x ^ (n - i) / x ^ A)) := by rw [mul_pow]; ring
      _ ≤ (n.choose i : ℝ) * σ ^ i * ((n - i) ! * KA A n * a ^ (n - i)) * Real.exp (-v) := by
          gcongr
  refine ⟨⟨f, hfs, fun k n => ?_⟩, fun v => rfl⟩
  obtain ⟨M1, hM1⟩ := hneg n
  obtain ⟨M2, hM2⟩ := hpos n
  obtain ⟨B, hB⟩ := abs_pow_mul_exp_le hσ 0 k
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB 0 le_rfl)
  refine ⟨|M1| * B + |M2| * k !, fun v => ?_⟩
  rw [Real.norm_eq_abs]
  rcases le_or_gt v 0 with hv | hv
  · have h1 := hM1 v hv
    have h2 := hB v hv
    have : |v| ^ k * ‖iteratedFDeriv ℝ n f v‖ ≤ |M1| * B :=
      calc |v| ^ k * ‖iteratedFDeriv ℝ n f v‖ ≤ |v| ^ k * (|M1| * Real.exp (σ * v)) := by
            gcongr; exact h1.trans (by gcongr; exact le_abs_self M1)
        _ = |M1| * (|v| ^ k * Real.exp (σ * v)) := by ring
        _ ≤ |M1| * B := by gcongr
    have : 0 ≤ |M2| * (k ! : ℝ) := by positivity
    linarith
  · have h1 := hM2 v hv.le
    have hvk : |v| ^ k * Real.exp (-v) ≤ k ! := by
      rw [abs_of_pos hv]
      have := Real.pow_div_factorial_le_exp v hv.le k
      have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
      rw [div_le_iff₀ hk] at this
      calc v ^ k * Real.exp (-v) ≤ (Real.exp v * k !) * Real.exp (-v) := by gcongr
        _ = k ! := by rw [mul_comm (Real.exp v), mul_assoc, ← Real.exp_add, add_neg_cancel,
            Real.exp_zero, mul_one]
    have : |v| ^ k * ‖iteratedFDeriv ℝ n f v‖ ≤ |M2| * k ! :=
      calc |v| ^ k * ‖iteratedFDeriv ℝ n f v‖ ≤ |v| ^ k * (|M2| * Real.exp (-v)) := by
            gcongr; exact h1.trans (by gcongr; exact le_abs_self M2)
        _ = |M2| * (|v| ^ k * Real.exp (-v)) := by ring
        _ ≤ |M2| * k ! := by gcongr
    have : 0 ≤ |M1| * B := by positivity
    linarith

/-- **Mellin separation of a Schwartz profile.** For `G` Schwartz on `ℝ` and `σ > 0` there is a
Schwartz `c` with `G(√y) = ∫ c(t)·y^{−σ+2πit} dt` for `y > 0`. -/
theorem mellin_of_schwartz (G : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ) :
    ∃ c : 𝓢(ℝ, ℂ), ∀ y : ℝ, 0 < y →
      G (Real.sqrt y) =
        ∫ t : ℝ, c t * ((y : ℂ) ^ ((-σ : ℂ) + ((2 * Real.pi * t : ℝ) : ℂ) * I)) := by
  obtain ⟨h, hh⟩ := schwartz_exp_comp_S G hσ (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨𝓕 h, fun y hy => ?_⟩
  have e := log_fourier_inversion h y hy
  rw [hh] at e
  have hsq : Real.exp (1 / 2 * Real.log y) = Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]; congr 1; ring
  have hpow : Real.exp (σ * Real.log y) = y ^ σ := by
    rw [Real.rpow_def_of_pos hy]; congr 1; ring
  rw [hsq, hpow] at e
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hone : (y : ℂ) ^ (-σ : ℂ) * ((y ^ σ : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_cpow hy.le, ← Complex.cpow_add _ _ hy']; simp
  calc G (Real.sqrt y) = (y : ℂ) ^ (-σ : ℂ) * ((y ^ σ : ℝ) • G (Real.sqrt y)) := by
        rw [Complex.real_smul, ← mul_assoc, hone, one_mul]
    _ = ∫ t : ℝ, (y : ℂ) ^ (-σ : ℂ) *
          (𝓕 (h : ℝ → ℂ) t * (y : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * I)) := by
        rw [e, integral_const_mul]
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [SchwartzMap.fourier_coe]
        rw [Complex.cpow_add _ _ hy']; ring

/-- **`N(μ)^{−s}` is summable over `ℤ[ω]`** for `s > 1` (the term `μ = 0` is `0`). -/
theorem summable_absNorm_elt_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun μ : 𝓞 K => (absNorm (span {μ}) : ℝ) ^ (-s) := by
  rw [← crdEquiv.summable_iff]
  have h := EisensteinSeries.summable_one_div_norm_rpow (k := 2 * s) (by linarith)
  refine (h.mul_left (2 ^ s)).of_nonneg_of_le
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) fun n => ?_
  simp only [Function.comp_apply]
  set N : ℝ := (absNorm (span {crdEquiv n}) : ℝ) with hN
  have hNe : N = ((n 0 : ℝ) - (n 1 : ℝ) / 2) ^ 2 + 3 / 4 * (n 1 : ℝ) ^ 2 := by
    rw [hN, ← normSq_σO]
    show Complex.normSq (σO (crd n)) = _
    have hv := varpi_re_im
    simp only [crd, map_add, map_mul, map_intCast, σO_ω, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      hv.1]
    nlinarith [hv.2]
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ N by positivity) with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith)]; positivity
  · -- `‖n‖² ≤ 2N`
    have hn : ‖n‖ ^ 2 ≤ 2 * N := by
      have hb : ‖n‖ ≤ Real.sqrt (2 * N) := by
        refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
        rw [Int.norm_eq_abs, Real.le_sqrt (abs_nonneg _) (by positivity), sq_abs]
        fin_cases i
        · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ((n 0 : ℝ) - (n 1 : ℝ))]
        · simp only [Fin.mk_one]; nlinarith [sq_nonneg ((n 0 : ℝ) - (n 1 : ℝ))]
      calc ‖n‖ ^ 2 ≤ Real.sqrt (2 * N) ^ 2 := by gcongr
        _ = 2 * N := Real.sq_sqrt (by positivity)
    have hn0 : 0 < ‖n‖ := by
      rcases eq_or_lt_of_le (norm_nonneg n) with h | h
      · exfalso
        have : n = 0 := norm_eq_zero.1 h.symm
        have : N = 0 := by rw [hNe, this]; simp
        linarith
      · exact h
    have e1 : ‖n‖ ^ (-(2 * s)) = (‖n‖ ^ 2) ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; congr 1; push_cast; ring
    rw [e1]
    calc N ^ (-s) ≤ (‖n‖ ^ 2 / 2) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      _ = 2 ^ s * (‖n‖ ^ 2) ^ (-s) := by
          rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
            div_eq_mul_inv, inv_inv, mul_comm]

/-- `𝓕` of a radial Schwartz function is radial. -/
theorem fourier_radS_rot (P : 𝓢(ℝ, ℂ)) (u : Circle) (ξ : ℂ) :
    𝓕 (radS P : ℂ → ℂ) ((u : ℂ) * ξ) = 𝓕 (radS P : ℂ → ℂ) ξ := by
  have hc : (radS P : ℂ → ℂ) ∘ rotation u = radS P := by
    funext z
    simp only [Function.comp_apply, rotation_apply, radS_apply, norm_mul, Circle.norm_coe, one_mul]
  have h := Real.fourier_comp_linearIsometry (rotation u) (radS P : ℂ → ℂ) ξ
  rw [hc, rotation_apply] at h
  exact h.symm

theorem fourier_radS_eq (P : 𝓢(ℝ, ℂ)) (ξ : ℂ) :
    𝓕 (radS P : ℂ → ℂ) ξ = 𝓕 (radS P : ℂ → ℂ) ((‖ξ‖ : ℝ) : ℂ) := by
  have hw : ξ = ((Circle.exp (Complex.arg ξ) : Circle) : ℂ) * ((‖ξ‖ : ℝ) : ℂ) := by
    rw [Circle.coe_exp, mul_comm]; exact (norm_mul_exp_arg_mul_I ξ).symm
  conv_lhs => rw [hw]
  exact fourier_radS_rot P _ _

/-- `𝓕F(0) = ∫F`. -/
theorem fourier_zero_eq (F : ℂ → ℂ) : 𝓕 F 0 = ∫ z : ℂ, F z := by
  show VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℂ) F 0 = _
  simp [VectorFourier.fourierIntegral]

/-- The lattice sum of a profile: `L_P(x) = Σ_e P(x·N(e))`. -/
def latS (P : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ := ∑' e : 𝓞 K, P (x * (absNorm (span {e}) : ℝ))

/-- The dual profile `ρ ↦ 𝓕(P(|·|²))(ρ)`. -/
def dualP (P : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) := onReal (𝓕 (radS P))

theorem dualP_apply (P : 𝓢(ℝ, ℂ)) (ρ : ℝ) : dualP P ρ = 𝓕 (radS P : ℂ → ℂ) (ρ : ℂ) := by
  rw [dualP, onReal_apply, SchwartzMap.fourier_coe]

theorem dualP_zero (P : 𝓢(ℝ, ℂ)) :
    dualP P 0 = ((Real.pi : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), P y := by
  rw [dualP_apply, Complex.ofReal_zero, fourier_zero_eq]
  have h := integral_radial_sq one_pos (P : ℝ → ℂ)
  simp only [one_mul, div_one] at h
  rw [← h]
  rfl

/-- **Poisson summation for the lattice sum**: `L_P(x) = (2/(√3x))·Σ_μ Ĝ(√(4N(μ)/(3x)))`. -/
theorem latS_poisson (P : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : 0 < x) :
    latS P x = ((2 / (Real.sqrt 3 * x) : ℝ) : ℂ) *
      ∑' μ : 𝓞 K, dualP P (Real.sqrt (4 * (absNorm (span {μ}) : ℝ) / (3 * x))) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hb : ((Real.sqrt x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsx.ne'
  set F := affS (radS P) 0 ((Real.sqrt x : ℝ) : ℂ) hb with hFdef
  have hF : ∀ e : 𝓞 K, F (σO e) = P (x * (absNorm (span {e}) : ℝ)) := by
    intro e
    rw [hFdef, affS_apply, zero_add, radS_apply, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg hsx.le, Real.sq_sqrt hx.le, sq_norm_σO]
  have hp := poisson_excl F 1 one_ne_zero (fun _ => (1 : ℂ)) (fun _ _ => rfl) (∅ : Finset Pr) πP
    (by simp) (by simp)
  simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, pow_zero, one_mul,
    Finset.prod_empty, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, ite_true,
    gaussTr_one_const, mul_one, map_one, absNorm_one_span, div_one] at hp
  rw [latS, show (fun e : 𝓞 K => P (x * (absNorm (span {e}) : ℝ))) = fun e => F (σO e) from
    funext fun e => (hF e).symm, hp]
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun μ => ?_
  rw [hFdef, fourier_affS, inner_zero_left, AddChar.map_zero_eq_one, Circle.coe_one, one_mul,
    fourier_radS_eq, dualP_apply]
  have hn : ‖conj (2 * σO μ / σO δ3) / conj ((Real.sqrt x : ℝ) : ℂ)‖ =
      Real.sqrt (4 * (absNorm (span {μ}) : ℝ) / (3 * x)) := by
    rw [norm_div, Complex.norm_conj, Complex.norm_conj, norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hsx.le, Complex.norm_two]
    have h3 : ‖σO δ3‖ = Real.sqrt 3 := by
      rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, normSq_σO_δ3]
    have hμ : ‖σO μ‖ = Real.sqrt (absNorm (span {μ}) : ℝ) := by
      rw [← Real.sqrt_sq (norm_nonneg _), sq_norm_σO]
    rw [h3, hμ]
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), h4, div_div]
  rw [hn, Complex.normSq_ofReal, Real.mul_self_sqrt hx.le]
  push_cast
  field_simp

/-- `ℤ[ω]` is countable, through its coordinates. -/
instance countable_O : Countable (𝓞 K) := crdEquiv.symm.injective.countable

/-- **The error of the lattice sum**: `r_P(x) = L_P(x) − (2π/(√3·x))·∫_0^∞ P`. -/
def latErr (P : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  latS P x - ((2 * Real.pi / (Real.sqrt 3 * x) : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), P y

/-- `|Ĝ(√(4N/(3x)))| ≤ C·N^{−2}` for `μ ≠ 0`, from the decay of `Ĝ`. -/
theorem exists_dualP_bound (P : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : 0 < x) :
    ∃ B, ∀ μ : 𝓞 K, μ ≠ 0 →
      ‖dualP P (Real.sqrt (4 * (absNorm (span {μ}) : ℝ) / (3 * x)))‖ ≤
        B * (absNorm (span {μ}) : ℝ) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := (dualP P).decay 4 0
  refine ⟨C * (3 * x / 4) ^ 2, fun μ hμ => ?_⟩
  set N : ℝ := (absNorm (span {μ}) : ℝ) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hμ)
  have h := hC (Real.sqrt (4 * N / (3 * x)))
  rw [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at h
  have h4 : Real.sqrt (4 * N / (3 * x)) ^ 4 = (4 * N / (3 * x)) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
  rw [h4] at h
  have hpos : 0 < (4 * N / (3 * x)) ^ 2 := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [← le_div_iff₀' hpos] at h
  refine h.trans (le_of_eq ?_)
  field_simp

theorem summable_dualP (P : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : 0 < x) :
    Summable fun μ : 𝓞 K => dualP P (Real.sqrt (4 * (absNorm (span {μ}) : ℝ) / (3 * x))) := by
  obtain ⟨B, hB⟩ := exists_dualP_bound P hx
  have hs := (summable_absNorm_elt_rpow (s := 2) (by norm_num)).mul_left B
  refine Summable.of_norm_bounded_eventually (g := fun μ => B * (absNorm (span {μ}) : ℝ) ^ (-(2:ℝ)))
    hs ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : 𝓞 K)).subset fun μ hμ => ?_
  by_contra h0
  exact hμ (hB μ h0)

/-- **The error as the nonzero frequencies**: `r_P(x) = (2/(√3x))·Σ_{μ≠0} Ĝ(√(4N(μ)/(3x)))`. -/
theorem latErr_eq (P : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : 0 < x) :
    latErr P x = ((2 / (Real.sqrt 3 * x) : ℝ) : ℂ) *
      ∑' μ : 𝓞 K, (if μ = 0 then 0 else
        dualP P (Real.sqrt (4 * (absNorm (span {μ}) : ℝ) / (3 * x)))) := by
  have hs := summable_dualP P hx
  set f : 𝓞 K → ℂ := fun μ => dualP P (Real.sqrt (4 * (absNorm (span {μ}) : ℝ) / (3 * x)))
  have hsplit : ∀ μ, f μ = (if μ = 0 then f 0 else 0) + (if μ = 0 then 0 else f μ) := by
    intro μ; by_cases h : μ = 0 <;> simp [h]
  have hs2 : Summable fun μ : 𝓞 K => (if μ = 0 then 0 else f μ) :=
    (hs.sub (summable_of_ne_finset_zero (s := {0}) (f := fun μ => if μ = 0 then f 0 else 0)
      (fun μ hμ => by simp at hμ; simp [hμ]))).congr fun μ => by
        by_cases h : μ = 0 <;> simp [h]
  have htot : ∑' μ, f μ = f 0 + ∑' μ, (if μ = 0 then 0 else f μ) := by
    rw [tsum_congr hsplit, Summable.tsum_add (summable_of_ne_finset_zero (s := {0})
      (fun μ hμ => by simp at hμ; simp [hμ])) hs2, tsum_ite_eq]
  have hf0 : f 0 = ((Real.pi : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), P y := by
    simp only [f, span_singleton_zero, absNorm_bot, Nat.cast_zero, mul_zero, zero_div,
      Real.sqrt_zero]
    exact dualP_zero P
  rw [latErr, latS_poisson P hx, htot, hf0]
  push_cast
  ring

/-- **The error of the lattice sum is a Mellin integral on `Re s = ε`**: for every `ε > 0` there is an
integrable `C` with `r_P(x) = ∫ C(t)·x^{ε−2πit} dt` for every `x > 0`. -/
theorem latErr_mellin (P : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ → ℂ, Integrable C ∧ ∀ x : ℝ, 0 < x →
      latErr P x = ∫ t : ℝ, C t * (x : ℂ) ^ ((ε : ℂ) - ((2 * Real.pi * t : ℝ) : ℂ) * I) := by
  obtain ⟨c, hc⟩ := mellin_of_schwartz (dualP P) (σ := 1 + ε) (by linarith)
  set w : ℝ → ℂ := fun t => -(((1 + ε : ℝ)) : ℂ) + ((2 * Real.pi * t : ℝ) : ℂ) * I with hw
  have hwre : ∀ t, (w t).re = -(1 + ε) := fun t => by simp [hw]
  set Nn : 𝓞 K → ℝ := fun μ => (absNorm (span {μ}) : ℝ) with hNn
  have hN1 : ∀ μ : 𝓞 K, μ ≠ 0 → 1 ≤ Nn μ := fun μ hμ => by
    simp only [hNn]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hμ)
  have hsN := summable_absNorm_elt_rpow (s := 1 + ε) (by linarith)
  -- the Dirichlet series of the lattice
  set Z : ℂ → ℂ := fun s => ∑' μ : 𝓞 K, (if μ = 0 then 0 else ((Nn μ : ℝ) : ℂ) ^ s) with hZ
  have hnormN : ∀ t (μ : 𝓞 K), μ ≠ 0 → ‖((Nn μ : ℝ) : ℂ) ^ (w t)‖ = Nn μ ^ (-(1 + ε)) := by
    intro t μ hμ
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hN1 μ hμ]), hwre]
  have hbd : ∀ t (μ : 𝓞 K), ‖(if μ = 0 then 0 else ((Nn μ : ℝ) : ℂ) ^ (w t))‖ ≤
      (absNorm (span {μ}) : ℝ) ^ (-(1 + ε)) := by
    intro t μ
    by_cases h : μ = 0
    · simp only [h, ite_true, norm_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · simp only [h, ite_false]; rw [hnormN t μ h]
  have hZsum : ∀ t, Summable fun μ : 𝓞 K => (if μ = 0 then 0 else ((Nn μ : ℝ) : ℂ) ^ (w t)) :=
    fun t => Summable.of_norm_bounded hsN (hbd t)
  set Z0 : ℝ := ∑' μ : 𝓞 K, (absNorm (span {μ}) : ℝ) ^ (-(1 + ε)) with hZ0
  have hZle : ∀ t, ‖Z (w t)‖ ≤ Z0 := fun t =>
    (norm_tsum_le_tsum_norm (hZsum t).norm).trans
      ((hZsum t).norm.tsum_le_tsum (hbd t) hsN)
  have hcont_w : Continuous w := by fun_prop
  have hZcont : Continuous fun t => Z (w t) := by
    refine continuous_tsum (fun μ => ?_) hsN fun μ t => hbd t μ
    by_cases h : μ = 0
    · simp only [h, ite_true]; exact continuous_const
    · simp only [h, ite_false]
      have : ((Nn μ : ℝ) : ℂ) ≠ 0 := by
        have := hN1 μ h; exact_mod_cast (show (Nn μ : ℝ) ≠ 0 by linarith)
      exact hcont_w.const_cpow (Or.inl this)
  have h43 : ∀ t, ‖((4 / 3 : ℝ) : ℂ) ^ (w t)‖ = (4 / 3 : ℝ) ^ (-(1 + ε)) := fun t => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), hwre]
  -- the coefficient
  set C : ℝ → ℂ := fun t => ((2 / Real.sqrt 3 : ℝ) : ℂ) * c t * (((4 / 3 : ℝ) : ℂ) ^ (w t)) *
    Z (w t) with hC
  have hCint : Integrable C := by
    refine (c.integrable.norm.const_mul ((2 / Real.sqrt 3) * (4 / 3 : ℝ) ^ (-(1 + ε)) * Z0)).mono'
      ?_ (Filter.Eventually.of_forall fun t => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine ((continuous_const.mul c.continuous).mul ?_).mul hZcont
      exact hcont_w.const_cpow (Or.inl (by norm_num))
    · simp only [hC, norm_mul, Complex.norm_real, h43]
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 := hZle t
      calc 2 / Real.sqrt 3 * ‖c t‖ * (4 / 3 : ℝ) ^ (-(1 + ε)) * ‖Z (w t)‖
          ≤ 2 / Real.sqrt 3 * ‖c t‖ * (4 / 3 : ℝ) ^ (-(1 + ε)) * Z0 := by gcongr
        _ = _ := by ring
  refine ⟨C, hCint, fun x hx => ?_⟩
  rw [latErr_eq P hx]
  -- each nonzero frequency through the Mellin representation
  set y : 𝓞 K → ℝ := fun μ => 4 * Nn μ / (3 * x) with hy
  have hypos : ∀ μ : 𝓞 K, μ ≠ 0 → 0 < y μ := fun μ hμ => by
    simp only [hy]; have := hN1 μ hμ; positivity
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hxarg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne
  have hfac : ∀ μ : 𝓞 K, μ ≠ 0 → ∀ t, ((y μ : ℝ) : ℂ) ^ (w t) =
      ((4 / 3 : ℝ) : ℂ) ^ (w t) * ((Nn μ : ℝ) : ℂ) ^ (w t) * ((x : ℂ) ^ (w t))⁻¹ := by
    intro μ hμ t
    have hN0 : 0 ≤ Nn μ := by linarith [hN1 μ hμ]
    rw [show y μ = (4 / 3) * Nn μ * x⁻¹ by simp only [hy]; field_simp]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) hN0, Complex.ofReal_inv,
      Complex.inv_cpow _ _ hxarg]
  -- the terms of the sum
  set F : 𝓞 K → ℝ → ℂ := fun μ t => if μ = 0 then 0 else c t * ((y μ : ℝ) : ℂ) ^ (w t) with hF
  have hterm : ∀ μ : 𝓞 K, (if μ = 0 then 0 else
      dualP P (Real.sqrt (4 * (absNorm (span {μ}) : ℝ) / (3 * x)))) = ∫ t, F μ t := by
    intro μ
    by_cases h : μ = 0
    · simp [hF, h]
    · simp only [h, ite_false, hF]
      exact hc (y μ) (hypos μ h)
  have hnormF : ∀ μ t, ‖F μ t‖ = (if μ = 0 then 0 else y μ ^ (-(1 + ε))) * ‖c t‖ := by
    intro μ t
    by_cases h : μ = 0
    · simp [hF, h]
    · simp only [hF, h, ite_false, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (hypos μ h), hwre, mul_comm]
  have hFint : ∀ μ, Integrable (F μ) := by
    intro μ
    refine (c.integrable.norm.const_mul (if μ = 0 then 0 else y μ ^ (-(1 + ε)))).mono' ?_
      (Filter.Eventually.of_forall fun t => (hnormF μ t).le)
    by_cases h : μ = 0
    · simp only [hF, h, ite_true]; exact aestronglyMeasurable_const
    · simp only [hF, h, ite_false]
      refine Continuous.aestronglyMeasurable (c.continuous.mul ?_)
      have : ((y μ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hypos μ h).ne'
      exact hcont_w.const_cpow (Or.inl this)
  have hFsum : Summable fun μ => ∫ t, ‖F μ t‖ := by
    simp_rw [hnormF, integral_const_mul]
    refine Summable.mul_right _ ?_
    refine (hsN.mul_left ((4 / (3 * x)) ^ (-(1 + ε)))).congr fun μ => ?_
    by_cases h : μ = 0
    · simp only [h, ite_true, span_singleton_zero, absNorm_bot, Nat.cast_zero]
      rw [Real.zero_rpow (by linarith), mul_zero]
    · simp only [h, ite_false, hy]
      rw [show 4 * Nn μ / (3 * x) = 4 / (3 * x) * Nn μ by ring,
        Real.mul_rpow (by positivity) (by linarith [hN1 μ h])]
  rw [tsum_congr hterm, integral_tsum_of_summable_integral_norm hFint hFsum, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  -- pointwise: the sum over `μ` is `Z(w t)` times the factors
  have hpt : ∀ μ, F μ t = (c t * ((4 / 3 : ℝ) : ℂ) ^ (w t) * ((x : ℂ) ^ (w t))⁻¹) *
      (if μ = 0 then 0 else ((Nn μ : ℝ) : ℂ) ^ (w t)) := by
    intro μ
    by_cases h : μ = 0
    · simp [hF, h]
    · simp only [hF, h, ite_false]; rw [hfac μ h t]; ring
  dsimp only
  rw [tsum_congr hpt, tsum_mul_left]
  have hexp : (x : ℂ) ^ ((ε : ℂ) - ((2 * Real.pi * t : ℝ) : ℂ) * I) =
      ((x : ℂ))⁻¹ * ((x : ℂ) ^ (w t))⁻¹ := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hxc]
    congr 1; simp only [hw]; push_cast; ring
  simp only [hC, hZ]
  rw [hexp]
  push_cast
  field_simp

/-- `Σ_{T⊆S} (−1)^{|T|}·∏_{P∈T} a_P = ∏_{P∈S} (1 − a_P)`. -/
theorem sum_powerset_neg_prod {ι : Type*} (S : Finset ι) (a : ι → ℂ) :
    ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * ∏ P ∈ T, a P = ∏ P ∈ S, (1 - a P) := by
  have h := Finset.prod_add (fun P => -a P) (fun _ => (1 : ℂ)) S
  simp only [Finset.prod_const_one, mul_one] at h
  rw [show (∏ P ∈ S, (1 - a P)) = ∏ P ∈ S, (-a P + 1) from
    Finset.prod_congr rfl fun P _ => by ring, h]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_neg]

/-- `(∏_{P∈T} x_P)^s = ∏_{P∈T} x_P^s` for nonnegative real `x_P`. -/
theorem cpow_prod_ofReal {ι : Type*} (T : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (s : ℂ) :
    (((∏ i ∈ T, x i : ℝ)) : ℂ) ^ s = ∏ i ∈ T, ((x i : ℝ) : ℂ) ^ s := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hx i) (Finset.prod_nonneg fun j _ => hx j), ih]

/-- **The Möbius sums of the lattice error are Euler products**: for every `ε > 0` there is an
integrable `C` with `Σ_{T⊆S} (−1)^{|T|}·r_P(β·N(T)) = ∫ C(t)·β^{s}·∏_{P∈S}(1 − N(P)^{s}) dt`,
`s = ε − 2πit`, for every `β > 0` and every finite set `S` of primes. -/
theorem latErr_moebius (P : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ → ℂ, Integrable C ∧ ∀ β : ℝ, 0 < β → ∀ S : Finset Pr,
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * latErr P (β * nI T) =
        ∫ t : ℝ, C t * ((β : ℂ) ^ ((ε : ℂ) - ((2 * Real.pi * t : ℝ) : ℂ) * I) *
          ∏ Q ∈ S, (1 - ((absNorm Q.1 : ℝ) : ℂ) ^ ((ε : ℂ) - ((2 * Real.pi * t : ℝ) : ℂ) * I))) := by
  obtain ⟨C, hC, hCrep⟩ := latErr_mellin P hε
  refine ⟨C, hC, fun β hβ S => ?_⟩
  set s : ℝ → ℂ := fun t => (ε : ℂ) - ((2 * Real.pi * t : ℝ) : ℂ) * I with hs
  have hsre : ∀ t, (s t).re = ε := fun t => by simp [hs]
  have hcs : Continuous s := by fun_prop
  -- each term as a Mellin integral
  have hterm : ∀ T ∈ S.powerset, (-1 : ℂ) ^ T.card * latErr P (β * nI T) =
      ∫ t : ℝ, (-1 : ℂ) ^ T.card * (C t * ((β * nI T : ℝ) : ℂ) ^ s t) := by
    intro T _
    rw [hCrep _ (mul_pos hβ (nI_pos T)), integral_const_mul]
  have hint : ∀ T ∈ S.powerset,
      Integrable fun t : ℝ => (-1 : ℂ) ^ T.card * (C t * ((β * nI T : ℝ) : ℂ) ^ s t) := by
    intro T _
    refine Integrable.const_mul ?_ _
    have hpos : 0 < β * nI T := mul_pos hβ (nI_pos T)
    refine (hC.norm.mul_const ((β * nI T) ^ ε)).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · refine hC.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
      exact hcs.const_cpow (Or.inl (by exact_mod_cast hpos.ne'))
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, hsre]
  rw [Finset.sum_congr rfl hterm, ← integral_finsetSum _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  have hfac : ∀ T : Finset Pr, ((β * nI T : ℝ) : ℂ) ^ s t =
      (β : ℂ) ^ s t * ∏ Q ∈ T, ((absNorm Q.1 : ℝ) : ℂ) ^ s t := by
    intro T
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hβ.le (nI_pos T).le, nI_eq_prod,
      cpow_prod_ofReal T _ (fun Q => Nat.cast_nonneg _)]
  simp_rw [hfac]
  rw [← sum_powerset_neg_prod S (fun Q => ((absNorm Q.1 : ℝ) : ℂ) ^ s t), Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  ring

/-- **The size of the Euler product**: `|∏_{P∈S}(1 − N(P)^{s})| ≤ ∏_{P∈S}(1 + N(P)^{ε})` on
`Re s = ε`. -/
theorem norm_prod_one_sub_le (S : Finset Pr) {ε : ℝ} (t : ℝ) :
    ‖∏ Q ∈ S, (1 - ((absNorm Q.1 : ℝ) : ℂ) ^ ((ε : ℂ) - ((2 * Real.pi * t : ℝ) : ℂ) * I))‖ ≤
      ∏ Q ∈ S, (1 + (absNorm Q.1 : ℝ) ^ ε) := by
  rw [norm_prod]
  gcongr with Q
  have hQ : (0 : ℝ) < absNorm Q.1 := by
    have h := one_le_nI {Q}
    rw [nI_eq_prod, Finset.prod_singleton] at h
    linarith
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

/-- `e ↦ P(β·N(e))` is summable over `ℤ[ω]` for `β > 0`. -/
theorem summable_profile (P : 𝓢(ℝ, ℂ)) {β : ℝ} (hβ : 0 < β) :
    Summable fun e : 𝓞 K => P (β * (absNorm (span {e}) : ℝ)) := by
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hb : ((Real.sqrt β : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsb.ne'
  refine (summable_σO (affS (radS P) 0 ((Real.sqrt β : ℝ) : ℂ) hb)).congr fun e => ?_
  rw [affS_apply, zero_add, radS_apply, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg hsb.le, Real.sq_sqrt hβ.le, sq_norm_σO]

/-- **The sum with excluded primes as a Möbius sum of lattice sums**:
`Σ_{e : π_Q ∤ e ∀Q∈S} P(β·N(e)) = Σ_{T⊆S} (−1)^{|T|}·L_P(β·N(T))`. -/
theorem excl_eq_latS (P : 𝓢(ℝ, ℂ)) {β : ℝ} (hβ : 0 < β) (S : Finset Pr) :
    ∑' e : 𝓞 K, (if ∀ Q ∈ S, ¬ πP Q ∣ e then P (β * (absNorm (span {e}) : ℝ)) else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * latS P (β * nI T) := by
  have hs := summable_profile P hβ
  set g : 𝓞 K → ℂ := fun e => P (β * (absNorm (span {e}) : ℝ)) with hg
  have hsplit : ∀ e, (if ∀ Q ∈ S, ¬ πP Q ∣ e then g e else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (if (∏ Q ∈ T, πP Q) ∣ e then g e else 0) := by
    intro e
    have h := indicator_not_dvd S πP (hcopPr S) e
    have e1 : (if ∀ Q ∈ S, ¬ πP Q ∣ e then g e else 0) =
        (if ∀ Q ∈ S, ¬ πP Q ∣ e then (1 : ℂ) else 0) * g e := by split_ifs <;> ring
    rw [e1, h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    split_ifs <;> ring
  have hsT : ∀ T ∈ S.powerset, Summable fun e =>
      (-1 : ℂ) ^ T.card * (if (∏ Q ∈ T, πP Q) ∣ e then g e else 0) := by
    intro T _
    refine Summable.of_norm_bounded hs.norm fun e => ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  rw [tsum_congr hsplit, Summable.tsum_finsetSum hsT]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [tsum_mul_left, tsum_ite_dvd_eq _ (prod_πP_ne_zero T)]
  congr 1
  refine tsum_congr fun ℓ => ?_
  simp only [hg]
  congr 1
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul, absNorm_span_prod_πP]
  ring

/-- **The explicit formula for the sum with excluded primes**:
`Σ_{e : π_Q ∤ e ∀Q∈S} P(β·N(e)) = (2π/(√3β))·(∫_0^∞P)·∏_{Q∈S}(1 − 1/N(Q))
  + Σ_{T⊆S} (−1)^{|T|}·r_P(β·N(T))`. -/
theorem excl_eq_main_add (P : 𝓢(ℝ, ℂ)) {β : ℝ} (hβ : 0 < β) (S : Finset Pr) :
    ∑' e : 𝓞 K, (if ∀ Q ∈ S, ¬ πP Q ∣ e then P (β * (absNorm (span {e}) : ℝ)) else 0) =
      ((2 * Real.pi / (Real.sqrt 3 * β) : ℝ) : ℂ) * (∫ y in Ioi (0 : ℝ), P y) *
          ∏ Q ∈ S, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹) +
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * latErr P (β * nI T) := by
  rw [excl_eq_latS P hβ S]
  have hlat : ∀ T : Finset Pr, latS P (β * nI T) =
      ((2 * Real.pi / (Real.sqrt 3 * β) : ℝ) : ℂ) * (∫ y in Ioi (0 : ℝ), P y) *
        ∏ Q ∈ T, (((absNorm Q.1 : ℝ) : ℂ))⁻¹ + latErr P (β * nI T) := by
    intro T
    have hnI : (nI T : ℂ) = ∏ Q ∈ T, ((absNorm Q.1 : ℝ) : ℂ) := by
      rw [nI_eq_prod]; push_cast; rfl
    have h0 : (nI T : ℂ) ≠ 0 := by exact_mod_cast (nI_pos T).ne'
    have hβ0 : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
    have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne'
    rw [latErr, Finset.prod_inv_distrib, ← hnI]
    push_cast
    field_simp
    ring
  simp_rw [hlat, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [← sum_powerset_neg_prod S (fun Q => (((absNorm Q.1 : ℝ) : ℂ))⁻¹), Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  ring

end Eis

end

#print axioms Eis.schwartz_exp_comp_S
#print axioms Eis.mellin_of_schwartz
#print axioms Eis.summable_absNorm_elt_rpow
#print axioms Eis.fourier_radS_eq
#print axioms Eis.dualP_zero
#print axioms Eis.latS_poisson
#print axioms Eis.latErr_eq
#print axioms Eis.latErr_mellin
#print axioms Eis.sum_powerset_neg_prod
#print axioms Eis.latErr_moebius
#print axioms Eis.norm_prod_one_sub_le
#print axioms Eis.summable_profile
#print axioms Eis.excl_eq_latS
#print axioms Eis.excl_eq_main_add
