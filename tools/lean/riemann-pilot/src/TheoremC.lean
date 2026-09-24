import Mathlib
import Mollify

/-! # Round 48's Theorem C, formal, in `H²` generality

**Theorem C (flat ⇒ degenerate).** If `h` is in the ground space and is `H²`-flat at the edges (`h, h'`
vanish outside `[−a, a]`, `h'` is the primitive of an `L²` function `h₂` which is a probe), then
`h₂ = h''` is in the ground space too. So a nonzero such `h` forces `dim V ≥ 2`.

The proof, in the Green form of round 53:
1. `f = h₂ − h/4` is a pole-free probe with `G f = h` (`flat_green`).
2. For every pole-free probe `m`, `Q_λ(G m − f) = Q_λ(G m) + Q_λ(f) ≥ Q_λ(f)` (`Qlam_green_sub`): the
   cross term vanishes by the swap `B(G m, f) = B(m, G f)` and Euler–Lagrange for `G f = h`.
3. **Density**: `G m` can be taken arbitrarily close to `f` in `L²` and in archimedean energy
   (`green_dense`), by dilating `f` into `[−λa, λa]` and smoothing it with three box averages.
4. Hence `Q_λ(f) = 0`, so `f ∈ V` and `h₂ = f + h/4 ∈ V`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## The algebraic core -/

/-- `Q_λ(g) = Q(g) − λ₁‖g‖²`, nonnegative on probes with kernel the ground space. -/
def Qlam (a : ℝ) (g : ℝ → ℝ) : ℝ := weilQ a g - lam a * normSq g

/-- Cauchy–Schwarz for the pole functional. -/
theorem poleR_sq_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    poleR g a ^ 2 ≤ (∫ u in (-a)..a, Real.exp (-u)) * normSq g := by
  set E := ∫ u in (-a)..a, Real.exp (-u)
  set P := poleR g a
  set N := ∫ u in (-a)..a, g u ^ 2
  have hE : 0 < E := intervalIntegral.intervalIntegral_pos_of_pos_on
    ((Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _) (fun _ _ => exp_pos _)
    (by linarith)
  have i1 : IntervalIntegrable (fun u => g u ^ 2) volume (-a) a :=
    hg.integrable_sq.intervalIntegrable
  have i2 := poleR_integrable hg a
  have i3 : IntervalIntegrable (fun u => Real.exp (-u)) volume (-a) a :=
    (Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _
  have key : ∀ s : ℝ, 0 ≤ N - 2 * s * P + s ^ 2 * E := by
    intro s
    have h0 : 0 ≤ ∫ u in (-a)..a, (g u - s * Real.exp (-(u / 2))) ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
    have e : (∫ u in (-a)..a, (g u - s * Real.exp (-(u / 2))) ^ 2)
        = N - 2 * s * P + s ^ 2 * E := by
      have hpt : ∀ u, (g u - s * Real.exp (-(u / 2))) ^ 2
          = g u ^ 2 - (2 * s) * (g u * Real.exp (-(u / 2))) + s ^ 2 * Real.exp (-u) := by
        intro u
        have : Real.exp (-(u / 2)) ^ 2 = Real.exp (-u) := by
          rw [← Real.exp_nat_mul]; ring_nf
        rw [sub_sq, mul_pow, this]; ring
      simp only [hpt]
      rw [intervalIntegral.integral_add (i1.sub (i2.const_mul _)) (i3.const_mul _),
        intervalIntegral.integral_sub i1 (i2.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      rfl
    linarith
  have hN : N ≤ normSq g := by
    unfold normSq
    simp only [N]
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_le_integral hg.integrable_sq (Eventually.of_forall fun _ => sq_nonneg _)
  have h1 := key (P / E)
  have h2 : P ^ 2 ≤ N * E := by
    have : N - 2 * (P / E) * P + (P / E) ^ 2 * E = N - P ^ 2 / E := by field_simp; ring
    rw [this, sub_nonneg, div_le_iff₀ hE] at h1; linarith
  nlinarith

/-- **`Q_λ` is controlled by the `L²` norm and the archimedean energy.** -/
theorem Qlam_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : Probe a g) :
    Qlam a g ≤ (2 * (∫ u in (-a)..a, Real.exp (-u)) + |weilConst| + |lam a| + 2 * primeWeight a)
      * normSq g + archE g := by
  have hN := normSq_nonneg g
  have hP := poleR_sq_le ha hg.memL2
  have hS : |primeS g| ≤ primeWeight a * normSq g := abs_prime_sum_le hg
  unfold Qlam
  rw [weilQ_eq']
  have h1 : weilConst * normSq g ≤ |weilConst| * normSq g :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hN
  have h2 : -(lam a * normSq g) ≤ |lam a| * normSq g := by
    rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs _) hN
  have h3 : -(2 * primeS g) ≤ 2 * (primeWeight a * normSq g) := by
    linarith [neg_abs_le (primeS g)]
  nlinarith

/-- **The cross term vanishes**: for `f` a pole-free probe with `G f` in the ground space and `m` a
pole-free probe, `Q_λ(G m + r f) = Q_λ(G m) + r² Q_λ(f)`. -/
theorem Qlam_green_add {a : ℝ} (ha : 0 < a) {f m : ℝ → ℝ} (hf : Probe a f) (hfp : poleR f a = 0)
    (hG : Gpole f a ∈ groundSpace a) (hm : Probe a m) (hmp : poleR m a = 0) (r : ℝ) :
    Qlam a (fun t => Gpole m a t + r * f t) = Qlam a (Gpole m a) + r ^ 2 * Qlam a f := by
  have hGm := Gpole_probe hm ha.le hmp
  have e := Qlam_add_smul hGm hf r
  have hB : bil0 a (Gpole m a) f + 2 * poleR (Gpole m a) a * poleR f a
      - lam a * xcorr (Gpole m a) f 0 = 0 := by
    rw [hfp, mul_zero, add_zero, bil0_G_swap ha.le hm hf hfp, xcorr_G_swap ha.le hm hf hfp]
    have el := euler_lagrange_mem hG hm
    rw [hmp, mul_zero, add_zero] at el
    rw [bil0_comm, xcorr_comm, el, sub_self]
  unfold Qlam
  rw [e, hB]; ring

/-- `Q_λ(G m − f) ≥ Q_λ(f)`. -/
theorem Qlam_green_sub {a : ℝ} (ha : 0 < a) {f m : ℝ → ℝ} (hf : Probe a f) (hfp : poleR f a = 0)
    (hG : Gpole f a ∈ groundSpace a) (hm : Probe a m) (hmp : poleR m a = 0) :
    Qlam a f ≤ Qlam a (fun t => Gpole m a t - f t) := by
  have e := Qlam_green_add ha hf hfp hG hm hmp (-1)
  have hfun : (fun t => Gpole m a t + (-1) * f t) = fun t => Gpole m a t - f t := by
    funext t; ring
  rw [hfun] at e
  have h0 := Qlam_nonneg (Gpole_probe hm ha.le hmp)
  rw [e]; unfold Qlam at h0 ⊢; nlinarith

/-- **Theorem C in Green form, given density.** If `f` is a pole-free probe with `G f` in the ground
space, and `G m` approximates `f` (in `L²` and archimedean energy) over pole-free probes `m`, then `f`
is in the ground space. -/
theorem mem_of_green_dense {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : Probe a f)
    (hfp : poleR f a = 0) (hG : Gpole f a ∈ groundSpace a)
    (hdense : ∀ ε > 0, ∃ m, Probe a m ∧ poleR m a = 0 ∧
      normSq (fun t => Gpole m a t - f t) ≤ ε ∧ archE (fun t => Gpole m a t - f t) ≤ ε) :
    f ∈ groundSpace a := by
  set K := 2 * (∫ u in (-a)..a, Real.exp (-u)) + |weilConst| + |lam a| + 2 * primeWeight a
  have hK : 0 ≤ K := by
    have : 0 ≤ primeWeight a := Finset.sum_nonneg fun n _ =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    have : 0 ≤ ∫ u in (-a)..a, Real.exp (-u) :=
      intervalIntegral.integral_nonneg (by linarith) fun _ _ => (exp_pos _).le
    positivity
  have hle : ∀ ε > 0, Qlam a f ≤ (K + 1) * ε := by
    intro ε hε
    obtain ⟨m, hm, hmp, hn, he⟩ := hdense ε hε
    have hd : Probe a (fun t => Gpole m a t - f t) :=
      (probe_add_sub (Gpole_probe hm ha.le hmp) hf).2
    have h1 := Qlam_green_sub ha hf hfp hG hm hmp
    have h2 := Qlam_le ha hd
    nlinarith [mul_le_mul_of_nonneg_left hn hK]
  have h0 : Qlam a f ≤ 0 := by
    by_contra hc
    push Not at hc
    have := hle (Qlam a f / (2 * (K + 1))) (by positivity)
    have hK1 : 0 < K + 1 := by linarith
    have e : (K + 1) * (Qlam a f / (2 * (K + 1))) = Qlam a f / 2 := by field_simp
    linarith
  have h1 := Qlam_nonneg hf
  refine ⟨hf, ?_⟩
  unfold Qlam at h0
  linarith

/-! ## `H²`-flat functions are Green solutions -/

/-- **Edge-flat in `H²`**: `h` is differentiable with derivative `h₁`, `h₁` is the primitive (from
`−a`) of `h₂`, `h` and `h₁` vanish outside `[−a, a]`, and `h₂ = h''` is a probe. -/
structure FlatH2 (a : ℝ) (h h₁ h₂ : ℝ → ℝ) : Prop where
  d1 : ∀ x, HasDerivAt h (h₁ x) x
  prim : ∀ x, h₁ x = ∫ y in (-a)..x, h₂ y
  supp : ∀ x, a < |x| → h x = 0
  supp1 : ∀ x, a < |x| → h₁ x = 0
  probe2 : Probe a h₂

/-- A continuous function vanishing on `|x| > a` vanishes at `±a`. -/
theorem zero_at_edge {a : ℝ} {φ : ℝ → ℝ} (hc : Continuous φ) (hs : ∀ x, a < |x| → φ x = 0) :
    φ a = 0 ∧ φ (-a) = 0 := by
  have hcl : IsClosed {x | φ x = 0} := isClosed_eq hc continuous_const
  by_cases ha : 0 ≤ a
  · have h1 : Ioi a ⊆ {x | φ x = 0} := fun x hx =>
      hs x (by rw [abs_of_pos (lt_of_le_of_lt ha hx)]; exact hx)
    have h2 : Iio (-a) ⊆ {x | φ x = 0} := fun x hx =>
      hs x (by rw [abs_of_neg (by linarith [show x < -a from hx])]; linarith [show x < -a from hx])
    have e1 := hcl.closure_subset_iff.2 h1
    have e2 := hcl.closure_subset_iff.2 h2
    rw [closure_Ioi] at e1; rw [closure_Iio] at e2
    exact ⟨e1 (le_refl a), e2 (le_refl (-a))⟩
  · push Not at ha
    exact ⟨hs a (by rw [abs_of_neg ha]; linarith), hs (-a) (by rw [abs_neg, abs_of_neg ha]; linarith)⟩

theorem FlatH2.cont {a : ℝ} {h h₁ h₂ : ℝ → ℝ} (hf : FlatH2 a h h₁ h₂) : Continuous h :=
  continuous_iff_continuousAt.2 fun x => (hf.d1 x).continuousAt

theorem FlatH2.ii2 {a : ℝ} {h h₁ h₂ : ℝ → ℝ} (hf : FlatH2 a h h₁ h₂) (α β : ℝ) :
    IntervalIntegrable h₂ volume α β :=
  memLp_intervalIntegrable hf.probe2.memL2 α β

theorem FlatH2.cont1 {a : ℝ} {h h₁ h₂ : ℝ → ℝ} (hf : FlatH2 a h h₁ h₂) : Continuous h₁ := by
  have : h₁ = fun x => ∫ y in (-a)..x, h₂ y := funext hf.prim
  rw [this]; exact intervalIntegral.continuous_primitive hf.ii2 _

/-- `∫_{−a}^x h₂(y) e^{cy} dy = e^{cx}h₁(x) − c∫_{−a}^x h₁(y) e^{cy} dy` (integration by parts with
`h₁` merely a primitive of an `L²` function), for `x ≥ −a`. -/
theorem ibp_prim {a : ℝ} {h h₁ h₂ : ℝ → ℝ} (hf : FlatH2 a h h₁ h₂) (c : ℝ) {x : ℝ} (hx : -a ≤ x) :
    (∫ y in (-a)..x, h₂ y * Real.exp (c * y))
      = Real.exp (c * x) * h₁ x - c * ∫ y in (-a)..x, h₁ y * Real.exp (c * y) := by
  have hcont : Continuous fun s => c * Real.exp (c * s) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hE : ∀ y, (∫ s in y..x, c * Real.exp (c * s)) = Real.exp (c * x) - Real.exp (c * y) := by
    intro y
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => Real.exp (c * s))
      (fun s _ => by simpa [mul_comm] using ((hasDerivAt_id s).const_mul c).exp)
      (hcont.intervalIntegrable _ _)
  have hsw := triangle_swap_int hx (e := fun s => c * Real.exp (c * s)) (f := h₂)
    (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) ((hf.ii2 (-a) x).1)
  have i2 := hf.ii2 (-a) x
  have i3 : IntervalIntegrable (fun y => h₂ y * (Real.exp (c * x) - Real.exp (c * y))) volume (-a) x :=
    i2.mul_continuousOn (by fun_prop)
  calc (∫ y in (-a)..x, h₂ y * Real.exp (c * y))
      = ∫ y in (-a)..x, (Real.exp (c * x) * h₂ y - h₂ y * (Real.exp (c * x) - Real.exp (c * y))) := by
        refine intervalIntegral.integral_congr fun y _ => ?_
        ring
    _ = Real.exp (c * x) * h₁ x - ∫ y in (-a)..x, h₂ y * ∫ s in y..x, c * Real.exp (c * s) := by
        rw [intervalIntegral.integral_sub (i2.const_mul _) i3, intervalIntegral.integral_const_mul,
          ← hf.prim]
        congr 1
        refine intervalIntegral.integral_congr fun y _ => ?_
        rw [hE y]
    _ = Real.exp (c * x) * h₁ x - ∫ s in (-a)..x, (c * Real.exp (c * s)) * ∫ y in (-a)..s, h₂ y := by
        rw [hsw]
    _ = _ := by
        congr 1
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        rw [← hf.prim]; ring

/-- Classical integration by parts: `∫_{−a}^x h₁(y) e^{cy} dy = e^{cx}h(x) − c∫_{−a}^x h(y) e^{cy} dy`. -/
theorem ibp_one {a : ℝ} {h h₁ h₂ : ℝ → ℝ} (hf : FlatH2 a h h₁ h₂) (c x : ℝ) :
    (∫ y in (-a)..x, h₁ y * Real.exp (c * y))
      = Real.exp (c * x) * h x - c * ∫ y in (-a)..x, h y * Real.exp (c * y) := by
  have hd : ∀ y, HasDerivAt (fun y => Real.exp (c * y) * h y)
      (c * Real.exp (c * y) * h y + Real.exp (c * y) * h₁ y) y := by
    intro y
    have h1 := (((hasDerivAt_id y).const_mul c).exp).mul (hf.d1 y)
    have e : Real.exp (c * id y) * (c * 1) * h y + Real.exp (c * id y) * h₁ y
        = c * Real.exp (c * y) * h y + Real.exp (c * y) * h₁ y := by simp only [id]; ring
    rw [e] at h1; exact h1
  have hc : Continuous fun y => c * Real.exp (c * y) * h y + Real.exp (c * y) * h₁ y := by
    have := hf.cont; have := hf.cont1; fun_prop
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hc.intervalIntegrable (-a) x)
  have h0 : h (-a) = 0 := (zero_at_edge hf.cont hf.supp).2
  rw [h0, mul_zero, sub_zero] at hF
  have i1 : IntervalIntegrable (fun y => c * Real.exp (c * y) * h y) volume (-a) x := by
    have := hf.cont; exact (by fun_prop : Continuous _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun y => Real.exp (c * y) * h₁ y) volume (-a) x := by
    have := hf.cont1; exact (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2] at hF
  have e1 : (∫ y in (-a)..x, c * Real.exp (c * y) * h y) = c * ∫ y in (-a)..x, h y * Real.exp (c * y) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun y _ => by ring
  have e2 : (∫ y in (-a)..x, Real.exp (c * y) * h₁ y) = ∫ y in (-a)..x, h₁ y * Real.exp (c * y) :=
    intervalIntegral.integral_congr fun y _ => by ring
  rw [e1, e2] at hF
  linarith

/-- **The two pole integrals of `f = h₂ − h/4`**: for `c = ±½`,
`∫_{−a}^x f(y) e^{cy} dy = e^{cx}(h₁(x) − c·h(x))`. -/
theorem flat_pole_int {a : ℝ} (ha : 0 ≤ a) {h h₁ h₂ : ℝ → ℝ} (hf : FlatH2 a h h₁ h₂) {c : ℝ}
    (hc : c ^ 2 = 1 / 4)
    (x : ℝ) :
    (∫ y in (-a)..x, (h₂ y - h y / 4) * Real.exp (c * y))
      = Real.exp (c * x) * (h₁ x - c * h x) := by
  have ih : IntervalIntegrable (fun y => h y * Real.exp (c * y)) volume (-a) x := by
    have := hf.cont; exact (by fun_prop : Continuous _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun y => h₂ y * Real.exp (c * y)) volume (-a) x :=
    (hf.ii2 (-a) x).mul_continuousOn (by fun_prop)
  have hsplit : (∫ y in (-a)..x, (h₂ y - h y / 4) * Real.exp (c * y))
      = (∫ y in (-a)..x, h₂ y * Real.exp (c * y)) - (1 / 4) * ∫ y in (-a)..x, h y * Real.exp (c * y) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub i2 (ih.const_mul _)]
    exact intervalIntegral.integral_congr fun y _ => by ring
  rcases le_or_gt (-a) x with hx | hx
  · rw [hsplit, ibp_prim hf c hx, ibp_one hf c x]
    linear_combination (∫ y in (-a)..x, h y * Real.exp (c * y)) * hc
  · -- to the left of the support everything vanishes
    have hx' : a < |x| := by rw [abs_of_neg (by linarith)]; linarith
    rw [hf.supp1 x hx', hf.supp x hx']
    simp only [mul_zero, sub_zero]
    refine intervalIntegral.integral_zero_ae ?_
    filter_upwards [ae_ne_pt (-a)] with y hy hyI
    rw [uIoc_of_ge hx.le] at hyI
    have hy1 : y < -a := lt_of_le_of_ne hyI.2 hy
    have hy' : a < |y| := by rw [abs_of_neg (by linarith)]; linarith
    rw [hf.probe2.supp y hy', hf.supp y hy']; ring

theorem FlatH2.memLp {a : ℝ} {h h₁ h₂ : ℝ → ℝ} (hf : FlatH2 a h h₁ h₂) : MemLp h 2 volume :=
  hf.cont.memLp_of_hasCompactSupport (hasCompactSupport_of_supp (a := a) hf.supp)

/-- **An `H²`-flat function is the Green solution of `f = h'' − h/4`**, which is pole-free. -/
theorem flat_green {a : ℝ} (ha : 0 ≤ a) {h h₁ h₂ : ℝ → ℝ} (hf : FlatH2 a h h₁ h₂) :
    poleR (fun x => h₂ x - h x / 4) a = 0 ∧ ∀ x, Gpole (fun x => h₂ x - h x / 4) a x = h x := by
  have hm : MemLp (fun x => h₂ x - h x / 4) 2 volume := by
    convert hf.probe2.memL2.sub (hf.memLp.const_mul (1 / 4)) using 1
    funext x; simp only [Pi.sub_apply]; ring
  have hc1 : (-1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  have hc2 : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  refine ⟨?_, fun x => ?_⟩
  · have e := flat_pole_int ha hf hc1 a
    obtain ⟨z1, -⟩ := zero_at_edge hf.cont1 hf.supp1
    obtain ⟨z0, -⟩ := zero_at_edge hf.cont hf.supp
    rw [z1, z0] at e
    unfold poleR
    have hc : (∫ u in (-a)..a, (fun x => h₂ x - h x / 4) u * Real.exp (-(u / 2)))
        = ∫ y in (-a)..a, (h₂ y - h y / 4) * Real.exp (-1 / 2 * y) :=
      intervalIntegral.integral_congr fun y _ => by simp only; ring_nf
    rw [hc, e]; ring
  · rw [Gpole_eq_exp hm, flat_pole_int ha hf hc1 x, flat_pole_int ha hf hc2 x]
    have e1 : Real.exp (x / 2) * Real.exp (-1 / 2 * x) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    have e2 : Real.exp (-(x / 2)) * Real.exp (1 / 2 * x) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    linear_combination (h₁ x + 1 / 2 * h x) * e1 - (h₁ x - 1 / 2 * h x) * e2

/-! ## The approximants: three box averages are Green solutions -/

theorem zero_of_ge {R : ℝ} (hR : 0 ≤ R) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hs : ∀ x, R < |x| → φ x = 0) (x : ℝ) (hx : R ≤ |x|) : φ x = 0 := by
  rcases hx.lt_or_eq with h | h
  · exact hs x h
  · obtain ⟨z1, z2⟩ := zero_at_edge hc hs
    rcases abs_eq hR |>.1 h.symm with e | e <;> rw [e]
    · exact z1
    · exact z2

/-- The shifted-support bound used repeatedly: if `|x| > R + c` and `|s| ≤ c` then `|x + s| > R`. -/
theorem lt_abs_add {R c x s : ℝ} (hx : R + c < |x|) (hs : |s| ≤ c) : R < |x + s| := by
  have := abs_add_le (x + s) (-s)
  rw [add_neg_cancel_right, abs_neg] at this; linarith

/-- **Three box averages of a probe are the Green solution of a pole-free probe.** -/
theorem exists_smooth_green {a ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hδ : 0 < δ) (hρ : ρ + 3 * δ / 2 ≤ a)
    {ψ : ℝ → ℝ} (hψ : Probe ρ ψ) :
    ∃ m, Probe a m ∧ poleR m a = 0 ∧ ∀ x, Gpole m a x = Av δ (Av δ (Av δ ψ)) x := by
  have ha : 0 ≤ a := by linarith
  set A1 := Av δ ψ
  set A2 := Av δ A1
  set A3 := Av δ A2
  have p1 : Probe (ρ + δ / 2) A1 := probe_Av hψ hδ
  have p2 : Probe (ρ + δ / 2 + δ / 2) A2 := probe_Av p1 hδ
  have p3 : Probe (ρ + δ / 2 + δ / 2 + δ / 2) A3 := probe_Av p2 hδ
  have c1 : Continuous A1 := Av_continuous hψ.memL2 δ
  have c2 : Continuous A2 := Av_continuous p1.memL2 δ
  set D2 : ℝ → ℝ := fun x => δ⁻¹ * (A1 (x + δ / 2) - A1 (x - δ / 2))
  have hd2 : ∀ x, HasDerivAt A2 (D2 x) x := fun x => Av_hasDerivAt p1.memL2 c1 δ x
  set A3' : ℝ → ℝ := fun x => δ⁻¹ * (A2 (x + δ / 2) - A2 (x - δ / 2))
  have hd3 : ∀ x, HasDerivAt A3 (A3' x) x := fun x => Av_hasDerivAt p2.memL2 c2 δ x
  set A3'' : ℝ → ℝ := fun x => (δ⁻¹) ^ 2 * (A1 (x + δ) - 2 * A1 x + A1 (x - δ))
  have hd3' : ∀ x, HasDerivAt A3' (A3'' x) x := by
    intro x
    have h := (((hd2 (x + δ / 2)).comp_add_const x (δ / 2)).sub
      ((hd2 (x - δ / 2)).comp_sub_const x (δ / 2))).const_mul δ⁻¹
    convert h using 1
    simp only [A3'', D2]
    rw [show x + δ / 2 + δ / 2 = x + δ by ring, show x + δ / 2 - δ / 2 = x by ring,
      show x - δ / 2 + δ / 2 = x by ring, show x - δ / 2 - δ / 2 = x - δ by ring]
    ring
  have c3'' : Continuous A3'' := by
    have := c1; fun_prop
  have c3' : Continuous A3' := by
    have := c2; fun_prop
  -- supports
  have s1 : ∀ x, ρ + δ / 2 < |x| → A1 x = 0 := p1.supp
  have s2 : ∀ x, ρ + δ / 2 + δ / 2 < |x| → A2 x = 0 := p2.supp
  have sR : ∀ x, ρ + 3 * δ / 2 < |x| → A3'' x = 0 := by
    intro x hx
    have hxp : ρ + δ / 2 < |x + δ| :=
      lt_abs_add (c := δ) (by linarith) (by rw [abs_of_pos hδ])
    have hxm : ρ + δ / 2 < |x - δ| := by
      rw [sub_eq_add_neg]; exact lt_abs_add (c := δ) (by linarith) (by rw [abs_neg, abs_of_pos hδ])
    simp only [A3'']
    rw [s1 _ hxp, s1 x (by linarith), s1 _ hxm]; ring
  have sR' : ∀ x, ρ + 3 * δ / 2 < |x| → A3' x = 0 := by
    intro x hx
    have hδ2 : |δ / 2| = δ / 2 := abs_of_pos (by linarith)
    have hxp : ρ + δ / 2 + δ / 2 < |x + δ / 2| :=
      lt_abs_add (c := δ / 2) (by linarith) hδ2.le
    have hxm : ρ + δ / 2 + δ / 2 < |x - δ / 2| := by
      rw [sub_eq_add_neg]; exact lt_abs_add (c := δ / 2) (by linarith) (by rw [abs_neg, hδ2])
    simp only [A3']
    rw [s2 _ hxp, s2 _ hxm]; ring
  -- `A3''` is a probe
  have hA3''m : MemLp A3'' 2 volume :=
    c3''.memLp_of_hasCompactSupport (hasCompactSupport_of_supp (a := ρ + 3 * δ / 2) sR)
  have pA3'' : Probe a A3'' := by
    refine ⟨fun x => ?_, fun x hx => sR x (by linarith), hA3''m, ?_⟩
    · simp only [A3'']
      rw [show -x + δ = -(x - δ) by ring, show -x - δ = -(x + δ) by ring, p1.even, p1.even, p1.even]
      ring
    · have hfun : A3'' = fun x => (δ⁻¹) ^ 2 * (A1 (x + δ) - 2 * A1 x + A1 (x - δ)) := rfl
      refine Integrable.mono' (p1.arch.const_mul (24 * ((δ⁻¹) ^ 2) ^ 2))
        (measurable_archIntegrand hA3''m).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg hA3''m hu), hfun]
      exact archIntegrand_d2_le p1.memL2 _ δ hu
  -- the flat structure of `A3`
  have hflat : FlatH2 a A3 A3' A3'' := by
    refine ⟨hd3, fun x => ?_, fun x hx => p3.supp x (by linarith), fun x hx => sR' x (by linarith),
      pA3''⟩
    have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd3' y)
      (c3''.intervalIntegrable (-a) x)
    have h0 : A3' (-a) = 0 :=
      zero_of_ge (by linarith) c3' sR' (-a) (by rw [abs_neg, abs_of_nonneg ha]; linarith)
    rw [hF, h0, sub_zero]
  obtain ⟨hpole, hG⟩ := flat_green ha hflat
  refine ⟨fun x => A3'' x - A3 x / 4, ?_, hpole, hG⟩
  have h4 : Probe a (fun x => (-(1 / 4)) * A3 x) := probe_smul (p3.mono (by linarith)) _
  have := (probe_add_sub pA3'' h4).1
  convert this using 1
  funext x; ring

/-! ## Density -/

theorem archE_Av_le {r δ : ℝ} (hδ : 0 < δ) {g : ℝ → ℝ} (hp : Probe r g) :
    archE (Av δ g) ≤ archE g := by
  have hA := memLp_Av hp.memL2 hδ hp.supp
  exact setIntegral_Ioi_le hp.arch (fun u hu => archIntegrand_nonneg hA hu)
    (fun u hu => archIntegrand_Av_le hp.memL2 hA hδ hu)

/-- **`G` of pole-free probes is dense near every probe**, in `L²` and archimedean energy. -/
theorem green_dense {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : Probe a f) :
    ∀ ε > 0, ∃ m, Probe a m ∧ poleR m a = 0 ∧
      normSq (fun t => Gpole m a t - f t) ≤ ε ∧ archE (fun t => Gpole m a t - f t) ≤ ε := by
  intro ε hε
  -- dilate into `[−la, la]`
  have hN := (tendsto_normSq_dil hf.memL2).mono_left (nhdsWithin_le_nhds (s := Iio 1))
  have hE := tendsto_archE_dil ha.le hf
  have ev1 : ∀ᶠ l in 𝓝[<] (1 : ℝ), normSq (fun x => f (x / l) - f x) < ε / 4 :=
    hN.eventually (Iio_mem_nhds (by positivity))
  have ev2 : ∀ᶠ l in 𝓝[<] (1 : ℝ), archE (fun x => f (x / l) - f x) < ε / 4 :=
    hE.eventually (Iio_mem_nhds (by positivity))
  have ev3 : ∀ᶠ l in 𝓝[<] (1 : ℝ), 1 / 2 < l ∧ l < 1 := by
    have h1 : ∀ᶠ l in 𝓝[<] (1 : ℝ), l < 1 := self_mem_nhdsWithin
    have h2 : ∀ᶠ l in 𝓝[<] (1 : ℝ), 1 / 2 < l := nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num))
    exact h2.and h1
  obtain ⟨l, hl1, hl2, hl3, hl4⟩ := (ev1.and (ev2.and ev3)).exists
  set ψ : ℝ → ℝ := fun x => f (x / l)
  have hψ : Probe (l * a) ψ := probe_dil' ha.le hf hl3.le hl4.le
  -- smooth with three box averages
  have ev4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), normSq (fun x => Av δ ψ x - ψ x) < ε / 48 :=
    (tendsto_Av hψ.memL2).eventually (Iio_mem_nhds (by positivity))
  have ev5 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), archE (fun x => Av δ ψ x - ψ x) < ε / 48 :=
    (tendsto_archE_Av hψ).eventually (Iio_mem_nhds (by positivity))
  have ev6 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < (1 - l) * a / 2 := by
    have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < (1 - l) * a / 2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by nlinarith))
    exact h1.and h2
  obtain ⟨δ, hd1, hd2, hδ, hδa⟩ := (ev4.and (ev5.and ev6)).exists
  obtain ⟨m, hm, hmp, hG⟩ := exists_smooth_green (a := a) (ρ := l * a) (by positivity) hδ (by nlinarith) hψ
  refine ⟨m, hm, hmp, ?_⟩
  -- the error `e = Av ψ − ψ` and its two averages
  set e : ℝ → ℝ := fun x => Av δ ψ x - ψ x
  have pA1 : Probe (l * a + δ / 2) (Av δ ψ) := probe_Av hψ hδ
  have pe : Probe (l * a + δ / 2) e := (probe_add_sub pA1 (hψ.mono (by linarith))).2
  have pAe : Probe (l * a + δ / 2 + δ / 2) (Av δ e) := probe_Av pe hδ
  have pAAe : Probe (l * a + δ / 2 + δ / 2 + δ / 2) (Av δ (Av δ e)) := probe_Av pAe hδ
  have pd : Probe a (fun x => ψ x - f x) := (probe_add_sub (hψ.mono (by nlinarith)) hf).2
  have e21 : ∀ x, Av δ (Av δ ψ) x - Av δ ψ x = Av δ e x := fun x =>
    (Av_sub pA1.memL2 hψ.memL2 δ x).symm
  have e32 : ∀ x, Av δ (Av δ (Av δ ψ)) x - Av δ (Av δ ψ) x = Av δ (Av δ e) x := by
    intro x
    have h := (Av_sub (probe_Av pA1 hδ).memL2 pA1.memL2 δ x).symm
    have hfun : (fun t => Av δ (Av δ ψ) t - Av δ ψ t) = Av δ e := funext e21
    rw [hfun] at h; exact h
  have hdec : (fun t => Gpole m a t - f t)
      = fun t => (Av δ (Av δ e) t + Av δ e t + e t) + (ψ t - f t) := by
    funext t
    rw [hG t]
    have h1 := e32 t
    have h2 := e21 t
    simp only [e] at h1 h2 ⊢
    linarith
  have mE3 : MemLp (fun t => Av δ (Av δ e) t + Av δ e t + e t) 2 volume :=
    (pAAe.memL2.add pAe.memL2).add pe.memL2
  rw [hdec]
  constructor
  · have h1 := normSq_add_le mE3 pd.memL2
    have h2 := normSq_add3_le pAAe.memL2 pAe.memL2 pe.memL2
    have h3 := normSq_Av_le pAe.memL2 hδ
    have h4 := normSq_Av_le pe.memL2 hδ
    have h5 : normSq e < ε / 48 := hd1
    have h6 : normSq (fun x => ψ x - f x) < ε / 4 := hl1
    linarith
  · have hsum : IntegrableOn (fun u => 8 * archIntegrand (Av δ (Av δ e)) u
        + 8 * archIntegrand (Av δ e) u + 8 * archIntegrand e u
        + 2 * archIntegrand (fun x => ψ x - f x) u) (Ioi 0) :=
      (((pAAe.arch.const_mul 8).add (pAe.arch.const_mul 8)).add (pe.arch.const_mul 8)).add
        (pd.arch.const_mul 2)
    have hle := setIntegral_Ioi_le
      (F := fun u => archIntegrand (fun t => (Av δ (Av δ e) t + Av δ e t + e t) + (ψ t - f t)) u) hsum
      (fun u hu => archIntegrand_nonneg (mE3.add pd.memL2) hu) (fun u hu => by
        have h1 : archIntegrand (fun t => (Av δ (Av δ e) t + Av δ e t + e t) + (ψ t - f t)) u
            ≤ 2 * archIntegrand (fun t => Av δ (Av δ e) t + Av δ e t + e t) u
              + 2 * archIntegrand (fun x => ψ x - f x) u := archIntegrand_add_le mE3 pd.memL2 hu
        have h2 : archIntegrand (fun t => Av δ (Av δ e) t + Av δ e t + e t) u
            ≤ 4 * archIntegrand (Av δ (Av δ e)) u + 4 * archIntegrand (Av δ e) u
              + 4 * archIntegrand e u := archIntegrand_add3_le pAAe.memL2 pAe.memL2 pe.memL2 hu
        linarith)
    have eint : (∫ u in Ioi (0 : ℝ), (8 * archIntegrand (Av δ (Av δ e)) u
        + 8 * archIntegrand (Av δ e) u + 8 * archIntegrand e u
        + 2 * archIntegrand (fun x => ψ x - f x) u))
        = 8 * archE (Av δ (Av δ e)) + 8 * archE (Av δ e) + 8 * archE e
          + 2 * archE (fun x => ψ x - f x) := by
      have i1 : IntegrableOn (fun u => 8 * archIntegrand (Av δ (Av δ e)) u) (Ioi 0) :=
        pAAe.arch.const_mul 8
      have i2 : IntegrableOn (fun u => 8 * archIntegrand (Av δ e) u) (Ioi 0) := pAe.arch.const_mul 8
      have i3 : IntegrableOn (fun u => 8 * archIntegrand e u) (Ioi 0) := pe.arch.const_mul 8
      have i4 : IntegrableOn (fun u => 2 * archIntegrand (fun x => ψ x - f x) u) (Ioi 0) :=
        pd.arch.const_mul 2
      have i12 : IntegrableOn (fun u => 8 * archIntegrand (Av δ (Av δ e)) u
          + 8 * archIntegrand (Av δ e) u) (Ioi 0) := by exact i1.add i2
      have i123 : IntegrableOn (fun u => 8 * archIntegrand (Av δ (Av δ e)) u
          + 8 * archIntegrand (Av δ e) u + 8 * archIntegrand e u) (Ioi 0) := by exact i12.add i3
      unfold archE
      rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
    rw [eint] at hle
    have c1 := archE_Av_le hδ pAe
    have c2 := archE_Av_le hδ pe
    have h5 : archE e < ε / 48 := hd2
    have h6 : archE (fun x => ψ x - f x) < ε / 4 := hl2
    unfold archE at hle c1 c2 h5 h6 ⊢
    linarith

/-! ## Theorem C -/

/-- **Theorem C, Green form.** A pole-free probe whose Green solution is in the ground space is
itself in the ground space. -/
theorem mem_of_green_mem {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : Probe a f) (hfp : poleR f a = 0)
    (hG : Gpole f a ∈ groundSpace a) : f ∈ groundSpace a :=
  mem_of_green_dense ha hf hfp hG (green_dense ha hf)

/-- **Theorem C (flat ⇒ degenerate), `H²` form.** If `h` is in the ground space and `H²`-flat at the
edges with `h'' = h₂` a probe, then `h₂` is in the ground space. -/
theorem theoremC {a : ℝ} (ha : 0 < a) {h h₁ h₂ : ℝ → ℝ} (hV : h ∈ groundSpace a)
    (hflat : FlatH2 a h h₁ h₂) : h₂ ∈ groundSpace a := by
  obtain ⟨hpole, hG⟩ := flat_green ha.le hflat
  set f : ℝ → ℝ := fun x => h₂ x - h x / 4
  have hf : Probe a f := by
    have := (probe_add_sub hflat.probe2 (probe_smul hV.1 (1 / 4))).2
    convert this using 1; funext x; simp only [f]; ring
  have hGV : Gpole f a ∈ groundSpace a := by
    have : Gpole f a = h := funext hG
    rw [this]; exact hV
  have hfV := mem_of_green_mem ha hf hpole hGV
  have := (groundSpace a).add_mem hfV ((groundSpace a).smul_mem (1 / 4) hV)
  convert this using 1; funext x; simp only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- **A nonzero `H²`-flat ground-space element forces degeneracy**: no ground state is simple. -/
theorem theoremC_not_simple {a : ℝ} (ha : 0 < a) {h h₁ h₂ : ℝ → ℝ} (hV : h ∈ groundSpace a)
    (hflat : FlatH2 a h h₁ h₂) (hpos : 0 < normSq h) (g : ℝ → ℝ) : ¬ SimpleGround a g := by
  intro hs
  obtain ⟨c₁, h1⟩ := hs.2 h hV
  obtain ⟨c₂, h2⟩ := hs.2 h₂ (theoremC ha hV hflat)
  have hc₁ : c₁ ≠ 0 := by
    rintro rfl
    have := normSq_congr_ae h1
    rw [this] at hpos
    simp [normSq] at hpos
  set c := c₂ / c₁
  have hae : h₂ =ᵐ[volume] fun t => c * h t := by
    filter_upwards [h1, h2] with t ht1 ht2
    rw [ht2, ht1]; simp only [c]; field_simp
  have hcont : Continuous fun t => c * h t := continuous_const.mul hflat.cont
  have hprim : ∀ x, h₁ x = ∫ y in (-a)..x, c * h y := by
    intro x
    rw [hflat.prim x]
    exact intervalIntegral.integral_congr_ae (hae.mono fun y hy _ => hy)
  have hd2 : ∀ x, HasDerivAt h₁ (c * h x) x := by
    intro x
    have := (hcont.integral_hasStrictDerivAt (-a) x).hasDerivAt
    have e : h₁ = fun x => ∫ y in (-a)..x, c * h y := funext hprim
    rw [e]; exact this
  have hC : C2Supp a h h₁ (fun t => c * h t) :=
    ⟨hflat.d1, hd2, hcont, hflat.supp, hflat.supp1, fun x hx => by rw [hflat.supp x hx, mul_zero]⟩
  have hz := eq_zero_of_deriv2_eq hC (fun t => rfl)
  have : normSq h = 0 := by unfold normSq; simp [hz]
  linarith

/-! ## The converse: Green solutions are `H²`-flat -/

section GreenFlat

variable {a : ℝ} {w : ℝ → ℝ}

/-- `∫_{−a}^x e^{−cs}(∫_{−a}^s w e^{cy} dy) ds = c⁻¹(∫_{−a}^x w − e^{−cx}∫_{−a}^x w e^{cy} dy)`. -/
theorem tri_exp (hw : MemLp w 2 volume) {c : ℝ} (hc : c ≠ 0) {x : ℝ} (hx : -a ≤ x) :
    (∫ s in (-a)..x, Real.exp (-c * s) * ∫ y in (-a)..s, w y * Real.exp (c * y))
      = c⁻¹ * ((∫ y in (-a)..x, w y) - Real.exp (-c * x) * ∫ y in (-a)..x, w y * Real.exp (c * y)) := by
  have hce : Continuous fun s => Real.exp (-c * s) := by fun_prop
  have hwi : ∀ α β, IntervalIntegrable w volume α β := memLp_intervalIntegrable hw
  have hwe : IntervalIntegrable (fun y => w y * Real.exp (c * y)) volume (-a) x :=
    (hwi _ _).mul_continuousOn (by fun_prop)
  rw [triangle_swap_int hx (e := fun s => Real.exp (-c * s)) (f := fun y => w y * Real.exp (c * y))
    (hce.integrableOn_Icc.mono_set Ioc_subset_Icc_self) hwe.1]
  have hin : ∀ y, (∫ s in y..x, Real.exp (-c * s)) = c⁻¹ * (Real.exp (-c * y) - Real.exp (-c * x)) := by
    intro y
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => -(c⁻¹ * Real.exp (-c * s)))
      (fun s _ => by
        have := (((hasDerivAt_id s).const_mul (-c)).exp).const_mul (-(c⁻¹))
        convert this using 1 <;> simp [id]; field_simp)
      (hce.intervalIntegrable _ _)]
    ring
  simp only [hin]
  have e1 : ∀ y, w y * Real.exp (c * y) * (c⁻¹ * (Real.exp (-c * y) - Real.exp (-c * x)))
      = c⁻¹ * w y - (c⁻¹ * Real.exp (-c * x)) * (w y * Real.exp (c * y)) := by
    intro y
    have : Real.exp (c * y) * Real.exp (-c * y) = 1 := by rw [← Real.exp_add]; simp
    linear_combination (c⁻¹ * w y) * this
  simp only [e1]
  rw [intervalIntegral.integral_sub ((hwi _ _).const_mul _) (hwe.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- The two pole primitives. -/
def I1 (w : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ y in (-a)..x, w y * Real.exp ((-1 / 2) * y)
def I2 (w : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ y in (-a)..x, w y * Real.exp ((1 / 2) * y)
/-- The derivative of the Green solution: `½(e^{x/2}I₁ + e^{−x/2}I₂) = ∫ cosh((x − y)/2) w`. -/
def G1 (w : ℝ → ℝ) (a x : ℝ) : ℝ :=
  (Real.exp (x / 2) * I1 w a x + Real.exp (-(x / 2)) * I2 w a x) / 2

theorem G1_continuous (hw : MemLp w 2 volume) : Continuous (G1 w a) := by
  have h1 : Continuous (I1 w a) := intervalIntegral.continuous_primitive
    (fun α β => (memLp_intervalIntegrable hw α β).mul_continuousOn (by fun_prop)) _
  have h2 : Continuous (I2 w a) := intervalIntegral.continuous_primitive
    (fun α β => (memLp_intervalIntegrable hw α β).mul_continuousOn (by fun_prop)) _
  unfold G1; fun_prop

/-- Left of the support every primitive from `−a` vanishes. -/
theorem prim_left (ha : 0 ≤ a) {φ : ℝ → ℝ} (hφ : ∀ y, a < |y| → φ y = 0) {x : ℝ} (hx : x < -a) :
    (∫ y in (-a)..x, φ y) = 0 := by
  refine intervalIntegral.integral_zero_ae ?_
  filter_upwards [ae_ne_pt (-a)] with y hy hyI
  rw [uIoc_of_ge hx.le] at hyI
  have hy1 : y < -a := lt_of_le_of_ne hyI.2 hy
  exact hφ y (by rw [abs_of_neg (by linarith)]; linarith)

theorem sq_half : ((-1 / 2 : ℝ)) ≠ 0 ∧ ((1 / 2 : ℝ)) ≠ 0 := ⟨by norm_num, by norm_num⟩

/-- `∫_{−a}^x G1 = G w` and `∫_{−a}^x G w = 2e^{x/2}I₁ + 2e^{−x/2}I₂ − 4∫w`. -/
theorem green_prims (hp : Probe a w) (ha : 0 ≤ a) (x : ℝ) :
    (∫ s in (-a)..x, G1 w a s) = Gpole w a x ∧
    (∫ s in (-a)..x, Gpole w a s)
      = 2 * Real.exp (x / 2) * I1 w a x + 2 * Real.exp (-(x / 2)) * I2 w a x
        - 4 * ∫ y in (-a)..x, w y := by
  have hw := hp.memL2
  rcases le_or_gt (-a) x with hx | hx
  · have t1 := tri_exp hw (c := -1 / 2) (by norm_num) hx
    have t2 := tri_exp hw (c := 1 / 2) (by norm_num) hx
    have c1 : Continuous fun s => Real.exp (s / 2) * I1 w a s := by
      have : Continuous (I1 w a) := intervalIntegral.continuous_primitive
        (fun α β => (memLp_intervalIntegrable hw α β).mul_continuousOn (by fun_prop)) _
      fun_prop
    have c2 : Continuous fun s => Real.exp (-(s / 2)) * I2 w a s := by
      have : Continuous (I2 w a) := intervalIntegral.continuous_primitive
        (fun α β => (memLp_intervalIntegrable hw α β).mul_continuousOn (by fun_prop)) _
      fun_prop
    have f1 : (∫ s in (-a)..x, Real.exp (s / 2) * I1 w a s)
        = ∫ s in (-a)..x, Real.exp (-(-1 / 2) * s) * ∫ y in (-a)..s, w y * Real.exp ((-1 / 2) * y) :=
      intervalIntegral.integral_congr fun s _ => by simp only [I1]; ring_nf
    have f2 : (∫ s in (-a)..x, Real.exp (-(s / 2)) * I2 w a s)
        = ∫ s in (-a)..x, Real.exp (-(1 / 2) * s) * ∫ y in (-a)..s, w y * Real.exp ((1 / 2) * y) :=
      intervalIntegral.integral_congr fun s _ => by simp only [I2]; ring_nf
    have eG := Gpole_eq_exp hw a x
    have ex1 : Real.exp (-(-1 / 2) * x) = Real.exp (x / 2) := by ring_nf
    have ex2 : Real.exp (-(1 / 2) * x) = Real.exp (-(x / 2)) := by ring_nf
    have hI1 : (∫ y in (-a)..x, w y * Real.exp ((-1 / 2) * y)) = I1 w a x := rfl
    have hI2 : (∫ y in (-a)..x, w y * Real.exp ((1 / 2) * y)) = I2 w a x := rfl
    constructor
    · unfold G1
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add (c1.intervalIntegrable _ _)
        (c2.intervalIntegrable _ _), f1, f2, t1, t2, eG, ex1, ex2, hI1, hI2]
      ring
    · have hG : ∀ s, Gpole w a s = Real.exp (s / 2) * I1 w a s - Real.exp (-(s / 2)) * I2 w a s :=
        fun s => Gpole_eq_exp hw a s
      simp only [hG]
      rw [intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
        f1, f2, t1, t2, ex1, ex2, hI1, hI2]
      ring
  · have z1 : I1 w a x = 0 := prim_left ha (fun y hy => by rw [hp.supp y hy, zero_mul]) hx
    have z2 : I2 w a x = 0 := prim_left ha (fun y hy => by rw [hp.supp y hy, zero_mul]) hx
    have zw : (∫ y in (-a)..x, w y) = 0 := prim_left ha hp.supp hx
    have hxa : a < |x| := by rw [abs_of_neg (by linarith)]; linarith
    have hG0 : Gpole w a x = 0 := by
      rw [Gpole_eq_exp hw a x]
      rw [show (∫ y in (-a)..x, w y * Real.exp ((-1 / 2) * y)) = I1 w a x from rfl,
        show (∫ y in (-a)..x, w y * Real.exp ((1 / 2) * y)) = I2 w a x from rfl, z1, z2]; ring
    have hG1z : ∀ s, s < -a → G1 w a s = 0 := by
      intro s hs
      have y1 : I1 w a s = 0 := prim_left ha (fun y hy => by rw [hp.supp y hy, zero_mul]) hs
      have y2 : I2 w a s = 0 := prim_left ha (fun y hy => by rw [hp.supp y hy, zero_mul]) hs
      unfold G1; rw [y1, y2]; ring
    have hGz : ∀ s, s < -a → Gpole w a s = 0 := by
      intro s hs
      rw [Gpole_eq_exp hw a s]
      have y1 : I1 w a s = 0 := prim_left ha (fun y hy => by rw [hp.supp y hy, zero_mul]) hs
      have y2 : I2 w a s = 0 := prim_left ha (fun y hy => by rw [hp.supp y hy, zero_mul]) hs
      rw [show (∫ y in (-a)..s, w y * Real.exp ((-1 / 2) * y)) = I1 w a s from rfl,
        show (∫ y in (-a)..s, w y * Real.exp ((1 / 2) * y)) = I2 w a s from rfl, y1, y2]; ring
    have i1 : (∫ s in (-a)..x, G1 w a s) = 0 := by
      refine intervalIntegral.integral_zero_ae ?_
      filter_upwards [ae_ne_pt (-a)] with y hy hyI
      rw [uIoc_of_ge hx.le] at hyI
      exact hG1z y (lt_of_le_of_ne hyI.2 hy)
    have i2 : (∫ s in (-a)..x, Gpole w a s) = 0 := by
      refine intervalIntegral.integral_zero_ae ?_
      filter_upwards [ae_ne_pt (-a)] with y hy hyI
      rw [uIoc_of_ge hx.le] at hyI
      exact hGz y (lt_of_le_of_ne hyI.2 hy)
    refine ⟨by rw [i1, hG0], ?_⟩
    rw [i2, z1, z2, zw]; ring

/-- **The Green solution of a pole-free probe is `H²`-flat**, with `(G w)'' = w + (G w)/4`. -/
theorem green_flat {a : ℝ} (ha : 0 ≤ a) {w : ℝ → ℝ} (hp : Probe a w) (hpole : poleR w a = 0) :
    FlatH2 a (Gpole w a) (G1 w a) (fun x => w x + Gpole w a x / 4) := by
  have hw := hp.memL2
  have hc := G1_continuous (a := a) hw
  have hGeq : Gpole w a = fun x => ∫ s in (-a)..x, G1 w a s :=
    funext fun x => (green_prims hp ha x).1.symm
  have hd : ∀ x, HasDerivAt (Gpole w a) (G1 w a x) x := by
    intro x; rw [hGeq]; exact (hc.integral_hasStrictDerivAt (-a) x).hasDerivAt
  have hsuppG := Gpole_supp hp hpole
  refine ⟨hd, fun x => ?_, hsuppG, fun x hx => ?_, ?_⟩
  · -- `G1 = ∫ (w + G/4)`
    rcases le_or_gt (-a) x with hx | hx
    · rw [intervalIntegral.integral_add (memLp_intervalIntegrable hw _ _)
        ((Gpole_continuous hw).intervalIntegrable _ _ |>.div_const 4),
        intervalIntegral.integral_div, (green_prims hp ha x).2]
      unfold G1; ring
    · have hG1z : G1 w a x = 0 := by
        have y1 : I1 w a x = 0 := prim_left ha (fun y hy => by rw [hp.supp y hy, zero_mul]) hx
        have y2 : I2 w a x = 0 := prim_left ha (fun y hy => by rw [hp.supp y hy, zero_mul]) hx
        unfold G1; rw [y1, y2]; ring
      rw [hG1z, prim_left ha (fun y hy => by rw [hp.supp y hy, hsuppG y hy]; ring) hx]
  · -- outside `[−a, a]` the derivative of the zero function is zero
    have hloc : (Gpole w a) =ᶠ[𝓝 x] fun _ => 0 := by
      have hopen : IsOpen {y : ℝ | a < |y|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds hx] with y hy using hsuppG y hy
    exact (hd x).unique ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hloc)
  · have := (probe_add_sub hp (probe_smul (Gpole_probe hp ha hpole) (1 / 4))).1
    convert this using 1; funext x; ring

end GreenFlat

/-- **Round 48's corollary, formal in `H²` form: the ground state is simple iff no nonzero
ground-space element is `H²`-flat at the edges.** -/
theorem simple_iff_no_flat {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g) :
    SimpleGround a g ↔
      ∀ h h₁ h₂, h ∈ groundSpace a → FlatH2 a h h₁ h₂ → normSq h = 0 := by
  constructor
  · intro hs h h₁ h₂ hV hflat
    rcases (normSq_nonneg h).lt_or_eq with hpos | h0
    · exact absurd hs (theoremC_not_simple ha hV hflat hpos g)
    · exact h0.symm
  · intro H
    by_contra hns
    obtain ⟨w, hwV, hwp, hwpos, hGV⟩ := degenerate_flat ha hg hns
    have h0 := H _ _ _ hGV (green_flat ha.le hwV.1 hwp)
    -- then `Ĝw ≡ 0` on the real line, so `ŵ ≡ 0` there: impossible
    obtain ⟨α, ε, hα, hε, hne⟩ := exists_interval_ghat ha hwV.1 hwpos
    set t := α + ε / 2
    have ht : t ∈ Ioo α (α + ε) := ⟨by simp only [t]; linarith, by simp only [t]; linarith⟩
    have hq : (0 : ℝ) < t ^ 2 + 1 / 4 := by positivity
    have hz : ((t : ℂ)) ^ 2 ≠ (Complex.I / 2) ^ 2 := by
      intro e
      have h0' : (((t ^ 2 + 1 / 4 : ℝ)) : ℂ) = 0 := by rw [← den_ne, e, sub_self]
      rw [Complex.ofReal_eq_zero] at h0'; linarith
    have hh := Gpole_hat hwV.1 ha.le hwp hz
    have hzero : (∫ x in (-a)..a, ((Gpole w a x : ℝ) : ℂ) * Complex.exp (Complex.I * t * x)) = 0 := by
      rw [show (∫ x in (-a)..a, ((Gpole w a x : ℝ) : ℂ) * Complex.exp (Complex.I * t * x))
        = ghatC (Gpole w a) a t from rfl, ghatC_congr_ae (ae_zero_of_normSq (Gpole_memLp hwV.1 hwp) h0)]
      simp [ghatC]
    rw [hzero, den_ne] at hh
    have hq' : (((t ^ 2 + 1 / 4 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have : ghatC w a t = 0 := by
      have := neg_eq_zero.1 hh.symm
      exact (div_eq_zero_iff.1 this).resolve_right hq'
    exact hne t ht this

end Pilot1ca


#print axioms Pilot1ca.mem_of_green_dense
#print axioms Pilot1ca.flat_green
#print axioms Pilot1ca.green_dense
#print axioms Pilot1ca.mem_of_green_mem
#print axioms Pilot1ca.theoremC
#print axioms Pilot1ca.theoremC_not_simple
#print axioms Pilot1ca.green_flat
#print axioms Pilot1ca.simple_iff_no_flat
