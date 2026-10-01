import DHHurwitzEM
import DHRealAxis

/-!
# A zero of `dh` within `1/100` of `c = 1617/2000 + (856993/10000) i`: the certificate skeleton

Stage 2 of the zero-location certificate. Target (`dh_zero_near_of_numerics` and its corollaries):
`∃ ρ, dh ρ = 0 ∧ ‖ρ − c‖ < 1/100`, `c = cLoc`, near the zero `ρ ≈ 0.808517182 + 85.699348485 i`.

**Route.** Minimum modulus (`exists_zero_of_center_lt_sphere`) for `f = dh` against the Euler–Maclaurin
approximant `P = dhEM 20 12` (`DHHurwitzEM`), linearised at `c` by two mean value inequalities on the
ball (`norm_sub_linear_le_ball`: `‖P z − P c − P′(c)(z − c)‖ ≤ M₂ r ‖z − c‖`, re-proved for `P`
differentiable only on the ball, since `dhEM` has a pole at `1`): `2(p₀ + e₀) < a₀ r − m₂ r²` gives the
zero (`exists_zero_of_bounds`).

**Decomposition** (`dhEM_eq`): `dhEM M K = a(1)·fEM M K`, `fEM = DEM + GEM`, with `u = 1, κ, −κ, −1`,
`DEM M s = Σ_{m<M} Σ_j u(j)(5m+j)^{-s}` (the Dirichlet polynomial over `n < 5M`) and
`GEM M K s = Σ_j u(j)(5M+j)^{-s} Q_{M+j/5}(s)`,
`Q_x(s) = x/(s−1) + 1/2 + Σ_{k<K} B_{2k+2}/(2k+2)! · s(s+1)⋯(s+2k)/x^{2k+1}` (`QEM`; for `K = 12` with
rational coefficients in `QEM_twelve`; `5^{-s} EM(j/5) = Σ_m (5m+j)^{-s} + (100+j)^{-s} Q` is
`EMmain_explicit`; `B₂, …, B₂₄` are `bernoulli_vals`, by Mathlib's recursion for `bernoulli'`).

**The second-derivative bound: termwise for `DEM`, Cauchy for `GEM`.** `(n^{-s})″ = log²n·n^{-s}`
gives `‖DEM″‖ ≤ D2sum(1597/2000, 20) ≤ 36` (true value 34.003; `D2sum_le`), and Cauchy's estimate
on circles of radius `2/5` with the termwise sup `‖GEM‖ ≤ 53/100` on `closedBall c (41/100)`
(`Gsup_ball_le`; true sup ≈ 0.52) gives `‖GEM″‖ ≤ 53/8` (`norm_deriv2_GEM_ball`). Why this split:
a Cauchy estimate for all of `fEM` needs a sup of `|DEM|` on a disc, and the only elementary sup is
termwise, `Σ |u(n)| n^{−Re}`, which makes `2·sup/R² ≥ 142` for every radius (`R = 0.6` is best),
above the admissible `m₂ < 124`; a termwise bound for `GEM″` needs `(s)_n″` bounds and would save
about 5 of a slack of ~80. The termwise `D2sum` is far above the true `sup ‖fEM″‖ ≈ 0.75`, but the
margin absorbs it: `m₂ r² = 4.26·10⁻³` against `|fEM′(c)| r = 1.256·10⁻²`.

**Proved numeric inputs.** Euler–Maclaurin error on the ball `‖dh − dhEM 20 12‖ ≤ ‖a(1)‖·16·10⁻⁶
≤ 6·10⁻⁵` (`norm_dh_sub_dhEM_le_ball`, `norm_dh_sub_dhEM_le_ball'`; true bound 1.482·10⁻⁵ per unit
of `a(1)`), from the box `1597/2000 ≤ Re ≤ 1637/2000`, `|Im| ≤ 857093/10000`, `B = 34·10⁴⁵`
(`prod_box_eq`: `Π_{i<24}((1637/2000 + i)² + (857093/10000)²) = 1.15358…·10⁹³` exactly, `prod_box_le`),
`5^{−1597/2000} ≤ 0.2805` (`five_rpow_le`), `(20 + j/5)^{−47597/2000} ≤ 8.8246, 6.9807, 5.5348, 4.3982
·10⁻³²` (`x1_rpow_le` … `x4_rpow_le`), `(π²/3)/(2π)²⁴ ≤ 1/(3·2²⁴·3.141592²²)` (`pi_const_le`),
`‖a(1)‖ = ‖a(4)‖ ≤ 3.7014`, `‖a(2)‖ = ‖a(3)‖ = κ‖a(1)‖ ≤ 1.0515` (`norm_aDH_le`), `κ ≤ 0.28408`.
Second derivative `‖dhEM″‖ ≤ ‖a(1)‖(36 + 53/8) ≤ 158` on the ball (`norm_deriv2_dhEM_ball`).
Exact Gaussian rationals `Q_{20+j/5}(c)`, `Q′_{20+j/5}(c)` (`QEM_cLoc_j`, `QEMd_cLoc_j`, through
`poch_cLoc_n`, `pochD_cLoc_n`).

**Theorem ladder.** `dh_zero_near_of_numerics` (five hypotheses, `dh` units) →
`dh_zero_near_of_dhEM` (`hM2`, `hE` discharged) → `dh_zero_near_of_fEM` (normalised) →
`dh_zero_near_of_elementary` (Re/Im split, `fEM_cLoc_re`, `fEM_cLoc_im`, `fEMd_cLoc_re`) →
`dh_zero_near_of_center` (`D2sum` discharged) → `dh_zero_near_of_center'` (fixed tolerances).

## Open numeric hypotheses (for the stage-3 generator)

```
OPEN-NUMERICS-BEGIN
target   PsiOmega.Locate.dh_zero_near_of_center'
H1       |PRe 20 12| ≤ 1/1000     unfold: PRe_20   value -3.2265086264189e-5   slack 9.677e-4
H2       |PIm 20 12| ≤ 1/1000     unfold: PIm_20   value -5.4359577231286e-5   slack 9.456e-4
H3       1 ≤ ARe 20 12            unfold: ARe_20   value  1.2323333731546      slack 0.2323
general  PsiOmega.Locate.dh_zero_near_of_center {pr pi ar : ℝ}
           (hPr : |PRe 20 12| ≤ pr) (hPi : |PIm 20 12| ≤ pi) (hAr : ar ≤ |ARe 20 12|)
           (hmargin : 2 * (pr + pi + 16 / 10 ^ 6) < ar / 100 - (36 + 53 / 8) / 10 ^ 4)
         i.e. pr + pi < ar/200 - 0.00214725  (with ar = 1.2323: pr + pi < 0.004014)
atoms    ex (1617/2000) n  = Real.exp (-(1617 / 2000 * Real.log n))   n ∈ NS   (≤ 1)
         cC n              = Real.cos (856993 / 10000 * Real.log n)    n ∈ NS
         sC n              = Real.sin (856993 / 10000 * Real.log n)    n ∈ NS
         Real.log n                                                    n ∈ NS   (H3 only)
         kappa             = 2 sin(π/5)/(√5 + 2 sin(2π/5))             (PsiOmega.kappa_bounds, 15 digits)
NS       {5m + j | m ∈ [0, 20), j ∈ {1, 2, 3, 4}} ∪ {101, 102, 103, 104}   (84 values; n = 1 trivial)
angles   856993/10000 · log n ∈ [0, 398.03]; log n for 2 ≤ n ≤ 121: PsiOmega.Num.log_bound_n
rationals  the Q-values are literals inside PRe_20 / PIm_20 / ARe_20 (|Re Q_j| < 0.54,
           |Im Q_j| < 0.31, |Q′_j| < 0.017); no further transcendental input
weights  H1, H2: Σ_{n ∈ NS} |u(n)| = 42 + 42κ ≈ 53.9, so an absolute error ≤ 1e-5 in each term
           (e_n C_n, e_n S_n, and each of the four Q-terms) keeps the total below 5.4e-4 < slack;
         H3: an absolute error ≤ 1e-3 in each term keeps the total below 0.054 < slack
         (Σ_{n ∈ NS} |u(n)| log n · e_n ≈ 10.2, Σ |u(n)| e_n ≈ 4.49)
OPEN-NUMERICS-END
```
-/

open Complex Metric
open scoped Nat

noncomputable section

namespace PsiOmega

namespace Locate

/-! ## 1. The minimum-modulus instrument -/

/-- If `‖f c‖ < ‖f z‖` on the whole sphere, `f` has a zero in the open ball. -/
theorem exists_zero_of_center_lt_sphere {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall c r))
    (hlt : ∀ z ∈ sphere c r, ‖f c‖ < ‖f z‖) : ∃ z ∈ ball c r, f z = 0 := by
  by_contra hno
  push Not at hno
  have hnz : ∀ z ∈ closedBall c r, f z ≠ 0 := by
    intro z hz
    rcases (mem_closedBall.1 hz).lt_or_eq with h | h
    · exact hno z (mem_ball.2 h)
    · have hz' : z ∈ sphere c r := mem_sphere.2 h
      intro h0; have := hlt z hz'; rw [h0, norm_zero] at this
      exact absurd this (not_lt.2 (norm_nonneg _))
  have hne : (sphere c r).Nonempty := ⟨c + r, by simp [abs_of_pos hr]⟩
  have hcont : ContinuousOn (fun z => ‖(f z)⁻¹‖) (sphere c r) :=
    ((hf.continuousOn.mono sphere_subset_closedBall).inv₀
      (fun z hz => hnz z (sphere_subset_closedBall hz))).norm
  obtain ⟨w, hwS, hwmax⟩ := (isCompact_sphere c r).exists_isMaxOn hne hcont
  have hdiff : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hr.ne']
    exact hf.inv hnz
  have hbound : ∀ z ∈ frontier (ball c r), ‖(f z)⁻¹‖ ≤ ‖(f w)⁻¹‖ := by
    intro z hz
    rw [frontier_ball c hr.ne'] at hz
    exact hwmax hz
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff hbound
    (subset_closure (mem_ball_self hr))
  have hc0 : f c ≠ 0 := hnz c (mem_closedBall_self hr.le)
  have hw0 : f w ≠ 0 := hnz w (sphere_subset_closedBall hwS)
  have hlt' := hlt w hwS
  rw [norm_inv, norm_inv] at hmax
  have := (inv_le_inv₀ (norm_pos_iff.2 hc0) (norm_pos_iff.2 hw0)).1 hmax
  linarith

/-- **Localisation in approximant form.** `‖f − P‖ ≤ E` on the closed ball, `P` within `M r²` of
its linearisation `P c + A (z − c)` on the sphere, and `‖A‖ r − M r² > 2(‖P c‖ + E)`: then `f` has
a zero within `r` of `c`. -/
theorem exists_zero_of_approx {f P : ℂ → ℂ} {c A : ℂ} {r E M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall c r))
    (hR : ∀ z ∈ closedBall c r, ‖f z - P z‖ ≤ E)
    (hlin : ∀ z ∈ sphere c r, ‖P z - P c - A * (z - c)‖ ≤ M * r ^ 2)
    (hmargin : 2 * (‖P c‖ + E) < ‖A‖ * r - M * r ^ 2) : ∃ z ∈ ball c r, f z = 0 := by
  refine exists_zero_of_center_lt_sphere hr hf fun z hz => ?_
  have hzc : ‖z - c‖ = r := mem_sphere_iff_norm.1 hz
  have h1 : ‖f c‖ ≤ ‖P c‖ + E := by
    have := hR c (mem_closedBall_self hr.le)
    calc ‖f c‖ = ‖P c + (f c - P c)‖ := by ring_nf
      _ ≤ ‖P c‖ + ‖f c - P c‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have h2 : ‖A‖ * r - ‖P c‖ - M * r ^ 2 - E ≤ ‖f z‖ := by
    have hRz := hR z (sphere_subset_closedBall hz)
    have hl := hlin z hz
    have hA : ‖A * (z - c)‖ = ‖A‖ * r := by rw [norm_mul, hzc]
    have key : A * (z - c) = f z - (f z - P z) - (P z - P c - A * (z - c)) - P c := by ring
    have : ‖A * (z - c)‖ ≤ ‖f z‖ + ‖f z - P z‖ + ‖P z - P c - A * (z - c)‖ + ‖P c‖ := by
      calc ‖A * (z - c)‖ = ‖f z - (f z - P z) - (P z - P c - A * (z - c)) - P c‖ :=
            congrArg norm key
        _ ≤ ‖f z - (f z - P z) - (P z - P c - A * (z - c))‖ + ‖P c‖ := norm_sub_le _ _
        _ ≤ ‖f z - (f z - P z)‖ + ‖P z - P c - A * (z - c)‖ + ‖P c‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ ‖f z‖ + ‖f z - P z‖ + ‖P z - P c - A * (z - c)‖ + ‖P c‖ := by
            gcongr; exact norm_sub_le _ _
    linarith
  linarith

/-- **The linearisation bound on a ball** (two mean value inequalities): if `P` and `P′` are
differentiable on `closedBall c r` and `‖P″‖ ≤ M₂` there, then
`‖P z − P c − P′(c)(z − c)‖ ≤ M₂ r ‖z − c‖` on the ball. -/
theorem norm_sub_linear_le_ball {P : ℂ → ℂ} {c : ℂ} {r M₂ : ℝ}
    (hP : ∀ w ∈ closedBall c r, DifferentiableAt ℂ P w)
    (hP' : ∀ w ∈ closedBall c r, DifferentiableAt ℂ (deriv P) w)
    (hM : ∀ w ∈ closedBall c r, ‖deriv (deriv P) w‖ ≤ M₂) {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖P z - P c - deriv P c * (z - c)‖ ≤ M₂ * r * ‖z - c‖ := by
  have hc : c ∈ closedBall c r := mem_closedBall_self (dist_nonneg.trans hz)
  have hM0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM c hc)
  have h1 : ∀ w ∈ closedBall c r, ‖deriv P w - deriv P c‖ ≤ M₂ * r := by
    intro w hw
    have := (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le hP' hM hc hw
    refine this.trans ?_
    rw [← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (mem_closedBall'.1 hw |>.trans_eq' (dist_comm _ _)) hM0
  have hg : ∀ w ∈ closedBall c r,
      HasDerivAt (fun w => P w - deriv P c * w) (deriv P w - deriv P c) w := fun w hw => by
    have h1 := (hP w hw).hasDerivAt
    have h2 := (hasDerivAt_id w).const_mul (deriv P c)
    simp only [id, mul_one] at h2
    exact h1.fun_sub h2
  have hgd : ∀ w ∈ closedBall c r, ‖deriv (fun w => P w - deriv P c * w) w‖ ≤ M₂ * r :=
    fun w hw => by rw [(hg w hw).deriv]; exact h1 w hw
  have := (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hg x hx).differentiableAt) hgd hc hz
  have e : (P z - deriv P c * z) - (P c - deriv P c * c) = P z - P c - deriv P c * (z - c) := by
    ring
  rw [e] at this
  exact this

/-- **The skeleton, abstract form.** `f` differentiable on `closedBall c r`, `P` twice
differentiable there, with `‖P c‖ ≤ p₀`, `a₀ ≤ ‖P′(c)‖`, `‖P″‖ ≤ m₂` and `‖f − P‖ ≤ e₀` on the
ball, and the margin `2(p₀ + e₀) < a₀ r − m₂ r²`: `f` has a zero in the open ball. -/
theorem exists_zero_of_bounds {f P : ℂ → ℂ} {c : ℂ} {r p₀ a₀ m₂ e₀ : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall c r))
    (hPd : ∀ w ∈ closedBall c r, DifferentiableAt ℂ P w)
    (hPd' : ∀ w ∈ closedBall c r, DifferentiableAt ℂ (deriv P) w)
    (hP : ‖P c‖ ≤ p₀) (hA : a₀ ≤ ‖deriv P c‖)
    (hM2 : ∀ z ∈ closedBall c r, ‖deriv (deriv P) z‖ ≤ m₂)
    (hE : ∀ z ∈ closedBall c r, ‖f z - P z‖ ≤ e₀)
    (hmargin : 2 * (p₀ + e₀) < a₀ * r - m₂ * r ^ 2) : ∃ z ∈ ball c r, f z = 0 := by
  refine exists_zero_of_approx (A := deriv P c) (M := m₂) hr hf hE (fun z hz => ?_) ?_
  · have hz' := sphere_subset_closedBall hz
    have h := norm_sub_linear_le_ball hPd hPd' hM2 hz'
    rw [mem_sphere_iff_norm.1 hz] at h
    linarith
  · have : a₀ * r ≤ ‖deriv P c‖ * r := mul_le_mul_of_nonneg_right hA hr.le
    linarith

/-! ## 2. The approximant, decomposed -/

/-- `n^{-s}`. -/
def nps (n : ℕ) (s : ℂ) : ℂ := (n : ℂ) ^ (-s)

/-- The Euler–Maclaurin tail factor at `x = M + j/5`:
`Q_x(s) = x/(s−1) + 1/2 + Σ_{k<K} B_{2k+2}/(2k+2)! · s(s+1)⋯(s+2k) / x^{2k+1}`
(so that `5^{-s} T(s, K, x) = (5x)^{-s} Q_x(s)`, `five_cpow_mul_T`). -/
def QEM (K : ℕ) (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) / (s - 1) + 1 / 2 +
    ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) *
      HurwitzEM.poch s (2 * k + 1) / (x : ℂ) ^ (2 * k + 1)

/-- The Dirichlet-polynomial part of `dhEM M K / a(1)`:
`Σ_{m<M} ((5m+1)^{-s} + κ(5m+2)^{-s} − κ(5m+3)^{-s} − (5m+4)^{-s})`. -/
def DEM (M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, (nps (5 * m + 1) s + (kappa : ℂ) * nps (5 * m + 2) s
    - (kappa : ℂ) * nps (5 * m + 3) s - nps (5 * m + 4) s)

/-- The tail part of `dhEM M K / a(1)`:
`Σ_j u(j) (5M+j)^{-s} Q_{M+j/5}(s)`, `u = 1, κ, −κ, −1`. -/
def GEM (M K : ℕ) (s : ℂ) : ℂ :=
  nps (5 * M + 1) s * QEM K (M + 1 / 5) s + (kappa : ℂ) * (nps (5 * M + 2) s * QEM K (M + 2 / 5) s)
    - (kappa : ℂ) * (nps (5 * M + 3) s * QEM K (M + 3 / 5) s)
    - nps (5 * M + 4) s * QEM K (M + 4 / 5) s

/-- `dhEM M K / a(1)`. -/
def fEM (M K : ℕ) (s : ℂ) : ℂ := DEM M s + GEM M K s

theorem five_cpow_mul (y : ℝ) (hy : 0 ≤ y) (s : ℂ) :
    (5 : ℂ) ^ (-s) * (y : ℂ) ^ (-s) = ((5 * y : ℝ) : ℂ) ^ (-s) := by
  rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) hy]
  norm_num

theorem five_cpow_mul_T (t : ℝ) (ht : 0 < t) (s : ℂ) (K : ℕ) :
    (5 : ℂ) ^ (-s) * HurwitzEM.T s K t = ((5 * t : ℝ) : ℂ) ^ (-s) * QEM K t s := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  have h1 : (t : ℂ) ^ (1 - s) = t * (t : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ ht', cpow_one]
  have h2 : ∀ k : ℕ, (t : ℂ) ^ (-s - (2 * k + 1)) = (t : ℂ) ^ (-s) / (t : ℂ) ^ (2 * k + 1) := by
    intro k
    rw [cpow_sub _ _ ht']
    have : ((2 * k + 1 : ℕ) : ℂ) = 2 * (k : ℂ) + 1 := by push_cast; ring
    rw [← this, cpow_natCast]
  rw [← five_cpow_mul t ht.le]
  unfold HurwitzEM.T QEM
  rw [h1, Finset.sum_congr rfl (fun k _ => by rw [h2 k])]
  have hs : ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) *
        HurwitzEM.poch s (2 * k + 1) * ((t : ℂ) ^ (-s) / (t : ℂ) ^ (2 * k + 1)) =
      (t : ℂ) ^ (-s) * ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) *
        HurwitzEM.poch s (2 * k + 1) / (t : ℂ) ^ (2 * k + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hs]
  ring

/-- `5^{-s} EM(j/5) = Σ_{m<M} (5m+j)^{-s} + (5M+j)^{-s} Q_{M+j/5}(s)`. -/
theorem five_cpow_mul_EMmain (M K : ℕ) {j : ℕ} (hj : 1 ≤ j) (s : ℂ) :
    (5 : ℂ) ^ (-s) * HurwitzEM.EMmain ((j : ℝ) / 5) M K s =
      ∑ m ∈ Finset.range M, nps (5 * m + j) s + nps (5 * M + j) s * QEM K (M + (j : ℝ) / 5) s := by
  unfold HurwitzEM.EMmain
  rw [mul_add, Finset.mul_sum]
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht : 0 < (M : ℝ) + (j : ℝ) / 5 := by positivity
  congr 1
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [five_cpow_mul _ (by positivity), nps]
    congr 2
    push_cast; ring
  · rw [five_cpow_mul_T _ ht, nps]
    congr 2
    push_cast; ring

theorem uval_one : uval 1 = 1 := by simp [uval]
theorem uval_two : uval 2 = kappa := by simp [uval]
theorem uval_three : uval 3 = -kappa := by simp [uval]
theorem uval_four : uval 4 = -1 := by simp [uval]

/-- **The approximant, normalised**: `dhEM M K s = a(1) · (DEM M s + GEM M K s)`. -/
theorem dhEM_eq (M K : ℕ) (s : ℂ) : dhEM M K s = aDH chi5 1 * fEM M K s := by
  have h2 : aDH chi5 2 = aDH chi5 1 * (kappa : ℂ) := by
    rw [aDH_chi5_eq_mul]; norm_num [uval_two]
  have h3 : aDH chi5 3 = aDH chi5 1 * (-(kappa : ℂ)) := by
    rw [aDH_chi5_eq_mul]; norm_num [uval_three]
  have h4 : aDH chi5 4 = aDH chi5 1 * (-1) := by
    rw [aDH_chi5_eq_mul]; norm_num [uval_four]
  unfold dhEM
  rw [h2, h3, h4]
  have e : ∀ j : ℕ, 1 ≤ j → (5 : ℂ) ^ (-s) * HurwitzEM.EMmain (((j : ℕ) : ℝ) / 5) M K s =
      ∑ m ∈ Finset.range M, nps (5 * m + j) s + nps (5 * M + j) s * QEM K (M + (j : ℝ) / 5) s :=
    fun j hj => five_cpow_mul_EMmain M K hj s
  have key : (5 : ℂ) ^ (-s) *
      (aDH chi5 1 * HurwitzEM.EMmain (((1 : ℕ) : ℝ) / 5) M K s +
        aDH chi5 1 * (kappa : ℂ) * HurwitzEM.EMmain (((2 : ℕ) : ℝ) / 5) M K s +
        aDH chi5 1 * (-(kappa : ℂ)) * HurwitzEM.EMmain (((3 : ℕ) : ℝ) / 5) M K s +
        aDH chi5 1 * (-1) * HurwitzEM.EMmain (((4 : ℕ) : ℝ) / 5) M K s) =
      aDH chi5 1 * ((5 : ℂ) ^ (-s) * HurwitzEM.EMmain (((1 : ℕ) : ℝ) / 5) M K s +
        (kappa : ℂ) * ((5 : ℂ) ^ (-s) * HurwitzEM.EMmain (((2 : ℕ) : ℝ) / 5) M K s) -
        (kappa : ℂ) * ((5 : ℂ) ^ (-s) * HurwitzEM.EMmain (((3 : ℕ) : ℝ) / 5) M K s) -
        (5 : ℂ) ^ (-s) * HurwitzEM.EMmain (((4 : ℕ) : ℝ) / 5) M K s) := by ring
  rw [key, e 1 le_rfl, e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num)]
  congr 1
  unfold fEM DEM GEM
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  push_cast
  ring

/-! ## 3. Derivatives -/

/-- `(−log n)^k n^{-s}`, the `k`-th derivative of `n^{-s}`. -/
def npsD (k n : ℕ) (s : ℂ) : ℂ := (-(Real.log n : ℂ)) ^ k * (n : ℂ) ^ (-s)

theorem nps_eq_npsD (n : ℕ) : nps n = npsD 0 n := by
  funext s; simp [nps, npsD]

theorem hasDerivAt_npsD (k : ℕ) {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    HasDerivAt (npsD k n) (npsD (k + 1) n s) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h : HasDerivAt (fun x : ℂ => (n : ℂ) ^ (-x)) ((n : ℂ) ^ (-s) * Complex.log n * (-1)) s :=
    ((hasDerivAt_id' s).fun_neg).const_cpow (c := (n : ℂ)) (Or.inl hn0)
  have h2 := h.const_mul ((-(Real.log n : ℂ)) ^ k)
  have hf : npsD k n = fun y => (-(Real.log n : ℂ)) ^ k * (n : ℂ) ^ (-y) := rfl
  rw [hf]
  convert h2 using 1
  simp only [npsD, natCast_log]
  ring

/-- The `k`-th derivative of `DEM M`. -/
def DEMk (k M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, (npsD k (5 * m + 1) s + (kappa : ℂ) * npsD k (5 * m + 2) s
    - (kappa : ℂ) * npsD k (5 * m + 3) s - npsD k (5 * m + 4) s)

theorem DEM_eq_DEMk (M : ℕ) : DEM M = DEMk 0 M := by
  funext s; simp only [DEM, DEMk, nps_eq_npsD]

theorem hasDerivAt_DEMk (k M : ℕ) (s : ℂ) : HasDerivAt (DEMk k M) (DEMk (k + 1) M s) s := by
  have hf : DEMk k M = fun s => ∑ m ∈ Finset.range M, (npsD k (5 * m + 1) s +
      (kappa : ℂ) * npsD k (5 * m + 2) s - (kappa : ℂ) * npsD k (5 * m + 3) s -
      npsD k (5 * m + 4) s) := rfl
  rw [hf, DEMk]
  apply HasDerivAt.fun_sum
  intro m _
  exact ((((hasDerivAt_npsD k (by omega) s).add
    ((hasDerivAt_npsD k (by omega) s).const_mul _)).sub
    ((hasDerivAt_npsD k (by omega) s).const_mul _)).sub (hasDerivAt_npsD k (by omega) s))

theorem deriv_DEMk (k M : ℕ) : deriv (DEMk k M) = DEMk (k + 1) M := by
  funext s; exact (hasDerivAt_DEMk k M s).deriv

/-- The derivative of the rising factorial, `d/ds (s)_n`. -/
def pochD (s : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => pochD s n * (s + n) + HurwitzEM.poch s n

theorem hasDerivAt_poch (n : ℕ) (s : ℂ) :
    HasDerivAt (fun s => HurwitzEM.poch s n) (pochD s n) s := by
  induction n with
  | zero =>
    simp only [HurwitzEM.poch, Finset.range_zero, Finset.prod_empty, pochD]
    exact hasDerivAt_const _ _
  | succ n ih =>
    have hf : (fun s => HurwitzEM.poch s (n + 1)) = fun s => HurwitzEM.poch s n * (s + n) := by
      funext s; exact HurwitzEM.poch_succ s n
    rw [hf]
    convert ih.fun_mul ((hasDerivAt_id' s).add_const (n : ℂ)) using 1
    simp only [pochD, mul_one]

/-- The derivative of `Q_x`. -/
def QEMd (K : ℕ) (x : ℝ) (s : ℂ) : ℂ :=
  -(x : ℂ) / (s - 1) ^ 2 +
    ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) *
      pochD s (2 * k + 1) / (x : ℂ) ^ (2 * k + 1)

theorem hasDerivAt_QEM (K : ℕ) (x : ℝ) {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt (QEM K x) (QEMd K x s) s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  have h1 : HasDerivAt (fun s : ℂ => (x : ℂ) / (s - 1)) (-(x : ℂ) / (s - 1) ^ 2) s := by
    have := (hasDerivAt_const s (x : ℂ)).fun_div ((hasDerivAt_id' s).sub_const 1) hs1
    convert this using 1
    ring
  have h2 : HasDerivAt (fun s => ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) /
      ((2 * k + 2)! : ℂ) * HurwitzEM.poch s (2 * k + 1) / (x : ℂ) ^ (2 * k + 1))
      (∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) *
        pochD s (2 * k + 1) / (x : ℂ) ^ (2 * k + 1)) s := by
    apply HasDerivAt.fun_sum
    intro k _
    exact ((hasDerivAt_poch (2 * k + 1) s).const_mul _).div_const _
  have := (h1.add_const (1 / 2 : ℂ)).add h2
  exact this

/-- The derivative of `GEM M K`. -/
def GEMd (M K : ℕ) (s : ℂ) : ℂ :=
  (npsD 1 (5 * M + 1) s * QEM K (M + 1 / 5) s + nps (5 * M + 1) s * QEMd K (M + 1 / 5) s) +
    (kappa : ℂ) * (npsD 1 (5 * M + 2) s * QEM K (M + 2 / 5) s +
      nps (5 * M + 2) s * QEMd K (M + 2 / 5) s) -
    (kappa : ℂ) * (npsD 1 (5 * M + 3) s * QEM K (M + 3 / 5) s +
      nps (5 * M + 3) s * QEMd K (M + 3 / 5) s) -
    (npsD 1 (5 * M + 4) s * QEM K (M + 4 / 5) s + nps (5 * M + 4) s * QEMd K (M + 4 / 5) s)

theorem hasDerivAt_npsQ (M K j : ℕ) (hj : 1 ≤ j) (x : ℝ) {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt (fun s => nps (5 * M + j) s * QEM K x s)
      (npsD 1 (5 * M + j) s * QEM K x s + nps (5 * M + j) s * QEMd K x s) s := by
  have h1 := hasDerivAt_npsD 0 (n := 5 * M + j) (by omega) s
  rw [← nps_eq_npsD] at h1
  exact h1.mul (hasDerivAt_QEM K x hs)

theorem hasDerivAt_GEM (M K : ℕ) {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt (GEM M K) (GEMd M K s) s := by
  have hf : GEM M K = fun s => nps (5 * M + 1) s * QEM K (M + 1 / 5) s +
      (kappa : ℂ) * (nps (5 * M + 2) s * QEM K (M + 2 / 5) s)
      - (kappa : ℂ) * (nps (5 * M + 3) s * QEM K (M + 3 / 5) s)
      - nps (5 * M + 4) s * QEM K (M + 4 / 5) s := rfl
  rw [hf]
  exact (((hasDerivAt_npsQ M K 1 le_rfl _ hs).add
    ((hasDerivAt_npsQ M K 2 (by norm_num) _ hs).const_mul _)).sub
    ((hasDerivAt_npsQ M K 3 (by norm_num) _ hs).const_mul _)).sub
    (hasDerivAt_npsQ M K 4 (by norm_num) _ hs)

theorem differentiableOn_GEM (M K : ℕ) : DifferentiableOn ℂ (GEM M K) {s | s ≠ 1} :=
  fun _ hs => (hasDerivAt_GEM M K hs).differentiableAt.differentiableWithinAt

theorem hasDerivAt_fEM (M K : ℕ) {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt (fEM M K) (DEMk 1 M s + GEMd M K s) s := by
  have hf : fEM M K = fun s => DEMk 0 M s + GEM M K s := by
    funext s; simp [fEM, DEM_eq_DEMk]
  rw [hf]
  exact (hasDerivAt_DEMk 0 M s).add (hasDerivAt_GEM M K hs)

/-! ## 4. Bounds on the closed ball -/

/-- `n^{-σ}`, written `exp(−σ log n)`. -/
def ex (σ : ℝ) (n : ℕ) : ℝ := Real.exp (-(σ * Real.log n))

theorem norm_nps_le {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} {w : ℂ} (hw : σ ≤ w.re) :
    ‖nps n w‖ ≤ ex σ n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e : -(σ * Real.log n) = Real.log n * (-σ) := by ring
  rw [nps, norm_natCast_cpow_of_pos (by omega), ex, e, ← Real.rpow_def_of_pos (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hn' (by simp; linarith)

theorem norm_npsD_le (k : ℕ) {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} {w : ℂ} (hw : σ ≤ w.re) :
    ‖npsD k n w‖ ≤ Real.log n ^ k * ex σ n := by
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h := norm_nps_le hn hw
  rw [npsD, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The termwise bound for `D″`: `Σ_{m<M} Σ_j |u(j)| log²(5m+j) (5m+j)^{-σ}`. -/
def D2sum (σ : ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.range M, (Real.log (5 * m + 1 : ℕ) ^ 2 * ex σ (5 * m + 1)
    + kappa * (Real.log (5 * m + 2 : ℕ) ^ 2 * ex σ (5 * m + 2))
    + kappa * (Real.log (5 * m + 3 : ℕ) ^ 2 * ex σ (5 * m + 3))
    + Real.log (5 * m + 4 : ℕ) ^ 2 * ex σ (5 * m + 4))

theorem norm_DEMk_two_le (M : ℕ) {σ : ℝ} {w : ℂ} (hw : σ ≤ w.re) :
    ‖DEMk 2 M w‖ ≤ D2sum σ M := by
  rw [DEMk, D2sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  have hk : ‖(kappa : ℂ)‖ = kappa := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos kappa_pos]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _).trans ?_
  rw [norm_mul, norm_mul, hk]
  have h1 := norm_npsD_le 2 (n := 5 * m + 1) (by omega) hw
  have h2 := norm_npsD_le 2 (n := 5 * m + 2) (by omega) hw
  have h3 := norm_npsD_le 2 (n := 5 * m + 3) (by omega) hw
  have h4 := norm_npsD_le 2 (n := 5 * m + 4) (by omega) hw
  have hk0 := kappa_pos
  nlinarith [mul_le_mul_of_nonneg_left h2 hk0.le, mul_le_mul_of_nonneg_left h3 hk0.le]

/-- The sup bound for `Q_x` on a box `0 ≤ Re w ≤ σ₁`, `τ₀ ≤ |Im w| ≤ τ`. -/
def QsupB (K : ℕ) (x σ₁ τ τ₀ : ℝ) : ℝ :=
  x / τ₀ + 1 / 2 +
    ∑ k ∈ Finset.range K, |(bernoulli (2 * k + 2) : ℝ)| / ((2 * k + 2)! : ℝ) *
      Real.sqrt (∏ i ∈ Finset.range (2 * k + 1), ((σ₁ + i) ^ 2 + τ ^ 2)) / x ^ (2 * k + 1)

theorem norm_QEM_le (K : ℕ) {x σ₁ τ τ₀ : ℝ} (hx : 0 < x) (hτ₀ : 0 < τ₀) {w : ℂ}
    (h0 : 0 ≤ w.re) (h1 : w.re ≤ σ₁) (hT : |w.im| ≤ τ) (hT0 : τ₀ ≤ |w.im|) :
    ‖QEM K x w‖ ≤ QsupB K x σ₁ τ τ₀ := by
  rw [QEM, QsupB]
  have hw1 : τ₀ ≤ ‖w - 1‖ := by
    refine hT0.trans ((le_of_eq ?_).trans (Complex.abs_im_le_norm (w - 1)))
    simp
  have e1 : ‖(x : ℂ) / (w - 1)‖ ≤ x / τ₀ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    exact div_le_div_of_nonneg_left hx.le hτ₀ hw1
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add e1 ?_)) ?_)
  · norm_num
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hp : ‖HurwitzEM.poch w (2 * k + 1)‖ ≤
      Real.sqrt (∏ i ∈ Finset.range (2 * k + 1), ((σ₁ + i) ^ 2 + τ ^ 2)) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (HurwitzEM.norm_poch_sq_le h0 h1 hT _)
  rw [norm_div, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx]
  have hb : ‖((bernoulli (2 * k + 2) : ℚ) : ℂ)‖ = |(bernoulli (2 * k + 2) : ℝ)| :=
    Complex.norm_ratCast _
  have hf : ‖(((2 * k + 2)! : ℕ) : ℂ)‖ = ((2 * k + 2)! : ℝ) := by
    rw [Complex.norm_natCast]
  rw [hb, hf]
  gcongr

/-- The sup bound for `GEM M K` on a box. -/
def Gsup (M K : ℕ) (σ₀ σ₁ τ τ₀ : ℝ) : ℝ :=
  ex σ₀ (5 * M + 1) * QsupB K (M + 1 / 5) σ₁ τ τ₀ +
    kappa * (ex σ₀ (5 * M + 2) * QsupB K (M + 2 / 5) σ₁ τ τ₀) +
    kappa * (ex σ₀ (5 * M + 3) * QsupB K (M + 3 / 5) σ₁ τ τ₀) +
    ex σ₀ (5 * M + 4) * QsupB K (M + 4 / 5) σ₁ τ τ₀

theorem norm_GEM_le (M K : ℕ) {σ₀ σ₁ τ τ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (hτ₀ : 0 < τ₀) {w : ℂ}
    (h0 : σ₀ ≤ w.re) (h1 : w.re ≤ σ₁) (hT : |w.im| ≤ τ) (hT0 : τ₀ ≤ |w.im|) :
    ‖GEM M K w‖ ≤ Gsup M K σ₀ σ₁ τ τ₀ := by
  have hk : ‖(kappa : ℂ)‖ = kappa := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos kappa_pos]
  have hw0 : 0 ≤ w.re := hσ₀.trans h0
  have hq : ∀ j : ℕ, 1 ≤ j → ‖nps (5 * M + j) w * QEM K (M + j / 5) w‖ ≤
      ex σ₀ (5 * M + j) * QsupB K (M + j / 5) σ₁ τ τ₀ := by
    intro j hj
    have hx : (0 : ℝ) < M + j / 5 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj
      positivity
    rw [norm_mul]
    exact mul_le_mul (norm_nps_le (by omega) h0) (norm_QEM_le K hx hτ₀ hw0 h1 hT hT0)
      (norm_nonneg _) (Real.exp_pos _).le
  have q1 := hq 1 le_rfl
  have q2 := hq 2 (by norm_num)
  have q3 := hq 3 (by norm_num)
  have q4 := hq 4 (by norm_num)
  push_cast at q1 q2 q3 q4
  rw [GEM, Gsup]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _).trans ?_
  rw [norm_mul (kappa : ℂ), norm_mul (kappa : ℂ), hk]
  have hk0 := kappa_pos
  nlinarith [mul_le_mul_of_nonneg_left q2 hk0.le, mul_le_mul_of_nonneg_left q3 hk0.le]

/-- **Cauchy's estimate for `GEM″`**: a sup bound `C` on a circle of radius `R` about `z` (avoiding
the pole at `1`) gives `‖GEM″(z)‖ ≤ 2C/R²`. -/
theorem norm_deriv2_GEM_le (M K : ℕ) {z : ℂ} {R C : ℝ} (hR : 0 < R)
    (h1 : ∀ w ∈ closedBall z R, w ≠ 1) (hC : ∀ w ∈ sphere z R, ‖GEM M K w‖ ≤ C) :
    ‖deriv (deriv (GEM M K)) z‖ ≤ 2 * C / R ^ 2 := by
  have hd : DiffContOnCl ℂ (GEM M K) (ball z R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hR.ne']
    exact (differentiableOn_GEM M K).mono fun w hw => h1 w hw
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR hd hC
  rw [iteratedDeriv_succ, iteratedDeriv_one] at this
  simpa using this

/-- The derivative of `dhEM`, normalised. -/
theorem hasDerivAt_dhEM (M K : ℕ) {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt (dhEM M K) (aDH chi5 1 * (DEMk 1 M s + GEMd M K s)) s := by
  have hf : dhEM M K = fun s => aDH chi5 1 * fEM M K s := funext (dhEM_eq M K)
  rw [hf]
  exact (hasDerivAt_fEM M K hs).const_mul _

theorem differentiableOn_dhEM (M K : ℕ) : DifferentiableOn ℂ (dhEM M K) {s | s ≠ 1} :=
  fun _ hs => (hasDerivAt_dhEM M K hs).differentiableAt.differentiableWithinAt

theorem deriv_dhEM (M K : ℕ) {s : ℂ} (hs : s ≠ 1) :
    deriv (dhEM M K) s = aDH chi5 1 * (DEMk 1 M s + GEMd M K s) :=
  (hasDerivAt_dhEM M K hs).deriv

/-- The second derivative of `dhEM`, normalised: `a(1)·(D″ + G″)`. -/
theorem deriv2_dhEM (M K : ℕ) {z : ℂ} (hz : z ≠ 1) :
    deriv (deriv (dhEM M K)) z = aDH chi5 1 * (DEMk 2 M z + deriv (deriv (GEM M K)) z) := by
  have hev : deriv (dhEM M K) =ᶠ[nhds z]
      fun s => aDH chi5 1 * (DEMk 1 M s + deriv (GEM M K) s) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with s hs
    rw [deriv_dhEM M K hs, (hasDerivAt_GEM M K hs).deriv]
  rw [hev.deriv_eq]
  have hG : HasDerivAt (deriv (GEM M K)) (deriv (deriv (GEM M K)) z) z :=
    (((differentiableOn_GEM M K).deriv isOpen_ne).differentiableAt
      (isOpen_ne.mem_nhds hz)).hasDerivAt
  exact (((hasDerivAt_DEMk 1 M z).add hG).const_mul _).deriv

/-! ## 5. The centre, the ball, and the Euler–Maclaurin error on it -/

/-- The centre `c = 1617/2000 + (856993/10000) i`. -/
def cLoc : ℂ := 1617 / 2000 + 856993 / 10000 * I

theorem cLoc_re : cLoc.re = 1617 / 2000 := by simp [cLoc]
theorem cLoc_im : cLoc.im = 856993 / 10000 := by simp [cLoc]

theorem re_im_of_mem_closedBall {c z : ℂ} {ρ : ℝ} (hz : z ∈ closedBall c ρ) :
    |z.re - c.re| ≤ ρ ∧ |z.im - c.im| ≤ ρ := by
  have h : ‖z - c‖ ≤ ρ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hz
  refine ⟨le_trans (le_of_eq ?_) ((Complex.abs_re_le_norm _).trans h),
    le_trans (le_of_eq ?_) ((Complex.abs_im_le_norm _).trans h)⟩ <;> simp

/-- Points of `closedBall cLoc ρ`, `ρ ≤ 1`, in coordinates. -/
theorem box_of_mem {z : ℂ} {ρ : ℝ} (hz : z ∈ closedBall cLoc ρ) :
    1617 / 2000 - ρ ≤ z.re ∧ z.re ≤ 1617 / 2000 + ρ ∧
      856993 / 10000 - ρ ≤ z.im ∧ z.im ≤ 856993 / 10000 + ρ := by
  obtain ⟨h1, h2⟩ := re_im_of_mem_closedBall hz
  rw [cLoc_re, abs_le] at h1
  rw [cLoc_im, abs_le] at h2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem ne_one_of_mem {z : ℂ} {ρ : ℝ} (hρ : ρ ≤ 1) (hz : z ∈ closedBall cLoc ρ) : z ≠ 1 := by
  intro h
  have := (box_of_mem hz).2.2.1
  rw [h, Complex.one_im] at this
  linarith

theorem norm_aDH_two : ‖aDH chi5 2‖ = ‖aDH chi5 1‖ * kappa := by
  rw [aDH_chi5_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num [uval_two, abs_of_pos kappa_pos]

theorem norm_aDH_three : ‖aDH chi5 3‖ = ‖aDH chi5 1‖ * kappa := by
  rw [aDH_chi5_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num [uval_three, abs_of_pos kappa_pos]

theorem norm_aDH_four : ‖aDH chi5 4‖ = ‖aDH chi5 1‖ := by
  rw [aDH_chi5_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num [uval_four]

theorem kappa_le : kappa ≤ 28408 / 100000 := kappa_lt.le

theorem rpow_neg_div_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {p q : ℕ} (hq : 0 < q)
    (h : 1 ≤ x ^ p * y ^ q) : x ^ (-((p : ℝ) / q)) ≤ y := by
  have hz : 0 ≤ x ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hx.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hxp : 0 < x ^ p := pow_pos hx p
  have hzq : (x ^ (-((p : ℝ) / q))) ^ q = (x ^ p)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le,
      show -((p : ℝ) / q) * q = -(p : ℝ) by field_simp, Real.rpow_neg hx.le, Real.rpow_natCast]
  have hle : (x ^ (-((p : ℝ) / q))) ^ q ≤ y ^ q := by
    rw [hzq]
    calc (x ^ p)⁻¹ = (x ^ p)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (x ^ p)⁻¹ * (x ^ p * y ^ q) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = y ^ q := by field_simp
  exact (pow_le_pow_iff_left₀ hz hy.le hq.ne').1 hle

theorem five_rpow_le : (5 : ℝ) ^ (-(1597 / 2000 : ℝ)) ≤ 2805 / 10000 := by
  calc (5 : ℝ) ^ (-(1597 / 2000 : ℝ)) ≤ (5 : ℝ) ^ (-((79 : ℕ) : ℝ) / ((100 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = (5 : ℝ) ^ (-(((79 : ℕ) : ℝ) / ((100 : ℕ) : ℝ))) := by rw [neg_div]
    _ ≤ 2805 / 10000 := rpow_neg_div_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `x^{-(n + p/q)} ≤ (x^n)⁻¹ y` from `1 ≤ x^p y^q`. -/
theorem rpow_neg_add_div_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (n : ℕ) {p q : ℕ} (hq : 0 < q)
    (h : 1 ≤ x ^ p * y ^ q) : x ^ (-((n : ℝ) + (p : ℝ) / q)) ≤ (x ^ n)⁻¹ * y := by
  rw [neg_add, Real.rpow_add hx, Real.rpow_neg hx.le, Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left (rpow_neg_div_le hx hy hq h) (by positivity)

theorem x1_rpow_le : (101 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) ≤ 44123 / 500000000000000000000000000000000000 := by
  calc (101 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ))
        ≤ (101 / 5 : ℝ) ^ (-(((23 : ℕ) : ℝ) + ((79 : ℕ) : ℝ) / ((100 : ℕ) : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ ((101 / 5 : ℝ) ^ 23)⁻¹ * (44123 / 500000000000000000000000000000000000 * (101 / 5 : ℝ) ^ 23) :=
        rpow_neg_add_div_le (by norm_num) (by norm_num) 23 (by norm_num) (by norm_num)
    _ = _ := by field_simp

theorem x2_rpow_le : (102 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) ≤ 69807 / 1000000000000000000000000000000000000 := by
  calc (102 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ))
        ≤ (102 / 5 : ℝ) ^ (-(((23 : ℕ) : ℝ) + ((79 : ℕ) : ℝ) / ((100 : ℕ) : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ ((102 / 5 : ℝ) ^ 23)⁻¹ * (69807 / 1000000000000000000000000000000000000 * (102 / 5 : ℝ) ^ 23) :=
        rpow_neg_add_div_le (by norm_num) (by norm_num) 23 (by norm_num) (by norm_num)
    _ = _ := by field_simp

theorem x3_rpow_le : (103 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) ≤ 13837 / 250000000000000000000000000000000000 := by
  calc (103 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ))
        ≤ (103 / 5 : ℝ) ^ (-(((23 : ℕ) : ℝ) + ((79 : ℕ) : ℝ) / ((100 : ℕ) : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ ((103 / 5 : ℝ) ^ 23)⁻¹ * (13837 / 250000000000000000000000000000000000 * (103 / 5 : ℝ) ^ 23) :=
        rpow_neg_add_div_le (by norm_num) (by norm_num) 23 (by norm_num) (by norm_num)
    _ = _ := by field_simp

theorem x4_rpow_le : (104 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) ≤ 21991 / 500000000000000000000000000000000000 := by
  calc (104 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ))
        ≤ (104 / 5 : ℝ) ^ (-(((23 : ℕ) : ℝ) + ((79 : ℕ) : ℝ) / ((100 : ℕ) : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ ((104 / 5 : ℝ) ^ 23)⁻¹ * (21991 / 500000000000000000000000000000000000 * (104 / 5 : ℝ) ^ 23) :=
        rpow_neg_add_div_le (by norm_num) (by norm_num) 23 (by norm_num) (by norm_num)
    _ = _ := by field_simp

theorem pi_const_le : Real.pi ^ 2 / 3 / (2 * Real.pi) ^ (2 * 12) ≤
    1 / (3 * 2 ^ 24 * (3141592 / 1000000 : ℝ) ^ 22) := by
  have hpi : (3141592 / 1000000 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hp : 0 < Real.pi := Real.pi_pos
  have e : Real.pi ^ 2 / 3 / (2 * Real.pi) ^ (2 * 12) = 1 / (3 * 2 ^ 24 * Real.pi ^ 22) := by
    field_simp; ring
  rw [e]
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

/-- **The Pochhammer box constant, exactly**: `Π_{i<24} ((1637/2000 + i)² + (857093/10000)²)`
`= 1.15358…·10⁹³` as a rational (`norm_num`), and `≤ B² = (34·10⁴⁵)²`. -/
theorem prod_box_eq : ∏ i ∈ Finset.range (2 * 12), (((1637 / 2000 : ℝ) + i) ^ 2 + (857093 / 10000 : ℝ) ^ 2) =
    68758936056384808780502339571199424726189967127887266458317637624197626193844372005049817675759467131311845511188851550261539980457632420592875011260202786164793117384608214480751345972284684604289455826799904582443933283107763045200689877299134066291941401816074890592055041761 / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]; norm_num

theorem prod_box_le : ∏ i ∈ Finset.range (2 * 12), (((1637 / 2000 : ℝ) + i) ^ 2 + (857093 / 10000 : ℝ) ^ 2)
    ≤ ((34 : ℝ) * 10 ^ 45) ^ 2 := by
  rw [prod_box_eq]; norm_num

/-- **The Euler–Maclaurin error on the ball**, normalised: on `closedBall cLoc (1/100)`,
`‖dh z − dhEM 20 12 z‖ ≤ ‖a(1)‖ · 16·10⁻⁶` (box `1597/2000 ≤ Re z ≤ 1637/2000`, `|Im z| ≤ 857093/10000`,
`B = 34·10⁴⁵`). -/
theorem norm_dh_sub_dhEM_le_ball {z : ℂ} (hz : z ∈ closedBall cLoc (1 / 100)) :
    ‖dh z - dhEM 20 12 z‖ ≤ ‖aDH chi5 1‖ * (16 / 10 ^ 6) := by
  obtain ⟨h1, h2, h3, h4⟩ := box_of_mem hz
  have hs0 : (1597 / 2000 : ℝ) ≤ z.re := by linarith
  have hs1 : z.re ≤ 1637 / 2000 := by linarith
  have hsT : |z.im| ≤ 857093 / 10000 := by rw [abs_le]; constructor <;> linarith
  have hPB := prod_box_le
  have hb := norm_dh_sub_EM_le_box (M := 20) (K := 12) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hPB hs0 hs1 hsT (ne_one_of_mem (by norm_num) hz)
  norm_num at hb
  rw [norm_aDH_two, norm_aDH_three, norm_aDH_four] at hb
  refine hb.trans ?_
  set A := ‖aDH chi5 1‖ with hA
  set C := Real.pi ^ 2 / 3 / (2 * Real.pi) ^ 24 with hC
  have hC' : C ≤ 1 / (3 * 2 ^ 24 * (3141592 / 1000000 : ℝ) ^ 22) := pi_const_le
  have hA0 : 0 ≤ A := norm_nonneg _
  have hk0 : 0 ≤ kappa := kappa_pos.le
  have hC0 : 0 ≤ C := by positivity
  have e : (5 : ℝ) ^ (-(1597 / 2000 : ℝ)) *
      (A * (C * 34000000000000000000000000000000000000000000000 *
          ((101 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) / (47597 / 2000))) +
        A * kappa * (C * 34000000000000000000000000000000000000000000000 *
          ((102 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) / (47597 / 2000))) +
        A * kappa * (C * 34000000000000000000000000000000000000000000000 *
          ((103 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) / (47597 / 2000))) +
        A * (C * 34000000000000000000000000000000000000000000000 *
          ((104 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) / (47597 / 2000)))) =
      A * ((5 : ℝ) ^ (-(1597 / 2000 : ℝ)) *
        (C * 34000000000000000000000000000000000000000000000 *
          ((101 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) / (47597 / 2000)) +
        kappa * (C * 34000000000000000000000000000000000000000000000 *
          ((102 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) / (47597 / 2000))) +
        kappa * (C * 34000000000000000000000000000000000000000000000 *
          ((103 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) / (47597 / 2000))) +
        C * 34000000000000000000000000000000000000000000000 *
          ((104 / 5 : ℝ) ^ (-(47597 / 2000 : ℝ)) / (47597 / 2000)))) := by ring
  rw [e]
  apply mul_le_mul_of_nonneg_left _ hA0
  have hx1 := x1_rpow_le
  have hx2 := x2_rpow_le
  have hx3 := x3_rpow_le
  have hx4 := x4_rpow_le
  have h5 := five_rpow_le
  have hk := kappa_le
  calc _ ≤ (2805 / 10000 : ℝ) *
        ((1 / (3 * 2 ^ 24 * (3141592 / 1000000 : ℝ) ^ 22)) * 34000000000000000000000000000000000000000000000 *
          ((44123 / 500000000000000000000000000000000000 : ℝ) / (47597 / 2000)) +
        (28408 / 100000 : ℝ) * ((1 / (3 * 2 ^ 24 * (3141592 / 1000000 : ℝ) ^ 22)) *
          34000000000000000000000000000000000000000000000 *
          ((69807 / 1000000000000000000000000000000000000 : ℝ) / (47597 / 2000))) +
        (28408 / 100000 : ℝ) * ((1 / (3 * 2 ^ 24 * (3141592 / 1000000 : ℝ) ^ 22)) *
          34000000000000000000000000000000000000000000000 *
          ((13837 / 250000000000000000000000000000000000 : ℝ) / (47597 / 2000))) +
        (1 / (3 * 2 ^ 24 * (3141592 / 1000000 : ℝ) ^ 22)) * 34000000000000000000000000000000000000000000000 *
          ((21991 / 500000000000000000000000000000000000 : ℝ) / (47597 / 2000))) := by
        gcongr
    _ ≤ 16 / 10 ^ 6 := by norm_num

/-! ## 6. Bernoulli numbers `B₂, …, B₂₄` as rationals

Mathlib's `bernoulli'` (`B₁ = +1/2`) by its defining recursion, one step per index (binomials by
`decide`); `bernoulli n = bernoulli' n` for `n ≠ 1` (`bernoulli_eq_bernoulli'_of_ne_one`). -/

theorem bernoulli'_5_val : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_6_val : bernoulli' 6 = 1 / 42 := by
  have c0 : Nat.choose 6 0 = 1 := by decide
  have c1 : Nat.choose 6 1 = 6 := by decide
  have c2 : Nat.choose 6 2 = 15 := by decide
  have c3 : Nat.choose 6 3 = 20 := by decide
  have c4 : Nat.choose 6 4 = 15 := by decide
  have c5 : Nat.choose 6 5 = 6 := by decide
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5_val,
    c0, c1, c2, c3, c4, c5]
  norm_num

theorem bernoulli'_7_val : bernoulli' 7 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_8_val : bernoulli' 8 = -1 / 30 := by
  have c0 : Nat.choose 8 0 = 1 := by decide
  have c1 : Nat.choose 8 1 = 8 := by decide
  have c2 : Nat.choose 8 2 = 28 := by decide
  have c3 : Nat.choose 8 3 = 56 := by decide
  have c4 : Nat.choose 8 4 = 70 := by decide
  have c5 : Nat.choose 8 5 = 56 := by decide
  have c6 : Nat.choose 8 6 = 28 := by decide
  have c7 : Nat.choose 8 7 = 8 := by decide
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5_val, bernoulli'_6_val, bernoulli'_7_val,
    c0, c1, c2, c3, c4, c5, c6, c7]
  norm_num

theorem bernoulli'_9_val : bernoulli' 9 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_10_val : bernoulli' 10 = 5 / 66 := by
  have c0 : Nat.choose 10 0 = 1 := by decide
  have c1 : Nat.choose 10 1 = 10 := by decide
  have c2 : Nat.choose 10 2 = 45 := by decide
  have c3 : Nat.choose 10 3 = 120 := by decide
  have c4 : Nat.choose 10 4 = 210 := by decide
  have c5 : Nat.choose 10 5 = 252 := by decide
  have c6 : Nat.choose 10 6 = 210 := by decide
  have c7 : Nat.choose 10 7 = 120 := by decide
  have c8 : Nat.choose 10 8 = 45 := by decide
  have c9 : Nat.choose 10 9 = 10 := by decide
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5_val, bernoulli'_6_val, bernoulli'_7_val, bernoulli'_8_val, bernoulli'_9_val,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9]
  norm_num

theorem bernoulli'_11_val : bernoulli' 11 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_12_val : bernoulli' 12 = -691 / 2730 := by
  have c0 : Nat.choose 12 0 = 1 := by decide
  have c1 : Nat.choose 12 1 = 12 := by decide
  have c2 : Nat.choose 12 2 = 66 := by decide
  have c3 : Nat.choose 12 3 = 220 := by decide
  have c4 : Nat.choose 12 4 = 495 := by decide
  have c5 : Nat.choose 12 5 = 792 := by decide
  have c6 : Nat.choose 12 6 = 924 := by decide
  have c7 : Nat.choose 12 7 = 792 := by decide
  have c8 : Nat.choose 12 8 = 495 := by decide
  have c9 : Nat.choose 12 9 = 220 := by decide
  have c10 : Nat.choose 12 10 = 66 := by decide
  have c11 : Nat.choose 12 11 = 12 := by decide
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5_val, bernoulli'_6_val, bernoulli'_7_val, bernoulli'_8_val, bernoulli'_9_val, bernoulli'_10_val, bernoulli'_11_val,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11]
  norm_num

theorem bernoulli'_13_val : bernoulli' 13 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_14_val : bernoulli' 14 = 7 / 6 := by
  have c0 : Nat.choose 14 0 = 1 := by decide
  have c1 : Nat.choose 14 1 = 14 := by decide
  have c2 : Nat.choose 14 2 = 91 := by decide
  have c3 : Nat.choose 14 3 = 364 := by decide
  have c4 : Nat.choose 14 4 = 1001 := by decide
  have c5 : Nat.choose 14 5 = 2002 := by decide
  have c6 : Nat.choose 14 6 = 3003 := by decide
  have c7 : Nat.choose 14 7 = 3432 := by decide
  have c8 : Nat.choose 14 8 = 3003 := by decide
  have c9 : Nat.choose 14 9 = 2002 := by decide
  have c10 : Nat.choose 14 10 = 1001 := by decide
  have c11 : Nat.choose 14 11 = 364 := by decide
  have c12 : Nat.choose 14 12 = 91 := by decide
  have c13 : Nat.choose 14 13 = 14 := by decide
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5_val, bernoulli'_6_val, bernoulli'_7_val, bernoulli'_8_val, bernoulli'_9_val, bernoulli'_10_val, bernoulli'_11_val, bernoulli'_12_val, bernoulli'_13_val,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13]
  norm_num

theorem bernoulli'_15_val : bernoulli' 15 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_16_val : bernoulli' 16 = -3617 / 510 := by
  have c0 : Nat.choose 16 0 = 1 := by decide
  have c1 : Nat.choose 16 1 = 16 := by decide
  have c2 : Nat.choose 16 2 = 120 := by decide
  have c3 : Nat.choose 16 3 = 560 := by decide
  have c4 : Nat.choose 16 4 = 1820 := by decide
  have c5 : Nat.choose 16 5 = 4368 := by decide
  have c6 : Nat.choose 16 6 = 8008 := by decide
  have c7 : Nat.choose 16 7 = 11440 := by decide
  have c8 : Nat.choose 16 8 = 12870 := by decide
  have c9 : Nat.choose 16 9 = 11440 := by decide
  have c10 : Nat.choose 16 10 = 8008 := by decide
  have c11 : Nat.choose 16 11 = 4368 := by decide
  have c12 : Nat.choose 16 12 = 1820 := by decide
  have c13 : Nat.choose 16 13 = 560 := by decide
  have c14 : Nat.choose 16 14 = 120 := by decide
  have c15 : Nat.choose 16 15 = 16 := by decide
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5_val, bernoulli'_6_val, bernoulli'_7_val, bernoulli'_8_val, bernoulli'_9_val, bernoulli'_10_val, bernoulli'_11_val, bernoulli'_12_val, bernoulli'_13_val, bernoulli'_14_val, bernoulli'_15_val,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15]
  norm_num

theorem bernoulli'_17_val : bernoulli' 17 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_18_val : bernoulli' 18 = 43867 / 798 := by
  have c0 : Nat.choose 18 0 = 1 := by decide
  have c1 : Nat.choose 18 1 = 18 := by decide
  have c2 : Nat.choose 18 2 = 153 := by decide
  have c3 : Nat.choose 18 3 = 816 := by decide
  have c4 : Nat.choose 18 4 = 3060 := by decide
  have c5 : Nat.choose 18 5 = 8568 := by decide
  have c6 : Nat.choose 18 6 = 18564 := by decide
  have c7 : Nat.choose 18 7 = 31824 := by decide
  have c8 : Nat.choose 18 8 = 43758 := by decide
  have c9 : Nat.choose 18 9 = 48620 := by decide
  have c10 : Nat.choose 18 10 = 43758 := by decide
  have c11 : Nat.choose 18 11 = 31824 := by decide
  have c12 : Nat.choose 18 12 = 18564 := by decide
  have c13 : Nat.choose 18 13 = 8568 := by decide
  have c14 : Nat.choose 18 14 = 3060 := by decide
  have c15 : Nat.choose 18 15 = 816 := by decide
  have c16 : Nat.choose 18 16 = 153 := by decide
  have c17 : Nat.choose 18 17 = 18 := by decide
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5_val, bernoulli'_6_val, bernoulli'_7_val, bernoulli'_8_val, bernoulli'_9_val, bernoulli'_10_val, bernoulli'_11_val, bernoulli'_12_val, bernoulli'_13_val, bernoulli'_14_val, bernoulli'_15_val, bernoulli'_16_val, bernoulli'_17_val,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17]
  norm_num

theorem bernoulli'_19_val : bernoulli' 19 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_20_val : bernoulli' 20 = -174611 / 330 := by
  have c0 : Nat.choose 20 0 = 1 := by decide
  have c1 : Nat.choose 20 1 = 20 := by decide
  have c2 : Nat.choose 20 2 = 190 := by decide
  have c3 : Nat.choose 20 3 = 1140 := by decide
  have c4 : Nat.choose 20 4 = 4845 := by decide
  have c5 : Nat.choose 20 5 = 15504 := by decide
  have c6 : Nat.choose 20 6 = 38760 := by decide
  have c7 : Nat.choose 20 7 = 77520 := by decide
  have c8 : Nat.choose 20 8 = 125970 := by decide
  have c9 : Nat.choose 20 9 = 167960 := by decide
  have c10 : Nat.choose 20 10 = 184756 := by decide
  have c11 : Nat.choose 20 11 = 167960 := by decide
  have c12 : Nat.choose 20 12 = 125970 := by decide
  have c13 : Nat.choose 20 13 = 77520 := by decide
  have c14 : Nat.choose 20 14 = 38760 := by decide
  have c15 : Nat.choose 20 15 = 15504 := by decide
  have c16 : Nat.choose 20 16 = 4845 := by decide
  have c17 : Nat.choose 20 17 = 1140 := by decide
  have c18 : Nat.choose 20 18 = 190 := by decide
  have c19 : Nat.choose 20 19 = 20 := by decide
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5_val, bernoulli'_6_val, bernoulli'_7_val, bernoulli'_8_val, bernoulli'_9_val, bernoulli'_10_val, bernoulli'_11_val, bernoulli'_12_val, bernoulli'_13_val, bernoulli'_14_val, bernoulli'_15_val, bernoulli'_16_val, bernoulli'_17_val, bernoulli'_18_val, bernoulli'_19_val,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19]
  norm_num

theorem bernoulli'_21_val : bernoulli' 21 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_22_val : bernoulli' 22 = 854513 / 138 := by
  have c0 : Nat.choose 22 0 = 1 := by decide
  have c1 : Nat.choose 22 1 = 22 := by decide
  have c2 : Nat.choose 22 2 = 231 := by decide
  have c3 : Nat.choose 22 3 = 1540 := by decide
  have c4 : Nat.choose 22 4 = 7315 := by decide
  have c5 : Nat.choose 22 5 = 26334 := by decide
  have c6 : Nat.choose 22 6 = 74613 := by decide
  have c7 : Nat.choose 22 7 = 170544 := by decide
  have c8 : Nat.choose 22 8 = 319770 := by decide
  have c9 : Nat.choose 22 9 = 497420 := by decide
  have c10 : Nat.choose 22 10 = 646646 := by decide
  have c11 : Nat.choose 22 11 = 705432 := by decide
  have c12 : Nat.choose 22 12 = 646646 := by decide
  have c13 : Nat.choose 22 13 = 497420 := by decide
  have c14 : Nat.choose 22 14 = 319770 := by decide
  have c15 : Nat.choose 22 15 = 170544 := by decide
  have c16 : Nat.choose 22 16 = 74613 := by decide
  have c17 : Nat.choose 22 17 = 26334 := by decide
  have c18 : Nat.choose 22 18 = 7315 := by decide
  have c19 : Nat.choose 22 19 = 1540 := by decide
  have c20 : Nat.choose 22 20 = 231 := by decide
  have c21 : Nat.choose 22 21 = 22 := by decide
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5_val, bernoulli'_6_val, bernoulli'_7_val, bernoulli'_8_val, bernoulli'_9_val, bernoulli'_10_val, bernoulli'_11_val, bernoulli'_12_val, bernoulli'_13_val, bernoulli'_14_val, bernoulli'_15_val, bernoulli'_16_val, bernoulli'_17_val, bernoulli'_18_val, bernoulli'_19_val, bernoulli'_20_val, bernoulli'_21_val,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21]
  norm_num

theorem bernoulli'_23_val : bernoulli' 23 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_24_val : bernoulli' 24 = -236364091 / 2730 := by
  have c0 : Nat.choose 24 0 = 1 := by decide
  have c1 : Nat.choose 24 1 = 24 := by decide
  have c2 : Nat.choose 24 2 = 276 := by decide
  have c3 : Nat.choose 24 3 = 2024 := by decide
  have c4 : Nat.choose 24 4 = 10626 := by decide
  have c5 : Nat.choose 24 5 = 42504 := by decide
  have c6 : Nat.choose 24 6 = 134596 := by decide
  have c7 : Nat.choose 24 7 = 346104 := by decide
  have c8 : Nat.choose 24 8 = 735471 := by decide
  have c9 : Nat.choose 24 9 = 1307504 := by decide
  have c10 : Nat.choose 24 10 = 1961256 := by decide
  have c11 : Nat.choose 24 11 = 2496144 := by decide
  have c12 : Nat.choose 24 12 = 2704156 := by decide
  have c13 : Nat.choose 24 13 = 2496144 := by decide
  have c14 : Nat.choose 24 14 = 1961256 := by decide
  have c15 : Nat.choose 24 15 = 1307504 := by decide
  have c16 : Nat.choose 24 16 = 735471 := by decide
  have c17 : Nat.choose 24 17 = 346104 := by decide
  have c18 : Nat.choose 24 18 = 134596 := by decide
  have c19 : Nat.choose 24 19 = 42504 := by decide
  have c20 : Nat.choose 24 20 = 10626 := by decide
  have c21 : Nat.choose 24 21 = 2024 := by decide
  have c22 : Nat.choose 24 22 = 276 := by decide
  have c23 : Nat.choose 24 23 = 24 := by decide
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5_val, bernoulli'_6_val, bernoulli'_7_val, bernoulli'_8_val, bernoulli'_9_val, bernoulli'_10_val, bernoulli'_11_val, bernoulli'_12_val, bernoulli'_13_val, bernoulli'_14_val, bernoulli'_15_val, bernoulli'_16_val, bernoulli'_17_val, bernoulli'_18_val, bernoulli'_19_val, bernoulli'_20_val, bernoulli'_21_val, bernoulli'_22_val, bernoulli'_23_val,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23]
  norm_num

theorem bernoulli_2_eq : bernoulli 2 = 1 / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_two]

theorem bernoulli_4_eq : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

theorem bernoulli_6_eq : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_6_val]

theorem bernoulli_8_eq : bernoulli 8 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_8_val]

theorem bernoulli_10_eq : bernoulli 10 = 5 / 66 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_10_val]

theorem bernoulli_12_eq : bernoulli 12 = -691 / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_12_val]

theorem bernoulli_14_eq : bernoulli 14 = 7 / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_14_val]

theorem bernoulli_16_eq : bernoulli 16 = -3617 / 510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_16_val]

theorem bernoulli_18_eq : bernoulli 18 = 43867 / 798 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_18_val]

theorem bernoulli_20_eq : bernoulli 20 = -174611 / 330 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_20_val]

theorem bernoulli_22_eq : bernoulli 22 = 854513 / 138 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_22_val]

theorem bernoulli_24_eq : bernoulli 24 = -236364091 / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_24_val]

/-- The twelve Bernoulli values used by `EM_{20,12}`. -/
theorem bernoulli_vals :
    bernoulli 2 = 1 / 6 ∧ bernoulli 4 = -1 / 30 ∧ bernoulli 6 = 1 / 42 ∧ bernoulli 8 = -1 / 30 ∧
      bernoulli 10 = 5 / 66 ∧ bernoulli 12 = -691 / 2730 ∧ bernoulli 14 = 7 / 6 ∧
      bernoulli 16 = -3617 / 510 ∧ bernoulli 18 = 43867 / 798 ∧ bernoulli 20 = -174611 / 330 ∧
      bernoulli 22 = 854513 / 138 ∧ bernoulli 24 = -236364091 / 2730 :=
  ⟨bernoulli_2_eq, bernoulli_4_eq, bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq, bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq⟩


/-! ## 7. `G″` on the ball, by Cauchy's estimate on circles of radius `2/5` -/

/-- `√(Π (a_i² + τ²)) ≤ Π (τ + a_i²/(2τ))` (`√(τ² + a²) ≤ τ + a²/(2τ)`), a rational bound. -/
theorem sqrt_prod_le (n : ℕ) {σ₁ τ : ℝ} (hτ : 0 < τ) :
    Real.sqrt (∏ i ∈ Finset.range n, ((σ₁ + i) ^ 2 + τ ^ 2)) ≤
      ∏ i ∈ Finset.range n, (τ + (σ₁ + i) ^ 2 / (2 * τ)) := by
  rw [Real.sqrt_le_left (Finset.prod_nonneg fun i _ => by positivity), ← Finset.prod_pow]
  apply Finset.prod_le_prod₀ (fun i _ => by positivity)
  intro i _
  have : (τ + (σ₁ + i) ^ 2 / (2 * τ)) ^ 2 = (σ₁ + i) ^ 2 + τ ^ 2 + ((σ₁ + i) ^ 2 / (2 * τ)) ^ 2 := by
    field_simp; ring
  rw [this]
  nlinarith [sq_nonneg ((σ₁ + i) ^ 2 / (2 * τ))]

/-- `QsupB` with the square roots replaced by the rational bound of `sqrt_prod_le`. -/
def QsupR (K : ℕ) (x σ₁ τ τ₀ : ℝ) : ℝ :=
  x / τ₀ + 1 / 2 +
    ∑ k ∈ Finset.range K, |(bernoulli (2 * k + 2) : ℝ)| / ((2 * k + 2)! : ℝ) *
      (∏ i ∈ Finset.range (2 * k + 1), (τ + (σ₁ + i) ^ 2 / (2 * τ))) / x ^ (2 * k + 1)

theorem QsupB_le_QsupR (K : ℕ) {x σ₁ τ τ₀ : ℝ} (hx : 0 < x) (hτ : 0 < τ) :
    QsupB K x σ₁ τ τ₀ ≤ QsupR K x σ₁ τ τ₀ := by
  unfold QsupB QsupR
  gcongr with k hk
  exact sqrt_prod_le _ hτ

theorem ex_eq_rpow (σ : ℝ) {n : ℕ} (hn : 1 ≤ n) : ex σ n = (n : ℝ) ^ (-σ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ex, Real.rpow_def_of_pos hn']
  ring_nf

theorem ex_le_of {σ : ℝ} {n : ℕ} (hn : 1 ≤ n) {p q : ℕ} (hq : 0 < q) (hσ : (p : ℝ) / q ≤ σ)
    {y : ℝ} (hy : 0 < y) (h : 1 ≤ (n : ℝ) ^ p * y ^ q) : ex σ n ≤ y := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [ex_eq_rpow σ hn]
  calc (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-((p : ℝ) / q)) :=
        Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
    _ ≤ y := rpow_neg_div_le (by linarith) hy hq h

/-- The four `Q`-factors on the box of `closedBall cLoc (41/100)`, in one rational bound each. -/
theorem QsupR_ball_le :
    QsupR 12 (20 + 1 / 5) (2437 / 2000) (861093 / 10000) (852893 / 10000) ≤ 1287 / 1000 ∧
    QsupR 12 (20 + 2 / 5) (2437 / 2000) (861093 / 10000) (852893 / 10000) ≤ 1277 / 1000 ∧
    QsupR 12 (20 + 3 / 5) (2437 / 2000) (861093 / 10000) (852893 / 10000) ≤ 1268 / 1000 ∧
    QsupR 12 (20 + 4 / 5) (2437 / 2000) (861093 / 10000) (852893 / 10000) ≤ 1259 / 1000 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [QsupR, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
      Finset.prod_range_zero, Nat.reduceMul, Nat.reduceAdd, bernoulli_2_eq, bernoulli_4_eq,
      bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq,
      bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq]
    norm_num [Nat.factorial]

/-- **The sup of `GEM 20 12` on `closedBall cLoc (41/100)`** is at most `53/100`. -/
theorem Gsup_ball_le :
    Gsup 20 12 (797 / 2000) (2437 / 2000) (861093 / 10000) (852893 / 10000) ≤ 53 / 100 := by
  obtain ⟨q1, q2, q3, q4⟩ := QsupR_ball_le
  have r1 := QsupB_le_QsupR 12 (x := 20 + 1 / 5) (σ₁ := 2437 / 2000) (τ := 861093 / 10000)
    (τ₀ := 852893 / 10000) (by norm_num) (by norm_num)
  have r2 := QsupB_le_QsupR 12 (x := 20 + 2 / 5) (σ₁ := 2437 / 2000) (τ := 861093 / 10000)
    (τ₀ := 852893 / 10000) (by norm_num) (by norm_num)
  have r3 := QsupB_le_QsupR 12 (x := 20 + 3 / 5) (σ₁ := 2437 / 2000) (τ := 861093 / 10000)
    (τ₀ := 852893 / 10000) (by norm_num) (by norm_num)
  have r4 := QsupB_le_QsupR 12 (x := 20 + 4 / 5) (σ₁ := 2437 / 2000) (τ := 861093 / 10000)
    (τ₀ := 852893 / 10000) (by norm_num) (by norm_num)
  have e1 : ex (797 / 2000) 101 ≤ 3231 / 20000 :=
    ex_le_of (p := 79) (q := 200) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : ex (797 / 2000) 102 ≤ 4023 / 25000 :=
    ex_le_of (p := 79) (q := 200) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : ex (797 / 2000) 103 ≤ 1603 / 10000 :=
    ex_le_of (p := 79) (q := 200) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : ex (797 / 2000) 104 ≤ 15969 / 100000 :=
    ex_le_of (p := 79) (q := 200) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hk := kappa_le
  have hk0 := kappa_pos.le
  have hq0 : ∀ j : ℕ, 0 ≤ QsupB 12 (20 + j / 5) (2437 / 2000) (861093 / 10000) (852893 / 10000) := by
    intro j
    unfold QsupB
    positivity
  have p1 := hq0 1
  have p2 := hq0 2
  have p3 := hq0 3
  have p4 := hq0 4
  have x1 : 0 ≤ ex (797 / 2000) 101 := (Real.exp_pos _).le
  have x2 : 0 ≤ ex (797 / 2000) 102 := (Real.exp_pos _).le
  have x3 : 0 ≤ ex (797 / 2000) 103 := (Real.exp_pos _).le
  have x4 : 0 ≤ ex (797 / 2000) 104 := (Real.exp_pos _).le
  unfold Gsup
  push_cast at p1 p2 p3 p4 ⊢
  refine le_trans ?_ (show (3231 / 20000 * (1287 / 1000) + 28408 / 100000 * (4023 / 25000 * (1277 / 1000)) +
      28408 / 100000 * (1603 / 10000 * (1268 / 1000)) + 15969 / 100000 * (1259 / 1000) : ℝ) ≤ 53 / 100
      by norm_num)
  gcongr
  · exact r1.trans q1
  · exact r2.trans q2
  · exact r3.trans q3
  · exact r4.trans q4

/-- **Cauchy for `G″` on the ball**: `‖GEM″(z)‖ ≤ 2·(53/100)/(2/5)² = 53/8` on `closedBall cLoc (1/100)`
(circles of radius `2/5` stay in `closedBall cLoc (41/100)`, where `‖GEM‖ ≤ 53/100`). -/
theorem norm_deriv2_GEM_ball {z : ℂ} (hz : z ∈ closedBall cLoc (1 / 100)) :
    ‖deriv (deriv (GEM 20 12)) z‖ ≤ 53 / 8 := by
  have hsub : closedBall z (2 / 5) ⊆ closedBall cLoc (41 / 100) := by
    apply closedBall_subset_closedBall'
    have := mem_closedBall.1 hz
    linarith
  have h := norm_deriv2_GEM_le 20 12 (z := z) (R := 2 / 5) (C := 53 / 100) (by norm_num)
    (fun w hw => ne_one_of_mem (by norm_num) (hsub hw)) (fun w hw => ?_)
  · refine h.trans (le_of_eq ?_)
    norm_num
  · obtain ⟨h1, h2, h3, h4⟩ := box_of_mem (hsub (sphere_subset_closedBall hw))
    have hT : |w.im| ≤ 861093 / 10000 := by rw [abs_le]; constructor <;> linarith
    have hT0 : (852893 / 10000 : ℝ) ≤ |w.im| := by
      rw [abs_of_pos (by linarith)]; linarith
    refine (norm_GEM_le 20 12 (σ₀ := 797 / 2000) (σ₁ := 2437 / 2000) (by norm_num) (by norm_num)
      (by linarith) (by linarith) hT hT0).trans ?_
    exact Gsup_ball_le

/-- **The second-derivative bound on the ball**, reduced to the Dirichlet-polynomial sum `D2sum`:
`‖dhEM″(z)‖ ≤ ‖a(1)‖·(D2sum(1597/2000, 20) + 53/8)` on `closedBall cLoc (1/100)`. -/
theorem norm_deriv2_dhEM_ball {z : ℂ} (hz : z ∈ closedBall cLoc (1 / 100)) :
    ‖deriv (deriv (dhEM 20 12)) z‖ ≤ ‖aDH chi5 1‖ * (D2sum (1597 / 2000) 20 + 53 / 8) := by
  rw [deriv2_dhEM 20 12 (ne_one_of_mem (by norm_num) hz), norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_deriv2_GEM_ball hz))
  exact norm_DEMk_two_le 20 (by linarith [(box_of_mem hz).1])

/-! ## 8. The certificate skeleton -/

theorem norm_aDH_one_pos : 0 < ‖aDH chi5 1‖ := norm_pos_iff.2 aDH_chi5_one_ne_zero

/-- **Stage 2, abstract form.** The minimum-modulus certificate for a zero of `dh` within `1/100`
of `c = 1617/2000 + (856993/10000) i`, from five numeric inputs about the Euler–Maclaurin
approximant `P = dhEM 20 12`: `‖P(c)‖ ≤ p₀`, `a₀ ≤ ‖P′(c)‖`, `‖P″‖ ≤ m₂` and `‖dh − P‖ ≤ e₀` on the
closed ball, and the margin `2(p₀ + e₀) < a₀/100 − m₂/100²`. -/
theorem dh_zero_near_of_numerics {p₀ a₀ m₂ e₀ : ℝ}
    (hP : ‖dhEM 20 12 cLoc‖ ≤ p₀)
    (hA : a₀ ≤ ‖deriv (dhEM 20 12) cLoc‖)
    (hM2 : ∀ z ∈ closedBall cLoc (1 / 100), ‖deriv (deriv (dhEM 20 12)) z‖ ≤ m₂)
    (hE : ∀ z ∈ closedBall cLoc (1 / 100), ‖dh z - dhEM 20 12 z‖ ≤ e₀)
    (hmargin : 2 * (p₀ + e₀) < a₀ * (1 / 100) - m₂ * (1 / 100) ^ 2) :
    ∃ ρ, dh ρ = 0 ∧ ‖ρ - cLoc‖ < 1 / 100 := by
  have hU : ∀ w ∈ closedBall cLoc (1 / 100), w ∈ {s : ℂ | s ≠ 1} :=
    fun w hw => ne_one_of_mem (by norm_num) hw
  obtain ⟨z, hz, h0⟩ := exists_zero_of_bounds (f := dh) (P := dhEM 20 12) (by norm_num)
    differentiable_dh.differentiableOn
    (fun w hw => (differentiableOn_dhEM 20 12).differentiableAt (isOpen_ne.mem_nhds (hU w hw)))
    (fun w hw => ((differentiableOn_dhEM 20 12).deriv isOpen_ne).differentiableAt
      (isOpen_ne.mem_nhds (hU w hw)))
    hP hA hM2 hE hmargin
  exact ⟨z, h0, mem_ball_iff_norm.1 hz⟩

/-- **Stage 2, normalised form**, with the Euler–Maclaurin error (`16·10⁻⁶ ‖a(1)‖`) and the
`G″` part of the second derivative (`53/8`) discharged. Three numeric inputs remain, all about the
normalised approximant `fEM = dhEM/a(1)` (`dhEM_eq`): `‖fEM(c)‖ ≤ p₀`, `a₀ ≤ ‖fEM′(c)‖`
(`fEM′ = DEMk 1 + GEMd`, `hasDerivAt_fEM`), and the termwise sum `D2sum(1597/2000, 20) ≤ d₂`. -/
theorem dh_zero_near_of_fEM {p₀ a₀ d₂ : ℝ}
    (hP : ‖fEM 20 12 cLoc‖ ≤ p₀)
    (hA : a₀ ≤ ‖DEMk 1 20 cLoc + GEMd 20 12 cLoc‖)
    (hD2 : D2sum (1597 / 2000) 20 ≤ d₂)
    (hmargin : 2 * (p₀ + 16 / 10 ^ 6) < a₀ / 100 - (d₂ + 53 / 8) / 10 ^ 4) :
    ∃ ρ, dh ρ = 0 ∧ ‖ρ - cLoc‖ < 1 / 100 := by
  have hA0 := norm_aDH_one_pos
  set A := ‖aDH chi5 1‖ with hAdef
  have hc1 : cLoc ≠ 1 := ne_one_of_mem (ρ := 1 / 100) (by norm_num) (mem_closedBall_self (by norm_num))
  refine dh_zero_near_of_numerics (p₀ := A * p₀) (a₀ := A * a₀) (m₂ := A * (d₂ + 53 / 8))
    (e₀ := A * (16 / 10 ^ 6)) ?_ ?_ ?_ (fun z hz => norm_dh_sub_dhEM_le_ball hz) ?_
  · rw [dhEM_eq, norm_mul]
    exact mul_le_mul_of_nonneg_left hP hA0.le
  · rw [deriv_dhEM 20 12 hc1, norm_mul]
    exact mul_le_mul_of_nonneg_left hA hA0.le
  · intro z hz
    refine (norm_deriv2_dhEM_ball hz).trans (mul_le_mul_of_nonneg_left ?_ hA0.le)
    linarith
  · have h := mul_lt_mul_of_pos_left hmargin hA0
    have e1 : A * (2 * (p₀ + 16 / 10 ^ 6)) = 2 * (A * p₀ + A * (16 / 10 ^ 6)) := by ring
    have e2 : A * (a₀ / 100 - (d₂ + 53 / 8) / 10 ^ 4) =
        A * a₀ * (1 / 100) - A * (d₂ + 53 / 8) * (1 / 100) ^ 2 := by ring
    rw [e1, e2] at h
    exact h

/-! ## 9. The open inputs in elementary form

At `c = σ + it`, `σ = 1617/2000`, `t = 856993/10000`: `n^{-c} = e_n (C_n − i S_n)` with
`e_n = exp(−σ log n)` (`ex`), `C_n = cos(t log n)` (`cC`), `S_n = sin(t log n)` (`sC`) (`nps_cLoc`). -/

/-- `cos(t log n)`, `t = 856993/10000`. -/
def cC (n : ℕ) : ℝ := Real.cos (856993 / 10000 * Real.log n)

/-- `sin(t log n)`, `t = 856993/10000`. -/
def sC (n : ℕ) : ℝ := Real.sin (856993 / 10000 * Real.log n)

theorem nps_cLoc {n : ℕ} (hn : 1 ≤ n) :
    (nps n cLoc).re = ex (1617 / 2000) n * cC n ∧
      (nps n cLoc).im = -(ex (1617 / 2000) n * sC n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have e : nps n cLoc = Complex.exp ((Real.log n : ℂ) * (-cLoc)) := by
    rw [nps, cpow_def_of_ne_zero hn0, ← natCast_log]
  have hre : ((Real.log n : ℂ) * (-cLoc)).re = -(1617 / 2000 * Real.log n) := by
    rw [Complex.re_ofReal_mul, Complex.neg_re, cLoc_re]; ring
  have him : ((Real.log n : ℂ) * (-cLoc)).im = -(856993 / 10000 * Real.log n) := by
    rw [Complex.im_ofReal_mul, Complex.neg_im, cLoc_im]; ring
  rw [e, Complex.exp_re, Complex.exp_im, hre, him, Real.cos_neg, Real.sin_neg, ex, cC, sC]
  constructor <;> ring

theorem npsD_one (n : ℕ) (s : ℂ) : npsD 1 n s = -(Real.log n : ℂ) * nps n s := by
  simp [npsD, nps]

/-- `Re fEM(c)`, elementary: `Σ_m Σ_j u(j) e C` over `n = 5m+j < 5M`, plus
`Σ_j u(j) e_N (C_N Re Q_j + S_N Im Q_j)` over `N = 5M + j`, `Q_j = Q_{M+j/5}(c)`. -/
def PRe (M K : ℕ) : ℝ :=
  (∑ m ∈ Finset.range M, (ex (1617 / 2000) (5 * m + 1) * cC (5 * m + 1)
      + kappa * (ex (1617 / 2000) (5 * m + 2) * cC (5 * m + 2))
      - kappa * (ex (1617 / 2000) (5 * m + 3) * cC (5 * m + 3))
      - ex (1617 / 2000) (5 * m + 4) * cC (5 * m + 4))) +
    (ex (1617 / 2000) (5 * M + 1) * (cC (5 * M + 1) * (QEM K (M + 1 / 5) cLoc).re
        + sC (5 * M + 1) * (QEM K (M + 1 / 5) cLoc).im)
      + kappa * (ex (1617 / 2000) (5 * M + 2) * (cC (5 * M + 2) * (QEM K (M + 2 / 5) cLoc).re
        + sC (5 * M + 2) * (QEM K (M + 2 / 5) cLoc).im))
      - kappa * (ex (1617 / 2000) (5 * M + 3) * (cC (5 * M + 3) * (QEM K (M + 3 / 5) cLoc).re
        + sC (5 * M + 3) * (QEM K (M + 3 / 5) cLoc).im))
      - ex (1617 / 2000) (5 * M + 4) * (cC (5 * M + 4) * (QEM K (M + 4 / 5) cLoc).re
        + sC (5 * M + 4) * (QEM K (M + 4 / 5) cLoc).im))

/-- `Im fEM(c)`, elementary. -/
def PIm (M K : ℕ) : ℝ :=
  -(∑ m ∈ Finset.range M, (ex (1617 / 2000) (5 * m + 1) * sC (5 * m + 1)
      + kappa * (ex (1617 / 2000) (5 * m + 2) * sC (5 * m + 2))
      - kappa * (ex (1617 / 2000) (5 * m + 3) * sC (5 * m + 3))
      - ex (1617 / 2000) (5 * m + 4) * sC (5 * m + 4))) +
    (ex (1617 / 2000) (5 * M + 1) * (cC (5 * M + 1) * (QEM K (M + 1 / 5) cLoc).im
        - sC (5 * M + 1) * (QEM K (M + 1 / 5) cLoc).re)
      + kappa * (ex (1617 / 2000) (5 * M + 2) * (cC (5 * M + 2) * (QEM K (M + 2 / 5) cLoc).im
        - sC (5 * M + 2) * (QEM K (M + 2 / 5) cLoc).re))
      - kappa * (ex (1617 / 2000) (5 * M + 3) * (cC (5 * M + 3) * (QEM K (M + 3 / 5) cLoc).im
        - sC (5 * M + 3) * (QEM K (M + 3 / 5) cLoc).re))
      - ex (1617 / 2000) (5 * M + 4) * (cC (5 * M + 4) * (QEM K (M + 4 / 5) cLoc).im
        - sC (5 * M + 4) * (QEM K (M + 4 / 5) cLoc).re))

/-- The `Q`-combination of the derivative: `Q′_x(c) − log N · Q_x(c)`. -/
def QD (K : ℕ) (x : ℝ) (N : ℕ) : ℂ := QEMd K x cLoc - (Real.log N : ℂ) * QEM K x cLoc

/-- `Re fEM′(c)`, elementary. -/
def ARe (M K : ℕ) : ℝ :=
  -(∑ m ∈ Finset.range M, (Real.log (5 * m + 1 : ℕ) * (ex (1617 / 2000) (5 * m + 1) * cC (5 * m + 1))
      + kappa * (Real.log (5 * m + 2 : ℕ) * (ex (1617 / 2000) (5 * m + 2) * cC (5 * m + 2)))
      - kappa * (Real.log (5 * m + 3 : ℕ) * (ex (1617 / 2000) (5 * m + 3) * cC (5 * m + 3)))
      - Real.log (5 * m + 4 : ℕ) * (ex (1617 / 2000) (5 * m + 4) * cC (5 * m + 4)))) +
    (ex (1617 / 2000) (5 * M + 1) * (cC (5 * M + 1) * (QD K (M + 1 / 5) (5 * M + 1)).re
        + sC (5 * M + 1) * (QD K (M + 1 / 5) (5 * M + 1)).im)
      + kappa * (ex (1617 / 2000) (5 * M + 2) * (cC (5 * M + 2) * (QD K (M + 2 / 5) (5 * M + 2)).re
        + sC (5 * M + 2) * (QD K (M + 2 / 5) (5 * M + 2)).im))
      - kappa * (ex (1617 / 2000) (5 * M + 3) * (cC (5 * M + 3) * (QD K (M + 3 / 5) (5 * M + 3)).re
        + sC (5 * M + 3) * (QD K (M + 3 / 5) (5 * M + 3)).im))
      - ex (1617 / 2000) (5 * M + 4) * (cC (5 * M + 4) * (QD K (M + 4 / 5) (5 * M + 4)).re
        + sC (5 * M + 4) * (QD K (M + 4 / 5) (5 * M + 4)).im))

/-- `Im fEM′(c)`, elementary. -/
def AIm (M K : ℕ) : ℝ :=
  (∑ m ∈ Finset.range M, (Real.log (5 * m + 1 : ℕ) * (ex (1617 / 2000) (5 * m + 1) * sC (5 * m + 1))
      + kappa * (Real.log (5 * m + 2 : ℕ) * (ex (1617 / 2000) (5 * m + 2) * sC (5 * m + 2)))
      - kappa * (Real.log (5 * m + 3 : ℕ) * (ex (1617 / 2000) (5 * m + 3) * sC (5 * m + 3)))
      - Real.log (5 * m + 4 : ℕ) * (ex (1617 / 2000) (5 * m + 4) * sC (5 * m + 4)))) +
    (ex (1617 / 2000) (5 * M + 1) * (cC (5 * M + 1) * (QD K (M + 1 / 5) (5 * M + 1)).im
        - sC (5 * M + 1) * (QD K (M + 1 / 5) (5 * M + 1)).re)
      + kappa * (ex (1617 / 2000) (5 * M + 2) * (cC (5 * M + 2) * (QD K (M + 2 / 5) (5 * M + 2)).im
        - sC (5 * M + 2) * (QD K (M + 2 / 5) (5 * M + 2)).re))
      - kappa * (ex (1617 / 2000) (5 * M + 3) * (cC (5 * M + 3) * (QD K (M + 3 / 5) (5 * M + 3)).im
        - sC (5 * M + 3) * (QD K (M + 3 / 5) (5 * M + 3)).re))
      - ex (1617 / 2000) (5 * M + 4) * (cC (5 * M + 4) * (QD K (M + 4 / 5) (5 * M + 4)).im
        - sC (5 * M + 4) * (QD K (M + 4 / 5) (5 * M + 4)).re))

theorem re_npsMul {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (nps n cLoc * z).re = ex (1617 / 2000) n * (cC n * z.re + sC n * z.im) := by
  obtain ⟨h1, h2⟩ := nps_cLoc hn
  rw [Complex.mul_re, h1, h2]; ring

theorem im_npsMul {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (nps n cLoc * z).im = ex (1617 / 2000) n * (cC n * z.im - sC n * z.re) := by
  obtain ⟨h1, h2⟩ := nps_cLoc hn
  rw [Complex.mul_im, h1, h2]; ring

theorem fEM_cLoc_re (M K : ℕ) : (fEM M K cLoc).re = PRe M K := by
  unfold fEM DEM GEM PRe
  simp only [Complex.add_re, Complex.sub_re, Complex.re_sum, Complex.re_ofReal_mul]
  rw [re_npsMul (by omega), re_npsMul (by omega), re_npsMul (by omega), re_npsMul (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [(nps_cLoc (n := 5 * m + 1) (by omega)).1, (nps_cLoc (n := 5 * m + 2) (by omega)).1,
    (nps_cLoc (n := 5 * m + 3) (by omega)).1, (nps_cLoc (n := 5 * m + 4) (by omega)).1]

theorem fEM_cLoc_im (M K : ℕ) : (fEM M K cLoc).im = PIm M K := by
  unfold fEM DEM GEM PIm
  simp only [Complex.add_im, Complex.sub_im, Complex.im_sum, Complex.im_ofReal_mul]
  rw [im_npsMul (by omega), im_npsMul (by omega), im_npsMul (by omega), im_npsMul (by omega)]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [(nps_cLoc (n := 5 * m + 1) (by omega)).2, (nps_cLoc (n := 5 * m + 2) (by omega)).2,
    (nps_cLoc (n := 5 * m + 3) (by omega)).2, (nps_cLoc (n := 5 * m + 4) (by omega)).2]
  ring

theorem GEMd_term (M K j : ℕ) (x : ℝ) :
    npsD 1 (5 * M + j) cLoc * QEM K x cLoc + nps (5 * M + j) cLoc * QEMd K x cLoc =
      nps (5 * M + j) cLoc * QD K x (5 * M + j) := by
  rw [npsD_one, QD]; ring

theorem fEMd_cLoc_re (M K : ℕ) : (DEMk 1 M cLoc + GEMd M K cLoc).re = ARe M K := by
  unfold DEMk GEMd ARe
  rw [GEMd_term, GEMd_term, GEMd_term, GEMd_term]
  simp only [Complex.add_re, Complex.sub_re, Complex.re_sum, Complex.re_ofReal_mul]
  rw [re_npsMul (by omega), re_npsMul (by omega), re_npsMul (by omega), re_npsMul (by omega)]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [npsD_one, Complex.neg_re, Complex.re_ofReal_mul, neg_mul]
  rw [(nps_cLoc (n := 5 * m + 1) (by omega)).1, (nps_cLoc (n := 5 * m + 2) (by omega)).1,
    (nps_cLoc (n := 5 * m + 3) (by omega)).1, (nps_cLoc (n := 5 * m + 4) (by omega)).1]
  ring

theorem fEMd_cLoc_im (M K : ℕ) : (DEMk 1 M cLoc + GEMd M K cLoc).im = AIm M K := by
  unfold DEMk GEMd AIm
  rw [GEMd_term, GEMd_term, GEMd_term, GEMd_term]
  simp only [Complex.add_im, Complex.sub_im, Complex.im_sum, Complex.im_ofReal_mul]
  rw [im_npsMul (by omega), im_npsMul (by omega), im_npsMul (by omega), im_npsMul (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [npsD_one, Complex.neg_im, Complex.im_ofReal_mul, neg_mul]
  rw [(nps_cLoc (n := 5 * m + 1) (by omega)).2, (nps_cLoc (n := 5 * m + 2) (by omega)).2,
    (nps_cLoc (n := 5 * m + 3) (by omega)).2, (nps_cLoc (n := 5 * m + 4) (by omega)).2]
  ring

/-! ## 10. Exact Gaussian-rational values of `Q_x(c)` and `Q′_x(c)`, `x = 20 + j/5`

`(s)_n` and its derivative at `c` by the recursions `poch_succ`, `pochD`, one step per `n`. -/

theorem poch_cLoc_0 : (HurwitzEM.poch cLoc 0).re = (1 : ℝ) ∧ (HurwitzEM.poch cLoc 0).im = (0 : ℝ) := by
  simp [HurwitzEM.poch]

theorem pochD_cLoc_0 : (pochD cLoc 0).re = (0 : ℝ) ∧ (pochD cLoc 0).im = (0 : ℝ) := by
  simp [pochD]

theorem poch_cLoc_1 : (HurwitzEM.poch cLoc 1).re = (1617 / 2000 : ℝ) ∧
    (HurwitzEM.poch cLoc 1).im = (856993 / 10000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_0
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_2 : (HurwitzEM.poch cLoc 2).re = (-91786348103 / 12500000 : ℝ) ∧
    (HurwitzEM.poch cLoc 2).im = (2242750681 / 10000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_1
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_3 : (HurwitzEM.poch cLoc 3).re = (-3984277303540437 / 100000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 3).im = (-314326093014957691 / 500000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_2
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_4 : (HurwitzEM.poch cLoc 4).re = (134308277712820474383719 / 2500000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 4).im = (-363044975605497653643 / 62500000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_3
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_5 : (HurwitzEM.poch cLoc 5).re = (756131745799370501531205923 / 1000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 5).im = (114402973135863542616509550767 / 25000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_4
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_6 : (HurwitzEM.poch cLoc 6).re = (-12118068668156774261001795879940907 / 31250000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 6).im = (2284508702529263197834827619553967 / 25000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_5
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_7 : (HurwitzEM.poch cLoc 7).re = (-2617854930723824036150308244153034163707 / 250000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 7).im = (-40762696213460189352911927033766131634629 / 1250000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_6
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_8 : (HurwitzEM.poch cLoc 8).re = (16955634652367019527403033494112445042295152561 / 6250000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 8).im = (-90002324294106559666780833673992715149867317 / 78125000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_7
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_9 : (HurwitzEM.poch cLoc 9).re = (1532809206131217989230475352950195567260997568231633 / 12500000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 9).im = (13896631828800259061187836704486014749013564669273473 / 62500000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_8
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_10 : (HurwitzEM.poch cLoc 10).re = (-1394698530742764728907023983239622947090925886776835354083 / 78125000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 10).im = (158621698657558558024791455678274910110510318710866957941 / 12500000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_9
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_11 : (HurwitzEM.poch cLoc 11).re = (-800285219544450787165833069663222967190741027392729433830505909 / 625000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 11).im = (-4352371854342281274678129205699238161702812698999560463680285051 / 3125000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_10
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_12 : (HurwitzEM.poch cLoc 12).re = (1628721905909411150208923496111949394754292646127689022240691037695159 / 15625000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 12).im = (-49289299827316198144355134832555834249164378300040624697340252657569 / 390625000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_11
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_13 : (HurwitzEM.poch cLoc 13).re = (379647648478970910205504713724351984130973739135746730332721503478781128239 / 31250000000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 13).im = (1143274473575752180278206875902351286466496741900478461662763484001698382287 / 156250000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_12
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_14 : (HurwitzEM.poch cLoc 14).re = (-89707499154001387194315719153381002174894362311089850250723427800716255158358927 / 195312500000000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 14).im = (178464594174840132606244670210284407707350409072113255671885269284232989828272703 / 156250000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_13
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_15 : (HurwitzEM.poch cLoc 15).re = (-32714075193091001220151926654837001196000146887241549539503735124879587193600274785183 / 312500000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 15).im = (-175375148148034438078294134477203948210762050323051838812817239735098691134111151587269 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_14
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_16 : (HurwitzEM.poch cLoc 16).re = (10502579957166851997419296028637379918621760637881827762950742775943347036793916073418529121 / 39062500000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 16).im = (-2276929738574368544875464469504834188443725517996139317348194766376316807134571776947286837 / 244140625000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_15
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_17 : (HurwitzEM.poch cLoc 17).re = (62795076348822120379707929982254106501746824938373766907656922397375331321229599343564468719097169 / 78125000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 17).im = (-52234200112091345904638436495605174601730758076440711124980964865234096877251191023002387752550047 / 390625000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_16
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_18 : (HurwitzEM.poch cLoc 18).re = (12584831214320179417494405145265847272409870518994326968485153393554311722103999492983659668302902391937 / 488281250000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 18).im = (25977257680006878971740765423308961994730836167001580407677590935244417243248731179786534348201332564409 / 390625000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_17
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_19 : (HurwitzEM.poch cLoc 19).re = (-20368713607805806474037485629019955759365395082015147008022817627546588690341915284248536127697903481260585621 / 3906250000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 19).im = (67570111581136043235146440317842587589992155265090482261702186704086392148626479369712933364878875095177395589 / 19531250000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_18
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_20 : (HurwitzEM.poch cLoc 20).re = (-39040397904631793488633215015715481174739809270600269820161970619428969785129871939945126148721418929934438645841401 / 97656250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 20).im = (-184736498379805686034475129944984114419163860154803965551058037705353038546875672150051105507097537543378877150603 / 488281250000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_19
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_21 : (HurwitzEM.poch cLoc 21).re = (4707971198643131222053269292168639666687753117811265164874234505020169226988355035590853567542422308069434229513087085743 / 195312500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 21).im = (-41145526574556487832900996318883461248166135734302013668328450042239968508273129191298070351460093192964103108792204818193 / 976562500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_20
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_22 : (HurwitzEM.poch cLoc 22).re = (5049389718748665567523594963277735376749704294354504302133723818398246920143661355590282963262035686374312304403745746153623053 / 1220703125000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 22).im = (1120026964418171312786727327031369542306237632684689318634791422834184589959541135539632218444624118130916681678459721658513359 / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_21
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem poch_cLoc_23 : (HurwitzEM.poch cLoc 23).re = (-38503225116990379084140486415232659444884464365072262243049488133445035278423436137668282041016629248020662221725553434135047834683 / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (HurwitzEM.poch cLoc 23).im = (18586473323854893622219796385386854705192028381581435637798027513587950252343316803943318542858997455811374755454674541006137621676091 / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := poch_cLoc_22
  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_1 : (pochD cLoc 1).re = (1 : ℝ) ∧
    (pochD cLoc 1).im = (0 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_0
  obtain ⟨g1, g2⟩ := poch_cLoc_0
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_2 : (pochD cLoc 2).re = (2617 / 1000 : ℝ) ∧
    (pochD cLoc 2).im = (856993 / 5000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_1
  obtain ⟨g1, g2⟩ := poch_cLoc_1
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_3 : (pochD cLoc 3).re = (-275303725559 / 12500000 : ℝ) ∧
    (pochD cLoc 3).im = (9299231043 / 10000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_2
  obtain ⟨g1, g2⟩ := poch_cLoc_2
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_4 : (pochD cLoc 4).re = (-5085401780776437 / 25000000000 : ℝ) ∧
    (pochD cLoc 4).im = (-314072187413882691 / 125000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_3
  obtain ⟨g1, g2⟩ := poch_cLoc_3
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_5 : (pochD cLoc 5).re = (134035658896661052533719 / 500000000000000 : ℝ) ∧
    (pochD cLoc 5).im = (-441538292854712076393 / 12500000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_4
  obtain ⟨g1, g2⟩ := poch_cLoc_4
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_6 : (pochD cLoc 6).re = (2670192902434694040344774769 / 500000000000000000 : ℝ) ∧
    (pochD cLoc 6).im = (341805864955950789697599652301 / 12500000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_5
  obtain ⟨g1, g2⟩ := poch_cLoc_5
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_7 : (pochD cLoc 7).re = (-84213126551191394641475088147617599 / 31250000000000000000000 : ℝ) ∧
    (pochD cLoc 7).im = (18380562295815523849732989902984769 / 25000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_6
  obtain ⟨g1, g2⟩ := poch_cLoc_6
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_8 : (pochD cLoc 8).re = (-2953811717962685163396024783310879559707 / 31250000000000000000000000 : ℝ) ∧
    (pochD cLoc 8).im = (-40283338128632135115725820664807287409629 / 156250000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_7
  obtain ⟨g1, g2⟩ := poch_cLoc_7
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_9 : (pochD cLoc 9).re = (149842059720315514551973129549334435158120073049 / 6250000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 9).im = (-900269207650133502308778646117955362351721103 / 78125000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_8
  obtain ⟨g1, g2⟩ := poch_cLoc_8
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_10 : (pochD cLoc 10).re = (1681665143681202120690224644768052789932405541280633 / 1250000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 10).im = (13524599569610354525771042063600040820117487528073473 / 6250000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_9
  obtain ⟨g1, g2⟩ := poch_cLoc_9
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_11 : (pochD cLoc 11).re = (-14746790122849230853944633980192141514035583042401440051163 / 78125000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 11).im = (1892158224032610040825061760960824857121532068643944740351 / 12500000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_10
  obtain ⟨g1, g2⟩ := poch_cLoc_10
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_12 : (pochD cLoc 12).re = (-2575304188327916202765058880264878768908605036689802336730473727 / 156250000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 12).im = (-12329516972055933986691434647242494702631123878470251088034230153 / 781250000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_11
  obtain ⟨g1, g2⟩ := poch_cLoc_11
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_13 : (pochD cLoc 13).re = (19462763013155861752010603134613253948981615376847267480614901767487067 / 15625000000000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 13).im = (-680005024462531885967682781415868393649312792450709673718298188795647 / 390625000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_12
  obtain ⟨g1, g2⟩ := poch_cLoc_12
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_14 : (pochD cLoc 14).re = (2789613571023522526309800249822200318334821577261912999807893701637927366673 / 15625000000000000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 14).im = (7033393192196442495882565306585780071241741985364349474930860889215932876009 / 78125000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_13
  obtain ⟨g1, g2⟩ := poch_cLoc_13
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_15 : (pochD cLoc 15).re = (-216044955012545986305410815821289437929509568608177870884477864159971630668708031 / 39062500000000000000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 15).im = (555490380684056762079322650478262474697606165883013560303055764657586712312845109 / 31250000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_14
  obtain ⟨g1, g2⟩ := poch_cLoc_14
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_16 : (pochD cLoc 16).re = (-33505513523574345232554348619465089175662185245535126787457409410666380545383281909183 / 19531250000000000000000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 16).im = (-105186750625524566005138108132405428186685572286700652116133108789916572460504387962269 / 488281250000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_15
  obtain ⟨g1, g2⟩ := poch_cLoc_15
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_17 : (pochD cLoc 17).re = (-394697796334270516529829659890204321955676091555700913779314898972852582296195576243996004943 / 39062500000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 17).im = (-39053433676404619433577207522828158968179506639045249411599566024767989989647834420974769479 / 244140625000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_16
  obtain ⟨g1, g2⟩ := poch_cLoc_16
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_18 : (pochD cLoc 18).re = (559864871054680588052066602398749508601198713722562070594708682000553525171965265775191921427387521 / 39062500000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 18).im = (-751630183243994751484831133243173738731605534588667611480905386282002574753022130676279973821750423 / 195312500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_17
  obtain ⟨g1, g2⟩ := poch_cLoc_17
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_19 : (pochD cLoc 19).re = (305248012961924875937020560628343646898184151083065941369706268887640007085894531968306676246746469815553 / 488281250000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 19).im = (477503460516681409601640586473612033089531120041619307431771550533174693586462326702615960892769660686771 / 390625000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_18
  obtain ⟨g1, g2⟩ := poch_cLoc_18
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_20 : (pochD cLoc 20).re = (-19060689731416392324639424127557389589810024609300565427246220050776851611409874467007493696480291686173373621 / 195312500000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 20).im = (79344155897624288457771578171711710670377656779441550299690463130610351420712323991730576000950612795371670589 / 976562500000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_19
  obtain ⟨g1, g2⟩ := poch_cLoc_19
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_21 : (pochD cLoc 21).re = (-917326440994448111715173324415951792439910349975755202826414746279635597114046225109759457628153178819243302072919421 / 97656250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 21).im = (-3442939483130880259715133688088900042861902729606879082643508501672551888032175112535126521506140777619327668320413 / 488281250000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_20
  obtain ⟨g1, g2⟩ := poch_cLoc_20
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_22 : (pochD cLoc 22).re = (41359972640229793294967308495686449456565103810539137755035416885747956897439657341825551312989874622441659090637594312173 / 97656250000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 22).im = (-488729278328715581362008757601728394438064918824168818575904006509057706743065163835115385355558656333113046595650546000123 / 488281250000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_21
  obtain ⟨g1, g2⟩ := poch_cLoc_21
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num

theorem pochD_cLoc_23 : (pochD cLoc 23).re = (121550769023997419126669860961920545640790661167108255430160215706434748175049227649239893912795225019669706856800427461589448969 / 1220703125000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (pochD cLoc 23).im = (14270870507765603883029892441157142752355128240587947603758845381078298006868641821216278381053236514493443584187452627142978257 / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pochD_cLoc_22
  obtain ⟨g1, g2⟩ := poch_cLoc_22
  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cLoc_re, cLoc_im]
  norm_num


/-- `Q_x(s)` with real coefficients. -/
theorem QEM_eq_real (K : ℕ) (x : ℝ) (s : ℂ) :
    QEM K x s = (x : ℂ) / (s - 1) + 1 / 2 +
      ∑ k ∈ Finset.range K, (((bernoulli (2 * k + 2) : ℝ) / ((2 * k + 2)! : ℝ) / x ^ (2 * k + 1) : ℝ) : ℂ) *
        HurwitzEM.poch s (2 * k + 1) := by
  unfold QEM
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- `Q′_x(s)` with real coefficients. -/
theorem QEMd_eq_real (K : ℕ) (x : ℝ) (s : ℂ) :
    QEMd K x s = -(x : ℂ) / (s - 1) ^ 2 +
      ∑ k ∈ Finset.range K, (((bernoulli (2 * k + 2) : ℝ) / ((2 * k + 2)! : ℝ) / x ^ (2 * k + 1) : ℝ) : ℂ) *
        pochD s (2 * k + 1) := by
  unfold QEMd
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem QEM_cLoc_1 : (QEM 12 (20 + 1 / 5) cLoc).re = (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (QEM 12 (20 + 1 / 5) cLoc).im = (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  rw [QEM_eq_real]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  rw [(poch_cLoc_1).1, (poch_cLoc_1).2, (poch_cLoc_3).1, (poch_cLoc_3).2, (poch_cLoc_5).1, (poch_cLoc_5).2, (poch_cLoc_7).1, (poch_cLoc_7).2, (poch_cLoc_9).1, (poch_cLoc_9).2, (poch_cLoc_11).1, (poch_cLoc_11).2, (poch_cLoc_13).1, (poch_cLoc_13).2, (poch_cLoc_15).1, (poch_cLoc_15).2, (poch_cLoc_17).1, (poch_cLoc_17).2, (poch_cLoc_19).1, (poch_cLoc_19).2, (poch_cLoc_21).1, (poch_cLoc_21).2, (poch_cLoc_23).1, (poch_cLoc_23).2]
  simp only [bernoulli_2_eq, bernoulli_4_eq, bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq, bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, cLoc_re, cLoc_im]
  norm_num [Nat.factorial]

theorem QEMd_cLoc_1 : (QEMd 12 (20 + 1 / 5) cLoc).re = (4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (QEMd 12 (20 + 1 / 5) cLoc).im = (-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  rw [QEMd_eq_real]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  rw [(pochD_cLoc_1).1, (pochD_cLoc_1).2, (pochD_cLoc_3).1, (pochD_cLoc_3).2, (pochD_cLoc_5).1, (pochD_cLoc_5).2, (pochD_cLoc_7).1, (pochD_cLoc_7).2, (pochD_cLoc_9).1, (pochD_cLoc_9).2, (pochD_cLoc_11).1, (pochD_cLoc_11).2, (pochD_cLoc_13).1, (pochD_cLoc_13).2, (pochD_cLoc_15).1, (pochD_cLoc_15).2, (pochD_cLoc_17).1, (pochD_cLoc_17).2, (pochD_cLoc_19).1, (pochD_cLoc_19).2, (pochD_cLoc_21).1, (pochD_cLoc_21).2, (pochD_cLoc_23).1, (pochD_cLoc_23).2]
  simp only [bernoulli_2_eq, bernoulli_4_eq, bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq, bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.neg_re,
    Complex.neg_im, pow_two, Complex.mul_re, Complex.mul_im, cLoc_re, cLoc_im]
  norm_num [Nat.factorial]

theorem QEM_cLoc_2 : (QEM 12 (20 + 2 / 5) cLoc).re = (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (QEM 12 (20 + 2 / 5) cLoc).im = (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  rw [QEM_eq_real]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  rw [(poch_cLoc_1).1, (poch_cLoc_1).2, (poch_cLoc_3).1, (poch_cLoc_3).2, (poch_cLoc_5).1, (poch_cLoc_5).2, (poch_cLoc_7).1, (poch_cLoc_7).2, (poch_cLoc_9).1, (poch_cLoc_9).2, (poch_cLoc_11).1, (poch_cLoc_11).2, (poch_cLoc_13).1, (poch_cLoc_13).2, (poch_cLoc_15).1, (poch_cLoc_15).2, (poch_cLoc_17).1, (poch_cLoc_17).2, (poch_cLoc_19).1, (poch_cLoc_19).2, (poch_cLoc_21).1, (poch_cLoc_21).2, (poch_cLoc_23).1, (poch_cLoc_23).2]
  simp only [bernoulli_2_eq, bernoulli_4_eq, bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq, bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, cLoc_re, cLoc_im]
  norm_num [Nat.factorial]

theorem QEMd_cLoc_2 : (QEMd 12 (20 + 2 / 5) cLoc).re = (4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (QEMd 12 (20 + 2 / 5) cLoc).im = (-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  rw [QEMd_eq_real]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  rw [(pochD_cLoc_1).1, (pochD_cLoc_1).2, (pochD_cLoc_3).1, (pochD_cLoc_3).2, (pochD_cLoc_5).1, (pochD_cLoc_5).2, (pochD_cLoc_7).1, (pochD_cLoc_7).2, (pochD_cLoc_9).1, (pochD_cLoc_9).2, (pochD_cLoc_11).1, (pochD_cLoc_11).2, (pochD_cLoc_13).1, (pochD_cLoc_13).2, (pochD_cLoc_15).1, (pochD_cLoc_15).2, (pochD_cLoc_17).1, (pochD_cLoc_17).2, (pochD_cLoc_19).1, (pochD_cLoc_19).2, (pochD_cLoc_21).1, (pochD_cLoc_21).2, (pochD_cLoc_23).1, (pochD_cLoc_23).2]
  simp only [bernoulli_2_eq, bernoulli_4_eq, bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq, bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.neg_re,
    Complex.neg_im, pow_two, Complex.mul_re, Complex.mul_im, cLoc_re, cLoc_im]
  norm_num [Nat.factorial]

theorem QEM_cLoc_3 : (QEM 12 (20 + 3 / 5) cLoc).re = (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (QEM 12 (20 + 3 / 5) cLoc).im = (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  rw [QEM_eq_real]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  rw [(poch_cLoc_1).1, (poch_cLoc_1).2, (poch_cLoc_3).1, (poch_cLoc_3).2, (poch_cLoc_5).1, (poch_cLoc_5).2, (poch_cLoc_7).1, (poch_cLoc_7).2, (poch_cLoc_9).1, (poch_cLoc_9).2, (poch_cLoc_11).1, (poch_cLoc_11).2, (poch_cLoc_13).1, (poch_cLoc_13).2, (poch_cLoc_15).1, (poch_cLoc_15).2, (poch_cLoc_17).1, (poch_cLoc_17).2, (poch_cLoc_19).1, (poch_cLoc_19).2, (poch_cLoc_21).1, (poch_cLoc_21).2, (poch_cLoc_23).1, (poch_cLoc_23).2]
  simp only [bernoulli_2_eq, bernoulli_4_eq, bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq, bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, cLoc_re, cLoc_im]
  norm_num [Nat.factorial]

theorem QEMd_cLoc_3 : (QEMd 12 (20 + 3 / 5) cLoc).re = (58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (QEMd 12 (20 + 3 / 5) cLoc).im = (-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  rw [QEMd_eq_real]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  rw [(pochD_cLoc_1).1, (pochD_cLoc_1).2, (pochD_cLoc_3).1, (pochD_cLoc_3).2, (pochD_cLoc_5).1, (pochD_cLoc_5).2, (pochD_cLoc_7).1, (pochD_cLoc_7).2, (pochD_cLoc_9).1, (pochD_cLoc_9).2, (pochD_cLoc_11).1, (pochD_cLoc_11).2, (pochD_cLoc_13).1, (pochD_cLoc_13).2, (pochD_cLoc_15).1, (pochD_cLoc_15).2, (pochD_cLoc_17).1, (pochD_cLoc_17).2, (pochD_cLoc_19).1, (pochD_cLoc_19).2, (pochD_cLoc_21).1, (pochD_cLoc_21).2, (pochD_cLoc_23).1, (pochD_cLoc_23).2]
  simp only [bernoulli_2_eq, bernoulli_4_eq, bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq, bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.neg_re,
    Complex.neg_im, pow_two, Complex.mul_re, Complex.mul_im, cLoc_re, cLoc_im]
  norm_num [Nat.factorial]

theorem QEM_cLoc_4 : (QEM 12 (20 + 4 / 5) cLoc).re = (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (QEM 12 (20 + 4 / 5) cLoc).im = (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  rw [QEM_eq_real]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  rw [(poch_cLoc_1).1, (poch_cLoc_1).2, (poch_cLoc_3).1, (poch_cLoc_3).2, (poch_cLoc_5).1, (poch_cLoc_5).2, (poch_cLoc_7).1, (poch_cLoc_7).2, (poch_cLoc_9).1, (poch_cLoc_9).2, (poch_cLoc_11).1, (poch_cLoc_11).2, (poch_cLoc_13).1, (poch_cLoc_13).2, (poch_cLoc_15).1, (poch_cLoc_15).2, (poch_cLoc_17).1, (poch_cLoc_17).2, (poch_cLoc_19).1, (poch_cLoc_19).2, (poch_cLoc_21).1, (poch_cLoc_21).2, (poch_cLoc_23).1, (poch_cLoc_23).2]
  simp only [bernoulli_2_eq, bernoulli_4_eq, bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq, bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, cLoc_re, cLoc_im]
  norm_num [Nat.factorial]

theorem QEMd_cLoc_4 : (QEMd 12 (20 + 4 / 5) cLoc).re = (94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧
    (QEMd 12 (20 + 4 / 5) cLoc).im = (-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  rw [QEMd_eq_real]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  rw [(pochD_cLoc_1).1, (pochD_cLoc_1).2, (pochD_cLoc_3).1, (pochD_cLoc_3).2, (pochD_cLoc_5).1, (pochD_cLoc_5).2, (pochD_cLoc_7).1, (pochD_cLoc_7).2, (pochD_cLoc_9).1, (pochD_cLoc_9).2, (pochD_cLoc_11).1, (pochD_cLoc_11).2, (pochD_cLoc_13).1, (pochD_cLoc_13).2, (pochD_cLoc_15).1, (pochD_cLoc_15).2, (pochD_cLoc_17).1, (pochD_cLoc_17).2, (pochD_cLoc_19).1, (pochD_cLoc_19).2, (pochD_cLoc_21).1, (pochD_cLoc_21).2, (pochD_cLoc_23).1, (pochD_cLoc_23).2]
  simp only [bernoulli_2_eq, bernoulli_4_eq, bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq, bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.neg_re,
    Complex.neg_im, pow_two, Complex.mul_re, Complex.mul_im, cLoc_re, cLoc_im]
  norm_num [Nat.factorial]

/-! ## 11. The explicit Euler–Maclaurin main term, and the elementary certificate -/

/-- **`Q_x` for `K = 12` with the Bernoulli coefficients `B_{2k+2}/(2k+2)!` as rationals.** -/
theorem QEM_twelve (x : ℝ) (s : ℂ) :
    QEM 12 x s = (x : ℂ) / (s - 1) + 1 / 2 +
      (1 / 12 * HurwitzEM.poch s 1 / (x : ℂ) +
        -1 / 720 * HurwitzEM.poch s 3 / (x : ℂ) ^ 3 +
        1 / 30240 * HurwitzEM.poch s 5 / (x : ℂ) ^ 5 +
        -1 / 1209600 * HurwitzEM.poch s 7 / (x : ℂ) ^ 7 +
        1 / 47900160 * HurwitzEM.poch s 9 / (x : ℂ) ^ 9 +
        -691 / 1307674368000 * HurwitzEM.poch s 11 / (x : ℂ) ^ 11 +
        1 / 74724249600 * HurwitzEM.poch s 13 / (x : ℂ) ^ 13 +
        -3617 / 10670622842880000 * HurwitzEM.poch s 15 / (x : ℂ) ^ 15 +
        43867 / 5109094217170944000 * HurwitzEM.poch s 17 / (x : ℂ) ^ 17 +
        -174611 / 802857662698291200000 * HurwitzEM.poch s 19 / (x : ℂ) ^ 19 +
        77683 / 14101100039391805440000 * HurwitzEM.poch s 21 / (x : ℂ) ^ 21 +
        -236364091 / 1693824136731743669452800000 * HurwitzEM.poch s 23 / (x : ℂ) ^ 23) := by
  unfold QEM
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd,
    bernoulli_2_eq, bernoulli_4_eq, bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq,
    bernoulli_14_eq, bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq,
    bernoulli_24_eq]
  push_cast
  norm_num [Nat.factorial]

/-- **`EMmain_explicit`**: for `j = 1, …, 4`,
`5^{-s} EM_{20,12}(j/5, s) = Σ_{m<20} (5m+j)^{-s} + (100+j)^{-s} Q_{20+j/5}(s)`, with `Q` explicit by
`QEM_twelve` (every `s`; at `s = 1` both sides use Lean's `x/0 = 0`). -/
theorem EMmain_explicit {j : ℕ} (hj : 1 ≤ j) (s : ℂ) :
    (5 : ℂ) ^ (-s) * HurwitzEM.EMmain ((j : ℝ) / 5) 20 12 s =
      ∑ m ∈ Finset.range 20, ((5 * m + j : ℕ) : ℂ) ^ (-s) +
        ((100 + j : ℕ) : ℂ) ^ (-s) * QEM 12 (20 + (j : ℝ) / 5) s := by
  rw [five_cpow_mul_EMmain 20 12 hj s]
  simp only [nps, Nat.cast_ofNat]

theorem QD_re (K : ℕ) (x : ℝ) (N : ℕ) :
    (QD K x N).re = (QEMd K x cLoc).re - Real.log N * (QEM K x cLoc).re := by
  rw [QD, Complex.sub_re, Complex.re_ofReal_mul]

theorem QD_im (K : ℕ) (x : ℝ) (N : ℕ) :
    (QD K x N).im = (QEMd K x cLoc).im - Real.log N * (QEM K x cLoc).im := by
  rw [QD, Complex.sub_im, Complex.im_ofReal_mul]

/-- `a(1) = 2(1 + 2 sin(2π/5)/√5) ≤ 3.7014`. -/
theorem norm_aDH_one_le : ‖aDH chi5 1‖ ≤ 37014 / 10000 := by
  have h5 := sqrt_five_bounds
  have h2 := sin_two_pi_div_five_bounds
  have hs : 0 < Real.sqrt 5 := by linarith
  rw [aDH_chi5_eq 1]
  simp only [Nat.cast_one, chi5_apply_one, Complex.one_re, Complex.one_im, mul_one, mul_zero,
    add_zero, Complex.norm_real, Real.norm_eq_abs]
  have hq : 2 * Real.sin (2 * Real.pi / 5) / Real.sqrt 5 ≤ 850651 / 1000000 := by
    rw [div_le_iff₀ hs]; nlinarith
  have hq0 : 0 ≤ 2 * Real.sin (2 * Real.pi / 5) / Real.sqrt 5 := by
    apply div_nonneg _ hs.le; linarith
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- The four coefficient norms: `‖a(1)‖ = ‖a(4)‖ ≤ 3.7014`, `‖a(2)‖ = ‖a(3)‖ = κ‖a(1)‖ ≤ 1.0515`. -/
theorem norm_aDH_le : ‖aDH chi5 1‖ ≤ 37014 / 10000 ∧ ‖aDH chi5 2‖ ≤ 10515 / 10000 ∧
    ‖aDH chi5 3‖ ≤ 10515 / 10000 ∧ ‖aDH chi5 4‖ ≤ 37014 / 10000 := by
  have h1 := norm_aDH_one_le
  have hk := kappa_le
  have hk0 := kappa_pos
  have h0 := norm_nonneg (aDH chi5 1)
  rw [norm_aDH_two, norm_aDH_three, norm_aDH_four]
  refine ⟨h1, ?_, ?_, h1⟩ <;> nlinarith

/-- **The Euler–Maclaurin error on the ball, in `dh` units**: `‖dh z − dhEM 20 12 z‖ ≤ 6·10⁻⁵`. -/
theorem norm_dh_sub_dhEM_le_ball' {z : ℂ} (hz : z ∈ closedBall cLoc (1 / 100)) :
    ‖dh z - dhEM 20 12 z‖ ≤ 6 / 10 ^ 5 := by
  refine (norm_dh_sub_dhEM_le_ball hz).trans ?_
  have := norm_aDH_one_le
  nlinarith [norm_nonneg (aDH chi5 1)]

/-- **Stage 2, elementary form.** A zero of `dh` within `1/100` of `c` follows from four real
inequalities about explicit elementary expressions (`PRe`, `PIm`, `ARe`, `D2sum`: finite sums of
rationals, `κ`, `log n`, `exp(−σ log n)`, `cos(t log n)`, `sin(t log n)`, and the Gaussian-rational
values `QEM_cLoc_j`, `QEMd_cLoc_j`) and the margin. -/
theorem dh_zero_near_of_elementary {pr pi ar d₂ : ℝ}
    (hPr : |PRe 20 12| ≤ pr) (hPi : |PIm 20 12| ≤ pi) (hAr : ar ≤ |ARe 20 12|)
    (hD2 : D2sum (1597 / 2000) 20 ≤ d₂)
    (hmargin : 2 * (pr + pi + 16 / 10 ^ 6) < ar / 100 - (d₂ + 53 / 8) / 10 ^ 4) :
    ∃ ρ, dh ρ = 0 ∧ ‖ρ - cLoc‖ < 1 / 100 := by
  refine dh_zero_near_of_fEM (p₀ := pr + pi) (a₀ := ar) ?_ ?_ hD2 (by linarith)
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [fEM_cLoc_re, fEM_cLoc_im]
    linarith
  · refine hAr.trans ?_
    rw [← fEMd_cLoc_re]
    exact Complex.abs_re_le_norm _

/-! ## 12. The termwise second-derivative sum `D2sum(1597/2000, 20) ≤ 36`

Per term `log² n · n^{-1597/2000} ≤ (log n)_hi² · y_n`, with `(log n)_hi` from the pilot's `log_bound_n`
(`DHLogBounds`) and `n^{-1597/2000} ≤ n^{-79/100} ≤ y_n` (`ex_le_of`, `1 ≤ n^79 y_n^100`). -/

theorem D2term_le {n : ℕ} (hn : 1 ≤ n) {hi y c : ℝ} (hl : Real.log n ≤ hi)
    (he : ex (1597 / 2000) n ≤ y) (hc : hi ^ 2 * y ≤ c) :
    Real.log n ^ 2 * ex (1597 / 2000) n ≤ c := by
  have h0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hx : 0 ≤ ex (1597 / 2000) n := (Real.exp_pos _).le
  calc Real.log n ^ 2 * ex (1597 / 2000) n ≤ hi ^ 2 * y :=
        mul_le_mul (pow_le_pow_left₀ h0 hl 2) he hx (by nlinarith)
    _ ≤ c := hc

theorem D2t_2 : Real.log 2 ^ 2 * ex (1597 / 2000) 2 ≤ (69467 / 250000 : ℝ) := by
  have h := D2term_le (n := 2) (hi := (574418000082871 / 828710000000000 : ℝ)) (y := (115669 / 200000 : ℝ)) (c := (69467 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_2).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_3 : Real.log 3 ^ 2 * ex (1597 / 2000) 3 ≤ (101343 / 200000 : ℝ) := by
  have h := D2term_le (n := 3) (hi := (1025259098474119453547 / 933231048750000000000 : ℝ)) (y := (419831 / 1000000 : ℝ)) (c := (101343 / 200000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_3).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_4 : Real.log 4 ^ 2 * ex (1597 / 2000) 4 ≤ (160703 / 250000 : ℝ) := by
  have h := D2term_le (n := 4) (hi := (121815844852038337805060919401 / 87871557623395796250000000000 : ℝ)) (y := (167241 / 500000 : ℝ)) (c := (160703 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_4).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_6 : Real.log 6 ^ 2 * ex (1597 / 2000) 6 ≤ (779509 / 1000000 : ℝ) := by
  have h := D2term_le (n := 6) (hi := (39225939500696939046754813626219140162395322227 / 21892413668788546283777010022137498750000000000 : ℝ)) (y := (242807 / 1000000 : ℝ)) (c := (779509 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_6).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_7 : Real.log 7 ^ 2 * ex (1597 / 2000) 7 ≤ (813991 / 1000000 : ℝ) := by
  have h := D2term_le (n := 7) (hi := (34750675214067554123969486052317847397694564474758035667 / 17858314386471136056607290988582447816474098750000000000 : ℝ)) (y := (26871 / 125000 : ℝ)) (c := (813991 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_7).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_8 : Real.log 8 ^ 2 * ex (1597 / 2000) 8 ≤ (209119 / 250000 : ℝ) := by
  have h := D2term_le (n := 8) (hi := (37135320804849204391149650347142524374154147886161035667 / 17858314386471136056607290988582447816474098750000000000 : ℝ)) (y := (96723 / 500000 : ℝ)) (c := (209119 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_8).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_9 : Real.log 9 ^ 2 * ex (1597 / 2000) 9 ≤ (425469 / 500000 : ℝ) := by
  have h := D2term_le (n := 9) (hi := (16101167284443510245472688931511908629523911287639379236777449891 / 7327957027361375122270688666379779788103729219945958750000000000 : ℝ)) (y := (88129 / 500000 : ℝ)) (c := (425469 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_9).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_11 : Real.log 11 ^ 2 * ex (1597 / 2000) 11 ≤ (864889 / 1000000 : ℝ) := by
  have h := D2term_le (n := 11) (hi := (15706822364226006743706670649674293886702007132724044758483916015053530449 / 6550253691364782961975438106944484593629331950218207633884766250000000000 : ℝ)) (y := (75209 / 500000 : ℝ)) (c := (864889 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_11).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_12 : Real.log 12 ^ 2 * ex (1597 / 2000) 12 ≤ (867097 / 1000000 : ℝ) := by
  have h := D2term_le (n := 12) (hi := (55419557141604335280931300882221567412105462129685771110940595791866242321194535703 / 22302470452664497188566005055498088560688603509713090554580511593646763750000000000 : ℝ)) (y := (70213 / 500000 : ℝ)) (c := (867097 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_12).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_13 : Real.log 13 ^ 2 * ex (1597 / 2000) 13 ≤ (867253 / 1000000 : ℝ) := by
  have h := D2term_le (n := 13) (hi := (286023536322275269872705655821131543329696821141282081016369185172406533960424507891 / 111512352263322485942830025277490442803443017548565452772902557968233818750000000000 : ℝ)) (y := (65911 / 500000 : ℝ)) (c := (867253 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_13).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_14 : Real.log 14 ^ 2 * ex (1597 / 2000) 14 ≤ (216471 / 250000 : ℝ) := by
  have h := D2term_le (n := 14) (hi := (294287490618627631273015842231878826681508693420419269834899284283963358647924507891 / 111512352263322485942830025277490442803443017548565452772902557968233818750000000000 : ℝ)) (y := (62163 / 500000 : ℝ)) (c := (216471 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_14).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_16 : Real.log 16 ^ 2 * ex (1597 / 2000) 16 ≤ (430021 / 500000 : ℝ) := by
  have h := D2term_le (n := 16) (hi := (152687288908253845811036601602936835221677789848504837661872629396471435750763258705127301771623753169 / 55070298621120717868545120379262723461019259358442945233082636038488603182475872208042806250000000000 : ℝ)) (y := (111879 / 1000000 : ℝ)) (c := (430021 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_16).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_17 : Real.log 17 ^ 2 * ex (1597 / 2000) 17 ≤ (428033 / 500000 : ℝ) := by
  have h := D2term_le (n := 17) (hi := (156025904937694683530059073222626949626391521301448564616053231391741848300055701494291787591936253169 / 55070298621120717868545120379262723461019259358442945233082636038488603182475872208042806250000000000 : ℝ)) (y := (106647 / 1000000 : ℝ)) (c := (428033 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_17).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_18 : Real.log 18 ^ 2 * ex (1597 / 2000) 18 ≤ (26613 / 31250 : ℝ) := by
  have h := D2term_le (n := 18) (hi := (159173635858038814420497469890463301379604908784639991045216817867387531073497970424711915637036253169 / 55070298621120717868545120379262723461019259358442945233082636038488603182475872208042806250000000000 : ℝ)) (y := (50969 / 500000 : ℝ)) (c := (26613 / 31250 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_18).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_19 : Real.log 19 ^ 2 * ex (1597 / 2000) 19 ≤ (423409 / 500000 : ℝ) := by
  have h := D2term_le (n := 19) (hi := (11244201255276124560058897686376300948691677946312769351816355551183245942199319174098778239952746734692249733 / 3818792419560154351685524480139417987383810697123715181196237290899604044075670035932015410759331250000000000 : ℝ)) (y := (976753 / 10000000 : ℝ)) (c := (423409 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_19).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_21 : Real.log 21 ^ 2 * ex (1597 / 2000) 21 ≤ (418269 / 500000 : ℝ) := by
  have h := D2term_le (n := 21) (hi := (1346990443573576049865422256229308902137906461232996118497467535493769747722359916488835536525692356189253020708644333 / 442430782137837574159902812961452918369354236271915267899422688018159996950843686892616799764030643925581250000000000 : ℝ)) (y := (361 / 4000 : ℝ)) (c := (418269 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_21).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_22 : Real.log 22 ^ 2 * ex (1597 / 2000) 22 ≤ (831183 / 1000000 : ℝ) := by
  have h := D2term_le (n := 22) (hi := (201044678993566596127931630161525904057146531189633253722542162933239541453594787284043764396017045454965815677499247535103519 / 65041060417355713164144345564783412547284865189788388161822009964424456876628277946463103928952912367787107432493750000000000 : ℝ)) (y := (434967 / 5000000 : ℝ)) (c := (831183 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_22).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_23 : Real.log 23 ^ 2 * ex (1597 / 2000) 23 ≤ (206437 / 250000 : ℝ) := by
  have h := D2term_le (n := 23) (hi := (203935868768892693232583237376176531034857034246303750533331102109988214509886901278050978186709177316860688637112761835103519 / 65041060417355713164144345564783412547284865189788388161822009964424456876628277946463103928952912367787107432493750000000000 : ℝ)) (y := (167983 / 2000000 : ℝ)) (c := (206437 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_23).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_24 : Real.log 24 ^ 2 * ex (1597 / 2000) 24 ≤ (820269 / 1000000 : ℝ) := by
  have h := D2term_le (n := 24) (hi := (47406528313706601062669804956026802455569352928908131154382491543400226000791984314211016974921448187333736630290993236359821285779633 / 14916842456705868957120677082565670704140935237946074211491786008044996813341510542029526195827433189660520728615031121206250000000000 : ℝ)) (y := (162429 / 2000000 : ℝ)) (c := (820269 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_24).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_26 : Real.log 26 ^ 2 * ex (1597 / 2000) 26 ≤ (404641 / 500000 : ℝ) := by
  have h := D2term_le (n := 26) (hi := (48600512773947132551998434052624611838371965708147260720940108461339773523424275754499854439066195100361096949099210085807680660779633 / 14916842456705868957120677082565670704140935237946074211491786008044996813341510542029526195827433189660520728615031121206250000000000 : ℝ)) (y := (38119 / 500000 : ℝ)) (c := (404641 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_26).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_27 : Real.log 27 ^ 2 * ex (1597 / 2000) 27 ≤ (200953 / 250000 : ℝ) := by
  have h := D2term_le (n := 27) (hi := (20559945463773882722245902668640926675287846874283792876094531009985680314024847147983482937092038568845939078404265740660879661602241886794069 / 6238156285185442024516477413037352364993875553313930812289393715084879408538781978488734928020467965674643968739882146943190473431250000000000 : ℝ)) (y := (147997 / 2000000 : ℝ)) (c := (200953 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_27).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_28 : Real.log 28 ^ 2 * ex (1597 / 2000) 28 ≤ (399189 / 500000 : ℝ) := by
  have h := D2term_le (n := 28) (hi := (20786812511842840039479632328715542778730926283285486911584580291357642889772467509428334888708386774839257876350040858058973695370603836794069 / 6238156285185442024516477413037352364993875553313930812289393715084879408538781978488734928020467965674643968739882146943190473431250000000000 : ℝ)) (y := (719027 / 10000000 : ℝ)) (c := (399189 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_28).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_29 : Real.log 29 ^ 2 * ex (1597 / 2000) 29 ≤ (24781 / 31250 : ℝ) := by
  have h := D2term_le (n := 29) (hi := (21005717649084439154313425191659788333472319124221455650194125493203969972915473196651137482170022408117377420490816590975392658893572586794069 / 6238156285185442024516477413037352364993875553313930812289393715084879408538781978488734928020467965674643968739882146943190473431250000000000 : ℝ)) (y := (87421 / 1250000 : ℝ)) (c := (24781 / 31250 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_29).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_31 : Real.log 31 ^ 2 * ex (1597 / 2000) 31 ≤ (195597 / 250000 : ℝ) := by
  have h := D2term_le (n := 31) (hi := (12934932207330736945821211369375099338401234142520044334307084652361179021500862718402310752557765085834775100448640202032205685974453387864654193731124004047931 / 3766738614667585927361145972505489979996854208991687179073685747846600411472307091205457963076757252285183375322912993064707205484934142012641289068750000000000 : ℝ)) (y := (26539 / 400000 : ℝ)) (c := (195597 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_31).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_32 : Real.log 32 ^ 2 * ex (1597 / 2000) 32 ≤ (388591 / 500000 : ℝ) := by
  have h := D2term_le (n := 32) (hi := (13054521255239338022217312807596671652833120815263748848742923731754608519811698830446899872496537393169628883554318524877897001046320585717642582093448222797931 / 3766738614667585927361145972505489979996854208991687179073685747846600411472307091205457963076757252285183375322912993064707205484934142012641289068750000000000 : ℝ)) (y := (647041 / 10000000 : ℝ)) (c := (388591 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_32).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_33 : Real.log 33 ^ 2 * ex (1597 / 2000) 33 ≤ (386023 / 500000 : ℝ) := by
  have h := D2term_le (n := 33) (hi := (13170430050178087158439552927388507968008728037842767470877693728243990395252316005512988691537587221918658536265792733191010112750150617286536734240020041547931 / 3766738614667585927361145972505489979996854208991687179073685747846600411472307091205457963076757252285183375322912993064707205484934142012641289068750000000000 : ℝ)) (y := (631501 / 10000000 : ℝ)) (c := (386023 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_33).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_34 : Real.log 34 ^ 2 * ex (1597 / 2000) 34 ≤ (383491 / 500000 : ℝ) := by
  have h := D2term_le (n := 34) (hi := (17933547566033251281443367970025380355049722937602764317373841006036806599879952483816310810031744525090633324940174609614187887743822273731230025172758384096732287003617 / 5085568375169106219610161433771593717330680648578302014757388131195766400125292639050627691383008934454559199122469064313178073729017695372770515756564024106250000000000 : ℝ)) (y := (308391 / 5000000 : ℝ)) (c := (383491 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_34).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_36 : Real.log 36 ^ 2 * ex (1597 / 2000) 36 ≤ (757079 / 1000000 : ℝ) := by
  have h := D2term_le (n := 36) (hi := (32880691725963262472433529678172431395401089220851056155277127587779904983960641126503323411239562500851832042054084490938516947648630291860464411831073630471737133437687884562567 / 9175531728997481029857305036658952014855211398972688916767714810402440466045663056839391255766594502238150882823812129423342536711535746389929450715400783203167792543750000000000 : ℝ)) (y := (589551 / 10000000 : ℝ)) (c := (757079 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_36).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_37 : Real.log 37 ^ 2 * ex (1597 / 2000) 37 ≤ (9403 / 12500 : ℝ) := by
  have h := D2term_le (n := 37) (hi := (68685198499250393814546166759436103943389013311472877279300755800431997626156550988127130767041050907626678296095804137730459881091245583074542730739419724836257703795686498594264628859231 / 19021534178054852291553563915033497051146452759220070776177090952970680228032945123983286375742324500939885516029916549476370883965244391245015045552190891268438698334965334693750000000000 : ℝ)) (y := (576927 / 10000000 : ℝ)) (c := (9403 / 12500 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_37).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_38 : Real.log 38 ^ 2 * ex (1597 / 2000) 38 ≤ (373739 / 500000 : ℝ) := by
  have h := D2term_le (n := 38) (hi := (69192469472594980365626293002875214648662796737807410965098958700245577393920406935206487702400346720649639375490790340724148848074464232303946072012862644942278242577103819666379020891231 / 19021534178054852291553563915033497051146452759220070776177090952970680228032945123983286375742324500939885516029916549476370883965244391245015045552190891268438698334965334693750000000000 : ℝ)) (y := (5649 / 100000 : ℝ)) (c := (373739 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_38).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_39 : Real.log 39 ^ 2 * ex (1597 / 2000) 39 ≤ (742791 / 1000000 : ℝ) := by
  have h := D2term_le (n := 39) (hi := (69686563075008234292739649669519490378166403068727642888362732826792761051524565402385521213318873278035823144845136712950026837085637412863076650794234390337258331710645503772316520891231 / 19021534178054852291553563915033497051146452759220070776177090952970680228032945123983286375742324500939885516029916549476370883965244391245015045552190891268438698334965334693750000000000 : ℝ)) (y := (276713 / 5000000 : ℝ)) (c := (742791 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_39).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_41 : Real.log 41 ^ 2 * ex (1597 / 2000) 41 ≤ (733643 / 1000000 : ℝ) := by
  have h := D2term_le (n := 41) (hi := (917116503911644095958057450499787062143590079414364795115884064015271892100214679919597515897785201724376273680077084540976115588331582931370339442807342993927537772093934097983680037898463213237 / 246963432326501639733015643443077275951805159278098417852610187654191728502327227749234682327119991479964372326697349341781717838829290074596342290158841647455960014560488306171224231250000000000 : ℝ)) (y := (531987 / 10000000 : ℝ)) (c := (733643 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_41).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_42 : Real.log 42 ^ 2 * ex (1597 / 2000) 42 ≤ (729181 / 1000000 : ℝ) := by
  have h := D2term_le (n := 42) (hi := (3636001257286840970938213665185256882060967062880833519623280151724278766473627211956269457205017562349889890595467592208363460841532019108264785966264056899587987187844052064844362697689634410743418591391 / 972798997268870004914492288477077846963887031613518207675428312805718047885088470189752825831719467577393382786845333017647484601506697142671494100075376175130104049936635219934679963960180693750000000000 : ℝ)) (y := (104391 / 2000000 : ℝ)) (c := (729181 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_42).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_43 : Real.log 43 ^ 2 * ex (1597 / 2000) 43 ≤ (90599 / 125000 : ℝ) := by
  have h := D2term_le (n := 43) (hi := (3658891701572767578911461388414422988759988290085273201805578344181285828335752451398879269140002907148322257398414777103793154989442718859419504015396578948627714619252515545141448149918812858462318591391 / 972798997268870004914492288477077846963887031613518207675428312805718047885088470189752825831719467577393382786845333017647484601506697142671494100075376175130104049936635219934679963960180693750000000000 : ℝ)) (y := (256171 / 5000000 : ℝ)) (c := (90599 / 125000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_43).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_44 : Real.log 44 ^ 2 * ex (1597 / 2000) 44 ≤ (360237 / 500000 : ℝ) := by
  have h := D2term_le (n := 44) (hi := (3681255881849493136201310497453791087516459738339359912927857475937635732708293113183012048959345340796353337661421042186556116455551953507051736354798610960029825845405291410392984604541884129243568591391 / 972798997268870004914492288477077846963887031613518207675428312805718047885088470189752825831719467577393382786845333017647484601506697142671494100075376175130104049936635219934679963960180693750000000000 : ℝ)) (y := (503121 / 10000000 : ℝ)) (c := (360237 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_44).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_46 : Real.log 46 ^ 2 * ex (1597 / 2000) 46 ≤ (178013 / 250000 : ℝ) := by
  have h := D2term_le (n := 46) (hi := (20797821108191252707673497234186913340741380699856552286885597233733802782011815762430040313714459560716579799174682641594713349037304374751784389317234218739105324053267969799600363574852347904182880109455283603559 / 5432167432676958744495447100508060371247269340650028063703519795244897566522562738164044090060064376842792657940957634738746120140125471816316057732473655942964736324401835751142442815542826462682062743750000000000 : ℝ)) (y := (759 / 15625 : ℝ)) (c := (178013 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_46).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_47 : Real.log 47 ^ 2 * ex (1597 / 2000) 47 ≤ (707943 / 1000000 : ℝ) := by
  have h := D2term_le (n := 47) (hi := (20914646415793193064743127841156617301868081514334917788339133675747627999630413520591036690283343410521006641124852232985502089578278675723733232575515977655325999300988076846205421116061598206306433384142783603559 / 5432167432676958744495447100508060371247269340650028063703519795244897566522562738164044090060064376842792657940957634738746120140125471816316057732473655942964736324401835751142442815542826462682062743750000000000 : ℝ)) (y := (477577 / 10000000 : ℝ)) (c := (707943 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_47).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_48 : Real.log 48 ^ 2 * ex (1597 / 2000) 48 ≤ (703901 / 1000000 : ℝ) := by
  have h := D2term_le (n := 48) (hi := (21029012059584612813471019933022401840958036396411888171820396129190647009828307538475854421388705240568414922139931531912282765747990794197592565102009267685620439558530634020119427041003250007024726089186646103559 / 5432167432676958744495447100508060371247269340650028063703519795244897566522562738164044090060064376842792657940957634738746120140125471816316057732473655942964736324401835751142442815542826462682062743750000000000 : ℝ)) (y := (469699 / 10000000 : ℝ)) (c := (703901 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_48).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_49 : Real.log 49 ^ 2 * ex (1597 / 2000) 49 ≤ (27997 / 40000 : ℝ) := by
  have h := D2term_le (n := 49) (hi := (181545127654732046912283855353454048472915677343934322756333553116175157052529106828006261716835726092064065980263674287737304716172586807721628252540302957080391710682867894347020452004377380516957773194131603784443454174663 / 46647870077391185102933930039406791978998041310285832539620996050302906046840538500244246084495724371273731951840416225923536235181857945159369792001607161870988376169926095590487332931231338990554585591204250143750000000000 : ℝ)) (y := (46211 / 1000000 : ℝ)) (c := (27997 / 40000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_49).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_51 : Real.log 51 ^ 2 * ex (1597 / 2000) 51 ≤ (173041 / 250000 : ℝ) := by
  have h := D2term_le (n := 51) (hi := (1927671104646308048183768022287365015132284175949336820585574054963845811706425206901338875794099034927912817001465938747485773863143281625219086126585652772543828101125169298893659199185051335109800790686189172250884542980171137806163 / 490273802670972003323329634677068274121270095453253825027872732938407594044654673158526839395025801046881960195177666448127487373076499015530322975760357224785463029748716718398554808674688294471528584289963170629156197018750000000000 : ℝ)) (y := (223867 / 5000000 : ℝ)) (c := (173041 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_51).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_52 : Real.log 52 ^ 2 * ex (1597 / 2000) 52 ≤ (86047 / 125000 : ℝ) := by
  have h := D2term_le (n := 52) (hi := (22457356318520131665601580730089974450020527960411786871245692450068498018155884342659964921021859674516217130229961774517437240939819000337222723876013561719922816027108745731690660554691254425293762715898288779317230216182731952082079696599109 / 5683617087449319366338694858340155029198340358468434669321213341753835825022072390890202588913733075332400553066340365956871618928081971393137764913046094604004846699088169353344184042841628824145271072587365774122079988890198259931250000000000 : ℝ)) (y := (220459 / 5000000 : ℝ)) (c := (86047 / 125000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_52).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_53 : Real.log 53 ^ 2 * ex (1597 / 2000) 53 ≤ (684649 / 1000000 : ℝ) := by
  have h := D2term_le (n := 53) (hi := (22565618964940706245692228393081079373913275091038090170471927234284598149641198688287905168970647679551067501713656611073391325380773310335645546482366006394847797901132740641375953568120630983305507169082017148516435386304162377070231146599109 / 5683617087449319366338694858340155029198340358468434669321213341753835825022072390890202588913733075332400553066340365956871618928081971393137764913046094604004846699088169353344184042841628824145271072587365774122079988890198259931250000000000 : ℝ)) (y := (434333 / 10000000 : ℝ)) (c := (684649 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_53).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_54 : Real.log 54 ^ 2 * ex (1597 / 2000) 54 ≤ (34049 / 50000 : ℝ) := by
  have h := D2term_le (n := 54) (hi := (317984535239491708709750350434008398040384944822715773897635712590950298039036994133868392056817769924824111189341447026151161308647597785040507787609394917575040875941976247047603441617158702735963889496947200624580725181106963399606593346068444970279463 / 79715669826381361257953637959441757655084413033375614467763499667007730097483699975437405547545769578052918734888328721880816506852922478089132622823225349957229288889942940384275851620668494533119558910780551934488685615017843417327031505143750000000000 : ℝ)) (y := (213983 / 5000000 : ℝ)) (c := (34049 / 50000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_54).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_56 : Real.log 56 ^ 2 * ex (1597 / 2000) 56 ≤ (673813 / 1000000 : ℝ) := by
  have h := D2term_le (n := 56) (hi := (4937192034718615698733193232403654556256228184119752587768197319842898674455988184601138103846636599881856136399288112290893715170626426302033889067850007131831147210710175696372312305712919523513342174785291463483908324287794904718686805047129250093646893818082187 / 1226524391757694864143582655179990429594733296747574936296079344155162667314621329944925337809600719769478860653621849479115240602152465358606098308388809915251286743179586377693894365931585336403774447658487090634478271702814930728366484011211763180168750000000000 : ℝ)) (y := (83169 / 2000000 : ℝ)) (c := (673813 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_56).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_57 : Real.log 57 ^ 2 * ex (1597 / 2000) 57 ≤ (670313 / 1000000 : ℝ) := by
  have h := D2term_le (n := 57) (hi := (91364536489293797448304893038358801036347970693896573515188011003150916936019945823171360376060017874450282471702027346876790121523742878827965147161705099103442704539696766066424947925553909260835833525736130209327213537336955849187264476259467655345198976068501360999811291 / 22597916876439119791730708502409157409226564679287983345948530243355435359744805995486829738923447713898888392959154874394512999241894174789204655348897636903196222952257942798862877866104202408103389916684231279998703252867299432112349825653075281051233491105068750000000000 : ℝ)) (y := (410071 / 10000000 : ℝ)) (c := (670313 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_57).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_58 : Real.log 58 ^ 2 * ex (1597 / 2000) 58 ≤ (166717 / 250000 : ℝ) := by
  have h := D2term_le (n := 58) (hi := (91757553647230804185086088238275310635241229982828983266867221768393272608253308288183480471490893570141456985343995484198441121524829839159902073519458491223801303999700891180339153080756531185537134066547334843835485093484873973959999146855649113150395835100009473499811291 / 22597916876439119791730708502409157409226564679287983345948530243355435359744805995486829738923447713898888392959154874394512999241894174789204655348897636903196222952257942798862877866104202408103389916684231279998703252867299432112349825653075281051233491105068750000000000 : ℝ)) (y := (101119 / 2500000 : ℝ)) (c := (166717 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_58).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_59 : Real.log 59 ^ 2 * ex (1597 / 2000) 59 ≤ (663473 / 1000000 : ℝ) := by
  have h := D2term_le (n := 59) (hi := (92143852232983371099558008593426118662527091666560178046973323213560080434513659681989261459937829247016510487878554126029737925199430634735004990324381860168987224034648768610003784754184688966994770376026737546794239319889213200695067056047027318260501894978498535999811291 / 22597916876439119791730708502409157409226564679287983345948530243355435359744805995486829738923447713898888392959154874394512999241894174789204655348897636903196222952257942798862877866104202408103389916684231279998703252867299432112349825653075281051233491105068750000000000 : ℝ)) (y := (7981 / 200000 : ℝ)) (c := (663473 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_59).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_61 : Real.log 61 ^ 2 * ex (1597 / 2000) 61 ≤ (328419 / 500000 : ℝ) := by
  have h := D2term_le (n := 61) (hi := (92897185890057806466520519800560458984078785060028871208700892043246112139723008226209272959781611508584738545438866919344429417984715370052561565636898343203379950488995842664772937583829546568579818138768167390918578972094961785078926241899361095665327514208791348499811291 / 22597916876439119791730708502409157409226564679287983345948530243355435359744805995486829738923447713898888392959154874394512999241894174789204655348897636903196222952257942798862877866104202408103389916684231279998703252867299432112349825653075281051233491105068750000000000 : ℝ)) (y := (194339 / 5000000 : ℝ)) (c := (328419 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_61).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_62 : Real.log 62 ^ 2 * ex (1597 / 2000) 62 ≤ (130719 / 200000 : ℝ) := by
  have h := D2term_le (n := 62) (hi := (93264639790370281370005218692409374356536584537814806153281904826860492898864213894694172132377548440375961780463807390006369517702597732600107004189697287426914669365560720114820977082390441838890153762430151625851686274357595161548742856920834837634163570595521035999811291 / 22597916876439119791730708502409157409226564679287983345948530243355435359744805995486829738923447713898888392959154874394512999241894174789204655348897636903196222952257942798862877866104202408103389916684231279998703252867299432112349825653075281051233491105068750000000000 : ℝ)) (y := (383717 / 10000000 : ℝ)) (c := (130719 / 200000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_62).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_63 : Real.log 63 ^ 2 * ex (1597 / 2000) 63 ≤ (650399 / 1000000 : ℝ) := by
  have h := D2term_le (n := 63) (hi := (93626214175296672980239729985454247243906800927844936183090236394151228926434384236893793002073698968205210424608621242447491153386490195326803315568153363487410458436067736018797804647665181776195621625137771998653516218515807464893483085863732047169001632859772879106211291 / 22597916876439119791730708502409157409226564679287983345948530243355435359744805995486829738923447713898888392959154874394512999241894174789204655348897636903196222952257942798862877866104202408103389916684231279998703252867299432112349825653075281051233491105068750000000000 : ℝ)) (y := (378897 / 10000000 : ℝ)) (c := (650399 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_63).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_64 : Real.log 64 ^ 2 * ex (1597 / 2000) 64 ≤ (647251 / 1000000 : ℝ) := by
  have h := D2term_le (n := 64) (hi := (192511324141717136682828998435358350842393529569284028643034470300676123911001876127486459644472063434708225141227468457017618773572904935780844621108799494998544691676730316673406960768898162954429518681641178950354580774152367946007097673627208649822116758265876791479493793517453 / 46289188765110993516344723874290377081383738237453957190124088225475136748500144939453298761105228598539346703034852539076855720926108915437235399537540988172679788759614981644163138352004124441318046147707395722017583765218077412648591472920723303425568812210274041331250000000000 : ℝ)) (y := (374213 / 10000000 : ℝ)) (c := (647251 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_64).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_66 : Real.log 66 ^ 2 * ex (1597 / 2000) 66 ≤ (641087 / 1000000 : ℝ) := by
  have h := D2term_le (n := 66) (hi := (435985145052218607407330760387624809261601015550728127397875953436339409124031045420425748638615851459098862230670077398798130092592718628611042961578163503120367873586218773066331638864364770802263758299489009626361332476650823738764421767295592818747520030565444169639780618510491307223 / 104062308660147138525152926639277328103265049477976104073503251622896625648072439337080505865151814465318918468972324679425827654512497117814209966581750057642107878992391603699408353860895304119407127682245666956106231904332872868678584652949821771921290416610607179850411143750000000000 : ℝ)) (y := (14609 / 400000 : ℝ)) (c := (641087 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_66).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_67 : Real.log 67 ^ 2 * ex (1597 / 2000) 67 ≤ (638073 / 1000000 : ℝ) := by
  have h := D2term_le (n := 67) (hi := (437550021292121982114774111144476635035650930317737762342714221048034379077840595010973891548913529886349282502558720479729429201419292354342270636434471220070101623326391487988670211412368129262298930174643012097585568961676591636319820348960959367330890871189219957223605620072991307223 / 104062308660147138525152926639277328103265049477976104073503251622896625648072439337080505865151814465318918468972324679425827654512497117814209966581750057642107878992391603699408353860895304119407127682245666956106231904332872868678584652949821771921290416610607179850411143750000000000 : ℝ)) (y := (22557 / 625000 : ℝ)) (c := (638073 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_67).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_68 : Real.log 68 ^ 2 * ex (1597 / 2000) 68 ≤ (635101 / 1000000 : ℝ) := by
  have h := D2term_le (n := 68) (hi := (439091713325635231931456148055765444043461811276244309535922596358182774074177594268476431614112298374350973912480598059483139560615470690726419378344330880441045103465916215224865825185368325377104818192681041533131782732060632929469760016078459830896474573943994727110330002766741307223 / 104062308660147138525152926639277328103265049477976104073503251622896625648072439337080505865151814465318918468972324679425827654512497117814209966581750057642107878992391603699408353860895304119407127682245666956106231904332872868678584652949821771921290416610607179850411143750000000000 : ℝ)) (y := (356713 / 10000000 : ℝ)) (c := (635101 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_68).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_69 : Real.log 69 ^ 2 * ex (1597 / 2000) 69 ≤ (632169 / 1000000 : ℝ) := by
  have h := D2term_le (n := 69) (hi := (1132966154663458507746634054714543699264892167818622305112561875916327056437965223378480194733475619685596721254308871300593416380534122358079814059476562772967890077875617322434925442144547498617084267870481042535449481557413015794787735738722264258236645352175496029122657584725189654301782719 / 267580929560195325088067553372685675450314894770342289137714806570290107050048011106719969997875713580841196961947393981415640216913673001382922240199882755968207020970723127347284768925274722933349875987125442464584627725902045649495284683116483062695125876622934603729894245714993750000000000 : ℝ)) (y := (176311 / 5000000 : ℝ)) (c := (632169 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_69).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_71 : Real.log 71 ^ 2 * ex (1597 / 2000) 71 ≤ (62643 / 100000 : ℝ) := by
  have h := D2term_le (n := 71) (hi := (3063248840512338978011208837881075282715619260101033204649697809533993357866108630645090319334059200255400897381903952882112700715274121091678328573477738719233574521295302382223865172083227037608234390078113352793580052390824374953018909718406348276502851641661133114284495221770465857185674404018061 / 718620428464522208767690894621198731017199237378231888211740501106495947005642889540418179105724976031265154543748198276975490263707481572301002243803368927200580171452372474543287573836327376129540160598667843666295303328609325935151876955386606126352221261650209007534474854282855799881250000000000 : ℝ)) (y := (21547 / 625000 : ℝ)) (c := (62643 / 100000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_71).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_72 : Real.log 72 ^ 2 * ex (1597 / 2000) 72 ≤ (623619 / 1000000 : ℝ) := by
  have h := D2term_le (n := 72) (hi := (3073299639732064282308118114513833862475318357712559724614415949528225840913944435016868055984484266601105114690188901174343451089779856298682810299234262011661682908584962353429991523693882028335313455543516164935524694585639462706111768713430369435239539219305695465423097636306108940972002529018061 / 718620428464522208767690894621198731017199237378231888211740501106495947005642889540418179105724976031265154543748198276975490263707481572301002243803368927200580171452372474543287573836327376129540160598667843666295303328609325935151876955386606126352221261650209007534474854282855799881250000000000 : ℝ)) (y := (85241 / 2500000 : ℝ)) (c := (623619 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_72).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_73 : Real.log 73 ^ 2 * ex (1597 / 2000) 73 ≤ (124169 / 200000 : ℝ) := by
  have h := D2term_le (n := 73) (hi := (3083211802810691766763952657528008386052985644264942881425970552396670856775469766687819597826427050551085144952302706744306339157637186587069486709019777154362867978912954909573744657369200488030856062592529220373646744626413916665979218051644272778024302687045305105976792954921469032775980654018061 / 718620428464522208767690894621198731017199237378231888211740501106495947005642889540418179105724976031265154543748198276975490263707481572301002243803368927200580171452372474543287573836327376129540160598667843666295303328609325935151876955386606126352221261650209007534474854282855799881250000000000 : ℝ)) (y := (84317 / 2500000 : ℝ)) (c := (124169 / 200000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_73).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_74 : Real.log 74 ^ 2 * ex (1597 / 2000) 74 ≤ (61811 / 100000 : ℝ) := by
  have h := D2term_le (n := 74) (hi := (3092989102337306136460406336427906297221460514041669758529436995565872198362405299011737552701824988639892466839772698882086059937793351493324840891951672607456789403024309839255877180045884568052083428721359706510617070945535097060764575778327549793799774223705619132971718853075544784530668154018061 / 718620428464522208767690894621198731017199237378231888211740501106495947005642889540418179105724976031265154543748198276975490263707481572301002243803368927200580171452372474543287573836327376129540160598667843666295303328609325935151876955386606126352221261650209007534474854282855799881250000000000 : ℝ)) (y := (333663 / 10000000 : ℝ)) (c := (61811 / 100000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_74).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_76 : Real.log 76 ^ 2 * ex (1597 / 2000) 76 ≤ (153187 / 250000 : ℝ) := by
  have h := D2term_le (n := 76) (hi := (35444646512865598453738441947463174534068006584557414059079442914452422096754742031764917874097742557788344623564867921730054312657297499198767339161558533349325613983093743465865973837564969827537231696985939354964702945547778445589855845644612450401231992819124677994438093659629016636593965758698857719796349439 / 8184444461709128092066697735608753545956345836849585735774909286934396989829006145466725712355318406756112324155785169971000422756773643856844470184910323274319521851426247920012612061924020542901308214068122980223307533116776957194126227828641109611566899795091863661644642452950230447514777268996993750000000000 : ℝ)) (y := (326707 / 10000000 : ℝ)) (c := (153187 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_76).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_77 : Real.log 77 ^ 2 * ex (1597 / 2000) 77 ≤ (305059 / 500000 : ℝ) := by
  have h := D2term_le (n := 77) (hi := (35551634238608725534518170868520230621763268193860707241447868048611980723191235869554486696245348152900680227675807978978857329564116455195449485495874734957330168155597228328375990232404375621672345029667429142937364515603098793391936945953523507871411653913027377026504978353085498143634672611840671001046349439 / 8184444461709128092066697735608753545956345836849585735774909286934396989829006145466725712355318406756112324155785169971000422756773643856844470184910323274319521851426247920012612061924020542901308214068122980223307533116776957194126227828641109611566899795091863661644642452950230447514777268996993750000000000 : ℝ)) (y := (6467 / 200000 : ℝ)) (c := (305059 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_77).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_78 : Real.log 78 ^ 2 * ex (1597 / 2000) 78 ≤ (151881 / 250000 : ℝ) := by
  have h := D2term_le (n := 78) (hi := (35657241439001538691163377070114022992828591422049854558939998920856777957336259764436635847437571746694107317971701161209060644657216055800298588425382084882849172954651293549696456273877035855819330138303557045820157586410392524788449343046006604376184188460832682335064760715468192366541295304259708838546349439 / 8184444461709128092066697735608753545956345836849585735774909286934396989829006145466725712355318406756112324155785169971000422756773643856844470184910323274319521851426247920012612061924020542901308214068122980223307533116776957194126227828641109611566899795091863661644642452950230447514777268996993750000000000 : ℝ)) (y := (320071 / 10000000 : ℝ)) (c := (151881 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_78).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_79 : Real.log 79 ^ 2 * ex (1597 / 2000) 79 ≤ (604963 / 1000000 : ℝ) := by
  have h := D2term_le (n := 79) (hi := (138393191244135732144766597270155921484196228744804018270248425757758329508947507708463083045478254316904743012010755676879620327001742480165278797243721302935135125398803951762423731243795010372002698509948947256190986981101632969691168878217665105087991109945128380136287439371084521426885950435445977120439585369540027 / 31672924331256922839592269100148166086221641059603353891775171025142414370160342079298663567163860215076631790464203938774584739023479026946095417257293165667026197376181476841921367330155333630829972348464730644305316259255883329206848730190463429598035464548727437541152970316174926157224303949850583134168750000000000 : ℝ)) (y := (158433 / 5000000 : ℝ)) (c := (604963 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_79).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_81 : Real.log 81 ^ 2 * ex (1597 / 2000) 81 ≤ (599939 / 1000000 : ℝ) := by
  have h := D2term_le (n := 81) (hi := (139185055598037988107814218407963839471047078296061994495477119524350982082120463248884003441852277035147578966001362798310003022874227785359713734626874975838476877717775015525990793538784537111669026135759262717442429300778012912374327905421319035636962799929314124561778869349176255404896418267334208012116694744540027 / 31672924331256922839592269100148166086221641059603353891775171025142414370160342079298663567163860215076631790464203938774584739023479026946095417257293165667026197376181476841921367330155333630829972348464730644305316259255883329206848730190463429598035464548727437541152970316174926157224303949850583134168750000000000 : ℝ)) (y := (310669 / 10000000 : ℝ)) (c := (599939 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_81).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_82 : Real.log 82 ^ 2 * ex (1597 / 2000) 82 ≤ (298737 / 500000 : ℝ) := by
  have h := D2term_le (n := 82) (hi := (604458318946817731956710335714761633658222144655182964379899433115587229386413772245282041550818981232833945038396727098491456722709914008898541807237773519865358459139398917389879063410412389788489471596396536722240798810181414545600474270092700503098415270626336824685221266793878839959048198535038555650697485544519988310169 / 137167422028817924816795700628659369833406113353954046056743646591622435606328790978896449347504186134862477896657479815236216534771714725509721890000770605332976703208305802288720435800968220655716010258196586843633315473823638960312572517726158926341403293988007703949035602737863612930620682657903563356551911556250000000000 : ℝ)) (y := (38459 / 1250000 : ℝ)) (c := (298737 / 500000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_82).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_83 : Real.log 83 ^ 2 * ex (1597 / 2000) 83 ≤ (3719 / 6250 : ℝ) := by
  have h := D2term_le (n := 83) (hi := (606120974724315932395967763624698361392660708699733391244993864643861694389320727420545427475621865454108609107456759521299834530078807015692849611112590771534133278055435182558892430953369105497580688075684887151473186155711126850096795426982032536267122722933698758193326095227907012763642793142475924773306256368657488310169 / 137167422028817924816795700628659369833406113353954046056743646591622435606328790978896449347504186134862477896657479815236216534771714725509721890000770605332976703208305802288720435800968220655716010258196586843633315473823638960312572517726158926341403293988007703949035602737863612930620682657903563356551911556250000000000 : ℝ)) (y := (15237 / 500000 : ℝ)) (c := (3719 / 6250 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_83).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_84 : Real.log 84 ^ 2 * ex (1597 / 2000) 84 ≤ (148159 / 250000 : ℝ) := by
  have h := D2term_le (n := 84) (hi := (2830637029223145101953506356086878515605092431672983952100444841918617504707409039797867403922266977700772939462392892423877061575271874377962999665486110184006446471653730277590099496205696015685655644322250162610678139689471859960006713760514328022714362443264140452220518703648183954371195287002785112609983564932790554446294641247 / 638852192904604418571007754237057754602405136919846873209579434485557603806358909818943993667374889268235000892000035912709514770687474780616685842968659065825941675054665566845030747086884851879833056285171049950508952386661066983014274936126429331554811209827268324857587205434298476270687396513927503901296335652506793750000000000 : ℝ)) (y := (30187 / 1000000 : ℝ)) (c := (148159 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_84).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_86 : Real.log 86 ^ 2 * ex (1597 / 2000) 86 ≤ (117583 / 200000 : ℝ) := by
  have h := D2term_le (n := 86) (hi := (2845669539108189856721172464957345092309299506698735372647890498662388822534770037376680478540148237935852721541890232053074306885181229758724550671461980118676612768046685366911247369772647794933922282768818653682421875232780659014608581535939424256749071042098908661948411370129749383396638223523668854479798690214292790852544641247 / 638852192904604418571007754237057754602405136919846873209579434485557603806358909818943993667374889268235000892000035912709514770687474780616685842968659065825941675054665566845030747086884851879833056285171049950508952386661066983014274936126429331554811209827268324857587205434298476270687396513927503901296335652506793750000000000 : ℝ)) (y := (29631 / 1000000 : ℝ)) (c := (117583 / 200000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_86).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_87 : Real.log 87 ^ 2 * ex (1597 / 2000) 87 ≤ (366 / 625 : ℝ) := by
  have h := D2term_le (n := 87) (hi := (14772312389529677816516477753813434394249560796208574156084483798127626674444952475849468984307179827224465369202948222766925001537797718359286798795815700210013867213502250601249456821196379930559259334811802656078239712980300860257089402682337919429831050436866443266439324497952166844922548480027916275838188529598734758499232069743493099 / 3307795859689449676310222556245035965986701318317218792814084000786257859707449235471013238059459309537257924113523749945846570689939639858670284772798156512331097251939017834768152064714464174620693572689686993236599361424605579756091722579455727299289982432913214269176651852559659603660834734615903173717308359145690518614868750000000000 : ℝ)) (y := (293617 / 10000000 : ℝ)) (c := (366 / 625 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_87).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_88 : Real.log 88 ^ 2 * ex (1597 / 2000) 88 ≤ (583311 / 1000000 : ℝ) := by
  have h := D2term_le (n := 88) (hi := (14810116182288953844227175369694720923602189905720877186600951655468027329105096305946901612375585917162503075501789739278230982167680423535894161215938761215927447702297414939660596275375986829435723045530044896711065093918041325606208362415941340739358602235654110566712523832983960991931444041505793590993457092956767676335188643768493099 / 3307795859689449676310222556245035965986701318317218792814084000786257859707449235471013238059459309537257924113523749945846570689939639858670284772798156512331097251939017834768152064714464174620693572689686993236599361424605579756091722579455727299289982432913214269176651852559659603660834734615903173717308359145690518614868750000000000 : ℝ)) (y := (145489 / 5000000 : ℝ)) (c := (583311 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_88).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_89 : Real.log 89 ^ 2 * ex (1597 / 2000) 89 ≤ (581049 / 1000000 : ℝ) := by
  have h := D2term_le (n := 89) (hi := (14847492804404712222796122086396487568433120323606346049378682588336777787354439360741791519503047876500588866310365333052472485097583474936731392859491367478475007836754077149558695516528382994557312545689696937031741070272545299707703062315688594638553550284253207103919805328921979067920241169879079094121499094095929626988248409393493099 / 3307795859689449676310222556245035965986701318317218792814084000786257859707449235471013238059459309537257924113523749945846570689939639858670284772798156512331097251939017834768152064714464174620693572689686993236599361424605579756091722579455727299289982432913214269176651852559659603660834734615903173717308359145690518614868750000000000 : ℝ)) (y := (36049 / 1250000 : ℝ)) (c := (581049 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_89).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_91 : Real.log 91 ^ 2 * ex (1597 / 2000) 91 ≤ (144151 / 250000 : ℝ) := by
  have h := D2term_le (n := 91) (hi := (507449487115667095858013146306997733466702846830035063607891236695557842410578889651081480081653443811558922815061281531189407702863749024672589620672687934554223681701144262259394334755052886787059681392441736994498897632889412749747171799683772436763428664662574710818291224398695995698162740880537893346269156155750346108233442731937261185958493009701 / 112495076872199579803268991902844153040790354518914180026517731293832533092401396095444921845820315186993598792800851940313286947236259988734851009304663737937330902662851044217263291966826100117619498680784110898260528376997918139564080515090580309654014053272119893852530459482829270135613267843353096905168252725615039414170594940589627631250000000000 : ℝ)) (y := (283373 / 10000000 : ℝ)) (c := (144151 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_91).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_92 : Real.log 92 ^ 2 * ex (1597 / 2000) 92 ≤ (28721 / 50000 : ℝ) := by
  have h := D2term_le (n := 92) (hi := (508678953746204556227267585442288412100230290291076481127408277397099478316506546169863046429961010590013344827646488913765919707304279058273885317927060214614668777718918739819945902382375241703671734798474566278953502709211684169603367256804178222204991807157423914571838128458210838775866601639811028562410488318165374331143750587204478060177243009701 / 112495076872199579803268991902844153040790354518914180026517731293832533092401396095444921845820315186993598792800851940313286947236259988734851009304663737937330902662851044217263291966826100117619498680784110898260528376997918139564080515090580309654014053272119893852530459482829270135613267843353096905168252725615039414170594940589627631250000000000 : ℝ)) (y := (280937 / 10000000 : ℝ)) (c := (28721 / 50000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_92).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_93 : Real.log 93 ^ 2 * ex (1597 / 2000) 93 ≤ (28613 / 50000 : ℝ) := by
  have h := D2term_le (n := 93) (hi := (509895128585237825275541852078441913410054603309913240654801398191336519059956164023592070528906583609240311123475108025922543274793787508654865838690271085407332890950133747641234830475223916334958018492435099896172302847613703100652569220023262007793587891700255187756497132378575030926694849444328213078043478181549603805147798040913801326845993009701 / 112495076872199579803268991902844153040790354518914180026517731293832533092401396095444921845820315186993598792800851940313286947236259988734851009304663737937330902662851044217263291966826100117619498680784110898260528376997918139564080515090580309654014053272119893852530459482829270135613267843353096905168252725615039414170594940589627631250000000000 : ℝ)) (y := (278547 / 10000000 : ℝ)) (c := (28613 / 50000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_93).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_94 : Real.log 94 ^ 2 * ex (1597 / 2000) 94 ≤ (35633 / 62500 : ℝ) := by
  have h := D2term_le (n := 94) (hi := (511098295957383938768461254056398783944538658588863608361803180444079157055584131365252869512149860217687559398296903368989763440049952875961570509656836366182485032673915017844275041686601907855744285780018271921300983650479118690776195147613606375299957521190043275792847104739200249940674251692677068470334498854190655545030680144707639347158493009701 / 112495076872199579803268991902844153040790354518914180026517731293832533092401396095444921845820315186993598792800851940313286947236259988734851009304663737937330902662851044217263291966826100117619498680784110898260528376997918139564080515090580309654014053272119893852530459482829270135613267843353096905168252725615039414170594940589627631250000000000 : ℝ)) (y := (69051 / 2500000 : ℝ)) (c := (35633 / 62500 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_94).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_96 : Real.log 96 ^ 2 * ex (1597 / 2000) 96 ≤ (141483 / 250000 : ℝ) := by
  have h := D2term_le (n := 96) (hi := (3577769734283345062283577726785121194390090940796631930921340490109298982176853246748258422317475177384592972548820481261056946750257185436190915323996559832360776540488925647766440683756973412346150457708546852506237367686975959815263286427252570641159933959762014890674457167512540549670929324800544734894216744653887775863349520085903047135646506412404566571 / 783851183780570158323383713879062591492484928332061066495552130868088186191084008212963903026757845402312274213992065010202683034326066123965895037054696624325127814068302568321186591460180545052657493892373863588773486122760860865042509262764716912809224555387259316898125265247081069329105756220932586685711618287483990297856277539281189272585568750000000000 : ℝ)) (y := (8489 / 312500 : ℝ)) (c := (141483 / 250000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_96).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_97 : Real.log 97 ^ 2 * ex (1597 / 2000) 97 ≤ (563869 / 1000000 : ℝ) := by
  have h := D2term_le (n := 97) (hi := (25779186420736650802163065962324618423551420575277460476446517362727813565004602832761536551636386655966690365666208042927950652302931614246367684094410578460053599777241756306305173641407931741033360569407711961647837360446268759451526624085026537120126974980222682795873090083305701832734305699365466746466135905882652937850534896899518622738326613036924065045463547 / 5635150839715994360685829951948272076807189221420101934517314515282145451554315826831465637801834675794410871124019152906052669886703045950959885477403326149980930387622429056907404713642951168674622725069427570649917151825236826127859906513043527475049545454478664302961685725001384891027893040500388958841021909430964792838735757037712208708406191121168750000000000 : ℝ)) (y := (269433 / 10000000 : ℝ)) (c := (563869 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_97).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_98 : Real.log 98 ^ 2 * ex (1597 / 2000) 98 ≤ (56183 / 100000 : ℝ) := by
  have h := D2term_le (n := 98) (hi := (25836983346298312669012955366783063120012061060853710721690967051302079800834696982712757105844885498779645028876890549866751643207275618760715264207563761333519937649102217361030323333070099728043933415949680652996273708984049342681783852295124379312274461871008592283668125723449648096148720147804056116112755213913296163004138272219842566535245962132677427545463547 / 5635150839715994360685829951948272076807189221420101934517314515282145451554315826831465637801834675794410871124019152906052669886703045950959885477403326149980930387622429056907404713642951168674622725069427570649917151825236826127859906513043527475049545454478664302961685725001384891027893040500388958841021909430964792838735757037712208708406191121168750000000000 : ℝ)) (y := (267259 / 10000000 : ℝ)) (c := (56183 / 100000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_98).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

theorem D2t_99 : Real.log 99 ^ 2 * ex (1597 / 2000) 99 ≤ (559813 / 1000000 : ℝ) := by
  have h := D2term_le (n := 99) (hi := (197970767772173483966891192619152048346777979356220916592708937472231437549537299279820750150840843460555606960632664642551505505680192411137539281135261674868472520263632215684033346879652640820986213206590542406866511703978289173384872247607107228175422339940327244169664855655799538568344303785044723072556987094378122709861859652181992969442415171586539923254605774718031 / 43082830080891990953339705797216616732675610679336268987406444427646202217386174255929962937677926180782342424998055683110806618929712526531228032512031499857258155700408053306095335497758550505303406367432224674102469044801566349083634677037347132782501968479943909137927092076411013008472595698729580235421260198771943591119863710990684902229613566630623289693750000000000 : ℝ)) (y := (66281 / 2500000 : ℝ)) (c := (559813 / 1000000 : ℝ)) (by norm_num)
    (by exact_mod_cast (PsiOmega.Num.log_bound_99).2)
    (ex_le_of (p := 79) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)
  exact_mod_cast h

/-- **`D2sum(1597/2000, 20) ≤ 36`** (true value `34.0033…`). -/
theorem D2sum_le : D2sum (1597 / 2000) 20 ≤ 36 := by
  have hk := kappa_le
  unfold D2sum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat,
    Nat.cast_one, Real.log_one]
  norm_num only
  linarith [mul_le_mul hk D2t_2 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_3 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_4,
    D2t_6,
    mul_le_mul hk D2t_7 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_8 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_9,
    D2t_11,
    mul_le_mul hk D2t_12 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_13 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_14,
    D2t_16,
    mul_le_mul hk D2t_17 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_18 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_19,
    D2t_21,
    mul_le_mul hk D2t_22 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_23 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_24,
    D2t_26,
    mul_le_mul hk D2t_27 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_28 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_29,
    D2t_31,
    mul_le_mul hk D2t_32 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_33 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_34,
    D2t_36,
    mul_le_mul hk D2t_37 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_38 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_39,
    D2t_41,
    mul_le_mul hk D2t_42 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_43 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_44,
    D2t_46,
    mul_le_mul hk D2t_47 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_48 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_49,
    D2t_51,
    mul_le_mul hk D2t_52 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_53 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_54,
    D2t_56,
    mul_le_mul hk D2t_57 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_58 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_59,
    D2t_61,
    mul_le_mul hk D2t_62 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_63 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_64,
    D2t_66,
    mul_le_mul hk D2t_67 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_68 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_69,
    D2t_71,
    mul_le_mul hk D2t_72 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_73 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_74,
    D2t_76,
    mul_le_mul hk D2t_77 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_78 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_79,
    D2t_81,
    mul_le_mul hk D2t_82 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_83 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_84,
    D2t_86,
    mul_le_mul hk D2t_87 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_88 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_89,
    D2t_91,
    mul_le_mul hk D2t_92 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_93 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_94,
    D2t_96,
    mul_le_mul hk D2t_97 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    mul_le_mul hk D2t_98 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num),
    D2t_99]

/-! ## 13. Stage 2, final form: three point values at the centre -/

/-- **Stage 2 with every ball-uniform input discharged.** The Euler–Maclaurin error (`16·10⁻⁶`),
the second-derivative bound (`36 + 53/8`) and the linearisation are proved; what remains are three
real inequalities about `fEM = dhEM/a(1)` and its derivative **at the single point `c`**, in the
elementary forms `PRe`, `PIm`, `ARe`. -/
theorem dh_zero_near_of_center {pr pi ar : ℝ}
    (hPr : |PRe 20 12| ≤ pr) (hPi : |PIm 20 12| ≤ pi) (hAr : ar ≤ |ARe 20 12|)
    (hmargin : 2 * (pr + pi + 16 / 10 ^ 6) < ar / 100 - (36 + 53 / 8) / 10 ^ 4) :
    ∃ ρ, dh ρ = 0 ∧ ‖ρ - cLoc‖ < 1 / 100 :=
  dh_zero_near_of_elementary hPr hPi hAr D2sum_le hmargin

/-- **The certificate's open inputs, packaged with fixed tolerances**: `|Re fEM(c)| ≤ 10⁻³`,
`|Im fEM(c)| ≤ 10⁻³`, `Re fEM′(c) ≥ 1` (true values `−3.23·10⁻⁵`, `−5.44·10⁻⁵`, `1.2323`). -/
theorem dh_zero_near_of_center' (hPr : |PRe 20 12| ≤ 1 / 1000) (hPi : |PIm 20 12| ≤ 1 / 1000)
    (hAr : 1 ≤ ARe 20 12) : ∃ ρ, dh ρ = 0 ∧ ‖ρ - cLoc‖ < 1 / 100 :=
  dh_zero_near_of_center hPr hPi (hAr.trans (le_abs_self _)) (by norm_num)

/-- **Stage 2 in `dh` units**, with `hM2` (`m₂ = 158 ≥ ‖a(1)‖(36 + 53/8)`) and `hE` (`e₀ = 6·10⁻⁵`)
of `dh_zero_near_of_numerics` discharged: only `‖P(c)‖` and `‖P′(c)‖` remain. -/
theorem dh_zero_near_of_dhEM {p₀ a₀ : ℝ}
    (hP : ‖dhEM 20 12 cLoc‖ ≤ p₀)
    (hA : a₀ ≤ ‖deriv (dhEM 20 12) cLoc‖)
    (hmargin : 2 * (p₀ + 6 / 10 ^ 5) < a₀ * (1 / 100) - 158 * (1 / 100) ^ 2) :
    ∃ ρ, dh ρ = 0 ∧ ‖ρ - cLoc‖ < 1 / 100 := by
  refine dh_zero_near_of_numerics hP hA (fun z hz => ?_)
    (fun z hz => norm_dh_sub_dhEM_le_ball' hz) hmargin
  refine (norm_deriv2_dhEM_ball hz).trans ?_
  have h1 := norm_aDH_one_le
  have h2 := D2sum_le
  have h0 := norm_nonneg (aDH chi5 1)
  have h3 : 0 ≤ D2sum (1597 / 2000) 20 := by
    unfold D2sum
    refine Finset.sum_nonneg fun m _ => ?_
    have hk := kappa_pos.le
    have e : ∀ n : ℕ, 0 ≤ Real.log n ^ 2 * ex (1597 / 2000) n :=
      fun n => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    have := e (5 * m + 1); have := e (5 * m + 2); have := e (5 * m + 3); have := e (5 * m + 4)
    positivity
  nlinarith

/-! ## 14. The three open quantities with every constant substituted

`PRe 20 12`, `PIm 20 12`, `ARe 20 12` (and `AIm 20 12`) with the numerals normalised and the
Gaussian-rational values `Q_j(c)`, `Q′_j(c)` substituted (`QEM_cLoc_j`, `QEMd_cLoc_j`): the forms a
generator discharges. The `m`-sums run over `n = 5m + j < 100`; `n = 1` contributes `ex · cC = 1`,
`ex · sC = 0`, `log 1 = 0`. -/

theorem PRe_20 : PRe 20 12 = (∑ m ∈ Finset.range 20, (ex (1617 / 2000) (5 * m + 1) * cC (5 * m + 1)
      + kappa * (ex (1617 / 2000) (5 * m + 2) * cC (5 * m + 2))
      - kappa * (ex (1617 / 2000) (5 * m + 3) * cC (5 * m + 3))
      - ex (1617 / 2000) (5 * m + 4) * cC (5 * m + 4))) +
    (ex (1617 / 2000) 101 * (cC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))
      + kappa * (ex (1617 / 2000) 102 * (cC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))
      - kappa * (ex (1617 / 2000) 103 * (cC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))
      - ex (1617 / 2000) 104 * (cC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) := by
  simp only [PRe, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat]
  rw [(QEM_cLoc_1).1, (QEM_cLoc_1).2, (QEM_cLoc_2).1, (QEM_cLoc_2).2, (QEM_cLoc_3).1, (QEM_cLoc_3).2, (QEM_cLoc_4).1, (QEM_cLoc_4).2]

theorem PIm_20 : PIm 20 12 = -(∑ m ∈ Finset.range 20, (ex (1617 / 2000) (5 * m + 1) * sC (5 * m + 1)
      + kappa * (ex (1617 / 2000) (5 * m + 2) * sC (5 * m + 2))
      - kappa * (ex (1617 / 2000) (5 * m + 3) * sC (5 * m + 3))
      - ex (1617 / 2000) (5 * m + 4) * sC (5 * m + 4))) +
    (ex (1617 / 2000) 101 * (cC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))
      + kappa * (ex (1617 / 2000) 102 * (cC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))
      - kappa * (ex (1617 / 2000) 103 * (cC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))
      - ex (1617 / 2000) 104 * (cC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) := by
  simp only [PIm, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat]
  rw [(QEM_cLoc_1).1, (QEM_cLoc_1).2, (QEM_cLoc_2).1, (QEM_cLoc_2).2, (QEM_cLoc_3).1, (QEM_cLoc_3).2, (QEM_cLoc_4).1, (QEM_cLoc_4).2]

theorem ARe_20 : ARe 20 12 = -(∑ m ∈ Finset.range 20, (Real.log (5 * m + 1 : ℕ) * (ex (1617 / 2000) (5 * m + 1) * cC (5 * m + 1))
      + kappa * (Real.log (5 * m + 2 : ℕ) * (ex (1617 / 2000) (5 * m + 2) * cC (5 * m + 2)))
      - kappa * (Real.log (5 * m + 3 : ℕ) * (ex (1617 / 2000) (5 * m + 3) * cC (5 * m + 3)))
      - Real.log (5 * m + 4 : ℕ) * (ex (1617 / 2000) (5 * m + 4) * cC (5 * m + 4)))) +
    (ex (1617 / 2000) 101 * (cC 101 * ((4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 101 * ((-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))
      + kappa * (ex (1617 / 2000) 102 * (cC 102 * ((4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 102 * ((-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))))
      - kappa * (ex (1617 / 2000) 103 * (cC 103 * ((58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 103 * ((-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))))
      - ex (1617 / 2000) 104 * (cC 104 * ((94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 104 * ((-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) := by
  simp only [ARe, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, QD_re, QD_im]
  rw [(QEM_cLoc_1).1, (QEM_cLoc_1).2, (QEM_cLoc_2).1, (QEM_cLoc_2).2, (QEM_cLoc_3).1, (QEM_cLoc_3).2, (QEM_cLoc_4).1, (QEM_cLoc_4).2, (QEMd_cLoc_1).1, (QEMd_cLoc_1).2, (QEMd_cLoc_2).1, (QEMd_cLoc_2).2, (QEMd_cLoc_3).1, (QEMd_cLoc_3).2, (QEMd_cLoc_4).1, (QEMd_cLoc_4).2]

theorem AIm_20 : AIm 20 12 = (∑ m ∈ Finset.range 20, (Real.log (5 * m + 1 : ℕ) * (ex (1617 / 2000) (5 * m + 1) * sC (5 * m + 1))
      + kappa * (Real.log (5 * m + 2 : ℕ) * (ex (1617 / 2000) (5 * m + 2) * sC (5 * m + 2)))
      - kappa * (Real.log (5 * m + 3 : ℕ) * (ex (1617 / 2000) (5 * m + 3) * sC (5 * m + 3)))
      - Real.log (5 * m + 4 : ℕ) * (ex (1617 / 2000) (5 * m + 4) * sC (5 * m + 4)))) +
    (ex (1617 / 2000) 101 * (cC 101 * ((-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) - sC 101 * ((4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))
      + kappa * (ex (1617 / 2000) 102 * (cC 102 * ((-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) - sC 102 * ((4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))))
      - kappa * (ex (1617 / 2000) 103 * (cC 103 * ((-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) - sC 103 * ((58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))))
      - ex (1617 / 2000) 104 * (cC 104 * ((-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) - sC 104 * ((94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) := by
  simp only [AIm, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, QD_re, QD_im]
  rw [(QEM_cLoc_1).1, (QEM_cLoc_1).2, (QEM_cLoc_2).1, (QEM_cLoc_2).2, (QEM_cLoc_3).1, (QEM_cLoc_3).2, (QEM_cLoc_4).1, (QEM_cLoc_4).2, (QEMd_cLoc_1).1, (QEMd_cLoc_1).2, (QEMd_cLoc_2).1, (QEMd_cLoc_2).2, (QEMd_cLoc_3).1, (QEMd_cLoc_3).2, (QEMd_cLoc_4).1, (QEMd_cLoc_4).2]

end Locate

end PsiOmega

#print axioms PsiOmega.Locate.dh_zero_near_of_numerics
#print axioms PsiOmega.Locate.dh_zero_near_of_dhEM
#print axioms PsiOmega.Locate.dh_zero_near_of_fEM
#print axioms PsiOmega.Locate.dh_zero_near_of_elementary
#print axioms PsiOmega.Locate.dh_zero_near_of_center
#print axioms PsiOmega.Locate.dh_zero_near_of_center'
#print axioms PsiOmega.Locate.norm_dh_sub_dhEM_le_ball
#print axioms PsiOmega.Locate.norm_dh_sub_dhEM_le_ball'
#print axioms PsiOmega.Locate.norm_deriv2_dhEM_ball
#print axioms PsiOmega.Locate.D2sum_le
#print axioms PsiOmega.Locate.Gsup_ball_le
#print axioms PsiOmega.Locate.bernoulli_vals
#print axioms PsiOmega.Locate.QEM_twelve
#print axioms PsiOmega.Locate.EMmain_explicit
#print axioms PsiOmega.Locate.dhEM_eq
#print axioms PsiOmega.Locate.fEM_cLoc_re
#print axioms PsiOmega.Locate.fEM_cLoc_im
#print axioms PsiOmega.Locate.fEMd_cLoc_re
#print axioms PsiOmega.Locate.fEMd_cLoc_im
#print axioms PsiOmega.Locate.QEM_cLoc_1
#print axioms PsiOmega.Locate.QEMd_cLoc_4
#print axioms PsiOmega.Locate.PRe_20
#print axioms PsiOmega.Locate.PIm_20
#print axioms PsiOmega.Locate.ARe_20
#print axioms PsiOmega.Locate.AIm_20
