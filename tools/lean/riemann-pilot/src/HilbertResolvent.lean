import Mathlib

/-! # Resolvents of self-adjoint operators off the real axis (round 419)

S5f-10 of round 360's plan, part 2 (S5f-10b, first half). Round 418 replanned the residue on the ball
average `T_R`. This file proves what that plan needs from a self-adjoint bounded operator `A` on a complex
Hilbert space `E`, with Mathlib's `resolvent A z = (z − A)⁻¹`. Nothing here depends on the operator's origin.

* **The lower bound** (**`abs_im_mul_norm_le`**, with `im_inner_apply_self`): `|Im z|·‖x‖ ≤ ‖(z − A)x‖`,
  since `⟪Ax, x⟫` is real.
* **The resolvent** (**`mem_resolventSet_of_im_ne_zero`**, **`norm_resolvent_le`** and
  **`hasDerivAt_resolvent_of_im_ne_zero`**, with `sub_apply_resolvent`, `resolvent_sub_apply`,
  `abs_im_mul_norm_resolvent_le`, `algebraMap_sub_apply_eq` and `resolvent_apply_sub`): every `z` with
  `Im z ≠ 0` is in the resolvent set (Mathlib's `IsSelfAdjoint.im_eq_zero_of_mem_spectrum`), there
  `‖R(z)‖ ≤ |Im z|⁻¹`, and `R` is complex-differentiable (Mathlib's
  `spectrum.hasDerivAt_resolvent_const_left`).
* **The limit at a real point** (`kerAt`, a definition; **`tendsto_resolvent_ker`**, with `kerAt_complete`,
  `isSelfAdjoint_sub_real`, `orthogonal_kerAt`, `im_real_add_I_mul`, `resolvent_apply_of_mem_ker`,
  `norm_smul_resolvent_apply_le`, `resolvent_apply_range`, `tendsto_resolvent_range` and
  `tendsto_resolvent_orthogonal`): for real `l`, `iη·R(l + iη)x → Px` as `η → 0+`, where `P` is the
  orthogonal projection onto `ker(A − l)`. On `ker(A − l)` the left side is `x`. On the range of `A − l` it
  is `O(η)`. Its operator norm is at most `1`, and `ker(A − l)ᗮ` is the closure of that range (Mathlib's
  `ContinuousLinearMap.orthogonal_ker`). No spectral theorem and no weak compactness are used.
* **Along a curve** (**`tendsto_resolvent_curve`**): if `ℓ(ε) = l + iεd + o(ε)` with `d > 0`,
  `Im ℓ(ε) ≥ cε` with `c > 0`, and `x(ε) → x₀`, then `iε·R(ℓ(ε))x(ε) → d⁻¹·Px₀` as `ε → 0+`.
-/

open Filter Topology Complex
open scoped InnerProductSpace

noncomputable section

namespace Eis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `⟪Ax, x⟫` is real for self-adjoint `A`. -/
theorem im_inner_apply_self {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (x : E) :
    (⟪A x, x⟫_ℂ).im = 0 := by
  have h := hA.isSymmetric.conj_inner_sym x x
  rw [Complex.conj_eq_iff_im] at h
  exact h

/-- **The lower bound**: `|Im z|·‖x‖ ≤ ‖(z − A)x‖` for self-adjoint `A`. -/
theorem abs_im_mul_norm_le {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (z : ℂ) (x : E) :
    |z.im| * ‖x‖ ≤ ‖(algebraMap ℂ (E →L[ℂ] E) z - A) x‖ := by
  have h1 : (⟪(algebraMap ℂ (E →L[ℂ] E) z - A) x, x⟫_ℂ).im = -(z.im * ‖x‖ ^ 2) := by
    rw [sub_apply, inner_sub_left, Algebra.algebraMap_eq_smul_one,
      smul_apply, one_apply_eq_self, inner_smul_left,
      inner_self_eq_norm_sq_to_K, Complex.sub_im, im_inner_apply_self hA x, sub_zero]
    simp [Complex.mul_im, ← Complex.ofReal_pow]
  have h2 : |z.im| * ‖x‖ ^ 2 ≤ ‖(algebraMap ℂ (E →L[ℂ] E) z - A) x‖ * ‖x‖ := by
    calc |z.im| * ‖x‖ ^ 2 = |(⟪(algebraMap ℂ (E →L[ℂ] E) z - A) x, x⟫_ℂ).im| := by
          rw [h1, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
      _ ≤ ‖⟪(algebraMap ℂ (E →L[ℂ] E) z - A) x, x⟫_ℂ‖ := Complex.abs_im_le_norm _
      _ ≤ ‖(algebraMap ℂ (E →L[ℂ] E) z - A) x‖ * ‖x‖ := norm_inner_le_norm _ _
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    have : |z.im| * ‖x‖ * ‖x‖ ≤ ‖(algebraMap ℂ (E →L[ℂ] E) z - A) x‖ * ‖x‖ := by
      rw [mul_assoc, ← sq]; exact h2
    exact le_of_mul_le_mul_right this hx'

/-- **Off the real axis is the resolvent set** (Mathlib's `IsSelfAdjoint.im_eq_zero_of_mem_spectrum`). -/
theorem mem_resolventSet_of_im_ne_zero {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) : z ∈ resolventSet ℂ A := by
  by_contra h
  exact hz (hA.im_eq_zero_of_mem_spectrum h)

omit [CompleteSpace E] in
theorem sub_apply_resolvent {A : E →L[ℂ] E} {z : ℂ} (hz : z ∈ resolventSet ℂ A) (x : E) :
    (algebraMap ℂ (E →L[ℂ] E) z - A) (resolvent A z x) = x := by
  have hu : IsUnit (algebraMap ℂ (E →L[ℂ] E) z - A) := hz
  have h : (algebraMap ℂ (E →L[ℂ] E) z - A) * resolvent A z = 1 := by
    rw [spectrum.resolvent_eq hz]; exact hu.mul_val_inv
  rw [← mul_apply_eq_comp, h, one_apply_eq_self]

omit [CompleteSpace E] in
theorem resolvent_sub_apply {A : E →L[ℂ] E} {z : ℂ} (hz : z ∈ resolventSet ℂ A) (x : E) :
    resolvent A z ((algebraMap ℂ (E →L[ℂ] E) z - A) x) = x := by
  have hu : IsUnit (algebraMap ℂ (E →L[ℂ] E) z - A) := hz
  have h : resolvent A z * (algebraMap ℂ (E →L[ℂ] E) z - A) = 1 := by
    rw [spectrum.resolvent_eq hz]; exact hu.val_inv_mul
  rw [← mul_apply_eq_comp, h, one_apply_eq_self]

/-- **The resolvent bound**: `|Im z|·‖R(z)x‖ ≤ ‖x‖`. -/
theorem abs_im_mul_norm_resolvent_le {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (x : E) : |z.im| * ‖resolvent A z x‖ ≤ ‖x‖ := by
  have h := abs_im_mul_norm_le hA z (resolvent A z x)
  rwa [sub_apply_resolvent (mem_resolventSet_of_im_ne_zero hA hz)] at h

/-- `‖R(z)‖ ≤ |Im z|⁻¹`. -/
theorem norm_resolvent_le {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolvent A z‖ ≤ |z.im|⁻¹ := by
  have hpos : 0 < |z.im| := abs_pos.2 hz
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hpos.le) fun x => ?_
  rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
  exact abs_im_mul_norm_resolvent_le hA hz x

/-- **The resolvent is holomorphic off the real axis** (Mathlib's
`spectrum.hasDerivAt_resolvent_const_left`). -/
theorem hasDerivAt_resolvent_of_im_ne_zero {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) : HasDerivAt (resolvent A) (-resolvent A z ^ 2) z :=
  spectrum.hasDerivAt_resolvent_const_left (mem_resolventSet_of_im_ne_zero hA hz)

omit [CompleteSpace E] in
/-- `(z − A)y = (w − A)y − (w − z)y`. -/
theorem algebraMap_sub_apply_eq (A : E →L[ℂ] E) (z w : ℂ) (y : E) :
    (algebraMap ℂ (E →L[ℂ] E) z - A) y = (algebraMap ℂ (E →L[ℂ] E) w - A) y - (w - z) • y := by
  simp only [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, sub_smul]
  abel

omit [CompleteSpace E] in
/-- The resolvent identity, applied: `R(z)x − R(w)x = (w − z)·R(z)(R(w)x)`. -/
theorem resolvent_apply_sub {A : E →L[ℂ] E} {z w : ℂ} (hz : z ∈ resolventSet ℂ A)
    (hw : w ∈ resolventSet ℂ A) (x : E) :
    resolvent A z x - resolvent A w x = (w - z) • resolvent A z (resolvent A w x) := by
  have key : (algebraMap ℂ (E →L[ℂ] E) z - A) (resolvent A z x - resolvent A w x) =
      (w - z) • resolvent A w x := by
    rw [map_sub, sub_apply_resolvent hz, algebraMap_sub_apply_eq A z w, sub_apply_resolvent hw,
      sub_sub_cancel]
  have := congrArg (fun y => resolvent A z y) key
  rwa [resolvent_sub_apply hz, map_smul] at this

/-! ### The limit at a real point -/

section Limit

variable {A : E →L[ℂ] E}

/-- The kernel of `A − λ₀`. -/
abbrev kerAt (A : E →L[ℂ] E) (l : ℝ) : Submodule ℂ E :=
  (A - algebraMap ℂ (E →L[ℂ] E) l).ker

instance kerAt_complete (A : E →L[ℂ] E) (l : ℝ) : CompleteSpace (kerAt A l) :=
  (ContinuousLinearMap.isClosed_ker (A - algebraMap ℂ (E →L[ℂ] E) l)).completeSpace_coe

theorem isSelfAdjoint_sub_real (hA : IsSelfAdjoint A) (l : ℝ) :
    IsSelfAdjoint (A - algebraMap ℂ (E →L[ℂ] E) l) := by
  refine hA.sub ?_
  have hr : IsSelfAdjoint (l : ℂ) := by
    rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]
  rw [Algebra.algebraMap_eq_smul_one]
  exact hr.smul (IsSelfAdjoint.one _)

/-- `(kerAt A l)ᗮ` is the closure of the range of `A − l` (Mathlib's
`ContinuousLinearMap.orthogonal_ker`). -/
theorem orthogonal_kerAt (hA : IsSelfAdjoint A) (l : ℝ) :
    (kerAt A l)ᗮ = (A - algebraMap ℂ (E →L[ℂ] E) l).range.topologicalClosure := by
  rw [kerAt, ContinuousLinearMap.orthogonal_ker, (isSelfAdjoint_sub_real hA l).adjoint_eq]

theorem im_real_add_I_mul (l η : ℝ) : ((l : ℂ) + I * η).im = η := by simp

theorem resolvent_apply_of_mem_ker (hA : IsSelfAdjoint A) (l : ℝ) {η : ℝ} (hη : η ≠ 0) {y : E}
    (hy : y ∈ kerAt A l) : (I * η) • resolvent A ((l : ℂ) + I * η) y = y := by
  have hz : ((l : ℂ) + I * η) ∈ resolventSet ℂ A :=
    mem_resolventSet_of_im_ne_zero hA (by rw [im_real_add_I_mul]; exact hη)
  have hAy : A y = (l : ℂ) • y := by
    have h0 : (A - algebraMap ℂ (E →L[ℂ] E) l) y = 0 := LinearMap.mem_ker.1 hy
    simp only [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self,
      sub_eq_zero] at h0
    exact h0
  have e : (algebraMap ℂ (E →L[ℂ] E) ((l : ℂ) + I * η) - A) y = (I * η) • y := by
    simp only [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, hAy,
      add_smul, add_apply]
    abel
  have := congrArg (fun v => resolvent A ((l : ℂ) + I * η) v) e
  rw [resolvent_sub_apply hz, map_smul] at this
  exact this.symm

/-- `‖iη·R(l + iη)‖ ≤ 1`. -/
theorem norm_smul_resolvent_apply_le (hA : IsSelfAdjoint A) (l : ℝ) {η : ℝ} (hη : η ≠ 0)
    (x : E) : ‖(I * η) • resolvent A ((l : ℂ) + I * η) x‖ ≤ ‖x‖ := by
  have h := abs_im_mul_norm_resolvent_le hA (z := (l : ℂ) + I * η)
    (by rw [im_real_add_I_mul]; exact hη) x
  rw [im_real_add_I_mul] at h
  rw [norm_smul, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact h

theorem resolvent_apply_range (hA : IsSelfAdjoint A) (l : ℝ) {η : ℝ} (hη : η ≠ 0) (w : E) :
    (I * η) • resolvent A ((l : ℂ) + I * η) ((A - algebraMap ℂ (E →L[ℂ] E) l) w) =
      (I * η) • ((I * η) • resolvent A ((l : ℂ) + I * η) w - w) := by
  have hz : ((l : ℂ) + I * η) ∈ resolventSet ℂ A :=
    mem_resolventSet_of_im_ne_zero hA (by rw [im_real_add_I_mul]; exact hη)
  congr 1
  have e : (A - algebraMap ℂ (E →L[ℂ] E) l) w =
      (I * η) • w - (algebraMap ℂ (E →L[ℂ] E) ((l : ℂ) + I * η) - A) w := by
    simp only [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, add_smul,
      add_apply]
    abel
  rw [e, map_sub, resolvent_sub_apply hz, map_smul]

/-- On the range of `A − l`, `iη·R(l + iη) → 0`. -/
theorem tendsto_resolvent_range (hA : IsSelfAdjoint A) (l : ℝ) (w : E) :
    Tendsto (fun η : ℝ => (I * η) • resolvent A ((l : ℂ) + I * η)
      ((A - algebraMap ℂ (E →L[ℂ] E) l) w)) (𝓝[>] 0) (𝓝 0) := by
  have hb : ∀ η : ℝ, 0 < η → ‖(I * η) • resolvent A ((l : ℂ) + I * η)
      ((A - algebraMap ℂ (E →L[ℂ] E) l) w)‖ ≤ η * (2 * ‖w‖) := by
    intro η hη
    rw [resolvent_apply_range hA l hη.ne' w, norm_smul, norm_mul, norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
    refine mul_le_mul_of_nonneg_left ?_ hη.le
    calc ‖(I * η) • resolvent A ((l : ℂ) + I * η) w - w‖
        ≤ ‖(I * η) • resolvent A ((l : ℂ) + I * η) w‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ ‖w‖ + ‖w‖ := by gcongr; exact norm_smul_resolvent_apply_le hA l hη.ne' w
      _ = 2 * ‖w‖ := by ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun η hη => hb η hη) ?_
  have : Tendsto (fun η : ℝ => η * (2 * ‖w‖)) (𝓝 0) (𝓝 (0 * (2 * ‖w‖))) :=
    tendsto_id.mul_const _
  rw [zero_mul] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- On `(ker(A − l))ᗮ`, `iη·R(l + iη) → 0`. -/
theorem tendsto_resolvent_orthogonal (hA : IsSelfAdjoint A) (l : ℝ) {y : E}
    (hy : y ∈ (kerAt A l)ᗮ) :
    Tendsto (fun η : ℝ => (I * η) • resolvent A ((l : ℂ) + I * η) y) (𝓝[>] 0) (𝓝 0) := by
  rw [orthogonal_kerAt hA l] at hy
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hy
  obtain ⟨y', hy', hyy'⟩ := Metric.mem_closure_iff.1 hy (ε / 2) (by positivity)
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hy'
  have h2 := Metric.tendsto_nhds.1 (tendsto_resolvent_range hA l w) (ε / 2) (by positivity)
  filter_upwards [h2, self_mem_nhdsWithin] with η hη hpos
  rw [dist_zero_right] at hη ⊢
  have hpos' : (η : ℝ) ≠ 0 := (Set.mem_Ioi.1 hpos).ne'
  have hsplit : (I * η) • resolvent A ((l : ℂ) + I * η) y =
      (I * η) • resolvent A ((l : ℂ) + I * η) (y - (A - algebraMap ℂ (E →L[ℂ] E) l) w) +
      (I * η) • resolvent A ((l : ℂ) + I * η) ((A - algebraMap ℂ (E →L[ℂ] E) l) w) := by
    rw [map_sub, smul_sub, sub_add_cancel]
  rw [hsplit]
  calc ‖(I * η) • resolvent A ((l : ℂ) + I * η) (y - (A - algebraMap ℂ (E →L[ℂ] E) l) w) +
        (I * η) • resolvent A ((l : ℂ) + I * η) ((A - algebraMap ℂ (E →L[ℂ] E) l) w)‖
      ≤ ‖y - (A - algebraMap ℂ (E →L[ℂ] E) l) w‖ + ‖(I * η) • resolvent A ((l : ℂ) + I * η)
          ((A - algebraMap ℂ (E →L[ℂ] E) l) w)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_smul_resolvent_apply_le hA l hpos' _
    _ < ε / 2 + ε / 2 := by
        gcongr
        rw [← dist_eq_norm]; exact hyy'
    _ = ε := by ring

/-- **The limit at a real point**: `iη·R(l + iη)x → Px` as `η → 0+`, where `P` is the orthogonal
projection onto `ker(A − l)`. -/
theorem tendsto_resolvent_ker (hA : IsSelfAdjoint A) (l : ℝ) (x : E) :
    Tendsto (fun η : ℝ => (I * η) • resolvent A ((l : ℂ) + I * η) x) (𝓝[>] 0)
      (𝓝 ((kerAt A l).starProjection x)) := by
  set P := (kerAt A l).starProjection
  have hsplit : ∀ η : ℝ, 0 < η → (I * η) • resolvent A ((l : ℂ) + I * η) x =
      P x + (I * η) • resolvent A ((l : ℂ) + I * η) (x - P x) := by
    intro η hη
    rw [map_sub, smul_sub,
      resolvent_apply_of_mem_ker hA l hη.ne' (Submodule.starProjection_apply_mem _ x)]
    abel
  have h0 := tendsto_resolvent_orthogonal hA l (Submodule.sub_starProjection_mem_orthogonal x)
  have h1 : Tendsto (fun η : ℝ => P x + (I * η) • resolvent A ((l : ℂ) + I * η) (x - P x))
      (𝓝[>] 0) (𝓝 (P x + 0)) := tendsto_const_nhds.add h0
  rw [add_zero] at h1
  exact h1.congr' (eventually_nhdsWithin_of_forall fun η hη => (hsplit η hη).symm)

/-- **Along a curve**: if `ℓ(ε) = l + iεd + o(ε)` with `d > 0` and `Im ℓ(ε) ≥ cε`, `c > 0`, and
`x(ε) → x₀`, then `iε·R(ℓ(ε))x(ε) → d⁻¹·Px₀`. -/
theorem tendsto_resolvent_curve (hA : IsSelfAdjoint A) {l d c : ℝ} (hd : 0 < d) (hc : 0 < c)
    {ℓ : ℝ → ℂ} (hℓ : Tendsto (fun ε : ℝ => (ℓ ε - ((l : ℂ) + I * (ε * d))) / ε) (𝓝[>] 0) (𝓝 0))
    (him : ∀ ε : ℝ, 0 < ε → c * ε ≤ (ℓ ε).im) {x : ℝ → E} {x₀ : E}
    (hx : Tendsto x (𝓝[>] 0) (𝓝 x₀)) :
    Tendsto (fun ε : ℝ => (I * ε) • resolvent A (ℓ ε) (x ε)) (𝓝[>] 0)
      (𝓝 ((d⁻¹ : ℂ) • (kerAt A l).starProjection x₀)) := by
  -- the three pieces
  have hℓim : ∀ ε : ℝ, 0 < ε → (ℓ ε).im ≠ 0 := fun ε hε =>
    (lt_of_lt_of_le (mul_pos hc hε) (him ε hε)).ne'
  have hres : ∀ ε : ℝ, 0 < ε → ∀ y : E, ‖(I * ε) • resolvent A (ℓ ε) y‖ ≤ c⁻¹ * ‖y‖ := by
    intro ε hε y
    have h := abs_im_mul_norm_resolvent_le hA (hℓim ε hε) y
    have hi : c * ε ≤ |(ℓ ε).im| := (him ε hε).trans (le_abs_self _)
    rw [norm_smul, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    have : c * ε * ‖resolvent A (ℓ ε) y‖ ≤ ‖y‖ :=
      (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans h
    rw [show c⁻¹ * ‖y‖ = ‖y‖ / c by ring, le_div_iff₀ hc]
    nlinarith [norm_nonneg (resolvent A (ℓ ε) y)]
  -- piece (a): replace `x ε` by `x₀`
  have ha : Tendsto (fun ε : ℝ => (I * ε) • resolvent A (ℓ ε) (x ε) -
      (I * ε) • resolvent A (ℓ ε) x₀) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hx' : Tendsto (fun ε => c⁻¹ * ‖x ε - x₀‖) (𝓝[>] 0) (𝓝 (c⁻¹ * 0)) :=
      ((tendsto_iff_norm_sub_tendsto_zero.1 hx).const_mul _)
    rw [mul_zero] at hx'
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall fun ε hε => ?_) hx'
    rw [← smul_sub, ← map_sub]
    exact hres ε hε _
  -- piece (b): replace `ℓ ε` by `l + iεd`
  have hb : Tendsto (fun ε : ℝ => (I * ε) • resolvent A (ℓ ε) x₀ -
      (I * ε) • resolvent A ((l : ℂ) + I * (ε * d)) x₀) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hℓn : Tendsto (fun ε : ℝ => ‖(ℓ ε - ((l : ℂ) + I * (ε * d))) / ε‖) (𝓝[>] 0) (𝓝 0) := by
      simpa using hℓ.norm
    have hℓ' := hℓn.const_mul (c⁻¹ * d⁻¹ * ‖x₀‖)
    rw [mul_zero] at hℓ'
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall fun ε hε => ?_) hℓ'
    have hε0 : 0 < ε := hε
    have hε' : (ε : ℝ) ≠ 0 := hε0.ne'
    have hεd : ((l : ℂ) + I * ((ε * d : ℝ) : ℂ)).im ≠ 0 := by
      rw [im_real_add_I_mul]; exact mul_ne_zero hε' hd.ne'
    have hz1 := mem_resolventSet_of_im_ne_zero hA (hℓim ε hε0)
    have hz2 := mem_resolventSet_of_im_ne_zero hA hεd
    have e1 : ((l : ℂ) + I * (ε * d)) = ((l : ℂ) + I * ((ε * d : ℝ) : ℂ)) := by push_cast; ring
    rw [← smul_sub, e1, resolvent_apply_sub hz1 hz2, smul_comm]
    have hr2 := abs_im_mul_norm_resolvent_le hA hεd x₀
    rw [im_real_add_I_mul, abs_of_pos (mul_pos hε0 hd)] at hr2
    calc ‖((l : ℂ) + I * ((ε * d : ℝ) : ℂ) - ℓ ε) •
          ((I * ε) • resolvent A (ℓ ε) (resolvent A ((l : ℂ) + I * ((ε * d : ℝ) : ℂ)) x₀))‖
        = ‖((l : ℂ) + I * ((ε * d : ℝ) : ℂ) - ℓ ε)‖ *
          ‖(I * ε) • resolvent A (ℓ ε) (resolvent A ((l : ℂ) + I * ((ε * d : ℝ) : ℂ)) x₀)‖ :=
          norm_smul _ _
      _ ≤ ‖((l : ℂ) + I * ((ε * d : ℝ) : ℂ) - ℓ ε)‖ *
          (c⁻¹ * ‖resolvent A ((l : ℂ) + I * ((ε * d : ℝ) : ℂ)) x₀‖) := by
          gcongr; exact hres ε hε0 _
      _ ≤ ‖((l : ℂ) + I * ((ε * d : ℝ) : ℂ) - ℓ ε)‖ * (c⁻¹ * (‖x₀‖ / (ε * d))) := by
          gcongr
          rw [le_div_iff₀ (mul_pos hε0 hd), mul_comm]; exact hr2
      _ = c⁻¹ * d⁻¹ * ‖x₀‖ * ‖(ℓ ε - ((l : ℂ) + I * ((ε * d : ℝ) : ℂ))) / ε‖ := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0, ← norm_neg (ℓ ε - _),
            neg_sub]
          field_simp
  -- piece (c): the straight line `l + i(εd)`
  have hc' : Tendsto (fun ε : ℝ => (I * ε) • resolvent A ((l : ℂ) + I * (ε * d)) x₀) (𝓝[>] 0)
      (𝓝 ((d⁻¹ : ℂ) • (kerAt A l).starProjection x₀)) := by
    have hmap : Tendsto (fun ε : ℝ => ε * d) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun ε : ℝ => ε * d) (𝓝 0) (𝓝 (0 * d)) := tendsto_id.mul_const d
        rw [zero_mul] at this; exact this.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun ε hε => mul_pos hε hd
    have h := ((tendsto_resolvent_ker hA l x₀).comp hmap).const_smul (d⁻¹ : ℂ)
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_)
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [Function.comp, smul_smul]
    congr 1
    · push_cast; field_simp
    · push_cast; ring_nf
  have := (ha.add hb).add hc'
  rw [zero_add, zero_add] at this
  refine this.congr' (Eventually.of_forall fun ε => ?_)
  abel

end Limit

end Eis

end

#print axioms Eis.im_inner_apply_self
#print axioms Eis.abs_im_mul_norm_le
#print axioms Eis.mem_resolventSet_of_im_ne_zero
#print axioms Eis.sub_apply_resolvent
#print axioms Eis.resolvent_sub_apply
#print axioms Eis.abs_im_mul_norm_resolvent_le
#print axioms Eis.norm_resolvent_le
#print axioms Eis.hasDerivAt_resolvent_of_im_ne_zero
#print axioms Eis.algebraMap_sub_apply_eq
#print axioms Eis.resolvent_apply_sub
#print axioms Eis.isSelfAdjoint_sub_real
#print axioms Eis.orthogonal_kerAt
#print axioms Eis.im_real_add_I_mul
#print axioms Eis.resolvent_apply_of_mem_ker
#print axioms Eis.norm_smul_resolvent_apply_le
#print axioms Eis.resolvent_apply_range
#print axioms Eis.tendsto_resolvent_range
#print axioms Eis.tendsto_resolvent_orthogonal
#print axioms Eis.tendsto_resolvent_ker
#print axioms Eis.tendsto_resolvent_curve
