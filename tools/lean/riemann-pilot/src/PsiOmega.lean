import Mathlib
import LandauLaplace
import HurwitzCross
import ZetaInputs
import ParityCont

/-! # Zeros of `ζ` from one-sided bounds on summatory functions (rounds 220–221)

Landau's theorem for Laplace transforms (`LandauLaplace.lean`), applied to the Mellin integral
(`φ = log` on `(1, ∞)`), turns a one-sided bound on a summatory function into a zero-free half-plane.

**The generic theorem** (`zeta_ne_zero_of_mellin`, round 221). Let `A ≥ 0` on `(1, ∞)`, with
`∫_1^∞ A(x)x^{−s}dx = F(s)` on some right half-plane, where `F` is holomorphic on `Re s > θ` off the
zeros of `Z(s) = (s − 1)ζ(s)` (entire, `differentiable_Zr`) and has a pole at each zero. Then `ζ` has
no zero with `Re s > θ`. The proof: zero-free strips around the real axis and Landau's theorem give
convergence on `Re s > θ`; at the rightmost zero `ρ*` on a horizontal line, a zero-free strip to its
right makes `F` equal the transform, which is continuous at `ρ*`, while `F` has a pole there
(`LandauLaplace.pole_test`).

**Summatory functions.** For `S(x) = Σ_{k ≤ x} f(k)` with `|S(x)| ≤ Kx` and a one-sided bound
`ε(S(x) − κx) ≤ c·x^θ`, the input `A(x) = (c·x^θ − ε(S(x) − κx))/x` has
`∫_1^∞ A x^{−s} = c/(s − θ) − ε·L(f, s)/s + εκ/(s − 1)` (`lap_Aof`). Given a zero-free theorem, the
Ω± statement follows from `omega_of_zeroFree`.

**`ψ`** (round 220): `f = Λ`, `κ = 1`, `L(Λ, s) = −ζ′/ζ`.
* `zeta_ne_zero_of_psi`: `ε(ψ(x) − x) ≤ c·x^θ` on `(1, ∞)` makes `ζ ≠ 0` on `Re s > θ`.
* `psi_omega`: `ψ(x) − x = Ω±(x^θ)` for every `0 < θ < Re ρ`, `ρ` any zero.
* `exists_zero_re_ge_half`, `psi_omega_half`: a zero with `Re ρ ≥ ½` exists (Hadamard's identity), so
  `ψ(x) − x = Ω±(x^θ)` for every `0 < θ < ½`, unconditionally.

`MertensOmega.lean` applies the same theorem to `μ` and to Liouville's `λ`.

These are classical (Landau 1905). No bearing on RH: the bounds run from zeros to oscillation.
-/

open Real Complex MeasureTheory Filter Topology Set Metric

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## `Z(s) = (s − 1)ζ(s)` is entire -/

/-- `Z(s) = (s − 1)ζ(s)`, with its limit `1` at `s = 1`. -/
def Zr : ℂ → ℂ := Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

theorem Zr_of_ne {s : ℂ} (hs : s ≠ 1) : Zr s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

theorem Zr_eventuallyEq {s : ℂ} (hs : s ≠ 1) : Zr =ᶠ[𝓝 s] fun w => (w - 1) * riemannZeta w :=
  (eventually_ne_nhds hs).mono fun _ hw => Zr_of_ne hw

theorem differentiable_Zr : Differentiable ℂ Zr := by
  have hne : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ Zr s := fun s hs =>
    ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq
      (Zr_eventuallyEq hs)
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with t ht using hne t ht
    · simpa only [Zr, continuousAt_update_same] using riemannZeta_residue_one
  · exact hne s hs

theorem Zr_eq_zero {s : ℂ} (h : Zr s = 0) : s ≠ 1 ∧ riemannZeta s = 0 := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [Zr] at h
  · rw [Zr_of_ne hs] at h
    exact ⟨hs, (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hs)⟩

theorem zeta_ne_zero_re_ge_one {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- No real point `σ > 0` is a zero of `Z`. -/
theorem Zr_real_ne {σ : ℝ} (hσ : 0 < σ) : Zr σ ≠ 0 := fun h => by
  obtain ⟨h1, h0⟩ := Zr_eq_zero h
  rcases lt_or_ge σ 1 with hl | hl
  · exact zetaNoZeroInUnitInterval σ hσ hl h0
  · exact zeta_ne_zero_re_ge_one (by simpa using hl) h0

/-! ## The Mellin data -/

/-- `μ = dx` on `(1, ∞)`; the transform is `∫_1^∞ A(x)x^{−s}dx` with `φ = log`. -/
abbrev μ1 : Measure ℝ := volume.restrict (Ioi 1)

theorem cexp_log {x : ℝ} (hx : 0 < x) (s : ℂ) : cexp (-s * (Real.log x : ℂ)) = (x : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.2 hx.ne'), ← Complex.ofReal_log hx.le]; ring_nf

/-! ## The generic zero-free theorem

`Z` is entire with no zero on `Re s ≥ 1` and no real zero on `(θ, ∞)`. For `ζ`, `Z(s) = (s − 1)ζ(s)`;
for a nontrivial Dirichlet character, `Z = L(·, χ)` (DirichletOmega.lean). -/

section Generic

variable {Z : ℂ → ℂ}

/-- The hypotheses on `Z`: entire, no zero on `Re s ≥ 1`, no real zero in `(θ, ∞)`. -/
structure ZData (Z : ℂ → ℂ) (θ : ℝ) : Prop where
  diff : Differentiable ℂ Z
  ne_zero_re_ge_one : ∀ s : ℂ, 1 ≤ s.re → Z s ≠ 0
  real_ne_zero : ∀ σ : ℝ, θ < σ → Z σ ≠ 0

theorem ZData.mono {θ θ' : ℝ} (hZ : ZData Z θ) (h : θ ≤ θ') : ZData Z θ' :=
  ⟨hZ.diff, hZ.ne_zero_re_ge_one, fun σ hσ => hZ.real_ne_zero σ (by linarith)⟩

/-- **The zeros of `Z` are finite in every compact set.** -/
theorem ZData.zeros_finite {θ : ℝ} (hZ : ZData Z θ) {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ Z ⁻¹' {0}).Finite := by
  have hc := AnalyticOnNhd.preimage_zero_mem_codiscrete (f := Z) (x := 2)
    (fun z _ => hZ.diff.analyticAt z) (hZ.ne_zero_re_ge_one 2 (by norm_num))
  rw [Set.preimage_compl, compl_mem_codiscrete_iff] at hc
  exact (hS.inter_right hc.1).finite (hc.2.mono Set.inter_subset_right)

/-- **A zero-free strip around the real half-line `[a, ∞)`**, `a > θ`. -/
theorem ZData.strip_free {θ a : ℝ} (hZ : ZData Z θ) (ha : θ < a) :
    ∃ η > 0, ∀ s : ℂ, a ≤ s.re → |s.im| < η → Z s ≠ 0 := by
  classical
  set K : Set ℂ := closedBall 0 (|a| + 2) ∩ {s | a ≤ s.re} ∩ {s | |s.im| ≤ 1}
  have hK : IsCompact K := ((isCompact_closedBall 0 _).inter_right
    (isClosed_le continuous_const Complex.continuous_re)).inter_right
    (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hfin := hZ.zeros_finite hK
  obtain ⟨m, hm, hmS⟩ := exists_pos_lb hfin.toFinset (fun z => if z.im = 0 then 1 else |z.im|)
    fun z => by split_ifs with h
                · exact one_pos
                · exact abs_pos.2 h
  refine ⟨min m 1, lt_min hm one_pos, fun s hs hsi h0 => ?_⟩
  have hre1 : s.re < 1 := by
    by_contra h; exact hZ.ne_zero_re_ge_one s (not_lt.1 h) h0
  have hsK : s ∈ K ∩ Z ⁻¹' {0} := by
    refine ⟨⟨⟨?_, hs⟩, ?_⟩, h0⟩
    · rw [mem_closedBall, dist_zero_right]
      have := Complex.norm_le_abs_re_add_abs_im s
      have : |s.re| ≤ |a| + 1 := abs_le.2 ⟨by linarith [neg_abs_le a], by linarith [abs_nonneg a]⟩
      linarith [min_le_right m 1]
    · show |s.im| ≤ 1; linarith [min_le_right m 1]
  have := hmS s (hfin.mem_toFinset.2 hsK)
  by_cases hi : s.im = 0
  · have e : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hi])
    rw [e] at h0
    exact hZ.real_ne_zero _ (by linarith) h0
  · simp only [hi, ↓reduceIte] at this
    linarith [min_le_left m 1]

/-- **Step 1: the transform converges on `Re s > θ`.** -/
theorem conv_of_mellin_gen {A : ℝ → ℝ} {θ R0 σ₁ : ℝ} {F : ℂ → ℂ} (hZ : ZData Z θ)
    (hH : Hyp μ1 A Real.log) (h₁ : Conv μ1 A Real.log σ₁)
    (hFL : ∀ s : ℂ, R0 < s.re → F s = lap μ1 A Real.log s)
    (hFd : ∀ s : ℂ, θ < s.re → Z s ≠ 0 → DifferentiableAt ℂ F s) :
    ∀ σ, θ < σ → Conv μ1 A Real.log σ := by
  refine landau_abscissa hH h₁ fun c' hc' habove => ?_
  set a := (θ + c') / 2
  obtain ⟨η, hη, hZ'⟩ := hZ.strip_free (a := a) (by simp only [a]; linarith)
  set e := min η (c' - a)
  have he : 0 < e := lt_min hη (by simp only [a]; linarith)
  have hFd' : ∀ z : ℂ, a ≤ z.re → |z.im| < η → DifferentiableAt ℂ F z := fun z hz hzi =>
    hFd z (by simp only [a] at hz; linarith) (hZ' z hz hzi)
  set W : Set ℂ := {s | c' < s.re} ∩ ({s | s.im < η} ∩ {s | -η < s.im})
  have hWo : IsOpen W := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im))
  have hWc : Convex ℝ W := (convex_halfSpace_re_gt c').inter
    ((convex_halfSpace_im_lt η).inter (convex_halfSpace_im_gt (-η)))
  set z1 : ℝ := max c' R0 + 1
  have hEq : EqOn F (lap μ1 A Real.log) W := by
    refine eqOn_convex hWo hWc (fun z hz => (hFd' z (by
        have : c' < z.re := hz.1; simp only [a]; linarith)
      (abs_lt.2 ⟨by linarith [show -η < z.im from hz.2.2], by linarith [show z.im < η from hz.2.1]⟩)).differentiableWithinAt)
      ((lap_differentiableOn hH habove).mono fun z hz => hz.1) (z0 := (z1 : ℂ)) ?_
      (Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show R0 < (z1 : ℂ).re by rw [ofReal_re]; linarith [le_max_right c' R0])) fun s hs => hFL s hs)
    refine ⟨?_, ?_, ?_⟩
    · show c' < (z1 : ℂ).re; rw [ofReal_re]; linarith [le_max_left c' R0]
    · show (z1 : ℂ).im < η; rw [ofReal_im]; exact hη
    · show -η < (z1 : ℂ).im; rw [ofReal_im]; linarith
  refine ⟨e, he, F, fun z hz => ?_, fun s hs hsc => hEq ⟨hsc, ?_, ?_⟩⟩
  · rw [mem_ball, Complex.dist_eq] at hz
    have h1 := Complex.abs_re_le_norm (z - c')
    have h2 := Complex.abs_im_le_norm (z - c')
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h1 h2
    refine (hFd' z ?_ ?_).differentiableWithinAt
    · have := (abs_lt.1 (h1.trans_lt (hz.trans_le (min_le_right _ _)))).1; linarith
    · exact h2.trans_lt (hz.trans_le (min_le_left _ _))
  · rw [mem_ball, Complex.dist_eq] at hs
    have h2 := Complex.abs_im_le_norm (s - c')
    simp only [sub_im, ofReal_im, sub_zero] at h2
    exact (abs_lt.1 (h2.trans_lt (hs.trans_le (min_le_left _ _)))).2
  · rw [mem_ball, Complex.dist_eq] at hs
    have h2 := Complex.abs_im_le_norm (s - c')
    simp only [sub_im, ofReal_im, sub_zero] at h2
    exact (abs_lt.1 (h2.trans_lt (hs.trans_le (min_le_left _ _)))).1

/-- The pole hypothesis of the generic theorem: at a zero `ρ` of `Z` with `Z = (s − ρ)ⁿg` near `ρ`,
`F = G + h/(s − ρ)ᵐ` on `ρ + (0, ε)`, with `G`, `h` continuous at `ρ` and `h(ρ) ≠ 0`. -/
def PoleAt (F : ℂ → ℂ) (ρ : ℂ) : Prop :=
  ∃ ε > 0, ∃ (G h : ℂ → ℂ) (m : ℕ), m ≠ 0 ∧ ContinuousAt G ρ ∧ ContinuousAt h ρ ∧ h ρ ≠ 0 ∧
    ∀ x : ℝ, 0 < x → x < ε → F (ρ + x) = G (ρ + x) + h (ρ + x) / ((ρ + x) - ρ) ^ m

/-- **The generic zero-free theorem.** If `A ≥ 0` has Mellin transform `F` on a right half-plane, `F`
is holomorphic on `Re s > θ` off the zeros of `Z`, and `F` has a pole at every zero with `Re ρ > θ`,
then `Z` has no zero with `Re s > θ`. -/
theorem ne_zero_of_mellin {A : ℝ → ℝ} {θ R0 σ₁ : ℝ} {F : ℂ → ℂ} (hZ : ZData Z θ)
    (hH : Hyp μ1 A Real.log) (h₁ : Conv μ1 A Real.log σ₁)
    (hFL : ∀ s : ℂ, R0 < s.re → F s = lap μ1 A Real.log s)
    (hFd : ∀ s : ℂ, θ < s.re → Z s ≠ 0 → DifferentiableAt ℂ F s)
    (hpole : ∀ ρ : ℂ, θ < ρ.re → Z ρ = 0 → ∀ (n : ℕ) (g : ℂ → ℂ), n ≠ 0 →
      AnalyticAt ℂ g ρ → g ρ ≠ 0 → (∀ᶠ z in 𝓝 ρ, Z z = (z - ρ) ^ n * g z) → PoleAt F ρ)
    {ρ : ℂ} (hρθ : θ < ρ.re) : Z ρ ≠ 0 := by
  classical
  intro hρ
  set L := lap μ1 A Real.log
  have hLd : DifferentiableOn ℂ L {s | θ < s.re} :=
    lap_differentiableOn hH (conv_of_mellin_gen hZ hH h₁ hFL hFd)
  have hlt1 : ∀ z, Z z = 0 → z.re < 1 := fun z hz => by
    by_contra h'; exact hZ.ne_zero_re_ge_one z (not_lt.1 h') hz
  -- the zeros near `ρ`, and the rightmost one on the horizontal line through `ρ`
  set K : Set ℂ := closedBall 0 (2 * ‖ρ‖ + 3) ∩ {s | ρ.re ≤ s.re} ∩ {s | |s.im - ρ.im| ≤ 1}
  have hK : IsCompact K := ((isCompact_closedBall 0 _).inter_right
    (isClosed_le continuous_const Complex.continuous_re)).inter_right
    (isClosed_le (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const)
  have hfin := hZ.zeros_finite hK
  set S := hfin.toFinset
  have hmem : ∀ z : ℂ, Z z = 0 → ρ.re ≤ z.re → |z.im - ρ.im| ≤ 1 → z ∈ S := by
    intro z hz hzre hzim
    have hz1 := hlt1 z hz
    refine hfin.mem_toFinset.2 ⟨⟨⟨?_, hzre⟩, hzim⟩, hz⟩
    rw [mem_closedBall, dist_zero_right]
    have := Complex.norm_le_abs_re_add_abs_im z
    have := Complex.abs_im_le_norm ρ
    have := Complex.abs_re_le_norm ρ
    have : |z.re| ≤ ‖ρ‖ + 1 := abs_le.2 ⟨by linarith [neg_abs_le ρ.re], by linarith [norm_nonneg ρ]⟩
    have : |z.im| ≤ |ρ.im| + 1 := by have := abs_sub_abs_le_abs_sub z.im ρ.im; linarith
    linarith
  set cand := S.filter fun z => z.im = ρ.im
  have hρc : ρ ∈ cand := Finset.mem_filter.2 ⟨hmem ρ hρ le_rfl (by simp), rfl⟩
  obtain ⟨ps, hps, hmax⟩ := cand.exists_max_image Complex.re ⟨ρ, hρc⟩
  obtain ⟨hpsS, hpsim⟩ := Finset.mem_filter.1 hps
  have hpsK := hfin.mem_toFinset.1 hpsS
  have hps0 : Z ps = 0 := hpsK.2
  have hpsre : ρ.re ≤ ps.re := hpsK.1.1.2
  have hpsθ : θ < ps.re := lt_of_lt_of_le hρθ hpsre
  -- the zero-free strip to the right of `ps`
  obtain ⟨m, hm, hmS⟩ := exists_pos_lb S (fun z => if z.im = ρ.im then 1 else |z.im - ρ.im|)
    fun z => by split_ifs with h1
                · exact one_pos
                · exact abs_pos.2 (sub_ne_zero.2 h1)
  set δ := min m 1
  have hδ : 0 < δ := lt_min hm one_pos
  set U : Set ℂ := {s | ps.re < s.re} ∩ ({s | s.im < ρ.im + δ} ∩ {s | ρ.im - δ < s.im})
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im))
  have hUc : Convex ℝ U := (convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_im_lt _).inter (convex_halfSpace_im_gt _))
  have hZU : ∀ z ∈ U, Z z ≠ 0 := by
    intro z hz hz0
    have hU1 : ps.re < z.re := hz.1
    have hU2 : z.im < ρ.im + δ := hz.2.1
    have hU3 : ρ.im - δ < z.im := hz.2.2
    have hzS := hmem z hz0 (by linarith) (by
      rw [abs_le]; constructor <;> linarith [min_le_right m 1])
    by_cases hi : z.im = ρ.im
    · have := hmax z (Finset.mem_filter.2 ⟨hzS, hi⟩); linarith
    · have := hmS z hzS
      simp only [hi, ↓reduceIte] at this
      have : |z.im - ρ.im| < δ := abs_lt.2 ⟨by linarith, by linarith⟩
      linarith [min_le_left m 1]
  have hFU : DifferentiableOn ℂ F U := fun z hz =>
    (hFd z (lt_trans hpsθ (show ps.re < z.re from hz.1)) (hZU z hz)).differentiableWithinAt
  have hLU : DifferentiableOn ℂ L U := hLd.mono fun z hz => lt_trans hpsθ (show ps.re < z.re from hz.1)
  set z0 : ℂ := ((max R0 1 + 2 : ℝ) : ℂ) + ρ.im * I
  have hz0re : z0.re = max R0 1 + 2 := by simp [z0]
  have hz0im : z0.im = ρ.im := by simp [z0]
  have hEq : EqOn F L U := eqOn_convex hUo hUc hFU hLU (z0 := z0)
    ⟨show ps.re < z0.re by rw [hz0re]; linarith [le_max_right R0 1, hlt1 ps hps0],
      show z0.im < ρ.im + δ by rw [hz0im]; linarith,
      show ρ.im - δ < z0.im by rw [hz0im]; linarith⟩
    (Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show R0 < z0.re by rw [hz0re]; linarith [le_max_left R0 1])) fun s hs => hFL s hs)
  have hright : ∀ x : ℝ, 0 < x → ps + x ∈ U := fun x hx =>
    ⟨show ps.re < (ps + x).re by simp; linarith, show (ps + x).im < ρ.im + δ by simp [hpsim]; linarith,
      show ρ.im - δ < (ps + x).im by simp [hpsim]; linarith⟩
  -- the order of the zero at `ps`
  have hnot : ¬ ∀ᶠ z in 𝓝 ps, Z z = 0 := by
    intro hev
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have : dist (ps + ((r / 2 : ℝ) : ℂ)) ps < r := by
      rw [Complex.dist_eq, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    exact hZU _ (hright _ (by positivity)) (hball this)
  obtain ⟨n, g, hg, hg0, hZg⟩ :=
    (hZ.diff.analyticAt ps).exists_eventuallyEq_pow_smul_nonzero_iff.2 hnot
  have hn : n ≠ 0 := by
    rintro rfl
    have := hZg.self_of_nhds
    simp only [pow_zero, one_smul, hps0] at this
    exact hg0 this.symm
  obtain ⟨ε, hε, G, h, k, hk, hG, hh, hh0, hsplit⟩ := hpole ps hpsθ hps0 n g hn hg hg0
    (hZg.mono fun z hz => by rw [hz, smul_eq_mul])
  exact hh0 (pole_test hk hε
    ((hLd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpsθ)).continuousAt)
    hG hh fun x hx hxe => by rw [← hEq (hright x hx)]; exact hsplit x hx hxe)

end Generic

/-! ## The `ζ` instance -/

theorem zData_Zr {θ : ℝ} (hθ : 0 ≤ θ) : ZData Zr θ :=
  ⟨differentiable_Zr, fun s hs h => zeta_ne_zero_re_ge_one hs (Zr_eq_zero h).2,
    fun σ hσ => Zr_real_ne (by linarith)⟩

/-- **A zero-free strip around the real half-line `[a, ∞)`**, `a > 0`. -/
theorem strip_free {a : ℝ} (ha : 0 < a) : ∃ η > 0, ∀ s : ℂ, a ≤ s.re → |s.im| < η → Zr s ≠ 0 :=
  (zData_Zr le_rfl).strip_free ha

/-- **The generic zero-free theorem for `ζ`.** -/
theorem zeta_ne_zero_of_mellin {A : ℝ → ℝ} {θ R0 σ₁ : ℝ} {F : ℂ → ℂ} (hθ : 0 < θ)
    (hH : Hyp μ1 A Real.log) (h₁ : Conv μ1 A Real.log σ₁)
    (hFL : ∀ s : ℂ, R0 < s.re → F s = lap μ1 A Real.log s)
    (hFd : ∀ s : ℂ, θ < s.re → Zr s ≠ 0 → DifferentiableAt ℂ F s)
    (hpole : ∀ ρ : ℂ, θ < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → ∀ (n : ℕ) (g : ℂ → ℂ), n ≠ 0 →
      AnalyticAt ℂ g ρ → g ρ ≠ 0 → (∀ᶠ z in 𝓝 ρ, Zr z = (z - ρ) ^ n * g z) → PoleAt F ρ)
    {ρ : ℂ} (hρθ : θ < ρ.re) : riemannZeta ρ ≠ 0 := by
  intro hρ
  have hρ1 : ρ.re < 1 := by by_contra h'; exact zeta_ne_zero_re_ge_one (not_lt.1 h') hρ
  have hne : ρ ≠ 1 := fun e => by rw [e, one_re] at hρ1; exact lt_irrefl _ hρ1
  refine ne_zero_of_mellin (zData_Zr hθ.le) hH h₁ hFL hFd (fun q hq hZq => ?_) hρθ
    (by rw [Zr_of_ne hne, hρ, mul_zero])
  obtain ⟨-, hq0⟩ := Zr_eq_zero hZq
  exact hpole q hq (by by_contra h'; exact zeta_ne_zero_re_ge_one (not_lt.1 h') hq0) hq0

/-- The local factorisation near a zero, in the form the pole computations use: on a ball around
`ρ`, `Z = (w − ρ)ⁿg` near each point, `g` is analytic and `g ≠ 0`. -/
theorem local_factor {Z : ℂ → ℂ} {ρ : ℂ} {n : ℕ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g ρ) (hg0 : g ρ ≠ 0)
    (hZg : ∀ᶠ z in 𝓝 ρ, Z z = (z - ρ) ^ n * g z) :
    ∃ r > 0, ∀ x : ℝ, 0 < x → x < r →
      (Z =ᶠ[𝓝 (ρ + x)] fun w => (w - ρ) ^ n * g w) ∧ AnalyticAt ℂ g (ρ + x) ∧ g (ρ + x) ≠ 0 := by
  have hev : ∀ᶠ z in 𝓝 ρ, (∀ᶠ w in 𝓝 z, Z w = (w - ρ) ^ n * g w) ∧ AnalyticAt ℂ g z ∧ g z ≠ 0 :=
    hZg.eventually_nhds.and (hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hg0))
  obtain ⟨r0, hr0, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨r0, hr0, fun x hx hxr => ?_⟩
  have hzb : dist (ρ + (x : ℂ)) ρ < r0 := by
    rw [Complex.dist_eq, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hx.le]
    exact hxr
  exact hball hzb

/-! ## Summatory functions -/

/-- `S(x) = Σ_{1 ≤ k ≤ x} f(k)`. -/
def summ (f : ℕ → ℝ) (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, f k

theorem measurable_summ (f : ℕ → ℝ) : Measurable (summ f) :=
  (measurable_from_nat (f := fun n => ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor

/-- A linear bound `|S(x)| ≤ Kx` on the summatory function. -/
def LinBound (f : ℕ → ℝ) (K : ℝ) : Prop := ∀ x : ℝ, 0 ≤ x → |summ f x| ≤ K * x

/-- The Mellin input `A(x) = (c·x^θ − ε(S(x) − κx))/x`. -/
def Aof (f : ℕ → ℝ) (κ θ c ε : ℝ) (x : ℝ) : ℝ := (c * x ^ θ - ε * (summ f x - κ * x)) / x

variable {f : ℕ → ℝ} {κ θ c ε K : ℝ}

theorem measurable_Aof : Measurable (Aof f κ θ c ε) := by
  unfold Aof
  exact ((measurable_const.mul (measurable_id.pow_const θ)).sub (measurable_const.mul
    ((measurable_summ f).sub (measurable_const.mul measurable_id)))).div measurable_id

theorem hyp_Aof (h : ∀ x : ℝ, 1 < x → ε * (summ f x - κ * x) ≤ c * x ^ θ) :
    Hyp μ1 (Aof f κ θ c ε) Real.log where
  A_nonneg := (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) =>
    div_nonneg (by linarith [h x hx]) (by linarith))
  ph_nonneg := (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) =>
    Real.log_nonneg hx.le)
  A_meas := measurable_Aof.aestronglyMeasurable
  ph_meas := Real.measurable_log.aestronglyMeasurable

theorem abs_Aof_le (hK : LinBound f K) (hθ1 : θ ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    |Aof f κ θ c ε x| ≤ |c| + |ε| * (K + |κ|) := by
  have hx0 : 0 < x := by linarith
  have hS : |summ f x / x| ≤ K := by
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]; exact hK x hx0.le
  have hxθ : x ^ θ / x ≤ 1 := by
    rw [div_le_one hx0]
    calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ1
      _ = x := Real.rpow_one x
  have hxθ0 : 0 ≤ x ^ θ / x := by positivity
  have e : Aof f κ θ c ε x = c * (x ^ θ / x) - ε * (summ f x / x - κ) := by
    unfold Aof; field_simp
  rw [e]
  have h1 : |c * (x ^ θ / x)| ≤ |c| := by
    rw [abs_mul, abs_of_nonneg hxθ0]; exact mul_le_of_le_one_right (abs_nonneg c) hxθ
  have h2 : |ε * (summ f x / x - κ)| ≤ |ε| * (K + |κ|) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith)) (abs_nonneg ε)
  calc _ ≤ |c * (x ^ θ / x)| + |ε * (summ f x / x - κ)| := abs_sub _ _
    _ ≤ _ := by linarith

theorem conv_Aof_three (hK : LinBound f K) (hθ1 : θ ≤ 1) :
    Conv μ1 (Aof f κ θ c ε) Real.log 3 := by
  set B := |c| + |ε| * (K + |κ|)
  have hi : IntegrableOn (fun x : ℝ => B * x ^ (-3 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul B
  refine hi.mono' (measurable_Aof.mul (by fun_prop)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_))
  have hx0 : 0 < x := by linarith
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  have e : Real.exp (-3 * Real.log x) = x ^ (-3 : ℝ) := by
    rw [Real.rpow_def_of_pos hx0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right (abs_Aof_le hK hθ1 hx.le) (by positivity)

theorem integrand_eq {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (Aof f κ θ c ε x : ℂ) * cexp (-s * (Real.log x : ℂ))
      = c * (x : ℂ) ^ ((θ : ℂ) - 1 - s) - ε * ((summ f x : ℂ) * (x : ℂ) ^ (-(s + 1)))
        + ε * κ * (x : ℂ) ^ (-s) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  rw [cexp_log hx]
  have e1 : (x : ℂ) ^ ((θ : ℂ) - 1 - s) = (x : ℂ) ^ (θ : ℂ) * (x : ℂ) ^ (-s) / x := by
    rw [show (θ : ℂ) - 1 - s = (θ : ℂ) + -s - 1 by ring, Complex.cpow_sub _ _ hx0,
      Complex.cpow_add _ _ hx0, Complex.cpow_one]
  have e2 : (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) / x := by
    rw [show -(s + 1) = -s - 1 by ring, Complex.cpow_sub _ _ hx0, Complex.cpow_one]
  have e3 : ((x ^ θ : ℝ) : ℂ) = (x : ℂ) ^ (θ : ℂ) := Complex.ofReal_cpow hx.le θ
  rw [e1, e2]
  unfold Aof
  push_cast
  rw [e3]
  field_simp
  ring

theorem summ_sum_eq (f : ℕ → ℝ) (t : ℝ) :
    (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (f k : ℂ)) = (summ f t : ℂ) := by
  unfold summ; push_cast; rfl

/-- **`∫_1^∞ S(x)x^{−s−1}dx = L(f, s)/s`** for `Re s > 1`. -/
theorem integral_summ (hK : LinBound f K) {s : ℂ} (hs : 1 < s.re)
    (hsum : LSeriesSummable (fun n => (f n : ℂ)) s) :
    ∫ x in Ioi (1 : ℝ), (summ f x : ℂ) * (x : ℂ) ^ (-(s + 1))
      = LSeries (fun n => (f n : ℂ)) s / s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (f k : ℂ)) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound K (Eventually.of_forall fun n => ?_)
    rw [show (∑ k ∈ Finset.Icc 1 n, (f k : ℂ)) = ∑ k ∈ Finset.Icc 1 ⌊(n : ℝ)⌋₊, (f k : ℂ) by
      rw [Nat.floor_natCast], summ_sum_eq, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one,
      Real.norm_of_nonneg (Nat.cast_nonneg n)]
    exact hK n (Nat.cast_nonneg n)
  have H := LSeries_eq_mul_integral _ zero_le_one (by simpa using hs) hsum hO
  simp_rw [summ_sum_eq] at H
  rw [H]; field_simp

theorem integrableOn_summ (hK : LinBound f K) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (summ f x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hi : IntegrableOn (fun x : ℝ => K * x ^ (-s.re)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine hi.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_))
  · refine ((Complex.continuous_ofReal.measurable.comp (measurable_summ f)).mul
      ?_).aestronglyMeasurable.restrict
    exact (Complex.continuous_ofReal.measurable).pow_const _
  · have hx0 : 0 < x := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
    rw [hre]
    have hp := hK x hx0.le
    have e : x ^ (-s.re - 1) = x ^ (-s.re) / x := by
      rw [Real.rpow_sub hx0, Real.rpow_one]
    rw [e]
    calc |summ f x| * (x ^ (-s.re) / x) ≤ K * x * (x ^ (-s.re) / x) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by field_simp

/-- **The transform of a summatory input.** For `Re s > 1`,
`∫_1^∞ A(x)x^{−s}dx = c/(s − θ) − ε·L(f, s)/s + εκ/(s − 1)`. -/
theorem lap_Aof (hK : LinBound f K) (hθ1 : θ ≤ 1) {s : ℂ} (hs : 1 < s.re)
    (hsum : LSeriesSummable (fun n => (f n : ℂ)) s) :
    lap μ1 (Aof f κ θ c ε) Real.log s
      = c / (s - θ) - ε * (LSeries (fun n => (f n : ℂ)) s / s) + ε * κ / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hsθ : s - θ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have i1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((θ : ℂ) - 1 - s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have i2 := integrableOn_summ hK hs
  have i3 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  unfold lap
  rw [setIntegral_congr_fun measurableSet_Ioi fun x (hx : 1 < x) => integrand_eq (by linarith) s]
  have i12 : IntegrableOn (fun x : ℝ => (c : ℂ) * (x : ℂ) ^ ((θ : ℂ) - 1 - s)
      - ε * ((summ f x : ℂ) * (x : ℂ) ^ (-(s + 1)))) (Ioi 1) :=
    (i1.const_mul _).sub (i2.const_mul _)
  rw [integral_add i12 (i3.const_mul _), integral_sub (i1.const_mul _) (i2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_summ hK hs hsum,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  have h1 : (θ : ℂ) - 1 - s + 1 ≠ 0 := by
    rw [show (θ : ℂ) - 1 - s + 1 = -(s - θ) by ring]; exact neg_ne_zero.2 hsθ
  have h2 : -s + 1 ≠ 0 := by rw [show -s + 1 = -(s - 1) by ring]; exact neg_ne_zero.2 hs1
  simp only [ofReal_one, one_cpow]
  field_simp
  ring

/-- **Ω± from a zero-free theorem.** If every one-sided bound `ε(S(x) − κx) ≤ c·x^θ` on `(1, ∞)`
(`ε = ±1`) is impossible, then `S(x) − κx` exceeds `c·x^θ` and falls below `−c·x^θ` at arbitrarily
large `x`, whatever `c`. -/
theorem omega_of_zeroFree (hK : LinBound f K) (hθ : 0 < θ)
    (hZF : ∀ c ε : ℝ, (ε = 1 ∨ ε = -1) → (∀ x : ℝ, 1 < x → ε * (summ f x - κ * x) ≤ c * x ^ θ) → False)
    (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < summ f x - κ * x) ∧ (∃ x, X < x ∧ summ f x - κ * x < -(c * x ^ θ)) := by
  set X' := max X 1
  have hX' : 1 ≤ X' := le_max_right _ _
  set c' := |c| + (|K| + |κ|) * X'
  have hc'0 : 0 ≤ (|K| + |κ|) * X' := by positivity
  have hcc' : c ≤ c' := by simp only [c']; linarith [le_abs_self c]
  have hsmall : ∀ x : ℝ, 1 < x → x ≤ X' → |summ f x - κ * x| ≤ c' * x ^ θ := fun x hx hxX => by
    have h1 := hK x (by linarith)
    have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx.le hθ.le
    have h2 : |summ f x - κ * x| ≤ (|K| + |κ|) * X' := by
      calc |summ f x - κ * x| ≤ |summ f x| + |κ * x| := abs_sub _ _
        _ ≤ |K| * x + |κ| * x := by
            rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < x)]
            nlinarith [le_abs_self K]
        _ ≤ (|K| + |κ|) * X' := by nlinarith [abs_nonneg K, abs_nonneg κ]
    have h3 : 0 ≤ (|K| + |κ|) * X' := by positivity
    calc |summ f x - κ * x| ≤ (|K| + |κ|) * X' := h2
      _ ≤ (|K| + |κ|) * X' * x ^ θ := le_mul_of_one_le_right h3 hxθ
      _ ≤ c' * x ^ θ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); simp only [c']; linarith [abs_nonneg c]
  constructor
  · by_contra hno
    push Not at hno
    refine hZF c' 1 (Or.inl rfl) fun x hx => ?_
    rw [one_mul]
    rcases le_or_gt x X' with hxX | hxX
    · exact (le_abs_self _).trans (hsmall x hx hxX)
    · have h1 := hno x (lt_of_le_of_lt (le_max_left _ _) hxX)
      have : c * x ^ θ ≤ c' * x ^ θ := mul_le_mul_of_nonneg_right hcc' (by positivity)
      linarith
  · by_contra hno
    push Not at hno
    refine hZF c' (-1) (Or.inr rfl) fun x hx => ?_
    rw [neg_one_mul]
    rcases le_or_gt x X' with hxX | hxX
    · exact (neg_le_abs _).trans (hsmall x hx hxX)
    · have h1 := hno x (lt_of_le_of_lt (le_max_left _ _) hxX)
      have : c * x ^ θ ≤ c' * x ^ θ := mul_le_mul_of_nonneg_right hcc' (by positivity)
      linarith

/-! ## `ψ` -/

theorem summ_vonMangoldt (x : ℝ) : summ (fun n => ArithmeticFunction.vonMangoldt n) x = Chebyshev.psi x := by
  unfold summ Chebyshev.psi; rw [← Finset.Icc_succ_left_eq_Ioc]; rfl

theorem linBound_vonMangoldt : LinBound (fun n => ArithmeticFunction.vonMangoldt n) (Real.log 4 + 4) :=
  fun x hx => by
    rw [summ_vonMangoldt, abs_of_nonneg (Chebyshev.psi_nonneg x)]
    exact Chebyshev.psi_le_const_mul_self hx

/-- `F(s) = c/(s − θ) + ε(Z′/(sZ) + b/s)`: the transform of `c·x^θ − ε·Σ_{n ≤ x} f(n)` when
`L(f, s) = −Z′/Z − b/(s − 1)`. -/
def FZ (Z : ℂ → ℂ) (θ c ε b : ℝ) (s : ℂ) : ℂ := c / (s - θ) + ε * (deriv Z s / (s * Z s) + b / s)

/-- For `ψ`: `Z(s) = (s − 1)ζ(s)` and `b = 1`. -/
abbrev Fψ (θ c ε : ℝ) : ℂ → ℂ := FZ Zr θ c ε 1

theorem deriv_Zr {s : ℂ} (hs : s ≠ 1) :
    deriv Zr s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  rw [(Zr_eventuallyEq hs).deriv_eq]
  have h : HasDerivAt (fun w => (w - 1) * riemannZeta w)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
  rw [h.deriv]; ring

/-- **The transform equals `F` for `Re s > 1`.** -/
theorem lap_eq_Fψ (hθ1 : θ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    lap μ1 (Aof (fun n => ArithmeticFunction.vonMangoldt n) 1 θ c ε) Real.log s = Fψ θ c ε s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl _ hs
  have hζ : riemannZeta s ≠ 0 := zeta_ne_zero_re_ge_one hs.le
  rw [lap_Aof linBound_vonMangoldt hθ1 hs (ArithmeticFunction.LSeriesSummable_vonMangoldt hs),
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  unfold Fψ FZ
  rw [deriv_Zr hs1, Zr_of_ne hs1]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  push_cast
  field_simp
  ring

/-- `F` is holomorphic wherever `s ≠ θ`, `s ≠ 0` and `Z(s) ≠ 0`. -/
theorem FZ_differentiableAt {Z : ℂ → ℂ} {b : ℝ} (hZd : Differentiable ℂ Z) {s : ℂ} (h1 : s ≠ θ)
    (h0 : s ≠ 0) (hZ : Z s ≠ 0) : DifferentiableAt ℂ (FZ Z θ c ε b) s := by
  have hd : DifferentiableAt ℂ (deriv Z) s := (hZd.analyticAt s).deriv.differentiableAt
  have hz : DifferentiableAt ℂ Z s := hZd s
  have hθ : s - θ ≠ 0 := sub_ne_zero.2 h1
  have hsz : s * Z s ≠ 0 := mul_ne_zero h0 hZ
  unfold FZ
  fun_prop (disch := assumption)

/-- **The pole of `F` at a zero**: `F = G + (εn/ρ)/(s − ρ)`. -/
theorem FZ_pole {Z : ℂ → ℂ} {b : ℝ} (hε : ε ≠ 0) {ρ : ℂ} (hρθ : θ < ρ.re) (hθ : 0 < θ) {n : ℕ}
    {g : ℂ → ℂ} (hn : n ≠ 0) (hg : AnalyticAt ℂ g ρ) (hg0 : g ρ ≠ 0)
    (hZg : ∀ᶠ z in 𝓝 ρ, Z z = (z - ρ) ^ n * g z) : PoleAt (FZ Z θ c ε b) ρ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hρ0 : ρ ≠ 0 := fun e => by rw [e, zero_re] at hρθ; linarith
  obtain ⟨r0, hr0, hloc⟩ := local_factor hg hg0 hZg
  refine ⟨r0, hr0, fun z => c / (z - θ) + ε * (-((k + 1 : ℕ) : ℂ) / (ρ * z) + deriv g z / (z * g z)
    + b / z), fun _ => ε * ((k + 1 : ℕ) : ℂ) / ρ, 1, one_ne_zero, ?_, continuousAt_const, ?_,
    fun x hx hxr => ?_⟩
  · have hθρ : ρ - θ ≠ 0 := fun e => by
      have := congrArg Complex.re e; simp at this; linarith
    have hdg : ContinuousAt (deriv g) ρ := hg.deriv.continuousAt
    have hgc : ContinuousAt g ρ := hg.continuousAt
    exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hθρ).add
      (continuousAt_const.mul ((((continuousAt_const.div (continuousAt_const.mul continuousAt_id)
        (mul_ne_zero hρ0 hρ0))).add (hdg.div (continuousAt_id.mul hgc) (mul_ne_zero hρ0 hg0))).add
        (continuousAt_const.div continuousAt_id hρ0)))
  · exact div_ne_zero (mul_ne_zero (by exact_mod_cast hε) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero k))) hρ0
  · obtain ⟨hZz, hgz, hgz0⟩ := hloc x hx hxr
    set z := ρ + (x : ℂ)
    have hu0 : z - ρ ≠ 0 := by simp only [z, add_sub_cancel_left]; exact_mod_cast hx.ne'
    have hz0 : z ≠ 0 := fun e => by
      have : (ρ + (x : ℂ)).re = ρ.re + x := by simp
      rw [show ρ + (x : ℂ) = z from rfl, e, zero_re] at this; linarith
    have hderiv : deriv Z z = ((k + 1 : ℕ) : ℂ) * (z - ρ) ^ k * g z + (z - ρ) ^ (k + 1) * deriv g z := by
      rw [hZz.deriv_eq]
      have h1 : HasDerivAt (fun w => (w - ρ) ^ (k + 1) * g w)
          (((k + 1 : ℕ) : ℂ) * (z - ρ) ^ k * 1 * g z + (z - ρ) ^ (k + 1) * deriv g z) z :=
        (((hasDerivAt_id z).sub_const ρ).pow (k + 1)).mul hgz.differentiableAt.hasDerivAt
      rw [h1.deriv]; ring
    have hZz' : Z z = (z - ρ) ^ (k + 1) * g z := hZz.self_of_nhds
    unfold FZ
    rw [hderiv, hZz', pow_one]
    have hpk : (z - ρ) ^ k ≠ 0 := pow_ne_zero _ hu0
    field_simp
    ring

/-- **Landau's oscillation theorem, one-sided form.** If `ε(ψ(x) − x) ≤ c·x^θ` for every `x > 1`,
with `ε ≠ 0` and `0 < θ ≤ 1`, then `ζ` has no zero with `Re s > θ`. -/
theorem zeta_ne_zero_of_psi (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hε : ε ≠ 0)
    (h : ∀ x : ℝ, 1 < x → ε * (Chebyshev.psi x - x) ≤ c * x ^ θ) {ρ : ℂ} (hρθ : θ < ρ.re) :
    riemannZeta ρ ≠ 0 := by
  have h' : ∀ x : ℝ, 1 < x →
      ε * (summ (fun n => ArithmeticFunction.vonMangoldt n) x - 1 * x) ≤ c * x ^ θ := fun x hx => by
    rw [summ_vonMangoldt, one_mul]; exact h x hx
  refine zeta_ne_zero_of_mellin (F := Fψ θ c ε) (R0 := 1) hθ (hyp_Aof h')
    (conv_Aof_three linBound_vonMangoldt hθ1) (fun s hs => (lap_eq_Fψ hθ1 hs).symm)
    (fun s hs hZ => FZ_differentiableAt differentiable_Zr (fun e => by rw [e, ofReal_re] at hs; exact lt_irrefl _ hs)
      (fun e => by rw [e, zero_re] at hs; linarith) hZ)
    (fun ρ hρθ _ _ n g hn hg hg0 hZg => FZ_pole hε hρθ hθ hn hg hg0 hZg) hρθ

/-! ## The Ω± statements for `ψ` -/

/-- **Landau's oscillation theorem.** For every zero `ρ` of `ζ` and every `0 < θ < Re ρ`, whatever
`c` and `X`, `ψ(x) − x` exceeds `c·x^θ` at some `x > X`, and falls below `−c·x^θ` at some `x > X`:
`ψ(x) − x = Ω±(x^θ)`. -/
theorem psi_omega {ρ : ℂ} (hρ : riemannZeta ρ = 0) {θ : ℝ} (hθ : 0 < θ) (hθρ : θ < ρ.re) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < Chebyshev.psi x - x) ∧
      (∃ x, X < x ∧ Chebyshev.psi x - x < -(c * x ^ θ)) := by
  have hρ1 : ρ.re < 1 := by by_contra h'; exact zeta_ne_zero_re_ge_one (not_lt.1 h') hρ
  have H := omega_of_zeroFree (κ := 1) linBound_vonMangoldt hθ (fun c ε hε h =>
    zeta_ne_zero_of_psi (c := c) (ε := ε) hθ (by linarith) (by rcases hε with rfl | rfl <;> norm_num)
      (fun x hx => by have := h x hx; rwa [summ_vonMangoldt, one_mul] at this) hθρ hρ) c X
  simp only [summ_vonMangoldt, one_mul] at H
  exact H

/-- `2 + γ − log 4π > 0` (true value 0.0462). -/
theorem hadamard_const_pos : 0 < 2 + eulerMascheroniConstant - Real.log (4 * π) := by
  have hγ := gamma_gt
  have hlog4pi : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    norm_num
  have hl2 := Real.log_two_lt_d9
  have hlpi : Real.log π < 1.15 := by
    rw [Real.log_lt_iff_lt_exp Real.pi_pos]
    have h := Real.sum_le_exp_of_nonneg (x := 1.15) (by norm_num) 8
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    have hπ := Real.pi_lt_d6
    linarith
  rw [hlog4pi]
  norm_num at hγ hl2 ⊢
  linarith

/-- `ρ ↦ 1 − ρ` preserves the nontrivial zeros. -/
theorem IsNontrivialZero.one_sub {s : ℂ} (hs : IsNontrivialZero s) : IsNontrivialZero (1 - s) := by
  rw [nontrivial_iff_Xi]
  have e : (1 - s - 1 / 2) / I = -((s - 1 / 2) / I) := by ring
  rw [e, Xi_even, ← nontrivial_iff_Xi]; exact hs

/-- **A zero-free half-plane `Re s > θ` puts every nontrivial zero in the band** `|2 Re s − 1| ≤ 2θ − 1`
(round 335; six proofs of the stack wrote this out). -/
theorem band_of_zeroFree {θ : ℝ} (hzf : ∀ ρ : ℂ, θ < ρ.re → riemannZeta ρ ≠ 0) {s : ℂ}
    (hs : IsNontrivialZero s) : |2 * s.re - 1| ≤ 2 * θ - 1 := by
  have h1 : s.re ≤ θ := by by_contra hc; exact hzf s (not_le.1 hc) hs.1
  have h2 : (1 - s).re ≤ θ := by
    by_contra hc; exact hzf _ (not_le.1 hc) (IsNontrivialZero.one_sub hs).1
  rw [Complex.sub_re, Complex.one_re] at h2
  rw [abs_le]; constructor <;> linarith

/-- **A zero-free half-plane `Re s > ½` is RH** (round 335). -/
theorem rh_of_zeroFree_half (hzf : ∀ ρ : ℂ, 1 / 2 < ρ.re → riemannZeta ρ ≠ 0) :
    RiemannHypothesis := by
  intro s hs htriv _
  have h := band_of_zeroFree hzf ⟨hs, htriv⟩
  have h0 : |2 * s.re - 1| ≤ 0 := by linarith
  have := abs_nonpos_iff.1 h0
  linarith

/-- **`ζ` has a zero with `½ ≤ Re ρ < 1`.** Hadamard's identity sums `1/(ρ(1 − ρ))` over the nontrivial
zeros to `2 + γ − log 4π ≠ 0`, so there is one; `ρ ↦ 1 − ρ` preserves them. -/
theorem exists_zero_re_ge_half : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re := by
  have hne : Nonempty ZIdx := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hasSum_empty.unique hadamard_zeta
    have h0 : (2 + eulerMascheroniConstant - Real.log (4 * π) : ℝ) = 0 := by exact_mod_cast this.symm
    linarith [hadamard_const_pos]
  obtain ⟨q⟩ := hne
  have hs : IsNontrivialZero (zetaZeroFamily q) := q.1.2
  set s := zetaZeroFamily q
  rcases le_or_gt (1 / 2) s.re with h | h
  · exact ⟨s, hs.1, h⟩
  · exact ⟨1 - s, (IsNontrivialZero.one_sub hs).1, by simp; linarith⟩

/-- **`ψ(x) − x = Ω±(x^θ)` for every `0 < θ < ½`, unconditionally.** -/
theorem psi_omega_half {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 1 / 2) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < Chebyshev.psi x - x) ∧
      (∃ x, X < x ∧ Chebyshev.psi x - x < -(c * x ^ θ)) := by
  obtain ⟨ρ, hρ, hre⟩ := exists_zero_re_ge_half
  exact psi_omega hρ hθ (by linarith) c X

end PsiOmega

#print axioms PsiOmega.zeta_ne_zero_of_mellin
#print axioms PsiOmega.lap_Aof
#print axioms PsiOmega.omega_of_zeroFree
#print axioms PsiOmega.zeta_ne_zero_of_psi
#print axioms PsiOmega.psi_omega
#print axioms PsiOmega.exists_zero_re_ge_half
#print axioms PsiOmega.psi_omega_half
#print axioms PsiOmega.band_of_zeroFree
#print axioms PsiOmega.rh_of_zeroFree_half
