import EisensteinGaussSum
import PlanePoisson

/-! # Poisson summation over `ℤ[ω]` (round 294)

Round 293's `PlanePoisson.lattice_poisson` for the lattice `σ(ℤ[ω]) ⊂ ℂ`, with periodic twists
modulo `c` and the dual lattice described through `ℤ[ω]`. Here `σ` is the embedding of
`K = ℚ(ζ₃)` fixed in `EisensteinSymbol`, `ϖ = σ(ω)` and `δ = 1 + 2ω`, with `δ² = −3` (`δ3_sq`).

* **Coordinates.** `n ↦ n₀ + n₁ω` is a bijection `ℤ² ≃ ℤ[ω]` (`crdEquiv`). `σ(n₀ + n₁ω)` is
  `M_ϖ(n₀ + n₁i)` for the `ℝ`-linear automorphism `M_ϖ(x + iy) = x + yϖ` of `ℂ` (`σO_crd`), and
  `|det M_ϖ| = √3/2` (`abs_det_Mw`).
* **`eis_poisson`**: `Σ_{z∈ℤ[ω]} F(σz) = |det M_ϖ|⁻¹ Σ_{k∈ℤ²} 𝓕F(ξ_k)` with `ξ_k = (M_ϖ⁻¹)* k`.
  The dual points pair with the coordinates: `⟪σ(m₀ + m₁ω), ξ_k⟫ = m₀k₀ + m₁k₁` (`inner_σO_dual`).
* **The affine Fourier transform** (`fourier_affine`):
  `𝓕[F(a + b·)](ξ) = |b|⁻²·e(⟪a, ξ/b̄⟫)·𝓕F(ξ/b̄)`. With `|σ(x)|² = N(x)` (`normSq_σO`) it turns
  each coset sum into a dual sum.
* **`eis_poisson_twisted`**: for `f` periodic modulo `c ≠ 0` and representatives `rep` of
  `ℤ[ω]/c`, `Σ_z f(z)F(σz) = |det M_ϖ|⁻¹N(c)⁻¹ Σ_{k∈ℤ²} (Σ_i f(rep i)e(⟪σ(rep i), ξ_k/σc̄⟫))·𝓕F(ξ_k/σc̄)`.
* **The dual lattice through `ℤ[ω]`** (`ξd_eq`): `ξ_k = conj(2σ(μ_k)/σ(δ))` with
  `μ_k = (k₀ + k₁) + k₀ω`, and `k ↦ μ_k` is a bijection `ℤ² ≃ ℤ[ω]` (`μEquiv`).
* **The trace character** `ψ_c(x) = e(Re(2σ(x)/σ(δc)))` (classically `e(Tr(x/(δc)))`, since
  `Tr = 2 Re σ` on `K`) is additive (`ψc_add`) and periodic modulo `c` (`ψc_add_mul`).
* **`eis_poisson_trace`** and **`eis_poisson_quot`**: for `P` on `ℤ[ω]/c`,
  `Σ_z P(z mod c)F(σz) = 2/(√3·N(c))·Σ_{μ∈ℤ[ω]} (Σ_{r∈ℤ[ω]/c} P(r)ψ_c(rμ))·𝓕F(conj(2σ(μ)/σ(δc)))`.
  The inner sums are the twisted Gauss sums of round 291's S3.
-/

open NumberField Complex MeasureTheory PlanePoisson Ideal
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

noncomputable section

namespace Eis

/-- `ϖ = σ(ω)`. -/
def varpi : ℂ := σ ((ω : 𝓞 K) : K)

theorem varpi_sq_add : varpi ^ 2 + varpi + 1 = 0 := by
  have h := congrArg (σ.comp (algebraMap (𝓞 K) K)) ω_sq_add
  rw [map_add, map_add, map_pow, map_one, map_zero] at h
  exact h

theorem varpi_re_im : varpi.re = -1 / 2 ∧ varpi.im ^ 2 = 3 / 4 := by
  have h := varpi_sq_add
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re, Complex.add_im,
    Complex.mul_im, Complex.one_im, Complex.zero_im] at hre him
  have hb : varpi.im ≠ 0 := by
    intro hb
    rw [hb] at hre
    nlinarith [sq_nonneg (varpi.re + 1 / 2)]
  have ha : varpi.re = -1 / 2 := by
    have : varpi.im * (2 * varpi.re + 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 hb
    · linarith
  refine ⟨ha, ?_⟩
  rw [ha] at hre; nlinarith

theorem varpi_im_ne_zero : varpi.im ≠ 0 := by
  intro h; have := varpi_re_im.2; rw [h] at this; norm_num at this

/-- Coordinates: `n ↦ n₀ + n₁ω`. -/
def crd (n : Fin 2 → ℤ) : 𝓞 K := (n 0 : 𝓞 K) + (n 1 : 𝓞 K) * ω

theorem crd_injective : Function.Injective crd := by
  intro m n h
  have h' : crd m - crd n = 0 := sub_eq_zero.2 h
  set a := m 0 - n 0
  set b := m 1 - n 1
  have hab : ((a : ℤ) : 𝓞 K) + (b : 𝓞 K) * ω = 0 := by
    rw [← h']; simp only [crd, a, b]; push_cast; ring
  have hN := mul_cj_coords a b
  rw [hab, zero_mul] at hN
  have hz : a ^ 2 - a * b + b ^ 2 = 0 := by exact_mod_cast hN.symm
  have h4 : (2 * a - b) ^ 2 + 3 * b ^ 2 = 0 := by linear_combination 4 * hz
  have hb2 : b ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
  have hb : b = 0 := pow_eq_zero_iff (by norm_num) |>.1 hb2
  have ha2 : a ^ 2 = 0 := by rw [hb] at hz; linarith
  have ha : a = 0 := pow_eq_zero_iff (by norm_num) |>.1 ha2
  funext i; fin_cases i
  · simp only [Fin.zero_eta]; have : m 0 - n 0 = 0 := ha; omega
  · simp only [Fin.mk_one]; have : m 1 - n 1 = 0 := hb; omega

theorem crd_surjective : Function.Surjective crd := by
  intro x
  obtain ⟨m, n, rfl⟩ := exists_coords x
  exact ⟨![m, n], by simp [crd]⟩

/-- `ℤ² ≃ ℤ[ω]`. -/
def crdEquiv : (Fin 2 → ℤ) ≃ 𝓞 K := Equiv.ofBijective crd ⟨crd_injective, crd_surjective⟩

/-- The embedding `ℤ[ω] → ℂ`. -/
abbrev σO : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K)

theorem σO_ω : σO ω = varpi := rfl

/-- `z ↦ Re z + Im z·ϖ`. -/
def MwL : ℂ →ₗ[ℝ] ℂ where
  toFun z := (z.re : ℂ) + (z.im : ℂ) * varpi
  map_add' z w := by simp; ring
  map_smul' r z := by simp; ring

def MwInv : ℂ →ₗ[ℝ] ℂ where
  toFun w := ((w.re - varpi.re / varpi.im * w.im : ℝ) : ℂ) + ((w.im / varpi.im : ℝ) : ℂ) * I
  map_add' z w := by simp; ring
  map_smul' r z := by simp; ring

/-- The `ℝ`-linear automorphism of `ℂ` taking `ℤ²` onto `σ(ℤ[ω])`. -/
def Mw : ℂ ≃ₗ[ℝ] ℂ :=
  LinearEquiv.ofLinearMap MwL MwInv
    (LinearMap.ext fun w => by
      have hb := varpi_im_ne_zero
      apply Complex.ext
      · simp [MwL, MwInv]; field_simp; ring
      · simp [MwL, MwInv]; field_simp)
    (LinearMap.ext fun z => by
      have hb := varpi_im_ne_zero
      apply Complex.ext
      · simp [MwL, MwInv]; field_simp; ring
      · simp [MwL, MwInv]; field_simp)

theorem Mw_apply (z : ℂ) : Mw z = (z.re : ℂ) + (z.im : ℂ) * varpi := rfl

theorem σO_crd (n : Fin 2 → ℤ) : σO (crd n) = Mw (cpt (nR n)) := by
  rw [Mw_apply]
  simp only [crd, map_add, map_mul, map_intCast, σO_ω, cpt, nR]
  simp

/-- A Schwartz function is summable over `ℤ²`. -/
theorem summable_schwartz_lattice (G : SchwartzMap ℂ ℂ) :
    Summable fun n : Fin 2 → ℤ => G (cpt (nR n)) := by
  obtain ⟨C, hC0, hC⟩ := schwartz_decay' G
  refine Summable.of_norm_bounded (summable_lattice_inv.mul_left C) fun n => ?_
  have h := hC (cpt (nR n))
  have hpos : 0 < (1 + ‖cpt (nR n)‖) ^ 3 := by positivity
  rw [mul_one_div, le_div_iff₀ hpos, mul_comm]; exact h

/-- **Poisson summation over `ℤ[ω]`**: `Σ_{z∈ℤ[ω]} F(σz) = |det M_ϖ|⁻¹·Σ_{k∈ℤ²} 𝓕F(ξ_k)`, with
`ξ_k = (M_ϖ⁻¹)* k` the dual lattice. -/
theorem eis_poisson (F : SchwartzMap ℂ ℂ) :
    ∑' z : 𝓞 K, F (σO z) =
      |(LinearMap.det (Mw : ℂ →ₗ[ℝ] ℂ))⁻¹| *
        ∑' k : Fin 2 → ℤ, 𝓕 (F : ℂ → ℂ) (LinearMap.adjoint (Mw.symm : ℂ →ₗ[ℝ] ℂ) (cpt (nR k))) := by
  rw [← crdEquiv.tsum_eq]
  have : ∀ n, crdEquiv n = crd n := fun n => rfl
  simp_rw [this, σO_crd]
  exact lattice_poisson F Mw

/-- The dual lattice pairs with `ℤ[ω]` through the coordinates: `⟪σ(m₀ + m₁ω), ξ_k⟫ = m₀k₀ + m₁k₁`. -/
theorem inner_σO_dual (m k : Fin 2 → ℤ) :
    ⟪σO (crd m), LinearMap.adjoint (Mw.symm : ℂ →ₗ[ℝ] ℂ) (cpt (nR k))⟫ =
      ((m 0 * k 0 + m 1 * k 1 : ℤ) : ℝ) := by
  rw [LinearMap.adjoint_inner_right, σO_crd]
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  simp [Complex.inner, cpt, nR]
  ring

/-- Multiplication by `b ≠ 0`, as an `ℝ`-linear automorphism of `ℂ`. -/
def mulL (b : ℂ) (hb : b ≠ 0) : ℂ ≃ₗ[ℝ] ℂ :=
  LinearEquiv.ofLinearMap (LinearMap.mulLeft ℝ b) (LinearMap.mulLeft ℝ b⁻¹)
    (LinearMap.ext fun z => by simp [hb]) (LinearMap.ext fun z => by simp [hb])

theorem det_mulL (b : ℂ) (hb : b ≠ 0) :
    LinearMap.det (mulL b hb : ℂ →ₗ[ℝ] ℂ) = Complex.normSq b := by
  rw [← Algebra.norm_complex_apply, Algebra.norm_apply]; rfl

theorem adjoint_mulL_symm (b : ℂ) (hb : b ≠ 0) :
    LinearMap.adjoint ((mulL b hb).symm : ℂ →ₗ[ℝ] ℂ) = LinearMap.mulLeft ℝ (conj b)⁻¹ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp only [LinearMap.mulLeft_apply, mulL, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_coe,
    LinearEquiv.coe_ofLinearMap, Complex.inner]
  simp [map_inv₀]
  ring

/-- **The Fourier transform of `ζ ↦ F(a + bζ)`**:
`|b|⁻²·e(⟪a, ξ/b̄⟫)·𝓕F(ξ/b̄)`. -/
theorem fourier_affine (F : ℂ → ℂ) (a b : ℂ) (hb : b ≠ 0) (ξ : ℂ) :
    𝓕 (fun ζ => F (a + b * ζ)) ξ =
      ((Complex.normSq b)⁻¹ : ℝ) • (𝐞 (⟪a, ξ / conj b⟫) • 𝓕 F (ξ / conj b)) := by
  have hcomp : (fun ζ => F (a + b * ζ)) = (F ∘ fun w => w + a) ∘ (mulL b hb) := by
    funext ζ; simp [mulL, add_comm]
  rw [hcomp, fourier_comp_linearEquiv, det_mulL, adjoint_mulL_symm]
  have hpos : 0 < Complex.normSq b := Complex.normSq_pos.2 hb
  rw [abs_of_pos (inv_pos.2 hpos)]
  congr 1
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ ℂ) F a)
    (ξ / conj b)
  simp only [LinearMap.mulLeft_apply]
  rw [show (conj b)⁻¹ * ξ = ξ / conj b by ring]
  exact h

/-- Conjugation commutes with the embedding: `σ(x̄) = conj σ(x)`. -/
theorem σO_cj (x : 𝓞 K) : σO (cj x) = conj (σO x) := by
  obtain ⟨m, n, rfl⟩ := exists_coords x
  rw [cj_coords]
  have hv : conj varpi = -1 - varpi := by
    apply Complex.ext
    · simp [varpi_re_im.1]; norm_num
    · simp
  simp only [map_sub, map_add, map_mul, map_intCast, σO_ω, map_intCast]
  rw [hv]; push_cast; ring

/-- `|σ(x)|² = N(x)`. -/
theorem normSq_σO (x : 𝓞 K) : Complex.normSq (σO x) = (absNorm (span {x}) : ℝ) := by
  have h := congrArg σO (mul_cj_eq_absNorm x)
  rw [map_mul, σO_cj, map_natCast, Complex.mul_conj] at h
  exact_mod_cast h

/-- The dual lattice point `ξ_k = (M_ϖ⁻¹)* k`. -/
def ξd (k : Fin 2 → ℤ) : ℂ := LinearMap.adjoint (Mw.symm : ℂ →ₗ[ℝ] ℂ) (cpt (nR k))

/-- `ζ ↦ F(a + bζ)` as a Schwartz function. -/
def affS (F : SchwartzMap ℂ ℂ) (a b : ℂ) (hb : b ≠ 0) : SchwartzMap ℂ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulL b hb).toContinuousLinearEquiv
    (SchwartzMap.compSubConstCLM ℂ (-a) F)

theorem affS_apply (F : SchwartzMap ℂ ℂ) (a b : ℂ) (hb : b ≠ 0) (ζ : ℂ) :
    affS F a b hb ζ = F (a + b * ζ) := by
  show F (b * ζ - -a) = F (a + b * ζ)
  rw [sub_neg_eq_add, add_comm]

/-- A Schwartz function is summable over `σ(ℤ[ω])`. -/
theorem summable_σO (G : SchwartzMap ℂ ℂ) : Summable fun z : 𝓞 K => G (σO z) := by
  rw [← crdEquiv.summable_iff]
  have h : (fun z : 𝓞 K => G (σO z)) ∘ crdEquiv = fun n =>
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Mw.toContinuousLinearEquiv G) (cpt (nR n)) := by
    funext n
    show G (σO (crd n)) = G (Mw (cpt (nR n)))
    rw [σO_crd]
  rw [h]
  exact summable_schwartz_lattice _

/-- `𝓕G(ξ_k) = |det M_ϖ|·𝓕(G ∘ M_ϖ)(k)`. -/
theorem fourier_dual (G : SchwartzMap ℂ ℂ) (k : Fin 2 → ℤ) :
    𝓕 (G : ℂ → ℂ) (ξd k) = ((|LinearMap.det (Mw : ℂ →ₗ[ℝ] ℂ)| : ℝ) : ℂ) *
      𝓕 ((G : ℂ → ℂ) ∘ Mw) (cpt (nR k)) := by
  have hd : LinearMap.det (Mw : ℂ →ₗ[ℝ] ℂ) ≠ 0 := (LinearEquiv.isUnit_det' Mw).ne_zero
  rw [fourier_comp_linearEquiv, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, ← abs_mul,
    mul_inv_cancel₀ hd, abs_one, Complex.ofReal_one, one_mul]
  rfl

/-- The Fourier transform of a Schwartz function is summable over the dual lattice. -/
theorem summable_fourier_dual (G : SchwartzMap ℂ ℂ) :
    Summable fun k : Fin 2 → ℤ => 𝓕 (G : ℂ → ℂ) (ξd k) := by
  simp_rw [fourier_dual]
  refine Summable.mul_left _ ?_
  set H : SchwartzMap ℂ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Mw.toContinuousLinearEquiv G
  have hH : (H : ℂ → ℂ) = (G : ℂ → ℂ) ∘ Mw := rfl
  rw [← hH]
  exact summable_schwartz_lattice (𝓕 H)

/-- `𝓕(F(a + b·))(ξ) = |b|⁻²·e(⟪a, ξ/b̄⟫)·𝓕F(ξ/b̄)`, for the Schwartz function `affS`. -/
theorem fourier_affS (F : SchwartzMap ℂ ℂ) (a b : ℂ) (hb : b ≠ 0) (ξ : ℂ) :
    𝓕 (affS F a b hb : ℂ → ℂ) ξ =
      ((Complex.normSq b : ℂ))⁻¹ * ((𝐞 (⟪a, ξ / conj b⟫) : ℂ) * 𝓕 (F : ℂ → ℂ) (ξ / conj b)) := by
  have h : (affS F a b hb : ℂ → ℂ) = fun ζ => F (a + b * ζ) := funext (affS_apply F a b hb)
  rw [h, fourier_affine F a b hb, Complex.real_smul, Circle.smul_def, smul_eq_mul,
    Complex.ofReal_inv]

/-- `eis_poisson` with the dual points written `ξ_k`. -/
theorem eis_poisson' (G : SchwartzMap ℂ ℂ) :
    ∑' z : 𝓞 K, G (σO z) =
      ((|(LinearMap.det (Mw : ℂ →ₗ[ℝ] ℂ))⁻¹| : ℝ) : ℂ) * ∑' k : Fin 2 → ℤ, 𝓕 (G : ℂ → ℂ) (ξd k) :=
  eis_poisson G

/-- **Twisted Poisson summation over `ℤ[ω]`**: for `f` periodic modulo `c ≠ 0` and representatives
`rep : ι → ℤ[ω]` of the residues modulo `c` (each class once),
`Σ_{z∈ℤ[ω]} f(z)F(σz) = |det M_ϖ|⁻¹N(c)⁻¹ Σ_{k∈ℤ²} (Σ_i f(rep i)e(⟪σ(rep i), ξ_k/σc̄⟫))·𝓕F(ξ_k/σc̄)`. -/
theorem eis_poisson_twisted {ι : Type*} [Fintype ι] (F : SchwartzMap ℂ ℂ) (c : 𝓞 K) (hc : c ≠ 0)
    (f : 𝓞 K → ℂ) (hf : ∀ z u, f (z + c * u) = f z) (rep : ι → 𝓞 K)
    (hR : Function.Bijective (fun p : ι × 𝓞 K => rep p.1 + c * p.2)) :
    ∑' z : 𝓞 K, f z * F (σO z) =
      ((|(LinearMap.det (Mw : ℂ →ₗ[ℝ] ℂ))⁻¹| * ((absNorm (span {c}) : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑' k : Fin 2 → ℤ, (∑ i, f (rep i) * (𝐞 (⟪σO (rep i), ξd k / conj (σO c)⟫) : ℂ)) *
          𝓕 (F : ℂ → ℂ) (ξd k / conj (σO c)) := by
  have hc' : σO c ≠ 0 := fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  set D : ℂ := ((|(LinearMap.det (Mw : ℂ →ₗ[ℝ] ℂ))⁻¹| : ℝ) : ℂ) with hD
  let e : ι × 𝓞 K ≃ 𝓞 K := Equiv.ofBijective _ hR
  let g : 𝓞 K → ℂ := fun z => f z * F (σO z)
  let A : 𝓞 K → SchwartzMap ℂ ℂ := fun r => affS F (σO r) (σO c) hc'
  -- `f` is bounded by `Σ_i ‖f (rep i)‖`
  have hB : ∀ z, ‖f z‖ ≤ ∑ i, ‖f (rep i)‖ := by
    intro z
    obtain ⟨⟨i, u⟩, hiu⟩ := hR.2 z
    simp only at hiu
    rw [← hiu, hf]
    exact Finset.single_le_sum (f := fun i => ‖f (rep i)‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
  have hg : Summable g := by
    refine Summable.of_norm_bounded ((summable_σO F).norm.mul_left (∑ i, ‖f (rep i)‖))
      fun z => ?_
    simp only [g, norm_mul]
    exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)
  have hge : ∀ (i : ι) (u : 𝓞 K), g (e (i, u)) = f (rep i) * A (rep i) (σO u) := by
    intro i u
    show f (rep i + c * u) * F (σO (rep i + c * u)) =
      f (rep i) * affS F (σO (rep i)) (σO c) hc' (σO u)
    rw [hf, affS_apply, map_add, map_mul]
  have hfib : ∀ i : ι, Summable fun u : 𝓞 K => g (e (i, u)) := by
    intro i
    simp only [hge]
    exact (summable_σO _).mul_left _
  have hdual : ∀ r : 𝓞 K, Summable fun k : Fin 2 → ℤ => f r * 𝓕 (A r : ℂ → ℂ) (ξd k) :=
    fun r => (summable_fourier_dual _).mul_left _
  have h1 : ∑' z : 𝓞 K, f z * F (σO z) = ∑' (i : ι) (u : 𝓞 K), g (e (i, u)) := by
    have h := (e.summable_iff.2 hg).tsum_prod' hfib
    show ∑' z : 𝓞 K, g z = _
    rw [← e.tsum_eq g]
    exact h
  have h2 : ∀ i : ι, ∑' u : 𝓞 K, g (e (i, u)) =
      D * ∑' k : Fin 2 → ℤ, f (rep i) * 𝓕 (A (rep i) : ℂ → ℂ) (ξd k) := by
    intro i
    simp only [hge]
    rw [tsum_mul_left, eis_poisson', tsum_mul_left]
    ring
  have h3 : ∀ (r : 𝓞 K) (k : Fin 2 → ℤ), f r * 𝓕 (A r : ℂ → ℂ) (ξd k) =
      ((absNorm (span {c}) : ℝ) : ℂ)⁻¹ *
        (f r * (𝐞 (⟪σO r, ξd k / conj (σO c)⟫) : ℂ) * 𝓕 (F : ℂ → ℂ) (ξd k / conj (σO c))) := by
    intro r k
    simp only [A]
    rw [fourier_affS, normSq_σO]
    ring
  have h4 : ∑' (i : ι) (u : 𝓞 K), g (e (i, u)) =
      D * ∑' k : Fin 2 → ℤ, ∑ i, f (rep i) * 𝓕 (A (rep i) : ℂ → ℂ) (ξd k) := by
    rw [tsum_fintype, Finset.sum_congr rfl fun i _ => h2 i, ← Finset.mul_sum,
      Summable.tsum_finsetSum fun i _ => hdual (rep i)]
  have h5 : ∀ k : Fin 2 → ℤ, ∑ i, f (rep i) * 𝓕 (A (rep i) : ℂ → ℂ) (ξd k) =
      ((absNorm (span {c}) : ℝ) : ℂ)⁻¹ *
        ((∑ i, f (rep i) * (𝐞 (⟪σO (rep i), ξd k / conj (σO c)⟫) : ℂ)) *
          𝓕 (F : ℂ → ℂ) (ξd k / conj (σO c))) := by
    intro k
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => h3 (rep i) k
  rw [h1, h4, tsum_congr h5, tsum_mul_left, Complex.ofReal_mul, Complex.ofReal_inv, mul_assoc, hD]

/-- `δ = 1 + 2ω`, a square root of `−3`. -/
def δ3 : 𝓞 K := 1 + 2 * ω

theorem δ3_sq : δ3 ^ 2 = -3 := by
  unfold δ3; linear_combination 4 * ω_sq_add

theorem σO_δ3 : σO δ3 = 2 * (varpi.im : ℂ) * I := by
  have h : σO δ3 = 1 + 2 * varpi := by
    show σO (1 + 2 * ω) = 1 + 2 * varpi
    rw [map_add, map_one, map_mul, map_ofNat, σO_ω]
  rw [h]
  apply Complex.ext <;> simp [varpi_re_im.1]
  norm_num

theorem σO_δ3_ne_zero : σO δ3 ≠ 0 := by
  rw [σO_δ3]
  have := varpi_im_ne_zero
  simp [this, Complex.I_ne_zero]

/-- `2σ(a + bω)/σ(δ) = b − i(a − b/2)/Im ϖ`. -/
theorem two_σO_div_δ3 (a b : ℤ) :
    2 * σO ((a : 𝓞 K) + (b : 𝓞 K) * ω) / σO δ3 =
      (b : ℂ) - I * ((((a : ℝ) - b / 2) / varpi.im : ℝ) : ℂ) := by
  have hv := varpi_im_ne_zero
  rw [div_eq_iff σO_δ3_ne_zero, σO_δ3]
  simp only [map_add, map_mul, map_intCast, σO_ω]
  apply Complex.ext
  · simp [varpi_re_im.1]; field_simp; ring
  · simp [varpi_re_im.1]; field_simp

/-- `Re(2σ(y)/σ(δ))` is the `ω`-coordinate of `y`, an integer. -/
theorem re_two_σO_div_δ3 (a b : ℤ) :
    (2 * σO ((a : 𝓞 K) + (b : 𝓞 K) * ω) / σO δ3).re = b := by
  rw [two_σO_div_δ3]; simp

theorem exists_re_two_σO_div_δ3 (y : 𝓞 K) : ∃ n : ℤ, (2 * σO y / σO δ3).re = n := by
  obtain ⟨a, b, rfl⟩ := exists_coords y
  exact ⟨b, re_two_σO_div_δ3 a b⟩

/-- The dual coordinates: `μ_k = (k₀ + k₁) + k₀ω`. -/
def μk (k : Fin 2 → ℤ) : 𝓞 K := ((k 0 + k 1 : ℤ) : 𝓞 K) + (k 0 : 𝓞 K) * ω

theorem μk_bijective : Function.Bijective μk := by
  have hμ : μk = crd ∘ fun k : Fin 2 → ℤ => ![k 0 + k 1, k 0] := by
    funext k; simp [μk, crd]
  rw [hμ]
  refine (crdEquiv.bijective).comp ⟨fun m n h => ?_, fun m => ⟨![m 1, m 0 - m 1], ?_⟩⟩
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    funext i; fin_cases i
    · simpa using h1
    · simp only [Fin.mk_one]; omega
  · funext i; fin_cases i <;> simp

/-- `ℤ² ≃ ℤ[ω]` through `μ_k`. -/
def μEquiv : (Fin 2 → ℤ) ≃ 𝓞 K := Equiv.ofBijective μk μk_bijective

theorem ξd_re (k : Fin 2 → ℤ) : (ξd k).re = k 0 := by
  have h := inner_σO_dual ![1, 0] k
  have hc : σO (crd ![1, 0]) = 1 := by simp [crd]
  rw [hc] at h
  simpa [ξd, Complex.inner] using h

theorem ξd_im (k : Fin 2 → ℤ) : varpi.im * (ξd k).im = k 1 + k 0 / 2 := by
  have h := inner_σO_dual ![0, 1] k
  have hc : σO (crd ![0, 1]) = varpi := by simp [crd, σO_ω]
  rw [hc] at h
  have hr := ξd_re k
  simp only [ξd] at hr ⊢
  simp [Complex.inner, varpi_re_im.1] at h
  rw [hr] at h
  linarith

/-- **The dual lattice through `ℤ[ω]`**: `ξ_k = conj(2σ(μ_k)/σ(δ))`. -/
theorem ξd_eq (k : Fin 2 → ℤ) : ξd k = conj (2 * σO (μk k) / σO δ3) := by
  have hv := varpi_im_ne_zero
  rw [μk, two_σO_div_δ3, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
  apply Complex.ext
  · rw [ξd_re]; simp
  · have h := ξd_im k
    have him : (ξd k).im = (((k 0 + k 1 : ℤ) : ℝ) - (k 0 : ℝ) / 2) / varpi.im := by
      rw [eq_div_iff hv]; push_cast; linarith
    rw [him]; simp

/-- The trace phase modulo `c`: `x ↦ Re(2σ(x)/σ(δc))`, so that `e(·)` of it is `e(Tr(x/(δc)))`. -/
def trPhase (c x : 𝓞 K) : ℝ := (2 * σO x / σO (δ3 * c)).re

theorem trPhase_add (c x y : 𝓞 K) : trPhase c (x + y) = trPhase c x + trPhase c y := by
  simp only [trPhase, map_add, mul_add, add_div, Complex.add_re]

theorem trPhase_mul_left (c u : 𝓞 K) (hc : c ≠ 0) : ∃ n : ℤ, trPhase c (c * u) = n := by
  have hc' : σO c ≠ 0 := fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  obtain ⟨n, hn⟩ := exists_re_two_σO_div_δ3 u
  refine ⟨n, ?_⟩
  rw [trPhase, map_mul, map_mul, ← hn]
  congr 1
  field_simp

theorem fourierChar_intCast (n : ℤ) : (𝐞 (n : ℝ) : ℂ) = 1 := by
  rw [Real.fourierChar_apply]
  convert Complex.exp_int_mul_two_pi_mul_I n using 2
  push_cast; ring

/-- The additive character `ψ_c(x) = e(Tr(x/(δc)))` of `ℤ[ω]/c`. -/
def ψc (c x : 𝓞 K) : ℂ := 𝐞 (trPhase c x)

theorem ψc_add (c x y : 𝓞 K) : ψc c (x + y) = ψc c x * ψc c y := by
  simp only [ψc, trPhase_add, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem ψc_add_mul (c : 𝓞 K) (hc : c ≠ 0) (x u : 𝓞 K) : ψc c (x + c * u) = ψc c x := by
  obtain ⟨n, hn⟩ := trPhase_mul_left c u hc
  rw [ψc_add, ψc, ψc, hn, fourierChar_intCast, mul_one]

theorem inner_conj (z w : ℂ) : ⟪z, conj w⟫ = (z * w).re := by
  simp [Complex.inner]; ring

theorem det_Mw : LinearMap.det (Mw : ℂ →ₗ[ℝ] ℂ) = varpi.im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Mw_apply]

theorem abs_det_Mw : |LinearMap.det (Mw : ℂ →ₗ[ℝ] ℂ)| = Real.sqrt 3 / 2 := by
  rw [det_Mw, ← Real.sqrt_sq_eq_abs, varpi_re_im.2]
  rw [show (3 / 4 : ℝ) = (Real.sqrt 3 / 2) ^ 2 by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num]
  exact Real.sqrt_sq (by positivity)

/-- **Twisted Poisson summation over `ℤ[ω]`, algebraic form.** With the trace character
`ψ_c(x) = e(Tr(x/(δc)))` (`ψc`) and representatives `rep` of the residues modulo `c`,
`Σ_z f(z)F(σz) = 2/(√3·N(c)) Σ_{μ∈ℤ[ω]} (Σ_i f(rep i)ψ_c(rep i·μ))·𝓕F(conj(2σ(μ)/σ(δc)))`. -/
theorem eis_poisson_trace {ι : Type*} [Fintype ι] (F : SchwartzMap ℂ ℂ) (c : 𝓞 K) (hc : c ≠ 0)
    (f : 𝓞 K → ℂ) (hf : ∀ z u, f (z + c * u) = f z) (rep : ι → 𝓞 K)
    (hR : Function.Bijective (fun p : ι × 𝓞 K => rep p.1 + c * p.2)) :
    ∑' z : 𝓞 K, f z * F (σO z) =
      ((2 / (Real.sqrt 3 * (absNorm (span {c}) : ℝ)) : ℝ) : ℂ) *
        ∑' μ : 𝓞 K, (∑ i, f (rep i) * ψc c (rep i * μ)) *
          𝓕 (F : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * c))) := by
  rw [eis_poisson_twisted F c hc f hf rep hR, ← μEquiv.tsum_eq (fun μ =>
    (∑ i, f (rep i) * ψc c (rep i * μ)) * 𝓕 (F : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * c))))]
  congr 1
  · rw [abs_inv, abs_det_Mw]
    congr 1
    ring
  · refine tsum_congr fun k => ?_
    have hk : ξd k / conj (σO c) = conj (2 * σO (μk k) / σO (δ3 * c)) := by
      rw [ξd_eq, map_mul, ← map_div₀, div_div]
    have hμ : μEquiv k = μk k := rfl
    rw [hμ, hk]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [ψc, trPhase, inner_conj, map_mul σO (rep i) (μk k)]
    congr 3
    ring

/-- Representatives of `ℤ[ω]/c`. -/
def repQ (c : 𝓞 K) (r : 𝓞 K ⧸ span {c}) : 𝓞 K := Function.surjInv Ideal.Quotient.mk_surjective r

theorem repQ_mk (c : 𝓞 K) (r : 𝓞 K ⧸ span {c}) : Ideal.Quotient.mk (span {c}) (repQ c r) = r :=
  Function.surjInv_eq Ideal.Quotient.mk_surjective r

theorem mk_mul_left (c u : 𝓞 K) : Ideal.Quotient.mk (span {c}) (c * u) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right u _ (mem_span_singleton_self c))

/-- Every `z ∈ ℤ[ω]` is `rep(r) + cu` for exactly one residue `r` and one `u`. -/
theorem repQ_bijective (c : 𝓞 K) (hc : c ≠ 0) :
    Function.Bijective (fun p : (𝓞 K ⧸ span {c}) × 𝓞 K => repQ c p.1 + c * p.2) := by
  constructor
  · rintro ⟨r, u⟩ ⟨r', u'⟩ h
    simp only at h
    have hr : r = r' := by
      have h' := congrArg (Ideal.Quotient.mk (span {c})) h
      rwa [map_add, map_add, repQ_mk, repQ_mk, mk_mul_left, mk_mul_left, add_zero,
        add_zero] at h'
    subst hr
    have hu : u = u' := mul_left_cancel₀ hc (add_left_cancel h)
    rw [hu]
  · intro z
    have h : Ideal.Quotient.mk (span {c}) (z - repQ c (Ideal.Quotient.mk (span {c}) z)) = 0 := by
      rw [map_sub, repQ_mk, sub_self]
    obtain ⟨a, ha⟩ := mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    refine ⟨(Ideal.Quotient.mk (span {c}) z, a), ?_⟩
    simp only
    linear_combination ha

/-- **Poisson summation over `ℤ[ω]` twisted by a function on `ℤ[ω]/c`**:
`Σ_z P(z mod c)F(σz) = 2/(√3·N(c)) Σ_{μ∈ℤ[ω]} (Σ_{r∈ℤ[ω]/c} P(r)ψ_c(rμ))·𝓕F(conj(2σ(μ)/σ(δc)))`. -/
theorem eis_poisson_quot (F : SchwartzMap ℂ ℂ) (c : 𝓞 K) (hc : c ≠ 0)
    [Fintype (𝓞 K ⧸ span {c})] (P : 𝓞 K ⧸ span {c} → ℂ) :
    ∑' z : 𝓞 K, P (Ideal.Quotient.mk (span {c}) z) * F (σO z) =
      ((2 / (Real.sqrt 3 * (absNorm (span {c}) : ℝ)) : ℝ) : ℂ) *
        ∑' μ : 𝓞 K, (∑ r, P r * ψc c (repQ c r * μ)) *
          𝓕 (F : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * c))) := by
  have hf : ∀ z u, P (Ideal.Quotient.mk (span {c}) (z + c * u)) =
      P (Ideal.Quotient.mk (span {c}) z) := by
    intro z u; rw [map_add, mk_mul_left, add_zero]
  rw [eis_poisson_trace F c hc (fun z => P (Ideal.Quotient.mk (span {c}) z)) hf (repQ c)
    (repQ_bijective c hc)]
  simp only [repQ_mk]

end Eis

end

#print axioms Eis.varpi_re_im
#print axioms Eis.crd_injective
#print axioms Eis.σO_crd
#print axioms Eis.eis_poisson
#print axioms Eis.inner_σO_dual
#print axioms Eis.fourier_affine
#print axioms Eis.normSq_σO
#print axioms Eis.summable_σO
#print axioms Eis.summable_fourier_dual
#print axioms Eis.eis_poisson_twisted
#print axioms Eis.ξd_eq
#print axioms Eis.ψc_add
#print axioms Eis.ψc_add_mul
#print axioms Eis.abs_det_Mw
#print axioms Eis.eis_poisson_trace
#print axioms Eis.repQ_bijective
#print axioms Eis.eis_poisson_quot
