import EisensteinGaussTransform
import PlaneGaussian

/-! # Quadratic Gauss sums over `ℤ[ω]` (round 297)

S3 of round 291's plan, part 3: the quadratic Gauss sums of `ℤ[ω]`, evaluated by Poisson summation with
round 296's Gaussian chirps, as in Appendix A.1 of the release's companion paper. The sum
`Σ_{x mod c} ψ_c(x²)` is round 295's Gauss transform `G_c(qphase c, 0)`, where `qphase c x = ψ_c(x²)`
for round 294's trace character `ψ_c`.

* **Gaussian Poisson summation modulo `m`** (`gauss_poisson`): round 295's `eis_poisson_gaussTr` for
  the Gaussian, whose Fourier transform is `a⁻¹e^{-π|ξ|²/a}` (`fourier_gaussC`). As `a → 0⁺` the zero
  frequency dominates (**`tendsto_gauss_poisson`**): `a·Σ_x f(x)e^{-πa|σx|²} → 2G_m(f, 0)/(√3·N(m))`,
  by dominated convergence with the uniform bound on `G_m(f, ·)` (`exists_norm_gaussTr_le`). At
  `m = 1` it gives the lattice sums `Σ_μ e^{-πaN(μ)} ≤ C/a` and `Σ_μ N(μ)e^{-πaN(μ)} ≤ C/a²` for
  `0 < a ≤ 1` (`exists_tsum_exp_le`, `exists_tsum_mul_exp_le`).
* **The chirp** (`chirp_σO`, `chirp_sum_dual`): `ψ_c(x²)e^{-πη|σx|²}` is round 296's chirp with
  `w_c = 2/σ(δc)`, evaluated at `σx`. Round 294's `eis_poisson'` gives
  `Σ_x ψ_c(x²)e^{-πη|σx|²} = (2/√3)·Σ_μ 𝓕F_η(conj(2σ(μ)/σ(δ)))`. By `fourier_chirp` and `re_wq_dual`,
  each term is `D^{-1/2}e^{-πεN(μ)}·P₂(μ)·e(R(μ)η²/(2D))` (**`dual_term`**), where `D = η² + 4|w_c|²`,
  `ε = 4η/(3D)`, `R(μ) = Re(σ(cμ²)/σ(δ))` and `P₂(μ) = e(-R(μ)/2)`. `P₂` is periodic modulo `2`
  (`P2_periodic`).
* **The limit** (`eta_sum_decomp`, `tendsto_main`, `tendsto_err`): `η·Σ_x ψ_c(x²)e^{-πη|σx|²}` is a
  main term plus an error. The main term tends to `(|w_c|/2)·G_2(P₂, 0)`, by `tendsto_gauss_poisson` at
  `m = 2`, since `ε → 0⁺`. The error is at most `K·η·√D` for small `η`, from `|e(t) − 1| ≤ 2π|t|`,
  `|R(μ)| ≤ |σc|·N(μ)/√3` (`norm_Rq_le`) and the second lattice sum.
* **`quad_gauss`**: by uniqueness of limits, for every `c ≠ 0`,
  `Σ_{x mod c} ψ_c(x²) = (|σc|/2)·Σ_{y mod 2} e(-Re(σ(cy²)/σ(δ))/2)`.
* **`quad_gauss_coords`**: the residues modulo `2` are `0, 1, ω, 1 + ω` (`rep2_bijective`,
  `gaussTr_two`), and `P₂(μ) = i^{-n}` for `n` the `ω`-coordinate of `cμ²` (`P2_coord`). So for
  `c = a + bω ≠ 0`, `Σ_{x mod c} ψ_c(x²) = (|σc|/2)·(1 + i^{-b} + i^a + i^{b-a})`.

In the paper's notation (`ω = e^{2πi/3}`, `e(z) = exp(4πi·Im z/√3)`), `ψ_c(x) = e(x/c)` and
`P₂(y) = e(-cy²/4)`, whichever root `σ(ω)` is. So `quad_gauss` is the paper's
`Γ_quad(c) = |c|⁻¹Σ_{x mod c} e(x²/c) = ½Σ_{y mod 2} e(-cy²/4)`, and `quad_gauss_coords` is its
`Γ_quad(a + bω) = (1 + i^{-b} + i^a + i^{b-a})/2`. The paper states the first for `c` coprime to `2`;
the proof here needs only `c ≠ 0`.
-/

open NumberField Complex Ideal Filter Topology
open scoped ComplexConjugate FourierTransform RealInnerProductSpace Real

noncomputable section

namespace Eis

open PlaneGaussian

/-- `𝓕[e^{-πa|z|²}](ξ) = a⁻¹e^{-π|ξ|²/a}`. -/
theorem fourier_gaussC (a : ℝ) (ha : 0 < a) (ξ : ℂ) :
    𝓕 (gaussC a ha : ℂ → ℂ) ξ = ((a⁻¹ : ℝ) : ℂ) * cexp (-(π : ℂ) * ‖ξ‖ ^ 2 / a) := by
  have h : (gaussC a ha : ℂ → ℂ) = fun v => cexp (-((π * a : ℝ) : ℂ) * ‖v‖ ^ 2) := by
    funext v; rw [gaussC_apply, Complex.ofReal_exp]; push_cast; ring_nf
  have hb : 0 < (((π * a : ℝ) : ℂ)).re := by simp; positivity
  rw [h, fourier_gaussian_innerProductSpace hb, finrank_real_complex]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : ((2 : ℕ) : ℂ) / 2 = 1 := by norm_num
  rw [h2, Complex.cpow_one]
  push_cast
  field_simp

/-- `|σ(δ)|² = 3`. -/
theorem norm_σO_δ3_sq : ‖σO δ3‖ ^ 2 = 3 := by
  rw [σO_δ3]
  simp [mul_pow, Complex.norm_I]
  rw [varpi_re_im.2]; norm_num

theorem sq_norm_σO (x : 𝓞 K) : ‖σO x‖ ^ 2 = (absNorm (span {x}) : ℝ) := by
  rw [Complex.sq_norm, normSq_σO]

/-- The dual frequencies have `|conj(2σ(ν)/σ(δm))|² = 4N(ν)/(3N(m))`. -/
theorem norm_dual_sq (m ν : 𝓞 K) :
    ‖conj (2 * σO ν / σO (δ3 * m))‖ ^ 2 =
      4 * (absNorm (span {ν}) : ℝ) / (3 * (absNorm (span {m}) : ℝ)) := by
  rw [Complex.norm_conj, norm_div, norm_mul, map_mul, norm_mul, div_pow, mul_pow, mul_pow,
    norm_σO_δ3_sq, sq_norm_σO, sq_norm_σO]
  norm_num

/-- The Gauss transform is bounded uniformly in the frequency. -/
theorem exists_norm_gaussTr_le (m : 𝓞 K) (hm : m ≠ 0) (f : 𝓞 K → ℂ) :
    ∃ B, ∀ ν, ‖gaussTr m f ν‖ ≤ B := by
  have : Finite (𝓞 K ⧸ span {m}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let : Fintype (𝓞 K ⧸ span {m}) := Fintype.ofFinite _
  refine ⟨∑ r, ‖f (repQ m r)‖, fun ν => ?_⟩
  rw [gaussTr, finsum_eq_sum_of_fintype]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul]
  have : ‖ψc m (repQ m r * ν)‖ = 1 := by simp [ψc]
  rw [this, mul_one]

/-- **Gaussian Poisson summation over `ℤ[ω]`, twisted modulo `m`**. -/
theorem gauss_poisson (m : 𝓞 K) (hm : m ≠ 0) (f : 𝓞 K → ℂ) (hf : ∀ z u, f (z + m * u) = f z)
    (a : ℝ) (ha : 0 < a) :
    ∑' x : 𝓞 K, f x * gaussC a ha (σO x) =
      ((2 / (Real.sqrt 3 * (absNorm (span {m}) : ℝ) * a) : ℝ) : ℂ) *
        ∑' ν : 𝓞 K, gaussTr m f ν *
          cexp (-(π : ℂ) * ((4 * (absNorm (span {ν}) : ℝ) /
            (3 * (absNorm (span {m}) : ℝ)) : ℝ) : ℂ) / a) := by
  rw [eis_poisson_gaussTr (gaussC a ha) m hm f hf]
  have hN : (0 : ℝ) < absNorm (span {m}) := by
    have : (absNorm (span {m}) : ℕ) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hm
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun ν => ?_
  rw [fourier_gaussC, ← Complex.ofReal_pow, norm_dual_sq]
  push_cast
  field_simp

theorem absNorm_pos (m : 𝓞 K) (hm : m ≠ 0) : (0 : ℝ) < absNorm (span {m}) := by
  have : (absNorm (span {m}) : ℕ) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hm
  exact_mod_cast Nat.pos_of_ne_zero this

/-- Gaussians are summable over `σ(ℤ[ω])`: `Σ_ν e^{-πb N(ν)} < ∞` for `b > 0`. -/
theorem summable_exp_absNorm {b : ℝ} (hb : 0 < b) :
    Summable fun ν : 𝓞 K => Real.exp (-(π * b) * (absNorm (span {ν}) : ℝ)) := by
  have h := (summable_σO (gaussC b hb)).norm
  refine h.congr fun ν => ?_
  rw [gaussC_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sq_norm_σO]

/-- **The zero mode dominates as `a → 0⁺`**: `a·Σ_x f(x)e^{-πa|σx|²} → 2G_m(f, 0)/(√3·N(m))`. -/
theorem tendsto_gauss_poisson (m : 𝓞 K) (hm : m ≠ 0) (f : 𝓞 K → ℂ)
    (hf : ∀ z u, f (z + m * u) = f z) :
    Tendsto (fun a : ℝ => (a : ℂ) * ∑' x : 𝓞 K, f x * (Real.exp (-(π * a) * ‖σO x‖ ^ 2) : ℂ))
      (𝓝[>] 0) (𝓝 (((2 / (Real.sqrt 3 * (absNorm (span {m}) : ℝ)) : ℝ) : ℂ) * gaussTr m f 0)) := by
  set N : ℝ := (absNorm (span {m}) : ℝ) with hNdef
  have hN : 0 < N := absNorm_pos m hm
  set cν : 𝓞 K → ℝ := fun ν => 4 * (absNorm (span {ν}) : ℝ) / (3 * N) with hcν
  have hc0 : ∀ ν, 0 ≤ cν ν := fun ν => by simp only [hcν]; positivity
  have heq : ∀ a : ℝ, 0 < a →
      (a : ℂ) * ∑' x : 𝓞 K, f x * (Real.exp (-(π * a) * ‖σO x‖ ^ 2) : ℂ) =
        (((2 / (Real.sqrt 3 * N)) : ℝ) : ℂ) *
          ∑' ν : 𝓞 K, gaussTr m f ν * ((Real.exp (-(π * cν ν) / a) : ℝ) : ℂ) := by
    intro a ha
    have h := gauss_poisson m hm f hf a ha
    have hl : (∑' x : 𝓞 K, f x * (Real.exp (-(π * a) * ‖σO x‖ ^ 2) : ℂ)) =
        ∑' x : 𝓞 K, f x * gaussC a ha (σO x) := rfl
    rw [hl, h, ← mul_assoc]
    congr 1
    · have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      rw [hNdef]; push_cast; field_simp
    · refine tsum_congr fun ν => ?_
      congr 1
      rw [Complex.ofReal_exp]; congr 1; simp only [hcν, hNdef]; push_cast; ring
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun a ha => (heq a ha).symm) ?_
  refine Tendsto.const_mul _ ?_
  classical
  obtain ⟨B, hB⟩ := exists_norm_gaussTr_le m hm f
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hsum : Summable fun ν : 𝓞 K => B * Real.exp (-(π * cν ν)) := by
    have := (summable_exp_absNorm (show (0 : ℝ) < 4 / (3 * N) by positivity)).mul_left B
    refine this.congr fun ν => ?_
    simp only [hcν]; congr 2; ring
  have key := @tendsto_tsum_of_dominated_convergence ℝ (𝓞 K) ℂ (𝓝[>] (0 : ℝ)) _ _
    (fun a ν => gaussTr m f ν * ((Real.exp (-(π * cν ν) / a) : ℝ) : ℂ))
    (fun ν => if ν = 0 then gaussTr m f 0 else 0) _ hsum ?_ ?_
  · rwa [tsum_ite_eq] at key
  · intro ν
    by_cases hν : ν = 0
    · subst hν
      have : cν 0 = 0 := by simp [hcν]
      simp only [this, mul_zero, neg_zero, zero_div, Real.exp_zero, Complex.ofReal_one, mul_one,
        ↓reduceIte]
      exact tendsto_const_nhds
    · simp only [hν, ↓reduceIte]
      have hpos : 0 < cν ν := by
        simp only [hcν]
        have := absNorm_pos ν hν
        positivity
      have h1 : Tendsto (fun a : ℝ => Real.exp (-(π * cν ν) / a)) (𝓝[>] 0) (𝓝 0) := by
        have h2 : Tendsto (fun a : ℝ => -(π * cν ν) / a) (𝓝[>] 0) atBot := by
          have := tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg
            (show -(π * cν ν) < 0 by have := Real.pi_pos; nlinarith)
          simpa [div_eq_mul_inv] using this
        exact Real.tendsto_exp_atBot.comp h2
      have h3 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa using h3.const_mul (gaussTr m f ν)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with a ha ν
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hB ν) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hB0
    have hpc : 0 ≤ π * cν ν := mul_nonneg Real.pi_pos.le (hc0 ν)
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ ha.1]
    nlinarith [ha.2]

/-- The chirp coefficient `w_c = 2/σ(δc)`. -/
def wq (c : 𝓞 K) : ℂ := 2 / (σO δ3 * σO c)

/-- The quadratic phase `x ↦ ψ_c(x²)`. -/
def qphase (c x : 𝓞 K) : ℂ := ψc c (x * x)

theorem sq_periodic (c t : 𝓞 K) (hc : c ≠ 0) (z u : 𝓞 K) :
    ψc c (t * ((z + c * u) * (z + c * u))) = ψc c (t * (z * z)) := by
  have : t * ((z + c * u) * (z + c * u)) = t * (z * z) + c * (t * (2 * z * u + c * u * u)) := by
    ring
  rw [this, ψc_add_mul c hc]

theorem qphase_periodic (c : 𝓞 K) (hc : c ≠ 0) (z u : 𝓞 K) :
    qphase c (z + c * u) = qphase c z := by
  simpa [qphase] using sq_periodic c 1 hc z u

/-- On `σ(ℤ[ω])` the chirp is `ψ_c(x²)·e^{-πη|σx|²}`. -/
theorem chirp_σO (c : 𝓞 K) (η : ℝ) (hη : 0 < η) (x : 𝓞 K) :
    chirp (fun z => (wq c * z ^ 2).re) η hη (σO x) =
      qphase c x * (Real.exp (-(π * η) * ‖σO x‖ ^ 2) : ℂ) := by
  rw [chirp_apply (quadPhase_temperate _)]
  congr 1
  rw [qphase, ψc, trPhase, Real.fourierChar_apply, wq]
  congr 2
  rw [map_mul, map_mul]
  congr 1
  ring_nf

/-- **The direct side**: `Σ_x ψ_c(x²)e^{-πη|σx|²} = (2/√3)·Σ_μ 𝓕F_η(conj(2σ(μ)/σ(δ)))`. -/
theorem chirp_sum_dual (c : 𝓞 K) (η : ℝ) (hη : 0 < η) :
    ∑' x : 𝓞 K, qphase c x * (Real.exp (-(π * η) * ‖σO x‖ ^ 2) : ℂ) =
      ((2 / Real.sqrt 3 : ℝ) : ℂ) * ∑' μ : 𝓞 K,
        𝓕 (chirp (fun z => (wq c * z ^ 2).re) η hη : ℂ → ℂ) (conj (2 * σO μ / σO δ3)) := by
  have h := eis_poisson' (chirp (fun z => (wq c * z ^ 2).re) η hη)
  simp_rw [chirp_σO] at h
  rw [h, abs_inv, abs_det_Mw]
  congr 1
  · have h3 : Real.sqrt 3 ≠ 0 := by positivity
    push_cast; field_simp
  · rw [← μEquiv.tsum_eq]
    refine tsum_congr fun k => ?_
    rw [ξd_eq]; rfl

theorem absNorm_one_span : (absNorm (span {(1 : 𝓞 K)}) : ℝ) = 1 := by
  rw [Ideal.span_singleton_one, Ideal.absNorm_top]; simp

/-- `|conj(2σ(μ)/σ(δ))|² = 4N(μ)/3`. -/
theorem norm_dualμ_sq (μ : 𝓞 K) :
    ‖conj (2 * σO μ / σO δ3)‖ ^ 2 = 4 * (absNorm (span {μ}) : ℝ) / 3 := by
  have h := norm_dual_sq 1 μ
  rw [mul_one, absNorm_one_span, mul_one] at h
  exact h

theorem conj_two : conj (2 : ℂ) = 2 := by apply Complex.ext <;> simp

theorem conj_σO_δ3 : conj (σO δ3) = -σO δ3 := by
  rw [σO_δ3, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, conj_two]; ring

theorem σO_δ3_sq : σO δ3 ^ 2 = -3 := by
  have := congrArg σO δ3_sq
  rw [map_pow] at this; rw [this, map_neg, map_ofNat]

/-- The dual phase: `Re(w_c·conj(2σ(μ)/σ(δ))²) = 2|w_c|²·Re(σ(cμ²)/σ(δ))`. -/
theorem re_wq_dual (c μ : 𝓞 K) (hc : c ≠ 0) :
    (wq c * (conj (2 * σO μ / σO δ3)) ^ 2).re =
      2 * ‖wq c‖ ^ 2 * (σO (c * μ * μ) / σO δ3).re := by
  have hγ : σO c ≠ 0 := fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  have hs : σO δ3 ≠ 0 := σO_δ3_ne_zero
  have hγn : (‖σO c‖ : ℂ) ^ 2 = conj (σO c) * σO c := by rw [conj_mul']
  rw [← Complex.conj_re]
  have hconj : conj (wq c * (conj (2 * σO μ / σO δ3)) ^ 2) =
      8 * (σO c * σO μ ^ 2) / (3 * σO δ3 * (‖σO c‖ : ℂ) ^ 2) := by
    rw [map_mul, map_pow, Complex.conj_conj, wq, map_div₀, map_mul, conj_σO_δ3, hγn, conj_two]
    rw [div_pow, σO_δ3_sq]
    have hcj : conj (σO c) ≠ 0 := (map_ne_zero _).2 hγ
    field_simp
    ring
  rw [hconj]
  have hnw : ‖wq c‖ ^ 2 = 4 / (3 * ‖σO c‖ ^ 2) := by
    rw [wq, norm_div, norm_mul, div_pow, mul_pow, norm_σO_δ3_sq]; norm_num
  rw [hnw, map_mul, map_mul]
  have hγr : 0 < ‖σO c‖ := norm_pos_iff.2 hγ
  rw [show (8 : ℂ) * (σO c * (σO μ ^ 2)) / (3 * σO δ3 * (‖σO c‖ : ℂ) ^ 2) =
    ((8 / (3 * ‖σO c‖ ^ 2) : ℝ) : ℂ) * (σO c * (σO μ * σO μ) / σO δ3) by
      push_cast; field_simp]
  rw [Complex.re_ofReal_mul]
  ring_nf

/-- `R(μ) = Re(σ(cμ²)/σ(δ))`. -/
def Rq (c μ : 𝓞 K) : ℝ := (σO (c * μ * μ) / σO δ3).re

/-- The phase `P₂(μ) = e(-R(μ)/2)` of the dual side, periodic modulo `2`. -/
def P2 (c μ : 𝓞 K) : ℂ := 𝐞 (-(Rq c μ / 2))

theorem fourierChar_neg_intCast (n : ℤ) : (𝐞 (-(n : ℝ)) : ℂ) = 1 := by
  have := fourierChar_intCast (-n); push_cast at this; exact this

theorem P2_periodic (c : 𝓞 K) (μ ν : 𝓞 K) : P2 c (μ + 2 * ν) = P2 c μ := by
  obtain ⟨n, hn⟩ := exists_re_two_σO_div_δ3 (c * (μ * ν + ν * ν))
  have h : Rq c (μ + 2 * ν) / 2 = Rq c μ / 2 + n := by
    rw [Rq, Rq, ← hn]
    have : c * (μ + 2 * ν) * (μ + 2 * ν) = c * μ * μ + 4 * (c * (μ * ν + ν * ν)) := by ring
    rw [this, map_add, add_div, Complex.add_re, map_mul σO (4 : 𝓞 K) (c * (μ * ν + ν * ν)),
      map_ofNat]
    rw [show (4 : ℂ) * σO (c * (μ * ν + ν * ν)) / σO δ3 =
      2 * (2 * σO (c * (μ * ν + ν * ν)) / σO δ3) by ring]
    have h2 : (2 * (2 * σO (c * (μ * ν + ν * ν)) / σO δ3)).re =
        2 * (2 * σO (c * (μ * ν + ν * ν)) / σO δ3).re := by simp [Complex.mul_re]
    rw [h2]
    ring
  rw [P2, P2, h, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, fourierChar_neg_intCast,
    mul_one]

theorem norm_Rq_le (c μ : 𝓞 K) :
    |Rq c μ| ≤ ‖σO c‖ * (absNorm (span {μ}) : ℝ) / Real.sqrt 3 := by
  rw [Rq]
  refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
  rw [norm_div, map_mul, map_mul, norm_mul, norm_mul, ← sq_norm_σO μ]
  have h3 : ‖σO δ3‖ = Real.sqrt 3 := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_σO_δ3_sq]
  rw [h3]; ring

/-- **The dual terms**: with `D = η² + 4|w_c|²` and `ε = 4η/(3D)`,
`𝓕F_η(conj(2σ(μ)/σ(δ))) = D^{-1/2}·e^{-πεN(μ)}·P₂(μ)·e(R(μ)η²/(2D))`. -/
theorem dual_term (c : 𝓞 K) (hc : c ≠ 0) (η : ℝ) (hη : 0 < η) (μ : 𝓞 K) :
    𝓕 (chirp (fun z => (wq c * z ^ 2).re) η hη : ℂ → ℂ) (conj (2 * σO μ / σO δ3)) =
      ((Real.sqrt (η ^ 2 + 4 * ‖wq c‖ ^ 2) : ℝ) : ℂ)⁻¹ *
        ((Real.exp (-(π * (4 * η / (3 * (η ^ 2 + 4 * ‖wq c‖ ^ 2)))) *
            (absNorm (span {μ}) : ℝ)) : ℂ) *
          (P2 c μ * 𝐞 (Rq c μ * η ^ 2 / (2 * (η ^ 2 + 4 * ‖wq c‖ ^ 2))))) := by
  have hR := re_wq_dual c μ hc
  rw [← Rq] at hR
  set A : ℝ := ‖wq c‖ with hA
  set D : ℝ := η ^ 2 + 4 * A ^ 2 with hDdef
  have hD : 0 < D := by positivity
  rw [fourier_chirp, norm_dualμ_sq, hR]
  congr 1
  have he : (𝐞 (-(2 * A ^ 2 * Rq c μ) / D) : ℂ) =
      P2 c μ * 𝐞 (Rq c μ * η ^ 2 / (2 * D)) := by
    rw [P2, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hDdef]; field_simp; ring_nf
  rw [← he, Real.fourierChar_apply, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have hD' : ((η ^ 2 + 4 * ‖wq c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [← hA, ← hDdef]; exact_mod_cast hD.ne'
  simp only [hDdef, hA] at hD' ⊢
  push_cast at hD' ⊢
  field_simp
  ring

theorem norm_fourierChar_sub_one_le (t : ℝ) : ‖(𝐞 t : ℂ) - 1‖ ≤ 2 * π * |t| := by
  rw [Real.fourierChar_apply, mul_comm _ I]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]

/-- **Lattice Gaussian sums**: `Σ_μ e^{-πaN(μ)} ≤ C/a` for `0 < a ≤ 1`. -/
theorem exists_tsum_exp_le : ∃ C, ∀ a : ℝ, 0 < a → a ≤ 1 →
    ∑' μ : 𝓞 K, Real.exp (-(π * a) * (absNorm (span {μ}) : ℝ)) ≤ C / a := by
  obtain ⟨B, hB⟩ := exists_norm_gaussTr_le 1 one_ne_zero (fun _ => 1)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hsum := summable_exp_absNorm (show (0 : ℝ) < 4 / 3 by norm_num)
  set S := ∑' ν : 𝓞 K, Real.exp (-(π * (4 / 3)) * (absNorm (span {ν}) : ℝ))
  refine ⟨2 / Real.sqrt 3 * B * S, fun a ha ha1 => ?_⟩
  have h := gauss_poisson 1 one_ne_zero (fun _ => 1) (fun _ _ => rfl) a ha
  have hL : (∑' x : 𝓞 K, (fun _ => (1 : ℂ)) x * gaussC a ha (σO x)) =
      ((∑' μ : 𝓞 K, Real.exp (-(π * a) * (absNorm (span {μ}) : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun x => ?_
    rw [one_mul, gaussC_apply, sq_norm_σO]
  rw [hL, absNorm_one_span, mul_one] at h
  have hpos : 0 ≤ ∑' μ : 𝓞 K, Real.exp (-(π * a) * (absNorm (span {μ}) : ℝ)) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  have hterm : ∀ ν : 𝓞 K, ‖gaussTr 1 (fun _ => 1) ν *
      cexp (-(π : ℂ) * ((4 * (absNorm (span {ν}) : ℝ) / (3 * 1) : ℝ) : ℂ) / a)‖ ≤
        B * Real.exp (-(π * (4 / 3)) * (absNorm (span {ν}) : ℝ)) := by
    intro ν
    rw [norm_mul]
    refine mul_le_mul (hB ν) ?_ (norm_nonneg _) hB0
    rw [show -(π : ℂ) * ((4 * (absNorm (span {ν}) : ℝ) / (3 * 1) : ℝ) : ℂ) / a =
      ((-(π * (4 * (absNorm (span {ν}) : ℝ) / 3) / a) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal]
    apply Real.exp_le_exp.2
    have hN : (0 : ℝ) ≤ absNorm (span {ν}) := Nat.cast_nonneg _
    have hX : 0 ≤ π * (4 * (absNorm (span {ν}) : ℝ) / 3) := by positivity
    have h1 := le_div_self hX ha ha1
    have h2 : -(π * (4 / 3)) * (absNorm (span {ν}) : ℝ) =
        -(π * (4 * (absNorm (span {ν}) : ℝ) / 3)) := by ring
    rw [h2]; linarith
  have hsum' : Summable fun ν : 𝓞 K => ‖gaussTr 1 (fun _ => 1) ν *
      cexp (-(π : ℂ) * ((4 * (absNorm (span {ν}) : ℝ) / (3 * 1) : ℝ) : ℂ) / a)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hsum.mul_left B)
  calc ∑' μ : 𝓞 K, Real.exp (-(π * a) * (absNorm (span {μ}) : ℝ))
      = ‖((∑' μ : 𝓞 K, Real.exp (-(π * a) * (absNorm (span {μ}) : ℝ)) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
    _ ≤ 2 / (Real.sqrt 3 * a) * ∑' ν : 𝓞 K, B * Real.exp (-(π * (4 / 3)) *
          (absNorm (span {ν}) : ℝ)) := by
        rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < 2 / (Real.sqrt 3 * a))]
        gcongr
        exact (norm_tsum_le_tsum_norm hsum').trans (hsum'.tsum_le_tsum hterm (hsum.mul_left B))
    _ = 2 / Real.sqrt 3 * B * S / a := by
        rw [tsum_mul_left]; ring

/-- `t·e^{-bt} ≤ (2/b)·e^{-bt/2}` for `b > 0`. -/
theorem mul_exp_neg_le {b : ℝ} (t : ℝ) (hb : 0 < b) :
    t * Real.exp (-b * t) ≤ (2 / b) * Real.exp (-(b / 2) * t) := by
  have h1 : b / 2 * t ≤ Real.exp (b / 2 * t) := by linarith [Real.add_one_le_exp (b / 2 * t)]
  have h2 : t = (2 / b) * (b / 2 * t) := by field_simp
  calc t * Real.exp (-b * t) = (2 / b) * (b / 2 * t) * Real.exp (-b * t) := by rw [← h2]
    _ ≤ (2 / b) * Real.exp (b / 2 * t) * Real.exp (-b * t) := by gcongr
    _ = (2 / b) * Real.exp (-(b / 2) * t) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- **The second moment**: `Σ_μ N(μ)e^{-πεN(μ)} ≤ C/ε²` for `0 < ε ≤ 1`. -/
theorem exists_tsum_mul_exp_le : ∃ C, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    Summable (fun μ : 𝓞 K => (absNorm (span {μ}) : ℝ) *
      Real.exp (-(π * ε) * (absNorm (span {μ}) : ℝ))) ∧
    ∑' μ : 𝓞 K, (absNorm (span {μ}) : ℝ) * Real.exp (-(π * ε) * (absNorm (span {μ}) : ℝ)) ≤
      C / ε ^ 2 := by
  obtain ⟨C₁, hC₁⟩ := exists_tsum_exp_le
  refine ⟨4 * C₁ / π, fun ε hε hε1 => ?_⟩
  have hb : 0 < π * ε := by positivity
  have hle : ∀ μ : 𝓞 K, (absNorm (span {μ}) : ℝ) * Real.exp (-(π * ε) * (absNorm (span {μ}) : ℝ)) ≤
      (2 / (π * ε)) * Real.exp (-(π * (ε / 2)) * (absNorm (span {μ}) : ℝ)) := fun μ => by
    have := mul_exp_neg_le (absNorm (span {μ}) : ℝ) hb
    rw [show -(π * ε / 2) = -(π * (ε / 2)) by ring] at this
    exact this
  have hs2 := summable_exp_absNorm (show (0 : ℝ) < ε / 2 by positivity)
  have hsum : Summable fun μ : 𝓞 K => (absNorm (span {μ}) : ℝ) *
      Real.exp (-(π * ε) * (absNorm (span {μ}) : ℝ)) :=
    Summable.of_nonneg_of_le (fun μ => by positivity) hle (hs2.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' μ : 𝓞 K, (absNorm (span {μ}) : ℝ) * Real.exp (-(π * ε) * (absNorm (span {μ}) : ℝ))
      ≤ ∑' μ : 𝓞 K, (2 / (π * ε)) * Real.exp (-(π * (ε / 2)) * (absNorm (span {μ}) : ℝ)) :=
        hsum.tsum_le_tsum hle (hs2.mul_left _)
    _ = (2 / (π * ε)) * ∑' μ : 𝓞 K, Real.exp (-(π * (ε / 2)) * (absNorm (span {μ}) : ℝ)) :=
        tsum_mul_left
    _ ≤ (2 / (π * ε)) * (C₁ / (ε / 2)) := by
        gcongr
        exact hC₁ (ε / 2) (by positivity) (by linarith)
    _ = 4 * C₁ / π / ε ^ 2 := by field_simp; ring

/-- `D(η) = η² + 4|w_c|²`. -/
def Dq (c : 𝓞 K) (η : ℝ) : ℝ := η ^ 2 + 4 * ‖wq c‖ ^ 2

/-- `ε(η) = 4η/(3D(η))`. -/
def εq (c : 𝓞 K) (η : ℝ) : ℝ := 4 * η / (3 * Dq c η)

theorem Dq_pos (c : 𝓞 K) {η : ℝ} (hη : 0 < η) : 0 < Dq c η := by unfold Dq; positivity

theorem εq_pos (c : 𝓞 K) {η : ℝ} (hη : 0 < η) : 0 < εq c η := by
  unfold εq; have := Dq_pos c hη; positivity

theorem norm_P2 (c μ : 𝓞 K) : ‖P2 c μ‖ = 1 := by simp [P2]

theorem summable_P2_exp (c : 𝓞 K) {ε : ℝ} (hε : 0 < ε) :
    Summable fun μ : 𝓞 K => P2 c μ * (Real.exp (-(π * ε) * (absNorm (span {μ}) : ℝ)) : ℂ) := by
  refine Summable.of_norm ((summable_exp_absNorm hε).congr fun μ => ?_)
  rw [norm_mul, norm_P2, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem norm_fourierChar_sub_one_le_two (t : ℝ) : ‖(𝐞 t : ℂ) - 1‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  simp; norm_num

/-- **The decomposition**: for `η > 0`, `η·T(η)` is the main term plus the error term. -/
theorem eta_sum_decomp (c : 𝓞 K) (hc : c ≠ 0) (η : ℝ) (hη : 0 < η) :
    (η : ℂ) * ∑' x : 𝓞 K, qphase c x * (Real.exp (-(π * η) * ‖σO x‖ ^ 2) : ℂ) =
      ((2 / Real.sqrt 3 * (3 / 4) * Real.sqrt (Dq c η) : ℝ) : ℂ) *
        ((εq c η : ℂ) * ∑' x : 𝓞 K, P2 c x * (Real.exp (-(π * εq c η) * ‖σO x‖ ^ 2) : ℂ)) +
      ((2 / Real.sqrt 3 * η / Real.sqrt (Dq c η) : ℝ) : ℂ) *
        ∑' μ : 𝓞 K, (Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ) *
          (P2 c μ * ((𝐞 (Rq c μ * η ^ 2 / (2 * Dq c η)) : ℂ) - 1)) := by
  have hD := Dq_pos c hη
  have hε := εq_pos c hη
  rw [chirp_sum_dual c η hη]
  simp_rw [dual_term c hc η hη]
  have hDq : η ^ 2 + 4 * ‖wq c‖ ^ 2 = Dq c η := rfl
  have hεq : 4 * η / (3 * Dq c η) = εq c η := rfl
  simp only [hDq, hεq]
  have s1 := summable_P2_exp c hε
  have s2 : Summable fun μ : 𝓞 K =>
      (Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ) *
        (P2 c μ * ((𝐞 (Rq c μ * η ^ 2 / (2 * Dq c η)) : ℂ) - 1)) := by
    refine Summable.of_norm_bounded ((summable_exp_absNorm hε).mul_left 2) fun μ => ?_
    rw [norm_mul, norm_mul, norm_P2, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have h2 := norm_fourierChar_sub_one_le_two (Rq c μ * η ^ 2 / (2 * Dq c η))
    nlinarith [Real.exp_pos (-(π * εq c η) * (absNorm (span {μ}) : ℝ))]
  have hsplit : ∀ μ : 𝓞 K, ((Real.sqrt (Dq c η) : ℝ) : ℂ)⁻¹ *
      ((Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ) *
        (P2 c μ * 𝐞 (Rq c μ * η ^ 2 / (2 * Dq c η)))) =
      ((Real.sqrt (Dq c η) : ℝ) : ℂ)⁻¹ *
          (P2 c μ * (Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ)) +
        ((Real.sqrt (Dq c η) : ℝ) : ℂ)⁻¹ *
          ((Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ) *
            (P2 c μ * ((𝐞 (Rq c μ * η ^ 2 / (2 * Dq c η)) : ℂ) - 1))) := fun μ => by ring
  rw [tsum_congr hsplit, Summable.tsum_add (s1.mul_left _) (s2.mul_left _), tsum_mul_left,
    tsum_mul_left]
  have hS1 : (∑' μ : 𝓞 K, P2 c μ * (Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ)) =
      ∑' x : 𝓞 K, P2 c x * (Real.exp (-(π * εq c η) * ‖σO x‖ ^ 2) : ℂ) :=
    tsum_congr fun x => by rw [sq_norm_σO]
  rw [hS1]
  set S₁ := ∑' x : 𝓞 K, P2 c x * (Real.exp (-(π * εq c η) * ‖σO x‖ ^ 2) : ℂ) with hS₁
  set S₂ := ∑' μ : 𝓞 K, (Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ) *
    (P2 c μ * ((𝐞 (Rq c μ * η ^ 2 / (2 * Dq c η)) : ℂ) - 1)) with hS₂
  set r : ℝ := Real.sqrt (Dq c η) with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hD
  have hr2 : r ^ 2 = Dq c η := Real.sq_sqrt hD.le
  have hεr : εq c η = 4 * η / (3 * r ^ 2) := by rw [hr2]; rfl
  rw [hεr]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 3 := by positivity
    exact_mod_cast this.ne'
  push_cast
  field_simp

theorem wq_ne_zero (c : 𝓞 K) (hc : c ≠ 0) : wq c ≠ 0 := by
  have hγ : σO c ≠ 0 := fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  unfold wq
  exact div_ne_zero two_ne_zero (mul_ne_zero σO_δ3_ne_zero hγ)

theorem norm_wq (c : 𝓞 K) : ‖wq c‖ = 2 / (Real.sqrt 3 * ‖σO c‖) := by
  have h3 : ‖σO δ3‖ = Real.sqrt 3 := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_σO_δ3_sq]
  rw [wq, norm_div, norm_mul, h3]; simp

theorem absNorm_two : (absNorm (span {(2 : 𝓞 K)}) : ℝ) = 4 := by
  have := absNorm_natCast_span_sq 2
  push_cast at this
  rw [this]; norm_num

/-- `√D(η) → 2|w_c|` as `η → 0⁺`. -/
theorem tendsto_sqrt_Dq (c : 𝓞 K) :
    Tendsto (fun η : ℝ => Real.sqrt (Dq c η)) (𝓝[>] 0) (𝓝 (2 * ‖wq c‖)) := by
  have hcontD : Continuous fun η : ℝ => Dq c η := by unfold Dq; fun_prop
  have hD0 : Dq c 0 = (2 * ‖wq c‖) ^ 2 := by unfold Dq; ring
  have h := (Real.continuous_sqrt.comp hcontD).tendsto 0
  simp only [Function.comp_apply, hD0, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * ‖wq c‖)] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **The main term**: it tends to `(|w_c|/2)·Σ_{y mod 2} P₂(y)`. -/
theorem tendsto_main (c : 𝓞 K) (hc : c ≠ 0) :
    Tendsto (fun η : ℝ => ((2 / Real.sqrt 3 * (3 / 4) * Real.sqrt (Dq c η) : ℝ) : ℂ) *
        ((εq c η : ℂ) * ∑' x : 𝓞 K, P2 c x * (Real.exp (-(π * εq c η) * ‖σO x‖ ^ 2) : ℂ)))
      (𝓝[>] 0) (𝓝 (((‖wq c‖ / 2 : ℝ) : ℂ) * gaussTr 2 (P2 c) 0)) := by
  have hA : 0 < ‖wq c‖ := norm_pos_iff.2 (wq_ne_zero c hc)
  have hcontD : Continuous fun η : ℝ => Dq c η := by unfold Dq; fun_prop
  have hD0 : Dq c 0 = (2 * ‖wq c‖) ^ 2 := by unfold Dq; ring
  have hsqrt := tendsto_sqrt_Dq c
  have hε : Tendsto (εq c) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (eventually_nhdsWithin_of_forall fun η hη => εq_pos c hη)
    have hc0 : Dq c 0 ≠ 0 := by rw [hD0]; positivity
    have h : ContinuousAt (εq c) 0 := by
      unfold εq
      exact (continuousAt_const.mul continuousAt_id).div
        (continuousAt_const.mul hcontD.continuousAt) (by simpa using hc0)
    have h' := h.tendsto
    have he0 : εq c 0 = 0 := by simp [εq]
    rw [he0] at h'
    exact h'.mono_left nhdsWithin_le_nhds
  have hG := (tendsto_gauss_poisson 2 two_ne_zero (P2 c) (P2_periodic c)).comp hε
  have hS := (Complex.continuous_ofReal.tendsto _).comp
    (hsqrt.const_mul (2 / Real.sqrt 3 * (3 / 4)))
  have hmul := hS.mul hG
  have hval : ((2 / Real.sqrt 3 * (3 / 4) * (2 * ‖wq c‖) : ℝ) : ℂ) *
      (((2 / (Real.sqrt 3 * (absNorm (span {(2 : 𝓞 K)}) : ℝ)) : ℝ) : ℂ) * gaussTr 2 (P2 c) 0) =
      ((‖wq c‖ / 2 : ℝ) : ℂ) * gaussTr 2 (P2 c) 0 := by
    rw [absNorm_two]
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h3' : (Real.sqrt 3 : ℂ) ≠ 0 := by
      have : (0 : ℝ) < Real.sqrt 3 := by positivity
      exact_mod_cast this.ne'
    have h3c : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by exact_mod_cast h3
    push_cast
    field_simp
    rw [h3c]
    ring
  rw [hval] at hmul
  exact hmul

/-- **The error term tends to `0`**: `‖err(η)‖ ≤ K·η·√D(η)` for small `η`. -/
theorem tendsto_err (c : 𝓞 K) (hc : c ≠ 0) :
    Tendsto (fun η : ℝ => ((2 / Real.sqrt 3 * η / Real.sqrt (Dq c η) : ℝ) : ℂ) *
        ∑' μ : 𝓞 K, (Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ) *
          (P2 c μ * ((𝐞 (Rq c μ * η ^ 2 / (2 * Dq c η)) : ℂ) - 1)))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C₂, hC₂⟩ := exists_tsum_mul_exp_le
  set A := ‖wq c‖ with hAdef
  have hA : 0 < A := norm_pos_iff.2 (wq_ne_zero c hc)
  set γ := ‖σO c‖ with hγdef
  have hγ : 0 ≤ γ := norm_nonneg _
  have h3 : 0 < Real.sqrt 3 := by positivity
  set K₀ := 2 / Real.sqrt 3 * (π * γ / Real.sqrt 3) * C₂ * (9 / 16) with hK₀
  have hbound : ∀ η : ℝ, 0 < η → η ≤ 3 * A ^ 2 →
      ‖((2 / Real.sqrt 3 * η / Real.sqrt (Dq c η) : ℝ) : ℂ) *
        ∑' μ : 𝓞 K, (Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ) *
          (P2 c μ * ((𝐞 (Rq c μ * η ^ 2 / (2 * Dq c η)) : ℂ) - 1))‖ ≤
        K₀ * (η * Real.sqrt (Dq c η)) := by
    intro η hη hη3
    have hD := Dq_pos c hη
    have hε := εq_pos c hη
    have hDA : 4 * A ^ 2 ≤ Dq c η := by unfold Dq; nlinarith
    have hε1 : εq c η ≤ 1 := by
      unfold εq; rw [div_le_one (by positivity)]; nlinarith
    obtain ⟨hs, hle⟩ := hC₂ (εq c η) hε hε1
    set B : ℝ := π * γ * η ^ 2 / (Real.sqrt 3 * Dq c η) with hBdef
    have hB : 0 ≤ B := by positivity
    have hterm : ∀ μ : 𝓞 K,
        ‖(Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ) *
          (P2 c μ * ((𝐞 (Rq c μ * η ^ 2 / (2 * Dq c η)) : ℂ) - 1))‖ ≤
        B * ((absNorm (span {μ}) : ℝ) * Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ))) := by
      intro μ
      rw [norm_mul, norm_mul, norm_P2, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have h1 := norm_fourierChar_sub_one_le (Rq c μ * η ^ 2 / (2 * Dq c η))
      have h2 := norm_Rq_le c μ
      have h4 : |Rq c μ * η ^ 2 / (2 * Dq c η)| ≤
          γ * (absNorm (span {μ}) : ℝ) / Real.sqrt 3 * η ^ 2 / (2 * Dq c η) := by
        rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Dq c η),
          abs_of_nonneg (sq_nonneg η)]
        gcongr
      have hE := Real.exp_pos (-(π * εq c η) * (absNorm (span {μ}) : ℝ))
      calc Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) *
            ‖(𝐞 (Rq c μ * η ^ 2 / (2 * Dq c η)) : ℂ) - 1‖
          ≤ Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) *
            (2 * π * (γ * (absNorm (span {μ}) : ℝ) / Real.sqrt 3 * η ^ 2 / (2 * Dq c η))) := by
            gcongr
            exact h1.trans (by gcongr)
        _ = B * ((absNorm (span {μ}) : ℝ) *
              Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ))) := by
            rw [hBdef]; field_simp
    have hsum' : Summable fun μ : 𝓞 K =>
        ‖(Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ) *
          (P2 c μ * ((𝐞 (Rq c μ * η ^ 2 / (2 * Dq c η)) : ℂ) - 1))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hs.mul_left B)
    have hcoef : 0 < 2 / Real.sqrt 3 * η / Real.sqrt (Dq c η) := by
      have := Real.sqrt_pos.2 hD; positivity
    set r := Real.sqrt (Dq c η) with hrdef
    have hr : 0 < r := Real.sqrt_pos.2 hD
    have hr2 : r ^ 2 = Dq c η := Real.sq_sqrt hD.le
    calc _ = (2 / Real.sqrt 3 * η / r) *
          ‖∑' μ : 𝓞 K, (Real.exp (-(π * εq c η) * (absNorm (span {μ}) : ℝ)) : ℂ) *
            (P2 c μ * ((𝐞 (Rq c μ * η ^ 2 / (2 * Dq c η)) : ℂ) - 1))‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcoef]
      _ ≤ (2 / Real.sqrt 3 * η / r) * (B * (C₂ / εq c η ^ 2)) := by
          gcongr
          refine (norm_tsum_le_tsum_norm hsum').trans ?_
          refine (hsum'.tsum_le_tsum hterm (hs.mul_left B)).trans ?_
          rw [tsum_mul_left]
          gcongr
      _ = K₀ * (η * r) := by
          rw [hBdef, hK₀]
          unfold εq
          rw [← hr2]
          field_simp
          ring
  refine squeeze_zero_norm' (a := fun η => K₀ * (η * Real.sqrt (Dq c η))) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 3 * A ^ 2 by positivity)] with η hη
    exact hbound η hη.1 hη.2.le
  · have h1 : Tendsto (fun η : ℝ => η * Real.sqrt (Dq c η)) (𝓝[>] 0) (𝓝 (0 * (2 * A))) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul (tendsto_sqrt_Dq c)
    simpa using h1.const_mul K₀

/-- **The quadratic Gauss sum over `ℤ[ω]`**: for `c ≠ 0`,
`Σ_{x mod c} ψ_c(x²) = (|σc|/2)·Σ_{y mod 2} P₂(y)`, where `P₂(y) = e(-Re(σ(cy²)/σ(δ))/2)`. -/
theorem quad_gauss (c : 𝓞 K) (hc : c ≠ 0) :
    gaussTr c (qphase c) 0 = ((‖σO c‖ / 2 : ℝ) : ℂ) * gaussTr 2 (P2 c) 0 := by
  have h1 := tendsto_gauss_poisson c hc (qphase c) (qphase_periodic c hc)
  have h2 : Tendsto (fun η : ℝ =>
      (η : ℂ) * ∑' x : 𝓞 K, qphase c x * (Real.exp (-(π * η) * ‖σO x‖ ^ 2) : ℂ))
      (𝓝[>] 0) (𝓝 (((‖wq c‖ / 2 : ℝ) : ℂ) * gaussTr 2 (P2 c) 0)) := by
    have h := (tendsto_main c hc).add (tendsto_err c hc)
    rw [add_zero] at h
    exact h.congr' (eventually_nhdsWithin_of_forall fun η hη => (eta_sum_decomp c hc η hη).symm)
  have h := tendsto_nhds_unique h1 h2
  have hγ : σO c ≠ 0 := fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  have hγr : 0 < ‖σO c‖ := norm_pos_iff.2 hγ
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  rw [norm_wq, ← sq_norm_σO c] at h
  have key : gaussTr c (qphase c) 0 = ((Real.sqrt 3 * ‖σO c‖ ^ 2 / 2 : ℝ) : ℂ) *
      ((((2 / (Real.sqrt 3 * ‖σO c‖ ^ 2)) : ℝ) : ℂ) * gaussTr c (qphase c) 0) := by
    rw [← mul_assoc, ← Complex.ofReal_mul]
    rw [show Real.sqrt 3 * ‖σO c‖ ^ 2 / 2 * (2 / (Real.sqrt 3 * ‖σO c‖ ^ 2)) = 1 by field_simp]
    simp
  rw [key, h]
  push_cast
  field_simp

/-- The residues modulo `2`: `i + jω` for `i, j ∈ {0, 1}`. -/
def rep2 (p : Fin 2 × Fin 2) : 𝓞 K := ((p.1 : ℕ) : 𝓞 K) + ((p.2 : ℕ) : 𝓞 K) * ω

theorem rep2_bijective :
    Function.Bijective (fun q : (Fin 2 × Fin 2) × 𝓞 K => rep2 q.1 + 2 * q.2) := by
  constructor
  · rintro ⟨⟨i, j⟩, u⟩ ⟨⟨i', j'⟩, u'⟩ h
    obtain ⟨u0, u1, rfl⟩ := exists_coords u
    obtain ⟨v0, v1, rfl⟩ := exists_coords u'
    simp only [rep2] at h
    have h' : crd ![(i : ℤ) + 2 * u0, (j : ℤ) + 2 * u1] =
        crd ![(i' : ℤ) + 2 * v0, (j' : ℤ) + 2 * v1] := by
      simp only [crd, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      linear_combination h
    have e := crd_injective h'
    have e0 := congrFun e 0
    have e1 := congrFun e 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    have hi := i.isLt
    have hi' := i'.isLt
    have hj := j.isLt
    have hj' := j'.isLt
    have h0 : (i : ℕ) = i' := by omega
    have h1 : (j : ℕ) = j' := by omega
    have hu0 : u0 = v0 := by omega
    have hu1 : u1 = v1 := by omega
    rw [Fin.ext h0, Fin.ext h1, hu0, hu1]
  · intro x
    obtain ⟨m, n, rfl⟩ := exists_coords x
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' m <;> obtain ⟨l, hl | hl⟩ := Int.even_or_odd' n <;>
      subst hk hl
    · exact ⟨((0, 0), (k : 𝓞 K) + (l : 𝓞 K) * ω), by
        simp only [rep2, Fin.val_zero, Nat.cast_zero]; push_cast; ring⟩
    · exact ⟨((0, 1), (k : 𝓞 K) + (l : 𝓞 K) * ω), by
        simp only [rep2, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]; push_cast; ring⟩
    · exact ⟨((1, 0), (k : 𝓞 K) + (l : 𝓞 K) * ω), by
        simp only [rep2, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]; push_cast; ring⟩
    · exact ⟨((1, 1), (k : 𝓞 K) + (l : 𝓞 K) * ω), by
        simp only [rep2, Fin.val_one, Nat.cast_one]; push_cast; ring⟩

/-- The Gauss transform modulo `2` at frequency `0` is the sum over `0, 1, ω, 1 + ω`. -/
theorem gaussTr_two (g : 𝓞 K → ℂ) (hg : ∀ z u, g (z + 2 * u) = g z) :
    gaussTr 2 g 0 = g 0 + g 1 + g ω + g (1 + ω) := by
  rw [gaussTr_eq_sum 2 two_ne_zero g hg rep2 rep2_bijective 0]
  simp only [mul_zero, ψc_zero, mul_one, Fintype.sum_prod_type, Fin.sum_univ_two, rep2]
  simp
  ring

/-- `R(μ)` is half the `ω`-coordinate of `cμ²`. -/
theorem Rq_coord (c μ : 𝓞 K) (m n : ℤ) (h : c * μ * μ = (m : 𝓞 K) + (n : 𝓞 K) * ω) :
    Rq c μ = n / 2 := by
  have h1 := re_two_σO_div_δ3 m n
  rw [← h] at h1
  have h2 : (2 * σO (c * μ * μ) / σO δ3).re = 2 * (σO (c * μ * μ) / σO δ3).re := by
    rw [mul_div_assoc]; simp [Complex.mul_re]
  rw [Rq]
  linarith

/-- `P₂(μ) = i^{-n}` for `n` the `ω`-coordinate of `cμ²`. -/
theorem P2_coord (c μ : 𝓞 K) (m n : ℤ) (h : c * μ * μ = (m : 𝓞 K) + (n : 𝓞 K) * ω) :
    P2 c μ = I ^ (-n) := by
  rw [P2, Rq_coord c μ m n h, Real.fourierChar_apply]
  have : (((2 * π * -((n : ℝ) / 2 / 2) : ℝ) : ℂ) * I) = ((-n : ℤ) : ℂ) * ((π : ℂ) / 2 * I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]

/-- **The quadratic Gauss sum in coordinates**: for `c = a + bω ≠ 0`,
`Σ_{x mod c} ψ_c(x²) = (|σc|/2)·(1 + i^{-b} + i^a + i^{b-a})`. -/
theorem quad_gauss_coords (a b : ℤ) (hc : (a : 𝓞 K) + (b : 𝓞 K) * ω ≠ 0) :
    gaussTr ((a : 𝓞 K) + (b : 𝓞 K) * ω) (qphase ((a : 𝓞 K) + (b : 𝓞 K) * ω)) 0 =
      ((‖σO ((a : 𝓞 K) + (b : 𝓞 K) * ω)‖ / 2 : ℝ) : ℂ) *
        (1 + I ^ (-b) + I ^ a + I ^ (b - a)) := by
  rw [quad_gauss _ hc, gaussTr_two _ (P2_periodic _)]
  congr 1
  rw [P2_coord _ 0 0 0 (by simp), P2_coord _ 1 a b (by ring),
    P2_coord _ ω (b - a) (-a)
      (by push_cast; linear_combination (a : 𝓞 K) * ω_sq_add + (b : 𝓞 K) * ω_cube),
    P2_coord _ (1 + ω) (-b) (a - b)
      (by push_cast; linear_combination ((a : 𝓞 K) + 2 * b) * ω_sq_add + (b : 𝓞 K) * ω_cube)]
  rw [neg_zero, zpow_zero, neg_neg, neg_sub]

end Eis

end

#print axioms Eis.fourier_gaussC
#print axioms Eis.gauss_poisson
#print axioms Eis.tendsto_gauss_poisson
#print axioms Eis.chirp_sum_dual
#print axioms Eis.re_wq_dual
#print axioms Eis.P2_periodic
#print axioms Eis.dual_term
#print axioms Eis.exists_tsum_exp_le
#print axioms Eis.exists_tsum_mul_exp_le
#print axioms Eis.eta_sum_decomp
#print axioms Eis.tendsto_main
#print axioms Eis.tendsto_err
#print axioms Eis.quad_gauss
#print axioms Eis.rep2_bijective
#print axioms Eis.gaussTr_two
#print axioms Eis.P2_coord
#print axioms Eis.quad_gauss_coords
