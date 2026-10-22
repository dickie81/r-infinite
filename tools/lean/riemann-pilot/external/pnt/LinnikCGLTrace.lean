/-
# Round 648: Chen–Gupta–Li's `S₃` at one point per character (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li split the Poisson expansion of the cubic trace by its frequencies `m⃗ = (m₁, m₂, m₃)`. In their (5.2),
"S₁ consists of terms with exactly one nonzero m_i, S₂ consists of terms with exactly two nonzero m_i and S₃ consists
of terms with all three m_i being nonzero", and their §7 opens "Let us first recall that
S₃ = Σ_{m₁,m₂,m₃≠0} I_{m⃗}, where I_{m⃗} = N³/q³ Σ_{(t₁,χ₁),(t₂,χ₂),(t₃,χ₃)∈W, not all equal}
Σ_{a₁,a₂,a₃ mod q, (a₁a₂a₃,q)=1} χ₁χ̄₂(a₁)χ₂χ̄₃(a₂)χ₃χ̄₁(a₃)e_q(a⃗·m⃗)
· ĥ_{t₁−t₂}(Nm₁/q)ĥ_{t₂−t₃}(Nm₂/q)ĥ_{t₃−t₁}(Nm₃/q)"
(spaces restored, the subscripts and the displays transcribed on one line, the bars read from the PDF). Round 639
named `S3 = X − 3μ₀‖E‖_F²` after their `S₃`, on an argument in its header; this file proves the identity at one
point per character.

The term `m = 0` of round 646's expansion of `G(i, k)` is `N^{iτ}(N/q)ĥ_τ(0)Σ_{a<q}χ_i(a)conj(χ_k(a))`, with
`τ = t_i − t_k`. By orthogonality it vanishes for `χ_i ≠ χ_k`; on the diagonal it is `(N/q)ĥ₀(0)φ(q) = μ₀`, since
`ĥ₀(0) = ∫w²`. So `E′(i, k) = G(i, k) − δ_{ik}μ₀` is `N^{iτ}F(i, k)`, with `F(i, k)` the sum of the terms `m ≠ 0` (named
`E′` because round 639's `E` is the off-diagonal part of `G`). A triple that is not all equal but has two equal points
carries `μ₀G(i, k)G(k, i) = μ₀|G(i, k)|²` in one of three positions, so `X − 3μ₀‖E‖_F²`, with round 639's
`‖E‖_F² = Σ_{i≠k}|G(i, k)|²`, is the real part of `Σ E′(i, j)E′(j, k)E′(k, i)` over the triples that are not all equal;
and the phases `N^{iτ}` cancel around a triple. Written out, `F(i, j)F(j, k)F(k, i)` is a product of three sums over
`m ≠ 0` whose terms multiply to the summand of their `I_{m⃗}`: the bar falls on the second character of each pair, as
`conj(χ_k(a))` does here, and their condition `(a₁a₂a₃, q) = 1` holds wherever the characters do not vanish. The file
keeps the product of the three sums; it does not form the sum over `(m₁, m₂, m₃)`.

Plain statement (`S3_eq_Fm`). For `q ≥ 1`, `N > 0` and `χ` injective on `R`, `S₃ = Re Σ F(i, j)F(j, k)F(k, i)` over the
triples of points of `R` that are not all equal, where
`F(i, k) = Σ_{a<q}χ_i(a)conj(χ_k(a))Σ_{m≠0}(N/q)ĥ_{t_i−t_k}(Nm/q)e^{2πima/q}` and `h_τ(u) = w(u)²u^{iτ}`.

Plain statement (`S3_eq_cube`). For any `q`, `N` and points, `S₃ = Re Σ E′(i, j)E′(j, k)E′(k, i)` over the triples that
are not all equal, with `E′(i, k) = G(i, k) − δ_{ik}μ₀`.

Plain statement (`Em_eq`). For `q ≥ 1`, `N > 0`, `χ` injective on `R` and `i, k ∈ R`,
`E′(i, k) = N^{i(t_i−t_k)}F(i, k)`.

* `triple_shift`, `triple_sum_split`, `S3_eq_cube`: the algebra, with round 639's `gramP_swap`.
* `sum_range_mul_star_eq_zero`, `sum_range_mul_star_self`: `Σ_{a<q}χ(a)conj(ψ(a)) = 0` for `χ ≠ ψ` (Mathlib's
  `MulChar.sum_eq_zero_of_ne_one` over `ZMod q`), and `Σ_{a<q}|χ(a)|² = φ(q)` (Mathlib's `Nat.totient_eq_card_coprime`).
* `fourier_Wt_zero`: `ĥ₀(0) = ∫_1^2 w²`.
* `summable_poisson`: the terms of each residue class's Poisson series are summable, being `O(m^{−2})` by round 645's
  `lemma43` at `K = 2`.
* `Fm`, `Em_eq`: the term `m = 0` split off (Mathlib's `Summable.tsum_eq_add_tsum_ite`).
* `S3_eq_Fm`: the identity.

The file imports `LinnikCGLPoisson.lean`.
-/

import LinnikCGLPoisson

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff

noncomputable section

namespace LinnikCGLTrace

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLS23

/-! ### The cubic trace less its main term -/

/-- The Gram matrix less its main term: `E′(i, k) = G(i, k) − δ_{ik}μ₀` (round 639's `E` is the off-diagonal part of
`G`). -/
def Em {ι : Type*} [DecidableEq ι] (q : ℕ) (N : ℝ) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i k : ι) : ℂ :=
  gramP N χ t i k - if i = k then (mu0 q N : ℂ) else 0

/-- One triple: a triple with exactly two equal points carries `μG(i, k)G(k, i)` in one of three positions. -/
lemma triple_shift {ι : Type*} [DecidableEq ι] (G : ι → ι → ℂ) (μ : ℂ) (i j k : ι) :
    (if i = j ∧ j = k then (0 : ℂ) else G i j * G j k * G k i) =
      (if i = j ∧ j = k then 0 else (G i j - if i = j then μ else 0) * (G j k - if j = k then μ else 0) *
        (G k i - if k = i then μ else 0)) +
      μ * ((if i = j ∧ j ≠ k then G j k * G k i else 0) + (if j = k ∧ k ≠ i then G k i * G i j else 0) +
        (if k = i ∧ i ≠ j then G i j * G j k else 0)) := by
  by_cases h1 : i = j <;> by_cases h2 : j = k <;> by_cases h3 : k = i <;> simp_all <;> ring

lemma triple_sum_split {ι : Type*} (R : Finset ι) (a b c d : ι → ι → ι → ℂ) (μ : ℂ) :
    ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (a i j k + μ * (b i j k + c i j k + d i j k)) =
      ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, a i j k + μ * (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, b i j k +
        ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, c i j k + ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, d i j k) := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_add]

/-- **`S₃` as a cubic trace** (algebra alone, for every `N`): `S₃ = X − 3μ₀‖E‖_F² = Re Σ E′(i, j)E′(j, k)E′(k, i)` over
the triples that are not all equal, with round 639's `‖E‖_F² = Σ_{i≠k}|G(i, k)|²` and
`E′(i, k) = G(i, k) − δ_{ik}μ₀`. -/
theorem S3_eq_cube {ι : Type*} [DecidableEq ι] (q : ℕ) (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) :
    S3 q N R χ t = (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
      if i = j ∧ j = k then 0 else Em q N χ t i j * Em q N χ t j k * Em q N χ t k i).re := by
  unfold S3 X3
  set G := gramP N χ t with hG
  set μ : ℂ := (mu0 q N : ℂ) with hμ
  have hsq : ∀ i k, G i k * G k i = ((‖G i k‖ ^ 2 : ℝ) : ℂ) := by
    intro i k
    rw [hG, gramP_swap N χ t i k, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hF : ((frobOff N R χ t : ℝ) : ℂ) = ∑ i ∈ R, ∑ k ∈ R, if i = k then 0 else G i k * G k i := by
    unfold frobOff
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · simp
    · exact (hsq i k).symm
  -- the pattern `i = j ≠ k`: the sum over `j` collapses to `j = i`
  have p1 : ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if i = j ∧ j ≠ k then G j k * G k i else 0) =
      ∑ i ∈ R, ∑ k ∈ R, if i = k then 0 else G i k * G k i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : i = k
      · simp [hk]
      · simp [hk]
    · intro j _ hji
      exact Finset.sum_eq_zero fun k _ => ite_eq_right fun h => hji h.1.symm
    · intro h; exact absurd hi h
  -- the pattern `j = k ≠ i`: the sum over `k` collapses to `k = j`
  have p2 : ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if j = k ∧ k ≠ i then G k i * G i j else 0) =
      ∑ i ∈ R, ∑ k ∈ R, if i = k then 0 else G i k * G k i := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_eq_single j]
    · by_cases hij : i = j
      · simp [hij]
      · rw [ite_eq_left ⟨rfl, Ne.symm hij⟩, ite_eq_right hij, mul_comm]
    · intro k _ hkj
      exact ite_eq_right fun h => hkj h.1.symm
    · intro h; exact absurd hj h
  -- the pattern `k = i ≠ j`: the sum over `k` collapses to `k = i`
  have p3 : ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if k = i ∧ i ≠ j then G i j * G j k else 0) =
      ∑ i ∈ R, ∑ k ∈ R, if i = k then 0 else G i k * G k i := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single i]
    · by_cases hij : i = j
      · simp [hij]
      · rw [ite_eq_left ⟨rfl, hij⟩, ite_eq_right hij]
    · intro k _ hki
      exact ite_eq_right fun h => hki h.1
    · intro h; exact absurd hi h
  have hX : (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, if i = j ∧ j = k then (0 : ℂ) else G i j * G j k * G k i) =
      (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
        if i = j ∧ j = k then 0 else Em q N χ t i j * Em q N χ t j k * Em q N χ t k i) +
      3 * (μ * ((frobOff N R χ t : ℝ) : ℂ)) := by
    calc (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, if i = j ∧ j = k then (0 : ℂ) else G i j * G j k * G k i)
        = ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ((if i = j ∧ j = k then 0 else
            Em q N χ t i j * Em q N χ t j k * Em q N χ t k i) +
          μ * ((if i = j ∧ j ≠ k then G j k * G k i else 0) + (if j = k ∧ k ≠ i then G k i * G i j else 0) +
            (if k = i ∧ i ≠ j then G i j * G j k else 0))) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
            triple_shift G μ i j k
      _ = _ := by rw [triple_sum_split, p1, p2, p3, ← hF]; ring
  have e3 : (3 * (μ * ((frobOff N R χ t : ℝ) : ℂ))).re = 3 * mu0 q N * frobOff N R χ t := by
    rw [hμ, show (3 : ℂ) * ((mu0 q N : ℂ) * ((frobOff N R χ t : ℝ) : ℂ)) =
      ((3 * mu0 q N * frobOff N R χ t : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [hX, Complex.add_re, e3]
  ring

/-! ### The terms `m = 0` -/

/-- Orthogonality over `0 ≤ a < q`: `Σ_{a<q}χ(a)conj(ψ(a)) = 0` for `χ ≠ ψ`. -/
lemma sum_range_mul_star_eq_zero {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q} (h : χ ≠ ψ) :
    ∑ a ∈ Finset.range q, χ a * star (ψ a) = 0 := by
  have e : ∑ a ∈ Finset.range q, χ a * star (ψ a) = ∑ x : ZMod q, χ x * star (ψ x) :=
    Finset.sum_nbij' (fun a => (a : ZMod q)) ZMod.val (fun _ _ => Finset.mem_univ _)
      (fun x _ => Finset.mem_range.2 (ZMod.val_lt x)) (fun a ha => ZMod.val_cast_of_lt (Finset.mem_range.1 ha))
      (fun x _ => ZMod.natCast_zmod_val x) (fun _ _ => rfl)
  rw [e]
  have e2 : ∀ x : ZMod q, χ x * star (ψ x) = (χ * ψ⁻¹) x := fun x => by
    rw [MulChar.star_apply', MulChar.mul_apply]
  simp only [e2]
  exact MulChar.sum_eq_zero_of_ne_one fun h1 => h (mul_inv_eq_one.1 h1)

/-- `Σ_{a<q}|χ(a)|² = φ(q)`. -/
lemma sum_range_mul_star_self {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∑ a ∈ Finset.range q, χ a * star (χ a) = q.totient := by
  have e : ∀ a ∈ Finset.range q, χ a * star (χ a) = if q.Coprime a then 1 else 0 := by
    intro a _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    split_ifs with hc
    · obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a q).2 hc.symm
      have h1 : ‖χ a‖ = 1 := by rw [← hu]; exact DirichletCharacter.unit_norm_eq_one χ u
      rw [h1]; norm_num
    · rw [MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime a q).1 h).symm)]; simp
  rw [Finset.sum_congr rfl e, Finset.sum_boole, Nat.totient_eq_card_coprime]

/-- `ĥ₀(0) = ∫w²`, the integral over `[1, 2]`. -/
lemma fourier_Wt_zero : 𝓕 (Wt 0) 0 = ((∫ u in (1 : ℝ)..2, wCGL u ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hW : ∀ v : ℝ, Complex.exp (((-2 * π * v * 0 : ℝ) : ℂ) * I) • Wt 0 v = ((wsq v : ℝ) : ℂ) := by
    intro v
    unfold Wt Wc
    simp
  simp only [hW]
  rw [integral_complex_ofReal, intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rfl
  · intro u hu
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hu
    rw [wCGL_zero (hu.elim Or.inl fun h => Or.inr h.le)]
    norm_num

/-- The terms of a residue class's Poisson series are summable: for `N, q > 0`,
`‖(N/q)ĥ_τ(Nm/q)e^{2πima/q}‖ ≤ (Cq/N)m^{−2}` for `m ≠ 0`, with `C` the constant of `sq_mul_norm_hhat_le`. -/
lemma summable_poisson (τ : ℝ) {N : ℝ} (hN : 0 < N) {q : ℕ} (hq : 0 < q) (a : ℕ) :
    Summable fun m : ℤ => ((N / q : ℝ) : ℂ) * 𝓕 (Wt τ) (N * m / q) * Complex.exp (2 * π * I * m * (a / q)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hN0 : N ≠ 0 := hN.ne'
  have hq0 : (q : ℝ) ≠ 0 := hq'.ne'
  obtain ⟨C, hC⟩ : ∃ C, C = CF 2 * (1 + |τ|) ^ 2 / (4 * π ^ 2) := ⟨_, rfl⟩
  refine Summable.of_norm_bounded_eventually ((Real.summable_abs_int_rpow one_lt_two).mul_left (C * q / N)) ?_
  filter_upwards [eventually_cofinite_ne 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hexp : ‖Complex.exp (2 * π * I * m * (a / q))‖ = 1 := by
    rw [show (2 * π * I * m * (a / q) : ℂ) = ((2 * π * m * (a / q) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h := sq_mul_norm_hhat_le τ (N * m / q)
  rw [← hC] at h
  have hξ0 : N * m / q ≠ 0 := by positivity
  have hξ : 0 < (N * m / q) ^ 2 := by positivity
  have hb : ‖𝓕 (Wt τ) (N * m / q)‖ ≤ C / (N * m / q) ^ 2 := by
    rw [le_div_iff₀ hξ]; linarith
  have habs : |(m : ℝ)| ^ (-(2 : ℝ)) = ((m : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs]
  rw [habs]
  calc N / q * ‖𝓕 (Wt τ) (N * m / q)‖ ≤ N / q * (C / (N * m / q) ^ 2) := by gcongr
    _ = C * q / N * ((m : ℝ) ^ 2)⁻¹ := by field_simp

/-! ### The paper's `S₃` -/

/-- **The frequencies `m ≠ 0` of a Gram entry**: with `τ = t_i − t_k`,
`F(i, k) = Σ_{a<q}χ_i(a)conj(χ_k(a))Σ_{m≠0}(N/q)ĥ_τ(Nm/q)e^{2πima/q}`. -/
def Fm {ι : Type*} {q : ℕ} (N : ℝ) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i k : ι) : ℂ :=
  ∑ a ∈ Finset.range q, (χ i a * star (χ k a)) * ∑' m : ℤ, if m = 0 then 0 else
    ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) (N * m / q) * Complex.exp (2 * π * I * m * (a / q))

/-- **A Gram entry less its main term**: for `N > 0`, `χ` injective on `R` and `i, k ∈ R`, `E′(i, k) = N^{iτ}F(i, k)`
with `τ = t_i − t_k`. The term `m = 0` of `gram_poisson` is `N^{iτ}(N/q)ĥ_τ(0)Σ_{a<q}χ_i(a)conj(χ_k(a))`: it vanishes
for `i ≠ k` by orthogonality, and for `i = k` it is `(N/q)ĥ₀(0)φ(q) = μ₀`. -/
theorem Em_eq {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R) (t : ι → ℝ) {i k : ι} (hi : i ∈ R) (hk : k ∈ R) :
    Em q N χ t i k = (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * Fm N χ t i k := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hsplit : ∀ a : ℕ, (∑' m : ℤ, ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) (N * m / q) *
      Complex.exp (2 * π * I * m * (a / q))) = ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) 0 +
      ∑' m : ℤ, if m = 0 then 0 else ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) (N * m / q) *
        Complex.exp (2 * π * I * m * (a / q)) := by
    intro a
    rw [(summable_poisson _ hN hq a).tsum_eq_add_tsum_ite 0]
    congr 1
    simp
  have hsum : ∑ a ∈ Finset.range q, (χ i a * star (χ k a)) * ∑' m : ℤ, ((N / q : ℝ) : ℂ) *
      𝓕 (Wt (t i - t k)) (N * m / q) * Complex.exp (2 * π * I * m * (a / q)) =
      ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) 0 * ∑ a ∈ Finset.range q, χ i a * star (χ k a) +
      Fm N χ t i k := by
    unfold Fm
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsplit a]; ring
  unfold Em
  rw [gram_poisson hN χ t i k, hsum]
  by_cases hik : i = k
  · subst hik
    rw [ite_eq_left rfl, sum_range_mul_star_self]
    simp only [sub_self, Complex.ofReal_zero, zero_mul, Complex.cpow_zero, one_mul, fourier_Wt_zero]
    unfold mu0
    push_cast
    ring
  · have hχ : χ i ≠ χ k := fun h => hik (hinj hi hk h)
    rw [ite_eq_right hik, sum_range_mul_star_eq_zero hχ, mul_zero, zero_add, sub_zero]

/-- **Chen–Gupta–Li's `S₃` at one point per character**: for `q ≥ 1`, `N > 0` and `χ` injective on `R`,
`S₃ = Re Σ F(i, j)F(j, k)F(k, i)` over the triples of points of `R` that are not all equal. -/
theorem S3_eq_Fm {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R) (t : ι → ℝ) :
    S3 q N R χ t = (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
      if i = j ∧ j = k then 0 else Fm N χ t i j * Fm N χ t j k * Fm N χ t k i).re := by
  rw [S3_eq_cube]
  congr 1
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
  split_ifs
  · rfl
  · rw [Em_eq hN hinj t hi hj, Em_eq hN hinj t hj hk, Em_eq hN hinj t hk hi]
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hph : (N : ℂ) ^ (((t i - t j : ℝ) : ℂ) * I) * (N : ℂ) ^ (((t j - t k : ℝ) : ℂ) * I) *
        (N : ℂ) ^ (((t k - t i : ℝ) : ℂ) * I) = 1 := by
      rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0,
        show ((t i - t j : ℝ) : ℂ) * I + ((t j - t k : ℝ) : ℂ) * I + ((t k - t i : ℝ) : ℂ) * I = 0 by
          push_cast; ring]
      exact Complex.cpow_zero _
    linear_combination (Fm N χ t i j * Fm N χ t j k * Fm N χ t k i) * hph

end LinnikCGLTrace

#print axioms LinnikCGLTrace.S3_eq_cube
#print axioms LinnikCGLTrace.sum_range_mul_star_eq_zero
#print axioms LinnikCGLTrace.fourier_Wt_zero
#print axioms LinnikCGLTrace.summable_poisson
#print axioms LinnikCGLTrace.Em_eq
#print axioms LinnikCGLTrace.S3_eq_Fm
