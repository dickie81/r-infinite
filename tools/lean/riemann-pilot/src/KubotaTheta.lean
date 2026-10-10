import UpperHalfSpace
import BesselK
import EisensteinThetaRows

/-! # The Kubota–Patterson theorem, displayed (round 361)

S5f-1 of round 360's plan, part 3: the display `KubotaTheta`, the form of the Kubota–Patterson
theorem that Appendix A.2 of the companion paper uses, and the absolute convergence of the series in it.

* **Theta-type series** (`ebr`, `thSer`): `c·v^{2/3} + Σ_{m ∈ ℤ[ω]} d(m)·v·K_{1/3}(4π|m|v/9)·ĕ(mz/9)`,
  `ĕ(z) = exp(2πi(z + z̄))`. The index is `m = λ⁴μ = 9μ` for Dunn and Radziwiłł's Fourier index
  `μ ∈ λ^{−4}𝒪`.
* **The support and size condition** (`ThetaSupp`): the companion paper's Lemma 6.4, `d(m) ≠ 0` only at
  `m = uλ^k n b³` (round 341's `dualPt`) with `n` squarefree and `N(n), N(b)` prime to `3`, and there
  `|d(m)| ≤ K·3^{k/6}N(b)^{1/2}`.
* **Kubota's character** (`kub`): `(c/a)₃` for `γ = (a, b; c, d) ≡ I (mod 3)` with `c ≠ 0`, and `1` if
  `c = 0`, with round 290's symbol `cub`. The cusps `γ_± = (1, 0; ω^{±1}, 1)` (`gamPlus`, `gamMinus`,
  Dunn and Radziwiłł's `γ_10` and `γ_19`).
* **`KubotaTheta`**: there is a function `θ` on upper half-space whose expansions at `∞` and at `γ_±`
  are theta-type series with coefficients satisfying the support and size condition, which is
  invariant under `SL_2(ℤ)` and automorphic on `Γ_1(3)` with Kubota's character, and whose coefficient
  at `±λnb³` (`n, b` primary, `n` squarefree, `N(nb)` prime to `6`) is `C·N(b)^{1/2}χ_n(λ)²·conj γ₂(n)`
  for a fixed `C ≠ 0`. The constant terms are left free.
* **Convergence** (`summable_thSer`, through `normSq_dualPt`, `norm_le_of_thetaSupp` and the lattice
  bound `summable_O_of_le`): under the support condition the series converge absolutely for `v > 0`.
-/

open Complex Set Filter NumberField Ideal PlanePoisson
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-- `ĕ(z) = exp(2πi(z + z̄)) = exp(4πi·Re z)`. -/
def ebr (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((2 * z.re : ℝ) : ℂ))

theorem norm_ebr (z : ℂ) : ‖ebr z‖ = 1 := by
  unfold ebr
  rw [Complex.norm_exp]
  simp

/-- **The theta-type series** `c·v^{2/3} + Σ_{m ∈ ℤ[ω]} d(m)·v·K_{1/3}(4π|m|v/9)·ĕ(mz/9)`: the Fourier
index is `μ = m/λ⁴ = m/9`, so that `m` runs over `λ⁴·(λ^{−4}𝒪)`. -/
def thSer (c : ℂ) (d : 𝓞 K → ℂ) (z : ℂ) (v : ℝ) : ℂ :=
  c * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ) +
    ∑' m : 𝓞 K, d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * z / 9)

/-- **The support and size condition** of the companion paper's Lemma 6.4 in the index `m = λ⁴ℓ`:
`d(m) ≠ 0` only at `m = uλ^k n b³` with `n` squarefree and `N(n), N(b)` prime to `3`, and there
`|d(m)| ≤ K·3^{k/6}·N(b)^{1/2}`. -/
def ThetaSupp (Kc : ℝ) (d : 𝓞 K → ℂ) : Prop :=
  0 ≤ Kc ∧ ∀ m : 𝓞 K, d m ≠ 0 → ∃ q : DualIdx, dualPt q = m ∧ Squarefree q.2.2.1 ∧
    (absNorm q.2.2.1).Coprime 3 ∧ (absNorm q.2.2.2).Coprime 3 ∧
    ‖d m‖ ≤ Kc * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2)

open Classical in
/-- **Kubota's cubic character** on `Γ_1(3)`: `(c/a)₃` if `c ≠ 0`, and `1` if `c = 0`. -/
def kub (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) : ℂ :=
  if γ 1 0 = 0 then 1 else σO (cub (γ 1 0) (span {γ 0 0}))

/-- `γ ≡ I (mod 3)`. -/
def ModThree (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) : Prop :=
  ∀ i j, (3 : 𝓞 K) ∣ γ i j - (1 : Matrix (Fin 2) (Fin 2) (𝓞 K)) i j

/-- The cusp representatives `γ_+ = (1 0; ω 1)` and `γ_− = (1 0; ω² 1)` (Dunn–Radziwiłł's `γ_10` and
`γ_19`). -/
def gamPlus : Matrix (Fin 2) (Fin 2) (𝓞 K) := !![1, 0; ω, 1]
def gamMinus : Matrix (Fin 2) (Fin 2) (𝓞 K) := !![1, 0; ω ^ 2, 1]

/-- The value of `θ ∘ γ` at `z + vj`. -/
def atG (θ : ℂ → ℝ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) (v : ℝ) : ℂ :=
  θ (uhsAct g z v).1 (uhsAct g z v).2

/-- **The Kubota–Patterson theorem, displayed** (in the form Appendix A.2 of the companion paper uses
it): a function `θ` on upper half-space whose expansions at `∞` and at `γ_±` are theta-type series with
coefficients satisfying the support and size condition, which is invariant under `SL_2(ℤ)` and
automorphic on `Γ_1(3)` with Kubota's character, and whose coefficients at `±λn b³` (`n, b` primary,
`n` squarefree, prime to `6`) are a fixed nonzero multiple of `N(b)^{1/2}·χ_n(λ)²·conj γ₂(n)`
(Patterson's, as Dunn and Radziwiłł's (5.7)). The constant terms are left free. -/
def KubotaTheta : Prop :=
  ∃ (θ : ℂ → ℝ → ℂ) (Kc : ℝ) (C c₀ cP cM : ℂ) (τ tP tM : 𝓞 K → ℂ), C ≠ 0 ∧
    ThetaSupp Kc τ ∧ ThetaSupp Kc tP ∧ ThetaSupp Kc tM ∧
    (∀ z v, 0 < v → θ z v = thSer c₀ τ z v) ∧
    (∀ z v, 0 < v → atG θ (gamPlus.map σO) z v = thSer cP tP z v) ∧
    (∀ z v, 0 < v → atG θ (gamMinus.map σO) z v = thSer cM tM z v) ∧
    (∀ γ : Matrix (Fin 2) (Fin 2) ℤ, γ.det = 1 → ∀ z v, 0 < v →
      atG θ (γ.map (Int.castRingHom ℂ)) z v = θ z v) ∧
    (∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
      atG θ (γ.map σO) z v = kub γ * θ z v) ∧
    (∀ n b : 𝓞 K, Primary n → Primary b → Squarefree (span {n}) →
      (absNorm (span {n * b})).Coprime 6 →
      τ (δ3 * n * b ^ 3) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})) ∧
      τ (-(δ3 * n * b ^ 3)) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})))

/-- `|σ(a + bω)|² = a² − ab + b²`. -/
theorem normSq_σO_crd (n : Fin 2 → ℤ) :
    Complex.normSq (σO (crd n)) = (n 0 : ℝ) ^ 2 - (n 0 : ℝ) * n 1 + (n 1 : ℝ) ^ 2 := by
  have h := congrArg σO (mul_cj_coords (n 0) (n 1))
  rw [map_mul, σO_cj, Complex.mul_conj, map_intCast] at h
  have h' : (Complex.normSq (σO (crd n)) : ℂ) = (((n 0 : ℤ) ^ 2 - n 0 * n 1 + n 1 ^ 2 : ℤ) : ℂ) := by
    rw [← h]; rfl
  exact_mod_cast h'

theorem norm_cpt_le_two_norm_σO (n : Fin 2 → ℤ) : ‖cpt (nR n)‖ ≤ 2 * ‖σO (crd n)‖ := by
  have h1 : ‖cpt (nR n)‖ ^ 2 = (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; simp [cpt, nR, Complex.normSq_apply]; ring
  have h2 : ‖σO (crd n)‖ ^ 2 = (n 0 : ℝ) ^ 2 - (n 0 : ℝ) * n 1 + (n 1 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_σO_crd]
  have h3 : ‖cpt (nR n)‖ ^ 2 ≤ (2 * ‖σO (crd n)‖) ^ 2 := by
    rw [mul_pow, h1, h2]; nlinarith [sq_nonneg ((n 0 : ℝ) - n 1)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

/-- **Lattice summability**: a nonnegative function on `ℤ[ω]` bounded by `A(1 + |σm|)^{−3}` is
summable. -/
theorem summable_O_of_le {f : 𝓞 K → ℝ} (hf0 : ∀ m, 0 ≤ f m) {A : ℝ}
    (hf : ∀ m, f m ≤ A * (1 + ‖σO m‖) ^ (-3 : ℝ)) : Summable f := by
  have hA : 0 ≤ A := by
    have := (hf0 0).trans (hf 0)
    simpa using this
  rw [← crdEquiv.summable_iff]
  refine Summable.of_nonneg_of_le (fun n => hf0 _) (fun n => ?_)
    (summable_lattice_decay.mul_left (8 * A))
  show f (crd n) ≤ 8 * A * (1 + ‖cpt (fun i => (n i : ℝ))‖) ^ (-3 : ℝ)
  have hc := norm_cpt_le_two_norm_σO n
  have hpos : 0 < 1 + ‖cpt (fun i => (n i : ℝ))‖ := by positivity
  have hle : 1 + ‖cpt (fun i => (n i : ℝ))‖ ≤ 2 * (1 + ‖σO (crd n)‖) := by
    have : ‖cpt (fun i => (n i : ℝ))‖ = ‖cpt (nR n)‖ := rfl
    rw [this]; linarith
  have key : (1 + ‖σO (crd n)‖) ^ (-3 : ℝ) ≤ 8 * (1 + ‖cpt (fun i => (n i : ℝ))‖) ^ (-3 : ℝ) := by
    have e8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
    have h2pos : 0 < 2 * (1 + ‖σO (crd n)‖) := by positivity
    calc (1 + ‖σO (crd n)‖) ^ (-3 : ℝ) = (2 : ℝ) ^ (3 : ℝ) * (2 * (1 + ‖σO (crd n)‖)) ^ (-3 : ℝ) := by
          rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ 1 + ‖σO (crd n)‖),
            ← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; norm_num
      _ ≤ (2 : ℝ) ^ (3 : ℝ) * (1 + ‖cpt (fun i => (n i : ℝ))‖) ^ (-3 : ℝ) := by
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num))
            (by positivity)
      _ = 8 * (1 + ‖cpt (fun i => (n i : ℝ))‖) ^ (-3 : ℝ) := by rw [← e8]
  calc f (crd n) ≤ A * (1 + ‖σO (crd n)‖) ^ (-3 : ℝ) := hf _
    _ ≤ A * (8 * (1 + ‖cpt (fun i => (n i : ℝ))‖) ^ (-3 : ℝ)) := mul_le_mul_of_nonneg_left key hA
    _ = 8 * A * (1 + ‖cpt (fun i => (n i : ℝ))‖) ^ (-3 : ℝ) := by ring

/-- `t^{1/3}e^{−ct} ≤ (24e^c/c⁴)(1 + t)^{−3}` for `t ≥ 0`, `c > 0`. -/
theorem rpow_third_exp_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    t ^ (1 / 3 : ℝ) * Real.exp (-(c * t)) ≤
      (24 * Real.exp c / c ^ 4) * (1 + t) ^ (-3 : ℝ) := by
  have h1t : 0 < 1 + t := by linarith
  have hfac : (c * (1 + t)) ^ 4 / 24 ≤ Real.exp (c * (1 + t)) := by
    have := Real.pow_div_factorial_le_exp (c * (1 + t)) (by positivity) 4
    simpa [Nat.factorial] using this
  have hroot : t ^ (1 / 3 : ℝ) ≤ 1 + t := by
    rcases le_or_gt t 1 with h | h
    · calc t ^ (1 / 3 : ℝ) ≤ 1 := Real.rpow_le_one ht h (by norm_num)
        _ ≤ 1 + t := by linarith
    · calc t ^ (1 / 3 : ℝ) ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
        _ = t := Real.rpow_one t
        _ ≤ 1 + t := by linarith
  rw [Real.rpow_neg h1t.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have e3 : (1 + t) ^ (3 : ℝ) = (1 + t) ^ 3 := by norm_cast
  rw [e3]
  have hexp : Real.exp (-(c * t)) = Real.exp c / Real.exp (c * (1 + t)) := by
    rw [← Real.exp_sub]; congr 1; ring
  rw [hexp]
  have hE := Real.exp_pos (c * (1 + t))
  rw [div_eq_mul_inv]
  have hc4 : 0 < c ^ 4 := by positivity
  calc t ^ (1 / 3 : ℝ) * (Real.exp c * (Real.exp (c * (1 + t)))⁻¹) * (1 + t) ^ 3
      ≤ (1 + t) * (Real.exp c * (Real.exp (c * (1 + t)))⁻¹) * (1 + t) ^ 3 := by
        gcongr
    _ = Real.exp c * ((1 + t) ^ 4 / Real.exp (c * (1 + t))) := by ring
    _ ≤ Real.exp c * (24 / c ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos c).le
        rw [div_le_div_iff₀ hE hc4]
        have : (c * (1 + t)) ^ 4 = c ^ 4 * (1 + t) ^ 4 := by ring
        nlinarith [hfac, this]
    _ = 24 * Real.exp c / c ^ 4 := by ring

theorem normSq_σO_unit (u : (𝓞 K)ˣ) : Complex.normSq (σO (u : 𝓞 K)) = 1 := by
  rw [normSq_σO, Ideal.span_singleton_eq_top.2 u.isUnit, absNorm_top]; simp

theorem normSq_σO_lam : Complex.normSq (σO (Eis.ω - 1)) = 3 := by
  rw [map_sub, map_one, σO_ω, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  have h := varpi_re_im
  rw [h.1]; nlinarith [h.2]

theorem normSq_σO_pgen {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 3) :
    Complex.normSq (σO (pgen I)) = (absNorm I : ℝ) := by
  rw [normSq_σO, (pgen_spec3 hI).2]

/-- `N(uλ^k n b³) = 3^k N(n) N(b)³`. -/
theorem normSq_dualPt {q : DualIdx} (hn : (absNorm q.2.2.1).Coprime 3)
    (hb : (absNorm q.2.2.2).Coprime 3) : Complex.normSq (σO (dualPt q)) = dualNorm q := by
  unfold dualPt dualNorm
  simp only [map_mul, map_pow]
  rw [normSq_σO_unit, normSq_σO_lam, normSq_σO_pgen hn, normSq_σO_pgen hb, one_mul]

theorem one_le_absNorm_of_coprime3 {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 3) :
    (1 : ℝ) ≤ absNorm I := by
  have h0 : absNorm I ≠ 0 := by
    intro h; rw [h] at hI; norm_num at hI
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h0

/-- **The coefficient bound**: under the support condition, `|d(m)| ≤ K·|σm|^{1/3}`. -/
theorem norm_le_of_thetaSupp {Kc : ℝ} {d : 𝓞 K → ℂ} (h : ThetaSupp Kc d) (m : 𝓞 K) :
    ‖d m‖ ≤ Kc * ‖σO m‖ ^ (1 / 3 : ℝ) := by
  by_cases hm : d m = 0
  · rw [hm, norm_zero]; exact mul_nonneg h.1 (by positivity)
  obtain ⟨q, rfl, -, hn, hb, hle⟩ := h.2 m hm
  refine hle.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ h.1
  have hN := normSq_dualPt hn hb
  have hn1 := one_le_absNorm_of_coprime3 hn
  have hb0 : (0 : ℝ) ≤ absNorm q.2.2.2 := by positivity
  set a := (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2)
  set b := ‖σO (dualPt q)‖ ^ (1 / 3 : ℝ)
  have ha : 0 ≤ a := by positivity
  have hb' : 0 ≤ b := by positivity
  have ha6 : a ^ 6 = (3 : ℝ) ^ q.2.1 * (absNorm q.2.2.2 : ℝ) ^ 3 := by
    simp only [a, mul_pow]
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((q.2.1 : ℝ) / 6)), ← Real.rpow_mul (by norm_num)]
    have e1 : (q.2.1 : ℝ) / 6 * ((6 : ℕ) : ℝ) = (q.2.1 : ℕ) := by push_cast; ring
    rw [e1, Real.rpow_natCast]
    congr 1
    rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Real.sq_sqrt hb0]
  have hb6 : b ^ 6 = Complex.normSq (σO (dualPt q)) := by
    simp only [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Complex.normSq_eq_norm_sq]
    norm_num
  have h6 : a ^ 6 ≤ b ^ 6 := by
    rw [ha6, hb6, hN, dualNorm]
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ q.2.1 * (absNorm q.2.2.2 : ℝ) ^ 3 := by positivity
    nlinarith
  exact (pow_le_pow_iff_left₀ ha hb' (by norm_num)).1 h6

theorem dualPt_ne_zero {q : DualIdx} (hn : (absNorm q.2.2.1).Coprime 3)
    (hb : (absNorm q.2.2.2).Coprime 3) : dualPt q ≠ 0 := by
  intro h
  have := normSq_dualPt hn hb
  rw [h, map_zero, map_zero] at this
  have hd : 0 < dualNorm q := by
    unfold dualNorm
    have := one_le_absNorm_of_coprime3 hn
    have := one_le_absNorm_of_coprime3 hb
    positivity
  linarith

theorem one_le_norm_σO {m : 𝓞 K} (hm : m ≠ 0) : 1 ≤ ‖σO m‖ := by
  have h := normSq_σO m
  have hN : absNorm (span {m}) ≠ 0 := by
    rw [Ne, absNorm_eq_zero_iff, span_singleton_eq_bot]; exact hm
  have h1 : (1 : ℝ) ≤ absNorm (span {m}) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN
  rw [← h, Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg (σO m)]

/-- **The theta-type series converge absolutely** under the support condition, for `v > 0`. -/
theorem summable_thSer {Kc : ℝ} {d : 𝓞 K → ℂ} (h : ThetaSupp Kc d) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    Summable fun m : 𝓞 K =>
      d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * z / 9) := by
  set c := 2 * Real.pi * v / 9 with hc_def
  have hc : 0 < c := by positivity
  set B := Kc * v * (1 / 2) * bkR (1 / 3) (4 * Real.pi * v / 9 / 2) with hB
  refine Summable.of_norm (summable_O_of_le (fun m => norm_nonneg _) (A := B * (24 * Real.exp c / c ^ 4))
    fun m => ?_)
  by_cases hm : d m = 0
  · rw [hm]; simp only [zero_mul, norm_zero]
    have := bkR_nonneg (1 / 3) (4 * Real.pi * v / 9 / 2)
    have := h.1
    positivity
  obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm
  have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb
  have h1 := one_le_norm_σO hm0
  rw [norm_mul, norm_mul, norm_mul, norm_ebr, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hv.le]
  have hK := norm_besselK_le (1 / 3 : ℂ) (4 * Real.pi * ‖σO m‖ * v / 9)
  have hre : (1 / 3 : ℂ).re = 1 / 3 := by norm_num
  rw [hre] at hK
  have hx₀ : 0 < 4 * Real.pi * v / 9 := by positivity
  have hxx : 4 * Real.pi * v / 9 ≤ 4 * Real.pi * ‖σO m‖ * v / 9 := by
    have := Real.pi_pos
    rw [div_le_div_iff_of_pos_right (by norm_num)]
    nlinarith
  have hdecay := bkR_le_exp (r := 1 / 3) hx₀ hxx
  have hexp : Real.exp (-(4 * Real.pi * ‖σO m‖ * v / 9 / 2)) = Real.exp (-(c * ‖σO m‖)) := by
    congr 1; rw [hc_def]; ring
  rw [hexp] at hdecay
  have hpoly := rpow_third_exp_le hc (norm_nonneg (σO m))
  have hd := norm_le_of_thetaSupp h m
  have hbk0 := bkR_nonneg (1 / 3) (4 * Real.pi * v / 9 / 2)
  have hKc := h.1
  calc ‖d m‖ * v * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)‖
      ≤ (Kc * ‖σO m‖ ^ (1 / 3 : ℝ)) * v *
          ((1 / 2) * (Real.exp (-(c * ‖σO m‖)) * bkR (1 / 3) (4 * Real.pi * v / 9 / 2))) := by
        gcongr
        exact hK.trans (by gcongr)
    _ = B * (‖σO m‖ ^ (1 / 3 : ℝ) * Real.exp (-(c * ‖σO m‖))) := by rw [hB]; ring
    _ ≤ B * ((24 * Real.exp c / c ^ 4) * (1 + ‖σO m‖) ^ (-3 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hpoly
        rw [hB]; positivity
    _ = B * (24 * Real.exp c / c ^ 4) * (1 + ‖σO m‖) ^ (-3 : ℝ) := by ring

end Eis

end

#print axioms Eis.norm_ebr
#print axioms Eis.normSq_σO_crd
#print axioms Eis.norm_cpt_le_two_norm_σO
#print axioms Eis.summable_O_of_le
#print axioms Eis.rpow_third_exp_le
#print axioms Eis.normSq_σO_unit
#print axioms Eis.normSq_σO_lam
#print axioms Eis.normSq_σO_pgen
#print axioms Eis.normSq_dualPt
#print axioms Eis.one_le_absNorm_of_coprime3
#print axioms Eis.norm_le_of_thetaSupp
#print axioms Eis.dualPt_ne_zero
#print axioms Eis.one_le_norm_σO
#print axioms Eis.summable_thSer
