import KubotaCoefPrime

/-! # θ's coefficients at the squarefree-times-cube indices prime to `6` (round 455)

S5f-13 of round 360's plan, part 6. Round 454 proved `ρ(hp²) = 0` and `ρ(hp) = (3/p)₃²·γ_2(h)·ρ(h)/|p|` for a
primary prime `p ∤ h`; its next step planned θ's coefficients at the squarefree indices prime to `6`, up to
`ρ(1)`, in the form of round 361's `KubotaTheta`: `C·N(b)^{1/2}·(δ₃/n)₆²·conj γ₂(n)` at `δ₃nb³`, with round
305's normalized Gauss sum `γ₂(n)` (`gamI 2`) and round 281's sextic symbol. This round proves it:

* **The Gauss sums modulo `p` in the display's normalization** (`gaussP_twist`, `conj_σO_cub`,
  **`gaussP_one_two`** and `cub_three_sq_eq_sym6`): `γ_j(h) = (h/p)₃^{2j}·γ_j(1)` for `p ∤ h`,
  `γ_2(1) = |p|·conj γ₂(𝔭)` and `(3/p)₃² = (δ₃/p)₆²`.
* **θ's coefficients at squarefree indices** (**`rhoM_mul_prime_sym`**, `gamI_one`, `conj_sym6_pow_four`,
  `rhoM_prod_πP` and **`rhoM_sqfree`**): `ρ(hp) = (δ₃/p)₆²·(h/p)₆²·conj γ₂(𝔭)·ρ(h)`, and
  `ρ(n) = (δ₃/n)₆²·conj γ₂(n)·ρ(1)` for primary `n` with `(n)` squarefree of norm prime to `6`.
* **The cube factor and the display's coefficients** (**`rhoM_mul_cube`** and **`tauTh_sqfree_cube`**):
  `ρ(nb³) = |b|·ρ(n)` for primary `b` of norm prime to `6`, and
  `τ(δ₃nb³) = τ(δ₃)·N(b)^{1/2}·(δ₃/n)₆²·conj γ₂(n)`.
-/

open Ideal NumberField
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Eis

/-! ### The Gauss sums modulo `p` in the display's normalization -/

/-- **`γ_j(h) = (h/p)₃^{2j}·γ_j(1)`** for a primary prime `p ∤ h`. With `ah + bp = 1`, `f ↦ af` permutes the
classes modulo `p` (round 452's `tsum_quot_affine'`), multiplies the symbol by `(a/p)₃^j = (h/p)₃^{2j}` and
leaves the phase `ψ_p(−fh)` at `ψ_p(−f)`. -/
theorem gaussP_twist {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {h : 𝓞 K} (hph : ¬ p ∣ h) (j : ℕ) :
    gaussP h p j = σO (cub h (span {p})) ^ (2 * j) * gaussP 1 p j := by
  have hp0 := hp.ne_zero
  obtain ⟨a, b, hab⟩ := isCoprime_of_not_dvd hp hph
  have ha : IsCoprime a p := ⟨h, b, by linear_combination hab⟩
  have hF : ∀ y y', p ∣ y - y' → gTerm h p j y = gTerm h p j y' := by
    intro y y' hyy
    obtain ⟨u, hu⟩ := hyy
    rw [show y = y' + p * u by rw [← hu]; ring, gTerm_add h hp0]
  have key := tsum_quot_affine' hp0 ha hF 0
  simp only [zero_add] at key
  have hterm : ∀ y, gTerm h p j (a * y) = σO (cub a (span {p})) ^ j * gTerm 1 p j y := by
    intro y
    unfold gTerm
    rw [ebr_gTerm, ebr_gTerm, cub_mul_left, map_mul, mul_pow]
    have : ψc p (-(a * y) * h) = ψc p (-y * 1) := by
      rw [show -(a * y) * h = -y * 1 + p * (y * b) by linear_combination (-y) * hab]
      exact ψc_add_mul p hp0 _ _
    rw [this]
    ring
  have hcub : σO (cub a (span {p})) = σO (cub h (span {p})) ^ 2 := by
    have h1 : cub a (span {p}) * cub h (span {p}) = 1 := by
      rw [← cub_mul_left, cub_congr (show p ∣ a * h - 1 from ⟨-b, by linear_combination hab⟩), cub_one hpp]
    have h3 : σO (cub h (span {p})) ^ 3 = 1 := by
      rw [← map_pow, cub_pow_three hpp (isCoprime_of_not_dvd hp hph), map_one]
    have h1' := congrArg σO h1
    rw [map_mul, map_one] at h1'
    linear_combination σO (cub h (span {p})) ^ 2 * h1' - σO (cub a (span {p})) * h3
  unfold gaussP
  rw [← key]
  simp_rw [hterm]
  rw [tsum_mul_left, hcub, ← pow_mul]

/-- **`conj (z/p)₃ = (z/p)₃²`**: `(z/p)₃` is `0` or a cube root of unity (round 370's `norm_σO_cub`). -/
theorem conj_σO_cub {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) (z : 𝓞 K) :
    conj (σO (cub z (span {p}))) = σO (cub z (span {p})) ^ 2 := by
  by_cases hz : p ∣ z
  · rw [cub_span_eq_zero hp hz, map_zero, map_zero]
    ring
  · have hc := isCoprime_of_not_dvd hp hz
    have h1 := norm_σO_cub hpp hc
    have h3 : σO (cub z (span {p})) ^ 3 = 1 := by rw [← map_pow, cub_pow_three hpp hc, map_one]
    set w := σO (cub z (span {p}))
    have hw : w * conj w = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
      norm_num
    linear_combination w ^ 2 * hw - conj w * h3

/-- **`γ_2(1) = |p|·conj γ₂(𝔭)`** for a primary prime `p` of norm prime to `6`, with round 305's normalized
Gauss sum `γ₂(𝔭) = gamI 2 (span {p})`: `(r/𝔭)₆² = (r/p)₃` (round 362's `sym6_sq_eq_cub`), and
`conj ψ_p(r) = ψ_p(−r)` (round 371's `conj_ψc`). -/
theorem gaussP_one_two {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) (h6 : (absNorm (span {p})).Coprime 6) :
    gaussP 1 p 2 = ((‖σO p‖ : ℝ) : ℂ) * conj (gamI 2 (span {p})) := by
  classical
  have hp0 := hp.ne_zero
  have := finite_quot p hp0
  let : Fintype (𝓞 K ⧸ span {p}) := Fintype.ofFinite _
  have hq' : ((‖σO p‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 (σO_ne_zero hp0)).ne'
  have hg : gaussP 1 p 2 = conj (gaussTr p (fun z => sym6 z (span {p}) ^ 2) 1) := by
    unfold gaussTr gaussP
    rw [finsum_eq_sum_of_fintype, tsum_fintype, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    unfold gTerm
    dsimp only
    rw [ebr_gTerm, map_mul, conj_ψc, sym6_sq_eq_cub h6, conj_σO_cub hp hpp, mul_one, mul_one]
  unfold gamI
  rw [pgen_eq hpp, hg, map_div₀, Complex.conj_ofReal]
  field_simp

/-- **`(3/p)₃² = (δ₃/p)₆²`** for a primary prime `p` of norm prime to `6`, since `3 = −δ₃²`. -/
theorem cub_three_sq_eq_sym6 {p : 𝓞 K} (hpp : Primary p) (h6 : (absNorm (span {p})).Coprime 6) :
    σO (cub 3 (span {p})) ^ 2 = sym6 δ3 (span {p}) ^ 2 := by
  rw [sym6_sq_eq_cub h6, show (3 : 𝓞 K) = -(δ3 * δ3) by rw [← sq, δ3_sq, neg_neg], cub_neg hpp,
    cub_mul_left, map_mul]
  have h3 : σO (cub δ3 (span {p})) ^ 3 = 1 := by
    rw [← map_pow, cub_pow_three hpp (isCoprime_δ3 hpp), map_one]
  linear_combination σO (cub δ3 (span {p})) * h3

/-! ### θ's coefficients at squarefree indices -/

/-- **`ρ(hp) = (δ₃/p)₆²·(h/p)₆²·conj γ₂(𝔭)·ρ(h)`** for a primary prime `p ∤ h` of norm prime to `6` (round
454's `rhoM_mul_prime_eq` in the display's normalization). -/
theorem rhoM_mul_prime_sym {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p)
    (hpp : Primary p) (h6 : (absNorm (span {p})).Coprime 6) {h : 𝓞 K} (hph : ¬ p ∣ h) :
    rhoM (h * p) r Y hY = sym6 δ3 (span {p}) ^ 2 * sym6 h (span {p}) ^ 2 * conj (gamI 2 (span {p})) *
      rhoM h r Y hY := by
  have hq' : ((‖σO p‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.2 (σO_ne_zero hp.ne_zero)).ne'
  have h3 : σO (cub h (span {p})) ^ 3 = 1 := by
    rw [← map_pow, cub_pow_three hpp (isCoprime_of_not_dvd hp hph), map_one]
  rw [rhoM_mul_prime_eq hr hY hp hpp hph, gaussP_twist hp hpp hph 2, gaussP_one_two hp hpp h6,
    cub_three_sq_eq_sym6 hpp h6, sym6_sq_eq_cub h6 h,
    show σO (cub h (span {p})) ^ (2 * 2) = σO (cub h (span {p})) by
      rw [show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]]
  field_simp

/-- `γ_j(𝒪) = 1` (round 313's `pgen_one`, round 295's `gaussTr_one_const`). -/
theorem gamI_one (j : ℕ) : gamI j (1 : Ideal (𝓞 K)) = 1 := by
  unfold gamI
  simp only [pgen_one, sym6_one_right, one_pow, gaussTr_one_const, map_one, norm_one, Complex.ofReal_one,
    div_one]

/-- `conj(w)⁴ = w²` for a value of the sextic symbol at a prime, through `conj w = w⁵` (round 319's
`chiS_conj_eq_pow_five`) and `w⁷ = w`. -/
theorem conj_sym6_pow_four (u : 𝓞 K) (P : Pr) :
    conj (sym6 u (idl {P}) ^ 4) = sym6 u (idl {P}) ^ 2 := by
  have h7 := sym6_pow_seven u (idl {P})
  rw [map_pow, sym6_idl, chiS_conj_eq_pow_five, ← pow_mul]
  rw [sym6_idl] at h7
  linear_combination (chiS {P} u ^ 13 + chiS {P} u ^ 7 + chiS {P} u) * h7

/-- **θ's coefficients over a finite set of primes prime to `6`**: `ρ(∏_{P∈A} π_P) = (δ₃/𝔫)₆²·conj γ₂(𝔫)·ρ(1)`
with `𝔫 = ∏_{P∈A} P` (round 307's `idl`), by induction on `A` through `rhoM_mul_prime_sym` and round 305's
twisted multiplicativity `gamI_two_mul`. -/
theorem rhoM_prod_πP {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (A : Finset Pr) :
    rhoM (∏ P ∈ A, πP P) r Y hY = sym6 δ3 (idl A) ^ 2 * conj (gamI 2 (idl A)) * rhoM 1 r Y hY := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, show idl (∅ : Finset Pr) = 1 by simp [idl], sym6_one_right, gamI_one, map_one]
    ring
  | insert P A hPA ih =>
    have hdisj : Disjoint A {P} := Finset.disjoint_singleton_right.2 hPA
    have hidl : idl (insert P A) = idl A * idl {P} := by
      rw [Finset.insert_eq, Finset.union_comm, idl_union hdisj]
    have hsing : idl {P} = span {πP P} := by
      rw [show idl {P} = P.1 by simp [idl], (πP_spec P).2]
    have h6 : (absNorm (span {πP P})).Coprime 6 := by
      rw [(πP_spec P).2]; exact coprime6_Pr P
    have hcop : IsCoprime (πP P) (∏ Q ∈ A, πP Q) :=
      IsCoprime.prod_right fun Q hQ => isCoprime_πP fun h => hPA (h ▸ hQ)
    have hndvd : ¬ πP P ∣ ∏ Q ∈ A, πP Q := fun h =>
      (prime_πP P).not_isUnit (hcop.isUnit_of_dvd' dvd_rfl h)
    rw [Finset.prod_insert hPA, mul_comm, rhoM_mul_prime_sym hr hY (prime_πP P) (πP_spec P).1 h6 hndvd, ih,
      hidl, sym6_mul_right _ (idl_ne_bot A) (idl_ne_bot {P}),
      gamI_two_mul (idl_coprime6 A) (idl_squarefree A) (idl_coprime6 {P}) (idl_squarefree {P})
        (isRelPrime_idl hdisj), map_mul, map_mul, conj_sym6_pow_four, pgen_idl, hsing]
    ring

/-- **θ's coefficients at the squarefree indices prime to `6`**: `ρ(n) = (δ₃/n)₆²·conj γ₂(n)·ρ(1)` for primary
`n` with `(n)` squarefree of norm prime to `6`. -/
theorem rhoM_sqfree {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {n : 𝓞 K} (hn : Primary n)
    (hsq : Squarefree (span {n})) (h6 : (absNorm (span {n})).Coprime 6) :
    rhoM n r Y hY = sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})) * rhoM 1 r Y hY := by
  have h1 := rhoM_prod_πP hr hY (primeSet (span {n}))
  rw [idl_primeSet h6 hsq, ← pgen_eq_prod h6 hsq, pgen_eq hn] at h1
  exact h1

/-! ### The cube factor and the display's coefficients -/

/-- **`ρ(nb³) = |b|·ρ(n)`** for `n ≠ 0` and primary `b` of norm prime to `6`: round 449's `rhoM_cube`, by
induction on `N(b)` over the primary prime factors of `b`. -/
theorem rhoM_mul_cube {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {n : 𝓞 K} (hn : n ≠ 0) {b : 𝓞 K}
    (hb : Primary b) (h6 : (absNorm (span {b})).Coprime 6) :
    rhoM (n * b ^ 3) r Y hY = (‖σO b‖ : ℂ) * rhoM n r Y hY := by
  suffices H : ∀ N : ℕ, ∀ b : 𝓞 K, absNorm (span {b}) = N → Primary b → (absNorm (span {b})).Coprime 6 →
      rhoM (n * b ^ 3) r Y hY = (‖σO b‖ : ℂ) * rhoM n r Y hY from H _ b rfl hb h6
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro b hN hb h6
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl, Ideal.absNorm_bot] at h6
      norm_num at h6
    by_cases hu : IsUnit b
    · have h1 : b = 1 := primary_unique hb primary_one
        (by rw [Ideal.span_singleton_eq_top.2 hu, Ideal.span_singleton_one])
      subst h1
      simp
    · have hI0 : span {b} ≠ (0 : Ideal (𝓞 K)) := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
      have hIu : ¬ IsUnit (span {b} : Ideal (𝓞 K)) := by
        rw [Ideal.isUnit_iff, Ideal.span_singleton_eq_top]; exact hu
      obtain ⟨P, hP⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hI0 hIu
      set P' : Pr := ⟨P, isMaximal_of_factor hP, six_not_mem_of_factor h6 hP⟩
      have hpb : πP P' ∣ b := by
        rw [← Ideal.mem_span_singleton, (πP_spec P').2]
        exact Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
          (Ideal.mem_span_singleton_self b)
      obtain ⟨b', hbb'⟩ := hpb
      have hb' : Primary b' := (primary_mul_iff (πP_spec P').1).1 (hbb' ▸ hb)
      have hb'0 : b' ≠ 0 := right_ne_zero_of_mul (hbb' ▸ hb0)
      have hNmul : absNorm (span {πP P' * b'}) = absNorm (span {πP P'}) * absNorm (span {b'}) := by
        rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
      have hNp : 1 < absNorm (span {πP P'}) := by
        have h0 : absNorm (span {πP P'}) ≠ 0 := by
          rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact (prime_πP P').ne_zero
        have h1 : absNorm (span {πP P'}) ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]; exact (prime_πP P').not_isUnit
        omega
      have hNb' : 0 < absNorm (span {b'}) := by
        rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb'0
      have hlt : absNorm (span {b'}) < N := by
        rw [← hN, hbb', hNmul]
        exact lt_mul_left hNb' hNp
      have h6' : (absNorm (span {b'})).Coprime 6 :=
        Nat.Coprime.coprime_dvd_left (by rw [hbb', hNmul]; exact dvd_mul_left _ _) h6
      have hx : n * b' ^ 3 ≠ 0 := mul_ne_zero hn (pow_ne_zero 3 hb'0)
      rw [hbb', show n * (πP P' * b') ^ 3 = πP P' ^ 3 * (n * b' ^ 3) by ring,
        rhoM_cube hr hY (prime_πP P') (πP_spec P').1 hx, ih _ hlt b' rfl hb' h6', map_mul, norm_mul,
        Complex.ofReal_mul]
      ring

/-- **θ's coefficients at `δ₃nb³`**: for primary `n` and `b` with `(n)` squarefree and `N(nb)` prime to `6`,
`τ(δ₃nb³) = τ(δ₃)·N(b)^{1/2}·(δ₃/n)₆²·conj γ₂(n)`, the coefficient formula of round 361's `KubotaTheta` at
`δ₃nb³` with `C = τ(δ₃)`, for round 436's `tauTh`. -/
theorem tauTh_sqfree_cube {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {n b : 𝓞 K} (hn : Primary n)
    (hb : Primary b) (hsq : Squarefree (span {n})) (h6 : (absNorm (span {n * b})).Coprime 6) :
    tauTh r Y hY (δ3 * n * b ^ 3) = tauTh r Y hY δ3 * (Real.sqrt (absNorm (span {b})) : ℂ) *
      sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})) := by
  have hNmul : absNorm (span {n * b}) = absNorm (span {n}) * absNorm (span {b}) := by
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  have h6n : (absNorm (span {n})).Coprime 6 :=
    Nat.Coprime.coprime_dvd_left (by rw [hNmul]; exact dvd_mul_right _ _) h6
  have h6b : (absNorm (span {b})).Coprime 6 :=
    Nat.Coprime.coprime_dvd_left (by rw [hNmul]; exact dvd_mul_left _ _) h6
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl, Ideal.absNorm_bot] at h6n
    norm_num at h6n
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl, Ideal.absNorm_bot] at h6b
    norm_num at h6b
  have hsqrt : Real.sqrt (absNorm (span {b})) = ‖σO b‖ := by
    rw [← sq_norm_σO, Real.sqrt_sq (norm_nonneg _)]
  rw [show δ3 * n * b ^ 3 = δ3 * (n * b ^ 3) by ring,
    tauTh_δ3_mul r Y hY (mul_ne_zero hn0 (pow_ne_zero 3 hb0)), show δ3 = δ3 * 1 by ring,
    tauTh_δ3_mul r Y hY one_ne_zero, mul_one, rhoM_mul_cube hr hY hn0 hb h6b,
    rhoM_sqfree hr hY hn hsq h6n, hsqrt]
  ring

end Eis

end

#print axioms Eis.gaussP_twist
#print axioms Eis.conj_σO_cub
#print axioms Eis.gaussP_one_two
#print axioms Eis.cub_three_sq_eq_sym6
#print axioms Eis.rhoM_mul_prime_sym
#print axioms Eis.gamI_one
#print axioms Eis.conj_sym6_pow_four
#print axioms Eis.rhoM_prod_πP
#print axioms Eis.rhoM_sqfree
#print axioms Eis.rhoM_mul_cube
#print axioms Eis.tauTh_sqfree_cube
