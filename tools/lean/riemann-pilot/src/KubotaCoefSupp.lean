import KubotaCoefScalar

/-! # θ's support and size condition away from `λ` (round 458)

S5f-14 of round 360's plan, part 3. Round 457's next step planned round 361's support and size condition
`ThetaSupp` for θ's coefficients at `∞`: `τ(m) ≠ 0` only at `m = uλ^k·n·b³` (round 341's `dualPt`,
`λ = ω − 1`) with `n` squarefree and `N(n)`, `N(b)` prime to `3`, and `|τ(m)| ≤ K·3^{k/6}·N(b)^{1/2}` there.
This round proves the support and the size away from `λ`, and with them `ThetaSupp` from the bound at `λ`
alone:

* **The modulus of the Gauss sums modulo `p`** (`conj_gaussP_one_one`, `norm_gaussP_two` and
  **`norm_rhoM_mul_prime`**): `conj γ_1(1) = γ_2(1)`, so `|γ_2(x)| = |p|` for `p ∤ x`, and `|ρ(xp)| = |ρ(x)|`.
* **The part at `λ`** (`absNorm_span_lam`, `not_dvd_unit_mul_lam_pow` and `exists_unit_lam_pow_primary`):
  `N(λ) = 3`, no primary prime divides `uλ^j`, and every `x ≠ 0` is `uλ^j·y` with `y` primary.
* **The support and the size away from `λ`** (**`rhoM_supp_norm`**): for `z` with no primary prime factor and
  `y` primary, `ρ(zy) ≠ 0` only if `y = n·b³` with `n`, `b` primary and `(n)` squarefree, and then
  `|ρ(zy)| = |b|·|ρ(z)|`.
* **Round 361's support and size condition** (`coprime_three_of_primary` and **`thetaSupp_tauTh_of_lam`**):
  `ThetaSupp` for `τ` from `|ρ(uλ^j)| ≤ A·3^{j/6}`.
-/

open Ideal NumberField
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Eis

/-! ### The modulus of the Gauss sums modulo `p` -/

/-- **`conj γ_1(1) = γ_2(1)`** for a primary prime `p`: `conj (f/p)₃ = (f/p)₃²` (round 455's `conj_σO_cub`),
`conj ψ_p(−f) = ψ_p(f)` (round 371's `conj_ψc`), and `f ↦ −f` permutes the classes modulo `p` (round 452's
`tsum_quot_affine'`), with `(−f/p)₃ = (f/p)₃` (round 362's `cub_neg`). -/
theorem conj_gaussP_one_one {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) :
    conj (gaussP 1 p 1) = gaussP 1 p 2 := by
  classical
  have hp0 := hp.ne_zero
  have := finite_quot p hp0
  let : Fintype (𝓞 K ⧸ span {p}) := Fintype.ofFinite _
  have hterm : ∀ f : 𝓞 K, conj (gTerm 1 p 1 f) = gTerm 1 p 2 (0 + -1 * f) := by
    intro f
    unfold gTerm
    rw [ebr_gTerm, ebr_gTerm, map_mul, conj_ψc, pow_one, conj_σO_cub hp hpp, zero_add,
      show -1 * f = -f by ring, cub_neg hpp]
    congr 2
    ring
  have hF : ∀ y y', p ∣ y - y' → gTerm 1 p 2 y = gTerm 1 p 2 y' := by
    intro y y' hyy
    obtain ⟨t, ht⟩ := hyy
    rw [show y = y' + p * t by linear_combination ht]
    exact gTerm_add 1 hp0 2 y' t
  have hu : IsCoprime (-1 : 𝓞 K) p := isCoprime_one_left.neg_left
  unfold gaussP
  rw [← tsum_quot_affine' hp0 hu hF 0, tsum_fintype, tsum_fintype, map_sum]
  exact Finset.sum_congr rfl fun f _ => hterm _

/-- **`|γ_2(x)| = |p|`** for a primary prime `p ∤ x`: `γ_1(1)·γ_2(1) = N(p)` (round 453's
`gaussP_one_mul_two`) with `γ_2(1) = conj γ_1(1)`, and `γ_2(x) = (x/p)₃⁴·γ_2(1)` (round 455's `gaussP_twist`).
-/
theorem norm_gaussP_two {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {h : 𝓞 K} (hph : ¬ p ∣ h) :
    ‖gaussP h p 2‖ = ‖σO p‖ := by
  have h1 := gaussP_one_mul_two hp hpp (show ¬ p ∣ (1 : 𝓞 K) from hp.not_dvd_one)
  rw [← conj_gaussP_one_one hp hpp, Complex.mul_conj] at h1
  have hN : ‖gaussP 1 p 2‖ ^ 2 = ‖σO p‖ ^ 2 := by
    rw [← conj_gaussP_one_one hp hpp, Complex.norm_conj, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, normSq_σO]
    exact_mod_cast h1
  rw [gaussP_twist hp hpp hph 2, norm_mul, norm_pow, norm_σO_cub hpp (isCoprime_of_not_dvd hp hph), one_pow,
    one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hN

/-- **`|ρ(xp)| = |ρ(x)|`** for a primary prime `p ∤ x`, from round 454's `rhoM_mul_prime_eq`. -/
theorem norm_rhoM_mul_prime {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p)
    (hpp : Primary p) {x : 𝓞 K} (hpx : ¬ p ∣ x) : ‖rhoM (x * p) r Y hY‖ = ‖rhoM x r Y hY‖ := by
  have hq : 0 < ‖σO p‖ := norm_pos_iff.2 (σO_ne_zero hp.ne_zero)
  rw [rhoM_mul_prime_eq hr hY hp hpp hpx, norm_div, norm_mul, norm_mul, norm_pow,
    norm_σO_cub hpp (isCoprime_three_of_primary hpp), one_pow, one_mul, norm_gaussP_two hp hpp hpx,
    Complex.norm_real, Real.norm_of_nonneg hq.le]
  field_simp

/-! ### The part at `λ` -/

/-- `N(λ) = 3` for `λ = ω − 1` (round 308's `absNorm_crd`). -/
theorem absNorm_span_lam : absNorm (span {(ω - 1 : 𝓞 K)}) = 3 := by
  have h := absNorm_crd ![-1, 1]
  have hc : crd ![-1, 1] = (ω - 1 : 𝓞 K) := by simp [crd]; ring
  rw [hc] at h
  have h3 : (absNorm (span {(ω - 1 : 𝓞 K)}) : ℝ) = 3 := by
    rw [h]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  exact_mod_cast h3

/-- **No primary prime divides `uλ^j`**: it would divide `λ`, and `N(p) ∣ 3` with `N(p) ≡ 1 (mod 3)` (round
362's `absNorm_primary_mod`) gives `N(p) = 1`. -/
theorem not_dvd_unit_mul_lam_pow {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) (u : (𝓞 K)ˣ) (j : ℕ) :
    ¬ p ∣ (u : 𝓞 K) * (ω - 1) ^ j := by
  intro h
  rcases hp.dvd_or_dvd h with h | h
  · exact hp.not_isUnit (isUnit_of_dvd_unit h u.isUnit)
  · have hl := hp.dvd_of_dvd_pow h
    have hle : span {(ω - 1 : 𝓞 K)} ≤ span {p} := Ideal.span_singleton_le_span_singleton.2 hl
    have hd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [absNorm_span_lam] at hd
    have h1 : absNorm (span {p}) ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]; exact hp.not_isUnit
    have hm := absNorm_primary_mod hpp
    have h3 : absNorm (span {p}) ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : absNorm (span {p}) <;> simp_all

/-- **`x = uλ^j·y` with `y` primary** for `x ≠ 0`, by induction on `N(x)`, with round 290's `exists_primary`
for `x` prime to `λ`. -/
theorem exists_unit_lam_pow_primary {x : 𝓞 K} (hx : x ≠ 0) :
    ∃ (u : (𝓞 K)ˣ) (j : ℕ) (y : 𝓞 K), Primary y ∧ x = u * (ω - 1) ^ j * y := by
  suffices H : ∀ N : ℕ, ∀ x : 𝓞 K, x ≠ 0 → absNorm (span {x}) = N →
      ∃ (u : (𝓞 K)ˣ) (j : ℕ) (y : 𝓞 K), Primary y ∧ x = u * (ω - 1) ^ j * y from H _ x hx rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x hx hN
    by_cases hl : (ω - 1 : 𝓞 K) ∣ x
    · obtain ⟨x', rfl⟩ := hl
      have hx' : x' ≠ 0 := right_ne_zero_of_mul hx
      have hlt : absNorm (span {x'}) < N := by
        rw [← hN, ← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_lam]
        have : 0 < absNorm (span {x'}) := by
          rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hx'
        omega
      obtain ⟨u, j, y, hy, rfl⟩ := ih _ hlt x' hx' rfl
      exact ⟨u, j + 1, y, hy, by ring⟩
    · obtain ⟨u, hu⟩ := exists_primary hl
      refine ⟨u⁻¹, 0, u * x, hu, ?_⟩
      rw [pow_zero, mul_one, ← mul_assoc, Units.inv_mul, one_mul]

/-! ### The support and the size away from `λ` -/

/-- **The support and the size away from `λ`**: for `z ≠ 0` with no primary prime factor and `y` primary with
`ρ(zy) ≠ 0`, `y = n·b³` with `n`, `b` primary and `(n)` squarefree, and `|ρ(zy)| = |b|·|ρ(z)|`. By induction
on `N(y)` at a primary prime factor `p` of `y`: round 449's `rhoM_cube` for `p³ ∣ y`, round 454's
`rhoM_mul_sq`, which excludes `p² ∥ y`, and `norm_rhoM_mul_prime` for `p ∥ y`. -/
theorem rhoM_supp_norm {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {z : 𝓞 K} (hz0 : z ≠ 0)
    (hz : ∀ p : 𝓞 K, Prime p → Primary p → ¬ p ∣ z) {y : 𝓞 K} (hy : Primary y)
    (hρ : rhoM (z * y) r Y hY ≠ 0) :
    ∃ n b : 𝓞 K, Primary n ∧ Primary b ∧ Squarefree (span {n}) ∧ y = n * b ^ 3 ∧
      ‖rhoM (z * y) r Y hY‖ = ‖σO b‖ * ‖rhoM z r Y hY‖ := by
  suffices H : ∀ N : ℕ, ∀ y : 𝓞 K, absNorm (span {y}) = N → Primary y → rhoM (z * y) r Y hY ≠ 0 →
      ∃ n b : 𝓞 K, Primary n ∧ Primary b ∧ Squarefree (span {n}) ∧ y = n * b ^ 3 ∧
        ‖rhoM (z * y) r Y hY‖ = ‖σO b‖ * ‖rhoM z r Y hY‖ from H _ y rfl hy hρ
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro y hN hy hρ
    have hy0 : y ≠ 0 := primary_ne_zero hy
    by_cases hu : IsUnit y
    · have : y = 1 := primary_unique hy primary_one
        (by rw [Ideal.span_singleton_eq_top.2 hu, Ideal.span_singleton_one])
      subst this
      refine ⟨1, 1, primary_one, primary_one, ?_, by ring, by simp⟩
      rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]
      exact squarefree_one
    have hI0 : span {y} ≠ (0 : Ideal (𝓞 K)) := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hy0
    have hIu : ¬ IsUnit (span {y} : Ideal (𝓞 K)) := by
      rw [Ideal.isUnit_iff, Ideal.span_singleton_eq_top]; exact hu
    obtain ⟨P, hP⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hI0 hIu
    have hPm : P.IsMaximal := isMaximal_of_factor hP
    have hyP : y ∈ P := Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
      (Ideal.mem_span_singleton_self y)
    have hP3 : (3 : 𝓞 K) ∉ P := by
      intro h3
      obtain ⟨t, ht⟩ := hy
      have h1P : (1 : 𝓞 K) ∈ P := by
        have : (1 : 𝓞 K) = y - 3 * t := by linear_combination -ht
        rw [this]
        exact P.sub_mem hyP (P.mul_mem_right t h3)
      exact hPm.ne_top ((Ideal.eq_top_iff_one P).2 h1P)
    obtain ⟨hpp, hpP⟩ := pgen_maximal P hP3
    set p := pgen P
    have hp0 : p ≠ 0 := by
      intro h
      rw [h, Ideal.span_singleton_eq_bot.2 rfl] at hpP
      rw [← hpP] at hyP
      exact hy0 ((Submodule.mem_bot _).1 hyP)
    have hp : Prime p := (Ideal.span_singleton_prime hp0).1 (hpP ▸ hPm.isPrime)
    have hNp : 1 < absNorm (span {p}) := by
      have h0 : absNorm (span {p}) ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hp0
      have h1 : absNorm (span {p}) ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]; exact hp.not_isUnit
      omega
    have hNmul : ∀ a b : 𝓞 K, absNorm (span {a * b}) = absNorm (span {a}) * absNorm (span {b}) := by
      intro a b
      rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
    have hNpos : ∀ b : 𝓞 K, b ≠ 0 → 0 < absNorm (span {b}) := by
      intro b hb
      rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
    have hpy : p ∣ y := by
      rw [← Ideal.mem_span_singleton, hpP]; exact hyP
    have hpz := hz p hp hpp
    by_cases h3 : p ^ 3 ∣ y
    · obtain ⟨y', rfl⟩ := h3
      have hy' : Primary y' := (primary_mul_iff (primary_pow hpp 3)).1 hy
      have hy'0 : y' ≠ 0 := primary_ne_zero hy'
      have hzy : z * (p ^ 3 * y') = p ^ 3 * (z * y') := by ring
      have hcube := rhoM_cube hr hY hp hpp (mul_ne_zero hz0 hy'0)
      rw [hzy, hcube] at hρ ⊢
      have hρ' : rhoM (z * y') r Y hY ≠ 0 := right_ne_zero_of_mul hρ
      have hlt : absNorm (span {y'}) < N := by
        rw [← hN, hNmul, pow_succ, hNmul, sq, hNmul]
        have := hNpos y' hy'0
        have : 1 < absNorm (span {p}) * absNorm (span {p}) * absNorm (span {p}) := by nlinarith
        nlinarith
      obtain ⟨n, b, hn, hb, hsq, rfl, hnorm⟩ := ih _ hlt y' rfl hy' hρ'
      refine ⟨n, p * b, hn, hpp.mul hb, hsq, by ring, ?_⟩
      rw [norm_mul, hnorm, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), map_mul, norm_mul]
      ring
    by_cases h2 : p ^ 2 ∣ y
    · exfalso
      obtain ⟨h, rfl⟩ := h2
      have hph : ¬ p ∣ h := by
        rintro ⟨t, rfl⟩
        exact h3 ⟨t, by ring⟩
      have hpzh : ¬ p ∣ z * h := by
        intro hd
        rcases hp.dvd_or_dvd hd with hd | hd
        · exact hpz hd
        · exact hph hd
      apply hρ
      rw [show z * (p ^ 2 * h) = z * h * p ^ 2 by ring]
      exact rhoM_mul_sq hr hY hp hpp hpzh
    · obtain ⟨h, rfl⟩ := hpy
      have hph : ¬ p ∣ h := by
        rintro ⟨t, rfl⟩
        exact h2 ⟨t, by ring⟩
      have hpzh : ¬ p ∣ z * h := by
        intro hd
        rcases hp.dvd_or_dvd hd with hd | hd
        · exact hpz hd
        · exact hph hd
      have hh : Primary h := (primary_mul_iff hpp).1 hy
      have hh0 : h ≠ 0 := primary_ne_zero hh
      have hnorm1 : ‖rhoM (z * (p * h)) r Y hY‖ = ‖rhoM (z * h) r Y hY‖ := by
        rw [show z * (p * h) = z * h * p by ring]
        exact norm_rhoM_mul_prime hr hY hp hpp hpzh
      have hρ' : rhoM (z * h) r Y hY ≠ 0 := by
        intro h0
        apply hρ
        rw [← norm_eq_zero, hnorm1, h0, norm_zero]
      have hlt : absNorm (span {h}) < N := by
        rw [← hN, hNmul]
        have := hNpos h hh0
        nlinarith
      obtain ⟨n, b, hn, hb, hsq, rfl, hnorm⟩ := ih _ hlt h rfl hh hρ'
      have hpn : ¬ p ∣ n := fun hd => hph (dvd_mul_of_dvd_left hd _)
      refine ⟨p * n, b, hpp.mul hn, hb, ?_, by ring, by rw [hnorm1, hnorm]⟩
      rw [← Ideal.span_singleton_mul_span_singleton, squarefree_mul_iff]
      have hPp : Prime (span {p} : Ideal (𝓞 K)) :=
        Ideal.prime_of_isPrime (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0) (hpP ▸ hPm.isPrime)
      refine ⟨?_, hPp.squarefree, hsq⟩
      rw [hPp.irreducible.isRelPrime_iff_not_dvd, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
      exact hpn

/-! ### Round 361's support and size condition, from the bound at `λ` -/

/-- `N(n)` is prime to `3` for primary `n` (round 362's `absNorm_primary_mod`). -/
theorem coprime_three_of_primary {n : 𝓞 K} (hn : Primary n) : (absNorm (span {n})).Coprime 3 := by
  have h := absNorm_primary_mod hn
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  omega

/-- **Round 361's support and size condition for θ's coefficients at `∞`, from the bound at `λ`**: if
`|ρ(uλ^j)| ≤ A·3^{j/6}` for every unit `u` and every `j`, then `ThetaSupp (A/(9√3/2)) τ`. For `τ(m) ≠ 0`,
`m = δ₃x` with `x = uλ^j·n·b³` (`exists_unit_lam_pow_primary`, `rhoM_supp_norm`), which is round 341's
`dualPt` at `(−ωu, j + 1, (n), (b))` since `δ₃ = −ω·λ`, and `|τ(m)| = |b|·|ρ(uλ^j)|/(9√3/2)` (round 436's
`tauTh_δ3_mul`). -/
theorem thetaSupp_tauTh_of_lam {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {A : ℝ} (hA : 0 ≤ A)
    (hlam : ∀ (u : (𝓞 K)ˣ) (j : ℕ), ‖rhoM ((u : 𝓞 K) * (ω - 1) ^ j) r Y hY‖ ≤ A * (3 : ℝ) ^ ((j : ℝ) / 6)) :
    ThetaSupp (A / (9 * (Real.sqrt 3 / 2))) (tauTh r Y hY) := by
  have hc : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
  refine ⟨div_nonneg hA hc.le, fun m hm => ?_⟩
  by_cases hex : ∃ x, x ≠ 0 ∧ m = δ3 * x
  swap
  · exact absurd (tauTh_of_not r Y hY hex) hm
  obtain ⟨x, hx, rfl⟩ := hex
  have hρ : rhoM x r Y hY ≠ 0 := by
    intro hz
    apply hm
    rw [tauTh_δ3_mul r Y hY hx, hz, zero_div]
  obtain ⟨u, j, y, hy, rfl⟩ := exists_unit_lam_pow_primary hx
  have hz0 : (u : 𝓞 K) * (ω - 1) ^ j ≠ 0 := by
    have hl : (ω - 1 : 𝓞 K) ≠ 0 := by
      intro h
      have := absNorm_span_lam
      rw [h, Ideal.span_singleton_eq_bot.2 rfl, Ideal.absNorm_bot] at this
      norm_num at this
    exact mul_ne_zero u.ne_zero (pow_ne_zero j hl)
  obtain ⟨n, b, hn, hb, hsq, rfl, hnorm⟩ :=
    rhoM_supp_norm hr hY hz0 (fun p hp hpp => not_dvd_unit_mul_lam_pow hp hpp u j) hy hρ
  refine ⟨(-(ωu * u), j + 1, span {n}, span {b}), ?_, hsq, coprime_three_of_primary hn,
    coprime_three_of_primary hb, ?_⟩
  · simp only [dualPt, pgen_eq hn, pgen_eq hb, Units.val_neg, Units.val_mul, coe_ωu]
    obtain ⟨t, ht⟩ := lam_dvd_δ3
    rw [ht]
    have : t = -ω := by
      have h' : δ3 = (ω - 1) * -ω := by unfold δ3; linear_combination ω_sq_add
      have hl : (ω - 1 : 𝓞 K) ≠ 0 := by
        intro h
        have := absNorm_span_lam
        rw [h, Ideal.span_singleton_eq_bot.2 rfl, Ideal.absNorm_bot] at this
        norm_num at this
      exact mul_left_cancel₀ hl (ht.symm.trans h')
    rw [this]
    ring
  · rw [tauTh_δ3_mul r Y hY hx, norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le, hnorm,
      norm_σO_eq_sqrt]
    have hb3 : (3 : ℝ) ^ ((j : ℝ) / 6) ≤ (3 : ℝ) ^ (((j + 1 : ℕ) : ℝ) / 6) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
    have hlj := hlam u j
    rw [div_le_iff₀ hc]
    have hs := Real.sqrt_nonneg (absNorm (span {b}) : ℝ)
    calc Real.sqrt (absNorm (span {b})) * ‖rhoM ((u : 𝓞 K) * (ω - 1) ^ j) r Y hY‖
        ≤ Real.sqrt (absNorm (span {b})) * (A * (3 : ℝ) ^ (((j + 1 : ℕ) : ℝ) / 6)) :=
          mul_le_mul_of_nonneg_left (hlj.trans (mul_le_mul_of_nonneg_left hb3 hA)) hs
      _ = A / (9 * (Real.sqrt 3 / 2)) * (3 : ℝ) ^ (((j + 1 : ℕ) : ℝ) / 6) * Real.sqrt (absNorm (span {b})) *
          (9 * (Real.sqrt 3 / 2)) := by
          field_simp

end Eis

end

#print axioms Eis.conj_gaussP_one_one
#print axioms Eis.norm_gaussP_two
#print axioms Eis.norm_rhoM_mul_prime
#print axioms Eis.absNorm_span_lam
#print axioms Eis.not_dvd_unit_mul_lam_pow
#print axioms Eis.exists_unit_lam_pow_primary
#print axioms Eis.rhoM_supp_norm
#print axioms Eis.coprime_three_of_primary
#print axioms Eis.thetaSupp_tauTh_of_lam
