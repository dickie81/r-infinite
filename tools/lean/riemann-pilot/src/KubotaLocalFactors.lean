import EisensteinRowTwist

/-! # The local factors of the cusp expansions (round 366)

S5f-3a, the first part of round 360's S5f-3. The companion paper's Appendix A.2 expands the twist
`χ_p^j` at a prime in additive characters, with
"`C_{p,j}(h_p)&:=\frac1{\NK(p)}\sum_{y\bmod p}\chi_p^j(y)e(-h_py/p).`" (its (A.3)), evaluates these
coefficients (its (A.5)), and after the change of cusp sums them, against the multiplier and the phase,
into the local factors `B_{p,j}` of its (6.5) (its (A.12)). This file proves (A.5) and (A.12) at every
prime `P` prime to `6`, with round 363's `fCoef` and round 341's `chiPow` and `Bloc`, and the
arithmetic of its (A.11).

* **Gauss sums at a prime** (`chiPow_eq`, `chiR_pow_ne_one`, `sym6_Pr`, **`gamI_Pr`**,
  **`sum_chiR_pow_psi`**, `sum_psi_ne_zero`): `χ_P^j(z) = (χ^j)(z mod π)` for every `j`; `χ^j ≠ 1` for
  `j ≢ 0 (mod 6)`; `γ_k(P) = g(χ_P^k, ψ_P)/N(P)^{1/2}`; `Σ_y(χ^k)(y)ψ(ay)` is `(χ_P(a)^k)⁻¹N(P)^{1/2}γ_k(P)`
  for `a ∉ P` and `0` for `a ∈ P`; `Σ_{y ≠ 0}ψ(ay) = N(P)·1_{a∈P} − 1`.
* **(A.5)** (`locCoef`, **`locCoef_eq`**, **`locCoef_eq_zero_exp`**): `C_{P,j}(h)` is
  `N(P)^{−1/2}χ_P(−1)^jγ_j(P)(χ_P(h)^j)⁻¹` for `j ≢ 0` and `h ∉ P`, `0` for `j ≢ 0` and `h ∈ P`, `−N(P)⁻¹`
  for `j ≡ 0` and `h ∉ P`, and `1 − N(P)⁻¹` for `j ≡ 0` and `h ∈ P`.
* **(A.12)** (`ωloc`, **`local_transform`**, `norm_ωloc`): for `s, e ∉ P`,
  `Σ_{h ≢ 0}C_{P,j}(h)·χ_P(sh)^{−2}·ψ_P(ex·h⁻¹) = χ_P(s)^{−2}ω_{P,j}B_{P,j}(x)` with `|ω_{P,j}| = 1`, in the
  three cases `j ≡ 4`, `j ≡ 0` and the rest, through the substitution `y = h⁻¹` (`sum_erase_inv`).
* **The additive Chinese remainder theorem** (`ψc_crt`, **`ψc_prod_crt`**): `ψ_{qr}(x) = ψ_q(xu)ψ_r(xv)`
  for `ur + vq = 1`; for `c` prime to every `P ∈ A`, `ψ_{c∏_{P∈A}π_P}(x) = ψ_c(xu)·∏_Pψ_{π_P}(xv_P)` with
  `v_P ∉ P`.
* **The cusp phase** (`ebr_cusp_phase`): `ĕ(σm·(−σδ′/σc)/9) = ψ_{λ³c}(−mδ′)`, the paper's `ĕ(−δ′ℓ/c)` at
  the index `m = λ⁴ℓ`.
-/

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-- The local Fourier coefficient `C_{P,j}(h) = N(P)⁻¹Σ_{y mod π}χ_P^j(y)e(−hy/π)` (the companion
paper's (A.3)): round 363's `fCoef` of round 341's `chiPow`. -/
def locCoef (P : Pr) (j : ℕ) (h : 𝓞 K) : ℂ := fCoef (πP P) (chiPow P.1 j) h

/-- The sextic character modulo `P`, on the residue field of its primary generator. -/
abbrev chiR (P : Pr) : MulChar (𝓞 K ⧸ span {πP P}) ℂ := chi6 (span {πP P}) (h6Pr P)

/-- The trace character modulo `P`. -/
abbrev psiR (P : Pr) : AddChar (𝓞 K ⧸ span {πP P}) ℂ := ψQ (πP P) (ne_zero_of_maximal (πP P))

theorem mkP_eq_zero_iff (P : Pr) (z : 𝓞 K) :
    Ideal.Quotient.mk (span {πP P}) z = 0 ↔ z ∈ P.1 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, (πP_spec P).2]

/-- `χ_P^j(z) = (χ^j)(z mod π)`, for every `j`, with the zero extension. -/
theorem chiPow_eq (P : Pr) (j : ℕ) (z : 𝓞 K) :
    chiPow P.1 j z = (chiR P ^ j) (Ideal.Quotient.mk (span {πP P}) z) := by
  unfold chiPow
  by_cases hz : z ∈ P.1
  · rw [ite_eq_left hz, (mkP_eq_zero_iff P z).2 hz, MulChar.map_zero]
  · rw [ite_eq_right hz, chiP_eq_chiF]
    have hu : IsUnit (Ideal.Quotient.mk (span {πP P}) z) :=
      isUnit_iff_ne_zero.2 fun h0 => hz ((mkP_eq_zero_iff P z).1 h0)
    rw [← hu.unit_spec, MulChar.pow_apply_coe]

theorem chiP_eq_chiR (P : Pr) (z : 𝓞 K) :
    chiP P.1 z = chiR P (Ideal.Quotient.mk (span {πP P}) z) := chiP_eq_chiF P z

theorem chiR_pow_mod (P : Pr) (j : ℕ) : chiR P ^ j = chiR P ^ (j % 6) := by
  conv_lhs => rw [← Nat.div_add_mod j 6, pow_add, pow_mul, chi6_pow_six, one_pow, one_mul]

theorem chiR_pow_ne_one (P : Pr) {j : ℕ} (hj : j % 6 ≠ 0) : chiR P ^ j ≠ 1 := by
  rw [chiR_pow_mod]
  have h6 := chi6_pow_six (span {πP P}) (h6Pr P)
  have hlt : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have h123 : ∀ k ∈ ({1, 2, 3} : Finset ℕ), chiR P ^ k ≠ 1 := fun k hk =>
    chi6_pow_ne_one (span {πP P}) (h6Pr P) hk
  interval_cases h : j % 6
  · exact absurd rfl hj
  · exact h123 1 (by simp)
  · exact h123 2 (by simp)
  · exact h123 3 (by simp)
  · intro h4
    apply h123 2 (by simp)
    rw [← h6, show (6 : ℕ) = 4 + 2 by norm_num, pow_add, h4, one_mul]
  · intro h5
    apply h123 1 (by simp)
    rw [pow_one]
    calc chiR P = chiR P ^ 5 * chiR P := by rw [h5, one_mul]
      _ = 1 := by rw [← pow_succ]; exact h6

/-- `(a/P)₆ = χ_P(a)` at a prime. -/
theorem sym6_Pr (P : Pr) (z : 𝓞 K) : sym6 z P.1 = chiP P.1 z := by
  have := P.2.1
  have hP0 : P.1 ≠ ⊥ := ne_bot P.1
  have hirr : Irreducible P.1 := (Ideal.prime_of_isPrime hP0 P.2.1.isPrime).irreducible
  rw [sym6, normalizedFactors_irreducible hirr, normalize_eq]
  simp

theorem absNorm_πP (P : Pr) : absNorm (span {πP P}) = absNorm P.1 := by rw [(πP_spec P).2]

theorem norm_σO_πP (P : Pr) : ‖σO (πP P)‖ = Real.sqrt (absNorm P.1) := by
  rw [← absNorm_πP, ← sq_norm_σO, Real.sqrt_sq (norm_nonneg _)]

theorem sqrtN_pos (P : Pr) : 0 < Real.sqrt (absNorm P.1) := by
  rw [← norm_σO_πP]
  exact norm_pos_iff.2 fun h => ne_zero_of_maximal (πP P) (σO_injective (h.trans (map_zero σO).symm))

/-- `γ_k(P) = g(χ_P^k, ψ_P)/N(P)^{1/2}` for `k ≢ 0 (mod 6)`. -/
theorem gamI_Pr (P : Pr) {k : ℕ} (hk : k % 6 ≠ 0) :
    gamI k P.1 = gaussSum (chiR P ^ k) (psiR P) / ((Real.sqrt (absNorm P.1) : ℝ) : ℂ) := by
  have hne := chiR_pow_ne_one P hk
  have hk0 : k ≠ 0 := by rintro rfl; exact hk rfl
  unfold gamI
  rw [show pgen P.1 = πP P from rfl, norm_σO_πP]
  congr 1
  unfold gaussTr
  rw [finsum_eq_sum_of_fintype]
  have e2 : ∀ r : 𝓞 K ⧸ span {πP P}, sym6 (repQ (πP P) r) P.1 ^ k *
      ψc (πP P) (repQ (πP P) r * 1) = (chiR P ^ k) r * ψc (πP P) (repQ (πP P) r * 1) := by
    intro r
    rw [sym6_Pr]
    congr 1
    have hc := chiPow_eq P k (repQ (πP P) r)
    rw [repQ_mk] at hc
    rw [← hc]
    unfold chiPow
    split_ifs with hm
    · rw [chiP_eq_zero_of_mem hm, zero_pow hk0]
    · rfl
  rw [Finset.sum_congr rfl fun r _ => e2 r, inner_sum_prime (πP P) _ hne 1, map_one,
    MulChar.map_one, one_mul]

open Classical in
/-- **The twisted Gauss sums at a prime**: `Σ_{y mod π}(χ^k)(y)ψ(ay) = 0` for `a ∈ P`, and
`(χ_P(a)^k)⁻¹·N(P)^{1/2}·γ_k(P)` for `a ∉ P`, when `k ≢ 0 (mod 6)`. -/
theorem sum_chiR_pow_psi (P : Pr) {k : ℕ} (hk : k % 6 ≠ 0) (a : 𝓞 K) :
    ∑ y, (chiR P ^ k) y * psiR P (Ideal.Quotient.mk (span {πP P}) a * y) =
      if a ∈ P.1 then 0
      else (chiP P.1 a ^ k)⁻¹ * ((Real.sqrt (absNorm P.1) : ℝ) : ℂ) * gamI k P.1 := by
  have hne := chiR_pow_ne_one P hk
  have e1 : ∀ y, psiR P (Ideal.Quotient.mk (span {πP P}) a * y) =
      ψc (πP P) (repQ (πP P) y * a) := by
    intro y
    rw [← ψQ_mk (πP P) (ne_zero_of_maximal (πP P)), map_mul (Ideal.Quotient.mk (span {πP P})),
      repQ_mk, mul_comm]
  simp_rw [e1]
  rw [inner_sum_prime (πP P) _ hne a]
  have hs : ((Real.sqrt (absNorm P.1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sqrtN_pos P).ne'
  have hg : gaussSum (chiR P ^ k) (psiR P) =
      ((Real.sqrt (absNorm P.1) : ℝ) : ℂ) * gamI k P.1 := by
    rw [gamI_Pr P hk, mul_div_cancel₀ _ hs]
  rw [hg]
  by_cases ha : a ∈ P.1
  · rw [ite_eq_left ha, (mkP_eq_zero_iff P a).2 ha, MulChar.map_zero, zero_mul]
  · rw [ite_eq_right ha, MulChar.inv_apply_eq_inv', ← chiPow_eq, ← mul_assoc]
    unfold chiPow
    rw [ite_eq_right ha]

open Classical in
/-- **The additive sums at a prime**: `Σ_{y ≠ 0}ψ(ay) = N(P) − 1` for `a ∈ P`, and `−1` otherwise. -/
theorem sum_psi_ne_zero (P : Pr) (a : 𝓞 K) :
    ∑ y ∈ (Finset.univ : Finset (𝓞 K ⧸ span {πP P})).erase 0,
        psiR P (Ideal.Quotient.mk (span {πP P}) a * y) =
      if a ∈ P.1 then (absNorm P.1 : ℂ) - 1 else -1 := by
  classical
  have hsum := AddChar.sum_mulShift (Ideal.Quotient.mk (span {πP P}) a)
    (ψQ_isPrimitive (πP P))
  rw [card_quot, absNorm_πP] at hsum
  have e : ∑ y ∈ (Finset.univ : Finset (𝓞 K ⧸ span {πP P})).erase 0,
      psiR P (Ideal.Quotient.mk (span {πP P}) a * y) + 1 =
        ∑ y, psiR P (y * Ideal.Quotient.mk (span {πP P}) a) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0), zero_mul, AddChar.map_zero_eq_one]
    congr 1
    exact Finset.sum_congr rfl fun y _ => by rw [mul_comm]
  rw [eq_sub_of_add_eq e, hsum, mkP_eq_zero_iff]
  split_ifs <;> push_cast <;> ring

open Classical in
/-- **The local Fourier coefficients** (the companion paper's (A.5)), for `j ≢ 0 (mod 6)`:
`C_{P,j}(h) = N(P)^{−1/2}χ_P(−1)^jγ_j(P)(χ_P(h)^j)⁻¹` for `h ∉ P`, and `0` for `h ∈ P`. -/
theorem locCoef_eq (P : Pr) {j : ℕ} (hj : j % 6 ≠ 0) (h : 𝓞 K) :
    locCoef P j h = if h ∈ P.1 then 0 else
      ((Real.sqrt (absNorm P.1) : ℝ) : ℂ)⁻¹ * chiP P.1 (-1) ^ j * gamI j P.1 * (chiP P.1 h ^ j)⁻¹ := by
  have := finite_quot (πP P) (ne_zero_of_maximal (πP P))
  unfold locCoef fCoef
  rw [finsum_eq_sum_of_fintype, absNorm_πP]
  have e : ∀ y : 𝓞 K ⧸ span {πP P}, chiPow P.1 j (repQ (πP P) y) * ψc (πP P) (-(h * repQ (πP P) y)) =
      (chiR P ^ j) y * psiR P (Ideal.Quotient.mk (span {πP P}) (-h) * y) := by
    intro y
    rw [chiPow_eq, repQ_mk, ← ψQ_mk (πP P) (ne_zero_of_maximal (πP P)),
      map_neg (Ideal.Quotient.mk (span {πP P})), map_mul (Ideal.Quotient.mk (span {πP P})), repQ_mk,
      map_neg (Ideal.Quotient.mk (span {πP P})), neg_mul]
  rw [Finset.sum_congr rfl fun y _ => e y, sum_chiR_pow_psi P hj]
  have hneg : -h ∈ P.1 ↔ h ∈ P.1 := P.1.neg_mem_iff
  by_cases hh : h ∈ P.1
  · rw [ite_eq_left (hneg.2 hh), ite_eq_left hh, mul_zero]
  · rw [ite_eq_right (fun h' => hh (hneg.1 h')), ite_eq_right hh]
    have hN : (absNorm P.1 : ℂ) = ((Real.sqrt (absNorm P.1) : ℝ) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    have hs : ((Real.sqrt (absNorm P.1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sqrtN_pos P).ne'
    have hm1 : chiP P.1 (-1) ^ 2 = 1 := by
      rw [sq, ← chiP_mul, neg_one_mul, neg_neg, chiP_one P.2]
    have hneg' : chiP P.1 (-h) = chiP P.1 (-1) * chiP P.1 h := by
      rw [← chiP_mul, neg_one_mul]
    have hc0 : chiP P.1 h ≠ 0 := by
      intro h0
      have h6 := chiP_pow_six P.2.1 P.2.2 h
      rw [ite_eq_right hh, h0] at h6
      norm_num at h6
    have hm0 : chiP P.1 (-1) ≠ 0 := by
      intro h0; rw [h0] at hm1; norm_num at hm1
    have hm1' : chiP P.1 (-1) ^ j * chiP P.1 (-1) ^ j = 1 := by
      rw [← mul_pow, ← sq, hm1, one_pow]
    have hcinv : (chiP P.1 (-1) ^ j)⁻¹ = chiP P.1 (-1) ^ j := inv_eq_of_mul_eq_one_right hm1'
    rw [hneg', mul_pow, mul_inv, hcinv, hN]
    have hx0 : chiP P.1 h ^ j ≠ 0 := pow_ne_zero _ hc0
    field_simp

open Classical in
/-- `C_{P,j}(h) = −N(P)⁻¹` for `j ≡ 0 (mod 6)` and `h ∉ P`, and `1 − N(P)⁻¹` for `h ∈ P`. -/
theorem locCoef_eq_zero_exp (P : Pr) {j : ℕ} (hj : j % 6 = 0) (h : 𝓞 K) :
    locCoef P j h = if h ∈ P.1 then 1 - (absNorm P.1 : ℂ)⁻¹ else -(absNorm P.1 : ℂ)⁻¹ := by
  unfold locCoef fCoef
  rw [finsum_eq_sum_of_fintype, absNorm_πP]
  have h0 : chiPow P.1 j (repQ (πP P) 0) * ψc (πP P) (-(h * repQ (πP P) 0)) = 0 := by
    rw [chiPow_eq, repQ_mk, MulChar.map_zero, zero_mul]
  have e : ∀ y ∈ (Finset.univ : Finset (𝓞 K ⧸ span {πP P})).erase 0,
      chiPow P.1 j (repQ (πP P) y) * ψc (πP P) (-(h * repQ (πP P) y)) =
        psiR P (Ideal.Quotient.mk (span {πP P}) (-h) * y) := by
    intro y hy
    rw [chiPow_eq, repQ_mk, chiR_pow_mod, hj, pow_zero,
      MulChar.one_apply (isUnit_iff_ne_zero.2 (Finset.ne_of_mem_erase hy)), one_mul,
      ← ψQ_mk (πP P) (ne_zero_of_maximal (πP P)), map_neg (Ideal.Quotient.mk (span {πP P})),
      map_mul (Ideal.Quotient.mk (span {πP P})), repQ_mk, map_neg (Ideal.Quotient.mk (span {πP P})),
      neg_mul]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0), h0, add_zero, Finset.sum_congr rfl e,
    sum_psi_ne_zero]
  have hneg : -h ∈ P.1 ↔ h ∈ P.1 := P.1.neg_mem_iff
  have hN : (absNorm P.1 : ℂ) ≠ 0 := by
    rw [← absNorm_πP]; exact absNorm_span_ne_zero (ne_zero_of_maximal (πP P))
  by_cases hh : h ∈ P.1
  · rw [ite_eq_left (hneg.2 hh), ite_eq_left hh]
    field_simp
  · rw [ite_eq_right (fun h' => hh (hneg.1 h')), ite_eq_right hh]
    field_simp

theorem mulChar_inv {F : Type*} [Field F] (χ : MulChar F ℂ) {h : F} (hh : h ≠ 0) :
    χ h⁻¹ = (χ h)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← map_mul χ, mul_inv_cancel₀ hh, MulChar.map_one]

/-- The sum over the nonzero residues is invariant under `h ↦ h⁻¹`. -/
theorem sum_erase_inv {F : Type*} [Field F] [Fintype F] [DecidableEq F] (f : F → ℂ) :
    ∑ h ∈ (Finset.univ : Finset F).erase 0, f h⁻¹ = ∑ y ∈ (Finset.univ : Finset F).erase 0, f y := by
  have h1 := Equiv.sum_comp (Equiv.inv F) f
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0), ← Finset.sum_erase_add _ _ (Finset.mem_univ 0)]
    at h1
  simp only [Equiv.inv_apply, inv_zero] at h1
  exact add_right_cancel h1

theorem pow_eq_pow_of_six {u : ℂ} (hu : u ^ 6 = 1) {a b : ℕ} (hab : a % 6 = b % 6) : u ^ a = u ^ b := by
  rw [← Nat.div_add_mod a 6, ← Nat.div_add_mod b 6, pow_add, pow_add, pow_mul, pow_mul, hu, one_pow,
    one_pow, hab]

theorem chiR_pow_six_of_ne_zero (P : Pr) {h : 𝓞 K ⧸ span {πP P}} (hh : h ≠ 0) : chiR P h ^ 6 = 1 := by
  rw [← (isUnit_iff_ne_zero.2 hh).unit_spec, ← MulChar.pow_apply_coe, chi6_pow_six,
    MulChar.one_apply_coe]

theorem chiR_ne_zero (P : Pr) {h : 𝓞 K ⧸ span {πP P}} (hh : h ≠ 0) : chiR P h ≠ 0 := by
  intro h0
  have := chiR_pow_six_of_ne_zero P hh
  rw [h0] at this
  norm_num at this

theorem repQ_not_mem (P : Pr) {h : 𝓞 K ⧸ span {πP P}} (hh : h ≠ 0) : repQ (πP P) h ∉ P.1 := by
  intro hm
  apply hh
  rw [← repQ_mk (πP P) h]
  exact (mkP_eq_zero_iff P _).2 hm

theorem chiP_repQ (P : Pr) (h : 𝓞 K ⧸ span {πP P}) : chiP P.1 (repQ (πP P) h) = chiR P h := by
  rw [chiP_eq_chiR, repQ_mk]

theorem chiP_ne_zero_of_not_mem (P : Pr) {a : 𝓞 K} (ha : a ∉ P.1) : chiP P.1 a ≠ 0 := by
  rw [chiP_eq_chiR]
  exact chiR_ne_zero P fun h0 => ha ((mkP_eq_zero_iff P a).1 h0)

theorem chiP_pow_six_of_not_mem (P : Pr) {a : 𝓞 K} (ha : a ∉ P.1) : chiP P.1 a ^ 6 = 1 := by
  have := chiP_pow_six P.2.1 P.2.2 a
  rwa [ite_eq_right ha] at this

theorem mul_mem_iff_right (P : Pr) {e x : 𝓞 K} (he : e ∉ P.1) : e * x ∈ P.1 ↔ x ∈ P.1 :=
  ⟨fun h => (P.2.1.isPrime.mem_or_mem h).resolve_left he, fun h => P.1.mul_mem_left _ h⟩

open Classical in
/-- The unimodular factor `ω_{P,j}` of the companion paper's (A.12), at `ε = e`. -/
def ωloc (P : Pr) (j : ℕ) (e : 𝓞 K) : ℂ :=
  if j % 6 = 4 then chiP P.1 (-1) ^ j * gamI j P.1
  else if j % 6 = 0 then -(gamI 2 P.1 * (chiP P.1 e ^ 2)⁻¹)
  else chiP P.1 (-1) ^ j * gamI j P.1 * gamI (j + 2) P.1 * (chiP P.1 e ^ (j + 2))⁻¹

theorem chiR_pow_inv (P : Pr) (k : ℕ) {h : 𝓞 K ⧸ span {πP P}} (hh : h ≠ 0) :
    (chiR P ^ k) h⁻¹ = (chiR P h)⁻¹ ^ k := by
  have hu : IsUnit h⁻¹ := isUnit_iff_ne_zero.2 (inv_ne_zero hh)
  rw [← hu.unit_spec, MulChar.pow_apply_coe, hu.unit_spec, mulChar_inv _ hh]

open Classical in
/-- **The local transformation** (the companion paper's (A.12)): for `s, e ∉ P`,
`Σ_{h ≠ 0} C_{P,j}(h)·χ_P(sh)^{−2}·e(ex/(hπ)) = χ_P(s)^{−2}·ω_{P,j}·B_{P,j}(x)`. -/
theorem local_transform (P : Pr) (j : ℕ) {s e : 𝓞 K} (hs : s ∉ P.1) (he : e ∉ P.1) (x : 𝓞 K) :
    ∑ h ∈ (Finset.univ : Finset (𝓞 K ⧸ span {πP P})).erase 0,
        locCoef P j (repQ (πP P) h) * (chiP P.1 (s * repQ (πP P) h) ^ 2)⁻¹ *
          psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * h⁻¹) =
      (chiP P.1 s ^ 2)⁻¹ * ωloc P j e * Bloc P.1 j x := by
  have hS := chiP_ne_zero_of_not_mem P hs
  have hE := chiP_ne_zero_of_not_mem P he
  have hsN : ((Real.sqrt (absNorm P.1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sqrtN_pos P).ne'
  have hN : (absNorm P.1 : ℂ) = ((Real.sqrt (absNorm P.1) : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
  have hex := mul_mem_iff_right P he (x := x)
  have hinv := sum_erase_inv fun y => psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * y)
  beta_reduce at hinv
  by_cases h4 : j % 6 = 4
  · -- `j ≡ 4`: the character `χ^{j+2}` is trivial
    have hj0 : j % 6 ≠ 0 := by omega
    have hterm : ∀ h ∈ (Finset.univ : Finset (𝓞 K ⧸ span {πP P})).erase 0,
        locCoef P j (repQ (πP P) h) * (chiP P.1 (s * repQ (πP P) h) ^ 2)⁻¹ *
          psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * h⁻¹) =
          ((Real.sqrt (absNorm P.1) : ℝ) : ℂ)⁻¹ * chiP P.1 (-1) ^ j * gamI j P.1 *
            (chiP P.1 s ^ 2)⁻¹ * psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * h⁻¹) := by
      intro h hh
      have hh0 := Finset.ne_of_mem_erase hh
      rw [locCoef_eq P hj0, ite_eq_right (repQ_not_mem P hh0), chiP_mul, chiP_repQ]
      have hX := chiR_ne_zero P hh0
      have h6 : chiR P h ^ (j + 2) = 1 := by
        rw [pow_eq_pow_of_six (chiR_pow_six_of_ne_zero P hh0) (show (j + 2) % 6 = 0 % 6 by omega),
          pow_zero]
      have e1 : (chiR P h ^ j)⁻¹ * ((chiP P.1 s * chiR P h) ^ 2)⁻¹ = (chiP P.1 s ^ 2)⁻¹ := by
        rw [mul_pow, mul_inv, ← mul_assoc, mul_comm (chiR P h ^ j)⁻¹, mul_assoc, ← mul_inv, ← pow_add,
          h6, inv_one, mul_one]
      calc ((Real.sqrt (absNorm P.1) : ℝ) : ℂ)⁻¹ * chiP P.1 (-1) ^ j * gamI j P.1 * (chiR P h ^ j)⁻¹ *
            ((chiP P.1 s * chiR P h) ^ 2)⁻¹ * psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * h⁻¹)
          = ((Real.sqrt (absNorm P.1) : ℝ) : ℂ)⁻¹ * chiP P.1 (-1) ^ j * gamI j P.1 *
            ((chiR P h ^ j)⁻¹ * ((chiP P.1 s * chiR P h) ^ 2)⁻¹) *
              psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * h⁻¹) := by ring
        _ = _ := by rw [e1]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hinv, sum_psi_ne_zero]
    unfold ωloc
    rw [ite_eq_left h4, Bloc_four h4 (Real.sqrt_pos.1 (sqrtN_pos P)) x]
    by_cases hx : x ∈ P.1
    · rw [ite_eq_left (hex.2 hx), ite_eq_left hx, hN]
      field_simp
      ring
    · rw [ite_eq_right (fun h' => hx (hex.1 h')), ite_eq_right hx]
      field_simp
      ring
  by_cases h0 : j % 6 = 0
  · -- `j ≡ 0`, an active prime: `C_{P,0}(h) = −N(P)⁻¹`
    have hterm : ∀ h ∈ (Finset.univ : Finset (𝓞 K ⧸ span {πP P})).erase 0,
        locCoef P j (repQ (πP P) h) * (chiP P.1 (s * repQ (πP P) h) ^ 2)⁻¹ *
          psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * h⁻¹) =
          -(absNorm P.1 : ℂ)⁻¹ * (chiP P.1 s ^ 2)⁻¹ *
            ((chiR P ^ 2) h⁻¹ * psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * h⁻¹)) := by
      intro h hh
      have hh0 := Finset.ne_of_mem_erase hh
      rw [locCoef_eq_zero_exp P h0, ite_eq_right (repQ_not_mem P hh0), chiP_mul, chiP_repQ,
        chiR_pow_inv P 2 hh0]
      ring
    have hsum := sum_erase_inv fun y =>
      (chiR P ^ 2) y * psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * y)
    beta_reduce at hsum
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum,
      Finset.sum_erase _ (by rw [MulChar.map_zero, zero_mul]), sum_chiR_pow_psi P (by norm_num)]
    unfold ωloc Bloc
    rw [ite_eq_right h4, ite_eq_left h0, ite_eq_right h4, ite_eq_left h0]
    unfold chiPow
    by_cases hx : x ∈ P.1
    · rw [ite_eq_left (hex.2 hx), ite_eq_left hx]
      ring
    · rw [ite_eq_right (fun h' => hx (hex.1 h')), ite_eq_right hx]
      have hX := chiP_ne_zero_of_not_mem P hx
      have hX6 := chiP_pow_six_of_not_mem P hx
      have hX4 : (chiP P.1 x ^ 2)⁻¹ = chiP P.1 x ^ 4 :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hX6)
      rw [chiP_mul, mul_pow, mul_inv, hX4, hN]
      field_simp
  · -- `j ≢ 0, 4`: the character `χ^{j+2}` is nontrivial
    have hk : (j + 2) % 6 ≠ 0 := by omega
    have hterm : ∀ h ∈ (Finset.univ : Finset (𝓞 K ⧸ span {πP P})).erase 0,
        locCoef P j (repQ (πP P) h) * (chiP P.1 (s * repQ (πP P) h) ^ 2)⁻¹ *
          psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * h⁻¹) =
          ((Real.sqrt (absNorm P.1) : ℝ) : ℂ)⁻¹ * chiP P.1 (-1) ^ j * gamI j P.1 *
            (chiP P.1 s ^ 2)⁻¹ *
              ((chiR P ^ (j + 2)) h⁻¹ * psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * h⁻¹)) := by
      intro h hh
      have hh0 := Finset.ne_of_mem_erase hh
      have hX := chiR_ne_zero P hh0
      rw [locCoef_eq P h0, ite_eq_right (repQ_not_mem P hh0), chiP_mul, chiP_repQ,
        chiR_pow_inv P (j + 2) hh0, inv_pow]
      field_simp
      ring
    have hsum := sum_erase_inv fun y =>
      (chiR P ^ (j + 2)) y * psiR P (Ideal.Quotient.mk (span {πP P}) (e * x) * y)
    beta_reduce at hsum
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum,
      Finset.sum_erase _ (by rw [MulChar.map_zero, zero_mul]), sum_chiR_pow_psi P hk]
    unfold ωloc Bloc
    rw [ite_eq_right h4, ite_eq_right h0, ite_eq_right h4, ite_eq_right h0]
    unfold chiPow
    by_cases hx : x ∈ P.1
    · rw [ite_eq_left (hex.2 hx), ite_eq_left hx]
      ring
    · rw [ite_eq_right (fun h' => hx (hex.1 h')), ite_eq_right hx]
      have hX := chiP_ne_zero_of_not_mem P hx
      have hX6 := chiP_pow_six_of_not_mem P hx
      have hXm : (chiP P.1 x ^ (j + 2))⁻¹ = chiP P.1 x ^ ((12 - (j % 6 + 2)) % 6) := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← pow_add, pow_eq_pow_of_six hX6 (show (j + 2 + (12 - (j % 6 + 2)) % 6) % 6 = 0 % 6 by omega),
          pow_zero]
      rw [chiP_mul, mul_pow, mul_inv, hXm]
      field_simp

theorem gamI_eq_gamN (P : Pr) {k : ℕ} (hk : k % 6 ≠ 0) : gamI k P.1 = gamN (πP P) (chiR P ^ k) := by
  rw [gamI_Pr P hk, gamN, norm_σO_πP]
  rfl

/-- `|γ_k(P)| = 1` for `k ≢ 0 (mod 6)`. -/
theorem norm_gamI_Pr (P : Pr) {k : ℕ} (hk : k % 6 ≠ 0) : ‖gamI k P.1‖ = 1 := by
  rw [gamI_eq_gamN P hk]; exact norm_gamN (πP P) (chiR_pow_ne_one P hk)

theorem norm_chiP_of_not_mem (P : Pr) {a : 𝓞 K} (ha : a ∉ P.1) : ‖chiP P.1 a‖ = 1 := by
  have h := congrArg norm (chiP_pow_six_of_not_mem P ha)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h

theorem neg_one_not_mem (P : Pr) : (-1 : 𝓞 K) ∉ P.1 := fun h =>
  P.2.1.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.1.neg_mem h))

/-- **`|ω_{P,j}| = 1`** for `e ∉ P`. -/
theorem norm_ωloc (P : Pr) (j : ℕ) {e : 𝓞 K} (he : e ∉ P.1) : ‖ωloc P j e‖ = 1 := by
  have hm := norm_chiP_of_not_mem P (neg_one_not_mem P)
  have hE := norm_chiP_of_not_mem P he
  unfold ωloc
  split_ifs with h4 h0
  · rw [norm_mul, norm_pow, hm, one_pow, one_mul, norm_gamI_Pr P (by omega)]
  · rw [norm_neg, norm_mul, norm_inv, norm_pow, hE, one_pow, inv_one, mul_one,
      norm_gamI_Pr P (by norm_num)]
  · rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_pow, norm_pow, hm, hE, one_pow, one_pow, inv_one,
      norm_gamI_Pr P h0, norm_gamI_Pr P (by omega)]
    norm_num

/-- The scalar `1 − N(P)⁻¹` of an inactive prime has modulus at most `1`. -/
theorem norm_locCoef_zero_le (P : Pr) {j : ℕ} (hj : j % 6 = 0) : ‖locCoef P j 0‖ ≤ 1 := by
  rw [locCoef_eq_zero_exp P hj, ite_eq_left P.1.zero_mem]
  have hN : (1 : ℝ) ≤ absNorm P.1 := by
    have := Real.sqrt_pos.1 (sqrtN_pos P)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by exact_mod_cast this.ne')
  have e : (1 : ℂ) - (absNorm P.1 : ℂ)⁻¹ = ((1 - (absNorm P.1 : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
    have := inv_le_one_of_one_le₀ hN; linarith)]
  have := inv_nonneg.2 (zero_le_one.trans hN)
  linarith

/-! ### The additive Chinese remainder theorem -/

/-- **`ψ_{qr}(x) = ψ_q(xu)ψ_r(xv)`** for `ur + vq = 1`. -/
theorem ψc_crt {q r u v : 𝓞 K} (hq : q ≠ 0) (hr : r ≠ 0) (h : u * r + v * q = 1) (x : 𝓞 K) :
    ψc (q * r) x = ψc q (x * u) * ψc r (x * v) := by
  have e : x = r * (x * u) + q * (x * v) := by linear_combination -x * h
  conv_lhs => rw [e]
  rw [ψc_add, ψc_mul_right q r _ hr, mul_comm q r, ψc_mul_right r q _ hq]

/-- `x` is prime to `π_P` iff `x ∉ P`. -/
theorem isCoprime_πP_iff (P : Pr) (x : 𝓞 K) : IsCoprime x (πP P) ↔ x ∉ P.1 := by
  rw [← Ideal.isCoprime_span_singleton_iff, (πP_spec P).2, Ideal.isCoprime_iff_sup_eq]
  constructor
  · intro h hx
    apply P.2.1.ne_top
    rw [← h, sup_eq_right.2 ((Ideal.span_singleton_le_iff_mem _).2 hx)]
  · intro hx
    have hlt : P.1 < span {x} ⊔ P.1 := lt_of_le_of_ne le_sup_right fun h =>
      hx (by rw [h]; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))
    exact P.2.1.out.2 _ hlt

theorem πP_mem_iff {P Q : Pr} : πP Q ∈ P.1 ↔ Q = P := by
  constructor
  · intro h
    have hle : Q.1 ≤ P.1 := by rw [← (πP_spec Q).2, Ideal.span_singleton_le_iff_mem]; exact h
    exact Subtype.ext (Q.2.1.eq_of_le P.2.1.ne_top hle)
  · rintro rfl; rw [← (πP_spec Q).2]; exact Ideal.mem_span_singleton_self _

theorem prod_πP_not_mem {P : Pr} {A : Finset Pr} (hP : P ∉ A) : ∏ Q ∈ A, πP Q ∉ P.1 := by
  have := P.2.1.isPrime
  intro h
  obtain ⟨Q, hQ, hQP⟩ := Ideal.IsPrime.prod_mem_iff.1 h
  exact hP (πP_mem_iff.1 hQP ▸ hQ)

theorem prod_πP_mem {P : Pr} {A : Finset Pr} (hP : P ∈ A) : ∏ Q ∈ A, πP Q ∈ P.1 := by
  have := P.2.1.isPrime
  exact Ideal.IsPrime.prod_mem_iff.2 ⟨P, hP, πP_mem_iff.2 rfl⟩

/-- **The Chinese remainder theorem over a set of primes**: for `c ≠ 0` prime to every `P ∈ A`, there
are `u` and `v_P ∉ P` with `ψ_{c∏π_P}(x) = ψ_c(xu)·∏_P ψ_{π_P}(xv_P)` for every `x`. -/
theorem ψc_prod_crt (A : Finset Pr) {c : 𝓞 K} (hc : c ≠ 0) (hcA : ∀ P ∈ A, c ∉ P.1) :
    ∃ (u : 𝓞 K) (v : Pr → 𝓞 K), (∀ P ∈ A, v P ∉ P.1) ∧
      ∀ x, ψc (c * ∏ P ∈ A, πP P) x = ψc c (x * u) * ∏ P ∈ A, ψc (πP P) (x * v P) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ => 0, by simp, fun x => ?_⟩
    simp
  | insert P A hP ih =>
    obtain ⟨u, v, hv, hx⟩ := ih fun Q hQ => hcA Q (Finset.mem_insert_of_mem hQ)
    have hPm := P.2.1.isPrime
    have hxP : c * ∏ Q ∈ A, πP Q ∉ P.1 := fun h =>
      (hPm.mem_or_mem h).elim (hcA P (Finset.mem_insert_self P A)) (prod_πP_not_mem hP)
    obtain ⟨a, b, hab⟩ := (isCoprime_πP_iff P _).2 hxP
    have hA0 : c * ∏ Q ∈ A, πP Q ≠ 0 := mul_ne_zero hc (prod_πP_ne_zero A)
    refine ⟨b * u, fun Q => if Q = P then a else b * v Q, ?_, fun x => ?_⟩
    · intro Q hQ
      dsimp only
      by_cases hQP : Q = P
      · rw [ite_eq_left hQP]
        subst hQP
        intro ha
        apply Q.2.1.ne_top
        rw [Ideal.eq_top_iff_one, ← hab]
        exact Q.1.add_mem (Q.1.mul_mem_right _ ha) (Q.1.mul_mem_left _ (πP_mem_iff.2 rfl))
      · rw [ite_eq_right hQP]
        have hQA : Q ∈ A := (Finset.mem_insert.1 hQ).resolve_left hQP
        have hQm := Q.2.1.isPrime
        intro hbv
        rcases hQm.mem_or_mem hbv with hb | hb
        · apply Q.2.1.ne_top
          rw [Ideal.eq_top_iff_one, ← hab]
          exact Q.1.add_mem (Q.1.mul_mem_left _ (Q.1.mul_mem_left _ (prod_πP_mem hQA)))
            (Q.1.mul_mem_right _ hb)
        · exact hv Q hQA hb
    · have hP0 := ne_zero_of_maximal (πP P)
      dsimp only
      rw [Finset.prod_insert hP, show c * (πP P * ∏ Q ∈ A, πP Q) = (c * ∏ Q ∈ A, πP Q) * πP P by ring,
        ψc_crt hA0 hP0 (show b * πP P + a * (c * ∏ Q ∈ A, πP Q) = 1 by linear_combination hab),
        hx, Finset.prod_insert hP, ite_eq_left rfl]
      have e : ∏ Q ∈ A, ψc (πP Q) (x * b * v Q) =
          ∏ Q ∈ A, ψc (πP Q) (x * (if Q = P then a else b * v Q)) := by
        refine Finset.prod_congr rfl fun Q hQ => ?_
        rw [ite_eq_right (fun (h : Q = P) => hP (h ▸ hQ)), mul_assoc]
      rw [e, show x * b * u = x * (b * u) by ring]
      ring

/-- **The cusp phase**: `ĕ(σm·(−σδ′/σc)/9) = ψ_{λ³c}(−mδ′)`, the paper's `ĕ(−δ′ℓ/c)` at `ℓ = m/λ⁴`. -/
theorem ebr_cusp_phase (m δ' c : 𝓞 K) :
    ebr (σO m * (-σO δ' / σO c) / 9) = ψc (δ3 ^ 3 * c) (-(m * δ')) := by
  unfold ebr ψc trPhase
  rw [Real.fourierChar_apply]
  congr 1
  have h4 : σO δ3 ^ 4 = 9 := by
    have : σO δ3 ^ 2 = -3 := by rw [← map_pow, δ3_sq, map_neg, map_ofNat]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, this]; norm_num
  have hd := σO_δ3_ne_zero
  have e : 2 * (σO m * (-σO δ' / σO c) / 9) = 2 * σO (-(m * δ')) / σO (δ3 * (δ3 ^ 3 * c)) := by
    simp only [map_mul, map_pow, map_neg]
    by_cases hc : σO c = 0
    · rw [hc]; simp
    · rw [← h4]; field_simp
  have e2 : (2 * (σO m * (-σO δ' / σO c) / 9)).re = 2 * (σO m * (-σO δ' / σO c) / 9).re := by
    simp [Complex.mul_re]
  rw [← e2, e]
  push_cast; ring

end Eis

end

#print axioms Eis.mkP_eq_zero_iff
#print axioms Eis.chiPow_eq
#print axioms Eis.chiP_eq_chiR
#print axioms Eis.chiR_pow_mod
#print axioms Eis.chiR_pow_ne_one
#print axioms Eis.sym6_Pr
#print axioms Eis.absNorm_πP
#print axioms Eis.norm_σO_πP
#print axioms Eis.sqrtN_pos
#print axioms Eis.gamI_Pr
#print axioms Eis.sum_chiR_pow_psi
#print axioms Eis.sum_psi_ne_zero
#print axioms Eis.locCoef_eq
#print axioms Eis.locCoef_eq_zero_exp
#print axioms Eis.mulChar_inv
#print axioms Eis.sum_erase_inv
#print axioms Eis.pow_eq_pow_of_six
#print axioms Eis.chiR_pow_six_of_ne_zero
#print axioms Eis.chiR_ne_zero
#print axioms Eis.repQ_not_mem
#print axioms Eis.chiP_repQ
#print axioms Eis.chiP_ne_zero_of_not_mem
#print axioms Eis.chiP_pow_six_of_not_mem
#print axioms Eis.mul_mem_iff_right
#print axioms Eis.chiR_pow_inv
#print axioms Eis.local_transform
#print axioms Eis.gamI_eq_gamN
#print axioms Eis.norm_gamI_Pr
#print axioms Eis.norm_chiP_of_not_mem
#print axioms Eis.neg_one_not_mem
#print axioms Eis.norm_ωloc
#print axioms Eis.norm_locCoef_zero_le
#print axioms Eis.ψc_crt
#print axioms Eis.isCoprime_πP_iff
#print axioms Eis.πP_mem_iff
#print axioms Eis.prod_πP_not_mem
#print axioms Eis.prod_πP_mem
#print axioms Eis.ψc_prod_crt
#print axioms Eis.ebr_cusp_phase
