import KubotaLocalFactors

/-! # The twisted theta function as grouped translates (round 367)

S5f-3b, the second part of round 360's S5f-3. The companion paper's Appendix A.2 writes the twisted theta
function as a sum of translates of `θ̄`, with
"`z_{\boldsymbol h}=\lambda^2\Bigl(h_0/L+\sum_{p\in\mathcal P}h_p/p\Bigr),`" and
"`c_{\mathrm F}(\boldsymbol h)=\widehat\phi(h_0)\prod_{p\in\mathcal P} C_{p,j_p}(h_p).`" (its (A.4)), and
groups the translates by their active primes `{p : h_p ≠ 0}`. This file proves (A.4) with that grouping,
for any twist `F = φ₀·∏_{P∈Ps}χ_P^{j_P}` with `φ₀` periodic modulo `L ≠ 0` and `φ₀(0) = 0`.

* **One prime** (`chiPow_periodic`, `locCoef_congr`, **`chiPow_expand`**): `χ_P^j(x) = Σ_{h ≢ 0}C_{P,j}(h)ψ_P(hx)
  + C_{P,j}(0)`, round 363's Fourier inversion with the zero residue split off.
* **The active sets** (**`prod_chiPow_expand`**): `∏_{P∈Ps}χ_P^{j_P}(x) = Σ_{A⊆Ps}∏_{P∈Ps∖A}C_{P,j_P}(0)·
  Σ_{(h_P)_{P∈A}, h_P ≢ 0}∏_{P∈A}C_{P,j_P}(h_P)ψ_P(h_Px)`, by Mathlib's `Finset.prod_add` and
  `Finset.prod_univ_sum`.
* **The translates** (`TrIdx`, `trShift`, `ebr_sum`, `ebr_trShift`, `trCoef_sum`, **`twisted_theta_groups`**):
  the index `(h₀, A, (h_P)_{P∈A})`, the shift `λ²(h₀/L + Σ_{P∈A}h_P/π_P)`, and
  `Σ_m F(m/λ)·conj τ(−m)·vK_{1/3}(4π|m|v/9)ĕ(mz/9) = Σ_{h₀}φ̂₀(h₀)Σ_{A⊆Ps}∏_{P∉A}C_{P,j_P}(0)·
  Σ_{(h_P)}∏_{P∈A}C_{P,j_P}(h_P)·θ̄(z + λ²(h₀/L + Σ_{P∈A}h_P/π_P), v)`, through round 363's
  `thSer_translates` for the whole family; the constant terms cancel since `F(0) = 0`.
* **The inactive primes** (`locCoef_zero_of_ne`, `prod_locCoef_zero_eq_zero`, `norm_prod_locCoef_zero_le`):
  `C_{P,j}(0) = 0` for `j ≢ 0`, so a group vanishes unless its active set contains every prime with
  `j_P ≢ 0`, and the scalar `∏_{P∉A}C_{P,j_P}(0)` has modulus at most `1`.
-/

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-- `χ_P^j` is periodic modulo `π_P`. -/
theorem chiPow_periodic (P : Pr) (j : ℕ) (z u : 𝓞 K) :
    chiPow P.1 j (z + πP P * u) = chiPow P.1 j z := by
  rw [chiPow_eq, chiPow_eq, map_add, map_mul,
    (mkP_eq_zero_iff P (πP P)).2 (πP_mem_iff.2 rfl), zero_mul, add_zero]

/-- `C_{P,j}(h)` depends only on `h mod π_P`. -/
theorem locCoef_congr (P : Pr) (j : ℕ) {h h' : 𝓞 K} (hh : h - h' ∈ P.1) :
    locCoef P j h = locCoef P j h' := by
  unfold locCoef fCoef
  congr 1
  refine finsum_congr fun y => ?_
  congr 1
  apply ψc_congr (πP P) (ne_zero_of_maximal (πP P))
  rw [Ideal.Quotient.eq, (πP_spec P).2]
  have : -(h * repQ (πP P) y) - -(h' * repQ (πP P) y) = -((h - h') * repQ (πP P) y) := by ring
  rw [this]
  exact P.1.neg_mem (P.1.mul_mem_right _ hh)

open Classical in
/-- **One factor of (A.4)**: `χ_P^j(x) = Σ_{h ≢ 0}C_{P,j}(h)ψ_P(hx) + C_{P,j}(0)`. -/
theorem chiPow_expand (P : Pr) (j : ℕ) (x : 𝓞 K) :
    chiPow P.1 j x = ∑ h ∈ (Finset.univ : Finset (𝓞 K ⧸ span {πP P})).erase 0,
      locCoef P j (repQ (πP P) h) * ψc (πP P) (repQ (πP P) h * x) + locCoef P j 0 := by
  have hinv := fourier_inv (πP P) (ne_zero_of_maximal (πP P)) (chiPow P.1 j) (chiPow_periodic P j) x
  rw [finsum_eq_sum_of_fintype] at hinv
  rw [← hinv, ← Finset.sum_erase_add _ _ (Finset.mem_univ 0)]
  congr 1
  have e1 : fCoef (πP P) (chiPow P.1 j) (repQ (πP P) 0) = locCoef P j 0 :=
    locCoef_congr P j (show repQ (πP P) 0 - 0 ∈ P.1 by
      rw [sub_zero, ← mkP_eq_zero_iff, repQ_mk])
  rw [e1, ψc_congr (πP P) (ne_zero_of_maximal (πP P))
    (show Ideal.Quotient.mk (span {πP P}) (repQ (πP P) 0 * x) = Ideal.Quotient.mk _ 0 by
      rw [map_mul, repQ_mk, zero_mul, map_zero]), ψc_zero, mul_one]

open Classical in
/-- **The product over the primes, expanded over the active sets**:
`∏_{P∈Ps}χ_P^{j_P}(x) = Σ_{A⊆Ps}∏_{P∉A}C_{P,j_P}(0)·Σ_{(h_P)_{P∈A}, h_P ≢ 0}∏_{P∈A}C_{P,j_P}(h_P)ψ_P(h_Px)`. -/
theorem prod_chiPow_expand (Ps : Finset Pr) (j : Pr → ℕ) (x : 𝓞 K) :
    ∏ P ∈ Ps, chiPow P.1 (j P) x =
      ∑ A ∈ Ps.powerset, (∏ P ∈ Ps \ A, locCoef P (j P) 0) *
        ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
          ∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P)) *
            ψc (πP P.1) (repQ (πP P.1) (h P) * x) := by
  classical
  simp_rw [chiPow_expand]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [mul_comm, ← Finset.prod_coe_sort A, Finset.prod_univ_sum]

theorem ebr_zero : ebr 0 = 1 := by simp [ebr]

theorem ebr_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) : ebr (∑ i ∈ s, f i) = ∏ i ∈ s, ebr (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ebr_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ebr_add, ih]

/-- The index of a translate in (A.4): a residue `h₀ mod L`, an active set `A`, and nonzero residues
`h_P mod π_P` at the primes of `A`. -/
abbrev TrIdx (L : 𝓞 K) : Type :=
  Σ p : (𝓞 K ⧸ span {L}) × Finset Pr, ((P : p.2) → 𝓞 K ⧸ span {πP P.1})

/-- The shift `λ²(h₀/L + Σ_{P∈A}h_P/π_P)` of a translate. -/
def trShift (L : 𝓞 K) (i : TrIdx L) : ℂ :=
  σO (δ3 ^ 2 * repQ L i.1.1) / σO L +
    ∑ P : i.1.2, σO (δ3 ^ 2 * repQ (πP P.1) (i.2 P)) / σO (πP P.1)

/-- The phase of a translate at `m = δ₃x` is `ψ_L(h₀x)∏_Pψ_{π_P}(h_Px)`. -/
theorem ebr_trShift (L : 𝓞 K) (i : TrIdx L) (x : 𝓞 K) :
    ebr (σO (δ3 * x) * trShift L i / 9) =
      ψc L (repQ L i.1.1 * x) * ∏ P : i.1.2, ψc (πP P.1) (repQ (πP P.1) (i.2 P) * x) := by
  unfold trShift
  rw [mul_add, add_div, ebr_add, ebr_shift, Finset.mul_sum, Finset.sum_div, ebr_sum]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [ebr_shift]

open Classical in
/-- **The coefficients of the translates reproduce the twist**: for every `x`,
`Σ_{(h₀,A,h)} φ̂₀(h₀)∏_{P∉A}C_P(0)∏_{P∈A}C_P(h_P)·ψ_L(h₀x)∏_Pψ_P(h_Px) = φ₀(x)∏_{P∈Ps}χ_P^{j_P}(x)`. -/
theorem trCoef_sum {L : 𝓞 K} (hL : L ≠ 0) [Fintype (𝓞 K ⧸ span {L})] (φ₀ : 𝓞 K → ℂ)
    (hφ : ∀ z u, φ₀ (z + L * u) = φ₀ z) (Ps : Finset Pr) (j : Pr → ℕ) (x : 𝓞 K) :
    ∑ h₀ : 𝓞 K ⧸ span {L}, fCoef L φ₀ (repQ L h₀) *
        ∑ A ∈ Ps.powerset, (∏ P ∈ Ps \ A, locCoef P (j P) 0) *
          ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
            (∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P))) *
              (ψc L (repQ L h₀ * x) * ∏ P : A, ψc (πP P.1) (repQ (πP P.1) (h P) * x)) =
      φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x := by
  have hinv := fourier_inv L hL φ₀ hφ x
  rw [finsum_eq_sum_of_fintype] at hinv
  rw [← hinv, prod_chiPow_expand, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h₀ _ => ?_
  rw [mul_assoc (fCoef L φ₀ (repQ L h₀))]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [mul_left_comm (ψc L (repQ L h₀ * x))]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

open Classical in
/-- **The twisted `θ̄` as grouped translates** (the companion paper's (A.4), with the translates
grouped by their active sets): for `θ = thSer(c₀, τ)` with `τ` under the support and size condition and
supported on `δ₃𝒪`, `φ₀` periodic modulo `L` with `φ₀(0) = 0`, and the twist
`F = φ₀·∏_{P∈Ps}χ_P^{j_P}`,
`Σ_m F(m/λ)·conj τ(−m)·vK_{1/3}(4π|m|v/9)ĕ(mz/9) =
Σ_{h₀ mod L}φ̂₀(h₀)Σ_{A⊆Ps}∏_{P∉A}C_{P,j_P}(0)Σ_{(h_P)_{P∈A}, h_P ≢ 0}∏_{P∈A}C_{P,j_P}(h_P)·
θ̄(z + λ²(h₀/L + Σ_{P∈A}h_P/π_P), v)`. -/
theorem twisted_theta_groups {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c₀ : ℂ} {τ : 𝓞 K → ℂ}
    (hθ : ∀ z v, 0 < v → θ z v = thSer c₀ τ z v) (hτ : ThetaSupp Kc τ)
    (hτd : ∀ m, τ m ≠ 0 → δ3 ∣ m) {L : 𝓞 K} (hL : L ≠ 0) (φ₀ : 𝓞 K → ℂ)
    (hφ : ∀ z u, φ₀ (z + L * u) = φ₀ z) (hφ0 : φ₀ 0 = 0) (Ps : Finset Pr) (j : Pr → ℕ)
    (z : ℂ) {v : ℝ} (hv : 0 < v) :
    ∑' m : 𝓞 K, twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m * conj (τ (-m)) * (v : ℂ) *
        besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * z / 9) =
      ∑ᶠ h₀ : 𝓞 K ⧸ span {L}, fCoef L φ₀ (repQ L h₀) *
        ∑ A ∈ Ps.powerset, (∏ P ∈ Ps \ A, locCoef P (j P) 0) *
          ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
            (∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P))) *
              conj (θ (z + trShift L ⟨(h₀, A), h⟩) v) := by
  have := finite_quot L hL
  let : Fintype (𝓞 K ⧸ span {L}) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  -- the family of translates
  set s : Finset (TrIdx L) := (Finset.univ ×ˢ Ps.powerset).sigma
    (fun p => Fintype.piFinset (fun P : p.2 => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0))
    with hs
  set a : TrIdx L → ℂ := fun i => fCoef L φ₀ (repQ L i.1.1) *
    ((∏ P ∈ Ps \ i.1.2, locCoef P (j P) 0) * ∏ P : i.1.2, locCoef P.1 (j P.1) (repQ (πP P.1) (i.2 P)))
    with ha
  have hkey : ∀ x, ∑ i ∈ s, a i * ebr (σO (δ3 * x) * trShift L i / 9) =
      φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x := by
    intro x
    rw [← trCoef_sum hL φ₀ hφ Ps j x, hs, Finset.sum_sigma, Finset.sum_product]
    refine Finset.sum_congr rfl fun h₀ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [ebr_trShift, ha]
    ring
  have hsum : ∑ i ∈ s, a i = 0 := by
    have := hkey 0
    simp only [mul_zero, map_zero, zero_mul, zero_div, ebr_zero, mul_one, hφ0] at this
    exact this
  have hT := thSer_translates s a (trShift L) (conj c₀) (fun m => conj (τ (-m)))
    (twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x)) z v
    (fun i _ => summable_thSer (thetaSupp_conj hτ) _ hv) (fun m hm => ?_)
  · rw [hsum, zero_mul, zero_add] at hT
    rw [← hT, hs, Finset.sum_sigma, Finset.sum_product]
    refine Finset.sum_congr rfl fun h₀ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [ha, hθ _ _ hv, conj_thSer]
    ring
  · have hm' : τ (-m) ≠ 0 := fun h0 => hm (by simp [h0])
    obtain ⟨x, rfl⟩ := dvd_neg.1 (hτd _ hm')
    rw [twAt_mul, ← hkey x]

/-- `C_{P,j}(0) = 0` for `j ≢ 0 (mod 6)`: only the primes with `j_P ≡ 0` can be inactive. -/
theorem locCoef_zero_of_ne (P : Pr) {j : ℕ} (hj : j % 6 ≠ 0) : locCoef P j 0 = 0 := by
  rw [locCoef_eq P hj, ite_eq_left P.1.zero_mem]

/-- A group of translates vanishes unless its active set contains every prime with `j_P ≢ 0`. -/
theorem prod_locCoef_zero_eq_zero {Ps A : Finset Pr} {j : Pr → ℕ} {P : Pr} (hP : P ∈ Ps \ A)
    (hj : j P % 6 ≠ 0) : ∏ Q ∈ Ps \ A, locCoef Q (j Q) 0 = 0 :=
  Finset.prod_eq_zero hP (locCoef_zero_of_ne P hj)

/-- The scalar `∏_{P∉A}C_{P,j_P}(0)` of the inactive primes has modulus at most `1`. -/
theorem norm_prod_locCoef_zero_le (S : Finset Pr) (j : Pr → ℕ) :
    ‖∏ P ∈ S, locCoef P (j P) 0‖ ≤ 1 := by
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun P _ => ?_
  by_cases hj : j P % 6 = 0
  · exact norm_locCoef_zero_le P hj
  · rw [locCoef_zero_of_ne P hj, norm_zero]; exact zero_le_one

end Eis

end

#print axioms Eis.chiPow_periodic
#print axioms Eis.locCoef_congr
#print axioms Eis.chiPow_expand
#print axioms Eis.prod_chiPow_expand
#print axioms Eis.ebr_zero
#print axioms Eis.ebr_sum
#print axioms Eis.ebr_trShift
#print axioms Eis.trCoef_sum
#print axioms Eis.twisted_theta_groups
#print axioms Eis.locCoef_zero_of_ne
#print axioms Eis.prod_locCoef_zero_eq_zero
#print axioms Eis.norm_prod_locCoef_zero_le
