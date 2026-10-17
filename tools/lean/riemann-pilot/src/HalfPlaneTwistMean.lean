import HalfPlaneTwist
import HalfPlaneMeanSquare
import EisensteinRealTwist
import KubotaThetaProof

/-!
# Round 476: the twisted extraction, and the half-plane for a twist by `J(d | ·)`; round 489: at every member; round 495: the twisted family

Step 3 of round 471's plan for the real characters, with the assembly of step 4 for a given character. Round 489
replaces the members `d³·gen(𝔟)⁶` by `u₀·gen(𝔟)⁶` for every `u₀ ≠ 0` whose sextic symbol is a function of the norm,
and keeps round 476's statements as the case `u₀ = d³`.

* **The twisted transfer**, round 285's S0′ twisted by a Dirichlet character `χ`: `χμ_K = (χf) ⍟ (χh)`
  (`muKTw_eq_fTw_mul_hTw`, from round 285's `fA_mul_hA`), so
  `Σ_n χ(n)μ_K(n)W(n/Z) = Σ_d χ(d)h(d)·Σ_m χ(m)f(m)W(md/Z)` (`smoothSumOf_muKTw_eq`). Bounds `O(Z^{θ+ε})` on
  `Σ_n χ(n)f(n)W(n/Z)` then give the hypothesis of round 475's `ne_zero_of_twistBound`
  (`twistBound_of_fSmoothTw`), since `|χ(d)h(d)| ≤ |h(d)|` and round 285's `summable_hfun`.
* **The family at `u₀·gen(𝔟)⁶`**: if `(u₀/𝔞)₆ = c(N𝔞)` on the ideals of norm prime to `6`, the family's weight
  at `u₀u` is `c(N𝔞)` times its weight at `u` (`wsym_member_mul`). So round 288's average over sixth powers, taken
  at the members `u₀·gen(𝔟)⁶`, is `κY·Σ_n c(n)f(n)W(n/Z)` up to round 288's error when `|c| ≤ 1`
  (`norm_sum_famSum_member_sub_le`). By round 474's identity, `u₀ = d³` and `c = J(d | ·)` qualify
  (`wsym_intCast_cube_mul`, `norm_sum_famSum_intCast_cube_sub_le`).
* **The twisted S2′** (`fSmoothC_isBigO_of_meanSquare`): round 288's Cauchy–Schwarz against `MeanSquare σ`,
  `σ ≥ 0`, with `N𝔟 ≤ Y = Z^{(1+σ)/6}/N(u₀)^{1/6}`, so that the members, distinct for `u₀ ≠ 0`, have norm
  `N(u₀)N(𝔟)⁶ ≤ Z^{1+σ}`: `Σ_n c(n)f(n)W(n/Z) = O(Z^{(11+5σ)/12+ε})`. At `u₀ = d³`, `N(u₀) = |d|⁶`
  (`fSmoothJ_isBigO_of_meanSquare`).
* **`ne_zero_of_memberTwist`**: for `3 ∣ N`, a Dirichlet character `χ` mod `N` with `χ ≠ 1` and `χχ₋₃ ≠ 1`, and
  `u₀ ≠ 0` with `(u₀/𝔞)₆ = χ(N𝔞)` on the ideals of norm prime to `6`: `L(s, χ) ≠ 0` and `L(s, χχ₋₃) ≠ 0` on
  `Re s > 11/12`. Round 466's mean square (`Eis.meanSquare`) at `σ = 6ε/5` gives the bound with exponent
  `11/12 + ε`, as round 468 did for `ζ`. **`ne_zero_of_jacobiTwist`** is the case `u₀ = d³`, for `χ` with
  `χ(n) = J(d | n)` on the `n` prime to `6`.
* **The twisted family** (round 495, step 4 of round 491's plan for door 5(b)): the statements above for round 494's
  family with coefficients, `A_Z^{c'}(u) = Σ_𝔞 c'(𝔞)μ(𝔞)(u/𝔞)₆W(N𝔞/Z)`, at the members `u₀·gen(𝔟)⁶` with
  `c'(𝔞)(u₀/𝔞)₆ = c(N𝔞)` on the ideals of norm prime to `6` (**`wsymC_member_mul`**, **`sum_famSumC_member_gen`**,
  **`norm_sum_famSumC_member_sub_le`**), against round 494's `MeanSquareC c' σ`
  (**`fSmoothC_isBigO_of_meanSquareC`**), and **`ne_zero_of_famTwist`**: `L(s, χ) ≠ 0` and `L(s, χχ₋₃) ≠ 0` on
  `Re s > 11/12` when `MeanSquareC c' σ` holds for every `σ > 0`. The statements of rounds 476 and 489 are the
  case `c' = 1` (round 494's `famSumC_one` and `meanSquareC_one_iff`).
-/

open NumberField Ideal UniqueFactorizationMonoid
open scoped LSeries.notation

namespace Eis

open HalfPlaneS0 ArithmeticFunction Filter Asymptotics

/-! ### The twist of round 285's transfer -/

section Transfer

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- The twisted totient-weighted coefficients `χ(n)f(n)`. -/
noncomputable def fTw : ArithmeticFunction ℂ := toArithmeticFunction fun n ↦ χ n * normSum wf n

/-- The twisted Euler correction `χ(n)h(n)`. -/
noncomputable def hTw : ArithmeticFunction ℂ := toArithmeticFunction fun n ↦ χ n * hfun n

/-- **`χμ_K = (χf) ⍟ (χh)`**, from round 285's `μ_K = f ⍟ h`. -/
theorem muKTw_eq_fTw_mul_hTw : muKTw χ = ⇑(fTw χ * hTw χ) := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [muKTw, muK_zero]
  · have hmu : muK n = (fA * hA) n := by rw [muK_eq, fA_mul_hA]
    rw [muKTw, hmu, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    obtain ⟨hx1, -⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    have h1 : x.1 ≠ 0 := fun h ↦ hn (by rw [← hx1, h, zero_mul])
    have h2 : x.2 ≠ 0 := fun h ↦ hn (by rw [← hx1, h, mul_zero])
    simp only [fTw, hTw, toArithmeticFunction, ArithmeticFunction.coe_mk, h1, h2, ite_false]
    rw [fA_apply h1, hA_apply h2, ← hx1, Nat.cast_mul, map_mul]
    ring

/-- The twisted smoothed sum `Σ_n χ(n)f(n)W(n/Z)`. -/
noncomputable def fSmoothTw (W : ℝ → ℝ) (Z : ℝ) : ℂ :=
  ∑' n : ℕ, χ n * normSum wf n * (W (n / Z) : ℂ)

theorem tw_wf_zero : (fun n : ℕ ↦ χ n * normSum wf n) 0 = 0 := by
  simp [normSum_wf_zero]

/-- **The twisted transfer identity**: `Σ_n χ(n)μ_K(n)W(n/Z) = Σ_d χ(d)h(d)·Σ_m χ(m)f(m)W(md/Z)`. -/
theorem smoothSumOf_muKTw_eq {W : ℝ → ℝ} {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x, R < x → W x = 0)
    {Z : ℝ} (hZ : 0 < Z) {M : ℕ} (hM : R * Z ≤ M) :
    smoothSumOf (muKTw χ) W Z = ∑ d ∈ Finset.Ioc 0 M, χ d * hfun d * fSmoothTw χ W (Z / d) := by
  rw [smoothSumOf, tsum_eq_Ioc (muKTw_zero χ) hR hZ hM, muKTw_eq_fTw_mul_hTw]
  rw [sum_Ioc_mul_weight (fTw χ) (hTw χ) (fun n => (W (n / Z) : ℂ)) M]
  rw [Finset.sum_filter_of_ne fun x hx hne => ?_]
  · rw [Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : 0 < d := (Finset.mem_Ioc.1 hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hZd : 0 < Z / d := div_pos hZ hdR
    have hfin := tsum_eq_Ioc (a := fun n : ℕ ↦ χ n * normSum wf n) (tw_wf_zero χ) hR hZd (N := M) (by
      calc R * (Z / d) ≤ R * Z := by
            apply mul_le_mul_of_nonneg_left _ hR0
            exact div_le_self hZ.le (by exact_mod_cast hd0)
        _ ≤ M := hM)
    rw [fSmoothTw, hfin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := (Finset.mem_Ioc.1 hm).1.ne'
    simp only [fTw, hTw, toArithmeticFunction, ArithmeticFunction.coe_mk, hm0, hd0.ne', ite_false]
    have e : ((m * d : ℕ) : ℝ) / Z = (m : ℝ) / (Z / d) := by
      push_cast; field_simp
    simp only [e]
    ring
  · -- a term with `x.1 * x.2 > M` vanishes
    by_contra hle
    apply hne
    have hlt : M < x.1 * x.2 := not_le.1 hle
    have : R < ((x.1 * x.2 : ℕ) : ℝ) / Z := by
      rw [lt_div_iff₀ hZ]
      calc R * Z ≤ M := hM
        _ < ((x.1 * x.2 : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [hR _ this, Complex.ofReal_zero, mul_zero]

/-- From `O(Z^α)` at infinity to a bound at every `Z > 0`, for the twisted sums. -/
theorem fSmoothTw_uniform {W : ℝ → ℝ} (hW : Weight W) {α : ℝ} (hα : 0 ≤ α)
    (hb : fSmoothTw χ W =O[atTop] fun Z => Z ^ α) :
    ∃ K, 0 ≤ K ∧ ∀ Z, 0 < Z → ‖fSmoothTw χ W Z‖ ≤ K * Z ^ α := by
  obtain ⟨c, hc⟩ := hb.bound
  obtain ⟨Z0, hZ0⟩ := Filter.eventually_atTop.1 hc
  obtain ⟨R, hR0, hR⟩ := hW.exists_vanish_right
  set R1 := R + 1 with hR1def
  have hR1 : 0 < R1 := by linarith
  have hR1' : ∀ x, R1 < x → W x = 0 := fun x hx => hR x (by linarith)
  obtain ⟨Mb, hMb⟩ := hW.compact.exists_bound_of_continuous hW.continuous
  set Z1 := max Z0 1 with hZ1def
  obtain ⟨M, hM⟩ := exists_nat_ge (R1 * Z1)
  set B := (∑ n ∈ Finset.Ioc 0 M, ‖χ n * normSum wf n‖) * Mb with hBdef
  have hMb0 : 0 ≤ Mb := le_trans (norm_nonneg _) (hMb 0)
  have hB0 : 0 ≤ B := mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hMb0
  refine ⟨max (max c 0) (B * R1 ^ α), le_trans (le_max_right c 0) (le_max_left _ _),
    fun Z hZ => ?_⟩
  have hZa : 0 ≤ Z ^ α := Real.rpow_nonneg hZ.le α
  by_cases hZ1 : Z1 ≤ Z
  · have h := hZ0 Z (le_trans (le_max_left _ _) hZ1)
    rw [Real.norm_of_nonneg hZa] at h
    calc ‖fSmoothTw χ W Z‖ ≤ c * Z ^ α := h
      _ ≤ max c 0 * Z ^ α := mul_le_mul_of_nonneg_right (le_max_left _ _) hZa
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hZa
  · rw [not_le] at hZ1
    have hRZ : R1 * Z ≤ M := le_trans (mul_le_mul_of_nonneg_left hZ1.le hR1.le) hM
    have hfin := tsum_eq_Ioc (a := fun n : ℕ ↦ χ n * normSum wf n) (tw_wf_zero χ) hR1' hZ hRZ
    by_cases hZs : R1 * Z < 1
    · have h0 : fSmoothTw χ W Z = 0 := by
        rw [fSmoothTw, hfin]
        refine Finset.sum_eq_zero fun n hn => ?_
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
        have : R1 < n / Z := by rw [lt_div_iff₀ hZ]; linarith
        rw [hR1' _ this, Complex.ofReal_zero, mul_zero]
      rw [h0, norm_zero]
      exact mul_nonneg (le_trans (le_max_right c 0) (le_max_left _ _)) hZa
    · rw [not_lt] at hZs
      have hsum : ‖fSmoothTw χ W Z‖ ≤ B := by
        rw [fSmoothTw, hfin]
        calc ‖∑ n ∈ Finset.Ioc 0 M, χ n * normSum wf n * (W (n / Z) : ℂ)‖
            ≤ ∑ n ∈ Finset.Ioc 0 M, ‖χ n * normSum wf n * (W (n / Z) : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.Ioc 0 M, ‖χ n * normSum wf n‖ * Mb := by
              refine Finset.sum_le_sum fun n _ => ?_
              rw [norm_mul, Complex.norm_real]
              exact mul_le_mul_of_nonneg_left (hMb _) (norm_nonneg _)
          _ = B := by rw [← Finset.sum_mul]
      calc ‖fSmoothTw χ W Z‖ ≤ B := hsum
        _ ≤ B * (R1 * Z) ^ α := le_mul_of_one_le_right hB0 (Real.one_le_rpow hZs hα)
        _ = B * R1 ^ α * Z ^ α := by rw [Real.mul_rpow hR1.le hZ.le]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hZa

/-- **The twisted S0′**: bounds `O(Z^{θ+ε})` on `Σ_n χ(n)f(n)W(n/Z)` for every weight and every `ε > 0`,
with `θ ≥ 0`, give the same bounds on `Σ_n χ(n)μ_K(n)W(n/D)`, the hypothesis of
`HalfPlaneS0.ne_zero_of_twistBound`. -/
theorem twistBound_of_fSmoothTw {θ : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ W : ℝ → ℝ, Weight W → ∀ ε : ℝ, 0 < ε → fSmoothTw χ W =O[atTop] fun Z => Z ^ (θ + ε)) :
    ∀ W : ℝ → ℝ, Weight W → ∀ ε : ℝ, 0 < ε →
      smoothSumOf (muKTw χ) W =O[atTop] fun D => D ^ (θ + ε) := by
  intro W hW ε hε
  have hα : 0 ≤ θ + ε := by linarith
  obtain ⟨K, hK0, hK⟩ := fSmoothTw_uniform χ hW hα (h W hW ε hε)
  obtain ⟨R, hR0, hR⟩ := hW.exists_vanish_right
  have hsumm := summable_hfun (σ := θ + ε) (by linarith)
  set Hs := ∑' d : ℕ, ‖hfun d‖ * (d : ℝ) ^ (-(θ + ε)) with hHs
  refine IsBigO.of_bound (K * Hs) ?_
  filter_upwards [eventually_gt_atTop 0] with Z hZ
  obtain ⟨M, hM⟩ := exists_nat_ge (R * Z)
  have hZa : 0 ≤ Z ^ (θ + ε) := Real.rpow_nonneg hZ.le _
  rw [smoothSumOf_muKTw_eq χ hR0 hR hZ hM, Real.norm_of_nonneg hZa]
  calc ‖∑ d ∈ Finset.Ioc 0 M, χ d * hfun d * fSmoothTw χ W (Z / d)‖
      ≤ ∑ d ∈ Finset.Ioc 0 M, ‖hfun d‖ * ‖fSmoothTw χ W (Z / d)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
        rw [norm_mul, norm_mul]
        gcongr
        exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
    _ ≤ ∑ d ∈ Finset.Ioc 0 M, ‖hfun d‖ * (K * (Z / d) ^ (θ + ε)) := by
        refine Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_left (hK _ ?_) (norm_nonneg _)
        exact div_pos hZ (by exact_mod_cast (Finset.mem_Ioc.1 hd).1)
    _ = K * Z ^ (θ + ε) * ∑ d ∈ Finset.Ioc 0 M, ‖hfun d‖ * (d : ℝ) ^ (-(θ + ε)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Ioc.1 hd).1
        rw [Real.div_rpow hZ.le hd.le, Real.rpow_neg hd.le]
        field_simp
    _ ≤ K * Z ^ (θ + ε) * Hs :=
        mul_le_mul_of_nonneg_left (hsumm.sum_le_tsum _ fun _ _ => by positivity)
          (mul_nonneg hK0 hZa)
    _ = K * Hs * Z ^ (θ + ε) := by ring

end Transfer

/-! ### The family at `u₀·gen(𝔟)⁶`, and at `d³·gen(𝔟)⁶` -/

section Average

open Classical in
/-- If `c'(𝔞)(u₀/𝔞)₆ = c(N𝔞)` on the ideals of norm prime to `6`, `c'(𝔞)` times the family's weight at `u₀u` is
`c(N𝔞)` times its weight at `u` (round 495). -/
theorem wsymC_member_mul {u₀ : 𝓞 K} {c' : Ideal (𝓞 K) → ℂ} {c : ℕ → ℂ}
    (hu₀ : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → c' I * sym6 u₀ I = c (absNorm I)) (u : 𝓞 K)
    (I : Ideal (𝓞 K)) :
    c' I * wsym (u₀ * u) I = c (absNorm I) * wsym u I := by
  unfold wsym
  split_ifs with hc
  · rw [sym6_mul_left, ← hu₀ I hc]
    ring
  · simp

open Classical in
/-- If `(u₀/𝔞)₆ = c(N𝔞)` on the ideals of norm prime to `6`, the family's weight at `u₀u` is `c(N𝔞)` times its
weight at `u`. -/
theorem wsym_member_mul {u₀ : 𝓞 K} {c : ℕ → ℂ}
    (hu₀ : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → sym6 u₀ I = c (absNorm I)) (u : 𝓞 K)
    (I : Ideal (𝓞 K)) :
    wsym (u₀ * u) I = c (absNorm I) * wsym u I := by
  simpa only [one_mul] using
    wsymC_member_mul (c' := fun _ => 1) (fun I hI => by simpa only [one_mul] using hu₀ I hI) u I

/-- Round 474's identity `(d³/𝔞)₆ = J(d | N𝔞)`, in the form of `wsym_member_mul`'s hypothesis. -/
theorem sym6_intCast_cube_member (d : ℤ) (I : Ideal (𝓞 K)) (hI : (absNorm I).Coprime 6) :
    sym6 ((d : 𝓞 K) ^ 3) I = (fun n : ℕ ↦ (jacobiSym d n : ℂ)) (absNorm I) :=
  sym6_intCast_cube d hI

open Classical in
/-- By round 474's identity, the family's weight at `d³u` is `J(d | N𝔞)` times its weight at `u`. -/
theorem wsym_intCast_cube_mul (d : ℤ) (u : 𝓞 K) (I : Ideal (𝓞 K)) :
    wsym ((d : 𝓞 K) ^ 3 * u) I = (jacobiSym d (absNorm I) : ℂ) * wsym u I :=
  wsym_member_mul (u₀ := (d : 𝓞 K) ^ 3) (c := fun n : ℕ ↦ (jacobiSym d n : ℂ)) (sym6_intCast_cube_member d) u I

open Classical in
/-- **The average of the twisted family over `u₀·gen(𝔟)⁶`**, as a finite sum (round 495): if
`c'(𝔞)(u₀/𝔞)₆ = c(N𝔞)` on the ideals of norm prime to `6`, round 288's `sum_famSum_gen` with the factor `c(n)`. -/
theorem sum_famSumC_member_gen {u₀ : 𝓞 K} {c' : Ideal (𝓞 K) → ℂ} {c : ℕ → ℂ}
    (hu₀ : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → c' I * sym6 u₀ I = c (absNorm I)) {W : ℝ → ℝ} {R : ℝ}
    (hR : ∀ x, R < x → W x = 0) {Z : ℝ} (hZ : 0 < Z) {M : ℕ} (hM : R * Z ≤ M) (Y : ℝ) :
    ∑ J ∈ idealsLe Y, famSumC c' W Z (u₀ * gen J ^ 6) =
      ∑ n ∈ Finset.Ioc 0 M, c n * (W (n / Z) : ℂ) * ∑ I ∈ ofNorm n,
        (if (absNorm I).Coprime 6 then (moebius I : ℂ) *
          (((idealsLe Y).filter fun J => ∀ P ∈ (normalizedFactors I).toFinset, ¬ P ∣ J).card : ℂ)
        else 0) := by
  simp only [famSumC]
  rw [Finset.sum_congr rfl fun J _ => tsum_eq_Ioc (normSum_wsymC_zero c' _) hR hZ hM, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_mul]
  simp only [normSum]
  rw [Finset.sum_comm]
  have hI : ∀ I ∈ ofNorm n, ∑ J ∈ idealsLe Y, c' I * wsym (u₀ * gen J ^ 6) I =
      c n * (if (absNorm I).Coprime 6 then (moebius I : ℂ) *
        (((idealsLe Y).filter fun J => ∀ P ∈ (normalizedFactors I).toFinset, ¬ P ∣ J).card : ℂ)
      else 0) := by
    intro I hI
    rw [Finset.sum_congr rfl fun J _ => wsymC_member_mul hu₀ (gen J ^ 6) I, ← Finset.mul_sum,
      sum_wsym_gen I Y, mem_ofNorm.1 hI]
  rw [Finset.sum_congr rfl hI, ← Finset.mul_sum]
  ring

open Classical in
/-- **The average over `u₀·gen(𝔟)⁶`**, as a finite sum: round 288's `sum_famSum_gen` with the factor
`c(n)`. -/
theorem sum_famSum_member_gen {u₀ : 𝓞 K} {c : ℕ → ℂ}
    (hu₀ : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → sym6 u₀ I = c (absNorm I)) {W : ℝ → ℝ} {R : ℝ}
    (hR : ∀ x, R < x → W x = 0) {Z : ℝ} (hZ : 0 < Z) {M : ℕ} (hM : R * Z ≤ M) (Y : ℝ) :
    ∑ J ∈ idealsLe Y, famSum W Z (u₀ * gen J ^ 6) =
      ∑ n ∈ Finset.Ioc 0 M, c n * (W (n / Z) : ℂ) * ∑ I ∈ ofNorm n,
        (if (absNorm I).Coprime 6 then (moebius I : ℂ) *
          (((idealsLe Y).filter fun J => ∀ P ∈ (normalizedFactors I).toFinset, ¬ P ∣ J).card : ℂ)
        else 0) := by
  simpa only [famSumC_one] using
    sum_famSumC_member_gen (c' := fun _ => 1) (fun I hI => by simpa only [one_mul] using hu₀ I hI) hR hZ hM Y

open Classical in
/-- **The average over `d³·gen(𝔟)⁶`**, as a finite sum: round 288's `sum_famSum_gen` with the factor
`J(d | n)`. -/
theorem sum_famSum_intCast_cube_gen (d : ℤ) {W : ℝ → ℝ} {R : ℝ} (hR : ∀ x, R < x → W x = 0) {Z : ℝ}
    (hZ : 0 < Z) {M : ℕ} (hM : R * Z ≤ M) (Y : ℝ) :
    ∑ J ∈ idealsLe Y, famSum W Z ((d : 𝓞 K) ^ 3 * gen J ^ 6) =
      ∑ n ∈ Finset.Ioc 0 M, (jacobiSym d n : ℂ) * (W (n / Z) : ℂ) * ∑ I ∈ ofNorm n,
        (if (absNorm I).Coprime 6 then (moebius I : ℂ) *
          (((idealsLe Y).filter fun J => ∀ P ∈ (normalizedFactors I).toFinset, ¬ P ∣ J).card : ℂ)
        else 0) :=
  sum_famSum_member_gen (sym6_intCast_cube_member d) hR hZ hM Y

/-- The twisted smoothed sum `Σ_n c(n)f(n)W(n/Z)`. -/
noncomputable def fSmoothC (c : ℕ → ℂ) (W : ℝ → ℝ) (Z : ℝ) : ℂ :=
  ∑' n : ℕ, c n * normSum wf n * (W (n / Z) : ℂ)

/-- The twisted smoothed sum `Σ_n J(d | n)f(n)W(n/Z)`. -/
noncomputable def fSmoothJ (d : ℤ) (W : ℝ → ℝ) (Z : ℝ) : ℂ :=
  fSmoothC (fun n ↦ (jacobiSym d n : ℂ)) W Z

theorem norm_jacobiSym_le (d : ℤ) (n : ℕ) : ‖(jacobiSym d n : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy d n with h | h | h <;> rw [h] <;> simp

open Classical in
/-- **The averaged identity with its error, for the twisted family** (round 495): if `c'(𝔞)(u₀/𝔞)₆ = c(N𝔞)` on the
ideals of norm prime to `6` and `|c(n)| ≤ 1`, then for `W` vanishing beyond `R`, bounded by `B`, and `RZ ≤ M`,
`|Σ_{N𝔟≤Y} A^{c'}_Z(u₀gen(𝔟)⁶) − κY·Σ_n c(n)f(n)W(n/Z)| ≤ B(5√Y + κ)·Σ_{n≤M} Σ_{N𝔞=n} 2^{ω(𝔞)}`. -/
theorem norm_sum_famSumC_member_sub_le {u₀ : 𝓞 K} {c' : Ideal (𝓞 K) → ℂ} {c : ℕ → ℂ}
    (hu₀ : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → c' I * sym6 u₀ I = c (absNorm I)) (hc1 : ∀ n, ‖c n‖ ≤ 1)
    {W : ℝ → ℝ} {R B : ℝ} (hR : ∀ x, R < x → W x = 0)
    (hB : ∀ x, |W x| ≤ B) {Z : ℝ} (hZ : 0 < Z) {M : ℕ} (hM : R * Z ≤ M) {Y : ℝ} (hY : 0 ≤ Y) :
    ‖∑ J ∈ idealsLe Y, famSumC c' W Z (u₀ * gen J ^ 6) - ((kappa * Y : ℝ) : ℂ) * fSmoothC c W Z‖ ≤
      B * (5 * √Y + kappa) * ∑ n ∈ Finset.Ioc 0 M, ‖normSum w2 n‖ := by
  have hk := kappa_pos
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hfin := tsum_eq_Ioc (a := fun n : ℕ ↦ c n * normSum wf n)
    (by simp [normSum_wf_zero]) hR hZ hM
  rw [sum_famSumC_member_gen hu₀ hR hZ hM Y, fSmoothC, hfin, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [normSum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    norm_normSum_w2, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  -- one ideal `𝔞`
  set S := (normalizedFactors I).toFinset
  have hSmax : ∀ P ∈ S, P.IsMaximal := fun P hP => isMaximal_of_factor (Multiset.mem_toFinset.1 hP)
  have hcnt := abs_card_coprime_sub_le hSmax hY
  have hWn : ‖(W (n / Z) : ℂ)‖ ≤ B := by rw [Complex.norm_real]; exact hB _
  have hJn := hc1 n
  unfold wf tot
  set c' : ℕ := ((idealsLe Y).filter fun J => ∀ P ∈ S, ¬ P ∣ J).card with hcdef
  set t : ℝ := ∏ P ∈ S, (1 - 1 / (absNorm P : ℝ)) with htdef
  have hct : |(c' : ℝ) - kappa * Y * t| ≤ 2 ^ S.card * (5 * √Y + kappa) := hcnt
  by_cases hc6 : (absNorm I).Coprime 6
  · rw [ite_eq_left hc6, ite_eq_left hc6]
    calc _ = ‖c n * (W (n / Z) : ℂ) * (moebius I : ℂ) *
            ((((c' : ℝ) - kappa * Y * t : ℝ)) : ℂ)‖ := by
          congr 1; simp only [htdef, S]; push_cast; ring
      _ = ‖c n‖ * ‖(W (n / Z) : ℂ)‖ * |(moebius I : ℝ)| * |(c' : ℝ) - kappa * Y * t| := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, Complex.norm_intCast]
      _ ≤ 1 * B * |(moebius I : ℝ)| * (2 ^ S.card * (5 * √Y + kappa)) := by gcongr
      _ = B * (5 * √Y + kappa) * (|(moebius I : ℝ)| * 2 ^ S.card) := by ring
      _ ≤ B * (5 * √Y + kappa) * ‖w2 I‖ :=
          mul_le_mul_of_nonneg_left (abs_moebius_mul_two_pow_le I) (by positivity)
  · rw [ite_eq_right hc6, ite_eq_right hc6]
    simp only [mul_zero, zero_mul, sub_zero, norm_zero]
    positivity

open Classical in
/-- **The averaged identity with its error, twisted**: for `W` vanishing beyond `R`, bounded by `B`, and
`RZ ≤ M`, `|Σ_{N𝔟≤Y} A_Z(u₀gen(𝔟)⁶) − κY·Σ_n c(n)f(n)W(n/Z)| ≤ B(5√Y + κ)·Σ_{n≤M} Σ_{N𝔞=n} 2^{ω(𝔞)}` when
`|c(n)| ≤ 1`. -/
theorem norm_sum_famSum_member_sub_le {u₀ : 𝓞 K} {c : ℕ → ℂ}
    (hu₀ : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → sym6 u₀ I = c (absNorm I)) (hc1 : ∀ n, ‖c n‖ ≤ 1)
    {W : ℝ → ℝ} {R B : ℝ} (hR : ∀ x, R < x → W x = 0)
    (hB : ∀ x, |W x| ≤ B) {Z : ℝ} (hZ : 0 < Z) {M : ℕ} (hM : R * Z ≤ M) {Y : ℝ} (hY : 0 ≤ Y) :
    ‖∑ J ∈ idealsLe Y, famSum W Z (u₀ * gen J ^ 6) - ((kappa * Y : ℝ) : ℂ) * fSmoothC c W Z‖ ≤
      B * (5 * √Y + kappa) * ∑ n ∈ Finset.Ioc 0 M, ‖normSum w2 n‖ := by
  simpa only [famSumC_one] using
    norm_sum_famSumC_member_sub_le (c' := fun _ => 1) (fun I hI => by simpa only [one_mul] using hu₀ I hI) hc1 hR
      hB hZ hM hY

open Classical in
/-- **The averaged identity with its error, twisted by `J(d | ·)`**: for `W` vanishing beyond `R`, bounded by `B`,
and `RZ ≤ M`, `|Σ_{N𝔟≤Y} A_Z(d³gen(𝔟)⁶) − κY·Σ_n J(d | n)f(n)W(n/Z)| ≤ B(5√Y + κ)·Σ_{n≤M} Σ_{N𝔞=n} 2^{ω(𝔞)}`. -/
theorem norm_sum_famSum_intCast_cube_sub_le (d : ℤ) {W : ℝ → ℝ} {R B : ℝ} (hR : ∀ x, R < x → W x = 0)
    (hB : ∀ x, |W x| ≤ B) {Z : ℝ} (hZ : 0 < Z) {M : ℕ} (hM : R * Z ≤ M) {Y : ℝ} (hY : 0 ≤ Y) :
    ‖∑ J ∈ idealsLe Y, famSum W Z ((d : 𝓞 K) ^ 3 * gen J ^ 6) - ((kappa * Y : ℝ) : ℂ) * fSmoothJ d W Z‖ ≤
      B * (5 * √Y + kappa) * ∑ n ∈ Finset.Ioc 0 M, ‖normSum w2 n‖ :=
  norm_sum_famSum_member_sub_le (sym6_intCast_cube_member d) (norm_jacobiSym_le d) hR hB hZ hM hY

end Average

/-! ### Cauchy–Schwarz against the mean square at `u₀·gen(𝔟)⁶` -/

section MeanSquareTw

/-- The members `u₀·gen(𝔟)⁶` with `N𝔟 ≤ Y`. -/
noncomputable def memberSixthPowers (u₀ : 𝓞 K) (Y : ℝ) : Finset (𝓞 K) := by
  classical exact (idealsLe Y).image fun J => u₀ * gen J ^ 6

theorem member_gen_injOn {u₀ : 𝓞 K} (hu₀ : u₀ ≠ 0) (Y : ℝ) :
    Set.InjOn (fun J => u₀ * gen J ^ 6) ↑(idealsLe Y) := by
  intro J hJ J' hJ' h
  exact gen_pow_six_injOn Y hJ hJ' (mul_left_cancel₀ hu₀ h)

theorem card_memberSixthPowers {u₀ : 𝓞 K} (hu₀ : u₀ ≠ 0) (Y : ℝ) :
    (memberSixthPowers u₀ Y).card = idealCount Y := by
  classical
  rw [memberSixthPowers, Finset.card_image_of_injOn (member_gen_injOn hu₀ Y), card_idealsLe]

theorem sum_memberSixthPowers {u₀ : 𝓞 K} (hu₀ : u₀ ≠ 0) (A : 𝓞 K → ℂ) (Y : ℝ) :
    ∑ z ∈ memberSixthPowers u₀ Y, A z = ∑ J ∈ idealsLe Y, A (u₀ * gen J ^ 6) := by
  classical
  rw [memberSixthPowers, Finset.sum_image (member_gen_injOn hu₀ Y)]

theorem mem_memberSixthPowers_spec {u₀ : 𝓞 K} (hu₀ : u₀ ≠ 0) {Y : ℝ} (hY : 0 ≤ Y) {z : 𝓞 K}
    (hz : z ∈ memberSixthPowers u₀ Y) :
    z ≠ 0 ∧ (absNorm (span {z}) : ℝ) ≤ (absNorm (span {u₀}) : ℝ) * Y ^ 6 := by
  classical
  rw [memberSixthPowers, Finset.mem_image] at hz
  obtain ⟨J, hJ, rfl⟩ := hz
  have hJ0 := ne_bot_of_mem_idealsLe hJ
  refine ⟨mul_ne_zero hu₀ (pow_ne_zero _ (gen_ne_zero hJ0)), ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, span_gen_pow, map_mul, map_pow, Nat.cast_mul,
    Nat.cast_pow]
  have h := (mem_idealsLe.1 hJ).2
  have hJY : (absNorm J : ℝ) ≤ Y := le_trans (by exact_mod_cast h) (Nat.floor_le hY)
  have h6 : (absNorm J : ℝ) ^ 6 ≤ Y ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) hJY 6
  exact mul_le_mul_of_nonneg_left h6 (by positivity)

/-- **The twisted S2′ for the twisted family at a member** (round 495): if `c'(𝔞)(u₀/𝔞)₆ = c(N𝔞)` on the ideals of
norm prime to `6`, `u₀ ≠ 0` and `|c| ≤ 1`, then round 494's `MeanSquareC c' σ` with `σ ≥ 0` gives
`Σ_n c(n)f(n)W(n/Z) = O(Z^{(11+5σ)/12+ε})` for every weight `W` and `ε > 0`. Round 476's proof, averaged over
`u₀gen(𝔟)⁶` with `N𝔟 ≤ Y = Z^{(1+σ)/6}/N(u₀)^{1/6}`. -/
theorem fSmoothC_isBigO_of_meanSquareC {σ : ℝ} (hσ : 0 ≤ σ) {c' : Ideal (𝓞 K) → ℂ} (h : MeanSquareC c' σ)
    {u₀ : 𝓞 K} (hu₀0 : u₀ ≠ 0)
    {c : ℕ → ℂ} (hu₀ : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → c' I * sym6 u₀ I = c (absNorm I))
    (hc1 : ∀ n, ‖c n‖ ≤ 1)
    (W : ℝ → ℝ) (hW : HalfPlaneS0.Weight W) {ε : ℝ} (hε : 0 < ε) :
    fSmoothC c W =O[atTop] fun Z => Z ^ ((11 + 5 * σ) / 12 + ε) := by
  obtain ⟨R, hR0, hR⟩ := hW.exists_vanish_right
  obtain ⟨B, hB⟩ := hW.compact.exists_bound_of_continuous hW.continuous
  have hB' : ∀ x, |W x| ≤ B := fun x => by have := hB x; rwa [Real.norm_eq_abs] at this
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB' 0)
  obtain ⟨Cms, hCms⟩ := h W hW ε hε
  obtain ⟨C2, hC20, hC2⟩ := sum_w2_le hε
  have hk := kappa_pos
  set Nu : ℝ := (absNorm (span {u₀}) : ℝ) with hNu
  have hNu1 : 1 ≤ Nu := by
    rw [hNu]
    have : absNorm (span {u₀}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hu₀0
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = Nu ^ ((1 : ℝ) / 6) := ⟨_, rfl⟩
  have he1 : 1 ≤ e := hedef ▸ Real.one_le_rpow hNu1 (by norm_num)
  have he0 : 0 < e := by linarith
  have he6 : e ^ 6 = Nu := by
    rw [hedef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  set C1 : ℝ := max Cms 0 with hC1
  have hC10 : 0 ≤ C1 := le_max_right _ _
  set A1 : ℝ := √((2 * kappa + 5) * C1) with hA1
  set A2 : ℝ := B * (5 + kappa) * C2 * (R + 1) ^ (1 + ε) with hA2
  have hA10 : 0 ≤ A1 := Real.sqrt_nonneg _
  have hA20 : 0 ≤ A2 := by positivity
  refine IsBigO.of_bound ((A1 + A2) / (kappa / e)) ?_
  filter_upwards [eventually_ge_atTop 1] with Z hZ
  have hZ0 : 0 < Z := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Z ^ ((1 + σ) / 12) := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := hs ▸ Real.one_le_rpow hZ (by linarith)
  have hs0 : 0 < s := by linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = s ^ 2 / e := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := hY ▸ div_nonneg (by positivity) he0.le
  have hYs : Y ≤ s ^ 2 := hY ▸ div_le_self (by positivity) he1
  have hsqrtY : √Y ≤ s := by
    calc √Y ≤ √(s ^ 2) := Real.sqrt_le_sqrt hYs
      _ = s := Real.sqrt_sq hs0.le
  have hY6 : e ^ 6 * Y ^ 6 = Z ^ (1 + σ) := by
    rw [hY, div_pow, mul_div_cancel₀ _ (by positivity), hs, ← pow_mul, ← Real.rpow_natCast,
      ← Real.rpow_mul hZ0.le]
    congr 1; push_cast; ring
  set M : ℕ := ⌈R * Z⌉₊ with hMdef
  have hM : R * Z ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) ≤ (R + 1) * Z := by
    have := Nat.ceil_lt_add_one (mul_nonneg hR0 hZ0.le)
    nlinarith
  -- the error of the average
  have herr : ‖∑ J ∈ idealsLe Y, famSumC c' W Z (u₀ * gen J ^ 6) -
      ((kappa * Y : ℝ) : ℂ) * fSmoothC c W Z‖ ≤ A2 * s * Z ^ (1 + ε) := by
    refine (norm_sum_famSumC_member_sub_le hu₀ hc1 hR hB' hZ0 hM hY0).trans ?_
    have h1 : 5 * √Y + kappa ≤ (5 + kappa) * s := by nlinarith
    have h2 : ∑ n ∈ Finset.Ioc 0 M, ‖normSum w2 n‖ ≤ C2 * ((R + 1) ^ (1 + ε) * Z ^ (1 + ε)) := by
      rw [← Real.mul_rpow (by linarith) hZ0.le]
      exact (hC2 M).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hM2 (by linarith)) hC20)
    have hE0 : 0 ≤ ∑ n ∈ Finset.Ioc 0 M, ‖normSum w2 n‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc B * (5 * √Y + kappa) * ∑ n ∈ Finset.Ioc 0 M, ‖normSum w2 n‖
        ≤ B * ((5 + kappa) * s) * (C2 * ((R + 1) ^ (1 + ε) * Z ^ (1 + ε))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hB0) h2 hE0 (by positivity)
      _ = A2 * s * Z ^ (1 + ε) := by rw [hA2]; ring
  -- the main sum, by Cauchy–Schwarz and the mean square
  have hT : ∀ z ∈ memberSixthPowers u₀ Y, z ≠ 0 ∧ (absNorm (span {z}) : ℝ) ≤ Z ^ (1 + σ) := fun z hz => by
    obtain ⟨h1, h2⟩ := mem_memberSixthPowers_spec hu₀0 hY0 hz
    refine ⟨h1, h2.trans_eq ?_⟩
    rw [← hNu, ← he6]
    exact hY6
  have hms := hCms Z hZ (memberSixthPowers u₀ Y) hT
  have hcs := norm_sum_sq_le (memberSixthPowers u₀ Y) (famSumC c' W Z)
  rw [sum_memberSixthPowers hu₀0 (famSumC c' W Z) Y, card_memberSixthPowers hu₀0] at hcs
  have hcount : (idealCount Y : ℝ) ≤ (2 * kappa + 5) * s ^ 2 := by
    have hic := abs_idealCount_sub_le hY0
    rw [abs_le] at hic
    have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs1
    have hq1 : kappa * Y ≤ kappa * s ^ 2 := mul_le_mul_of_nonneg_left hYs hk.le
    have hq2 : √Y ≤ s ^ 2 := hsqrtY.trans (by nlinarith)
    have hq3 : kappa ≤ kappa * s ^ 2 := le_mul_of_one_le_right hk.le hs2
    linarith [hic.2]
  have hsum0 : 0 ≤ ∑ z ∈ memberSixthPowers u₀ Y, ‖famSumC c' W Z z‖ ^ 2 :=
    Finset.sum_nonneg fun z _ => by positivity
  have hsq : ‖∑ J ∈ idealsLe Y, famSumC c' W Z (u₀ * gen J ^ 6)‖ ^ 2 ≤
      (2 * kappa + 5) * s ^ 2 * (C1 * Z ^ (2 + σ + ε)) :=
    hcs.trans (mul_le_mul hcount (hms.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity))) hsum0 (by positivity))
  have hmain := le_of_sq_le_aux (norm_nonneg _) (by positivity) hC10 hs0.le hZ0 hsq
  -- combine
  have hcomb : kappa / e * s ^ 2 * ‖fSmoothC c W Z‖ ≤
      A1 * s * Z ^ ((2 + σ + ε) / 2) + A2 * s * Z ^ (1 + ε) := by
    have e1 : kappa / e * s ^ 2 * ‖fSmoothC c W Z‖ = ‖((kappa * Y : ℝ) : ℂ) * fSmoothC c W Z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hY]
      ring
    rw [e1]
    have htri := norm_sub_le (∑ J ∈ idealsLe Y, famSumC c' W Z (u₀ * gen J ^ 6))
      (∑ J ∈ idealsLe Y, famSumC c' W Z (u₀ * gen J ^ 6) -
        ((kappa * Y : ℝ) : ℂ) * fSmoothC c W Z)
    rw [sub_sub_cancel] at htri
    exact htri.trans (add_le_add hmain herr)
  -- divide by `(κ/e)s²`, and compare exponents
  have hE1 : Z ^ ((2 + σ + ε) / 2) = s * Z ^ ((11 + 5 * σ) / 12 + ε / 2) := by
    rw [hs, ← Real.rpow_add hZ0]; congr 1; ring
  have hE2 : Z ^ (1 + ε) = s * Z ^ (1 + ε - (1 + σ) / 12) := by
    rw [hs, ← Real.rpow_add hZ0]; congr 1; ring
  rw [hE1, hE2] at hcomb
  rw [Real.norm_of_nonneg (by positivity)]
  exact le_of_mul_le_aux (div_pos hk he0) hs0 hA10 hA20
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hcomb

/-- **The twisted S2′ at a member**: if `(u₀/𝔞)₆ = c(N𝔞)` on the ideals of norm prime to `6`, `u₀ ≠ 0` and
`|c| ≤ 1`, then `MeanSquare σ` with `σ ≥ 0` gives `Σ_n c(n)f(n)W(n/Z) = O(Z^{(11+5σ)/12+ε})` for every weight `W`
and `ε > 0`. Round 476's proof, averaged over `u₀gen(𝔟)⁶` with `N𝔟 ≤ Y = Z^{(1+σ)/6}/N(u₀)^{1/6}`. -/
theorem fSmoothC_isBigO_of_meanSquare {σ : ℝ} (hσ : 0 ≤ σ) (h : MeanSquare σ) {u₀ : 𝓞 K} (hu₀0 : u₀ ≠ 0)
    {c : ℕ → ℂ} (hu₀ : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → sym6 u₀ I = c (absNorm I))
    (hc1 : ∀ n, ‖c n‖ ≤ 1)
    (W : ℝ → ℝ) (hW : HalfPlaneS0.Weight W) {ε : ℝ} (hε : 0 < ε) :
    fSmoothC c W =O[atTop] fun Z => Z ^ ((11 + 5 * σ) / 12 + ε) :=
  fSmoothC_isBigO_of_meanSquareC hσ (meanSquareC_one_iff.2 h) hu₀0 (c' := fun _ => 1)
    (fun I hI => by simpa only [one_mul] using hu₀ I hI) hc1 W hW hε

/-- **The twisted S2′ at `d³`**: `MeanSquare σ` with `σ ≥ 0` gives `Σ_n J(d | n)f(n)W(n/Z) = O(Z^{(11+5σ)/12+ε})`
for every `d ≠ 0`, weight `W` and `ε > 0`: `fSmoothC_isBigO_of_meanSquare` at the member `d³`, whose norm is
`|d|⁶`, so that `Y = Z^{(1+σ)/6}/|d|`. -/
theorem fSmoothJ_isBigO_of_meanSquare {σ : ℝ} (hσ : 0 ≤ σ) (h : MeanSquare σ) {d : ℤ} (hd : d ≠ 0)
    (W : ℝ → ℝ) (hW : HalfPlaneS0.Weight W) {ε : ℝ} (hε : 0 < ε) :
    fSmoothJ d W =O[atTop] fun Z => Z ^ ((11 + 5 * σ) / 12 + ε) :=
  fSmoothC_isBigO_of_meanSquare hσ h (pow_ne_zero 3 (Int.cast_ne_zero.2 hd)) (sym6_intCast_cube_member d)
    (norm_jacobiSym_le d) W hW hε

end MeanSquareTw

/-! ### The half-plane for a twist through a member, and by `J(d | ·)` -/

section HalfPlane

open DirichletCharacter

theorem normSum_wf_eq_zero {n : ℕ} (hn : ¬ n.Coprime 6) : normSum wf n = 0 := by
  classical
  refine Finset.sum_eq_zero fun I hI => ?_
  rw [wf, ite_eq_right]
  intro hc
  exact hn (by rw [← mem_ofNorm.1 hI]; exact hc)

/-- **The half-plane `Re s > 11/12` for a twist through the twisted family** (round 495). For `3 ∣ N`, a Dirichlet
character `χ` mod `N` with `χ ≠ 1` and `χχ₋₃ ≠ 1`, coefficients `c'` with `MeanSquareC c' σ` for every `σ > 0`, and
`u₀ ≠ 0` with `c'(𝔞)(u₀/𝔞)₆ = χ(N𝔞)` on the ideals of norm prime to `6`: `L(s, χ) ≠ 0` and `L(s, χχ₋₃) ≠ 0` on
`Re s > 11/12`. -/
theorem ne_zero_of_famTwist {N : ℕ} [NeZero N] (h3 : 3 ∣ N) {χ : DirichletCharacter ℂ N}
    {c' : Ideal (𝓞 K) → ℂ} (hms : ∀ σ : ℝ, 0 < σ → MeanSquareC c' σ) {u₀ : 𝓞 K} (hu₀0 : u₀ ≠ 0)
    (hu₀ : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → c' I * sym6 u₀ I = χ (absNorm I))
    (hχ : χ ≠ 1) (hχ3 : mulChi3 h3 χ ≠ 1) {s : ℂ} (hs : 11 / 12 < s.re) :
    LFunction χ s ≠ 0 ∧ LFunction (mulChi3 h3 χ) s ≠ 0 := by
  refine ne_zero_of_twistBound h3 hχ hχ3 (θ := 11 / 12)
    (twistBound_of_fSmoothTw χ (by norm_num) fun W hW ε hε => ?_) hs
  have hσ : (0 : ℝ) < 6 * ε / 5 := by positivity
  have hb := fSmoothC_isBigO_of_meanSquareC hσ.le (hms _ hσ) hu₀0 (c := fun n ↦ χ n) hu₀
    (fun n ↦ DirichletCharacter.norm_le_one χ n) W hW (ε := ε / 2) (by positivity)
  have e : (11 + 5 * (6 * ε / 5)) / 12 + ε / 2 = 11 / 12 + ε := by ring
  rw [e] at hb
  exact hb

/-- **The half-plane `Re s > 11/12` for a twist through a member.** For `3 ∣ N`, a Dirichlet character `χ` mod
`N` with `χ ≠ 1` and `χχ₋₃ ≠ 1`, and `u₀ ≠ 0` with `(u₀/𝔞)₆ = χ(N𝔞)` on the ideals of norm prime to `6`:
`L(s, χ) ≠ 0` and `L(s, χχ₋₃) ≠ 0` on `Re s > 11/12`. -/
theorem ne_zero_of_memberTwist {N : ℕ} [NeZero N] (h3 : 3 ∣ N) {χ : DirichletCharacter ℂ N} {u₀ : 𝓞 K}
    (hu₀0 : u₀ ≠ 0) (hu₀ : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → sym6 u₀ I = χ (absNorm I))
    (hχ : χ ≠ 1) (hχ3 : mulChi3 h3 χ ≠ 1) {s : ℂ} (hs : 11 / 12 < s.re) :
    LFunction χ s ≠ 0 ∧ LFunction (mulChi3 h3 χ) s ≠ 0 :=
  ne_zero_of_famTwist h3 (fun _ hσ => meanSquareC_one_iff.2 (meanSquare hσ)) hu₀0
    (fun I hI => by simpa only [one_mul] using hu₀ I hI) hχ hχ3 hs

/-- **The half-plane `Re s > 11/12` for a twist by `J(d | ·)`.** For `d ≠ 0`, `3 ∣ N` and a Dirichlet
character `χ` mod `N` with `χ(n) = J(d | n)` for every `n` prime to `6`, `χ ≠ 1` and `χχ₋₃ ≠ 1`:
`L(s, χ) ≠ 0` and `L(s, χχ₋₃) ≠ 0` on `Re s > 11/12`. The member `d³` of `ne_zero_of_memberTwist`. -/
theorem ne_zero_of_jacobiTwist {N : ℕ} [NeZero N] (h3 : 3 ∣ N) {χ : DirichletCharacter ℂ N} {d : ℤ}
    (hd : d ≠ 0) (hχd : ∀ n : ℕ, n.Coprime 6 → χ n = jacobiSym d n) (hχ : χ ≠ 1)
    (hχ3 : mulChi3 h3 χ ≠ 1) {s : ℂ} (hs : 11 / 12 < s.re) :
    LFunction χ s ≠ 0 ∧ LFunction (mulChi3 h3 χ) s ≠ 0 :=
  ne_zero_of_memberTwist h3 (pow_ne_zero 3 (Int.cast_ne_zero.2 hd))
    (fun I hI ↦ by rw [sym6_intCast_cube d hI, hχd _ hI]) hχ hχ3 hs

end HalfPlane

end Eis

#print axioms Eis.muKTw_eq_fTw_mul_hTw
#print axioms Eis.smoothSumOf_muKTw_eq
#print axioms Eis.twistBound_of_fSmoothTw
#print axioms Eis.wsym_intCast_cube_mul
#print axioms Eis.norm_sum_famSum_intCast_cube_sub_le
#print axioms Eis.fSmoothJ_isBigO_of_meanSquare
#print axioms Eis.ne_zero_of_jacobiTwist
#print axioms Eis.wsym_member_mul
#print axioms Eis.norm_sum_famSum_member_sub_le
#print axioms Eis.fSmoothC_isBigO_of_meanSquare
#print axioms Eis.ne_zero_of_memberTwist
#print axioms Eis.wsymC_member_mul
#print axioms Eis.sum_famSumC_member_gen
#print axioms Eis.norm_sum_famSumC_member_sub_le
#print axioms Eis.fSmoothC_isBigO_of_meanSquareC
#print axioms Eis.ne_zero_of_famTwist
