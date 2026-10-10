import EisensteinThirdTransfer

/-! # The transfer estimate (round 326)

S5c-6 in round 316's plan: the companion paper's Proposition 5.4, displayed in round 315 as
`TransferEstimate`, derived from its Lemmas 7.1 and 7.3 as in its proof:
"Lemma~\ref{lem:second-transfer}, with loss $D^{\varepsilon/4}$, supplies the hypothesis of
Lemma~\ref{lem:first-transfer} with $j=2m+4$ and $M\ll D^{\varepsilon/4}\Sigma(1+S_m)$."

* **The losses as powers of `D`** (`rpow_le_of_le_pow`): `x^e ≤ c^e·(D^{C₀e})^k` for
  `0 ≤ x ≤ c·(D^{C₀})^k`.
* **`transferEstimate`**: round 320's `first_transfer` with `J = 2m+2` and round 325's
  `third_transfer`, with all four losses at the exponent `ε/(8C₀)` and `c_I = 3β²R_Φ² + 1`. A weight with
  empty support (`β < α`) has row sum `0` (`rowE_eq_zero_of_zero`).
* **`ne_zero_of_completed`**: `ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` on `Re s > 11/12` from
  `CompletedMeanSquare` alone, through round 315's `ne_zero_of_completed_transfer`.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### The losses as powers of `D` -/

/-- `x^e ≤ c^e·(D^{C₀e})^k` for `0 ≤ x ≤ c·(D^{C₀})^k`. -/
theorem rpow_le_of_le_pow {D C₀ c x e : ℝ} (hD : 1 ≤ D) (hc : 0 ≤ c) (hx0 : 0 ≤ x) (k : ℕ)
    (hx : x ≤ c * (D ^ C₀) ^ k) (he : 0 ≤ e) : x ^ e ≤ c ^ e * (D ^ (C₀ * e)) ^ k := by
  have hD0 : 0 ≤ D := by linarith
  have hDC : 0 ≤ D ^ C₀ := Real.rpow_nonneg hD0 _
  calc x ^ e ≤ (c * (D ^ C₀) ^ k) ^ e := Real.rpow_le_rpow hx0 hx he
    _ = c ^ e * ((D ^ C₀) ^ k) ^ e := Real.mul_rpow hc (pow_nonneg hDC _)
    _ = c ^ e * (D ^ (C₀ * e)) ^ k := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hDC, ← Real.rpow_mul hD0,
          ← Real.rpow_mul hD0]
        congr 1
        ring

/-- A row sum with the zero weight vanishes. -/
theorem rowE_eq_zero_of_zero (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {W : ℝ → ℂ}
    (hW : ∀ x, W x = 0) (X : ℝ) (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)) :
    rowE ξ W X Fs T = 0 := by
  have h : W = fun x => (0 : ℂ) * W x := by funext x; rw [hW x, mul_zero]
  rw [h, rowE_const_mul, norm_zero]
  ring

/-! ### The transfer estimate -/

/-- **The companion paper's Proposition 5.4, the transfer estimate** (round 315's displayed
`TransferEstimate`), from its Lemmas 7.1–7.3: `first_transfer` with `J = 2m+2` reduces the row sum
to the form `𝒬`, and `third_transfer` bounds `𝒬` under the hypothesis on the child mean squares.
The losses `(4𝓗/(3L²))^{−σ}`, `(c_IΣLF/𝓗)^δ`, `(3𝓗L)^σ` and `L^η` are powers of `D` of total
exponent `ε` for `σ = δ = η = ε/(8C₀)`, and `c_I = 3β²R_Φ² + 1`. -/
theorem transferEstimate : TransferEstimate := by
  intro C₀ hC₀ m ε hε α β hα
  by_cases hαβ : α ≤ β
  swap
  · -- an empty support: the weight vanishes
    refine ⟨0, fun ξ W _ hWs N _ D Hh L F S _ _ _ _ _ _ _ _ _ _ _ M _ _ Fs T _ _ => ?_⟩
    have hW0 : ∀ x, W x = 0 := fun x => by
      rcases lt_or_ge x α with h | h
      · exact hWs x (Or.inl h)
      · exact hWs x (Or.inr (lt_of_lt_of_le (not_le.1 hαβ) h))
    rw [rowE_eq_zero_of_zero ξ hW0]
    simp
  have hC₀0 : 0 < C₀ := by linarith
  set e1 := ε / (8 * C₀) with he1
  have he10 : 0 < e1 := by positivity
  have he1ε : 8 * C₀ * e1 = ε := by rw [he1]; field_simp
  set cI := 3 * β ^ 2 * RΦ ^ 2 + 1 with hcIdef
  have hcI : 3 * β ^ 2 * RΦ ^ 2 ≤ cI := by linarith
  have hcI1 : 1 ≤ cI := by have := RΦ_pos; nlinarith [sq_nonneg β, sq_nonneg RΦ]
  have hcI0 : 0 < cI := by linarith
  obtain ⟨K1, K2, hK10, hK20, hK⟩ := first_transfer hα hαβ (2 * m + 2) he10 he10
  obtain ⟨K3, hK30, hK3⟩ := third_transfer hα hαβ m he10 he10
  refine ⟨K1 + K2 * K3 * cI * (3 ^ e1 * cI ^ e1 * 3 ^ e1), fun ξ W hW hWs N hN D Hh L F S hD hH
    hL hF hS hHD hLD hFD hSD hHS hLFS M hM0 hM Fs T hFs hT => ?_⟩
  have hD0 : 0 < D := by linarith
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < Hh := by linarith
  have hF0 : 0 < F := by linarith
  have hS0 : 0 < S := by linarith
  have hN' : ∀ x, ‖W x‖ ≤ N := fun x => by
    have := hN 0 (Nat.zero_le _) x; rwa [iteratedDeriv_zero] at this
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN' 0)
  -- the form `𝒬` by Lemma 7.3
  set MQ := K3 * (cI * S * F * L) * (3 * Hh * L) ^ e1 * L ^ e1 * (1 + M) with hMQ
  have hMQ0 : 0 ≤ MQ := by positivity
  have hQ : ∀ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ U : ℝ → ℂ, ContDiff ℝ ∞ U →
      (∀ x, x < α / 2 ∨ 2 * β < x → U x = 0) → ∀ NU : ℝ,
      (∀ j ≤ 2 * m + 2, ∀ x, ‖iteratedDeriv j U x‖ ≤ NU) →
      Qform ξ1 U β Hh L S F cI ≤ MQ * NU ^ 2 := by
    intro ξ1 U hU hUs NU hNU
    exact hK3 ξ1 U hU hUs NU hNU hH hL hF hHS hcI hcI1 hM0 hM
  -- Lemma 7.1
  have hW' : ∀ j ≤ 2 * (2 * m + 2) + 2, ∀ x, ‖iteratedDeriv j W x‖ ≤ N :=
    fun j hj x => hN j (by omega) x
  have h71 := hK ξ W hW hWs N hW' hH hL hF hLFS hcI hcI0 MQ hMQ0 hQ Fs T hFs hT
  -- the losses
  set u := D ^ (C₀ * e1) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow hD (by positivity)
  have hDε : D ^ ε = u ^ 8 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le, ← he1ε]; push_cast; ring_nf
  have hDC : 0 ≤ D ^ C₀ := Real.rpow_nonneg hD0.le _
  have hLsq : 3 * L ^ 2 ≤ 3 * (D ^ C₀) ^ 2 := by
    have := pow_le_pow_left₀ hL0.le hLD 2; linarith
  have hA : (4 * Hh / (3 * L ^ 2)) ^ (-e1) ≤ 3 ^ e1 * u ^ 2 := by
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
    refine rpow_le_of_le_pow hD (by norm_num) (by positivity) 2 ?_ he10.le
    calc 3 * L ^ 2 / (4 * Hh) ≤ 3 * L ^ 2 := div_le_self (by positivity) (by linarith)
      _ ≤ 3 * (D ^ C₀) ^ 2 := hLsq
  have hB : (cI * S * L * F / Hh) ^ e1 ≤ cI ^ e1 * u ^ 3 := by
    refine rpow_le_of_le_pow hD hcI0.le (by positivity) 3 ?_ he10.le
    calc cI * S * L * F / Hh ≤ cI * S * L * F := div_le_self (by positivity) hH
      _ = cI * (S * L * F) := by ring
      _ ≤ cI * ((D ^ C₀) ^ 3) := by
          refine mul_le_mul_of_nonneg_left ?_ hcI0.le
          rw [pow_three]
          calc S * L * F = S * (L * F) := by ring
            _ ≤ D ^ C₀ * (D ^ C₀ * D ^ C₀) :=
              mul_le_mul hSD (mul_le_mul hLD hFD hF0.le hDC) (by positivity) hDC
  have hC : (3 * Hh * L) ^ e1 ≤ 3 ^ e1 * u ^ 2 := by
    refine rpow_le_of_le_pow hD (by norm_num) (by positivity) 2 ?_ he10.le
    rw [sq]
    calc 3 * Hh * L = 3 * (Hh * L) := by ring
      _ ≤ 3 * (D ^ C₀ * D ^ C₀) := by gcongr
  have hE : L ^ e1 ≤ 1 ^ e1 * u ^ 1 := by
    refine rpow_le_of_le_pow hD zero_le_one hL0.le 1 ?_ he10.le
    rw [pow_one, one_mul]; exact hLD
  rw [Real.one_rpow, one_mul, pow_one] at hE
  have hA0 : 0 ≤ (4 * Hh / (3 * L ^ 2)) ^ (-e1) := Real.rpow_nonneg (by positivity) _
  have hB0 : 0 ≤ (cI * S * L * F / Hh) ^ e1 := Real.rpow_nonneg (by positivity) _
  have hC0 : 0 ≤ (3 * Hh * L) ^ e1 := Real.rpow_nonneg (by positivity) _
  have hE0 : 0 ≤ L ^ e1 := Real.rpow_nonneg hL0.le _
  have hM1 : 1 ≤ 1 + M := by linarith
  have hu8 : 1 ≤ u ^ 8 := one_le_pow₀ hu1
  -- the first term: the zero frequency
  have hT1 : K1 * N ^ 2 * (Hh * L * F) ≤ K1 * D ^ ε * S * N ^ 2 * (1 + M) * (L * F) := by
    rw [hDε]
    have h1 : Hh * L * F ≤ S * (L * F) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hHS (by positivity)
    calc K1 * N ^ 2 * (Hh * L * F) ≤ K1 * N ^ 2 * (S * (L * F)) := by gcongr
      _ = K1 * 1 * S * N ^ 2 * 1 * (L * F) := by ring
      _ ≤ K1 * u ^ 8 * S * N ^ 2 * (1 + M) * (L * F) := by gcongr
  -- the second term: the form `𝒬`
  have hT2 : K2 * N ^ 2 * (4 * Hh / (3 * L ^ 2)) ^ (-e1) * (cI * S * L * F / Hh) ^ e1 * MQ ≤
      K2 * K3 * cI * (3 ^ e1 * cI ^ e1 * 3 ^ e1) * D ^ ε * S * N ^ 2 * (1 + M) * (L * F) := by
    rw [hMQ, hDε]
    calc K2 * N ^ 2 * (4 * Hh / (3 * L ^ 2)) ^ (-e1) * (cI * S * L * F / Hh) ^ e1 *
          (K3 * (cI * S * F * L) * (3 * Hh * L) ^ e1 * L ^ e1 * (1 + M))
        = K2 * K3 * cI * N ^ 2 * S * (L * F) * (1 + M) *
          ((4 * Hh / (3 * L ^ 2)) ^ (-e1) * (cI * S * L * F / Hh) ^ e1 *
            ((3 * Hh * L) ^ e1 * L ^ e1)) := by ring
      _ ≤ K2 * K3 * cI * N ^ 2 * S * (L * F) * (1 + M) *
          ((3 ^ e1 * u ^ 2) * (cI ^ e1 * u ^ 3) * ((3 ^ e1 * u ^ 2) * u)) := by
          gcongr
      _ = K2 * K3 * cI * (3 ^ e1 * cI ^ e1 * 3 ^ e1) * u ^ 8 * S * N ^ 2 * (1 + M) * (L * F) := by
          ring
  calc rowE ξ W L Fs T ≤ K1 * N ^ 2 * (Hh * L * F) +
        K2 * N ^ 2 * (4 * Hh / (3 * L ^ 2)) ^ (-e1) * (cI * S * L * F / Hh) ^ e1 * MQ := h71
    _ ≤ K1 * D ^ ε * S * N ^ 2 * (1 + M) * (L * F) +
        K2 * K3 * cI * (3 ^ e1 * cI ^ e1 * 3 ^ e1) * D ^ ε * S * N ^ 2 * (1 + M) * (L * F) :=
        add_le_add hT1 hT2
    _ = (K1 + K2 * K3 * cI * (3 ^ e1 * cI ^ e1 * 3 ^ e1)) * D ^ ε * S * N ^ 2 * (1 + M) *
        (L * F) := by ring

/-- **The fourth conditional milestone**: the companion paper's Proposition 5.2, displayed as
`CompletedMeanSquare`, gives `ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` on `Re s > 11/12`; the transfer estimate
is now derived (`transferEstimate`). -/
theorem ne_zero_of_completed (hC : CompletedMeanSquare) {s : ℂ} (hs : 11 / 12 < s.re) :
    riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction PsiOmega.chi3 s ≠ 0 :=
  ne_zero_of_completed_transfer hC transferEstimate hs

end Eis

end

#print axioms Eis.rpow_le_of_le_pow
#print axioms Eis.rowE_eq_zero_of_zero
#print axioms Eis.transferEstimate
#print axioms Eis.ne_zero_of_completed
