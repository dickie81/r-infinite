/-
# Round 521, part 3: density over the characters mod `q` from a bound on the critical line

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. Let `0 < c ≤ 1` and suppose `|L(½ + it, χ)| ≤ C_L(q(|t| + 2))^c` for every character `χ ≠ 1` modulo
every `q ≥ 1` and every real `t` (`CritBoundχ c`). Then `CharDensity (2 + 4c) 10 C` with an explicit `C`
(`charDensity_of_LBound`): for every `q ≥ 1`, `½ ≤ σ ≤ 1` and `T ≥ 2`, at most `C(qT)^{(2+4c)(1−σ)}(log qT)^{10}`
characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. With round 520's `linnik_of_charDensity`,
for every `η > 0` every reduced class mod `q` has a prime `p ≤ K q^{2+4c+η}` (`linnik_of_critBound`). This is round
518's `densityXi_of_zetaCrit` over the family of characters mod `q`, with one point per character in place of one point
per unit window of ordinates.

* `class1_count`: characters with `|P_χ(ρ_χ)| ≥ c₁` at one zero `ρ_χ` each number at most
  `K³/c₁²·32e(1 + log 2XN)⁶(Q X^{1−2σ} + (XN)^{2−2σ})` for `q(2T + 1) ≤ 2Q`, `K = ⌊log₂ N⌋ + 1`: the dyadic blocks of
  `P_χ` (`Fkχ`), `LinnikHybrid.large_values_chars_off` at `lo, hi = ∓(T + ½)`, and round 518's
  `InghamDensity.block_mass_le_b`.
* `class2_count`: characters `χ ≠ 1` with `|I_χ(ρ_χ)| ≥ ¼` number at most `4A² MV(X)(q(T + 1) + X)`,
  `A = KG C_L Q^c Y^{½−σ}/δ`, for `σ ≥ ½ + δ` and `q(T + 2) ≤ Q`. On the line,
  `|G_χ(w)|(1 + |v|)³ ≤ A|M_X(½ + i(γ + v), χ)|` (`Gχ_left_le`); then `m ≤ λ/2 + m²/(2λ)` at `λ = 1/(2A)`, and the
  mean value of the mollifier at one point per character, `Σ_χ |M_X(½ + it_χ, χ)|² ≤ MV(X)(q(T + 1 + V) + X)` for
  `|t_χ| ≤ T + V` (`mean_value_mollχ`, with at most `q` characters, `card_chars_le`).
* `count_nontrivial`: at `X = ⌊Q⌋`, `Y = Q^{1+2c}`, `N = ⌊22Y log Y/X⌋ + 1` (round 518's `Xw`, `Yw`, `Nw`) and
  `Q ≥ q(T + 6)`, `LinnikDetect.dichotomy` at one zero of each counted `χ ≠ 1` (with `β < 1` by Mathlib's
  `LFunction_ne_zero_of_one_le_re`) puts the character in one of the two classes.
* `bound_class1`, `bound_class2`: the two counts are at most `16·13³·96·9⁶·71 (log Q)¹⁰ Q^{(2+4c)(1−σ)}` and
  `6400(KG C_L/δ)²(log Q)⁵ Q^{(2+4c)(1−σ)}` (round 518's `bound_K`, `bound_ell`, `bound_S1`, `bound_MV`).
* `charDensity_of_LBound`: below `σ = ½ + c/(1 + 2c)`, where `(2 + 4c)(1 − σ) ≥ 1`, at most `q ≤ qT` characters are
  counted; above it, the trivial character and `count_nontrivial` at `Q = q(T + 6) ≤ 4qT`, with `log Q ≤ 3 log qT`.
-/
import LinnikHybrid
import LinnikDetect
import InghamDensity
import LinnikDeduction

open Complex Real Filter Topology MeasureTheory

noncomputable section

namespace LinnikDensity

open InghamDensity Linnik LinnikDetect LinnikHybrid DirichletCharacter ShortWeil DirMean Finset

variable {q : ℕ} [NeZero q]

/-! ### The polynomial class: `|P_χ(ρ)| ≥ ¼` -/

omit [NeZero q] in
/-- The `k`-th dyadic block of `P_χ`. -/
def Fkχ (χ : DirichletCharacter ℂ q) (X N : ℕ) (Y : ℝ) (k : ℕ) (β γ : ℝ) : ℂ :=
  dp ((Ioc X (X * N)).filter (fun j => blk X j = k)) (fun j => b1 X Y j * χ j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) γ

omit [NeZero q] in
theorem Pvχ_eq_blocks (χ : DirichletCharacter ℂ q) (X N : ℕ) (hX : 1 ≤ X) (Y β γ : ℝ) :
    Pvχ χ X N Y β γ = ∑ k ∈ range (Nat.log 2 N + 1), Fkχ χ X N Y k β γ := by
  unfold Pvχ Fkχ
  exact dp_blocks X N hX _ γ

/-- **One block over the characters**: with one point `x_χ`, `|x_χ| ≤ T`, per character and `q(2T + 1) ≤ 2Q`,
`c₀²·#R ≤ 32e(1 + log 2XN)⁶(Q X^{1−2σ} + (XN)^{2−2σ})`. -/
theorem block_count_chars {σ T Q : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hT0 : 0 ≤ T)
    (hQ : (q : ℝ) * (2 * T + 1) ≤ 2 * Q)
    {X N k : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hk : k < Nat.log 2 N + 1) {Y : ℝ} (hY : 0 < Y)
    (Rs : Finset (DirichletCharacter ℂ q)) (x β : DirichletCharacter ℂ q → ℝ)
    (hx : ∀ χ ∈ Rs, |x χ| ≤ T) (hβ : ∀ χ ∈ Rs, σ ≤ β χ ∧ β χ ≤ σ + 1 / 2) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hbig : ∀ χ ∈ Rs, c₀ ≤ ‖Fkχ χ X N Y k (β χ) (x χ)‖) :
    (Rs.card : ℝ) * c₀ ^ 2 ≤ 32 * Real.exp 1 * (1 + Real.log (2 * X * N)) ^ 6
      * (Q * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ0 : 0 ≤ Q := by nlinarith
  set P := 2 ^ k * X with hPdef
  have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hPN : P ≤ X * N := by
    rw [hPdef, mul_comm X N]; exact Nat.mul_le_mul_right X (pow_blk_le hk hN)
  have hXP : X ≤ P := by rw [hPdef]; exact Nat.le_mul_of_pos_left X (by positivity)
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hPNr : (P : ℝ) ≤ X * N := by exact_mod_cast hPN
  have hXPr : (X : ℝ) ≤ P := by exact_mod_cast hXP
  set ℓ := Real.log (2 * X * N) with hℓ
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by nlinarith [mul_le_mul hXr hNr zero_le_one (by linarith)])
  have hlP : Real.log P ≤ ℓ := Real.log_le_log hP0 (by nlinarith)
  have hl2P : Real.log (2 * P) ≤ ℓ := Real.log_le_log (by positivity) (by nlinarith)
  have hlP0 : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast hP)
  have hl2P0 : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by nlinarith [(by exact_mod_cast hP : (1 : ℝ) ≤ P)])
  have hLV := large_values_chars_off hP (block_sub (N := N) (k := k) hX) (b1 X Y) q (σ := σ)
    (lo := -T - 1 / 2) (hi := T + 1 / 2) (by linarith) Rs x β
    (fun χ hχ => by have := abs_le.1 (hx χ hχ); constructor <;> linarith) hβ
  have hmass := block_mass_le_b (b1 X Y) (norm_b1_le X hY) hP (block_sub (N := N) (k := k) hX)
    (by linarith : 0 ≤ σ)
  have hlow : (Rs.card : ℝ) * c₀ ^ 2 ≤ ∑ χ ∈ Rs, ‖Fkχ χ X N Y k (β χ) (x χ)‖ ^ 2 := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun χ hχ => pow_le_pow_left₀ hc₀.le (hbig χ hχ) 2
  have hL : ((q : ℝ) * (T + 1 / 2 - (-T - 1 / 2)) + 8 * P * (1 + Real.log P)) ≤ 8 * (Q + P) * (1 + ℓ) := by
    have e : (q : ℝ) * (T + 1 / 2 - (-T - 1 / 2)) = q * (2 * T + 1) := by ring
    rw [e]
    nlinarith
  have hL2 : 2 + Real.log (2 * P) ^ 2 ≤ 2 * (1 + ℓ) ^ 2 := by nlinarith
  have hsplit : (P : ℝ) ^ (1 - 2 * σ) * (Q + P) ≤ Q * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ) := by
    have h1 : (P : ℝ) ^ (1 - 2 * σ) ≤ (X : ℝ) ^ (1 - 2 * σ) :=
      Real.rpow_le_rpow_of_nonpos hX0 hXPr (by linarith)
    have h2 : (P : ℝ) ^ (1 - 2 * σ) * P = (P : ℝ) ^ (2 - 2 * σ) := by
      rw [show (2 : ℝ) - 2 * σ = (1 - 2 * σ) + 1 by ring, Real.rpow_add hP0, Real.rpow_one]
    have h3 : (P : ℝ) ^ (2 - 2 * σ) ≤ ((X : ℝ) * N) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow hP0.le hPNr (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 hQ0]
  have hmass0 : 0 ≤ ∑ j ∈ (Ioc X (X * N)).filter (fun j => blk X j = k),
      ‖b1 X Y j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2 := sum_nonneg fun _ _ => by positivity
  have hPs : 0 ≤ (P : ℝ) ^ (1 - 2 * σ) := by positivity
  calc (Rs.card : ℝ) * c₀ ^ 2 ≤ ∑ χ ∈ Rs, ‖Fkχ χ X N Y k (β χ) (x χ)‖ ^ 2 := hlow
    _ ≤ Real.exp 1 * (((q : ℝ) * (T + 1 / 2 - (-T - 1 / 2)) + 8 * P * (1 + Real.log P))
          * (2 + Real.log (2 * P) ^ 2))
          * ∑ j ∈ (Ioc X (X * N)).filter (fun j => blk X j = k), ‖b1 X Y j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2 := hLV
    _ ≤ Real.exp 1 * ((8 * (Q + P) * (1 + ℓ)) * (2 * (1 + ℓ) ^ 2))
          * (2 * (P : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * P)) ^ 3) := by
        gcongr
    _ ≤ Real.exp 1 * ((8 * (Q + P) * (1 + ℓ)) * (2 * (1 + ℓ) ^ 2))
          * (2 * (P : ℝ) ^ (1 - 2 * σ) * (1 + ℓ) ^ 3) := by gcongr
    _ = 32 * Real.exp 1 * (1 + ℓ) ^ 6 * ((P : ℝ) ^ (1 - 2 * σ) * (Q + P)) := by ring
    _ ≤ 32 * Real.exp 1 * (1 + ℓ) ^ 6 * (Q * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) := by
        gcongr

/-- **The polynomial class**: characters with one point each, `|P_χ(β_χ + iγ_χ)| ≥ c₁`, number at most
`K³/c₁²·32e(1 + log 2XN)⁶(Q X^{1−2σ} + (XN)^{2−2σ})`, `K = ⌊log₂ N⌋ + 1`. -/
theorem class1_count {σ T Q : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hT0 : 0 ≤ T)
    (hQ : (q : ℝ) * (2 * T + 1) ≤ 2 * Q)
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) {Y : ℝ} (hY : 0 < Y) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (Rs : Finset (DirichletCharacter ℂ q)) (x β : DirichletCharacter ℂ q → ℝ)
    (hx : ∀ χ ∈ Rs, |x χ| ≤ T) (hβ : ∀ χ ∈ Rs, σ ≤ β χ ∧ β χ ≤ σ + 1 / 2)
    (hbig : ∀ χ ∈ Rs, c₁ ≤ ‖Pvχ χ X N Y (β χ) (x χ)‖) :
    (Rs.card : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3 / c₁ ^ 2 * (32 * Real.exp 1
      * (1 + Real.log (2 * X * N)) ^ 6 * (Q * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ))) := by
  classical
  set K := Nat.log 2 N + 1 with hK
  set B := 32 * Real.exp 1 * (1 + Real.log (2 * X * N)) ^ 6
      * (Q * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) with hB
  have hK0 : (0 : ℝ) < K := by positivity
  have hlarge : ∀ χ ∈ Rs, ∃ k ∈ range K, c₁ / K ≤ ‖Fkχ χ X N Y k (β χ) (x χ)‖ := by
    intro χ hχ
    by_contra hcon
    push Not at hcon
    have h1 := hbig χ hχ
    rw [Pvχ_eq_blocks χ X N hX] at h1
    have h2 : ∑ k ∈ range K, ‖Fkχ χ X N Y k (β χ) (x χ)‖ < ∑ _k ∈ range K, c₁ / (K : ℝ) :=
      sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ fun k hk => hcon k hk
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    have h3 : (K : ℝ) * (c₁ / K) = c₁ := by field_simp
    linarith [(norm_sum_le (range K) fun k => Fkχ χ X N Y k (β χ) (x χ)).trans_lt (h3 ▸ h2)]
  set Ck : ℕ → Finset (DirichletCharacter ℂ q) :=
    fun k => Rs.filter fun χ => c₁ / (K : ℝ) ≤ ‖Fkχ χ X N Y k (β χ) (x χ)‖
  have hsub : Rs ⊆ (range K).biUnion Ck := by
    intro χ hχ
    obtain ⟨k, hk, hbig⟩ := hlarge χ hχ
    exact mem_biUnion.2 ⟨k, hk, mem_filter.2 ⟨hχ, hbig⟩⟩
  have hCk : ∀ k ∈ range K, ((Ck k).card : ℝ) ≤ (K : ℝ) ^ 2 / c₁ ^ 2 * B := by
    intro k hk
    have hc0 : (0 : ℝ) < c₁ / K := by positivity
    have h := block_count_chars hσ hσ1 hT0 hQ hX hN (mem_range.1 hk) hY (Ck k) x β
      (fun χ hχ => hx χ (mem_filter.1 hχ).1) (fun χ hχ => hβ χ (mem_filter.1 hχ).1) hc0
      (fun χ hχ => (mem_filter.1 hχ).2)
    rw [div_pow, ← le_div_iff₀ (by positivity)] at h
    calc ((Ck k).card : ℝ) ≤ B / (c₁ ^ 2 / (K : ℝ) ^ 2) := h
      _ = (K : ℝ) ^ 2 / c₁ ^ 2 * B := by field_simp
  calc (Rs.card : ℝ) ≤ ((range K).biUnion Ck).card := by exact_mod_cast card_le_card hsub
    _ ≤ ∑ k ∈ range K, ((Ck k).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _k ∈ range K, (K : ℝ) ^ 2 / c₁ ^ 2 * B := sum_le_sum hCk
    _ = (K : ℝ) ^ 3 / c₁ ^ 2 * B := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-! ### The integral class: `|I_χ(ρ)| ≥ ¼` -/

/-- **On the line `Re w = ½ − β`**: `|G(w)|(1 + |v|)³ ≤ A·|M_X(½ + i(γ + v), χ)|` with `A = KG C_L Q^c Y^{½−σ}/δ`,
for a zero `ρ = β + iγ` of `L(·, χ)` with `σ ≤ β < 1`, `½ + δ ≤ σ`, `|γ| ≤ T`, `q(T + 2) ≤ Q`, given
`|L(½ + it, χ)| ≤ C_L(q(|t| + 2))^c`. -/
theorem Gχ_left_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {CL : ℝ} (hCL0 : 0 ≤ CL)
    {χ : DirichletCharacter ℂ q}
    (hL : ∀ t : ℝ, ‖LFunction χ (1 / 2 + t * I)‖ ≤ CL * ((q : ℝ) * (|t| + 2)) ^ c) (X : ℕ)
    {σ δ T Q Y β γ : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hσβ : σ ≤ β) (hβ1 : β < 1)
    (hγ : |γ| ≤ T) (hQ : (q : ℝ) * (T + 2) ≤ Q) (hY : 1 ≤ Y) (hz : LFunction χ ((β : ℂ) + γ * I) = 0)
    (v : ℝ) :
    ‖Gχ χ X Y ((β : ℂ) + γ * I) (((1 / 2 - ((β : ℂ) + γ * I).re : ℝ) : ℂ) + v * I)‖ * (1 + |v|) ^ 3
      ≤ KG * CL * Q ^ c * Y ^ (1 / 2 - σ) / δ * ‖mollχ χ X (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ := by
  have hre : ((β : ℂ) + γ * I).re = β := by simp
  rw [hre]
  set w : ℂ := ((1 / 2 - β : ℝ) : ℂ) + v * I with hw
  have hwre : w.re = 1 / 2 - β := by simp [hw]
  have hwim : w.im = v := by simp [hw]
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwre; simp at hwre; linarith
  have hsum : (β : ℂ) + γ * I + w = 1 / 2 + ((γ + v : ℝ) : ℂ) * I := by
    rw [hw]; push_cast; ring
  rw [Gχ_eq_left X Y hz hw0, hsum, norm_mul, norm_mul, norm_mul, norm_div]
  have hT0 : 0 ≤ T := (abs_nonneg γ).trans hγ
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hQ
  have hLb : ‖LFunction χ (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ ≤ CL * Q ^ c * (1 + |v|) ^ 2 := by
    refine (hL (γ + v)).trans ?_
    have hb : (q : ℝ) * (|γ + v| + 2) ≤ Q * (1 + |v|) := by
      have h1 := abs_add_le γ v
      have h2 : |γ + v| + 2 ≤ (T + 2) * (1 + |v|) := by nlinarith [abs_nonneg v]
      calc (q : ℝ) * (|γ + v| + 2) ≤ q * ((T + 2) * (1 + |v|)) := by gcongr
        _ = (q * (T + 2)) * (1 + |v|) := by ring
        _ ≤ Q * (1 + |v|) := by gcongr
    have hp : ((q : ℝ) * (|γ + v| + 2)) ^ c ≤ (Q * (1 + |v|)) ^ c :=
      Real.rpow_le_rpow (by positivity) hb hc0
    rw [Real.mul_rpow hQ0 (by positivity)] at hp
    have hv2 : (1 + |v|) ^ c ≤ (1 + |v|) ^ 2 := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) (by push_cast; linarith)
    calc CL * ((q : ℝ) * (|γ + v| + 2)) ^ c ≤ CL * (Q ^ c * (1 + |v|) ^ c) := by gcongr
      _ ≤ CL * (Q ^ c * (1 + |v|) ^ 2) := by gcongr
      _ = CL * Q ^ c * (1 + |v|) ^ 2 := by ring
  have hG := norm_Gamma_le' (z := w + 1) (by simp [hwre]; linarith) (by simp [hwre]; linarith)
  have hGim : (w + 1).im = v := by simp [hwim]
  rw [hGim] at hG
  have hwn : δ ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    rw [hwre, abs_of_neg (by linarith)] at this
    linarith
  have hYw : ‖(Y : ℂ) ^ w‖ ≤ Y ^ (1 / 2 - σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), hwre]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  have hwpos : 0 < ‖w‖ := by linarith
  set m := ‖mollχ χ X (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ with hm
  set g := ‖Complex.Gamma (w + 1)‖ with hg
  have hm0 : 0 ≤ m := norm_nonneg _
  have hg0 : 0 ≤ g := norm_nonneg _
  have hdiv : g / ‖w‖ ≤ g / δ := div_le_div_of_nonneg_left hg0 hδ hwn
  have hQc : 0 ≤ Q ^ c := Real.rpow_nonneg hQ0 c
  calc m * ‖LFunction χ (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ * (g / ‖w‖) * ‖(Y : ℂ) ^ w‖ * (1 + |v|) ^ 3
      ≤ m * (CL * Q ^ c * (1 + |v|) ^ 2) * (g / δ) * Y ^ (1 / 2 - σ) * (1 + |v|) ^ 3 := by
        gcongr
    _ = CL * Q ^ c * Y ^ (1 / 2 - σ) / δ * m * (g * (1 + |v|) ^ 5) := by ring
    _ ≤ CL * Q ^ c * Y ^ (1 / 2 - σ) / δ * m * KG := by gcongr
    _ = KG * CL * Q ^ c * Y ^ (1 / 2 - σ) / δ * m := by ring

omit [NeZero q] in
/-- The `k`-th dyadic block of `M_X(½ + it, χ) − 1`. -/
def Fmχ (χ : DirichletCharacter ℂ q) (X k : ℕ) (t : ℝ) : ℂ :=
  dp ((Ioc 1 (1 * X)).filter (fun j => blk 1 j = k))
    (fun j => ((ArithmeticFunction.moebius j : ℤ) : ℂ) * χ j * (((j : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) t

omit [NeZero q] in
theorem mollχ_half_eq (χ : DirichletCharacter ℂ q) {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    mollχ χ X (1 / 2 + (t : ℂ) * I) = 1 + ∑ k ∈ range (Nat.log 2 X + 1), Fmχ χ X k t := by
  have hsplit : Ioc 0 X = insert 1 (Ioc 1 X) := by
    ext m; simp only [mem_Ioc, mem_insert]; omega
  unfold mollχ
  rw [hsplit, sum_insert (by simp)]
  have h1 : ((ArithmeticFunction.moebius 1 : ℤ) : ℂ) * χ ((1 : ℕ) : ZMod q)
      * ((1 : ℕ) : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)) = 1 := by
    simp
  rw [h1]
  congr 1
  have hdp : ∑ m ∈ Ioc 1 X, ((ArithmeticFunction.moebius m : ℤ) : ℂ) * χ m * (m : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))
      = dp (Ioc 1 (1 * X))
          (fun j => ((ArithmeticFunction.moebius j : ℤ) : ℂ) * χ j * (((j : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) t := by
    rw [one_mul]
    unfold dp
    refine sum_congr rfl fun m hm => ?_
    have hm0 : 0 < m := by have := (mem_Ioc.1 hm).1; omega
    have e : (1 / 2 + (t : ℂ) * I) = (((1 / 2 : ℝ) : ℂ) + t * I) := by push_cast; ring
    rw [e, natCast_cpow_neg m hm0 (1 / 2) t]
    ring
  rw [hdp, dp_blocks 1 X le_rfl]
  rfl

omit [NeZero q] in
theorem norm_mollχ_half_sq_le (χ : DirichletCharacter ℂ q) {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    ‖mollχ χ X (1 / 2 + (t : ℂ) * I)‖ ^ 2
      ≤ 2 + 2 * ((Nat.log 2 X + 1 : ℕ) : ℝ) * ∑ k ∈ range (Nat.log 2 X + 1), ‖Fmχ χ X k t‖ ^ 2 := by
  rw [mollχ_half_eq χ hX]
  set K := Nat.log 2 X + 1 with hK
  set S := ∑ k ∈ range K, ‖Fmχ χ X k t‖ with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => norm_nonneg _
  have h1 : ‖(1 : ℂ) + ∑ k ∈ range K, Fmχ χ X k t‖ ≤ 1 + S :=
    (norm_add_le _ _).trans (by rw [norm_one]; gcongr; exact norm_sum_le _ _)
  have h2 : S ^ 2 ≤ K * ∑ k ∈ range K, ‖Fmχ χ X k t‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range K) (f := fun k => ‖Fmχ χ X k t‖)
    simpa [hS] using this
  calc ‖(1 : ℂ) + ∑ k ∈ range K, Fmχ χ X k t‖ ^ 2 ≤ (1 + S) ^ 2 := by gcongr
    _ ≤ 2 + 2 * S ^ 2 := by nlinarith [sq_nonneg (S - 1)]
    _ ≤ 2 + 2 * (K * ∑ k ∈ range K, ‖Fmχ χ X k t‖ ^ 2) := by gcongr
    _ = 2 + 2 * (K : ℝ) * ∑ k ∈ range K, ‖Fmχ χ X k t‖ ^ 2 := by ring

/-- At most `q` characters modulo `q`. -/
theorem card_chars_le (R : Finset (DirichletCharacter ℂ q)) : (R.card : ℝ) ≤ q := by
  have h1 : R.card ≤ Fintype.card (DirichletCharacter ℂ q) := Finset.card_le_univ R
  have h2 : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]; exact card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  exact_mod_cast h1.trans (h2 ▸ Nat.totient_le q)

/-- **The mean value of `M_X(½ + it, χ)` at one point per character**: for `|t_χ| ≤ T + V`,
`Σ_χ |M_X(½ + it_χ, χ)|² ≤ MV(X)(q(T + 1 + V) + X)`. -/
theorem mean_value_mollχ {X : ℕ} (hX : 1 ≤ X) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V)
    (R : Finset (DirichletCharacter ℂ q)) (t : DirichletCharacter ℂ q → ℝ)
    (ht : ∀ χ ∈ R, |t χ| ≤ T + V) :
    ∑ χ ∈ R, ‖mollχ χ X (1 / 2 + (t χ : ℂ) * I)‖ ^ 2 ≤ MV X * ((q : ℝ) * (T + 1 + V) + X) := by
  set K := Nat.log 2 X + 1 with hK
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hl2X : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hRq := card_chars_le R
  set E := Real.exp 1 * (((q : ℝ) * (2 * T + 2 * V + 1) + 8 * X * (1 + Real.log X))
    * (2 + Real.log (2 * X) ^ 2)) with hE
  have hblock : ∀ k ∈ range K, ∑ χ ∈ R, ‖Fmχ χ X k (t χ)‖ ^ 2 ≤ E := by
    intro k hk
    have hk' := mem_range.1 hk
    have hP : 1 ≤ 2 ^ k * 1 := by rw [mul_one]; exact Nat.one_le_two_pow
    have hPX : 2 ^ k ≤ X := pow_blk_le hk' hX
    have hLV := large_values_chars_off hP (block_sub (X := 1) (N := X) (k := k) le_rfl)
      (fun j => ((ArithmeticFunction.moebius j : ℤ) : ℂ)) q (σ := 1 / 2)
      (lo := -(T + V + 1 / 2)) (hi := T + V + 1 / 2) (by linarith) R t (fun _ => 1 / 2)
      (fun χ hχ => by have := abs_le.1 (ht χ hχ); constructor <;> linarith) (fun χ hχ => by norm_num)
    set S := (Ioc 1 (1 * X)).filter (fun j => blk 1 j = k) with hSdef
    have hSsub : S ⊆ Ioc (2 ^ k * 1) (2 * (2 ^ k * 1)) := block_sub le_rfl
    set P : ℕ := 2 ^ k * 1 with hPdef
    have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
    have hPXr : (P : ℝ) ≤ X := by rw [hPdef, mul_one]; exact_mod_cast hPX
    have hmass : ∑ j ∈ S, ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ 1 := by
      have hterm : ∀ j ∈ S, ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2
          ≤ 1 / P := by
        intro j hj
        obtain ⟨hj1, _⟩ := mem_Ioc.1 (hSsub hj)
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
        have hPj : (P : ℝ) ≤ j := by exact_mod_cast hj1.le
        have hμ : ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2 ≤ 1 := by
          rw [Complex.norm_intCast]
          have : |((ArithmeticFunction.moebius j : ℤ) : ℝ)| ≤ 1 := by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          nlinarith [abs_nonneg ((ArithmeticFunction.moebius j : ℤ) : ℝ)]
        have hj2 : ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / j := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hj0.le]
          norm_num
          rw [Real.rpow_neg_one]
        rw [hj2]
        calc ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2 * (1 / (j : ℝ)) ≤ 1 * (1 / P) := by
              gcongr
          _ = 1 / P := one_mul _
      have hcard : (S.card : ℝ) ≤ P := by
        have := card_le_card hSsub
        rw [Nat.card_Ioc] at this
        have e : 2 * P - P = P := by omega
        rw [e] at this
        exact_mod_cast this
      calc ∑ j ∈ S, ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2
          ≤ ∑ _j ∈ S, 1 / (P : ℝ) := sum_le_sum hterm
        _ = S.card * (1 / P) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ P * (1 / P) := by gcongr
        _ = 1 := by field_simp
    have hlP : Real.log P ≤ Real.log X := Real.log_le_log hP0 hPXr
    have hlP0 : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast hP)
    have hl2P : Real.log (2 * P) ≤ Real.log (2 * X) := Real.log_le_log (by positivity) (by linarith)
    have hl2P0 : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ P := by exact_mod_cast hP
      linarith)
    have hF : ∀ χ, Fmχ χ X k (t χ) = dp S (fun j => ((ArithmeticFunction.moebius j : ℤ) : ℂ) * χ j
        * (((j : ℝ) ^ (-(fun _ : DirichletCharacter ℂ q => (1 / 2 : ℝ)) χ) : ℝ) : ℂ)) (t χ) := fun χ => rfl
    simp_rw [hF]
    refine hLV.trans ?_
    have hmass0 : 0 ≤ ∑ j ∈ S, ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2
        * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := sum_nonneg fun _ _ => by positivity
    calc Real.exp 1 * (((q : ℝ) * (T + V + 1 / 2 - -(T + V + 1 / 2)) + 8 * P * (1 + Real.log P))
          * (2 + Real.log (2 * P) ^ 2)) * ∑ j ∈ S, ‖((ArithmeticFunction.moebius j : ℤ) : ℂ)‖ ^ 2
            * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2
        ≤ Real.exp 1 * (((q : ℝ) * (2 * T + 2 * V + 1) + 8 * X * (1 + Real.log X))
            * (2 + Real.log (2 * X) ^ 2)) * 1 := by
          have e : (q : ℝ) * (T + V + 1 / 2 - -(T + V + 1 / 2)) = q * (2 * T + 2 * V + 1) := by ring
          rw [e]
          gcongr
      _ = E := by rw [hE, mul_one]
  have hpt := fun χ => norm_mollχ_half_sq_le χ hX (t χ)
  calc ∑ χ ∈ R, ‖mollχ χ X (1 / 2 + (t χ : ℂ) * I)‖ ^ 2
      ≤ ∑ χ ∈ R, (2 + 2 * (K : ℝ) * ∑ k ∈ range K, ‖Fmχ χ X k (t χ)‖ ^ 2) := sum_le_sum fun χ _ => hpt χ
    _ = 2 * R.card + 2 * (K : ℝ) * ∑ k ∈ range K, ∑ χ ∈ R, ‖Fmχ χ X k (t χ)‖ ^ 2 := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, sum_comm]; ring
    _ ≤ 2 * q + 2 * (K : ℝ) * ∑ _k ∈ range K, E := by
        gcongr with k hk
        exact hblock k hk
    _ = 2 * q + 2 * (K : ℝ) ^ 2 * E := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ MV X * ((q : ℝ) * (T + 1 + V) + X) := by
        unfold MV
        rw [hE]
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
        have hb : (q : ℝ) * (2 * T + 2 * V + 1) + 8 * X * (1 + Real.log X)
            ≤ 8 * (1 + Real.log X) * ((q : ℝ) * (T + 1 + V) + X) := by
          nlinarith [mul_nonneg hq0 hT, mul_nonneg hq0 hV, mul_nonneg hq0 hlX, mul_nonneg (mul_nonneg hq0 hT) hlX,
            mul_nonneg (mul_nonneg hq0 hV) hlX]
        have hL0 : 0 ≤ 2 + Real.log (2 * X) ^ 2 := by positivity
        have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
        have h3 : 2 * (K : ℝ) ^ 2 * (Real.exp 1 * (((q : ℝ) * (2 * T + 2 * V + 1) + 8 * X * (1 + Real.log X))
            * (2 + Real.log (2 * X) ^ 2)))
            ≤ 2 * (K : ℝ) ^ 2 * (Real.exp 1 * ((8 * (1 + Real.log X) * ((q : ℝ) * (T + 1 + V) + X))
            * (2 + Real.log (2 * X) ^ 2))) := by gcongr
        nlinarith [mul_nonneg hq0 hT, mul_nonneg hq0 hV]

/-- **The integral class**: characters `χ ≠ 1` with a zero `ρ_χ = β_χ + iγ_χ`, `σ ≤ β_χ < 1`, `|γ_χ| ≤ T`, and
`|I_χ(ρ_χ)| ≥ ¼`, number at most `4A² MV(X)(q(T + 1) + X)` with `A = KG C_L Q^c Y^{½−σ}/δ`. The steps: the bound on
the line for each character; the sum over the class; `m ≤ λ/2 + m²/(2λ)` at `λ = 1/(2A)`; the mean value of `M_X`
over the characters. -/
theorem class2_count {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {CL : ℝ} (hCL1 : 1 ≤ CL)
    (hL : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ,
      ‖LFunction χ (1 / 2 + t * I)‖ ≤ CL * ((q : ℝ) * (|t| + 2)) ^ c)
    {X : ℕ} (hX : 1 ≤ X) {σ δ T Q Y : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hT : 0 ≤ T)
    (hQ : (q : ℝ) * (T + 2) ≤ Q) (hY : 1 ≤ Y)
    (Rs : Finset (DirichletCharacter ℂ q)) (β γ : DirichletCharacter ℂ q → ℝ)
    (hdet : ∀ χ ∈ Rs, χ ≠ 1 ∧ σ ≤ β χ ∧ β χ < 1 ∧ |γ χ| ≤ T ∧ LFunction χ ((β χ : ℂ) + γ χ * I) = 0
      ∧ 1 / 4 ≤ ‖Ivχ χ X Y ((β χ : ℂ) + γ χ * I)‖) :
    (Rs.card : ℝ) ≤ 4 * (KG * CL * Q ^ c * Y ^ (1 / 2 - σ) / δ) ^ 2 * MV X * ((q : ℝ) * (T + 1) + X) := by
  classical
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hQ0 : 0 < Q := by nlinarith
  set A := KG * CL * Q ^ c * Y ^ (1 / 2 - σ) / δ with hA
  have hA0 : 0 < A := by
    have := KG_pos
    have : (0 : ℝ) < CL := by linarith
    have : 0 < Y := by linarith
    positivity
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  set m : DirichletCharacter ℂ q → ℝ → ℝ := fun χ v => ‖mollχ χ X (1 / 2 + ((γ χ + v : ℝ) : ℂ) * I)‖ with hm
  have hmc : ∀ χ, Continuous (m χ) := fun χ =>
    ((differentiable_mollχ χ X).continuous.comp (by fun_prop)).norm
  have hmX : ∀ χ v, m χ v ≤ X := fun χ v => norm_mollχ_le_X χ X (by simp)
  have hm0 : ∀ χ v, 0 ≤ m χ v := fun χ v => norm_nonneg _
  have hint : ∀ χ, Integrable fun v => m χ v * wt v := by
    intro χ
    refine integrable_real_of_le ((hmc χ).mul continuous_wt) (K := X) fun v => ?_
    rw [abs_of_nonneg (mul_nonneg (hm0 χ v) (wt_pos v).le)]
    exact mul_le_mul (hmX χ v) (wt_le v) (wt_pos v).le (by positivity)
  -- (i) each character
  have hIv : ∀ χ ∈ Rs, 1 / 4 ≤ A / (2 * π) * ∫ v, m χ v * wt v := by
    intro χ hχ
    obtain ⟨hχ1, hσβ, hβ1, hγ, hz, hI⟩ := hdet χ hχ
    refine hI.trans ?_
    unfold Ivχ
    rw [norm_mul]
    have hc2 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hc2]
    have hle : ‖∫ v : ℝ, Gχ χ X Y ((β χ : ℂ) + γ χ * I)
        (((1 / 2 - ((β χ : ℂ) + γ χ * I).re : ℝ) : ℂ) + v * I)‖
        ≤ ∫ v, A * (m χ v * wt v) := by
      refine norm_integral_le_of_norm_le ((hint χ).const_mul A) (Eventually.of_forall fun v => ?_)
      have h := Gχ_left_le hc0 hc1 (by linarith) (hL χ hχ1) X hδ hσδ hσβ hβ1 hγ hQ hY hz v
      have hp : 0 < (1 + |v|) ^ 3 := by positivity
      change _ ≤ A * (‖mollχ χ X (1 / 2 + ((γ χ + v : ℝ) : ℂ) * I)‖ * ((1 + |v|) ^ 3)⁻¹)
      rw [← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ hp]
      exact h
    rw [integral_const_mul] at hle
    calc 1 / (2 * π) * ‖∫ v : ℝ, Gχ χ X Y ((β χ : ℂ) + γ χ * I)
          (((1 / 2 - ((β χ : ℂ) + γ χ * I).re : ℝ) : ℂ) + v * I)‖
        ≤ 1 / (2 * π) * (A * ∫ v, m χ v * wt v) := by gcongr
      _ = A / (2 * π) * ∫ v, m χ v * wt v := by ring
  -- (ii) the sum over the class
  have hsum1 : (Rs.card : ℝ) * (1 / 4) ≤ A / (2 * π) * ∫ v, ∑ χ ∈ Rs, m χ v * wt v := by
    rw [integral_finsetSum Rs fun χ _ => hint χ, mul_sum, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hIv
  -- (iii) pointwise: `m ≤ λ/2 + m²/(2λ)` at `λ = 1/(2A)`, and the mean value
  set K' := (Rs.card : ℝ) / (4 * A) + A * MV X * ((q : ℝ) * (T + 1) + X) with hK'
  have hpt : ∀ v : ℝ, ∑ χ ∈ Rs, m χ v * wt v ≤ K' * (1 + v ^ 2)⁻¹ := by
    intro v
    have hamgm : ∀ χ, m χ v ≤ 1 / (4 * A) + A * m χ v ^ 2 := by
      intro χ
      have e : 1 / (4 * A) + A * m χ v ^ 2 - m χ v = A * (m χ v - 1 / (2 * A)) ^ 2 := by
        field_simp; ring
      have : 0 ≤ A * (m χ v - 1 / (2 * A)) ^ 2 := by positivity
      linarith
    have hmv := mean_value_mollχ hX hT (abs_nonneg v) Rs (fun χ => γ χ + v)
      (fun χ hχ => by
        have h1 := abs_add_le (γ χ) v
        have h2 := (hdet χ hχ).2.2.2.1
        linarith)
    have hsumm : ∑ χ ∈ Rs, m χ v
        ≤ Rs.card * (1 / (4 * A)) + A * (MV X * ((q : ℝ) * (T + 1 + |v|) + X)) := by
      calc ∑ χ ∈ Rs, m χ v ≤ ∑ χ ∈ Rs, (1 / (4 * A) + A * m χ v ^ 2) := sum_le_sum fun χ _ => hamgm χ
        _ = Rs.card * (1 / (4 * A)) + A * ∑ χ ∈ Rs, m χ v ^ 2 := by
            rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
        _ ≤ Rs.card * (1 / (4 * A)) + A * (MV X * ((q : ℝ) * (T + 1 + |v|) + X)) := by
            gcongr
    have hMV0 : 0 ≤ MV X := by unfold MV; have := Real.log_nonneg hXr; positivity
    have hw1 := wt_le v
    have hw2 := wt_mul_le v
    have hwp := (wt_pos v).le
    have hb : (q : ℝ) * (T + 1 + |v|) + X ≤ ((q : ℝ) * (T + 1) + X) * (1 + |v|) := by
      nlinarith [abs_nonneg v, mul_nonneg (mul_nonneg hq0 hT) (abs_nonneg v),
        mul_nonneg (Nat.cast_nonneg X : (0 : ℝ) ≤ X) (abs_nonneg v)]
    calc ∑ χ ∈ Rs, m χ v * wt v = wt v * ∑ χ ∈ Rs, m χ v := by
          rw [mul_sum]; exact sum_congr rfl fun χ _ => by ring
      _ ≤ wt v * (Rs.card * (1 / (4 * A)) + A * (MV X * ((q : ℝ) * (T + 1 + |v|) + X))) := by gcongr
      _ = Rs.card * (1 / (4 * A)) * wt v + A * MV X * (wt v * ((q : ℝ) * (T + 1 + |v|) + X)) := by ring
      _ ≤ Rs.card * (1 / (4 * A)) * (1 + v ^ 2)⁻¹ + A * MV X * (((q : ℝ) * (T + 1) + X) * (1 + v ^ 2)⁻¹) := by
          have hq : wt v * ((q : ℝ) * (T + 1 + |v|) + X) ≤ ((q : ℝ) * (T + 1) + X) * (1 + v ^ 2)⁻¹ := by
            calc wt v * ((q : ℝ) * (T + 1 + |v|) + X) ≤ wt v * (((q : ℝ) * (T + 1) + X) * (1 + |v|)) := by
                  gcongr
              _ = ((q : ℝ) * (T + 1) + X) * (wt v * (1 + |v|)) := by ring
              _ ≤ ((q : ℝ) * (T + 1) + X) * (1 + v ^ 2)⁻¹ := by gcongr
          have hcoef : 0 ≤ A * MV X := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left hw1 (by positivity))
            (mul_le_mul_of_nonneg_left hq hcoef)
      _ = K' * (1 + v ^ 2)⁻¹ := by rw [hK']; ring
  -- (iv) integrate
  have hint_sum : Integrable fun v => ∑ χ ∈ Rs, m χ v * wt v := integrable_finsetSum Rs fun χ _ => hint χ
  have hI2 : ∫ v, ∑ χ ∈ Rs, m χ v * wt v ≤ K' * π := by
    calc ∫ v, ∑ χ ∈ Rs, m χ v * wt v ≤ ∫ v, K' * (1 + v ^ 2)⁻¹ :=
          integral_mono hint_sum (integrable_inv_one_add_sq.const_mul K') hpt
      _ = K' * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hpi : 0 < π := Real.pi_pos
  have hfin : (Rs.card : ℝ) * (1 / 4) ≤ A / 2 * K' := by
    calc (Rs.card : ℝ) * (1 / 4) ≤ A / (2 * π) * ∫ v, ∑ χ ∈ Rs, m χ v * wt v := hsum1
      _ ≤ A / (2 * π) * (K' * π) := by gcongr
      _ = A / 2 * K' := by field_simp
  rw [hK'] at hfin
  have e : A / 2 * ((Rs.card : ℝ) / (4 * A) + A * MV X * ((q : ℝ) * (T + 1) + X))
      = (Rs.card : ℝ) / 8 + A ^ 2 * MV X * ((q : ℝ) * (T + 1) + X) / 2 := by
    field_simp; ring
  rw [e] at hfin
  linarith

/-! ### One modulus -/

open scoped Classical in
/-- **The two classes at one modulus.** For `σ ≥ ½ + δ`, `T ≥ 2` and `Q ≥ q(T + 6)`, with `X = ⌊Q⌋`,
`Y = Q^{1+2c}` and `N = ⌊22Y log Y/X⌋ + 1`: every character `χ ≠ 1` with a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T` falls, at one such zero, in one of the two classes of `dichotomy`, counted by `class1_count` and
`class2_count`. -/
theorem count_nontrivial {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {CL : ℝ} (hCL1 : 1 ≤ CL)
    (hL : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ,
      ‖LFunction χ (1 / 2 + t * I)‖ ≤ CL * ((q : ℝ) * (|t| + 2)) ^ c)
    {σ δ T Q : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hσ1 : σ ≤ 1) (hT : 2 ≤ T)
    (hQ : (q : ℝ) * (T + 6) ≤ Q) :
    ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ ((Nat.log 2 (Nw c Q) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2 * (32 * Real.exp 1
          * (1 + Real.log (2 * (Xw Q : ℝ) * (Nw c Q))) ^ 6
          * (Q * ((Xw Q : ℝ)) ^ (1 - 2 * σ) + ((Xw Q : ℝ) * (Nw c Q)) ^ (2 - 2 * σ)))
        + 4 * (KG * CL * Q ^ c * (Yw c Q) ^ (1 / 2 - σ) / δ) ^ 2 * MV (Xw Q)
          * ((q : ℝ) * (T + 1) + (Xw Q)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ8 : 8 ≤ Q := by nlinarith
  have hT0 : 0 ≤ T := by linarith
  have hX : 1 ≤ Xw Q := Xw_one hQ8
  have hN : 1 ≤ Nw c Q := Nw_one
  have hY8 : 8 ≤ Yw c Q := le_trans hQ8 (Yw_ge hc0 hQ8)
  have hY0 : 0 < Yw c Q := by linarith
  have hM : 22 * Yw c Q * Real.log (Yw c Q) ≤ ((Xw Q * Nw c Q : ℕ) : ℝ) := XN_ge hQ8
  set Z := univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
    ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0 with hZ
  -- a zero for each character
  have hch : ∀ χ ∈ Z, ∃ s : ℂ, χ ≠ 1 ∧ σ ≤ s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
    intro χ hχ
    obtain ⟨hχ1, s, hs1, hs2, hs3⟩ := (mem_filter.1 hχ).2
    refine ⟨s, hχ1, hs1, ?_, hs2, hs3⟩
    by_contra hge
    push Not at hge
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hge hs3
  choose! s0 hs0 using hch
  have hz0 : ∀ χ ∈ Z, LFunction χ (((s0 χ).re : ℂ) + (s0 χ).im * I) = 0 := fun χ hχ => by
    rw [Complex.re_add_im]; exact (hs0 χ hχ).2.2.2.2
  have hdich : ∀ χ ∈ Z, 1 / 4 ≤ ‖Pvχ χ (Xw Q) (Nw c Q) (Yw c Q) (s0 χ).re (s0 χ).im‖
      ∨ 1 / 4 ≤ ‖Ivχ χ (Xw Q) (Yw c Q) (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ := by
    intro χ hχ
    obtain ⟨hχ1, h1, h2, _, _⟩ := hs0 χ hχ
    exact dichotomy hχ1 hX hN hY8 hM (by linarith) h2 (hz0 χ hχ)
  set Z1 := Z.filter fun χ => 1 / 4 ≤ ‖Pvχ χ (Xw Q) (Nw c Q) (Yw c Q) (s0 χ).re (s0 χ).im‖ with hZ1
  set Z2 := Z.filter fun χ => 1 / 4 ≤ ‖Ivχ χ (Xw Q) (Yw c Q) (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ with hZ2
  have hcover : Z ⊆ Z1 ∪ Z2 := by
    intro χ hχ
    rcases hdich χ hχ with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨hχ, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨hχ, h⟩)
  have hc1' := class1_count (by linarith : 1 / 2 ≤ σ) hσ1 hT0 (by nlinarith : (q : ℝ) * (2 * T + 1) ≤ 2 * Q)
    hX hN hY0 (by norm_num : (0 : ℝ) < 1 / 4) Z1 (fun χ => (s0 χ).im) (fun χ => (s0 χ).re)
    (fun χ hχ => (hs0 χ (mem_filter.1 hχ).1).2.2.2.1)
    (fun χ hχ => ⟨(hs0 χ (mem_filter.1 hχ).1).2.1, by linarith [(hs0 χ (mem_filter.1 hχ).1).2.2.1]⟩)
    (fun χ hχ => (mem_filter.1 hχ).2)
  have hc2' := class2_count hc0 hc1 hCL1 hL hX hδ hσδ hT0 (by nlinarith : (q : ℝ) * (T + 2) ≤ Q)
    (by linarith : 1 ≤ Yw c Q) Z2 (fun χ => (s0 χ).re) (fun χ => (s0 χ).im)
    (fun χ hχ => by
      obtain ⟨hχ1, h1, h2, h3, _⟩ := hs0 χ (mem_filter.1 hχ).1
      exact ⟨hχ1, h1, h2, h3, hz0 χ (mem_filter.1 hχ).1, (mem_filter.1 hχ).2⟩)
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card := by exact_mod_cast card_union_le Z1 Z2
    _ ≤ _ := add_le_add hc1' hc2'

/-! ### The bound at `Q` -/

/-- The polynomial class at `X = ⌊Q⌋`, `Y = Q^{1+2c}`: at most `16·13³·96·9⁶·71 (log Q)¹⁰ Q^{(2+4c)(1−σ)}`. -/
theorem bound_class1 {c σ Q : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hQ : 8 ≤ Q) :
    ((Nat.log 2 (Nw c Q) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2 * (32 * Real.exp 1
      * (1 + Real.log (2 * (Xw Q : ℝ) * (Nw c Q))) ^ 6
      * (Q * ((Xw Q : ℝ)) ^ (1 - 2 * σ) + ((Xw Q : ℝ) * (Nw c Q)) ^ (2 - 2 * σ)))
    ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log Q ^ 10 * Q ^ ((2 + 4 * c) * (1 - σ)) := by
  have hL := log_ge_two hQ
  have hK := bound_K hc0 hc1 hQ
  have hl := bound_ell hc0 hc1 hQ
  have hS := bound_S1 hc0 hc1 hσ hσ1 hQ
  have he : 32 * Real.exp 1 ≤ 96 := by have := Real.exp_one_lt_d9; linarith
  have hK0 : (0 : ℝ) ≤ ((Nat.log 2 (Nw c Q) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hX1 : (1 : ℝ) ≤ Xw Q := by exact_mod_cast Xw_one hQ
  have hN1 : (1 : ℝ) ≤ Nw c Q := by exact_mod_cast (Nw_one (c := c) (U := Q))
  have hl0 : 0 ≤ 1 + Real.log (2 * (Xw Q : ℝ) * (Nw c Q)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (Xw Q : ℝ) * (Nw c Q) by nlinarith)
    linarith
  have hS0 : 0 ≤ Q * ((Xw Q : ℝ)) ^ (1 - 2 * σ) + ((Xw Q : ℝ) * (Nw c Q)) ^ (2 - 2 * σ) := by
    have : 0 ≤ Q := by linarith
    positivity
  have e16 : ∀ x : ℝ, x / (1 / 4) ^ 2 = 16 * x := fun x => by norm_num [div_eq_mul_inv]; ring
  rw [e16]
  calc 16 * ((Nat.log 2 (Nw c Q) + 1 : ℕ) : ℝ) ^ 3
        * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw Q : ℝ) * (Nw c Q))) ^ 6
          * (Q * ((Xw Q : ℝ)) ^ (1 - 2 * σ) + ((Xw Q : ℝ) * (Nw c Q)) ^ (2 - 2 * σ)))
      ≤ 16 * (13 * Real.log Q) ^ 3 * (96 * (9 * Real.log Q) ^ 6
          * (71 * Real.log Q * Q ^ ((2 + 4 * c) * (1 - σ)))) := by gcongr
    _ = 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log Q ^ 10 * Q ^ ((2 + 4 * c) * (1 - σ)) := by ring

/-- `A = KG C_L Q^c Y^{½−σ}/δ` at `Y = Q^{1+2c}`: `A² = (KG C_L/δ)² Q^{(2+4c)(1−σ)−1}`. -/
theorem sq_Aχ {c CL δ σ Q : ℝ} (hQ : 0 < Q) :
    (KG * CL * Q ^ c * (Yw c Q) ^ (1 / 2 - σ) / δ) ^ 2 = (KG * CL / δ) ^ 2 * Q ^ ((2 + 4 * c) * (1 - σ) - 1) := by
  have h2 : (Yw c Q) ^ (1 / 2 - σ) = Q ^ ((1 + 2 * c) * (1 / 2 - σ)) := by
    unfold Yw; rw [← Real.rpow_mul hQ.le]
  have h3 : Q ^ c * Q ^ ((1 + 2 * c) * (1 / 2 - σ)) = Q ^ (((2 + 4 * c) * (1 - σ) - 1) / 2) := by
    rw [← Real.rpow_add hQ]; congr 1; ring
  have h4 : (Q ^ (((2 + 4 * c) * (1 - σ) - 1) / 2)) ^ 2 = Q ^ ((2 + 4 * c) * (1 - σ) - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]; congr 1; push_cast; ring
  calc (KG * CL * Q ^ c * (Yw c Q) ^ (1 / 2 - σ) / δ) ^ 2
      = ((KG * CL / δ) * (Q ^ c * Q ^ ((1 + 2 * c) * (1 / 2 - σ)))) ^ 2 := by rw [h2]; ring
    _ = (KG * CL / δ) ^ 2 * (Q ^ (((2 + 4 * c) * (1 - σ) - 1) / 2)) ^ 2 := by rw [h3]; ring
    _ = (KG * CL / δ) ^ 2 * Q ^ ((2 + 4 * c) * (1 - σ) - 1) := by rw [h4]

omit [NeZero q] in
/-- The integral class at `X = ⌊Q⌋`, `Y = Q^{1+2c}`, `q(T + 1) ≤ Q`: at most
`6400 (KG C_L/δ)² (log Q)⁵ Q^{(2+4c)(1−σ)}`. -/
theorem bound_class2 {c CL δ σ T Q : ℝ} (hQ : 8 ≤ Q) (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 1) ≤ Q) :
    4 * (KG * CL * Q ^ c * (Yw c Q) ^ (1 / 2 - σ) / δ) ^ 2 * MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q))
      ≤ 6400 * (KG * CL / δ) ^ 2 * Real.log Q ^ 5 * Q ^ ((2 + 4 * c) * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  rw [sq_Aχ hQ0]
  have hMV := bound_MV hQ
  have hMV0 : 0 ≤ MV (Xw Q) := by
    unfold MV; have := Real.log_nonneg (by exact_mod_cast Xw_one hQ : (1 : ℝ) ≤ Xw Q); positivity
  have hXQ := Xw_le hQ
  have hW : (q : ℝ) * (T + 1) + (Xw Q) ≤ 2 * Q := by linarith
  have hW0 : 0 ≤ (q : ℝ) * (T + 1) + (Xw Q) :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg q) (by linarith)) (Nat.cast_nonneg _)
  have hE : Q ^ ((2 + 4 * c) * (1 - σ) - 1) * Q = Q ^ ((2 + 4 * c) * (1 - σ)) := by
    rw [← Real.rpow_add_one hQ0.ne']; congr 1; ring
  have hp : 0 ≤ (KG * CL / δ) ^ 2 * Q ^ ((2 + 4 * c) * (1 - σ) - 1) := by positivity
  have h800 : 0 ≤ 4 * ((KG * CL / δ) ^ 2 * Q ^ ((2 + 4 * c) * (1 - σ) - 1)) * (800 * Real.log Q ^ 5) :=
    mul_nonneg (by positivity) (mul_nonneg (by norm_num) (pow_nonneg (by linarith [log_ge_two hQ]) 5))
  calc 4 * ((KG * CL / δ) ^ 2 * Q ^ ((2 + 4 * c) * (1 - σ) - 1)) * MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q))
      ≤ 4 * ((KG * CL / δ) ^ 2 * Q ^ ((2 + 4 * c) * (1 - σ) - 1)) * (800 * Real.log Q ^ 5) * (2 * Q) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hMV (by positivity)) hW hW0 h800
    _ = 6400 * (KG * CL / δ) ^ 2 * Real.log Q ^ 5 * (Q ^ ((2 + 4 * c) * (1 - σ) - 1) * Q) := by ring
    _ = 6400 * (KG * CL / δ) ^ 2 * Real.log Q ^ 5 * Q ^ ((2 + 4 * c) * (1 - σ)) := by rw [hE]

/-! ### Density over the characters -/

/-- The constant of `charDensity_of_LBound`. -/
def CD (CL δ : ℝ) : ℝ := 2 ^ 10 + 64 * 3 ^ 10 * (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + 6400 * (KG * CL / δ) ^ 2)

theorem CD_nonneg (CL δ : ℝ) : 0 ≤ CD CL δ := by unfold CD; positivity

open scoped Classical in
/-- **Density over the characters from a uniform critical-line bound.** If `|L(½ + it, χ)| ≤ C_L(q(|t| + 2))^c` for
every character `χ ≠ 1` modulo every `q ≥ 1`, with `0 < c ≤ 1`, then `CharDensity (2 + 4c) 10 C`. Below
`σ = ½ + c/(1 + 2c)` (where `(2 + 4c)(1 − σ) ≥ 1`) at most `q ≤ qT` characters are counted; above it, the trivial
character and `count_nontrivial` at `Q = q(T + 6) ≤ 4qT`, with `log Q ≤ 3 log qT`. -/
theorem charDensity_of_LBound {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {CL : ℝ}
    (hL : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ,
      ‖LFunction χ (1 / 2 + t * I)‖ ≤ CL * ((q : ℝ) * (|t| + 2)) ^ c) :
    CharDensity (2 + 4 * c) 10 (CD (max CL 1) (c / (1 + 2 * c))) := by
  intro q _ σ T hσ hσ1 hT
  set C' := max CL 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hL' : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ,
      ‖LFunction χ (1 / 2 + t * I)‖ ≤ C' * ((q : ℝ) * (|t| + 2)) ^ c := fun χ hχ t =>
    (hL q χ hχ t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  set δ₀ := c / (1 + 2 * c) with hδ₀
  have hδ₀0 : 0 < δ₀ := by positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ q * T := by nlinarith
  set ℓ := Real.log ((q : ℝ) * T) with hℓdef
  have hℓ : 1 / 2 ≤ ℓ := half_le_log hqT
  set E := (2 + 4 * c) * (1 - σ) with hE
  have hE0 : 0 ≤ E := by rw [hE]; nlinarith
  have hE3 : E ≤ 3 := by rw [hE]; nlinarith
  have hpowE : 0 ≤ ((q : ℝ) * T) ^ E := by positivity
  have e10 : ℓ ^ (10 : ℝ) = ℓ ^ (10 : ℕ) := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e10]
  have hCD : 2 ^ 10 ≤ CD C' δ₀ := by
    unfold CD; have : 0 ≤ (KG * C' / δ₀) ^ 2 := sq_nonneg _; nlinarith
  have h2ℓ : 1 ≤ 2 ^ 10 * ℓ ^ 10 := by
    have h1 : 1 ≤ (2 * ℓ) ^ 10 := one_le_pow₀ (by linarith)
    calc (1 : ℝ) ≤ (2 * ℓ) ^ 10 := h1
      _ = 2 ^ 10 * ℓ ^ 10 := by ring
  have hCℓ : 1 ≤ CD C' δ₀ * ℓ ^ 10 := h2ℓ.trans (by gcongr)
  rcases lt_or_ge σ (1 / 2 + δ₀) with hsmall | hbig
  · -- below `½ + δ₀`: at most `q ≤ qT ≤ (qT)^E` characters
    have hE1 : 1 ≤ E := by
      have e : (2 + 4 * c) * (1 / 2 - δ₀) = 1 := by rw [hδ₀]; field_simp; ring
      rw [hE]; nlinarith
    calc _ ≤ (q : ℝ) := card_chars_le _
      _ ≤ (q : ℝ) * T := by nlinarith
      _ = ((q : ℝ) * T) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((q : ℝ) * T) ^ E := Real.rpow_le_rpow_of_exponent_le (by linarith) hE1
      _ = ((q : ℝ) * T) ^ E * 1 := (mul_one _).symm
      _ ≤ ((q : ℝ) * T) ^ E * (CD C' δ₀ * ℓ ^ 10) := by gcongr
      _ = CD C' δ₀ * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by ring
  · -- above: the trivial character, and `count_nontrivial` at `Q = q(T + 6)`
    set Q := (q : ℝ) * (T + 6) with hQdef
    have hQ8 : 8 ≤ Q := by nlinarith
    have hQ4 : Q ≤ 4 * ((q : ℝ) * T) := by nlinarith
    have hcount := count_nontrivial hc0.le hc1 hC'1 hL' hδ₀0 hbig hσ1 hT (le_refl Q)
    have hb1 := bound_class1 hc0.le hc1 (by linarith) hσ1 hQ8
    have hb2 := bound_class2 (q := q) (c := c) (CL := C') (δ := δ₀) (σ := σ) hQ8 (by linarith)
      (by nlinarith : (q : ℝ) * (T + 1) ≤ Q)
    have hL0 : 2 ≤ Real.log Q := log_ge_two hQ8
    have hLQ : Real.log Q ≤ 3 * ℓ := by
      have h2 : Real.log Q ≤ Real.log (4 * ((q : ℝ) * T)) := Real.log_le_log (by linarith) hQ4
      rw [Real.log_mul (by norm_num) (by linarith : (0 : ℝ) < q * T).ne'] at h2
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have h5 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hqT
      linarith
    have hQE : Q ^ E ≤ 64 * ((q : ℝ) * T) ^ E := by
      calc Q ^ E ≤ (4 * ((q : ℝ) * T)) ^ E := Real.rpow_le_rpow (by linarith) hQ4 hE0
        _ = 4 ^ E * ((q : ℝ) * T) ^ E := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ 4 ^ (3 : ℝ) * ((q : ℝ) * T) ^ E :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE3) hpowE
        _ = 64 * ((q : ℝ) * T) ^ E := by norm_num
    have hsub : (univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)
        ⊆ insert 1 (univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
          ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) := by
      intro χ hχ
      rw [mem_insert]
      by_cases h1 : χ = 1
      · exact Or.inl h1
      · exact Or.inr (mem_filter.2 ⟨mem_univ _, h1, (mem_filter.1 hχ).2⟩)
    have hcard := (card_le_card hsub).trans (card_insert_le _ _)
    set Mc := 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + 6400 * (KG * C' / δ₀) ^ 2 with hMc
    have hMc0 : 0 ≤ Mc := by positivity
    have h510 : Real.log Q ^ 5 ≤ Real.log Q ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hQE0 : 0 ≤ Q ^ E := by positivity
    have hZ : ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
          ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
        ≤ Mc * Real.log Q ^ 10 * Q ^ E := by
      refine hcount.trans ?_
      calc _ ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log Q ^ 10 * Q ^ E
            + 6400 * (KG * C' / δ₀) ^ 2 * Real.log Q ^ 5 * Q ^ E := add_le_add hb1 hb2
        _ ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log Q ^ 10 * Q ^ E
            + 6400 * (KG * C' / δ₀) ^ 2 * Real.log Q ^ 10 * Q ^ E := by gcongr
        _ = Mc * Real.log Q ^ 10 * Q ^ E := by rw [hMc]; ring
    have hL10 : Real.log Q ^ 10 ≤ 3 ^ 10 * ℓ ^ 10 := by
      calc Real.log Q ^ 10 ≤ (3 * ℓ) ^ 10 := by gcongr
        _ = 3 ^ 10 * ℓ ^ 10 := by ring
    have h1 : 1 ≤ ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) hE0) h2ℓ
    have hF : ((univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
        ≤ ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
          ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) + 1 := by exact_mod_cast hcard
    calc _ ≤ _ := hF
      _ ≤ Mc * Real.log Q ^ 10 * Q ^ E + ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := add_le_add hZ h1
      _ ≤ Mc * (3 ^ 10 * ℓ ^ 10) * (64 * ((q : ℝ) * T) ^ E) + ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := by
          gcongr
      _ = CD C' δ₀ * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by simp only [hMc, CD]; ring

/-- **A uniform bound on the critical line**: `|L(½ + it, χ)| ≤ C(q(|t| + 2))^c` for every character `χ ≠ 1`
modulo every `q ≥ 1`. -/
def CritBoundχ (c : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ,
    ‖LFunction χ (1 / 2 + t * I)‖ ≤ C * ((q : ℝ) * (|t| + 2)) ^ c

theorem charDensity_of_critBound {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (h : CritBoundχ c) :
    ∃ C : ℝ, 0 ≤ C ∧ CharDensity (2 + 4 * c) 10 C := by
  obtain ⟨CL, hL⟩ := h
  exact ⟨_, CD_nonneg _ _, charDensity_of_LBound hc0 hc1 hL⟩

/-- **Linnik's theorem from a uniform critical-line bound**: `CritBoundχ c` with `0 < c ≤ 1` gives, for every
`η > 0`, a prime `p ≡ a (mod q)` with `p ≤ K q^{2+4c+η}`. -/
theorem linnik_of_critBound {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (h : CritBoundχ c) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (2 + 4 * c + η) := by
  obtain ⟨C, hC0, hD⟩ := charDensity_of_critBound hc0 hc1 h
  exact linnik_of_charDensity (by linarith) (by norm_num) hC0 hD hη

end LinnikDensity

#print axioms LinnikDensity.class1_count
#print axioms LinnikDensity.class2_count
#print axioms LinnikDensity.count_nontrivial
#print axioms LinnikDensity.charDensity_of_LBound
#print axioms LinnikDensity.charDensity_of_critBound
#print axioms LinnikDensity.linnik_of_critBound
