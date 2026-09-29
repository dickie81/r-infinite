/-
# Vinogradov's mean value theorem, step I.3a: p-adic rigidity (round 196)

Plain statement. Take a prime `p > k` and two integer `k`-tuples `x, y` that agree modulo `p`,
where the coordinates of `x` are distinct modulo `p`. If their power sums in degrees `1..k`
agree modulo `p^M`, then `x ≡ y` modulo `p^M` coordinate by coordinate (`rigid`).

In words: once the residues mod `p` are fixed and distinct, the power sums pin down every
further `p`-adic digit. The proof lifts one power of `p` at a time (`lift_step`). Writing
`y = x + pᵐz`, the degree-`j` congruence becomes `j·Σ xᵢ^{j−1} zᵢ ≡ 0 (mod p)`. The
Vandermonde matrix of the distinct residues is invertible mod `p`, so `z ≡ 0`.

This is the engine of Linnik's lemma, which counts "well-conditioned" solutions in the classical
p-adic proof of Vinogradov's mean value theorem.
-/
import Mathlib

open Finset

namespace VinoPadic

/-- First-order expansion with a `d²` remainder: `(a + d·b)^j = a^j + j·a^{j−1}·d·b + d²·r`. -/
lemma pow_add_mul_expand (a b d : ℤ) (j : ℕ) :
    ∃ r : ℤ, (a + d * b) ^ j = a ^ j + j * a ^ (j - 1) * (d * b) + d ^ 2 * r := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨j * a ^ (j - 1) * b ^ 2 + r * (a + d * b), ?_⟩
    rw [pow_succ, hr]
    rcases j with _ | j
    · simp; ring
    · simp only [Nat.add_sub_cancel]; push_cast; ring

/-- **One `p`-adic digit.** If `x ≡ y (mod pᵐ)`, `m ≥ 1`, the residues of `x` are distinct
mod `p > k`, and the power sums agree mod `p^{m+1}` in degrees `1..k`, then `x ≡ y (mod p^{m+1})`. -/
theorem lift_step {k p m : ℕ} (hp : p.Prime) (hpk : k < p) (hm : 1 ≤ m) (x y : Fin k → ℤ)
    (hdist : Function.Injective fun i => (x i : ZMod p))
    (hxy : ∀ i, (p : ℤ) ^ m ∣ y i - x i)
    (hsum : ∀ j ∈ Icc 1 k, (p : ℤ) ^ (m + 1) ∣ ∑ i, y i ^ j - ∑ i, x i ^ j) :
    ∀ i, (p : ℤ) ^ (m + 1) ∣ y i - x i := by
  have : Fact p.Prime := ⟨hp⟩
  set d : ℤ := (p : ℤ) ^ m with hd
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  choose z hz using hxy
  have hy : ∀ i, y i = x i + d * z i := fun i => by linarith [hz i]
  have hlin : ∀ j ∈ Icc 1 k, (p : ℤ) ∣ (j : ℤ) * ∑ i, x i ^ (j - 1) * z i := by
    intro j hj
    have hexp : ∀ i, ∃ r, y i ^ j = x i ^ j + j * x i ^ (j - 1) * (d * z i) + d ^ 2 * r :=
      fun i => by rw [hy i]; exact pow_add_mul_expand _ _ _ _
    choose r hr using hexp
    have hdiff : ∑ i, y i ^ j - ∑ i, x i ^ j =
        d * ((j : ℤ) * ∑ i, x i ^ (j - 1) * z i) + d ^ 2 * ∑ i, r i := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro i _
      rw [hr]; ring
    have h2 : (p : ℤ) ^ (m + 1) ∣ d ^ 2 * ∑ i, r i := by
      apply Dvd.dvd.mul_right
      rw [hd, ← pow_mul]
      exact pow_dvd_pow _ (by omega)
    have h3 : (p : ℤ) ^ (m + 1) ∣ d * ((j : ℤ) * ∑ i, x i ^ (j - 1) * z i) := by
      have := hsum j hj
      rw [hdiff] at this
      exact (dvd_add_left h2).mp this
    rw [pow_succ] at h3
    exact (mul_dvd_mul_iff_left (pow_ne_zero m hp0)).mp h3
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hlin' : ∀ e : Fin k, ((∑ i, x i ^ (e : ℕ) * z i : ℤ) : ZMod p) = 0 := by
    intro e
    have h := hlin ((e : ℕ) + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
    simp only [Nat.add_sub_cancel] at h
    have hpj : ¬ (p : ℤ) ∣ (((e : ℕ) + 1 : ℕ) : ℤ) := by
      intro hdv
      have h1 := Int.natCast_dvd_natCast.mp hdv
      have := Nat.le_of_dvd (by omega) h1
      omega
    have h' : (p : ℤ) ∣ ∑ i, x i ^ (e : ℕ) * z i := by
      rcases hprime.dvd_or_dvd (by exact_mod_cast h) with h1 | h1
      · exact absurd h1 hpj
      · exact h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h'
  set v : Fin k → ZMod p := fun i => (x i : ZMod p) with hv
  set w : Fin k → ZMod p := fun i => (z i : ZMod p) with hw
  have hvec : Matrix.vecMul w (Matrix.vandermonde v) = 0 := by
    funext e
    have := hlin' e
    push_cast at this
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply, hv, hw]
    rw [← this]
    apply sum_congr rfl
    intro i _
    ring
  have hw0 := Matrix.eq_zero_of_vecMul_eq_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hdist) hvec
  intro i
  have hzi : (p : ℤ) ∣ z i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (congrFun hw0 i)
  rw [hz i, pow_succ]
  exact mul_dvd_mul_left _ hzi

/-- **p-adic rigidity.** Distinct residues mod `p > k`, agreement mod `p`, and power sums agreeing
mod `p^M` in degrees `1..k` force `x ≡ y (mod p^M)`. -/
theorem rigid {k p M : ℕ} (hp : p.Prime) (hpk : k < p) (hM : 1 ≤ M) (x y : Fin k → ℤ)
    (hdist : Function.Injective fun i => (x i : ZMod p))
    (h1 : ∀ i, (p : ℤ) ∣ y i - x i)
    (hsum : ∀ j ∈ Icc 1 k, (p : ℤ) ^ M ∣ ∑ i, y i ^ j - ∑ i, x i ^ j) :
    ∀ i, (p : ℤ) ^ M ∣ y i - x i := by
  induction M, hM using Nat.le_induction with
  | base => simpa using h1
  | succ m hm ih =>
    have ih' := ih (fun j hj => (pow_dvd_pow _ (Nat.le_succ m)).trans (hsum j hj))
    exact lift_step hp hpk hm x y hdist ih' hsum

/-! ## The exponent in Linnik's lemma (the lemma itself is `VinoStep.linnikZ`) -/

/-- The exponent in Linnik's lemma: `∑_{j=1}^{k} (k − j) = k(k−1)/2`. -/
lemma linnik_exponent (p k : ℕ) : ∏ e : Fin k, p ^ (k - (e + 1)) = p ^ (k * (k - 1) / 2) := by
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun e => k - (e + 1)),
    ← Finset.sum_range_id]
  congr 1
  rw [← Finset.sum_range_reflect]
  apply sum_congr rfl
  intro e he
  rw [mem_range] at he
  omega

end VinoPadic
