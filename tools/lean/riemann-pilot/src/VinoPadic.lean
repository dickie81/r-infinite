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

/-! ## Linnik's lemma: counting well-conditioned solutions -/

/-- Residues below `p^k` in a fixed class mod `p^j` (with `j ≤ k`): at most `p^{k−j}`. -/
lemma card_residue_le (p k j c : ℕ) (hp : 0 < p) (hjk : j ≤ k) :
    ((range (p ^ k)).filter fun v => v ≡ c [MOD p ^ j]).card ≤ p ^ (k - j) := by
  have hpj : 0 < p ^ j := pow_pos hp j
  calc ((range (p ^ k)).filter fun v => v ≡ c [MOD p ^ j]).card
      ≤ (range (p ^ (k - j))).card := by
        refine card_le_card_of_injOn (fun v => v / p ^ j) ?_ ?_
        · intro v hv
          rw [coe_filter, Set.mem_ofPred_eq, mem_range] at hv
          rw [mem_coe, mem_range, Nat.div_lt_iff_lt_mul hpj, ← pow_add, Nat.sub_add_cancel hjk]
          exact hv.1
        · intro v hv w hw hvw
          rw [coe_filter, Set.mem_ofPred_eq] at hv hw
          have hm : v % p ^ j = w % p ^ j := hv.2.trans hw.2.symm
          rw [← Nat.div_add_mod v (p ^ j), ← Nat.div_add_mod w (p ^ j)]
          simp only at hvw
          rw [hvw, hm]
    _ = p ^ (k - j) := card_range _

/-- **Linnik's lemma.** Fix a prime `p > k`, residues `a₁, …, a_k` distinct mod `p`, and targets
`c_j`. The tuples `x ∈ [0, p^k)^k` with `x ≡ a (mod p)` and `Σ xᵢʲ ≡ c_j (mod p^j)` for
`j = 1..k` number at most `∏_{j=1}^{k} p^{k−j} = p^{k(k−1)/2}`. -/
theorem linnik {k p : ℕ} (hp : p.Prime) (hpk : k < p) (a : Fin k → ℕ)
    (hdist : Function.Injective fun i => (a i : ZMod p)) (c : ℕ → ℕ) :
    ((Fintype.piFinset fun _ : Fin k => range (p ^ k)).filter fun x =>
        (∀ i, x i ≡ a i [MOD p]) ∧ ∀ j ∈ Icc 1 k, ∑ i, x i ^ j ≡ c j [MOD p ^ j]).card ≤
      ∏ e : Fin k, p ^ (k - (e + 1)) := by
  set L := (Fintype.piFinset fun _ : Fin k => range (p ^ k)).filter fun x =>
    (∀ i, x i ≡ a i [MOD p]) ∧ ∀ j ∈ Icc 1 k, ∑ i, x i ^ j ≡ c j [MOD p ^ j] with hL
  set T := Fintype.piFinset fun e : Fin k =>
    (range (p ^ k)).filter fun v => v ≡ c (e + 1) [MOD p ^ ((e : ℕ) + 1)] with hT
  have hp0 : 0 < p := hp.pos
  have hTcard : T.card ≤ ∏ e : Fin k, p ^ (k - (e + 1)) := by
    rw [hT, Fintype.card_piFinset]
    exact Finset.prod_le_prod fun e _ => card_residue_le p k _ _ hp0 (by omega)
  refine le_trans ?_ hTcard
  refine card_le_card_of_injOn (fun x e => (∑ i, x i ^ ((e : ℕ) + 1)) % p ^ k) ?_ ?_
  · intro x hx
    rw [hL, coe_filter, Set.mem_ofPred_eq] at hx
    rw [mem_coe, hT, Fintype.mem_piFinset]
    intro e
    rw [mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ (pow_pos hp0 k), ?_⟩
    have hc := hx.2.2 ((e : ℕ) + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
    refine Nat.ModEq.trans ?_ hc
    exact Nat.mod_mod_of_dvd _ (pow_dvd_pow p (by omega))
  · intro x hx y hy hxy
    rw [hL, coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset] at hx hy
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; funext i; exact i.elim0
    have hdx : Function.Injective fun i => ((x i : ℤ) : ZMod p) := by
      intro i i' h
      apply hdist
      have e1 : ((x i : ℤ) : ZMod p) = (a i : ZMod p) := by
        push_cast; exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hx.2.1 i)
      have e2 : ((x i' : ℤ) : ZMod p) = (a i' : ZMod p) := by
        push_cast; exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hx.2.1 i')
      simp only at h ⊢
      rw [← e1, ← e2]; exact h
    have h1 : ∀ i, (p : ℤ) ∣ (y i : ℤ) - (x i : ℤ) := fun i =>
      (Nat.modEq_iff_dvd).mp ((hx.2.1 i).trans (hy.2.1 i).symm)
    have hsum : ∀ j ∈ Icc 1 k, (p : ℤ) ^ k ∣ ∑ i, (y i : ℤ) ^ j - ∑ i, (x i : ℤ) ^ j := by
      intro j hj
      rw [mem_Icc] at hj
      have := congrFun hxy ⟨j - 1, by omega⟩
      simp only [show j - 1 + 1 = j by omega] at this
      have hmod : ∑ i, x i ^ j ≡ ∑ i, y i ^ j [MOD p ^ k] := this
      have := (Nat.modEq_iff_dvd).mp hmod
      push_cast at this
      exact this
    have hr := rigid hp hpk hk (fun i => (x i : ℤ)) (fun i => (y i : ℤ)) hdx h1 hsum
    funext i
    have hmod : x i ≡ y i [MOD p ^ k] := (Nat.modEq_iff_dvd).mpr (by exact_mod_cast hr i)
    have hxi := mem_range.mp (hx.1 i)
    have hyi := mem_range.mp (hy.1 i)
    unfold Nat.ModEq at hmod
    rwa [Nat.mod_eq_of_lt hxi, Nat.mod_eq_of_lt hyi] at hmod

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
