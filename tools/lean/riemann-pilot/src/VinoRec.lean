/-
# Vinogradov's mean value theorem, step I.3b: bad count and the one-step inequality (round 201)

Plain statements.
* `bad_card` (Step D): the tuples in `[1,P]^n` whose coordinates meet fewer than `k` residue
  classes mod `p` number at most `p^{k−1}·((k−1)(⌊P/p⌋+1))^n`. Such a tuple lives inside some
  set `S` of `k−1` classes; there are `C(p,k−1) ≤ p^{k−1}` choices of `S`, and each class holds
  at most `⌊P/p⌋+1` numbers.
* `one_step` (Steps A–D chained). For a prime `p > k` with `P ≤ p^k` and `s ≥ 1`:
  `J_{k+s,k}(P) ≤ 2·(p^{k−1}((k−1)(⌊P/p⌋+1))^{k+s})²
     + 16(k+s)^{2k}·p^{2s−1}·p·P^k·k!·p^{k(k−1)/2}·J_{s,k}(⌊P/p⌋+1)`.
* `exists_good_prime`: Bertrand gives a prime `p > k` with `P ≤ p^k` and
  `P^{1/k} ≤ p ≤ 2(k+2)P^{1/k}`.
* `step_real`: one step in real exponents.
* **`vmvt_weak` (round 202): Vinogradov's mean value theorem, weak classical form.** For every
  `k ≥ 2` and `ε > 0` there are `s` and `C` with `J_{s,k}(P) ≤ C·P^{2s − k(k+1)/2 + ε}` for all
  `P ≥ 1`. The excess exponent satisfies `η_{m+1} = max((1−1/k)η_m, k(k+1)/2 − 2(s+1)/k)`
  (`vmvt_iter`) and tends to 0 (`eta_small`). It contracts geometrically once `m ≥ k²`, so
  `s ≈ k³`, versus `k² log k` classically.
-/
import VinoSplit

open Finset

namespace VinoRec

open Vinogradov VinoIter VinoHolder VinoSplit

lemma card_cls_le {P p a : ℕ} : (cls P p a).card ≤ P / p + 1 := by
  calc (cls P p a).card ≤ (range (P / p + 1)).card := by
        refine card_le_card_of_injOn (fun n => n / p) ?_ ?_
        · intro n hn
          have hn' := mem_coe.mp hn
          rw [cls, mem_filter, mem_Icc] at hn'
          rw [mem_coe, mem_range]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hn'.1.2)
        · intro n hn m hm h
          have hn' := mem_coe.mp hn
          have hm' := mem_coe.mp hm
          rw [cls, mem_filter] at hn' hm'
          simp only at h
          rw [← Nat.div_add_mod n p, ← Nat.div_add_mod m p, h, hn'.2, hm'.2]
    _ = P / p + 1 := card_range _

/-- Numbers in `[1,P]` with residue in `S`. -/
def pieceS (P p : ℕ) (S : Finset (ZMod p)) : Finset ℕ :=
  (Icc 1 P).filter fun m => ((m : ℕ) : ZMod p) ∈ S

/-- Tuples with every coordinate in `pieceS`. -/
def piece (n P p : ℕ) (S : Finset (ZMod p)) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun _ : Fin n => pieceS P p S

/-- A bad tuple lies in a piece `S^n` with `|S| = k − 1` (from `VinoBad.lean` since round 334). -/
lemma bad_sub {n k P p : ℕ} [NeZero p] (hp : p.Prime) (hk : 1 ≤ k) (hkp : k ≤ p) :
    (box n P).filter (isBad k p) ⊆
      (powersetCard (k - 1) (univ : Finset (ZMod p))).biUnion (piece n P p) := by
  have : Fact p.Prime := ⟨hp⟩
  intro x hx
  rw [mem_filter] at hx
  set R := univ.image fun i => (x i : ZMod p)
  have hR0 : R.card < k := hx.2
  have hR : R.card ≤ k - 1 := by omega
  have hRp : k - 1 ≤ (univ : Finset (ZMod p)).card := by
    rw [card_univ, ZMod.card]; omega
  obtain ⟨S, hRS, _, hS⟩ := exists_subsuperset_card_eq (subset_univ R) hR hRp
  refine mem_biUnion.mpr ⟨S, mem_powersetCard.mpr ⟨subset_univ _, hS⟩, ?_⟩
  rw [piece, Fintype.mem_piFinset]
  intro i
  rw [pieceS, mem_filter]
  have hb := hx.1
  rw [Vinogradov.box, Fintype.mem_piFinset] at hb
  exact ⟨hb i, hRS (mem_image_of_mem _ (mem_univ i))⟩

/-- **Step D (bad count).** -/
theorem bad_card {n k P p : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkp : k ≤ p) :
    ((box n P).filter (isBad k p)).card ≤ p ^ (k - 1) * ((k - 1) * (P / p + 1)) ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  set F := powersetCard (k - 1) (univ : Finset (ZMod p)) with hF
  have hpc : ∀ S ∈ F, (piece n P p S).card ≤ ((k - 1) * (P / p + 1)) ^ n := by
    intro S hS
    rw [mem_powersetCard] at hS
    rw [piece, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
    apply Nat.pow_le_pow_left
    calc (pieceS P p S).card
        ≤ (S.biUnion fun r => cls P p r.val).card := by
          apply card_le_card
          intro m hm
          rw [pieceS, mem_filter] at hm
          refine mem_biUnion.mpr ⟨((m : ℕ) : ZMod p), hm.2, ?_⟩
          rw [cls, mem_filter, ZMod.val_natCast]
          exact ⟨hm.1, rfl⟩
      _ ≤ ∑ r ∈ S, (cls P p r.val).card := card_biUnion_le
      _ ≤ ∑ _r ∈ S, (P / p + 1) := sum_le_sum fun r _ => card_cls_le
      _ = (k - 1) * (P / p + 1) := by rw [sum_const, hS.2, smul_eq_mul]
  have hFc : F.card ≤ p ^ (k - 1) := by
    rw [hF, card_powersetCard, card_univ, ZMod.card]
    exact Nat.choose_le_pow p (k - 1)
  calc ((box n P).filter (isBad k p)).card ≤ (F.biUnion (piece n P p)).card :=
        card_le_card (bad_sub hp hk hkp)
    _ ≤ ∑ S ∈ F, (piece n P p S).card := card_biUnion_le
    _ ≤ ∑ _S ∈ F, ((k - 1) * (P / p + 1)) ^ n := sum_le_sum hpc
    _ = F.card * ((k - 1) * (P / p + 1)) ^ n := by rw [sum_const, smul_eq_mul]
    _ ≤ p ^ (k - 1) * ((k - 1) * (P / p + 1)) ^ n := Nat.mul_le_mul_right _ hFc

lemma TBB_le {k s P p : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkp : k ≤ p) :
    TBB k s P p ≤ (p ^ (k - 1) * ((k - 1) * (P / p + 1)) ^ (k + s)) ^ 2 := by
  unfold TBB pairCount
  refine (card_filter_le _ _).trans ?_
  rw [card_product, sq]
  exact Nat.mul_le_mul (bad_card hp hk hkp) (bad_card hp hk hkp)

/-- **Steps B and C**: `G ≤ p^{2s−1}·p·P^k·k!·p^{k(k−1)/2}·J_{s,k}(⌊P/p⌋+1)` (round 334: `one_step` and
`VinoBad.one_step2` share it). -/
lemma Gfull_le_J {k s P p : ℕ} (hp : p.Prime) (hpk : k < p) (hP : P ≤ p ^ k) (hs : 1 ≤ s) :
    Gfull k s P p ≤ p ^ (2 * s - 1) *
      (p * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J s k (P / p + 1))) := by
  refine (Gfull_le hp.pos hs).trans (Nat.mul_le_mul_left _ ?_)
  calc ∑ a ∈ range p, Gcls k s P p a
      ≤ ∑ _a ∈ range p, P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J s k (P / p + 1) := by
        apply sum_le_sum
        intro a _
        exact (Gcls_le hp hpk hP).trans (Nat.mul_le_mul_left _ (Jc_cls_le hp.pos s k))
    _ = _ := by rw [sum_const, card_range, smul_eq_mul]

/-- **One Karatsuba step** (A–D chained). -/
theorem one_step {k s P p : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hpk : k < p) (hP : P ≤ p ^ k)
    (hs : 1 ≤ s) :
    J (k + s) k P ≤ 2 * (p ^ (k - 1) * ((k - 1) * (P / p + 1)) ^ (k + s)) ^ 2 +
      16 * (k + s) ^ (2 * k) * (p ^ (2 * s - 1) *
        (p * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J s k (P / p + 1)))) := by
  have hA := stepA k s P p
  have hD := TBB_le (s := s) (P := P) hp hk hpk.le
  calc J (k + s) k P ≤ 2 * TBB k s P p + 16 * (k + s) ^ (2 * k) * Gfull k s P p := hA
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ hD)
          (Nat.mul_le_mul_left _ (Gfull_le_J hp hpk hP hs))

/-! ## Choosing the prime -/

/-- **The Bertrand prime.** For `k ≥ 1` and `P ≥ 1`, with `t = P^{1/k}`: there is a prime `p`
with `k < p`, `P ≤ p^k`, `t ≤ p` and `p ≤ 2(k+2)·t`. -/
theorem exists_good_prime {k P : ℕ} (hk : 1 ≤ k) (hP : 1 ≤ P) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ P ≤ p ^ k ∧
      (P : ℝ) ^ ((k : ℝ)⁻¹) ≤ p ∧ (p : ℝ) ≤ 2 * (k + 2) * (P : ℝ) ^ ((k : ℝ)⁻¹) := by
  classical
  have hex : ∃ m, P ≤ m ^ k := ⟨P, Nat.le_self_pow (by omega) P⟩
  set m := Nat.find hex with hmdef
  have hm : P ≤ m ^ k := Nat.find_spec hex
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, zero_pow (by omega)] at hm; omega
    · exact h
  have hmin : (m - 1) ^ k < P := by
    have := Nat.find_min hex (show m - 1 < m by omega)
    omega
  obtain ⟨p, hp, hnp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (max m k) (by omega)
  have hkp : k < p := lt_of_le_of_lt (le_max_right m k) hnp
  have hmp : m < p := lt_of_le_of_lt (le_max_left m k) hnp
  have hPp : P ≤ p ^ k := hm.trans (Nat.pow_le_pow_left hmp.le k)
  set t : ℝ := (P : ℝ) ^ ((k : ℝ)⁻¹) with ht
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have ht1 : 1 ≤ t := Real.one_le_rpow hPr (by positivity)
  refine ⟨p, hp, hkp, hPp, ?_, ?_⟩
  · have h1 : t ≤ ((p : ℝ) ^ k) ^ ((k : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hPp) (by positivity)
    rwa [Real.pow_rpow_inv_natCast (by positivity) (by omega)] at h1
  · have hm_lt : ((m - 1 : ℕ) : ℝ) < t := by
      rw [ht, Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) hkpos,
        Real.rpow_natCast]
      exact_mod_cast hmin
    have hm_le : (m : ℝ) ≤ t + 1 := by
      have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm1]; simp
      linarith
    have hp_le : (p : ℝ) ≤ 2 * ((m : ℝ) + k) := by
      have : p ≤ 2 * (m + k) := hp2.trans (by
        have := max_le_iff.mpr ⟨Nat.le_add_right m k, Nat.le_add_left k m⟩; omega)
      exact_mod_cast this
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith

/-! ## One step in real exponents -/

def Nn (k s : ℕ) : ℕ := 2 * s + k * (k - 1) / 2
def βn (k s : ℕ) : ℕ := 2 * (k - 1) + 2 * (k - 1) * (k + s)
noncomputable def μ (k s : ℕ) (E : ℝ) : ℝ := ((Nn k s + k * k : ℕ) : ℝ) + ((k : ℝ) - 1) * E
noncomputable def Kbad (k s : ℕ) : ℝ :=
  2 * ((2 * ((k : ℝ) + 2)) ^ (k - 1) * (((k - 1 : ℕ) : ℝ) * 2) ^ (k + s)) ^ 2
noncomputable def Kmain (k s : ℕ) (C E : ℝ) : ℝ :=
  16 * ((k + s : ℕ) : ℝ) ^ (2 * k) * ((k.factorial : ℝ) * (2 * ((k : ℝ) + 2)) ^ Nn k s) * C * (2 : ℝ) ^ E

/-- `Q = ⌊P/p⌋ + 1 ≤ 2t^{k−1}` when `P = t^k` and `t ≤ p`. -/
lemma q_bound {k p P : ℕ} {t : ℝ} (hk : 2 ≤ k) (ht1 : 1 ≤ t) (hx : (P : ℝ) = t ^ k)
    (htp : t ≤ p) : ((P / p + 1 : ℕ) : ℝ) ≤ 2 * t ^ (k - 1) := by
  have ht0 : 0 < t := by linarith
  set Q := P / p + 1 with hQdef
  have h1 : ((P / p : ℕ) : ℝ) ≤ (P : ℝ) / p := Nat.cast_div_le
  have h2 : (P : ℝ) / p ≤ (P : ℝ) / t :=
    div_le_div_of_nonneg_left (by positivity) ht0 htp
  have h3 : (P : ℝ) / t = t ^ (k - 1) := by
    rw [hx, div_eq_iff ht0.ne', ← pow_succ, Nat.sub_add_cancel (by omega)]
  have h4 : 1 ≤ t ^ (k - 1) := one_le_pow₀ ht1
  rw [hQdef]; push_cast; linarith

/-- **The main part of one step**, bounded by `K_main·t^μ`. -/
lemma main_part {k s p P Q : ℕ} {C E t : ℝ} (hk : 2 ≤ k) (hs : 1 ≤ s) (hC : 0 < C) (hE : 0 ≤ E)
    (hJ : ∀ Q : ℕ, 1 ≤ Q → (J s k Q : ℝ) ≤ C * (Q : ℝ) ^ E) (hQ1 : 1 ≤ Q) (ht0 : 0 < t)
    (hx : (P : ℝ) = t ^ k) (hQ : (Q : ℝ) ≤ 2 * t ^ (k - 1)) (hpc : (p : ℝ) ≤ (2 * ((k : ℝ) + 2)) * t) :
    16 * ((k + s : ℕ) : ℝ) ^ (2 * k) * ((p : ℝ) ^ (2 * s - 1) * ((p : ℝ) *
        ((P : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2)) * (J s k Q : ℝ)))) ≤
      Kmain k s C E * t ^ (μ k s E) := by
  have hJQ : (J s k Q : ℝ) ≤ C * ((2 : ℝ) ^ E * t ^ (((k : ℝ) - 1) * E)) := by
    have h1 := hJ Q hQ1
    have h2 : (Q : ℝ) ^ E ≤ (2 * t ^ (k - 1)) ^ E :=
      Real.rpow_le_rpow (by positivity) hQ hE
    have h3 : (2 * t ^ (k - 1) : ℝ) ^ E = (2 : ℝ) ^ E * t ^ (((k : ℝ) - 1) * E) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      congr 2
      rw [Nat.cast_sub (by omega)]; simp
    rw [h3] at h2
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC.le)
  have hmain : 16 * ((k + s : ℕ) : ℝ) ^ (2 * k) * ((p : ℝ) ^ (2 * s - 1) * ((p : ℝ) *
        ((P : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2)) * (J s k Q : ℝ)))) ≤
      Kmain k s C E * (t ^ (Nn k s + k * k) * t ^ (((k : ℝ) - 1) * E)) := by
    have hpp : (p : ℝ) ^ (2 * s - 1) * (p : ℝ) = (p : ℝ) ^ (2 * s) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hJ0 : (0 : ℝ) ≤ (J s k Q : ℝ) := by positivity
    calc 16 * ((k + s : ℕ) : ℝ) ^ (2 * k) * ((p : ℝ) ^ (2 * s - 1) * ((p : ℝ) *
          ((P : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2)) * (J s k Q : ℝ))))
        = 16 * ((k + s : ℕ) : ℝ) ^ (2 * k) * ((p : ℝ) ^ (2 * s) *
          ((P : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2)) * (J s k Q : ℝ))) := by
          rw [← hpp]; ring
      _ ≤ 16 * ((k + s : ℕ) : ℝ) ^ (2 * k) * (((2 * ((k : ℝ) + 2)) * t) ^ (2 * s) *
          ((t ^ k) ^ k * ((k.factorial : ℝ) * ((2 * ((k : ℝ) + 2)) * t) ^ (k * (k - 1) / 2)) *
            (C * ((2 : ℝ) ^ E * t ^ (((k : ℝ) - 1) * E))))) := by
          rw [hx]
          gcongr
      _ = Kmain k s C E * (t ^ (Nn k s + k * k) * t ^ (((k : ℝ) - 1) * E)) := by
          unfold Kmain Nn
          simp only [mul_pow]
          ring
  have hμ : t ^ (Nn k s + k * k) * t ^ (((k : ℝ) - 1) * E) = t ^ (μ k s E) := by
    rw [μ, Real.rpow_add ht0, Real.rpow_natCast]
  rwa [hμ] at hmain

/-- **One step, real form.** If `J_s(Q) ≤ C·Q^E` for all `Q ≥ 1`, then
`J_{k+s}(P) ≤ (K_bad + K_main)·P^{max(μ, β)/k}` for all `P ≥ 1`. -/
theorem step_real {k s : ℕ} (hk : 2 ≤ k) (hs : 1 ≤ s) {C E : ℝ} (hC : 0 < C) (hE : 0 ≤ E)
    (hJ : ∀ Q : ℕ, 1 ≤ Q → (J s k Q : ℝ) ≤ C * (Q : ℝ) ^ E) (P : ℕ) (hP : 1 ≤ P) :
    (J (k + s) k P : ℝ) ≤
      (Kbad k s + Kmain k s C E) * (P : ℝ) ^ (max (μ k s E) (βn k s : ℝ) / k) := by
  obtain ⟨p, hp, hkp, hPp, htp, hpt⟩ := exists_good_prime (by omega : 1 ≤ k) hP
  set t : ℝ := (P : ℝ) ^ ((k : ℝ)⁻¹) with ht
  have hk0 : k ≠ 0 := by omega
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hx : (P : ℝ) = t ^ k := (Real.rpow_inv_natCast_pow (by positivity) hk0).symm
  have ht1 : 1 ≤ t := Real.one_le_rpow hPr (by positivity)
  have ht0 : 0 < t := by linarith
  have hpc : (p : ℝ) ≤ (2 * ((k : ℝ) + 2)) * t := hpt
  have hp0 : (0 : ℝ) ≤ p := by positivity
  set Q := P / p + 1 with hQdef
  have hQ1 : 1 ≤ Q := by rw [hQdef]; exact Nat.le_add_left 1 _
  have hQ : (Q : ℝ) ≤ 2 * t ^ (k - 1) := q_bound hk ht1 hx htp
  have hos : (J (k + s) k P : ℝ) ≤
      2 * ((p : ℝ) ^ (k - 1) * (((k - 1 : ℕ) : ℝ) * (Q : ℝ)) ^ (k + s)) ^ 2 +
      16 * ((k + s : ℕ) : ℝ) ^ (2 * k) * ((p : ℝ) ^ (2 * s - 1) * ((p : ℝ) *
        ((P : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2)) * (J s k Q : ℝ)))) := by
    have := one_step hp (by omega) hkp hPp hs
    rw [← hQdef] at this
    exact_mod_cast this
  -- the bad part
  have hbad : 2 * ((p : ℝ) ^ (k - 1) * (((k - 1 : ℕ) : ℝ) * (Q : ℝ)) ^ (k + s)) ^ 2 ≤
      Kbad k s * t ^ (βn k s) := by
    have hk1 : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by positivity
    calc 2 * ((p : ℝ) ^ (k - 1) * (((k - 1 : ℕ) : ℝ) * (Q : ℝ)) ^ (k + s)) ^ 2
        ≤ 2 * (((2 * ((k : ℝ) + 2)) * t) ^ (k - 1) * (((k - 1 : ℕ) : ℝ) * (2 * t ^ (k - 1))) ^ (k + s)) ^ 2 := by
          gcongr
      _ = Kbad k s * t ^ (βn k s) := by
          unfold Kbad βn
          simp only [mul_pow]
          ring
  -- the main part
  have hmain := main_part hk hs hC hE hJ hQ1 ht0 hx hQ hpc
  -- combine
  have hβ : t ^ (βn k s) = t ^ ((βn k s : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
  set M := max (μ k s E) (βn k s : ℝ)
  have hmono1 : t ^ (μ k s E) ≤ t ^ M := Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left _ _)
  have hmono2 : t ^ ((βn k s : ℕ) : ℝ) ≤ t ^ M :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_right _ _)
  have htM : t ^ M = (P : ℝ) ^ (M / k) := by
    rw [ht, ← Real.rpow_mul (by positivity)]
    congr 1
    field_simp
  have hKb : 0 ≤ Kbad k s := by unfold Kbad; positivity
  have hKm : 0 ≤ Kmain k s C E := by
    unfold Kmain; positivity
  rw [← htM]
  rw [hβ] at hbad
  nlinarith [mul_le_mul_of_nonneg_left hmono1 hKm, mul_le_mul_of_nonneg_left hmono2 hKb]

/-! ## The iteration -/

/-- The excess exponent `η_m` after `m` steps, with `s = k + mk` variables. -/
noncomputable def eta (k : ℕ) : ℕ → ℝ
  | 0 => (k : ℝ) * ((k : ℝ) - 1) / 2
  | m + 1 => max ((1 - 1 / (k : ℝ)) * eta k m)
      ((k : ℝ) * ((k : ℝ) + 1) / 2 - 2 * (((k + m * k : ℕ) : ℝ) + 1) / k)

/-- The exponent `2s − k(k+1)/2 + η_m` for `s = k + mk`. -/
noncomputable def expo (k m : ℕ) : ℝ :=
  2 * ((k + m * k : ℕ) : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eta k m

lemma expo_nonneg {k : ℕ} (hk : 2 ≤ k) (m : ℕ) : 0 ≤ expo k m := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  cases m with
  | zero => simp [expo, eta]; nlinarith
  | succ m =>
    unfold expo
    rw [eta]
    have h := le_max_right ((1 - 1 / (k : ℝ)) * eta k m)
      ((k : ℝ) * ((k : ℝ) + 1) / 2 - 2 * (((k + m * k : ℕ) : ℝ) + 1) / k)
    have hs : ((k + (m + 1) * k : ℕ) : ℝ) = k + ((k + m * k : ℕ) : ℝ) := by push_cast; ring
    rw [hs]
    set s : ℝ := ((k + m * k : ℕ) : ℝ)
    have hs0 : 0 ≤ s := by positivity
    have : 2 * (s + 1) / (k : ℝ) ≤ s + 1 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith

lemma Nn_cast (k s : ℕ) : ((Nn k s : ℕ) : ℝ) = 2 * s + (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  unfold Nn
  have h2 : 2 ∣ k * (k - 1) := (Nat.even_mul_pred_self k).two_dvd
  rw [Nat.cast_add, Nat.cast_div h2 (by norm_num)]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · push_cast [Nat.cast_sub hk]; ring

/-- One iteration step moves the exponent from `expo k m` to `expo k (m + 1)`. -/
lemma expo_step {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    max (μ k (k + m * k) (expo k m)) (βn k (k + m * k) : ℝ) / k = expo k (m + 1) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set s := k + m * k with hsdef
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hsr : (s : ℝ) = (k : ℝ) + (m : ℝ) * k := by rw [hsdef]; push_cast; ring
  rw [← max_div_div_right (by positivity : (0 : ℝ) ≤ k)]
  have e1 : μ k s (expo k m) / k = 2 * ((k : ℝ) + s) - (k : ℝ) * ((k : ℝ) + 1) / 2 +
      (1 - 1 / (k : ℝ)) * eta k m := by
    unfold μ expo
    rw [Nat.cast_add, Nn_cast]
    push_cast
    rw [hsr]
    field_simp
    ring
  have e2 : ((βn k s : ℕ) : ℝ) / k = 2 * ((k : ℝ) + s) - (k : ℝ) * ((k : ℝ) + 1) / 2 +
      ((k : ℝ) * ((k : ℝ) + 1) / 2 - 2 * ((s : ℝ) + 1) / k) := by
    unfold βn
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    field_simp
    ring
  rw [e1, e2, max_add_add_left, expo, eta]
  push_cast
  rw [hsr]
  ring_nf

/-- **Vinogradov's mean value theorem, iterated form.** For `k ≥ 2` and every `m`,
`J_{k+mk,k}(P) ≤ C·P^{2(k+mk) − k(k+1)/2 + η_m}` for all `P ≥ 1`. -/
theorem vmvt_iter {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    ∃ C > 0, ∀ P : ℕ, 1 ≤ P → (J (k + m * k) k P : ℝ) ≤ C * (P : ℝ) ^ (expo k m) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  induction m with
  | zero =>
    refine ⟨k.factorial, by positivity, fun P hP => ?_⟩
    have h := J_le_diag (le_refl k) P
    simp only [zero_mul, add_zero]
    have he : expo k 0 = (k : ℝ) := by simp [expo, eta]; ring
    rw [he, Real.rpow_natCast]
    exact_mod_cast h
  | succ m ih =>
    obtain ⟨C, hC, hJ⟩ := ih
    set s := k + m * k with hsdef
    have hs : 1 ≤ s := by omega
    have hstep := step_real hk hs hC (expo_nonneg hk m) hJ
    refine ⟨Kbad k s + Kmain k s C (expo k m), ?_, fun P hP => ?_⟩
    · have : 0 < Kmain k s C (expo k m) := by unfold Kmain; positivity
      have : 0 ≤ Kbad k s := by unfold Kbad; positivity
      linarith
    have hlen : k + (m + 1) * k = k + s := by rw [hsdef]; ring
    rw [hlen]
    have hexp := expo_step hk m
    rw [← hexp]
    exact hstep P hP

/-- `η_m ≥ 0`. -/
lemma eta_nonneg {k : ℕ} (hk : 2 ≤ k) (m : ℕ) : 0 ≤ eta k m := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 0 ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  induction m with
  | zero => simp only [eta]; nlinarith
  | succ m ih => rw [eta]; exact le_max_of_le_left (mul_nonneg h1 ih)

/-- Once `m ≥ k²`, `η_{m+1} ≤ (1 − 1/k)η_m` (from `VinoConst2.lean` since round 334). -/
lemma eta_contract {k : ℕ} (hk : 2 ≤ k) (m : ℕ) (hm : k * k ≤ m) :
    eta k (m + 1) ≤ (1 - 1 / (k : ℝ)) * eta k m := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [eta]
  apply max_le le_rfl
  have hmr : ((k * k : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
  push_cast at hmr
  have hlin : (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ 2 * (((k + m * k : ℕ) : ℝ) + 1) / k := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    push_cast
    nlinarith
  have hr0 : 0 ≤ 1 - 1 / (k : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have := mul_nonneg hr0 (eta_nonneg hk m)
  linarith

/-- `η_{k²+j} ≤ (1 − 1/k)^j η_{k²}` (from `VinoConst2.lean` since round 334). -/
lemma eta_geo {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    eta k (k * k + j) ≤ (1 - 1 / (k : ℝ)) ^ j * eta k (k * k) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : 0 ≤ 1 - 1 / (k : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  induction j with
  | zero => simp
  | succ j ih =>
    calc eta k (k * k + (j + 1)) = eta k (k * k + j + 1) := by rw [add_assoc]
      _ ≤ (1 - 1 / (k : ℝ)) * eta k (k * k + j) := eta_contract hk _ (Nat.le_add_right _ _)
      _ ≤ (1 - 1 / (k : ℝ)) * ((1 - 1 / (k : ℝ)) ^ j * eta k (k * k)) :=
          mul_le_mul_of_nonneg_left ih hr0
      _ = (1 - 1 / (k : ℝ)) ^ (j + 1) * eta k (k * k) := by ring

/-- **`η_m → 0`**: the excess exponent can be made as small as we like. -/
theorem eta_small {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) : ∃ m, eta k m ≤ ε := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hgeo := eta_geo hk
  set r : ℝ := 1 - 1 / (k : ℝ)
  have hr0 : 0 ≤ r := by
    show 0 ≤ 1 - 1 / (k : ℝ); rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hr1 : r < 1 := by
    show 1 - 1 / (k : ℝ) < 1; have : 0 < 1 / (k : ℝ) := by positivity
    linarith
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (eta k (k * k) + 1) by
    have := eta_nonneg hk (k * k); positivity) hr1
  refine ⟨k * k + j, (hgeo j).trans ?_⟩
  have h0 := eta_nonneg hk (k * k)
  have hpos : 0 < eta k (k * k) + 1 := by linarith
  rw [lt_div_iff₀ hpos] at hj
  nlinarith [pow_nonneg hr0 j]

/-- **Vinogradov's mean value theorem (weak classical form).** For every `k ≥ 2` and `ε > 0`
there are `s` and `C` with `J_{s,k}(P) ≤ C·P^{2s − k(k+1)/2 + ε}` for all `P ≥ 1`. -/
theorem vmvt_weak {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℕ, ∃ C > 0, ∀ P : ℕ, 1 ≤ P →
      (J s k P : ℝ) ≤ C * (P : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + ε) := by
  obtain ⟨m, hm⟩ := eta_small hk ε hε
  obtain ⟨C, hC, hJ⟩ := vmvt_iter hk m
  refine ⟨k + m * k, C, hC, fun P hP => (hJ P hP).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hP)
  unfold expo
  linarith

end VinoRec
