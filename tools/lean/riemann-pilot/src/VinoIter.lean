/-
# Vinogradov's mean value theorem, step I.3b continued: the class count `G_a` (round 198)

Plain statement (`Gcls_le`). Fix a prime `p > k` with `P ≤ p^k` and a residue `a < p`. Count
the quadruples `(u, w, u', w')` where:
* `u, u' ∈ [1,P]^k` have distinct residues mod `p`;
* `w, w'` are `s`-tuples from the residue class `a` inside `[1,P]`;
* `pv u + pv w = pv u' + pv w'` (power sums in degrees `1..k`).

There are at most `P^k · k!·p^{k(k−1)/2} · J_{s,k}(⌊P/p⌋ + 1)` of them. This is Step C′ of
`frontier/vmvt/KARATSUBA_SPEC.md`: the conditioned count (round 197) fibred over `(u, u')`,
with the residue class rescaled to an interval (`Jc_cls_le`).
-/
import VinoStep

open Finset

namespace VinoIter

open Vinogradov

/-- Power sums of an integer tuple, degrees `1..k`. -/
def psZ (k : ℕ) {m : ℕ} (x : Fin m → ℤ) : Fin k → ℤ := fun j => ∑ i, x i ^ (j.val + 1)

lemma pv_eq_psZ (k : ℕ) {m : ℕ} (x : Fin m → ℕ) : pv k x = psZ k (fun i => (x i : ℤ)) := by
  funext j; simp [pv, psZ]

/-- Translation invariance, vector form. -/
lemma psZ_shift {k m : ℕ} (x y : Fin m → ℤ) (h : ℤ) (hxy : psZ k x = psZ k y) :
    psZ k (fun i => x i + h) = psZ k (fun i => y i + h) := by
  have hA : ∀ j ∈ Icc 1 k, ∑ i, x i ^ j = ∑ i, y i ^ j := by
    intro j hj
    rw [mem_Icc] at hj
    have := congrFun hxy ⟨j - 1, by omega⟩
    simpa [psZ, show j - 1 + 1 = j by omega] using this
  funext j
  exact agree_shift x y h hA (j.val + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)

/-- Scaling: `psZ(c·z) = c^{j+1}·psZ(z)` degree by degree, so agreement survives division by `c ≠ 0`. -/
lemma psZ_smul_cancel {k m : ℕ} {c : ℤ} (hc : c ≠ 0) (z z' : Fin m → ℤ)
    (h : psZ k (fun i => c * z i) = psZ k (fun i => c * z' i)) : psZ k z = psZ k z' := by
  funext j
  have := congrFun h j
  simp only [psZ, mul_pow, ← Finset.mul_sum] at this
  exact mul_left_cancel₀ (pow_ne_zero _ hc) this

/-- The residue class `a` mod `p` inside `[1, P]`. -/
def cls (P p a : ℕ) : Finset ℕ := (Icc 1 P).filter fun n => n % p = a

/-- The mean value over a finite set `C` of values. -/
noncomputable def Jc (C : Finset ℕ) (s k : ℕ) : ℕ :=
  shiftCount (Fintype.piFinset fun _ : Fin s => C) (pv k) 0

/-- **A residue class is no richer than an interval of length `⌊P/p⌋ + 1`.** -/
theorem Jc_cls_le {P p a : ℕ} (hp : 0 < p) (s k : ℕ) :
    Jc (cls P p a) s k ≤ J s k (P / p + 1) := by
  rw [J_eq_shiftCount]
  unfold Jc shiftCount
  have hdecomp : ∀ n ∈ cls P p a, (n : ℤ) = (a : ℤ) + p * ((n / p : ℕ) : ℤ) := by
    intro n hn
    rw [cls, mem_filter] at hn
    have := Nat.div_add_mod n p
    rw [hn.2] at this
    have h2 : ((p * (n / p) + a : ℕ) : ℤ) = (n : ℤ) := by rw [this]
    rw [Nat.cast_add, Nat.cast_mul] at h2
    linarith
  refine card_le_card_of_injOn
    (fun q => (fun i => q.1 i / p + 1, fun i => q.2 i / p + 1)) ?_ ?_
  · intro q hq
    rw [coe_filter, Set.mem_ofPred_eq, mem_product, Fintype.mem_piFinset,
      Fintype.mem_piFinset, add_zero] at hq
    obtain ⟨⟨hw, hw'⟩, hag⟩ := hq
    rw [coe_filter, Set.mem_ofPred_eq, mem_product, add_zero]
    have hbox : ∀ w : Fin s → ℕ, (∀ i, w i ∈ cls P p a) → (fun i => w i / p + 1) ∈ Vinogradov.box s (P / p + 1) := by
      intro w hw
      rw [Vinogradov.box, Fintype.mem_piFinset]
      intro i
      have := hw i
      rw [cls, mem_filter, mem_Icc] at this
      rw [mem_Icc]
      exact ⟨Nat.le_add_left 1 _, Nat.add_le_add_right (Nat.div_le_div_right this.1.2) 1⟩
    refine ⟨⟨hbox _ hw, hbox _ hw'⟩, ?_⟩
    rw [pv_eq_psZ, pv_eq_psZ] at hag ⊢
    have h1 := psZ_shift _ _ (-(a : ℤ)) hag
    have e : ∀ w : Fin s → ℕ, (∀ i, w i ∈ cls P p a) →
        (fun i => (w i : ℤ) + -(a : ℤ)) = fun i => (p : ℤ) * ((w i / p : ℕ) : ℤ) := by
      intro w hw; funext i; rw [hdecomp _ (hw i)]; ring
    rw [e _ hw, e _ hw'] at h1
    have h2 := psZ_smul_cancel (by exact_mod_cast hp.ne') _ _ h1
    have h3 := psZ_shift _ _ 1 h2
    convert h3 using 2 <;> funext i <;> push_cast <;> ring
  · intro q hq r hr hqr
    rw [coe_filter, Set.mem_ofPred_eq, mem_product, Fintype.mem_piFinset,
      Fintype.mem_piFinset] at hq hr
    simp only [Prod.mk.injEq] at hqr
    have key : ∀ (w v : Fin s → ℕ), (∀ i, w i ∈ cls P p a) → (∀ i, v i ∈ cls P p a) →
        (fun i => w i / p + 1) = (fun i => v i / p + 1) → w = v := by
      intro w v hw hv h
      funext i
      have hd : w i / p + 1 = v i / p + 1 := congrFun h i
      have e1 := hdecomp _ (hw i)
      have e2 := hdecomp _ (hv i)
      have : w i / p = v i / p := by omega
      have : (w i : ℤ) = v i := by rw [e1, e2, this]
      exact_mod_cast this
    exact Prod.ext (key _ _ hq.1.1 hr.1.1 hqr.1) (key _ _ hq.1.2 hr.1.2 hqr.2)

/-- Class elements decompose as `a + p·(n/p)`. -/
lemma cls_decomp {p a n : ℕ} (hn : n % p = a) : (n : ℤ) + -(a : ℤ) = p * ((n / p : ℕ) : ℤ) := by
  have := Nat.div_add_mod n p
  rw [hn] at this
  have h2 : ((p * (n / p) + a : ℕ) : ℤ) = (n : ℤ) := by rw [this]
  rw [Nat.cast_add, Nat.cast_mul] at h2
  linarith

/-- **A non-empty fibre forces the congruences.** If `pv u + pv w = pv u' + pv w'` with every
entry of `w, w'` in the class `a` mod `p`, then `Σ(uᵢ−a)^j ≡ Σ(u'ᵢ−a)^j (mod p^j)`, `j ≤ k`. -/
lemma cong_of_agree {k s p a : ℕ} (u u' : Fin k → ℕ) (w w' : Fin s → ℕ)
    (hw : ∀ i, w i % p = a) (hw' : ∀ i, w' i % p = a)
    (h : pv k u + pv k w = pv k u' + pv k w') :
    ∀ j ∈ Icc 1 k, (p : ℤ) ^ j ∣ ∑ i, ((u i : ℤ) - a) ^ j - ∑ i, ((u' i : ℤ) - a) ^ j := by
  set X : Fin (k + s) → ℤ := Fin.append (fun i => (u i : ℤ)) (fun i => (w i : ℤ)) with hX
  set Y : Fin (k + s) → ℤ := Fin.append (fun i => (u' i : ℤ)) (fun i => (w' i : ℤ)) with hY
  have hXY : psZ k X = psZ k Y := by
    funext j
    have := congrFun h j
    simp only [Pi.add_apply, pv] at this
    simp only [psZ, hX, hY, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    exact_mod_cast this
  have hsh := psZ_shift X Y (-(a : ℤ)) hXY
  intro j hj
  rw [mem_Icc] at hj
  have hj' := congrFun hsh ⟨j - 1, by omega⟩
  simp only [psZ, hX, hY, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    show j - 1 + 1 = j by omega] at hj'
  have hdw : ∀ v : Fin s → ℕ, (∀ i, v i % p = a) →
      (p : ℤ) ^ j ∣ ∑ i, ((v i : ℤ) + -(a : ℤ)) ^ j := by
    intro v hv
    apply Finset.dvd_sum
    intro i _
    rw [cls_decomp (hv i), mul_pow]
    exact dvd_mul_right _ _
  have e : ∑ i, ((u i : ℤ) - a) ^ j - ∑ i, ((u' i : ℤ) - a) ^ j =
      ∑ i, ((w' i : ℤ) + -(a : ℤ)) ^ j - ∑ i, ((w i : ℤ) + -(a : ℤ)) ^ j := by
    simp only [sub_eq_add_neg] at hj' ⊢
    linarith
  rw [e]
  exact dvd_sub (hdw w' hw') (hdw w hw)

/-- Tuples with distinct residues mod `p`. -/
def Dk (k P p : ℕ) : Finset (Fin k → ℕ) :=
  (Vinogradov.box k P).filter fun u => Function.Injective fun i => (u i : ZMod p)

/-- `s`-tuples from the class `a`. -/
def Wa (s P p a : ℕ) : Finset (Fin s → ℕ) := Fintype.piFinset fun _ : Fin s => cls P p a

/-- The class count `G_a`. -/
def Gcls (k s P p a : ℕ) : ℕ :=
  (((Dk k P p ×ˢ Wa s P p a) ×ˢ (Dk k P p ×ˢ Wa s P p a)).filter fun q =>
    pv k q.1.1 + pv k q.1.2 = pv k q.2.1 + pv k q.2.2).card

/-- **Step C′.** `G_a ≤ P^k · k!·p^{k(k−1)/2} · J_c(class a)`. -/
theorem Gcls_le {k s P p a : ℕ} (hp : p.Prime) (hpk : k < p) (hP : P ≤ p ^ k) :
    Gcls k s P p a ≤ P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * Jc (cls P p a) s k := by
  have : Fact p.Prime := ⟨hp⟩
  set Gset := ((Dk k P p ×ˢ Wa s P p a) ×ˢ (Dk k P p ×ˢ Wa s P p a)).filter fun q =>
    pv k q.1.1 + pv k q.1.2 = pv k q.2.1 + pv k q.2.2 with hG
  set t := (Dk k P p ×ˢ Dk k P p).filter fun uu => ∀ j ∈ Icc 1 k,
    (p : ℤ) ^ j ∣ ∑ i, ((uu.1 i : ℤ) - a) ^ j - ∑ i, ((uu.2 i : ℤ) - a) ^ j with ht
  have hwcls : ∀ w ∈ Wa s P p a, ∀ i, w i % p = a := by
    intro w hw i
    have := Fintype.mem_piFinset.mp hw i
    rw [cls, mem_filter] at this
    exact this.2
  -- fibres over `(u, u')` are shifted counts
  have hfib : ∀ uu ∈ t, (Gset.filter fun q => (q.1.1, q.2.1) = uu).card ≤ Jc (cls P p a) s k := by
    intro uu _
    unfold Jc
    refine le_trans ?_ (shiftCount_le _ (pv k) (pv k uu.2 - pv k uu.1))
    unfold shiftCount
    refine card_le_card_of_injOn (fun q => (q.1.2, q.2.2)) ?_ ?_
    · intro q hq
      rw [coe_filter, Set.mem_ofPred_eq, hG, mem_filter, mem_product, mem_product,
        mem_product] at hq
      obtain ⟨⟨⟨⟨_, hw⟩, _, hw'⟩, hag⟩, hq2⟩ := hq
      rw [coe_filter, Set.mem_ofPred_eq, mem_product]
      refine ⟨⟨hw, hw'⟩, ?_⟩
      have h1 : q.1.1 = uu.1 := congrArg Prod.fst hq2
      have h2 : q.2.1 = uu.2 := congrArg Prod.snd hq2
      rw [← h1, ← h2]
      linear_combination hag
    · intro q hq r hr hqr
      rw [coe_filter, Set.mem_ofPred_eq] at hq hr
      simp only [Prod.mk.injEq] at hqr
      obtain ⟨e1, e2⟩ := Prod.mk.inj (hq.2.trans hr.2.symm)
      exact Prod.ext (Prod.ext e1 hqr.1) (Prod.ext e2 hqr.2)
  -- the admissible `(u, u')` pairs
  have htcard : t.card ≤ P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) := by
    have hfib2 : ∀ u' ∈ t.image Prod.snd, (t.filter fun uu => uu.2 = u').card ≤
        k.factorial * p ^ (k * (k - 1) / 2) := by
      intro u' _
      refine le_trans ?_ (VinoStep.cond_count hp hpk hP (a : ℤ) u')
      refine card_le_card_of_injOn Prod.fst ?_ ?_
      · intro uu huu
        rw [coe_filter, Set.mem_ofPred_eq, ht, mem_filter, mem_product] at huu
        obtain ⟨⟨⟨hu, _⟩, hcong⟩, h2⟩ := huu
        rw [Dk, mem_filter] at hu
        rw [coe_filter, Set.mem_ofPred_eq]
        refine ⟨hu.1, ?_, ?_⟩
        · intro i i' h
          apply hu.2
          simp only [Int.cast_sub, Int.cast_natCast, sub_left_inj] at h
          exact h
        · rw [← h2]; exact hcong
      · intro x hx y hy hxy
        rw [coe_filter, Set.mem_ofPred_eq] at hx hy
        exact Prod.ext hxy (hx.2.trans hy.2.symm)
    have himg : (t.image Prod.snd).card ≤ P ^ k := by
      rw [← card_box k P]
      apply card_le_card
      intro u' hu'
      obtain ⟨uu, huu, rfl⟩ := mem_image.mp hu'
      simp only [ht, Dk, mem_filter, mem_product] at huu
      exact huu.1.2.1
    calc t.card ≤ k.factorial * p ^ (k * (k - 1) / 2) * (t.image Prod.snd).card :=
          card_le_mul_card_image t _ hfib2
      _ ≤ k.factorial * p ^ (k * (k - 1) / 2) * P ^ k := Nat.mul_le_mul_left _ himg
      _ = P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) := mul_comm _ _
  unfold Gcls
  rw [← hG, card_eq_sum_card_fiberwise (f := fun q => (q.1.1, q.2.1)) (t := t)]
  · calc ∑ uu ∈ t, (Gset.filter fun q => (q.1.1, q.2.1) = uu).card
        ≤ ∑ _uu ∈ t, Jc (cls P p a) s k := sum_le_sum hfib
      _ = t.card * Jc (cls P p a) s k := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ htcard
  · intro q hq
    rw [coe_filter, Set.mem_ofPred_eq, mem_product, mem_product, mem_product] at hq
    obtain ⟨⟨⟨hu, hw⟩, hu', hw'⟩, hag⟩ := hq
    rw [mem_coe, ht, mem_filter, mem_product]
    exact ⟨⟨hu, hu'⟩, cong_of_agree _ _ _ _ (hwcls _ hw) (hwcls _ hw') hag⟩

end VinoIter
