import SieveTypeIIU
import SieveRoughTuple

open Real Finset Filter SieveFamily

namespace SieveTypeIIR

/-! ### The comparisons of a rough cofactor: order, roughness and range -/

/-- The forms' `m`-parts: `0` for the order, `−log z(m)` for roughness, `log m − log X` and `log 2X − log m` for
the range `(X, 2X]`. -/
noncomputable def phiR (n : ℕ) (z : ℕ → ℕ) (X : ℝ) (j : Fin (n + 3)) (m : ℕ) : ℝ :=
  if j.val < n then 0
  else if j.val = n then -Real.log (z m)
  else if j.val = n + 1 then Real.log m - Real.log X
  else Real.log (2 * X) - Real.log m

/-- The forms' coefficients. -/
noncomputable def eR (n : ℕ) (j : Fin (n + 3)) (i : Fin (n + 1)) : ℝ :=
  if j.val < n then (if i.val = j.val then 1 else if i.val = j.val + 1 then -1 else 0)
  else if j.val = n then (if i.val = n then 1 else 0)
  else if j.val = n + 1 then 1
  else -1

/-- The comparisons: `0 ≤ ℓ_j`, and `0 < ℓ_j` at the lower end of the range. -/
def PrR (n : ℕ) (z : ℕ → ℕ) (X : ℝ) (j : Fin (n + 3)) (m : ℕ) (x : Fin (n + 1) → ℕ) : Prop :=
  if j.val = n + 1 then 0 < phiR n z X j m + ∑ i, eR n j i * Real.log (x i)
  else 0 ≤ phiR n z X j m + ∑ i, eR n j i * Real.log (x i)

theorem PrR_spec (n : ℕ) (z : ℕ → ℕ) (X : ℝ) (j : Fin (n + 3)) (m : ℕ) (x : Fin (n + 1) → ℕ) :
    (0 < phiR n z X j m + ∑ i, eR n j i * Real.log (x i) → PrR n z X j m x) ∧
      (PrR n z X j m x → 0 ≤ phiR n z X j m + ∑ i, eR n j i * Real.log (x i)) := by
  unfold PrR
  split_ifs
  · exact ⟨id, le_of_lt⟩
  · exact ⟨le_of_lt, id⟩

theorem abs_eR_le (n : ℕ) (j : Fin (n + 3)) (i : Fin (n + 1)) : |eR n j i| ≤ 1 := by
  unfold eR
  split_ifs <;> norm_num

theorem sum_eR_order {n : ℕ} (t : Fin n) (j : Fin (n + 3)) (hj : j.val = t.val) (x : Fin (n + 1) → ℕ) :
    ∑ i, eR n j i * Real.log (x i) = Real.log (x t.castSucc) - Real.log (x t.succ) := by
  have hjn : j.val < n := hj ▸ t.isLt
  have he : ∀ i, eR n j i * Real.log (x i) =
      (if t.castSucc = i then Real.log (x i) else 0) + (if t.succ = i then -Real.log (x i) else 0) := by
    intro i
    unfold eR
    rw [ite_eq_left hjn]
    split_ifs <;> simp_all [Fin.ext_iff]
  rw [Finset.sum_congr rfl fun i _ => he i, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  ring

theorem sum_eR_rough {n : ℕ} (j : Fin (n + 3)) (hj : j.val = n) (x : Fin (n + 1) → ℕ) :
    ∑ i, eR n j i * Real.log (x i) = Real.log (x (Fin.last n)) := by
  have he : ∀ i, eR n j i * Real.log (x i) = if Fin.last n = i then Real.log (x i) else 0 := by
    intro i
    unfold eR
    rw [ite_eq_right (by omega), ite_eq_left hj]
    split_ifs <;> simp_all [Fin.ext_iff]
  rw [Finset.sum_congr rfl fun i _ => he i, Finset.sum_ite_eq]
  simp

theorem sum_eR_low {n : ℕ} (j : Fin (n + 3)) (hj : j.val = n + 1) (x : Fin (n + 1) → ℕ) :
    ∑ i, eR n j i * Real.log (x i) = ∑ i, Real.log (x i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold eR
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hj, one_mul]

theorem sum_eR_high {n : ℕ} (j : Fin (n + 3)) (hj : j.val = n + 2) (x : Fin (n + 1) → ℕ) :
    ∑ i, eR n j i * Real.log (x i) = -∑ i, Real.log (x i) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold eR
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), neg_one_mul]

/-- **What the comparisons say.** For `m ≥ 1`, `z(m) ≥ 1`, `X > 0` and `x_i ≥ 1`: all hold iff `x` is non-increasing,
`x_n ≥ z(m)` and `X < m∏x_i ≤ 2X`. -/
theorem PrR_all_iff {n : ℕ} {z : ℕ → ℕ} {X : ℝ} (hX : 0 < X) {m : ℕ} (hm : 1 ≤ m) (hz : 1 ≤ z m)
    {x : Fin (n + 1) → ℕ} (hx : ∀ i, 1 ≤ x i) :
    (∀ j, PrR n z X j m x) ↔
      (Antitone x ∧ z m ≤ x (Fin.last n) ∧ X < (m : ℝ) * ∏ i, (x i : ℝ) ∧
        (m : ℝ) * ∏ i, (x i : ℝ) ≤ 2 * X) := by
  have hxpos : ∀ i, (0 : ℝ) < x i := fun i => by exact_mod_cast (hx i)
  have hlogprod : ∑ i, Real.log (x i) = Real.log (∏ i, (x i : ℝ)) :=
    (Real.log_prod (fun i _ => (hxpos i).ne')).symm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hz0 : (0 : ℝ) < z m := by exact_mod_cast hz
  have hP0 : (0 : ℝ) < ∏ i, (x i : ℝ) := Finset.prod_pos fun i _ => hxpos i
  have hmP : (0 : ℝ) < m * ∏ i, (x i : ℝ) := mul_pos hm0 hP0
  have hlogmP : Real.log m + Real.log (∏ i, (x i : ℝ)) = Real.log (m * ∏ i, (x i : ℝ)) :=
    (Real.log_mul hm0.ne' hP0.ne').symm
  -- the four kinds of comparison
  have hord : ∀ t : Fin n, PrR n z X ⟨t.val, by omega⟩ m x ↔ x t.succ ≤ x t.castSucc := by
    intro t
    unfold PrR
    rw [ite_eq_right (show ¬ (t.val = n + 1) by omega),
      sum_eR_order t ⟨t.val, by omega⟩ rfl x]
    unfold phiR
    rw [ite_eq_left (show (⟨t.val, by omega⟩ : Fin (n + 3)).val < n from t.isLt), zero_add, sub_nonneg,
      Real.log_le_log_iff (hxpos _) (hxpos _), Nat.cast_le]
  have hrough : PrR n z X ⟨n, by omega⟩ m x ↔ z m ≤ x (Fin.last n) := by
    unfold PrR
    rw [ite_eq_right (show ¬ (n = n + 1) by omega), sum_eR_rough ⟨n, by omega⟩ rfl x]
    unfold phiR
    rw [ite_eq_right (show ¬ (n < n) by omega), ite_eq_left rfl, neg_add_eq_sub, sub_nonneg,
      Real.log_le_log_iff hz0 (hxpos _), Nat.cast_le]
  have hlow : PrR n z X ⟨n + 1, by omega⟩ m x ↔ X < (m : ℝ) * ∏ i, (x i : ℝ) := by
    unfold PrR
    rw [ite_eq_left rfl, sum_eR_low ⟨n + 1, by omega⟩ rfl x]
    unfold phiR
    rw [ite_eq_right (show ¬ (n + 1 < n) by omega), ite_eq_right (show ¬ (n + 1 = n) by omega), ite_eq_left rfl,
      hlogprod, sub_add_eq_add_sub, sub_pos, hlogmP, Real.log_lt_log_iff hX hmP]
  have hhigh : PrR n z X ⟨n + 2, by omega⟩ m x ↔ (m : ℝ) * ∏ i, (x i : ℝ) ≤ 2 * X := by
    unfold PrR
    rw [ite_eq_right (show ¬ (n + 2 = n + 1) by omega), sum_eR_high ⟨n + 2, by omega⟩ rfl x]
    unfold phiR
    rw [ite_eq_right (show ¬ (n + 2 < n) by omega), ite_eq_right (show ¬ (n + 2 = n) by omega),
      ite_eq_right (show ¬ (n + 2 = n + 1) by omega), hlogprod]
    have h2X : (0 : ℝ) < 2 * X := by linarith
    constructor
    · intro h
      have : Real.log (m * ∏ i, (x i : ℝ)) ≤ Real.log (2 * X) := by rw [← hlogmP]; linarith
      exact (Real.log_le_log_iff hmP h2X).1 this
    · intro h
      have := Real.log_le_log hmP h
      rw [← hlogmP] at this
      linarith
  constructor
  · intro h
    refine ⟨Fin.antitone_iff_succ_le.2 fun t => (hord t).1 (h _), hrough.1 (h _), hlow.1 (h _), hhigh.1 (h _)⟩
  · rintro ⟨ha, hr, hl, hh⟩ j
    rcases lt_or_ge j.val n with hj | hj
    · have : j = ⟨(⟨j.val, hj⟩ : Fin n).val, by omega⟩ := Fin.ext rfl
      rw [this]
      exact (hord ⟨j.val, hj⟩).2 (Fin.antitone_iff_succ_le.1 ha _)
    · rcases (show j.val = n ∨ j.val = n + 1 ∨ j.val = n + 2 by omega) with h | h | h
      · rw [show j = ⟨n, by omega⟩ from Fin.ext h]; exact hrough.2 hr
      · rw [show j = ⟨n + 1, by omega⟩ from Fin.ext h]; exact hlow.2 hl
      · rw [show j = ⟨n + 2, by omega⟩ from Fin.ext h]; exact hhigh.2 hh

theorem sum_Icc_one {M : Type*} [AddCommMonoid M] (K : ℕ) (g : ℕ → M) :
    ∑ n ∈ Finset.Icc 1 K, g n = ∑ n ∈ Finset.range K, g (n + 1) := by
  have h : Finset.Icc 1 K = (Finset.range K).map (addRightEmbedding 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addRightEmbedding_apply]
    constructor
    · intro h
      exact ⟨n - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [h, Finset.sum_map]
  rfl

section Main

open Classical

/-- **A rough cofactor as tuples of primes, with the comparisons.** For `X > 0`, `m ≥ 1`, `z(m) ≥ 2` and
`⌊2X⌋ < z(m)^{K+1}`: the sum over the `z(m)`-rough `k ≥ 2` with `⌊X⌋ < mk ≤ ⌊2X⌋` is the sum over `n < K` and the
`(n + 1)`-tuples of primes up to `⌊2X⌋`, weighted by the comparisons `PrR`. -/
theorem rough_sum_eq_box {z : ℕ → ℕ} {X : ℝ} (hX : 0 < X) {m : ℕ} (hm : 1 ≤ m) (hz2 : 2 ≤ z m) (K : ℕ)
    (hK : ⌊2 * X⌋₊ < z m ^ (K + 1)) (F : ℕ → ℂ) :
    ∑ k ∈ (Finset.Icc 2 ⌊2 * X⌋₊).filter
        (fun k => (∀ p < z m, p.Prime → ¬ p ∣ k) ∧ ⌊X⌋₊ < m * k ∧ m * k ≤ ⌊2 * X⌋₊), F (m * k) =
      ∑ n ∈ Finset.range K, ∑ x ∈ Fintype.piFinset (fun _ : Fin (n + 1) => SieveTypeIIU.primesLe ⌊2 * X⌋₊),
        (∏ j, ((if PrR n z X j m x then 1 else 0 : ℝ) : ℂ)) * F (m * ∏ i, x i) := by
  rw [← Finset.filter_filter, Finset.sum_filter,
    SieveRoughTuple.sum_rough_eq hz2 (fun k => if ⌊X⌋₊ < m * k ∧ m * k ≤ ⌊2 * X⌋₊ then F (m * k) else 0) K hK,
    sum_Icc_one]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [SieveRoughTuple.tuples, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Fintype.mem_piFinset] at hx
  have hxp : ∀ i, (x i).Prime := fun i => (Finset.mem_filter.1 (hx i)).2
  have hx1 : ∀ i, 1 ≤ x i := fun i => (hxp i).one_lt.le
  have hall := PrR_all_iff (n := n) (z := z) hX hm (by omega) hx1
  have hcast : ∀ j, ((if PrR n z X j m x then 1 else 0 : ℝ) : ℂ) = if PrR n z X j m x then 1 else 0 :=
    fun j => by split_ifs <;> simp
  rw [Finset.prod_congr rfl fun j _ => hcast j, Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- the tuple's conditions and the range are the comparisons
  have hiff : ((∀ i j : Fin (n + 1), i ≤ j → x j ≤ x i) ∧ (∀ i, z m ≤ x i) ∧ ∏ i, x i ≤ ⌊2 * X⌋₊) ∧
      (⌊X⌋₊ < m * ∏ i, x i ∧ m * ∏ i, x i ≤ ⌊2 * X⌋₊) ↔ ∀ j, PrR n z X j m x := by
    rw [hall]
    have hcastP : ((m * ∏ i, x i : ℕ) : ℝ) = (m : ℝ) * ∏ i, (x i : ℝ) := by push_cast; ring
    constructor
    · rintro ⟨⟨ha, hz, -⟩, hlo, hhi⟩
      refine ⟨fun i j hij => ha i j hij, hz _, ?_, ?_⟩
      · rw [← hcastP]; exact (Nat.floor_lt hX.le).1 hlo
      · rw [← hcastP]; exact (Nat.le_floor_iff (by linarith)).1 hhi
    · rintro ⟨ha, hz, hlo, hhi⟩
      have hhi' : m * ∏ i, x i ≤ ⌊2 * X⌋₊ := (Nat.le_floor_iff (by linarith)).2 (by rw [hcastP]; exact hhi)
      refine ⟨⟨fun i j hij => ha hij, fun i => le_trans hz (ha (Fin.le_last i)), ?_⟩,
        (Nat.floor_lt hX.le).2 (by rw [hcastP]; exact hlo), hhi'⟩
      exact le_trans (Nat.le_mul_of_pos_left _ hm) hhi'
  by_cases h : ∀ j, PrR n z X j m x
  · have h' := hiff.2 h
    rw [ite_eq_left h, one_mul, ite_eq_left h'.1, ite_eq_left h'.2]
  · rw [ite_eq_right h, zero_mul]
    split_ifs with h1 h2
    · exact absurd (hiff.1 ⟨h1, h2⟩) h
    · rfl
    · rfl

/-- **Type II for a variable times a rough cofactor.** Fix `e₀ > 0`. There are `δ > 0` and `q₀` such that for
`q ≥ q₀` and a unit `a` mod `q`: let `m` run over `S ⊆ (P₁, P₂]` with `q^{0.401L} ≤ P₁` and `P₂ ≤ q^{0.485L}`, with
coefficients `|a_m| ≤ 1` for every `m`, and let `z(m) ≥ q^{e₀}` on `S`. Then the sum over `m ∈ S` of `a_m` times the
sum, over the `k ≥ 2` with no prime factor below `z(m)` and `⌊q^L⌋ < mk ≤ ⌊2q^L⌋`, of
`1[mk ≡ a] − 1[(mk, q) = 1]/φ(q)` is at most `q^{L−δ}/φ(q)` in absolute value, `L = 2.333`. -/
theorem typeII_rough {e₀ : ℝ} (he₀ : 0 < e₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (P₁ P₂ : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P₁ P₂ →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ∀ (acoef : ℕ → ℂ), (∀ m, ‖acoef m‖ ≤ 1) →
      ∀ z : ℕ → ℕ, (∀ m ∈ S, (q : ℝ) ^ e₀ ≤ z m) →
      ‖∑ m ∈ S, acoef m * ∑ k ∈ (Finset.Icc 2 ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊).filter
          (fun k => (∀ p < z m, p.Prime → ¬ p ∣ k) ∧ ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ < m * k ∧
            m * k ≤ ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊), dw q a (m * k)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
  set Kmax : ℕ := ⌈(2333 / 1000 + 1) / e₀⌉₊ with hKmax
  obtain ⟨δ, hδ, q₁, hq₁⟩ := SieveTypeIIU.typeII_unw (Kmax + 1) (Kmax + 2) (e₁ := e₀ / 2) (E₀ := 1)
    (Λ₁ := 2333 / 1000 + 1) (half_pos he₀) zero_le_one (by norm_num)
  have hev1 := (tendsto_rpow_atTop (half_pos he₀)).eventually_ge_atTop (2 : ℝ)
  have hev2 := (tendsto_rpow_atTop (half_pos hδ)).eventually_ge_atTop (Kmax : ℝ)
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually (hev1.and hev2))
  refine ⟨δ / 2, half_pos hδ, max (max q₁ q₂) 3, ?_⟩
  intro q _ hq a ha P₁ P₂ S hS hP₁ hP₂ acoef hacoef z hz
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  obtain ⟨hqe, hqK⟩ := hq₂ q hq2
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  set X : ℝ := (q : ℝ) ^ (2333 / 1000 : ℝ) with hXdef
  have hX : 0 < X := Real.rpow_pos_of_pos hq0 _
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hP₁1 : 1 ≤ P₁ := by
    have : (1 : ℝ) ≤ (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    exact_mod_cast this.trans hP₁
  have hqe0 : (2 : ℝ) * (q : ℝ) ^ (e₀ / 2) ≤ (q : ℝ) ^ e₀ := by
    have : (q : ℝ) ^ e₀ = (q : ℝ) ^ (e₀ / 2) * (q : ℝ) ^ (e₀ / 2) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [this]
    have : (0 : ℝ) ≤ (q : ℝ) ^ (e₀ / 2) := by positivity
    nlinarith
  -- per `m`: the tuples
  have hzm : ∀ m ∈ S, 2 ≤ z m ∧ ⌊2 * X⌋₊ < z m ^ (Kmax + 1) := by
    intro m hm
    have hzm := hz m hm
    have h2 : (2 : ℝ) ≤ z m := le_trans (by nlinarith) (le_trans hqe0 hzm)
    refine ⟨by exact_mod_cast h2, ?_⟩
    have hK : (2333 / 1000 + 1 : ℝ) ≤ e₀ * (Kmax + 1) := by
      have := Nat.le_ceil ((2333 / 1000 + 1) / e₀)
      rw [← hKmax, div_le_iff₀ he₀] at this
      nlinarith
    have hpow : (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) ≤ ((z m : ℕ) : ℝ) ^ (Kmax + 1) := by
      calc (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) ≤ (q : ℝ) ^ (e₀ * (Kmax + 1)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hK
        _ = ((q : ℝ) ^ e₀) ^ (Kmax + 1) := by rw [Real.rpow_mul hq0.le, ← Real.rpow_natCast]; push_cast; ring_nf
        _ ≤ ((z m : ℕ) : ℝ) ^ (Kmax + 1) := pow_le_pow_left₀ (by positivity) hzm _
    have hlt : (⌊2 * X⌋₊ : ℝ) < (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) := by
      calc (⌊2 * X⌋₊ : ℝ) ≤ 2 * X := Nat.floor_le (by positivity)
        _ < 3 * X := by linarith
        _ ≤ (q : ℝ) * X := by nlinarith
        _ = (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) := by
            rw [Real.rpow_add hq0, Real.rpow_one, hXdef]; ring
    exact_mod_cast lt_of_lt_of_le hlt hpow
  have hrewrite : ∑ m ∈ S, acoef m * ∑ k ∈ (Finset.Icc 2 ⌊2 * X⌋₊).filter
        (fun k => (∀ p < z m, p.Prime → ¬ p ∣ k) ∧ ⌊X⌋₊ < m * k ∧ m * k ≤ ⌊2 * X⌋₊), dw q a (m * k) =
      ∑ n ∈ Finset.range Kmax, Dsum q a (S ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => SieveTypeIIU.primesLe ⌊2 * X⌋₊))
        (fun mx => mx.1 * ∏ i, mx.2 i)
        (fun mx => acoef mx.1 * ∏ j, ((if PrR n z X j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) := by
    rw [Finset.sum_congr rfl fun m hm => by
      rw [rough_sum_eq_box hX (by have := (Finset.mem_Ioc.1 (hS hm)).1; omega) (hzm m hm).1 Kmax (hzm m hm).2
        (fun n => dw q a n)]]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold Dsum
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hrewrite]
  refine (norm_sum_le _ _).trans ?_
  have hbound : ∀ n ∈ Finset.range Kmax, ‖Dsum q a (S ×ˢ Fintype.piFinset
      (fun _ : Fin (n + 1) => SieveTypeIIU.primesLe ⌊2 * X⌋₊))
      (fun mx => mx.1 * ∏ i, mx.2 i)
      (fun mx => acoef mx.1 * ∏ j, ((if PrR n z X j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
    intro n hn
    have hnK := Finset.mem_range.1 hn
    have hφ : ∀ j, ∀ m ∈ S, phiR n z X j m ≤ (2333 / 1000 + 1) * Real.log q := by
      intro j m hm
      have hm1 : 1 ≤ m := by have := (Finset.mem_Ioc.1 (hS hm)).1; omega
      have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1'
      have hmX : (m : ℝ) ≤ X := by
        have h1 : (m : ℝ) ≤ P₂ := by exact_mod_cast (Finset.mem_Ioc.1 (hS hm)).2
        have h2 : (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) ≤ X :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        linarith
      have hzlog : 0 ≤ Real.log (z m) := Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) (hzm m hm).1))
      have hlog2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) (by linarith)
      have hlogX : Real.log X = 2333 / 1000 * Real.log q := by rw [hXdef, Real.log_rpow hq0]
      unfold phiR
      split_ifs
      · positivity
      · linarith
      · have := Real.log_le_log (by linarith) hmX
        linarith
      · rw [Real.log_mul (by norm_num) hX.ne', hlogX]
        linarith
    set piv : Fin (n + 3) → Fin (n + 1) := fun j => if h : j.val < n then ⟨j.val, by omega⟩ else Fin.last n
      with hpiv
    have hpivs : ∀ j, eR n j (piv j) = 1 ∨ eR n j (piv j) = -1 := by
      intro j
      by_cases h : j.val < n
      · left
        simp only [hpiv, h, dite_true, eR, ite_true]
      · rcases (show j.val = n ∨ j.val = n + 1 ∨ j.val = n + 2 by omega) with h' | h' | h'
        · left
          simp [hpiv, eR, h']
        · left
          simp [eR, h']
        · right
          simp [eR, h']
    have hsupp : ∀ m ∈ S, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) → (∀ j, PrR n z X j m x) →
        (∀ i, 2 * (q : ℝ) ^ (e₀ / 2) ≤ x i) ∧ (m : ℝ) * ∏ i, (x i : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) := by
      intro m hm x hx hall
      have hm1 : 1 ≤ m := by have := (Finset.mem_Ioc.1 (hS hm)).1; omega
      obtain ⟨ha, hzl, -, hhi⟩ := (PrR_all_iff hX hm1 (by have := (hzm m hm).1; omega)
        (fun i => (hx i).one_lt.le)).1 hall
      refine ⟨fun i => ?_, hhi⟩
      have h1 : z m ≤ x i := le_trans hzl (ha (Fin.le_last i))
      have h2 : (z m : ℝ) ≤ x i := by exact_mod_cast h1
      linarith [hz m hm]
    exact hq₁ q hq1 a ha P₁ P₂ S hS hP₁ hP₂ acoef hacoef n (by omega) (J := n + 3) (by omega) (phiR n z X) (eR n)
      (PrR n z X) (fun j i => abs_eR_le n j i) (PrR_spec n z X) hφ piv hpivs hsupp
  refine (Finset.sum_le_card_nsmul _ _ _ hbound).trans ?_
  rw [Finset.card_range, nsmul_eq_mul]
  calc (Kmax : ℝ) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ))
      ≤ (q : ℝ) ^ (δ / 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ)) :=
        mul_le_mul_of_nonneg_right hqK (by positivity)
    _ = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ / 2 : ℝ) := by
        rw [mul_left_comm, ← Real.rpow_add hq0]
        congr 2
        ring

end Main

end SieveTypeIIR
