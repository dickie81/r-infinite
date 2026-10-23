/-
# Round 604: Type I counts in a residue class (milestone M5)

Plain statements, for `N₁ ≤ N₂`.

* `card_Ioc_modEq`: the integers of `(N₁, N₂]` in a residue class mod `r > 0` number `(N₂ − N₁)/r` within `1`.
* `card_A`: for `M > 0` prime to `q > 0`, the `n ∈ (N₁, N₂]` with `n ≡ a (mod q)` and `M ∣ n` number
  `(N₂ − N₁)/(Mq)` within `1`.
* `card_B`: for `M > 0` prime to `q > 0`, the `n ∈ (N₁, N₂]` prime to `q` with `M ∣ n` number
  `φ(q)(N₂ − N₁)/(Mq)` within `φ(q)`.

These are the counts `|A_d|` and `|B_d|` of `frontier/linnik/SIEVE-ROUTE.md` §1 that Lemma 5 (§5) and the leaves of
§13's M5 use. The file imports only Mathlib.
-/
import Mathlib

open Finset

namespace SieveCount

/-- For `N₁ ≤ N₂`, the integers of `(N₁, N₂]` in a residue class mod `r > 0` number `(N₂ − N₁)/r` within `1`. -/
theorem card_Ioc_modEq {N₁ N₂ r : ℕ} (hr : 0 < r) (hN : N₁ ≤ N₂) (v : ℕ) :
    |((#{x ∈ Ioc N₁ N₂ | x ≡ v [MOD r]} : ℕ) : ℝ) - ((N₂ : ℝ) - N₁) / r| ≤ 1 := by
  have h := Nat.Ioc_filter_modEq_card N₁ N₂ hr v
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  set A : ℚ := ((N₂ : ℚ) - v) / r with hA
  set B : ℚ := ((N₁ : ℚ) - v) / r with hB
  have hAB : B ≤ A := by
    rw [hA, hB]; apply div_le_div_of_nonneg_right _ hr'.le; have : (N₁ : ℚ) ≤ N₂ := by exact_mod_cast hN
    linarith
  have hfl : ⌊B⌋ ≤ ⌊A⌋ := Int.floor_le_floor hAB
  rw [max_eq_left (by linarith)] at h
  have hc : ((#{x ∈ Ioc N₁ N₂ | x ≡ v [MOD r]} : ℕ) : ℚ) = ((⌊A⌋ - ⌊B⌋ : ℤ) : ℚ) := by
    rw [← h]; push_cast; rfl
  have hdiff : A - B = ((N₂ : ℚ) - N₁) / r := by rw [hA, hB]; field_simp; ring
  have h1 := Int.floor_le A
  have h2 := Int.lt_floor_add_one A
  have h3 := Int.floor_le B
  have h4 := Int.lt_floor_add_one B
  have key : |((#{x ∈ Ioc N₁ N₂ | x ≡ v [MOD r]} : ℕ) : ℚ) - ((N₂ : ℚ) - N₁) / r| ≤ 1 := by
    rw [hc, ← hdiff, abs_le]
    push_cast
    constructor <;> linarith
  have : ((((#{x ∈ Ioc N₁ N₂ | x ≡ v [MOD r]} : ℕ) : ℚ) - ((N₂ : ℚ) - N₁) / r : ℚ) : ℝ) =
      ((#{x ∈ Ioc N₁ N₂ | x ≡ v [MOD r]} : ℕ) : ℝ) - ((N₂ : ℝ) - N₁) / r := by push_cast; ring
  rw [← this]
  exact_mod_cast key

/-- **Type I for `A`.** For `N₁ ≤ N₂` and `M > 0` coprime to `q > 0`, the `n ∈ (N₁, N₂]` with `n ≡ a (mod q)` and
`M ∣ n` number `(N₂ − N₁)/(Mq)` within `1`. -/
theorem card_A {N₁ N₂ q M : ℕ} (hq : 0 < q) (hM : 0 < M) (hcop : Nat.Coprime M q) (hN : N₁ ≤ N₂) (a : ℕ) :
    |((#{n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ M ∣ n} : ℕ) : ℝ) - ((N₂ : ℝ) - N₁) / (M * q)| ≤ 1 := by
  -- the class `c ≡ 0 (mod M)`, `c ≡ a (mod q)`
  obtain ⟨c, hc⟩ := Nat.chineseRemainder hcop 0 a
  have hset : {n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ M ∣ n} = {n ∈ Ioc N₁ N₂ | n ≡ c [MOD M * q]} := by
    refine Finset.filter_congr fun n _ => ?_
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    constructor
    · rintro ⟨ha, hd⟩
      exact ⟨(Nat.modEq_zero_iff_dvd.2 hd).trans hc.1.symm, ha.trans hc.2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2.trans hc.2, Nat.modEq_zero_iff_dvd.1 (h1.trans hc.1)⟩
  rw [hset]
  have h := card_Ioc_modEq (r := M * q) (Nat.mul_pos hM hq) hN c
  push_cast at h
  exact h

/-- **Type I for `B`.** For `N₁ ≤ N₂` and `M > 0` coprime to `q > 0`, the `n ∈ (N₁, N₂]` prime to `q` with `M ∣ n`
number `φ(q)(N₂ − N₁)/(Mq)` within `φ(q)`. -/
theorem card_B {N₁ N₂ q M : ℕ} (hq : 0 < q) (hM : 0 < M) (hcop : Nat.Coprime M q) (hN : N₁ ≤ N₂) :
    |((#{n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ M ∣ n} : ℕ) : ℝ) - q.totient * (((N₂ : ℝ) - N₁) / (M * q))| ≤
      q.totient := by
  set t := (Finset.range q).filter (fun b => Nat.Coprime b q) with ht
  have htot : t.card = q.totient := by
    rw [ht, Nat.totient_eq_card_coprime]
    congr 1
    ext b
    simp [Nat.coprime_comm]
  have hfib := Finset.card_eq_sum_card_fiberwise (s := {n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ M ∣ n}) (t := t)
    (f := fun n => n % q) (fun n hn => by
      have hn' := Finset.mem_filter.1 (Finset.mem_coe.1 hn)
      refine Finset.mem_coe.2 ?_
      rw [ht, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hq, ?_⟩
      rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
      exact hn'.2.1)
  have hfiber : ∀ b ∈ t, {n ∈ {n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ M ∣ n} | n % q = b} =
      {n ∈ Ioc N₁ N₂ | n ≡ b [MOD q] ∧ M ∣ n} := by
    intro b hb
    rw [ht, Finset.mem_filter, Finset.mem_range] at hb
    ext n
    simp only [Finset.mem_filter, Nat.ModEq, Nat.mod_eq_of_lt hb.1]
    constructor
    · rintro ⟨⟨hI, -, hd⟩, hm⟩
      exact ⟨hI, hm, hd⟩
    · rintro ⟨hI, hm, hd⟩
      refine ⟨⟨hI, ?_, hd⟩, hm⟩
      have h2 := hb.2
      rw [← hm] at h2
      rw [Nat.Coprime] at h2 ⊢
      rwa [← Nat.gcd_rec, Nat.gcd_comm] at h2
  rw [hfib, Nat.cast_sum, ← htot]
  have hsum : ∑ b ∈ t, ((#{n ∈ {n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ M ∣ n} | n % q = b} : ℕ) : ℝ) -
      (t.card : ℝ) * (((N₂ : ℝ) - N₁) / (M * q)) =
      ∑ b ∈ t, (((#{n ∈ Ioc N₁ N₂ | n ≡ b [MOD q] ∧ M ∣ n} : ℕ) : ℝ) - ((N₂ : ℝ) - N₁) / (M * q)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun b hb => by rw [hfiber b hb]
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ b ∈ t, |((#{n ∈ Ioc N₁ N₂ | n ≡ b [MOD q] ∧ M ∣ n} : ℕ) : ℝ) - ((N₂ : ℝ) - N₁) / (M * q)|
      ≤ ∑ _b ∈ t, (1 : ℝ) := Finset.sum_le_sum fun b _ => card_A hq hM hcop hN b
    _ = t.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end SieveCount
