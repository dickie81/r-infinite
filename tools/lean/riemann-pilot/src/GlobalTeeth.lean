/-
# The global step in 2D: Jacobi's two-square theorem (round 187)

Plain statement. The number of whole-number points on the circle `x² + y² = n` is
`4 · Σ_{d ∣ n} χ₄(d)` for every `n ≥ 1` (`two_sq_count`). Equivalently, prime by prime
(`R_two_pow_mul`, `R_one_mod_four_pow_mul`, `R_three_pow_mul`): write `n = pᵏ·m` with `p ∤ m`; then the count on shell `n` is the count on
shell `m` times the prime-`p` factor
* `1` if `p = 2`,
* `k + 1` if `p ≡ 1 (mod 4)` (the prime splits into two tilted Gaussian primes),
* `1` or `0` (as `k` is even or odd) if `p ≡ 3 (mod 4)` (the prime stays a single wheel of radius `p`).
So the teeth on each shell are exactly a product of one factor per prime: the global step of
round 182, proved for the 2D ball. (Siegel's formula for general `d ≤ 8` is not attempted.)

Proof: Gaussian integers `ℤ[i]`. Multiplying by `π` maps shell `m` onto the part of shell
`N(π)·m` divisible by `π` (`image_mul_shell`). For `p ≡ 1` the shell splits as the union of the
`π`- and `π̄`-divisible parts with overlap the `p`-divisible part, giving
`t_{k+1} = 2 t_k − t_{k−1}`, so `t_k = (k+1) t_0`.
-/
import Mathlib

open Finset GaussianInt
open scoped Classical

namespace GlobalTeeth

lemma norm_eq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

/-- Shell `n` of the 2D lattice ball, as Gaussian integers. -/
def shell (n : ℕ) : Finset GaussianInt :=
  ((Icc (-(n : ℤ)) (n : ℤ) ×ˢ Icc (-(n : ℤ)) (n : ℤ)).filter (fun p : ℤ × ℤ => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ))).image
    (fun p => (⟨p.1, p.2⟩ : GaussianInt))

lemma mem_shell {n : ℕ} {z : GaussianInt} : z ∈ shell n ↔ z.norm = n := by
  rw [shell, mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_filter] at hp
    rw [norm_eq]; exact hp.2
  · intro h
    rw [norm_eq] at h
    have h1 : z.re ^ 2 ≤ n := by nlinarith [sq_nonneg z.im]
    have h2 : z.im ^ 2 ≤ n := by nlinarith [sq_nonneg z.re]
    have a1 := Int.le_self_sq z.re
    have a2 := Int.le_self_sq (-z.re)
    have a3 := Int.le_self_sq z.im
    have a4 := Int.le_self_sq (-z.im)
    rw [neg_sq] at a2 a4
    refine ⟨(z.re, z.im), ?_, rfl⟩
    simp only [mem_filter, mem_product, mem_Icc]
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, h⟩

/-- The number of teeth on shell `n`. -/
def R (n : ℕ) : ℕ := (shell n).card

/-- The same count on integer pairs. -/
theorem R_eq_pairs (n : ℕ) :
    R n = ((Icc (-(n : ℤ)) (n : ℤ) ×ˢ Icc (-(n : ℤ)) (n : ℤ)).filter (fun p : ℤ × ℤ => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ))).card := by
  unfold R shell
  refine card_image_of_injective _ fun p q h => ?_
  simp only [Zsqrtd.mk.injEq] at h
  exact Prod.ext h.1 h.2

lemma R_one : R 1 = 4 := by rw [R_eq_pairs]; decide

/-- Multiplying by `π` maps shell `m` bijectively onto the `π`-divisible part of shell `N(π)·m`. -/
lemma image_mul_shell {π : GaussianInt} (hπ : π ≠ 0) {N : ℕ} (hN : π.norm = N) (m : ℕ) :
    (shell m).image (π * ·) = (shell (N * m)).filter (π ∣ ·) := by
  ext w
  simp only [mem_image, mem_filter, mem_shell]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨by rw [Zsqrtd.norm_mul, hN, hz]; push_cast; ring, dvd_mul_right _ _⟩
  · rintro ⟨hw, z, rfl⟩
    refine ⟨z, ?_, rfl⟩
    rw [Zsqrtd.norm_mul, hN] at hw
    have hN0 : (N : ℤ) ≠ 0 := by
      rw [← hN]; exact fun h => hπ (Zsqrtd.norm_eq_zero (fun n hn => by nlinarith [mul_self_nonneg n]) π |>.mp h)
    push_cast at hw
    exact mul_left_cancel₀ hN0 hw

lemma card_image_mul {π : GaussianInt} (hπ : π ≠ 0) (m : ℕ) : ((shell m).image (π * ·)).card = R m :=
  card_image_of_injective _ (mul_right_injective₀ hπ)

lemma card_filter_dvd {π : GaussianInt} (hπ : π ≠ 0) {N : ℕ} (hN : π.norm = N) (m : ℕ) :
    ((shell (N * m)).filter (π ∣ ·)).card = R m := by
  rw [← image_mul_shell hπ hN, card_image_mul hπ]

/-! ### `p = 2` -/

lemma one_add_i_dvd {w : GaussianInt} (h : Even w.norm) : (⟨1, 1⟩ : GaussianInt) ∣ w := by
  rw [norm_eq] at h
  have hpar : Even (w.re + w.im) := by
    have : Even (w.re ^ 2 + w.im ^ 2 + 2 * (w.re * w.im)) := h.add (even_two_mul _)
    have e : w.re ^ 2 + w.im ^ 2 + 2 * (w.re * w.im) = (w.re + w.im) ^ 2 := by ring
    rw [e] at this
    exact (Int.even_pow.mp this).1
  obtain ⟨s, hs⟩ := hpar
  refine ⟨⟨s, s - w.re⟩, ?_⟩
  apply Zsqrtd.ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]; linarith

lemma R_two_mul (m : ℕ) : R (2 * m) = R m := by
  have hπ : (⟨1, 1⟩ : GaussianInt) ≠ 0 := fun h => by
    have := congrArg Zsqrtd.re h; simp at this
  have hN : (⟨1, 1⟩ : GaussianInt).norm = (2 : ℕ) := by rw [norm_eq]; norm_num
  rw [← card_filter_dvd hπ hN m, R]
  congr 1
  refine (filter_true_of_mem fun w hw => one_add_i_dvd ?_).symm
  rw [mem_shell.mp hw]; push_cast; exact even_two_mul _

lemma R_two_pow_mul (k m : ℕ) : R (2 ^ k * m) = R m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc, R_two_mul, ih]

/-! ### `p ≡ 3 (mod 4)` -/

lemma dvd_both_of_three {p : ℕ} [hp : Fact p.Prime] (h3 : p % 4 = 3) {x y : ℤ}
    (h : (p : ℤ) ∣ x ^ 2 + y ^ 2) : (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  have hsq : ¬ IsSquare (-1 : ZMod p) := fun h => (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp h h3
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast at h
  by_cases hy : (y : ZMod p) = 0
  · rw [hy] at h ⊢; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      pow_eq_zero_iff] at h; exact ⟨h, rfl⟩
  · exfalso
    apply hsq
    have h' : ((x : ZMod p) / y) ^ 2 + 1 = 0 := by
      rw [div_pow, div_add_one (pow_ne_zero 2 hy), h, zero_div]
    exact ⟨(x : ZMod p) / y, (eq_neg_of_add_eq_zero_left h').symm.trans (sq _)⟩

lemma p_dvd_of_three {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) {w : GaussianInt} (h : (p : ℤ) ∣ w.norm) :
    (p : GaussianInt) ∣ w := by
  rw [norm_eq] at h
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := dvd_both_of_three h3 h
  refine ⟨⟨a, b⟩, ?_⟩
  apply Zsqrtd.ext <;> simp [ha, hb]

lemma R_three_zero {p : ℕ} [hp : Fact p.Prime] (h3 : p % 4 = 3) {m : ℕ} (hm : ¬ p ∣ m) :
    R (p * m) = 0 := by
  rw [R, card_eq_zero, eq_empty_iff_forall_notMem]
  intro w hw
  rw [mem_shell] at hw
  obtain ⟨z, rfl⟩ := p_dvd_of_three h3 (by rw [hw]; push_cast; exact dvd_mul_right _ _)
  rw [Zsqrtd.norm_mul, Zsqrtd.norm_natCast] at hw
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  push_cast at hw
  have hmz : (p : ℤ) * z.norm = m := mul_left_cancel₀ hp0 (by linear_combination hw)
  exact hm (Int.natCast_dvd_natCast.mp ⟨z.norm, hmz.symm⟩)

lemma R_three_sq_mul {p : ℕ} [hp : Fact p.Prime] (h3 : p % 4 = 3) (m : ℕ) :
    R (p ^ 2 * m) = R m := by
  have hπ : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hN : (p : GaussianInt).norm = ((p ^ 2 : ℕ) : ℤ) := by rw [Zsqrtd.norm_natCast]; push_cast; ring
  rw [← card_filter_dvd hπ hN m, R]
  congr 1
  refine (filter_true_of_mem fun w hw => p_dvd_of_three h3 ?_).symm
  rw [mem_shell.mp hw]; push_cast; exact Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _

lemma R_three_pow_mul {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) {m : ℕ} (hm : ¬ p ∣ m) (k : ℕ) :
    R (p ^ k * m) = if Even k then R m else 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · simp
    · simp [R_three_zero h3 hm]
    · rw [show p ^ (k + 2) * m = p ^ 2 * (p ^ k * m) by ring, R_three_sq_mul h3, ih k (by omega)]
      simp [Nat.even_add]

/-! ### `p ≡ 1 (mod 4)` -/

section Split

variable {p : ℕ} [hp : Fact p.Prime] (h1 : p % 4 = 1)
include h1

lemma irreducible_of_norm_prime {π : GaussianInt} (hN : π.norm = p) : Irreducible π := by
  refine ⟨fun hu => ?_, fun u v huv => ?_⟩
  · have := (Zsqrtd.norm_eq_one_iff' (by norm_num) π).mpr hu
    rw [hN] at this; have := hp.out.one_lt; omega
  · have hn : u.norm * v.norm = p := by rw [← Zsqrtd.norm_mul, ← huv, hN]
    have hu0 : 0 ≤ u.norm := Zsqrtd.norm_nonneg (by norm_num) u
    have hv0 : 0 ≤ v.norm := Zsqrtd.norm_nonneg (by norm_num) v
    have hnat : u.norm.toNat * v.norm.toNat = p := by
      have := congrArg Int.toNat hn
      rwa [Int.toNat_mul hu0 hv0, Int.toNat_natCast] at this
    rcases (Nat.prime_mul_iff.mp (hnat ▸ hp.out)) with ⟨_, hv1⟩ | ⟨hu1, _⟩
    · right; rw [← Zsqrtd.norm_eq_one_iff' (by norm_num)]; omega
    · left; rw [← Zsqrtd.norm_eq_one_iff' (by norm_num)]; omega

lemma exists_split : ∃ π : GaussianInt, π.norm = p ∧ π * star π = p ∧ ¬ (star π ∣ π) := by
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have hab' : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = p := by exact_mod_cast hab
  refine ⟨⟨a, b⟩, ?_, ?_, ?_⟩
  · rw [norm_eq]; exact hab'
  · apply Zsqrtd.ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> first | linear_combination hab' | ring
  · intro hd
    -- `π̄ ∣ π` forces `π̄ ∣ π + π̄ = 2a`, so `p ∣ 4a²`, so `p ∣ a`, impossible
    have h2 : star (⟨a, b⟩ : GaussianInt) ∣ ((2 * a : ℕ) : GaussianInt) := by
      have : ((2 * a : ℕ) : GaussianInt) = ⟨a, b⟩ + star ⟨a, b⟩ := by
        apply Zsqrtd.ext <;> simp; ring
      rw [this]; exact dvd_add hd dvd_rfl
    have hn : (star (⟨a, b⟩ : GaussianInt)).norm ∣ ((2 * a : ℕ) : GaussianInt).norm := by
      obtain ⟨c, hc⟩ := h2; exact ⟨c.norm, by rw [hc, Zsqrtd.norm_mul]⟩
    rw [Zsqrtd.norm_natCast, Zsqrtd.norm_conj, norm_eq] at hn
    simp only at hn
    have hp' : (p : ℤ) ∣ (2 * a) * (2 * a) := by
      have e : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) = p := by exact_mod_cast hab
      rw [e] at hn; exact_mod_cast hn
    have hpa : p ∣ a := by
      have : p ∣ (2 * a) * (2 * a) := by exact_mod_cast hp'
      have h2a : p ∣ 2 * a := (Nat.Prime.dvd_mul hp.out).mp this |>.elim id id
      rcases (Nat.Prime.dvd_mul hp.out).mp h2a with h | h
      · have := Nat.le_of_dvd (by norm_num) h; have := hp.out.two_le; omega
      · exact h
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      have hpb : p = b * b := by rw [← hab]; ring
      have hb1 : b = 1 := by
        rcases Nat.prime_mul_iff.mp (hpb ▸ hp.out) with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
      rw [hb1] at hpb
      have := hp.out.two_le
      omega
    · have := Nat.le_of_dvd ha hpa
      have : p * p ≤ a * a := Nat.mul_le_mul this this
      have hp2 := hp.out.two_le
      nlinarith

end Split

lemma star_dvd_iff {π w : GaussianInt} : π ∣ star w ↔ star π ∣ w := by
  constructor
  · rintro ⟨c, hc⟩; exact ⟨star c, by rw [← star_star w, hc, star_mul, mul_comm]⟩
  · rintro ⟨c, rfl⟩; exact ⟨star c, by rw [star_mul, star_star, mul_comm]⟩

lemma R_one_mod_four_pow_mul {p : ℕ} [hp : Fact p.Prime] (h1 : p % 4 = 1) {m : ℕ} (hm : ¬ p ∣ m)
    (k : ℕ) : R (p ^ k * m) = (k + 1) * R m := by
  obtain ⟨π, hN, hππ, hnd⟩ := exists_split h1
  have hπ0 : π ≠ 0 := fun h => by
    rw [h, Zsqrtd.norm_zero] at hN; exact hp.out.ne_zero (by exact_mod_cast hN.symm)
  have hNs : (star π).norm = p := by rw [Zsqrtd.norm_conj, hN]
  have hs0 : star π ≠ 0 := fun h => hπ0 (by simpa using congrArg star h)
  have hpπ : Prime π := irreducible_iff_prime.mp (irreducible_of_norm_prime h1 hN)
  have hpπs : Prime (star π) :=
    irreducible_iff_prime.mp (irreducible_of_norm_prime h1 hNs)
  have hp0 : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hNp : (p : GaussianInt).norm = ((p * p : ℕ) : ℤ) := by rw [Zsqrtd.norm_natCast]; push_cast; ring
  -- every point of a shell divisible by `p` splits as `π` or `π̄`
  have hcover : ∀ n, p ∣ n → ∀ w ∈ shell n, π ∣ w ∨ star π ∣ w := by
    intro n hn w hw
    have : π ∣ w * star w := by
      rw [← Zsqrtd.norm_eq_mul_conj, mem_shell.mp hw]
      obtain ⟨c, rfl⟩ := hn
      refine ⟨star π * c, ?_⟩
      push_cast
      rw [← hππ]; ring
    rcases hpπ.dvd_or_dvd this with h | h
    · exact Or.inl h
    · exact Or.inr (star_dvd_iff.mp h)
  have hboth : ∀ w : GaussianInt, (π ∣ w ∧ star π ∣ w) ↔ (p : GaussianInt) ∣ w := by
    intro w
    constructor
    · rintro ⟨⟨t, rfl⟩, h2⟩
      rcases hpπs.dvd_or_dvd h2 with h | h
      · exact absurd h hnd
      · obtain ⟨s, rfl⟩ := h; exact ⟨s, by rw [← hππ]; ring⟩
    · rintro ⟨s, rfl⟩
      rw [← hππ]; exact ⟨dvd_mul_of_dvd_left (dvd_mul_right _ _) _,
        dvd_mul_of_dvd_left (dvd_mul_left _ _) _⟩
  -- the recursion
  have step : ∀ j, (R (p ^ (j + 1) * m) : ℤ) + (if j = 0 then 0 else R (p ^ (j - 1) * m)) =
      2 * R (p ^ j * m) := by
    intro j
    set S := shell (p ^ (j + 1) * m)
    have hsplit : S = S.filter (π ∣ ·) ∪ S.filter (star π ∣ ·) := by
      ext w; simp only [mem_union, mem_filter]
      constructor
      · intro hw; rcases hcover _ (by rw [pow_succ]; exact Dvd.dvd.mul_right (dvd_mul_left _ _) _) w hw
          with h | h
        · exact Or.inl ⟨hw, h⟩
        · exact Or.inr ⟨hw, h⟩
      · rintro (h | h) <;> exact h.1
    have hinter : S.filter (π ∣ ·) ∩ S.filter (star π ∣ ·) = S.filter ((p : GaussianInt) ∣ ·) := by
      ext w; simp only [mem_inter, mem_filter, ← hboth]; tauto
    have hA : (S.filter (π ∣ ·)).card = R (p ^ j * m) := by
      have := card_filter_dvd hπ0 hN (p ^ j * m)
      rwa [show p * (p ^ j * m) = p ^ (j + 1) * m by ring] at this
    have hB : (S.filter (star π ∣ ·)).card = R (p ^ j * m) := by
      have := card_filter_dvd hs0 hNs (p ^ j * m)
      rwa [show p * (p ^ j * m) = p ^ (j + 1) * m by ring] at this
    have hC : (S.filter ((p : GaussianInt) ∣ ·)).card = if j = 0 then 0 else R (p ^ (j - 1) * m) := by
      rcases j with _ | j
      · simp only [ite_true]
        rw [card_eq_zero, eq_empty_iff_forall_notMem]
        intro w hw
        rw [mem_filter, mem_shell] at hw
        obtain ⟨z, rfl⟩ := hw.2
        have h := hw.1
        rw [Zsqrtd.norm_mul, Zsqrtd.norm_natCast] at h
        have hp0' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
        have : (p : ℤ) * z.norm = m := by
          push_cast at h; exact mul_left_cancel₀ hp0' (by linear_combination h)
        exact hm (by exact_mod_cast (Dvd.intro _ this))
      · simp only [Nat.add_sub_cancel, add_eq_zero, one_ne_zero, and_false, ite_false]
        have := card_filter_dvd hp0 hNp (p ^ j * m)
        rwa [show p * p * (p ^ j * m) = p ^ (j + 1 + 1) * m by ring] at this
    have hS : S.card = R (p ^ (j + 1) * m) := rfl
    have hcard := card_union_add_card_inter (S.filter (π ∣ ·)) (S.filter (star π ∣ ·))
    rw [← hsplit, hinter, hA, hB, hC, hS] at hcard
    split_ifs at hcard ⊢ <;> push_cast <;> omega
  -- solve the recursion
  have main : ∀ j : ℕ, (R (p ^ j * m) : ℤ) = ((j : ℤ) + 1) * R m := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      rcases j with _ | _ | j
      · simp
      · have := step 0; simp at this; (try simp only [zero_add, pow_one]); push_cast; linarith
      · have := step (j + 1)
        simp only [add_eq_zero, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel] at this
        rw [ih (j + 1) (by omega), ih j (by omega)] at this
        push_cast at this ⊢
        linarith
  have := main k
  exact_mod_cast this

/-! ### The divisor side and the assembly -/

/-- `f(n) = Σ_{d ∣ n} χ₄(d)`. -/
def f (n : ℕ) : ℤ := ∑ d ∈ n.divisors, ZMod.χ₄ d

lemma f_mul {a b : ℕ} (h : a.Coprime b) : f (a * b) = f a * f b := by
  unfold f
  rw [Nat.Coprime.divisors_mul h, sum_map, sum_mul_sum, ← sum_product']
  rw [← sum_attach (a.divisors ×ˢ b.divisors)]
  refine sum_congr rfl fun x _ => ?_
  simp [Nat.cast_mul, map_mul]

lemma f_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    f (p ^ k) = ∑ j ∈ range (k + 1), (ZMod.χ₄ p) ^ j := by
  unfold f
  rw [Nat.divisors_prime_pow hp, sum_map]
  simp [map_pow]

lemma geom_neg_one (k : ℕ) : ∑ j ∈ range (k + 1), ((-1 : ℤ)) ^ j = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd k with he | ho
    · simp [he, Nat.even_add_one, he.neg_one_pow, pow_succ]
    · simp [Nat.not_even_iff_odd.mpr ho, Nat.even_add_one, ho.neg_one_pow, pow_succ]

/-- **Jacobi's two-square theorem:** the number of whole-number points on `x² + y² = n` is
`4 · Σ_{d ∣ n} χ₄(d)`. -/
theorem two_sq_count (n : ℕ) (hn : 0 < n) : (R n : ℤ) = 4 * f n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rw [R_one]; simp [f]
    obtain ⟨p, hp, hpn⟩ : ∃ p, p.Prime ∧ p ∣ n :=
      ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
    have hk : k ≠ 0 := by
      rintro rfl
      simp only [pow_zero, one_mul] at hkm
      exact hm (hkm ▸ hpn)
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hkm; omega)
    have hmlt : m < n := by
      have : 2 ≤ p ^ k := (Nat.one_lt_pow hk hp.one_lt)
      rw [hkm]; nlinarith
    rw [hkm]
    have hcop : (p ^ k).Coprime m := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
    rw [f_mul hcop, f_prime_pow hp]
    have ihm := ih m hmlt hm0
    have hodd : p ≠ 2 → p % 4 = 1 ∨ p % 4 = 3 := fun h2 => by
      have : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
      omega
    by_cases h2 : p = 2
    · subst h2
      rw [R_two_pow_mul, ihm]
      have : ZMod.χ₄ ((2 : ℕ) : ZMod 4) = 0 := by decide
      rw [this, sum_range_succ']
      simp
    · rcases hodd h2 with h1 | h3
      · rw [R_one_mod_four_pow_mul h1 hm, ZMod.χ₄_nat_one_mod_four h1]
        push_cast; rw [ihm]; simp; ring
      · rw [R_three_pow_mul h3 hm, ZMod.χ₄_nat_three_mod_four h3, geom_neg_one]
        split_ifs <;> simp [ihm]

end GlobalTeeth
