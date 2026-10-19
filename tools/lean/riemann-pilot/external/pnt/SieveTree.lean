/-
# Round 604: Buchstab's tree over a finite set (milestone M5)

Plain statements. `rough z n` says that `n` has no prime factor below `z`; `S C m z` is `S(C_m, z)`, the number of
`n ∈ C` with `m ∣ n` and `rough z n`; `primesIco w z` is the set of primes of `[w, z)`.

* `tree_pt`: Buchstab's tree at one `n`. For `w ≤ z₀` and `r ≤ X` with every prime factor of `r` at least `z₀`,
  `[r ∣ n, rough z₀ n]` is the leaves' sum `Σ_{P ⊆ [w, z₀), r∏P ≤ X} (−1)^{|P|} [r∏P ∣ n, rough w n]` plus the stops'
  sum `Σ_{w ≤ p < z₀} Σ_{P ⊆ (p, z₀), r∏P ≤ X < r∏P·p} (−1)^{|P|+1} [r∏P·p ∣ n, rough p n]`, over sets `P` of primes.
* `tree_sum`: the same summed over a finite set `C`, as an identity of the counts `S`.

This is Buchstab's identity iterated from `z₀` down to `w`, each branch stopped once its product would pass the
threshold `X`: the tree of Proposition 6 in `frontier/linnik/SIEVE-ROUTE.md` §5, for §13's M5.

The proof: for `n` with `r ∣ n` and `rough w n`, let `Q` be the primes of `[w, z₀)` that divide `n`. The leaves that
count `n` are the `P ⊆ Q`, and the stops those with `p = min Q`. `alt_cancel`,
`Σ_{P⊆Q} (−1)^{|P|}[a∏P ≤ X] + Σ_{P'⊆Q∖{q}} (−1)^{|P'|+1}[a∏P' ≤ X < a∏P'q] = 0` with `q = min Q`, leaves `[Q = ∅]`.

The file imports only Mathlib.
-/
import Mathlib

open Finset

namespace SieveTree

/-- `n` has no prime factor below `z`. -/
def rough (z n : ℕ) : Prop := ∀ p < z, p.Prime → ¬ p ∣ n

instance (z n : ℕ) : Decidable (rough z n) := by unfold rough; infer_instance

/-- `S(C_m, z)`: the `n ∈ C` divisible by `m` with no prime factor below `z`. -/
def S (C : Finset ℕ) (m z : ℕ) : ℕ := #{n ∈ C | m ∣ n ∧ rough z n}

/-- The primes of `[w, z)`. -/
def primesIco (w z : ℕ) : Finset ℕ := (Finset.Ico w z).filter Nat.Prime

theorem rough_mono {w z n : ℕ} (h : w ≤ z) (hz : rough z n) : rough w n :=
  fun p hp hpp => hz p (lt_of_lt_of_le hp h) hpp

/-- For a set `P` of primes, `∏P ∣ n` iff every `p ∈ P` divides `n`. -/
theorem prod_dvd_iff {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (n : ℕ) : (∏ p ∈ P, p) ∣ n ↔ ∀ p ∈ P, p ∣ n := by
  constructor
  · intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem _ hp) h
  · intro h
    exact Finset.prod_primes_dvd n (fun p hp => (hP p hp).prime) h

/-- `r`, whose primes are at least `z`, is prime to a product of primes below `z`. -/
theorem coprime_r {r z : ℕ} (hr : ∀ p : ℕ, p.Prime → p ∣ r → z ≤ p) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hPz : ∀ p ∈ P, p < z) : Nat.Coprime r (∏ p ∈ P, p) := by
  refine Nat.Coprime.prod_right fun p hp => ?_
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hP p hp)).2 fun h => ?_)
  have := hr p (hP p hp) h
  have := hPz p hp
  omega

/-- The per-`n` alternating identity: with `q = min Q` and `Q' = Q ∖ {q}`,
`Σ_{P⊆Q} (−1)^{|P|}[a∏P ≤ X] + Σ_{P'⊆Q'} (−1)^{|P'|+1}[a∏P' ≤ X < a∏P'q] = 0`. -/
theorem alt_cancel (a X q : ℕ) (hq : 1 ≤ q) (Q' : Finset ℕ) (hqQ : q ∉ Q') :
    ∑ P ∈ (insert q Q').powerset, (-1 : ℤ) ^ P.card * (if a * ∏ p ∈ P, p ≤ X then 1 else 0) +
      ∑ P ∈ Q'.powerset, (-1 : ℤ) ^ (P.card + 1) *
        (if a * ∏ p ∈ P, p ≤ X ∧ X < a * (∏ p ∈ P, p) * q then 1 else 0) = 0 := by
  rw [Finset.sum_powerset_insert hqQ, add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun P hP => ?_
  have hqP : q ∉ P := fun h => hqQ (Finset.mem_powerset.1 hP h)
  rw [Finset.card_insert_of_notMem hqP, Finset.prod_insert hqP]
  set A := a * ∏ p ∈ P, p with hA
  have hAq : a * (q * ∏ p ∈ P, p) = A * q := by rw [hA]; ring
  rw [hAq]
  have hle : A ≤ A * q := Nat.le_mul_of_pos_right A hq
  by_cases h1 : A ≤ X
  · by_cases h2 : A * q ≤ X
    · simp only [h1, h2, true_and, show ¬ X < A * q from not_lt.2 h2, ite_true, ite_false]
      ring
    · simp only [h1, h2, true_and, show X < A * q from not_le.1 h2, ite_true, ite_false]
      ring
  · have h2 : ¬ A * q ≤ X := fun h => h1 (le_trans hle h)
    simp only [h1, h2, false_and, ite_false]
    ring

theorem mem_primesIco {w z p : ℕ} : p ∈ primesIco w z ↔ w ≤ p ∧ p < z ∧ p.Prime := by
  rw [primesIco, Finset.mem_filter, Finset.mem_Ico, and_assoc]

/-- **The Buchstab tree at one `n`.** For `w ≤ z₀` and `r ≤ X` with all primes of `r` at least `z₀`, the indicator of
`r ∣ n` with no prime factor of `n` below `z₀` is the leaves' alternating sum plus the stops'. -/
theorem tree_pt (n : ℕ) {r X w z₀ : ℕ} (hwz : w ≤ z₀) (hr : ∀ p : ℕ, p.Prime → p ∣ r → z₀ ≤ p) (hrX : r ≤ X) :
    (if r ∣ n ∧ rough z₀ n then (1 : ℤ) else 0) =
      ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℤ) ^ P.card *
          (if r * ∏ p ∈ P, p ≤ X then (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) +
        ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℤ) ^ (P.card + 1) *
          (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * p then
            (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) := by
  have hPprime : ∀ P ∈ (primesIco w z₀).powerset, ∀ p ∈ P, p.Prime := fun P hP p hp =>
    (mem_primesIco.1 (Finset.mem_powerset.1 hP hp)).2.2
  by_cases hb : r ∣ n ∧ rough w n
  · obtain ⟨hrn, hwn⟩ := hb
    set Q := (primesIco w z₀).filter (· ∣ n) with hQ
    have hQsub : Q ⊆ primesIco w z₀ := Finset.filter_subset _ _
    have hmemQ : ∀ p, p ∈ Q ↔ (w ≤ p ∧ p < z₀ ∧ p.Prime) ∧ p ∣ n := fun p => by
      rw [hQ, Finset.mem_filter, mem_primesIco]
    -- the left side
    have hL : (r ∣ n ∧ rough z₀ n) ↔ Q = ∅ := by
      constructor
      · rintro ⟨-, hz⟩
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        obtain ⟨⟨-, hpz, hpp⟩, hpn⟩ := (hmemQ p).1 hp
        exact hz p hpz hpp hpn
      · intro hQe
        refine ⟨hrn, fun p hpz hpp hpn => ?_⟩
        by_cases hpw : p < w
        · exact hwn p hpw hpp hpn
        · have : p ∈ Q := (hmemQ p).2 ⟨⟨not_lt.1 hpw, hpz, hpp⟩, hpn⟩
          rw [hQe] at this; exact Finset.notMem_empty p this
    -- the leaves: `r∏P ∣ n` iff `P ⊆ Q`
    have hleaf : ∀ P ∈ (primesIco w z₀).powerset, (r * ∏ p ∈ P, p ∣ n ∧ rough w n) ↔ P ⊆ Q := by
      intro P hP
      have hPp := hPprime P hP
      have hPz : ∀ p ∈ P, p < z₀ := fun p hp => (mem_primesIco.1 (Finset.mem_powerset.1 hP hp)).2.1
      constructor
      · rintro ⟨h, -⟩ p hp
        exact (hmemQ p).2 ⟨mem_primesIco.1 (Finset.mem_powerset.1 hP hp),
          dvd_trans (dvd_trans (Finset.dvd_prod_of_mem _ hp) (dvd_mul_left _ r)) h⟩
      · intro hPQ
        refine ⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_r hr hPp hPz) hrn
          ((prod_dvd_iff hPp n).2 fun p hp => ((hmemQ p).1 (hPQ hp)).2), hwn⟩
    have hleaves : ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℤ) ^ P.card *
        (if r * ∏ p ∈ P, p ≤ X then (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) =
        ∑ P ∈ Q.powerset, (-1 : ℤ) ^ P.card * (if r * ∏ p ∈ P, p ≤ X then 1 else 0) := by
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun P => P ⊆ Q)]
      have h0 : ∑ P ∈ ((primesIco w z₀).powerset).filter (fun P => ¬ P ⊆ Q), (-1 : ℤ) ^ P.card *
          (if r * ∏ p ∈ P, p ≤ X then (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) = 0 :=
        Finset.sum_eq_zero fun P hP => by
          rw [Finset.mem_filter] at hP
          rw [ite_eq_right (fun h => hP.2 ((hleaf P hP.1).1 h))]
          simp
      rw [h0, add_zero]
      have hfilt : ((primesIco w z₀).powerset).filter (fun P => P ⊆ Q) = Q.powerset := by
        ext P
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun h => h.2, fun h => ⟨h.trans hQsub, h⟩⟩
      rw [hfilt]
      refine Finset.sum_congr rfl fun P hP => ?_
      have hPQ := Finset.mem_powerset.1 hP
      have hP' : P ∈ (primesIco w z₀).powerset := Finset.mem_powerset.2 (hPQ.trans hQsub)
      by_cases hX : r * ∏ p ∈ P, p ≤ X
      · rw [ite_eq_left hX, ite_eq_left hX, ite_eq_left ((hleaf P hP').2 hPQ)]
      · rw [ite_eq_right hX, ite_eq_right hX]
    -- the stops: only `p = min Q` contributes
    have hstop : ∀ p ∈ primesIco w z₀, ∀ P ∈ (primesIco (p + 1) z₀).powerset,
        (r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n) ↔ (p ∈ Q ∧ (∀ q ∈ Q, p ≤ q) ∧ P ⊆ Q) := by
      intro p hp P hP
      have hpm := mem_primesIco.1 hp
      have hPm : ∀ p' ∈ P, p + 1 ≤ p' ∧ p' < z₀ ∧ p'.Prime := fun p' hp' =>
        mem_primesIco.1 (Finset.mem_powerset.1 hP hp')
      have hPp : ∀ p' ∈ P, p'.Prime := fun p' hp' => (hPm p' hp').2.2
      have hPz : ∀ p' ∈ P, p' < z₀ := fun p' hp' => (hPm p' hp').2.1
      constructor
      · rintro ⟨h, hrough⟩
        have hpn : p ∣ n := dvd_trans (dvd_mul_left p _) h
        refine ⟨(hmemQ p).2 ⟨hpm, hpn⟩, fun q hq => ?_, fun p' hp' => ?_⟩
        · obtain ⟨⟨-, -, hqp⟩, hqn⟩ := (hmemQ q).1 hq
          by_contra hlt
          exact hrough q (not_le.1 hlt) hqp hqn
        · refine (hmemQ p').2 ⟨⟨le_trans hpm.1 (by have := (hPm p' hp').1; omega), hPz p' hp', hPp p' hp'⟩, ?_⟩
          exact dvd_trans (dvd_trans (Finset.dvd_prod_of_mem _ hp') (dvd_mul_left _ r))
            (dvd_trans (dvd_mul_right _ p) h)
      · rintro ⟨hpQ, hmin, hPQ⟩
        have hpn := ((hmemQ p).1 hpQ).2
        have hPn : (∏ p' ∈ P, p') ∣ n := (prod_dvd_iff hPp n).2 fun p' hp' => ((hmemQ p').1 (hPQ hp')).2
        have hcop1 : Nat.Coprime r (∏ p' ∈ P, p') := coprime_r hr hPp hPz
        have hrP : r * ∏ p' ∈ P, p' ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop1 hrn hPn
        have hpr : ¬ p ∣ r := fun h => by have := hr p hpm.2.2 h; have := hpm.2.1; omega
        have hcop2 : Nat.Coprime (r * ∏ p' ∈ P, p') p := by
          refine Nat.coprime_mul_iff_left.2 ⟨((Nat.Prime.coprime_iff_not_dvd hpm.2.2).2 hpr).symm, ?_⟩
          exact Nat.Coprime.prod_left fun p' hp' => (Nat.coprime_primes (hPp p' hp') hpm.2.2).2
            (by have := (hPm p' hp').1; omega)
        refine ⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop2 hrP hpn, fun q hq hqp hqn => ?_⟩
        by_cases hqw : q < w
        · exact hwn q hqw hqp hqn
        · have := hmin q ((hmemQ q).2 ⟨⟨not_lt.1 hqw, lt_trans hq hpm.2.1, hqp⟩, hqn⟩)
          omega
    rw [hleaves]
    by_cases hQe : Q = ∅
    · -- `n` is `z₀`-rough: the leaves give `[r ≤ X] = 1` and the stops vanish
      have hstop0 : ∀ p ∈ primesIco w z₀, ∀ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℤ) ^ (P.card + 1) *
          (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * p then
            (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) = 0 := by
        intro p hp P hP
        have h := hstop p hp P hP
        rw [hQe] at h
        simp only [Finset.notMem_empty, false_and, iff_false] at h
        simp [h]
      rw [Finset.sum_congr rfl fun p hp => Finset.sum_eq_zero (hstop0 p hp), Finset.sum_const_zero, add_zero,
        ite_eq_left (hL.2 hQe), hQe, Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, pow_zero,
        one_mul, Finset.prod_empty, mul_one, ite_eq_left hrX]
    · -- only the least prime `q₀` of `Q` stops, and the identity is `alt_cancel`
      have hne : Q.Nonempty := Finset.nonempty_iff_ne_empty.2 hQe
      set q₀ := Q.min' hne with hq₀
      have hq₀Q : q₀ ∈ Q := Finset.min'_mem Q hne
      have hq₀min : ∀ q ∈ Q, q₀ ≤ q := fun q hq => Finset.min'_le Q q hq
      have hq₀m := (hmemQ q₀).1 hq₀Q
      have hq₀1 : 1 ≤ q₀ := hq₀m.1.2.2.one_lt.le
      have hother : ∀ p ∈ primesIco w z₀, p ≠ q₀ → ∑ P ∈ (primesIco (p + 1) z₀).powerset,
          (-1 : ℤ) ^ (P.card + 1) * (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * p then
            (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) = 0 := by
        intro p hp hpq
        refine Finset.sum_eq_zero fun P hP => ?_
        have h : ¬ (r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n) := fun h => by
          obtain ⟨hpQ, hmin, -⟩ := (hstop p hp P hP).1 h
          exact hpq (le_antisymm (hmin q₀ hq₀Q) (hq₀min p hpQ))
        simp [h]
      have hsub : (Q.erase q₀).powerset ⊆ (primesIco (q₀ + 1) z₀).powerset := by
        intro P hP
        refine Finset.mem_powerset.2 fun p hp => ?_
        have hpe := Finset.mem_erase.1 (Finset.mem_powerset.1 hP hp)
        obtain ⟨⟨-, hpz, hpp⟩, -⟩ := (hmemQ p).1 hpe.2
        have := hq₀min p hpe.2
        exact mem_primesIco.2 ⟨by have := hpe.1; omega, hpz, hpp⟩
      have hq₀mem : q₀ ∈ primesIco w z₀ := hQsub hq₀Q
      have hstopq : ∑ P ∈ (primesIco (q₀ + 1) z₀).powerset, (-1 : ℤ) ^ (P.card + 1) *
          (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * q₀ then
            (if r * (∏ p' ∈ P, p') * q₀ ∣ n ∧ rough q₀ n then 1 else 0) else 0) =
          ∑ P ∈ (Q.erase q₀).powerset, (-1 : ℤ) ^ (P.card + 1) *
            (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * q₀ then 1 else 0) := by
        rw [← Finset.sum_subset hsub]
        · refine Finset.sum_congr rfl fun P hP => ?_
          have hPQ : P ⊆ Q := (Finset.mem_powerset.1 hP).trans (Finset.erase_subset _ _)
          rw [ite_eq_left ((hstop q₀ hq₀mem P (hsub hP)).2 ⟨hq₀Q, hq₀min, hPQ⟩)]
        · intro P hP hP'
          have h : ¬ (r * (∏ p' ∈ P, p') * q₀ ∣ n ∧ rough q₀ n) := fun h => by
            obtain ⟨-, -, hPQ⟩ := (hstop q₀ hq₀mem P hP).1 h
            refine hP' (Finset.mem_powerset.2 fun p hp => Finset.mem_erase.2 ⟨fun he => ?_, hPQ hp⟩)
            have := (mem_primesIco.1 (Finset.mem_powerset.1 hP hp)).1
            omega
          simp [h]
      rw [Finset.sum_eq_single q₀ hother (fun h => absurd hq₀mem h), hstopq, ite_eq_right (fun h => hQe (hL.1 h))]
      have hc := alt_cancel r X q₀ hq₀1 (Q.erase q₀) (Finset.notMem_erase q₀ Q)
      rw [Finset.insert_erase hq₀Q] at hc
      exact hc.symm
  · -- every term vanishes
    have hL0 : ¬ (r ∣ n ∧ rough z₀ n) := fun h => hb ⟨h.1, rough_mono hwz h.2⟩
    have h1 : ∀ P ∈ (primesIco w z₀).powerset, (-1 : ℤ) ^ P.card *
        (if r * ∏ p ∈ P, p ≤ X then (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) = 0 := by
      intro P _
      have h : ¬ (r * ∏ p ∈ P, p ∣ n ∧ rough w n) := fun h => hb ⟨dvd_trans (dvd_mul_right r _) h.1, h.2⟩
      simp [h]
    have h2 : ∀ p ∈ primesIco w z₀, ∀ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℤ) ^ (P.card + 1) *
        (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * p then
          (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) = 0 := by
      intro p hp P _
      have h : ¬ (r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n) := fun h =>
        hb ⟨dvd_trans (dvd_trans (dvd_mul_right r _) (dvd_mul_right _ p)) h.1,
          rough_mono (mem_primesIco.1 hp).1 h.2⟩
      simp [h]
    rw [ite_eq_right hL0, Finset.sum_eq_zero h1, Finset.sum_congr rfl fun p hp => Finset.sum_eq_zero (h2 p hp),
      Finset.sum_const_zero, add_zero]

theorem S_eq_sum (C : Finset ℕ) (m z : ℕ) :
    (S C m z : ℤ) = ∑ n ∈ C, (if m ∣ n ∧ rough z n then (1 : ℤ) else 0) := by
  rw [S, Finset.card_filter]
  push_cast
  rfl

/-- **The Buchstab tree over a finite set.** For `w ≤ z₀`, `r ≤ X` with all primes of `r` at least `z₀`:
`S(C_r, z₀) = Σ_{P ⊆ [w, z₀), r∏P ≤ X} (−1)^{|P|} S(C_{r∏P}, w)
  + Σ_{w ≤ p < z₀} Σ_{P ⊆ (p, z₀), r∏P ≤ X < r∏P·p} (−1)^{|P|+1} S(C_{r∏P·p}, p)`, the sets `P` of primes. -/
theorem tree_sum (C : Finset ℕ) {r X w z₀ : ℕ} (hwz : w ≤ z₀) (hr : ∀ p : ℕ, p.Prime → p ∣ r → z₀ ≤ p)
    (hrX : r ≤ X) :
    (S C r z₀ : ℤ) =
      ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℤ) ^ P.card *
          (if r * ∏ p ∈ P, p ≤ X then (S C (r * ∏ p ∈ P, p) w : ℤ) else 0) +
        ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℤ) ^ (P.card + 1) *
          (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * p then
            (S C (r * (∏ p' ∈ P, p') * p) p : ℤ) else 0) := by
  rw [S_eq_sum, Finset.sum_congr rfl fun n _ => tree_pt n hwz hr hrX, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    split_ifs with h
    · rw [S_eq_sum]
    · simp
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    split_ifs with h
    · rw [S_eq_sum]
    · simp

end SieveTree
