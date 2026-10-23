/-
# Round 696: the lengthening of Heath-Brown's double sums (the CGL plan's stage M5)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Kerr lengthens the double sum over `N ⩽ n ⩽ KN` to one over `UN ⩽ n ⩽ 3KNU/2` (arXiv:1909.12075, his Lemma 20). His
proof averages over the characters modulo an auxiliary prime: "Let P be a prime number satisfying" `8U ⩽ P ⩽ 16U` (his
(35); text layer lines 1307–1308, the condition transcribed). It puts `a(m, χ) = Σ_{U⩽u⩽3U/2, N⩽n⩽KN, un=m}χ(u)`,
which the divisor bound controls, before positivity (his Lemma 18). This file proves that step for round 694's double
sums with characters.

The stack's form.
* The integers `u` run over `⌊U⌋ < u ≤ ⌊3U/2⌋` and are prime to `q` (`useg`), so that `|χ_r(u)| = 1`. Summed over
  the characters `ψ` mod `p`, `|Σ_uψ(u)u^{−1/2}A_r(u)Ā_s(u)|²` is then `φ(p)c(q, U)` for every pair `(r, s)`, with
  `c(q, U) = Σ_u 1/u` (`cqU`).
* The auxiliary prime is any prime `p > ⌊3U/2⌋`, from Euclid's theorem, so that the `u` are distinct units mod `p`.
  Its size enters nowhere else: the number `φ(p)` of characters appears on both sides.
* The coefficient of `m` is `a(m, ψ) = Σ_{nu=m}n^{−1/2}u^{−1/2}ψ(u)` (`alen`), at most `d(m)m^{−1/2}` by round 694's
  `card_fiber_le`. Round 694's `dsum_le` (positivity) then bounds the double sum over `m ∈ (NU, 4NU]`, which
  `|x + y|² ≤ 2|x|² + 2|y|²` splits into `σ(NU)` and `σ(2NU)`.
* The count of the integers prime to `q` in `(a, b]` is Möbius's, `Σ_{d∣q}μ(d)(⌊b/d⌋ − ⌊a/d⌋)`. With
  `Σ_{d∣q}μ(d)/d = φ(q)/q` and round 689's `q ≤ φ(q)d(q)` (`LinnikCGLConst.le_totient_mul_card_divisors`) it gives
  `c(q, U) ≥ 1/(9d(q))` for `U ≥ 12d(q)² + 4`.

Plain statements, with `d(n)` the number of divisors of `n`, `μ` Möbius's function and `σ(N)` round 694's `sig`.
* `card_Ioc_filter_dvd`: for `a ≤ b`, `#{u ∈ (a, b] : d ∣ u} = b/d − a/d` (natural division).
* `sum_moebius_divisors`, `coprime_ind_eq`: `Σ_{d∣n}μ(d) = [n = 1]`; and for `q ≥ 1`, `[(u, q) = 1] = Σ_{d∣q, d∣u}μ(d)`.
* `sum_moebius_mul_div`, `sum_moebius_div`: for `q ≥ 1`, `Σ_{d∣q}μ(d)(q/d) = φ(q)` and `Σ_{d∣q}μ(d)/d = φ(q)/q`.
* `card_coprime_Ioc_ge`: for `q ≥ 1` and `a ≤ b`, `#{u ∈ (a, b] : (u, q) = 1} ≥ (b − a)φ(q)/q − d(q)`.
* `mem_useg`, `cqU_ge`: for `U ≥ 0`, each `u` in `useg q U` has `U < u ≤ 3U/2` and `(u, q) = 1`; and for `q ≥ 1` and
  `U ≥ 12d(q)² + 4`, `c(q, U) ≥ 1/(9d(q))`.
* `sum_chars_norm_sq_eq`: for a prime `p`, a set `V` of integers `0 < u < p` and any `b`,
  `Σ_ψ|Σ_{u∈V}b_uψ(u)|² = φ(p)Σ_{u∈V}|b_u|²`, the sum over all characters `ψ` mod `p`.
* `sum_alen_eq`, `norm_alen_le`: for a family with `A_r(nm) = A_r(n)A_r(m)` and `M` holding every `nu`,
  `Σ_{m∈M}a(m, ψ)A_r(m)Ā_s(m) = (Σ_{n∈S}n^{−1/2}A_r(n)Ā_s(n))(Σ_{u∈V}u^{−1/2}A_r(u)Ā_s(u)ψ(u))`; and for `|ψ| ≤ 1`
  and `m ≥ 1`, `|a(m, ψ)| ≤ d(m)m^{−1/2}`.
* `norm_famA_eq_one`: `|χ_r(u)u^{it_r}| = 1` for `u ≥ 1` prime to `q`.
* `dsum_two_le`: the double sum over `(NU, 2NU] ∪ (2NU, 4NU]` is at most `2(σ(NU) + σ(2NU))`.
* `cqU_mul_sig_le`: the lengthening; for `N, U, D ≥ 0` with `d(m) ≤ D` for `1 ≤ m ≤ 4NU`,
  `c(q, U)σ(N) ≤ 2D²(σ(NU) + σ(2NU))`.
* `sig_le_lengthen`: for `q ≥ 1`, `N ≥ 0`, `U ≥ 12d(q)² + 4` and `D ≥ 0` with `d(m) ≤ D` for `1 ≤ m ≤ 4NU`,
  `σ(N) ≤ 18d(q)D²(σ(NU) + σ(2NU))`.

The file imports `LinnikCGLHBPos.lean` and `LinnikCGLConst.lean`.
-/

import LinnikCGLHBPos
import LinnikCGLConst

open Complex Set Real Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace LinnikCGLHBLen

open LinnikCGLT101 LinnikCGLHBPos

variable {ι : Type*}

/-! ### The integers prime to `q` in an interval -/

/-- For `a ≤ b`, `#{u ∈ (a, b] : d ∣ u} = b/d − a/d` (natural division). -/
lemma card_Ioc_filter_dvd {a b : ℕ} (hab : a ≤ b) (d : ℕ) :
    ((Finset.Ioc a b).filter (fun u => d ∣ u)).card = b / d - a / d := by
  have h1 := Nat.Ioc_filter_dvd_card_eq_div b d
  have h2 := Nat.Ioc_filter_dvd_card_eq_div a d
  have hsplit : (Finset.Ioc 0 b).filter (fun u => d ∣ u) =
      (Finset.Ioc 0 a).filter (fun u => d ∣ u) ∪ (Finset.Ioc a b).filter (fun u => d ∣ u) := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab]
  have hdisj : Disjoint ((Finset.Ioc 0 a).filter (fun u => d ∣ u))
      ((Finset.Ioc a b).filter (fun u => d ∣ u)) :=
    Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)
  rw [hsplit, Finset.card_union_of_disjoint hdisj] at h1
  rw [← h1, ← h2]
  omega

/-- `Σ_{d∣n}μ(d) = [n = 1]`. -/
lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using h

/-- For `q ≥ 1`, `[(u, q) = 1] = Σ_{d∣q, d∣u}μ(d)`. -/
lemma coprime_ind_eq {q : ℕ} (hq : 0 < q) (u : ℕ) :
    (if u.Coprime q then (1 : ℤ) else 0) =
      ∑ d ∈ q.divisors.filter (fun d => d ∣ u), (ArithmeticFunction.moebius d : ℤ) := by
  have e : q.divisors.filter (fun d => d ∣ u) = (Nat.gcd u q).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hg : Nat.gcd u q ≠ 0 := (Nat.gcd_pos_of_pos_right u hq).ne'
    constructor
    · rintro ⟨⟨hdq, -⟩, hdu⟩
      exact ⟨⟨hdu, hdq⟩, hg⟩
    · rintro ⟨⟨hdu, hdq⟩, -⟩
      exact ⟨⟨hdq, hq.ne'⟩, hdu⟩
  rw [e, sum_moebius_divisors]

/-- For `q ≥ 1`, `Σ_{d∣q}μ(d)(q/d) = φ(q)`: Möbius inversion of Gauss's `Σ_{d∣n}φ(d) = n`. -/
lemma sum_moebius_mul_div {q : ℕ} (hq : 0 < q) :
    ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ((q / d : ℕ) : ℝ) = q.totient := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (R := ℝ) (f := fun n => (n.totient : ℝ))
    (g := fun n => (n : ℝ))).1 (fun n _ => by exact_mod_cast Nat.sum_totient n) q hq
  beta_reduce at h
  rw [Nat.sum_divisorsAntidiagonal (fun x y => (ArithmeticFunction.moebius x : ℤ) • (y : ℝ))] at h
  rw [← h]
  exact Finset.sum_congr rfl fun d _ => by rw [zsmul_eq_mul]

/-- For `q ≥ 1`, `Σ_{d∣q}μ(d)/d = φ(q)/q`. -/
lemma sum_moebius_div {q : ℕ} (hq : 0 < q) :
    ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) / d = q.totient / q := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← sum_moebius_mul_div hq, eq_div_iff hqR, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div hdq hd0]
  ring

/-- **The integers prime to `q` in `(a, b]`** (Möbius): for `q ≥ 1` and `a ≤ b`, there are at least
`(b − a)φ(q)/q − d(q)` of them. -/
theorem card_coprime_Ioc_ge {q : ℕ} (hq : 0 < q) {a b : ℕ} (hab : a ≤ b) :
    ((b : ℝ) - a) * q.totient / q - q.divisors.card ≤
      (((Finset.Ioc a b).filter (fun u => u.Coprime q)).card : ℝ) := by
  have hZ : (((Finset.Ioc a b).filter (fun u => u.Coprime q)).card : ℤ) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℤ) * ((b / d - a / d : ℕ) : ℤ) := by
    rw [Finset.card_filter]
    push_cast
    rw [Finset.sum_congr rfl fun u _ => coprime_ind_eq hq u]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, card_Ioc_filter_dvd hab, nsmul_eq_mul, mul_comm]
  have hR : (((Finset.Ioc a b).filter (fun u => u.Coprime q)).card : ℝ) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ((b / d - a / d : ℕ) : ℝ) := by
    exact_mod_cast hZ
  rw [hR]
  have hdiv : ∀ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ((b : ℝ) - a) / d - 1 ≤
      (ArithmeticFunction.moebius d : ℝ) * ((b / d - a / d : ℕ) : ℝ) := by
    intro d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast h
    have hle : a / d ≤ b / d := Nat.div_le_div_right hab
    have hcast : ((b / d - a / d : ℕ) : ℝ) = ((b / d : ℕ) : ℝ) - ((a / d : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]
    have fl : ∀ m : ℕ, ((m / d : ℕ) : ℝ) ≤ (m : ℝ) / d ∧ (m : ℝ) / d - 1 < ((m / d : ℕ) : ℝ) := by
      intro m
      have e : ⌊(m : ℝ) / d⌋₊ = m / d := Nat.floor_div_eq_div (K := ℝ) m d
      refine ⟨?_, ?_⟩
      · rw [← e]
        exact Nat.floor_le (by positivity)
      · rw [← e]
        have := Nat.lt_floor_add_one ((m : ℝ) / d)
        linarith
    obtain ⟨hb1, hb2⟩ := fl b
    obtain ⟨ha1, ha2⟩ := fl a
    have hx : |((b / d - a / d : ℕ) : ℝ) - ((b : ℝ) - a) / d| ≤ 1 := by
      rw [hcast, sub_div, abs_le]
      constructor <;> linarith
    have h1 : |(ArithmeticFunction.moebius d : ℝ) * (((b / d - a / d : ℕ) : ℝ) - ((b : ℝ) - a) / d)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul hμ hx (abs_nonneg _) zero_le_one).trans (by norm_num)
    have h2 := neg_abs_le ((ArithmeticFunction.moebius d : ℝ) * (((b / d - a / d : ℕ) : ℝ) - ((b : ℝ) - a) / d))
    have h3 : (ArithmeticFunction.moebius d : ℝ) * (((b / d - a / d : ℕ) : ℝ) - ((b : ℝ) - a) / d) =
        (ArithmeticFunction.moebius d : ℝ) * ((b / d - a / d : ℕ) : ℝ) -
          (ArithmeticFunction.moebius d : ℝ) * ((b : ℝ) - a) / d := by ring
    linarith
  have hsum := Finset.sum_le_sum hdiv
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hφ : ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ((b : ℝ) - a) / d =
      ((b : ℝ) - a) * q.totient / q := by
    rw [mul_div_assoc, ← sum_moebius_div hq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hφ] at hsum
  linarith

/-! ### The integers of the lengthening and their weight `c(q, U)` -/

/-- The integers `⌊U⌋ < u ≤ ⌊3U/2⌋` prime to `q`. -/
def useg (q : ℕ) (U : ℝ) : Finset ℕ := (Finset.Ioc ⌊U⌋₊ ⌊3 * U / 2⌋₊).filter (fun u => u.Coprime q)

/-- `c(q, U) = Σ_{u∈useg}1/u`. -/
def cqU (q : ℕ) (U : ℝ) : ℝ := ∑ u ∈ useg q U, ((u : ℝ))⁻¹

/-- For `U ≥ 0`, each `u` in `useg q U` has `U < u ≤ 3U/2` and `(u, q) = 1`. -/
lemma mem_useg {q : ℕ} {U : ℝ} (hU : 0 ≤ U) {u : ℕ} (hu : u ∈ useg q U) :
    U < u ∧ (u : ℝ) ≤ 3 * U / 2 ∧ u.Coprime q := by
  rw [useg, Finset.mem_filter, Finset.mem_Ioc] at hu
  exact ⟨(Nat.floor_lt hU).1 hu.1.1, (Nat.le_floor_iff (by positivity)).1 hu.1.2, hu.2⟩

/-- **`c(q, U)` from below**: for `q ≥ 1` and `U ≥ 12d(q)² + 4`, `c(q, U) ≥ 1/(9d(q))`. -/
theorem cqU_ge {q : ℕ} (hq : 0 < q) {U : ℝ} (hU : 12 * (q.divisors.card : ℝ) ^ 2 + 4 ≤ U) :
    1 / (9 * (q.divisors.card : ℝ)) ≤ cqU q U := by
  have hdq1 : (1 : ℝ) ≤ q.divisors.card := by
    have : 1 ≤ q.divisors.card := Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 hq.ne'⟩
    exact_mod_cast this
  have hphi : (q : ℝ) ≤ q.totient * (q.divisors.card : ℝ) := by
    have := LinnikCGLConst.le_totient_mul_card_divisors q
    exact_mod_cast this
  set dq : ℝ := (q.divisors.card : ℝ) with hdq_def
  have hdq0 : 0 < dq := by linarith
  have hU4 : 4 ≤ U := by nlinarith
  have hU0 : 0 < U := by linarith
  have hab : ⌊U⌋₊ ≤ ⌊3 * U / 2⌋₊ := Nat.floor_le_floor (by linarith)
  have ha : (⌊U⌋₊ : ℝ) ≤ U := Nat.floor_le hU0.le
  have hb : 3 * U / 2 - 1 < (⌊3 * U / 2⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (3 * U / 2)
    linarith
  have hcnt := card_coprime_Ioc_ge hq hab
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard : 5 / 12 * (U - 2) / dq ≤ ((useg q U).card : ℝ) := by
    have h1 : (U / 2 - 1) / dq ≤ ((⌊3 * U / 2⌋₊ : ℝ) - ⌊U⌋₊) * q.totient / q := by
      rw [div_le_div_iff₀ hdq0 hqR]
      have hba : U / 2 - 1 ≤ (⌊3 * U / 2⌋₊ : ℝ) - ⌊U⌋₊ := by linarith
      have hU2 : 0 ≤ U / 2 - 1 := by linarith
      have hφ0 : (0 : ℝ) ≤ q.totient * dq := by positivity
      calc (U / 2 - 1) * q ≤ (U / 2 - 1) * (q.totient * dq) := mul_le_mul_of_nonneg_left hphi hU2
        _ ≤ ((⌊3 * U / 2⌋₊ : ℝ) - ⌊U⌋₊) * (q.totient * dq) := mul_le_mul_of_nonneg_right hba hφ0
        _ = ((⌊3 * U / 2⌋₊ : ℝ) - ⌊U⌋₊) * q.totient * dq := by ring
    have h2 : dq ≤ (U / 2 - 1) / (6 * dq) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have e : 5 / 12 * (U - 2) / dq = (U / 2 - 1) / dq - (U / 2 - 1) / (6 * dq) := by
      field_simp
      ring
    unfold useg
    rw [e]
    linarith
  have hsum : ((useg q U).card : ℝ) * (2 / (3 * U)) ≤ cqU q U := by
    have hle : ∀ u ∈ useg q U, 2 / (3 * U) ≤ ((u : ℝ))⁻¹ := by
      intro u hu
      obtain ⟨h1, h2, -⟩ := mem_useg hU0.le hu
      have hu0 : (0 : ℝ) < u := by linarith
      rw [show (2 : ℝ) / (3 * U) = (3 * U / 2)⁻¹ by field_simp]
      exact inv_anti₀ hu0 h2
    have := Finset.card_nsmul_le_sum (useg q U) (fun u : ℕ => ((u : ℝ))⁻¹) (2 / (3 * U)) hle
    rw [nsmul_eq_mul] at this
    exact this
  calc 1 / (9 * dq) ≤ 5 / 12 * (U - 2) / dq * (2 / (3 * U)) := by
        rw [show 5 / 12 * (U - 2) / dq * (2 / (3 * U)) = 5 * (U - 2) / (18 * U * dq) by field_simp; ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ ≤ ((useg q U).card : ℝ) * (2 / (3 * U)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ cqU q U := hsum

/-! ### Orthogonality modulo a prime -/

/-- For `n ≥ 1`, `conj ψ(b) = ψ(b⁻¹)` for a unit `b`. -/
lemma conj_apply_unit {n : ℕ} [NeZero n] (ψ : DirichletCharacter ℂ n) {b : ZMod n} (hb : IsUnit b) :
    conj (ψ b) = ψ b⁻¹ := by
  have h1 : conj (ψ b) = ψ⁻¹ b := MulChar.star_apply' ψ b
  rw [h1, MulChar.inv_apply_eq_inv']
  have hu : ψ b * ψ b⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit _ hb, map_one]
  exact inv_eq_of_mul_eq_one_right hu

/-- **Orthogonality modulo a prime**: for a prime `p`, a set `V` of integers `0 < u < p` and any `b`,
`Σ_ψ|Σ_{u∈V}b_uψ(u)|² = φ(p)Σ_{u∈V}|b_u|²`, the sum over all characters `ψ` mod `p`. -/
theorem sum_chars_norm_sq_eq {p : ℕ} [NeZero p] (hp : p.Prime) (V : Finset ℕ) (hV : ∀ u ∈ V, 0 < u ∧ u < p)
    (b : ℕ → ℂ) :
    ∑ ψ : DirichletCharacter ℂ p, ‖∑ u ∈ V, b u * ψ u‖ ^ 2 = p.totient * ∑ u ∈ V, ‖b u‖ ^ 2 := by
  have hunit : ∀ u ∈ V, IsUnit (u : ZMod p) := fun u hu =>
    (ZMod.isUnit_iff_coprime u p).2 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
      (Nat.not_dvd_of_pos_of_lt (hV u hu).1 (hV u hu).2)))
  have hinj : ∀ u ∈ V, ∀ v ∈ V, (u : ZMod p) = (v : ZMod p) → u = v := fun u hu v hv h => by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hV u hu).2, Nat.mod_eq_of_lt (hV v hv).2] at h
    exact h
  have horth : ∀ u ∈ V, ∀ v ∈ V, ∑ ψ : DirichletCharacter ℂ p, ψ u * conj (ψ v) =
      if u = v then (p.totient : ℂ) else 0 := by
    intro u hu v hv
    have e : ∀ ψ : DirichletCharacter ℂ p, ψ u * conj (ψ v) = ψ (v : ZMod p)⁻¹ * ψ u := fun ψ => by
      rw [conj_apply_unit ψ (hunit v hv), mul_comm]
    rw [Finset.sum_congr rfl fun ψ _ => e ψ,
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ (hunit v hv) (u : ZMod p)]
    by_cases huv : u = v
    · rw [ite_eq_left (congrArg _ huv.symm), ite_eq_left huv]
    · rw [ite_eq_right (fun h => huv (hinj u hu v hv h.symm)), ite_eq_right huv]
  have key : ∑ ψ : DirichletCharacter ℂ p, (∑ u ∈ V, b u * ψ u) * conj (∑ u ∈ V, b u * ψ u) =
      (p.totient : ℂ) * ∑ u ∈ V, b u * conj (b u) := by
    have e1 : ∀ ψ : DirichletCharacter ℂ p, (∑ u ∈ V, b u * ψ u) * conj (∑ u ∈ V, b u * ψ u) =
        ∑ u ∈ V, ∑ v ∈ V, b u * conj (b v) * (ψ u * conj (ψ v)) := by
      intro ψ
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [map_mul]
      ring
    rw [Finset.sum_congr rfl fun ψ _ => e1 ψ, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.sum_comm]
    have e2 : ∀ v ∈ V, ∑ ψ : DirichletCharacter ℂ p, b u * conj (b v) * (ψ u * conj (ψ v)) =
        b u * conj (b v) * (if u = v then (p.totient : ℂ) else 0) := fun v hv => by
      rw [← Finset.mul_sum, horth u hu v hv]
    rw [Finset.sum_congr rfl e2, Finset.sum_eq_single u]
    · rw [ite_eq_left rfl]
      ring
    · intro v _ hvu
      rw [ite_eq_right (fun h => hvu h.symm), mul_zero]
    · intro h
      exact absurd hu h
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj']
  exact key

/-! ### The lengthening -/

/-- The coefficients of the lengthened sum: `a(m, ψ) = Σ_{n∈S, u∈V, nu=m}n^{−1/2}u^{−1/2}ψ(u)`. -/
def alen (S V : Finset ℕ) (ψ : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ x ∈ (S ×ˢ V).filter (fun x : ℕ × ℕ => x.1 * x.2 = m), wh x.1 * wh x.2 * ψ x.2

/-- **The lengthened sum factors**: for a family with `A_r(nm) = A_r(n)A_r(m)` and `M` holding every product `nu`,
`Σ_{m∈M}a(m, ψ)A_r(m)Ā_s(m) = (Σ_{n∈S}n^{−1/2}A_r(n)Ā_s(n))(Σ_{u∈V}u^{−1/2}A_r(u)Ā_s(u)ψ(u))`. -/
lemma sum_alen_eq (A : ι → ℕ → ℂ) (hA : ∀ r n m, A r (n * m) = A r n * A r m) {S V M : Finset ℕ}
    (hM : ∀ x ∈ S ×ˢ V, x.1 * x.2 ∈ M) (ψ : ℕ → ℂ) (r s : ι) :
    ∑ m ∈ M, alen S V ψ m * A r m * conj (A s m) =
      (∑ n ∈ S, wh n * A r n * conj (A s n)) * ∑ u ∈ V, wh u * A r u * conj (A s u) * ψ u := by
  unfold alen
  have e1 : ∀ m ∈ M, (∑ x ∈ (S ×ˢ V).filter (fun x : ℕ × ℕ => x.1 * x.2 = m), wh x.1 * wh x.2 * ψ x.2) *
      A r m * conj (A s m) = ∑ x ∈ (S ×ˢ V).filter (fun x : ℕ × ℕ => x.1 * x.2 = m),
        wh x.1 * wh x.2 * ψ x.2 * A r (x.1 * x.2) * conj (A s (x.1 * x.2)) := by
    intro m _
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl e1, Finset.sum_fiberwise_of_maps_to hM, Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun u _ => ?_
  rw [hA, hA, map_mul]
  ring

/-- For `|ψ| ≤ 1` and `m ≥ 1`, `|a(m, ψ)| ≤ d(m)m^{−1/2}`. -/
lemma norm_alen_le (S V : Finset ℕ) {ψ : ℕ → ℂ} (hψ : ∀ u, ‖ψ u‖ ≤ 1) {m : ℕ} (hm : 0 < m) :
    ‖alen S V ψ m‖ ≤ m.divisors.card * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold alen
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x ∈ (S ×ˢ V).filter (fun x : ℕ × ℕ => x.1 * x.2 = m),
      ‖wh x.1 * wh x.2 * ψ x.2‖ ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro x hx
    have hxm := (Finset.mem_filter.1 hx).2
    rw [norm_mul, norm_mul, norm_wh, norm_wh]
    have h1 : (x.1 : ℝ) ^ (-(1 / 2 : ℝ)) * (x.2 : ℝ) ^ (-(1 / 2 : ℝ)) = (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), ← Nat.cast_mul, hxm]
    rw [h1]
    calc (m : ℝ) ^ (-(1 / 2 : ℝ)) * ‖ψ x.2‖ ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left (hψ _) (by positivity)
      _ = (m : ℝ) ^ (-(1 / 2 : ℝ)) := mul_one _
  have hsub : (S ×ˢ V).filter (fun x : ℕ × ℕ => x.1 * x.2 = m) ⊆
      ((S ∪ V) ×ˢ (S ∪ V)).filter (fun x : ℕ × ℕ => x.1 * x.2 = m) :=
    Finset.filter_subset_filter _ (Finset.product_subset_product Finset.subset_union_left Finset.subset_union_right)
  have hcard : (((S ×ˢ V).filter (fun x : ℕ × ℕ => x.1 * x.2 = m)).card : ℝ) ≤ m.divisors.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (card_fiber_le (S ∪ V) hm)
  calc ∑ x ∈ (S ×ˢ V).filter (fun x : ℕ × ℕ => x.1 * x.2 = m), ‖wh x.1 * wh x.2 * ψ x.2‖
      ≤ ∑ x ∈ (S ×ˢ V).filter (fun x : ℕ × ℕ => x.1 * x.2 = m), (m : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (((S ×ˢ V).filter (fun x : ℕ × ℕ => x.1 * x.2 = m)).card : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ m.divisors.card * (m : ℝ) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)

/-- `|χ_r(u)u^{it_r}| = 1` for `u ≥ 1` prime to `q`. -/
lemma norm_famA_eq_one {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (r : ι) {u : ℕ} (hu : 0 < u)
    (hcop : u.Coprime q) : ‖famA χ t r u‖ = 1 := by
  unfold famA
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hu]
  have h1 : ‖χ r (u : ZMod q)‖ = 1 := by
    have hU : IsUnit (u : ZMod q) := (ZMod.isUnit_iff_coprime u q).2 hcop
    have := DirichletCharacter.unit_norm_eq_one (χ r) hU.unit
    rwa [IsUnit.unit_spec] at this
  rw [h1]
  simp

section Lengthening

variable {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)

/-- The double sum over `(NU, 2NU] ∪ (2NU, 4NU]` is at most `2(σ(NU) + σ(2NU))`. -/
lemma dsum_two_le (N U : ℝ) :
    dsum P (famA χ t) (dyad (N * U) ∪ dyad (2 * N * U)) wh ≤
      2 * (sig P χ t (N * U) + sig P χ t (2 * N * U)) := by
  have hdisj : Disjoint (dyad (N * U)) (dyad (2 * N * U)) := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    rw [dyad, Finset.mem_Ioc] at h1 h2
    have e : 2 * (N * U) = 2 * N * U := by ring
    rw [e] at h1
    omega
  have key : ∀ r ∈ P, ∀ s ∈ P,
      ‖∑ n ∈ dyad (N * U) ∪ dyad (2 * N * U), wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2 ≤
        2 * (‖∑ n ∈ dyad (N * U), wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2 +
          ‖∑ n ∈ dyad (2 * N * U), wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2) := by
    intro r _ s _
    rw [Finset.sum_union hdisj]
    set x := ∑ n ∈ dyad (N * U), wh n * famA χ t r n * conj (famA χ t s n)
    set y := ∑ n ∈ dyad (2 * N * U), wh n * famA χ t r n * conj (famA χ t s n)
    have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  calc dsum P (famA χ t) (dyad (N * U) ∪ dyad (2 * N * U)) wh
      ≤ ∑ r ∈ P, ∑ s ∈ P, 2 * (‖∑ n ∈ dyad (N * U), wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2 +
          ‖∑ n ∈ dyad (2 * N * U), wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2) := by
        unfold dsum
        exact Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun s hs => key r hr s hs
    _ = 2 * (sig P χ t (N * U) + sig P χ t (2 * N * U)) := by
        unfold sig dsum
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]

/-- **The lengthening** (Kerr's Lemma 20, with characters): for `N, U, D ≥ 0` with `d(m) ≤ D` for `1 ≤ m ≤ 4NU`,
`c(q, U)σ(N) ≤ 2D²(σ(NU) + σ(2NU))`. -/
theorem cqU_mul_sig_le {N U D : ℝ} (hN : 0 ≤ N) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (hdiv : ∀ m ∈ Finset.Icc 1 ⌊4 * N * U⌋₊, (m.divisors.card : ℝ) ≤ D) :
    cqU q U * sig P χ t N ≤ 2 * D ^ 2 * (sig P χ t (N * U) + sig P χ t (2 * N * U)) := by
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (⌊3 * U / 2⌋₊ + 1)
  have : NeZero p := ⟨hp.ne_zero⟩
  have hNU : 0 ≤ N * U := mul_nonneg hN hU
  have h2NU : 0 ≤ 2 * N * U := by linarith
  have hVp : ∀ u ∈ useg q U, 0 < u ∧ u < p := by
    intro u hu
    rw [useg, Finset.mem_filter, Finset.mem_Ioc] at hu
    exact ⟨by omega, by omega⟩
  have hMm : ∀ x ∈ dyad N ×ˢ useg q U, x.1 * x.2 ∈ dyad (N * U) ∪ dyad (2 * N * U) := by
    intro x hx
    rw [Finset.mem_product] at hx
    obtain ⟨hn1, hn2⟩ := (mem_dyad hN).1 hx.1
    obtain ⟨hu1, hu2, -⟩ := mem_useg hU hx.2
    have hu0 : (0 : ℝ) < x.2 := by linarith
    have hlo : N * U < ((x.1 * x.2 : ℕ) : ℝ) := by
      push_cast
      calc N * U ≤ N * x.2 := mul_le_mul_of_nonneg_left hu1.le hN
        _ < x.1 * x.2 := mul_lt_mul_of_pos_right hn1 hu0
    have hhi : ((x.1 * x.2 : ℕ) : ℝ) ≤ 3 * (N * U) := by
      push_cast
      calc (x.1 : ℝ) * x.2 ≤ (2 * N) * (3 * U / 2) := mul_le_mul hn2 hu2 hu0.le (by linarith)
        _ = 3 * (N * U) := by ring
    rw [Finset.mem_union, mem_dyad hNU, mem_dyad h2NU]
    by_cases h : ((x.1 * x.2 : ℕ) : ℝ) ≤ 2 * (N * U)
    · exact Or.inl ⟨hlo, h⟩
    · have h' := not_le.1 h
      exact Or.inr ⟨by linarith, by linarith⟩
  -- the double sum of each twist factors
  have hfac : ∀ ψ : DirichletCharacter ℂ p,
      dsum P (famA χ t) (dyad (N * U) ∪ dyad (2 * N * U)) (alen (dyad N) (useg q U) (fun u => ψ u)) =
        ∑ r ∈ P, ∑ s ∈ P, ‖∑ n ∈ dyad N, wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2 *
          ‖∑ u ∈ useg q U, wh u * famA χ t r u * conj (famA χ t s u) * ψ u‖ ^ 2 := by
    intro ψ
    unfold dsum
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [sum_alen_eq (famA χ t) (famA_mul χ t) hMm, norm_mul, mul_pow]
  -- the average over the characters mod `p`
  have hnorm : ∀ r s, ∀ u ∈ useg q U, ‖wh u * famA χ t r u * conj (famA χ t s u)‖ ^ 2 = ((u : ℝ))⁻¹ := by
    intro r s u hu
    obtain ⟨-, -, hcop⟩ := mem_useg hU hu
    have hu0 : 0 < u := (hVp u hu).1
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_famA_eq_one χ t r hu0 hcop,
      norm_famA_eq_one χ t s hu0 hcop, norm_wh, mul_one, mul_one, ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg _), show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num,
      Real.rpow_neg_one]
  have hY : ∀ r s, ∑ ψ : DirichletCharacter ℂ p,
      ‖∑ u ∈ useg q U, wh u * famA χ t r u * conj (famA χ t s u) * ψ u‖ ^ 2 = p.totient * cqU q U := by
    intro r s
    rw [sum_chars_norm_sq_eq hp (useg q U) hVp, cqU]
    congr 1
    exact Finset.sum_congr rfl fun u hu => hnorm r s u hu
  have hsum : ∑ ψ : DirichletCharacter ℂ p,
      dsum P (famA χ t) (dyad (N * U) ∪ dyad (2 * N * U)) (alen (dyad N) (useg q U) (fun u => ψ u)) =
        p.totient * (cqU q U * sig P χ t N) := by
    rw [Finset.sum_congr rfl fun ψ _ => hfac ψ, Finset.sum_comm]
    have e : ∀ r ∈ P, ∑ ψ : DirichletCharacter ℂ p, ∑ s ∈ P,
        ‖∑ n ∈ dyad N, wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2 *
          ‖∑ u ∈ useg q U, wh u * famA χ t r u * conj (famA χ t s u) * ψ u‖ ^ 2 =
        ∑ s ∈ P, ‖∑ n ∈ dyad N, wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2 * (p.totient * cqU q U) := by
      intro r _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.mul_sum, hY r s]
    rw [Finset.sum_congr rfl e]
    unfold sig dsum
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  -- positivity bounds each twist
  have hle : ∀ ψ : DirichletCharacter ℂ p,
      dsum P (famA χ t) (dyad (N * U) ∪ dyad (2 * N * U)) (alen (dyad N) (useg q U) (fun u => ψ u)) ≤
        2 * D ^ 2 * (sig P χ t (N * U) + sig P χ t (2 * N * U)) := by
    intro ψ
    have hb : ∀ m ∈ dyad (N * U) ∪ dyad (2 * N * U),
        ‖alen (dyad N) (useg q U) (fun u => ψ u) m‖ ≤ D * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
      intro m hm
      rw [Finset.mem_union, mem_dyad hNU, mem_dyad h2NU] at hm
      have h : N * U < (m : ℝ) ∧ (m : ℝ) ≤ 4 * N * U := by
        rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, by linarith⟩
        · exact ⟨by linarith, by linarith⟩
      have hm0 : 0 < m := by
        have : (0 : ℝ) < m := by linarith [h.1]
        exact_mod_cast this
      refine (norm_alen_le (dyad N) (useg q U) (fun u => DirichletCharacter.norm_le_one ψ _) hm0).trans ?_
      exact mul_le_mul_of_nonneg_right (hdiv m (Finset.mem_Icc.2 ⟨hm0, Nat.le_floor h.2⟩)) (by positivity)
    have e : (fun m : ℕ => ((D * (m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = fun m => (D : ℂ) * wh m := by
      funext m
      simp only [wh, Complex.ofReal_mul]
    calc dsum P (famA χ t) (dyad (N * U) ∪ dyad (2 * N * U)) (alen (dyad N) (useg q U) (fun u => ψ u))
        ≤ dsum P (famA χ t) (dyad (N * U) ∪ dyad (2 * N * U))
            (fun m : ℕ => ((D * (m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) :=
          dsum_le P (famA χ t) (Finset.Subset.refl _) (b := fun m => D * (m : ℝ) ^ (-(1 / 2 : ℝ))) hb
            (fun m _ => by positivity)
      _ = D ^ 2 * dsum P (famA χ t) (dyad (N * U) ∪ dyad (2 * N * U)) wh := by
          rw [e, dsum_const_mul, Complex.norm_real, Real.norm_of_nonneg hD]
      _ ≤ D ^ 2 * (2 * (sig P χ t (N * U) + sig P χ t (2 * N * U))) :=
          mul_le_mul_of_nonneg_left (dsum_two_le P χ t N U) (by positivity)
      _ = 2 * D ^ 2 * (sig P χ t (N * U) + sig P χ t (2 * N * U)) := by ring
  -- sum over the `φ(p)` characters and divide
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ p)).card = p.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p
  have hφ : (0 : ℝ) < p.totient := by exact_mod_cast Nat.totient_pos.2 hp.pos
  have htot := Finset.sum_le_sum fun ψ (_ : ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p))) => hle ψ
  rw [hsum, Finset.sum_const, hcard, nsmul_eq_mul] at htot
  exact le_of_mul_le_mul_left htot hφ

/-- **The lengthening with its constant**: for `q ≥ 1`, `N ≥ 0`, `U ≥ 12d(q)² + 4` and `D ≥ 0` with `d(m) ≤ D` for
`1 ≤ m ≤ 4NU`, `σ(N) ≤ 18d(q)D²(σ(NU) + σ(2NU))`. -/
theorem sig_le_lengthen (hq : 0 < q) {N U D : ℝ} (hN : 0 ≤ N) (hU : 12 * (q.divisors.card : ℝ) ^ 2 + 4 ≤ U)
    (hD : 0 ≤ D) (hdiv : ∀ m ∈ Finset.Icc 1 ⌊4 * N * U⌋₊, (m.divisors.card : ℝ) ≤ D) :
    sig P χ t N ≤ 18 * q.divisors.card * D ^ 2 * (sig P χ t (N * U) + sig P χ t (2 * N * U)) := by
  have hU0 : 0 ≤ U := by nlinarith
  have h1 := cqU_mul_sig_le P χ t hN hU0 hD hdiv
  have h2 := cqU_ge hq hU
  have hsig : 0 ≤ sig P χ t N := dsum_nonneg _ _ _ _
  have hdq : (0 : ℝ) < q.divisors.card := by
    have : 0 < q.divisors.card := Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 hq.ne'⟩
    exact_mod_cast this
  calc sig P χ t N = 9 * q.divisors.card * (1 / (9 * q.divisors.card) * sig P χ t N) := by
        rw [← mul_assoc, mul_one_div_cancel (mul_pos (by norm_num) hdq).ne', one_mul]
    _ ≤ 9 * q.divisors.card * (cqU q U * sig P χ t N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hsig) (by positivity)
    _ ≤ 9 * q.divisors.card * (2 * D ^ 2 * (sig P χ t (N * U) + sig P χ t (2 * N * U))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 18 * q.divisors.card * D ^ 2 * (sig P χ t (N * U) + sig P χ t (2 * N * U)) := by ring

end Lengthening

end LinnikCGLHBLen

#print axioms LinnikCGLHBLen.card_coprime_Ioc_ge
#print axioms LinnikCGLHBLen.cqU_ge
#print axioms LinnikCGLHBLen.sum_chars_norm_sq_eq
#print axioms LinnikCGLHBLen.cqU_mul_sig_le
#print axioms LinnikCGLHBLen.sig_le_lengthen
