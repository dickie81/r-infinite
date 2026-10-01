import Mathlib
import DHPrime

/-! # Coefficient localisation of the Davenport–Heilbronn prime side

`DHPrime.lean` writes `−dh′/dh = Σ c(n) n^{−s}` on `Re s > 2` with
`c = logMul(δ + u) ⍟ (δ + u)⁻¹` (`cDH`), where `δ + u = a/a(1)` is the normalised coefficient
sequence of `dh`. This file proves that `c` differs from the prime side `Λ·χ₅` of `L(s, χ₅)` only on
**inert-smooth** integers, those whose prime factors are all `≡ ±2 (mod 5)` (the primes with
`χ₅(p) = ±i`):

`c(n) = Λ(n) χ₅(n)` for every `n` with a prime factor `p = 5` or `p ≡ ±1 (mod 5)`
(`cDH_chi5_eq_of_dvd`), and in general `c = Λ·s + c_inert` with `c_inert` supported on the
inert-smooth integers (`cDH_chi5_decomp`, `logDer_inertA_mul_inertInvA_eq_zero`).

**The argument.** On `n ≥ 1`, `δ + u = αχ₅ + βχ₅⁻¹` with `α = (1 + ε′)/a(1)`, `β = (1 + ε)/a(1)`,
`α + β = 1` (`dhA_eq`, `alpha_add_beta`).

* *Unique factorisation*: for disjoint prime sets `P`, `Q`, `1_P ⍟ 1_Q = 1` on every `n ≠ 0` whose
  prime factors lie in `P ∪ Q` (`smoothInd_conv_eq_one`; both indicators are multiplicative, and the
  prime-power values are checked directly). For `P` = split (`≡ ±1`) and `Q` = inert (`≡ ±2`) this
  covers every `n` prime to `5`.
* *The split part* `s = χ₅·1_{split-smooth}` is completely multiplicative, and `χ₅` is real on it:
  `n² ≡ 1 (mod 5)` for split-smooth `n`, so `χ₅⁻¹(n) = χ₅(n)` (`chi5_inv_eq_of_split`). Twisting the
  factorisation by `χ₅` and by `χ₅⁻¹` gives `χ₅ = s ⍟ t` and `χ₅⁻¹ = s ⍟ t̄` with
  `t = χ₅·1_{inert-smooth}`, `t̄ = χ₅⁻¹·1_{inert-smooth}` (`splitSeq_conv_chi5Seq`,
  `splitSeq_conv_chi5InvSeq`), hence `δ + u = s ⍟ b` with `b = αt + βt̄`, `b(1) = 1`, `b` supported
  on inert-smooth integers (`dhA_eq_splitA_mul_inertA`).
* *The logarithmic derivative splits*: in the ring of arithmetic functions `X ↦ log·X` is a
  derivation (`logDer_mul`); with `(δ + u)⁻¹ = s⁻¹ ⍟ b⁻¹`, `s⁻¹ = μs` (`dhInvA_eq`,
  `cmul_convolution_moebiusC`), `c = log s ⍟ s⁻¹ + log b ⍟ b⁻¹` (`logDer_dhA_mul_dhInvA`);
  `log s ⍟ μs = Λs` (`cmul_logMul_convolution_moebiusC`, from Mathlib's `log * μ = Λ`); `b⁻¹` is
  supported on inert-smooth integers (`dinv_inertW_eq_zero`, by the recursion of `DInv.dinv`), so
  `log b ⍟ b⁻¹` is too.
* At `n` with a non-inert prime factor the inert term vanishes and `Λ(n)s(n) = Λ(n)χ₅(n)`: either `n`
  is split-smooth, or `Λ(n) = 0`, or `n` is a power of `5` and `χ₅(n) = 0`.
-/

open Complex DirichletCharacter LSeries
open scoped LSeries.notation

noncomputable section

namespace PsiOmega

/-! ## Smooth integers and their indicators -/

/-- `n` is `P`-smooth: every prime factor of `n` satisfies `P` (`0` and `1` are `P`-smooth). -/
def PrimeSmooth (P : ℕ → Prop) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, P p

instance (P : ℕ → Prop) [DecidablePred P] : DecidablePred (PrimeSmooth P) := fun n => by
  unfold PrimeSmooth; infer_instance

theorem primeSmooth_one (P : ℕ → Prop) : PrimeSmooth P 1 := by
  simp [PrimeSmooth]

theorem primeSmooth_mul (P : ℕ → Prop) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    PrimeSmooth P (m * n) ↔ PrimeSmooth P m ∧ PrimeSmooth P n := by
  simp only [PrimeSmooth, Nat.primeFactors_mul hm hn, Finset.mem_union]
  constructor
  · intro h
    exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp)
    exacts [h1 p hp, h2 p hp]

theorem primeSmooth_prime_pow (P : ℕ → Prop) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    PrimeSmooth P (p ^ k) ↔ P p := by
  simp [PrimeSmooth, Nat.primeFactors_prime_pow hk hp]

theorem not_primeSmooth_of_dvd (P : ℕ → Prop) {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hn : n ≠ 0) (hP : ¬ P p) : ¬ PrimeSmooth P n :=
  fun h => hP (h p (Nat.mem_primeFactors.2 ⟨hp, hpn, hn⟩))

/-- The indicator of the `P`-smooth integers. -/
def smoothInd (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℂ :=
  if PrimeSmooth P n then 1 else 0

theorem toAF_apply (f : ℕ → ℂ) (n : ℕ) :
    toArithmeticFunction f n = if n = 0 then 0 else f n := rfl

theorem isMultiplicative_smoothInd (P : ℕ → Prop) [DecidablePred P] :
    (toArithmeticFunction (smoothInd P)).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, fun {m n} hm hn _ => ?_⟩
  · simp [toAF_apply, smoothInd, primeSmooth_one]
  · simp only [toAF_apply, mul_ne_zero hm hn, hm, hn, ↓reduceIte, smoothInd,
      primeSmooth_mul P hm hn]
    split_ifs <;> simp_all

theorem smoothInd_prime_pow (P : ℕ → Prop) [DecidablePred P] {p : ℕ} (hp : p.Prime) (k : ℕ) :
    toArithmeticFunction (smoothInd P) (p ^ k) = if k = 0 ∨ P p then 1 else 0 := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  simp only [toAF_apply, hpk, ↓reduceIte, smoothInd]
  rcases eq_or_ne k 0 with rfl | hk
  · simp [primeSmooth_one]
  · simp [primeSmooth_prime_pow P hp hk, hk]

/-- **Unique factorisation into a `P`-part and a `Q`-part**: for disjoint prime sets `P`, `Q`,
`(1_P ⍟ 1_Q)(n) = 1` for every `n ≠ 0` whose prime factors all lie in `P ∪ Q`. -/
theorem smoothInd_conv_eq_one (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ p, ¬ (P p ∧ Q p)) {n : ℕ} (hn : n ≠ 0) (h : ∀ p ∈ n.primeFactors, P p ∨ Q p) :
    (smoothInd P ⍟ smoothInd Q) n = 1 := by
  rw [LSeries.convolution]
  have hmul :
      (toArithmeticFunction (smoothInd P) * toArithmeticFunction (smoothInd Q)).IsMultiplicative :=
    (isMultiplicative_smoothInd P).mul (isMultiplicative_smoothInd Q)
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd rfl hn
  | one => exact hmul.map_one
  | prime_pow p k hp hk =>
    have hpq : P p ∨ Q p :=
      h p (by rw [Nat.primeFactors_prime_pow hk.ne' hp]; exact Finset.mem_singleton_self p)
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal
        (fun a b => toArithmeticFunction (smoothInd P) a * toArithmeticFunction (smoothInd Q) b),
      Nat.sum_divisors_prime_pow hp]
    rcases hpq with hP | hQ
    · have hQ : ¬ Q p := fun hQ => hPQ p ⟨hP, hQ⟩
      rw [Finset.sum_eq_single k]
      · rw [Nat.div_self (pow_pos hp.pos k), (isMultiplicative_smoothInd Q).map_one,
          smoothInd_prime_pow P hp k]
        simp [hP]
      · intro i hi hik
        have hik' : i < k := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hik
        rw [Nat.pow_div hik'.le hp.pos, smoothInd_prime_pow Q hp (k - i)]
        simp [hQ, Nat.sub_ne_zero_of_lt hik']
      · intro hk'
        exact absurd (Finset.mem_range.2 (Nat.lt_succ_self k)) hk'
    · have hP : ¬ P p := fun hP => hPQ p ⟨hP, hQ⟩
      rw [Finset.sum_eq_single 0]
      · rw [pow_zero, Nat.div_one, (isMultiplicative_smoothInd P).map_one,
          smoothInd_prime_pow Q hp k]
        simp [hQ]
      · intro i _ hi0
        rw [smoothInd_prime_pow P hp i]
        simp [hP, hi0]
      · intro h0
        exact absurd (Finset.mem_range.2 (Nat.succ_pos k)) h0
  | coprime a b ha hb hab iha ihb =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    rw [hmul.map_mul_of_coprime hab,
      iha ha0 (fun p hp => h p (Nat.primeFactors_mono (Nat.dvd_mul_right a b) hn hp)),
      ihb hb0 (fun p hp => h p (Nat.primeFactors_mono (Nat.dvd_mul_left b a) hn hp)), mul_one]

/-! ## Completely multiplicative twists -/

/-- Twisting by a completely multiplicative `g` distributes over convolution. -/
theorem cmul_convolution_distrib (g : ℕ → ℂ) (hg : ∀ m n, g (m * n) = g m * g n)
    (f h : ℕ → ℂ) : (g * f) ⍟ (g * h) = g * (f ⍟ h) := by
  ext n
  simp only [Pi.mul_apply, LSeries.convolution_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(Nat.mem_divisorsAntidiagonal.mp hp).1.symm, hg]
  exact mul_mul_mul_comm ..

/-- `μ` as a complex sequence. -/
abbrev moebiusC : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)

/-- `Λ` as a complex sequence. -/
abbrev vonMangoldtC : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)

theorem one_convolution_moebiusC : (1 : ℕ → ℂ) ⍟ moebiusC = LSeries.delta := by
  show (1 : ℕ → ℂ) ⍟ (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) = LSeries.delta
  rw [one_convolution_eq_zeta_convolution, ← ArithmeticFunction.one_eq_delta]
  simp_rw [← ArithmeticFunction.natCoe_apply, ← ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.coe_mul, ArithmeticFunction.coe_zeta_mul_coe_moebius]

/-- `g ⍟ gμ = δ` for completely multiplicative `g` with `g 1 = 1`. -/
theorem cmul_convolution_moebiusC (g : ℕ → ℂ) (hg : ∀ m n, g (m * n) = g m * g n)
    (hg1 : g 1 = 1) : g ⍟ (g * moebiusC) = LSeries.delta := by
  nth_rewrite 1 [← mul_one g]
  rw [cmul_convolution_distrib g hg, one_convolution_moebiusC, LSeries.mul_delta hg1]

/-- `log ⍟ μ = Λ`, from Mathlib's `log * μ = Λ`. -/
theorem log_convolution_moebiusC :
    (fun n : ℕ => Complex.log n) ⍟ moebiusC = vonMangoldtC := by
  ext n
  rw [vonMangoldtC, ← ArithmeticFunction.log_mul_moebius_eq_vonMangoldt,
    ArithmeticFunction.mul_apply, LSeries.convolution_def]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ArithmeticFunction.log_apply, ArithmeticFunction.intCoe_apply, Complex.natCast_log]
  push_cast
  ring

/-- `log g ⍟ gμ = gΛ` for completely multiplicative `g`. -/
theorem cmul_logMul_convolution_moebiusC (g : ℕ → ℂ) (hg : ∀ m n, g (m * n) = g m * g n) :
    LSeries.logMul g ⍟ (g * moebiusC) = g * vonMangoldtC := by
  have e : LSeries.logMul g = g * fun n : ℕ => Complex.log n := by
    ext n
    show Complex.log n * g n = g n * Complex.log n
    ring
  rw [e, cmul_convolution_distrib g hg, log_convolution_moebiusC]

/-! ## The character on split and inert primes -/

/-- Primes `≡ ±1 (mod 5)`, where `χ₅(p) = ±1`. -/
def splitP (p : ℕ) : Prop := p % 5 = 1 ∨ p % 5 = 4

/-- Primes `≡ ±2 (mod 5)`, where `χ₅(p) = ±i`. -/
def inertP (p : ℕ) : Prop := p % 5 = 2 ∨ p % 5 = 3

instance : DecidablePred splitP := fun p => by unfold splitP; infer_instance

instance : DecidablePred inertP := fun p => by unfold inertP; infer_instance

theorem not_splitP_and_inertP (p : ℕ) : ¬ (splitP p ∧ inertP p) := by
  unfold splitP inertP; omega

theorem splitP_or_inertP {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : splitP p ∨ inertP p := by
  have h0 : p % 5 ≠ 0 := by
    intro h
    have h5p : 5 ∣ p := Nat.dvd_of_mod_eq_zero h
    exact h5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 h5p).symm
  unfold splitP inertP
  omega

theorem chi5_natCast_mul (m n : ℕ) : chi5 ((m * n : ℕ) : ZMod 5) = chi5 m * chi5 n := by
  rw [Nat.cast_mul, map_mul]

theorem chi5_inv_natCast_mul (m n : ℕ) :
    chi5⁻¹ ((m * n : ℕ) : ZMod 5) = chi5⁻¹ m * chi5⁻¹ n := by
  rw [Nat.cast_mul, map_mul]

theorem chi5_natCast_eq_zero {n : ℕ} (h : 5 ∣ n) : chi5 (n : ZMod 5) = 0 := by
  rw [(ZMod.natCast_eq_zero_iff n 5).2 h, chi5_apply_zero]

theorem chi5_inv_natCast_eq_zero {n : ℕ} (h : 5 ∣ n) : chi5⁻¹ (n : ZMod 5) = 0 := by
  rw [chi5_inv_apply, chi5_natCast_eq_zero h, map_zero]

/-- Split-smooth integers are `≡ ±1 (mod 5)`. -/
theorem zmod5_sq_of_split {n : ℕ} (hn : n ≠ 0) (h : PrimeSmooth splitP n) :
    ((n : ZMod 5)) ^ 2 = 1 := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simp
  | prime p hp =>
    have hp5 := h p (Nat.mem_primeFactors.2 ⟨hp, dvd_refl p, hp.ne_zero⟩)
    rw [← ZMod.natCast_mod p 5]
    rcases hp5 with h1 | h4
    · rw [h1]; decide
    · rw [h4]; decide
  | mul a b iha ihb =>
    have ha : a ≠ 0 := left_ne_zero_of_mul hn
    have hb : b ≠ 0 := right_ne_zero_of_mul hn
    have hab := (primeSmooth_mul splitP ha hb).1 h
    rw [Nat.cast_mul, mul_pow, iha ha hab.1, ihb hb hab.2, one_mul]

/-- **`χ₅` is real on split-smooth integers**: `χ₅⁻¹(n) = χ₅(n)`. -/
theorem chi5_inv_eq_of_split {n : ℕ} (h : PrimeSmooth splitP n) :
    chi5⁻¹ (n : ZMod 5) = chi5 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero, chi5_inv_apply, chi5_apply_zero, map_zero]
  · have hsq := zmod5_sq_of_split hn h
    have h1 : chi5 (n : ZMod 5) * chi5 n = 1 := by rw [← map_mul, ← sq, hsq, map_one]
    rw [MulChar.inv_apply_eq_inv']
    exact inv_eq_of_mul_eq_one_right h1

/-! ## The split part `s` and the inert parts `t`, `t̄` -/

/-- `χ₅` as a sequence. -/
abbrev chi5Seq : ℕ → ℂ := fun n => chi5 n

/-- `χ₅⁻¹` as a sequence. -/
abbrev chi5InvSeq : ℕ → ℂ := fun n => chi5⁻¹ n

/-- The split part `s = χ₅ · 1_{split-smooth}`. -/
def splitSeq : ℕ → ℂ := chi5Seq * smoothInd splitP

theorem smoothInd_mul (P : ℕ → Prop) [DecidablePred P] {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    smoothInd P (m * n) = smoothInd P m * smoothInd P n := by
  simp only [smoothInd, primeSmooth_mul P hm hn]
  split_ifs <;> simp_all

theorem chi5Seq_zero : chi5Seq 0 = 0 := by
  show chi5 ((0 : ℕ) : ZMod 5) = 0
  rw [Nat.cast_zero, chi5_apply_zero]

theorem chi5Seq_one : chi5Seq 1 = 1 := by
  show chi5 ((1 : ℕ) : ZMod 5) = 1
  rw [Nat.cast_one, chi5_apply_one]

/-- `s` is completely multiplicative. -/
theorem splitSeq_mul (m n : ℕ) : splitSeq (m * n) = splitSeq m * splitSeq n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [splitSeq, chi5Seq_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [splitSeq, chi5Seq_zero]
  simp only [splitSeq, Pi.mul_apply, chi5Seq, chi5_natCast_mul, smoothInd_mul splitP hm hn]
  ring

theorem splitSeq_one : splitSeq 1 = 1 := by
  simp [splitSeq, smoothInd, primeSmooth_one, chi5Seq_one]

/-- On split-smooth integers `χ₅⁻¹ = χ₅`, so `χ₅⁻¹ · 1_{split-smooth} = s`. -/
theorem chi5InvSeq_mul_split : chi5InvSeq * smoothInd splitP = splitSeq := by
  ext n
  simp only [Pi.mul_apply, splitSeq, chi5Seq, chi5InvSeq, smoothInd]
  split_ifs with h
  · rw [chi5_inv_eq_of_split h]
  · simp

/-- Twisting `1_{split} ⍟ 1_{inert}` by any `g` vanishing on multiples of `5` gives back `g`. -/
theorem mul_conv_smoothInd (g : ℕ → ℂ) (hg0 : ∀ n, 5 ∣ n → g n = 0) :
    g * (smoothInd splitP ⍟ smoothInd inertP) = g := by
  ext n
  rw [Pi.mul_apply]
  by_cases h5 : 5 ∣ n
  · rw [hg0 n h5, zero_mul]
  · have hn : n ≠ 0 := by rintro rfl; exact h5 (dvd_zero 5)
    rw [smoothInd_conv_eq_one splitP inertP not_splitP_and_inertP hn, mul_one]
    intro p hp
    have hp' := Nat.mem_primeFactors.1 hp
    refine splitP_or_inertP hp'.1 ?_
    rintro rfl
    exact h5 hp'.2.1

/-- **`χ₅ = s ⍟ t`**, `t = χ₅ · 1_{inert-smooth}`. -/
theorem splitSeq_conv_chi5Seq : splitSeq ⍟ (chi5Seq * smoothInd inertP) = chi5Seq := by
  rw [splitSeq, cmul_convolution_distrib chi5Seq chi5_natCast_mul,
    mul_conv_smoothInd chi5Seq (fun _ h => chi5_natCast_eq_zero h)]

/-- **`χ₅⁻¹ = s ⍟ t̄`**, `t̄ = χ₅⁻¹ · 1_{inert-smooth}`. -/
theorem splitSeq_conv_chi5InvSeq :
    splitSeq ⍟ (chi5InvSeq * smoothInd inertP) = chi5InvSeq := by
  rw [← chi5InvSeq_mul_split, cmul_convolution_distrib chi5InvSeq chi5_inv_natCast_mul,
    mul_conv_smoothInd chi5InvSeq (fun _ h => chi5_inv_natCast_eq_zero h)]

/-! ## The factorisation `δ + u = s ⍟ b` in the ring of arithmetic functions -/

theorem toAF_conv (f g : ℕ → ℂ) :
    toArithmeticFunction (f ⍟ g) = toArithmeticFunction f * toArithmeticFunction g :=
  ArithmeticFunction.toArithmeticFunction_eq_self _

theorem toAF_delta : toArithmeticFunction LSeries.delta = (1 : ArithmeticFunction ℂ) := by
  rw [← ArithmeticFunction.one_eq_delta]
  exact ArithmeticFunction.toArithmeticFunction_eq_self _

/-- The logarithmic derivation `X ↦ log · X` on arithmetic functions. -/
def logDer (X : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  toArithmeticFunction (LSeries.logMul ⇑X)

theorem logDer_apply (X : ArithmeticFunction ℂ) (n : ℕ) :
    logDer X n = Complex.log n * X n := by
  rw [logDer, toAF_apply]
  split_ifs with h
  · rw [h, ArithmeticFunction.map_zero, mul_zero]
  · rfl

/-- **`log` is a derivation of Dirichlet convolution.** -/
theorem logDer_mul (X Y : ArithmeticFunction ℂ) :
    logDer (X * Y) = logDer X * Y + X * logDer Y := by
  ext n
  rw [logDer_apply, ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [logDer_apply, logDer_apply]
  obtain ⟨hpn, hn0⟩ := Nat.mem_divisorsAntidiagonal.1 hp
  have h0 : p.1 * p.2 ≠ 0 := by rw [hpn]; exact hn0
  have ha : (p.1 : ℝ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul h0
  have hb : (p.2 : ℝ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul h0
  rw [← hpn, ← Complex.natCast_log, ← Complex.natCast_log, ← Complex.natCast_log, Nat.cast_mul,
    Real.log_mul ha hb, Complex.ofReal_add]
  ring

/-- `δ + u` as an arithmetic function. -/
def dhA : ArithmeticFunction ℂ := toArithmeticFunction (LSeries.delta + uDH chi5)

/-- Its inverse `(δ + u)⁻¹`. -/
def dhInvA : ArithmeticFunction ℂ := toArithmeticFunction (DInv.dinv (uDH chi5))

/-- The split part `s`. -/
def splitA : ArithmeticFunction ℂ := toArithmeticFunction splitSeq

/-- Its inverse `sμ`. -/
def splitInvA : ArithmeticFunction ℂ := toArithmeticFunction (splitSeq * moebiusC)

/-- `t = χ₅ · 1_{inert-smooth}`. -/
def inertChiA : ArithmeticFunction ℂ := toArithmeticFunction (chi5Seq * smoothInd inertP)

/-- `t̄ = χ₅⁻¹ · 1_{inert-smooth}`. -/
def inertChiInvA : ArithmeticFunction ℂ :=
  toArithmeticFunction (chi5InvSeq * smoothInd inertP)

/-- `α = (1 + ε′)/a(1)`. -/
def alphaDH : ℂ := (1 + rootNumber chi5⁻¹) / aDH chi5 1

/-- `β = (1 + ε)/a(1)`. -/
def betaDH : ℂ := (1 + rootNumber chi5) / aDH chi5 1

/-- The inert part `b = αt + βt̄`, supported on inert-smooth integers. -/
def inertA : ArithmeticFunction ℂ := alphaDH • inertChiA + betaDH • inertChiInvA

/-- `b − δ`, vanishing at `0` and `1`. -/
def inertW (n : ℕ) : ℂ := inertA n - LSeries.delta n

/-- The inverse of `b`. -/
def inertInvA : ArithmeticFunction ℂ := toArithmeticFunction (DInv.dinv inertW)

theorem aDH_one_ne_zero_chi5 : aDH chi5 1 ≠ 0 :=
  aDH_one_ne_zero chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero

theorem dhA_mul_dhInvA : dhA * dhInvA = 1 := by
  rw [dhA, dhInvA, ← toAF_conv, DInv.convolution_dinv (uDH chi5) uDH_zero uDH_one, toAF_delta]

theorem splitA_mul_splitInvA : splitA * splitInvA = 1 := by
  rw [splitA, splitInvA, ← toAF_conv,
    cmul_convolution_moebiusC splitSeq splitSeq_mul splitSeq_one, toAF_delta]

theorem toAF_chi5Seq : toArithmeticFunction chi5Seq = splitA * inertChiA := by
  rw [splitA, inertChiA, ← toAF_conv, splitSeq_conv_chi5Seq]

theorem toAF_chi5InvSeq : toArithmeticFunction chi5InvSeq = splitA * inertChiInvA := by
  rw [splitA, inertChiInvA, ← toAF_conv, splitSeq_conv_chi5InvSeq]

/-- `δ + u = αχ₅ + βχ₅⁻¹` on `n ≥ 1`. -/
theorem dhA_eq :
    dhA = alphaDH • toArithmeticFunction chi5Seq + betaDH • toArithmeticFunction chi5InvSeq := by
  ext n
  rw [ArithmeticFunction.add_apply, ArithmeticFunction.smul_map, ArithmeticFunction.smul_map, dhA,
    toAF_apply, toAF_apply, toAF_apply]
  split_ifs with hn
  · simp
  · have h := aDH_eq_of_ne_zero aDH_one_ne_zero_chi5 hn
    have ha : aDH chi5 n =
        (1 + rootNumber chi5⁻¹) * chi5 n + (1 + rootNumber chi5) * chi5⁻¹ n := rfl
    rw [smul_eq_mul, smul_eq_mul, alphaDH, betaDH, div_mul_eq_mul_div, div_mul_eq_mul_div,
      ← add_div, eq_div_iff aDH_one_ne_zero_chi5]
    linear_combination ha - h

/-- **`δ + u = s ⍟ b`.** -/
theorem dhA_eq_splitA_mul_inertA : dhA = splitA * inertA := by
  rw [dhA_eq, toAF_chi5Seq, toAF_chi5InvSeq, inertA, mul_add, mul_smul_comm, mul_smul_comm]

theorem alpha_add_beta : alphaDH + betaDH = 1 := by
  rw [alphaDH, betaDH, ← add_div, div_eq_one_iff_eq aDH_one_ne_zero_chi5, aDH_one]
  ring

theorem inertA_apply_one : inertA 1 = 1 := by
  have hT : inertChiA 1 = 1 := by
    simp [inertChiA, toAF_apply, chi5Seq, smoothInd, primeSmooth_one]
  have hTb : inertChiInvA 1 = 1 := by
    simp [inertChiInvA, toAF_apply, chi5InvSeq, smoothInd, primeSmooth_one]
  rw [inertA, ArithmeticFunction.add_apply, ArithmeticFunction.smul_map,
    ArithmeticFunction.smul_map, hT, hTb, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    alpha_add_beta]

/-- `b` is supported on inert-smooth integers. -/
theorem inertA_apply_of_not {n : ℕ} (h : ¬ PrimeSmooth inertP n) : inertA n = 0 := by
  simp [inertA, inertChiA, inertChiInvA, toAF_apply, smoothInd, h]

theorem inertA_mul_inertInvA : inertA * inertInvA = 1 := by
  have hw0 : inertW 0 = 0 := by simp [inertW, LSeries.delta]
  have hw1 : inertW 1 = 0 := by simp [inertW, LSeries.delta, inertA_apply_one]
  have e : LSeries.delta + inertW = ⇑inertA := by
    ext n
    simp [inertW]
  have h := DInv.convolution_dinv inertW hw0 hw1
  rw [e] at h
  have h2 := congrArg toArithmeticFunction h
  rw [toAF_conv, ArithmeticFunction.toArithmeticFunction_eq_self, toAF_delta] at h2
  exact h2

/-- The inverse of `b` is supported on inert-smooth integers. -/
theorem dinv_inertW_eq_zero (n : ℕ) (hn : ¬ PrimeSmooth inertP n) :
    DInv.dinv inertW n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hn (by simp [PrimeSmooth])
    have hn1 : n ≠ 1 := by
      rintro rfl
      exact hn (primeSmooth_one _)
    obtain ⟨p, hp, hpi⟩ : ∃ p ∈ n.primeFactors, ¬ inertP p := by
      by_contra hc
      push Not at hc
      exact hn hc
    have hp' := Nat.mem_primeFactors.1 hp
    rw [DInv.dinv_of_two_le inertW (by omega), neg_eq_zero]
    refine Finset.sum_eq_zero fun q hq => ?_
    obtain ⟨hqn, hq1⟩ := Finset.mem_filter.1 hq
    obtain ⟨hde, -⟩ := Nat.mem_divisorsAntidiagonal.1 hqn
    have hd0 : q.1 ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hde
      exact hn0 hde.symm
    have he0 : q.2 ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hde
      exact hn0 hde.symm
    rcases (Nat.Prime.dvd_mul hp'.1).1 (by rw [hde]; exact hp'.2.1) with hpd | hpe
    · have hw : inertW q.1 = 0 := by
        rw [inertW, inertA_apply_of_not (not_primeSmooth_of_dvd inertP hp'.1 hpd hd0 hpi)]
        simp [LSeries.delta, hq1]
      rw [hw, zero_mul]
    · have hlt : q.2 < n := by
        have h2 : 2 ≤ q.1 := by omega
        have h1 : 1 ≤ q.2 := Nat.one_le_iff_ne_zero.2 he0
        nlinarith
      rw [ih q.2 hlt (not_primeSmooth_of_dvd inertP hp'.1 hpe he0 hpi), mul_zero]

/-- `(δ + u)⁻¹ = s⁻¹ ⍟ b⁻¹`. -/
theorem dhInvA_eq : dhInvA = splitInvA * inertInvA := by
  linear_combination (-dhInvA * inertA * inertInvA) * splitA_mul_splitInvA
    - dhInvA * inertA_mul_inertInvA - (splitInvA * inertInvA * dhInvA) * dhA_eq_splitA_mul_inertA
    + (splitInvA * inertInvA) * dhA_mul_dhInvA

/-- **The logarithmic derivative splits**:
`log(δ + u) ⍟ (δ + u)⁻¹ = log s ⍟ s⁻¹ + log b ⍟ b⁻¹`. -/
theorem logDer_dhA_mul_dhInvA :
    logDer dhA * dhInvA = logDer splitA * splitInvA + logDer inertA * inertInvA := by
  rw [dhA_eq_splitA_mul_inertA, logDer_mul, dhInvA_eq]
  linear_combination (logDer splitA * splitInvA) * inertA_mul_inertInvA
    + (logDer inertA * inertInvA) * splitA_mul_splitInvA

/-- The split contribution is `Λ · s`. -/
theorem logDer_splitA_mul_splitInvA :
    logDer splitA * splitInvA = toArithmeticFunction (splitSeq * vonMangoldtC) := by
  have e : logDer splitA = toArithmeticFunction (LSeries.logMul splitSeq) := by
    rw [logDer, splitA]
    exact toArithmeticFunction_congr (fun {n} hn => by simp [LSeries.logMul, toAF_apply, hn])
  rw [e, splitInvA, ← toAF_conv, cmul_logMul_convolution_moebiusC splitSeq splitSeq_mul]

/-- The inert contribution is supported on inert-smooth integers. -/
theorem logDer_inertA_mul_inertInvA_eq_zero {n : ℕ} (h : ¬ PrimeSmooth inertP n) :
    (logDer inertA * inertInvA) n = 0 := by
  obtain ⟨p, hp, hpi⟩ : ∃ p ∈ n.primeFactors, ¬ inertP p := by
    by_contra hc
    push Not at hc
    exact h hc
  have hp' := Nat.mem_primeFactors.1 hp
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨hde, hn0⟩ := Nat.mem_divisorsAntidiagonal.1 hq
  have hd0 : q.1 ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hde
    exact hn0 hde.symm
  have he0 : q.2 ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hde
    exact hn0 hde.symm
  rcases (Nat.Prime.dvd_mul hp'.1).1 (by rw [hde]; exact hp'.2.1) with hpd | hpe
  · rw [logDer_apply, inertA_apply_of_not (not_primeSmooth_of_dvd inertP hp'.1 hpd hd0 hpi),
      mul_zero, zero_mul]
  · simp only [inertInvA, toAF_apply, he0, ↓reduceIte,
      dinv_inertW_eq_zero q.2 (not_primeSmooth_of_dvd inertP hp'.1 hpe he0 hpi), mul_zero]

theorem cDH_chi5_eq_logDer : cDH chi5 = ⇑(logDer dhA * dhInvA) := by
  have e : toArithmeticFunction (LSeries.logMul (LSeries.delta + uDH chi5)) = logDer dhA := by
    rw [logDer, dhA]
    exact toArithmeticFunction_congr (fun {n} hn => by simp [LSeries.logMul, toAF_apply, hn])
  rw [cDH, LSeries.convolution, e, dhInvA]

/-- **The split/inert decomposition of the prime side**: `c(n) = Λ(n)s(n) + c_inert(n)` for every
`n`, with `s = χ₅·1_{split-smooth}` and `c_inert = log b ⍟ b⁻¹` supported on inert-smooth integers
(`logDer_inertA_mul_inertInvA_eq_zero`). -/
theorem cDH_chi5_decomp (n : ℕ) :
    cDH chi5 n = (ArithmeticFunction.vonMangoldt n : ℂ) * splitSeq n
      + (logDer inertA * inertInvA) n := by
  rw [cDH_chi5_eq_logDer, logDer_dhA_mul_dhInvA, ArithmeticFunction.add_apply,
    logDer_splitA_mul_splitInvA, toAF_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [hn, ↓reduceIte, Pi.mul_apply, vonMangoldtC]
    ring

/-- **Coefficient localisation**: at every `n` with a prime factor `p ≢ ±2 (mod 5)` (that is,
`p = 5` or `p ≡ ±1`), `c(n) = Λ(n) χ₅(n)`. -/
theorem cDH_chi5_eq_of_dvd {n : ℕ} (h : ∃ p, p.Prime ∧ p ∣ n ∧ p % 5 ≠ 2 ∧ p % 5 ≠ 3) :
    cDH chi5 n = (ArithmeticFunction.vonMangoldt n : ℂ) * chi5 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [cDH]
  obtain ⟨p, hp, hpn, hp2, hp3⟩ := h
  have hpi : ¬ inertP p := by unfold inertP; omega
  have hni : ¬ PrimeSmooth inertP n := not_primeSmooth_of_dvd inertP hp hpn hn hpi
  rw [cDH_chi5_decomp, logDer_inertA_mul_inertInvA_eq_zero hni, add_zero]
  simp only [splitSeq, Pi.mul_apply, chi5Seq, smoothInd]
  split_ifs with hs
  · ring
  · by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · rw [hΛ]
      simp
    · obtain ⟨q, k, hq, hk, rfl⟩ :=
        (isPrimePow_nat_iff n).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
      have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hpn)
      subst hpq
      have hsp : ¬ splitP p := fun h' => hs ((primeSmooth_prime_pow splitP hp hk.ne').2 h')
      have h5 : p = 5 := by
        have h0 : p % 5 = 0 := by unfold splitP at hsp; omega
        exact ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1
          (Nat.dvd_of_mod_eq_zero h0)).symm
      rw [chi5_natCast_eq_zero (h5 ▸ dvd_pow_self p hk.ne')]
      ring

end PsiOmega

#print axioms PsiOmega.smoothInd_conv_eq_one
#print axioms PsiOmega.cmul_convolution_distrib
#print axioms PsiOmega.cmul_convolution_moebiusC
#print axioms PsiOmega.log_convolution_moebiusC
#print axioms PsiOmega.cmul_logMul_convolution_moebiusC
#print axioms PsiOmega.zmod5_sq_of_split
#print axioms PsiOmega.chi5_inv_eq_of_split
#print axioms PsiOmega.splitSeq_mul
#print axioms PsiOmega.splitSeq_conv_chi5Seq
#print axioms PsiOmega.splitSeq_conv_chi5InvSeq
#print axioms PsiOmega.logDer_mul
#print axioms PsiOmega.dhA_eq
#print axioms PsiOmega.dhA_eq_splitA_mul_inertA
#print axioms PsiOmega.alpha_add_beta
#print axioms PsiOmega.inertA_mul_inertInvA
#print axioms PsiOmega.dinv_inertW_eq_zero
#print axioms PsiOmega.dhInvA_eq
#print axioms PsiOmega.logDer_dhA_mul_dhInvA
#print axioms PsiOmega.logDer_splitA_mul_splitInvA
#print axioms PsiOmega.logDer_inertA_mul_inertInvA_eq_zero
#print axioms PsiOmega.cDH_chi5_eq_logDer
#print axioms PsiOmega.cDH_chi5_decomp
#print axioms PsiOmega.cDH_chi5_eq_of_dvd
