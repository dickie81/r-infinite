import Mathlib
import DensityCore

/-! # The mollifier identity (round 235)

* `moll_identity`: `M_X(s)·Σ_{n≤N} n^{−s} = 1 + Σ_{X<j≤XN} a_j j^{−s}` for `X ≤ N`, where
  `M_X(s) = Σ_{m≤X} μ(m)m^{−s}` (`a_1 = 1`; `a_j = Σ_{m|j} μ(m) = 0` for `1 < j ≤ X`);
* `DPval_eq_cpow`: `D(β + iγ) = Σ_{X<j≤XN} a_j j^{−(β+iγ)}`;
* `norm_moll_le`: `|M_X(β + iγ)| ≤ X^{1−σ}(1 + log X)` for `β ≥ σ ≥ 0`.
-/

open Real Finset Complex

noncomputable section

namespace ShortWeil

open Pilot1ca Pilot1bt DirMean

/-- `M_X(s) = Σ_{m≤X} μ(m) m^{−s}`. -/
def moll (X : ℕ) (s : ℂ) : ℂ := ∑ m ∈ Ioc 0 X, ((ArithmeticFunction.moebius m : ℤ) : ℂ) * (m : ℂ) ^ (-s)

/-- `Σ_{d|n} μ(d) = [n = 1]`. -/
theorem sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n) (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] at h
  exact h

theorem natCast_mul_cpow (m n : ℕ) (s : ℂ) : ((m * n : ℕ) : ℂ) ^ s = (m : ℂ) ^ s * (n : ℂ) ^ s := by
  have := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) n) s
  push_cast at this ⊢
  exact this

/-- **The mollifier identity.** -/
theorem moll_identity {X N : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) (s : ℂ) :
    moll X s * ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s)
      = 1 + ∑ j ∈ Ioc X (X * N), mollC X N j * (j : ℂ) ^ (-s) := by
  classical
  set f : ℕ → ℂ := fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ) with hf
  -- expand and regroup by `j = mn`
  have h1 : moll X s * ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s)
      = ∑ m ∈ Ioc 0 X, ∑ j ∈ (Ioc 0 (X * N)).filter (fun j => m ∣ j ∧ j / m ≤ N), f m * (j : ℂ) ^ (-s) := by
    unfold moll
    rw [sum_mul]
    refine sum_congr rfl fun m hm => ?_
    have hm0 : 0 < m := (mem_Ioc.1 hm).1
    rw [mul_sum]
    have himg : (Ioc 0 N).image (m * ·) = (Ioc 0 (X * N)).filter (fun j => m ∣ j ∧ j / m ≤ N) := by
      ext j
      simp only [mem_image, mem_filter, mem_Ioc]
      constructor
      · rintro ⟨n, ⟨hn0, hnN⟩, rfl⟩
        refine ⟨⟨by positivity, Nat.mul_le_mul (mem_Ioc.1 hm).2 hnN⟩, dvd_mul_right m n, ?_⟩
        rw [Nat.mul_div_cancel_left n hm0]; exact hnN
      · rintro ⟨⟨hj0, _⟩, ⟨n, rfl⟩, hnN⟩
        rw [Nat.mul_div_cancel_left n hm0] at hnN
        exact ⟨n, ⟨Nat.pos_of_ne_zero fun h => by simp [h] at hj0, hnN⟩, rfl⟩
    rw [← himg, sum_image fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hm0 hab]
    refine sum_congr rfl fun n _ => ?_
    rw [natCast_mul_cpow]; ring
  -- swap the sums
  have h2 : ∑ m ∈ Ioc 0 X, ∑ j ∈ (Ioc 0 (X * N)).filter (fun j => m ∣ j ∧ j / m ≤ N), f m * (j : ℂ) ^ (-s)
      = ∑ j ∈ Ioc 0 (X * N), mollC X N j * (j : ℂ) ^ (-s) := by
    simp_rw [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun j hj => ?_
    have hj0 : j ≠ 0 := (Nat.pos_of_ne_zero fun h => by simp [h] at hj).ne'
    unfold mollC
    rw [sum_mul]
    simp only [ite_mul, zero_mul]
    rw [← sum_filter, ← sum_filter]
    apply sum_congr _ fun _ _ => rfl
    · ext m
      simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hm0, hmX⟩, hmj, hjN⟩; exact ⟨⟨hmj, hj0⟩, hmX, hjN⟩
      · rintro ⟨⟨hmj, _⟩, hmX, hjN⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hmj (Nat.pos_of_ne_zero hj0), hmX⟩, hmj, hjN⟩
  -- split off `j = 1` and the vanishing range `1 < j ≤ X`
  have hsplit : Ioc 0 (X * N) = {1} ∪ Ioc 1 X ∪ Ioc X (X * N) := by
    ext j
    simp only [mem_union, mem_singleton, mem_Ioc]
    have : X ≤ X * N := Nat.le_mul_of_pos_right X (by omega)
    omega
  have hdisj1 : Disjoint ({1} : Finset ℕ) (Ioc 1 X) := by
    rw [disjoint_singleton_left]; simp
  have hdisj2 : Disjoint ({1} ∪ Ioc 1 X) (Ioc X (X * N)) := by
    rw [disjoint_union_left]
    constructor
    · rw [disjoint_singleton_left]; simp; omega
    · exact disjoint_left.2 fun a ha hb => by simp only [mem_Ioc] at ha hb; omega
  have h1c : mollC X N 1 = 1 := by
    unfold mollC
    simp [Nat.divisors_one, hX, show 1 ≤ N by omega]
  have hzero : ∀ j ∈ Ioc 1 X, mollC X N j = 0 := by
    intro j hj
    obtain ⟨hj1, hjX⟩ := mem_Ioc.1 hj
    unfold mollC
    have hall : ∀ m ∈ j.divisors, (m ≤ X ∧ j / m ≤ N) := by
      intro m hm
      have hmj := Nat.divisor_le hm
      exact ⟨hmj.trans hjX, (Nat.div_le_self j m).trans (hjX.trans hXN)⟩
    rw [sum_congr rfl (g := fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) fun m hm => by
      simp only [hall m hm, and_self, ↓reduceIte], sum_divisors_moebius]
    simp only [show j ≠ 1 by omega, ↓reduceIte]
  rw [h1, h2, hsplit, sum_union hdisj2, sum_union hdisj1, sum_singleton, h1c,
    sum_eq_zero fun j hj => by rw [hzero j hj, zero_mul]]
  simp

/-- `j^{−(β+iγ)} = j^{−β} e^{−iγ log j}`. -/
theorem natCast_cpow_neg (j : ℕ) (hj : 0 < j) (β γ : ℝ) :
    (j : ℂ) ^ (-((β : ℂ) + γ * I)) = (((j : ℝ) ^ (-β) : ℝ) : ℂ) * Complex.exp (-(I * ((γ * Real.log j : ℝ) : ℂ))) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hj.ne'), Real.rpow_def_of_pos hj0,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  rw [show ((j : ℂ)) = ((j : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_log hj0.le]
  push_cast; ring

/-- `D(β + iγ) = Σ_{X<j≤XN} a_j j^{−(β+iγ)}`. -/
theorem DPval_eq_cpow (X N : ℕ) (β γ : ℝ) :
    DPval X N β γ = ∑ j ∈ Ioc X (X * N), mollC X N j * (j : ℂ) ^ (-((β : ℂ) + γ * I)) := by
  unfold DPval dp
  refine sum_congr rfl fun j hj => ?_
  rw [natCast_cpow_neg j (by have := (mem_Ioc.1 hj).1; omega)]
  ring

/-- **`|M_X(β + iγ)| ≤ X^{1−σ}(1 + log X)`** for `β ≥ σ`, `σ ≤ 1`. -/
theorem norm_moll_le {X : ℕ} {σ β γ : ℝ} (hσ1 : σ ≤ 1) (hβ : σ ≤ β) :
    ‖moll X ((β : ℂ) + γ * I)‖ ≤ (X : ℝ) ^ (1 - σ) * (1 + Real.log X) := by
  unfold moll
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ Ioc 0 X, ‖((ArithmeticFunction.moebius m : ℤ) : ℂ) * (m : ℂ) ^ (-((β : ℂ) + γ * I))‖
      ≤ (X : ℝ) ^ (1 - σ) * (1 / m) := by
    intro m hm
    obtain ⟨hm0, hmX⟩ := mem_Ioc.1 hm
    have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
    have hmX' : (m : ℝ) ≤ X := by exact_mod_cast hmX
    rw [norm_mul, Complex.norm_intCast, natCast_cpow_neg m hm0 β γ, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _),
      DirMean.norm_exp_neg_I_mul, mul_one]
    have hμ : (|((ArithmeticFunction.moebius m : ℤ) : ℝ)|) ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h1 : (m : ℝ) ^ (-β) ≤ (m : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm0) (by linarith)
    have h2 : (m : ℝ) ^ (-σ) = (m : ℝ) ^ (1 - σ) * (1 / m) := by
      rw [show -σ = (1 - σ) + (-1) by ring, Real.rpow_add hm0', Real.rpow_neg_one, one_div]
    have h3 : (m : ℝ) ^ (1 - σ) ≤ (X : ℝ) ^ (1 - σ) := Real.rpow_le_rpow hm0'.le hmX' (by linarith)
    calc |((ArithmeticFunction.moebius m : ℤ) : ℝ)| * (m : ℝ) ^ (-β) ≤ 1 * (m : ℝ) ^ (-σ) :=
          mul_le_mul hμ h1 (by positivity) zero_le_one
      _ = (m : ℝ) ^ (1 - σ) * (1 / m) := by rw [one_mul, h2]
      _ ≤ (X : ℝ) ^ (1 - σ) * (1 / m) := by gcongr
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (DivSq.harmonic_le X) (by positivity)

end ShortWeil

#print axioms ShortWeil.moll_identity
#print axioms ShortWeil.DPval_eq_cpow
#print axioms ShortWeil.norm_moll_le
