/-
# Round 664: the Fourier decay of `ψ·K(· − u′)`, the pieces of their `f_b` (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 663's `f_b = ψR̃(·, −b)²` has `R̃(u, a)² = ∫_{[1/2,2]}K(u − u′)|R(u′, a)|² du′`, with the kernel
`K(x) = Lψ̃₀(Lx/(2X))` (`kerL`), `L = NM₂/q` and `X` for their `(qT)^ϵ`. So `f_b` is an average over `u′` of
`φ_{u′}(u) = ψ(u)K(u − u′)` against `|R(u′, −b)|²`. This file bounds the Fourier transform of each `φ_{u′}`, the
first half of the decay that their Proposition 8.1 asks for. They argue: "By (7.4), it follows that
F((NM₂/q) ψ̃((NM₂/q) u))(ξ) = ψ̃̂(qξ/(NM₂)) = 2(qT)^ϵ ψ̃̂₀(2(qT)^ϵqξ/(NM₂)) ≪_j 2(qT)^ϵ (NM₂/(2(qT)^ϵq|ξ|))^j ≪_j
(qT)^ϵ (NM₂/(q|ξ|))^j." (text layer lines 5761–5785; spaces restored, the transform, tildes, hats, large
parentheses, fractions, subscripts and exponents transcribed), and then apply "the convolution theorem" (line 5786).
The stack keeps `ψ` in the integrand and integrates by parts instead.

The bound. `K(· − u′)` has `m`-th derivative `L·c^m·ψ̃₀^{(m)}(c(x − u′))` with `c = L/(2X)`, so
`|K^{(m)}| ≤ Lc^m·S₀(m)` with `S₀(m) = sup|ψ̃₀^{(m)}|`, and `∫|K^{(m)}| = 2Xc^m·I₀(m)` with `I₀(m) = ∫|ψ̃₀^{(m)}|`. By
Leibniz's rule `|φ_{u′}^{(j)}| ≤ Σ_{i≤j}C(j, i)|ψ^{(i)}||K^{(j−i)}(· − u′)|`. The term `i = 0` is at most `|K^{(j)}|`,
since `|ψ| ≤ 1`, and integrates to `2Xc^j·I₀(j)`. A term `i ≥ 1` integrates to at most `P(i)·Lc^{j−i}S₀(j−i)`, with
`P(i) = ∫|ψ^{(i)}|`. So `∫|φ_{u′}^{(j)}| ≤ B_j(L, X)`, the sum of these, and round 588's integration by parts
(`SieveSmooth.pow_mul_norm_fourier_le`) gives `(2π|ξ|)^j|φ̂_{u′}(ξ)| ≤ B_j(L, X)` for every `u′`.

Plain statements, with `X > 0`, `L = NM₂/q` and `c = L/(2X)`.
* `iteratedDeriv_ofReal`: for `g` smooth and real, the `n`-th derivative of `x ↦ (g x : ℂ)` is that of `g`, cast.
* `iteratedDeriv_kerS`, `abs_iteratedDeriv_kerS_le`, `integral_abs_iteratedDeriv_kerS`:
  `(K(· − u′))^{(m)}(x) = Lc^mψ̃₀^{(m)}(c(x − u′))`; for `L ≥ 0`, `|(K(· − u′))^{(m)}| ≤ Lc^mS₀(m)`; and for `L > 0`,
  `∫|(K(· − u′))^{(m)}| = 2Xc^mI₀(m)`.
* `integral_abs_iteratedDeriv_phi_le`: for `L > 0`, `∫|φ_{u′}^{(j)}| ≤ B_j(L, X)`.
* `fourier_phi_le`: for `L > 0`, `(2π|ξ|)^j|φ̂_{u′}(ξ)| ≤ B_j(L, X)`.

* `iteratedDeriv_ofReal`, `hasCompactSupport_iteratedDeriv`, `integrable_iteratedDeriv`: smooth functions.
* `S0`, `I0`, `Pw`, `abs_iteratedDeriv_psi0_le`: the constants.
* `kerS_eq`, `iteratedDeriv_kerS`, `abs_iteratedDeriv_kerS_le`, `integral_abs_iteratedDeriv_kerS`: the kernel.
* `phiR`, `contDiff_phiR`, `hasCompactSupport_phiR`, `Bj`, `abs_iteratedDeriv_phi_le`,
  `integral_abs_iteratedDeriv_phi_le`, `fourier_phi_le`: `φ_{u′}` and the bound.

The file imports `LinnikCGLFb.lean`.
-/

import LinnikCGLFb

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLPhi

open LinnikCGLRt LinnikCGLMom4 LinnikCGLFb

/-! ### Smooth functions -/

/-- For `g` smooth and real, `(x ↦ (g x : ℂ))^{(n)} = (g^{(n)} : ℂ)`. -/
lemma iteratedDeriv_ofReal {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => (g y : ℂ)) x = ((iteratedDeriv n g x : ℝ) : ℂ) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  have h := Complex.ofRealCLM.iteratedFDeriv_comp_left (x := x) (hg.contDiffAt (x := x)) (i := n)
    (WithTop.coe_le_coe.mpr le_top)
  have e : (fun y => (g y : ℂ)) = ⇑Complex.ofRealCLM ∘ g := rfl
  rw [e, h]
  rfl

/-- The derivatives of a function with compact support have compact support. -/
lemma hasCompactSupport_iteratedDeriv {g : ℝ → ℝ} (hc : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n g) := by
  have h := hc.iteratedFDeriv (𝕜 := ℝ) n
  have e : iteratedDeriv n g =
      (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℝ => M fun _ => 1) ∘ iteratedFDeriv ℝ n g := by
    funext x; simp [iteratedDeriv_eq_iteratedFDeriv]
  rw [e]
  exact h.comp_left (by simp)

lemma integrable_iteratedDeriv {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (n : ℕ) :
    Integrable (iteratedDeriv n g) :=
  (hg.continuous_iteratedDeriv n (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv hc n)

/-! ### The constants -/

lemma contDiff_psi0 : ContDiff ℝ ∞ psi0 := psiBump.contDiff

lemma hasCompactSupport_psi0 : HasCompactSupport psi0 := psiBump.hasCompactSupport

lemma hasCompactSupport_psiW : HasCompactSupport psiW := psiWide.hasCompactSupport

/-- `S₀(m) = sup|ψ̃₀^{(m)}|`. -/
def S0 (m : ℕ) : ℝ := ⨆ y, |iteratedDeriv m psi0 y|

/-- `I₀(m) = ∫|ψ̃₀^{(m)}|`. -/
def I0 (m : ℕ) : ℝ := ∫ y, |iteratedDeriv m psi0 y|

/-- `P(i) = ∫|ψ^{(i)}|`, for round 663's `ψ`. -/
def Pw (i : ℕ) : ℝ := ∫ x, |iteratedDeriv i psiW x|

lemma abs_iteratedDeriv_psi0_le (m : ℕ) (y : ℝ) : |iteratedDeriv m psi0 y| ≤ S0 m := by
  have hc : Continuous fun y => |iteratedDeriv m psi0 y| :=
    (contDiff_psi0.continuous_iteratedDeriv m (WithTop.coe_le_coe.mpr le_top)).abs
  have hs : HasCompactSupport fun y => |iteratedDeriv m psi0 y| :=
    (hasCompactSupport_iteratedDeriv hasCompactSupport_psi0 m).comp_left abs_zero
  exact le_ciSup (hc.bddAbove_range_of_hasCompactSupport hs) y

lemma S0_nonneg (m : ℕ) : 0 ≤ S0 m := (abs_nonneg _).trans (abs_iteratedDeriv_psi0_le m 0)

lemma I0_nonneg (m : ℕ) : 0 ≤ I0 m := integral_nonneg fun _ => abs_nonneg _

lemma Pw_nonneg (i : ℕ) : 0 ≤ Pw i := integral_nonneg fun _ => abs_nonneg _

/-! ### The kernel -/

section kernel

variable {L X : ℝ} (u' : ℝ)

lemma kerS_eq (x : ℝ) : kerL L X (x - u') = L * psi0 (L / (2 * X) * (x - u')) := by
  unfold kerL
  congr 2
  ring

/-- `(K(· − u′))^{(m)}(x) = Lc^mψ̃₀^{(m)}(c(x − u′))` with `c = L/(2X)`. -/
lemma iteratedDeriv_kerS (m : ℕ) (x : ℝ) :
    iteratedDeriv m (fun x => kerL L X (x - u')) x =
      L * (L / (2 * X)) ^ m * iteratedDeriv m psi0 (L / (2 * X) * (x - u')) := by
  set c := L / (2 * X) with hc
  have e : (fun x => kerL L X (x - u')) = fun x => L * psi0 (c * (x - u')) := by
    funext x; rw [kerS_eq]
  have hf : ContDiff ℝ ∞ fun x => psi0 (c * (x - u')) :=
    contDiff_psi0.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  rw [e, iteratedDeriv_const_mul (x := x) (f := fun x => psi0 (c * (x - u'))) L
    (hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
  have e2 : (fun x => psi0 (c * (x - u'))) = fun x => (fun y => psi0 (c * y)) (x - u') := rfl
  rw [e2, iteratedDeriv_comp_sub_const m (fun y => psi0 (c * y)) u',
    iteratedDeriv_comp_const_mul (contDiff_psi0.of_le (WithTop.coe_le_coe.mpr le_top)) c]
  simp only
  ring

lemma abs_iteratedDeriv_kerS_le (hL : 0 ≤ L) (hX : 0 < X) (m : ℕ) (x : ℝ) :
    |iteratedDeriv m (fun x => kerL L X (x - u')) x| ≤ L * (L / (2 * X)) ^ m * S0 m := by
  rw [iteratedDeriv_kerS, abs_mul, abs_of_nonneg (by positivity : 0 ≤ L * (L / (2 * X)) ^ m)]
  exact mul_le_mul_of_nonneg_left (abs_iteratedDeriv_psi0_le m _) (by positivity)

/-- `∫|(K(· − u′))^{(m)}| = 2Xc^mI₀(m)` for `L > 0`. -/
lemma integral_abs_iteratedDeriv_kerS (hL : 0 < L) (hX : 0 < X) (m : ℕ) :
    ∫ x, |iteratedDeriv m (fun x => kerL L X (x - u')) x| = 2 * X * (L / (2 * X)) ^ m * I0 m := by
  set c := L / (2 * X) with hc
  have hc0 : 0 < c := by positivity
  have e1 : ∀ x, |iteratedDeriv m (fun x => kerL L X (x - u')) x| =
      L * c ^ m * (fun y => |iteratedDeriv m psi0 (c * y)|) (x - u') := fun x => by
    rw [iteratedDeriv_kerS, abs_mul, abs_of_nonneg (by positivity : 0 ≤ L * c ^ m)]
  simp_rw [e1]
  rw [integral_const_mul, integral_sub_right_eq_self (fun y => |iteratedDeriv m psi0 (c * y)|) u',
    Measure.integral_comp_mul_left (fun y => |iteratedDeriv m psi0 y|) c, smul_eq_mul,
    abs_of_pos (inv_pos.2 hc0)]
  unfold I0
  have hL2 : L = 2 * X * c := by rw [hc]; field_simp
  rw [hL2]
  field_simp

end kernel

/-! ### `φ_{u′}` and its Fourier transform -/

/-- `φ_{u′}(x) = ψ(x)K(x − u′)`. -/
def phiR (L X u' : ℝ) (x : ℝ) : ℝ := psiW x * kerL L X (x - u')

lemma contDiff_phiR (L X u' : ℝ) : ContDiff ℝ ∞ (phiR L X u') :=
  contDiff_psiW.mul ((contDiff_kerL L X).comp (contDiff_id.sub contDiff_const))

lemma hasCompactSupport_phiR (L X u' : ℝ) : HasCompactSupport (phiR L X u') := by
  have : phiR L X u' = psiW * fun x => kerL L X (x - u') := rfl
  rw [this]
  exact hasCompactSupport_psiW.mul_right

/-- `B_j(L, X) = Σ_{i≤j}C(j, i)T_i`, with `T_0 = 2Xc^jI₀(j)` and `T_i = P(i)·Lc^{j−i}S₀(j−i)` for `i ≥ 1`. -/
def Bj (L X : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    (if i = 0 then 2 * X * (L / (2 * X)) ^ j * I0 j else Pw i * (L * (L / (2 * X)) ^ (j - i) * S0 (j - i)))

/-- Leibniz's rule: `|φ_{u′}^{(j)}| ≤ Σ_{i≤j}C(j, i)|ψ^{(i)}||(K(· − u′))^{(j−i)}|`. -/
lemma abs_iteratedDeriv_phi_le (L X u' : ℝ) (j : ℕ) (x : ℝ) :
    |iteratedDeriv j (phiR L X u') x| ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
      |iteratedDeriv i psiW x| * |iteratedDeriv (j - i) (fun x => kerL L X (x - u')) x| := by
  have hK : ContDiff ℝ ∞ fun x => kerL L X (x - u') :=
    (contDiff_kerL L X).comp (contDiff_id.sub (contDiff_const (c := u')))
  have h := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ∞) (f := psiW) (g := fun x => kerL L X (x - u'))
    contDiff_psiW hK x (n := j) (WithTop.coe_le_coe.mpr le_top)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
  have e : phiR L X u' = fun y => psiW y * kerL L X (y - u') := rfl
  rw [e]
  exact h

/-- `∫|φ_{u′}^{(j)}| ≤ B_j(L, X)` for `L, X > 0`. -/
lemma integral_abs_iteratedDeriv_phi_le {L X : ℝ} (hL : 0 < L) (hX : 0 < X) (u' : ℝ) (j : ℕ) :
    ∫ x, |iteratedDeriv j (phiR L X u') x| ≤ Bj L X j := by
  set K : ℝ → ℝ := fun x => kerL L X (x - u') with hK
  have hKs : ContDiff ℝ ∞ K := (contDiff_kerL L X).comp (contDiff_id.sub contDiff_const)
  -- each term is integrable
  have hterm : ∀ i ∈ Finset.range (j + 1), Integrable fun x =>
      (j.choose i : ℝ) * |iteratedDeriv i psiW x| * |iteratedDeriv (j - i) K x| := by
    intro i _
    have hc : Continuous fun x => (j.choose i : ℝ) * |iteratedDeriv i psiW x| * |iteratedDeriv (j - i) K x| :=
      (continuous_const.mul (contDiff_psiW.continuous_iteratedDeriv i (WithTop.coe_le_coe.mpr le_top)).abs).mul
        (hKs.continuous_iteratedDeriv (j - i) (WithTop.coe_le_coe.mpr le_top)).abs
    refine hc.integrable_of_hasCompactSupport ?_
    have hs : HasCompactSupport fun x => |iteratedDeriv i psiW x| :=
      (hasCompactSupport_iteratedDeriv hasCompactSupport_psiW i).comp_left abs_zero
    have : (fun x => (j.choose i : ℝ) * |iteratedDeriv i psiW x| * |iteratedDeriv (j - i) K x|) =
        (fun x => (j.choose i : ℝ)) * ((fun x => |iteratedDeriv i psiW x|) * fun x => |iteratedDeriv (j - i) K x|) := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [this]
    exact (hs.mul_right).mul_left
  have hphi_int : Integrable fun x => |iteratedDeriv j (phiR L X u') x| :=
    ((integrable_iteratedDeriv (contDiff_phiR L X u') (hasCompactSupport_phiR L X u') j).abs)
  calc ∫ x, |iteratedDeriv j (phiR L X u') x|
      ≤ ∫ x, ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * |iteratedDeriv i psiW x| *
          |iteratedDeriv (j - i) K x| :=
        integral_mono hphi_int (integrable_finsetSum _ hterm) fun x => abs_iteratedDeriv_phi_le L X u' j x
    _ = ∑ i ∈ Finset.range (j + 1), ∫ x, (j.choose i : ℝ) * |iteratedDeriv i psiW x| *
          |iteratedDeriv (j - i) K x| := integral_finsetSum _ hterm
    _ ≤ Bj L X j := by
        unfold Bj
        refine Finset.sum_le_sum fun i hi => ?_
        by_cases hi0 : i = 0
        · subst hi0
          rw [ite_eq_left rfl]
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero]
          have hK1 : Integrable fun x => |iteratedDeriv j K x| :=
            (integrable_iteratedDeriv hKs ((hasCompactSupport_kerL hL hX).comp_homeomorph
              (Homeomorph.subRight u')) j).abs
          calc ∫ x, |psiW x| * |iteratedDeriv j K x| ≤ ∫ x, |iteratedDeriv j K x| := by
                refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hK1
                  (Eventually.of_forall fun x => ?_)
                show |psiW x| * |iteratedDeriv j K x| ≤ |iteratedDeriv j K x|
                rw [abs_of_nonneg (psiW_nonneg x)]
                exact mul_le_of_le_one_left (abs_nonneg _) (psiW_le_one x)
            _ = 2 * X * (L / (2 * X)) ^ j * I0 j := integral_abs_iteratedDeriv_kerS u' hL hX j
        · rw [ite_eq_right hi0]
          have hC0 : (0 : ℝ) ≤ j.choose i := Nat.cast_nonneg _
          set M := L * (L / (2 * X)) ^ (j - i) * S0 (j - i) with hM
          have hpw : Integrable fun x => |iteratedDeriv i psiW x| :=
            (integrable_iteratedDeriv contDiff_psiW hasCompactSupport_psiW i).abs
          calc ∫ x, (j.choose i : ℝ) * |iteratedDeriv i psiW x| * |iteratedDeriv (j - i) K x|
              ≤ ∫ x, ((j.choose i : ℝ) * M) * |iteratedDeriv i psiW x| := by
                refine integral_mono (hterm i hi) (hpw.const_mul _) fun x => ?_
                have hk := abs_iteratedDeriv_kerS_le (L := L) (X := X) u' hL.le hX (j - i) x
                have h0 : 0 ≤ (j.choose i : ℝ) * |iteratedDeriv i psiW x| := by positivity
                calc (j.choose i : ℝ) * |iteratedDeriv i psiW x| * |iteratedDeriv (j - i) K x|
                    ≤ (j.choose i : ℝ) * |iteratedDeriv i psiW x| * M := mul_le_mul_of_nonneg_left hk h0
                  _ = ((j.choose i : ℝ) * M) * |iteratedDeriv i psiW x| := by ring
            _ = (j.choose i : ℝ) * (Pw i * M) := by
                rw [integral_const_mul]
                unfold Pw
                ring

/-- **The Fourier decay of `φ_{u′}`**: `(2π|ξ|)^j|φ̂_{u′}(ξ)| ≤ B_j(L, X)` for `L, X > 0`, by round 588's
integration by parts. -/
theorem fourier_phi_le {L X : ℝ} (hL : 0 < L) (hX : 0 < X) (u' : ℝ) (j : ℕ) (ξ : ℝ) :
    (2 * π * |ξ|) ^ j * ‖𝓕 (fun x => (phiR L X u' x : ℂ)) ξ‖ ≤ Bj L X j := by
  have hC : ContDiff ℝ ∞ (fun x => (phiR L X u' x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_phiR L X u')
  have hint : ∀ n : ℕ, n ≤ j → Integrable (iteratedDeriv n fun x => (phiR L X u' x : ℂ)) := fun n _ => by
    have e : iteratedDeriv n (fun x => (phiR L X u' x : ℂ)) =
        fun x => ((iteratedDeriv n (phiR L X u') x : ℝ) : ℂ) :=
      funext fun x => iteratedDeriv_ofReal (contDiff_phiR L X u') n x
    rw [e]
    exact (integrable_iteratedDeriv (contDiff_phiR L X u') (hasCompactSupport_phiR L X u') n).ofReal
  have h := SieveSmooth.pow_mul_norm_fourier_le (hC.of_le (WithTop.coe_le_coe.mpr le_top)) hint ξ
  have e2 : ∫ x, ‖iteratedDeriv j (fun x => (phiR L X u' x : ℂ)) x‖ =
      ∫ x, |iteratedDeriv j (phiR L X u') x| := by
    congr 1
    funext x
    rw [iteratedDeriv_ofReal (contDiff_phiR L X u') j x, Complex.norm_real, Real.norm_eq_abs]
  rw [e2] at h
  exact h.trans (integral_abs_iteratedDeriv_phi_le hL hX u' j)

end LinnikCGLPhi

#print axioms LinnikCGLPhi.integral_abs_iteratedDeriv_kerS
#print axioms LinnikCGLPhi.integral_abs_iteratedDeriv_phi_le
#print axioms LinnikCGLPhi.fourier_phi_le
