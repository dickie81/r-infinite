/-
# Round 652: their `I′_{m⃗}` as an integral over `(v₁, v₂)` (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li define "R(v,a) := Σ_{(t,χ)∈W} v^{it}χ(a), v > 0, a ∈ Z/qZ" (their (7.2)). After their change of
variables (round 651) they continue: "Since the R factors do not depend on u₃, a₃, performing the u₃ integral and the
a₃ summation first yields" their (7.3) (text layer lines 2036–2039 and 2193–2194; spaces restored, the sum, exponents
and subscripts transcribed). In (7.3) (lines 2195–2226), `I′_{m⃗}` is `N³/q³` times a sum over `b₁, b₂` modulo `q`
with `(b₁b₂, q) = 1` of an integral over `ℝ²` of `C_q(b₁m₁ + b₂m₂ + m₃)R(v₁, b₁)R(v₂/v₁, b₂b₁⁻¹)R(1/v₂, b₂⁻¹)`
against the inner integral over `u₃`. Their `C_q` is "the Ramanujan sum" (line 2016). This file proves their (7.3)
at one point per character, from round 651's `hhat_prod`, with the finite sums inside the integral.

Plain statement (`Ip_eq`). For `q ≥ 1`, real `N`, points `t_i` and characters `χ_i` modulo `q` (`i ∈ R`) and integers
`m₁, m₂, m₃`: `I′(m₁, m₂, m₃) = (N/q)³∫∫Ψ(v₁, v₂) dv₂ dv₁`, where
`Ψ(v₁, v₂) = J(v₁, v₂, λ)Σ_{b₁,b₂∈(ℤ/qℤ)ˣ}C_q(b₁m₁ + b₂m₂ + m₃)R(v₁, b₁)R(v₂/v₁, b₂b₁⁻¹)R(1/v₂, b₂⁻¹)`,
`λ = (N/q)(m₁v₁ + m₂v₂ + m₃)`, `R(v, a) = Σ_{i∈R}v^{it_i}χ_i(a)`, `C_q(n) = Σ_{a∈(ℤ/qℤ)ˣ}e(an/q)`, and `J` is round
651's kernel, the inner integral of their (7.3).

The proof. Round 650's `φ_{ik}(m)` is `(N/q)ĥ_{t_i−t_k}(Nm/q)S_{ik}(m)`, with the residue sum
`S_{ik}(m) = Σ_{a∈(ℤ/qℤ)ˣ}χ_i(a)conj(χ_k(a))e(ma/q)`; the non-units drop out, since `χ_i` vanishes there (`phi_eq`).
For a triple `(i, j, k)`, round 651's `hhat_prod` writes the product of the three `ĥ`s as an integral over `(v₁, v₂)`
of `v₁^{i(t_i−t_j)}v₂^{i(t_j−t_k)}J(v₁, v₂, λ)`. By round 651's Fubini lemmas that integrand is integrable in `v₂`,
and its integral over `v₂` is integrable in `v₁`, so the finite sums pass inside. The substitution `a₁ = b₁a₃`,
`a₂ = b₂a₃` gives
`S_{ij}(m₁)S_{jk}(m₂)S_{ki}(m₃) = Σ_{b₁,b₂}χ_i(b₁)χ_j(b₂b₁⁻¹)χ_k(b₂⁻¹)C_q(b₁m₁ + b₂m₂ + m₃)` (`S2_triple`),
since `conj(χ(a)) = χ(a⁻¹)` at a unit. For `v₁, v₂ > 0`,
`v₁^{i(t_i−t_j)}v₂^{i(t_j−t_k)} = v₁^{it_i}(v₂/v₁)^{it_j}(1/v₂)^{it_k}` (`phases`), and the sum over the triples
factors into the three `R`s (`sum_Qk`); otherwise `J = 0` (`Jk_eq_zero`).

* `Rf`, `Cq`, `fS`, `S2`, `sum_eq_sum_units`, `phi_eq`: their `R`, the Ramanujan sum, and `φ_{ik}(m)` with its
  residue sum over the units (Mathlib's `ZMod.stdAddChar_coe`).
* `prod3_sum`, `sum_rot3`, `unit_mul_inv`, `star_unit`, `triple_term`, `S2_triple`: the substitution (Mathlib's
  `MulChar.star_apply'`, and `Fintype.sum_equiv` with `Equiv.mulRight`).
* `cpow_eq_exp`, `phases`: the phases.
* `gv_eq_zero`, `Jk_eq_zero`, `integral_Phi`, `integrable_v₂`, `integrable_v₁`: the kernel off `(0, ∞)²`, and
  integrability.
* `sum_integral_integral`, `sum3_eq`, `sum3_eq'`, `sum_comm4`, `sum_comm5`: finite sums.
* `Qk`, `Psi`, `sum_Qk`, `Ip_eq`: the formula.

The file imports `LinnikCGLProd.lean`.
-/

import LinnikCGLProd

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff

noncomputable section

namespace LinnikCGLRFact

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLTrunc LinnikCGLProd

/-! ### Their `R(v, a)`, the Ramanujan sum and the residue sums -/

/-- **Their (7.2)** at one point per character: `R(v, a) = Σ_{i∈R}v^{it_i}χ_i(a)`. -/
def Rf {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (v : ℝ) (a : ZMod q) : ℂ :=
  ∑ i ∈ R, (v : ℂ) ^ ((t i : ℂ) * I) * χ i a

/-- The Ramanujan sum `C_q(n) = Σ_{a∈(ℤ/qℤ)ˣ}e(an/q)`. -/
def Cq (q : ℕ) [NeZero q] (n : ZMod q) : ℂ := ∑ a : (ZMod q)ˣ, ZMod.stdAddChar ((a : ZMod q) * n)

/-- A term of the residue sum: `χ_i(a)conj(χ_k(a))e(ma/q)` at a unit `a`. -/
def fS {ι : Type*} {q : ℕ} [NeZero q] (χ : ι → DirichletCharacter ℂ q) (i k : ι) (m : ℤ) (a : (ZMod q)ˣ) : ℂ :=
  χ i a * star (χ k a) * ZMod.stdAddChar ((m : ZMod q) * (a : ZMod q))

/-- The residue sum of `φ_{ik}(m)`: `S_{ik}(m) = Σ_{a∈(ℤ/qℤ)ˣ}χ_i(a)conj(χ_k(a))e(ma/q)`. -/
def S2 {ι : Type*} {q : ℕ} [NeZero q] (χ : ι → DirichletCharacter ℂ q) (i k : ι) (m : ℤ) : ℂ :=
  ∑ a : (ZMod q)ˣ, fS χ i k m a

lemma sum_eq_sum_units {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (hf : ∀ x, ¬ IsUnit x → f x = 0) :
    ∑ x : ZMod q, f x = ∑ u : (ZMod q)ˣ, f u := by
  classical
  symm
  calc ∑ u : (ZMod q)ˣ, f u = ∑ x ∈ Finset.univ.map ⟨((↑) : (ZMod q)ˣ → ZMod q), fun _ _ h => Units.ext h⟩, f x := by
        rw [Finset.sum_map]; rfl
    _ = ∑ x : ZMod q, f x := by
        refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => hf x fun hu => hx ?_
        obtain ⟨u, rfl⟩ := hu
        exact Finset.mem_map_of_mem _ (Finset.mem_univ u)

/-- **`φ_{ik}(m)` with its residue sum over the units**: `φ_{ik}(m) = (N/q)ĥ_{t_i−t_k}(Nm/q)S_{ik}(m)`. -/
lemma phi_eq {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i k : ι)
    (m : ℤ) : phi N χ t i k m = ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) (N * m / q) * S2 χ i k m := by
  unfold phi S2
  have e1 : ∀ a ∈ Finset.range q, (χ i a * star (χ k a)) *
      (((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) (N * m / q) * Complex.exp (2 * π * I * m * (a / q))) =
      ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) (N * m / q) *
        (χ i (a : ZMod q) * star (χ k (a : ZMod q)) * ZMod.stdAddChar ((m : ZMod q) * (a : ZMod q))) := by
    intro a _
    have h := ZMod.stdAddChar_coe (N := q) (m * (a : ℤ))
    push_cast at h
    rw [h]
    have e : 2 * π * I * m * (a / q) = 2 * π * I * (m * a) / q := by ring
    rw [e]; ring
  rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
  congr 1
  refine Eq.trans ?_ (sum_eq_sum_units (fun x => χ i x * star (χ k x) * ZMod.stdAddChar ((m : ZMod q) * x)) ?_)
  · exact Finset.sum_nbij' (fun a => (a : ZMod q)) ZMod.val (fun _ _ => Finset.mem_univ _)
      (fun x _ => Finset.mem_range.2 (ZMod.val_lt x)) (fun a ha => ZMod.val_cast_of_lt (Finset.mem_range.1 ha))
      (fun x _ => ZMod.natCast_zmod_val x) (fun _ _ => rfl)
  · intro x hx
    show χ i x * star (χ k x) * _ = 0
    rw [MulChar.map_nonunit (χ i) hx, zero_mul, zero_mul]

/-! ### The substitution `a₁ = b₁a₃`, `a₂ = b₂a₃` -/

lemma prod3_sum {α : Type*} (A : Finset α) (a b c : α → ℂ) :
    (∑ i ∈ A, a i) * (∑ j ∈ A, b j) * (∑ k ∈ A, c k) = ∑ i ∈ A, ∑ j ∈ A, ∑ k ∈ A, a i * b j * c k := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

lemma sum_rot3 {α β γ : Type*} (A : Finset α) (B : Finset β) (C : Finset γ) (f : α → β → γ → ℂ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c :=
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, f a b c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c := Finset.sum_comm

lemma unit_mul_inv {q : ℕ} (ψ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    ψ (u : ZMod q) * ψ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
  rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]

lemma star_unit {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    star (ψ (u : ZMod q)) = ψ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]

/-- **One term after the substitution**: `f_{ij}(b₁a)f_{jk}(b₂a)f_{ki}(a) =
χ_i(b₁)χ_j(b₂b₁⁻¹)χ_k(b₂⁻¹)e(a(b₁m₁ + b₂m₂ + m₃)/q)` for units `a, b₁, b₂`. -/
lemma triple_term {ι : Type*} {q : ℕ} [NeZero q] (χ : ι → DirichletCharacter ℂ q) (i j k : ι) (m₁ m₂ m₃ : ℤ)
    (b₁ b₂ x : (ZMod q)ˣ) :
    fS χ i j m₁ (b₁ * x) * fS χ j k m₂ (b₂ * x) * fS χ k i m₃ x =
      χ i (b₁ : ZMod q) * χ j ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q) * χ k ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q) *
        ZMod.stdAddChar ((x : ZMod q) *
          ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q))) := by
  have hP : ZMod.stdAddChar ((m₁ : ZMod q) * ((b₁ : ZMod q) * (x : ZMod q))) *
      ZMod.stdAddChar ((m₂ : ZMod q) * ((b₂ : ZMod q) * (x : ZMod q))) *
        ZMod.stdAddChar ((m₃ : ZMod q) * (x : ZMod q)) =
      ZMod.stdAddChar ((x : ZMod q) *
        ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q))) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1; ring
  have hi := unit_mul_inv (χ i) x
  have hj := unit_mul_inv (χ j) x
  have hk := unit_mul_inv (χ k) x
  unfold fS
  rw [star_unit, star_unit, star_unit, mul_inv, mul_inv]
  simp only [Units.val_mul, map_mul]
  set P1 := ZMod.stdAddChar ((m₁ : ZMod q) * ((b₁ : ZMod q) * (x : ZMod q)))
  set P2 := ZMod.stdAddChar ((m₂ : ZMod q) * ((b₂ : ZMod q) * (x : ZMod q)))
  set P3 := ZMod.stdAddChar ((m₃ : ZMod q) * (x : ZMod q))
  set Bj := χ j (x : ZMod q)
  set Bj' := χ j ((x⁻¹ : (ZMod q)ˣ) : ZMod q)
  set Bk := χ k (x : ZMod q)
  set Bk' := χ k ((x⁻¹ : (ZMod q)ˣ) : ZMod q)
  linear_combination (χ i (b₁ : ZMod q) * χ j ((b₁⁻¹ : (ZMod q)ˣ) : ZMod q) * χ j (b₂ : ZMod q) *
      χ k ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q)) *
    (Bj * Bj' * (Bk * Bk') * (P1 * P2 * P3) * hi + Bk * Bk' * (P1 * P2 * P3) * hj + P1 * P2 * P3 * hk + hP)

/-- **The residue sums of a triple**: `S_{ij}(m₁)S_{jk}(m₂)S_{ki}(m₃) =
Σ_{b₁,b₂}χ_i(b₁)χ_j(b₂b₁⁻¹)χ_k(b₂⁻¹)C_q(b₁m₁ + b₂m₂ + m₃)`. -/
lemma S2_triple {ι : Type*} {q : ℕ} [NeZero q] (χ : ι → DirichletCharacter ℂ q) (i j k : ι) (m₁ m₂ m₃ : ℤ) :
    S2 χ i j m₁ * S2 χ j k m₂ * S2 χ k i m₃ =
      ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ, χ i (b₁ : ZMod q) * χ j ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q) *
        χ k ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q) *
          Cq q ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)) := by
  unfold S2
  rw [prod3_sum, sum_rot3]
  unfold Cq
  simp only [Finset.mul_sum]
  conv_rhs => rw [sum_rot3]
  refine Finset.sum_congr rfl fun x _ => ?_
  calc ∑ x₁ : (ZMod q)ˣ, ∑ x₂ : (ZMod q)ˣ, fS χ i j m₁ x₁ * fS χ j k m₂ x₂ * fS χ k i m₃ x
      = ∑ b₁ : (ZMod q)ˣ, ∑ x₂ : (ZMod q)ˣ, fS χ i j m₁ (b₁ * x) * fS χ j k m₂ x₂ * fS χ k i m₃ x :=
        (Fintype.sum_equiv (Equiv.mulRight x) _ _ fun _ => rfl).symm
    _ = ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ, fS χ i j m₁ (b₁ * x) * fS χ j k m₂ (b₂ * x) * fS χ k i m₃ x :=
        Finset.sum_congr rfl fun _ _ => (Fintype.sum_equiv (Equiv.mulRight x) _ _ fun _ => rfl).symm
    _ = _ := Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ =>
        triple_term χ i j k m₁ m₂ m₃ b₁ b₂ x

/-! ### The phases -/

lemma cpow_eq_exp {v : ℝ} (hv : 0 < v) (τ : ℝ) :
    (v : ℂ) ^ ((τ : ℂ) * I) = Complex.exp (((Real.log v * τ : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hv.ne'), ← Complex.ofReal_log hv.le]
  congr 1; push_cast; ring

/-- **The phases**: `v₁^{i(a−b)}v₂^{i(b−c)} = v₁^{ia}(v₂/v₁)^{ib}(1/v₂)^{ic}` for `v₁, v₂ > 0`. -/
lemma phases {v₁ v₂ : ℝ} (h1 : 0 < v₁) (h2 : 0 < v₂) (a b c : ℝ) :
    (v₁ : ℂ) ^ (((a - b : ℝ) : ℂ) * I) * (v₂ : ℂ) ^ (((b - c : ℝ) : ℂ) * I) =
      (v₁ : ℂ) ^ ((a : ℂ) * I) * ((v₂ / v₁ : ℝ) : ℂ) ^ ((b : ℂ) * I) * ((1 / v₂ : ℝ) : ℂ) ^ ((c : ℂ) * I) := by
  rw [cpow_eq_exp h1, cpow_eq_exp h2, cpow_eq_exp h1, cpow_eq_exp (div_pos h2 h1), cpow_eq_exp (one_div_pos.2 h2),
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, Real.log_div h2.ne' h1.ne', one_div, Real.log_inv]
  congr 1; push_cast; ring

/-! ### The kernel off `(0, ∞)²`, and integrability -/

lemma gv_eq_zero {v₁ v₂ : ℝ} (h : ¬ (0 < v₁ ∧ 0 < v₂)) (u : ℝ) : gv v₁ v₂ u = 0 := by
  unfold gv
  by_cases hu : wCGL u = 0
  · rw [hu]; ring
  obtain ⟨hu1, -⟩ := one_lt_of_wCGL_ne hu
  rcases not_and_or.1 h with h1 | h1
  · rw [wCGL_zero (Or.inl (by nlinarith [not_lt.1 h1]) : v₁ * u ≤ 1 ∨ 2 ≤ v₁ * u)]; ring
  · rw [wCGL_zero (Or.inl (by nlinarith [not_lt.1 h1]) : v₂ * u ≤ 1 ∨ 2 ≤ v₂ * u)]; ring

lemma Jk_eq_zero {v₁ v₂ : ℝ} (h : ¬ (0 < v₁ ∧ 0 < v₂)) (lam : ℝ) : Jk v₁ v₂ lam = 0 := by
  unfold Jk
  simp [gv_eq_zero h]

lemma integral_Phi {τ₁ τ₂ τ₃ : ℝ} (hτ : τ₁ + τ₂ + τ₃ = 0) (ξ₁ ξ₂ ξ₃ v₁ v₂ : ℝ) :
    ∫ u₃ : ℝ, Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ =
      (v₁ : ℂ) ^ ((τ₁ : ℂ) * I) * (v₂ : ℂ) ^ ((τ₂ : ℂ) * I) * Jk v₁ v₂ (v₁ * ξ₁ + v₂ * ξ₂ + ξ₃) := by
  simp only [Phi_eq hτ]
  rw [integral_const_mul]
  rfl

lemma integrable_v₂ {τ₁ τ₂ τ₃ : ℝ} (hτ : τ₁ + τ₂ + τ₃ = 0) (ξ₁ ξ₂ ξ₃ v₁ : ℝ) :
    Integrable fun v₂ : ℝ => (v₁ : ℂ) ^ ((τ₁ : ℂ) * I) * (v₂ : ℂ) ^ ((τ₂ : ℂ) * I) *
      Jk v₁ v₂ (v₁ * ξ₁ + v₂ * ξ₂ + ξ₃) :=
  (integrable_Phi2 τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ v₁).integral_prod_right.congr
    (Filter.Eventually.of_forall fun v₂ => integral_Phi hτ ξ₁ ξ₂ ξ₃ v₁ v₂)

lemma integrable_v₁ {τ₁ τ₂ τ₃ : ℝ} (hτ : τ₁ + τ₂ + τ₃ = 0) (ξ₁ ξ₂ ξ₃ : ℝ) :
    Integrable fun v₁ : ℝ => ∫ v₂ : ℝ, (v₁ : ℂ) ^ ((τ₁ : ℂ) * I) * (v₂ : ℂ) ^ ((τ₂ : ℂ) * I) *
      Jk v₁ v₂ (v₁ * ξ₁ + v₂ * ξ₂ + ξ₃) := by
  refine (integrable_Phi3 τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃).integral_prod_left.integral_prod_right.congr
    (Filter.Eventually.of_forall fun v₁ => ?_)
  show ∫ u₃ : ℝ, ∫ v₂ : ℝ, Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ = _
  have e : ∫ u₃ : ℝ, ∫ v₂ : ℝ, Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ =
      ∫ v₂ : ℝ, ∫ u₃ : ℝ, Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ :=
    integral_integral_swap (integrable_Phi2 τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ v₁)
  rw [e]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v₂ => integral_Phi hτ ξ₁ ξ₂ ξ₃ v₁ v₂)

/-! ### Finite sums through the double integral -/

lemma sum_integral_integral {α : Type*} (S : Finset α) (P : α → ℝ → ℝ → ℂ)
    (h2 : ∀ s ∈ S, ∀ v₁, Integrable (P s v₁)) (h1 : ∀ s ∈ S, Integrable fun v₁ => ∫ v₂, P s v₁ v₂) :
    ∑ s ∈ S, ∫ v₁, ∫ v₂, P s v₁ v₂ = ∫ v₁, ∫ v₂, ∑ s ∈ S, P s v₁ v₂ := by
  rw [← integral_finsetSum S h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v₁ => ?_)
  exact (integral_finsetSum S fun s hs => h2 s hs v₁).symm

lemma sum3_eq {ι : Type*} (R : Finset ι) (F : ι → ι → ι → ℂ) :
    ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, F i j k = ∑ p ∈ R ×ˢ (R ×ˢ R), F p.1 p.2.1 p.2.2 := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_product]

lemma sum3_eq' {ι : Type*} (R : Finset ι) (G : ι × ι × ι → ℂ) :
    ∑ p ∈ R ×ˢ (R ×ˢ R), G p = ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, G (i, (j, k)) := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_product]

lemma sum_comm4 {α β : Type*} (A : Finset α) (B : Finset β) (G : α → α → α → β → ℂ) :
    ∑ i ∈ A, ∑ j ∈ A, ∑ k ∈ A, ∑ b ∈ B, G i j k b = ∑ b ∈ B, ∑ i ∈ A, ∑ j ∈ A, ∑ k ∈ A, G i j k b :=
  calc ∑ i ∈ A, ∑ j ∈ A, ∑ k ∈ A, ∑ b ∈ B, G i j k b = ∑ i ∈ A, ∑ j ∈ A, ∑ b ∈ B, ∑ k ∈ A, G i j k b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i ∈ A, ∑ b ∈ B, ∑ j ∈ A, ∑ k ∈ A, G i j k b := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b ∈ B, ∑ i ∈ A, ∑ j ∈ A, ∑ k ∈ A, G i j k b := Finset.sum_comm

lemma sum_comm5 {α β : Type*} (A : Finset α) (B : Finset β) (F : α → α → α → β → β → ℂ) :
    ∑ i ∈ A, ∑ j ∈ A, ∑ k ∈ A, ∑ b₁ ∈ B, ∑ b₂ ∈ B, F i j k b₁ b₂ =
      ∑ b₁ ∈ B, ∑ b₂ ∈ B, ∑ i ∈ A, ∑ j ∈ A, ∑ k ∈ A, F i j k b₁ b₂ := by
  rw [sum_comm4 A B fun i j k b₁ => ∑ b₂ ∈ B, F i j k b₁ b₂]
  exact Finset.sum_congr rfl fun b₁ _ => sum_comm4 A B fun i j k b₂ => F i j k b₁ b₂

/-! ### Their `I′_{m⃗}` as an integral over `(v₁, v₂)` -/

/-- The integrand of one triple of points: `v₁^{i(t_i−t_j)}v₂^{i(t_j−t_k)}J(v₁, v₂, λ)` with
`λ = v₁Nm₁/q + v₂Nm₂/q + Nm₃/q`. -/
def Qk {ι : Type*} (q : ℕ) (N : ℝ) (t : ι → ℝ) (m₁ m₂ m₃ : ℤ) (i j k : ι) (v₁ v₂ : ℝ) : ℂ :=
  (v₁ : ℂ) ^ (((t i - t j : ℝ) : ℂ) * I) * (v₂ : ℂ) ^ (((t j - t k : ℝ) : ℂ) * I) *
    Jk v₁ v₂ (v₁ * (N * m₁ / q) + v₂ * (N * m₂ / q) + N * m₃ / q)

/-- **The integrand of their (7.3)** after the sums over the points and over `a₃`:
`J(v₁, v₂, λ)Σ_{b₁,b₂}C_q(b₁m₁ + b₂m₂ + m₃)R(v₁, b₁)R(v₂/v₁, b₂b₁⁻¹)R(1/v₂, b₂⁻¹)`. -/
def Psi {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (m₁ m₂ m₃ : ℤ) (v₁ v₂ : ℝ) : ℂ :=
  Jk v₁ v₂ (v₁ * (N * m₁ / q) + v₂ * (N * m₂ / q) + N * m₃ / q) *
    ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ,
      Cq q ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)) *
      (Rf R χ t v₁ b₁ * Rf R χ t (v₂ / v₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q) *
        Rf R χ t (1 / v₂) ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q))

/-- **The sum over the triples of points, at one `(v₁, v₂)`**: the characters and the phases factor. -/
lemma sum_Qk {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (m₁ m₂ m₃ : ℤ) (v₁ v₂ : ℝ) :
    ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ((N / q : ℝ) : ℂ) ^ 3 * (S2 χ i j m₁ * S2 χ j k m₂ * S2 χ k i m₃) *
        Qk q N t m₁ m₂ m₃ i j k v₁ v₂ = ((N / q : ℝ) : ℂ) ^ 3 * Psi N R χ t m₁ m₂ m₃ v₁ v₂ := by
  by_cases h : 0 < v₁ ∧ 0 < v₂
  swap
  · simp [Qk, Psi, Jk_eq_zero h]
  calc ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ((N / q : ℝ) : ℂ) ^ 3 * (S2 χ i j m₁ * S2 χ j k m₂ * S2 χ k i m₃) *
        Qk q N t m₁ m₂ m₃ i j k v₁ v₂
      = ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ, ((N / q : ℝ) : ℂ) ^ 3 *
          Jk v₁ v₂ (v₁ * (N * m₁ / q) + v₂ * (N * m₂ / q) + N * m₃ / q) *
          Cq q ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)) *
          ((v₁ : ℂ) ^ ((t i : ℂ) * I) * χ i (b₁ : ZMod q) *
            (((v₂ / v₁ : ℝ) : ℂ) ^ ((t j : ℂ) * I) * χ j ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q)) *
            (((1 / v₂ : ℝ) : ℂ) ^ ((t k : ℂ) * I) * χ k ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [S2_triple, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b₁ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b₂ _ => ?_
        unfold Qk
        linear_combination (((N / q : ℝ) : ℂ) ^ 3 * χ i (b₁ : ZMod q) *
          χ j ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q) * χ k ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q) *
          Cq q ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)) *
          Jk v₁ v₂ (v₁ * (N * m₁ / q) + v₂ * (N * m₂ / q) + N * m₃ / q)) * phases h.1 h.2 (t i) (t j) (t k)
    _ = ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ, ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ((N / q : ℝ) : ℂ) ^ 3 *
          Jk v₁ v₂ (v₁ * (N * m₁ / q) + v₂ * (N * m₂ / q) + N * m₃ / q) *
          Cq q ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)) *
          ((v₁ : ℂ) ^ ((t i : ℂ) * I) * χ i (b₁ : ZMod q) *
            (((v₂ / v₁ : ℝ) : ℂ) ^ ((t j : ℂ) * I) * χ j ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q)) *
            (((1 / v₂ : ℝ) : ℂ) ^ ((t k : ℂ) * I) * χ k ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q))) :=
        sum_comm5 _ _ _
    _ = ((N / q : ℝ) : ℂ) ^ 3 * Psi N R χ t m₁ m₂ m₃ v₁ v₂ := by
        unfold Psi
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b₁ _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b₂ _ => ?_
        unfold Rf
        rw [prod3_sum]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        ring

/-- **Their `I′_{m⃗}` as an integral over `(v₁, v₂)`** (the change of variables and the substitution of their
proof of Proposition 7.1): `I′(m₁, m₂, m₃) = (N/q)³∫∫Ψ(v₁, v₂) dv₂ dv₁` with
`Ψ = J(v₁, v₂, λ)Σ_{b₁,b₂}C_q(b₁m₁ + b₂m₂ + m₃)R(v₁, b₁)R(v₂/v₁, b₂b₁⁻¹)R(1/v₂, b₂⁻¹)`. -/
theorem Ip_eq {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) (m₁ m₂ m₃ : ℤ) :
    Ip N R χ t m₁ m₂ m₃ = ((N / q : ℝ) : ℂ) ^ 3 * ∫ v₁ : ℝ, ∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂ := by
  have hτ : ∀ i j k : ι, (t i - t j) + (t j - t k) + (t k - t i) = 0 := fun i j k => by ring
  have hA : ∀ i j k : ι, phi N χ t i j m₁ * phi N χ t j k m₂ * phi N χ t k i m₃ =
      ∫ v₁ : ℝ, ∫ v₂ : ℝ, ((N / q : ℝ) : ℂ) ^ 3 * (S2 χ i j m₁ * S2 χ j k m₂ * S2 χ k i m₃) *
        Qk q N t m₁ m₂ m₃ i j k v₁ v₂ := by
    intro i j k
    have hh := hhat_prod (hτ i j k) (N * m₁ / q) (N * m₂ / q) (N * m₃ / q)
    simp only [integral_const_mul]
    rw [phi_eq, phi_eq, phi_eq]
    unfold Qk
    rw [← hh]
    ring
  have h2 : ∀ p ∈ R ×ˢ (R ×ˢ R), ∀ v₁ : ℝ, Integrable fun v₂ : ℝ =>
      ((N / q : ℝ) : ℂ) ^ 3 * (S2 χ p.1 p.2.1 m₁ * S2 χ p.2.1 p.2.2 m₂ * S2 χ p.2.2 p.1 m₃) *
        Qk q N t m₁ m₂ m₃ p.1 p.2.1 p.2.2 v₁ v₂ :=
    fun p _ v₁ => (integrable_v₂ (hτ p.1 p.2.1 p.2.2) _ _ _ v₁).const_mul _
  have h1 : ∀ p ∈ R ×ˢ (R ×ˢ R), Integrable fun v₁ : ℝ => ∫ v₂ : ℝ,
      ((N / q : ℝ) : ℂ) ^ 3 * (S2 χ p.1 p.2.1 m₁ * S2 χ p.2.1 p.2.2 m₂ * S2 χ p.2.2 p.1 m₃) *
        Qk q N t m₁ m₂ m₃ p.1 p.2.1 p.2.2 v₁ v₂ :=
    fun p _ => ((integrable_v₁ (hτ p.1 p.2.1 p.2.2) _ _ _).const_mul _).congr
      (Filter.Eventually.of_forall fun v₁ => (integral_const_mul _ _).symm)
  unfold Ip
  simp only [hA]
  rw [sum3_eq, sum_integral_integral _ _ h2 h1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v₁ => ?_)
  dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v₂ => ?_)
  dsimp only
  rw [sum3_eq']
  exact sum_Qk N R χ t m₁ m₂ m₃ v₁ v₂

end LinnikCGLRFact

#print axioms LinnikCGLRFact.phi_eq
#print axioms LinnikCGLRFact.S2_triple
#print axioms LinnikCGLRFact.sum_Qk
#print axioms LinnikCGLRFact.Ip_eq
