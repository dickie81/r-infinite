/-
# Vinogradov's mean value theorem, step I.3b: Hölder over residue classes (round 199)

Plain statement (`Gfull_le`). Let `G` count the quadruples `(u, w, u', w')` with:
* `u, u' ∈ [1,P]^k` having distinct residues mod `p`;
* `w, w' ∈ [1,P]^s` arbitrary;
* `pv u + pv w = pv u' + pv w'`.

Then `G ≤ p^{2s−1} Σ_{a<p} G_a`, where `G_a` restricts `w, w'` to the residue class `a`
(round 198). The proof has three parts.
* Orthogonality for any finite set (`count_eq_integral`).
* The generating function factorises as `F·f^s`, with `f = Σ_a f_a`.
* The power mean inequality, pointwise: `|Σ_a f_a|^{2s} ≤ p^{2s−1} Σ_a |f_a|^{2s}`.
-/
import VinoIter

open Finset MeasureTheory Complex

namespace VinoHolder

open Vinogradov VinoIter

/-- The generating function of a finite set `X` of points `φ x ∈ ℤᵏ`. -/
noncomputable def E {β : Type*} {k : ℕ} (X : Finset β) (φ : β → Fin k → ℤ) (α : Fin k → ℝ) : ℂ :=
  ∑ x ∈ X, ee (∑ j, (φ x j : ℝ) * α j)

lemma continuous_E {β : Type*} {k : ℕ} (X : Finset β) (φ : β → Fin k → ℤ) :
    Continuous (E X φ) := by
  unfold E
  refine continuous_finsetSum _ fun x _ => continuous_ee.comp ?_
  fun_prop

/-- **Orthogonality for any finite set.** `∫ |E_X|² = #{(x, y) ∈ X² : φ x = φ y}`. -/
theorem count_eq_integral {β : Type*} {k : ℕ} (X : Finset β) (φ : β → Fin k → ℤ) :
    ((((X ×ˢ X).filter fun q => φ q.1 = φ q.2).card : ℕ) : ℝ) =
      ∫ α, ‖E X φ α‖ ^ 2 ∂torus k := by
  have hc : ((((X ×ˢ X).filter fun q => φ q.1 = φ q.2).card : ℕ) : ℂ) =
      ∫ α, E X φ α * (starRingEnd ℂ) (E X φ α) ∂torus k := by
    have hexp : ∀ α, E X φ α * (starRingEnd ℂ) (E X φ α) =
        ∑ x ∈ X, ∑ y ∈ X, ee (∑ j, ((φ x j - φ y j : ℤ) : ℝ) * α j) := by
      intro α
      rw [E, map_sum, Finset.sum_mul_sum]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro y _
      rw [conj_ee, ← ee_add]
      congr 1
      push_cast
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply sum_congr rfl; intro j _; ring
    simp_rw [hexp]
    have hint : ∀ x y : β, Integrable
        (fun α => ee (∑ j, ((φ x j - φ y j : ℤ) : ℝ) * α j)) (torus k) := fun x y =>
      integrable_ee _ (by fun_prop)
    rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hint x y))]
    simp_rw [integral_finsetSum _ (fun y _ => hint _ y)]
    have e : ∀ x y : β, ∫ α, ee (∑ j, ((φ x j - φ y j : ℤ) : ℝ) * α j) ∂torus k =
        if φ x = φ y then 1 else 0 := by
      intro x y
      rw [show (fun α : Fin k → ℝ => ee (∑ j, ((φ x j - φ y j : ℤ) : ℝ) * α j)) =
        fun α => ee (∑ j, (((φ x - φ y) j : ℤ) : ℝ) * α j) by rfl, integral_torus]
      simp only [sub_eq_zero]
    simp_rw [e]
    rw [← Finset.sum_product', Finset.sum_boole]
  have e2 : ∀ α, E X φ α * (starRingEnd ℂ) (E X φ α) = ((‖E X φ α‖ ^ 2 : ℝ) : ℂ) := by
    intro α
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e2, integral_complex_ofReal] at hc
  exact_mod_cast hc

/-- The one-variable sum over a value set `C`. -/
noncomputable def g (C : Finset ℕ) {k : ℕ} (α : Fin k → ℝ) : ℂ :=
  ∑ n ∈ C, ee (∑ j : Fin k, α j * (n : ℝ) ^ (j.val + 1))

lemma E_pi (C : Finset ℕ) (s k : ℕ) (α : Fin k → ℝ) :
    E (Fintype.piFinset fun _ : Fin s => C) (pv k) α = g C α ^ s := by
  have h1 : g C α ^ s = ∏ _i : Fin s, g C α := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h1, g, Finset.prod_univ_sum, E]
  apply sum_congr rfl
  intro x _
  rw [← ee_sum]
  congr 1
  simp only [pv]
  push_cast
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro i _
  ring

lemma E_prod {β γ : Type*} {k : ℕ} (X : Finset β) (W : Finset γ) (φ : β → Fin k → ℤ)
    (ψ : γ → Fin k → ℤ) (α : Fin k → ℝ) :
    E (X ×ˢ W) (fun q => φ q.1 + ψ q.2) α = E X φ α * E W ψ α := by
  rw [E, E, E, Finset.sum_product, Finset.sum_mul_sum]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro w _
  rw [← ee_add]
  congr 1
  simp only [Pi.add_apply]
  push_cast
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl; intro j _; ring

lemma g_split (P p : ℕ) (hp : 0 < p) {k : ℕ} (α : Fin k → ℝ) :
    g (Icc 1 P) α = ∑ a ∈ range p, g (cls P p a) α := by
  unfold g cls
  exact (Finset.sum_fiberwise_of_maps_to (g := fun n => n % p)
    (fun n _ => mem_range.mpr (Nat.mod_lt n hp)) _).symm

/-- Power mean: `(Σ_{a<p} rₐ)^{2s} ≤ p^{2s−1} Σ rₐ^{2s}` for `rₐ ≥ 0`, `s ≥ 1`. -/
lemma power_mean (p s : ℕ) (hs : 1 ≤ s) (r : ℕ → ℝ) (hr : ∀ a, 0 ≤ r a) :
    (∑ a ∈ range p, r a) ^ (2 * s) ≤ (p : ℝ) ^ (2 * s - 1) * ∑ a ∈ range p, r a ^ (2 * s) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp; exact (pow_eq_zero_iff (by omega)).mpr rfl |>.le
  have h := pow_sum_div_card_le_sum_pow (s := range p) (f := r) (fun a _ => hr a) (2 * s - 1)
  rw [show 2 * s - 1 + 1 = 2 * s by omega, card_range] at h
  have hpos : (0 : ℝ) < (p : ℝ) ^ (2 * s - 1) := by positivity
  rw [div_le_iff₀ hpos] at h
  linarith [mul_comm ((p : ℝ) ^ (2 * s - 1)) (∑ a ∈ range p, r a ^ (2 * s))]

/-- The full count `G` (the `w`-variables unrestricted). -/
def Gfull (k s P p : ℕ) : ℕ :=
  (((Dk k P p ×ˢ box s P) ×ˢ (Dk k P p ×ˢ box s P)).filter fun q =>
    pv k q.1.1 + pv k q.1.2 = pv k q.2.1 + pv k q.2.2).card

/-- **Step B (Hölder over classes).** `G ≤ p^{2s−1} Σ_{a<p} G_a`. -/
theorem Gfull_le {k s P p : ℕ} (hp : 0 < p) (hs : 1 ≤ s) :
    Gfull k s P p ≤ p ^ (2 * s - 1) * ∑ a ∈ range p, Gcls k s P p a := by
  set φ : (Fin k → ℕ) × (Fin s → ℕ) → Fin k → ℤ := fun q => pv k q.1 + pv k q.2 with hφ
  have hG : (Gfull k s P p : ℝ) = ∫ α, ‖E (Dk k P p ×ˢ box s P) φ α‖ ^ 2 ∂torus k :=
    count_eq_integral _ φ
  have hGa : ∀ a, (Gcls k s P p a : ℝ) = ∫ α, ‖E (Dk k P p ×ˢ Wa s P p a) φ α‖ ^ 2 ∂torus k :=
    fun a => count_eq_integral _ φ
  have hpt : ∀ α, ‖E (Dk k P p ×ˢ box s P) φ α‖ ^ 2 ≤
      (p : ℝ) ^ (2 * s - 1) * ∑ a ∈ range p, ‖E (Dk k P p ×ˢ Wa s P p a) φ α‖ ^ 2 := by
    intro α
    rw [hφ, E_prod]
    simp_rw [E_prod]
    have hbox : E (box s P) (pv k) α = g (Icc 1 P) α ^ s := E_pi _ s k α
    have hWa : ∀ a, E (Wa s P p a) (pv k) α = g (cls P p a) α ^ s := fun a => E_pi _ s k α
    simp_rw [hbox, hWa, norm_mul, norm_pow, mul_pow, ← pow_mul]
    rw [g_split P p hp α, show s * 2 = 2 * s from mul_comm s 2]
    have h1 : ‖∑ a ∈ range p, g (cls P p a) α‖ ^ (2 * s) ≤
        (∑ a ∈ range p, ‖g (cls P p a) α‖) ^ (2 * s) :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    have h2 := power_mean p s hs (fun a => ‖g (cls P p a) α‖) (fun a => norm_nonneg _)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2)
      (by positivity : (0 : ℝ) ≤ ‖E (Dk k P p) (pv k) α‖ ^ 2)
    refine h3.trans (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply sum_congr rfl
    intro a _
    ring
  have hintE : ∀ (X : Finset ((Fin k → ℕ) × (Fin s → ℕ))),
      Integrable (fun α => ‖E X φ α‖ ^ 2) (torus k) := by
    intro X
    refine Integrable.of_bound ((continuous_E X φ).norm.pow 2).aestronglyMeasurable
      ((X.card : ℝ) ^ 2) (Filter.Eventually.of_forall fun α => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc ‖E X φ α‖ ≤ ∑ x ∈ X, ‖ee (∑ j, (φ x j : ℝ) * α j)‖ := norm_sum_le _ _
      _ = X.card := by simp [norm_ee]
  have hmono := integral_mono (hintE _)
    ((integrable_finsetSum _ fun a _ => hintE _).const_mul ((p : ℝ) ^ (2 * s - 1))) hpt
  rw [integral_const_mul, integral_finsetSum _ fun a _ => hintE _] at hmono
  rw [← hG] at hmono
  simp_rw [← hGa] at hmono
  exact_mod_cast hmono

end VinoHolder
