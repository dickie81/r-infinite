import Mathlib
import WeilDischarge

/-! # The explicit formula over Mathlib's `ζ` zeros (round 156, part 6)

`weilExplicit_Xi` is stated over the zero family of `Ξ` (`rhoXi`). Here that family is identified
with `zetaZeroFamily` (Mathlib's nontrivial zeros of `riemannZeta`, with multiplicity): the two index
types are in bijection, fiber by fiber over each zero `ρ`, because
`ord_ζ(ρ) = ord_ξ(ρ) = ord_Ξ(τ) = ord_{Ξ(√·)}(τ²)` for `ρ = ½ + iτ`
(`analyticOrderAt_comp_of_deriv_ne_zero`, and `ξ = ½s(s − 1)Γℝ(s)ζ(s)` with the prefactor nonzero on
the strip). So `WeilExplicit zetaZeroFamily h hR` holds for every test function in the strip class.
-/

open Real Filter Topology Complex Set MeasureTheory

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-! ## Orders -/

theorem order_sqF_Xi {t : ℂ} (ht : t ≠ 0) :
    analyticOrderAt (sqF Xi) (t ^ 2) = analyticOrderAt Xi t := by
  have hg : AnalyticAt ℂ (fun w : ℂ => w ^ 2) t := by fun_prop
  have hd : deriv (fun w : ℂ => w ^ 2) t ≠ 0 := by
    rw [deriv_pow_field]; simpa using ht
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := sqF Xi) hg hd
  have e : (sqF Xi ∘ fun w : ℂ => w ^ 2) = Xi := funext fun w => sqF_sq Xi_even w
  rw [e] at h
  exact h.symm

theorem order_Xi_xi (t : ℂ) : analyticOrderAt Xi t = analyticOrderAt xi (1 / 2 + I * t) := by
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 / 2 + I * z) t := by fun_prop
  have hd : deriv (fun z : ℂ => 1 / 2 + I * z) t ≠ 0 := by
    have : HasDerivAt (fun z : ℂ => 1 / 2 + I * z) I t := by
      simpa using ((hasDerivAt_id t).const_mul I).const_add (1 / 2)
    rw [this.deriv]; exact I_ne_zero
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := xi) hg hd
  exact h

/-- `ord_ξ(s) = ord_ζ(s)` for `Re s > 0`, `s ≠ 1`. -/
theorem order_xi_zeta {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    analyticOrderAt xi s = analyticOrderAt riemannZeta s := by
  set U : Set ℂ := {z | 0 < z.re} ∩ {1}ᶜ
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
  have hsU : s ∈ U := ⟨hs, h1⟩
  set u : ℂ → ℂ := fun z => z * (z - 1) * Gammaℝ z / 2
  have hEq : ∀ z ∈ U, xi z = u z * riemannZeta z := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => by
      have h' : 0 < z.re := hz.1
      rw [h, zero_re] at h'; exact lt_irrefl _ h'
    have hGz : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hz.1
    simp only [u]
    rw [xi_eq hz0 hz.2, riemannZeta_def_of_ne_zero hz0]
    field_simp
  have hev : xi =ᶠ[𝓝 s] fun z => u z * riemannZeta z :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hsU) hEq
  rw [analyticOrderAt_congr hev]
  have hua : AnalyticAt ℂ u s := by
    have hd : DifferentiableOn ℂ u {z : ℂ | 0 < z.re} := fun z hz =>
      ((((differentiableAt_id.mul (differentiableAt_id.sub_const 1))).mul
        (differentiableAt_Gammaℝ' hz)).div_const 2).differentiableWithinAt
    exact hd.analyticAt ((isOpen_lt continuous_const continuous_re).mem_nhds hs)
  have hza : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s h1
  have hu0 : u s ≠ 0 := by
    have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl _ hs
    simp only [u]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.2 h1))
      (Gammaℝ_ne_zero_of_re_pos hs)) two_ne_zero
  show analyticOrderAt (u * riemannZeta) s = _
  rw [analyticOrderAt_mul hua hza, analyticOrderAt_eq_zero.2 (Or.inr hu0), zero_add]

/-- The zeros of `Ξ` are exactly the ordinates of the nontrivial zeros of `ζ`. -/
theorem nontrivial_iff_Xi (z : ℂ) : IsNontrivialZero z ↔ Xi ((z - 1 / 2) / I) = 0 := by
  constructor
  · intro h; rw [Xi_at_ordinate]; exact xi_eq_zero_of_nontrivial h
  · intro h
    have him := Xi_zero_im h
    have hre : z.re = 1 / 2 - ((z - 1 / 2) / I).im := by
      have e : (z - 1 / 2) / I = -I * (z - 1 / 2) := by field_simp; rw [I_sq]; ring
      rw [e]; simp
    have hre0 : 0 < z.re := by rw [hre]; linarith [le_abs_self ((z - 1 / 2) / I).im]
    have hre1 : z.re < 1 := by rw [hre]; linarith [neg_abs_le ((z - 1 / 2) / I).im]
    have h1 : z ≠ 1 := fun h' => by rw [h', one_re] at hre1; exact lt_irrefl _ hre1
    have h0 : z ≠ 0 := fun h' => by rw [h', zero_re] at hre0; exact lt_irrefl _ hre0
    rw [Xi_at_ordinate, xi_eq h0 h1] at h
    refine ⟨?_, ?_⟩
    · have hΛ : completedRiemannZeta z = 0 := by
        have hz1 : z - 1 ≠ 0 := sub_ne_zero.2 h1
        have := (div_eq_zero_iff.1 h).resolve_right two_ne_zero
        rcases mul_eq_zero.1 this with h2 | h2
        · rcases mul_eq_zero.1 h2 with h3 | h3
          · exact absurd h3 h0
          · exact absurd h3 hz1
        · exact h2
      rw [riemannZeta_def_of_ne_zero h0, hΛ, zero_div]
    · rintro ⟨n, hn⟩
      have := congrArg Complex.re hn
      simp at this
      linarith [Nat.cast_nonneg (α := ℝ) n]


/-! ## The two zero families agree -/

/-- The common multiplicity at `z`: the order of `Ξ(√·)` at `((z − ½)/i)²`. -/
def nZ (z : ℂ) : ℕ := ordN (sqF Xi) (((z - 1 / 2) / I) ^ 2)

theorem hF_sqXi : Differentiable ℂ (sqF Xi) := sqF_differentiable differentiable_Xi Xi_even
theorem hF0_sqXi : sqF Xi 0 ≠ 0 := by rw [sqF_zero]; exact Xi_zero_ne_zero

theorem zeroMult_eq_nZ {z : ℂ} (h : IsNontrivialZero z) : zeroMult ⟨z, h⟩ = nZ z := by
  set t := (z - 1 / 2) / I
  have hXt : Xi t = 0 := (nontrivial_iff_Xi z).1 h
  have ht0 : t ≠ 0 := fun h0 => Xi_zero_ne_zero (by rw [h0] at hXt; exact hXt)
  have hz : 1 / 2 + I * t = z := by simp only [t]; field_simp; ring
  obtain ⟨hre0, hre1⟩ := h.mem_strip
  have h1 : z ≠ 1 := fun h' => by rw [h', one_re] at hre1; exact lt_irrefl _ hre1
  unfold zeroMult nZ ordN
  rw [order_sqF_Xi ht0, order_Xi_xi, hz, order_xi_zeta hre0 h1]

theorem nZ_eq_zero {z : ℂ} (h : ¬ IsNontrivialZero z) : nZ z = 0 := by
  by_contra hne
  apply h
  rw [nontrivial_iff_Xi]
  have := (ordN_ne_zero_iff hF_sqXi hF0_sqXi _).1 hne
  rwa [sqF_sq Xi_even] at this

theorem fib_zeta (z : ℂ) : Nonempty ({q : Σ w : NontrivialZero, Fin (zeroMult w) // zetaZeroFamily q = z}
    ≃ Fin (nZ z)) := by
  by_cases h : IsNontrivialZero z
  · refine ⟨(Equiv.subtypeEquivRight fun q => ?_).trans ((Equiv.sigmaSubtype (⟨z, h⟩ : NontrivialZero)).trans
      (finCongr (zeroMult_eq_nZ h)))⟩
    simp only [zetaZeroFamily]
    constructor
    · intro hq; exact Subtype.ext hq
    · intro hq; rw [hq]
  · have hE : IsEmpty {q : Σ w : NontrivialZero, Fin (zeroMult w) // zetaZeroFamily q = z} :=
      ⟨fun ⟨q, hq⟩ => h (hq ▸ q.1.2)⟩
    rw [nZ_eq_zero h]
    exact ⟨Equiv.equivOfIsEmpty _ _⟩

theorem rhoXi_eq_iff (p : Bool × ZeroIdx (sqF Xi)) (z : ℂ) :
    rhoXi p = z ↔ (if p.1 then tau p.2 else -tau p.2) = (z - 1 / 2) / I := by
  unfold rhoXi
  constructor
  · intro h; rw [← h]; field_simp; ring
  · intro h; rw [h]; field_simp; ring

theorem fib_Xi (z : ℂ) : Nonempty ({p : Bool × ZeroIdx (sqF Xi) // rhoXi p = z} ≃ Fin (nZ z)) := by
  set t := (z - 1 / 2) / I
  by_cases ht : t = 0
  · have hE : IsEmpty {p : Bool × ZeroIdx (sqF Xi) // rhoXi p = z} := by
      refine ⟨fun ⟨p, hp⟩ => ?_⟩
      rw [rhoXi_eq_iff] at hp
      have hτ : tau p.2 = 0 := by
        split_ifs at hp with hb
        · exact hp.trans ht
        · have := neg_eq_zero.1 (hp.trans ht); exact this
      have := ZeroIdx_ne_zero p.2
      rw [← tau_sq, hτ] at this; exact this (by ring)
    have hn : nZ z = 0 := by
      unfold nZ; rw [show (z - 1 / 2) / I = t from rfl, ht]
      by_contra hne
      exact hF0_sqXi (by
        have := (ordN_ne_zero_iff hF_sqXi hF0_sqXi _).1 hne
        simpa using this)
    rw [hn]
    exact ⟨Equiv.equivOfIsEmpty _ _⟩
  · set r : ℂ := (t ^ 2) ^ ((2 : ℂ)⁻¹)
    have hr : r = t ∨ r = -t := by
      have h2 : r ^ 2 = t ^ 2 := sqrt_sq' (t ^ 2)
      have : (r - t) * (r + t) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 this with h | h
      · left; linear_combination h
      · right; linear_combination h
    have htau : ∀ i : ZeroIdx (sqF Xi), i.1 = t ^ 2 → tau i = r := fun i hi => by
      unfold tau; rw [hi]
    have hsq : ∀ i : ZeroIdx (sqF Xi), (tau i = t ∨ -tau i = t) → i.1 = t ^ 2 := fun i hi => by
      rw [← tau_sq i]
      rcases hi with hi | hi
      · rw [hi]
      · rw [← hi]; ring
    classical
    set b0 : Bool := decide (r = t)
    have hfwd : ∀ p : {p : Bool × ZeroIdx (sqF Xi) // rhoXi p = z}, p.1.2.1 = t ^ 2 := fun p => by
      have hp := (rhoXi_eq_iff _ _).1 p.2
      apply hsq
      split_ifs at hp
      · exact Or.inl hp
      · exact Or.inr hp
    have hb : ∀ p : {p : Bool × ZeroIdx (sqF Xi) // rhoXi p = z}, p.1.1 = b0 := fun p => by
      have hp := (rhoXi_eq_iff _ _).1 p.2
      have hτ := htau p.1.2 (hfwd p)
      simp only [b0]
      cases hb1 : p.1.1
      · simp only [hb1, Bool.false_eq_true, ↓reduceIte] at hp
        rw [hτ] at hp
        change -r = t at hp
        have : r ≠ t := fun h' => ht (by rw [h'] at hp; linear_combination -hp / 2)
        exact (decide_eq_false this).symm
      · simp only [hb1, ↓reduceIte] at hp
        rw [hτ] at hp
        exact (decide_eq_true hp).symm
    have hinv : ∀ i : {i : ZeroIdx (sqF Xi) // i.1 = t ^ 2}, rhoXi (b0, i.1) = z := fun i => by
      rw [rhoXi_eq_iff]
      have hτ := htau i.1 i.2
      change _ = t
      by_cases hrt : r = t
      · rw [show b0 = true from decide_eq_true hrt]
        simp only [↓reduceIte]
        rw [hτ, hrt]
      · rw [show b0 = false from decide_eq_false hrt]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hτ, hr.resolve_left hrt, neg_neg]
    let e : {p : Bool × ZeroIdx (sqF Xi) // rhoXi p = z} ≃ {i : ZeroIdx (sqF Xi) // i.1 = t ^ 2} :=
      { toFun := fun p => ⟨p.1.2, hfwd p⟩
        invFun := fun i => ⟨(b0, i.1), hinv i⟩
        left_inv := fun p => by
          apply Subtype.ext
          apply Prod.ext
          · exact (hb p).symm
          · rfl
        right_inv := fun i => rfl }
    exact ⟨e.trans (Equiv.sigmaSubtype (t ^ 2))⟩

/-- **The zero family of `Ξ` is Mathlib's zero family of `ζ`**: an equivalence of index types
carrying `rhoXi` to `zetaZeroFamily`. -/
def zetaEquiv : (Σ w : NontrivialZero, Fin (zeroMult w)) ≃ Bool × ZeroIdx (sqF Xi) :=
  Equiv.ofFiberEquiv (f := zetaZeroFamily) (g := rhoXi) fun z =>
    (fib_zeta z).some.trans (fib_Xi z).some.symm

theorem rhoXi_zetaEquiv (q : Σ w : NontrivialZero, Fin (zeroMult w)) :
    rhoXi (zetaEquiv q) = zetaZeroFamily q :=
  Equiv.ofFiberEquiv_map _ q

theorem weilExplicit_zeta_of {h : ℂ → ℂ} {hR : ℝ → ℝ} (hE : WeilExplicit rhoXi h hR) :
    WeilExplicit zetaZeroFamily h hR := by
  refine ⟨hE.1, ?_⟩
  have := (zetaEquiv.hasSum_iff (f := fun p => h ((rhoXi p - 1 / 2) / I))).2 hE.2
  simpa [Function.comp_def, rhoXi_zetaEquiv] using this

/-- **Weil's explicit formula over the nontrivial zeros of `ζ`, proved** (no RH input): for every
even test function holomorphic on `|Im t| ≤ 1` with `|h(t)| ≤ C/(1 + (Re t)²)` there and real on
`ℝ`, `WeilExplicit zetaZeroFamily h hR`. -/
theorem weilExplicit_zeta {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) : WeilExplicit zetaZeroFamily h hR :=
  weilExplicit_zeta_of (weilExplicit_Xi H heven hreal)

/-- Round 133's corollary over the zeros of `ζ`, with its named inputs discharged. -/
theorem lam_decay_zeta_uncond (B : ℝ) : ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → lam a ≤ K * Real.exp (-B * a) :=
  lam_decay_zeta (fun a ha => weilExplicit_zeta_of (weilExplicit_PhiA (by linarith)))
    (weilExplicit_zeta_of (weilExplicit_Xi striptest_four (fun t => by simp) (fun r => by push_cast; rfl))) B

end Pilot1ca

#print axioms Pilot1ca.order_xi_zeta
#print axioms Pilot1ca.zetaEquiv
#print axioms Pilot1ca.weilExplicit_zeta
#print axioms Pilot1ca.lam_decay_zeta_uncond
