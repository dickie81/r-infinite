import LatticeCount
import WeilDedekind

/-! # The residue of the radial member and `L(1, χ₋₄) = π/4` (round 243)

Lattice points in a disc (`LatticeCount`, `BallTower`) count Gaussian integers by norm (`GlobalTeeth` shells), so `Σ_{k≤N} r₂(k)/4 ∼ (π/4)N`; Mathlib's Abelian theorem gives the residue `π/4` of `ζ(s)L(s, χ₋₄)` at `s = 1` (`residue_angular`), and the residue of `ζ` gives `L(1, χ₋₄) = π/4`. This joins the `BallTower`/`LatticeCount` island to the `GlobalTeeth`/`AngularFamily` island.
-/

open Filter Topology Complex

namespace AngularResidue

open BallTower GlobalTeeth AngularFamily

/-- The Gaussian integers of norm at most `N`. -/
noncomputable def disc (N : ℕ) : Finset GaussianInt := (Finset.range (N + 1)).biUnion shell

theorem mem_disc {N : ℕ} {z : GaussianInt} : z ∈ disc N ↔ z.norm ≤ N := by
  unfold disc
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨m, hm, hz⟩
    rw [mem_shell] at hz
    rw [hz]; exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  · intro h
    have h0 : 0 ≤ z.norm := Zsqrtd.norm_nonneg (by norm_num) z
    refine ⟨z.norm.toNat, Finset.mem_range.2 (Nat.lt_succ_of_le (by omega)), mem_shell.2 ?_⟩
    exact (Int.toNat_of_nonneg h0).symm

theorem card_disc (N : ℕ) : ((disc N).card : ℝ) = ∑ m ∈ Finset.range (N + 1), (R m : ℝ) := by
  classical
  unfold disc
  rw [Finset.card_biUnion]
  · push_cast; rfl
  · intro m _ m' _ hmm'
    show Disjoint (shell m) (shell m')
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [mem_shell] at hz hz'
    exact hmm' (by exact_mod_cast hz.symm.trans hz')

/-- The embedding `ℤ[i] → ℝ²`. -/
noncomputable def emb (z : GaussianInt) : Fin 2 → ℝ := ![(z.re : ℝ), (z.im : ℝ)]

theorem emb_injective : Function.Injective emb := by
  intro z w h
  have h0 : (z.re : ℝ) = (w.re : ℝ) := congrFun h 0
  have h1 : (z.im : ℝ) = (w.im : ℝ) := congrFun h 1
  exact Zsqrtd.ext (by exact_mod_cast h0) (by exact_mod_cast h1)

theorem eLen_emb (z : GaussianInt) : eLen 2 (emb z) = Real.sqrt (z.norm : ℝ) := by
  unfold eLen emb
  rw [Fin.sum_univ_two, Real.sqrt_eq_rpow, GlobalTeeth.norm_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.rpow_two, sq_abs]
  push_cast
  ring_nf

/-- **Lattice count = shell sum**: `#{v ∈ ℤ² : |v| ≤ √N} = Σ_{m ≤ N} r₂(m)`. -/
theorem latticeCount_two_sqrt (N : ℕ) : (latticeCount 2 (Real.sqrt N) : ℝ) = (disc N).card := by
  have hset : ({x : Fin 2 → ℝ | eLen 2 x ≤ Real.sqrt N} ∩ (intLattice 2 : Set (Fin 2 → ℝ))) =
      emb '' (disc N : Set GaussianInt) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SetLike.mem_coe, Set.mem_image]
    constructor
    · rintro ⟨hx, hl⟩
      rw [mem_intLattice] at hl
      obtain ⟨k0, hk0⟩ := hl 0
      obtain ⟨k1, hk1⟩ := hl 1
      have hxe : x = emb ⟨k0, k1⟩ := by
        funext i; fin_cases i <;> simp [emb, hk0, hk1]
      refine ⟨⟨k0, k1⟩, ?_, hxe.symm⟩
      rw [mem_disc]
      rw [hxe, eLen_emb, Real.sqrt_le_sqrt_iff (by positivity)] at hx
      exact_mod_cast hx
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [eLen_emb]
        exact Real.sqrt_le_sqrt (by exact_mod_cast mem_disc.1 hz)
      · rw [mem_intLattice]
        intro i; fin_cases i
        · exact ⟨z.re, by simp [emb]⟩
        · exact ⟨z.im, by simp [emb]⟩
  unfold latticeCount
  rw [Nat.card_coe_set_eq, hset, Set.ncard_image_of_injective _ emb_injective, Set.ncard_coe_finset]

theorem tendsto_disc : Tendsto (fun N : ℕ => ((disc N).card : ℝ) / N) atTop (𝓝 Real.pi) := by
  have h := (count_div_pow_tendsto_ballVol 2).comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  rw [ballVol_two] at h
  refine h.congr' ?_
  filter_upwards with N
  simp only [Function.comp_apply]
  rw [latticeCount_two_sqrt, Real.sq_sqrt (Nat.cast_nonneg N)]

theorem R_zero : R 0 = 1 := by rw [R_eq_pairs]; decide

theorem sum_Icc_R (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ((R k : ℝ) / 4) = (((disc n).card : ℝ) - 1) / 4 := by
  have e : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [← Finset.sum_div, e, Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ n + 1), Finset.sum_range_one,
    card_disc, R_zero]
  push_cast; ring

theorem tendsto_sum_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, ((R k : ℝ) / 4)) / (n : ℝ)) atTop
      (𝓝 (Real.pi / 4)) := by
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h := (tendsto_disc.sub h1).div_const 4
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards with n
  rw [sum_Icc_R]; ring

/-- **The residue of the radial member**: `(s − 1)·Σ r₂(n)/(4nˢ) → π/4` as `s → 1⁺`. -/
theorem residue_angular :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * angularL 0 s) (𝓝[>] 1) (𝓝 ((Real.pi / 4 : ℝ) : ℂ)) := by
  have h := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg
    (fun n => (R n : ℝ) / 4) tendsto_sum_div (fun n => by positivity)
  refine h.congr' ?_
  filter_upwards with s
  congr 1
  unfold angularL
  refine LSeries_congr (fun {n} _ => ?_) _
  simp only [angularCoeff, R, mul_zero, pow_zero, div_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  push_cast; ring

/-- **`L(1, χ₋₄) = π/4`**, from counting lattice points in a disc (LatticeCount), Jacobi's two-square
theorem (GlobalTeeth) and the radial member's factorisation (AngularFamily). -/
theorem LFunction_chi4_one : DirichletCharacter.LFunction χ4C 1 = ((Real.pi / 4 : ℝ) : ℂ) := by
  have hχ : χ4C ≠ 1 := by rw [Dedekind4.χ4C_eq]; exact PsiOmega.chi4_ne_one
  have hof : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  have hmap : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hof, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact Set.mem_compl_singleton_iff.2 (by exact_mod_cast (ne_of_gt hs))
  have hz : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta s) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp hmap
  have hL : Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ4C s) (𝓝[>] 1)
      (𝓝 (DirichletCharacter.LFunction χ4C 1)) :=
    ((DirichletCharacter.differentiable_LFunction hχ).continuous.tendsto 1).comp hof
  have hprod : ∀ᶠ s : ℝ in 𝓝[>] 1, ((s : ℂ) - 1) * angularL 0 s =
      (((s : ℂ) - 1) * riemannZeta s) * DirichletCharacter.LFunction χ4C s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < (s : ℂ).re := by simpa using hs
    rw [member_zero_eq hs', angularL0]; ring
  have h3 := residue_angular.congr' hprod
  have h2 := hz.mul hL
  have := tendsto_nhds_unique h3 h2
  rw [one_mul] at this
  exact this.symm

end AngularResidue

#print axioms AngularResidue.latticeCount_two_sqrt
#print axioms AngularResidue.tendsto_disc
#print axioms AngularResidue.residue_angular
#print axioms AngularResidue.LFunction_chi4_one
