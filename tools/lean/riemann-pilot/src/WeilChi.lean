import Mathlib
import RealDirichlet
import WeilAssemble

/-! # Weil's explicit formula for primitive real Dirichlet characters (round 225) -/

open Real Complex MeasureTheory Filter Topology Set ArithmeticFunction

noncomputable section

namespace PsiOmega

open LandauLaplace DirichletCharacter Pilot1ca Pilot1bt PilotWeil

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- The hypotheses: `χ ≠ 1` primitive and real, with `L(½, χ) ≠ 0`. -/
structure GoodChar (χ : DirichletCharacter ℂ N) : Prop where
  ne_one : χ ≠ 1
  quad : χ.IsQuadratic
  prim : χ.IsPrimitive
  half : LFunction χ (1 / 2) ≠ 0

/-- The parity `δ ∈ {0, 1}`: `Γ_ℝ(s + δ)` is the gamma factor. -/
def parity (χ : DirichletCharacter ℂ N) : ℕ := by
  classical exact if χ.Even then 0 else 1

omit [NeZero N] in
theorem parity_le (χ : DirichletCharacter ℂ N) : parity χ ≤ 1 := by
  unfold parity; split_ifs <;> norm_num

omit [NeZero N] in
theorem gammaFactor_parity (χ : DirichletCharacter ℂ N) (s : ℂ) :
    gammaFactor χ s = Gammaℝ (s + parity χ) := by
  classical
  unfold gammaFactor parity; split_ifs <;> simp

omit [NeZero N] in
theorem parity_nonneg' (χ : DirichletCharacter ℂ N) : (0 : ℝ) ≤ parity χ := Nat.cast_nonneg _

omit [NeZero N] in
theorem parity_le' (χ : DirichletCharacter ℂ N) : (parity χ : ℝ) ≤ 1 := by
  exact_mod_cast parity_le χ

variable (hG : GoodChar χ)
include hG

/-! ## `Ξ_χ` -/

theorem LamG_half_ne : LamG χ (1 / 2) ≠ 0 := LamG_ne_zero (by norm_num) hG.half

/-- **The root number is `1`**: `Λ*(½) = εΛ*(½) ≠ 0`. -/
theorem rootNumber_eq_one : rootNumber χ = 1 := by
  have h := LamG_one_sub hG.quad hG.prim (1 / 2)
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at h
  have h0 := LamG_half_ne hG
  have : (rootNumber χ - 1) * LamG χ (1 / 2) = 0 := by linear_combination -h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)

omit hG in
/-- `Ξ_χ(t) = Λ*(½ + it)`. -/
def XiC (χ : DirichletCharacter ℂ N) (t : ℂ) : ℂ := LamG χ (1 / 2 + I * t)

theorem differentiable_XiC : Differentiable ℂ (XiC χ) :=
  (differentiable_LamG hG.ne_one).comp ((differentiable_const _).add
    ((differentiable_const _).mul differentiable_id))

theorem XiC_even (t : ℂ) : XiC χ (-t) = XiC χ t := by
  unfold XiC
  rw [show 1 / 2 + I * -t = 1 - (1 / 2 + I * t) by ring, LamG_one_sub hG.quad hG.prim,
    rootNumber_eq_one hG, one_mul]

theorem XiC_zero_ne : XiC χ 0 ≠ 0 := by
  unfold XiC; simpa using LamG_half_ne hG

theorem XiC_sq (t : ℂ) : XiC χ t ^ 2 = fG χ t := by
  rw [fG_eq hG.quad hG.prim, rootNumber_eq_one hG, one_mul]; rfl

/-- The constant of the growth bound. -/
def KC (χ : DirichletCharacter ℂ N) : ℝ :=
  (‖rootNumber χ‖ + 1) * Real.exp (36 * (((N : ℝ) + 5) * Real.sqrt ((N : ℝ) + 5))) + 1

omit hG in
theorem one_le_KC : 1 ≤ KC χ := by
  unfold KC
  have := Real.one_le_exp (show (0 : ℝ) ≤ 36 * (((N : ℝ) + 5) * Real.sqrt ((N : ℝ) + 5)) by positivity)
  nlinarith [norm_nonneg (rootNumber χ)]

/-- **The order of `Ξ_χ`**: `‖Ξ_χ(t)‖ ≤ K·exp(36‖t‖^{3/2})`. -/
theorem norm_XiC_le (t : ℂ) : ‖XiC χ t‖ ≤ KC χ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) := by
  have hf := norm_fG_le hG.ne_one hG.quad hG.prim t
  rw [← XiC_sq hG, norm_pow] at hf
  have he := Real.one_le_exp (show (0 : ℝ) ≤ 36 * ‖t‖ ^ (3 / 2 : ℝ) by positivity)
  have hK : 1 ≤ KC χ := one_le_KC
  rcases le_total ‖XiC χ t‖ 1 with h | h
  · nlinarith
  · have : ‖XiC χ t‖ ≤ ‖XiC χ t‖ ^ 2 := by nlinarith
    unfold KC at hK ⊢
    nlinarith [Real.exp_pos (36 * ‖t‖ ^ (3 / 2 : ℝ))]

theorem hadamard_XiC : HadamardW (XiC χ) (fun i : ZeroIdx (sqF (XiC χ)) => i.1⁻¹) :=
  hadamardW_even (differentiable_XiC hG) (XiC_even hG) (XiC_zero_ne hG) one_le_KC (by norm_num)
    (by norm_num) (by norm_num) (norm_XiC_le hG)

omit hG in
theorem LamG_ne_zero_of_one_le_re (hχ1 : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : LamG χ s ≠ 0 :=
  LamG_ne_zero (by linarith) (LFunction_ne_zero_of_one_le_re χ (.inl hχ1) hs)

/-- **The zeros of `Ξ_χ` lie in `|Im t| < ½`.** -/
theorem XiC_zero_im {t : ℂ} (ht : XiC χ t = 0) : |t.im| < 1 / 2 := by
  have hre : (1 / 2 + I * t).re = 1 / 2 - t.im := by simp; ring
  rw [abs_lt]
  constructor
  · by_contra h; push Not at h
    exact LamG_ne_zero_of_one_le_re hG.ne_one (by rw [hre]; linarith) ht
  · by_contra h; push Not at h
    have h1 : 1 ≤ (1 - (1 / 2 + I * t)).re := by simp; linarith
    apply LamG_ne_zero_of_one_le_re hG.ne_one h1
    rw [LamG_one_sub hG.quad hG.prim, rootNumber_eq_one hG, one_mul]; exact ht

theorem ZeroIdxC_ne_zero (i : ZeroIdx (sqF (XiC χ))) : i.1 ≠ 0 := by
  intro h
  have hz : sqF (XiC χ) i.1 = 0 := (ordN_ne_zero_iff (sqF_differentiable (differentiable_XiC hG)
    (XiC_even hG)) (by rw [sqF_zero]; exact XiC_zero_ne hG) i.1).1 (by
      intro h0; exact Fin.elim0 (h0 ▸ i.2))
  rw [h, sqF_zero] at hz
  exact XiC_zero_ne hG hz

/-- **The logarithmic derivative of Hadamard's product**: off the zeros,
`Ξ_χ′(t)/Ξ_χ(t) = Σ_u 2t/(t² − u)`. -/
theorem hasSum_logDeriv_XiC {t : ℂ} (ht : XiC χ t ≠ 0) :
    HasSum (fun i : ZeroIdx (sqF (XiC χ)) => 2 * t / (t ^ 2 - i.1)) (logDeriv (XiC χ) t) :=
  hasSum_logDeriv_of_hadamardW (hadamard_XiC hG) (XiC_zero_ne hG) (ZeroIdxC_ne_zero hG) ht

/-- `Σ_i |u_i|^{−7/8} < ∞` over the zeros of `Ξ_χ(√w)`. -/
theorem summable_XiC_zeros_rpow :
    Summable (fun i : ZeroIdx (sqF (XiC χ)) => (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹) := by
  have hF := sqF_differentiable (differentiable_XiC hG) (XiC_even hG)
  have hF0 : sqF (XiC χ) 0 ≠ 0 := by rw [sqF_zero]; exact XiC_zero_ne hG
  have hgF : ∀ w, ‖sqF (XiC χ) w‖ ≤ KC χ * Real.exp (36 * ‖w‖ ^ (3 / 4 : ℝ)) := by
    intro w
    refine (norm_XiC_le hG _).trans ?_
    have hn : ‖w ^ ((2 : ℂ)⁻¹)‖ = ‖w‖ ^ (2⁻¹ : ℝ) := by
      rw [show ((2 : ℂ)⁻¹) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
    rw [hn, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hs := summable_ord_div_rpow hF hF0 one_le_KC (by norm_num) (by norm_num)
    (by norm_num : (3 / 4 : ℝ) < 7 / 8) hgF
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  refine ⟨fun u => (hasSum_fintype _).summable, ?_⟩
  refine hs.congr fun u => ?_
  rw [tsum_fintype]
  show _ = ∑ _b : Fin (ordN (sqF (XiC χ)) u), (‖u‖ ^ (7 / 8 : ℝ))⁻¹
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]

/-! ## `Ξ_χ′/Ξ_χ` on `Re s > 1` -/

omit hG in
theorem logDeriv_LFunction_eq (hq : χ.IsQuadratic) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (LFunction χ) s = -LSeries (fun n => (fχ χ n : ℂ)) s := by
  rw [LSeries_fχ (isReal_of_isQuadratic hq) hs, logDeriv_apply]; ring

omit hG in
theorem differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have hs2 : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := fun m h => by
    have := congrArg Complex.re h
    simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  exact (((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (π : ℂ)) (Or.inl hπ)).differentiableAt.mul
    ((Complex.differentiableAt_Gamma _ hs2).comp s ((hasDerivAt_id s).div_const 2).differentiableAt)

omit hG in
/-- `Λ*′/Λ* = ½ log N + Γ_ℝ′/Γ_ℝ(s + δ) − Σ Λ(n)χ(n)n^{−s}` on `Re s > 1`. -/
theorem logDeriv_LamG (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (LamG χ) s = (Real.log N : ℂ) / 2 + logDeriv Gammaℝ (s + parity χ)
      - LSeries (fun n => (fχ χ n : ℂ)) s := by
  set δ : ℂ := (parity χ : ℂ)
  have hδ : 0 ≤ δ.re := by simp [δ]
  set U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  set Pf : ℂ → ℂ := fun z => (N : ℂ) ^ (z / 2) * (Gammaℝ (z + δ) * LFunction χ z)
  have hEq : ∀ z ∈ U, LamG χ z = Pf z := by
    intro z hz
    simp only [Pf, LamG]
    rw [completed_eq_mul hz, gammaFactor_parity]
  have hev : LamG χ =ᶠ[𝓝 s] Pf := Filter.eventuallyEq_of_mem (hU.mem_nhds (by show 0 < s.re; linarith)) hEq
  have hlog : logDeriv (LamG χ) s = logDeriv Pf s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hEq s (by show 0 < s.re; linarith)]
  rw [hlog]
  have hN : (N : ℂ) ≠ 0 := natCast_ne_zero'
  have hsδ : 0 < (s + δ).re := by simp only [add_re]; linarith
  have hGs : Gammaℝ (s + δ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos hsδ
  have hL : LFunction χ s ≠ 0 := LFunction_ne_zero_of_one_le_re χ (.inl hχ1) hs.le
  have hdG : DifferentiableAt ℂ (fun z => Gammaℝ (z + δ)) s :=
    (differentiableAt_Gammaℝ_of_re_pos hsδ).comp s (differentiableAt_id.add_const δ)
  have hdL : DifferentiableAt ℂ (LFunction χ) s := differentiable_LFunction hχ1 s
  have hc : HasDerivAt (fun z : ℂ => (N : ℂ) ^ (z / 2)) ((N : ℂ) ^ (s / 2) * Complex.log N * (1 / 2)) s := by
    simpa using ((hasDerivAt_id s).div_const 2).const_cpow (c := (N : ℂ)) (Or.inl hN)
  have hc0 : (N : ℂ) ^ (s / 2) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  have e1 : deriv (fun z : ℂ => z + δ) s = 1 := ((hasDerivAt_id s).add_const δ).deriv
  have hcomp : logDeriv (fun z => Gammaℝ (z + δ)) s = logDeriv Gammaℝ (s + δ) := by
    have hg : DifferentiableAt ℂ (fun z : ℂ => z + δ) s := differentiableAt_id.add_const δ
    have := logDeriv_comp (f := Gammaℝ) (g := fun z : ℂ => z + δ)
      (differentiableAt_Gammaℝ_of_re_pos hsδ) hg
    rw [e1, mul_one] at this
    exact this
  simp only [Pf]
  rw [logDeriv_fun_mul (f := fun z : ℂ => (N : ℂ) ^ (z / 2))
      (g := fun z => Gammaℝ (z + δ) * LFunction χ z) s hc0 (mul_ne_zero hGs hL) hc.differentiableAt
      (hdG.mul hdL),
    logDeriv_fun_mul (f := fun z => Gammaℝ (z + δ)) (g := LFunction χ) s hGs hL hdG hdL,
    hcomp, logDeriv_LFunction_eq hq hs, logDeriv_apply, hc.deriv, ← Complex.natCast_log]
  field_simp
  ring

/-- **`Ξ_χ′/Ξ_χ` on the line `Re s > 1`**: with `s = ½ + it`,
`Ξ_χ′(t)/Ξ_χ(t) = i(½ log N − ½ log π + ½ψ((s + δ)/2) − Σ Λ(n)χ(n)n^{−s})`. -/
theorem logDeriv_XiC_eq {t : ℂ} (ht : 1 < (1 / 2 + I * t).re) :
    logDeriv (XiC χ) t = I * ((Real.log N : ℂ) / 2 - (Real.log π : ℂ) / 2
      + Complex.digamma ((1 / 2 + I * t + parity χ) / 2) / 2
      - LSeries (fun n => (fχ χ n : ℂ)) (1 / 2 + I * t)) := by
  set s := 1 / 2 + I * t
  have hg : HasDerivAt (fun z : ℂ => 1 / 2 + I * z) I t := by
    simpa using ((hasDerivAt_id t).const_mul I).const_add (1 / 2)
  have hdx : DifferentiableAt ℂ (LamG χ) s := differentiable_LamG hG.ne_one s
  have e : XiC χ = LamG χ ∘ fun z : ℂ => 1 / 2 + I * z := by funext z; rfl
  have hsδ : 0 < (s + parity χ).re := by simp only [add_re, natCast_re]; linarith [parity_nonneg' χ]
  rw [e, logDeriv_comp (f := LamG χ) (g := fun z : ℂ => 1 / 2 + I * z) hdx hg.differentiableAt,
    hg.deriv, logDeriv_LamG hG.ne_one hG.quad ht, logDeriv_Gammaℝ hsδ]
  ring

/-! ## The explicit formula -/

/-- A square root `τ` of the zero `u` of `Ξ_χ(√w)`: a zero of `Ξ_χ`. -/
def tauC (i : ZeroIdx (sqF (XiC χ))) : ℂ := i.1 ^ ((2 : ℂ)⁻¹)

omit hG in
theorem tauC_sq (i : ZeroIdx (sqF (XiC χ))) : tauC i ^ 2 = i.1 := sqrt_sq' i.1

theorem XiC_tau (i : ZeroIdx (sqF (XiC χ))) : XiC χ (tauC i) = 0 :=
  (ordN_ne_zero_iff (sqF_differentiable (differentiable_XiC hG) (XiC_even hG))
    (by rw [sqF_zero]; exact XiC_zero_ne hG) i.1).1 (by
      intro h0; exact Fin.elim0 (h0 ▸ i.2))

theorem tauC_im (i : ZeroIdx (sqF (XiC χ))) : |(tauC i).im| < 1 / 2 := XiC_zero_im hG (XiC_tau hG i)

omit hG in
theorem norm_tauC (i : ZeroIdx (sqF (XiC χ))) : ‖tauC i‖ = ‖i.1‖ ^ (2⁻¹ : ℝ) := by
  unfold tauC
  rw [show ((2 : ℂ)⁻¹) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]

theorem countable_ZeroIdxC : Countable (ZeroIdx (sqF (XiC χ))) := by
  have hs : Summable fun i : ZeroIdx (sqF (XiC χ)) => ‖i.1⁻¹‖ := (hadamard_XiC hG).summ
  have hc := hs.countable_support
  have e : Function.support (fun i : ZeroIdx (sqF (XiC χ)) => ‖i.1⁻¹‖) = univ := by
    ext i; simp [ZeroIdxC_ne_zero hG i]
  rw [e] at hc
  exact Set.countable_univ_iff.1 hc

theorem XiC_line_ne_zero (r : ℝ) : XiC χ ((r : ℂ) - I) ≠ 0 := by
  intro h
  have := XiC_zero_im hG h
  simp at this; norm_num at this

theorem summable_kernel_normsC {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Summable fun i : ZeroIdx (sqF (XiC χ)) =>
      ∫ r : ℝ, ‖h (r - I) * (1 / ((r : ℂ) - I - tauC i) + 1 / ((r : ℂ) - I + tauC i))‖ := by
  refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun r => norm_nonneg _)
    (fun i => ?_) ((summable_XiC_zeros_rpow hG).mul_left (600 * C * ∫ x, om x))
  refine (kernel_integral_le H (tauC_im hG i).le).trans ?_
  have hK : 0 ≤ 600 * C * ∫ x, om x :=
    mul_nonneg (by linarith [H.C_nonneg]) (integral_nonneg om_nonneg)
  apply mul_le_mul_of_nonneg_left _ hK
  have hu : 0 < ‖i.1‖ := norm_pos_iff.2 (ZeroIdxC_ne_zero hG i)
  have ht : 0 < ‖tauC i‖ := by rw [norm_tauC]; positivity
  calc (1 + ‖tauC i‖) ^ (-(7 / 4 : ℝ)) ≤ ‖tauC i‖ ^ (-(7 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
    _ = (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ := by
        rw [norm_tauC, ← Real.rpow_mul hu.le, ← Real.rpow_neg hu.le]; norm_num

theorem kernel_eqC (i : ZeroIdx (sqF (XiC χ))) (r : ℝ) :
    2 * ((r : ℂ) - I) / (((r : ℂ) - I) ^ 2 - i.1)
      = 1 / ((r : ℂ) - I - tauC i) + 1 / ((r : ℂ) - I + tauC i) := by
  have him := tauC_im hG i
  have h1 : (r : ℂ) - I - tauC i ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this
    rw [abs_lt] at him; linarith
  have h2 : (r : ℂ) - I + tauC i ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this
    rw [abs_lt] at him; linarith
  have h3 : ((r : ℂ) - I) ^ 2 - tauC i ^ 2 ≠ 0 := by
    rw [show ((r : ℂ) - I) ^ 2 - tauC i ^ 2 = ((r : ℂ) - I - tauC i) * ((r : ℂ) - I + tauC i) by ring]
    exact mul_ne_zero h1 h2
  rw [← tauC_sq i]
  field_simp
  ring

/-- **The zero side**: `∫_ℝ h(r − i)Ξ_χ′/Ξ_χ(r − i) dr = Σ_u 2πi h(τ_u)`. -/
theorem zero_sideC {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t) :
    HasSum (fun i : ZeroIdx (sqF (XiC χ)) => 2 * π * I * h (tauC i))
      (∫ r : ℝ, h (r - I) * logDeriv (XiC χ) (r - I)) := by
  have := countable_ZeroIdxC hG
  set F : ZeroIdx (sqF (XiC χ)) → ℝ → ℂ := fun i r =>
    h (r - I) * (1 / ((r : ℂ) - I - tauC i) + 1 / ((r : ℂ) - I + tauC i))
  have hint : ∀ i, Integrable (F i) := fun i =>
    integrable_kernel H (by linarith [tauC_im hG i])
  have H1 := hasSum_integral_of_summable_integral_norm hint (summable_kernel_normsC hG H)
  have hval : ∀ i, ∫ r, F i r = 2 * π * I * h (tauC i) := fun i =>
    pole_pair H heven (by linarith [tauC_im hG i])
  simp_rw [hval] at H1
  convert H1 using 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  have hs := (hasSum_logDeriv_XiC hG (XiC_line_ne_zero hG r)).mul_left (h (r - I))
  simp only [kernel_eqC hG] at hs
  exact hs.tsum_eq.symm

/-! ## The archimedean term -/

omit [NeZero N] hG in
/-- `z_χ(t) = (½ + it + δ)/2`. -/
def zC (χ : DirichletCharacter ℂ N) (t : ℂ) : ℂ := (1 / 2 + I * t + parity χ) / 2

omit [NeZero N] hG in
/-- `Re ψ((½ + δ)/2 + ir/2)`. -/
def psiReC (χ : DirichletCharacter ℂ N) (r : ℝ) : ℝ := (Complex.digamma (zC χ r)).re

omit [NeZero N] hG in
theorem digamma_zC_neg (r : ℝ) :
    Complex.digamma (zC χ ((-r : ℝ) : ℂ)) = (starRingEnd ℂ) (Complex.digamma (zC χ r)) := by
  have hconj : zC χ ((-r : ℝ) : ℂ) = (starRingEnd ℂ) (zC χ r) := by
    apply Complex.ext
    · rw [Complex.conj_re]; simp [zC]
    · rw [Complex.conj_im]; simp [zC]; ring
  have hnp : ∀ m : ℕ, zC χ r ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp [zC] at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), parity_nonneg' χ]
  have hdiff := (Complex.differentiableAt_Gamma (zC χ r) hnp).hasDerivAt
  have hGc : (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) = Complex.Gamma := by
    funext z; simp [Complex.Gamma_conj]
  have hd := hdiff.conj_conj
  rw [hGc] at hd
  rw [hconj, Complex.digamma, logDeriv_apply, logDeriv_apply, hd.deriv, Complex.Gamma_conj,
    ← map_div₀]

omit [NeZero N] hG in
theorem psi_strip_boundC {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {t : ℂ} (ht : t ∈ PilotWeil.strip (-1) 0) :
    ‖h t * Complex.digamma (zC χ t)‖ ≤ 48 * C * (1 + |t.re|) ^ (-(3 / 2 : ℝ)) := by
  have hC := H.C_nonneg
  obtain ⟨h1, h2⟩ := ht
  set x := t.re
  set z : ℂ := zC χ t
  have hδ0 := parity_nonneg' χ
  have hδ1 := parity_le' χ
  have hzre : z.re = (1 / 2 - t.im + parity χ) / 2 := by simp [z, zC]; ring
  have hz : 1 / 4 ≤ z.re := by rw [hzre]; linarith
  have hnz : 1 + ‖z‖ ≤ 4 * (1 + |x|) := by
    have ht' : ‖t‖ ≤ |x| + 1 := by
      refine (Complex.norm_le_abs_re_add_abs_im t).trans ?_
      have : |t.im| ≤ 1 := abs_le.2 ⟨h1, by linarith⟩
      linarith
    have : ‖z‖ ≤ (1 / 2 + ‖t‖ + parity χ) / 2 := by
      simp only [z, zC, norm_div, Complex.norm_two]
      gcongr
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans ?_) (by simp)
      rw [norm_mul, Complex.norm_I, one_mul]; norm_num
    linarith [abs_nonneg x]
  have hX : 0 < 1 + |x| := by positivity
  have hpsi : ‖Complex.digamma z‖ ≤ 24 * (1 + |x|) ^ (1 / 2 : ℝ) := by
    refine (norm_digamma_le hz).trans ?_
    have : Real.sqrt (1 + ‖z‖) ≤ 2 * (1 + |x|) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc (1 + ‖z‖) ^ (1 / 2 : ℝ) ≤ (4 * (1 + |x|)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hnz (by norm_num)
        _ = 2 * (1 + |x|) ^ (1 / 2 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) hX.le]
            congr 1
            rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  have hh : ‖h t‖ ≤ 2 * C * (1 + |x|) ^ (-(2 : ℝ)) := by
    have := H.bound t ⟨h1, by linarith⟩
    refine this.trans ?_
    rw [Real.rpow_neg hX.le, div_le_iff₀ (by positivity)]
    have hsq : (1 + |x|) ^ (2 : ℝ) ≤ 2 * (1 + x ^ 2) := by
      rw [Real.rpow_two]; nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
    have hp : 0 < (1 + |x|) ^ (2 : ℝ) := by positivity
    calc C = 2 * C * ((1 + |x|) ^ (2 : ℝ))⁻¹ * ((1 + |x|) ^ (2 : ℝ) / 2) := by field_simp
      _ ≤ 2 * C * ((1 + |x|) ^ (2 : ℝ))⁻¹ * (1 + x ^ 2) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [norm_mul]
  calc ‖h t‖ * ‖Complex.digamma z‖ ≤ (2 * C * (1 + |x|) ^ (-(2 : ℝ))) * (24 * (1 + |x|) ^ (1 / 2 : ℝ)) :=
        mul_le_mul hh hpsi (norm_nonneg _) (by positivity)
    _ = 48 * C * ((1 + |x|) ^ (-(2 : ℝ)) * (1 + |x|) ^ (1 / 2 : ℝ)) := by ring
    _ = 48 * C * (1 + |x|) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hX]; norm_num

omit [NeZero N] hG in
theorem psi_strip_diffC {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    DifferentiableOn ℂ (fun t => h t * Complex.digamma (zC χ t)) (PilotWeil.strip (-1) 0) := by
  refine (H.diff.mono (strip_mono le_rfl (by norm_num))).mul ?_
  refine PilotDigamma.differentiableOn_digamma.comp (Differentiable.differentiableOn (by
    unfold zC; fun_prop)) fun t ht => ?_
  show 0 < (zC χ t).re
  have := ht.2
  have := parity_nonneg' χ
  simp [zC]; linarith

omit [NeZero N] hG in
theorem psi_lineC {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    ∫ r : ℝ, h ((r : ℂ) - I) * Complex.digamma (zC χ ((r : ℂ) - I))
      = ∫ r : ℝ, h r * Complex.digamma (zC χ r) := by
  have := strip_shift' (by norm_num : (-1 : ℝ) ≤ 0) (psi_strip_diffC (χ := χ) H)
    (fun t ht => psi_strip_boundC (χ := χ) H ht)
  calc ∫ r : ℝ, h ((r : ℂ) - I) * Complex.digamma (zC χ ((r : ℂ) - I))
      = ∫ r : ℝ, h (↑r + ↑(-1 : ℝ) * I) * Complex.digamma (zC χ (↑r + ↑(-1 : ℝ) * I)) := by
        congr 1; funext r; push_cast; ring_nf
    _ = ∫ r : ℝ, h (↑r + ↑(0 : ℝ) * I) * Complex.digamma (zC χ (↑r + ↑(0 : ℝ) * I)) := this
    _ = _ := by congr 1; funext r; push_cast; ring_nf

omit [NeZero N] hG in
theorem integrable_psi_realC {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Integrable fun r : ℝ => h r * Complex.digamma (zC χ r) := by
  have hmem : ∀ r : ℝ, (r : ℂ) ∈ PilotWeil.strip (-1) 0 := fun r => by
    show -1 ≤ (r : ℂ).im ∧ (r : ℂ).im ≤ 0
    simp
  have hc : Continuous fun r : ℝ => h r * Complex.digamma (zC χ r) :=
    (psi_strip_diffC H).continuousOn.comp_continuous (by fun_prop) hmem
  refine (integrable_om32.const_mul (48 * C)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  have := psi_strip_boundC (χ := χ) H (hmem r)
  simpa using this

omit [NeZero N] hG in
theorem psi_realC {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) :
    ∫ r : ℝ, h r * Complex.digamma (zC χ r) = ((∫ r : ℝ, hR r * psiReC χ r : ℝ) : ℂ) := by
  have hi := integrable_psi_realC (χ := χ) H
  rw [← integral_re_add_im hi]
  have hre : ∀ r : ℝ, RCLike.re (h r * Complex.digamma (zC χ r)) = hR r * psiReC χ r := fun r => by
    rw [hreal]; simp [psiReC]
  have him0 : ∫ r : ℝ, RCLike.im (h r * Complex.digamma (zC χ r)) = 0 := by
    set g : ℝ → ℝ := fun r => RCLike.im (h r * Complex.digamma (zC χ r))
    have hg : ∀ r, g (-r) = -g r := fun r => by
      simp only [g]
      have e := digamma_zC_neg (χ := χ) r
      rw [hreal, hreal, hR_even heven hreal, e]
      simp
    have := integral_neg_eq_self g volume
    simp_rw [hg, integral_neg] at this
    linarith
  simp_rw [hre]
  rw [him0]
  simp

/-! ## The prime term -/

omit [NeZero N] hG in
theorem term_lineR (f : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) (r : ℝ) :
    LSeries.term (fun n => (f n : ℂ)) (1 / 2 + I * ((r : ℂ) - I)) n
      = ((f n / Real.sqrt n : ℝ) : ℂ) * Complex.exp (-(I * ((r : ℂ) - I) * (Real.log n : ℝ))) := by
  rw [LSeries.term_of_ne_zero hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hc, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log hn0.le]
  have hs : ((Real.sqrt n : ℝ) : ℂ) = Complex.exp ((Real.log n : ℝ) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, Complex.ofReal_exp]; push_cast; ring_nf
  rw [Complex.ofReal_div, hs]
  simp only [div_eq_mul_inv, ← Complex.exp_neg]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2; ring

omit [NeZero N] hG in
theorem norm_term_lineR (f : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    ‖LSeries.term (fun n => (f n : ℂ)) (1 / 2 + I * ((r : ℂ) - I)) n‖
      = ‖LSeries.term (fun n => (f n : ℂ)) (3 / 2 : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  have e : (1 / 2 + I * ((r : ℂ) - I)).re = (3 / 2 : ℂ).re := by simp; norm_num
  rw [e]

omit [NeZero N] hG in
theorem LSeriesSummable_fχ' (hq : χ.IsQuadratic) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (fχ χ n : ℂ)) s := LSeriesSummable_fχ (isReal_of_isQuadratic hq) hs

/-- **The prime term**: `∫_ℝ h(r − i) Σ Λ(n)χ(n)n^{−s} dr = 2π Σ Λ(n)χ(n)n^{−1/2} g_h(log n)`. -/
theorem prime_lineC {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) :
    HasSum (fun n : ℕ => ((2 * π * (fχ χ n / Real.sqrt n * gh hR (Real.log n)) : ℝ) : ℂ))
      (∫ r : ℝ, h ((r : ℂ) - I) * LSeries (fun n => (fχ χ n : ℂ)) (1 / 2 + I * ((r : ℂ) - I))) := by
  set f : ℕ → ℂ := fun n => (fχ χ n : ℂ)
  set s : ℝ → ℂ := fun r => 1 / 2 + I * ((r : ℂ) - I)
  have hsre : ∀ r, (s r).re = 3 / 2 := fun r => by simp [s]; norm_num
  set D : ℕ → ℝ → ℂ := fun n r => h ((r : ℂ) - I) * LSeries.term f (s r) n
  have hy : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hline : ∀ x : ℝ, Integrable fun r : ℝ => h ((r : ℂ) - I) * Complex.exp (-(I * ((r : ℂ) - I) * x)) := by
    intro x
    have := integrable_line (H.mul_exp x).diff (H.mul_exp x).bound hy
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only; push_cast; ring_nf
  have hD : ∀ n, n ≠ 0 → D n = fun r : ℝ => ((fχ χ n / Real.sqrt n : ℝ) : ℂ)
      * (h ((r : ℂ) - I) * Complex.exp (-(I * ((r : ℂ) - I) * (Real.log n : ℝ)))) := by
    intro n hn; funext r; simp only [D, s, f]; rw [term_lineR (fχ χ) n hn]; ring
  have hD0 : D 0 = fun _ => 0 := by funext r; simp [D, LSeries.term_zero]
  have hint : ∀ n, Integrable (D n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hD0]; exact integrable_zero _ _ _
    · rw [hD n hn]; exact (hline _).const_mul _
  have hsum : Summable fun n => ∫ r, ‖D n r‖ := by
    have hS : Summable fun n => ‖LSeries.term f (3 / 2 : ℂ) n‖ :=
      summable_norm_iff.2 (LSeriesSummable_fχ' hG.quad (by norm_num))
    refine (hS.mul_right (∫ r : ℝ, ‖h ((r : ℂ) - I)‖)).congr fun n => ?_
    simp only [D, s, f]
    simp_rw [norm_mul, norm_term_lineR]
    rw [integral_mul_const, mul_comm]
  have H1 := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ n, ∫ r, D n r = ((2 * π * (fχ χ n / Real.sqrt n * gh hR (Real.log n)) : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hD0]; simp [fχ]
    · rw [hD n hn, integral_const_mul]
      have := line_eq H hy (Real.log n)
      have e : ∫ r : ℝ, h ((r : ℂ) - I) * Complex.exp (-(I * ((r : ℂ) - I) * (Real.log n : ℝ)))
          = FK h (Real.log n) := by
        rw [← this]; congr 1; funext r; push_cast; ring_nf
      rw [e, FK_eq_gh H heven hreal]
      push_cast; ring
  simp_rw [hval] at H1
  convert H1 using 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  have hs := ((LSeriesSummable_fχ' hG.quad (s := s r) (by rw [hsre]; norm_num)).LSeriesHasSum).mul_left
    (h ((r : ℂ) - I))
  exact hs.tsum_eq.symm

/-! ## Assembly -/

omit [NeZero N] hG in
theorem integrable_psi_lineC {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Integrable fun r : ℝ => h ((r : ℂ) - I) * Complex.digamma (zC χ ((r : ℂ) - I)) := by
  have hmem : ∀ r : ℝ, ((r : ℂ) - I) ∈ PilotWeil.strip (-1) 0 := fun r => by
    show -1 ≤ ((r : ℂ) - I).im ∧ ((r : ℂ) - I).im ≤ 0
    simp
  have hc : Continuous fun r : ℝ => h ((r : ℂ) - I) * Complex.digamma (zC χ ((r : ℂ) - I)) :=
    (psi_strip_diffC H).continuousOn.comp_continuous (by fun_prop) hmem
  refine (integrable_om32.const_mul (48 * C)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  have := psi_strip_boundC (χ := χ) H (hmem r)
  simpa using this

theorem integrable_prime_lineC {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Integrable fun r : ℝ => h ((r : ℂ) - I)
      * LSeries (fun n => (fχ χ n : ℂ)) (1 / 2 + I * ((r : ℂ) - I)) := by
  set f : ℕ → ℂ := fun n => (fχ χ n : ℂ)
  have hy : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hL : Integrable fun r : ℝ => h ((r : ℂ) - I) := by
    have := integrable_line H.diff H.bound hy
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only; push_cast; ring_nf
  have hab : LSeries.abscissaOfAbsConv f ≤ ((5 / 4 : ℂ).re : EReal) :=
    (LSeriesSummable_fχ' hG.quad (by norm_num)).abscissaOfAbsConv_le
  have hmem : ∀ r : ℝ, (1 / 2 + I * ((r : ℂ) - I)) ∈ {s : ℂ | LSeries.abscissaOfAbsConv f < s.re} := by
    intro r
    show LSeries.abscissaOfAbsConv f < ((1 / 2 + I * ((r : ℂ) - I)).re : EReal)
    refine lt_of_le_of_lt hab ?_
    have e1 : (5 / 4 : ℂ).re = 5 / 4 := by norm_num
    have e2 : (1 / 2 + I * ((r : ℂ) - I)).re = 3 / 2 := by simp; norm_num
    rw [e1, e2]; exact_mod_cast (by norm_num : (5 / 4 : ℝ) < 3 / 2)
  have hcf : Continuous fun r : ℝ => (1 / 2 + I * ((r : ℂ) - I) : ℂ) := by fun_prop
  have hc : Continuous fun r : ℝ => LSeries f (1 / 2 + I * ((r : ℂ) - I)) :=
    continuous_iff_continuousAt.2 fun r =>
      ContinuousAt.comp (f := fun r : ℝ => (1 / 2 + I * ((r : ℂ) - I) : ℂ))
        (((LSeries_differentiableOn f).differentiableAt
          ((isOpen_re_gt_EReal _).mem_nhds (hmem r))).continuousAt) hcf.continuousAt
  have hS : Summable fun n => ‖LSeries.term f (3 / 2 : ℂ) n‖ :=
    summable_norm_iff.2 (LSeriesSummable_fχ' hG.quad (by norm_num))
  set M := ∑' n, ‖LSeries.term f (3 / 2 : ℂ) n‖
  have hb : ∀ r : ℝ, ‖LSeries f (1 / 2 + I * ((r : ℂ) - I))‖ ≤ M := fun r => by
    unfold LSeries
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · exact hS.congr fun n => (norm_term_lineR (fχ χ) n r).symm
    · exact tsum_congr fun n => norm_term_lineR (fχ χ) n r
  refine (hL.norm.mul_const M).mono' ((hL.aestronglyMeasurable.mul hc.aestronglyMeasurable))
    (Eventually.of_forall fun r => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb r) (norm_nonneg _)

omit hG in
/-- The right-hand side of the explicit formula for `χ`:
`g_h(0) log(N/π) + (1/2π)∫ h Re ψ((½ + δ)/2 + ir/2) − 2Σ Λ(n)χ(n)n^{−1/2} g_h(log n)`. -/
def weilRHSC (χ : DirichletCharacter ℂ N) (hR : ℝ → ℝ) : ℝ :=
  gh hR 0 * (Real.log N - Real.log π) + 1 / (2 * π) * (∫ r, hR r * psiReC χ r)
    - 2 * ∑' n : ℕ, fχ χ n / Real.sqrt n * gh hR (Real.log n)

/-- **Weil's explicit formula over the zeros of `Ξ_χ`** (each pair `±τ` once, with multiplicity):
for `h` even, holomorphic on `|Im t| ≤ 1` with `|h(t)| ≤ C/(1 + (Re t)²)` there, and real on `ℝ`,
`Σ_u 2h(τ_u) = g_h(0) log(N/π) + (1/2π)∫h Re ψ((½ + δ)/2 + ir/2) − 2Σ Λ(n)χ(n)n^{−1/2}g_h(log n)`. -/
theorem weil_XiC {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) :
    HasSum (fun i : ZeroIdx (sqF (XiC χ)) => 2 * h (tauC i)) (weilRHSC χ hR : ℂ) := by
  set LS : ℝ → ℂ := fun r => LSeries (fun n => (fχ χ n : ℂ)) (1 / 2 + I * ((r : ℂ) - I))
  set PS : ℝ → ℂ := fun r => Complex.digamma (zC χ ((r : ℂ) - I))
  set κ : ℂ := I * ((Real.log N : ℂ) - (Real.log π : ℂ)) / 2
  have hZ := zero_sideC hG H heven
  have hpt : ∀ r : ℝ, h ((r : ℂ) - I) * logDeriv (XiC χ) ((r : ℂ) - I)
      = κ * h ((r : ℂ) - I) + I / 2 * (h ((r : ℂ) - I) * PS r) - I * (h ((r : ℂ) - I) * LS r) := by
    intro r
    rw [logDeriv_XiC_eq hG (by simp)]
    simp only [LS, PS, κ, zC]
    ring
  have hy : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hL : Integrable fun r : ℝ => h ((r : ℂ) - I) := by
    have := integrable_line H.diff H.bound hy
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only; push_cast; ring_nf
  have I2 : Integrable fun r : ℝ => κ * h ((r : ℂ) - I) := hL.const_mul _
  have I3 : Integrable fun r : ℝ => I / 2 * (h ((r : ℂ) - I) * PS r) :=
    (integrable_psi_lineC H).const_mul _
  have I4 : Integrable fun r : ℝ => I * (h ((r : ℂ) - I) * LS r) :=
    (integrable_prime_lineC hG H).const_mul _
  have hsplit : ∫ r : ℝ, h ((r : ℂ) - I) * logDeriv (XiC χ) ((r : ℂ) - I)
      = (∫ r : ℝ, κ * h ((r : ℂ) - I)) + (∫ r : ℝ, I / 2 * (h ((r : ℂ) - I) * PS r))
        - ∫ r : ℝ, I * (h ((r : ℂ) - I) * LS r) := by
    simp_rw [hpt]
    have a1 : (∫ r : ℝ, (κ * h ((r : ℂ) - I) + I / 2 * (h ((r : ℂ) - I) * PS r)
          - I * (h ((r : ℂ) - I) * LS r)))
        = (∫ r : ℝ, (κ * h ((r : ℂ) - I) + I / 2 * (h ((r : ℂ) - I) * PS r)))
          - ∫ r : ℝ, I * (h ((r : ℂ) - I) * LS r) := integral_sub (I2.add I3) I4
    have a2 : (∫ r : ℝ, (κ * h ((r : ℂ) - I) + I / 2 * (h ((r : ℂ) - I) * PS r)))
        = (∫ r : ℝ, κ * h ((r : ℂ) - I)) + ∫ r : ℝ, I / 2 * (h ((r : ℂ) - I) * PS r) :=
      integral_add I2 I3
    rw [a1, a2]
  have v2 : ∫ r : ℝ, κ * h ((r : ℂ) - I) = κ * ((2 * π * gh hR 0 : ℝ) : ℂ) := by
    rw [integral_const_mul, integral_line_const H heven hreal]
  have v3 : ∫ r : ℝ, I / 2 * (h ((r : ℂ) - I) * PS r) = I / 2 * ((∫ r : ℝ, hR r * psiReC χ r : ℝ) : ℂ) := by
    rw [integral_const_mul]
    simp only [PS]
    rw [psi_lineC H, psi_realC H heven hreal]
  have hP := prime_lineC hG H heven hreal
  have v4 : ∫ r : ℝ, I * (h ((r : ℂ) - I) * LS r)
      = I * ((2 * π * ∑' n : ℕ, fχ χ n / Real.sqrt n * gh hR (Real.log n) : ℝ) : ℂ) := by
    rw [integral_const_mul]
    simp only [LS]
    rw [← hP.tsum_eq, ← Complex.ofReal_tsum, tsum_mul_left]
  rw [hsplit, v2, v3, v4] at hZ
  have hZ' := hZ.mul_left ((π * I)⁻¹)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  convert hZ' using 1
  · funext i; field_simp
  · unfold weilRHSC
    simp only [κ]
    push_cast
    field_simp

end PsiOmega

#print axioms PsiOmega.hasSum_logDeriv_XiC
#print axioms PsiOmega.logDeriv_XiC_eq
#print axioms PsiOmega.zero_sideC
#print axioms PsiOmega.prime_lineC
#print axioms PsiOmega.weil_XiC
