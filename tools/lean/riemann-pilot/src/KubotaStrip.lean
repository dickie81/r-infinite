import KubotaMellin

/-! # Polynomial bounds in vertical strips (round 375)

S5f-5 of round 360's plan, part 1. The companion paper writes that the functional equation and Stirling's
formula "`therefore give polynomial bounds in $|\operatorname{Im}s|$ for $\mathcal T(s,\Psi)$ on both sides
of the strip $0\le\Rea s\le1$.`" It continues: "`Splitting the integral defining $\mathcal J(s)$ at $v=1$
gives finite order;`" and Phragmén–Lindelöf "`then gives the same type of bound inside the strip`". This file
proves such bounds for round 374's `𝒥(s)`, divided by its Gamma factors `Γ(s + 1/3)Γ(s + 2/3)`. The Gamma
quotient of the functional equation is handled by complex conjugation and `Γ(z + 1) = zΓ(z)` in place of
Stirling's formula.

* **The Gamma function in vertical strips** (`Gamma_add_nat_eq`, `exists_norm_Gamma_le`, `norm_sin_le_exp`,
  `exists_norm_inv_Gamma_le`): `Γ(s + n) = Γ(s)∏_{j<n}(s + j)`. On `{a ≤ Re s ≤ b, |Im s| ≥ 1}`, `|Γ(s)|` is
  bounded and `|1/Γ(s)| ≤ Ce^{π|Im s|}`.
* **Phragmén–Lindelöf with polynomial bounds** (**`poly_bound_strip`**): if `f` is holomorphic on the closed
  strip `a ≤ Re z ≤ b`, at most `C(1 + |Im z|)^M` on both edges and at most `Ae^{B|Im z|}` where `|Im z| ≥ 1`,
  then `|f(z)| ≤ C2^M(b − a + 1)^M(1 + |Im z|)^M` in the strip.
* **Mellin transforms in strips** (`norm_mellin_le_strip`): a Mellin transform that converges on both edges
  of a strip is bounded in it.
* **The Gamma quotient** (`gRatio`, `differentiableOn_gRatio`, **`norm_gRatio_half`**, **`norm_gRatio_le`**,
  `exists_gRatio_strip`, with `norm_le_of_re_im` and `norm_prod_range_le`):
  `Γ(4/3 − s)Γ(5/3 − s)/(Γ(s + 1/3)Γ(s + 2/3))`, holomorphic on `Re s < 4/3`. It has modulus `1` on
  `Re s = 1/2`, is at most `((k + 3)(1 + |Im s|))^{4k}` on `Re s = 1/2 − k`, and is at most a constant times
  `(1 + |Im s|)^{4k}` between the two lines.
* **The strip bound** (**`poly_bound_FE`**, with `summable_dSer_abs`, `norm_mellin_dSer_le` and
  `norm_nested_sum_le`): under the hypotheses of round 374's `mellin_FE`,
  `|𝒥(s)/(Γ(s + 1/3)Γ(s + 2/3))| ≤ C(1 + |Im s|)^{12}` for `−5/2 ≤ Re s ≤ 2`.
* **For the twisted `θ̄`** (**`twisted_theta_poly`**): the same bound with the data of round 373's
  `twisted_theta_dbar`.
-/

open Real Set Filter MeasureTheory Complex NumberField Ideal Asymptotics
open scoped Topology ComplexConjugate

noncomputable section

namespace Eis

/-- `Γ(s + n) = Γ(s)·∏_{j<n}(s + j)` when no `s + j` vanishes. -/
theorem Gamma_add_nat_eq (s : ℂ) (n : ℕ) (hs : ∀ j : ℕ, s + j ≠ 0) :
    Gamma (s + n) = Gamma s * ∏ j ∈ Finset.range n, (s + j) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, show s + ((k + 1 : ℕ) : ℂ) = (s + k) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ (hs k), ih]
    ring

/-- `|Γ(s)|` is bounded on `{a ≤ Re s ≤ b, |Im s| ≥ 1}`. -/
theorem exists_norm_Gamma_le (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → ‖Gamma s‖ ≤ C := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 - a)
  obtain ⟨N, hN⟩ := exists_nat_gt (b + n + 1)
  refine ⟨4 * N.factorial, by positivity, fun s ha hb him => ?_⟩
  have hne : ∀ j : ℕ, s + j ≠ 0 := fun j h => by
    have := congrArg Complex.im h
    simp at this
    rw [this, abs_zero] at him
    linarith
  have hge : ∀ j : ℕ, 1 ≤ ‖s + j‖ := fun j => him.trans (by
    have := Complex.abs_im_le_norm (s + j)
    simpa using this)
  have hprod : 1 ≤ ‖∏ j ∈ Finset.range n, (s + j)‖ := by
    rw [norm_prod]
    exact Finset.one_le_prod₀ fun j _ => hge j
  have hre : 0 < (s + n).re := by simp; linarith
  have h1 := PsiOmega.norm_cGamma_le' hre
  have h2 : Real.Gamma (s + n).re ≤ 4 * N.factorial :=
    PsiOmega.rGamma_le' (by simp; linarith) (by simp; linarith)
  calc ‖Gamma s‖ ≤ ‖Gamma s‖ * ‖∏ j ∈ Finset.range n, (s + j)‖ :=
        le_mul_of_one_le_right (norm_nonneg _) hprod
    _ = ‖Gamma (s + n)‖ := by rw [Gamma_add_nat_eq s n hne, norm_mul]
    _ ≤ 4 * N.factorial := h1.trans h2

/-- `|sin z| ≤ e^{|Im z|}`. -/
theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have e1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by rw [Complex.norm_exp]; simp
  have e2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by rw [Complex.norm_exp]; simp
  have h3 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have h4 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  calc ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2
      ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by gcongr; exact norm_sub_le _ _
    _ ≤ Real.exp |z.im| := by rw [e1, e2]; linarith

/-- `|1/Γ(s)| ≤ Ce^{π|Im s|}` on `{a ≤ Re s ≤ b, |Im s| ≥ 1}`, by the reflection formula. -/
theorem exists_norm_inv_Gamma_le (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖(Gamma s)⁻¹‖ ≤ C * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_Gamma_le (1 - b) (1 - a)
  refine ⟨C / Real.pi, by positivity, fun s ha hb him => ?_⟩
  have him0 : s.im ≠ 0 := fun h => by rw [h, abs_zero] at him; linarith
  have hsin : Complex.sin (π * s) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 h
    have e1 : ((π : ℂ) * s).im = π * s.im := by simp
    have e2 : ((k : ℂ) * π).im = 0 := by simp
    have := congrArg Complex.im hk
    rw [e1, e2] at this
    exact him0 ((mul_eq_zero.1 this).resolve_left Real.pi_pos.ne')
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  have hΓ : Gamma s ≠ 0 := fun h => by
    rw [h, zero_mul] at hrefl
    exact (div_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_pos.ne') hsin) hrefl.symm
  have hinv : (Gamma s)⁻¹ = Gamma (1 - s) * Complex.sin (π * s) / π := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
    field_simp
    rw [hrefl]
    field_simp
  rw [hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have h1 := hC (1 - s) (by simp; linarith) (by simp; linarith) (by simpa using him)
  have h2 : ‖Complex.sin (π * s)‖ ≤ Real.exp (Real.pi * |s.im|) := by
    refine (norm_sin_le_exp _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  calc ‖Gamma (1 - s)‖ * ‖Complex.sin (π * s)‖ / π
      ≤ C * Real.exp (Real.pi * |s.im|) / π := by gcongr
    _ = C / Real.pi * Real.exp (Real.pi * |s.im|) := by ring

/-- **Phragmén–Lindelöf with polynomial bounds** in a vertical strip: if `f` is holomorphic on the closed
strip,
`|f(z)| ≤ C(1 + |Im z|)^M` on the lines `Re z = a` and `Re z = b`, and `|f(z)| ≤ Ae^{B|Im z|}` in the strip
where `|Im z| ≥ 1`, then `|f(z)| ≤ C2^M(b − a + 1)^M(1 + |Im z|)^M` in the strip (Mathlib's
`PhragmenLindelof.vertical_strip` for `f(z)/(z − a + 1)^M`). -/
theorem poly_bound_strip {f : ℂ → ℂ} {a b C A B : ℝ} (hf : DifferentiableOn ℂ f (re ⁻¹' Icc a b))
    (hab : a < b) (M : ℕ)
    (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C * (1 + |z.im|) ^ M)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C * (1 + |z.im|) ^ M)
    (hgr : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| → ‖f z‖ ≤ A * Real.exp (B * |z.im|)) :
    ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C * 2 ^ M * (b - a + 1) ^ M * (1 + |z.im|) ^ M := by
  set z₀ : ℂ := ((a - 1 : ℝ) : ℂ) with hz₀
  have hlow : ∀ z : ℂ, a ≤ z.re → (1 + |z.im|) / 2 ≤ ‖z - z₀‖ := by
    intro z hz
    have h1 := Complex.abs_re_le_norm (z - z₀)
    have h2 := Complex.abs_im_le_norm (z - z₀)
    have e1 : (z - z₀).re = z.re - a + 1 := by simp [hz₀]; ring
    have e2 : (z - z₀).im = z.im := by simp [hz₀]
    rw [e1, abs_of_pos (by linarith)] at h1
    rw [e2] at h2
    linarith
  have hup : ∀ z : ℂ, z.re ≤ b → a ≤ z.re → ‖z - z₀‖ ≤ (b - a + 1) * (1 + |z.im|) := by
    intro z hz hz'
    have h := Complex.norm_le_abs_re_add_abs_im (z - z₀)
    have e1 : (z - z₀).re = z.re - a + 1 := by simp [hz₀]; ring
    have e2 : (z - z₀).im = z.im := by simp [hz₀]
    rw [e1, e2, abs_of_pos (by linarith)] at h
    nlinarith [abs_nonneg z.im]
  have hne : ∀ z : ℂ, a ≤ z.re → z - z₀ ≠ 0 := fun z hz h => by
    have := hlow z hz
    rw [h, norm_zero] at this
    linarith [abs_nonneg z.im]
  set g : ℂ → ℂ := fun z => f z / (z - z₀) ^ M with hg_def
  have hgd : DiffContOnCl ℂ g (re ⁻¹' Ioo a b) := by
    refine DifferentiableOn.diffContOnCl ?_
    have hsub : closure (re ⁻¹' Ioo a b) ⊆ re ⁻¹' Icc a b :=
      closure_minimal (preimage_mono Ioo_subset_Icc_self)
        (isClosed_Icc.preimage Complex.continuous_re)
    refine DifferentiableOn.div (hf.mono hsub) ((differentiable_id.sub_const _).pow M).differentiableOn
      fun z hz => pow_ne_zero _ (hne z (hsub hz).1)
  have hgb : ∀ z : ℂ, (z.re = a ∨ z.re = b) → ‖g z‖ ≤ C * 2 ^ M := by
    intro z hz
    have hza : a ≤ z.re := by rcases hz with h | h <;> linarith
    have hfz : ‖f z‖ ≤ C * (1 + |z.im|) ^ M := by rcases hz with h | h; exact ha z h; exact hb z h
    have hl := hlow z hza
    have hpos : 0 < (1 + |z.im|) / 2 := by positivity
    simp only [hg_def, norm_div, norm_pow]
    rw [div_le_iff₀ (pow_pos (hpos.trans_le hl) M)]
    calc ‖f z‖ ≤ C * (1 + |z.im|) ^ M := hfz
      _ = C * 2 ^ M * ((1 + |z.im|) / 2) ^ M := by rw [div_pow]; field_simp
      _ ≤ C * 2 ^ M * ‖z - z₀‖ ^ M := by
          have hC : 0 ≤ C := by
            have := (norm_nonneg _).trans hfz
            exact nonneg_of_mul_nonneg_left this (by positivity)
          gcongr
  have hgr' : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      ‖g z‖ ≤ max A 1 * Real.exp ((|B| / (Real.pi / (2 * (b - a)))) *
        Real.exp (Real.pi / (2 * (b - a)) * |z.im|)) := by
    intro z hza hzb him
    have hc : 0 < Real.pi / (2 * (b - a)) := by have := Real.pi_pos; apply div_pos this; linarith
    have hl := hlow z hza
    have h1 : 1 ≤ ‖z - z₀‖ := le_trans (by linarith [abs_nonneg z.im] : (1 : ℝ) ≤ (1 + |z.im|) / 2) hl
    have hgle : ‖g z‖ ≤ ‖f z‖ := by
      simp only [hg_def, norm_div, norm_pow]
      exact div_le_self (norm_nonneg _) (one_le_pow₀ h1)
    have hBt : B * |z.im| ≤ |B| / (Real.pi / (2 * (b - a))) *
        Real.exp (Real.pi / (2 * (b - a)) * |z.im|) := by
      have hx := Real.add_one_le_exp (Real.pi / (2 * (b - a)) * |z.im|)
      have : B * |z.im| ≤ |B| * |z.im| := mul_le_mul_of_nonneg_right (le_abs_self B) (abs_nonneg _)
      calc B * |z.im| ≤ |B| * |z.im| := this
        _ = |B| / (Real.pi / (2 * (b - a))) * (Real.pi / (2 * (b - a)) * |z.im|) := by
            rw [← mul_assoc, div_mul_cancel₀ _ hc.ne']
        _ ≤ |B| / (Real.pi / (2 * (b - a))) * Real.exp (Real.pi / (2 * (b - a)) * |z.im|) := by
            gcongr; linarith
    calc ‖g z‖ ≤ ‖f z‖ := hgle
      _ ≤ A * Real.exp (B * |z.im|) := hgr z hza hzb him
      _ ≤ max A 1 * Real.exp (B * |z.im|) := by gcongr; exact le_max_left _ _
      _ ≤ max A 1 * Real.exp ((|B| / (Real.pi / (2 * (b - a)))) *
            Real.exp (Real.pi / (2 * (b - a)) * |z.im|)) := by
          gcongr
  intro z hza hzb
  have hPL := PhragmenLindelof.vertical_strip (f := g) (C := C * 2 ^ M) (z := z) hgd
    ⟨Real.pi / (2 * (b - a)), by
      have := Real.pi_pos
      rw [div_lt_div_iff_of_pos_left this (by linarith) (by linarith)]
      linarith,
     |B| / (Real.pi / (2 * (b - a))), by
      refine IsBigO.of_bound (max A 1) ?_
      filter_upwards [mem_inf_of_left (tendsto_comap.eventually (eventually_ge_atTop 1)),
        mem_inf_of_right (mem_principal_self _)] with w hw1 hw2
      have hw2' : a < w.re ∧ w.re < b := hw2
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hgr' w hw2'.1.le hw2'.2.le hw1⟩
    (fun w hw => hgb w (Or.inl hw)) (fun w hw => hgb w (Or.inr hw)) hza hzb
  have hl := hup z hzb hza
  have hgz : f z = g z * (z - z₀) ^ M := by
    simp only [hg_def]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ (hne z hza))]
  rw [hgz, norm_mul, norm_pow]
  have hC : 0 ≤ C * 2 ^ M := (norm_nonneg _).trans hPL
  calc ‖g z‖ * ‖z - z₀‖ ^ M ≤ C * 2 ^ M * ((b - a + 1) * (1 + |z.im|)) ^ M := by
        gcongr
    _ = C * 2 ^ M * (b - a + 1) ^ M * (1 + |z.im|) ^ M := by rw [mul_pow]; ring

/-- **The Mellin transform is bounded in a vertical strip** where it converges on both edges. -/
theorem norm_mellin_le_strip {f : ℝ → ℂ} {a b : ℝ} (ha : MellinConvergent f a)
    (hb : MellinConvergent f b) {s : ℂ} (hs1 : a ≤ s.re) (hs2 : s.re ≤ b) :
    ‖mellin f s‖ ≤ (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((a : ℂ) - 1) • f t‖) +
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((b : ℂ) - 1) • f t‖ := by
  unfold mellin
  rw [← integral_add (Integrable.norm ha) (Integrable.norm hb)]
  refine norm_integral_le_of_norm_le (Integrable.add (Integrable.norm ha) (Integrable.norm hb)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  have ht' : (0 : ℝ) < t := ht
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht']
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rcases le_or_gt t 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge ht' h (by linarith : a - 1 ≤ s.re - 1)
    linarith [Real.rpow_nonneg ht'.le (b - 1)]
  · have := Real.rpow_le_rpow_of_exponent_le h.le (by linarith : s.re - 1 ≤ b - 1)
    linarith [Real.rpow_nonneg ht'.le (a - 1)]

/-- The Gamma quotient `Γ(4/3 − s)Γ(5/3 − s)/(Γ(s + 1/3)Γ(s + 2/3))` of the functional equation; at
`s = 1/2 − t` it is the quotient `Γ(7/6 + t)Γ(5/6 + t)/(Γ(7/6 − t)Γ(5/6 − t))` of the paper's (6.6). -/
def gRatio (s : ℂ) : ℂ :=
  Gamma (4 / 3 - s) * Gamma (5 / 3 - s) * (Gamma (s + 1 / 3))⁻¹ * (Gamma (s + 2 / 3))⁻¹

theorem differentiableOn_gRatio : DifferentiableOn ℂ gRatio {s | s.re < 4 / 3} := by
  intro s hs
  have hs' : s.re < 4 / 3 := hs
  apply DifferentiableAt.differentiableWithinAt
  have h1 : DifferentiableAt ℂ (fun s : ℂ => Gamma (4 / 3 - s)) s := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp s
      ((differentiableAt_const _).sub differentiableAt_id)
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h2 : DifferentiableAt ℂ (fun s : ℂ => Gamma (5 / 3 - s)) s := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp s
      ((differentiableAt_const _).sub differentiableAt_id)
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h3 : DifferentiableAt ℂ (fun s : ℂ => (Gamma (s + 1 / 3))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma _).comp s (differentiableAt_id.add_const _)
  have h4 : DifferentiableAt ℂ (fun s : ℂ => (Gamma (s + 2 / 3))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma _).comp s (differentiableAt_id.add_const _)
  exact ((h1.mul h2).mul h3).mul h4

/-- `|Γ(4/3 − s)Γ(5/3 − s)/(Γ(s + 1/3)Γ(s + 2/3))| = 1` on `Re s = 1/2`: the factors pair off as complex
conjugates. -/
theorem norm_gRatio_half {s : ℂ} (hs : s.re = 1 / 2) : ‖gRatio s‖ = 1 := by
  have c1 : conj (1 / 3 : ℂ) = 1 / 3 := Complex.conj_eq_iff_re.2 (by norm_num)
  have c2 : conj (2 / 3 : ℂ) = 2 / 3 := Complex.conj_eq_iff_re.2 (by norm_num)
  have e1 : (4 / 3 : ℂ) - s = conj (s + 1 / 3) := by
    rw [map_add, c1]; apply Complex.ext <;> simp [hs]
    norm_num
  have e2 : (5 / 3 : ℂ) - s = conj (s + 2 / 3) := by
    rw [map_add, c2]; apply Complex.ext <;> simp [hs]
    norm_num
  have h1 : ‖Gamma (s + 1 / 3)‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num))
  have h2 : ‖Gamma (s + 2 / 3)‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num))
  unfold gRatio
  rw [e1, e2, Complex.Gamma_conj, Complex.Gamma_conj, norm_mul, norm_mul, norm_mul, Complex.norm_conj,
    Complex.norm_conj, norm_inv, norm_inv]
  generalize ‖Gamma (s + 1 / 3)‖ = a at h1 ⊢
  generalize ‖Gamma (s + 2 / 3)‖ = b at h2 ⊢
  field_simp

theorem norm_le_of_re_im {x : ℂ} {K y : ℝ} (hK : 0 ≤ K) (hre : |x.re| ≤ K) (him : |x.im| = |y|) :
    ‖x‖ ≤ (K + 1) * (1 + |y|) := by
  have := Complex.norm_le_abs_re_add_abs_im x
  nlinarith [abs_nonneg y]

theorem norm_prod_range_le {f : ℕ → ℂ} {B : ℝ} (k : ℕ) (hf : ∀ j < k, ‖f j‖ ≤ B) :
    ‖∏ j ∈ Finset.range k, f j‖ ≤ B ^ k := by
  rw [norm_prod]
  calc ∏ j ∈ Finset.range k, ‖f j‖ ≤ ∏ _j ∈ Finset.range k, B :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j hj => hf j (Finset.mem_range.1 hj)
    _ = B ^ k := by rw [Finset.prod_const, Finset.card_range]

/-- On `Re s = 1/2 − k`, `|Γ(4/3 − s)Γ(5/3 − s)/(Γ(s + 1/3)Γ(s + 2/3))| ≤ ((k + 3)(1 + |Im s|))^{4k}`:
`Γ(z + 1) = zΓ(z)` moves each factor to the line `Re s = 1/2`, at the cost of `4k` linear factors. -/
theorem norm_gRatio_le (k : ℕ) {s : ℂ} (hs : s.re = 1 / 2 - k) :
    ‖gRatio s‖ ≤ (((k : ℝ) + 3) * (1 + |s.im|)) ^ (4 * k) := by
  set s₀ : ℂ := s + k with hs₀
  have hs₀re : s₀.re = 1 / 2 := by simp [hs₀, hs]
  have hj0 : ∀ j : ℕ, (0 : ℝ) ≤ j := fun j => Nat.cast_nonneg j
  have hA : Gamma (4 / 3 - s) = Gamma (4 / 3 - s₀) * ∏ j ∈ Finset.range k, (4 / 3 - s₀ + j) := by
    rw [← Gamma_add_nat_eq _ k fun j h => ?_]
    · congr 1; rw [hs₀]; ring
    · have := congrArg Complex.re h
      simp [hs₀re] at this
      linarith [hj0 j]
  have hB : Gamma (5 / 3 - s) = Gamma (5 / 3 - s₀) * ∏ j ∈ Finset.range k, (5 / 3 - s₀ + j) := by
    rw [← Gamma_add_nat_eq _ k fun j h => ?_]
    · congr 1; rw [hs₀]; ring
    · have := congrArg Complex.re h
      simp [hs₀re] at this
      linarith [hj0 j]
  have hne : ∀ (c : ℝ) (j : ℕ), (6 * c = 2 ∨ 6 * c = 4) → s + c + j ≠ 0 := by
    intro c j hc h
    have := congrArg Complex.re h
    simp [hs] at this
    rcases hc with hc | hc
    · have h7 : ((6 * j + 5 : ℕ) : ℝ) = ((6 * k : ℕ) : ℝ) := by push_cast; linarith
      have h8 : 6 * j + 5 = 6 * k := by exact_mod_cast h7
      omega
    · have h7 : ((6 * j + 7 : ℕ) : ℝ) = ((6 * k : ℕ) : ℝ) := by push_cast; linarith
      have h8 : 6 * j + 7 = 6 * k := by exact_mod_cast h7
      omega
  have hC : Gamma (s₀ + 1 / 3) = Gamma (s + 1 / 3) * ∏ j ∈ Finset.range k, (s + 1 / 3 + j) := by
    rw [← Gamma_add_nat_eq _ k fun j => ?_]
    · congr 1; rw [hs₀]; ring
    · have := hne (1 / 3) j (Or.inl (by norm_num)); push_cast at this; exact this
  have hD : Gamma (s₀ + 2 / 3) = Gamma (s + 2 / 3) * ∏ j ∈ Finset.range k, (s + 2 / 3 + j) := by
    rw [← Gamma_add_nat_eq _ k fun j => ?_]
    · congr 1; rw [hs₀]; ring
    · have := hne (2 / 3) j (Or.inr (by norm_num)); push_cast at this; exact this
  have hPC : (∏ j ∈ Finset.range k, (s + 1 / 3 + j)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => by
    have := hne (1 / 3) j (Or.inl (by norm_num)); push_cast at this; exact this
  have hPD : (∏ j ∈ Finset.range k, (s + 2 / 3 + j)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => by
    have := hne (2 / 3) j (Or.inr (by norm_num)); push_cast at this; exact this
  have hC' : (Gamma (s + 1 / 3))⁻¹ = (Gamma (s₀ + 1 / 3))⁻¹ * ∏ j ∈ Finset.range k, (s + 1 / 3 + j) := by
    rw [hC, mul_inv, mul_assoc, inv_mul_cancel₀ hPC, mul_one]
  have hD' : (Gamma (s + 2 / 3))⁻¹ = (Gamma (s₀ + 2 / 3))⁻¹ * ∏ j ∈ Finset.range k, (s + 2 / 3 + j) := by
    rw [hD, mul_inv, mul_assoc, inv_mul_cancel₀ hPD, mul_one]
  have heq : gRatio s = gRatio s₀ * ((∏ j ∈ Finset.range k, (4 / 3 - s₀ + j)) *
      (∏ j ∈ Finset.range k, (5 / 3 - s₀ + j)) * (∏ j ∈ Finset.range k, (s + 1 / 3 + j)) *
      ∏ j ∈ Finset.range k, (s + 2 / 3 + j)) := by
    unfold gRatio; rw [hA, hB, hC', hD']; ring
  have hk0 : (0 : ℝ) ≤ k + 2 := by positivity
  have him : s₀.im = s.im := by simp [hs₀]
  have hb : ∀ (x : ℕ → ℂ), (∀ j < k, |(x j).re| ≤ k + 2 ∧ |(x j).im| = |s.im|) →
      ‖∏ j ∈ Finset.range k, x j‖ ≤ (((k : ℝ) + 3) * (1 + |s.im|)) ^ k := by
    intro x hx
    refine norm_prod_range_le k fun j hj => ?_
    have := norm_le_of_re_im hk0 (hx j hj).1 (hx j hj).2
    linarith
  have hjk : ∀ j < k, (j : ℝ) + 1 ≤ k := fun j hj => by exact_mod_cast hj
  have b1 := hb (fun j => 4 / 3 - s₀ + j) fun j hj => by
    constructor
    · simp [hs₀re]; rw [abs_le]; constructor <;> linarith [hj0 j, hjk j hj]
    · simp [him]
  have b2 := hb (fun j => 5 / 3 - s₀ + j) fun j hj => by
    constructor
    · simp [hs₀re]; rw [abs_le]; constructor <;> linarith [hj0 j, hjk j hj]
    · simp [him]
  have b3 := hb (fun j => s + 1 / 3 + j) fun j hj => by
    constructor
    · simp [hs]; rw [abs_le]; constructor <;> linarith [hj0 j, hjk j hj]
    · simp
  have b4 := hb (fun j => s + 2 / 3 + j) fun j hj => by
    constructor
    · simp [hs]; rw [abs_le]; constructor <;> linarith [hj0 j, hjk j hj]
    · simp
  rw [heq, norm_mul, norm_gRatio_half hs₀re, one_mul, norm_mul, norm_mul, norm_mul]
  have hB0 : (0 : ℝ) ≤ ((k : ℝ) + 3) * (1 + |s.im|) := by positivity
  calc _ ≤ (((k : ℝ) + 3) * (1 + |s.im|)) ^ k * (((k : ℝ) + 3) * (1 + |s.im|)) ^ k *
        (((k : ℝ) + 3) * (1 + |s.im|)) ^ k * (((k : ℝ) + 3) * (1 + |s.im|)) ^ k := by
        gcongr
    _ = _ := by ring

/-- **The Gamma quotient is polynomially bounded in the strip** `1/2 − k ≤ Re s ≤ 1/2`, with exponent
`4k`, by Phragmén–Lindelöf between its two edges. -/
theorem exists_gRatio_strip (k : ℕ) :
    ∃ C, ∀ s : ℂ, 1 / 2 - k ≤ s.re → s.re ≤ 1 / 2 → ‖gRatio s‖ ≤ C * (1 + |s.im|) ^ (4 * k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, fun s h1 h2 => ?_⟩
    have : s.re = 1 / 2 := by simp at h1; linarith
    rw [norm_gRatio_half this]; simp
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    obtain ⟨C1, hC1, hΓ1⟩ := exists_norm_Gamma_le (5 / 6) (5 / 6 + k)
    obtain ⟨C2, hC2, hΓ2⟩ := exists_norm_Gamma_le (7 / 6) (7 / 6 + k)
    obtain ⟨C3, hC3, hΓ3⟩ := exists_norm_inv_Gamma_le (5 / 6 - k) (5 / 6)
    obtain ⟨C4, hC4, hΓ4⟩ := exists_norm_inv_Gamma_le (7 / 6 - k) (7 / 6)
    have hd : DifferentiableOn ℂ gRatio (re ⁻¹' Icc (1 / 2 - (k : ℝ)) (1 / 2)) :=
      differentiableOn_gRatio.mono fun s hs => by
        have := hs.2
        show s.re < 4 / 3
        linarith
    have hPL := poly_bound_strip (C := ((k : ℝ) + 3) ^ (4 * k)) (A := C1 * C2 * C3 * C4)
      (B := 2 * Real.pi) hd (by linarith) (4 * k)
      (fun z hz => by
        have := norm_gRatio_le k hz
        rwa [mul_pow] at this)
      (fun z hz => by
        rw [norm_gRatio_half hz]
        have h1 : (1 : ℝ) ≤ ((k : ℝ) + 3) ^ (4 * k) := one_le_pow₀ (by linarith)
        have h2 : (1 : ℝ) ≤ (1 + |z.im|) ^ (4 * k) := one_le_pow₀ (by linarith [abs_nonneg z.im])
        nlinarith)
      (fun z hz1 hz2 him => by
        have e1 : |(4 / 3 - z).im| = |z.im| := by simp
        have e2 : |(5 / 3 - z).im| = |z.im| := by simp
        have e3 : (z + 1 / 3).im = z.im := by simp
        have e4 : (z + 2 / 3).im = z.im := by simp
        have g1 := hΓ1 (4 / 3 - z) (by simp; linarith) (by simp; linarith) (by rw [e1]; exact him)
        have g2 := hΓ2 (5 / 3 - z) (by simp; linarith) (by simp; linarith) (by rw [e2]; exact him)
        have g3 := hΓ3 (z + 1 / 3) (by simp; linarith) (by simp; linarith) (by rw [e3]; exact him)
        have g4 := hΓ4 (z + 2 / 3) (by simp; linarith) (by simp; linarith) (by rw [e4]; exact him)
        rw [e3] at g3
        rw [e4] at g4
        unfold gRatio
        rw [norm_mul, norm_mul, norm_mul]
        calc _ ≤ C1 * C2 * (C3 * Real.exp (Real.pi * |z.im|)) * (C4 * Real.exp (Real.pi * |z.im|)) := by
              gcongr
          _ = C1 * C2 * C3 * C4 * Real.exp (2 * Real.pi * |z.im|) := by
              rw [show 2 * Real.pi * |z.im| = Real.pi * |z.im| + Real.pi * |z.im| by ring, Real.exp_add]
              ring)
    exact ⟨_, fun s h1 h2 => by
      have := hPL s h1 h2
      calc ‖gRatio s‖ ≤ _ := this
        _ = ((k : ℝ) + 3) ^ (4 * k) * 2 ^ (4 * k) * (1 / 2 - (1 / 2 - k) + 1) ^ (4 * k) *
            (1 + |s.im|) ^ (4 * k) := rfl⟩

/-- The absolute Dirichlet series of a derivative series converges on `Re w = σ ≥ 5/3`. -/
theorem summable_dSer_abs {Kc C : ℝ} {d φ : 𝓞 K → ℂ} (h : ThetaSupp Kc d)
    (hφ : ∀ m, ‖φ m‖ ≤ C * ‖σO m‖) {σ : ℝ} (hσ : 5 / 3 ≤ σ) :
    Summable fun m : 𝓞 K => ‖d m‖ * ‖φ m‖ * (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * σ + 1)) := by
  have hKc := h.1
  refine summable_O_of_le (fun m => by positivity)
    (A := Kc * |C| * (4 * Real.pi / 9) ^ (-(2 * σ + 1)) * 8) fun m => ?_
  by_cases hm : d m = 0
  · rw [hm, norm_zero, zero_mul, zero_mul]; positivity
  obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm
  have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb
  have h1 := one_le_norm_σO hm0
  have hn0 : 0 < ‖σO m‖ := by linarith
  have hd := norm_le_of_thetaSupp h m
  have hφm : ‖φ m‖ ≤ |C| * ‖σO m‖ :=
    (hφ m).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
  have hsplit : (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * σ + 1)) =
      (4 * Real.pi / 9) ^ (-(2 * σ + 1)) * ‖σO m‖ ^ (-(2 * σ + 1)) := by
    rw [show 4 * Real.pi * ‖σO m‖ / 9 = 4 * Real.pi / 9 * ‖σO m‖ by ring,
      Real.mul_rpow (by positivity) hn0.le]
  have hexp : ‖σO m‖ ^ (1 / 3 : ℝ) * ‖σO m‖ * ‖σO m‖ ^ (-(2 * σ + 1)) ≤ (‖σO m‖ ^ 3)⁻¹ := by
    rw [show ‖σO m‖ ^ (1 / 3 : ℝ) * ‖σO m‖ = ‖σO m‖ ^ (1 / 3 + 1 : ℝ) by
        rw [Real.rpow_add hn0, Real.rpow_one],
      ← Real.rpow_add hn0]
    calc ‖σO m‖ ^ (1 / 3 + 1 + -(2 * σ + 1)) ≤ ‖σO m‖ ^ (-3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = (‖σO m‖ ^ 3)⁻¹ := by rw [Real.rpow_neg hn0.le]; norm_cast
  have hic := inv_cube_le h1
  calc ‖d m‖ * ‖φ m‖ * (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * σ + 1))
      ≤ (Kc * ‖σO m‖ ^ (1 / 3 : ℝ)) * (|C| * ‖σO m‖) *
          ((4 * Real.pi / 9) ^ (-(2 * σ + 1)) * ‖σO m‖ ^ (-(2 * σ + 1))) := by
        rw [hsplit]; gcongr
    _ = Kc * |C| * (4 * Real.pi / 9) ^ (-(2 * σ + 1)) *
          (‖σO m‖ ^ (1 / 3 : ℝ) * ‖σO m‖ * ‖σO m‖ ^ (-(2 * σ + 1))) := by ring
    _ ≤ Kc * |C| * (4 * Real.pi / 9) ^ (-(2 * σ + 1)) * (8 * (1 + ‖σO m‖) ^ (-3 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hexp.trans hic) (by positivity)
    _ = _ := by ring

/-- On `Re w = σ ≥ 5/3`, `|∫_0^∞ G(v)v^{2w−1} dv| ≤ |Γ(w + 1/3)Γ(w + 2/3)|·2^{2σ−1}Σ_m|d(m)φ(m)|(4π|m|/9)^{−(2σ+1)}`. -/
theorem norm_mellin_dSer_le {Kc C : ℝ} {d φ : 𝓞 K → ℂ} (h : ThetaSupp Kc d)
    (hφ : ∀ m, ‖φ m‖ ≤ C * ‖σO m‖) {w : ℂ} (hw : 5 / 3 ≤ w.re) :
    ‖mellin (dSer d φ) (2 * w)‖ ≤ ‖Gamma (w + 1 / 3) * Gamma (w + 2 / 3)‖ *
      (2 ^ (2 * w.re - 1) *
        ∑' m : 𝓞 K, ‖d m‖ * ‖φ m‖ * (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * w.re + 1))) := by
  rw [mellin_dSer h hφ hw]
  have hs := summable_dSer_abs h hφ hw
  have e : ∀ m : 𝓞 K, d m * φ m * (2 ^ (2 * w - 1) * Gamma (w + 1 / 3) * Gamma (w + 2 / 3) *
      (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * w + 1))) =
      Gamma (w + 1 / 3) * Gamma (w + 2 / 3) * (2 ^ (2 * w - 1) * (d m * φ m *
        (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * w + 1)))) := fun m => by ring
  rw [tsum_congr e, tsum_mul_left, tsum_mul_left]
  have h2 : ‖(2 : ℂ) ^ (2 * w - 1)‖ = 2 ^ (2 * w.re - 1) := by
    have := Complex.norm_natCast_cpow_of_pos (n := 2) (by norm_num) (2 * w - 1)
    simpa using this
  have hterm : ∀ m : 𝓞 K, ‖d m * φ m * (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * w + 1))‖ =
      ‖d m‖ * ‖φ m‖ * (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * w.re + 1)) := by
    intro m
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_nonneg (by positivity)
      (by simp; linarith)]
    simp
  rw [norm_mul, norm_mul, norm_mul, h2]
  gcongr
  calc ‖∑' m : 𝓞 K, d m * φ m * (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * w + 1))‖
      ≤ ∑' m : 𝓞 K, ‖d m * φ m * (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * w + 1))‖ :=
        norm_tsum_le_tsum_norm (by simpa only [hterm] using hs)
    _ = _ := tsum_congr hterm

/-- `‖Σ_i α_i Σ_k β_k X_{ik}‖ ≤ Σ_i ‖α_i‖ Σ_k ‖β_k‖ Z_{ik}` when `‖X_{ik}‖ ≤ Z_{ik}`. -/
theorem norm_nested_sum_le {ι κ : Type*} (S : Finset ι) (T : Finset κ) (α : ι → ℂ) (β : κ → ℂ)
    (X : ι → κ → ℂ) (Z : ι → κ → ℝ) (hX : ∀ i ∈ S, ∀ k ∈ T, ‖X i k‖ ≤ Z i k) :
    ‖∑ i ∈ S, α i * ∑ k ∈ T, β k * X i k‖ ≤ ∑ i ∈ S, ‖α i‖ * ∑ k ∈ T, ‖β k‖ * Z i k := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_))
    (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hX i hi k hk) (norm_nonneg _)

/-- **Polynomial bounds in a vertical strip** (the paper's Phragmén–Lindelöf step): under the
hypotheses of `mellin_FE`, `|𝒥(s)/(Γ(s + 1/3)Γ(s + 2/3))| ≤ C(1 + |Im s|)^{12}` for `−5/2 ≤ Re s ≤ 2`.
On `Re s = 2` it is a Dirichlet series; on `Re s = −5/2` the functional equation gives a Dirichlet
series at `1 − s` times the Gamma quotient `gRatio`; in between, `𝒥` is bounded and `1/Γ` grows at
most exponentially. -/
theorem poly_bound_FE {ι κ : Type*} (S : Finset ι) (T : Finset κ) {Ka Ca Cc : ℝ} {a φa φc : 𝓞 K → ℂ}
    (ha : ThetaSupp Ka a) (hφa : ∀ m, ‖φa m‖ ≤ Ca * ‖σO m‖) (hφc : ∀ m, ‖φc m‖ ≤ Cc * ‖σO m‖)
    (α : ι → ℂ) (β : κ → ℂ) (γ : ι → κ → ℂ) (dd : ι → κ → 𝓞 K → ℂ) (cc : ι → κ → 𝓞 K)
    (Kd : ι → κ → ℝ) (hdd : ∀ i ∈ S, ∀ k ∈ T, ThetaSupp (Kd i k) (dd i k) ∧ σO (cc i k) ≠ 0)
    (hid : ∀ v : ℝ, 0 < v → dSer a φa v = ∑ i ∈ S, α i * ∑ k ∈ T, β k * (γ i k *
      (-(σO (cc i k) ^ 2 * (v : ℂ) ^ 2)⁻¹ *
        dSer (dd i k) φc (Complex.normSq (σO (cc i k)) * v)⁻¹))) :
    ∃ C, ∀ s : ℂ, -5 / 2 ≤ s.re → s.re ≤ 2 →
      ‖mellin (dSer a φa) (2 * s) * (Gamma (s + 1 / 3))⁻¹ * (Gamma (s + 2 / 3))⁻¹‖ ≤
        C * (1 + |s.im|) ^ 12 := by
  obtain ⟨hconv, hdiff, hFE⟩ := mellin_FE S T ha hφa hφc α β γ dd cc Kd hdd hid
  set f : ℂ → ℂ := fun s => mellin (dSer a φa) (2 * s) * (Gamma (s + 1 / 3))⁻¹ *
    (Gamma (s + 2 / 3))⁻¹ with hf
  have hfd : Differentiable ℂ f := fun s =>
    ((hdiff.comp (differentiable_id.const_mul 2) s).mul
      ((Complex.differentiable_one_div_Gamma _).comp s (differentiableAt_id.add_const _))).mul
      ((Complex.differentiable_one_div_Gamma _).comp s (differentiableAt_id.add_const _))
  -- the edge `Re s = 2`
  set B₁ : ℝ := 2 ^ (2 * 2 - 1 : ℝ) *
    ∑' m : 𝓞 K, ‖a m‖ * ‖φa m‖ * (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * 2 + 1 : ℝ)) with hB₁
  have hB₁0 : 0 ≤ B₁ := mul_nonneg (by positivity) (tsum_nonneg fun m => by positivity)
  have hedge1 : ∀ s : ℂ, s.re = 2 → ‖f s‖ ≤ B₁ := by
    intro s hs
    have hm := norm_mellin_dSer_le ha hφa (w := s) (by rw [hs]; norm_num)
    rw [hs] at hm
    have hg1 : Gamma (s + 1 / 3) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num)
    have hg2 : Gamma (s + 2 / 3) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num)
    simp only [hf]
    rw [norm_mul, norm_mul, norm_inv, norm_inv]
    have hn1 : 0 < ‖Gamma (s + 1 / 3)‖ := norm_pos_iff.2 hg1
    have hn2 : 0 < ‖Gamma (s + 2 / 3)‖ := norm_pos_iff.2 hg2
    rw [norm_mul] at hm
    calc ‖mellin (dSer a φa) (2 * s)‖ * ‖Gamma (s + 1 / 3)‖⁻¹ * ‖Gamma (s + 2 / 3)‖⁻¹
        ≤ ‖Gamma (s + 1 / 3)‖ * ‖Gamma (s + 2 / 3)‖ * B₁ * ‖Gamma (s + 1 / 3)‖⁻¹ *
            ‖Gamma (s + 2 / 3)‖⁻¹ := by gcongr
      _ = B₁ := by
        generalize ‖Gamma (s + 1 / 3)‖ = A at hn1 ⊢
        generalize ‖Gamma (s + 2 / 3)‖ = B at hn2 ⊢
        field_simp
  -- the edge `Re s = −5/2`
  set N : ι → κ → ℝ := fun i k => Complex.normSq (σO (cc i k)) with hN
  set Y : ι → κ → ℝ := fun i k => ‖γ i k‖ * (‖(σO (cc i k) ^ 2)⁻¹‖ * (N i k ^ (7 : ℝ) *
    (2 ^ (2 * (7 / 2) - 1 : ℝ) * ∑' m : 𝓞 K, ‖dd i k m‖ * ‖φc m‖ *
      (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * (7 / 2) + 1 : ℝ))))) with hY
  set B₂ : ℝ := ∑ i ∈ S, ‖α i‖ * ∑ k ∈ T, ‖β k‖ * Y i k with hB₂
  have hY0 : ∀ i k, 0 ≤ Y i k := fun i k =>
    mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg
      (Real.rpow_nonneg (Complex.normSq_nonneg _) _)
      (mul_nonneg (by positivity) (tsum_nonneg fun m => by positivity))))
  have hB₂0 : 0 ≤ B₂ := Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (hY0 i k))
  have hedge2 : ∀ s : ℂ, s.re = -5 / 2 → ‖f s‖ ≤ B₂ * ‖gRatio s‖ := by
    intro s hs
    have hFs := hFE s (by rw [hs]; norm_num)
    simp only [hf]
    rw [hFs]
    set Γn : ℝ := ‖Gamma (4 / 3 - s) * Gamma (5 / 3 - s)‖ with hΓn
    have hX : ∀ i ∈ S, ∀ k ∈ T, ‖γ i k * (-(σO (cc i k) ^ 2)⁻¹ *
        ((Complex.normSq (σO (cc i k)) : ℂ) ^ (2 - 2 * s) * mellin (dSer (dd i k) φc) (2 - 2 * s)))‖ ≤
        Y i k * Γn := by
      intro i hi k hk
      obtain ⟨hd, hc⟩ := hdd i hi k hk
      have hNpos : 0 < N i k := Complex.normSq_pos.2 hc
      have hm := norm_mellin_dSer_le hd hφc (w := 1 - s) (by simp [hs]; norm_num)
      have hre : (1 - s).re = 7 / 2 := by simp [hs]; norm_num
      rw [hre, show (1 - s) + 1 / 3 = 4 / 3 - s by ring, show (1 - s) + 2 / 3 = 5 / 3 - s by ring,
        show 2 * (1 - s) = 2 - 2 * s by ring] at hm
      have hNs : ‖((Complex.normSq (σO (cc i k)) : ℝ) : ℂ) ^ (2 - 2 * s)‖ = N i k ^ (7 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
        congr 1
        simp [hs]; norm_num
      rw [norm_mul, norm_mul, norm_mul, norm_neg, hNs]
      simp only [hY]
      calc ‖γ i k‖ * (‖(σO (cc i k) ^ 2)⁻¹‖ * (N i k ^ (7 : ℝ) * ‖mellin (dSer (dd i k) φc) (2 - 2 * s)‖))
          ≤ ‖γ i k‖ * (‖(σO (cc i k) ^ 2)⁻¹‖ * (N i k ^ (7 : ℝ) * (Γn *
              (2 ^ (2 * (7 / 2) - 1 : ℝ) * ∑' m : 𝓞 K, ‖dd i k m‖ * ‖φc m‖ *
                (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * (7 / 2) + 1 : ℝ)))))) := by
            gcongr
        _ = _ := by ring
    have hsum := norm_nested_sum_le S T α β _ _ hX
    have hfac : ∑ i ∈ S, ‖α i‖ * ∑ k ∈ T, ‖β k‖ * (Y i k * Γn) = B₂ * Γn := by
      rw [hB₂, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hfac] at hsum
    rw [norm_mul, norm_mul]
    have hgr : ‖gRatio s‖ = Γn * ‖(Gamma (s + 1 / 3))⁻¹‖ * ‖(Gamma (s + 2 / 3))⁻¹‖ := by
      unfold gRatio; rw [hΓn, norm_mul, norm_mul, norm_mul]
    rw [hgr]
    calc _ ≤ B₂ * Γn * ‖(Gamma (s + 1 / 3))⁻¹‖ * ‖(Gamma (s + 2 / 3))⁻¹‖ := by gcongr
      _ = _ := by ring
  -- growth inside the strip
  obtain ⟨C3, hC3, hΓ3⟩ := exists_norm_inv_Gamma_le (-5 / 2 + 1 / 3) (2 + 1 / 3)
  obtain ⟨C4, hC4, hΓ4⟩ := exists_norm_inv_Gamma_le (-5 / 2 + 2 / 3) (2 + 2 / 3)
  set M₀ : ℝ := (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (((-5 : ℝ) : ℂ) - 1) • dSer a φa t‖) +
    ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (((4 : ℝ) : ℂ) - 1) • dSer a φa t‖ with hM₀
  have hgrowth : ∀ z : ℂ, -5 / 2 ≤ z.re → z.re ≤ 2 → 1 ≤ |z.im| →
      ‖f z‖ ≤ M₀ * C3 * C4 * Real.exp (2 * Real.pi * |z.im|) := by
    intro z hz1 hz2 him
    have hm : ‖mellin (dSer a φa) (2 * z)‖ ≤ M₀ :=
      norm_mellin_le_strip (hconv _) (hconv _) (by simp; linarith) (by simp; linarith)
    have e3 : (z + 1 / 3).im = z.im := by simp
    have e4 : (z + 2 / 3).im = z.im := by simp
    have g3 := hΓ3 (z + 1 / 3) (by simp; linarith) (by simp; linarith) (by rw [e3]; exact him)
    have g4 := hΓ4 (z + 2 / 3) (by simp; linarith) (by simp; linarith) (by rw [e4]; exact him)
    rw [e3] at g3
    rw [e4] at g4
    simp only [hf]
    rw [norm_mul, norm_mul]
    calc _ ≤ M₀ * (C3 * Real.exp (Real.pi * |z.im|)) * (C4 * Real.exp (Real.pi * |z.im|)) := by
          gcongr
      _ = M₀ * C3 * C4 * Real.exp (2 * Real.pi * |z.im|) := by
          rw [show 2 * Real.pi * |z.im| = Real.pi * |z.im| + Real.pi * |z.im| by ring, Real.exp_add]
          ring
  -- Phragmén–Lindelöf
  set C₁ : ℝ := B₁ + B₂ * 6 ^ 12 with hC₁
  have hPL := poly_bound_strip (f := f) (a := -5 / 2) (b := 2) (C := C₁) (A := M₀ * C3 * C4)
    (B := 2 * Real.pi) hfd.differentiableOn (by norm_num) 12
    (fun z hz => by
      have h1 := hedge2 z hz
      have h2 := norm_gRatio_le 3 (s := z) (by rw [hz]; norm_num)
      have h3 : (1 : ℝ) ≤ (1 + |z.im|) ^ 12 := one_le_pow₀ (by linarith [abs_nonneg z.im])
      calc ‖f z‖ ≤ B₂ * ‖gRatio z‖ := h1
        _ ≤ B₂ * ((((3 : ℕ) : ℝ) + 3) * (1 + |z.im|)) ^ (4 * 3) := by gcongr
        _ = B₂ * 6 ^ 12 * (1 + |z.im|) ^ 12 := by rw [mul_pow]; norm_num; ring
        _ ≤ C₁ * (1 + |z.im|) ^ 12 := by
          gcongr
          rw [hC₁]; linarith)
    (fun z hz => by
      have h1 := hedge1 z hz
      have h3 : (1 : ℝ) ≤ (1 + |z.im|) ^ 12 := one_le_pow₀ (by linarith [abs_nonneg z.im])
      have h4 : 0 ≤ B₂ * 6 ^ 12 := by positivity
      calc ‖f z‖ ≤ B₁ := h1
        _ ≤ C₁ := by rw [hC₁]; linarith
        _ ≤ C₁ * (1 + |z.im|) ^ 12 := le_mul_of_one_le_right (by positivity) h3)
    hgrowth
  exact ⟨C₁ * 2 ^ 12 * (2 - -5 / 2 + 1) ^ 12, fun s h1 h2 => hPL s h1 h2⟩

open Classical in
/-- **Polynomial bounds for the twisted `θ̄`** (the paper's "`polynomial bounds in |Im s|`" for `𝒯(s, Ψ)`,
inside the strip by Phragmén–Lindelöf): with the data of round 373's `twisted_theta_dbar`,
`|𝒥(s)/(Γ(s + 1/3)Γ(s + 2/3))| ≤ C(1 + |Im s|)^{12}` for `−5/2 ≤ Re s ≤ 2`. -/
theorem twisted_theta_poly {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (φ₀ : 𝓞 K → ℂ)
    (hφ : ∀ z u, φ₀ (z + L * u) = φ₀ z) (hφ0 : φ₀ 0 = 0) (Ps : Finset Pr) (hPs : ∀ P ∈ Ps, L ∉ P.1)
    (j : Pr → ℕ) :
    ∃ C, ∀ s : ℂ, -5 / 2 ≤ s.re → s.re ≤ 2 →
      ‖mellin (dSer (fun m => twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m *
        conj (τ (-m))) fun m => 2 * Real.pi * I * conj (σO m) / 9) (2 * s) *
        (Gamma (s + 1 / 3))⁻¹ * (Gamma (s + 2 / 3))⁻¹‖ ≤ C * (1 + |s.im|) ^ 12 := by
  obtain ⟨D, C₀, dH, y, hDATA, hid⟩ := twisted_theta_dbar hd hL φ₀ hφ hφ0 Ps hPs j
  obtain ⟨B₀, hB₀⟩ := exists_bound_of_periodic L hL φ₀ hφ
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0)
  have hF : ∀ x, ‖φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x‖ ≤ B₀ := by
    intro x
    rw [norm_mul, norm_prod]
    exact (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun P _ => norm_chiPow_le _ _ _))).trans (hB₀ x)
  have ha := thetaSupp_twisted hd.1 hB₀0 hF
  have hcne : ∀ (h₀ : 𝓞 K ⧸ span {L}), ∀ A ∈ Ps.powerset, σO (D h₀ A * ∏ P ∈ A, πP P) ≠ 0 := by
    intro h₀ A hA
    have hD := (hDATA h₀ A hA).1
    have hprod : (∏ P ∈ A, πP P) ≠ 0 := Finset.prod_ne_zero_iff.2 fun P _ => ne_zero_of_maximal (πP P)
    have hc : D h₀ A * ∏ P ∈ A, πP P ≠ 0 := mul_ne_zero hD hprod
    exact fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  have := finite_quot L hL
  let _ : Fintype (𝓞 K ⧸ span {L}) := Fintype.ofFinite _
  exact poly_bound_FE Finset.univ Ps.powerset ha (fun m => norm_phiInf_le m)
    (fun m => norm_phiCusp_le m) (fun h₀ => fCoef L φ₀ (repQ L h₀))
    (fun A => ∏ P ∈ Ps \ A, locCoef P (j P) 0) C₀
    (fun h₀ A m => conj (dH h₀ A (-m)) * ψc (δ3 ^ 3 * D h₀ A) (-(m * y h₀ A)) *
      ∏ P : A, Bloc P.1.1 (j P.1) m)
    (fun h₀ A => D h₀ A * ∏ P ∈ A, πP P) (fun _ A => (∏ P : A, Real.sqrt (absNorm P.1.1)) * Kc)
    (fun h₀ _ A hA => ⟨thetaSupp_cuspCoef (hDATA h₀ A hA).2.2.2 _ _ A j, hcne h₀ A hA⟩)
    (fun v hv => by rw [← finsum_eq_sum_of_fintype]; exact hid v hv)

end Eis

end

#print axioms Eis.Gamma_add_nat_eq
#print axioms Eis.exists_norm_Gamma_le
#print axioms Eis.norm_sin_le_exp
#print axioms Eis.exists_norm_inv_Gamma_le
#print axioms Eis.poly_bound_strip
#print axioms Eis.norm_mellin_le_strip
#print axioms Eis.differentiableOn_gRatio
#print axioms Eis.norm_gRatio_half
#print axioms Eis.norm_le_of_re_im
#print axioms Eis.norm_prod_range_le
#print axioms Eis.norm_gRatio_le
#print axioms Eis.exists_gRatio_strip
#print axioms Eis.summable_dSer_abs
#print axioms Eis.norm_mellin_dSer_le
#print axioms Eis.norm_nested_sum_le
#print axioms Eis.poly_bound_FE
#print axioms Eis.twisted_theta_poly
