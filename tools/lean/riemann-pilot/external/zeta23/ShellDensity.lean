import Mathlib
import Zeta23.FromPNTPlus.ZetaBounds
import SlogZeta
import CountCompare
import DetectCore
import ShellCount

/-! # For every `w > ¼`, almost every zero lies within `w` of the critical line, in Bohr-shell form (round 400)

`ShellCount` (src) reads zero density as counts outside shells around round 391's Bohr sphere: `NX w T` counts the
pairs up to height `T` with `|β − ½| ≥ w`, which are exactly those whose Bohr vectors lie outside the shell between
the radii at `½ + w` and `½ − w`. This file supplies its two inputs on zeta23's side of the layer boundary.
`external/pnt/DetectEM.lean` cannot be imported here: its PNT+ files and zeta23's copies declare the same names.

* **`emBound_zeta23`**: the Euler–Maclaurin bound at a zero (`DetectCore.EMBound`), from zeta23's copy of PNT+'s
  `ZetaBounds`; the proof is that of `DetectEM.norm_partial_zeta_le`. Hence **`density_zeta23`**: `DensityXi (4(1+δ)) 11`,
  by round 235's detection argument (`DetectCore`).
* **`Ncount_le_NX`**, **`NX_zero_ge`**: zeta23's Riemann–von Mangoldt count injects into the pilot's pairs, so at
  least `X log X/(8π)` pairs lie up to height `X`, for large `X`.
* **`tendsto_NX_div_quarter`**, **`tendsto_outside_div_quarter`**: for every `w > ¼` the proportion of pairs up to height `T` that
  lie outside the shell of half-width `w` tends to `0`. **`ncard_outside_le_unconditional`**: their number is at most
  `C T^{4(1+δ)(½−w)}(log T)^{11}`.

Not proved here: the same for `w ≤ ¼`. Bohr and Landau (1914) proved it for every `w > 0`; the standard proof uses a
mean-square bound for `ζ` on `Re s > ½`. The exponent `4(1+δ)` gives a vanishing proportion only for `w > ¼`.
(Round 401: `ShellSixth.lean` proves it for every `w > 1/6`, from a mean square of `ζ` on `Re s ≥ 2/3` and Jensen's
formula.) A proportion statement, for any `w`, allows a set of off-shell zeros of
smaller order than the set of all zeros, so it does not bear on RH.
-/

open Real Filter Topology Complex Finset BohrSphere

noncomputable section

namespace ShellDensity

open ShortWeil Pilot1ca Pilot1bt ShellCount

/-- **The Euler–Maclaurin bound at a zero**, from zeta23's copy of PNT+'s `ZetaBounds` (the proof of
`DetectEM.norm_partial_zeta_le`). -/
theorem emBound_zeta23 : DetectCore.EMBound := by
  intro β γ hβ0 hβ2 hγ hz N hN
  set s : ℂ := (β : ℂ) + γ * I with hs
  have hsre : s.re = β := by simp [hs]
  have hsim : s.im = γ := by simp [hs]
  have hs1 : s ≠ 1 := fun h => by
    have := congrArg Complex.im h; rw [hsim] at this; simp at this
    rw [this] at hγ; norm_num at hγ
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith
  have hEM := Zeta0EqZeta (N := N) (by omega) (by rw [hsre]; exact hβ0) hs1
  rw [hz] at hEM
  unfold riemannZeta0 at hEM
  set I0 := ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hI0
  have hsum : ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s = ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s) := by
    rw [Finset.sum_range_succ', Nat.cast_zero, Complex.zero_cpow hs0, div_zero, add_zero]
    have hmap : Ioc 0 N = (Finset.range N).map ⟨(· + 1), add_left_injective 1⟩ := by
      ext n; simp only [mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro h; exact ⟨n - 1, by omega, by omega⟩
      · rintro ⟨m, hm, rfl⟩; omega
    rw [hmap, Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Function.Embedding.coeFn_mk]
    rw [Complex.cpow_neg, one_div]
  rw [hsum] at hEM
  have hZ : ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s)
      = (N : ℂ) ^ (1 - s) / (1 - s) + (N : ℂ) ^ (-s) / 2 - s * I0 := by
    linear_combination hEM
  rw [hZ]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ ≤ (N : ℝ) ^ (1 - β) / |γ| := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega)]
    have : (1 - s).re = 1 - β := by simp [hsre]
    rw [this]
    apply div_le_div_of_nonneg_left (by positivity) (by linarith)
    have := Complex.abs_im_le_norm (1 - s)
    simpa [hsim] using this
  have h2 : ‖(N : ℂ) ^ (-s) / 2‖ = (N : ℝ) ^ (-β) / 2 := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega)]; simp [hsre]
  have h3 : ‖s * I0‖ ≤ 2 * |γ| * (N : ℝ) ^ (-β) / β := by
    have := ZetaBnd_aux1 N hN (σ := β) (t := γ) ⟨hβ0, hβ2⟩ hγ
    rw [hI0, hs]; convert this using 2
  calc ‖(N : ℂ) ^ (1 - s) / (1 - s) + (N : ℂ) ^ (-s) / 2 - s * I0‖
      ≤ ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ + ‖s * I0‖ :=
        (norm_sub_le _ _).trans (by linarith [norm_add_le ((N : ℂ) ^ (1 - s) / (1 - s)) ((N : ℂ) ^ (-s) / 2)])
    _ ≤ _ := by rw [h2]; linarith

/-- **Zero density**, on this side of the layer boundary. -/
theorem density_zeta23 {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) : DensityXi (4 * (1 + δ)) 11 :=
  DetectCore.density_of_EMBound emBound_zeta23 hδ0 hδ1

/-- **zeta23's zeros with `T < γ ≤ 2T` inject into the pilot's pairs up to height `2T`.** -/
theorem Ncount_le_NX {T : ℝ} (hT : 0 ≤ T) : (Zeta23.Ncount T (2 * T) : ℝ) ≤ NX 0 (2 * T) := by
  classical
  set s := Zeta23.zerosIn T (2 * T) with hs
  have hfin : s.Finite := (SlogZeta.Zs_finite (2 * T + 1)).subset fun ρ ⟨h, h0, h1⟩ =>
    ⟨h, by linarith, by linarith⟩
  let W := {p : ZIdx // T < (zetaZeroFamily p).im ∧ (zetaZeroFamily p).im ≤ 2 * T}
  have hcard : Zeta23.Ncount T (2 * T) = Nat.card W := by
    rw [Zeta23.Ncount, SlogZeta.finsum_eq_card hfin]
    refine Nat.card_congr ?_
    exact
      { toFun := fun x => ⟨⟨⟨x.1.1, (CountCompare.nontriv_iff' _).2 x.1.2.1⟩, x.2⟩, x.1.2.2.1, x.1.2.2.2⟩
        invFun := fun p => ⟨⟨p.1.1.1, (CountCompare.nontriv_iff' _).1 p.1.1.2, p.2.1, p.2.2⟩, p.1.2⟩
        left_inv := fun x => rfl
        right_inv := fun p => rfl }
  set S := {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ 2 * T} with hSdef
  have hSfin : S.Finite := finite_re_le (2 * T)
  have hre : ∀ p : W, |(tau (zetaEquiv p.1).2).re| = (zetaZeroFamily p.1).im := by
    intro p
    have e := congrArg Complex.im (rhoXi_zetaEquiv p.1)
    rw [CountCompare.im_rhoXi] at e
    have hpos : 0 < (zetaZeroFamily p.1).im := by linarith [p.2.1]
    split_ifs at e with hb
    · rw [← e] at hpos ⊢; exact abs_of_pos hpos
    · rw [← e] at hpos ⊢; rw [abs_of_neg (by linarith)]
  let φ : W → S := fun p => ⟨(zetaEquiv p.1).2, by
    show |(tau (zetaEquiv p.1).2).re| ≤ 2 * T
    rw [hre p]
    exact p.2.2⟩
  have hinj : Function.Injective φ := by
    intro p q hpq
    have h2 : (zetaEquiv p.1).2 = (zetaEquiv q.1).2 := congrArg Subtype.val hpq
    have hsign : ∀ r : W, (zetaEquiv r.1).1 = true ↔ 0 < (tau (zetaEquiv r.1).2).re := by
      intro r
      have e := congrArg Complex.im (rhoXi_zetaEquiv r.1)
      rw [CountCompare.im_rhoXi] at e
      have hpos : 0 < (zetaZeroFamily r.1).im := by linarith [r.2.1]
      constructor
      · intro hb; rw [ite_eq_left hb] at e; rw [e]; exact hpos
      · intro h; by_contra hb
        rw [ite_eq_right hb] at e; rw [← e] at hpos; linarith
    have h1 : (zetaEquiv p.1).1 = (zetaEquiv q.1).1 := by
      have hp := hsign p
      have hq := hsign q
      rw [h2] at hp
      exact Bool.eq_iff_iff.2 (hp.trans hq.symm)
    have : zetaEquiv p.1 = zetaEquiv q.1 := Prod.ext h1 h2
    exact Subtype.ext (zetaEquiv.injective this)
  have : Finite S := hSfin.to_subtype
  have hle : Nat.card W ≤ Nat.card S := Nat.card_le_card_of_injective φ hinj
  rw [hcard, NX_zero_eq, ← Nat.card_coe_set_eq]
  exact_mod_cast hle

/-- **Riemann–von Mangoldt in the pilot's family**: for large `X`, at least `X log X/(8π)` pairs lie up to
height `X`. -/
theorem NX_zero_ge : ∀ᶠ X : ℝ in atTop, X * Real.log X / (8 * π) ≤ NX 0 X := by
  obtain ⟨C, T₀, hR⟩ := (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts).main
  have hπ := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  -- `log(2π) < 2`
  have hl2π : Real.log (2 * π) < 2 := by
    rw [Real.log_lt_iff_lt_exp (by positivity)]
    have := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith
  filter_upwards [eventually_ge_atTop (2 * |T₀| + 2), eventually_ge_atTop (Real.exp 16),
    eventually_ge_atTop (16 * π * |C| + 1)] with X hX1 hX2 hX3
  have hX0 : 0 < X := by linarith [abs_nonneg T₀]
  set T := X / 2 with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hT1 : 1 ≤ T := by rw [hTdef]; linarith [abs_nonneg T₀]
  have hTT₀ : T₀ ≤ T := by rw [hTdef]; linarith [le_abs_self T₀, abs_nonneg T₀]
  have hXT : X = 2 * T := by rw [hTdef]; ring
  have hR' := hR T hTT₀
  rw [Zeta23.zetaZeroConfig_N] at hR'
  have hcnt := Ncount_le_NX hT0
  have hNX : (NX 0 (2 * T) : ℝ) = NX 0 X := by rw [← hXT]
  have hlogX : 16 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; exact hX2
  have hlogT : Real.log T = Real.log X - Real.log 2 := by
    rw [hTdef, Real.log_div hX0.ne' (by norm_num)]
  have hell : Real.log X - 4 ≤ Zeta23.ell1 T := by
    unfold Zeta23.ell1 Zeta23.l
    rw [Real.log_div (by positivity) (by positivity), hlogT]
    linarith
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hClog : C * Real.log T ≤ |C| * Real.log X := by
    have : Real.log T ≤ Real.log X := by rw [hlogT]; linarith
    calc C * Real.log T ≤ |C| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self C) hlogT0
      _ ≤ |C| * Real.log X := mul_le_mul_of_nonneg_left this (abs_nonneg C)
  have hN : T / (2 * π) * (Real.log X - 4) - |C| * Real.log X ≤ (Zeta23.Ncount T (2 * T) : ℝ) := by
    have h1 := (abs_le.1 hR').1
    have h2 : T / (2 * π) * (Real.log X - 4) ≤ T / (2 * π) * Zeta23.ell1 T :=
      mul_le_mul_of_nonneg_left hell (by positivity)
    linarith
  have hgoal : X * Real.log X / (8 * π) ≤ T / (2 * π) * (Real.log X - 4) - |C| * Real.log X := by
    have hpos : 0 < π := Real.pi_pos
    have hlX0 : 0 ≤ Real.log X := by linarith
    rw [div_le_iff₀ (by positivity)]
    have e : (T / (2 * π) * (Real.log X - 4) - |C| * Real.log X) * (8 * π)
        = 4 * T * (Real.log X - 4) - 8 * π * |C| * Real.log X := by field_simp; ring
    rw [e]
    have hXl : X * Real.log X = 2 * T * Real.log X := by rw [← hXT]
    have h16 : 2 * T * 16 ≤ 2 * T * Real.log X := mul_le_mul_of_nonneg_left hlogX (by positivity)
    have hC2 : 8 * π * |C| * Real.log X ≤ T * Real.log X := by
      have : 8 * π * |C| ≤ T := by rw [hTdef]; linarith
      exact mul_le_mul_of_nonneg_right this hlX0
    linarith
  linarith

/-- **For every `w > ¼`, the proportion of pairs up to height `T` with `|β − ½| ≥ w` tends to `0`.** -/
theorem tendsto_NX_div_quarter {w : ℝ} (hw : 1 / 4 < w) :
    Tendsto (fun T => (NX w T : ℝ) / NX 0 T) atTop (𝓝 0) := by
  set δ := min (1 / 4) ((4 * w - 1) / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 4 := min_le_left _ _
  have hδ2 : δ ≤ (4 * w - 1) / 4 := min_le_right _ _
  have hA : 4 * (1 + δ) * (1 / 2 - w) < 1 := by
    rcases le_or_gt (1 / 2) w with h | h
    · nlinarith
    · nlinarith
  refine ShellCount.tendsto_NX_div (density_zeta23 hδ0 hδ1) (by linarith) hA ⟨1 / (8 * π), by positivity, ?_⟩
  filter_upwards [NX_zero_ge, eventually_ge_atTop (Real.exp 1)] with X hX hXe
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hlog : 1 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; exact hXe
  calc 1 / (8 * π) * X ≤ X * Real.log X / (8 * π) := by
        rw [one_div_mul_eq_div]
        exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _ ≤ NX 0 X := hX

/-- **The same in sphere form**: for every `w > ¼` and every nonempty finite set `F` of primes, the proportion of
pairs up to height `T` whose Bohr vectors lie outside the shell between the radii at `½ + w` and `½ − w` tends to
`0`. -/
theorem tendsto_outside_div_quarter {w : ℝ} (hw : 1 / 4 < w) {F : Finset Nat.Primes} (hF : F.Nonempty) :
    Tendsto (fun T => (Set.ncard {i : ZeroIdx (sqF Xi) |
        |(tau i).re| ≤ T ∧ ‖vF F (rhoS i)‖ ≤ ‖vF F ((1 / 2 + w : ℝ) : ℂ)‖} : ℝ) /
      Set.ncard {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T}) atTop (𝓝 0) := by
  refine (tendsto_NX_div_quarter hw).congr fun T => ?_
  rw [NX_eq_ncard_outside hF, NX_zero_eq]

/-- **The count**: at most `C T^{4(1+δ)(½−w)}(log T)^{11}` pairs up to height `T` lie outside the shell. -/
theorem ncard_outside_le_unconditional {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Finset Nat.Primes, F.Nonempty → ∀ T : ℝ, 2 ≤ T → ∀ w : ℝ, 0 ≤ w → w ≤ 1 / 2 →
      (Set.ncard {i : ZeroIdx (sqF Xi) |
        |(tau i).re| ≤ T ∧ ‖vF F (rhoS i)‖ ≤ ‖vF F ((1 / 2 + w : ℝ) : ℂ)‖} : ℝ)
        ≤ C * T ^ (4 * (1 + δ) * (1 / 2 - w)) * Real.log T ^ (11 : ℝ) :=
  ShellCount.ncard_outside_le (density_zeta23 hδ0 hδ1)

end ShellDensity

#print axioms ShellDensity.emBound_zeta23
#print axioms ShellDensity.density_zeta23
#print axioms ShellDensity.Ncount_le_NX
#print axioms ShellDensity.NX_zero_ge
#print axioms ShellDensity.tendsto_NX_div_quarter
#print axioms ShellDensity.tendsto_outside_div_quarter
#print axioms ShellDensity.ncard_outside_le_unconditional
