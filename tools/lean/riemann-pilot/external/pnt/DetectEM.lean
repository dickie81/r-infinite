import PrimeNumberTheoremAnd.ZetaBounds
import KaiserKV
import ShortKV
import MollId
import DensityAsym

/-! # Zero detection by Euler–Maclaurin, and primes in short intervals (round 235)

At a zero `ρ = β + iγ` of `ζ`, PNT+'s Euler–Maclaurin formula (`Zeta0EqZeta`, `ZetaBnd_aux1`) gives
`|Σ_{n≤N} n^{−ρ}| ≤ N^{1−β}/|γ| + N^{−β}/2 + 2|γ|N^{−β}/β` (`norm_partial_zeta_le`). With the mollifier
identity `M_X(ρ)Σ_{n≤N} n^{−ρ} = 1 + D(ρ)` and `|M_X(ρ)| ≤ X^{1−σ}(1 + log X)`, the choice
`X = ⌊U^{2σ−1}⌋`, `N = ⌊U^{3−2σ+2δ}⌋` gives `|D(ρ)| ≥ 1 − (1 + log U)(U^{−1/4} + 14U^{−3δ/2})` for
`U ≤ |γ| ≤ 2U`, `β ≥ σ ≥ ¾`: the two exponents are `(2+2δ)(1−σ) − 1 ≤ −¼` and `−2δσ`.
So `DetectHyp δ` holds (`detectHyp`), hence `N(σ, T) ≪ T^{4(1+δ)(1−σ)}(log T)^{11}`
(`density_unconditional`), and with the Korobov–Vinogradov region:

**`short_primes`**: for every `θ > ¾`, every large `y` has a prime in `(y, y + y^θ]`.
-/

open Real Filter Topology Complex Finset

noncomputable section

namespace DetectEM

open ShortWeil ShortKV KaiserKV Pilot1ca Pilot1bt DirMean

/-- The zero `½ ± iτ` of `ζ` with `β ≥ ½`. -/
theorem zeta_βsγs (i : ZeroIdx (sqF Xi)) : riemannZeta ((βs i : ℂ) + (γs i : ℝ) * I) = 0 := by
  by_cases h : (tau i).im ≤ 0
  · have e : rhoXi (true, i) = (βs i : ℂ) + (γs i : ℝ) * I := by
      unfold βs γs; simp only [h, ↓reduceIte]; rw [abs_of_nonpos h]
      apply Complex.ext <;> simp [rhoXi]
    rw [← e]; exact zeta_rhoXi _
  · push Not at h
    have e : rhoXi (false, i) = (βs i : ℂ) + (γs i : ℝ) * I := by
      unfold βs γs; simp only [not_le.2 h, ↓reduceIte]; rw [abs_of_pos h]
      apply Complex.ext <;> simp [rhoXi]
    rw [← e]; exact zeta_rhoXi _

/-- **Euler–Maclaurin at a zero.** -/
theorem norm_partial_zeta_le {β γ : ℝ} (hβ0 : 0 < β) (hβ2 : β ≤ 2) (hγ : 2 ≤ |γ|)
    (hz : riemannZeta ((β : ℂ) + γ * I) = 0) {N : ℕ} (hN : 1 ≤ N) :
    ‖∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I))‖
      ≤ (N : ℝ) ^ (1 - β) / |γ| + (N : ℝ) ^ (-β) / 2 + 2 * |γ| * (N : ℝ) ^ (-β) / β := by
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

theorem aux_Z {U γ β q : ℝ} (hU : 1 ≤ U) (hγ : |γ| ≤ 2 * U) (hβ : 3 / 4 ≤ β) (hq : 0 ≤ q) :
    q / 2 + 2 * |γ| * q / β ≤ 7 * U * q := by
  have hβ0 : 0 < β := by linarith
  have h1 : 2 * |γ| / β ≤ 6 * U := by
    rw [div_le_iff₀ hβ0]
    have : 2 * |γ| ≤ 4 * U := by linarith
    have : 4 * U ≤ 6 * U * β := by nlinarith
    linarith
  have e : 2 * |γ| * q / β = (2 * |γ| / β) * q := by ring
  rw [e]
  have h2 := mul_le_mul_of_nonneg_right h1 hq
  have h3 : q / 2 ≤ U * q := by nlinarith
  linarith

theorem aux_exp1 {σ δ : ℝ} (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hδ1 : δ ≤ 1 / 4) :
    (2 * σ - 1) * (1 - σ) + (3 - 2 * σ + 2 * δ) * (1 - σ) + (-1) ≤ -(1 / 4) := by
  have e : (2 * σ - 1) * (1 - σ) + (3 - 2 * σ + 2 * δ) * (1 - σ) + (-1) = (2 + 2 * δ) * (1 - σ) - 1 := by ring
  rw [e]
  have h1 : 0 ≤ 1 - σ := by linarith
  have h2 : (2 + 2 * δ) * (1 - σ) ≤ (5 / 2) * (1 / 4) :=
    mul_le_mul (by linarith) (by linarith) h1 (by norm_num)
  linarith

theorem aux_exp2 {σ δ : ℝ} (hσ : 3 / 4 ≤ σ) (hδ0 : 0 < δ) :
    (2 * σ - 1) * (1 - σ) + 1 + -((3 - 2 * σ + 2 * δ) * σ) ≤ -(3 * δ / 2) := by
  have e : (2 * σ - 1) * (1 - σ) + 1 + -((3 - 2 * σ + 2 * δ) * σ) = -(2 * δ * σ) := by ring
  rw [e]
  have : 3 * δ / 2 ≤ 2 * δ * σ := by nlinarith
  linarith

/-- **Detection holds** for every `0 < δ ≤ ¼`. -/
theorem detectHyp {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) : DetectHyp δ := by
  have hev : ∀ᶠ U : ℝ in atTop,
      (1 + Real.log U) * (U ^ (-(1 / 4 : ℝ)) + 14 * U ^ (-(3 * δ / 2))) ≤ 1 / 2 := by
    have h1 := tendsto_log_rpow_neg (a := 1 / 4) (by norm_num) 1 1
    have h2 := tendsto_log_rpow_neg (a := 3 * δ / 2) (by positivity) 14 14
    have h3 := h1.add h2
    rw [add_zero] at h3
    filter_upwards [h3.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with U hU
    have e : (1 + Real.log U) * (U ^ (-(1 / 4 : ℝ)) + 14 * U ^ (-(3 * δ / 2)))
        = (1 * Real.log U + 1) * U ^ (-(1 / 4 : ℝ)) + (14 * Real.log U + 14) * U ^ (-(3 * δ / 2)) := by
      ring
    rw [e]; exact hU
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.1 hev
  refine ⟨max U₁ 2, le_max_right _ _, fun σ U hσ hσ1 hU i hlo hhi hβ => ?_⟩
  have hU2 : 2 ≤ U := (le_max_right _ _).trans hU
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hUb := hU₁ U ((le_max_left _ _).trans hU)
  have hlU : 0 ≤ Real.log U := Real.log_nonneg hU1
  set β := βs i with hβdef
  set γ := γs i with hγdef
  have hγabs : |γ| = |(tau i).re| := abs_γs i
  have hγU : U ≤ |γ| := by rw [hγabs]; exact hlo
  have hγ2U : |γ| ≤ 2 * U := by rw [hγabs]; exact hhi
  have hγ2 : 2 ≤ |γ| := hU2.trans hγU
  have hβ1 : β < 1 := βs_lt_one i
  have hβ0 : 0 < β := by linarith
  -- the parameters
  set a := 3 - 2 * σ + 2 * δ with ha
  set y1 := U ^ (2 * σ - 1) with hy1def
  set y2 := U ^ a with hy2def
  set X := Xp σ U with hXdef
  set N := Np δ σ U with hNdef
  have hy1 : 1 ≤ y1 := Real.one_le_rpow hU1 (by linarith)
  have hy2 : 1 ≤ y2 := Real.one_le_rpow hU1 (by rw [ha]; linarith)
  have hX1 : 1 ≤ X := (Nat.one_le_floor_iff _).2 hy1
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff _).2 hy2
  have hy12 : y1 ≤ y2 := Real.rpow_le_rpow_of_exponent_le hU1 (by rw [ha]; linarith)
  have hXN : X ≤ N := Nat.floor_le_floor hy12
  have hXle : (X : ℝ) ≤ y1 := Nat.floor_le (by linarith)
  have hNle : (N : ℝ) ≤ y2 := Nat.floor_le (by linarith)
  have hNge : y2 / 2 ≤ N := by
    have h := Nat.lt_floor_add_one y2
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    change y2 < (N : ℝ) + 1 at h
    linarith
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  -- the identity
  have hz := zeta_βsγs i
  have hZ := norm_partial_zeta_le hβ0 (by linarith) hγ2 hz hN1
  have hM := norm_moll_le (X := X) (γ := γ) hσ1 hβ
  have hid := moll_identity hX1 hXN ((β : ℂ) + γ * I)
  have hD : DPval X N β γ = moll X ((β : ℂ) + γ * I) * ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I)) - 1 := by
    rw [DPval_eq_cpow, hid]; ring
  -- `|M|` and `|Z|` in powers of `U`
  set p1 := (2 * σ - 1) * (1 - σ) with hp1
  have hXp : (X : ℝ) ^ (1 - σ) ≤ U ^ p1 := by
    calc (X : ℝ) ^ (1 - σ) ≤ y1 ^ (1 - σ) := Real.rpow_le_rpow hX0.le hXle (by linarith)
      _ = U ^ p1 := by rw [hy1def, ← Real.rpow_mul hU0.le]
  have hlX : 1 + Real.log X ≤ 1 + Real.log U := by
    have : (X : ℝ) ≤ U := hXle.trans (by
      calc y1 ≤ U ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
        _ = U := Real.rpow_one U)
    linarith [Real.log_le_log hX0 this]
  have hMb : ‖moll X ((β : ℂ) + γ * I)‖ ≤ U ^ p1 * (1 + Real.log U) :=
    hM.trans (mul_le_mul hXp hlX (by linarith [Real.log_nonneg (by exact_mod_cast hX1 : (1 : ℝ) ≤ X)])
      (by positivity))
  have hNa : (N : ℝ) ^ (1 - β) ≤ U ^ (a * (1 - σ)) := by
    calc (N : ℝ) ^ (1 - β) ≤ (N : ℝ) ^ (1 - σ) := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      _ ≤ y2 ^ (1 - σ) := Real.rpow_le_rpow hN0.le hNle (by linarith)
      _ = U ^ (a * (1 - σ)) := by rw [hy2def, ← Real.rpow_mul hU0.le]
  have hNb : (N : ℝ) ^ (-β) ≤ 2 * U ^ (-(a * σ)) := by
    have h2σ : (2 : ℝ) ^ σ ≤ 2 := by
      calc (2 : ℝ) ^ σ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
        _ = 2 := Real.rpow_one 2
    calc (N : ℝ) ^ (-β) ≤ (N : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      _ ≤ (y2 / 2) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by positivity) hNge (by linarith)
      _ = y2 ^ (-σ) * 2 ^ σ := by
          rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
            div_inv_eq_mul]
      _ ≤ y2 ^ (-σ) * 2 := by gcongr
      _ = 2 * U ^ (-(a * σ)) := by rw [hy2def, ← Real.rpow_mul hU0.le]; ring_nf
  have hZb : ‖∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I))‖
      ≤ U ^ (a * (1 - σ)) / U + 14 * U * U ^ (-(a * σ)) := by
    refine hZ.trans ?_
    have hNbpos : 0 ≤ (N : ℝ) ^ (-β) := by positivity
    have t1 : (N : ℝ) ^ (1 - β) / |γ| ≤ U ^ (a * (1 - σ)) / U :=
      div_le_div₀ (by positivity) hNa hU0 hγU
    have t2 : (N : ℝ) ^ (-β) / 2 + 2 * |γ| * (N : ℝ) ^ (-β) / β ≤ 7 * U * (N : ℝ) ^ (-β) :=
      aux_Z hU1 hγ2U (by linarith) hNbpos
    have t3 : 7 * U * (N : ℝ) ^ (-β) ≤ 14 * U * U ^ (-(a * σ)) := by
      have := mul_le_mul_of_nonneg_left hNb (by linarith : (0 : ℝ) ≤ 7 * U)
      linarith
    linarith
  -- the two exponents
  have hE1 : U ^ p1 * (U ^ (a * (1 - σ)) / U) ≤ U ^ (-(1 / 4 : ℝ)) := by
    have e : U ^ p1 * (U ^ (a * (1 - σ)) / U) = U ^ (p1 + a * (1 - σ) + (-1)) := by
      rw [Real.rpow_add hU0, Real.rpow_add hU0, Real.rpow_neg_one]; ring
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hU1 (by rw [hp1, ha]; exact aux_exp1 hσ hσ1 hδ1)
  have hE2 : U ^ p1 * (14 * U * U ^ (-(a * σ))) ≤ 14 * U ^ (-(3 * δ / 2)) := by
    have e : U ^ p1 * (14 * U * U ^ (-(a * σ))) = 14 * U ^ (p1 + 1 + (-(a * σ))) := by
      rw [Real.rpow_add hU0, Real.rpow_add hU0, Real.rpow_one]; ring
    rw [e]
    gcongr
    rw [hp1, ha]; exact aux_exp2 hσ hδ0
  have hMZ : ‖moll X ((β : ℂ) + γ * I)‖ * ‖∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I))‖ ≤ 1 / 2 := by
    calc ‖moll X ((β : ℂ) + γ * I)‖ * ‖∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I))‖
        ≤ (U ^ p1 * (1 + Real.log U)) * (U ^ (a * (1 - σ)) / U + 14 * U * U ^ (-(a * σ))) :=
          mul_le_mul hMb hZb (norm_nonneg _) (by positivity)
      _ = (1 + Real.log U) * (U ^ p1 * (U ^ (a * (1 - σ)) / U) + U ^ p1 * (14 * U * U ^ (-(a * σ)))) := by
          ring
      _ ≤ (1 + Real.log U) * (U ^ (-(1 / 4 : ℝ)) + 14 * U ^ (-(3 * δ / 2))) := by gcongr
      _ ≤ 1 / 2 := hUb
  rw [hD]
  have := norm_sub_norm_le (1 : ℂ) (moll X ((β : ℂ) + γ * I) * ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I)))
  rw [norm_one, norm_mul, norm_sub_rev] at this
  linarith

/-- **Zero density**: `N(σ, T) ≪ T^{4(1+δ)(1−σ)}(log T)^{11}` for every `0 < δ ≤ ¼`. -/
theorem density_unconditional {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) : DensityXi (4 * (1 + δ)) 11 :=
  density_of_detect hδ0 hδ1 (detectHyp hδ0 hδ1)

/-- **Primes in short intervals**: for every `θ > ¾`, every large `y` has a prime in `(y, y + y^θ]`. -/
theorem short_primes {θ : ℝ} (hθ : 3 / 4 < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ := by
  set δ := min (1 / 4) ((4 * θ - 3) / 8) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 4 := min_le_left _ _
  have hδ2 : δ ≤ (4 * θ - 3) / 8 := min_le_right _ _
  have hA : 0 < 4 * (1 + δ) := by positivity
  refine short_primes_KV_of_density hA (density_unconditional hδ0 hδ1) (by linarith) ?_
  -- `1 − 1/(4(1+δ)) < θ`
  rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_div_iff₀ hA]
  rcases le_or_gt 1 θ with h1 | h1
  · nlinarith
  · nlinarith

end DetectEM

#print axioms DetectEM.detectHyp
#print axioms DetectEM.density_unconditional
#print axioms DetectEM.short_primes

#print axioms DetectEM.zeta_βsγs
#print axioms DetectEM.norm_partial_zeta_le
