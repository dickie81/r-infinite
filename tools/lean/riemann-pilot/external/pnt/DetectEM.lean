import PrimeNumberTheoremAnd.ZetaBounds
import KaiserKV
import ShortKV
import DetectCore

/-! # Zero detection by Euler–Maclaurin, and primes in short intervals (round 235)

At a zero `ρ = β + iγ` of `ζ`, PNT+'s Euler–Maclaurin formula (`Zeta0EqZeta`, `ZetaBnd_aux1`) gives
`|Σ_{n≤N} n^{−ρ}| ≤ N^{1−β}/|γ| + N^{−β}/2 + 2|γ|N^{−β}/β` (`norm_partial_zeta_le`), that is `DetectCore.EMBound`
(`emBound`). With the mollifier identity `M_X(ρ)Σ_{n≤N} n^{−ρ} = 1 + D(ρ)` and `|M_X(ρ)| ≤ X^{1−σ}(1 + log X)`, the
choice `X = ⌊U^{2σ−1}⌋`, `N = ⌊U^{3−2σ+2δ}⌋` gives `|D(ρ)| ≥ 1 − (1 + log U)(U^{−1/4} + 14U^{−3δ/2})` for
`U ≤ |γ| ≤ 2U`, `β ≥ σ ≥ ¾`: the two exponents are `(2+2δ)(1−σ) − 1 ≤ −¼` and `−2δσ`.
So `DetectHyp δ` holds (`detectHyp`), hence `N(σ, T) ≪ T^{4(1+δ)(1−σ)}(log T)^{11}`
(`density_unconditional`), and with the Korobov–Vinogradov region:

**`short_primes`**: for every `θ > ¾`, every large `y` has a prime in `(y, y + y^θ]`.

Since round 400 the detection argument is `src/DetectCore.lean` (`detectHyp_of_EMBound`), so that zeta23's layer,
which cannot import this file, runs it from its own copy of PNT+'s `ZetaBounds`
(`external/zeta23/ShellDensity.lean`).
-/

open Real Filter Topology Complex Finset

noncomputable section

namespace DetectEM

open ShortWeil ShortKV KaiserKV Pilot1ca Pilot1bt DirMean

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

/-- `norm_partial_zeta_le` is `DetectCore.EMBound`. -/
theorem emBound : DetectCore.EMBound := fun hβ0 hβ2 hγ hz _ hN => norm_partial_zeta_le hβ0 hβ2 hγ hz hN

/-- **Detection holds** for every `0 < δ ≤ ¼`. -/
theorem detectHyp {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) : DetectHyp δ :=
  DetectCore.detectHyp_of_EMBound emBound hδ0 hδ1

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

#print axioms DetectEM.norm_partial_zeta_le
#print axioms DetectEM.emBound
