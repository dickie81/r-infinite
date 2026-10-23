/-
# Round 607: the Type II estimate for the curve of the `7/3` result at `L = 229/100` (the second goal, N2)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`typeII_73`). Assume `LinnikCGL.CGLDensity`. Let `L = 229/100`, `f0` smooth and real with support
in `[1/2, 2]`, `K₀ ≥ 0`, `e₁ > 0` and `0 < η ≤ 10⁻⁵`. For every large `q`, every `P` with
`q^{(4123/10000)L} ≤ P ≤ q^{(4902/10000)L}`, every `S ⊆ (P, 2P]`, `a_m` and `h₀`, every `K ≤ K₀`, and every
`Q_j ≥ q^{e₁}` and `|h_j| ≤ q^η` (`j < K`) with `∏_j Q_j ≤ 2^{K₀}q^L/P`:
`Σ_{χ≠1} |Σ_{m∈S} a_mχ(m)m^{−ih₀}||∏_{j<K} Σ_{p≤2Q_j} χ(p)(p/Q_j)^{−ih_j}f0(p/Q_j)|` is at most
`q^{L−1/50000}(Σ_m |a_m|²/P)^{1/2}`.

This is `SieveTypeIIGen.typeII_gen` for the curve of `frontier/linnik/SIEVE-ROUTE.md` §14: the trivial count below
`8003/14003 = 1 − 1/A₇`, `A₇ = 7/3 + 1/2000` on `[8003/14003, 5/6]` and `101/50` from `5/6` on.

* `g73`, `g73_le_one`, `g73_half`: the curve's exponent `A(σ)(1 − σ)`, at most `1`, and `1` at `σ = 1/2`.
* `counts_73`: its counts. Below `8003/14003` at most `q` characters; up to `5/7`
  `LinnikIngham73.charDensity_ingham73` at `ε = 1/8000`; up to `16/21` `CGLDensity` at `ε = 1/8400`, since
  `(7/3)(1 − σ) + 1/8400 ≤ A₇(1 − σ)` for `σ ≤ 16/21`; up to `5/6` `LinnikHuxStep.charDensity_hux73`; and from `5/6`
  on `LinnikStep.charDensity_step`.
* `window_73`: the window's exponents, at most `L − 1/25000`. The left sides are linear in `β` on each piece of `g`,
  so their largest values lie at the pieces' ends. Before the width they lie at least `6.9·10⁻⁵` below `L`, least at
  `β = 11/12` and `m = (4123/10000)L`; at `w = 4·10⁻⁶`, at least `2.4·10⁻⁵` below `L − 1/25000`.
* `typeII_73`.

The file imports `SieveTypeIIGen.lean`, `LinnikIngham73.lean`, `LinnikHuxStep.lean` and `LinnikCGL.lean`.
-/
import SieveTypeIIGen
import LinnikIngham73
import LinnikHuxStep
import LinnikCGL

open Complex Finset

noncomputable section

namespace SieveTypeII73

open DirMean DirichletCharacter SieveTypeIIGen

section Curve

open scoped Classical ContDiff

/-- The exponent `A(σ)(1 − σ)` of the curve: `1` below `8003/14003` (the trivial count), `(14003/6000)(1 − σ)` below
`5/6` and `(101/50)(1 − σ)` from `5/6` on. -/
noncomputable def g73 (σ : ℝ) : ℝ :=
  if σ < 8003 / 14003 then 1 else if σ < 5 / 6 then 14003 / 6000 * (1 - σ) else 101 / 50 * (1 - σ)

lemma g73_le_one (σ : ℝ) : g73 σ ≤ 1 := by
  unfold g73
  split_ifs with h1 h2
  · exact le_rfl
  · have := not_lt.1 h1; nlinarith
  · have := not_lt.1 h2; nlinarith

lemma g73_half : g73 (1 / 2) = 1 := by unfold g73; norm_num

/-- **The counts of the curve** under `CGLDensity` (`CurveCounts g73`): there is `C ≥ 0` such that for every `q ≥ 1`,
`1/2 ≤ σ ≤ 1` and `T ≥ 2` at most `C(qT)^{g(σ)}(1 + log qT)^{10}` characters have a zero with `Re s ≥ σ` and
`|Im s| ≤ T`. -/
theorem counts_73 (hCGL : LinnikCGL.CGLDensity) : CurveCounts g73 := by
  obtain ⟨C₁, -, hC₁⟩ := LinnikIngham73.charDensity_ingham73 (ε := 1 / 8000) (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂⟩ := hCGL (1 / 8400) (by norm_num)
  obtain ⟨C₃, -, hC₃⟩ := LinnikHuxStep.charDensity_hux73
  obtain ⟨C₄, -, hC₄⟩ := LinnikStep.charDensity_step
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max 1 (max (max C₁ C₂) (max C₃ C₄)) := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := hM ▸ le_max_left _ _
  have hMC₁ : C₁ ≤ M := hM ▸ (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hMC₂ : C₂ ≤ M := hM ▸ (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hMC₃ : C₃ ≤ M := hM ▸ (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hMC₄ : C₄ ≤ M := hM ▸ (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨M, by linarith, fun q _ σ T hσ hσ1 hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : 2 ≤ (q : ℝ) * T := by nlinarith
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by linarith)
  have hlog : Real.log ((q : ℝ) * T) ^ (10 : ℝ) ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ hl (by linarith) 10
  have hl1 : 1 ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := one_le_pow₀ (by linarith)
  unfold g73
  split_ifs with h1 h2
  · have hc := LinnikDensity.card_chars_le (q := q) (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)
    rw [Real.rpow_one]
    calc _ ≤ (q : ℝ) := hc
      _ ≤ 1 * ((q : ℝ) * T) * 1 := by nlinarith
      _ ≤ M * ((q : ℝ) * T) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by gcongr
  · have hP : 0 ≤ ((q : ℝ) * T) ^ (14003 / 6000 * (1 - σ)) := Real.rpow_nonneg (by linarith) _
    rcases le_or_gt σ (5 / 7) with h57 | h57
    · have hc := hC₁ q σ T hσ h57 hT
      rw [show (7 / 3 + 4 * (1 / 8000) : ℝ) * (1 - σ) = 14003 / 6000 * (1 - σ) by ring] at hc
      calc _ ≤ C₁ * ((q : ℝ) * T) ^ (14003 / 6000 * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := hc
        _ ≤ M * ((q : ℝ) * T) ^ (14003 / 6000 * (1 - σ)) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by gcongr
    rcases lt_or_ge σ (16 / 21) with h1621 | h1621
    · have hc := hC₂ q σ T h57.le h1621.le hT
      have hX : ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + 1 / 8400) ≤ ((q : ℝ) * T) ^ (14003 / 6000 * (1 - σ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hX0 : 0 ≤ ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + 1 / 8400) := Real.rpow_nonneg (by linarith) _
      calc _ ≤ C₂ * ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + 1 / 8400) := hc
        _ ≤ M * ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + 1 / 8400) := mul_le_mul_of_nonneg_right hMC₂ hX0
        _ ≤ M * ((q : ℝ) * T) ^ (14003 / 6000 * (1 - σ)) * 1 := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left hX (by linarith)
        _ ≤ M * ((q : ℝ) * T) ^ (14003 / 6000 * (1 - σ)) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by gcongr
    · have hc := hC₃ q σ T h1621 h2.le hT
      rw [show (7 / 3 + 1 / 2000 : ℝ) * (1 - σ) = 14003 / 6000 * (1 - σ) by ring] at hc
      calc _ ≤ C₃ * ((q : ℝ) * T) ^ (14003 / 6000 * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := hc
        _ ≤ M * ((q : ℝ) * T) ^ (14003 / 6000 * (1 - σ)) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by gcongr
  · have hc := hC₄ q σ T (not_lt.1 h2) hσ1 hT
    calc _ ≤ C₄ * ((q : ℝ) * T) ^ (101 / 50 * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := hc
      _ ≤ M * ((q : ℝ) * T) ^ (101 / 50 * (1 - σ)) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by gcongr

/-- **The window's exponents** for the curve at `L = 229/100` on `m ∈ [4123/10000, 4902/10000]·L`: for
`1/2 ≤ β ≤ 11/12` and `0 ≤ w ≤ 4·10⁻⁶`, `(L − m)(β + w) + g(β)/2 + (1 + m)/2 ≤ L − 1/25000` when `m ≤ 1`, and with
`m` in place of `(1 + m)/2` when `m ≥ 1`. -/
theorem window_73 : WindowOK g73 (229 / 100) (4123 / 10000 * (229 / 100)) (4902 / 10000 * (229 / 100)) := by
  intro β m w hβ hβ1 hm hm1 hw hw1
  have hwm : (229 / 100 - m) * w ≤ 6 / 10 ^ 6 := by
    calc (229 / 100 - m) * w ≤ (3 / 2) * (4 / 10 ^ 6) := by
          apply mul_le_mul (by linarith) hw1 hw (by norm_num)
      _ = 6 / 10 ^ 6 := by norm_num
  unfold g73
  constructor
  · intro hm2
    split_ifs with h1 h2
    · nlinarith [mul_nonneg (sub_nonneg.2 hβ) (sub_nonneg.2 hm)]
    · nlinarith [mul_nonneg (sub_nonneg.2 (not_lt.1 h1)) (sub_nonneg.2 hm),
        mul_nonneg (sub_nonneg.2 h2.le) (sub_nonneg.2 hm)]
    · nlinarith [mul_nonneg (sub_nonneg.2 (not_lt.1 h2)) (sub_nonneg.2 hm),
        mul_nonneg (sub_nonneg.2 hβ1) (sub_nonneg.2 hm)]
  · intro hm2
    split_ifs with h1 h2
    · nlinarith [mul_nonneg (sub_nonneg.2 hβ) (sub_nonneg.2 hm1), mul_nonneg (sub_nonneg.2 h1.le) (sub_nonneg.2 hm1)]
    · nlinarith [mul_nonneg (sub_nonneg.2 (not_lt.1 h1)) (sub_nonneg.2 hm1),
        mul_nonneg (sub_nonneg.2 h2.le) (sub_nonneg.2 hm1)]
    · nlinarith [mul_nonneg (sub_nonneg.2 (not_lt.1 h2)) (sub_nonneg.2 hm1),
        mul_nonneg (sub_nonneg.2 hβ1) (sub_nonneg.2 hm1)]

/-- **Proposition 3′ for the curve at `L = 229/100`, pointwise in the heights, under `CGLDensity`.** Let `f0` be
smooth with support in `[1/2, 2]`, `K₀ ≥ 0`, `e₁ > 0` and `0 < η ≤ 10⁻⁵`. For every large `q`, every `P` with
`q^{(4123/10000)L} ≤ P ≤ q^{(4902/10000)L}`, `W(χ) = Σ_{m∈S} a_mχ(m)m^{−ih₀}` with `S ⊆ (P, 2P]`, and
`B(χ) = ∏_{j<K} Σ_{p ≤ 2Q_j} χ(p)(p/Q_j)^{−ih_j}f0(p/Q_j)` with `K ≤ K₀`, `Q_j ≥ q^{e₁}`, `|h_j| ≤ q^η` and
`∏_j Q_j ≤ 2^{K₀}q^L/P`: `Σ_{χ≠1} |W(χ)||B(χ)| ≤ q^{L−1/50000}(Σ_m |a_m|²/P)^{1/2}`. -/
theorem typeII_73 (hCGL : LinnikCGL.CGLDensity) {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0)
    (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2) (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η)
    (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (4123 / 10000 * (229 / 100) : ℝ) ≤ P → (P : ℝ) ≤ (q : ℝ) ^ (4902 / 10000 * (229 / 100) : ℝ) →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ (229 / 100 : ℝ) / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ (229 / 100 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) :=
  typeII_gen g73_le_one g73_half (counts_73 hCGL) window_73 hf0 hsupp K₀ he₁ hη hη1

end Curve

end SieveTypeII73

#print axioms SieveTypeII73.counts_73
#print axioms SieveTypeII73.window_73
#print axioms SieveTypeII73.typeII_73
