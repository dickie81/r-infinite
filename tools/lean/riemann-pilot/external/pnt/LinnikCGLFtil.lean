/-
# Round 685: their smoothing `f̃_b`, and the inner integral of their `Σ_II` (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li bound the inner integral of their `Σ_II` after Poisson summation: "Let ψ(x) be a smooth bump function
supported on |x| ≪ 1 and define" (line 3649; spaces restored) `f̃_{b′}(u) := ∫_ℝTψ(T(u − v))f_{b′}(v) dv` (lines
3650–3653, transcribed), "We can then bound the above integral over u′ by" (line 3654; spaces restored)
`f̃_{b′}((qj + m₂u + bm₂ − b′m₂′)/m₂′)` (lines 3654–3658, transcribed), and "In the final line we have introduced a
sum over m₃ such that m₃ = qj + bm₂ − b′m₂′ for some integer j." (lines 3726–3728; spaces restored, the subscripts
transcribed). This file proves that bound, for round 684's `S₂`, and with it the majorant `H` that round 684's
`sum_psi_norm_Phi_sq_le` asks for.

The stack's form.
* Their `ψ` is round 656's bump `ψ̃₀`, which is `1` on `[−1, 1]`, and `f̃_b = (Tψ̃₀(T·)) ⋆ f_b` (Mathlib's
  `convolution`), so `∫_{|u−c|≤1/T}f_b ≤ f̃_b(c)/T` for `f_b ≥ 0` (`integral_indicator_le_ftil`).
* Their restriction of `j` to `|u′ − (qj + m₂u + bm₂ − b′m₂′)/m₂′| ≪ 1/T`, at an error `O((qT)^{−50})`, is the split
  `|ψ̂₀(y)| ≤ C_K[|y| ≤ V] + C_K(1 + V)^{−(K−2)}L₁(y)` (`norm_fourier_psiC_le_split`) with
  `Σ_kL₁(N₀k + z) ≤ 2π + 4π/N₀` (round 673's `sum_lor_le`); the error keeps its explicit factor
  `(1 + N₀m₂′/(qT))^{−(K−2)}`.
* Their sum over `j` becomes a sum over `m₃ = qj + k₀` with `m₃ ≡ bm₂ − b′m₂′ (mod q)` and `|m₃| ≤ (4|A| + 2)M₂`
  (`sum_ind_le`), for `|u|, |u′| ≤ |A|`, `T ≥ 1` and `m₂, m₂′ ∈ P2 M₂`.

Plain statements, with `q ≥ 1` (`[NeZero q]`), `L_c(r) = (1 + c²r²)⁻¹` round 673's `lor`, `C_K` round 684's `CK`,
`S₂` round 684's `S2`, `Φ(n, τ)` round 683's `Phi`, `x = (m₂′u′ − m₂u)/q`, `[·]` the indicator, and
`R = {m₃ ∈ ℤ : |m₃| ≤ (4|A| + 2)M₂}` (`R3`).
* `ftil`, `ftil_apply`, `continuous_ftil`, `ftil_nonneg`, `ftil_le`: `f̃_b(x) = ∫Tψ̃₀(Tt)f_b(x − t) dt`; for `T > 0`
  and integrable `f_b`, `f̃_b` is continuous; for `T ≥ 0` and `f_b ≥ 0`, `f̃_b ≥ 0`, and if `f_b` is also integrable,
  `f̃_b ≤ T∫f_b`.
* `integral_indicator_le_ftil`: for `T > 0` and integrable `f_b ≥ 0`, `∫_{|u−c|≤1/T}f_b(u) du ≤ f̃_b(c)/T`.
* `norm_fourier_psiC_le_split`: for `K ≥ 2` and `V ≥ 0`, `|ψ̂₀(y)| ≤ C_K[|y| ≤ V] + C_K(1 + V)^{−(K−2)}L₁(y)`.
* `sum_lor_lattice_le`: for `N₀ > 0`, `Σ_{k∈S}L₁(N₀k + z) ≤ 2π + 4π/N₀` for every finite set `S` of integers.
* `sum_ind_le`: for `T ≥ 1`, `N₀ > 0`, `m₂, m₂′ ∈ P2 M₂` and `|u|, |u′| ≤ |A|`, and every finite set `S` of integers,
  `Σ_{k∈S}[|N₀(k − x + k₀/q)| ≤ N₀m₂′/(qT)] ≤ Σ_{m₃∈R}[m₃ ≡ k₀][|u′ − (m₂u + m₃)/m₂′| ≤ 1/T]`, with `k₀` read as its
  value in `{0, …, q − 1}`.
* `norm_S2_le_split`: with the same hypotheses and `K ≥ 2`,
  `|S₂(k₀, x)| ≤ N₀C_K(Σ_{m₃∈R}[m₃ ≡ k₀][|u′ − (m₂u + m₃)/m₂′| ≤ 1/T] + (1 + N₀m₂′/(qT))^{−(K−2)}(2π + 4π/N₀))`.
* `Hmaj`, `integral_S2_le`: for smooth `f_b ≥ 0` that are `0` for `|u| > A`, `T ≥ 1`, `N₀ > 0`, `K ≥ 2`,
  `m₂, m₂′ ∈ P2 M₂` and `|u| ≤ |A|`, `∫f_{b′}(u′)|S₂(k₀, x)| du′ ≤ Hmaj = N₀C_K(Σ_{m₃∈R}[m₃ ≡ k₀]f̃_{b′}((m₂u +
  m₃)/m₂′)/T + (1 + N₀m₂′/(qT))^{−(K−2)}(2π + 4π/N₀)∫f_{b′})`.
* `sum_psi_norm_Phi_sq_le_ftil`: for smooth `f_b ≥ 0` that are `0` for `|u| > A`, `T ≥ 1`, `N₀ > 0` and `K ≥ 2`,
  `Σ_{n∈P3 N₀}ψ̃₀(n/N₀)|Φ(n, τ)|² ≤ Σ_{b,m₂,b′,m₂′}m₂m₂′∫f_b(u)Hmaj(b, m₂, b′, m₂′, u) du` for every `τ`, with
  `k₀ = bm₂ − b′m₂′` in `Hmaj`.

The file imports `LinnikCGLSig2.lean`.
-/

import LinnikCGLSig2

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate Convolution

noncomputable section

namespace LinnikCGLFtil

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLRFact LinnikCGLRam LinnikCGLJ LinnikCGLG
  LinnikCGLPois8 LinnikCGLCount LinnikCGLAsum LinnikCGLNsum LinnikCGLN0 LinnikCGLCov LinnikCGLSig2

/-! ### The smoothing `f̃_b` -/

/-- Their smoothing `f̃_b = (Tψ̃₀(T·)) ⋆ f_b`. -/
def ftil {q : ℕ} (f : (ZMod q)ˣ → ℝ → ℝ) (T : ℝ) (b : (ZMod q)ˣ) : ℝ → ℝ :=
  (fun t => T * psi0 (T * t)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f b

lemma ftil_apply {q : ℕ} (f : (ZMod q)ˣ → ℝ → ℝ) (T : ℝ) (b : (ZMod q)ˣ) (x : ℝ) :
    ftil f T b x = ∫ t, T * psi0 (T * t) * f b (x - t) := rfl

/-- For `T > 0` and integrable `f_b`, `f̃_b` is continuous. -/
lemma continuous_ftil {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} {T : ℝ} (hT : 0 < T) (b : (ZMod q)ˣ)
    (hfi : Integrable (f b)) : Continuous (ftil f T b) := by
  have hcs : HasCompactSupport (fun t : ℝ => T * psi0 (T * t)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(2 / T)) (b := 2 / T)) fun t ht => ?_
    have h2 : 2 ≤ |T * t| := by
      rw [abs_mul, abs_of_pos hT]
      by_contra hc
      push Not at hc
      exact ht (abs_le.mp ((lt_div_iff₀' hT).mpr hc).le)
    rw [psi0_eq_zero h2, mul_zero]
  exact hcs.continuous_convolution_left (L := ContinuousLinearMap.mul ℝ ℝ)
    (continuous_const.mul (continuous_psi0.comp (continuous_const.mul continuous_id))) hfi.locallyIntegrable

/-- For `T ≥ 0` and `f_b ≥ 0`, `f̃_b ≥ 0`. -/
lemma ftil_nonneg {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hf : ∀ b u, 0 ≤ f b u)
    (b : (ZMod q)ˣ) (x : ℝ) : 0 ≤ ftil f T b x := by
  rw [ftil_apply]
  exact integral_nonneg fun t => mul_nonneg (mul_nonneg hT (psi0_nonneg _)) (hf b _)

/-- For `T ≥ 0` and integrable `f_b ≥ 0`, `f̃_b ≤ T∫f_b`. -/
lemma ftil_le {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hf : ∀ b u, 0 ≤ f b u)
    (b : (ZMod q)ˣ) (hfi : Integrable (f b)) (x : ℝ) : ftil f T b x ≤ T * ∫ u, f b u := by
  rw [ftil_apply, ← integral_sub_left_eq_self (f b) volume x, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => mul_nonneg (mul_nonneg hT (psi0_nonneg _))
    (hf b _)) ((hfi.comp_sub_left x).const_mul T) (Eventually.of_forall fun t => ?_)
  have h1 := psi0_le_one (T * t)
  have h0 := hf b (x - t)
  have : 0 ≤ T * f b (x - t) * (1 - psi0 (T * t)) := mul_nonneg (mul_nonneg hT h0) (by linarith)
  dsimp only
  nlinarith

/-- **The window against `f̃_b`**: for `T > 0` and integrable `f_b ≥ 0`, `∫_{|u−c|≤1/T}f_b(u) du ≤ f̃_b(c)/T`. -/
lemma integral_indicator_le_ftil {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : ∀ b u, 0 ≤ f b u)
    (b : (ZMod q)ˣ) (hfi : Integrable (f b)) (c : ℝ) :
    ∫ u, (Metric.closedBall c (1 / T)).indicator (f b) u ≤ ftil f T b c / T := by
  rw [le_div_iff₀ hT, ← integral_sub_left_eq_self _ volume c, ← integral_mul_const, ftil_apply]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => ?_) ?_ (Eventually.of_forall fun t => ?_)
  · exact mul_nonneg (Set.indicator_nonneg (fun u _ => hf b u) _) hT.le
  · refine (hfi.comp_sub_left c).bdd_mul (c := T)
      (continuous_const.mul (continuous_psi0.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hT.le (psi0_nonneg _))]
    nlinarith [psi0_le_one (T * t), psi0_nonneg (T * t)]
  · dsimp only
    by_cases ht : |t| ≤ 1 / T
    · have hmem : c - t ∈ Metric.closedBall c (1 / T) := by
        rw [Metric.mem_closedBall, Real.dist_eq, show c - t - c = -t by ring, abs_neg]; exact ht
      have hpsi : psi0 (T * t) = 1 := by
        refine psi0_eq_one ?_
        rw [abs_mul, abs_of_pos hT]
        calc T * |t| ≤ T * (1 / T) := mul_le_mul_of_nonneg_left ht hT.le
          _ = 1 := by field_simp
      rw [Set.indicator_of_mem hmem, hpsi]
      ring_nf
      exact le_refl _
    · have hmem : c - t ∉ Metric.closedBall c (1 / T) := by
        rw [Metric.mem_closedBall, Real.dist_eq, show c - t - c = -t by ring, abs_neg]; exact ht
      rw [Set.indicator_of_notMem hmem, zero_mul]
      exact mul_nonneg (mul_nonneg hT.le (psi0_nonneg _)) (hf b _)

/-! ### The split of `ψ̂₀` and the lattice sums -/

/-- **The split of `ψ̂₀`**: for `K ≥ 2` and `V ≥ 0`, `|ψ̂₀(y)| ≤ C_K[|y| ≤ V] + C_K(1 + V)^{−(K−2)}L₁(y)`. -/
lemma norm_fourier_psiC_le_split {K : ℕ} (hK : 2 ≤ K) {V : ℝ} (hV : 0 ≤ V) (y : ℝ) :
    ‖𝓕 psiC y‖ ≤ CK K * (if |y| ≤ V then 1 else 0) + CK K * ((1 + V) ^ (K - 2))⁻¹ * lor 1 y := by
  have h := norm_fourier_psiC_le_CK K y
  have hpos : 0 < (1 + |y|) ^ K := by positivity
  have hCK : 0 ≤ CK K := le_trans (mul_nonneg hpos.le (norm_nonneg _)) h
  have h1 : ‖𝓕 psiC y‖ ≤ CK K / (1 + |y|) ^ K := by
    rw [le_div_iff₀ hpos]; linarith
  have hl : 0 ≤ lor 1 y := (lor_pos' _ _).le
  have hP : 0 < (1 + V) ^ (K - 2) := by positivity
  split_ifs with hy
  · have h2 : CK K / (1 + |y|) ^ K ≤ CK K := div_le_self hCK (one_le_pow₀ (by linarith [abs_nonneg y]))
    have h3 : 0 ≤ CK K * ((1 + V) ^ (K - 2))⁻¹ * lor 1 y := by positivity
    linarith
  · push Not at hy
    have hA : (1 + V) ^ (K - 2) ≤ (1 + |y|) ^ (K - 2) := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hB : 1 + 1 ^ 2 * y ^ 2 ≤ (1 + |y|) ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
    have hC : (1 + V) ^ (K - 2) * (1 + 1 ^ 2 * y ^ 2) ≤ (1 + |y|) ^ K := by
      calc (1 + V) ^ (K - 2) * (1 + 1 ^ 2 * y ^ 2) ≤ (1 + |y|) ^ (K - 2) * (1 + |y|) ^ 2 :=
            mul_le_mul hA hB (by positivity) (by positivity)
        _ = (1 + |y|) ^ K := by rw [← pow_add]; congr 1; omega
    have h4 : CK K / (1 + |y|) ^ K ≤ CK K / ((1 + V) ^ (K - 2) * (1 + 1 ^ 2 * y ^ 2)) :=
      div_le_div_of_nonneg_left hCK (by positivity) hC
    have h5 : CK K / ((1 + V) ^ (K - 2) * (1 + 1 ^ 2 * y ^ 2)) = CK K * ((1 + V) ^ (K - 2))⁻¹ * lor 1 y := by
      unfold lor; rw [div_eq_mul_inv, mul_inv]; ring
    linarith

/-- For `N₀ > 0`, `Σ_{k∈S}L₁(N₀k + z) ≤ 2π + 4π/N₀` for every finite set `S` of integers. -/
lemma sum_lor_lattice_le {N₀ : ℝ} (hN₀ : 0 < N₀) (z : ℝ) (S : Finset ℤ) :
    ∑ k ∈ S, lor 1 (N₀ * k + z) ≤ 2 * π + 4 * π / N₀ := by
  have hsep : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → N₀ ≤ |(fun k : ℤ => -(N₀ * k)) p - (fun k : ℤ => -(N₀ * k)) p'| := by
    intro p _ p' _ hne
    have h1 : (1 : ℝ) ≤ |(p : ℝ) - p'| := by
      have : (1 : ℤ) ≤ |p - p'| := Int.one_le_abs (sub_ne_zero.mpr hne)
      exact_mod_cast this
    calc N₀ = N₀ * 1 := by ring
      _ ≤ N₀ * |(p : ℝ) - p'| := mul_le_mul_of_nonneg_left h1 hN₀.le
      _ = |(fun k : ℤ => -(N₀ * k)) p - (fun k : ℤ => -(N₀ * k)) p'| := by
          simp only
          rw [show -(N₀ * p) - -(N₀ * p') = N₀ * (p' - p) by ring, abs_mul, abs_of_pos hN₀, abs_sub_comm]
  have h := sum_lor_le S (fun k : ℤ => -(N₀ * k)) hN₀ one_pos hsep z
  rw [one_mul] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) h
  congr 1; ring

/-! ### The window in residue classes -/

/-- Their range `|m₃| ≪ M₂`: `R = {m₃ : |m₃| ≤ (4|A| + 2)M₂}`. -/
def R3 (A M₂ : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌈(4 * |A| + 2) * M₂⌉) ⌈(4 * |A| + 2) * M₂⌉).filter fun m => |(m : ℝ)| ≤ (4 * |A| + 2) * M₂

lemma mem_R3 {A M₂ : ℝ} {m : ℤ} : m ∈ R3 A M₂ ↔ |(m : ℝ)| ≤ (4 * |A| + 2) * M₂ := by
  unfold R3
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have c := Int.le_ceil ((4 * |A| + 2) * M₂)
    have a := abs_le.mp h
    refine ⟨⟨?_, ?_⟩, h⟩
    · have : -((⌈(4 * |A| + 2) * M₂⌉ : ℤ) : ℝ) ≤ (m : ℝ) := by linarith
      exact_mod_cast this
    · have : (m : ℝ) ≤ ((⌈(4 * |A| + 2) * M₂⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this

/-- **The window in residue classes**: for `q ≥ 1`, `T ≥ 1`, `N₀ > 0`, `m₂, m₂′ ∈ P2 M₂`, `|u|, |u′| ≤ |A|` and every
finite set `S` of integers, `Σ_{k∈S}[|N₀(k − x + k₀/q)| ≤ N₀m₂′/(qT)] ≤ Σ_{m₃∈R}[m₃ ≡ k₀][|u′ − (m₂u + m₃)/m₂′| ≤ 1/T]`,
with `x = (m₂′u′ − m₂u)/q` and `k₀` read as its value in `{0, …, q − 1}`. -/
lemma sum_ind_le {q : ℕ} [NeZero q] {T N₀ M₂ A u u' : ℝ} (hT : 1 ≤ T) (hN₀ : 0 < N₀) {m₂ m₂' : ℤ}
    (hm₂ : m₂ ∈ P2 M₂) (hm₂' : m₂' ∈ P2 M₂) (hu : |u| ≤ |A|) (hu' : |u'| ≤ |A|) (k₀ : ZMod q) (S : Finset ℤ) :
    ∑ k ∈ S, (if |N₀ * (k - (((m₂' : ℝ) * u' - m₂ * u) / q - (k₀.val : ℝ) / q))| ≤ N₀ * m₂' / (q * T) then
        (1 : ℝ) else 0) ≤
      ∑ m ∈ R3 A M₂, (if (m : ZMod q) = k₀ ∧ |u' - (m₂ * u + m) / m₂'| ≤ 1 / T then (1 : ℝ) else 0) := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hT0 : 0 < T := by linarith
  have h2 := (mem_P2 m₂).1 hm₂
  have h2' := (mem_P2 m₂').1 hm₂'
  have hM₂ : 0 < M₂ := by linarith [h2.1, h2.2]
  have hp2 : (0 : ℝ) < m₂ := by linarith [h2.1]
  have hp2' : (0 : ℝ) < m₂' := by linarith [h2'.1]
  set G : ℤ → ℝ := fun m => if (m : ZMod q) = k₀ ∧ |u' - (m₂ * u + m) / m₂'| ≤ 1 / T then 1 else 0 with hG
  -- each term is `G(qk + k₀)`
  have hterm : ∀ k : ℤ, (if |N₀ * (k - (((m₂' : ℝ) * u' - m₂ * u) / q - (k₀.val : ℝ) / q))| ≤
      N₀ * m₂' / (q * T) then (1 : ℝ) else 0) = G (q * k + k₀.val) := by
    intro k
    have hres : (((q * k + k₀.val : ℤ) : ZMod q)) = k₀ := by
      push_cast
      rw [ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_zmod_val]
    have e : N₀ * (k - (((m₂' : ℝ) * u' - m₂ * u) / q - (k₀.val : ℝ) / q)) =
        (N₀ * m₂' / q) * ((m₂ * u + ((q * k + k₀.val : ℤ) : ℝ)) / m₂' - u') := by
      push_cast
      field_simp
      ring
    have hiff : |N₀ * (k - (((m₂' : ℝ) * u' - m₂ * u) / q - (k₀.val : ℝ) / q))| ≤ N₀ * m₂' / (q * T) ↔
        |u' - (m₂ * u + ((q * k + k₀.val : ℤ) : ℝ)) / m₂'| ≤ 1 / T := by
      rw [e, abs_mul, abs_of_pos (by positivity), abs_sub_comm,
        show N₀ * m₂' / (q * T) = N₀ * m₂' / q * (1 / T) by field_simp]
      exact mul_le_mul_iff_of_pos_left (by positivity)
    rw [hG]
    simp only [hres, true_and, hiff]
  simp_rw [hterm]
  -- the map `k ↦ qk + k₀` is injective
  have hinj : Set.InjOn (fun k : ℤ => (q : ℤ) * k + k₀.val) S := by
    intro k₁ _ k₂ _ h
    have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
    have : (q : ℤ) * k₁ = q * k₂ := by simpa using h
    exact mul_left_cancel₀ hq' this
  rw [← Finset.sum_image (f := G) hinj]
  -- the image lies in `R` wherever `G ≠ 0`
  have hG0 : ∀ m, 0 ≤ G m := fun m => by simp only [hG]; split_ifs <;> norm_num
  have hout : ∀ m, m ∉ R3 A M₂ → G m = 0 := by
    intro m hm
    simp only [hG]
    split_ifs with hcond
    swap
    · rfl
    exfalso
    obtain ⟨-, hw⟩ := hcond
    apply hm
    rw [mem_R3]
    have h1T : 1 / T ≤ 1 := by rw [div_le_one hT0]; exact hT
    have hc : |(m₂ * u + m) / m₂'| ≤ |A| + 1 := by
      have := abs_sub_abs_le_abs_sub ((m₂ * u + m) / m₂') u'
      rw [abs_sub_comm] at hw
      linarith
    have hc' : |(m₂ : ℝ) * u + m| ≤ m₂' * (|A| + 1) := by
      rw [abs_div, abs_of_pos hp2', div_le_iff₀ hp2'] at hc
      linarith
    have hmu : |(m₂ : ℝ) * u| ≤ m₂ * |A| := by
      rw [abs_mul, abs_of_pos hp2]; exact mul_le_mul_of_nonneg_left hu hp2.le
    have htri : |(m : ℝ)| ≤ |(m₂ : ℝ) * u + m| + |(m₂ : ℝ) * u| := by
      have := abs_sub ((m₂ : ℝ) * u + m) ((m₂ : ℝ) * u)
      rw [show (m₂ : ℝ) * u + m - m₂ * u = m by ring] at this
      exact this
    have hA0 : 0 ≤ |A| := abs_nonneg A
    nlinarith [h2.2, h2'.2]
  rw [← Finset.sum_filter_add_sum_filter_not (S.image fun k : ℤ => (q : ℤ) * k + k₀.val) (· ∈ R3 A M₂)]
  rw [Finset.sum_eq_zero (s := (S.image fun k : ℤ => (q : ℤ) * k + k₀.val).filter (fun m => ¬m ∈ R3 A M₂))
    fun m hm => hout m (Finset.mem_filter.1 hm).2, add_zero]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => (Finset.mem_filter.1 hm).2) fun m _ _ => hG0 m

/-! ### `S₂` and the inner integral -/

/-- **`S₂` split**: for `q ≥ 1`, `T ≥ 1`, `N₀ > 0`, `K ≥ 2`, `m₂, m₂′ ∈ P2 M₂` and `|u|, |u′| ≤ |A|`,
`|S₂(k₀, x)| ≤ N₀C_K(Σ_{m₃∈R}[m₃ ≡ k₀][|u′ − (m₂u + m₃)/m₂′| ≤ 1/T] + (1 + N₀m₂′/(qT))^{−(K−2)}(2π + 4π/N₀))`. -/
theorem norm_S2_le_split {q : ℕ} [NeZero q] {T N₀ M₂ A u u' : ℝ} (hT : 1 ≤ T) (hN₀ : 0 < N₀) {K : ℕ}
    (hK : 2 ≤ K) {m₂ m₂' : ℤ} (hm₂ : m₂ ∈ P2 M₂) (hm₂' : m₂' ∈ P2 M₂) (hu : |u| ≤ |A|) (hu' : |u'| ≤ |A|)
    (k₀ : ZMod q) :
    ‖S2 q N₀ k₀ (((m₂' : ℝ) * u' - m₂ * u) / q)‖ ≤
      N₀ * CK K * (∑ m ∈ R3 A M₂, (if (m : ZMod q) = k₀ ∧ |u' - (m₂ * u + m) / m₂'| ≤ 1 / T then (1 : ℝ) else 0) +
        ((1 + N₀ * m₂' / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hT0 : 0 < T := by linarith
  have hp2' : (0 : ℝ) < m₂' := by have := (mem_P2 m₂').1 hm₂'; linarith [this.1, this.2]
  set x : ℝ := ((m₂' : ℝ) * u' - m₂ * u) / q with hx
  set V : ℝ := N₀ * m₂' / (q * T) with hV
  have hV0 : 0 ≤ V := by positivity
  set ind : ℤ → ℝ := fun k => if |N₀ * (k - (x - (k₀.val : ℝ) / q))| ≤ V then 1 else 0 with hind
  set lk : ℤ → ℝ := fun k => lor 1 (N₀ * k + -(N₀ * (x - (k₀.val : ℝ) / q))) with hlk
  have hCK : 0 ≤ CK K := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (norm_fourier_psiC_le_CK K 0)
  obtain ⟨hs, hS2⟩ := norm_S2_le hN₀ k₀ x
  have hind0 : 0 ≤ ind := fun k => by simp only [hind]; split_ifs <;> norm_num
  have hindS : ∀ S : Finset ℤ, ∑ k ∈ S, ind k ≤ ∑ m ∈ R3 A M₂,
      (if (m : ZMod q) = k₀ ∧ |u' - (m₂ * u + m) / m₂'| ≤ 1 / T then (1 : ℝ) else 0) := fun S =>
    sum_ind_le hT hN₀ hm₂ hm₂' hu hu' k₀ S
  have hind_s : Summable ind := summable_of_sum_le hind0 hindS
  have hlk0 : 0 ≤ lk := fun k => (lor_pos' _ _).le
  have hlkS : ∀ S : Finset ℤ, ∑ k ∈ S, lk k ≤ 2 * π + 4 * π / N₀ := fun S => sum_lor_lattice_le hN₀ _ S
  have hlk_s : Summable lk := summable_of_sum_le hlk0 hlkS
  have hpt : ∀ k : ℤ, ‖𝓕 psiC (N₀ * (k - (x - (k₀.val : ℝ) / q)))‖ ≤
      CK K * ind k + CK K * ((1 + V) ^ (K - 2))⁻¹ * lk k := by
    intro k
    have h := norm_fourier_psiC_le_split hK hV0 (N₀ * (k - (x - (k₀.val : ℝ) / q)))
    simp only [hind, hlk]
    rw [show N₀ * (k : ℝ) + -(N₀ * (x - (k₀.val : ℝ) / q)) = N₀ * (k - (x - (k₀.val : ℝ) / q)) by ring]
    exact h
  have hsum : ∑' k : ℤ, ‖𝓕 psiC (N₀ * (k - (x - (k₀.val : ℝ) / q)))‖ ≤
      CK K * ∑ m ∈ R3 A M₂, (if (m : ZMod q) = k₀ ∧ |u' - (m₂ * u + m) / m₂'| ≤ 1 / T then (1 : ℝ) else 0) +
        CK K * ((1 + V) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) := by
    refine (hs.tsum_le_tsum hpt ((hind_s.mul_left _).add (hlk_s.mul_left _))).trans ?_
    rw [(hind_s.mul_left _).tsum_add (hlk_s.mul_left _), tsum_mul_left, tsum_mul_left]
    have h1 := Real.tsum_le_of_sum_le hind0 hindS
    have h2 := Real.tsum_le_of_sum_le hlk0 hlkS
    have hP : 0 ≤ CK K * ((1 + V) ^ (K - 2))⁻¹ := by positivity
    gcongr
  calc ‖S2 q N₀ k₀ x‖ ≤ N₀ * ∑' k : ℤ, ‖𝓕 psiC (N₀ * (k - (x - (k₀.val : ℝ) / q)))‖ := hS2
    _ ≤ N₀ * (CK K * ∑ m ∈ R3 A M₂, (if (m : ZMod q) = k₀ ∧ |u' - (m₂ * u + m) / m₂'| ≤ 1 / T then (1 : ℝ) else 0) +
        CK K * ((1 + V) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀)) := mul_le_mul_of_nonneg_left hsum hN₀.le
    _ = _ := by ring

/-- The majorant of the inner integral: `N₀C_K(Σ_{m₃∈R}[m₃ ≡ k₀]f̃_{b′}((m₂u + m₃)/m₂′)/T +
(1 + N₀m₂′/(qT))^{−(K−2)}(2π + 4π/N₀)∫f_{b′})`, with `k₀ = bm₂ − b′m₂′`. -/
def Hmaj {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (A M₂ T N₀ : ℝ) (K : ℕ) (b : (ZMod q)ˣ) (m₂ : ℤ)
    (b' : (ZMod q)ˣ) (m₂' : ℤ) (u : ℝ) : ℝ :=
  N₀ * CK K * (∑ m ∈ R3 A M₂, (if (m : ZMod q) = (b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q) then
      ftil f T b' ((m₂ * u + m) / m₂') / T else 0) +
    ((1 + N₀ * m₂' / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) * ∫ v, f b' v)

/-- **The inner integral**: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A`, `T ≥ 1`, `N₀ > 0`, `K ≥ 2`,
`m₂, m₂′ ∈ P2 M₂` and `|u| ≤ |A|`, `∫f_{b′}(u′)|S₂(bm₂ − b′m₂′, x)| du′ ≤ Hmaj(b, m₂, b′, m₂′, u)`. -/
theorem integral_S2_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) (hf : ∀ b u, 0 ≤ f b u) {T N₀ M₂ : ℝ} (hT : 1 ≤ T) (hN₀ : 0 < N₀) {K : ℕ}
    (hK : 2 ≤ K) (b : (ZMod q)ˣ) {m₂ : ℤ} (hm₂ : m₂ ∈ P2 M₂) (b' : (ZMod q)ˣ) {m₂' : ℤ} (hm₂' : m₂' ∈ P2 M₂)
    {u : ℝ} (hu : |u| ≤ |A|) :
    ∫ u', f b' u' *
      ‖S2 q N₀ ((b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q)) (((m₂' : ℝ) * u' - m₂ * u) / q)‖ ≤
      Hmaj f A M₂ T N₀ K b m₂ b' m₂' u := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hT0 : 0 < T := by linarith
  have hfi : ∀ b, Integrable (f b) := fun b => (hfs b).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -|A|) (b := |A|)) fun u hu => hA b u
      (lt_of_le_of_lt (le_abs_self A) (not_le.mp fun h => hu (abs_le.mp h))))
  set k₀ : ZMod q := (b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q) with hk₀
  have hp2' : (0 : ℝ) < m₂' := by have := (mem_P2 m₂').1 hm₂'; linarith [this.1, this.2]
  set E : ℝ := ((1 + N₀ * m₂' / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) with hE
  have hE0 : 0 ≤ E := by positivity
  have hCK : 0 ≤ CK K := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (norm_fourier_psiC_le_CK K 0)
  set c : ℤ → ℝ := fun m => (m₂ * u + m) / m₂' with hc
  -- the pointwise majorant
  set g : ℝ → ℝ := fun u' => N₀ * CK K * (∑ m ∈ R3 A M₂,
    (if (m : ZMod q) = k₀ then (Metric.closedBall (c m) (1 / T)).indicator (f b') u' else 0) + E * f b' u')
    with hg
  have hgi : Integrable g := by
    refine (Integrable.add (integrable_finsetSum _ fun m _ => ?_) ((hfi b').const_mul E)).const_mul _
    split_ifs
    · exact (hfi b').indicator Metric.isClosed_closedBall.measurableSet
    · exact integrable_zero _ _ _
  have hpt : ∀ u', f b' u' * ‖S2 q N₀ k₀ (((m₂' : ℝ) * u' - m₂ * u) / q)‖ ≤ g u' := by
    intro u'
    by_cases hu' : |u'| ≤ |A|
    · have h := norm_S2_le_split hT hN₀ hK hm₂ hm₂' hu hu' k₀
      have hf0 := hf b' u'
      calc f b' u' * ‖S2 q N₀ k₀ (((m₂' : ℝ) * u' - m₂ * u) / q)‖
          ≤ f b' u' * (N₀ * CK K * (∑ m ∈ R3 A M₂,
            (if (m : ZMod q) = k₀ ∧ |u' - (m₂ * u + m) / m₂'| ≤ 1 / T then (1 : ℝ) else 0) + E)) :=
            mul_le_mul_of_nonneg_left h hf0
        _ = g u' := by
            have hsum : f b' u' * ∑ m ∈ R3 A M₂,
                (if (m : ZMod q) = k₀ ∧ |u' - (m₂ * u + m) / m₂'| ≤ 1 / T then (1 : ℝ) else 0) =
                ∑ m ∈ R3 A M₂, (if (m : ZMod q) = k₀ then
                  (Metric.closedBall (c m) (1 / T)).indicator (f b') u' else 0) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun m _ => ?_
              by_cases hm : (m : ZMod q) = k₀
              · by_cases hw : |u' - (m₂ * u + m) / m₂'| ≤ 1 / T
                · have hmem : u' ∈ Metric.closedBall (c m) (1 / T) := by
                    rw [Metric.mem_closedBall, Real.dist_eq, hc]; exact hw
                  rw [ite_eq_left ⟨hm, hw⟩, ite_eq_left hm, Set.indicator_of_mem hmem, mul_one]
                · have hmem : u' ∉ Metric.closedBall (c m) (1 / T) := by
                    rw [Metric.mem_closedBall, Real.dist_eq, hc]; exact hw
                  rw [ite_eq_right (fun h => hw h.2), ite_eq_left hm, Set.indicator_of_notMem hmem, mul_zero]
              · rw [ite_eq_right (fun h => hm h.1), ite_eq_right hm, mul_zero]
            rw [hg]
            simp only
            rw [← hsum]
            ring
    · have hz : f b' u' = 0 := hA b' u' (lt_of_le_of_lt (le_abs_self A) (not_le.mp hu'))
      rw [hz, zero_mul]
      rw [hg]
      simp only
      refine mul_nonneg (by positivity) (add_nonneg (Finset.sum_nonneg fun m _ => ?_) (mul_nonneg hE0 (hf b' u')))
      split_ifs
      · exact Set.indicator_nonneg (fun v _ => hf b' v) _
      · exact le_refl 0
  refine (integral_mono_of_nonneg (Eventually.of_forall fun u' => mul_nonneg (hf b' u') (norm_nonneg _)) hgi
    (Eventually.of_forall hpt)).trans ?_
  rw [hg, integral_const_mul, integral_add (integrable_finsetSum _ fun m _ => ?_) ((hfi b').const_mul E),
    integral_finsetSum _ fun m _ => ?_, integral_const_mul]
  · unfold Hmaj
    rw [← hk₀, ← hE]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    gcongr with m hm
    split_ifs
    · exact integral_indicator_le_ftil hT0 hf b' (hfi b') (c m)
    · rw [integral_zero]
  · split_ifs
    · exact (hfi b').indicator Metric.isClosed_closedBall.measurableSet
    · exact integrable_zero _ _ _
  · split_ifs
    · exact (hfi b').indicator Metric.isClosed_closedBall.measurableSet
    · exact integrable_zero _ _ _

/-! ### Their `Σ_II`, before the return to `J(f̃⃗)` -/

/-- **Their `Σ_II` with the majorant**: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A`, `T ≥ 1`, `N₀ > 0`
and `K ≥ 2`, `Σ_{n∈P3 N₀}ψ̃₀(n/N₀)|Φ(n, τ)|² ≤ Σ_{b,m₂,b′,m₂′}m₂m₂′∫f_b(u)Hmaj(b, m₂, b′, m₂′, u) du` for every
`τ`. -/
theorem sum_psi_norm_Phi_sq_le_ftil {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) (hf : ∀ b u, 0 ≤ f b u) {T N₀ : ℝ} (hT : 1 ≤ T) (hN₀ : 0 < N₀)
    {K : ℕ} (hK : 2 ≤ K) (M₂ L τ : ℝ) :
    ∑ n ∈ P3 N₀, psi0 (n / N₀) * ‖Phi f M₂ L n τ‖ ^ 2 ≤
      ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂,
        (m₂ : ℝ) * m₂' * ∫ u, f b u * Hmaj f A M₂ T N₀ K b m₂ b' m₂' u := by
  have hT0 : 0 < T := by linarith
  have hfi : ∀ b, Integrable (f b) := fun b => (hfs b).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -|A|) (b := |A|)) fun u hu => hA b u
      (lt_of_le_of_lt (le_abs_self A) (not_le.mp fun h => hu (abs_le.mp h))))
  refine sum_psi_norm_Phi_sq_le hfs hA hf M₂ L N₀ τ (Hmaj f A M₂ T N₀ K) (fun b m₂ hm₂ b' m₂' hm₂' => ?_)
    (fun b m₂ hm₂ b' m₂' hm₂' u hu => ?_)
  · -- `f_b · Hmaj` is integrable: `Hmaj` is continuous and bounded in `u`
    have hcont : Continuous fun u => Hmaj f A M₂ T N₀ K b m₂ b' m₂' u := by
      unfold Hmaj
      refine continuous_const.mul (Continuous.add (continuous_finsetSum _ fun m _ => ?_) continuous_const)
      split_ifs
      · exact ((continuous_ftil hT0 b' (hfi b')).comp (by fun_prop)).div_const _
      · exact continuous_const
    refine (hfi b).mul_bdd (c := N₀ * CK K * (∑ m ∈ R3 A M₂, (∫ v, f b' v) +
      ((1 + N₀ * m₂' / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) * ∫ v, f b' v)) hcont.aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    have hCK : 0 ≤ CK K := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (norm_fourier_psiC_le_CK K 0)
    have hI : 0 ≤ ∫ v, f b' v := integral_nonneg fun v => hf b' v
    have hp2' : (0 : ℝ) < m₂' := by have := (mem_P2 m₂').1 hm₂'; linarith [this.1, this.2]
    have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hE0 : 0 ≤ ((1 + N₀ * m₂' / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) := by positivity
    have hterm : ∀ m ∈ R3 A M₂, 0 ≤ (if (m : ZMod q) = (b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q)
        then ftil f T b' ((m₂ * u + m) / m₂') / T else 0) ∧
        (if (m : ZMod q) = (b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q)
        then ftil f T b' ((m₂ * u + m) / m₂') / T else 0) ≤ ∫ v, f b' v := by
      intro m _
      split_ifs
      · refine ⟨div_nonneg (ftil_nonneg hT0.le hf b' _) hT0.le, ?_⟩
        rw [div_le_iff₀ hT0]
        linarith [ftil_le hT0.le hf b' (hfi b') ((m₂ * u + m) / m₂')]
      · exact ⟨le_refl 0, hI⟩
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · unfold Hmaj
      refine mul_le_mul_of_nonneg_left (add_le_add (Finset.sum_le_sum fun m hm => (hterm m hm).2) le_rfl)
        (by positivity)
    · unfold Hmaj
      exact mul_nonneg (by positivity) (add_nonneg (Finset.sum_nonneg fun m hm => (hterm m hm).1)
        (mul_nonneg hE0 hI))
  · -- the inner integral, wherever `f_b(u) ≠ 0`
    have hu' : |u| ≤ |A| := by
      by_contra h
      exact hu (hA b u (lt_of_le_of_lt (le_abs_self A) (not_le.mp h)))
    exact integral_S2_le hfs hA hf hT hN₀ hK b hm₂ b' hm₂' hu'

end LinnikCGLFtil

#print axioms LinnikCGLFtil.integral_indicator_le_ftil
#print axioms LinnikCGLFtil.sum_ind_le
#print axioms LinnikCGLFtil.norm_S2_le_split
#print axioms LinnikCGLFtil.integral_S2_le
#print axioms LinnikCGLFtil.sum_psi_norm_Phi_sq_le_ftil
