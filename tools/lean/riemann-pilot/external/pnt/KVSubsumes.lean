import LandauKV
import Rung3

/-! # The Korobov–Vinogradov width subsumes the growth chain (round 249)

`LandauKV.growthW_kv` gives `Landau.PolylogGrowth a K` for every `a > 2/3` (`polylogGrowth_of_KV`), hence `KVBridge`'s `zeroFree_kv`, `rung3_kv` and `Rung3.KVInput n₁ 3` for every `n₁ > 2/3`, without rounds 212–214's `GrowthSum` route.
-/

open Complex Filter

noncomputable section

namespace KVSubsumes

/-- The power width sits inside the KV width eventually: `L^{−a} ≤ wkv L` for `L ≥ L₀`, `a > 2/3`. -/
theorem wpow_le_wkv {a : ℝ} (ha : 2 / 3 < a) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L, L₀ ≤ L → L ^ (-a) ≤ LandauKV.wkv L := by
  set e := a - 2 / 3 with he
  have he0 : 0 < e := by rw [he]; linarith
  have hc := LandauKV.c2_pos
  refine ⟨max 2 ((2 / VinoKV.c2) ^ e⁻¹), le_max_left _ _, fun L hL => ?_⟩
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hE : 2 / VinoKV.c2 ≤ L ^ e := by
    have h1 : (2 / VinoKV.c2) ^ e⁻¹ ≤ L := (le_max_right _ _).trans hL
    have h2 := Real.rpow_le_rpow (by positivity) h1 he0.le
    rwa [Real.rpow_inv_rpow (by positivity) he0.ne'] at h2
  have hP : 0 < L ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hL0 _
  have hEpos : 0 < L ^ e := Real.rpow_pos_of_pos hL0 _
  have hsplit : L ^ a = L ^ ((2 : ℝ) / 3) * L ^ e := by
    rw [← Real.rpow_add hL0]; congr 1; rw [he]; ring
  have hlog : 1 ≤ Real.log (L + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith [LandauKV.e_le_three]
  have hq : (L + 2) ^ ((2 : ℝ) / 3) ≤ 2 * L ^ ((2 : ℝ) / 3) := by
    calc (L + 2) ^ ((2 : ℝ) / 3) ≤ (2 * L) ^ ((2 : ℝ) / 3) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = 2 ^ ((2 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) := Real.mul_rpow (by norm_num) hL0.le
      _ ≤ 2 * L ^ ((2 : ℝ) / 3) := by
          have h22 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
            calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          nlinarith
  have hlog23 : 1 ≤ Real.log (L + 2) ^ ((2 : ℝ) / 3) := Real.one_le_rpow hlog (by norm_num)
  have hQpos : 0 < (L + 2) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos (by linarith) _
  have hw : VinoKV.c2 / (2 * L ^ ((2 : ℝ) / 3)) ≤ LandauKV.wkv L := by
    unfold LandauKV.wkv LandauKV.fl
    rw [Real.div_rpow (Real.log_nonneg (by linarith)) (by linarith)]
    calc VinoKV.c2 / (2 * L ^ ((2 : ℝ) / 3)) ≤ VinoKV.c2 / (L + 2) ^ ((2 : ℝ) / 3) :=
          div_le_div_of_nonneg_left hc.le hQpos hq
      _ = VinoKV.c2 * (1 / (L + 2) ^ ((2 : ℝ) / 3)) := by ring
      _ ≤ VinoKV.c2 * (Real.log (L + 2) ^ ((2 : ℝ) / 3) / (L + 2) ^ ((2 : ℝ) / 3)) := by
          gcongr
  calc L ^ (-a) = (L ^ ((2 : ℝ) / 3) * L ^ e)⁻¹ := by rw [Real.rpow_neg hL0.le, hsplit]
    _ ≤ VinoKV.c2 / (2 * L ^ ((2 : ℝ) / 3)) := by
        rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : 2 ≤ L ^ e * VinoKV.c2 := (div_le_iff₀ hc).1 hE
        nlinarith
    _ ≤ LandauKV.wkv L := hw

/-- **The power-width growth hypothesis from the KV width** (replaces round 214's route). -/
theorem polylogGrowth_of_KV {a : ℝ} (ha : 2 / 3 < a) (_ha1 : a ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ Landau.PolylogGrowth a K := by
  obtain ⟨K₁, hK₁, hG⟩ := LandauKV.growthW_kv
  obtain ⟨L₀, hL₀, hcmp⟩ := wpow_le_wkv ha
  obtain ⟨M, hM⟩ := KVBridge.zeta_bound_compact (Real.exp L₀)
  refine ⟨max K₁ (max M 1), by positivity, fun t ht3 σ hσ hσ2 => ?_⟩
  have htpos : 0 < |t| := by linarith
  have hL1 : 1 ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le htpos]; linarith [LandauKV.e_le_three]
  have hK0 : 0 ≤ max K₁ (max M 1) := by positivity
  rcases le_or_gt L₀ (Real.log |t|) with hbig | hsmall
  · have hσ' : 1 - LandauKV.wkv (Real.log |t|) ≤ σ := by
      have := hcmp _ hbig; linarith
    have h := hG t ht3 σ hσ' hσ2
    calc ‖riemannZeta (σ + t * I)‖ ≤ K₁ * Real.log |t| ^ K₁ := h
      _ ≤ max K₁ (max M 1) * Real.log |t| ^ (max K₁ (max M 1)) := by
          apply mul_le_mul (le_max_left _ _)
            (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
            (Real.rpow_nonneg (by linarith) _) hK0
  · have htT : |t| ≤ Real.exp L₀ := by
      rw [← Real.exp_log htpos]; exact Real.exp_le_exp.mpr hsmall.le
    have hσ0 : 0 ≤ σ := by
      have : Real.log |t| ^ (-a) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
      linarith
    calc ‖riemannZeta (σ + t * I)‖ ≤ M := hM t σ ht3 htT hσ0 hσ2
      _ ≤ max K₁ (max M 1) := le_trans (le_max_left M 1) (le_max_right _ _)
      _ = max K₁ (max M 1) * 1 := (mul_one _).symm
      _ ≤ max K₁ (max M 1) * Real.log |t| ^ (max K₁ (max M 1)) := by
          gcongr
          exact Real.one_le_rpow hL1 hK0

/-- `zeroFree_kv`, re-proved through the KV width. -/
theorem zeroFree_kv' {n₁ : ℝ} (hn : 2 / 3 < n₁) : ZetaZeroFreeGenProp n₁ := by
  obtain ⟨h1, h2, h3⟩ := KVBridge.mid_exponent hn
  obtain ⟨K, hK, hG⟩ := polylogGrowth_of_KV h1 h2
  exact Landau.zeroFree_of_growth (by linarith) hK hG h3

/-- `rung3_kv`, re-proved through the KV width. -/
theorem rung3_kv' {n₁ : ℝ} (hn : 2 / 3 < n₁) :
    ∃ c > 0, (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop]
      (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁)))) := by
  obtain ⟨h1, h2, h3⟩ := KVBridge.mid_exponent hn
  obtain ⟨K, hK, hG⟩ := polylogGrowth_of_KV h1 h2
  exact Landau.rung3_of_growth (by linarith) h2 hK hG h3

/-- Round 192's named input `KVInput`, discharged for every `n₁ > 2/3` (with `n₂ = 3`). -/
theorem kvInput_of_KV {n₁ : ℝ} (hn : 2 / 3 < n₁) : Rung3.KVInput n₁ 3 := by
  obtain ⟨h1, h2, h3⟩ := KVBridge.mid_exponent hn
  obtain ⟨K, hK, hG⟩ := polylogGrowth_of_KV h1 h2
  exact ⟨Landau.zeroFree_of_growth (by linarith) hK hG h3,
    Landau.logDerivBnd_of_growth (by linarith) h2 hK hG h3⟩

end KVSubsumes

#print axioms KVSubsumes.wpow_le_wkv
#print axioms KVSubsumes.polylogGrowth_of_KV
#print axioms KVSubsumes.zeroFree_kv'
#print axioms KVSubsumes.rung3_kv'
#print axioms KVSubsumes.kvInput_of_KV
