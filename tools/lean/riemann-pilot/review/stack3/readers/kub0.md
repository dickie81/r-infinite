<!-- Stack review 3 reader report: model output, a list of CANDIDATES, not findings. STRUCTURAL-REVIEW.md §9.2 and §9.7 record what the lead verified (Check 3). Scratchpad paths below are the reader's session files, not committed. -->

Running mandatory review protocol. Checks 0–9 active.

Read-only throughout. I created, edited and built nothing. All commands below are grep/sed/diff/wc, plus python3 heredocs that only read files: a token-index use census and an import-closure walk over `import` lines. Line numbers are in tools/lean/riemann-pilot.

COVERAGE
KubotaBall.lean: lines 1–560 read
KubotaBallCount.lean: lines 1–280 read
KubotaBallKernel.lean: lines 1–358 read
KubotaBallOp.lean: lines 1–337 read
KubotaBesselMellin.lean: lines 1–339 read
KubotaCTCover.lean: lines 1–609 read
KubotaCTPrinciple.lean: lines 1–306 read
KubotaCharacter.lean: lines 1–627 read
KubotaCoefPrime.lean: lines 1–237 read
KubotaCoefResidue.lean: lines 1–228 read
KubotaCoefScalar.lean: lines 1–451 read
KubotaCoefSqfree.lean: lines 1–280 read
KubotaCoefSupp.lean: lines 1–340 read
KubotaCoefUnit.lean: lines 1–157 read
KubotaCompleted.lean: lines 1–547 read
KubotaConstTerm.lean: lines 1–677 read
KubotaContour.lean: lines 1–835 read
KubotaCubeCoef.lean: lines 1–276 read
KubotaCubeCover.lean: lines 1–378 read
KubotaCubeDecomp.lean: lines 1–532 read
KubotaCubeEigen.lean: lines 1–449 read
KubotaCubeSum.lean: lines 1–687 read

Excluded because §9 already lists them: sq_norm_σO/norm_sq_σO, absNorm_span_one_add_three_ω/absNorm_span_seven_pt, the cpow_ofReal_* pairs, and kubHom.

CANDIDATES

1. (D) src/KubotaBall.lean:102–128
`theorem pinv_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) : PInv (actP g) := by`
- Same proof at src/KubotaMeasure.lean:314–337 `theorem uinv_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) : UInv (actP g) := by`.
- Same proof at src/KubotaEnergy.lean:211–234 `theorem conf_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) : Conf (actP g) := by`.
- Each comes with its own comp/congr/mul helpers: PInv.comp and PInv.congr at KubotaBall:51,56 plus a local hmul at 104–106; UInv.comp/.congr/.mul at KubotaMeasure:132,137,308; Conf.comp/.congr/.mul at KubotaEnergy:98,108,206.
- Commands:
  - `grep -n "by_cases hc : g 1 0 = 0\|!!\[1, g 0 0 / g 1 0; 0, 1\] \* !!\[0, -1; 1, 0\]" src/*.lean` hits only those three proofs (KubotaBall 107/116/121/123, KubotaEnergy 213/222/227/229, KubotaMeasure 316/325/330/332).
  - `diff <(sed -n 107,128p src/KubotaBall.lean | sed 's/hmul/MUL/g;s/pinv_/X_/g') <(sed -n 316,337p src/KubotaMeasure.lean | sed 's/UInv.mul/MUL/g;s/uinv_actP_/X_/g')` differs only in line wrapping.
- Candidate: the 22-line SL₂(ℂ) decomposition is proved three times. One induction principle would serve all three: a property of actP g that is closed under det-1 products and holds for translations, diagonals and E holds for every det-1 g.

2. (D)+(B) src/KubotaCoefScalar.lean:145–182 (inside `theorem rhoM_primary_eq_zero ... (h1 : rhoM 1 r Y hY = 0) {x : 𝓞 K} (hx : Primary x) : rhoM x r Y hY = 0`, line 131)
- Copy at src/KubotaCoefSupp.lean:161–198, inside `theorem rhoM_supp_norm` (line 141).
- Partial third copy at src/KubotaCoefSqfree.lean:203–225 (rhoM_mul_cube).
- Command: `diff <(sed -n 145,191p src/KubotaCoefScalar.lean | <rename x→Y>) <(sed -n 161,212p src/KubotaCoefSupp.lean | <rename y→Y>)`. The first 38 lines are identical; they cover hI0, hIu, the normalizedFactors prime, hP3, pgen, hp0, hp, hNp, hNmul, hNpos and hpx.
- Candidate: the 38-line "primary prime factor of a non-unit primary" block is duplicated.
- rhoM_supp_norm is downstream (round 458) and implies rhoM_primary_eq_zero at z = 1: a primary prime dividing 1 is impossible, and ‖ρ(y)‖ = ‖σ b‖·‖ρ(1)‖ = 0.

3. (A) Inline re-proofs inside those blocks.
- KubotaCoefScalar:141–142, KubotaCoefSqfree:199–200 and KubotaCoefSupp:155–156 each have `have : x = 1 := primary_unique hx primary_one (by rw [Ideal.span_singleton_eq_top.2 hu, Ideal.span_singleton_one])` (variable names vary).
  - This is src/KubotaCharacter.lean:52 `theorem primary_eq_one_of_isUnit {a : 𝓞 K} (ha : Primary a) (hu : IsUnit a) : a = 1 :=`, which is in all three files' import closure.
- KubotaCoefScalar:153–160 and KubotaCoefSupp:169–176 each have `have hP3 : (3 : 𝓞 K) ∉ P := by` (8 lines).
  - This is src/EisensteinCubicRecip.lean:171 `theorem three_not_mem_of_primary_mem {P : Ideal (𝓞 K)} (hP : P ≠ ⊤) {a : 𝓞 K} (ha : Primary a) (haP : a ∈ P) : (3 : 𝓞 K) ∉ P`, i.e. `three_not_mem_of_primary_mem hPm.ne_top hx hxP`.
- Commands: `grep -rn "primary_unique [a-z]* primary_one" src/*.lean` hits the three sites plus KubotaCharacter:53; `grep -rn "theorem three_not_mem_of_primary" -A 8 src/*.lean`.
- Candidate: five inline blocks re-prove two existing lemmas.

4. (D) src/KubotaCubeEigen.lean:68 `theorem integrable_cubeDiff_slAct` (75–113) and 117 `theorem integrable_cubeDiff_inv_slAct` (127–147)
- Copied from src/KubotaCubeDecomp.lean:404 `theorem integral_cubeDiff_slAct` and 475 `theorem integral_cubeDiff_inv_slAct`.
- Commands:
  - `diff <(sed -n 484,502p KubotaCubeDecomp) <(sed -n 127,145p KubotaCubeEigen)`: identical (19 lines).
  - Lines 411–417 = 75–81; 452–458 = 104–110 (identical).
  - Lines 425–442 vs 84–100 differ only in a `-` binder and one line wrap.
- Candidate: the integral lemmas already prove the integrability internally (`key q` returns `Integrable … ∧ …`; hi0). A combined "Integrable ∧ integral = 0" lemma would remove about 50 duplicated lines.

5. (D) src/KubotaConstTerm.lean:119–142
`theorem lintegral_tile3 {G : ℂ → ℝ≥0∞} (hG : Measurable G) : ∫⁻ x, G x = ∑' t : 𝓞 K, ∫⁻ y in fundP3, G (y + σO (3 * t))`
- Copy of src/KubotaGrowth.lean:81–102 `theorem lintegral_tile {G : ℂ → ℝ≥0∞} (hG : Measurable G) : ∫⁻ x, G x = ∑' t : 𝓞 K, ∫⁻ y in fundP, G (y + σO t)`. KubotaGrowth is in KubotaConstTerm's closure.
- Command: diff after renaming fundP3→F, σO(3·t)→σO t. Only line wrapping and one rewrite step differ.
- Candidate: one tiling lemma for any set S with Σ_t 1_S(w + τ t) = 1 would cover fundP and fundP3; tsum_fundP3 (106) is likewise derived from tsum_fundP.

6. (D) src/KubotaCompleted.lean:37–66
`theorem sqfree_cube_unique {D D' E E' : Ideal (𝓞 K)} (hD : Squarefree D) (hD' : Squarefree D') (hE : E ≠ ⊥) (h : D * E ^ 3 = D' * E' ^ 3) : D = D' ∧ E = E'`
- Copy of src/EisensteinQuadSieveSquares.lean:37–66 `theorem sqfree_sq_unique … (h : D * E ^ 2 = D' * E' ^ 2) : D = D' ∧ E = E'`, which is in the closure.
- Command: diff after renaming ^2/^3 → ^N, hE2/hE3 → hEN: rc=0, identical (28 lines).
- Candidate: one `sqfree_pow_unique (2 ≤ n)` would serve both.

7. (D) src/KubotaBall.lean:174–185 (in bavg_cpow) vs src/KubotaBallCount.lean:107–118 (in uhsMeasure_hball)
- Both build `a = √p.2`, `g = T_{p.1}·diag(a)`, `hg`, and `hgp : actP g (0, 1) = p`.
- Command: `diff <(sed -n 174,185p src/KubotaBall.lean) <(sed -n 107,118p src/KubotaBallCount.lean)`: identical (12 lines). `grep -rn "actP g (0, 1) = p\|sqrt p.2" src/*.lean` finds only these two.
- Candidate: a lemma "∃ g, det g = 1 ∧ actP g (0,1) = p" would replace both.

8. (D) src/KubotaBallCount.lean:59–74 `theorem measurable_hball_ind (R : ℝ) (γ : SL(2, 𝓞 K)) : Measurable fun x … => (hball R x.1).indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ x.2)` vs src/KubotaBallOp.lean:73–88 `theorem measurable_hball_indC … (1 : ℂ × ℝ → ℂ) …`
- Command: diff after normalising the codomain shows only a `with hSdef` difference (16 lines).
- Candidate: one lemma generic in the codomain (Zero, One, MeasurableSpace) would serve both.

9. (D) src/KubotaCTCover.lean:75–91 `theorem integral_muR_actP` vs 94–111 `theorem integral_muR_slAct`, and 60–71 `lintegral_muR_actP` vs 114–125 `lintegral_muR_slAct`
- Command: diffs show only the renaming `actP g⁻¹ ↔ slAct γ`, plus the closing rewrite (actP_inv_actP vs slAct_slAct_inv).
- slAct γ is `actP ((γ : Matrix …).map σO)` (src/KubotaSiegel.lean:40).
- Candidate: the slAct versions are the actP versions at g = σ(γ⁻¹) (14- and 9-line copies).

10. (D) src/KubotaCTCover.lean:158–180 (in `theorem integral_isPU_eq`, line 144)
- Lifts a lintegral identity to complex integrals through positive/negative parts and integral_re/integral_im.
- Same scheme in src/KubotaTorusScale.lean:132–166 (integral_fundP3_mul_real and integral_fundP3_mul). KubotaTorusScale is downstream of KubotaCTCover.
- Command: `diff <(sed -n 168,180p KubotaCTCover) <(sed -n 153,166p KubotaTorusScale)` differs only in hypothesis names and the inner lemma.
- `grep integral_eq_lintegral_pos_part_sub_lintegral_neg_part` hits only these two files.
- Candidate: a shared re/im + pos/neg lifting lemma.

11. (D) src/KubotaCubeSum.lean:570–577 (hxp/hxc in cubeTerm_eq) vs src/KubotaCubeDecomp.lean:267–274 (hxp/hxc in cubeMat_slAct)
- Both prove "a + 3cr is primary and coprime to c" in 8 identical lines.
- The adjacent "first column of γ ∈ Γ₁(3): a primary, 3 ∣ c, coprime" block recurs at KubotaCubeSum:631–636, KubotaCubeDecomp:256–261 and 314–318.
- Command: sed of all five ranges.
- Candidate: one first-column lemma.

12. (B) src/KubotaCubeSum.lean:228 `theorem tsum_quot_affine {p u : 𝓞 K} (hp : p ≠ 0) (hu : IsCoprime u p) …` and 390 `theorem tsum_eq_zero_of_twist`
- These are the modulus-p³ cases of src/KubotaLocTable.lean:31 `theorem tsum_quot_affine' {N u : 𝓞 K} (hN : N ≠ 0) (hu : IsCoprime u N) …` and :56 `theorem tsum_quot_eq_zero_of_mul`.
- The proofs are line-for-line the same (22 and 8 lines). KubotaLocTable's docstring (29) says "(round 445's `tsum_quot_affine` for any modulus)".
- KubotaLocTable is downstream of KubotaCubeSum (closure check).
- Candidate: the general versions moved upstream would replace the special ones.

13. (B) src/KubotaCharacter.lean:375 `def Gam3 : Subgroup SL(2, 𝓞 K) := (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (span {(3 : 𝓞 K)}))).ker`
- This is definitionally src/KubotaCubeCover.lean:41 `def gamPrin (N : 𝓞 K) …` at N = 3.
- `mem_Gam3` (380–388) is `mem_gamPrin` (48–58) at N = 3; the diff shows only N↔3 and the unfold of `ModThree` (KubotaTheta:64: `∀ i j, (3 : 𝓞 K) ∣ γ i j - (1 : Matrix …) i j`).
- `gam3_normal` (378) = `gamPrin_normal 3` (45).
- `finiteIndex_Gam3` (src/KubotaEisTrunc.lean:66, `unfold Gam3; infer_instance`) = `finiteIndex_gamPrin` (79) at N = 3.
- `modThree_iff` (152) parallels `mem_gamPrin_iff` (61).
- Candidate: define Gam3 := gamPrin 3 and drop the special-case proofs.

14. (B) Mathlib duplicates
- src/KubotaCharacter.lean:411 `theorem conj_mem_Gam3 {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) (g : SL(2, 𝓞 K)) : g⁻¹ * γ * g ∈ Gam3`.
  - Mathlib/Algebra/Group/Subgroup/Defs.lean:640 `theorem conj_mem' (nH : H.Normal) (n : G) (hn : n ∈ H) (g : G) : g⁻¹ * n * g ∈ H` has the same statement and proof (conj_mem at g⁻¹ plus inv_inv).
- src/KubotaCubeCover.lean:245 `def conjPrin (g : SL(2, 𝓞 K)) (N : 𝓞 K) : gamPrin N ≃ gamPrin N` (toFun `g * γ * g⁻¹`).
  - This is `(MulAut.conjNormal g).toEquiv`: Mathlib/GroupTheory/GroupAction/ConjAct.lean:248, with `conjNormal_apply : ↑(MulAut.conjNormal g h) = g * h * g⁻¹` at 251.
- src/KubotaCubeSum.lean:183 `theorem span_isMaximal_of_prime {p : 𝓞 K} (hp : Prime p) : (span {p} : Ideal (𝓞 K)).IsMaximal`.
  - This is `PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible` (Mathlib RingTheory/PrincipalIdealDomain.lean:315), which KubotaCharacter:322 already uses directly.
- src/KubotaCubeSum.lean:191 `theorem isCoprime_of_not_dvd … : IsCoprime x p` is `((Prime.coprime_iff_not_dvd hp).2 h).symm` (PrincipalIdealDomain.lean:482), via the stack wrapper KubotaCuspSums:268.
- src/KubotaCTPrinciple.lean:46 `theorem orthogonal_invariant (hA : IsSelfAdjoint A) {S : Submodule ℂ E} (hS : ∀ x ∈ S, A x ∈ S) : ∀ y ∈ Sᗮ, A y ∈ Sᗮ` is a special case (T = A = A†) of Mathlib Analysis/InnerProductSpace/Adjoint.lean:490 `theorem orthogonal_mem_invtSubmodule … (h : U ∈ invtSubmodule T.adjoint.toLinearMap) : Uᗮ ∈ invtSubmodule T.toLinearMap`.
- src/KubotaBallKernel.lean:92 `lintegral_enorm_sq_lt_top` and :304 `lintegral_enorm_sq_lt_top_of_memLp` are p = 2 cases (rpow vs npow) of Mathlib MeasureTheory/Function/LpSeminorm/Basic.lean:50 `lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top`.
- Commands: grep in the pinned Mathlib tree for conj_mem', conjNormal, isMaximal_of_irreducible, coprime_iff_not_dvd, orthogonal_mem_invtSubmodule, lintegral_rpow_enorm_lt_top.
- Candidate: these restate pinned-Mathlib lemmas.

15. (B) src/KubotaCTPrinciple.lean:254 `theorem enorm_slAct_of_isAut {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (fun g => kub ↑g) u) : ∀ γ ∈ Gam3, ∀ p ∈ UHS, ‖u (slAct γ p)‖ₑ = ‖u p‖ₑ`
- This is `IsAut.enorm isUChar_kub hu hγ hp`: src/KubotaBallKernel.lean:181 `theorem IsAut.enorm (hχ : IsUChar Γ χ) {u} (hu : IsAut Γ χ u) {γ} (hγ : γ ∈ Γ) {q} (hq : q ∈ UHS) : ‖u (slAct γ q)‖ₑ = ‖u q‖ₑ`. KubotaBallKernel is in the closure.
- The same content is inline again at KubotaCTCover:530–538 and KubotaThetaCoef:316.
- Command: `grep -rn "enorm_slAct_of_isAut\|IsAut.enorm\|isUChar_kub.norm_eq γ .*ENNReal.ofReal_one" src/*.lean` shows 8 use sites.
- Candidate: special case of the general lemma.

16. (A) src/KubotaBallKernel.lean:208 `theorem conj_mul_self_of_uchar (hχ : IsUChar Γ χ) {γ} (hγ : γ ∈ Γ) : χ γ * conj (χ γ) = 1`
- Re-proved for instances downstream: src/KubotaPoincare.lean:73 `theorem kub_mul_conj_kub {g} (hg : g ∈ Gam3) : kub ↑g * conj (kub ↑g) = 1` and src/KubotaCuspPoincare.lean:55 `theorem kubT_mul_conj (t) {g} (hg : g ∈ Gam3) : kubT t g * conj (kubT t g) = 1`.
- Both files have KubotaBallKernel, isUChar_kub (KubotaEisTrunc:59) and isUChar_kubT in closure.
- Candidate: both are `conj_mul_self_of_uchar isUChar_… hg`.

17. (A) src/KubotaCTCover.lean:184 `theorem rhoG_lt_top {p : ℂ × ℝ} (hp : p ∈ UHS) : rhoG p < ⊤ := lt_of_le_of_lt (isPU_rhoG.le_one hp) ENNReal.one_lt_top`
- The proof works for any IsPU. The general form is inlined at KubotaCTCover:338, KubotaBallKernel:246–248, KubotaPoincare:316–317, KubotaCuspPoincare:274–275 and KubotaUnfoldEis:336, 412–413 (grep `le_one .*ENNReal.one_lt_top`).
- Similarly stated only for (Gam3, rhoG) with general proofs: measurable_puLe (187), whose proof is the first component of isPU_puLe (KubotaUnfold:134); rhoG_slAct_le_puLe (191); integral_puLe_eq (197); lintegral_slAct_inv_le_puLe (398).
- Candidate: IsPU.lt_top and general-ρ folding lemmas.

18. (A) src/KubotaCTCover.lean:292 `theorem isAut_comp_actP` and :303 `theorem isAut_comp_actP_inv`
- Both are stated for `fun g => kub ↑g`, but the proofs (296–300, 308–319) use no property of kub (only hκ).
- isAut_trK (254) and integral_conj_comp_actP_mul (326) use only kub_mul_Gam3, kub_inv_Gam3 and kub_mul_conj_kub, i.e. IsUChar (KubotaBallOp:41).
- Candidate: these hold for any χ, or any unitary χ.

19. (A) src/KubotaCoefScalar.lean:326–365 `theorem kub_perW_ne_one : kub (perW : Matrix (Fin 2) (Fin 2) (𝓞 K)) ≠ 1`
- It re-derives `cub (-3) (span {1 + 3ω}) ≠ 1` through cubChar_spec and m3 = 2 (340–365).
- The upstream src/KubotaCuspSums.lean already has:
  - 214 `theorem cub_δ3_seven_pt_ne_one : cub δ3 (span {1 + 3 * ω}) ≠ 1`
  - 243 `cub_δ3_seven_pt_cube`
  - 246 `theorem pow_ne_one_of_cube … (ha : ¬ 3 ∣ a) : ζ ^ a ≠ 1`
- With δ3_sq (EisensteinPoisson:344) and cub_mul_left (EisensteinSupplement:45) these give (cub δ3 P)² = cub (−3) P ≠ 1.
- isMaximal_span_one_add_three_ω (299) and three_not_mem_span_one_add_three_ω (312) have one use each (lines 327–328) in that argument.
- Closure: KubotaCoefScalar has KubotaCuspSums.
- Candidate: about 50 lines replaceable by upstream lemmas. The absNorm pair is excluded (already §9.3).

20. (A)+(B) λ = ω − 1 lemmas
- src/KubotaCoefSupp.lean:291–295 and 306–310 inline `have hl : (ω - 1 : 𝓞 K) ≠ 0 := by …`. This is the same text as src/KubotaLamCube.lean:37 `theorem lam_ne_zero : (ω - 1 : 𝓞 K) ≠ 0`, which is downstream. KubotaCompleted:129–132 proves it a third way.
- KubotaCoefSupp:302–312 obtains t from lam_dvd_δ3 and cancels λ (hence the second hl), although its own `h' : δ3 = (ω - 1) * -ω` (305) already gives the rewrite.
- That identity is a lemma twice on parallel branches: src/KubotaCuspIdent.lean:150 `theorem δ3_eq_lam_neg : δ3 = (ω - 1) * -ω` and src/KubotaCompleted.lean:69 `theorem δ3_eq_neg_ω_lam : δ3 = -(ω * (ω - 1))`. Neither file imports the other.
- src/KubotaCoefSupp.lean:84 `theorem absNorm_span_lam : absNorm (span {(ω - 1 : 𝓞 K)}) = 3` follows from normSq_σO (EisensteinPoisson:209) and normSq_σO_lam (KubotaTheta:186), both in closure.
- Candidate: move lam_ne_zero and one δ3 identity upstream; the detour and the copies go.

21. (A) src/KubotaCompleted.lean:72 `theorem ω_cube_eq : ω * ω ^ 2 = (1 : 𝓞 K)`
- Its one use (140) builds the unit `⟨ω, ω ^ 2, ω_cube_eq, …⟩`, which is src/EisensteinSymbol.lean:41 `ωu` (coe_ωu at 43).
- Candidate: use ωu; the lemma then has no use.

22. (A) src/KubotaCoefScalar.lean:34 `theorem besselK_third_ne_zero {u : ℝ} (hu : 0 < u) : besselK (1 / 3) u ≠ 0`
- Re-proved inline upstream at src/KubotaCubeCoef.lean:180–185 (hK, from besselK_third_ofReal and bkR_pos).
- Candidate: move it next to bkR_pos (KubotaPmTheta:432).

23. (A) σO and cub one-liners stated late or for one value
- src/KubotaConstTerm.lean:403 `theorem σO_ne_zero {c : 𝓞 K} (hc : c ≠ 0) : σO c ≠ 0`.
  - `grep -rn "σO_injective (h.trans (map_zero σO).symm)" src/*.lean external/dh/*.lean | wc -l` gives 22. Mine: KubotaContour:753 and KubotaCompleted:495, which are not downstream of KubotaConstTerm.
- src/KubotaDirSplit.lean:266 `theorem cub_three_pow_three … : σO (cub 3 (span {p})) ^ 3 = 1` is the x = 3 case.
  - The general one-liner is inline at KubotaCoefSqfree:56–57, 74, 107–108, 121–122 and KubotaDirSplit:119, 221 (grep `rw \[← map_pow, cub_pow_three`: 7 hits).
- Candidate: put σO_ne_zero next to σO_injective (EisensteinGaussSum:107), and add a general σO_cub_pow_three.

24. (B) src/KubotaCoefSupp.lean:266 `theorem coprime_three_of_primary {n : 𝓞 K} (hn : Primary n) : (absNorm (span {n})).Coprime 3`
- This is `(coprime_three_absNorm hn).symm`: src/KubotaCuspSums.lean:174 `theorem coprime_three_absNorm {n : 𝓞 K} (hn : Primary n) : Nat.Coprime 3 (absNorm (span {n}))`, which is upstream. Same proof idea (absNorm_primary_mod and omega).
- Candidate: duplicate up to Nat.Coprime.symm.

25. (B) src/KubotaCubeDecomp.lean:51 `theorem uhsAct_upper_inv {a : ℂ} (ha : a ≠ 0) (b z : ℂ) (v : ℝ) : uhsAct !![a, b; 0, a⁻¹] z v = (a ^ 2 * z + a * b, Complex.normSq a * v)`
- src/KubotaMeasure.lean:229 `theorem uhsAct_diag … : uhsAct !![a, 0; 0, a⁻¹] z v = (a ^ 2 * z, Complex.normSq a * v)` is its b = 0 case.
- Command: `diff <(sed -n 229,241p KubotaMeasure) <(sed -n 51,63p KubotaCubeDecomp)` differs only in the statement lines. The proof is identical (11 lines).
- Candidate: the general lemma subsumes uhsAct_diag.

26. (B) Small restatements of upstream lemmas
- src/KubotaCTCover.lean:43 `theorem actP_one (p : ℂ × ℝ) : actP (1 : Matrix (Fin 2) (Fin 2) ℂ) p = p` is src/KubotaCusps.lean:162 `uhsAct_one` at (p.1, p.2), with the same simp proof.
- src/KubotaConstTerm.lean:346 `theorem finite_quot_three_mul {c : 𝓞 K} (hc : c ≠ 0) : Finite (𝓞 K ⧸ span {3 * c})` is `finite_quot (3 * c) (three_mul_ne_zero hc)` (src/KubotaTranslates.lean:85, upstream). Same proof via Ideal.finiteQuotientOfFreeOfNeBot.
- src/KubotaTorusScale.lean:123 integrableOn_fundP3_mul and src/KubotaCubeEigen.lean:59 integrableOn_fundP3_of_mul are the two directions of one iff with the same 5-line proof (also inline at KubotaTorusScale:135–139).
- KubotaCoefSqfree:194–197, 229–230, 246–257 and 258–259 re-prove coprime6_left/right (KubotaTranslates:381,384), span_ne_zero_of_coprime6 / ne_bot_of_coprime6 (KubotaTranslates:387, EisensteinCompletedSums:41) and norm_σO_eq_sqrt (EisensteinMeanSquarePoisson:331).
- Candidate: inline or restated duplicates.

27. (B) `(3 : 𝓞 K) ≠ 0` proved inline nine times
- Mine: KubotaCoefUnit:68–71, KubotaConstTerm:342–343, KubotaCubeCover:135–138 and 340–343.
- Others: EisensteinCubicChar:235, KubotaDirSplit:51, KubotaLamCube:88, KubotaSmFactor:216, 306.
- Mathlib has three_ne_zero (Algebra/NeZero.lean:39), NeZero.charZero_ofNat (Algebra/CharZero/Defs.lean:122) and `CharZero (𝓞 K)` (NumberTheory/NumberField/Basic.lean:109).
- Not compiled. Note that EisensteinDualMeanSquare:40 declares NeZero (4 : 𝓞 K) by hand, so the lead should check that the instance fires.
- Candidate: replace the copies with three_ne_zero.

28. (B) Two-sided rpow envelope x^t ≤ x^a + x^b
- Lemma src/KubotaEisenstein.lean:415 `theorem rpow_le_add_rpow {x a b t : ℝ} (hx : 0 < x) (ha : a ≤ t) (hb : t ≤ b) : x ^ t ≤ x ^ a + x ^ b` (parallel branch).
- src/KubotaContour.lean:338 `theorem norm_ofReal_cpow_le … : ‖(Y : ℂ) ^ z‖ ≤ Y ^ e₁ + Y ^ e₂` is that lemma after norm_cpow_eq_rpow_re_of_pos.
- The same 5-line case split is inline at KubotaContour:151–156 (hpow in norm_mellin_le_bound) and KubotaStrip:241–246 (in norm_mellin_le_strip), with variants at KubotaContour:412–417 and KubotaVsharp:301.
- Command: grep `rpow_le_rpow_of_exponent_ge` (hits listed).
- Candidate: one upstream lemma.

29. (B, low confidence) src/KubotaContour.lean:167 `theorem mellin_decay {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (k : ℕ) (a b : ℝ) : ∃ C, 0 ≤ C ∧ ∀ (W : ℝ → ℂ), (∀ y, y < α ∨ β < y → W y = 0) → ContDiff ℝ ∞ W → ∀ N : ℝ, (∀ i ≤ k, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) → ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖mellin W z‖ ≤ C * N / (1 + |z.im|) ^ k`
- Compare src/MellinUniform.lean:150 `theorem norm_fourier_expSchwartz_le … (hN : ∀ j ≤ q, ∀ y, ‖iteratedDeriv j W y‖ ≤ N) (t : ℝ) : ‖(𝓕 (expSchwartz W hW hα hαβ hs)) t‖ * (1 + |t|) ^ q ≤ …`, which is in KubotaContour's closure.
- Since 𝓕(W∘exp)(t) = Ŵ(−2πit), the MellinUniform bound is the Re z = 0 case under the same hypotheses. mellin_decay (strips, integration by parts) is more general.
- Separately, src/KubotaCompleted.lean:350–360 mellin_Vstar_line_integrable duplicates KubotaContour:298–304 inside Vstar_mellinInv (diff: one argument differs).
- Candidate: overlapping independent proofs.

30. (B) src/KubotaContour.lean:772 `theorem twisted_theta_voronoi {θ …} (hd : KubotaData θ Kc c0 cP cM τ tP tM) …` has no uses
- It is subsumed by src/KubotaUniform.lean:225 `theorem twisted_theta_voronoi_unif … (hd : KubotaData …) {L} (hL : L ≠ 0) : ∃ D dH y, … ∀ φ₀ …, ∃ C₀, …`, whose data are chosen before φ₀, Ps and j.
- Command: `grep -rn "twisted_theta_voronoi" src/*.lean` finds only KubotaContour (defs and docstring) and KubotaUniform/KubotaRowsDual using _unif.
- Candidate: superseded headline.

31. (C) src/KubotaCharacter.lean helpers with no use (zero hits outside their own docstring and #print axioms lines):
- 210 `theorem modThree_mul {γ γ' : Matrix (Fin 2) (Fin 2) (𝓞 K)} (h : ModThree γ) (h' : ModThree γ') : ModThree (γ * γ')`
- 502 `theorem kub2_Gam3`
- 514 `theorem mul_inv_mem_Gam3_of_cong`. Its docstring also asserts "so `Γ_2g = Γ_2g′`", which is not stated.
- 520 `theorem Gam3_le_Gam2 : Gam3 ≤ Gam2 := le_sup_right`
- Also, 498 `kub2_toSL` and 487 `kub2_mul` are used only by kubHom (506), which §9.4 lists as dead. kub2_eq stays used by KubotaThetaInv:398.
- Commands: a token-index census over src/ and external/ (non-upstream), excluding #print axioms lines and backtick mentions; then `grep -rn -- "<name>" src external`.
- Instances sFinite_muR and countable_ideal also showed zero textual uses, but they are typeclass instances, so this is not checkable by grep.

32. (E) No maxHeartbeats, maxRecDepth, decide or native_decide in any of the 22 files (grep per file, no hits).
- Near-generated repetition: the "good heights" hypothesis block (`∫ z in fundP3, thetaF r Y hY (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * w) = thetaCT (…)`, with its j,k-nested form) is written out at KubotaCubeDecomp:406–408 and 478–482, and KubotaCubeEigen:70–72, 120–124, 224–229 and 308–313.
- Candidate: one named predicate would shorten six statements.

33. (F) src/KubotaBall.lean:9 says "and `Im ĥ(s) > 0` just above the real axis."
- `theorem im_hhat_pos {r : ℝ} (hr : 0 < r) {s : ℂ} (hσ : 1 < s.re) (ht : 0 < s.im) (htr : s.im * r < Real.pi)` (439) needs 1 < Re s.
- By im_hhat_eq (410), the sign is negative for Re s < 1.
- Candidate: the intro sentence overclaims.

34. (F) src/KubotaBesselMellin.lean:50–51 docstring: "**The Beta integral of the second kind**: `∫_0^∞ u^{p−1}(1 + u)^{−(p+q)} du = B(p, q)` for `Re p, Re q > 0`."
- The statement `theorem integral_beta2 (p q : ℂ) :` (52) is unconditional, and the header (11–12) says "it needs no condition on `p, q`".
- Candidate: the docstring claims less than the statement proves.

35. (F) src/KubotaConstTerm.lean:6–7 header: "`φ(s) = π/((9√3/2)(s − 1))·Σ_c S(c)N(c)^{−s}` and `S(c) = Σ_{d mod 3c} (c/d)₃`."
- `def cuspS (c : 𝓞 K) : ℂ := ∑' r : 𝓞 K ⧸ span {3 * c}, if BRow (c, repQ (3 * c) r) then σO (cub c (span {repQ (3 * c) r})) else 0` (359–361) sums only over bottom rows. BRow is `IsCoprime ∧ 3 ∣ c ∧ Primary d` (KubotaEisenstein:39), as its own docstring (357–358) says.
- Candidate: the header formula omits the restriction.

36. (F) src/KubotaCoefScalar.lean:404–405 docstring: "so `τ(δ₃x) = 0` for `x = ±ωy` and `x = ±ω²y` with `y` primary, and for `λ ∥ x`."
- `theorem tauTh_mask … (hx : tauTh r Y hY (δ3 * x) ≠ 0) : (3 : 𝓞 K) ∣ x ∨ Primary x ∨ Primary (-x)` (406–407) proves only the mask.
- Candidate: the stated consequences are not formalized.

Lower confidence, not pure renamings:
- (D) KubotaConstTerm:179–227 integral_Ioi_mul_cpow and 231–255 integral_normSq_add_cpow repeat the antiderivative and polar-coordinate skeletons of KubotaGrowth:105–143 and 145–171 (the rpow versions), but with complex exponents.
- (D) KubotaCharacter:269–278 vs 285–294: the kub_conj_S_raw and kub_conj_T_raw prefixes differ only in the conjugating matrices.