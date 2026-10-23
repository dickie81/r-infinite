<!-- Stack review 3 reader report: model output, a list of CANDIDATES, not findings. STRUCTURAL-REVIEW.md §9.2 and §9.7 record what the lead verified (Check 3). Scratchpad paths below are the reader's session files, not committed. -->

Running mandatory review protocol. Checks 0–9 active.

Coverage (every line read with Read):
src/KubotaRowsDual.lean: lines 1–196 read
src/KubotaSiegel.lean: lines 1–507 read
src/KubotaSmFactor.lean: lines 1–350 read
src/KubotaStrip.lean: lines 1–726 read
src/KubotaTheta.lean: lines 1–325 read
src/KubotaThetaCoef.lean: lines 1–687 read
src/KubotaThetaConst.lean: lines 1–435 read
src/KubotaThetaEq.lean: lines 1–324 read
src/KubotaThetaGrowth.lean: lines 1–278 read
src/KubotaThetaInv.lean: lines 1–469 read
src/KubotaThetaPair.lean: lines 1–576 read
src/KubotaThetaProof.lean: lines 1–131 read
src/KubotaThetaSeries.lean: lines 1–416 read
src/KubotaThetaZero.lean: lines 1–641 read
src/KubotaTorus.lean: lines 1–363 read
src/KubotaTorusScale.lean: lines 1–215 read
src/KubotaTranslates.lean: lines 1–486 read
src/KubotaUnfold.lean: lines 1–408 read
src/KubotaUnfoldEis.lean: lines 1–456 read
src/KubotaUniform.lean: lines 1–270 read
src/KubotaVsharp.lean: lines 1–393 read
Also read STRUCTURAL-REVIEW.md 322–405 (§9); nothing below repeats an item listed there.

Socket sweep for the special-attention question (basis for items 1–4): `grep -rn -E "\([^ ():]+ : (Eis\.|HalfPlaneS0\.)?<D>\b" src external --include=*.lean` for D in KubotaTheta, ThetaRowsM, ThetaRows, SquarefreeCompleted(M), CompletedMeanSquare(M), DualMeanSquare(M), MeanSquare, MeanSquareC, QuadLargeSieve, TransferEstimate(M), SmoothBound, WeightedBound, plus `grep -rn -E "s\.re → riemannZeta s ≠ 0|< ρ\.re →"` for zero-free half-plane hypotheses. Every hit is either applied to a KubotaThetaProof theorem or sits on the chain that reaches `ne_zero_of_kubotaTheta`/`meanSquare`/`meanSquareNu`, except the four theorems in items 1–4. Consumers of KubotaThetaProof: `ne_zero_of_re_gt_eleven_twelfths` (RealCharHalfPlane.lean:331,363; pnt PsiExponent:35, MertensExponent:252, HalfPlaneFinal:22, DivisorExponent:1262, SquarefreeCount:660, HalfPlaneLindelof:467), `meanSquare` (HalfPlaneJoinsFinal, HalfPlaneTwistMean), `meanSquareNu` (DirichletCharHalfPlane.lean:199), `kubotaTheta` (HalfPlaneJoinsFinal.lean:105); `exists_zeroFree_halfPlane` has no consumer (headline).

1. (A) src/KubotaTranslates.lean:434
   `theorem lemma61_of_kubotaTheta (hK : KubotaTheta) :`
   Discharger: src/KubotaThetaProof.lean:46 `theorem kubotaTheta : KubotaTheta := by`
   Checked: `grep -rn "lemma61_of_kubotaTheta\|conj_theta_translates\|thSer_twist" src external --include=*.lean` → KubotaTranslates.lean:22, 29 (header), 307, 332 (decls), 344 (thSer_twist used only in conj_theta_translates), 434, 449 (conj_theta_translates used only in lemma61), 476, 477, 486 (#print). The KubotaTheta-hypothesis grep above → KubotaTranslates:434, KubotaRows:514/522/526, KubotaCusps:94, BohrJoins:79; all but KubotaTranslates:434 and KubotaCusps:94 are applied to Eis.kubotaTheta (KubotaThetaProof:57, 78, 107; HalfPlaneJoinsFinal:105).
   Candidate: the hypothesis of `lemma61_of_kubotaTheta` is now proved by `Eis.kubotaTheta`, but no unconditional Lemma 6.1 is stated and nothing consumes it; `thSer_twist` and `conj_theta_translates` serve only it.

2. (A) src/KubotaStrip.lean:672–673
   `theorem twisted_theta_poly {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}`
   `    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (φ₀ : 𝓞 K → ℂ)`
   Other: src/KubotaCusps.lean:94 `theorem kubotaData_of (hK : KubotaTheta) :` (yields `KubotaData …`); src/KubotaRows.lean:515 `obtain ⟨θ, Kc, C, c₀, cP, cM, τ, tP, tM, hC, h1, h2, h3, h4, h5, h6, h7, h8, h9, hv⟩ := hK` re-destructures instead of using it.
   Checked: `grep -rn "twisted_theta_poly\|kubotaData_of" src external --include=*.lean` → KubotaStrip.lean:29 (header), 672, 726 (#print); KubotaCusps.lean:15 (header), 94, 444 (#print).
   Candidate: through `kubotaData_of` and `Eis.kubotaTheta` the `KubotaData` hypothesis of `twisted_theta_poly` is dischargeable, but the theorem has no instance and no consumer, and `kubotaData_of` has no code use.

3. (A) external/pnt/HalfPlanePNT.lean:451–452
   `theorem psi_isBigO_of_completed (hC : Eis.CompletedMeanSquare) {ε : ℝ} (hε : 0 < ε) :`
   `    (ψ - id) =O[atTop] fun x : ℝ ↦ x ^ ((11 : ℝ) / 12 + ε) :=`
   Other: src/KubotaThetaProof.lean:65 `theorem completedMeanSquare : CompletedMeanSquare := completedMeanSquare_of_squarefree squarefreeCompleted`; external/pnt/HalfPlaneFinal.lean:20 `theorem psi_isBigO_eleven_twelfths {ε : ℝ} (hε : 0 < ε) :` (same conclusion).
   Checked: `grep -rn "psi_isBigO_of_completed\|psi_isBigO_eleven_twelfths" src external --include=*.lean` → HalfPlanePNT.lean:451, 465 (#print); HalfPlaneFinal.lean:7, 20; PNTProgressions.lean:16, 182.
   Candidate: the hypothesis is now `Eis.completedMeanSquare` and the conclusion is proved unconditionally as `psi_isBigO_eleven_twelfths`, so the conditional theorem is superseded and unconsumed.

4. (A) src/HalfPlaneTwistMean.lean:542 and :553
   `theorem fSmoothC_isBigO_of_meanSquare {σ : ℝ} (hσ : 0 ≤ σ) (h : MeanSquare σ) {u₀ : 𝓞 K} (hu₀0 : u₀ ≠ 0)`
   `theorem fSmoothJ_isBigO_of_meanSquare {σ : ℝ} (hσ : 0 ≤ σ) (h : MeanSquare σ) {d : ℤ} (hd : d ≠ 0)`
   Discharger: src/KubotaThetaProof.lean:74 `theorem meanSquare {σ : ℝ} (hσ : 0 < σ) : MeanSquare σ := …` (HalfPlaneTwistMean.lean:4 imports KubotaThetaProof).
   Checked: `grep -rn "fSmoothJ_isBigO_of_meanSquare\|fSmoothC_isBigO_of_meanSquare\b" src external --include=*.lean` → HalfPlaneTwistMean.lean:23, 26, 551 (docs), 542, 553 (decls), 556 (fSmoothC used only by fSmoothJ), 621, 625 (#print). `grep -rn -E "theorem [A-Za-z0-9_']*fSmooth" src` → no unconditional fSmoothC/fSmoothJ bound.
   Candidate: `MeanSquare σ` holds for every σ > 0 in the imported file, yet both bounds stay conditional, `fSmoothJ_isBigO_of_meanSquare` has no consumer, and the half-plane route uses `fSmoothC_isBigO_of_meanSquareC` (line 586) instead.

5. (C) Helpers with no use (none is bold in its module header):
   src/KubotaThetaCoef.lean:107 `theorem measurableSet_boxT (t : 𝓞 K) (α β : ℝ) : MeasurableSet (boxT t α β) :=`
   src/KubotaThetaZero.lean:175 `theorem isAut_thetaFS (r Y : ℝ) (hY : 0 < Y) : IsAut Gam3 (fun g => kub ↑g) (thetaFS r Y hY) :=`
   src/KubotaThetaZero.lean:178 `theorem measurable_thetaFS (r Y : ℝ) (hY : 0 < Y) : Measurable (thetaFS r Y hY) :=`
   src/KubotaThetaZero.lean:181 `theorem memLp_thetaFS {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :`
   src/KubotaThetaZero.lean:259 `theorem isAut_pseisS (ψ : ℝ → ℂ) : IsAut Gam3 (fun g => kub ↑g) (pseisS ψ) :=`
   src/KubotaTorus.lean:75 `theorem frq_injective : Function.Injective frq := by`
   src/KubotaUnfold.lean:125 `theorem outMul_apply {α : Type*} [Group α] (s : Subgroup α) (x : (α ⧸ s) × s) :`
   Checked: `grep -rn -w <name> src external --include=*.lean` for each → only the declaration, a "with …" mention in the module header (KubotaThetaCoef:11; KubotaThetaZero:18, 26; KubotaTorus:11; KubotaUnfold:18) and its own #print line (668; 626–628, 634; 344; 396). A comment-stripped token census over src/ and external/{dh,pnt,zeta23} (scratchpad script dead2.py) also found no code use; none carries @[simp].
   Candidate: these seven helpers are dead.

6. (B) src/KubotaThetaPair.lean:390 (round-427 branch)
   `theorem inner_pseis_thetaL {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ} (hψ : Measurable ψ)` … `(hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hYα : Y ≤ α) (h1 : 1 < Y * α) :`
   Other: src/KubotaThetaConst.lean:159 `theorem inner_pseis_thetaL_gen …` with `(hα : 0 < α) (hαβ : α ≤ β)`; docstring line 158: "(round 427's `inner_pseis_thetaL` without its condition `α ≥ Y`, `Yα > 1`)". Same conclusion.
   Checked: grep of each name → `inner_pseis_thetaL` used only at KubotaThetaPair.lean:545 (in `thetaL_ne_zero`, β = α + 1, so `_gen` applies); `thetaL_ne_zero` (527) has no code use; `inner_pseis_uL` (311) used only at 438; `integral_conj_eisLow` (170) only at 320; `lintegral_rhoT3_eisLow_ne_top` (269) only at 319; `eisHigh_eq` (57), `eisLow_eq_sub` (88), `one_lt_of_Y_le` (93), `norm_eisLow_le` (99), `integral_fundP3_eisLow` (109), `uhsMeasure_fundP3_Icc_lt_top` (151), `mellinPsi_indicator_ne_zero` (498) are used only inside this chain (e.g. `eisHigh_eq` → KubotaThetaPair.lean:11, 57, 91). The display's `C ≠ 0` comes from `tauTh_δ3_ne_zero` (KubotaCoefScalar.lean:427), not from θ ≠ 0. Inside the branch the 9-line block `have hv … have hYv … have h1' … have hv1 … have hE : ‖eisLow s Y q‖ ≤ cuspC s.re := …` is written twice (186–200, 282–290), and `lintegral_rhoT3_eisLow_ne_top` is the eisLow instance of `KubotaThetaConst.lintegral_rhoT3_ps_ne_top` (45).
   Candidate: `inner_pseis_thetaL` is replaced at its only call site by `inner_pseis_thetaL_gen`, which leaves KubotaThetaPair's round-427 chain (lines 55–320, 387–552, about 380 lines) with no consumer above the headline `thetaL_ne_zero`.

7. (A)/(B) src/KubotaUnfold.lean:374 (and the coset/B_∞ branch)
   `theorem lintegral_puLe_top_lt_top (Γ : Subgroup SL(2, 𝓞 K))` (conclusion `∫⁻ p, puLe ⊤ Γ rhoK p ∂uhsMeasure < ⊤`)
   Other: src/KubotaEisTrunc.lean:276 `theorem lintegral_puLe_top_mul_lt_top (Γ : Subgroup SL(2, 𝓞 K))` (adds `F`); src/KubotaThetaCoef.lean:240 `have h := lintegral_puLe_top_mul_lt_top Gam3 (F := fun _ => 1) measurable_const`, with KubotaEisTrunc.lean:78 `def rhoG : ℂ × ℝ → ℝ≥0∞ := puLe ⊤ Gam3 rhoK`.
   Checked: `grep -rn -B1 -A2 lintegral_puLe_top_mul_lt_top src` → the F = 1 call at KubotaThetaCoef:240 (instance `isFiniteMeasure_muR_rhoG`). The dead-code scripts give no code use for `lintegral_puLe_top_lt_top`, `lintegral_unfold_cosets` (330) and `lintegral_rhoInf` (349), all bold; `tsum_fold` (157), `isPU_rhoInf` (305), `rhoInf` (303), `bInf` (214), `mem_bInf` (231), `bInf_det` (233), `slAct_bInf` (240) and `bInfEquiv` (268) are used only by them (grep: all hits in KubotaUnfold.lean). The Γ_∞\Γ_1(3) unfolding used downstream is KubotaUnfoldEis's `lintegral_unfold_family`/`rhoH`/`rhoT3`.
   Candidate: `lintegral_puLe_top_lt_top` is the F = 1 case of the later `lintegral_puLe_top_mul_lt_top`, and it is exactly the fact used at KubotaThetaCoef:240–242, yet it is never called; the coset and B_∞ unfolding branch (lines 155–191, 213–370) reaches no consumer.

8. (C, headlines: not dead under the brief's rule; listed for the special-attention question) Headlines with no code use, superseded by `kubotaTheta`, which calls `atG_thS_int`/`atG_thS` directly (KubotaThetaProof.lean:53–54):
   src/KubotaThetaEq.lean:297 `theorem exists_theta_series {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :`
   src/KubotaThetaInv.lean:430 `theorem exists_theta_series_inv {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :`
   src/KubotaThetaInv.lean:393 `theorem isAut_thS_Gam2 {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) : IsAut Gam2 kub2 (thS r Y hY) := by`
   src/KubotaTorusScale.lean:194 `theorem integral_thS_affine …`; its non-bold helper `integrableOn_thS_slice` (186) is used only by it.
   Checked: comment-stripped census (dead2.py/dead3.py); `grep -rn -w exists_theta_series src` → KubotaThetaEq:22, 297; KubotaThetaInv:33, 429 (docstrings only).
   Candidate: these four headlines have no consumer at the head.

9. (D) Identity-theorem and residue-limit block (z₀ = 3 + iπ/(2r) ∈ domU r, `hfg`, `eqOn_of_preconnected_of_eventuallyEq`, the curve γ(ε) = 4/3 + iε, `hγU`, `hγ`, `hRt`, `hEq`), about 80–100 lines with renamings only:
   src/KubotaThetaPair.lean:413–493 (inner_pseis_thetaL); src/KubotaThetaConst.lean:188–286 (inner_pseis_thetaL_gen); src/KubotaThetaZero.lean:407–503 (inner_pseisS_thetaL; differs only by phi0C/tendsto_phi0C_residue and F's band term). The z₀/heq/hγ/hγU skeleton is also at src/KubotaPmTheta.lean:357–405 and src/KubotaCuspTheta.lean:141–185.
   Verbatim shared opening: `obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = Real.pi / (2 * r) := ⟨_, rfl⟩` (ThetaPair:413, ThetaConst:188, ThetaZero:407; `t` at PmTheta:357, CuspTheta:141).
   Checked: `grep -n -E "x = Real.pi / \(2 \* r\)|t = Real.pi / \(2 \* r\)|have hz0 : z0 ∈ domU r|hγU : ∀ᶠ ε|Ioo_mem_nhdsGT \(div_pos Real.pi_pos hr\)" src/*.lean` → CuspTheta 141, 149, 176, 177; PmTheta 357, 365, 396, 397; ThetaConst 188, 196, 221, 222; ThetaPair 413, 421, 446, 447; ThetaZero 407, 415, 440, 441; read all five.
   Candidate: one lemma (F, G holomorphic on domU r, equal where Re s > 2, plus the two limits along 4/3 + iε) would replace five copies.

10. (D) src/KubotaThetaConst.lean:339–422 `theorem const_thetaF_ae …` and src/KubotaThetaZero.lean:526–610 `theorem const_thetaFS_ae …` are the same 85-line proof. They differ only in `a` (thetaF vs thetaFS), the slice integrability lemma, and the pair `inner_pseis(S)_thetaL_unfold`/`_gen`. Their profile block (`ψ := S.indicator fun _ => 1`, `hψm`, `hψM`, `hψ0`, the e1/e2 indicator `calc`s) recurs in src/KubotaThetaCoef.lean:595–637 (`coef_thetaF_ae`). That proof also re-does inline at 563–592 and 644–646 the argument packaged by src/KubotaThetaConst.lean:320 `theorem ae_eq_of_setIntegral_Icc {f g : ℝ → ℂ}`.
   Checked: read side by side; `grep -rn -w ae_eq_of_setIntegral_Icc src` → used only at ThetaConst:346 and ThetaZero:534.
   Candidate: a shared lemma for this proof (and for the indicator-profile reduction) would remove two 85-line copies and a third copy of about 40 lines.

11. (D)+(B) Fubini on 3P × (0, ∞). The blocks `hstep1` (20 lines) and `hslice` (22 lines) are verbatim in:
   src/KubotaThetaPair.lean:205/236 (integral_conj_eisLow, 170); src/KubotaPmPair.lean:378/414 (`theorem integral_fundP3_conj_mul … (hB : ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → ‖F p‖ ≤ B) :`, 364); src/KubotaThetaCoef.lean:363/396 (`theorem integral_fundP3_conj_mul_of_int … (hFi : IntegrableOn F (fundP3 ×ˢ Icc α β)) :`, 351).
   Checked: `grep -n -E "have hstep1|have hslice|have hint : Integrable \(T.indicator H\)|integral_prod_symm _ \(by rw" src/KubotaPmPair.lean src/KubotaThetaPair.lean src/KubotaThetaCoef.lean` → PmPair 378/398/414/437, ThetaPair 205/227/236/263, ThetaCoef 363/383/396/419.
   Candidate: the bounded-F `integral_fundP3_conj_mul` is a special case of the integrable-F `_of_int` (a bounded measurable F on the finite-measure box is integrable), and `integral_conj_eisLow` is its eisLow instance; three copies of the same proof.

11a. (D) src/KubotaThetaEq.lean:249–280 `theorem isAut_thS …` and src/KubotaThetaInv.lean:339–369 `theorem thS_slAct_of_ae …` share the same 25-line proof: `S' = UHS.piecewise (thS r Y hY) 0`, `hS'm`, `hset`, `hS'ae`, `hae` with `hq1'`/`hq2'`, `hU`, `hc1`, `Measure.eqOn_open_of_ae_eq`. The inline `S'` is the later def src/KubotaCuspPoincare.lean:306 `def thSU (r Y : ℝ) (hY : 0 < Y) : ℂ × ℝ → ℂ := UHS.piecewise (thS r Y hY) 0`. src/KubotaThetaInv.lean:329 `theorem restrict_UHS_ac : volume.restrict UHS ≪ uhsMeasure := by` (329–334) repeats the `hW` block of `ae_slAct` (KubotaThetaEq.lean:229–234) verbatim.
   Checked: `grep -rn -E "UHS.piecewise \(thS|Measure.eqOn_open_of_ae_eq" src` → ThetaEq 180, 253, 280; ThetaInv 343, 369; CuspPoincare 306; CubeEigen 414; CuspTheta 529.
   Candidate: one lemma (a.e. relation for θ̃ ⇒ everywhere relation for thS) would replace both proofs.

12. (B)+(D) src/KubotaThetaEq.lean:210 `theorem continuousOn_slAct (γ : SL(2, 𝓞 K)) : ContinuousOn (slAct γ) UHS := by`
   Other: src/KubotaCubeEigen.lean:356 `theorem continuousOn_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) : ContinuousOn (actP g) UHS := by`. The 12-line proofs (210–223 vs 356–370) are identical; `slAct γ = actP (γ.map σO)` and `det_map_σO γ.2` gives det 1.
   Checked: `grep -rn -E "theorem (continuousOn_slAct|continuousOn_actP)" src` → those two; import check: KubotaCubeEigen imports KubotaThetaEq.
   Candidate: `continuousOn_slAct` is the σO-image case of the later, more general `continuousOn_actP`.

13. (B)+(D) src/KubotaTheta.lean:263 `theorem summable_thSer {Kc : ℝ} {d : 𝓞 K → ℂ} (h : ThetaSupp Kc d) (z : ℂ) {v : ℝ} (hv : 0 < v) :`
   Other: src/KubotaThetaSeries.lean:132–133 `theorem summable_thTerm {d : 𝓞 K → ℂ} {C : ℝ} (hC : 0 ≤ C) (hd : ∀ m, ‖d m‖ ≤ C * ‖σO m‖ ^ 5)` / `(hd0 : d 0 = 0) {p : ℂ × ℝ} (hp : 0 < p.2) : Summable fun m => thTerm d m p := by`. `ThetaSupp` gives `‖d m‖ ≤ Kc‖σO m‖^{1/3} ≤ Kc‖σO m‖^5` for m ≠ 0 (`norm_le_of_thetaSupp`, `one_le_norm_σO`) and `d 0 = 0` (`dualPt_ne_zero`). The Bessel-decay proofs (KubotaTheta.lean:279–306, KubotaThetaSeries.lean:90–124) and the lemmas `rpow_third_exp_le` (KubotaTheta.lean:149–181) and `pow_five_exp_le` (KubotaThetaSeries.lean:46–71) are parallel 25-line copies (factorial exponential bound with 4! vs 8!).
   Checked: read both; `grep -rn -w "summable_thSer\|summable_thTerm\|rpow_third_exp_le\|pow_five_exp_le" src` → summable_thSer used at KubotaDerivative:273, KubotaGroups:185, KubotaTranslates:345, KubotaCubeCoef:127, KubotaExpansion:68 (all upstream of KubotaThetaSeries).
   Candidate: `summable_thSer` is a special case of `summable_thTerm`, and one generic bound tᵃe^{−ct} ≤ (N!eᶜ/cᴺ)(1 + t)^{−3} would replace both copies.

14. (B)+(D) src/KubotaContour.lean:360 `theorem kernG_bound {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :` (bound `C * N * Y ^ (s.re - 1 / 2) / (1 + |s.im|) ^ 2`, with 14 derivatives)
   Other: src/KubotaVsharp.lean:113, 117 `theorem kernG_bound_gen {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (k : ℕ) :` … `‖kernG W Y s‖ ≤ C * N * Y ^ (s.re - 1 / 2) * (1 + |s.im|) ^ 12 / (1 + |s.im|) ^ k := by`. The first 14 proof lines are identical (Contour 365–381 vs Vsharp 118–133).
   Checked: `grep -rn -w "kernG_bound\|kernG_bound_gen" src` → Contour 360, 404, 590; Vsharp 113, 245.
   Candidate: `kernG_bound` is `kernG_bound_gen` at k = 14, with (1 + |Im s|)^{12}/(1 + |Im s|)^{14} = ((1 + |Im s|)²)⁻¹; the general version is downstream (Vsharp imports Contour).

15. (B)+(F) src/KubotaThetaPair.lean:151 `theorem uhsMeasure_fundP3_Icc_lt_top {α β : ℝ} (hα : 1 ≤ α) :`
   Other: src/KubotaPmPair.lean:322 `theorem uhsMeasure_fundP3_Icc_lt_top_of_pos {α β : ℝ} (hα : 0 < α) :`, same conclusion `uhsMeasure (fundP3 ×ˢ Icc α β) < ⊤`, and a parallel 15-line calc. Docstring at KubotaThetaPair.lean:150: "**`ν_{ρ_3}`-finiteness above height `α > 1`**", while the statement assumes `1 ≤ α`.
   Checked: `grep -rn -E "uhsMeasure_fundP3_Icc_lt_top(_of_pos)?\b" src` → ThetaPair 151, 279 (only use); PmPair 322, 351, 452; ThetaConst 41.
   Candidate: the ThetaPair lemma is a special case of the PmPair one (and is used only on item 6's branch), and its docstring states α > 1 where the Lean has 1 ≤ α.

16. (B) src/KubotaRowsDual.lean:53–54 `theorem disjoint_primeSet {x y : 𝓞 K} (h : IsCoprime x y) :` / `Disjoint (primeSet (span {y})) (primeSet (span {x})) := by`
   Other: src/EisensteinQuadSieveNorm.lean:246–247 `theorem primeSet_disjoint {k n : 𝓞 K} (hcop : IsCoprime k n) :` / `Disjoint (primeSet (span {k})) (primeSet (span {n})) := by`
   Checked: `grep -rn -E "primeSet_disjoint|disjoint_primeSet" src` → QuadSieveNorm 246, 265; KubotaRows 124, 221, 284, 447; KubotaRowsDual 53, 78. Import check: KubotaRowsDual imports EisensteinQuadSieveNorm.
   Candidate: identical statements up to `Disjoint.symm` (`disjoint_primeSet h = (primeSet_disjoint h).symm`).

17. (D) src/KubotaUnfold.lean:69 `theorem lintegral_unfold {Γ : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ)` (body 73–90) and src/KubotaUnfoldEis.lean:44 `theorem lintegral_unfold_family {ι : Type*} [Countable ι] (g : ι → SL(2, 𝓞 K))` (body 48–66): the same 20-line `h1` plus 5-step calc (`ENNReal.tsum_mul_left`, `lintegral_tsum`, `tsum_congr h1`, `(lintegral_tsum …).symm`, `lintegral_congr_ae`).
   Checked: read both; `grep -rn -w "lintegral_unfold\|lintegral_unfold_family" src` → users KubotaBallCount 80, KubotaBallKernel 198, KubotaThetaCoef 254, KubotaUnfold 103, 342, KubotaCTCover 437; UnfoldEis 94, 304.
   Candidate: `lintegral_unfold` is the ρ′ = 1 case of `lintegral_unfold_family` (after writing Φ_γ = Ψ∘γ on UHS), with a duplicated proof.

18. (D) Twisted-θ̄ data block (`obtain ⟨B₀, hB₀⟩ := exists_bound_of_periodic L hL φ₀ hφ`, `hB₀0`, `hF`, `ha := thetaSupp_twisted …`, `hcne`, `finite_quot`/`Fintype`, then the same 9-argument list ending `(fun v hv => by rw [← finsum_eq_sum_of_fintype]; exact hid v hv)`), about 20 lines:
   src/KubotaStrip.lean:681–704; src/KubotaMellin.lean:723–747; src/KubotaContour.lean:742–764; the hB₀/hF part also at src/KubotaDerivative.lean:557–563.
   Checked: `grep -rn -E "exists_bound_of_periodic L hL|have hcne : ∀ \(h₀|thetaSupp_twisted hd.1" src` → Derivative 557; Strip 681, 688, 689; Contour 742, 750; Mellin 723, 730, 731.
   Candidate: a lemma producing the twisted data (ThetaSupp of the twisted coefficients and `σO(D·∏π_P) ≠ 0`) would replace four copies.

19. (D) src/KubotaSiegel.lean:67 `theorem finite_normSq_le (R : ℝ) : {x : 𝓞 K | Complex.normSq (σO x) ≤ R}.Finite := by` (76–92) and src/KubotaThetaGrowth.lean:30 `theorem tsum_normSq_le_le {R : ℝ} (hR : 0 ≤ R) :` (35–54): the same 15-line `key : ∀ m : ℤ, (m : ℝ) ^ 2 ≤ 2 * R → m ∈ … Icc (-⌈2 * R⌉) ⌈2 * R⌉` block and the h0/h1 coordinate bounds (ThetaGrowth's docstring: "as in the proof of round 385's `finite_normSq_le`").
   Checked: read both.
   Candidate: a shared coordinate-bound lemma would remove the copy.

20. (D) The 9-line proof "tsum of the indicator of a finite set ≠ ⊤" (`tsum_eq_sum (s := hfin.toFinset)`, `ENNReal.sum_ne_top`, two `indicator` cases): src/KubotaThetaCoef.lean:115 `theorem cBox_ne_top (α : ℝ) : cBox α ≠ ⊤ := by` (115–124), :186 `theorem cTr_ne_top (Z : ℝ) : cTr Z ≠ ⊤ := by` (186–195), and src/KubotaSiegel.lean:386 `theorem hitsK_ne_top {p : ℂ × ℝ} (hp : p ∈ UHS) : hitsK p ≠ ⊤ := by` (386–395).
   Checked: read all three.
   Candidate: three copies of one argument.

21. (B) src/KubotaPhiPole.lean:36 `theorem nine_sqrt_ne_zero : (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ)) ≠ 0 := by` is re-proved inline (`have hc9 … := by have : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity; exact_mod_cast this.ne'`) at src/KubotaThetaPair.lean:128–130 and 548–550, src/KubotaThetaConst.lean:126–128, src/KubotaThetaZero.lean:360–362, src/KubotaThetaSeries.lean:368–370.
   Checked: `grep -rn nine_sqrt_ne_zero src` (used at KubotaCubeCoef, KubotaCoefScalar, KubotaThetaInv:199, KubotaPhiPole); `grep -c` of the inline `have` pattern; import check: all four files import KubotaPhiPole.
   Candidate: five inline copies of an upstream lemma.

22. (B) Small equivalents of Mathlib or Lean-core lemmas:
   src/KubotaTranslates.lean:381 `theorem coprime6_left {a b : ℕ} (h : (a * b).Coprime 6) : a.Coprime 6 :=` and :384 `theorem coprime6_right …` are core `Nat.Coprime.coprime_mul_right` and `Nat.Coprime.coprime_mul_left` (toolchain Init/Data/Nat/Coprime.lean:105 and 102: `theorem Coprime.coprime_mul_right (H : Coprime (m * k) n) : Coprime m n`) at n = 6.
   src/KubotaThetaInv.lean:46 `theorem subsingleton_quot_gam3 : Subsingleton (Gam3 ⧸ Gam3.subgroupOf Gam3) := by` follows from Mathlib `Subgroup.subgroupOf_self` (Algebra/Group/Subgroup/Map.lean:345) and `QuotientGroup.subsingleton_quotient_top` (GroupTheory/QuotientGroup/Basic.lean:394).
   src/KubotaThetaInv.lean:144 `def conjGam3 (g : SL(2, 𝓞 K)) : Gam3 ≃ Gam3 where` and the identical inline `let e : Gam3 ≃ Gam3 := { toFun := fun γ => ⟨g * γ * g⁻¹, gam3_normal.conj_mem _ γ.2 g⟩ …` (src/KubotaThetaZero.lean:86–90) are Mathlib `MulAut.conjNormal` (GroupTheory/GroupAction/ConjAct.lean:247, with `conjNormal_apply : ↑(MulAut.conjNormal g h) = g * h * g⁻¹`) for the instance `gam3_normal` (KubotaCharacter.lean:378).
   src/KubotaVsharp.lean:59 `theorem norm_cexp_I_mul (u w : ℝ) : ‖Complex.exp (I * u * w)‖ = 1 := by` is Mathlib `Complex.norm_exp_I_mul_ofReal` (Analysis/Complex/Trigonometric.lean:954) at u·w.
   src/KubotaTheta.lean:203 `theorem one_le_absNorm_of_coprime3` is more general than src/EisensteinCompletedSums.lean:235 `theorem one_le_absNorm_of_coprime6` (coprime to 6 implies coprime to 3); the 2-line proofs are the same.
   Checked: grep of the Mathlib tree at the pinned commit and of the toolchain source for each name; `grep -rn -w` of the stack names for their uses.
   Candidate: each is a restatement of an existing lemma.

23. (B) src/KubotaVsharp.lean:63/88/97: `hasDerivAt_fourierG`, `theorem iteratedDeriv_fourierG {F : ℝ → ℂ} (hc : Continuous F)` … `iteratedDeriv n (fourierG F 0) = fourierG F n := by`, and `theorem contDiff_fourierG …` `: ContDiff ℝ ∞ (fourierG F 0) :=`, where `fourierG F n w = ∫ (iu)ⁿF(u)e^{iuw} du`.
   Other: Mathlib Analysis/Fourier/FourierTransformDeriv.lean:760 `lemma hasDerivAt_fourier`, :801 `theorem iteratedDeriv_fourier {f : ℝ → E} {N : ℕ∞} {n : ℕ}` (`iteratedDeriv n (𝓕 f) = 𝓕 (fun x : ℝ ↦ (-2 * π * I * x) ^ n • f x)`), :703 `theorem contDiff_fourier {N : ℕ∞}` (namespace Real).
   Checked: `grep -n -E "^(theorem|lemma) " Mathlib/Analysis/Fourier/FourierTransformDeriv.lean` and the namespace lines (Real at 669–830).
   Candidate: the three stack lemmas restate Mathlib's results for the real Fourier transform, with frequency rescaled by w ↦ −w/2π.

24. (B) src/KubotaStrip.lean:41–42 `theorem Gamma_add_nat_eq (s : ℂ) (n : ℕ) (hs : ∀ j : ℕ, s + j ≠ 0) :` / `Gamma (s + n) = Gamma s * ∏ j ∈ Finset.range n, (s + j) := by`
   Other: Mathlib Analysis/SpecialFunctions/Gamma/Beta.lean:459 `theorem Gamma_add_nat_div_Gamma_eq {n : ℕ} (z : ℂ) (hz : ∀ k : ℕ, z ≠ -k) :` (`Gamma (z + n) / Gamma z = (ascPochhammer ℂ n).eval z`).
   Checked: `grep -rn -E "theorem .*Gamma.*(add_nat|Pochhammer)" Mathlib`; stack grep found no other copy. No other Phragmén–Lindelöf use in src/, external/ or the vendored trees (`grep -rln "PhragmenLindelof|vertical_strip"`), and no polynomial-bound PL in Mathlib's PhragmenLindelof.lean, so `poly_bound_strip` (128) is not a duplicate.
   Candidate: the same identity as Mathlib's, in ascending-Pochhammer form.

25. (E) Inline re-derivations of available facts:
   src/KubotaSmFactor.lean:216–219 and 306–309 `have h30 : (3 : 𝓞 K) ≠ 0 := fun h => by …` (4 lines each; also KubotaCoefUnit.lean:68, KubotaDirSplit.lean:51). Mathlib has `instance [NumberField K] : CharZero (𝓞 K)` (NumberTheory/NumberField/Basic.lean:109), so `three_ne_zero` closes it; KubotaUnfoldEis.lean:214 already uses `(by norm_num)` for it.
   src/KubotaSmFactor.lean:107–111 and 224–227 re-derive `¬ p ∣ 3` for a primary prime, and 311–313 `IsCoprime p 3`. Upstream lemmas: src/KubotaCubeSum.lean:187 `theorem three_not_mem_span {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) : (3 : 𝓞 K) ∉ span {p} :=` and src/KubotaCuspData.lean:511 `theorem isCoprime_three_of_primary {r : 𝓞 K} (hr : Primary r) : IsCoprime (3 : 𝓞 K) r := by` (both imported by KubotaSmFactor).
   src/KubotaThetaEq.lean:111 `have : Countable (𝓞 K) := crdEquiv.symm.injective.countable` duplicates the global instance src/EisensteinQuadSieveLattice.lean:349 `instance countable_O : Countable (𝓞 K) := crdEquiv.symm.injective.countable` (imported).
   Checked: `grep -rn -E "have h30 : \(3 : 𝓞 K\) ≠ 0"`; Mathlib grep for the CharZero instance; import closure (scratchpad imports.py).
   No `set_option maxHeartbeats`/`maxRecDepth`, `decide` or `native_decide` occurs in the 21 files (grep).
   Candidate: these local proofs can be replaced by the existing lemmas and instances.

26. (F) src/KubotaTranslates.lean:431–433 docstring: "the twisted coefficient at `λnb³` is `conj C·N(b)^{1/2}γ₂(n)Ψ(n)Ψ(b)³` (its (6.3), with `C = 3^{5/2}`)."
   Statement (434–435): `theorem lemma61_of_kubotaTheta (hK : KubotaTheta) :` / `∃ (θ : ℂ → ℝ → ℂ) (Kc : ℝ) (C : ℂ) (τ : 𝓞 K → ℂ), C ≠ 0 ∧ ThetaSupp Kc τ ∧`
   Other: the C that `Eis.kubotaTheta` supplies is `tauTh r Y hY δ3` (src/KubotaCoefScalar.lean:418 docstring "`C = τ(δ₃) ≠ 0`", line 427).
   Candidate: the docstring assigns C the value 3^{5/2}, which the statement does not fix and the stack does not prove.

Scratchpad tools used for the censuses (read-only, outside the repo): /tmp/claude-0/-home-user-r-infinite/db46f946-fd0e-58a3-baf6-61ea74b579d4/scratchpad/sr3/kub/dead2.py (comment-stripped use census), /tmp/claude-0/-home-user-r-infinite/db46f946-fd0e-58a3-baf6-61ea74b579d4/scratchpad/sr3/kub/dead3.py (second-order: used only by unconsumed declarations), /tmp/claude-0/-home-user-r-infinite/db46f946-fd0e-58a3-baf6-61ea74b579d4/scratchpad/sr3/kub/imports.py (import closure).