<!-- Stack review 3 reader report: model output, a list of CANDIDATES, not findings. STRUCTURAL-REVIEW.md §9.2 and §9.7 record what the lead verified (Check 3). Scratchpad paths below are the reader's session files, not committed. -->

Reader report, stack review 3: the geometric/Bohr strand and its zeta23/dh joins, plus Part 2 (the DetectEM and MediumPNTW diffs). Paths are relative to tools/lean/riemann-pilot. I created or edited no files and ran no builds.

Coverage
src/BohrJoins.lean: lines 1–328 read
src/BohrLandauCore.lean: lines 1–396 read
src/BohrSphere.lean: lines 1–693 read
src/BohrTorus.lean: lines 1–450 read
src/CubeBall.lean: lines 1–734 read
src/DetectCore.lean: lines 1–218 read
src/EuclideanForcing.lean: lines 1–327 read
src/Orthogonality.lean: lines 1–308 read
src/ShellCount.lean: lines 1–157 read
src/ShellSixthCore.lean: lines 1–470 read
src/SphereDimensions.lean: lines 1–90 read
src/VolumeShell.lean: lines 1–63 read
src/HurwitzEM.lean: lines 1–759 read
external/zeta23/BohrLandau.lean: lines 1–49 read
external/zeta23/ShellDensity.lean: lines 1–250 read
external/zeta23/ShellSixth.lean: lines 1–105 read
external/dh/DHBohrSphere.lean: lines 1–49 read
Part 2: all 782 lines of `git -C /home/user/r-infinite diff 2d63e9e -- …/DetectEM.lean …/MediumPNTW.lean` read; external/pnt/DetectEM.lean lines 1–114 read (the whole file); external/pnt/MediumPNTW.lean context read at lines 1–60, 456–575, 780–880, 955–994 and 1085–1365.
STRUCTURAL-REVIEW.md lines 322–405 (§9) read; nothing below repeats an item listed there.

Candidates

1. (A) src/BohrJoins.lean:56–58. The shells are stated for ζ only.
`theorem shell_of_zeroFree {θ : ℝ} (hzf : ∀ ρ : ℂ, θ < ρ.re → riemannZeta ρ ≠ 0)` … `‖vF F θ‖ ≤ ‖vF F ρ‖ ∧ ‖vF F ρ‖ ≤ ‖vF F ((1 - θ : ℝ) : ℂ)‖`
Other locations:
- src/DirichletCharHalfPlane.lean:207–208: `theorem LFunction_ne_zero_of_re_gt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}` / `(hs : 11 / 12 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) : LFunction χ s ≠ 0`.
- Mathlib NumberTheory/LSeries/DirichletContinuation.lean:283, `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`: `completedLFunction χ (1 - s) = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s`.
- The stack's only L-band is for χ₋₃: src/HalfPlaneJoinsFinal.lean:49, `theorem chi3_band_eleven_twelfths {s : ℂ} (hs : DirichletCharacter.LFunction chi3 s = 0)`, through `XiC_even good_chi3` (src/HalfPlaneJoins.lean:36–50).
Commands:
- `grep -rn "LFunction"` over BohrJoins, BohrSphere, ShellCount, BohrLandauCore and HalfPlaneJoinsFinal: only HalfPlaneJoinsFinal.lean:49.
- `grep -rn "vF.*LFunction\|LFunction.*vF"` over src and external: no hits.
- The band lemmas: band_of_zeroFree (ζ), zeta_band and chi3_band only.
Candidate: with `BohrJoins.norm_vF_le_norm_vF`, round 495 gives `‖vF F (11/12)‖ ≤ ‖vF F ρ‖` for every zero ρ of every L(s, χ) (χ ≠ 1 ∨ ρ ≠ 1). Round 495 at χ⁻¹, with Mathlib's functional equation, gives the two-sided shell between the radii at 11/12 and 1/12 for the zeros in 0 < Re s < 1 of every primitive χ. Neither is stated.

2. (A) src/BohrJoins.lean:56 (the same hypothesis `hzf`). The Θ shell.
Other locations: external/pnt/PsiExponent.lean:69 `theorem zeta_ne_zero_of_Theta_lt {s : ℂ} (hs : Theta < s.re) : riemannZeta s ≠ 0 := by`; :56 `theorem re_le_Theta`; :141 `theorem limsup_expo : limsup expo atTop = Theta := by`.
Commands:
- `grep -rn "shell_of_zeroFree"`: BohrJoins and BohrKV.lean:6 (the KV region) only.
- `grep -rln "PsiExponent" src external/pnt`: DivisorExponent, HalfPlaneLindelof, MertensExponent, PsiExponent and SquarefreeCount; none mentions vF.
Candidate: `shell_of_zeroFree (fun _ hs => PsiExponent.zeta_ne_zero_of_Theta_lt hs)` is the tightest Bohr shell, with radii at Θ and 1 − Θ (no θ < Θ is zero-free). `limsup_expo` identifies its θ with the PNT error exponent. The join is not stated; it would sit in the pnt layer beside BohrKV.

3. (A) src/DetectCore.lean:29–32. EMApprox implies EMBound.
`def EMBound : Prop :=` / `∀ {β γ : ℝ}, 0 < β → β ≤ 2 → 2 ≤ |γ| → riemannZeta ((β : ℂ) + γ * I) = 0 → ∀ {N : ℕ}, 1 ≤ N →` / `‖∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I))‖` / `≤ (N : ℝ) ^ (1 - β) / |γ| + (N : ℝ) ^ (-β) / 2 + 2 * |γ| * (N : ℝ) ^ (-β) / β`
Other locations:
- src/MeanSquareZeta.lean:30–33: `def EMApprox : Prop :=` / `∀ {σ t : ℝ}, 0 < σ → 2 ≤ |t| → ∀ {N : ℕ}, 1 ≤ N →` / `‖riemannZeta (σ + t * I) - ∑ n ∈ Finset.Ioc 0 N, (n : ℂ) ^ (-((σ : ℂ) + t * I))‖` / `≤ (N : ℝ) ^ (1 - σ) / |t| + (N : ℝ) ^ (-σ) / 2 + (σ + |t|) * (N : ℝ) ^ (-σ) / σ`.
- zeta23 proves each separately: external/zeta23/ShellDensity.lean:41 `theorem emBound_zeta23 : DetectCore.EMBound := by` and external/zeta23/ShellSixth.lean:33 `theorem emApprox_zeta23 : MeanSquareZeta.EMApprox := by`.
Commands:
- `grep -rn "EMBound"`: DetectCore (the definition and two consumers), DetectEM.lean:82 and ShellDensity.lean:41. No lemma derives it from EMApprox.
- `grep -rn "EMApprox\b"`: MeanSquareZeta, ShellSixthCore and ShellSixth only.
Candidate: at a zero, EMApprox gives EMBound, since β + |γ| ≤ 2|γ| when β ≤ 2 ≤ |γ|. A short src lemma `EMApprox → EMBound` would make `emBound_zeta23` a corollary of `emApprox_zeta23` (see 20). The deliberate pnt/zeta23 cross-check of §9.3 is not affected.

4. (A) src/ShellCount.lean:83. `NX_eq_zero` could be sharpened.
`theorem NX_eq_zero {w : ℝ} (hw : 1 / 2 ≤ w) (T : ℝ) : NX w T = 0 := by`
Other location: src/HalfPlaneJoinsFinal.lean:56 `theorem abs_im_tau_le_five_twelfths (i : ZeroIdx (sqF Xi)) : |(tau i).im| ≤ 5 / 12 := by`
Commands: `grep -rn "NX_eq_zero\|5 / 12 < w\|five_twelfths"` returns HalfPlaneJoinsFinal.lean:17 and 56, ShellCount.lean:83 and 109, BohrLandauCore.lean:312 and ShellSixthCore.lean:403. All three uses take `1/2 ≤ w`.
Candidate: `NX w T = 0` holds unconditionally for every w > 5/12, so no pair lies outside the shell of half-width w > 5/12. Only the case w ≥ 1/2 is stated.

5. (A) src/BohrTorus.lean:329–332. The explicit moment is stated only at a = 1, σ = 0.
`theorem integral_moment_eq_count (F : Finset Nat.Primes) (ℓ : ℕ) :` / `∫ α, ‖torusPoly F 1 0 α‖ ^ (2 * ℓ) ∂torus F.card =` …
Other locations: BohrTorus.lean:269 `lemma norm_pow_expand (F : Finset Nat.Primes) (a : Nat.Primes → ℂ) (σ : ℝ) (ℓ : ℕ) …` (every a and σ); src/Vinogradov.lean:384–385 `lemma integral_torus {k : ℕ} (m : Fin k → ℤ) :` / `∫ α, ee (∑ j, (m j : ℝ) * α j) ∂torus k = if m = 0 then 1 else 0 := by`.
Commands: read both files; `grep -n "integral_torus\|count_eq_integral" src/Vinogradov.lean` returns lines 384, 430 and 456.
Candidate: the value of the torus moment, and so the limit in `tendsto_mean_moment`, is stated only at a = 1, σ = 0, through the unweighted `count_eq_integral`. Integrating `norm_pow_expand` term by term with `integral_torus` gives `Σ_{m(x)=m(y)} w_x·conj w_y` for every a and σ.

6. (B) src/ShellSixthCore.lean:56, 117 and 175 against src/BohrLandauCore.lean:37, 100 and 158. The window lemmas are proved twice.
- ShellSixthCore:56 `theorem cell_int {σ₁ lam u v a : ℝ} (hσ : 2 / 3 < σ₁) (hσ' : σ₁ < 1) (hlam : 1 ≤ lam)`.
- BohrLandauCore:37 `theorem cell_int_R {σ₀ σ₁ lam u v a : ℝ} (hσ₀ : 0 < σ₀) (hσ : σ₀ < σ₁) (hσ' : σ₁ < 1) (hlam : 1 ≤ lam)`.
- The `window_zero_count` hypotheses: `(hMS : ∀ σ ∈ Icc (2 / 3 : ℝ) (10 / 3),` / `∫ t in (u - 4 / 3)..(u + K * hS σ₁ + 4 / 3), …` against `(hMS : ∀ σ ∈ Icc σ₀ (4 - σ₀),` / `∫ t in (u - (2 - σ₀))..(u + K * cellH σ₀ σ₁ + (2 - σ₀)), …`.
- Definitions: ZetaDiscs.lean:148 `def hS (σ₁ : ℝ) : ℝ := σ₁ - 2 / 3` and :154 `def LS (σ₁ : ℝ) : ℝ := Real.log ((4 / 3) / rS σ₁)`; ZetaDiscsR.lean:29 `def cellH (σ₀ σ₁ : ℝ) : ℝ := σ₁ - σ₀` and :35 `def logRadii (σ₀ σ₁ : ℝ) : ℝ := Real.log ((2 - σ₀) / innerR σ₀ σ₁)`.
Commands: `diff` of `sed -n 56,113p` of ShellSixthCore against `sed -n 37,97p` of BohrLandauCore, both piped through sed renamings (hS σ₁ / cellH σ₀ σ₁ → H, LS / logRadii → L, avgOnCircle(R) → A, cell_bound(_R) → CB, …). The only differences are the signature, `have hσ₀2`, one comment and line wraps. The same holds for ShellSixthCore 117–189 against BohrLandauCore 100–172.
Candidate: ShellSixthCore's three window lemmas (about 130 lines) are the `_R` lemmas at σ₀ = 2/3:
- cellH (2/3) = hS and innerR (2/3) = rS by unfolding;
- 2 − 2/3 = 4/3 in logRadii and in the circle radius;
- the general block is downstream, since BohrLandauCore imports ShellSixthCore;
- ZetaDiscs.cell_bound and integral_avgOnCircle_le against ZetaDiscsR.cell_bound_R and integral_avgOnCircleR_le are the same pair one level down (those files are not assigned to me).

7. (B) src/ShellSixthCore.lean:399–400. The round-401 chain is superseded.
`theorem tendsto_NX_div_of_EMApprox (hEM : EMApprox) {c : ℝ} (hc : 0 < c)` / `(hN : ∀ᶠ T in atTop, c * (T * Real.log T) ≤ NX 0 T) {w : ℝ} (hw : 1 / 6 < w) :`
Other locations:
- src/BohrLandauCore.lean:368–369: `theorem tendsto_NX_div_of_lower {c : ℝ} (hc : 0 < c) (hN : ∀ᶠ T in atTop, c * (T * Real.log T) ≤ NX 0 T)` / `{w : ℝ} (hw : 0 < w) : …`.
- external/zeta23/BohrLandau.lean:30 `theorem tendsto_NX_div_pos {w : ℝ} (hw : 0 < w) :` and :39 `tendsto_outside_div_pos`.
- These subsume ShellSixth.lean:84 `theorem tendsto_NX_div_sixth {w : ℝ} (hw : 1 / 6 < w) :`, :94 `tendsto_outside_div_sixth`, ShellDensity.lean:205 `theorem tendsto_NX_div_quarter {w : ℝ} (hw : 1 / 4 < w) :` and :227 `tendsto_outside_div_quarter`.
Commands:
- `grep -rn "mean_square_zeta_le\b"`: MeanSquareZeta.lean:240 and ShellSixthCore.lean:297 and 307 only.
- `grep -rn "EMApprox\b"`: MeanSquareZeta, ShellSixthCore and ShellSixth only. MeanSquareHigh imports MeanSquareZeta but uses neither.
- The w > 1/6 and w > 1/4 theorems are used only in their own files.
Candidate: two groups are implied by round 402's statements, which have fewer hypotheses:
- the EMApprox chain: MeanSquareZeta.EMApprox and mean_square_zeta_le, ShellSixthCore.count_bound and tendsto_NX_div_of_EMApprox, ShellSixth's emApprox_zeta23, tendsto_NX_div_sixth and tendsto_outside_div_sixth;
- ShellDensity's two w > 1/4 conclusions.
They stay reachable only through their own `#print axioms` lines.

8. (B) src/ShellCount.lean:40–41 against src/BohrJoins.lean:49–50.
`lemma norm_vF_le_iff {F : Finset Nat.Primes} (hF : F.Nonempty) (s s' : ℂ) :` / `‖vF F s‖ ≤ ‖vF F s'‖ ↔ s'.re ≤ s.re := by`
Other location: BohrJoins:49–50 `lemma norm_vF_le_norm_vF {F : Finset Nat.Primes} (hF : F.Nonempty) {s s' : ℂ} (h : s.re ≤ s'.re) :` / `‖vF F s'‖ ≤ ‖vF F s‖ := by`. Its proof (lines 51–53) is ShellCount lines 47–49.
Commands: `grep -rn "norm_vF_le"` returns these two and their uses (BohrJoins.lean:62–63, ShellCount.lean:55 and 61). Neither file imports the other. BohrSphere has only the strict `norm_vF_lt_norm_vF` (234) and `norm_vF_eq_of_re_eq` (241).
Candidate: BohrJoins's lemma is one direction of ShellCount's iff.

9. (B) src/VolumeShell.lean:30–32 against src/EuclideanForcing.lean:291–294.
`theorem volume_ball_fraction (n : ℕ) {r : ℝ} (hr : 0 < r) :` / `(volume (ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal /` / `(volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal = r ^ n := by`
Other location: EuclideanForcing:291–294 `theorem addHaar_ball_fraction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]` … `(μ (ball (0 : F) r)).toReal / (μ (ball (0 : F) 1)).toReal = r ^ Module.finrank ℝ F := by`. Its proof (295–299) is VolumeShell 33–37 without `finrank_euclideanSpace_fin`.
Commands: read both; `grep -rn "volume_ball_fraction\|addHaar_ball_fraction"` returns the two files and the SphereDimensions.lean:22 docstring.
Candidate: VolumeShell's lemma is the instance of the general one at μ = volume on EuclideanSpace ℝ (Fin n).

10. (B) src/Orthogonality.lean:178–180. Two more copies of the cpow bridge.
`lemma natCast_cpow_line (p : Nat.Primes) (σ t : ℝ) :` / `((p : ℕ) : ℂ) ^ (-((σ : ℂ) + t * I)) =` / `((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * exp ((-Real.log (p : ℕ) : ℝ) * t * I) := by`
Other locations:
- src/MeanSquareZeta.lean:36–38: `lemma natCast_cpow_eq {n : ℕ} (hn : 1 ≤ n) (σ t : ℝ) :` / `(n : ℂ) ^ (-((σ : ℂ) + t * I))` / `= (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-(I * ((t * Real.log n : ℝ) : ℂ))) := by`.
- src/MollId.lean:113–114: `theorem natCast_cpow_neg (j : ℕ) (hj : 0 < j) (β γ : ℝ) :` / `(j : ℂ) ^ (-((β : ℂ) + γ * I)) = (((j : ℝ) ^ (-β) : ℝ) : ℂ) * Complex.exp (-(I * ((γ * Real.log j : ℝ) : ℂ))) := by`.
Commands: `grep -rn "natCast_cpow_line\|natCast_cpow_eq\b\|natCast_cpow_neg"` returns these definitions and their uses. STRUCTURAL-REVIEW.md:102 and 299 record MollId.natCast_cpow_neg, ExpSum.cpow_phase and cpow_pos_real as three copies of one bridge, but not these two.
Candidate: two more copies since round 336:
- MeanSquareZeta.natCast_cpow_eq is MollId.natCast_cpow_neg verbatim (1 ≤ n in place of 0 < j);
- Orthogonality's lemma is the prime case of the same identity;
- none of the three files imports another.

11. (B) src/DetectCore.lean:35–50 and its relatives. rhoXi in coordinates, and `zeta_rhoXi`.
`theorem zeta_βsγs (i : ZeroIdx (sqF Xi)) : riemannZeta ((βs i : ℂ) + (γs i : ℝ) * I) = 0 := by` / `have zeta_rhoXi : ∀ p : Bool × ZeroIdx (sqF Xi), riemannZeta (rhoXi p) = 0 := fun p => by` (lines 36–40). Lines 41–50 split on `(tau i).im ≤ 0` and compute `rhoXi (true, i)` and `rhoXi (false, i)`.
Other locations:
- external/pnt/KaiserKV.lean:81 `theorem zeta_rhoXi (p : Bool × ZeroIdx (sqF Xi)) : riemannZeta (rhoXi p) = 0 := by`, lines 81–85, with the same proof.
- KaiserKV.lean:91–95 compute `rhoXi (true, i)` and `rhoXi (false, i)` in coordinates again.
- src/ShellSixthCore.lean:192 `def pairZero (i : ZeroIdx (sqF Xi)) : ZIdx := zetaEquiv.symm (decide ((tau i).im ≤ 0), i)` and `lemma pairZero_spec` (194–213), with the same case split.
- src/ShellCount.lean:34 `def rhoS (i : ZeroIdx (sqF Xi)) : ℂ := (βs i : ℂ) + (γs i : ℝ) * I`, the point of `zeta_βsγs`, unnamed there.
Commands:
- `grep -rn "zeta_rhoXi\|riemannZeta (rhoXi\|(zetaEquiv.symm p).1.2"`: DetectCore.lean:36 and 40 and KaiserKV.lean:81, 85, 98 and 99 only.
- `grep -rn "rhoXi_re\|rhoXi_im\|re_rhoXi\|im_rhoXi"`: only `Pilot1ca.im_rhoXi` (a different statement, WeilAssemble.lean:586) and zeta23's CountCompare.im_rhoXi.
Candidate: two src lemmas would serve `zeta_βsγs`, `pairZero_spec` and KaiserKV's two uses:
- `rhoXi (decide ((tau i).im ≤ 0), i) = rhoS i`;
- `zeta_rhoXi` placed beside `rhoXi_zetaEquiv` (src/WeilZeta.lean:235).
These three re-derivations are the source of the `rhoXi.eq_1` triplication in §9.1.

12. (B) src/SphereDimensions.lean:35–36.
`lemma orthonormal_singleton_of_norm {v : E} (hv : ‖v‖ = 1) :` / `Orthonormal 𝕜 ((↑) : ({v} : Set E) → E) := by`
Other locations: Mathlib Analysis/InnerProductSpace/Orthonormal.lean:101–102 `theorem orthonormal_subsingleton_iff [Subsingleton ι] {v : ι → E} :` / `Orthonormal 𝕜 v ↔ ∀ i, ‖v i‖ = 1 := by`; Data/Set/Insert.lean:263 `instance uniqueSingleton (a : α) : Unique (↥({a} : Set α)) :=`.
Commands: grep of the pinned Mathlib tree for orthonormal singleton or subsingleton lemmas and for `uniqueSingleton`.
Candidate: the 9-line helper is `orthonormal_subsingleton_iff.2` applied at the singleton subtype.

13. (B) src/CubeBall.lean:81–82, with `sub_eq_sub_of_dist_eq_half` (lines 66–89).
`theorem eq_of_midpoints_inner {X Y Z₁ Z₂ : E} (hXY : dist X Y = 2) (h₁ : dist X Z₁ = 1) (h₁' : dist Z₁ Y = 1)` / `(h₂ : dist X Z₂ = 1) (h₂' : dist Z₂ Y = 1) : Z₁ = Z₂ := by`
Other location: Mathlib Analysis/Convex/StrictConvexBetween.lean:130–131 `lemma eq_midpoint_of_dist_eq_half (hx : dist x y = dist x z / 2) (hy : dist y z = dist x z / 2) :` / `y = midpoint ℝ x z := by`. Its context is `[NormedSpace ℝ E] [StrictConvexSpace ℝ E]`. Real inner product spaces have the instance through `InnerProductSpace.toUniformConvexSpace` (InnerProductSpace/Convex.lean:36). A general 𝕜 goes through `InnerProductSpace.toInnerProductSpaceable` (OfNorm.lean:74, a theorem, not an instance) and `InnerProductSpaceable.to_uniformConvexSpace` (OfNorm.lean:234).
Commands: grep of the pinned Mathlib tree for these four names.
Candidate: CubeBall's midpoint-uniqueness pair (24 lines) re-proves Mathlib's lemma in the inner-product case. Over a general RCLike 𝕜, the Mathlib route needs a `NormedSpace ℝ E` structure and the non-instance theorem.

14. (B, Part 2) external/pnt/MediumPNTW.lean:822–823 and 851.
`lemma MellinOfPsi_bdd {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν) (suppν : ν.support ⊆ Icc (1 / 2) 2) :` / `∃ B > 0, ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 2 → ‖𝓜 (fun x ↦ (ν x : ℂ)) w‖ ≤ B := by`; :851 `lemma MellinOfSmooth1d`.
Other locations: external/pnt/ExplicitSmooth.lean:302–304 `lemma norm_mellin_le_of_norm {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) {S₀ : ℝ}` / `(hS₀ : ∀ x, ‖ν x‖ ≤ S₀) {w : ℂ} (hw0 : 0 ≤ w.re) (hw2 : w.re ≤ 2) :` / `‖𝓜 (fun x ↦ (ν x : ℂ)) w‖ ≤ 12 * S₀ + 1 := by`. Its lines 306–325 are MediumPNTW 828–847 with `‖ν a‖` replaced by `S₀`. ExplicitSmooth.lean:329 `norm_mellin_smooth1_le_d` is MediumPNTW 851–859 with the constant made explicit.
Commands: read both; `grep -n "^import"` shows the chain ExplicitSmooth → SmoothPerron → HalfPlaneLindelof → …, so MediumPNTW is upstream.
Candidate: round 484 re-proved round 338's Mellin bounds with an explicit constant. The explicit form, which uses no smoothness, implies `MellinOfPsi_bdd` with S₀ = max |ν| on [1/2, 2].

15. (C) src/BohrSphere.lean:102 and 104.
`lemma lineRefl_lineRefl (s : ℂ) : lineRefl (lineRefl s) = s := by simp [lineRefl]` and `lemma lineRefl_eq_self_iff (s : ℂ) : lineRefl s = s ↔ s.re = 1 / 2 := by`
Commands: `grep -rn "lineRefl_lineRefl\|lineRefl_eq_self_iff" src external` returns header lines 14–15, the declarations and the `#print axioms` lines 647–648 only.
Candidate: two helpers (listed after "with" in the header) have no uses.

16. (C) src/Orthogonality.lean:68.
`lemma continuous_trig : Continuous (trig s c lam) := by`
Commands: `grep -rn "continuous_trig" src external` returns header line 10, the declaration and `#print axioms` line 295 only. `integral_sq_norm_trig` proves the continuity it needs by `fun_prop` (lines 100–104).
Candidate: this helper has no uses.

17. (D) src/BohrJoins.lean:233–290 (`gap_sum_le`) against src/DirMean.lean:152–252 (`mean_value`).
`set K : ℕ → ℕ → ℝ := fun j j' => if j' = j then 0 else 1 / |(j : ℝ) - j'| with hK`
- BohrJoins 236–242 is DirMean 202–208.
- BohrJoins:262 `have h2 : 2 / |Real.log j - Real.log k| ≤ 4 * P / |(j : ℝ) - k| := by` (262–265) matches DirMean 193–197.
- The symmetrisation calc, BohrJoins 275–290, matches DirMean 237–252.
Commands: `diff <(sed -n 236,242p src/BohrJoins.lean) <(sed -n 202,208p src/DirMean.lean)` is identical once the `DirMean.` prefix is removed. The diff of 275–290 against 237–252 differs only by the diagonal (b − a) term.
Candidate: the off-diagonal estimate is proved twice. STRUCTURAL-REVIEW.md:101 records only the oscillatory-integral pair.

18. (D) src/BohrLandauCore.lean:177–304 and 308–363 against src/ShellSixthCore.lean:239–395 and 399–458.
`set K : ℕ := ⌈(T - 4) / h⌉₊ + 1 with hK`
- The K-choice block is BohrLandauCore 192–203 and ShellSixthCore 252–263.
- The window cover is BohrLandauCore 236–259 and ShellSixthCore 314–337.
- The closing calc is BohrLandauCore 295–304 and ShellSixthCore 386–395.
- `tendsto_NX_div_of_msPoly` and `tendsto_NX_div_of_EMApprox` share the NX_eq_zero split, `squeeze_zero'`, `NX_le_ncard`, `hN0`, `hNXr` and the final 4-line calc.
Commands: the diffs differ only in `hh1` and two added lines (the K block), only in the lemma names (the window cover), only in the last line (the calc), and only in the g-function and count lemma (the two tendsto proofs).
Candidate: the proof skeletons repeat with renamings; this goes with 6.

19. (D) external/zeta23/ShellDensity.lean:93–143 (`Ncount_le_NX`) against external/zeta23/CountCompare.lean:25–82 (`local_count_le`).
`have hre : ∀ p : W, |(tau (zetaEquiv p.1).2).re| = (zetaZeroFamily p.1).im := by` (ShellDensity:109 and CountCompare:46)
- `have hinj : Function.Injective φ := by`: ShellDensity 121–141 is CountCompare 58–78.
- The `classical`, `set s`, `hfin`, `W` and `hcard` lines: ShellDensity 94–106 is CountCompare 28–40.
Commands: a grep for the `have` names gives these positions. The diff of the two bodies differs only in the set S, its finiteness and membership proofs, and the last two lines.
Candidate: about 40 lines of the injection from zeta23's zeros into the pilot's pairs are copied within one layer.

20. (D) external/zeta23/ShellDensity.lean:43–65 against external/zeta23/ShellSixth.lean:35–56. The `hsum` block also appears at external/pnt/DetectEM.lean:47–57.
`have hsum : ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s = ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s) := by` (ShellDensity:54, ShellSixth:45 and DetectEM:47)
Commands: the diff of ShellDensity 42–72 (with β → σ and γ → t) against ShellSixth 34–70 differs only in `rw [hz] at hEM` (line 51), `hZ`, and the signs in h1 and h2. `grep -rn "have hmap : Ioc 0 N = (Finset.range N).map"` returns DetectEM.lean:49, ShellDensity.lean:56 and ShellSixth.lean:47.
Candidate: the 23-line setup is duplicated inside zeta23, where 3 would remove it. The `hsum`/`hmap` rewrite is a Mathlib-only fact that one src lemma could give to both layers.

21. (D, Part 2) external/pnt/MediumPNTW.lean: `GenPNTW'` at 1244–1257 and 1265–1269 against `GenPNTWNoEps` at 1298–1311 and 1322–1326.
`refine GenPNTWOfLeft hD n₂_pos C₂_pos hb holo Tx εx Fx hT hε0 hε σ₂InIoo holo2 h2 hσ₂D e1 e2`, then in both: the five `obtain`s, `refine ⟨c₃ + c₄ + c₅ + c₆ + c₇, ?_⟩`, the three-line `filter_upwards`, `set ε`, `set T`, `Xpos`, and the five `specialize hc₃ … hc₇` lines.
Commands: the diff of 1247–1281 against 1301–1341, with the bound-lemma names normalised, differs only in q3/q4/q5, the r-rewrites and the k-lines.
Candidate: 19 lines repeat with renamings between two proofs added since round 336.

22. (E, Part 2) external/pnt/DetectEM.lean:2–3 and 29.
`import KaiserKV` / `import ShortKV` and `open ShortWeil ShortKV KaiserKV Pilot1ca Pilot1bt DirMean`
Commands: `head -2 external/pnt/ShortKV.lean` shows `import KaiserKV`. A grep of DetectEM for KaiserKV's and DirMean's names (fKV, region, zeta_rhoXi, abs_im_tau_le, dp, mean_value, …) finds only the word "region" in a docstring.
Candidate: after the round-400 move, `import KaiserKV` is redundant (ShortKV imports it) and the KaiserKV and DirMean opens are unused.
Other (E) checks: there is no `set_option maxHeartbeats` or `maxRecDepth`, no `decide` and no `native_decide` in the 17 files or the MediumPNTW hunks. No timing data exists in the repository, so slow `simp` calls were not assessed.

23. (F) src/ShellCount.lean:21–22. The module header is stale.
"Not proved: that proportion for every `w > 0` (the theorem of Bohr and Landau); with the stack's `A = 4(1+δ)` the condition `A(½ − w) < 1` holds only for `w > ¼` (`external/zeta23/ShellDensity.lean`)."
Other location: external/zeta23/BohrLandau.lean:30 `theorem tendsto_NX_div_pos {w : ℝ} (hw : 0 < w) :` (round 402).
Commands: `grep -n "Round 402\|round 402"` finds the updated headers of ShellSixthCore:27, ShellSixth:19, ShellDensity:27, BohrLandau:5 and BohrLandauCore:6, and nothing in ShellCount.
Candidate: the header has been stale since round 402.

24. (F) src/DetectCore.lean:16–17. The header overstates the layer clash.
"The two layers cannot be imported together (their PNT+ declarations clash), so the proof lives here and each layer supplies the bound."
Other location: external/zeta23/CoImportMV.lean:1 `import DetectEM`; its line 7 reads "`DetectEM` and `Zeta23.MV.Final` load together (the clash is only with the vendored `FromPNTPlus` copies that `SlogZeta` uses)", and its line 20 uses `DetectEM.density_unconditional`.
Commands: `grep -rn "DetectEM\."` over src and external returns CoImportMV.lean:20.
Candidate: the clash is between DetectEM and zeta23's `FromPNTPlus` copies, which ShellDensity imports; ShellDensity's own header (line 13) states it precisely.

25. (F, Part 2) external/pnt/MediumPNTW.lean:821.
"The Mellin transform of a continuous bump supported in `[1/2, 2]` is bounded on `0 ≤ Re w ≤ 2`." The statement at 822 takes `(diffν : ContDiff ℝ 1 ν)`; the proof uses only `diffν.continuous` (line 826).
Candidate: the docstring describes a weaker hypothesis than the statement takes (see 14).

26. (F, cosmetic) src/VolumeShell.lean:9 and 29.
"the ball of radius `r ∈ (0, 1]` holds the fraction `rⁿ`"; the statement at line 30 takes only `(hr : 0 < r)`.
Candidate: the docstring understates the result, which holds for every r > 0.

27. (F, cosmetic) src/Orthogonality.lean:21–23 and 253–254.
"the `ℓ^p` gauge `(Σ|x_i|^p)^{1/p}` satisfies Pythagoras for every orthogonal pair if and only if `p = 2`." The statement at 255 has `{p : ℝ} (hp : 0 < p)`. EuclideanForcing's header (line 23) says "for `p > 0`".
Candidate: the header and the theorem docstring omit the `0 < p` hypothesis.

28. (F, cosmetic) src/HurwitzEM.lean:8–9 and 14 against 597–598 and 618–619.
The header has "`… · (M+x)^{-s-2k-1} − R`" and "`R = Σ_n ∫_0^1 B_{2K}(u)/(2K)! · (s)_{2K} (M+x+n+u)^{-s-2K} du`". The theorem docstrings have "`… + R`" and "`R = -Σ_n ∫_0^1 …`".
Candidate: the header and the theorem docstrings use opposite sign conventions for R. Each is consistent with its own statement, and the bound is on ‖R‖.

Checked, nothing to report:
- `shell_of_kubotaTheta`'s hypothesis is already discharged at round 466's `Eis.kubotaTheta` by `BohrJoins.shell_eleven_twelfths` (src/HalfPlaneJoinsFinal.lean:103–105).
- `shell_of_smoothBound` at 11/12 gives the same shell through `smoothBound_eleven_twelfths`.
- `MSPoly` is discharged in src by `MeanSquareHigh.msPoly_of_order`. The lower bound `c·T log T ≤ NX 0 T` exists only in zeta23 (`ShellDensity.NX_zero_ge`); `NX 0` appears nowhere else in src, pnt or dh.
- `MeanSquareHigh.norm_zeta_sub_partial_le` (src, via HurwitzEM) does not give EMBound or EMApprox: its remainder is the constant `CE K`, and it needs `|t| ≤ N + 1`.
- No hypothesis in the 17 files is fed by HalfPlaneLindelof or MertensExponent.
- DHHurwitzEM imports HurwitzEM, so no second copy remains after the round-402 move.
- `lineRefl` = `Zeta23.reflect` is known (§9.3).