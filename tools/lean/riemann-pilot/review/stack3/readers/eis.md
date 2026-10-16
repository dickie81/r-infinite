<!-- Stack review 3 reader report: model output, a list of CANDIDATES, not findings. STRUCTURAL-REVIEW.md §9.2 and §9.7 record what the lead verified (Check 3). Scratchpad paths below are the reader's session files, not committed. -->

STACK REVIEW 3: READER REPORT (Part 1: 9 new files; Part 2: 18 changed files since 2d63e9e). Read-only; HEAD bdc39f3, clean tree.

COVERAGE
Part 1, read end to end:
- src/EisensteinPrepared.lean: lines 1–1109 read
- src/EisensteinQuadSupplement.lean: lines 1–583 read
- src/EisensteinRealTwist.lean: lines 1–158 read
- src/EisensteinRowTwist.lean: lines 1–541 read
- src/EisensteinSquarefreeRows.lean: lines 1–350 read
- src/EisensteinSupplement.lean: lines 1–513 read
- src/EisensteinThetaAssembly.lean: lines 1–713 read
- src/EisensteinThetaMeanSquare.lean: lines 1–592 read
- src/EisensteinThetaRows.lean: lines 1–854 read

Part 2: every hunk of `git diff 2d63e9e` read, with context around each hunk (18 files, +1445 −559):
- src/EisensteinCompletedSums.lean: 7 hunks (+13 −8); context 1–135
- src/EisensteinCubeReduction.lean: 18 hunks (+30 −21); context includes 120–150 and 586–635
- src/EisensteinDescent.lean: 12 hunks (+29 −18); context includes 310–330
- src/EisensteinDualExcl.lean: 11 hunks (+17 −13); context includes 244–268, 350–366 and 570–590
- src/EisensteinDualMeanSquare.lean: 8 hunks (+35 −10); context 36–55
- src/EisensteinFirstTransfer.lean: 31 hunks (+92 −68)
- src/EisensteinMeanSquareBlock.lean: 13 hunks (+35 −18); context includes 76–145
- src/EisensteinMeanSquareDual.lean: 13 hunks (+266 −15); context includes 1–16, 300–385, 700–1030 and 1076–1250
- src/EisensteinMeanSquarePoisson.lean: 10 hunks (+95 −28); context includes 150–230
- src/EisensteinMeanSquareRowCol.lean: 14 hunks (+322 −36); context includes 1–22, 432–480, 530–559, 800–869, 1008–1067 and 1086–1093
- src/EisensteinPairRatio.lean: 11 hunks (+104 −60); context includes 1–40
- src/EisensteinSecondPoisson.lean: 15 hunks (+122 −66); context includes 1–40 and 186–208
- src/EisensteinThirdTransfer.lean: 16 hunks (+47 −33)
- src/EisensteinTransferColumns.lean: 13 hunks (+29 −22)
- src/EisensteinTransferEstimate.lean: 8 hunks (+24 −6); context includes 32–47 and 176–200
- src/EisensteinTransferPoisson.lean: 8 hunks (+32 −21); context includes 148–185
- src/EisensteinTransferRegroup.lean: 12 hunks (+44 −33)
- src/EisensteinTransferRowCol.lean: 20 hunks (+109 −83); context includes 41–100, 246–321 and 515–531

Exclusion list: STRUCTURAL-REVIEW.md lines 323–457 read. §9 grew from 406 to 457 lines during the run (commits 32a1c74 to bdc39f3), so I read it again at HEAD. Nothing below is listed there.

Conventions:
- All rg commands were run from tools/lean/riemann-pilot.
- A "code use" excludes the declaration line, docstrings and #print lines.
- "Upstream/downstream" comes from a read-only Python walk of the import lines of src/*.lean.
- Mathlib was checked in a scratch clone at MATHLIB_REV 0f64d30a.
- None of the replacements suggested below has been compiled. Each was checked by reading.

CANDIDATES

1. A/B. src/EisensteinMeanSquareDual.lean:874, plus src/EisensteinMeanSquareRowCol.lean:464, 536, 808, 1017. The untwisted modulus-4 chain is still proved separately.
- Statements:
  - MeanSquareDual:874–875: `theorem meanSquare_of_dualMeanSquare {ϑ : ℝ} (hϑ : 0 < ϑ) (hDM : DualMeanSquare ϑ) :` / `MeanSquare ϑ := by` (lines 874–1004)
  - MeanSquareDual:738: `theorem famSum_meanSquare_le (W : ℝ → ℝ) {α β : ℝ} (hβ : 0 ≤ β) (hW : ∀ x, β < x → W x = 0)` (738–799)
  - RowCol:1017: `theorem meanSquare_rowcol {W : ℝ → ℝ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {Z : ℝ} (hZ : 0 < Z)` (1017–1067)
  - RowCol:808: `theorem pair_char_form (H : ℝ) (hH : 0 < H) {R : ℝ} (hR0 : 0 < R)` (808–864)
  - RowCol:536: `theorem pairTerm_expand {C1 C2 : Finset Pr} (hd : Disjoint C1 C2) :` (536–557)
  - RowCol:464: `theorem isUnit_cls4 (C : Finset Pr) : IsUnit (cls 4 C) :=`
- Round-494 counterparts:
  - MeanSquareDual:1112–1114: `theorem meanSquareNu_of_dualMeanSquareM [NeZero m] [Fact ((4 : 𝓞 K) ∣ m)] (ν : MulChar (𝓞 K ⧸ span {m}) ℂ)` / `{ϑ : ℝ} (hϑ : 0 < ϑ) (hDM : DualMeanSquareM m ϑ) :` / `MeanSquareC (fun I => ν (Ideal.Quotient.mk _ (pgen I))) ϑ := by` (1112–1249)
  - famSumNu_meanSquare_le (MeanSquareDual:1034–1106)
  - meanSquare_rowcolNu (RowCol:1215–1311)
  - pair_char_formNu (RowCol:1134–1207)
  - pairTerm_expandNu (RowCol:1100–1126)
- RowCol docstring 16–17 records the retention but not the instance relation: "Round 308's expansion of the paired factor (`pairTerm_expand`, `pair_char_form`, `meanSquare_rowcol`) stays at `m = 4`, where every class is a unit (`isUnit_cls4`)."
- Checked with `rg -n -w <name> src external`. Each link's only code use is in the next link:
  - isUnit_cls4: RowCol:540 and 541
  - pairTerm_expand: RowCol:847
  - pair_char_form: RowCol:1044
  - meanSquare_rowcol: MeanSquareDual:789
  - famSum_meanSquare_le: MeanSquareDual:942
  - meanSquare_of_dualMeanSquare: MeanSquareDual:1013 (inside ne_zero_of_dualMeanSquare, which is used at Descent:445) and KubotaThetaProof:74 (`theorem meanSquare {σ : ℝ} (hσ : 0 < σ) : MeanSquare σ := meanSquare_of_dualMeanSquare hσ (dualMeanSquare hσ)`)
  - None of these names occurs inside the Nu ranges.
- Instances at m = 4: `rg -n "instance" src/Eisenstein*.lean src/Kubota*.lean src/HalfPlane*.lean | rg -i "fact|neZero"` finds DualMeanSquare:40 `instance neZero_four : NeZero (4 : 𝓞 K)` and :53 `instance fact_four_dvd_four : Fact ((4 : 𝓞 K) ∣ 4) := ⟨dvd_refl _⟩`. DualMeanSquare:283 reads `def DualMeanSquare (ϑ : ℝ) : Prop := DualMeanSquareM 4 ϑ`.
- Glue lemmas, all read:
  - HalfPlaneMeanSquare:367–368: `noncomputable def wsym (u : 𝓞 K) (I : Ideal (𝓞 K)) : ℂ :=` / `if (absNorm I).Coprime 6 then (moebius I : ℂ) * sym6 u I else 0`. This is Mathlib's moebius, which is 0 off squarefree ideals (moebius_of_not_squarefree, used at EisensteinCount:284).
  - DualExcl:583: `theorem isCoprime_pgen_two {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hsq : Squarefree I) :`
  - DualExcl:574: isUnit_mk_four
  - Mathlib MulChar/Basic.lean:261: `lemma one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R') x = 1`
  - MeanSquareDual:1025: `theorem meanSquareC_one_iff {σ : ℝ} : MeanSquareC (fun _ => 1) σ ↔ MeanSquare σ := by`
- Verbatim overlap (sed ranges compared with diff in scratch files):
  - 874–1004 vs 1112–1249: 123 of 131 lines
  - 738–799 vs 1034–1106: 42 of 62
  - 536–557 vs 1100–1126: 10 of 22
  - 808–864 vs 1134–1207: 40 of 57
  - 1017–1067 vs 1215–1311: 36 of 51
- The other modulus-4 results are now one-line instances of their m-general versions:
  - display aliases: SquarefreeRows:186, CubeReduction:610, Descent:75, ThetaRows:192
  - instance proofs: ThetaAssembly:689–690 (`squarefreeCompletedM_of hθ hLS`), SquarefreeRows:333–334, KubotaRows:522, TransferEstimate:177
- Candidate: the untwisted chain (323 lines, plus isUnit_cls4) is the case m = 4, ν = 1 of round 494's twisted chain.
  - meanSquareNu_of_dualMeanSquareM (m := 4) (ν := 1) gives MeanSquareC with c(𝔞) = 1(pgen 𝔞 mod 4).
  - That c equals 1 wherever wsym u 𝔞 ≠ 0. There 𝔞 is squarefree of norm prime to 6, so pgen 𝔞 is prime to 2 and its class is a unit.
  - meanSquareC_one_iff then gives MeanSquare ϑ.
  - It is the only modulus-4 line of rounds 492–494 that is still proved separately.

2. B. src/EisensteinSquarefreeRows.lean:108 against src/EisensteinPrepared.lean:68 and src/EisensteinMeanSquareDual.lean:324.
- Statements:
  - SquarefreeRows:108–109: `theorem sum_idealsLe_inv_sq_le (x : ℝ) :` / `∑ I ∈ idealsLe x, 1 / (absNorm I : ℝ) ^ 2 ≤ 4 * (2 * kappa + 5) := by` (108–162)
  - Prepared:68–69: `theorem sum_idealsLe_rpow_le {s : ℝ} (hs : 1 < s) (x : ℝ) :` / `∑ I ∈ idealsLe x, (absNorm I : ℝ) ^ (-s) ≤ 2 * (2 * kappa + 5) / (1 - (2 : ℝ) ^ (1 - s)) := by` (68–129)
  - MeanSquareDual:324–326: `theorem sum_idealsLe_inv_le (x : ℝ) :` / `∑ I ∈ idealsLe x, 1 / (absNorm I : ℝ) ≤` / `2 * (2 * kappa + 5) * ((Nat.log 2 ⌊x⌋₊ : ℕ) + 1 : ℝ) := by` (324–372)
- Checked:
  - `rg -n -w "sum_idealsLe_inv_sq_le|sum_idealsLe_rpow_le|sum_idealsLe_inv_le" src external`: inv_sq at SquarefreeRows:108 and 328; rpow at Prepared:68 and 155; inv at MeanSquareDual:324, 386 and CubeReduction:726.
  - `rg -n -F 'hf : ⌊(2 : ℝ) ^ (j + 1)⌋₊ = 2 ^ (j + 1)' src`: SquarefreeRows:128, MeanSquareDual:345, Prepared:95 and 746.
  - 34 of SquarefreeRows' 55 lines reappear verbatim in Prepared 68–129, and 35 in MeanSquareDual 324–372.
  - The own constants used by sum_idealsLe_rpow_le are idealsLe, kappa, kappa_pos, card_idealsLe, idealCount, mem_idealsLe (EisensteinIdealCount) and idealCount_le (MeanSquareDual). All are upstream of SquarefreeRows; Prepared imports SquarefreeRows (Prepared:2).
- Candidate: sum_idealsLe_inv_sq_le is sum_idealsLe_rpow_le at s = 2, since 2(2κ+5)/(1 − 2^{−1}) = 4(2κ+5). It is proved separately only because the general lemma sits downstream, and the dyadic-shell scaffold is written three times.

3. B. src/EisensteinSquarefreeRows.lean:36 and src/EisensteinThetaRows.lean:250 against src/EisensteinQuadSupplement.lean:482.
- Statements:
  - SquarefreeRows:36–37: `theorem sym6_sq_eq_pow_eight {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (m : 𝓞 K) :` / `sym6 m I ^ 2 = sym6 m I ^ 8 := by`
  - ThetaRows:250–251: `theorem sym6_pow_nine {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (m : 𝓞 K) :` / `sym6 m I ^ 9 = sym6 m I ^ 3 := by`
  - QuadSupplement:482: `theorem sym6_pow_seven (a : 𝓞 K) (I : Ideal (𝓞 K)) : sym6 a I ^ 7 = sym6 a I := by`
  - QuadSupplement:473: `theorem chiP_pow_seven (P : Ideal (𝓞 K)) (a : 𝓞 K) : chiP P a ^ 7 = chiP P a := by`. Its inputs are chiP_pow_six (HalfPlaneMeanSquare:61) and chiP_eq_zero_of_mem (EisensteinSymbol:322).
- Checked with rg:
  - sym6_sq_eq_pow_eight: SquarefreeRows:36, 61; ThetaRows:252
  - sym6_pow_nine: ThetaRows:250, 265
  - sym6_pow_seven: QuadSupplement:482, 492; KubotaCoefSqfree:139
  - chiP_pow_seven: QuadSupplement:473, 486
  - QuadSupplement reaches both SquarefreeRows and ThetaRows.
- Candidate: both lemmas follow from sym6_pow_seven in one line (x⁸ = x⁷·x = x², x⁹ = x⁷·x² = x³) without the coprimality hypothesis. sym6_pow_seven sits downstream, although its inputs are upstream of both files.

4. B. src/EisensteinCompletedSums.lean:41, 46, 62, 66 against src/EisensteinPrepared.lean:177, 181, 197 and src/EisensteinThetaRows.lean:196.
- Statements:
  - CompletedSums:46–47: `theorem exists_primary_gen {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :` / `∃ a, Primary a ∧ span {a} = I := by`
  - CompletedSums:62: `theorem pgen_spec6 {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :`
  - CompletedSums:66: `theorem pgen_mul6 {I J : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hJ : (absNorm J).Coprime 6) :`
  - CompletedSums:41: `theorem ne_bot_of_coprime6 ...`
  - Prepared:181–182: `theorem exists_primary_gen3 {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 3) :` / `∃ a, Primary a ∧ span {a} = I := by`
  - Prepared:197: `theorem pgen_spec3 ...`
  - Prepared:177: `theorem ne_bot_of_coprime3 ...`
  - ThetaRows:196: `theorem pgen_mul3 {I J : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 3) (hJ : (absNorm J).Coprime 3) :`
- Read 41–72 against 177–198 and 196–202. The 15-line proofs are identical except:
  - `exact pgen_maximal P (three_not_mem_of_six P (six_not_mem_of_factor hI hP))` against `exact pgen_maximal P (three_not_mem_of_factor hI hP)`
  - ne_bot_of_coprime6 against ne_bot_of_coprime3
  - pgen_mul6 and pgen_mul3 are identical up to the spec name.
- Checked: rg hit counts are exists_primary_gen 4, pgen_spec6 12, pgen_mul6 5, ne_bot_of_coprime6 15, exists_primary_gen3 4, pgen_spec3 16, pgen_mul3 2, ne_bot_of_coprime3 6. The inputs of the Coprime-3 block are all in CompletedSums' import closure: pgen_maximal, primary_multiset_prod, pgen_spec and pgen_eq (EisensteinCubicRecip), absNorm_natCast_span_sq (EisensteinCount), isMaximal_of_factor (HalfPlaneMeanSquare).
- Candidate: the Coprime-6 primary-generator block is the Coprime-3 block restricted, proved twice. The more general block sits downstream.

5. A/B. src/EisensteinQuadSupplement.lean:203, 210, 222, 233 (round 364) against src/EisensteinRealTwist.lean:101, 127 (round 474).
- Statements:
  - QuadSupplement:222–223: `theorem sym2_neg_one {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :` / `sym2 (-1) I = ((ZMod.χ₄ (absNorm I : ZMod 4) : ℤ) : ℂ) := by`
  - QuadSupplement:233–234: `theorem sym2_two ...` / `sym2 2 I = ((ZMod.χ₈ (absNorm I : ZMod 8) : ℤ) : ℂ) := by`
  - QuadSupplement:203–204: `theorem chiP_cube_neg_one {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P) :` / `chiP P (-1) ^ 3 = ((ZMod.χ₄ (absNorm P : ZMod 4) : ℤ) : ℂ) := by`
  - QuadSupplement:210–211: chiP_cube_two, `chiP P 2 ^ 3 = ((ZMod.χ₈ (absNorm P : ZMod 8) : ℤ) : ℂ) := by`
- Other locations:
  - RealTwist:127–128: `theorem sym6_intCast_cube (d : ℤ) {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :` / `sym6 ((d : 𝓞 K) ^ 3) I = (jacobiSym d (absNorm I) : ℂ) := by`
  - RealTwist:101–102: `theorem chiP_intCast_cube {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hP6 : (6 : 𝓞 K) ∉ P) (d : ℤ) :` / `chiP P ((d : 𝓞 K) ^ 3) = (jacobiSym d (absNorm P) : ℂ) := by`
  - EisensteinSymbol:346: `noncomputable def sym2 (a : 𝓞 K) (I : Ideal (𝓞 K)) : ℂ := sym6 a I ^ 3`
  - HalfPlaneMeanSquare:72–73: `theorem sym6_pow_succ (a : 𝓞 K) (I : Ideal (𝓞 K)) (n : ℕ) :` / `sym6 (a ^ (n + 1)) I = sym6 a I ^ (n + 1) := by`
  - EisensteinSymbol:310: chiP_mul
  - Mathlib NumberTheory/LegendreSymbol/JacobiSymbol.lean:311 `theorem at_neg_one {b : ℕ} (hb : Odd b) : J(-1 | b) = χ₄ b :=` and :321 `theorem at_two {b : ℕ} (hb : Odd b) : J(2 | b) = χ₈ b :=`
- Checked:
  - `rg -n -w "sym6_intCast_cube|chiP_intCast_cube|sym2_neg_one|sym2_two|chiP_cube_neg_one|chiP_cube_two" src external`: uses at QuadSupplement:227, 238, 262, 271; RealTwist:148; HalfPlaneTwistMean:239, 610.
  - RealTwist imports only EisensteinGaussSum, and neither file reaches the other.
  - diff of 222–230 against 233–241: only the statement and line 227/238 (chiP_cube_neg_one vs chiP_cube_two) differ.
  - sym2_neg_one_congr (259–266) and sym2_two_congr (268–275) differ only in 4 against 8.
- Candidate: round 364's supplementary laws at −1 and 2 are the cases d = −1 and d = 2 of round 474's Jacobi identity.
  - sym2 d 𝔞 = sym6 d 𝔞³ = sym6 (d³) 𝔞 = J(d | N𝔞), then Mathlib's at_neg_one or at_two (N𝔞 is odd).
  - chiP_cube_neg_one and chiP_cube_two follow the same way from chiP_intCast_cube and chiP_mul.
  - The 9-line twin proofs would collapse into one lemma.

6. B. src/EisensteinSupplement.lean:231 against src/EisensteinQuadSupplement.lean:244, plus DirichletCharHalfPlane.
- Statements:
  - Supplement:231–232: `theorem absNorm_congr_nine {b b' : 𝓞 K} (h : (9 : 𝓞 K) ∣ b - b') :` / `((absNorm (span {b}) : ℤ) - absNorm (span {b'})) % 9 = 0 := by`
  - QuadSupplement:244–245: `theorem absNorm_congr (m : ℤ) {b b' : 𝓞 K} (h : (m : 𝓞 K) ∣ b - b') :` / `((absNorm (span {b}) : ℤ) - absNorm (span {b'})) % m = 0 := by`
  - DirichletCharHalfPlane:45: `theorem intCast_dvd_of_dvd {q : ℕ} {z : ℤ} (h : (q : 𝓞 K) ∣ (z : 𝓞 K)) : (q : ℤ) ∣ z := by`
  - Supplement:220: `theorem int_dvd_of_dvd {a n : ℤ} (h : (a : 𝓞 K) ∣ (n : 𝓞 K)) : a ∣ n := by`
  - DirichletCharHalfPlane:53: `theorem normZ_congr {q : ℕ} {a b : 𝓞 K} (h : (q : 𝓞 K) ∣ a - b) : normZ q a = normZ q b := by`, with :34 `noncomputable def normZ (q : ℕ) (a : 𝓞 K) : ZMod q := (absNorm (span {a}) : ZMod q)`
- Checked with rg:
  - absNorm_congr_nine: Supplement:231, 253
  - absNorm_congr: QuadSupplement:244, 263, 272
  - int_dvd_of_dvd: Supplement:220, 244; QuadSupplement:257
  - intCast_dvd_of_dvd: DirichletCharHalfPlane:45, 61
  - normZ_congr: DirichletCharHalfPlane:53, 93
  - diff of Supplement 231–244 against QuadSupplement 244–257: 8 of 14 lines verbatim. The other 6 differ only in 9 against m and map_ofNat against map_intCast.
  - QuadSupplement imports EisensteinSupplement (line 2), and DirichletCharHalfPlane reaches both.
- Candidate: absNorm_congr_nine is absNorm_congr 9, proved separately. Round 495's DirichletCharHalfPlane re-proves int_dvd_of_dvd at a = q, and the same norm congruence (as normZ_congr) by a separate route.

7. B. src/EisensteinSupplement.lean:192 against src/EisensteinQuadSupplement.lean:216.
- Statements:
  - Supplement:192–193: `theorem absNorm_span_eq_prod {b : 𝓞 K} (hb : b ≠ 0) :` / `absNorm (span {b}) = ((normalizedFactors (span {b})).map absNorm).prod := by`
  - QuadSupplement:216–217: `theorem absNorm_eq_prod_nf {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :` / `absNorm I = ((normalizedFactors I).map absNorm).prod := by`
  - Both proofs are `conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self h0]` / `rw [Multiset.prod_hom]`.
- Checked with rg: absNorm_span_eq_prod at Supplement:192, 205, 209; absNorm_eq_prod_nf at QuadSupplement:216, 228, 239. QuadSupplement imports Supplement.
- Candidate: absNorm_span_eq_prod is absNorm_eq_prod_nf at I = span {b}, and the general lemma sits downstream.

8. B. src/EisensteinMeanSquareDual.lean:1078–1083 against src/EisensteinTransferRowCol.lean:515, 518. A definition is duplicated between a transfer file and a mean-square file.
- Inline code at MeanSquareDual:1078: `set U := (primesLe (max (⌈β * Z⌉₊ : ℝ) (2 * β * Z))).filter fun P => IsUnit (cls m {P}) with hUdef`. hU1 and hU2 (1079–1082) are `Finset.mem_filter.2 ⟨primesLe_mono (le_max_left _ _) hP, hu⟩`, and hUu is at 1083.
- Other location:
  - TransferRowCol:515: `def unitPrimes (m : 𝓞 K) (Y : ℝ) : Finset Pr := (primesLe Y).filter fun P => IsUnit (cls m {P})`
  - TransferRowCol:518–520: `theorem mem_unitPrimes_of {Y Y' : ℝ} (h : Y ≤ Y') {P : Pr} (hP : P ∈ primesLe Y)` … `unfold unitPrimes; exact Finset.mem_filter.2 ⟨primesLe_mono h hP, hu⟩`
- Checked:
  - `rg -n "IsUnit \(cls m \{P\}\)|IsUnit \(cls md \{P\}\)" src`
  - unitPrimes is used at FirstTransfer:1012 and ThirdTransfer:335, 349, 544, 582.
  - TransferRowCol reaches MeanSquareDual, not the reverse.
  - The inputs are upstream of MeanSquareDual:1078: primesLe (RowCol:432), cls (RowCol:461), isUnit_cls_of_forall (RowCol:477) and primesLe_mono (MeanSquareDual:295).
- Candidate: round 494's twisted mean square rebuilds round 492's unitPrimes and mem_unitPrimes_of inline. The definition could sit next to primesLe_mono and serve both files.

9. B (Mathlib). src/EisensteinQuadSupplement.lean:494.
- Statement: `theorem dvd_of_dvd_mul_left' {a b c : 𝓞 K} (h : a * b ∣ c) : a ∣ c := (dvd_mul_right a b).trans h`
- Mathlib Algebra/Divisibility/Basic.lean:88–89: `theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c :=` / `(dvd_mul_right a b).trans h`
- Checked with rg: QuadSupplement:494, 500 (the only use) and 579 (#print).
- Candidate: same statement and proof as Mathlib's dvd_of_mul_right_dvd.

10. B (Mathlib). src/EisensteinPrepared.lean:934.
- Statement: `theorem pow_rpow_comm {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) : (a ^ n) ^ x = (a ^ x) ^ n := by`
- Mathlib Analysis/SpecialFunctions/Pow/Real.lean:420: `lemma rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : (x ^ y) ^ n = (x ^ n) ^ y := by`
- Checked with rg: Prepared:934, 1038 (twice) and 1039.
- Candidate: pow_rpow_comm ha n x is (Real.rpow_pow_comm ha.le x n).symm.

11. B (Mathlib). src/EisensteinRowTwist.lean:174.
- Statement: `theorem count_nf_pow (P : Ideal (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (n : ℕ) :` / `(normalizedFactors (I ^ n)).count P = n * (normalizedFactors I).count P := by`
- Mathlib:
  - RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean:165–166: `theorem normalizedFactors_pow {x : α} (n : ℕ) :` / `normalizedFactors (x ^ n) = n • normalizedFactors x := by`
  - Algebra/Order/Group/Multiset.lean:184: `lemma count_nsmul (a : α) (n s) : count a (n • s) = n * count a s := by`
- Checked with rg: RowTwist:174, 194 (two uses) and 528 (#print).
- Candidate: the lemma is `rw [normalizedFactors_pow, Multiset.count_nsmul]`, and the hypothesis hI is not needed.

12. B (Mathlib). src/EisensteinThetaAssembly.lean:78 and src/EisensteinRowTwist.lean:278.
- Statements:
  - ThetaAssembly:78–79: `theorem mem_nf_of_dvd {I Q : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hQ : Prime Q) (h : Q ∣ I) :` / `Q ∈ normalizedFactors I := by`
  - RowTwist:278: `theorem mem_nf_span_of_mem {x : 𝓞 K} (hx : x ≠ 0) {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (h : x ∈ P) :`
- Mathlib RingTheory/DedekindDomain/Ideal/Lemmas.lean:141–142: `nonrec theorem mem_normalizedFactors_iff {p I : Ideal A} (hI : I ≠ ⊥) :` / `p ∈ normalizedFactors I ↔ p.IsPrime ∧ I ≤ p := by`. The stack already uses it this way at KubotaCuspSums:611: `exact ⟨(Ideal.mem_normalizedFactors_iff hbot).2 ⟨hP, by rwa [Ideal.span_singleton_le_iff_mem]⟩, h3⟩`.
- Checked:
  - rg: mem_nf_of_dvd at ThetaAssembly:78, 143, 161, 162 and RowTwist:280; mem_nf_span_of_mem at RowTwist:278, 359, 368, 374.
  - `rg -n mem_normalizedFactors_iff src external`: 10 hits, including KubotaCuspSums:601, 611 and EisensteinCount:173, 263.
- Candidate: both lemmas are the ← direction of Ideal.mem_normalizedFactors_iff. mem_nf_span_of_mem converts IsPrime to Prime and ≤ to ∣, only for mem_nf_of_dvd to recover them.

13. B. src/EisensteinThetaMeanSquare.lean:28 against src/HalfPlaneMeanSquare.lean:558.
- Statements:
  - ThetaMeanSquare:28–29: `theorem norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (f : ι → ℂ) :` / `‖∑ i ∈ s, f i‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖f i‖ ^ 2 :=`
  - HalfPlaneMeanSquare:558–559: `theorem norm_sum_sq_le (T : Finset (𝓞 K)) (A : 𝓞 K → ℂ) :` / `‖∑ z ∈ T, A z‖ ^ 2 ≤ T.card * ∑ z ∈ T, ‖A z‖ ^ 2 := by`
  - Both proofs use the same two steps: pow_le_pow_left₀ with norm_sum_le, then sq_sum_le_card_mul_sum_sq.
- Checked with rg: norm_sum_sq_le_card at ThetaAssembly:206, ThetaMeanSquare:489 and EisensteinQuadSieveNorm:491; norm_sum_sq_le at HalfPlaneMeanSquare:658 and HalfPlaneTwistMean:499. ThetaMeanSquare reaches HalfPlaneMeanSquare.
- Candidate: norm_sum_sq_le is norm_sum_sq_le_card at ι = 𝓞 K, and the general lemma is downstream.

14. B. src/MellinRowDep.lean:469 (used by Prepared:562) against src/EisensteinCubeReduction.lean:125.
- Statements:
  - MellinRowDep:469–471: `theorem norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)` / `(x : ι → ℂ) :` / `‖∑ i ∈ s, (w i : ℂ) * x i‖ ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖x i‖ ^ 2 := by`
  - CubeReduction:125–127: `theorem norm_sum_sq_le_weighted {ι : Type*} (s : Finset ι) (c z : ι → ℂ) (w : ι → ℝ)` / `(hw : ∀ i ∈ s, 0 ≤ w i) (hc : ∀ i ∈ s, ‖c i‖ ≤ 1) :` / `‖∑ i ∈ s, c i * (w i : ℂ) * z i‖ ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖z i‖ ^ 2 := by`
  - Both use the same √w Cauchy–Schwarz argument through Finset.sum_mul_sq_le_sq_mul_sq.
- Checked:
  - rg: MellinSep.norm_sum_mul_sq_le has one use (Prepared:562); norm_sum_sq_le_weighted has one use (CubeReduction:282).
  - `git log -S`: the lemmas came in round 340 (648af87) and round 314 (b8bf6c1).
  - Neither file reaches the other, and both reach EisensteinMeanSquareDual.
- Candidate: round 340 re-proved round 314's lemma at c = 1 because neither file imports the other.

15. B. src/EisensteinThetaMeanSquare.lean:33 against src/KubotaPhi.lean:43.
- Statements:
  - ThetaMeanSquare:33: `theorem card_units_le : Fintype.card (𝓞 K)ˣ ≤ 6 := by`
  - KubotaPhi:43: `theorem card_units_O : Fintype.card (𝓞 K)ˣ = 6 := by`, proved from the cyclotomic torsion order and units_pow_six (EisensteinSymbol:57).
- Checked:
  - rg: card_units_le at ThetaAssembly:649 and ThetaMeanSquare:266; card_units_O at KubotaPhi:124.
  - `rg -n "Fintype.card \(𝓞 K\)ˣ|Nat.card \(𝓞 K\)ˣ" src` finds no other such statement.
  - KubotaPhi reaches ThetaMeanSquare.
- Candidate: card_units_le is card_units_O.le. The equality sits downstream although its inputs are in EisensteinSymbol.

16. B (minor). src/EisensteinThetaRows.lean:204 and :121; src/EisensteinRowTwist.lean:165.
- ThetaRows:204: `theorem lam_not_mem (P : Pr) : (Eis.ω - 1 : 𝓞 K) ∉ P.1 := by` (6 lines). It equals `fun h => P.2.2 (six_mem_of_lam_mem P.1 h)`, using EisensteinSymbol:89 `theorem six_mem_of_lam_mem (h : ω - 1 ∈ P) : (6 : 𝓞 K) ∈ P := by`.
- ThetaRows:121: `theorem four_not_mem (P : Pr) : (4 : 𝓞 K) ∉ P.1 := by`. Lines 125–127 (`have h6 : (2 : 𝓞 K) * 3 ∈ P.1 := P.1.mul_mem_right 3 h2` / `norm_num at h6` / `exact P.2.2 h6`) re-prove EisensteinSymbol:84, six_mem_of_two_mem.
- The step δ₃ ∈ P ⇒ 3 ∈ P: `rg -n -F "(3 : 𝓞 K) = -(δ3 * δ3)" src external` finds RowTwist:167 (inside six_of_δ3), KubotaTranslates:367 (inside δ3_not_mem_of_factor, upstream of RowTwist), KubotaCuspSums:230, and KubotaPhi:143. KubotaPhi:142 holds the only named lemma, `theorem three_mem_of_δ3_mem {P : Ideal (𝓞 K)} (h : δ3 ∈ P) : (3 : 𝓞 K) ∈ P := by`, and it is downstream of the other three sites.
- Candidate: two small re-proofs of lemmas the file already sees. The δ₃ step is written inline three times and named once, downstream.

17. B (minor). src/EisensteinDualMeanSquare.lean:45.
- Statement: `instance finite_quot_of_neZero {m : 𝓞 K} [NeZero m] : Finite (𝓞 K ⧸ span {m}) :=`
- Other locations:
  - KubotaConstTerm:346: `theorem finite_quot_three_mul {c : 𝓞 K} (hc : c ≠ 0) : Finite (𝓞 K ⧸ span {3 * c}) :=`, with the same `Ideal.finiteQuotientOfFreeOfNeBot` proof
  - KubotaEisTrunc:63: `instance finite_quot_three : Finite (𝓞 K ⧸ span {(3 : 𝓞 K)}) := by`
  - ThetaAssembly:185–186, inline `have : Finite (𝓞 K ⧸ span {M}) :=`
- Checked: rg finds 10 uses of finite_quot_three_mul. KubotaConstTerm and KubotaEisTrunc both reach DualMeanSquare.
- Candidate: round 492's instance covers both older lemmas, given a NeZero (3 * c) from three_mul_ne_zero, and also the inline copy.

18. C. src/EisensteinTransferRowCol.lean:62 and src/EisensteinCubeReduction.lean:392.
- Statements:
  - TransferRowCol:62–63: `theorem colP_union (ξ : MulChar (𝓞 K ⧸ span {m}) ℂ) (y c : 𝓞 K) {V M : Finset Pr}` / `(h : Disjoint V M) : colP ξ y c (V ∪ M) = colP ξ y c V * colP ξ y c M := by`
  - CubeReduction:392–393: `theorem rowE_nonneg (ξ : MulChar (𝓞 K ⧸ span {m}) ℂ) (W : ℝ → ℂ) (L : ℝ)` / `(Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)) : 0 ≤ rowE ξ W L Fs T :=`
- Checked:
  - `rg -n -w colP_union src external`: TransferRowCol:62 and 531 (#print) only.
  - rowE_nonneg: CubeReduction:392 and 796 (#print) only.
  - Neither name appears in a docstring.
  - `git grep -n -w <name> 2d63e9e -- src external`: also declaration and #print only at 2d63e9e. Both were generalized from span {(4 : 𝓞 K)} in round 492.
- Candidate: two helpers have no user, had none at stack review 2, and were still carried through round 492.

19. C/E (superseded; a docstring headline, so not dead under the brief's rule). src/EisensteinSecondPoisson.lean:340, 39, 77.
- Declarations: `theorem Mq_rowcol [NeZero m] [Fact ((4 : 𝓞 K) ∣ m)] (ξ1 : MulChar (𝓞 K ⧸ span {m}) ℂ)` (340–421), pairTerm_expandTw (39–68) and pair_char_formTw (77–138).
- Docstrings:
  - SecondPoisson:20: "* **`Mq_rowcol`**: `𝓜` in row/column form; **`zero_Mq_le`**: its zero frequency."
  - PairRatio:10–12: "Round 321's `Mq_rowcol` expands the twisted paired factor in pairs `(ξ_a, ξ_b)` of characters (modulo `m` since round 492), and its row factor `ā_{ξ_a}(w)a_{ξ_b}(w)` does not cancel when `ξ_a ≠ ξ_b`."
  - The consumer TransferRegroup:127 uses Mq_rowcolD (PairRatio:396).
- Checked:
  - rg: Mq_rowcol has no code use (declaration at 340, #print at 459, docstrings only).
  - pairTerm_expandTw is used only at :120, inside pair_char_formTw. pair_char_formTw is used only at :392, inside Mq_rowcol.
  - At 2d63e9e, Mq_rowcol had no code use either.
  - `git diff 2d63e9e -U0`: the hunks inside 39–138 and 340–421 add 62 lines.
- Candidate: Mq_rowcol and its two helpers (174 lines) have had no consumer since round 322's Mq_rowcolD superseded them. Round 492 still generalized them to modulus m.

20. D. src/EisensteinPrepared.lean:160 against src/HalfPlaneMeanSquare.lean:40.
- Statements:
  - Prepared:160–161: `theorem three_not_mem_of_factor {I P : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 3)` / `(hP : P ∈ normalizedFactors I) : (3 : 𝓞 K) ∉ P := by` (160–175)
  - HalfPlaneMeanSquare:40–41: `theorem six_not_mem_of_factor {I P : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6)` / `(hP : P ∈ normalizedFactors I) : (6 : 𝓞 K) ∉ P := by` (40–53)
- Checked: `sed -n 39,53p HalfPlaneMeanSquare.lean | sed -e 's/36/9/g' -e 's/6/3/g' -e 's/six_not_mem_of_factor/three_not_mem_of_factor/'` diffed against `sed -n 159,175p Prepared.lean`. Only HalfPlaneMeanSquare:47–48 (`rw [← absNorm_six]` / `exact absNorm_dvd_absNorm_of_le …`) differ, against Prepared:167–170.
- Candidate: one lemma for a natural n (norm prime to n ⇒ (n : 𝓞 K) ∉ P, through absNorm_natCast_span_sq n) gives both.

21. D. src/EisensteinThetaRows.lean:392 against src/EisensteinThetaMeanSquare.lean:82.
- Statements: `theorem norm_dualCoef_le {d : DualIdx → ℂ} {Kd : ℝ} (hKd : 0 ≤ Kd)` (392–422) and `theorem norm_coefRest_le {d : DualIdx → ℂ} {Kd : ℝ} (hKd : 0 ≤ Kd)` (82–116).
- Checked: diff shows 19 of 31 lines verbatim. The rest differ only in the product being bounded (∏ over A of √N(P), against the product over A.filter (j P % 6 ≠ 4) of wB) and in its bounds hPB and hP0.
- Candidate: a lemma that takes the product's bound B ≥ 0 as a hypothesis would serve both.

22. D. src/EisensteinSupplement.lean:264 (in cub_unit_congr, :257) and src/EisensteinQuadSupplement.lean:308 (in sym2_unit_congr, :300).
- The skeleton is `rcases List.mem_cons.1 (units_mem u) with rfl | hu`, then five `rcases List.mem_cons.1 hu with rfl | hu`, then `simp at hu`.
- Checked:
  - `rg -n units_mem src external` finds the same six-way split at EisensteinSymbol:62 and 102, EisensteinCubicChar:52 and 244, KubotaCuspSums:414, Supplement:264 and QuadSupplement:308.
  - `rg` for an existing ±ωʲ lemma (`ωu \^ j|∃ j.*ωu`) finds nothing besides units_mem (EisensteinSymbol:52).
- Candidate: the 7-line case skeleton over the six units is written out seven times. Two of the sites are in scope.

23. D. src/EisensteinSupplement.lean:300.
- Statement: `theorem cub_δ3_congr_odd {p p' : 𝓞 K} (hp : Primary p) (hp' : Primary p') (h2 : IsCoprime p 2)`
- Checked: the branches at 321–334 and 337–348 share 9 verbatim lines. They differ only in the hv' target (`-(t' + 1)` against `-t'`) and in the comparison point (`primary_neg_two` with hq2 and hq2', against `primary_one` with `isCoprime_one_right`).
- Candidate: the two branches are one argument parametrized by the comparison point q ∈ {−2, 1}.

24. D. The pair-expansion families, five copies each. This overlaps candidates 1 and 19, which account for two copies of each family.
- pair_char_form*: RowCol:808, RowCol:1134, TransferRowCol:246 (pair_char_form_dual), PairRatio:334 (pair_char_formD), SecondPoisson:77
- pairTerm_expand*: RowCol:536, RowCol:1100, TransferRowCol:97 (dualPair_expand), PairRatio:298, SecondPoisson:39
- *_rowcol: RowCol:1017, RowCol:1215, TransferRowCol:442 (dualMS_rowcol), PairRatio:396, SecondPoisson:340
- Checked:
  - `rg -n -F "rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]" src`: RowCol:855 and 1198, TransferRowCol:300, SecondPoisson:129, PairRatio:382.
  - `rg -n -F "· subst he; rw [Finset.inter_self]" src`: TransferRowCol:303, RowCol:858 and 1201, PairRatio:385, SecondPoisson:132.
  - Pairwise diffs of the five pair_char_form* bodies (56–74 lines each): 26–48 lines of one reappear verbatim in another. The largest overlap is PairRatio 334–389 against SecondPoisson 77–138, 48 of 56 lines.
  - Round 332 already factored the neighbouring steps: RowCol:310–314 on sum_pair_chain ("`xi_chain`, `xi_chainQ` and `xi_chain_dual` are its instances") and MeanSquareDual:212–214 on norm_zeroSum_le.
- Candidate: the split of one pair into characters is written five times with renamings. It is the step round 332 left unfactored.

25. F. src/EisensteinQuadSupplement.lean:287–288.
- Docstring: "**The quadratic symbols of the units** depend only on the class modulo `4`."
- It sits on `theorem sym6_one_left {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) : sym6 1 I = 1 := by`.
- The property it describes is QuadSupplement:300, sym2_unit_congr, which has no docstring: `theorem sym2_unit_congr (u : (𝓞 K)ˣ) {x x' : 𝓞 K} (h6 : (absNorm (span {x})).Coprime 6)` / `(h6' : (absNorm (span {x'})).Coprime 6) (h4 : (4 : 𝓞 K) ∣ x - x') :`
- Checked: `sed -n 284,300p`.
- Candidate: the docstring is attached to the wrong declaration.

26. F. src/EisensteinDualExcl.lean:258–259.
- Docstring: "A character of `ℤ[ω]/4` has values of norm at most `1`."
- Statement: `theorem norm_xi_le [NeZero m] (ξ : MulChar (𝓞 K ⧸ span {m}) ℂ) (x : 𝓞 K ⧸ span {m}) :`
- At 2d63e9e (DualExcl:252–253) the same docstring sat over `(ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)`.
- Checked: an awk scan of the 18 Part 2 files for docstrings naming `ℤ[ω]/4` or "modulo `4`" over m-general declarations found only this one. PairRatio:242 and 249 describe the reduction to 4 correctly.
- Candidate: round 492 generalized the statement to any m ≠ 0 but left the modulus-4 docstring.

E: none found. `rg -n "set_option|maxHeartbeats|maxRecDepth|native_decide|\bdecide\b"` over the nine Part 1 files finds no hits, and the same pattern over the added lines of the 18-file diff finds 0.

Checked and excluded:
- twist_617, tgPrimes_four (with four_not_mem), sym6_sq_omega_congr and famSum_eq have no code use but are named in their module docstrings, so the headline rule applies.
- cub_omega_ideal and the sym6 induction scaffold are mostly inside Cubic/SexticCharHalfPlane, the branch §9.3 already lists as superseded.

Scratch files written (none in the repository):
- /tmp/claude-0/-home-user-r-infinite/db46f946-fd0e-58a3-baf6-61ea74b579d4/scratchpad/tmp_reader_a950/
- At the scratchpad top level I wrote a1–a4, b1–b4, x1, x2 and s2. If another agent used those names, I may have overwritten its files.