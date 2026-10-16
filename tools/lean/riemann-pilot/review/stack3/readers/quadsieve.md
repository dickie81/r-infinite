<!-- Stack review 3 reader report: model output, a list of CANDIDATES, not findings. STRUCTURAL-REVIEW.md §9.2 and §9.7 record what the lead verified (Check 3). Scratchpad paths below are the reader's session files, not committed. -->

Running mandatory review protocol. Checks 0–9 active.

COVERAGE (Read tool, chunked where needed)
src/EisensteinQuadSieveBase.lean: lines 1–611 read
src/EisensteinQuadSieveCor.lean: lines 1–792 read
src/EisensteinQuadSieveErrors.lean: lines 1–718 read
src/EisensteinQuadSieveFinal.lean: lines 1–167 read
src/EisensteinQuadSieveGamma.lean: lines 1–260 read
src/EisensteinQuadSieveGcdPart.lean: lines 1–477 read
src/EisensteinQuadSieveLattice.lean: lines 1–704 read
src/EisensteinQuadSieveLemma14.lean: lines 1–398 read
src/EisensteinQuadSieveMain.lean: lines 1–385 read
src/EisensteinQuadSieveMainBound.lean: lines 1–357 read
src/EisensteinQuadSieveNorm.lean: lines 1–672 read
src/EisensteinQuadSieveRecursion.lean: lines 1–782 read
src/EisensteinQuadSieveSep.lean: lines 1–1203 read
src/EisensteinQuadSieveSigma3.lean: lines 1–295 read
src/EisensteinQuadSieveSigma4.lean: lines 1–318 read
src/EisensteinQuadSieveSquares.lean: lines 1–397 read
STRUCTURAL-REVIEW.md lines 322–405 (§9) read. Its only item on these files (Base:171 `one_le_absNorm_of_ne_zero` vs MeanSquareBlock:482) is not re-reported.

Conventions. Paths are under tools/lean/riemann-pilot/src unless marked. ML = /tmp/claude-0/-home-user-r-infinite/db46f946-fd0e-58a3-baf6-61ea74b579d4/scratchpad/mathlib4/Mathlib.
- Import chain, from `grep -n "^import" src/EisensteinQuadSieve*.lean`: Norm → Base → Sep → Lemma14 → Lattice → Squares → Sigma4 → Sigma3 → Errors → Gamma → Main → MainBound → GcdPart → Recursion → Cor → Final.
- "Upstream" means in the closure of Norm's `^import` lines, found by a BFS over 121 modules. The list is at /tmp/claude-0/-home-user-r-infinite/db46f946-fd0e-58a3-baf6-61ea74b579d4/scratchpad/sr3/norm_closure.txt.
- Dead-code sweep: for each of the 373 declarations, `rg -n -w -F <name> src external`, minus the declaration line, its `#print axioms` line and mentions in backticked docstrings.

CANDIDATES

(A) Doors and missed connections

1. A — Norm.lean:343
- Statement: `theorem coprime6_of_primary {n : 𝓞 K} (hn : n ≠ 0) (hp : Primary n) (h2 : ¬ (2 : 𝓞 K) ∣ n) :`
- Other locations:
  - EisensteinSupplement.lean:198–200: `theorem primary_ne_zero {b : 𝓞 K} (hb : Primary b) : b ≠ 0 := by` / `rintro rfl` / `exact Primary.not_lam_dvd hb (dvd_zero _)`.
  - EisensteinQuadSupplement.lean:328–330: `theorem coprime6_of_primary_two {r : 𝓞 K} (hr : Primary r) (h2 : ¬ (2 : 𝓞 K) ∣ r) : … := coprime6_of_primary (primary_ne_zero hr) hr h2`.
  - Norm's two callers build `hn` from squarefreeness, at Norm:538–539 and Norm:588–589: `intro h0; apply hsq.ne_zero; rw [h0, Ideal.span_singleton_eq_bot.2 rfl]; rfl`.
- Checked:
  - `rg -n "theorem primary_ne_zero"` → EisensteinSupplement.lean:198. That module is not upstream of Norm.
  - `rg -n "theorem Primary.not_lam_dvd"` → EisensteinCubicChar.lean:282, which is upstream.
  - `rg -n coprime6_of_primary` → Norm:548, Norm:590, QuadSupplement:330.
  - The wrapper `coprime6_of_primary_two` is used at QuadSupplement:339 and 451, and at EisensteinRowTwist:270, 396 and 397.
- Candidate: `hn` follows from `hp` in two lines whose only ingredient is already upstream of Norm, and a later wrapper exists only to drop it.

2. A — Main.lean:148
- Statement: `theorem summable_of_eltsLe {f : 𝓞 K → ℂ} (Y : ℝ)` / `(h : ∀ d, Y < (absNorm (span {d}) : ℝ) → f d = 0) : Summable f :=`
- The same `summable_of_ne_finset_zero (s := eltsLe …)` argument is re-proved at:
  - Sep:1092 `theorem summable_admW (M : ℝ) : Summable (admW M) := by` (ℝ-valued);
  - Errors:203 `theorem summable_sqfW (Y : ℝ) : Summable (sqfW Y) := by` (ℝ-valued);
  - MainBound:41 `theorem summable_wR (Y₁ Y₂ : ℝ) : Summable (wR Y₁ Y₂) := by` (ℝ-valued);
  - MainBound:204 `theorem summable_cU (G U : Finset Pr) (K₁ Kt : ℝ) (f : 𝓞 K → ℂ) :` (ℂ-valued, downstream of Main).
- Checked: `rg -n "summable_of_ne_finset_zero \(s := eltsLe" src` → Sep:1093, Errors:204, MainBound:42, MainBound:206, Main:150. No hits elsewhere.
- Candidate: the lemma is stated for ℂ only although its proof works for any target. The three ℝ-valued weights re-prove it, and `summable_cU` re-proves it even though the lemma is already upstream.

(B) Duplicates

3. B and D — Sep:419 vs Recursion:45
- Sep:419: `theorem fBound_gcd {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) {δ : ℝ} (hδ : 0 < δ) :` … `FBound w N (C * N ^ δ * Δ + ∑ G ∈ fsLe g0, F3 G) := by`
- Recursion:45: `theorem fBoundP_gcd {δ : ℝ} (hδ : 0 < δ) :` / `∃ C : ℝ, 0 ≤ C ∧ ∀ (w : 𝓞 K → ℝ), (∀ m, 0 ≤ w m) → Summable w →` / `∀ (S : Finset Pr → Prop) …` … `FBoundP w S N (C * N ^ δ * Δ + ∑ G ∈ fsLe g0, F3 G) := by`
- Checked:
  - `diff <(sed -n 425,505p src/EisensteinQuadSieveSep.lean) <(sed -n 52,132p src/EisensteinQuadSieveRecursion.lean)` → 3 of 81 lines differ: the binder line, and `(h𝒩 A hA)` vs `(h𝒩 A hA).2` twice.
  - `rg -w fBound_gcd` → no code use. Sep:15, Recursion:9 and Recursion:43 are docstrings; Sep:1194 is its print line.
- Candidate: `fBound_gcd` is `fBoundP_gcd` at `S := fun _ => True`, and `fBoundP_gcd`'s constant is also uniform in `w`. The ~80-line body is copied, and `fBound_gcd` has no consumer.

4. B and D — Lattice:198 vs MellinSeparation.lean:226
- Lattice:198: `theorem mellin_of_schwartz (G : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ) :`
- MellinSeparation:226: `theorem mellin_of_dual (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G) …`
- Both conclude `∃ c : 𝓢(ℝ, ℂ), ∀ y : ℝ, 0 < y → G (Real.sqrt y) = ∫ t : ℝ, c t * ((y : ℂ) ^ ((-σ : ℂ) + ((2 * Real.pi * t : ℝ) : ℂ) * I))`.
- Checked:
  - `diff <(sed -n 202,222p …Lattice.lean) <(sed -n 232,252p …MellinSeparation.lean)` → only line 1 differs: `schwartz_exp_comp_S G hσ …` vs `schwartz_exp_comp G hG hGb hR hσ …`.
  - `schwartz_exp_comp_S` (Lattice:58) and `schwartz_exp_comp` (MellinSeparation:137) share their setup verbatim (Lattice:60–67, MellinSeparation:141–147: `he1`, `he2`, `hGe`, `hfs`).
- Candidate: the 20-line Fourier-inversion step is copied. A lemma taking `h : 𝓢(ℝ, ℂ)` with `h v = e^{σv}·G(e^{v/2})` would serve both. Neither hypothesis set (Schwartz, vs bounded derivatives vanishing on [R, ∞)) implies the other.

5. B — Lemma14:149–155, inside `integrable_norm_mul_inv_norm`
- Text: `set C : ℝ := 2 ^ 3 * (Finset.Iic ((3 : ℕ), (0 : ℕ))).sup` / `(fun m => SchwartzMap.seminorm ℝ m.1 m.2) F with hC` / `have hbound : ∀ w : ℂ, (1 + ‖w‖) ^ 3 * ‖F w‖ ≤ C := by` …
- Other locations:
  - PlanePoisson.lean:110: `theorem schwartz_decay' (F : SchwartzMap ℂ ℂ) : ∃ C, 0 ≤ C ∧ ∀ z, (1 + ‖z‖) ^ 3 * ‖F z‖ ≤ C := by`. Same constant, same `one_add_le_sup_seminorm_apply` call.
  - The derived `h2` (Lemma14:162–163, `‖F w‖ ≤ C * ((1 + ‖w‖) ^ 3)⁻¹`) is PlanePoisson.lean:84 `schwartz_decay` (`‖F z‖ ≤ C * (1 + ‖z‖) ^ (-3 : ℝ)`).
- Checked: read both; PlanePoisson is upstream.
- Candidate: the decay bound is re-proved inline, with the same statement as `schwartz_decay'`.

6. B — Lemma14:94 vs EisensteinQuadGauss.lean:49
- Lemma14:94: `theorem fourier_gaussian_plane {t : ℝ} (ht : 0 < t) (x : ℂ) :` / `𝓕 (fun w : ℂ => cexp (-((Real.pi * t : ℝ) : ℂ) * (‖w‖ : ℂ) ^ 2)) x =` / `((t⁻¹ : ℝ) : ℂ) * cexp (-((Real.pi / t : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by`
- QuadGauss:49: `theorem fourier_gaussC (a : ℝ) (ha : 0 < a) (ξ : ℂ) :` / `𝓕 (gaussC a ha : ℂ → ℂ) ξ = ((a⁻¹ : ℝ) : ℂ) * cexp (-(π : ℂ) * ‖ξ‖ ^ 2 / a) := by`, where PlaneGaussian.lean:158–159 gives `gaussC a ha z = (Real.exp (-(π * a) * ‖z‖ ^ 2) : ℂ) := rfl`.
- Checked: `rg -n "fourier_gaussian_innerProductSpace" src` → Lemma14:99 and QuadGauss:55; both proofs run it and then `field_simp`. QuadGauss is upstream.
- Candidate: the same Gaussian Fourier identity is proved twice in two packagings.

7. B — Lemma14:168
- Statement: `theorem ae_ne_zero_complex : ∀ᵐ w : ℂ, w ≠ 0 := by`
- Other locations:
  - ML/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean:67: `lemma Measure.ae_ne (μ : Measure α) [NullSingletonClass μ] (a : α) : ∀ᵐ x ∂μ, x ≠ a :=`.
  - The instance for Haar measures is shown at ML/MeasureTheory/Measure/Haar/NormedSpace.lean:27–33.
  - The stack already calls `Measure.ae_ne volume T` at Osc.lean:293 and 349.
- Checked: `rg -n "theorem ae_ne|lemma ae_ne" ML/MeasureTheory`; `rg -n "ae_ne_zero|ae_ne\b" src` → only Lemma14 and Osc.
- Candidate: identical to Mathlib's `Measure.ae_ne volume 0`.

8. B — Errors:36
- Statement: `theorem integrable_mul_bdd {C g : ℝ → ℂ} (hC : Integrable C) (hg : Continuous g) {B : ℝ}` / `(hB : ∀ t, ‖g t‖ ≤ B) : Integrable fun t => C t * g t := by`
- Mathlib: ML/MeasureTheory/Function/L1Space/Integrable.lean:1072–1074: `theorem Integrable.mul_bdd {f g : α → 𝕜} {c : ℝ} (hf : Integrable f μ)` / `(hg : AEStronglyMeasurable g μ) (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ c) :` / `Integrable (fun x => f x * g x) μ :=`
- Checked: `rg -n "mul_bdd|bdd_mul" src external` → the Mathlib form is used in about a dozen places (e.g. MellinRowDep:122, OddPositivity:99).
- Candidate: a special case of Mathlib's `Integrable.mul_bdd`.

9. B — Lattice:541
- Statement: `theorem sum_powerset_neg_prod {ι : Type*} (S : Finset ι) (a : ι → ℂ) :` / `∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * ∏ P ∈ T, a P = ∏ P ∈ S, (1 - a P) := by`
- Mathlib: ML/Algebra/BigOperators/Ring/Finset.lean:261–262: `lemma prod_sub [DecidableEq ι] (f g : ι → R) (s : Finset ι) :` / `∏ i ∈ s, (f i - g i) = ∑ t ∈ s.powerset, (-1) ^ #t * (∏ i ∈ s \ t, f i) * ∏ i ∈ t, g i := by`
- Checked: `rg -n "lemma prod_sub\b" ML`. Uses of the stack lemma: Lattice:595, Lattice:683, Main:202.
- Candidate: Mathlib's `Finset.prod_sub` at `f = 1` is the more general statement.

10. B — Gamma:174
- Statement: `theorem I_zpow_four_mul_add (q k : ℤ) : I ^ (4 * q + k) = I ^ k := by`
- Mathlib: ML/Basic/Complex/Basic.lean:744 (namespace Complex): `lemma I_zpow_eq_zpow_mod (m : ℤ) : I ^ m = I ^ (m % 4) := by`
- Checked: `rg -n "I_zpow|zpow_four" src` → Gamma only. `gq4_val_eq_two` (Gamma:182–197) writes `a = 4q + r` and `b = 4s + u` by hand to use the lemma, before the 16-case `interval_cases r <;> interval_cases u <;> norm_num at h <;> norm_num <;> ring` at Gamma:198.
- Candidate: follows from Mathlib's `Complex.I_zpow_eq_zpow_mod`, which also gives the mod-4 reduction directly.

11. B — Recursion:545
- Statement: `theorem rpow_le_rpow_Q {Q a b : ℝ} (hQ : 1 ≤ Q) (hab : a ≤ b) : Q ^ a ≤ Q ^ b :=` / `Real.rpow_le_rpow_of_exponent_le hQ hab`
- Checked: `rg -w rpow_le_rpow_Q` → one use, Recursion:600. The same files call `Real.rpow_le_rpow_of_exponent_le` directly elsewhere (e.g. Cor:506, 714).
- Candidate: an identical restatement of a Mathlib lemma.

12. B — Lattice:349 vs KubotaThetaEq.lean:111
- Lattice:349: `instance countable_O : Countable (𝓞 K) := crdEquiv.symm.injective.countable`
- KubotaThetaEq:111: `have : Countable (𝓞 K) := crdEquiv.symm.injective.countable`
- Checked: `rg -n "injective\.countable|Countable \(𝓞"` → these two only. The BFS closure of KubotaThetaEq (174 modules) contains EisensteinQuadSieveLattice.
- Candidate: the local `have` re-derives a global instance that the file already imports. (`crdEquiv` itself is at EisensteinPoisson.lean:93, upstream.)

13. B — Gamma:156 (with Gamma:147) vs EisensteinQuadSupplement.lean:222 (with QuadSupplement:203)
- Gamma:156: `theorem q2_neg_one_eq (D : Finset Pr) :` / `q2 D (-1) = ((ZMod.χ₄ ((absNorm (idl D) : ℕ) : ZMod 4) : ℤ) : ℂ) := by`
- QuadSupplement:222: `theorem sym2_neg_one {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :` / `sym2 (-1) I = ((ZMod.χ₄ (absNorm I : ZMod 4) : ℤ) : ℂ) := by`
- Link:
  - Norm:83: `theorem sym2_idl (A : Finset Pr) (t : 𝓞 K) : sym2 t (idl A) = ∏ P ∈ A, quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) t)`; the right side is `q2 A t` by definition.
  - `idl_coprime6` (EisensteinMeanSquarePoisson:77).
  - Both proofs re-run Mathlib's `quadraticChar_neg_one` prime by prime (Gamma:153, QuadSupplement:206).
- Checked: read both. The closure of QuadSupplement contains Squares but not Gamma; Final's closure contains neither QuadSupplement nor EisensteinSupplement.
- Candidate: `q2_neg_one_eq` is the case `I = idl D` of the later and more general `sym2_neg_one`; the two sit in sibling modules.

14. B — Recursion:380–383
- Statement: `theorem card_fsLe_mono {x y : ℝ} (h : x ≤ y) : ((fsLe x).card : ℝ) ≤ (fsLe y).card := by` / `have : fsLe x ⊆ fsLe y := fun A hA => by` / `rw [mem_fsLe] at hA ⊢; exact hA.trans (Nat.floor_le_floor h)`
- Other locations:
  - EisensteinFirstTransfer.lean:833–834: `theorem fsLe_mono {x y : ℝ} (h : x ≤ y) : fsLe x ⊆ fsLe y := fun _A hA =>` / `mem_fsLe.2 ((mem_fsLe.1 hA).trans (Nat.floor_mono h))`.
  - EisensteinSecondPoisson.lean:423 `card_fsLe_le_max` takes the same card step through `fsLe_mono`.
- Related: Sep:602 `theorem card_fsLe_le' {x : ℝ} (hx : 0 ≤ x) : …` and SecondPoisson:423 `theorem card_fsLe_le_max (Λ : ℝ) : ((fsLe Λ).card : ℝ) ≤ (2 * kappa + 5) * max Λ 1 := by` are two separate extensions of `card_fsLe_le` (EisensteinMeanSquareDual:148). Cor:649 and Cor:661 call `card_fsLe_le'` with `0 ≤ 2 * g0` and `0 ≤ g0`, although `hg0 : 1 ≤ g0` (Cor:577) is in context.
- Checked: `rg -n "theorem fsLe_mono|theorem card_fsLe" src`.
- Candidate: `card_fsLe_mono` re-proves the upstream `fsLe_mono` inline.

15. B — Lattice:225–267 vs EisensteinPrepared.lean:136
- Lattice:225 (43 lines, via `EisensteinSeries.summable_one_div_norm_rpow` and coordinates): `theorem summable_absNorm_elt_rpow {s : ℝ} (hs : 1 < s) :` / `Summable fun μ : 𝓞 K => (absNorm (span {μ}) : ℝ) ^ (-s) := by`
- Prepared:136: `theorem summable_absNorm_rpow {s : ℝ} (hs : 1 < s) :` / `Summable fun I : Ideal (𝓞 K) => (absNorm I : ℝ) ^ (-s) := by`
- Checked: `rg -n "summable_absNorm|summable_one_div_norm_rpow" src` → only these two. Prepared is upstream.
- Candidate: related but not identical (elements vs ideals). The element sum is controlled by the ideal sum through `μ ↦ span {μ}`, whose fibres on μ ≠ 0 have size `Fintype.card (𝓞 K)ˣ`.

16. B — inline re-proofs of lemmas the stack already names (2–4 lines each, seven places):
- Lattice:363–365 and Lattice:421–423: `exact_mod_cast Nat.one_le_iff_ne_zero.2 (by` / `rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hμ)`. This is Base:171 `one_le_absNorm_of_ne_zero`, upstream of Lattice. (The Base/MeanSquareBlock pair is §9.3's; these two copies are not listed there.)
- Lattice:607–610: `have hQ : (0 : ℝ) < absNorm Q.1 := by` / `have h := one_le_nI {Q}` … This is EisensteinThetaRows.lean:567 `theorem absNorm_Pr_pos (P : Pr) : (0 : ℝ) < absNorm P.1 := by`.
- MainBound:133–135: `have h1 : (1 : ℝ) ≤ absNorm Q.1 := by` / `have := one_le_nI {Q}` / `rwa [nI_eq_prod, Finset.prod_singleton] at this`. This is the cast of EisensteinMeanSquareRowCol.lean:437 `theorem one_le_absNorm_Pr (P : Pr) : 1 ≤ absNorm P.1 :=`, which Cor:32 uses exactly that way.
- Sigma3:265–268 and Sigma4:185–188: `refine Nat.cast_pos.2 (Nat.pos_of_ne_zero ?_)` / `rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]` / `exact sqf_ne_zero hd`. This is Errors:229 `absNorm_sqf_pos`, with the same three lines, declared downstream of both.
- Squares:105–106 and Squares:226–227: `intro h; rw [h, Ideal.span_singleton_eq_bot.2 rfl] at hd; exact hd.ne_zero rfl`. This is Sigma4:74 `sqf_ne_zero`, declared downstream.
- Checked:
  - `rg -n "absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot\]" src/EisensteinQuadSieve*.lean` → Base:173, Sigma3:267, Lattice:365, Lattice:423, Sigma4:187, Errors:232.
  - `rg -n "span_singleton_eq_bot.2 rfl"` → Squares:106, Squares:227, Sigma4:75, Norm:539, Norm:589 (plus files outside the 16).
- Candidate: five facts that have named lemmas are re-derived inline at seven places.

17. B — Squares:344–347 and Sigma4:88–93
- Text in both: `have hb : ((Real.sqrt M)⁻¹ : ℂ) ≠ 0 := by` / `rw [ne_eq, inv_eq_zero]; exact_mod_cast …` / `have hs := summable_σO (affS Majorant.Phi 0 ((Real.sqrt M)⁻¹ : ℂ) hb)`
- Other locations:
  - EisensteinMeanSquarePoisson.lean:487: `theorem Phi_div_sqrt_eq (H : ℝ) (hH : 0 < H) :` builds exactly this `affS`.
  - MeanSquarePoisson:496: `theorem summable_mul_Phi (H : ℝ) (hH : 0 < H) (g : 𝓞 K → ℂ) {B : ℝ} (hg : ∀ u, ‖g u‖ ≤ B) :`.
  - GcdPart:121–122 gets the same `sig4` summand summable with `have hs4 := summable_mul_Phi M hM _ hb4`.
  - Cor:435–439 gets the real part summable with `summable_mul_Phi M hM (fun _ => 1) …` and `Complex.reCLM.summable`.
- Checked: `rg -n "theorem Phi_div_sqrt_eq|theorem summable_mul_Phi"` → MeanSquarePoisson:487 and 496, both upstream.
- Candidate: `summable_bw` (9 lines) and `sig4_eq`'s `hfs` (Sigma4:89–100, 12 lines) rebuild `Phi_div_sqrt_eq`/`summable_mul_Phi`, which the later files use for the same sums.

18. B and D (near-generated) — the quadratic product character `q2` (Base:32) and the sextic `chiS` (EisensteinMeanSquarePoisson:75) carry the same basic lemmas with identical proofs:
- Base:48–50 `theorem q2_union …` / `unfold q2; rw [Finset.prod_union h]` vs MeanSquarePoisson:128–130 `theorem chiS_union …` / `unfold chiS; rw [Finset.prod_union h]`.
- Base:92–94 `theorem q2_mul …` vs EisensteinMeanSquareRowCol.lean:690–692 `theorem chiS_mul …`: the same three lines.
- Sigma4:49–52 `theorem q2_zero …` vs RowCol:594–597 `theorem chiS_zero …`: the same four lines.
- Link: `q2 A u = chiS A u ^ 3`, from Norm:83 `sym2_idl`, MeanSquarePoisson:115 `sym6_idl` and EisensteinSymbol.lean:346 `noncomputable def sym2 (a : 𝓞 K) (I : Ideal (𝓞 K)) : ℂ := sym6 a I ^ 3`. Base:361 `sym2_eq_q2` already uses this route.
- Candidate: the q2 lemmas re-prove the chiS ones with the character renamed; they follow from the chiS lemmas through the cube.

(C) Dead code

19. C — Lemma14:379
- Statement: `theorem integral_dualG_sq {a : ℝ} (ha : 0 < a) :` / `∫ z : ℂ, dualG (a * ‖z‖ ^ 2) =` / `((Real.pi / a : ℝ) : ℂ) * ∫ s in Ioi (0 : ℝ), Majorant.Phi ((s : ℝ) : ℂ) := by`
- Checked: `rg -w integral_dualG_sq src external` → Lemma14:21 (header), 379 (declaration), 398 (print) only.
- Candidate: no use. The main terms go through `integral_dualR_Ioi` (Sigma3:39) and `excl_eq_main_add` instead. See also item 34.

20. C — Norm:512
- Statement: `theorem QExp.reverse {α : ℝ} (h : QExp α) (ε : ℝ) (hε : 0 < ε) :`
- Checked: `rg -n "reverse" src external` → Norm:27 (header), 512, 670 (print) only.
- Candidate: no use. `qExp_two` (Base:584) and `qExp_improve` (Final:107) apply `QBound.symm` directly.

21. C — Norm:482
- Statement: `theorem qBound_trivial {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :` / `QBound M N ((2 * kappa + 5) ^ 2 * M * N) := by`
- Checked: `rg -w qBound_trivial` → Norm:24 (header), 482, 669 (print) only.
- Candidate: no use. The recursion uses the weighted analogue `fBound_triv` (Recursion:208).

22. C — headline results with no consumer. Under the brief's rule these are not dead; they are listed for the record.
- Sep:859: `theorem fBound_sep {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) {δ : ℝ} (hδ : 0 < δ) :` (Heath-Brown's Lemma 10).
- Lemma14:358: `theorem integral_fourier_Phi_sq {α : ℂ} (hα : α ≠ 0) :` (the planar Lemma 14).
- Sep:419 `fBound_gcd` (item 3).
- Checked: `rg -w` on each → declaration, print line and docstrings only.
- Helpers reachable only from `fBound_sep`: `pow_clog_lt_two_mul` (Sep:591), `sum_union_subset_le` (615), `count_cover` (632), `sum_triple_swap` (692), `sum3_sqrt_le` (730), `sum_powerset_compl` (749) and `nI_clog_bounds` (842). Each one's only use is inside this chain. With `fBound_sep` itself that is about 385 lines (Sep:591–599, 615–756, 841–1075).
- The only other caller of `sep_one` is Sigma4:231, with `Ad := ∅`, where `ite_disjoint_cover` (Sep:514) is trivial.
- Candidate: the Lemma-10 branch is proved but feeds nothing.

(D) Patterns

23. D — Lemma14:211–231 vs 232–252 (`hint1`/`hint2` in `integral_fourier_mul_inv_norm`)
- `have hint1 : Integrable (Function.uncurry fun (w : ℂ) (t : ℝ) => G w * ((k w t : ℝ) : ℂ))`
- `have hint2 : Integrable (Function.uncurry fun (x : ℂ) (t : ℝ) => F x * ((k' x t : ℝ) : ℂ))`
- Checked: `diff` of the two ranges → only renamings: G/F, k/k', w/x, hk/hk', hkint/hk'int, hk0/hk'0, `integral_kernel_eq`/`integral_dual_kernel_eq`.
- Candidate: a 21-line block repeated with renamings. One lemma over a kernel family (nonnegative, integrable on (0, ∞), integral ‖w‖⁻¹) would replace both.

24. D — MainBound:295–307 vs 308–320 (`hsa`/`hsb` in `main_bilin`)
- `have hsa : Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * ‖α T U B‖ ^ 2) ≤`
- `have hsb : Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * ‖β T U B‖ ^ 2) ≤`
- Checked: `diff` of the two ranges → only α/β, a/b, hα/hβ.
- Candidate: a 13-line block repeated with renamings.

25. D — Sep:160–173 vs 235–248 (the tails of `sum_disjoint_factor` and `sum_inter_eq_factor`)
- `by_cases h1 : E ⊆ A1 ∧ P A1` / `by_cases h1 : G ∪ E ⊆ A1`
- Checked: `diff` of the two ranges → only the two `by_cases` predicates differ. `sum_disjoint_factor` (used once, Sep:569) is `sum_inter_eq_factor` (Sep:187) at `G = ∅` with `f·1_P` and `g·1_Q`, up to merging the filters.
- Candidate: 14 lines repeated, and the first lemma is a corollary of the second.

26. D — Cor:101–108 (`hNM` inside `shell_facts`) vs Cor:522–532 (`N_le_M_of_K_le`)
- `have h1 : CK * N ^ 2 * (M * N) ^ ε ≤ M ^ 2 := by` … vs `have h1 : CK * N ^ 2 * Q ^ ε ≤ M ^ 2 := by` …
- Checked: `diff` of the two ranges → the same proof with `Q := M * N`. `shell_facts` has `hQ1 : 1 ≤ M * N` (Cor:97) in context, so `N_le_M_of_K_le hM hN hQ1 hε hcK1 hKM` closes `hNM`.
- Candidate: the lemma's proof is copied into an earlier `have` in the same file.

27. D — Errors:449–464 (`norm_u3_le`) vs Errors:506–519 (`hub` inside `err3T_mellin`)
- `theorem norm_u3_le … : ‖u3 ε T t B‖ ≤ (Real.sqrt (nI B))⁻¹ * ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε) := by`
- `have hub : ∀ B t, ‖u3 ε T t B‖ ≤ (Real.sqrt (nI B))⁻¹ * (Real.sqrt (nI B))⁻¹ ^ ε * ∏ Q ∈ B, …`
- Checked: `diff` → both run the same `unfold u3` / `rw [norm_mul, norm_mul, norm_mul, norm_cpow_sM hB, …]` / `norm_q2_le` / `norm_eulS_le` / `gcongr` sequence; `norm_u3_le` adds a `Real.rpow_le_one` step.
- Candidate: `norm_u3_le` re-proves the sharper `hub`. One lemma for `hub` would give `norm_u3_le` in one step.

28. D — GcdPart:237–246 vs 247–256 (`e3`/`e4` in `bilin_pairX`)
- Checked: `diff` → the two statements differ only in the column factor, `((Real.sqrt (nI B))⁻¹ * ∏ …) ^ 2` vs `(∏ …) ^ 2`. Both proofs are `have := hsq (…) (fun B => by positivity)` / `simp only [mul_assoc] at this ⊢` / `exact this`.
- Candidate: two 10-line restatements of `hsq` (GcdPart:227). A `hsq` stated in the `c B * (x * ‖a B‖ ^ 2)` shape would remove both.

29. D — Cor:585–599 vs Recursion:282–289 and 351–364
- `have hexL : ∃ L : ℕ, N < 2 ^ L := pow_unbounded_of_one_lt N (by norm_num)` … `have h2 := nat_le_rpow_of_two_pow_le hδ h1`
- `have hex : ∃ J : ℕ, Y₂ ≤ 2 ^ J * Y₁ := by` … `have h3 := nat_le_rpow_of_two_pow_le hδ h2`
- Checked: read both. Each takes `Nat.find`, splits on `Nat.eq_zero_or_pos`, applies `Nat.find_min` at `L − 1`, then `nat_le_rpow_of_two_pow_le` and `Nat.cast_sub`.
- Candidate: the same argument, "the least L with x < 2^L is at most 1 + x^δ/(δ log 2)", is written twice. The side conditions differ (strict vs non-strict), so it is not renaming-only.

30. D — the rotation argument, four copies of 5–8 lines each:
- Lattice:270–277 `fourier_radS_rot` and Lattice:279–284 `fourier_radS_eq`;
- PlaneMajorant.lean:201–205 `fourier_eta_rot` and 212–218 `fourier_Phi_rot`;
- EisensteinPoissonExcl.lean:161–166 `fourier_Phi_eq_dualG`;
- Lemma14:285–289 `Phi_eq_norm`.
- Checked: `rg -n "norm_mul_exp_arg_mul_I|fourier_comp_linearIsometry" src` → Lattice:275, 282; PlaneMajorant:203, 216; PoissonExcl:163; Lemma14:287 (plus unrelated uses at PlaneGaussian:206, 248 and WeilConverse:501).
- Candidate: "f rotation-invariant ⇒ 𝓕f rotation-invariant" and "a rotation-invariant f satisfies f w = f ‖w‖" are re-proved for each function; two generic lemmas would replace the four copies.

31. D (near-generated) — the indicator weights `admW` (Sep:1087) and `sqfW` (Squares:215) carry three lemma pairs with identical proofs:
- Sep:1089 `admW_nonneg` / Squares:218 `sqfW_nonneg`, both `unfold …; split_ifs <;> norm_num`;
- Sep:1092 `summable_admW` / Errors:203 `summable_sqfW`;
- Cor:417 `theorem admW_mono {Y Y' : ℝ} (h : Y ≤ Y') (m : 𝓞 K) : admW Y m ≤ admW Y' m := by` / Recursion:241 `theorem sqfW_mono {Y Y' : ℝ} (h : Y ≤ Y') (d : 𝓞 K) : sqfW Y d ≤ sqfW Y' d := by`.
- Checked: three `diff`s → only the names differ, plus one `rw [mem_eltsLe] at hm`.
- Candidate: a single indicator weight parameterised by the predicate would carry all six lemmas.

32. D — injectivity of `· \ G` on the supersets of `G` appears four times, and one construction is duplicated:
- Sep:79–84: `have hinj : Set.InjOn (· \ F) (𝒩F : Set (Finset Pr)) := by` (6 lines).
- Sep:666–671: the same with `(· \ D)`.
- GcdPart:74–80 and GcdPart:187–193: `have hinj : Set.InjOn (fun A => A \ G) (𝒩.filter (fun A => G ⊆ A) : Set (Finset Pr)) := by` (7 lines, verbatim twice).
- GcdPart:32–33, `def colG (𝒩 : Finset (Finset Pr)) (G : Finset Pr) : Finset (Finset Pr) :=` / `(𝒩.filter (fun A => G ⊆ A)).image (fun A => A \ G)`, is the family `FBound.sub` builds at Sep:85: `set 𝒩' := 𝒩F.image (· \ F) with h𝒩'`.
- Checked: `rg -n "Set.InjOn \(· \\\\|Set.InjOn \(fun A => A \\\\ G\)|image \(fun A => A \\\\ G\)|image \(· \\\\ F\)" src`; `diff` of GcdPart 74–80 vs 187–193 → identical.
- Candidate: each copy is under 8 lines, but the block recurs four times and `colG` duplicates `FBound.sub`'s family. One `injOn_sdiff` lemma, with `FBound.sub` stated through `colG`, would remove them.

(E) Efficiencies

33. E — GcdPart:296, Cor:254, Cor:534: `set_option maxHeartbeats 800000 in`, on `gcdPart_bw_le`, `gcdPart_shell_le` and `fBound_bw_le`.
- Checked:
  - `rg -n "set_option" src/EisensteinQuadSieve*.lean` → these three only; no `maxRecDepth`.
  - README.md:11935: "`gcdPart_bw_le` raises `maxHeartbeats` to 800000, as ten other files of `src/` already do for their theorems."
  - README.md:12021: "`gcdPart_shell_le` and `fBound_bw_le` raise `maxHeartbeats` to 800000."
  - Neither README entry gives a cause.
  - `git log --oneline -S "maxHeartbeats 800000"` on the two files → d55d17c (round 358) and 53e8bd8 (round 356), which are the files' only commits, so each override has been there since the first version.
  - No profile exists in the repository (review/stack3/ holds only Door*.lean, OleanDeps.lean and census.py).
- Likely cost centres, by reading only:
  - `gcdPart_bw_le`: `nlinarith` in a large context (GcdPart:344); `ring` over nested sums (363–365, 454); `linarith` after the large `set T` abbreviation (376–383, 390, 459); 8 `positivity` calls.
  - `gcdPart_shell_le`: 21 `positivity` calls on rpow/sqrt/max terms (e.g. 272–290, 331–345, 377–381); the 31-argument `bracket_le` application (382–384); the ~20-atom `ring` identity `hbr` (385–400).
  - `fBound_bw_le`: `nlinarith` at 570, 599, 641, 652 and 672 in a large context; 22 `positivity` calls; `field_simp` at 548 and 580.
- Candidate: the three overrides are unexplained in the record and unprofiled. The calls above are where to look; I did not verify this, since the brief excludes building.

(F) Mismatches

34. F — Lemma14:20–22 (module header)
- Text: "The form used for the main terms is `integral_dualG_sq`, `∫_ℂ G(a|z|²) dz = (π/a)∫_0^∞ Φ` for `a > 0`, with `integral_radial_sq` for `∫_ℂ Φ(b|z|²) dz`."
- Checked: item 19's grep (no use). The main terms use `integral_dualR_Ioi` (Sigma3:39–41, 271) and `dualP_zero` (Lattice:300, via `integral_radial_sq`).
- Candidate: the header calls "used" a theorem that nothing uses.

35. F — Gamma:200
- Docstring: "/-- **`φ` in coordinates** (round 344's `quad_gauss_coords`):"
- The same file's header, Gamma:18–19, says "(`gq4_coords`, from round 297's `quad_gauss_coords`)". The lemma is at EisensteinQuadGauss.lean:749, in a module headed "/-! # Quadratic Gauss sums over `ℤ[ω]` (round 297)".
- Checked: `rg -n "theorem quad_gauss_coords" src` → that line only.
- Candidate: the docstring gives the wrong round.

36. F — Base:127–128 (docstring of `gaussTr_q2_eq`, Base:129)
- Docstring: "/-- **The Gauss sum bound**: `|G_c(ρ_D, μ)| ≤ |σc|` for `c = ∏_{P∈D} π_P`, with `G_c(ρ_D, 0) = 0` for nonempty `D`. -/"
- Statement: `gaussTr (∏ P ∈ D, πP P) (q2 D) μ = (∏ P ∈ D, (quadR (𝓞 K ⧸ span {πP P}) ℂ)⁻¹ (Ideal.Quotient.mk (span {πP P}) μ)) * (((‖σO (∏ P ∈ D, πP P)‖ : ℝ) : ℂ) * gamF πP D (fun P => quadR (𝓞 K ⧸ span {πP P}) ℂ))`
- Candidate: the docstring states the bound and the zero value, which are `norm_gaussTr_q2_le` (Base:139) and `gaussTr_q2_zero` (Base:157), neither of which has a docstring. The theorem it sits on is the exact evaluation.

37. F — Base:236–237 (docstring of `norm_pS_term_le`, Base:238)
- Docstring: "the `T`-term of Poisson summation for the pair sum is at most `2H/(√3·N(c)·N(d_T))·|G_c(ρ_D, 0)|·B + 49·R_Φ²·B·√N(c)`"
- Statement's bound (Base:246): `2 * H * ‖gaussTr (∏ P ∈ D, πP P) (q2 D) 0‖ * B + 49 * RΦ ^ 2 * B * Real.sqrt (nI D)`. The proof drops the factor at Base:264, `have hk : 2 * H / (Real.sqrt 3 * nI D * nI T) ≤ 2 * H := by`.
- Candidate: the docstring claims a first term smaller by √3·N(c)·N(d_T) than the theorem proves.

38. F — Sep:591–592
- Docstring and statement: "/-- `2^{⌈log₂ n⌉}` lies in `[n, 2n)` for `n ≥ 1`. -/" / `theorem pow_clog_lt_two_mul {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n < 2 * n := by`
- Candidate: the theorem proves only the upper end. The lower end, `n ≤ 2^{clog}`, is Mathlib's `Nat.le_pow_clog`, applied separately at Sep:849.

39. F — Final:7–8 (module header)
- Text: "The zero-free half-plane `Re s > 11/12` then rests on the displayed theta transformation alone."
- Other: KubotaThetaProof.lean:57 `theorem thetaRows : ThetaRows := thetaRows_of_kubota kubotaTheta` and KubotaThetaProof:105 `theorem ne_zero_of_re_gt_eleven_twelfths {s : ℂ} (hs : 11 / 12 < s.re) :`.
- Candidate: a round-359 status sentence that later rounds superseded (the display is now proved), with no net-state marker.

SPECIAL-ATTENTION ANSWERS

(1) Where the proved sieve is used, and other sockets.

`quadLargeSieve` (Final:149, `theorem quadLargeSieve : QuadLargeSieve := quadLargeSieve_of_exp qExp_one`) has three consumers, all on half-plane chains:
- Final:155, `ne_zero_of_theta hθ quadLargeSieve hs`. This feeds KubotaRows:528 `ne_zero_of_thetaRows (thetaRows_of_kubota hK) hs`, which feeds KubotaThetaProof:107 `ne_zero_of_kubotaTheta kubotaTheta hs`.
- KubotaThetaProof:61, `squarefreeCompleted_of thetaRows quadLargeSieve`.
- KubotaThetaProof:83, `squarefreeCompletedM_of thetaRowsM quadLargeSieve`. This feeds `meanSquareNu` (KubotaThetaProof:98), which feeds DirichletCharHalfPlane:199.

Commands and results:
- `rg -n "QuadLargeSieve|quadLargeSieve" src external` → the display at EisensteinPrepared:206, and `(hLS : QuadLargeSieve)` hypotheses at EisensteinPrepared:340, 460, 535, 954, EisensteinThetaMeanSquare:344 and EisensteinThetaAssembly:287, 507, 689, 695. All are discharged through the three instantiations above.
- The stronger ball form (`qExp_one`, `QExp`, `QBound`, `FBound`, `fBound_cor`, `fBound_improve`) has no use outside the 16 files. `rg … --glob '!src/EisensteinQuadSieve*'` on those names finds only `QAdm` (KubotaRows:134, 206, 390, 440; QuadSupplement:93) and `sym2_recip_adm` (QuadSupplement:171).

No other socket found:
- `rg -n "^(noncomputable )?def .*: Prop" src external | rg -i "sieve|moment|mean|square|sixth|cubic|character|large|bilin|dual|sum"` lists no large-sieve display other than `QuadLargeSieve`.
- The moment displays it lists are the mean squares already proved through this sieve: `MeanSquare`, `MeanSquareC`, `DualMeanSquareM`, `CompletedMeanSquareM` and `SquarefreeCompletedM`. `WeightedBound` is reached from `MeanSquare` (HalfPlaneMeanSquare:618).
- `rg -n -i "sixth|SixthMoment" --glob '*.lean'` finds no sixth-moment display.
- The register's sixth-moment items for rounds 497 and 506–508 (STRUCTURAL-REVIEW.md:248, 260, 263–264) are attack notes with no Lean display. The cubic and higher-order large sieves on the machinery checklist have no display either.

(2) Heartbeat overrides: see item 33.

(3) Lattice-point and Poisson duplicates: items 4, 5, 6, 15, 17 and 30, plus items 7 and 9 for Mathlib. Checked and not duplicated:
- `latS_poisson` instantiates `poisson_excl` at `c = 1`, `S = ∅` (Lattice:319). `eis_poisson'` (EisensteinPoisson:266) is indexed by ℤ², not μ.
- `fourier_zero_eq` (Lattice:287) has no copy in Mathlib or the stack (`rg "fourierIntegral_zero|𝓕 … 0 = ∫"`).
- `cpow_prod_ofReal` (Lattice:551) has none either (`rg "cpow_prod|prod_cpow"` in ML and src).
- `card_eltsLe_le` (EisensteinCubeReduction:102) is reused, not copied.
- LatticeCount.lean counts ℤⁿ ball points through `ZLattice` and shares nothing with these files.
- ThermalZeta.lean:263 `integral_radial` is the real-valued polar formula on ℝ^d, not Lemma14's ℂ-valued ones.