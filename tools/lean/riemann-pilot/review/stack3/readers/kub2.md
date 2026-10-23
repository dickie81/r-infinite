<!-- Stack review 3 reader report: model output, a list of CANDIDATES, not findings. STRUCTURAL-REVIEW.md §9.2 and §9.7 record what the lead verified (Check 3). Scratchpad paths below are the reader's session files, not committed. -->

Coverage (each file read end to end with Read; paths relative to tools/lean/riemann-pilot)
- src/KubotaEnergy.lean: lines 1–301 read
- src/KubotaExpansion.lean: lines 1–398 read
- src/KubotaGHolo.lean: lines 1–746 read
- src/KubotaGroups.lean: lines 1–232 read
- src/KubotaGrowth.lean: lines 1–519 read
- src/KubotaLamCube.lean: lines 1–571 read
- src/KubotaLocTable.lean: lines 1–332 read
- src/KubotaLocalFactors.lean: lines 1–610 read
- src/KubotaMeasure.lean: lines 1–417 read
- src/KubotaMellin.lean: lines 1–780 read
- src/KubotaMultiplier.lean: lines 1–262 read
- src/KubotaPhi.lean: lines 1–549 read
- src/KubotaPhiPole.lean: lines 1–154 read
- src/KubotaPhiSeries.lean: lines 1–389 read
- src/KubotaPmPair.lean: lines 1–732 read
- src/KubotaPmTheta.lean: lines 1–557 read
- src/KubotaPoincare.lean: lines 1–351 read
- src/KubotaResidue.lean: lines 1–286 read
- src/KubotaRows.lean: lines 1–551 read

STRUCTURAL-REVIEW.md §9 (lines 322–405) read first; none of the items below is listed there. Import direction ("X imports Y") was checked with a scratch closure script over the `import` lines (scratchpad/sr3reader/deps.py). Usage counts come from `grep -rn -w NAME src external`, excluding `#print axioms` lines, and from a comment-stripped token scan (scratchpad/sr3reader/dead2.py).

=== (A) Doors and special cases ===

1. (A) KubotaMellin.lean:694–696
`theorem twisted_theta_mellin {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}`
`(hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (φ₀ : 𝓞 K → ℂ) ...`
Discharger: KubotaCusps.lean:94 `theorem kubotaData_of (hK : KubotaTheta) : ∃ (θ ...) ..., KubotaData θ Kc c₀ cP cM τ tP tM`, with KubotaThetaProof.lean:46 `theorem kubotaTheta : KubotaTheta`.
Checks: `grep -rn -w twisted_theta_mellin src external` gives only its own file. The dead-code token scan gives code-uses=0 (it is a headline). `grep -rn kubotaData_of src` gives only KubotaCusps:94.
Candidate: the S5f-4c result (𝒥(s) is entire and has its functional equation) is still conditional on `KubotaData`. Since round 466 it can be stated unconditionally for the proved θ, and no file does so.

2. (A) KubotaPhiSeries.lean:37–38
`theorem three_mem_iff_dvd_absNorm {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :`
`    (3 : 𝓞 K) ∈ P ↔ 3 ∣ absNorm P := by`
Checks: the proof uses only `Nat.prime_three` and `absNorm_natCast_span_sq` (EisensteinCount:161, stated for every `a : ℕ`). `grep -rnE "∈ P ↔ .* ∣ absNorm|mem_iff_dvd_absNorm"` over src and external/pnt has no other hit.
Candidate: stated for p = 3, but the same proof gives "p ∈ P ↔ p ∣ N(P)" for every rational prime p.

3. (A) KubotaLocalFactors.lean:68
`theorem chiR_pow_ne_one (P : Pr) {j : ℕ} (hj : j % 6 ≠ 0) : chiR P ^ j ≠ 1 := by`
Other location: EisensteinGaussPrime.lean:137 `theorem chi6_pow_ne_one (P : Ideal (𝓞 K)) [P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P) {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) : chi6 P hP6 ^ j ≠ 1`.
Checks: the proof calls only `chi6_pow_six` and `chi6_pow_ne_one` at `(span {πP P}) (h6Pr P)`.
Candidate: the j % 6 ≠ 0 form is proved only for `chiR P`, but the proof works for every `chi6 P hP6`, and it would extend `chi6_pow_ne_one`.

4. (A) KubotaResidue.lean:64–65
`theorem deriv_hhat_im {r : ℝ} (hr : 0 < r) (σ : ℝ) :`
`    (deriv (hhat (2 * Real.cosh r - 2)) σ).im = 0 := by`
Check: lines 66–75 use only differentiability and `(hhat_real_pos hr y).1` (the imaginary part vanishes on ℝ). `grep -rn real_of_complex src` gives only this file.
Candidate: a general lemma ("f differentiable and real on ℝ ⇒ f′(σ) real") is proved here for `hhat` only.

5. (A) KubotaPmPair.lean:314 `theorem zpow_neg_three_le {α v : ℝ} (hα : 0 < α) (hv : α ≤ v) : v ^ (-3 : ℤ) ≤ α ^ (-3 : ℤ) := by`, and KubotaPmTheta.lean:46 `theorem zpow_neg_two_le {α v : ℝ} (hα : 0 < α) (hv : α ≤ v) : v ^ (-2 : ℤ) ≤ α ^ (-2 : ℤ) := by`.
Checks: `grep -rnE "theorem zpow_neg_[a-z]+_le" src` gives exactly these two. Their bodies are identical apart from the exponent. No Mathlib lemma for negative exponents was found (`grep "lemma zpow_le_zpow" Mathlib/Algebra/Order`).
Candidate: one lemma for every n replaces both constant-specific copies.

6. (A) KubotaLamCube.lean:37 `theorem lam_ne_zero : (ω - 1 : 𝓞 K) ≠ 0 := by`
Inline re-proofs in files that import KubotaLamCube (deps.py: True for each):
- KubotaCuspSeries.lean:354 `have hl0 : (ω - 1 : 𝓞 K) ≠ 0 := fun h => by`, the same proof text;
- KubotaCuspIdent.lean:442 and KubotaCuspTheta.lean:255 `have hl0 : (ω - 1 : 𝓞 K) ≠ 0 := fun h => by` (via `normSq_σO_lam`).
Within KubotaLamCube itself, lines 88–93 (`have h3 : (3 : 𝓞 K) ≠ 0 := by` … `have hM : (3 : 𝓞 K) * c ≠ 0 := mul_ne_zero h3 hc0`) and lines 211–216 (`have h3c : (3 : 𝓞 K) * c ≠ 0 := by`) re-prove KubotaConstTerm.lean:341 `theorem three_mul_ne_zero {c : 𝓞 K} (hc : c ≠ 0) : (3 : 𝓞 K) * c ≠ 0`. KubotaLamCube imports KubotaConstTerm.
Checks: `grep -rnF "ω - 1 : 𝓞 K) ≠ 0" src external` gives 9 hits, and `grep -rnF "(3 : 𝓞 K) ≠ 0" src` gives 9 inline hits.
Candidate: existing named lemmas are re-proved inline where they are already in scope.

7. (A) KubotaEnergy.lean:90 `theorem isOpen_UHS : IsOpen UHS := isOpen_lt continuous_const continuous_snd`
The same term is written inline as `have hU : IsOpen UHS := isOpen_lt continuous_const continuous_snd` at KubotaThetaEq.lean:275, KubotaCubeEigen.lean:405 and KubotaThetaInv.lean:366. All three import KubotaEnergy transitively.
Check: `grep -rnE "IsOpen UHS|isOpen_lt continuous_const continuous_snd" src`.
Candidate: the named lemma is available but not used (one-liner).

8. (A, minor) KubotaLamCube.lean:435–437
`theorem norm_le_of_lam_rec {ρ : ℕ → ℂ}`
`    (h : ∀ j, 3 ≤ j → ρ (j + 6) = ((4 / Real.sqrt 3 : ℝ) : ℂ) * ρ (j + 3) - ρ j) :`
`    ∃ A : ℝ, 0 ≤ A ∧ ∀ j : ℕ, ‖ρ j‖ ≤ A * (3 : ℝ) ^ ((j : ℝ) / 6) := by`
Candidate: the proof splits the recurrence with roots q, q⁻¹ for q = √3 (lines 438–464). It is stated for one constant, and the same argument applies for every q ≥ 1.

=== (B) Duplicates ===

9. (B, more general exists downstream) KubotaGrowth.lean:449–451
`theorem norm_eis1_slAct_sub_le {s : ℂ} (hs : 2 < s.re) (g : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hv : 1 / 2 ≤ p.2) :`
`    ‖eis1 s (slAct g p) - cuspA g * ((p.2 : ℝ) : ℂ) ^ s‖ ≤ cuspC s.re * p.2 ^ (2 - s.re) := by`
Other location: KubotaEisTrunc.lean:224–226 `theorem norm_pseis_slAct_sub_le ... (hf : ∀ v, 0 < v → ‖f v‖ ≤ C * v ^ τ) (g ...) {p} (hv : 1 / 2 ≤ p.2) : ‖pseis f (slAct g p) - cuspA g * f p.2‖ ≤ C * (cuspC τ * p.2 ^ (2 - τ))`, together with KubotaEisTrunc.lean:97 `theorem eis1_eq_pseis (s : ℂ) : eis1 s = pseis (fun v => ((v : ℝ) : ℂ) ^ s) := rfl`.
Checks: the token scan gives code-uses=0 for `norm_eis1_slAct_sub_le`. `diff <(sed -n '468,491p' KubotaGrowth) <(sed -n '230,266p' KubotaEisTrunc)` shows the hN/h1/h2/hsplit/final `tsum_of_norm_bounded` skeleton shared. `eisTerm_slAct_of_fst` (Growth:434, body 439–444) and `height_slAct_of_fst` (EisTrunc:210, body 211–218) share the same 7 lines.
Candidate: the Growth theorem is the f = v^s, C = 1, τ = Re s instance of the EisTrunc one; the proof was copied, and the Growth theorem has no users.

10. (B, more general downstream) KubotaPhi.lean:203 `theorem summable_phiTerm {s : ℂ} (hs : 2 < s.re) : Summable (phiTerm s) := by` and :268 `theorem LSeries_normA {s : ℂ} (hs : 2 < s.re) : LSeries normA s = ∑' c, phiTerm s c := by`, with `tsum_fiber_phiTerm` at :250 and `def normA (n : ℕ) : ℂ := ∑ c ∈ eltsN n, cuspS c` at :239.
Other location: KubotaCuspZeroPhi.lean:216 `theorem summable_mul_normSq_cpow {f : 𝓞 K → ℂ} (hf : ∀ c, ‖f c‖ ≤ absNorm (span {c})) {s : ℂ} (hs : 2 < s.re) : Summable fun c => f c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)` (docstring: "as round 416's `summable_phiTerm`"); :250 `def eltSum (f : 𝓞 K → ℂ) (n : ℕ) : ℂ := ∑ c ∈ eltsN n, f c`; :254 `theorem LSeries_eltSum` (docstring: "as round 416's `LSeries_normA`").
Checks: the bodies (Phi 204–234 against CuspZeroPhi 218–248, and Phi 252–273 against CuspZeroPhi 256–275) are line-for-line copies with f in place of cuspS.
Candidate: KubotaPhi's results are instances (normA = eltSum cuspS by definition). The general lemma's `hf` is used only for c ≠ 0; the c = 0 branch does not use it. Weakening `hf` to c ≠ 0 would let it cover `norm_cuspS_le`, which requires c ≠ 0.

11. (B, more general downstream) KubotaPhi.lean:475 `theorem one_sub_three_cpow_ne_zero {w : ℂ} (hw : 0 < w.re) : 1 - (3 : ℂ) ^ (-w) ≠ 0 := by`
Other location: RealCharHalfPlane.lean:338–339 `theorem one_sub_mul_cpow_ne_zero {p : ℕ} (hp : p.Prime) {a : ℂ} (ha : ‖a‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) : 1 - a * (p : ℂ) ^ (-s) ≠ 0`. RealCharHalfPlane imports KubotaPhi.
Check: `grep -rnE "one_sub_.*cpow_ne_zero" src external`.
Candidate: the KubotaPhi lemma is the case p = 3, a = 1 of the later lemma.

12. (B, Mathlib) KubotaPhi.lean:99 `theorem span_unit_mul (u : (𝓞 K)ˣ) (x : 𝓞 K) : span {(u : 𝓞 K) * x} = span {x} := by`
Mathlib/RingTheory/Ideal/Span.lean:100 `theorem span_singleton_mul_left_unit {a : α} (h2 : IsUnit a) (x : α) : span ({a * x} : Set α) = span {x}`. It is already used as `Ideal.span_singleton_mul_left_unit u.isUnit` at EisensteinCubicRecip.lean:312 and EisensteinRowTwist.lean:189.
Candidate: identical statement up to `u.isUnit`.

13. (B, Mathlib) KubotaPhi.lean:400 `theorem cpow_ne_zero_of_ne {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y ≠ 0 := by`
Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean:51 `theorem cpow_ne_zero_iff {x y : ℂ} : x ^ y ≠ 0 ↔ x ≠ 0 ∨ y = 0`.
Candidate: equal to `Complex.cpow_ne_zero_iff.2 (Or.inl hx)`. It is used at KubotaPhi and KubotaCuspZeroPhi:444/497/508/521.

14. (B, Mathlib) KubotaLocalFactors.lean:289 `theorem mul_mem_iff_right (P : Pr) {e x : 𝓞 K} (he : e ∉ P.1) : e * x ∈ P.1 ↔ x ∈ P.1 :=`
Mathlib/RingTheory/Ideal/Prime.lean:105 `lemma IsPrime.mul_mem_left_iff {I : Ideal α} [I.IsTwoSided] [I.IsPrime] {x y : α} (hx : x ∉ I) : x * y ∈ I ↔ y ∈ I`.
Candidate: identical, given the `IsPrime` instance for `P.1`.

15. (B, Mathlib) KubotaLocalFactors.lean:244–245 `theorem mulChar_inv {F : Type*} [Field F] (χ : MulChar F ℂ) {h : F} (hh : h ≠ 0) : χ h⁻¹ = (χ h)⁻¹ := by`
Mathlib/NumberTheory/MulChar/Basic.lean:324 `theorem inv_apply' ... : χ⁻¹ a = χ a⁻¹` and :302 `theorem inv_apply_eq_inv' ... : χ⁻¹ a = (χ a)⁻¹`.
Candidate: the result is `(inv_apply' χ h).symm.trans (inv_apply_eq_inv' χ h)`, which needs no `h ≠ 0`.

16. (B, Mathlib) KubotaLocalFactors.lean:258 `theorem pow_eq_pow_of_six {u : ℂ} (hu : u ^ 6 = 1) {a b : ℕ} (hab : a % 6 = b % 6) : u ^ a = u ^ b := by`, and :65 `theorem chiR_pow_mod (P : Pr) (j : ℕ) : chiR P ^ j = chiR P ^ (j % 6) := by`
Mathlib/Algebra/Group/Basic.lean:169 `lemma pow_eq_pow_mod (m : ℕ) (ha : a ^ n = 1) : a ^ m = a ^ (m % n)`.
Candidate: both are one-line consequences of Mathlib's more general lemma.

17. (B, Mathlib) KubotaLocalFactors.lean:471 `theorem isCoprime_πP_iff (P : Pr) (x : 𝓞 K) : IsCoprime x (πP P) ↔ x ∉ P.1 := by` (a 10-line ideal-sup proof)
Mathlib/RingTheory/PrincipalIdealDomain.lean:440 `theorem Irreducible.coprime_iff_not_dvd {p n : R} (hp : Irreducible p) : IsCoprime p n ↔ ¬p ∣ n` (IsBezout section). One direction is re-stated at KubotaCubeSum.lean:191 `theorem isCoprime_of_not_dvd`.
Candidate: equal to the Mathlib lemma composed with `(πP_spec P).2` and `Ideal.mem_span_singleton`.

18. (B, Mathlib) KubotaLocTable.lean:144–145
`theorem gaussP_three {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {h : 𝓞 K} (hph : ¬ p ∣ h) {j : ℕ}`
`    (hj : 0 < j) (h3 : 3 ∣ j) : gaussP h p j = -1 := by` (40 lines)
Mathlib/NumberTheory/GaussSum.lean:126 `theorem gaussSum_one_left {ψ : AddChar R R'} (hψ : ψ ≠ 1) : gaussSum (1 : MulChar R R') ψ = -1`. The bridge already exists inline at KubotaDirSplit.lean:246 `have hg : ∀ j, 0 < j → gaussP h p j = gaussSum (χ ^ j) ψ`, with EisensteinGaussSum.lean:122 `orderOf_cubCharC` giving χ^j = 1 for 3 ∣ j.
Candidate: the trivial-character Gauss sum is re-derived by hand instead of taken from Mathlib.

19. (B, more general here) KubotaLocTable.lean:31 `theorem tsum_quot_affine' {N u : 𝓞 K} (hN : N ≠ 0) (hu : IsCoprime u N) ...`, :56 `theorem tsum_quot_eq_zero_of_mul {N g : 𝓞 K} ...`, :80 `theorem tsum_quot_dvd_fiber ...`
Other locations (modulus p³ only, upstream): KubotaCubeSum.lean:228 `theorem tsum_quot_affine {p u : 𝓞 K} (hp : p ≠ 0) (hu : IsCoprime u p) {F} (hF : ∀ y y', p ^ 3 ∣ y - y' → F y = F y') (a : 𝓞 K)`; :390 `theorem tsum_eq_zero_of_twist`; :260 `theorem tsum_quot_dvd`.
Checks: the bodies of 228↔31 and 390↔56 are textually identical with p ^ 3 ↦ N. `tsum_quot_dvd` is `tsum_quot_dvd_fiber` at M = p, N = p³, F = [p ∣ ·]. `grep -rnP "tsum_quot_affine(?!')"` shows uses at KubotaCubeSum:393 and :622 only.
Candidate: the p³ versions are instances of the round-452 lemmas.

20. (B, more general here) KubotaPmPair.lean:322 `theorem uhsMeasure_fundP3_Icc_lt_top_of_pos {α β : ℝ} (hα : 0 < α) : uhsMeasure (fundP3 ×ˢ Icc α β) < ⊤`, :364 `integral_fundP3_conj_mul` (any F bounded on 3P × [α, β]), :443 `lintegral_rhoT3_pm_ne_top`
Other locations (upstream; PmPair imports ThetaPair): KubotaThetaPair.lean:151 `theorem uhsMeasure_fundP3_Icc_lt_top {α β : ℝ} (hα : 1 ≤ α) : uhsMeasure (fundP3 ×ˢ Icc α β) < ⊤`; :170 `integral_conj_eisLow` (its steps 1–4); :269 `lintegral_rhoT3_eisLow_ne_top`.
Check: `diff <(sed -n '207,225p' KubotaThetaPair) <(sed -n '378,397p' KubotaPmPair)` shows the `hstep1` body identical (19 lines). The `hint`/`hslice`/Fubini blocks match the same way, and the two finiteness calcs match.
Candidate: the round-430 generic lemmas subsume the round-427 eisLow-specific proofs.

21. (B, more general here) KubotaGHolo.lean:49–53 `theorem lintegral_puLe_top_mul_le (Γ : Subgroup SL(2, 𝓞 K)) {F} (hF : Measurable F) {C : SL(2, 𝓞 K) → ℝ≥0∞} (hb : ∀ g, ∀ p ∈ siegelK, F (slAct g p) ≤ C g) : ∫⁻ p, puLe ⊤ Γ rhoK p * F p ∂uhsMeasure ≤ ∑' q ..., C (q.out : SL(2, 𝓞 K))⁻¹ * ∫⁻ p, rhoK p ∂uhsMeasure`
Other location: KubotaEisTrunc.lean:276–279 `theorem lintegral_puLe_top_mul_lt_top (Γ) [Finite (... ⧸ Γ.subgroupOf ⊤)] {F} (hF) (hb : ∀ g, ∃ C, C ≠ ⊤ ∧ ∀ p ∈ siegelK, F (slAct g p) ≤ C) : ∫⁻ ... < ⊤`.
Check: `diff <(sed -n '54,82p' KubotaGHolo) <(sed -n '281,310p' KubotaEisTrunc)` differs only in the constant and in the final finite-sum step.
Candidate: the `< ⊤` lemma follows from the quantitative one (a finite sum of finite terms); the 25-line `h1` block is written twice.

22. (B, small) KubotaPhi.lean:167 `theorem norm_one_sub_inv_natCast_le (n : ℕ) : ‖(1 : ℂ) - 1 / (n : ℂ)‖ ≤ 1 := by`
Other location: KubotaLocalFactors.lean:450–459 (`norm_locCoef_zero_le`) proves `‖1 − N(P)⁻¹‖ ≤ 1` inline, through `have e : (1 : ℂ) - (absNorm P.1 : ℂ)⁻¹ = ((1 - (absNorm P.1 : ℝ)⁻¹ : ℝ) : ℂ)` and the same abs/linarith steps.
Check: `grep -rnF "(1 : ℂ) - 1 / (" src`.
Candidate: the same fact is proved twice.

23. (B, minor, Mathlib) KubotaExpansion.lean:38 `theorem conj_ψc (c x : 𝓞 K) : conj (ψc c x) = ψc c (-x) := by`
Mathlib/Analysis/RCLike/Basic.lean:1285 `lemma map_neg_eq_conj [AddCommGroup G] (ψ : AddChar G K) (x : G) : ψ (-x) = conj (ψ x)`, applied to the stack's `ψQ c hc` (EisensteinGaussTransform:62) through `ψQ_mk`.
Candidate: an instance of a Mathlib lemma for c ≠ 0. The stack version also covers c = 0.

=== (C) Dead code ===

24. (C) KubotaGrowth.lean:410 `theorem cuspA_one : cuspA 1 = 1 := by`
Checks: `grep -n -w cuspA_one src/KubotaGrowth.lean` hits only line 21 (the module docstring, which lists it as a helper and says "`a_1 = 1`") and 410. The repo-wide token scan (comments stripped) gives code-uses=0.
Candidate: a helper with no use.

25. (C) KubotaRows.lean:507 `theorem isCoprime_four_of_coprime6 {k : 𝓞 K} (h : (absNorm (span {k})).Coprime 6) : IsCoprime k 4 := by`
Checks: the token scan gives code-uses=0. `grep -rnE "IsCoprime [a-z₀0-9]+ 4\b"` shows no consumer. `ThetaRows` is now `def ThetaRows : Prop := ThetaRowsM 4` (EisensteinThetaRows:192), so nothing needs it.
Candidate: no use. Its claim (module docstring lines 30–31) is not used by any proof.

=== (D) Patterns ===

26. (D) The SL₂(ℂ) T·E·D·T decomposition proof appears 3 times with only renamings:
- KubotaMeasure.lean:314–337 `uinv_actP`;
- KubotaEnergy.lean:211–234 `conf_actP`;
- KubotaBall.lean:102–131 `pinv_actP`.
Checks: `diff` of Energy 211–234 (after sed renaming conf→uinv, Conf→UInv) against Measure 314–337 prints IDENTICAL-after-renaming. `grep -rnF "!![1, g 0 0 / g 1 0; 0, 1] * !![0, -1; 1, 0]" src` hits Measure:325, Energy:222, Ball:116.
Also: KubotaEnergy:189–195 `actP_E_eq` repeats the computation of KubotaMeasure:285–291 inside `uinv_actP_E` (the diff differs only by `Function.comp_apply` in the simp list), and KubotaEnergy:185 `psiInv_mem` repeats KubotaMeasure:168–170's inline `hU`.
Candidate: an induction principle over det-1 matrices (predicate closed under `actP` products, true for translations, the diagonal and E) would replace all three.

27. (D) L²-holomorphy of s ↦ E(f_s): KubotaGHolo.lean:548–636 `hasDerivAt_gL` and KubotaPmPair.lean:151–231 `hasDerivAt_bandL`. The PmPair docstring says "by round 424's method".
Checks: `diff <(sed -n '560,636p' KubotaGHolo) <(sed -n '163,231p' KubotaPmPair)` matches the ε/h1/h2 block (16 lines) and the hpw/hsub/hae/hnorm/hfin/calc skeleton modulo names. `grep -rnF "set ε := min (1 / (L + 1)) (c / (K + 1))" src` hits exactly these two.
Candidate: a generic lemma (profiles vanishing below a, with a uniform Taylor bound ⇒ HasDerivAt into L²(ν)) would replace about 80 lines each.

28. (D) Bounding E(f) on the Siegel set at every cusp:
- KubotaGHolo.lean:128–145 (in `lintegral_pseis_sq_le`) and KubotaEisTrunc.lean:324–341 (in `memLp_pseis`): `hv`, `hp0`, `h := norm_pseis_slAct_sub_le …`, `h2`, then the `hb` calc through `norm_le_insert'`, `change ‖…‖ₑ ^ 2 ≤ _`, `rw [← ofReal_norm]`, `gcongr`. The diff differs only in the constants.
- The first 5 lines of KubotaPoincare.lean:229–234 (`memLp_pmSer`) repeat EisTrunc 319–323.
Candidate: a shared cusp-bound lemma.

29. (D) Tiling: KubotaGrowth.lean:81–102 `theorem lintegral_tile {G : ℂ → ℝ≥0∞} (hG : Measurable G) : ∫⁻ x, G x = ∑' t : 𝓞 K, ∫⁻ y in fundP, G (y + σO t)` and KubotaConstTerm.lean:119–145 `theorem lintegral_tile3 … : ∫⁻ x, G x = ∑' t : 𝓞 K, ∫⁻ y in fundP3, G (y + σO (3 * t))`.
Check: the same 20-line calc with fundP↔fundP3 and σO t↔σO (3 * t).
Candidate: one tiling lemma would serve both.

30. (D) Radial integral computed twice: KubotaGrowth.lean:105 `integral_Ioi_mul_rpow` and :145 `lintegral_normSq_add_rpow` (real exponent, lintegral), against KubotaConstTerm.lean:179 `integral_Ioi_mul_cpow` and :231 `integral_normSq_add_cpow` (complex exponent, Bochner).
Check: `grep -rn "polarCoord_symm" src` hits only Growth:149 and ConstTerm:240. The antiderivative, `hlim` and `polarCoord` blocks have the same shape.
Candidate: the cpow version contains the rpow one.

31. (D) The identity-theorem and residue argument on `domU r`: KubotaPmTheta.lean:357–427 (inside `inner_pmSer_thetaL_cross`) and KubotaCuspTheta.lean:141–208 (`residue_eq_of_eq_cpow`, whose docstring says "as in round 431's `inner_pmSer_thetaL_cross`").
Checks: `grep -rnF "set z0 : ℂ := 3 + I * (t : ℂ)"` hits these two. The `hγU` grep hits these two, and the `hγ` grep hits PmTheta:289/391 and CuspTheta:63/171.
Also: `aPm`/`differentiableOn_aPm`/`tendsto_aPm` (PmTheta:249/266/283) duplicate `aBand`/`differentiableOn_aBand`/`tendsto_aBand` (CuspTheta:45/50/59). By the definitions, aPm = aBand − I_m·M_ψ(2 − s), and the hγ/hI/hL/h3 blocks are verbatim.
Candidate: a generic residue lemma (F holomorphic on U and 0 on Re s > 2 ⇒ the residue limits agree) and one `A_y` would serve both files.

32. (D) Unfolding: KubotaPoincare.lean:294–318 (`integral_conj_pmSer_mul`) and KubotaUnfoldEis.lean:394–414 (`integral_conj_pseis_mul`).
Check: the diff differs only in Φ (the extra `ebr` factor) and the two `ebr_period` lines. `inner_toLp_pmSer` (Poincare:321) has the same shape as `inner_toLp_pseis` (UnfoldEis:417).
Candidate: the pseis case is the m = 0 case of the pmSer proof, which was copied.

33. (D) Bessel decay bounds: KubotaMellin.lean:136–167 (`dSer_le_exp`) and KubotaDerivative.lean:116–151 (`exists_thTerm_bound`) share the obtain/hK/hre/hx₀/hxx/hdecay/hexp/hd/e43/hKb block, with the constants changed. KubotaMellin.lean:310–317 (`continuousOn_dSer`) and KubotaDerivative.lean:167–178 (`summable_thDer`) share the `h2` and the 4-step calc to `|C| * A * (1 + ‖σO m‖) ^ (-3 : ℝ)`.
Check: the two diffs match.
Candidate: a lemma for the termwise majorant would serve both files.

34. (D) "bkK = O(t^{−b}) at 0⁺": named as KubotaPmTheta.lean:54 `theorem bkK_isBigO_bot {x : ℝ} (hx : 0 < x) (b : ℝ) : (fun t => bkK x t) =O[𝓝[>] 0] fun t : ℝ => t ^ (-b)`, but written inline at BesselK.lean:64–76 (`mellinConvergent_bkK`) and KubotaEisFourier.lean:228–240 (`differentiable_besselK`).
Checks: `diff <(sed -n '58,76p' BesselK) <(sed -n '222,240p' KubotaEisFourier)` differs only in the refine line. `grep -rn isLittleO_exp_neg_mul_rpow_atTop src` hits BesselK:64, EisFourier:228, PmTheta:57 and Mellin:493.
Candidate: the later named lemma belongs in BesselK, where both earlier copies could use it.

35. (D) The calc `‖σO c‖ ^ (-τ) = 2 ^ τ * (2 * ‖σO c‖) ^ (-τ) ≤ 2 ^ τ * (1 + ‖σO c‖) ^ (-τ)` (7 lines) appears at KubotaGrowth.lean:300–305, KubotaPhi.lean:228–234 and KubotaCuspZeroPhi.lean:241–247.
Check: `grep -rnF "2 ^ τ * (2 * ‖σO c‖) ^ (-τ)" src` gives 3 hits.
Candidate: a pointwise lemma.

36. (D, in-file repeats ≥ 8 lines)
- KubotaLocTable.lean:150–160 (`hsym` in `gaussP_three`) and :221–231 (`hsym` in `locG_low`): the diff differs only in renamings and the `if` form.
- KubotaLocalFactors.lean:366–377 and :399–410 (two branches of `local_transform`): the diff differs only in 2 ↔ j + 2.
- KubotaExpansion.lean:133–140 and :230–237 (the `he` block): `diff` prints IDENTICAL.
- KubotaResidue.lean:102–112 (`imK_le_deriv_hhat`) and :168–179 (`tendsto_uL_thetaL`): the same hev/hs/hb block at σ and at 4/3.

37. (D, short but frequent) The 3-line extraction `obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm` / `have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb` / `have h1 := one_le_norm_σO hm0` appears 7 times in KubotaMellin (136, 224, 295, 396, 409, 430, 453), twice in KubotaDerivative, once in KubotaStrip and once in KubotaTheta.
Check: `grep -rn "hq ▸ dualPt_ne_zero hn hb" src | uniq -c`.
Candidate: a lemma `ThetaSupp … → d m ≠ 0 → 1 ≤ ‖σO m‖`.

=== (E) Efficiencies ===
None found. `grep -n "set_option\|maxHeartbeats\|maxRecDepth\|native_decide"` over the 19 files has no hits. The only `decide` is KubotaPhi:45 (`ite_eq_right (by decide)`). `interval_cases` at LamCube:477, LocalFactors:74 and PhiSeries:267 is on small ranges.

=== (F) Mismatches ===

38. (F) KubotaEnergy.lean:7, docstring: "Round 360's S5f-10 plans Lax–Milgram for this energy form."
Other location: README.md:12133 (round-418 note): "the resolvent is replanned on `T_R` in place of the energy form".
Check: a grep of every KubotaEnergy declaration name outside the file returns nothing. KubotaSiegel imports KubotaEnergy but uses none of it.
Candidate: the stated purpose was superseded, and the whole file (headlines `edens_actP`, `lintegral_energy_actP`, `edens_automorphic`) has no consumer.

39. (F) KubotaRows.lean:21–23, module docstring: "**The assembly** (**`thetaRows_of_data`**, …; **`thetaRows_of_kubota`**): `KubotaTheta → ThetaRows`, with `J = 16`, `M = 9·72`, and the residues modulo `72` as the indices `i`."
Lean:
- line 407: `thetaRows_of_data … : ThetaRowsM md`, with the witness `refine ⟨Cw, 9 * (72 * md), KH, …⟩` at line 423 and `KH` the residues mod `72 * md`;
- line 522: `theorem thetaRows_of_kubota (hK : KubotaTheta) : ThetaRows := thetaRowsM_of_kubota (md := 4) hK`;
- EisensteinThetaRows.lean:192: `def ThetaRows : Prop := ThetaRowsM 4`.
Candidate: after round 493 the witness for ThetaRows is M = 9·288 with residues mod 288. The bullet is stale and contradicts the round-493 paragraph at lines 27–31 of the same header.

=== Outside the assigned files (seen while checking; not read end to end) ===

40. (D) EisensteinPrepared.lean:160 `three_not_mem_of_factor` and HalfPlaneMeanSquare.lean:40 `six_not_mem_of_factor` have the same 13-line proof with 3/9 ↔ 6/36. KubotaPhiSeries:61 `not_three_dvd_absNorm_of_factor` wraps the first.

41. (D) KubotaCuspSums.lean:561–589 (in `count_primary_mem`, :536) and KubotaCuspZeroPhi.lean:94–122 (in `count_three_mem`, :79): the `card_fiber_mul` counting block is identical except for the class (`e` vs `0`) and the filter predicate.
