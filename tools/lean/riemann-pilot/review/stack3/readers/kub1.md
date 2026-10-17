<!-- Stack review 3 reader report: model output, a list of CANDIDATES, not findings. STRUCTURAL-REVIEW.md §9.2 and §9.7 record what the lead verified (Check 3). Scratchpad paths below are the reader's session files, not committed. -->

Coverage (each file read end to end with Read, in chunks):
File: src/KubotaCuspCoef.lean: lines 1–764 read
File: src/KubotaCuspData.lean: lines 1–660 read
File: src/KubotaCuspIdent.lean: lines 1–493 read
File: src/KubotaCuspPoincare.lean: lines 1–413 read
File: src/KubotaCuspSeries.lean: lines 1–452 read
File: src/KubotaCuspSums.lean: lines 1–775 read
File: src/KubotaCuspTheta.lean: lines 1–550 read
File: src/KubotaCuspTrans.lean: lines 1–474 read
File: src/KubotaCuspZero.lean: lines 1–402 read
File: src/KubotaCuspZeroPhi.lean: lines 1–559 read
File: src/KubotaCusps.lean: lines 1–476 read
File: src/KubotaDerivative.lean: lines 1–646 read
File: src/KubotaDirSplit.lean: lines 1–364 read
File: src/KubotaEisFourier.lean: lines 1–491 read
File: src/KubotaEisTrunc.lean: lines 1–784 read
File: src/KubotaEisenstein.lean: lines 1–489 read

Tools (in my scratchpad, read-only on the repo):
- Use census: /tmp/claude-0/-home-user-r-infinite/db46f946-fd0e-58a3-baf6-61ea74b579d4/scratchpad/sr3r/census2.py <File…>. For every declaration it counts whole-name hits in src/, external/dh, external/pnt and external/zeta23, with comments and docstrings stripped and `#print axioms` lines excluded.
- Import closure: /tmp/claude-0/-home-user-r-infinite/db46f946-fd0e-58a3-baf6-61ea74b579d4/scratchpad/sr3r/clos.py A B. It prints whether A imports B transitively. Every "upstream" below was checked with it.
- Verbatim-copy checks used `diff <(sed -n a,bp F1) <(sed -n c,dp F2)`. "N diff lines" means the number of `<`/`>` lines.
- Already in §9 and not repeated here: `eq_of_mk_eq_of_periodic`/`periodic_congr`, and `absNorm_span_seven_pt`/`absNorm_span_one_add_three_ω`.

(A) DOORS

1. [A] src/KubotaCuspTheta.lean:357 `theorem coef_lowT_ae {t t' m : 𝓞 K} (htt : t * t' = 1) (hm : CuspClass t m) (hm0 : m ≠ 0) {r : ℝ}`. Lines 374–456 prove "for each n, g = 0 a.e. on Icc (1/(n+1)) (n+1)" by hand (`have key : ∀ n : ℕ, ∀ᵐ v ∂(volume.restrict (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1))), g v = 0`, then `rw [Ioi_zero_eq_iUnion_Icc, ae_restrict_iUnion_iff]`).
   - Other: src/KubotaThetaConst.lean:320 `theorem ae_eq_of_setIntegral_Icc {f g : ℝ → ℂ}` concludes `∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), f v = g v`. It is upstream (clos.py KubotaCuspTheta KubotaThetaConst → True) and is already used at KubotaThetaConst.lean:346 and KubotaThetaZero.lean:534.
   - Also: src/KubotaThetaCoef.lean:547 `theorem coef_thetaF_ae {x : 𝓞 K} (hx : x ≠ 0) …` is the cusp-∞ original. `diff` of KubotaCuspTheta 357–470 against KubotaThetaCoef 547–660 gives 26 diff lines out of 114.
   - Checked: `grep -rn -w ae_eq_of_setIntegral_Icc src` → KubotaThetaConst:320, 346; KubotaThetaZero:534.
   - Candidate: coef_lowT_ae (round 464) re-derives inline the generic lemma ae_eq_of_setIntegral_Icc (round 433) that it imports, and is otherwise a near-verbatim copy of coef_thetaF_ae.

2. [A] src/KubotaCuspTrans.lean:394 `theorem thS_lowT_twist_add … : thS r Y hY (slAct (lowT t) (z + σO (3 * x), v)) * ebr (-(σO m₀ * (z + σO (3 * x))) / 9) = thS r Y hY (slAct (lowT t) (z, v)) * ebr (-(σO m₀ * z) / 9)`. It is a bold headline and has no use (census2 KubotaCuspTrans: in-file 0, out 0).
   - Other: src/KubotaCuspSeries.lean:285 `have hper : ∀ z u, g (z + σO (3 * u)) = g z`. Its body (286–298: `rw [thS_lowT_add hr hY t u z hv, thSer_add_period_shift hsupp z u v, ← hcl u]`, then ebr_add and inverse bookkeeping) re-derives that twisted periodicity for the θ half of g.
   - Candidate: round 465's thS_lowT_eq redoes inline the twisted periodicity that round 460's thS_lowT_twist_add provides, and that lemma has no consumer.

(B) DUPLICATES

3. [B] src/KubotaCuspZero.lean:285 `def cuspF0 (d c : 𝓞 K) : ℂ := if BRow (c, d) then σO (cub c (span {d})) else 0` and src/KubotaCuspSums.lean:55 `def cuspF (c d : 𝓞 K) : ℂ := if BRow (c, d) then σO (cub c (span {d})) else 0` are the same definition with the arguments swapped (KubotaCuspZero imports KubotaCuspSums).
   - src/KubotaCuspCoef.lean:355 `theorem cuspF_add_fst (c d x : 𝓞 K) : cuspF (c + 3 * d * x) d = cuspF c d` and src/KubotaCuspZero.lean:290 `theorem cuspF0_add (d c x : 𝓞 K) : cuspF0 d (c + 3 * d * x) = cuspF0 d c` state the same thing after unfolding. `diff` of Coef 355–360 against Zero 290–295 differs only in the statement and `unfold` lines.
   - Candidate: cuspF0 duplicates cuspF, and cuspF_add_fst re-proves cuspF0_add, which is upstream.

4. [B] src/KubotaCuspIdent.lean:56 `theorem tsum_repQ_eq_of_span {c c' : 𝓞 K} (h : span {c} = span {c'}) {G : 𝓞 K → ℂ} (hG : ∀ x y, G (x + c * y) = G x) : ∑' r : 𝓞 K ⧸ span {c}, G (repQ c r) = ∑' r : 𝓞 K ⧸ span {c'}, G (repQ c' r)`.
   - Other: src/KubotaCoefUnit.lean:27 `theorem tsum_quot_congr {N N' : 𝓞 K} (hN : N ≠ 0) (h : span {N} = span {N'}) {F : 𝓞 K → ℂ} (hF : ∀ y y', N ∣ y - y' → F y = F y') : ∑' r : 𝓞 K ⧸ span {N}, F (repQ N r) = ∑' r : 𝓞 K ⧸ span {N'}, F (repQ N' r)`. It is upstream (clos.py KubotaCuspIdent KubotaCoefUnit → True).
   - Comparison: the conclusions are identical. The periodicity hypotheses are equivalent; the KubotaCuspIdent version drops `N ≠ 0`.
   - Candidate: tsum_repQ_eq_of_span (round 463) re-proves the upstream tsum_quot_congr.

5. [B] src/KubotaCuspSums.lean:272 `theorem exists_max_pow_dvd {π n : 𝓞 K} (hπ : ¬ IsUnit π) (hπ0 : π ≠ 0) (hn : n ≠ 0) : ∃ e : ℕ, π ^ e ∣ n ∧ ¬ π ^ (e + 1) ∣ n`. It is 27 lines; its only use is line 324, followed at 325–327 by extracting `n₁` with `¬ π ∣ n₁`.
   - Mathlib: RingTheory/UniqueFactorizationDomain/Multiplicity.lean:32 `theorem WfDvdMonoid.max_power_factor' … (h : a₀ ≠ 0) (hx : ¬IsUnit x) : ∃ (n : ℕ) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a`. The unprimed form is already used in this strand at src/KubotaDirSplit.lean:171.
   - Candidate: exists_max_pow_dvd plus the extraction after it re-proves Mathlib's max_power_factor'.

6. [B] src/KubotaCuspSums.lean:268 `theorem isCoprime_of_irreducible {π x : 𝓞 K} (hπ : Irreducible π) (h : ¬ π ∣ x) : IsCoprime π x := (Irreducible.coprime_iff_not_dvd hπ).2 h`.
   - Mathlib: RingTheory/PrincipalIdealDomain.lean:440 `theorem Irreducible.coprime_iff_not_dvd`.
   - Uses: in-file 333, 353, 390; KubotaCubeSum.lean:192.
   - Candidate: a one-line alias of a Mathlib lemma.

7. [B] src/KubotaCuspPoincare.lean:55 `theorem kubT_mul_conj (t : 𝓞 K) {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) : kubT t g * conj (kubT t g) = 1`.
   - Other: src/KubotaBallKernel.lean:208 `theorem conj_mul_self_of_uchar (hχ : IsUChar Γ χ) {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Γ) : χ γ * conj (χ γ) = 1`, which is upstream. `isUChar_kubT` is KubotaCuspTrans.lean:413.
   - Same pattern: src/KubotaCuspTrans.lean:147 `chiT_mul_conj`, since `chiT t x = kubT t (slT (3 * x))` by kubT_slT:421.
   - Candidate: kubT_mul_conj is exactly `conj_mul_self_of_uchar (isUChar_kubT t) hg`.

8. [B] src/KubotaEisenstein.lean:341 `theorem eisTerm_rowMul … : eisTerm s (slAct g p) (rowMul g⁻¹ cd) = kub ↑g * eisTerm s p cd` and :355 `theorem eis1_slAct … : eis1 s (slAct g p) = kub ↑g * eis1 s p`.
   - Other: src/KubotaEisTrunc.lean:128 `theorem psTerm_rowMul … : psTerm f (slAct g p) (rowMul g⁻¹ cd) = kub ↑g * psTerm f p cd` and :142 `theorem isAut_pseis (f : ℝ → ℂ) : IsAut Gam3 (fun g => kub ↑g) (pseis f)`.
   - The proofs are the same text with eisTerm s replaced by psTerm f, and `eis1_eq_pseis` (KubotaEisTrunc:97) is `rfl`.
   - Checked: `grep -rn -w eis1_slAct src` → only Eisenstein:370, inside eis1_transl, which is dead (item 23).
   - Candidate: the general isAut_pseis supersedes eis1_slAct and eisTerm_rowMul, and eis1_slAct has no live consumer.

9. [B] src/KubotaEisenstein.lean:152 `theorem kub_inv_Gam3 {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) : kub ↑(g⁻¹) = conj (kub ↑g)`.
   - Other: src/KubotaBallOp.lean:57 `theorem IsUChar.map_inv (hχ : IsUChar Γ χ) {g} (hg : g ∈ Γ) : χ g⁻¹ = conj (χ g)`, with src/KubotaEisTrunc.lean:59 `theorem isUChar_kub : IsUChar Gam3 (fun g => kub ↑g)`.
   - Candidate: kub_inv_Gam3 is the instance `isUChar_kub.map_inv hg`. The general lemma came later, and its 6-line proof repeats this one.

10. [B] src/KubotaEisTrunc.lean:224 `theorem norm_pseis_slAct_sub_le … : ‖pseis f (slAct g p) - cuspA g * f p.2‖ ≤ C * (cuspC τ * p.2 ^ (2 - τ))` (lines 224–263) and :210 `height_slAct_of_fst`.
    - Other: src/KubotaGrowth.lean:449 `theorem norm_eis1_slAct_sub_le … : ‖eis1 s (slAct g p) - cuspA g * ((p.2 : ℝ) : ℂ) ^ s‖ ≤ cuspC s.re * p.2 ^ (2 - s.re)` (449–490), whose core sits in src/KubotaGrowth.lean:434 `eisTerm_slAct_of_fst` (the `hD : uhsDen (σO 0) (σO (u : 𝓞 K)) p.1 p.2 = 1` block, the same as EisTrunc:215–218).
    - Checked: `grep -rn -w norm_eis1_slAct_sub_le src` → only KubotaGrowth.lean:20 (header) and :449.
    - Candidate: the general version (any profile f) re-runs round 388's 40-line argument, and the f = v^s original has no use outside its file.

11. [B] src/KubotaEisTrunc.lean:722 `theorem memLp_gfun {R : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : 0 ≤ s.re) {Y : ℝ} (hY : 0 < Y) : MemLp (gfun R s Y) 2 (muR rhoG)`. It is a bold headline with no use (census2 KubotaEisTrunc).
    - Other: src/KubotaGHolo.lean:509 `theorem memLp_gfun_all {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) (s : ℂ) : MemLp (gfun R s Y) 2 (muR rhoG)`. It drops `0 ≤ s.re` and is the one used (`gL`, 534).
    - Candidate: memLp_gfun is strictly less general than memLp_gfun_all and has no consumer.

12. [B] src/KubotaCuspZeroPhi.lean:216 `theorem summable_mul_normSq_cpow {f : 𝓞 K → ℂ} (hf : ∀ c, ‖f c‖ ≤ absNorm (span {c})) {s : ℂ} (hs : 2 < s.re) : Summable fun c => f c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)` and :254 `LSeries_eltSum`.
    - Other: src/KubotaPhi.lean:203 `theorem summable_phiTerm {s : ℂ} (hs : 2 < s.re) : Summable (phiTerm s)`, :250 `tsum_fiber_phiTerm` and :268 `LSeries_normA`. These are upstream; `normA` (239) is `∑ c ∈ eltsN n, cuspS c`, which is `eltSum cuspS`.
    - `diff` of ZeroPhi 216–247 against Phi 203–235 differs only in the signature, `phiTerm` unfolds, and `hf c` vs `norm_cuspS_le hc`. The proof never uses `hf` at `c = 0`.
    - Candidate: summable_phiTerm and LSeries_normA are instances of the round-441 generalizations, once `hf` is weakened to `c ≠ 0`.

13. [B] src/KubotaCuspCoef.lean:402 `eisHigh_slAct_eq_band (s : ℂ) {g : SL(2, 𝓞 K)} (hg : ∀ cd, BRow cd → (rowMul g cd).1 ≠ 0) …`, :430 `eisLow_slAct_eq_band` and :446 `setLIntegral_lowT_lt_top`.
    - Other: src/KubotaThetaZero.lean:219 `eisHigh_sS_eq_band`, :247 `eisLow_sS_eq_band` and :187 `setLIntegral_sS_lt_top`. `diff` shows the same text with sS for g.
    - The sS case satisfies hg by `rowMul_sS` (KubotaCuspZero:46, `(d, -c)`) and `primary_ne_zero`. Yet KubotaCuspCoef's own inner_pmSerS_uL uses the sS copies (lines 646–647, 657, 692).
    - Candidate: the sS lemmas are instances of the g-general ones that sit beside them.

14. [B] src/KubotaCuspSums.lean:174 `theorem coprime_three_absNorm {n : 𝓞 K} (hn : Primary n) : Nat.Coprime 3 (absNorm (span {n}))`.
    - Other: src/KubotaCoefSupp.lean:266 `theorem coprime_three_of_primary {n : 𝓞 K} (hn : Primary n) : (absNorm (span {n})).Coprime 3`. It is downstream, and both prove the statement from absNorm_primary_mod.
    - Candidate: the same fact (up to Nat.Coprime.symm) is proved twice.

15. [B] Small inline re-proofs of named upstream facts, each checked by grep:
    - `lam_ne_zero : (ω - 1 : 𝓞 K) ≠ 0` (src/KubotaLamCube.lean:37, upstream) is re-proved inline: verbatim at KubotaCuspSeries.lean:354–357, and via normSq_σO_lam at KubotaCuspIdent.lean:442–443 and KubotaCuspTheta.lean:255–256.
    - `ω_ne_zero` (src/KubotaPhi.lean:58, upstream) is re-proved at KubotaCuspIdent:441 and KubotaCuspTheta:254.
    - `cuspIdx_ne_zero` (KubotaCuspTheta.lean:251–257) repeats the `hx` block of KubotaCuspIdent.lean:440–444 verbatim.
    - `lam_not_unit` (src/EisensteinCubicRecip.lean:291) is re-derived at KubotaCuspSeries.lean:170–172.
    - `normSq_varpi` (KubotaCusps.lean:175) is re-derived at KubotaCuspIdent.lean:362.
    - `three_mul_ne_zero`/`finite_quot_three_mul` (KubotaConstTerm.lean:341/346) are re-derived at KubotaDirSplit.lean:51–56.
    - `absNorm_span_three` (KubotaCuspSums.lean:162) is re-derived at KubotaCoefScalar.lean:316–319.
    - `isCoprime_of_dvd_sub_one` (KubotaCuspSums.lean:263) is the e = 1 case of the upstream `isCoprime_of_dvd_sub` (KubotaCuspData.lean:317).
    - `δ3_eq_lam_neg` (KubotaCuspIdent.lean:150) and `δ3_eq_neg_ω_lam` (KubotaCompleted.lean:69) state the same identity in sibling branches.
    - Candidate: repeated 1–7-line re-proofs of facts that already have names.

16. [B, Mathlib] src/KubotaCuspTrans.lean:165 `chiT_neg`, :169 `chiT_nsmul (t x : 𝓞 K) (n : ℕ) : chiT t (n * x) = chiT t x ^ n`, :175 `chiT_zsmul_eq_one`, :336 `ebr_nsmul`, and the integer-extension block `key` inside exists_cuspClass (368–387).
    - These re-derive Mathlib's Algebra/Group/AddChar.lean:129 `map_nsmul_eq_pow`, :386 `map_neg_eq_inv` and :391 `map_zsmul_eq_zpow`, for the additive characters x ↦ χ_t(x) (chiT_add, chiT_zero) and x ↦ ĕ(m₀·3x/9) (ebr_add_period). The stack already uses AddChar (e.g. EisensteinGaussTransform.lean:62).
    - Candidate: about 35 lines re-derive AddChar API.

(C) DEAD CODE (helpers with no use besides header mention and #print)

17. [C] src/KubotaCusps.lean:94 `theorem kubotaData_of (hK : KubotaTheta) :`.
    - Checked: `grep -rn kubotaData_of src external` → only :15 (header), :94, :444 (#print).
    - KubotaRows.lean:514–517 destructures KubotaTheta itself because it also needs C and the value clause, which kubotaData_of drops.
    - Candidate: dead.

18. [C] src/KubotaCuspTrans.lean:46 `theorem lowT_ω : (lowT ω : Matrix (Fin 2) (Fin 2) (𝓞 K)) = gamPlus := rfl` and :49 `lowT_ω_sq … = gamMinus := rfl`.
    - Checked: grep → only :9 (header) and #print 438–439.
    - Related: the same SL elements already exist upstream as KubotaCharacter.lean:554/556 `gamPlusSL`/`gamMinusSL`.
    - Candidate: dead.

19. [C] src/KubotaCuspPoincare.lean:41 `theorem exists_cuspClass' (t : 𝓞 K) (ht : t = ω ∨ t = ω ^ 2) :`.
    - Checked: grep → only :10 (header), :41, :388.
    - Candidate: dead, an unused restatement of exists_cuspClass.

20. [C] src/KubotaCuspCoef.lean:590 `theorem isAut_pmSerS (x : 𝓞 K) (ψ : ℝ → ℂ) : IsAut Gam3 (fun g => kub ↑g) (pmSerS (δ3 * x) ψ) :=`.
    - Checked: grep → only :38 (header), :590, :761.
    - Candidate: dead.

21. [C] src/KubotaEisenstein.lean:368 `theorem eis1_transl {t : 𝓞 K} (ht : (3 : 𝓞 K) ∣ t) (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS) :`.
    - Checked: grep → only :23 (header), :368, :484.
    - Candidate: dead, and it is the sole consumer of eis1_slAct (item 8).

22. [C] src/KubotaEisTrunc.lean:94 `theorem eisTerm_eq_psTerm (s : ℂ) (p : ℂ × ℝ) (cd : 𝓞 K × 𝓞 K) :` (rfl) and :484 `theorem measurable_highF (s : ℂ) (Y : ℝ) : Measurable (highF s Y) :=`.
    - Checked: grep → only the header (16/34), the declaration and #print.
    - Candidate: dead.

(D) PATTERNS (cusp-by-cusp copies)

23. [D] The tiling / Fourier-coefficient argument appears four times:
    - KubotaConstTerm.lean:448 `hasSum_integral_eisTerm_c` (cusp ∞, ξ = 0).
    - src/KubotaEisFourier.lean:354 `hasSum_integral_ebr_eisTerm_c` (cusp ∞, ξ ≠ 0).
    - src/KubotaCuspZero.lean:132 `hasSum_integral_eisTermS_d` (cusp 0).
    - src/KubotaCuspCoef.lean:62 `hasSum_integral_ebr_wt` (any weight).
    - The integral–sum interchange around them also appears four times: ConstTerm:567 `integral_eis1_fundP3`, EisFourier:414 `integral_ebr_eis1_fundP3`, CuspZero:221 `integral_eis1_sS_fundP3`, CuspCoef:160 `integral_ebr_wtSeries`.
    - The majorant appears three times: ConstTerm:523, CuspZero:183 `tsum_lintegral_eisTermS_ne_top`, CuspCoef:120 `tsum_lintegral_wt_ne_top`.
    - Diffs: CuspZero 137–173 against ConstTerm 453–491 after renaming c↔d gives 18 diff lines; CuspCoef 70–115 against EisFourier 360–408 differs only in weight handling.
    - EisFourier's `cuspSm m c` unfolds to `wtSum (cuspF c) (σO m / 9) c`, i.e. cusp ∞ is t = 0 of `wtCuspT`.
    - Candidate: one ξ- and weight-parametric tiling lemma covers all cusps. The round-462 weighted versions already do so for ξ ≠ 0.

24. [D] The cusp-0 character sums mirror the cusp-∞ ones with c and d swapped:
    - KubotaCuspZero.lean:328 `cuspS0_twist` (328–343) vs KubotaCuspSums.lean:102 `cuspS_twist` (102–119).
    - :318 `isUnit_mk_three_mul` vs Sums:91 `isUnit_mk_of_bRow`.
    - :356–360 vs Sums:122–129 `cuspS_eq_zero_of_witness`.
    - KubotaCuspZeroPhi.lean:50 `bRow_iff_fst` (50–74) vs Sums:614 `bRow_iff_primary`.
    - ZeroPhi:79 `count_three_mem` (79–122) vs Sums:536 `count_primary_mem`. Their tails 94–122 and 561–589 are identical except `e`↔`0` and one condition (2 diff lines).
    - ZeroPhi:128 `count_bRow_fst` (128–183) vs Sums:652 `count_bRow` (652–706): 29 diff lines out of 55.
    - ZeroPhi:199/:280 vs KubotaPhi.lean:184 `norm_cuspS_le`/:275 `normA_eq_zero_of_not_cube`.
    - Candidate: about 250 lines are re-proved with roles renamed, where a row/column-parametric lemma would serve both cusps.

25. [D] The pairing with ũ_s is written out three times:
    - src/KubotaCuspCoef.lean:479 `inner_pmSerC_uL` (489–583).
    - src/KubotaCuspCoef.lean:627 `inner_pmSerS_uL` (636–728): `diff` after `slAct (lowT t)`→`slAct sS` gives 22 diff lines out of ~95.
    - KubotaThetaZero.lean:306 `inner_pseisS_uL_band`, which shares the setup and hEfin calc.
    - The L² pairing step appears three times: CuspCoef:600 `inner_toLp_pmSerS`, ThetaZero:281 `inner_toLp_pseisS`, CuspPoincare:280 `inner_toLp_pmSerC`.
    - Candidate: one lemma over the cusp matrix g (with its Fourier-coefficient identity as a hypothesis) would replace two of these ~100-line proofs and most of the third.

26. [D] src/KubotaCuspPoincare.lean:189 `integral_conj_lowT_inv_mul` (189–220) and src/KubotaThetaZero.lean:139 `integral_conj_sS_inv_mul` (139–170) are the same proof.
    - `diff` after `lowT t`→`sS` differs only in the character step (kubT vs kub_sS_conj).
    - Candidate: one lemma for any g (character γ ↦ κ(gγg⁻¹), normality from gam3_normal) covers both.

27. [D] KubotaCuspPoincare.lean (cusp γ_t) repeats KubotaPoincare.lean (cusp ∞):
    - memLp_pmSerC 145–172 vs memLp_pmSer 226–250. The `diff` after renaming differs only in the `(lowT t)⁻¹ *` shift.
    - memLp_pmSerC_Icc 176 vs 253; measurable_pmTermT 96 vs 117; conj_pmSerT_mul 234 vs 277; integral_conj_pmSerT_mul 247–276 vs integral_conj_pmSer_mul 289–318.
    - At t = 0, lowT 0 = 1 and kubT 0 = kub, and CuspClass 0 (δ3*x) holds by ebr_period. `conj (kub (gamRow cd)) = σO (cub cd.1 (span {cd.2}))` by kub_eq_conj_cub, as in KubotaPoincare:271. So pmSer m = pmSerT 0 m.
    - Candidate: the cusp-∞ Poincaré lemmas are the t = 0 instances of the γ_t ones.

28. [D] src/KubotaCuspTheta.lean:129 `residue_eq_of_eq_cpow` and :59 `tendsto_aBand` repeat blocks of KubotaPmTheta.lean:
    - The identity-theorem and path block 141–185 equals KubotaPmTheta.lean:357–405 (inside `inner_pmSer_thetaL_cross`, :325) except the `hfg` line.
    - tendsto_aBand's hγ/hI/hL/h3 (63–83) equal KubotaPmTheta:289–313 (`tendsto_aPm`, :283).
    - `aBand … y = aPm x … 0 y`, since `mellinPsi 0 = 0` (KubotaThetaPair:332), so tendsto_aBand and differentiableOn_aBand are instances of tendsto_aPm and differentiableOn_aPm (:266).
    - Candidate: ~60 lines are repeated across the two files.

29. [D] src/KubotaCuspSeries.lean repeats KubotaThetaSeries.lean:
    - :46 `integral_ebr_thTerm_shift` vs :211 `integral_ebr_thTerm`.
    - :85 `integral_ebr_thSer_shift` (92–116 is the same setup as 245–274) vs :236 `integral_ebr_thSer`.
    - :136 `thSer_add_period_shift` vs :183 `thSer_add_period`.
    - Candidate: the m₀-shifted versions at m₀ = 0 give the unshifted ones (for c = 0), with the same proofs.

30. [D] src/KubotaCuspSeries.lean:272–283 (`hg2`, "bounded on 3P ⇒ ∫⁻|g|² < ⊤") equals src/KubotaThetaEq.lean:131–140 (`hS2`) except for the bound's source.
    - Candidate: a 10-line block is repeated.

31. [D] Exponential–polynomial and Bessel-decay bounds:
    - src/KubotaDerivative.lean:66 `rpow_four_thirds_exp_le` (66–97) vs KubotaTheta.lean:149 `rpow_third_exp_le` vs KubotaThetaSeries.lean:46 `pow_five_exp_le`: the same 30-line proof with (exponent, factorial) = (4/3, 5!), (1/3, 4!), (5, 8!).
    - The Bessel-decay block (hK/hre/hx₀/hxx/hdecay/hexp) at Derivative:116–135 recurs at ThetaSeries:84–107, Theta:276–293 and KubotaMellin:136–157.
    - Checked: `grep -rn "bkR_le_exp (r := 1 / 3)" src` → 4 hits.
    - Candidate: two parametric lemmas would replace three plus four copies.

32. [D] src/KubotaCusps.lean:299–320 (branch u ≡ ω) and :321–341 (branch u ≡ 2ω) of `cusp_table` repeat the same proof with gamMinus↔gamPlus, ω↔ω² and tM↔tP (diffed).
    - Candidate: one per-cusp lemma would replace two 20-line branches.

33. [D] src/KubotaCuspTrans.lean:261 `ebr_third` (261–272) and :275 `ebr_neg_third` (275–286) repeat the same 12-line proof with the sign flipped (diffed).
    - The second follows from the first and `conj_ebr` (KubotaTranslates.lean:251, upstream).
    - Candidate: duplicated proof.

34. [D] src/KubotaEisTrunc.lean:345 `le_snd_of_mem_hball` (345–353) and :356 `snd_le_of_mem_hball` (356–364) are mirror proofs with p↔q.
    - With KubotaBallCount.lean:41 `ppi_comm` (upstream), q ∈ hball R p gives p ∈ hball R q.
    - Candidate: one lemma would replace the other.

35. [D] src/KubotaCuspPoincare.lean:306 `def thSU … := UHS.piecewise (thS r Y hY) 0` and :315 `measurable_thSU` name a construction that is built inline elsewhere:
    - inline `obtain ⟨S', hS'⟩ … S' = UHS.piecewise (thS r Y hY) 0` with the same measurability at KubotaThetaEq.lean:180 and :253, and KubotaThetaInv.lean:343;
    - the 23-line blocks KubotaThetaEq:253–275 (`isAut_thS`) and KubotaThetaInv:343–366 (`thS_slAct_of_ae`) differ in only 4 lines (diffed).
    - Candidate: repeated inline block; the named form exists, but downstream of both copies.

(E) EFFICIENCY

36. [E] src/KubotaDirSplit.lean:276–294 and :314–327 contain ten near-identical lines of the form `have Lk : locG (δ3 * (x * p ^ e)) p k = 0 := by rw [locG_low hp hpp x _ _, ite_eq_right (by decide)]`.
    - Checked: `grep -n "by decide"` → 13 hits, all in this file. There is no set_option, maxHeartbeats or native_decide in any of the 16 files.
    - Candidate: near-generated repetition.

37. [E] src/KubotaCuspIdent.lean:163 `theorem kubota_sum_poly …` has a machine-generated `linear_combination` certificate (lines 170–185, about 80 monomials in 7 variables), and kubTermT_affine runs `field_simp; ring` on kubPoly (283–286).
    - Not timed (no builds).
    - Candidate: generated certificate, flagged for timing only.

(F) MISMATCHES

38. [F] src/KubotaCuspSums.lean:5–7: "Round 389's `S(c) = Σ_{d mod 3c} (c/d)₃`, … is zero unless `c = m³` with `δ₃ ∣ m`; there it counts the bottom rows, `S(m³) = N(m)³·Π_{P ∣ m, 3 ∉ P}(1 − 1/N(P))`."
    - Lean: :717 `theorem cuspS_cube_eq {m : 𝓞 K} (hm : m ≠ 0) (hδ : δ3 ∣ m)`.
    - At m = 0 the stated formula gives 0, but cuspS 0 = 1: by bRow_zero_iff (KubotaEisenstein:376) the only bottom row (0, d) is (0, 1), and cub_one_right gives its symbol 1. The header's own bullet (line 41) does say `δ₃ ∣ m ≠ 0`.
    - Candidate: the module intro omits m ≠ 0.

39. [F] The strand uses λ for two different elements.
    - src/KubotaCusps.lean:21: "`(1, 0; λ, 1) = (1, 0; 2, 1)(1, 0; 3ω, 1)γ_−`". The Lean, `lowerδ3_eq : (!![1, 0; δ3, 1] …) = …` (:218), has `δ3 := 1 + 2 * ω` (EisensteinPoisson:342).
    - KubotaCuspData.lean:15 likewise writes "`λ²h₀/L = a₀/c₀`" for `δ3 ^ 2 * repQ L h₀ = g₀ * a₀`.
    - But src/KubotaCuspIdent.lean:7–8 ("`λ = ω − 1` and `m′ = δ₃ω²tλ²m = −tλ³m`") and KubotaCuspTheta.lean:7 define λ = ω − 1. Under that definition the KubotaCusps factorization is false: the product is (1, 0; 2 + 3ω + ω², 1) = (1, 0; 1 + 2ω, 1).
    - Candidate: headers in one strand use λ for both δ₃ and ω − 1.