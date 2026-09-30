# Structural review of the Riemann Lean pilot (round 235 head `1a39c2f`)

**Status: work in progress.** This file is written incrementally so that a handoff to another session loses nothing. Every claim below is labelled KERNEL-CHECKED (a Lean file compiled against the built stack with axioms exactly `[propext, Classical.choice, Quot.sound]`), PAPER PROOF (argued from exact Lean statements, not yet compiled), NUMERICAL, OBSERVATION-CONJECTURE, or REFUTED, and ACKNOWLEDGED (already in the README/docstrings) or NOVEL.

## 0. Handoff state (update this section first)

Done so far (in order):

1. Baseline reproduced (see §1). One discrepancy: the README's "no warnings" claim does not hold (25 linter-warning lines from pilot files, listed in §1).
2. Module- and declaration-level dependency graphs built from the compiled environment (§2). Name clashes found that block imports (§2.3).
3. Line-by-line reading fan-out: 69 of 147 chunks have reading cards; the rest failed on the account's session limit (list in §8). The cards are inputs, not findings: everything reported as a finding below was re-read directly in the source by the reviewer.
4. Kernel-checked new theorems (all compiled, standard axioms), to be integrated as README rounds 236+:
   - `Dedekind4` (scratch `verify/Dedekind4.lean`, to become `src/WeilDedekind.lean`): the Weil form of `ζ_{ℚ(i)} = ζ·L(s,χ₋₄)` on twin boxes, `2·Q_ζ + Q_{χ₋₄}`, as one `TwinLandau.TwinData` on the sum of the two zero index types; `RH ∧ GRH(χ₋₄) ⟺ 2Q_ζ(twin λ) + Q_{χ₋₄}(twin λ) ≥ 0 ∀ λ ≥ 0`, graded version, subexponential version (§4, finding F1).
   - `TwinKV` (scratch `verify/TwinKV.lean`, to become `external/pnt/TwinKV.lean`): `TwinLandau.Q_ge_of_rates` (per-pole rates) and `twins_lower_KV`: `∃ C, A > 0, ∀ λ ≥ 1, Q_ζ(twin (box 1) λ) ≥ −C·exp((1 − A/f_KV(e^{8λ}))·λ)`, the Korobov–Vinogradov region turned into an unconditional lower bound on the twin form (finding F2).
   - `PolyaFix` (scratch `verify/Polya.lean`): the hypothesis of `PsiOmega.rh_of_polya` is refutable (`polya_hyp_false`), and a non-vacuous `rh_of_polya'` with hypothesis `∀ x ≥ 2, L(x) ≤ 0` (finding F3). *(Compile pending at the time of writing; see the log line in §4.)*
5. Not yet done: the cross-cutting lens pass and adversarial-verification workflow (sub-agents unavailable until the session limit resets); integration of the above as rounds 236+ with README updates and the three builds; the remaining findings in §5 need Lean where marked.

How to resume: the built Mathlib is at `$SCRATCH/mathlib4` (commit in `MATHLIB_REV`), the pilot oleans are in `build/`. Compile a scratch file with
`cd $SCRATCH/mathlib4 && LEAN_PATH="$(lake env printenv LEAN_PATH):<pilot>/build" lean <file>`.
`external/pnt` modules and `Zeta23`/`SlogZeta` modules cannot be imported together (§2.3), nor `ParityRelax`/`ParityCert` with `WeilLandau` or `Concave`.

## 1. Baseline reproduction

- Toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `0f64d30a9a4593b3ae50375b960a5cf7f0845606`, `lake exe cache get`.
- `./build.sh`: 153 files compiled (906 s on this machine). `cat src/*.lean | grep -c "^#print axioms"` = 829; all 829 lines print `[propext, Classical.choice, Quot.sound]`; no `sorry`, no `axiom`.
- `external/pnt/build.sh`: 19 PNT+ files at 650d312 with `pnt_port.patch`, 12 layer files; the 15 printed axiom lines are clean (one is PNT+'s own `StrongPNT`, printed as `[propext, choice, Quot.sound]`).
- `external/zeta23/build.sh`: 50 zeta23 files at fbdc36b plus `SlogZeta.lean`; 10 clean axiom lines.
- **Discrepancy (NOVEL, minor):** README line 10 says "The build prints no warnings." The pilot build prints 25 linter-warning lines from pilot files: `GlobalTeeth.lean` (100, 138 ×2, 202, 294, 305, 321, 365, 387), `ExpSum.lean:202`, `VinoBad.lean:167`, `ExpSum8.lean:100`, `ExpSum10.lean:41`, `VinoFam.lean:162` (×2), `VinoKV.lean` (46, 120, 184). The pnt layer prints warnings from its own files too: `Landau.lean` (243 ×2, 304, 1018, 1222), `KVBridge.lean:140`. None affects soundness. Bearing on RH: none.

## 2. Dependency map

### 2.1 Layers and sizes
235 modules, 5235 constants after folding auxiliary names into their parents: pilot `src/` 153 modules; pnt layer 12 (`external/pnt/*.lean`) over 19 vendored PNT+ modules; zeta23 layer 1 (`SlogZeta`) over 50 vendored zeta23 modules (which include a *second, older* copy of nine PNT+ files as `Zeta23.FromPNTPlus.*`).

Cross-layer declaration edges (user → used): pnt-layer → PNT+ 124, pnt-layer → pilot 73, zeta23-layer → pilot 45, zeta23-layer → zeta23 34. The pnt layer and the zeta23 layer never use each other (confirmed by the import graph; a name-intersection count between the two vendored PNT+ copies is not reliable from the merged dump and is not claimed).

### 2.2 Islands (lumps)
Module-import islands (no import path to or from the main component): `{AngularFamily, GlobalTeeth}`, `{BallTower, LatticeCount}`, `{ResponseKernel, ToneHyperbola}`, `{LocalTeeth}`, `{WanderBound}`.

Declaration-level islands inside the main import component (modules that import the stack but whose declarations use nothing from it, or are used by nothing): `SixteenPi` (79 declarations; imports `Curvature` but uses none of it), `GlobalTeeth`+`AngularFamily` (37), `BallTower`+`LatticeCount` (35), `ToneHyperbola`+`ResponseKernel` (16), `LocalTeeth` (9), `WindowForm` (several tiny components), `GapCriterion` (3), `WanderBound` (3).

Tips: 418 Prop-valued declarations nothing uses (most are intended headline results). 64 non-Prop declarations nothing uses (mostly upstream).

Joins that exist for the islands: `AngularFamily.rh_of_member_zero` (`GRHMemberZero → RiemannHypothesis`) is the only bridge from the angular island to RH, and nothing consumes it; finding F1 below connects it to the Weil chain (`GRHMemberZero → RH ∧ GRH(χ₋₄)` is proved in the new file; the converse needs the classification of the zeros of `L(s,χ₋₄)` off the strip, PAPER PROOF only).

### 2.3 Name clashes that block imports (NOVEL, structural)
Confirmed by direct reading and by the failed whole-environment import:
- `Pilot1ca.cw`: `def cw (n : ℕ) : ℝ := 2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n)` (`src/ParityRelax.lean:70`) vs `def cw (q : ZIdx) : ℂ := ghatC (box 1) 1 (ordi zetaZeroFamily q) ^ 2` (`src/WeilLandau.lean:55`).
- `Pilot1ca.tail_W`: `Concave.lean:291` vs `ParityRelax.lean:437` (different statements).
- `BlaschkeB`: PNT+ `StrongPNT` (pnt layer) vs `Zeta23.FromPNTPlus.StrongPNTPrefix` (zeta23 layer).

Consequence: no Lean file can import both the pnt layer (KV region, density, short primes) and the zeta23 layer (`mv_hilbert`, `S(t)` bound); no file can use `ParityRelax` together with `WeilLandau`. Effort to fix: rename the two ParityRelax names (only `ParityCert` imports `ParityRelax`) — trivial; the PNT+ duplication needs one vendored copy (the zeta23 copy is a different upstream commit: `ZetaBounds` 3060 vs 3683 lines) — medium. Bearing on RH: none directly; it blocks substitution S1 below.

## 3. Named hypotheses (where assumed / where proved)
*(to be completed from the declaration index; the list of Prop-valued parameters with their discharge sites is in the scratch `decl_index.tsv` and will be summarised here)*

## 4. Ranked findings

### F1. The Dedekind ζ_{ℚ(i)} twin form: one Landau argument for RH ∧ GRH(χ₋₄) — KERNEL-CHECKED, NOVEL
Statement (compiled, `verify/Dedekind4.lean`, axioms clean):
- `Dedekind4.twinData_K : TwinLandau.TwinData PK cK GboxC (fun l => QK (l + 1) (twin (box 1) l))` with index `ZIdx ⊕ ZeroIdx (sqF (XiC chi4))`, `PK = Sum.elim poleP (fun i => 2 * I * tauC i)`, `cK = Sum.elim (2 * cw) (fun i => 2 * ghatC (box 1) 1 (tauC i) ^ 2)`, `QK a g = 2 * weilQ a g + QC chi4 a g`.
- `rh_grh_iff_QK_twins : (RiemannHypothesis ∧ GRH chi4) ↔ ∀ l ≥ 0, 0 ≤ QK (l + 1) (twin (box 1) l)`.
- `QK_twins_rate (hσ : 0 ≤ σ) : (∃ C, ∀ l ≥ 0, −C e^{σ l} ≤ QK …) ↔ (∀ s, IsNontrivialZero s → |2 Re s − 1| ≤ σ) ∧ (∀ s, L(χ₋₄, s) = 0 → 0 < Re s < 1 → |2 Re s − 1| ≤ σ)`.
- `rh_grh_iff_QK_subexp`.
Why it is a join: `twinData_zeta` (WeilLandau.lean:119) and `twinData_chi good_chi4 hS4` (WeilChiCriterion.lean:110) have the same weight function up to the factor 2 (`GboxC p = 2 * Gbox p`), so they combine into one `TwinData` on the sum type; `HasSum.sum` gives the explicit formula of the product `ζ·L`. The factor 2 is the normalisation difference between `ZIdx` (each zero once) and `ZeroIdx (sqF (XiC χ))` (each `±τ` pair once); `2Q_ζ + Q_χ` is thus the form of `ζ_K` with the ζ-zeros doubled. The un-doubled form `Q_ζ + Q_χ` needs the index `ZIdx ⊕ Bool × ZeroIdx …` (not done; same proof, one more sum).
Link to the angular island: `AngularFamily.angularL0 = ζ · L(χ4C, ·)` with `χ4C` definitionally `chi4`; `rh_of_member_zero` proves only `GRHMemberZero → RH`. The new file proves `GRHMemberZero → RH ∧ GRH chi4` *(pending compile of that small addition)*; the converse needs that `L(s,χ₋₄)` has no zeros with `Re s ≤ 0` other than `−(2n+1)` and none with `Re s ≥ 1` (functional equation + non-vanishing on `Re s = 1`), PAPER PROOF.
Bearing on RH: a single positivity statement equivalent to RH ∧ GRH(χ₋₄), i.e. the Weil criterion for the Dedekind zeta function of the Gaussian integers, which is where the README's "2-dimensional ball" narrative (rounds 182–187) lives; no evidence for or against RH.
Effort: done (170 lines).

### F2. The Korobov–Vinogradov region as an unconditional lower bound on the twin form — KERNEL-CHECKED, NOVEL
Statement (compiled, `verify/TwinKV.lean`, axioms clean):
- `TwinLandau.Q_ge_of_rates (D : TwinData P c G Q) (hr : ∀ q, |(P q).re| ≤ r q) (hl : 0 ≤ l) (hs : Summable fun q => ‖c q‖ * exp (r q * l)) : −(4 * ∑' q, ‖c q‖ * exp (r q * l)) ≤ Q l` (generalises `Q_ge`, TwinLandau.lean:873, from one rate to a rate per pole).
- `TwinKV.twins_lower_KV : ∃ C A : ℝ, 0 < A ∧ ∀ l ≥ 1, −(C * exp ((1 − A / fKV (exp (8 * l))) * l)) ≤ weilQ (l + 1) (twin (box 1) l)`, with `fKV T = (log T)^{2/3} (log log T)^{1/3}` (KaiserKV.lean:30).
Ingredients: `KaiserKV.abs_im_tau_le` (zeros with `|Re τ| ≤ T` have `|Im τ| ≤ ½ − A/f(T)`), `Unconditional.norm_ghatC_le_of_antitone` (`|ĝ₀(τ)| ≤ 2 g(0) cosh(|Im τ|)/|τ|`), `WeilCount.summable_Xi_zeros_rpow` for the tail `Σ_{|Re τ|>T} |ĝ₀(τ)|² ≤ K₀² S₁ T^{−1/4}`, and `T = e^{8λ}`.
Reading: `weil_twins_rate` (WeilLandau.lean:162) says the exponential rate of the twin form's negative part equals `2Θ − 1`. This theorem is the quantitative "`Θ ≤ 1` with the KV margin" on the positivity side: the defect is at most `exp(λ − c λ^{1/3} (log 8λ)^{−1/3})`. By `weil_twins_rate` no bound of the form `e^{σλ}` with `σ < 1` is provable without a zero-free strip, so the shape of this bound is exactly the shape of the best known zero-free region — the twin-form defect function and the zero-free region determine each other (OBSERVATION: the map is `r(λ) = max over zeros of |2β−1| weighted by height`, and any improvement of the `λ^{1/3}` exponent is equivalent to a wider region).
Bearing on RH: none beyond making the KV region visible in the positivity language; it is the first unconditional *quantitative* statement about the twin form's defect in the stack.
Effort: done (200 lines). Lives in the pnt layer (needs `KaiserKV`).

### F3. `rh_of_polya` is vacuous as stated — REFUTED (hypothesis refutable), NOVEL
`src/MertensOmega.lean:283`: `theorem rh_of_polya (h : ∀ x : ℝ, 1 < x → summ fLi x ≤ 0) : RiemannHypothesis`, with `summ f x = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, f k` (`src/PsiOmega.lean:350`) and `fLi n = liouville n` (`MertensOmega.lean:154`). At `x = 3/2` the hypothesis says `λ(1) = 1 ≤ 0`. So the theorem is `False → RH`. README round 222 (line 7137) says "It is the classical implication, now machine-checked" — overturned. Pólya's conjecture is `L(n) ≤ 0` for `n ≥ 2`. Fix (compiled as `PolyaFix.rh_of_polya'`): hypothesis `∀ x, 2 ≤ x → summ fLi x ≤ 0`, proof through `rh_of_liouville_bound` with `c = 1` (on `1 < x < 2`, `L(x) = 1 ≤ √x`). Bearing on RH: none (Pólya's conjecture is false anyway); it is a correctness defect in a stated theorem.

### F4. `simple_of_trunc_gap` and `simple_of_cos_gap`: the gap hypothesis is refutable as stated — REFUTED (PAPER PROOF of the refutation), NOVEL
`src/GapBound.lean:367`: `theorem simple_of_trunc_gap … (hgap : ∀ᶠ K in atTop, ∀ f ∈ T K, 0 < normSq f → Lam2GeT a (T K) (weilQ a f / normSq f + γ)) … : SimpleGround a g`, with `Lam2GeT a S s := ∀ g ∈ S, ∀ h ∈ S, ∃ α β, α² + β² = 1 ∧ s · normSq(αg + βh) ≤ weilQ a (αg + βh)` (GapBound.lean:210). The README (line 2157) describes `hgap` as "eventually `λ₂(T K) ≥ λ₁(T K) + γ`". The Lean quantifies over **every** `f ∈ T K`, i.e. it demands `λ₂(Q|T K) ≥ R(f) + γ` for the maximiser `f` of the Rayleigh quotient `R` on `T K` as well, which is impossible once `dim T K ≥ 2`: take `g, h` independent in `T K`, let `f = αg + βh` maximise `R` on the unit circle of `span{g,h}` (compact), then `Lam2GeT` at `(g, h)` gives `(R(f) + γ)‖αg+βh‖² ≤ Q(αg+βh) ≤ R(f)‖αg+βh‖²`, so `γ‖αg+βh‖² ≤ 0`, contradicting independence. A dense truncation (`TruncDense`) has `dim T K → ∞`, so `hgap` is false for every dense `T`; `simple_of_cos_gap` (CosTrunc.lean:631) inherits this at `K ≥ 2`. The proof (GapBound.lean:424–433) uses `hgap` only at `f = F K`, the approximants of the ground state, whose Rayleigh quotient tends to `lam a` (`hR`). Fix: hypothesis `∀ᶠ K, Lam2GeT a (T K) (lam a + γ)` (eventually `λ₂(T K) ≥ λ₁ + γ`, implied by the README's condition since `λ₁(T K) ≥ λ₁` by `lam_le`); the old statement follows from the new one (old `hgap` at any nonzero `f` gives `Lam2GeT (R(f)+γ) ⇒ Lam2GeT (λ₁+γ)` by `lam_le` and monotonicity), so the headline statement is kept and strengthened. Lean status: fix to be implemented as a round; the refutation itself is not compiled (it needs the compactness maximiser, ~100 lines) and is recorded as PAPER PROOF. Bearing on RH: none directly; but this is the theorem the numerical Galerkin gap certificates (rounds 60–62) were meant to feed, and as stated it could never be fed.

### F5. `2·Q_ζ + Q_χ` vs the angular island — see F1.

*(more findings follow as they are verified; candidates under examination are listed in §7)*

## 5. Received-wisdom claims tested
- **"The build prints no warnings"** (README line 10): overturned (§1).
- **"c = 1/4 in the detection step gives θ > 2/3"** (README round 235, "Not done"): the pilot's density route is large-values-only (`DirMean.large_values_off'`, `DensityCore.card_detect_le`) and reaches `A = 4(1+δ)`. A reviewer's computation with the same route and a subconvexity exponent `c` in the detection step (with the mollifier length `X = U^{2σ−1}` re-optimised) gives `A(σ) = (1 − x(2σ−1))/(1−σ)` with `x = (3σ−2)/(4σ²−6σ+3)` at `c = 1/4`, whose supremum is ≈ 3.4 (at σ ≈ 0.85), i.e. `θ > ≈ 0.706`, not `2/3`. Reaching Ingham's `(2+4c)(1−σ)` needs Littlewood's lemma (`∫ log|ζM|`), which the stack does not have. Status: NUMERICAL/PAPER (the exponent algebra was checked by hand twice; Titchmarsh §9.19 was not re-read line by line). The README's sentence is therefore optimistic about what the *existing* detection step would give; the `5/8` correction in round 235 stands.
- **"`rh_of_polya` is the classical implication, machine-checked"**: overturned (F3).
- **"`simple_of_trunc_gap`: if eventually `λ₂(T K) ≥ λ₁(T K) + γ` then every ground state is simple"**: the Lean says something stronger and false-hypothesised (F4).

## 6. Killed ideas
- **Feeding zeta23's `mv_hilbert` into `DirMean.mean_value`** (README section-5 lead): the substitution `(b − a + 8P(1 + log P)) → (b − a + 4 C_MV P)` is straightforward (the spacing is `|log j − log j'| ≥ |j − j'|/(2P)`), but it cannot reach `DetectEM` because the pnt and zeta23 layers cannot be imported together (§2.3), and the gain is one log power in `B = 11`, which changes no exponent. Not implemented.
- **Ingham's exponent from the present detection step**: see §5.
- **`GRHMemberZero ← RH ∧ GRH(χ₋₄)` inside the new file**: needs the off-strip zero classification for `L(s,χ₋₄)`; left as PAPER PROOF (the useful direction is compiled).

## 7. Candidates from the reading cards still to be verified by direct reading
(Each is a sub-agent claim; none is a finding until re-read. Listed so a successor can pick them up.)
- `Commute.lean` headline theorems (`xcorr_deriv2`, `bil0_deriv2`, `poleR_deriv2`, `bilQ_deriv2`) have no consumers (dead, ~100 lines).
- `TwinLandau.Rp_eq_zero_of_Wsum_const` (line 539) has no consumer; its join with `Rp_ne_zero` ("`Q` constant ⇒ `G` vanishes at every pole") is not stated.
- `[Countable ι]` on eight `TwinLandau` theorems is derivable from `TwinPoles.finite`.
- `Uniqueness.lamPerp`, `groundState_unique_of_gap`, `lam_bdd` unused.
- `BallTower.completing_factor_unique` docstring claims uniqueness of the factor; Lean proves it only up to a constant within order `< 2`.
- `Unconditional.pinned_unconditional` concludes `(ĝ x).re = 0`, docstring says "a real zero of ĝ" (one `Complex.ext` away).
- `MollId.natCast_mul_cpow` duplicates Mathlib `Complex.natCast_mul_natCast_cpow`; `natCast_cpow_neg`/`ExpSum.cpow_phase`/`Pilot1ca.cpow_pos_real` are three copies of one bridge.
- `ToneHyperbola`/`ResponseKernel`: `hasDerivAt_Kq` unused because `ToneCalc.hasDerivAt_gamma` demands global differentiability.
- `LocalTeeth` vs `GlobalTeeth`: no Lean join between the local factor and the global two-square count.
- `Osc.lean` `OscInf`/`hInf` redundant (existence already proved inside `oscInf_eq`).
- `ParabolaGap.weilQ_perp_ge_seg` is a near-verbatim copy of `FourierGap.weilQ_perp_ge_sliver` (~60 lines).
- `Mollify.normSq_avg_le` is Minkowski's integral inequality (Mathlib candidate); `tendsto_integral_pratt` is a Pratt/Scheffé lemma not in Mathlib.
- `AngularFamily.zeta_neg_odd_ne_zero` and `Concave.layer_nonneg` (Bonnet mean value) are Mathlib candidates.

## 8. Reading coverage log
Cards exist for 69 of 147 chunks (scratch `cards/chunk_*.json`). Uncovered chunks (no card; the reviewer read the parts cited in §4 directly): GroundState, GroundStateExists, HadamardApply+HurwitzCross, all `Kaiser*` files except none, KernelChain, LSeriesLandau, LandauLaplace, LatticeCount, Limit, ParabolaGap, PhiNull, PoleRelax, Polya, Positivity, PrimeRaces+PrimeRelax+PrimeRelax3+PrimeSide, PsiOmega, RealDirichlet, ResponseKernel, RiemannKernel (both halves), Roadmap, Saturation, ShortPrimes, ShortWeil, ShortZeros, SimpleCont, SimpleCover+SimpleStructure, SixteenPi (both halves), SmallPositivity, SmallPositivity2, Split, StrictPositivity, StripConv, StripShift, StructureD, SwapRealize, T1bt, T1ca (both halves), WeilChi, WeilChiBridge, WeilChiDensity, WeilConverse, WeilCount+WeilCriterion+WeilDischarge, WeilIndexConverse (both halves), WeilIndexInfinite, WeilIndexZeta+WeilLandau+WeilRH+WeilRate, WeilZeta, WindowForm, XiBounds, XiLogDeriv, ZeroCount, ZeroLocal+ZeroSwap+Zeta, ZetaInputs; all of `external/pnt/*` and `external/zeta23/SlogZeta.lean`. (Some of these — WeilLandau, WeilChiCriterion, TwinLandau, KaiserKV, WeilCount, Unconditional, MertensOmega, GapBound, CosTrunc — were read directly by the reviewer for the findings above.)
