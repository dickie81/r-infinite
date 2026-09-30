# Structural review of the Riemann Lean pilot (round 235 head `1a39c2f`)

**Status: work in progress.** This file is written incrementally so that a handoff to another session loses nothing. Every claim below is labelled KERNEL-CHECKED (a Lean file compiled against the built stack with axioms exactly `[propext, Classical.choice, Quot.sound]`), PAPER PROOF (argued from exact Lean statements, not yet compiled), NUMERICAL, OBSERVATION-CONJECTURE, or REFUTED, and ACKNOWLEDGED (already in the README/docstrings) or NOVEL.

## 0. Handoff state (update this section first)

Done so far (in order):

1. Baseline reproduced (see §1). One discrepancy: the README's "no warnings" claim does not hold (21 linter-warning lines from eight pilot files, listed in §1; fixed in round 240).
2. Module- and declaration-level dependency graphs built from the compiled environment (§2). Name clashes found that block imports (§2.3).
3. Line-by-line reading fan-out: 69 of 147 chunks have reading cards; the rest failed on the account's session limit (list in §8). The cards are inputs, not findings: everything reported as a finding below was re-read directly in the source by the reviewer.
4. Kernel-checked new theorems (all compiled, standard axioms), to be integrated as README rounds 236+:
   - `Dedekind4` (scratch `verify/Dedekind4.lean`, to become `src/WeilDedekind.lean`): the Weil form of `ζ_{ℚ(i)} = ζ·L(s,χ₋₄)` on twin boxes, `2·Q_ζ + Q_{χ₋₄}`, as one `TwinLandau.TwinData` on the sum of the two zero index types; `RH ∧ GRH(χ₋₄) ⟺ 2Q_ζ(twin λ) + Q_{χ₋₄}(twin λ) ≥ 0 ∀ λ ≥ 0`, graded version, subexponential version (§4, finding F1).
   - `TwinKV` (scratch `verify/TwinKV.lean`, to become `external/pnt/TwinKV.lean`): `TwinLandau.Q_ge_of_rates` (per-pole rates) and `twins_lower_KV`: `∃ C, A > 0, ∀ λ ≥ 1, Q_ζ(twin (box 1) λ) ≥ −C·exp((1 − A/f_KV(e^{8λ}))·λ)`, the Korobov–Vinogradov region turned into an unconditional lower bound on the twin form (finding F2).
   - `PolyaFix` (scratch `verify/Polya.lean`, compiled clean): the hypothesis of `PsiOmega.rh_of_polya` is refutable (`polya_hyp_false`), and a non-vacuous `rh_of_polya'` with hypothesis `∀ x ≥ 2, L(x) ≤ 0` (finding F3).
5. Repo edits applied (rounds 236–239 in README.md): `src/WeilDedekind.lean` (F1), `external/pnt/TwinKV.lean` (F2, added to `external/pnt/build.sh`), `src/MertensOmega.lean` (F3: `polya_hyp_false`, `rh_of_polya` restated from `x ≥ 2`), `src/GapBound.lean` + `src/CosTrunc.lean` (F4: `simple_of_trunc_gap`/`simple_of_cos_gap` restated with `Lam2GeT a (T K) (lam a + γ)`, `Lam2GeT.anti`, the old forms kept as `*_of_forall` corollaries). The rebuild chain (pilot → pnt → zeta23) is running in the background (first attempt failed on a misplaced `set_option … in` in `VinoKV.lean`, fixed); the remaining 77 reading chunks were relaunched with Opus readers (six workflows, per the owner's instruction) to finish coverage without spending the Fable allowance. Round 241 candidates compiled as scratch: `pinned_unconditional_zero` (clean); the explicit-shape `twins_lower_KV'` awaits the `TwinKV` olean. Round 240 (warning cleanup, 21 pilot + 6 pnt sites, README entry written) is applied in the sources but not yet rebuilt: after the running build, run `./build.sh` again (GlobalTeeth/ExpSum/Vino/KaiserIBP chains recompile), then `external/pnt/build.sh`, check both logs for `warning:` and `error`, then commit and push.
6. Notes sections written: §2 dependency map, §3 named hypotheses (+ dead code from the compiled graph), §4 findings F1–F4, §5 received wisdom, §6 open conjectures, §8 coverage. Pending small round 241: `Unconditional.pinned_unconditional` concludes `(ĝ x).re = 0`; with `ghatC_im_eq_zero hev hint x` (Unconditional.lean:229, same hypotheses) the docstring's "real zero of ĝ" is one `Complex.ext` away — add the corollary after the rounds 236–240 commit (it recompiles the whole Weil chain).
7. Not yet done: the cross-cutting lens pass and adversarial-verification workflow (sub-agents unavailable until the session limit resets); integration of the above as rounds 236+ with README updates and the three builds; the remaining findings in §5 need Lean where marked.

How to resume: the built Mathlib is at `$SCRATCH/mathlib4` (commit in `MATHLIB_REV`), the pilot oleans are in `build/`. Compile a scratch file with
`cd $SCRATCH/mathlib4 && LEAN_PATH="$(lake env printenv LEAN_PATH):<pilot>/build" lean <file>`.
`external/pnt` modules and `Zeta23`/`SlogZeta` modules cannot be imported together (§2.3), nor `ParityRelax`/`ParityCert` with `WeilLandau` or `Concave`.

## 1. Baseline reproduction

- Toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `0f64d30a9a4593b3ae50375b960a5cf7f0845606`, `lake exe cache get`.
- `./build.sh`: 153 files compiled (906 s on this machine). `cat src/*.lean | grep -c "^#print axioms"` = 829; all 829 lines print `[propext, Classical.choice, Quot.sound]`; no `sorry`, no `axiom`.
- `external/pnt/build.sh`: 19 PNT+ files at 650d312 with `pnt_port.patch`, 12 layer files; the 15 printed axiom lines are clean (one is PNT+'s own `StrongPNT`, printed as `[propext, choice, Quot.sound]`).
- `external/zeta23/build.sh`: 50 zeta23 files at fbdc36b plus `SlogZeta.lean`; 10 clean axiom lines.
- **Discrepancy (NOVEL, minor):** README line 10 says "The build prints no warnings." The pilot build prints 21 linter-warning lines from eight files: `GlobalTeeth.lean` (100, 138 ×2, 202, 294, 305, 321, 365, 387), `ExpSum.lean:202`, `VinoBad.lean:167`, `ExpSum8.lean:100`, `ExpSum10.lean:41`, `VinoFam.lean:162` (×2), `VinoKV.lean` (46, 120 ×2, 184, 360), `KaiserIBP.lean:151` (deprecated names, unused simp arguments and variables, unnecessary `<;>`, `haveI`, unreachable tactics, the exponentiation threshold). The pnt layer prints warnings from its own files too: `Landau.lean` (243 ×2, 304, 1018, 1222), `KVBridge.lean:140`. None affects soundness. Bearing on RH: none.

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
80 Prop-valued definitions (`def`/`structure … : Prop`) exist across the three layers. Most are input *classes* (`Probe`, `SProbe`, `Par`, `Setup`, `ESupp`, `Orb`, `Hyp`, `Lam2GeT`, `TruncDense`, …) or are discharged in Lean (`WeilExplicit` by round 158, `DensityXi`/`ZeroFreeXi`/`DetectHyp` by round 235, `GoodChar` for `χ₋₃, χ₋₄, χ₋₈`, `LinBound`, `PoleAt`, `IsReal`, `JacobiEig`, …). The Prop-valued **named inputs that no Lean theorem proves** (checked by grepping every `theorem … : Name` and instance form in `src/`, `external/pnt/`):

| named input | defined | assumed by | status |
|---|---|---|---|
| `Cert14` | `src/PoleRelax.lean:465` | `weilQ_ge_pole`, `weilQg_ge_all` | arb certificate checked outside Lean (README round 4128 ff.) — ACKNOWLEDGED |
| `CertE`, `CertO` | `src/ParityCert.lean:66,89` | `weilQ_ge_E`, `weilQ_ge_O`, `weilQg_ge_both` | numerical certificates — ACKNOWLEDGED |
| `CertP`, `CertP3` | `src/PrimeRelax.lean:60`, `src/PrimeRelax3.lean:35` | `weilQ_ge_prime`, `weilQ_ge_prime3` | numerical certificates — ACKNOWLEDGED |
| `Round47Certs` | `src/SimpleCover.lean:180` | `simpleGround_le_1035` | "the fourteen inequalities, as a named hypothesis" (README line 1739) — ACKNOWLEDGED |
| `EnergyGap` | `src/GapCriterion.lean:80` | `simpleGround_of_gap` | open (CCM simplicity) — ACKNOWLEDGED (GLOSSARY "open step") |
| `KVInput` | `external/pnt/Rung3.lean:26` | `rung3_of_region` | superseded by `KVBridge.rung3_kv`, which does not go through `KVInput` — harmless |
| `HypD` | `src/Roadmap.lean:138` | `finite_advance` | the roadmap's item D, open — ACKNOWLEDGED |
| `DFamW` | `src/Limit.lean:239` | `rh_of_D_and_realRooted`, `hypConv_of_D`, `pairing_of_D`, … | the dodging-D family, open — ACKNOWLEDGED |

The full table (all 80, with counts of assuming and concluding theorems) is in the scratch file `named_hyps.md`; nothing in it is a hidden RH-strength input: every conditional headline theorem names its input in its signature, and the unconditional ones (`rh_of_weil_twins`, `weil_twins_rate`, `short_primes`, `density_unconditional`, `PNT_KV`, `lam_prefactor_KV`, the new `twins_lower_KV`) take none.

### 3.1 Dead code confirmed from the compiled dependency graph (NOVEL; round 218 removed dead code but these remain)
Zero users in the compiled environment (`users.json`): `Commute.bilQ_deriv2` (and the chain `xcorr_deriv2 → bil0_deriv2 → poleR_deriv2 → bilQ_deriv2` whose only users are each other), `Uniqueness.groundState_unique_of_gap` and `lamPerp` (only used by it), `Uniqueness.lam_bdd`, `BallTower.zeta_from_primes`, `ballVol_eq_volume`, `completing_factor_unique`, `sphereArea_lt_seven`, `TwinLandau.summable_hk`, `ToneHyperbola.hasDerivAt_Kq`, `boost_mul`, `multiplier_deriv`; before round 236 also `AngularFamily.rh_of_member_zero` and `member_zero_eq`. Headline results are allowed to be tips; the `Commute` chain (~100 lines) and `lamPerp`/`groundState_unique_of_gap`/`lam_bdd` are scaffolding that the file headers themselves call superseded (Commute.lean lines 14–15: Theorem C is proved by the H² route). Effort: trivial. Bearing on RH: none.

### 3.2 Duplicate definitions of the same object (missing connections)
- **Zero-free predicates, three of them.** `ShortPrimes.ZeroFreeXi α` (width `Az/(log T)^α` on the `Ξ`-zero family `ZeroIdx (sqF Xi)`), PNT+'s `ZetaZeroFreeGenProp n` (`ZetaBounds.lean:2962`, same width on `ζ`'s zeros, `|t| > 3`), and the conjunct of `Rung3.KVInput`. Two proofs of the Korobov–Vinogradov-class region coexist: `KVBridge.zeroFree_kv : 2/3 < n₁ → ZetaZeroFreeGenProp n₁` (round 214, PNT+'s Landau machinery) and `LandauKV.zeroFree_KV` (round 215, full `(log log)^{1/3}` factor). Both are ACKNOWLEDGED in the README; what is missing is the three-line bridge `ZetaZeroFreeGenProp α → ZeroFreeXi α` (through `zeta_rhoXi`, exactly as `ShortKV.zeroFreeXi_KV` bridges `abs_im_tau_le`). `zeroFreeXi_KV` proves only `ZeroFreeXi (3/4)`; `zeroFree_kv` would give every `α > 2/3`. No consequence for `θ` (which depends on `A` alone). NOVEL, trivial effort, no bearing.
- **Zero families.** `ZIdx = Σ w : NontrivialZero, Fin (zeroMult w)` (Mathlib's zeros with multiplicity), `Bool × ZeroIdx (sqF Xi)` (the `Ξ` family through `rhoXi`), joined by `zetaEquiv` (WeilZeta.lean:239); for `L(s,χ)` only the `ZeroIdx (sqF (XiC χ))` family exists — no `Σ`-family and no equivalence, which is why round 236 needs the factor 2. `zeta23` has its own zero counting through `Zeta23.RvM` (Riemann–von Mangoldt) and PNT+ none. Local counts: `ZeroLocal.card_local_le` (pilot, from round 164's zero weight) and zeta23's `N(t, t+1] ≤ A₀ log(|t|+3)` — same statement class, never compared (layer clash).
- **Explicit formulas.** `WeilExplicit zetaZeroFamily h hR` (ζ) and the `weilRHSC`/`QC_hasSum` route (χ) are separate developments with the same skeleton (Hadamard + `LamG` log-derivative); `TwinLandau` abstracts only the Landau step. A parametric explicit formula over any `GoodChar`-like family (with ζ as the trivial character) would remove ~600 lines (`WeilChi.lean` is 733 lines against `WeilAssemble.lean`'s 629). Effort: large; bearing: none.
- **Name-level duplicates** (confirmed by reading): `Pilot1ca.cw`, `Pilot1ca.tail_W` (§2.3); `BinetProof.bose_le'` vs `Exterior.bose_le`; `MollId.natCast_cpow_neg` / `ExpSum.cpow_phase` / `Pilot1ca.cpow_pos_real`; `Compactness.hdist` vs `GroundStateExists.norm_toLp_sub_sq` (card claims, not re-read).

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

## 5b. Substitution matrix (parametric theorems × instances)

| parametric theorem (file) | parameter | instances in the stack | sharper input available? |
|---|---|---|---|
| `TwinLandau.abs_re_le`, `rate_iff`, `Q_ge` (TwinLandau.lean) | pole family `P`, weights `c`, weight function `G`, form `Q` | `twinData_zeta` (ζ), `twinData_chi` (`L(s,χ)`, `GoodChar χ`), **`twinData_K` (ζ·L(χ₋₄), round 236)** | any product of `GoodChar` L-functions and ζ (same proof); Dedekind zeta of any real quadratic field is the next instance |
| `TwinLandau.Q_ge_of_rates` (round 237) | rate per pole `r q` | ζ with the KV rates | a wider zero-free region, if one existed |
| `LandauLaplace.landau_abscissa` (LandauLaplace.lean:338) | positive measure, phase, transform | `TwinLandau` (Laplace in λ), `PsiOmega.zeta_ne_zero_of_mellin` (Mellin in `x`), `LSeriesLandau` (Dirichlet series) | — |
| `HadamardW` genus-0 factorisation (Hadamard.lean) | entire `F` of order `< 1` in `w = t²` | `sqF ĝ` (curvature sum rule), `sqF Ξ`, `sqF (XiC χ)` | — |
| `weilExplicit_zeta` (WeilZeta.lean) | strip test `h` | box twins (`WeilLandau`), Kaiser probes, `PhiA`, the short-interval `2cos(Lz)ĝ_J²` (`ShortWeil`) | — |
| `arch_termQ` (ArchShift.lean:218) | digamma shift `q ≥ ¼` | `q = ¼` (ζ), `q_χ ∈ {¼, ¾}` (`WeilChiBridge`/`WeilChiDensity`) | a `Γ_ℂ` factor is the sum of two instances (Dedekind case) — not stated |
| `ShortPrimes.short_primes_of_density` | `DensityXi A B`, `ZeroFreeXi α` (`α < 1`) | `A = 4(1+δ)`, `B = 11` (`DetectEM`), `α = 3/4` (`ShortKV`) | `A`: none in the stack (see §6); `α`: `2/3 + ε` is what `zeroFree_KV` actually gives (the `3/4` is slack, harmless) |
| `DensityAsym.density_of_detect` | `DetectHyp δ` | `DetectEM.detectHyp` via Euler–Maclaurin | a subconvexity input would lower `A` (see §5, §6) |
| `DirMean.mean_value` | Hilbert-inequality constant | crude `8P(1 + log P)` | zeta23's `mv_hilbert` gives `4·C_MV·P` (no log) — blocked by the layer clash (§2.3); gain is one log power in `B` |
| `KaiserSplit.lam_le_split` (round 234) | `κ₁` bounding the zeros up to `2e^{40a}` | `κ₁ = e^{a − 2aA/f}` (`KaiserKV`) | same region as `TwinKV`; the two rounds are the same substitution in two forms |
| `PsiOmega.zeta_ne_zero_of_mellin` | coefficient sequence, transform | `ψ`, Mertens `M`, Liouville `L`, `ψ(x;χ)` races | — |
| `Concave.realRooted_of_concaveOn` | even concave `g ≥ 0` | boxes, parabola, sliver profiles in the certificate rounds | — |

## 6. Killed ideas
- **Feeding zeta23's `mv_hilbert` into `DirMean.mean_value`** (README section-5 lead): the substitution `(b − a + 8P(1 + log P)) → (b − a + 4 C_MV P)` is straightforward (the spacing is `|log j − log j'| ≥ |j − j'|/(2P)`), but it cannot reach `DetectEM` because the pnt and zeta23 layers cannot be imported together (§2.3), and the gain is one log power in `B = 11`, which changes no exponent. Not implemented.
- **Ingham's exponent from the present detection step**: see §5.
- **`GRHMemberZero ← RH ∧ GRH(χ₋₄)` inside the new file**: needs the off-strip zero classification for `L(s,χ₋₄)`; left as PAPER PROOF (the useful direction is compiled).

## 6. Open conjectures: what the stack proves, and the exact missing Prop

All statements below are quoted from the compiled sources; "missing" means no theorem in the three layers has the Prop as conclusion.

**RH.** Mathlib's `RiemannHypothesis`. Equivalences in the stack (all KERNEL-CHECKED, no named input):
- `Pilot1ca.rh_iff_twins_subexp : RiemannHypothesis ↔ ∀ σ > 0, ∃ C, ∀ l ≥ 0, −(C·exp(σl)) ≤ weilQ (l + 1) (twin (box 1) l)` (WeilLandau.lean:173); `rh_of_weil_twins` (positivity of the twin form on one-parameter family suffices); `weil_criterion_zeta` (both directions, all probes).
- Graded: `weil_twins_rate` — the exponential rate of the negative part is `2Θ − 1`.
- What is proved unconditionally about the rate: `TwinKV.twins_lower_KV` (round 237): rate `1 − A/f(e^{8λ})`, i.e. `Θ ≤ 1` with the KV margin. The exact missing Prop for RH in this language is `∃ C, ∀ l ≥ 0, −C ≤ weilQ (l + 1) (twin (box 1) l)` (the case `σ = 0`), and for any zero-free strip `Re ρ ≤ 1 − η`: `∃ C, ∀ l ≥ 0, −C exp((1 − 2η) l) ≤ …`. No narrowing beyond KV is available: by `weil_twins_rate` any bound `e^{σλ}`, `σ < 1`, *is* a zero-free strip.
- Other RH-equivalents in the stack: `rh_of_dodging` (Curvature.lean:86, needs `DFamW`/dodging D + real-rootedness — the roadmap's open items), `rh_of_liouville_bound` (`εL(x) ≤ c√x`), `rh_of_polya` (now non-vacuous, round 238), `rh_of_member_zero`.
- Negative index results (rounds 229–232): the number of negative directions of `Q` equals the number of off-line zero quadruples — RH ⟺ `Q` positive semidefinite, with no finiteness hypothesis.

**GRH for real characters.** `PsiOmega.grh_iff_twins (hS : ∀ σ ∈ (0,1), L(χ,σ) ≠ 0) : GRH χ ↔ ∀ l ≥ 0, 0 ≤ QC χ (l + 1) (twin (box 1) l)` for every `GoodChar χ`; instances `χ₋₃, χ₋₄, χ₋₈` with `hS` discharged from nonnegative partial sums. The hypothesis `hS` (no real zero in `(0,1)`, i.e. no Siegel zero for that `χ`) is the only extra input, and it is proved for the three instances only. Missing Prop for a general primitive real `χ`: `∀ σ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0` (Siegel-zero exclusion), which the stack does not attempt; `LFunction_ne_zero_of_sums_nonneg` proves it from `∀ x, 0 ≤ Σ_{n≤x} χ(n)`, which holds for the three characters and fails in general.
- New (round 236): `RH ∧ GRH(χ₋₄) ↔ ∀ l ≥ 0, 0 ≤ 2·weilQ … + QC chi4 …`.

**Zero density.** `DetectEM.density_unconditional (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/4) : DensityXi (4(1 + δ)) 11` with `DensityXi A B := ∃ C, ∀ σ T, ½ ≤ σ → σ ≤ 1 → 2 ≤ T → NX σ T ≤ C T^{A(1−σ)} (log T)^B` (ShortPrimes.lean:28; `NX` counts zeros of `Ξ` with `|Re τ| ≤ T`, `|Im τ| ≥ σ − ½`). This is Carlson/Chudakov level (`sup A = 4`). Density hypothesis `A = 2`: missing. Ingham's `A(σ) = 3/(2−σ)`: missing; the exact missing ingredient is a mean-value/large-values input with a power saving in the detection step: `∃ c < ½, ζ(½ + it) = O(|t|^c)` (van der Corput `c = 1/4`, Weyl `c = 1/6`), which no layer has — every pointwise bound on `ζ` in the stack is Euler–Maclaurin (`PNT+ ZetaBnd_aux1`, exponent ½) or the Vinogradov region near `σ = 1`.

**Lindelöf.** Nothing: no subconvexity bound of any strength is in the three layers (checked by grepping for `riemannZeta` growth theorems: only `ZetaBnd_aux1`-type `|t|^{1−σ}` bounds and the KV-region bounds near `σ = 1`). Missing Prop: `∀ ε > 0, (fun t => riemannZeta (1/2 + t I)) =O[atTop] fun t => |t|^ε`.

**Zero-free regions.** `LandauKV.zeroFree_KV : ∃ A > 0, ∀ σ t, e³ ≤ |t| → 1 − A/((log|t|)^{2/3}(log log|t|)^{1/3}) ≤ σ → ζ(σ + it) ≠ 0` — Korobov–Vinogradov, unconditional, non-explicit `A`. Explicit `A` (Ford's `1/57.54`): missing, and the README (round 234) records the decision not to pursue it.

**Primes in short intervals.** `DetectEM.short_primes (hθ : 3/4 < θ) : ∀ᶠ y in atTop, ∃ p, p.Prime ∧ y < p ∧ p ≤ y + y^θ`; the parametric form `ShortPrimes.short_primes_of_density (hden : DensityXi A B) (hzf : ZeroFreeXi α) … (hθA : 1 − 1/A < θ)`. Every improvement of `θ` is exactly an improvement of `A`: `θ > 2/3` needs `sup A ≤ 3`, `θ > 5/8` needs `8/3`, `θ > 7/12` (Huxley) needs `12/5`. The stack's `sup A = 4(1+δ)` cannot be lowered without a new mean-value input (see Zero density).

**PNT error term.** `PNTKV.PNT_KV : ∃ c > 0, (ψ − id) =O[atTop] fun x => x·exp(−c (log x)^{3/5}/(log log x)^{1/5})` — the Korobov–Vinogradov error term, unconditional.

**Prime races / oscillation.** `PsiOmega.psi_omega_half (hθ : 0 < θ) (hθ2 : θ < 1/2) (c X) : …` (unconditional `Ω±(x^θ)` for `θ < ½` from `exists_zero_re_ge_half`), `mertens_omega_half`, races mod 3/4/8 (rounds 222–224). Missing: `Ω(x^{1/2})` itself (needs a zero *on* `Re = ½` with the Landau argument at the real singularity, which `PoleAt`-at-a-zero does not capture — see the killed `liouville_omega` idea in §6 of the reading cards).

**`S(T)`.** zeta23's `SlogZeta` gives `S(t) = O(log t)` (round 228) and `N(t, t+1] ≤ A₀ log(|t| + 3)`; the pilot has its own local count `ZeroLocal.card_local_le` from round 164's zero weight. These two zero-counting routes are never compared in Lean (the layers cannot be imported together, §2.3).

**Effective/explicit questions.** Every constant of the Vinogradov layer, the KV region, the density theorem and `twins_lower_KV` is existential. The stack contains no explicit numerical constant on the analytic side except in the certificate rounds (Weil positivity at small support). Missing Prop for any explicit statement: an explicit `A` in `zeroFree_KV` or an explicit `C` in `DensityXi`.

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
