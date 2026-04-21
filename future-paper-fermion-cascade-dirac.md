# Future Paper — The Discrete Dirac Operator on the Cascade Lattice

## Purpose

Close the single non-derived link in the fermion obstruction factor of Part IVb Theorem 2.2: the conjectured **Clifford absorption** of $\Gamma(\tfrac{1}{2}) = \sqrt{\pi}$ on Dirac-layer spheres.

A cascade-native proof would take the last remaining step of Part IVb's fermion-mass derivation from "asserted on physical grounds" to "forced by the cascade action", closing SP-31 structurally and every charged-fermion mass, `C = alpha_s/(2 sqrt(pi))`, and the entire geometric-topological factorisation that rests on it.

## Current state (as of commit `847a9dd` on `claude/audit-cleanup`)

Part IVb Theorem `thm:sp31-decomposition` factorises the fermion-to-scalar propagator ratio as

```
1/(2 sqrt(pi)) = (1/chi) * (1/Gamma(1/2))
```

- **Chirality half** `1/chi = 1/2`: **derived** from Theorem `thm:chirality-factorisation` (chirality-basin filtering on even-sphere Dirac layers, via the $\mathbb{Z}_2$ grading of the spinor bundle).
- **Jacobian half** `1/sqrt(pi) = 1/Gamma(1/2)`: **conjectured** via Clifford absorption on the cascade lattice; the scalar side's $\sqrt{\pi}$ is identified as the $t^{-1/2}$ Jacobian of the $t = x^2$ substitution in the axial Beta integral.

The decomposition narrows the residual problem from "why $1/(2\sqrt{\pi})$" to the single, better-posed question: **why does the cascade's fermion action not receive the scalar's axial Jacobian?**

## The computational barrier (findings from the dig)

Closing the conjecture rigorously is a research-scale computation. Three sub-problems:

### 1. The scalar side is a 1D axial integral

The cascade's scalar lapse

```
N(d) = V_d / V_{d-1} = integral_{-1}^{1} (1 - x^2)^{(d-1)/2} dx
     = B(1/2, (d+1)/2) = sqrt(pi) * R(d)
```

is a one-dimensional integral over the axial coordinate $x \in [-1, 1]$. Under $t = x^2$, $dx = dt / (2\sqrt{t})$, producing the $t^{-1/2}$ Jacobian. This Jacobian **is** the $\sqrt{\pi}$ factor, via the first Gamma-function half-integer argument in $B(1/2, \cdot)$.

### 2. The fermion side lives on the full sphere, not on an axial projection

The Dirac operator acts on the spinor bundle of $S^{d-1}$, which is the full even-dimensional sphere at Dirac layers. There is no canonical "axial Beta integral" for the fermion — the natural Dirac computation is a spectral decomposition (spinor spherical harmonics / Camporesi-Higuchi expansion), not a projection onto a 1D axial coordinate.

Concretely, on round $S^{2n}$ the Dirac eigenvalues are $\lambda_k = \pm(k + n)$ for $k \geq 0$, with multiplicity $D_k = 2^{n-1} \cdot (\text{Camporesi-Higuchi formula})$. The Green's function at coincident points is the regularised spectral trace

```
G_D(x, x) = sum_k D_k / lambda_k
```

which diverges and needs zeta-function regularisation (Hurwitz zeta at $s = 1$).

### 3. Bridging the two

A rigorous Clifford-absorption proof needs a **bridge** between these two frameworks: the cascade's 1D axial slicing for scalars, and the full-sphere Dirac operator for fermions. Specifically, the bridge would:

- Construct a **discrete Dirac operator** $D_{\text{lat}}$ on the cascade lattice, with adjacent layers coupled via a spin connection lifted from the slicing map $B^d \to B^{d-1}$.
- Show $D_{\text{lat}}$'s Green's function at Dirac layer $d$ equals $R(d)$ (not $\sqrt{\pi} R(d)$).
- Verify via zeta regularisation on each $S^{d-1}$ that the $\sqrt{\pi}$ does not appear in the spectral trace.
- Confirm that cumulative cascade descent reproduces the observed fermion masses.

## Proposed paper outline

**Title (candidate).** *The Discrete Dirac Operator on the Cascade Lattice and the Fermion Obstruction Factor*

**Target length.** ~30–40 pages.

**Dependencies.** Spectral zeta-function methods on round spheres (Camporesi–Higuchi 1996; Trautman 1993; Bär 1996 for Dirac spectrum on $S^{2n}$). Standard spin-structure machinery on manifolds with boundary. No new cascade axioms.

**Outline.**

1. **Motivation.** Part IVb's Theorem 2.2 decomposition; the Clifford-absorption conjecture; what a cascade-internal proof would achieve.

2. **The scalar side.** Re-derive the $\sqrt{\pi}$ factor in $N(d) = \sqrt{\pi}\, R(d)$ as the axial-Jacobian $\Gamma(1/2)$ in $B(1/2, (d+1)/2)$. Identify the specific mechanism ($t = x^2$ substitution on the 1D axial coordinate).

3. **The round-sphere Dirac operator.** Standard spectral decomposition of $\slashed{D}$ on $S^{2n}$. Zeta-regularised Green's function at coincident points. Closed-form expression in terms of Barnes $G$-functions and Hurwitz zeta values.

4. **The cascade-lattice Dirac operator $D_{\text{lat}}$.** Definition as a discrete operator on layer-indexed spinor sections with a slicing-map-induced spin connection. Unitarity, self-adjointness, and locality properties.

5. **Clifford absorption theorem.** The main result: $D_{\text{lat}}$'s Green's function at Dirac layer $d$ equals $R(d)$ up to chirality halving, with the $\sqrt{\pi}$ absent. The proof factorises as:
   - (a) scalar Green's function on $D_{\text{lat}}$'s bosonic sector reproduces $\sqrt{\pi} R(d)$ (consistency with Part IVb);
   - (b) chirality projection + zeta regularisation yield $R(d) / \chi$ for the fermionic sector.

6. **Numerical verification.** Compute the regularised spectral trace explicitly at Dirac layers $d = 5, 13, 21, 29$ and check against $R(d)/2$ to at least 4 significant figures. Cross-check against observed charged-fermion mass ratios.

7. **Connection to Part IVb.** Show the proof closes SP-31 in the audit sense: the decomposition of Theorem 2.2 becomes fully derived. Consequences for each charged-fermion mass and for $C = \alpha_s / (2\sqrt{\pi})$.

8. **Remaining questions.** Extension to non-Dirac layers; the geometric-mean mixing rule for CKM/PMNS (SP-35 residual); the source-selection categorical derivation (SP-36 residual).

## Expected difficulty and timeline

- **Section 3 (round-sphere Dirac spectrum):** well-established mathematics. Mostly citation + careful setup. ~1 week.
- **Section 4 ($D_{\text{lat}}$ construction):** novel but uses standard discrete-differential-geometry machinery. ~2–4 weeks.
- **Section 5 (Clifford absorption theorem):** the hard core. The spectral argument is the main technical content. ~4–8 weeks.
- **Section 6 (numerical verification):** parallel to Section 5. ~1 week to implement, iteratively improved as Section 5 refines the formulas. Can serve as a sanity check at each stage.
- **Writing and revision:** ~4 weeks.

**Total:** ~3–5 months of focused work, assuming Section 5's spectral argument goes through. If it reveals an inconsistency, the timeline extends substantially (the conjecture might need reformulation, or a different bridge between axial and full-sphere frameworks).

## Alternative paths

If the full theorem is intractable, two weaker results would still advance SP-31:

**(A) Numerical verification only.** Compute the regularised Dirac spectral trace at Dirac layers 5, 13, 21, 29 and demonstrate numerical equality with $R(d)/2$. This would not prove the conjecture but would convert it from "plausible heuristic" to "numerically validated ansatz at every cascade-relevant Dirac layer". A single-session tool could deliver this — roughly `tools/fermion_dirac_spectral_zeta.py` — and it would strongly constrain any future rigorous proof.

**(B) Partial theorem with an ansatz.** Prove that the cascade-lattice Dirac operator's Green's function equals $R(d)$ **given** a specific choice of spin connection on the slicing map. The paper then reduces the conjecture to "this specific connection is the canonical one", which is a cleaner, narrower problem than the original.

Either alternative would count as genuine progress. Alternative (A) is the cheapest ~1-day sanity check; alternative (B) is a ~1-month partial result that could be publishable on its own.

## Status update: alternative (A) has been run — naive formulation falsified

Alternative (A)'s sanity check was implemented as `tools/fermion_dirac_spectral_zeta.py` and run on all four cascade Dirac layers. The naive formulation of the conjecture — "fermion lapse = regularised Dirac spectral zeta on boundary sphere $S^{2n}$" — **does not hold**.

### What was computed

The regularised Dirac spectral zeta on round $S^{2n}$, per chirality:

$$\zeta_D^+(s) = \sum_{k=0}^{\infty} \frac{D_k}{(k+n)^s}, \quad D_k = 2^{n-1}\binom{2n+k-1}{k}$$

evaluated at $s=1$ via Hurwitz-zeta analytic continuation (`mpmath.zeta` at 50 decimal digits, with polynomial expansion of $D_k$ in $m = k+n$ giving a closed-form linear combination of $\zeta(-2j-1, n)$ terms).

### The numbers

| $d$ | $n$ | $\zeta_D^+(1)$ | $\lvert\zeta_D\rvert(1)$ | $R(d)/2$ | ratio $\lvert\zeta_D\rvert(1)/(R(d)/2)$ |
|---|---|---|---|---|---|
| 5  | 2  | $1/6 = 0.1667$    | $1/3 = 0.3333$ | $8/(15\sqrt\pi) = 0.3009$ | **1.108** |
| 13 | 6  | $5.77\times 10^{-3}$ | $1.15\times 10^{-2}$ | $0.1924$ | $0.060$ |
| 21 | 10 | $2.77\times 10^{-4}$ | $5.54\times 10^{-4}$ | $0.1525$ | $0.00364$ |
| 29 | 14 | $1.46\times 10^{-5}$ | $2.92\times 10^{-5}$ | $0.1302$ | $0.000224$ |

The regularised spectral zeta decays **exponentially** in $d$ (ratios drop by ~17× per Bott period of 8 in $d$), while $R(d) \sim \sqrt{2/d}$ decays **polynomially**. The two are not proportional — even allowing for an overall multiplicative constant, no $d$-independent factor recovers the cascade's target.

The $d=5$ ratio of 1.108 is close to 1 and might suggest a small-$n$ correspondence, but the rapid falloff at higher $d$ shows this is coincidental rather than structural.

### What this tells us about Part IVc

The tool's negative result meaningfully **constrains the future paper** before any of Section 5's work has been written:

1. **Section 4 cannot inherit the round-sphere Dirac spectrum.** The $D_{\text{lat}}$ construction must give a Green's function that differs from the round-sphere Dirac operator's spectral trace. A naive "one Dirac operator per layer, compose across the cascade" construction is ruled out.

2. **A slicing-map-induced spin connection with layer-wise volumetric rescaling is required.** The scaling factor must grow fast enough with $d$ to compensate for the spectral zeta's exponential decay — plausibly a factor of order $\Omega_{2n}$ (sphere volume, growing super-exponentially) or $R(d)/\zeta_D(1)$ fitted layer-by-layer, with the question being whether any such factor has a principled cascade-internal origin.

3. **Alternative (A) is closed as negative.** The cheapest validation path is now known to fail. Remaining paths: alternative (B) (partial theorem conditional on a specific spin-connection choice with the layer-wise rescaling above) or a reformulation of the conjecture itself.

4. **Reformulation candidates.** Three natural ones, in decreasing order of plausibility:
   - *(i) Boundary-dominance correction.* $\zeta_D(1) \cdot \Omega_{2n}$ or $\zeta_D(1) / V_{2n+1}$ might recover $R(d)$ after a volumetric factor. Worth computing as a follow-up.
   - *(ii) Cascade-lattice Dirac, not sphere Dirac.* The correct operator acts on layer-indexed spinor sections with discrete-difference coupling across layers — not on individual sphere sections per layer. Its spectrum lives in $\mathbb{R}$, not on any single sphere, and the "Green's function at layer $d$" involves a sum over cascade paths rather than a sphere spectral trace.
   - *(iii) Slicing-Jacobian fermion integral.* Rather than constructing a discrete Dirac operator, apply the scalar slicing integral machinery with a spinor measure that explicitly absorbs the $t^{-1/2}$ Jacobian. The fermion analogue of $B(1/2, (d+1)/2) = \sqrt\pi R(d)$ would then be $B(1, (d+1)/2) = R(d+1)$ or similar — which also doesn't match $R(d)$ but might with a chirality halving or a shifted argument.

5. **Timeline revision.** Section 6 is done in its alternative-A form (negative); Section 4 now has a well-defined open problem (construct a $D_{\text{lat}}$ whose spectrum is NOT the sphere Dirac spectrum); Section 5's spectral argument needs to be rewritten around whichever reformulation of (i)–(iii) proves tractable. Net: the $3$–$5$ month timeline is unchanged, but the work is now better-scoped — no time will be lost discovering that the round-sphere route fails.

### Reproducibility

The tool is deterministic (no randomness, no external data) and runs in under a second at 50 decimal digits. Rerunning on a different machine reproduces the ratios exactly. The negative result is robust to further precision increases.

Dependencies: `mpmath` only. No cascade-specific inputs; all quantities derived from the integer $d$ alone.

## The Wyler route: bounded symmetric domains and their Silov boundaries

The alternatives (i)–(iii) above are all reformulations of a naive sphere-Dirac approach. A more principled framework — and the one Part IVc should adopt — comes from Wyler's 1969 work on symmetric-space volume ratios ("L'espace symétrique du groupe des équations de Maxwell"). Wyler showed that physical coupling constants can arise as ratios of **bounded-symmetric-domain volumes** to their **Silov-boundary volumes**, using Hua Loo-Keng's explicit volume formulae for the four classical types of bounded symmetric domains (Hua 1963).

### Why this matters for the Clifford-absorption conjecture

The cascade's fermion lapse target $R(d)/\chi$ is, like Wyler's $\alpha^{-1}$, a specific **Gamma-function ratio**. Wyler's formalism supplies a natural home for such ratios: bounded symmetric domains have intrinsic complex/quaternionic/octonionic structure, and their Silov boundaries carry spin structures that are built into the geometry rather than imposed. The distinction between scalar $\sqrt{\pi}\,R(d)$ and fermion $R(d)/\chi$ should correspond, in Wyler's framework, to:

- **Scalar case**: the axial 1D Beta integral is the volume of a slice of the real unit ball $B^d = D_I$ (type I trivial). The $\sqrt{\pi}$ comes from the real-analytic Jacobian, exactly as in the current cascade derivation.
- **Fermion case**: the Dirac fermion lives on the **Silov boundary** of a bounded symmetric domain of type III ($\text{SU}(n,n)/\text{S}(\text{U}(n)\times\text{U}(n))$) or type IV ($\text{SO}(n,2)/\text{SO}(n)\times\text{SO}(2)$). The Silov boundary's volume is a Gamma-function ratio *without* the axial $\sqrt{\pi}$ — because the complex/real-form structure absorbs the Jacobian into the symmetric space's measure.

### Concrete research direction for Part IVc

The reformulation of Section 4 should proceed as follows:

1. **Identify the correct bounded symmetric domain $\mathcal{D}_d$ for each Dirac layer $d \in \{5, 13, 21, 29\}$.** The candidates are type III and type IV domains whose Silov boundaries are the Dirac-layer sphere $S^{d-1}$ equipped with its spin structure. For $d = 5$ the candidate is $\mathcal{D}_5 = \text{SO}(5,2)/\text{SO}(5)\times\text{SO}(2)$ (type IV, dimension 5); for higher Dirac layers the type III series $\mathcal{D}^{\rm III}_n = \text{SU}(n,n)/\text{S}(\text{U}(n)\times\text{U}(n))$ is a natural candidate.

2. **Compute $V(\mathcal{D}_d)$ and $V(\partial_S\mathcal{D}_d)$ using Hua's formulae.** The type IV domain of dimension $n$ has Bergman volume
   $$V(\mathcal{D}^{\rm IV}_n) = \frac{\pi^n}{n! \cdot (n-1)! \cdot 2^{n-1}}$$
   (up to conventions; see Hua 1963 for precise forms) and Silov boundary volume
   $$V(\partial_S\mathcal{D}^{\rm IV}_n) = \frac{2\pi^{n/2+1}}{\Gamma(n/2)}$$
   both of which are Gamma-function ratios of the form that naturally give $R(d)$ combinations.

3. **Prove that the ratio $V(\mathcal{D}_d)/V(\partial_S\mathcal{D}_d)$, or a specific power thereof, equals $R(d)/\chi$.** This is the cascade-Wyler version of the Clifford-absorption theorem: instead of trying to compute a discrete Dirac operator's Green's function from scratch, identify the cascade's fermion slicing integral with a specific volume ratio of an already-studied symmetric space. Hua's formulae make the computation tractable.

4. **Show that the cascade's Dirac-layer selection $d \in \{5, 13, 21, 29\}$ corresponds to a sequence of symmetric domains with a period-8 Bott structure.** This is a structural claim that should fall out of the symmetric-space classification: the Bott periodicity in the cascade's Dirac layer assignments should correspond to the periodicity in the spin structure of the symmetric domain's Silov boundary.

### What Part IVc actually needs

Under the Wyler route, the paper outline reshapes:

- **Old Section 3** (round-sphere Dirac spectrum via Camporesi–Higuchi): **demoted to Appendix A** (for completeness; the computed spectral zeta is not the cascade's fermion lapse, as alternative (A) established).
- **New Section 3** (bounded symmetric domains and Hua's volume formulae): cite Wyler 1969 and Hua 1963; state the volume/Silov-boundary formulae for types III and IV; identify the cascade's Dirac layers with specific domain parameters.
- **New Section 4** (cascade-Wyler construction): define $\mathcal{D}_d$ for each Dirac layer; state the conjectured identification $V(\mathcal{D}_d)/V(\partial_S\mathcal{D}_d) = (R(d)/\chi)^{\alpha_d}$ for some cascade-determined exponent $\alpha_d$.
- **New Section 5** (proof of the cascade-Wyler identification): the theorem's proof reduces to Gamma-function algebra on Hua's formulae. Tractable by comparison to the round-sphere Dirac approach.
- **New Section 6** (numerical verification): reimplement `tools/fermion_dirac_spectral_zeta.py` as `tools/cascade_wyler_volume_check.py`; verify the volume ratio identification numerically at all four Dirac layers to $\geq 8$ significant figures.

### Why this is genuinely cascade-native rather than another guess

Three structural matches that the round-sphere Dirac approach lacked:

- **Gamma-function volumes.** Bounded symmetric domains have closed-form Gamma-function volumes (Hua). The cascade's $R(d)$ is a Gamma-function ratio. The two frameworks share the same mathematical vocabulary, making the identification tractable rather than aspirational.
- **Intrinsic complex/spin structure.** The domains of types II, III, IV have built-in complex or quaternionic structure; their Silov boundaries carry spin bundles by construction. No need to separately impose a spin connection, as alternative (B) required.
- **Wyler's prior precedent.** Wyler derived $\alpha^{-1} \approx 137.036$ from symmetric-space volume ratios. Part IVb Open Question `oq:alpha-em-screening` proposes a cascade derivation of $1/\alpha_{\rm em} = 137.028$; if the cascade-Wyler construction in Part IVc closes the fermion-lapse problem, the same framework plausibly closes Open Question `oq:alpha-em-screening` in parallel. The two problems share geometric machinery.

### Expected difficulty

Lower than the original plan. Hua's volume formulae are explicit; the only task is identifying the correct domain for each Dirac layer and evaluating the ratio. Revised timeline:

- **Section 3 (symmetric-domain volumes):** ~2 weeks (literature review + setup).
- **Section 4 (cascade-Wyler construction):** ~3–4 weeks.
- **Section 5 (proof):** ~2–4 weeks if the identification is clean; 4–8 weeks if exponent fitting is needed.
- **Sections 6–8 (numerical verification + consequences + remaining questions):** ~2 weeks.
- **Writing:** ~2 weeks.

**Total: ~2–3 months**, down from the original 3–5. The Wyler route is more constrained than the round-sphere route (Hua's formulae are tighter), which makes the work faster rather than harder.

### References for this route

- A. Wyler, *L'espace symétrique du groupe des équations de Maxwell*, C. R. Acad. Sci. Paris **269** (1969), 743–745.
- A. Wyler, *Les groupes des potentiels de Coulomb et de Yukawa*, C. R. Acad. Sci. Paris **271** (1969), 186–188.
- L. K. Hua, *Harmonic Analysis of Functions of Several Complex Variables in the Classical Domains* (AMS, 1963).
- F. D. Smith Jr., *Calculation of $1/\alpha = 137.03608$*, various preprints 1986–2004 (cascade-adjacent: Smith attempts to close Wyler's framework into a complete derivation; his methods partially anticipate the cascade's Bott-periodic layer structure).
- Part IVb, Open Question `oq:alpha-em-screening` (the parallel problem that may close in the same framework).

## Dependencies on other open questions

- **Not blocking:** the cascade action principle of Part IVb Remark 4.8 already supplies the scalar sector; the fermion sector is the extension.
- **Blocking (if path B is taken):** the choice of spin connection on the cascade's slicing map is itself a cascade-structural question; a principled (rather than arbitrary) choice might require input from a categorical framework for cascade observables (SP-36's residual).
- **Parallel:** SP-35's geometric-mean mixing rule (for CKM/PMNS) may share machinery with the fermion-action approach; both involve off-diagonal cascade-lattice propagators between Dirac layers.

## Why it matters

Closing this derivation would move the cascade's charged-fermion mass spectrum from "seven precision predictions anchored to one asserted factor" to "seven precision predictions derived end-to-end from the cascade action". It would also make `C = alpha_s / (2 sqrt(pi))` a **theorem**, not a match.

In epistemic terms: the charged-fermion mass sector is currently the largest remaining "asserted pending cascade-action derivation" load in Part IVb. Closing it would leave the cascade's precision predictions free of any non-derived ingredients — the last major structural item after the audit's hardening pass.
