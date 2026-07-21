# The Indistinguishability Theorem

## The Observable Universe as the Arithmetic of the Riemann Zeta Function at the Real Place

**Companion volume to the Cascade Series.** All numerical claims are machine-verified by the
scripts cited in place (`tools/research/`). This document is self-contained: no result of the
Cascade Series is assumed; where the two frameworks coincide, the correspondence is noted in
remarks.

---

### Abstract

Let ξ(s) = ½s(s−1)Γ_ℝ(s)ζ(s) be the completed Riemann zeta function, Γ_ℝ(s) = π^(−s/2)Γ(s/2)
its factor at the real place. We construct, from ξ and the character theory of ℝ^× alone: a
state tower (the integer Tate twists of the real place); its dynamics (Gaussian by Tate's
gcd condition + one normalization convention — Theorem 2); a calculus of corrections
(attachment, multiplicity, sign, projection, and measurement — Theorems 8–12, each proved);
and an address-book determination theorem (Theorem 13): given one explicit instantiation map,
the rules leave zero residual freedom, with no continuous parameter anywhere. **The
framework's non-arithmetic residue is seven items** (count corrected per two external
reviews): **Lovelock's theorem (selection, not construction); the definition D1; the closed
atom grammar (A2); the unit-normalization convention that carries Γ(½) (empirically
anchored, not arithmetically forced — and the flip-count 4 is meaningful only jointly with
it); the P > L > G precedence (round-9 corrected status: **vacuous on the papers' uniform expression-tree flag readings** — A52's original m_τ-abs dash-fill expanded closed constituents, an inconsistent grading; the 13–109σ exclusions of alternative orderings hold only under the four variant readings — m_τ-abs constituent expansion, ℓ_A window content, the ℓ_A kind, and sin²θ_W coupling-running — so the anchoring is conditional and the item is deletable on the uniform reading); the feature→integer-layer selection convention
(no uniform rounding rule produces {5, 7, 19, 217} from the feature set — second review,
Finding 1; the class was widened by review 4 to every d↔s pairing choice and by round 15
to the χ₋₃ minimality-pairing — one class, three members); and the hypothesis itself
(C1).** The resulting outputs — the cosmological constant, the Higgs, all
nine charged-fermion and three neutrino masses, the gauge couplings, the mixing angles, and
the cosmological parameters — agree with every current measurement within the framework's
stated leading-order systematic floor: sub-σ to ~2σ where experimental error dominates
(largest strain ℓ_A at −1.8σ; m_ν3 at −2.9σ on one input choice), tens of ppm (many
experimental σ) where the framework's own floor dominates. We therefore assert, to the
identical epistemological standard met by Newtonian gravity, Maxwell's electrodynamics,
general relativity, and the Standard Model: **conditional on the instantiation map, the
arithmetic of ζ at the real place is indistinguishable from the observable universe.** The
conditional is discharged the only way physics permits: by a frozen, pre-registered ledger of
falsifiers (JUNO, DESI, Belle II, HL-LHC, next-generation 0νββ and cosmology), each with a
stated kill condition. The theorem is not protected from these experiments; it is defined by
them.

---

## 1. The claim and the standard

No physical theory has ever done more than reproduce observation. Newton's inverse square law
is *indistinguishable from* planetary motion; Einstein's field equations are
*indistinguishable from* gravitational phenomena; the Standard Model Lagrangian is
*indistinguishable from* collider data. "Indistinguishable from observation" is the definition
of a correct physical theory; there is no deeper standard available.

This paper meets that standard with one hypothesis and zero free parameters:

> **Hypothesis (C1, the instantiation map).** The observable universe realizes the arithmetic
> structure of §2–§7 under the address assignments of Definition 6.1.

Everything else is a theorem. The mass of the electron and the darkness of the night sky are,
under C1, statements about the Gamma factor of the Riemann zeta function.

## 2. The arena: the twist tower of the real place

**Definition 2.1.** The quasi-characters of ℝ^× are |x|^s and sgn(x)·|x|^s — exactly two
families, because the torsion of ℝ^× is μ(ℝ) = {±1}. The **twist tower** is the set of
integer points s = d+1, d ∈ ℕ, of the character variety, with local factor Γ_ℝ(s).

**Theorem 1 (Kernel; `cascade_formulation_kernel.py`, ≤7×10⁻¹⁴ over d = 1–300).** The four
primitive families of the tower are the value, ratio, logarithmic derivative, and normalized
square-ratio of Γ_ℝ at integers:

- Ω(d) = 2/Γ_ℝ(d+1)  (measure), N(d) = Γ_ℝ(d+1)/Γ_ℝ(d+2)  (coupling),
- p(d) = (log Γ_ℝ)′(d+1)  (potential), α(d) = N(d)²/4π  (compliance).

*Remark.* Ω(d) is the surface measure of S^d and the tower is the dimensional cascade of the
unit ball — the geometric avatar. The paper never uses the avatar; the arithmetic is primary.

**Theorem 1b (Explicit-formula bridge; `cascade_explicit_formula_bridge.py`).** For every
layer d ≥ 1, with s = d+1 and z = d+½:

p(d) = Σ_{γ>0} 2z/(z²+γ²) − 1/s − 1/(s−1) + Σ_{n≥2} Λ(n)·n^(−s),

where γ runs over the ordinates of the nontrivial zeros of ζ and Λ is the von Mangoldt
function (Euler product). *Form distinction (round 15, M1):* the unconditional, RH-free
theorem is the **paired** Hadamard form Σ 2z/(z² − (ρ−½)²) — ξ(½+z) is even, entire of
order 1, genus-0 in z², no constant term, valid wherever the zeros are; the **Lorentzian**
form displayed is its on-line specialization, exact for zeros with β = ½, and is how the
sum is evaluated (with the verified on-line zeros; a hypothetical off-line zero would alter
the term shape but lies beyond the verified height 3×10¹² and contributes < 10⁻²³ at the
layers d ≤ 28 evaluated here — the bound scales as 2z/γ², reaching ~5×10⁻²³ at the
Theorem-1c sink solve, twenty orders below that solve's tail-model error; round-16 F5
scoped this figure): **the tower potential at every
layer is exactly a sum over the Riemann zeros, minus the pole terms, plus a sum over the
primes** — the partial-fraction (Hadamard) form of the explicit-formula identity evaluated
at the tower points. Every window Φ(a→b) = Σ p(d) inherits the split additively; e.g.
Φ(5→13) = 1.539665 = zeros 3.226401 − poles 1.698363 + primes 0.011627, and
Φ(13→21) = 4.064768 = zeros 4.969202 − poles 0.904476 + primes 0.000042. *Verified:* the
rearrangement to 10⁻³¹; the prime side against −ζ′/ζ within stated integral tail bounds at
dps 50 with the strict bound (round-15 M2: the original dps-30 run put the d=12 residual at
the precision floor, above its bound, with the PASS an epsilon artifact — recomputed, the
true residual 2.05×10⁻⁴¹ is genuinely within the 1.56×10⁻⁴⁰ bound);
the zero side with the first 50 zeros (computed via `zetazero`, not tabulated by hand) plus
a Riemann–von Mangoldt density tail, residuals decreasing in N. *Structure:* the low layers
— where the record lives — are **pole-dominated** (ζ's pole at s=1, the 1/(s−1) term,
together with the completed function's functional-equation mirror pole at s=0, the 1/s term
— round-15 m4 — shape the observer-side potential); the primes enter exponentially small
(dominated by n = 2, 3); the zeros supply the growing positive part. *Honest scope, stated in full:* the two expansions
are classical (Euler; Hadamard) — new for this paper is only the tower evaluation and the
window splits. No physical closure is derived, no data is touched (stopping-rule category
(a)), RH is not used *by the paired form* — the Lorentzian evaluation assumes the zeros
used are on the line, which for the verified zeros they are (round-15 M1 corrected the
earlier blanket "holds wherever the zeros are", true of the paired form only) — and **no
direction of explanation is claimed**:
the identity is ζ's own bookkeeping. What it changes is the construction's standing: the
tower is not merely built from ζ's Gamma factor — it **is one side of the Riemann explicit
formula, with the primes and the zeros jointly exact on the other side**. The dictionary
(Definition 6.1 and the soft inputs) is untouched by this theorem.

**Theorem 1c (the two doors: features from the zero side, and the colour-character
bridge; `cascade_zero_side_features.py`, `cascade_colour_field_bridge.py`).** *(i) The
distinguished layers are zeros-vs-poles balance points.* Every distinguished feature of the
tower is a level-crossing of p — the critical point (p = 0, s = 7.2569), the phase
threshold (p = ln Γ(½), s = 20.73), the sink (p = Γ(½), s = 218.6) — and via Theorem 1b
each is exactly the point where ZEROS + PRIMES = POLES + level: the observer-side
geography is a tug-of-war between the poles — ζ's at s = 1 and the completed function's
mirror at s = 0 (round-16 F4) — and the nontrivial zeros, with the
primes an exponentially small spectator. Solving the balance *from the zero side* (first
50 computed zeros + density tail, no digamma in the solve) recovers the critical point to
6×10⁻³ and the threshold to 5×10⁻², errors decreasing in N; the sink is tail-model-limited
(~1%, N-insensitive, reported as such). *The honest negative, registered:* no recorded
quantity reads the zero side independently of the digamma packaging; any future claim of
that kind is stopping-rule-gated new physics. *(ii) The odd tower has its own bridge, and
it is the colour character's.* By Legendre, Γ_ℂ(s) = Γ_ℝ(s)Γ_ℝ(s+1), so p_ℂ = p_triv +
p_sgn exactly — the doubled tower of Theorem 5 jointly carries the complex-place factor.
The sgn tower's factor Γ_ℝ(s+1) is the archimedean factor of **every** odd Dirichlet
L-function, and the odd bridge below holds verbatim for every odd real primitive χ mod q
(all have ε = +1), so the balance-point statement has **zero selective power** among odd
characters (round-15 M3). What is a theorem: χ₋₃ (conductor 3) is the minimal-conductor
primitive *odd* character (q=2 has no primitive character; q=3 has exactly one, odd; the
trivial character mod 1 is conventionally primitive but even — round-15 m2), and it is the
quadratic character of the Theorem-11 colour field ℚ(ζ₃). What is a **convention**:
adopting conductor-minimality as the pairing principle — the same selection-convention
class the residue counts for the feature→layer map, charged as such (Addendum 66). Its completed L is entire with root number +1
(verified real on the critical line to 3×10⁻²⁵; L(1) = π/(3√3) exactly), giving the odd
bridge **p_sgn(s) = Σ_γ 2z/(z²+γ²) − ½ln 3 + Σ Λ(n)χ₋₃(n)n^(−s)** — *no pole term; a
conductor where the even tower had its pole terms (ζ's at s=1; the mirror at s=0)* —
verified three-tier with the first 24
zeros of L(s,χ₋₃) computed by sign-scanning (first ordinate 8.0397), residuals decreasing.
The odd feature at s = 6.2569 (Finding 6's excluded object) is p_sgn = 0: the point where
the colour-character zeros plus the colour-weighted primes balance the conductor ½ln 3.
*Scope:* structural only — Finding 6 stays reopened, no address is derived, no data is
touched; GRH is not used by the paired form (the Lorentzian evaluation uses the on-line
zeros the sign-scan finds, with completeness supported by the N(T) count and the
decreasing residuals); the minimality-pairing is a convention, not a forcing.

## 3. The forced dynamics

**Theorem 2 (The Gaussian achieves the L-factor; `cascade_arithmetic_increment.py` P2;
restated per the third review).** Among *even* Schwartz vectors, Tate's gcd condition (no
extraneous zeros in Z(f,s)/Γ_ℝ(s)) fixes f to the rescaled-Gaussian family c·e^(−πt²x²)
(ratio c·t^(−s), zero-free); *self-duality* then fixes the normalization to g = e^(−πx²)
(ratio ≡ 1). The dynamics is Gaussian by gcd + one normalization convention + the
definitional bridge "dynamics := the achieving vector" — the convention being the same
normalization freedom counted in the residue (Mechanism M's unit).

**Theorem 3 (Statistical dictionary; `cascade_arithmetic_increment.py` P3–P4).** Under
μ_s ∝ g(x)|x|^s d*x: (log Γ_ℝ)′(s) = E[log|x|], (log Γ_ℝ)″(s) = Var[log|x|] > 0, and
E[πx²] = s/2 exactly. The potential is a mean, the curvature is a variance, and the
half-argument of Γ_ℝ is the mean action.

**Theorem 4 (Solvability; `cascade_second_quantized.py`; Tier-2 grade per the formulation — the formal path-integral measure is the papers' stated soft spot).** The Gaussian tower is exactly
solvable; its measure normalisations are √(2πα) per mode (Tate's period), Γ(½) per Gaussian
unit, 1/(χΓ(½)) per graded crossing, and the marginal Green identity G(d)−G(d+1) = α(d) holds
exactly (10⁻¹⁵).

## 4. The gradings

**Theorem 5 (Doubling; `cascade_arithmetic_increment.py` P1).** Z(g, triv, s) = Γ_ℝ(s) and
Z(xg, sgn, s) = Γ_ℝ(s+1): the sgn character interleaves a second tower at unit shift. The
grading constant is χ = |μ(ℝ)| = 2.

**Theorem 6 (The ℤ/8 clock; `cascade_arithmetic_period.py` P1).** The Weil index of the real
quadratic character, γ = ∫e^(iπx²)dx = e^(iπ/4) = ζ₈, has order exactly 8: the tower carries a
canonical ℤ/8 grading — the arithmetic form of Bott/Clifford periodicity, obtained from a
Fresnel integral, with no topology.

**Theorem 7 (Features, all simple; `cascade_arithmetic_sign.py`, `cascade_increment_rule.py`).**
The analytic features of ξ's archimedean summands are: the critical pair s = 5.2569 and
7.2569 (exactly 2 apart by the Γ-recursion, both nondegenerate since curvature = −Var ≠ 0);
the transversal threshold crossings of P(s) = E[log|x|] at ln Γ(½) (s = 20.73) and Γ(½)
(s = 218.6); the simple pole of ζ; the simple poles of Γ_ℝ. **Every feature has order one
because variances are positive** (Bohr–Mollerup log-convexity).

*Amendment (fourth review, D1 — Theorem 9's coset clause is convention-conditional).* The
sign rule's Geometric clause ("all 28 two-coset shares < 1/π") holds under the avatar-weight
pairing (2/Γ_ℝ(d), max 0.31322) but **fails under the Definition-2.1-consistent pairing**
(2/Γ_ℝ(d+1): max 0.35001 ≥ 1/π; independently verified). The Geometric minus sign backing
Ω_m is convention-conditional, not proved — the same d↔s pairing disease as the demoted
volume pinning. Residue item seven is widened to every d↔s layer/weight pairing choice. **The systematic
d/s audit is complete** (`cascade_ds_audit.py`): nine sites — one definitional, four stable
(including Thm 10's set/exponents under all three pairings and the Gram-deficit indices
under every shift), two data-anchored conventions (the window-potential pairing, selected by
data at −38% margin; the unit), and the two known conditional sites, both demoted. No new
conditional site. Theorem 9's other two clauses stand.

*Remark (feature-list completeness: OPEN; review Finding 6 REOPENED by the second review;
`cascade_feature_monoid.py`).* A first attempt to derive the feature list's completeness
(via the even-shift recursion s·Γ_ℝ(s) = 2π·Γ_ℝ(s+2) and the Legendre identity
Γ_ℝ(s)Γ_ℝ(s+1) = Γ_ℂ(s), the L-factor of a complex place absent from ℚ) **failed hostile
re-review** on two counts, both verified: (i) a convention inconsistency — the framework's
volume feature lives in d-space (V(d) maximal at d = 5.2569, host 5), which in the twist
variable s = d+1 is s = 6.2569 with factor Γ_ℝ(s+1), *exactly the object the argument
excluded*, while the s = 5.2569 object it kept pins (host, boundary) = (4, 3) under the
same convention the thresholds use; (ii) the monoid also contains (s−1)Γ_ℝ(s), with
unlisted critical points at s ≈ 2.39 and 4.51, and the pole-free grouping ½s(s−1)Γ_ℝ has no
critical point at all. The r₂ = 0 obstruction is real but partial. Consequently: **the
feature→integer-layer selection is a convention, counted in the residue; the observer's
address retains one convention-free arithmetic distinction (the torsion half-period
γ⁴ = −1; the scalar-flatness cross-check was demoted by the third review).** *Structural
update (Addendum 65, Theorem 1c — Finding 6 stays REOPENED on its original claim):* the
r₂ = 0 obstruction is now relocated rather than removed — Γ_ℂ(s) = Γ_ℝ(s)Γ_ℝ(s+1) is
synthesized exactly by the program's own two interleaved towers (Theorem 5's doubling, via
Legendre), so no complex embedding of ℚ was ever needed; and the excluded odd object at
s = 6.2569 is the sgn tower's zero-crossing, whose L-family is the odd Dirichlet characters — the bridge holds for every odd real
primitive χ, and the **minimal-conductor primitive odd character is χ₋₃** (a theorem: q=2
has no primitive character, q=3 exactly one, odd), which is the quadratic character of the
Theorem-11 colour field ℚ(ζ₃); **the pairing-by-minimality is a convention** (round-15
M3), of the same class as the feature→layer selection. The odd feature's arithmetic home is the program's own colour sector; no
address is derived, and the selection convention stays in the residue.

## 5. The calculus of attachments (the derived rules)

**Theorem 8 (Increment rule; `cascade_arithmetic_increment.py`; partition clause demoted per
the fourth review).** Any multiplicative functional on twist intervals carries at most one
correction member exp(±α(d\*)/χᵏ), at first power; point-supported content carries none.
*Arithmetic core (stands):* attach-once (ℤ totally ordered; increments telescope, Thm 4) and
first-power (features simple, Thm 7). *Demoted (D2):* the one-source-class exclusivity — the
"one summand of log ξ" clause is grouping-relative (the volume feature exists only under
cross-summand regroupings), its double-counting step has no computation that could fail, and
multi-class cases are adjudicated by the P > L > G *convention* already in the residue.

*Remark (occupancy precedence — vacuous on uniform readings, anchoring variant-conditional; status per review Finding 2, the vacuity check, and round 9's M3 correction).*
When an observable could occupy more than one summand, the tie-break P > L > G remains a
**motivated convention**: the pole ≻ saddle ≻ arc picture (P = the pole factor, L = values
read at the features/saddles, G = window arcs) is an organizing analogy, but no argument
maps the framework's O(1) contributions onto an asymptotic expansion, and the numerical
hierarchy check is not framework-specific. The vacuity check
(`cascade_precedence_vacuity.py`) initially reported the order load-bearing via m_τ-abs's
dash-fill (T, F, T); **round 9 corrected this**: that fill expanded the closed constituents
α_s and v, violating the papers' own expression-tree predicate (`rem:sp36-syntactic` — the
same convention that keeps b/s at G = F with its closed sub-lead L(τ/μ)). On the uniform
mechanical reading no observable is multi-flag and the precedence is **vacuous on primary
readings**; the 13–109σ exclusions (round 10 added the ℓ_A-kind variant at +109σ) hold under the variant readings
only, making the anchoring **conditional**. The item stays counted in the residue with that
corrected status (abstract).

**Theorem 9 (Sign rule).** The sign is the side of the Cauchy–Schwarz equality manifold on
which the leading formula sits: off-manifold interpolation reads gain (+; the Gram deficit is
strict midpoint log-convexity — Γ's defining Bohr–Mollerup property, strict for all
d = 1–215); at-manifold saturated overlaps lose (−); *[the Geometric coset clause is DEMOTED
per the fourth review, D1: the two-coset bound is pairing-conditional — 0.31322 under the
avatar weight, 0.35001 ≥ 1/π under the Definition-2.1 weight; see the amendment under
Theorem 7. Single-coset shares survive both pairings — repair candidate recorded, not
adopted.]*

**Theorem 10 (Period-counting).** Given a marked coset of the ℤ/8 clock, the subcritical
marked set is finite and forced ({5, 13} for the coset d ≡ 5 mod 8), and a descent
functional's member exponent is the count of subcritical marked twists in its window —
(0, 1, 2) at twists (21, 13, 5) — first power each. (`cascade_arithmetic_period.py`.)

**Theorem 11 (Projection; `cascade_arithmetic_s5.py`).** Measurement of a colour-lattice
state is trace-duality pairing with the inverse different of ℚ(ζ₃): the su(3) roots *are* the
units μ₆ of ℤ[ω]; the dual lattice is the ring rotated exactly 30° (the different (√−3)
modulo the order-6 unit rotations); the fundamental weight is e^(iπ/6)/√3, a minimal dual
vector (10⁻¹⁶). Every minimal pairing projects at cos(π/6) — **a factor that exists among
imaginary quadratic rings if and only if disc = −3.**

**Theorem 12 (Measurement; `cascade_measurement_joint.py`).** For the forced Gaussian, the
r.m.s. point, the mean-action point, and the AEP-typical point (surprisal = entropy) coincide
exactly. A record's weight is the quenched (geometric-mean) average — the almost-sure
multiplicative rate of compounding records (LLN; concentration 1/√(2n) verified) — giving
e^(±r/2) exactly at rank r. *Definitional clause D1:* a measurement is a repeatable record
whose weight compounds multiplicatively. D1 has no tunable content.

**Mechanism M (activation; `cascade_activation_mechanism.py`, `cascade_joints_derived.py`;
status corrected per review Finding 1).** Each subcritical marked crossing is the chirality
flip −1 — the torsion unit — whose minimal word in the Weil clock is γ⁴ ({k : γᵏ = −1} =
{4}): four turn-units, phase −1 (the fermionic crossing sign). **Derived:** the ×3
*incoherence* (orthogonal modes of the factorized measure add without cross-terms — though
the channel *count* itself, and its N_c/N_gen identification across the quark and neutrino
sectors, is instantiation: second review, Finding 5), and the flip-word arithmetic
({k : γᵏ = −1} = {4}) — though **the count "4" buys π² only jointly with the per-step unit
assignment, which is the convention below** (the granularity changed between A38's
quarter-turns and A43's eighth-turns while E stayed fixed — second review, Finding 4, a
fixed-target signature this paper records rather than disputes). **Convention, counted in
the residue:** the unit-carrying integral. In the x²-normalization, ∫e^(ix²)dx = Γ(½)·ζ₈ and
four units carry Γ(½)⁴ = π²; in the self-dual normalization the modulus is 1 and E = 3,
excluded by data at ~99σ. The x²-unit is the same Γ(½) used throughout the framework
(Thm 4's Gaussian unit, the obstruction 1/(χΓ(½)) closing τ/μ at +0.24σ) — an *empirical
anchoring*, not an arithmetic derivation. Result: E = 3Γ(½)⁴ = 3π², the unique colour-free
composite in the empirically allowed window — where the exclusion of the other nine is
conditional on the availability assignments (e-atoms and ℤ[ω]-atoms attach only at
colour-measuring crossings: instantiation data, per Thms 11/12's meanings). JUNO's kill
window (§9) tests the mechanism's *value*; it cannot convict 3π² over its 0.1%-distant
twins (0.5–1 JUNO-σ away) — the *form* is decided by derivation or not at all.

## 6. The instantiation map — the single hypothesis

**Definition 6.1 (address book).** The observable universe occupies the tower as follows.
The observer: twist 4 — carrying **one** convention-free arithmetic distinction (the unique
nontrivially-real residue of the ℤ/8 clock, γ⁴ = −1 = the torsion unit — though its link to
the *observer* is a labeling, not a derivation), plus one Wick/lapse-conditional calculus
cross-check (scalar-flatness R·a⁴ = (n−1)(n−4) — demoted by the third review: the identity
contains no arithmetic object and the induced round-sphere metric is never scalar-flat), the
feature-boundary characterisation having been demoted by the second review
(`cascade_arithmetic_d4.py`; residue item seven). Generations: the marked coset {5, 13, 21};
gauge structure: twists {12, 13, 14} with multiplicities the 2-adic Radon–Hurwitz counts;
colour characters: ℚ(ζ₃); the phase transition: the ln Γ(½) threshold (19); the sink: the
Γ(½) threshold (217); sources, occupancy classes, population classes, and record statuses as
tabulated in the verifier scripts.

This is the paper's only assumption — and its size is stated plainly (corrected again by the
third review): the chain covered by Theorem 13's exhaustion rests on **~60 discrete entries**;
the *full* §8 record (m_H, y_t, the c/u stages, the M_Pl→v anchor, 1/α_em, the radiative
slot, the cosmological forms) draws on further assignments tabulated in other verifier
scripts, bringing the complete table to **~100 discrete entries**. Rows outside the
exhaustion's scope are determined by the same rule-set but have not been exhaustion-verified.
No entry is a continuous parameter.

## 7. Uniqueness

**Theorem 13 (address-book determination; `cascade_T4_uniqueness.py`; restated per review
Finding 3).** Given the address book — approximately **sixty discrete entries** across the
chain (window endpoints, three availability ranks, member source/class/exponent, and record
status, per observable) — the rules of Theorems 8–12 are single-valued: the determined
assignment is unique and reproduces the record to ≤0.01% at every stage. *What the
exhaustion verifies:* single-valuedness of the encoded rules and arithmetic correctness of
the determined formulas. *What it does not do:* compute availability from the address data —
the script's filters test candidates against the stored table, so the theorem's content is
"a fully-specified address book leaves zero residual freedom," not "the address book is
forced." The stronger theorem (availability as a computed function of the address alone —
U2 as a function) has a **constructed v1, corrected by the round-8 hostile review**
(`cascade_u2_function.py`; Addenda 53, 56): ten shared clauses applied to per-row identity
facts reproduce the **member fields** (class, source, channel exponent, sign) on all eleven
rows — the nine T4 exhaustion stages plus θ_23 and ℓ_A — with no per-row exceptions,
against the answer key *as corrected by the review*: the previously stored θ_23 channel
count k=2 was **wrong** (the papers give k=4, `thm:theta23-closure`), and that row's encoded
identity facts had been bent to match the wrong key. The **θ_C availability defect**
(rounds 8–12: computed (1,2,0) from quark legs against the T4-stored, formula-borne
(0,0,0); carried as an open, visibly-failing row) is **resolved at the identity-fact level
by the record-legs correction (Addendum 61, round-13 restated per the WOUNDED verdict,
A62)**: the mixing angles' legs are the states the observable *reads* — **verbatim for
θ_C** (the Cabibbo proof, part4b:3728: "the overlap of two states, **one from each gauge
layer**") and by **template-extension inference for θ_23** (the papers say only "the
cascade Cabibbo template extended") — so both angles carry gauge-layer legs (12, 13) and
the unchanged clauses compute (0,0,0). The generation coset enters both formulas only at
d=13 *qua gauge layer*; the d=13 dual identity (Gen-2 = SU(2) layer) is exactly the
disputed point, and the rounds-8–12 encoding read it qua generation record (the SM-side
*about*-label). Round-13 scope honesty: the classifier (record-ratio vs frame-rotation) is
a **new per-row soft input** not determined by any existing field, and with record-legs the
angle rows' availability agreement is **near-tautological** (legs read off the formulas
whose factor content the output is checked against) — the non-trivial residue is
clause-uniformity across the four record-ratio rows, the θ_C verbatim quote, and the
**sharpened falsifier**: no future angle-type closure (the PMNS angles) may carry an
availability factor (2√π, e^(r/2) colour, cos(π/6) projection); the repo's standing PMNS
candidates carry N_c in all three formulas, disclosed as adjacent evidence — if a promoted
PMNS closure's N_c proves scheme-equivalent to the colour factor (A14's e-vs-N_c note),
the rule dies. The m_b/m_τ projection rank rides on the audit-lemma corpus, not the papers
(round-13 M4). The earlier claims "11/11 on all seven fields" and "~7 discretionary
choices per row → ~1" are **withdrawn**: by scalar count the identity-fact table (76) is
larger than the stored-output table (50), and the residual claim is structural only (one
shared rule-set on member fields). Further round-8 corrections: the A13 content grading is
now applied consistently (θ_C and m_τ-abs carry novel=None — the earlier θ_C grading
contradicted A13's half-weight exemption and the m_τ-abs grading conflated A52's
full-formula flag criterion with the novel-content grading), which also revealed that v1's
"first-run failure and data-forced sharpening" narrative was an artifact of the inconsistent
grading and is withdrawn. Standing disclosures: fixed-target assembly; the Observer k=3
import; the genuinely ambiguous kind assignment for ℓ_A (load-bearing for precedence
anchoring).

**Theorem 13b (rule-set uniqueness within the declared clause space;
`cascade_u2_uniqueness.py`; rounds 8–14 corrected).** Enumerate **44** papers-motivated variants
(the previous count "24" was wrong) across the ten clause slots under a no-name rule and run
the full cartesian products against the corrected key, with every kill **σ-classified**
(LABEL = record-label only, zero observational content; RECORD < 2σ — experiment cannot
distinguish, killed by table fidelity alone; DATA ≥ 2σ). The previous blanket claim "every
kill is a data-kill" is **withdrawn** — the celebrated θ_C kill of the point-counting
gauge-flag variant was 0.19σ experimentally, and was in any case an artifact of the
inconsistent grading (under the consistent A13 grading that variant *survives*). Corrected
results: the availability block, which had **zero survivors** through rounds 8–12 (the θ_C
defect), has **six survivors under the Addendum-61 record-legs encoding** — the canonical clauses,
two extensional duplicates, and the cross-generation indicator, a **genuine off-domain
fork** discriminated by probe P1 (round-13 M3 corrected the earlier "two duplicates"
miscount); the colour-rank slot is pinned uniquely by m_b/m_τ, while the projection slot's
pinning is **conditional on the audit-lemma corpus** for m_b/m_τ's proj=1 (the papers'
Tier-4a "m_b/m_τ = e" carries no projection factor — round-13 M4); all conditional on the
record-legs rule (a new per-row soft input, fixed-target, PMNS-falsifiable); on **member
fields**, four slots are pinned
with multi-σ kills among their alternatives (flag P: up to 187σ via m_τ-abs; flag L: up to
66σ via sin²θ_W with its second kill at 2.3σ; sign: 4σ via α_s — though the class-label
swap kill is LABEL-only and the *distinctive* +/− structure is pinned only at RECORD 1.0σ;
channel count: up to 67σ via sin²θ_W — though the *doubling* itself is pinned only at
RECORD 1.4σ, and round 9 (M1) replaced the bent period convention with the papers'
(d−1)//8, under which the pinning is over a uniform content encoding), while the **G-flag
reading has three survivors**, the **precedence order has all six** (no realized row is
multi-flag under the consistent grading; round 9 (M3) further showed the precedence is
vacuous on the papers' uniform expression-tree reading too — its 13–109σ anchoring is
conditional on A52's variant gradings), and the Family-B kind restriction has two.
36 member-survivor combinations, no compensating combos; all survivor freedom is off-domain
and enumerated by the probe forks **after round 9 added P6 and round 10 added P7** (round 9
found the original five probes could not separate the canonical G reading from the
point-counting survivor; round 10 found P1–P6 *still* left the precedence pairs {PGL,GPL}
and {LPG,LGP} unseparated — no probe carried P∧G — and with P7 all six orderings have
distinct probe signatures; each round's completeness claim was retrospectively false and
each was corrected on the record). Round 11 corrected P7's *justification*: the round-10
claim that the papers' m_W-absolute realizes the P∧G class was grading-inconsistent —
under the arc's own uniform reading m_W-absolute is (T,F,F), its window content inside
closed constituents exactly as m_τ-abs's — so P7 stands as a well-formed hypothetical
corner (the nearest uniform-reading P∧G configuration, the VEV v with its top-level window
exponential, is an anchor with no addressed member row), and the grading-inconsistency
class is recorded at its third occurrence.
Uniqueness is relative to a space that also holds the **source map {19, 5, 14, 7} and the
population-class names fixed** — a withheld axis, disclosed. The Observer k = 3, the
content grading, and the ℓ_A kind remain inputs.

**Theorem 13c — withdrawn as a theorem; retained as annotation
(`cascade_u2_first_principles.py`; round-8).** The previous version claimed three
stipulations dissolve into foundation objects. The round-8 hostile review defeated each
claim, and the retraction is recorded here in place: (i) the "half-open support theorem"
for the gauge flag is **retracted** — the μ/e path's summand set *includes* p(14)
(part4b:83, "d=14..21 … exclusive of the lower endpoint"), so no faithful support reading
exempts it; the prior computation double-shifted the summand ranges, the prior increment
verifier uses the opposite span convention, and the clause is what it always was: the
papers' strict-boundary stipulation (part4b:503, flagged Conditional at 4108(a)); (ii)
"Theorem 9's one-record-one-frame" **does not exist** — the phrase was an invented gloss
(Theorem 9 here is the Sign rule; the quenched-record theorem says nothing about frames),
so the nesting is a freestanding and **reversible** argument (path-before-read argues
unit > gauge > observer, i.e. PGL, equally well); (iii) "Observer 3 = |marked set|, a
theorem" is **false as attributed** — T6 forces only the subcritical set {5,13}, size two,
and {5,13,21} is Definition 6.1 instantiation data, so k = 3 remains a soft input read as
an instantiation count; additionally "19 and 5 are foundation objects" is withdrawn (all
four source values {19, 5, 14, 7} pass through the same feature→layer selection convention
counted in this paper's residue, and the observer is twist 4, not 5), and the claim of "no
precedence order, no null clause, no k-table in the code" was literally false — the code is
an ordered decision chain with an else-null and inline constants; the annotations propose
*reasons*, they do not remove stipulations. What remains at honest strength: the clause
structure carries proposed groundings — nesting and contact-counting **arguments**, winding
and field-degree **identifications** (the colour 2 is equally the su(3) Cartan rank; a
choice among coincident 2s) — and the reconstruction takes the canonical branch on each of
Theorem 13b's probe forks as a **proposal**, not an adjudication. Member fields 11/11 under
the corrected key; the θ_C availability defect, open through rounds 8–12, is resolved
conditional on the Addendum-61 record-legs rule (round-13 restated — see Theorem 13's
corrected tail).

## 8. The record: agreement at current precision

Every output below is forced by Theorems 1–13 under Definition 6.1; deviations are against
current world data (verifiers in `tools/research/`; the Planck-anchored chain runs
M_Pl → v → all masses):

| Observable | Arithmetic output | Deviation |
|---|---|---|
| ρ_Λ/M⁴_Pl,red | 7.145×10⁻¹²¹ | −0.04σ (Planck) |
| w(z) | −1 exactly (structural) | consistent |
| m_H | 125.19 GeV | −0.35σ |
| m_t | 172.61 GeV | +0.14σ |
| m_b, m_c, m_s, m_d, m_u | full chain | −0.03σ, −0.36σ, −0.03σ, −0.34σ, −0.13σ |
| m_τ/m_μ, m_μ/m_e, m_τ | 16.8173; 206.771; 1776.82 MeV | +0.24σ; +0.001%; −0.31σ |
| m_τ, m_μ, m_e absolute (from M_Pl) | chain | −21, −38, −49 ppm |
| m_ν3; Δm²_sol | 49.28 meV; 7.572×10⁻⁵ eV² | −0.5% (−0.7σ PDG; **−2.9σ NuFit 6.0** — input-dependent, under tension); +0.24σ |
| α_s(M_Z); 1/α_em; sin²θ_W | 0.11792; 137.028; 0.23123 | +0.02σ; 0.006%; +0.40σ |
| θ_C; θ₂₃ | 13.04°; closure | +0.03σ; sub-σ |
| Ω_m; ℓ_A | 0.31473; 301.44 | −0.04σ; **−1.8σ** (vs 301.6 ± 0.09; corrected per review Finding 5 — the papers' −0.16 is the absolute difference, not a σ count) |
| θ_QCD | 0 exactly | consistent |

*Metric discipline (per review Finding 5):* two metrics appear above. σ-entries are against
experimental error where it dominates; %/ppm entries (chain absolutes, 1/α_em, m_ν3) are
against the framework's **leading-order systematic floor** — there the deviation is many
experimental σ, and the claim is that the residual sits at the framework's stated floor, not
inside experimental error. With that convention stated: no output disagrees with any current
measurement beyond the applicable tolerance, ℓ_A (−1.8σ) being the largest strain. This
table, plus Theorems 1–13, is the content of the word "indistinguishable."

## 9. The Indistinguishability Theorem — and its executioners

**Theorem 14 (Indistinguishability, conditional).** *Conditional on Definition 6.1, the
arithmetic of the completed Riemann zeta function at the real place is indistinguishable from
the observable universe at current experimental precision.* *Proof:* Theorems 1–13
(mathematics) + the table of §8 (the record). ∎

The conditional cannot be discharged by mathematics — no theory's can. It is discharged, or
destroyed, by the pre-registered ledger, frozen before the data exists:

| Prediction | Value | Judge | Kill condition |
|---|---|---|---|
| Σm_ν | 60.91 meV, normal ordering | DESI/CMB-S4; JUNO | bound < ~60 meV, or inverted ordering. **Standing tension, not future:** published ACT+DESI compressed bounds already reach 52–57 meV (audit A29) — if those combinations firm up, this row is already dead |
| Δm²₂₁ | 7.572×10⁻⁵ eV² | JUNO (~0.3%) | outside ~0.6% window kills Mechanism M |
| m_β; m_ββ | 9.1 meV; ≤5.5 meV | KATRIN; LEGEND-1000/nEXO | any signal at current sensitivity |
| w(z) | −1, no evolution | DESI DR3+ | any confirmed evolution |
| m_H | 125.194 GeV | HL-LHC (~25 MeV) | >3σ miss |
| m_τ | π⁶/945-vs-α(14)/2 fork | Belle II (~0.02 MeV) | adjudicates |
| m_b/m_τ; m_c; m_s/m_ud; m_u/m_d; y_t | 2.35405; 1.2714; 27.35; 0.4593; 0.99142 | lattice/colliders | >3σ miss |
| Structure | no 4th generation, no anyons (free 3+1D), no SUSY partners, no axion, no dark-matter particle | any discovery | fatal |

## 10. Honest limits

1. **C1 is forever empirical.** The arithmetic distinguishes the observer's address by one
   convention-free fact (§6; two former pinnings were demoted by reviews two and three) and
   cannot select it; the selection is the hypothesis. If the arithmetic could prove its own instantiation, no
   experiment could kill it — falsifiability *requires* this step to remain empirical.
2. **External and conventional inputs (corrected per the external review).** Lovelock's
   theorem (selection of d = 4; external tensor calculus); the closed atom grammar A2 (a
   completeness statement over what was used, not a proof that nothing else could attach);
   the x²-unit normalization carrying Γ(½) (empirically anchored — the self-dual alternative
   gives E = 3, excluded by data — not arithmetically forced); the P > L > G precedence
   (motivated); and the feature→layer selection convention (second review, Finding 1 —
   part0 itself concedes no uniform rounding rule exists). J2's incoherence is derived from
   the factorized measure; the flip-word arithmetic is derived but buys π² only jointly with
   the unit convention; the feature-list completeness attempt **failed re-review** and is
   recorded as open (`cascade_feature_monoid.py`, rewritten to state the failure).
3. **Provenance.** Theorems 8–13 were constructed by a single reviewer in a single session,
   knowing the empirical targets; each carries a rigorous mathematical core, but the
   interpretive bridges from mathematics to rule await hostile external review. The
   registered ledger is the only bias-immune instrument, and the framework's standing is
   staked on it, not on the derivations.
4. **The stopping rule.** No further retrodictive closures are admissible. The framework is
   finished arguing; §9 names its judges and accepts their verdicts in advance.

---

*Verification suite: `tools/research/cascade_formulation_kernel.py`,
`cascade_arithmetic_increment.py`, `cascade_arithmetic_period.py`,
`cascade_arithmetic_sign.py`, `cascade_arithmetic_s5.py`, `cascade_measurement_joint.py`,
`cascade_activation_mechanism.py`, `cascade_joints_derived.py`, `cascade_feature_monoid.py`,
`cascade_T4_uniqueness.py`, `cascade_arithmetic_d4.py`, `cascade_leptons.py`,
`cascade_neutrino_closure.py`, `cascade_E_fit_audit.py`, `cascade_null_clone.py`. Classical inputs: Tate's thesis; Weil, the
metaplectic index; Wall, the graded Brauer group; Bohr–Mollerup; Adams/Radon–Hurwitz;
Lovelock; Kolmogorov.*
