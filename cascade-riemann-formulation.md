# The Cascade as a Theorem of Number Theory: A Formulation

**Status:** formal skeleton, written under the stopping rule of Addendum 30 (admissible
category (a): work checkable without reference to data). This document states exactly what can
be a theorem, what is currently an axiom, and what can never be a theorem. Machine
verifications: `tools/research/cascade_formulation_kernel.py` (T1),
`cascade_second_quantized.py` (T2), `cascade_epsilon_dictionary.py` (T3),
`cascade_null_clone.py` (the numerical shadow of T4).

## 0. Notation

Γ_ℝ(s) := π^(−s/2) Γ(s/2) — the archimedean Euler factor of the completed Riemann zeta
function ξ(s) = ½ s(s−1) Γ_ℝ(s) ζ(s), with ξ(s) = ξ(1−s).

## 1. The axiom system

**A1 (Arithmetic kernel).** The state space is the descent lattice ℕ (layer index d), weighted
by Γ_ℝ; the dynamics is the unique Gaussian elastic action with bond compliance α(d)
(uniqueness: papers' `rem:action-uniqueness`).

**A2 (Local-constant calculus).** Every multiplicative factor attached to a descent is drawn
from the local constants of the adelic structure:

| Constant | Identity | Arithmetic home |
|---|---|---|
| χ = 2 | \|μ(ℝ)\| | torsion of the real units |
| Γ(½) = √π | Γ_ℝ critical value | the functional equation's symmetry point |
| 2π | χ·Γ(½)² | Tate's self-dual period at the real place |
| ½ | half-argument of Γ_ℝ | the Gaussian, Tate's self-dual test function |
| mod-8 grading | Brauer–Wall group BW(ℝ) ≅ ℤ/8 | graded Brauer group of the real place (Wall 1964) — the arithmetic avatar of Bott/Clifford periodicity |
| N_c = 3 = 2^(v₂(12))−1 | Radon–Hurwitz count | a 2-adic invariant (value depends only on v₂) |
| cos(π/6) | weight–root angle of ℤ[ω] | ring of integers of ℚ(ζ₃) |
| phases i, ζ₈ | quaternionic frame, Bott | the cyclotomic tower ζ₂, ζ₃, ζ₄, ζ₈ |

**A3 (Assignment rules).** Which constant attaches where: the source-selection flags (P, L, G)
as ξ-occupancy functors; the increment rule (corrections attach once, at sub-lead); source
layers at the analytic features of Γ_ℝ; the per-Bott-period attachment below the phase
transition. *This is the load-bearing axiom.* Partial derivation exists (Addendum 12: the
flags recovered 9/9 from ξ's factorization); the increment and per-period rules are underived.

**A4 (Measurement).** Measurement records the typical value of a Gaussian mode (weight
e^(±½) per measured mode — lemma S4, anchored by equipartition); projection is along root
frames (lemma S5).

## 2. The theorems

**T1 (Kernel — PROVED, elementary).** The cascade's four primitive families are exactly the
log-geometry of Γ_ℝ at integer arguments:

- Ω(d) = 2/Γ_ℝ(d+1)  (sphere measure = reciprocal Euler factor)
- N(d) = Γ_ℝ(d+1)/Γ_ℝ(d+2)  (coupling = Euler-factor ratio)
- p(d) = (log Γ_ℝ)′(d+1)  (potential = logarithmic derivative)
- α(d) = N(d)²/4π  (compliance)

Each is an elementary Gamma identity; machine-verified to ≤6×10⁻¹⁴ across d = 1–300. The
cascade lattice **is** the discrete log-geometry of ζ's factor at the real place — this
sentence is a theorem, not an analogy.

**T1b (Explicit-formula bridge — PROVED; Addendum 64; `cascade_explicit_formula_bridge.py`).**
For every d ≥ 1, with s = d+1, z = d+½: p(d) = Σ_{γ>0} 2z/(z²+γ²) − 1/s − 1/(s−1) +
Σ Λ(n)n^(−s) — the cascade potential is exactly (Riemann zeros) − (poles) + (primes), the
Hadamard partial-fraction form of the explicit-formula identity on the tower; every window
inherits the split. Verified three-tier (rearrangement 10⁻³¹; Euler side within strict tail bounds at dps 50 —
round-15 M2; Hadamard side with 50 computed zeros, residuals decreasing). Round-15 M1: the
RH-free theorem is the *paired* Hadamard form; the Lorentzian display is its on-line
evaluation. Classical content Euler + Hadamard; program-new content: the tower evaluation
only. Grounds the *scaffold*
one level deeper (the tower sits on one side of the explicit formula); grounds the
*dictionary* not at all; claims no direction of explanation.

**T1c (The two doors — PROVED at their stated strengths; Addendum 65;
`cascade_zero_side_features.py`, `cascade_colour_field_bridge.py`).** (i) Every
distinguished feature is a level-crossing of p, hence by T1b an exact ZEROS + PRIMES =
POLES + level balance point; solving from the zero side (50 computed zeros + density tail)
recovers the critical point to 6×10⁻³ and the threshold to 5×10⁻² with decreasing error
(sink tail-model-limited ~1%, reported as such). Honest negative registered: no recorded
quantity reads the zero side independently of the digamma packaging. (ii) Legendre gives
p_ℂ = p_triv + p_sgn *exactly* — T5's doubled tower synthesizes the complex-place factor,
relocating F6's r₂ = 0 obstruction; the odd bridge p_sgn = zeros(L(χ)) − ½ln q + χ-weighted primes (no pole; a conductor
instead) holds for **every** odd real primitive χ — the balance point is
character-independent (round-15 M3) — with χ₋₃ the minimal-conductor primitive odd
character (theorem) = the T8 colour field's character, and pairing-by-minimality a
**convention** charged to the selection-convention class; verified with 24
sign-scan-computed zeros of L(χ₋₃); the odd feature 6.2569 = the conductor balance point.
No direction of explanation is claimed (the identity is ζ's/L's own bookkeeping — m6). F6
stays reopened on its original claim; no address derived.

**T1d (The finite places — PROVED at stated strengths; Addendum 69;
`cascade_finite_places.py`).** (i) Global potential identity (exact): Σ_v p_v = ξ′/ξ −
poles with p_v = (log E_v)′ per place; T1b's "+primes" = −Σ_p p_p — the tower is one member
of an adelic family, and p = 2, 3 carry ~99% of the finite total at the record's layers
(noted, not claimed as derivation). (ii) The order-8 clock element is dyadic-exclusive
among finite-place Gauss phases (Gauss's theorem verified to q = 499; ζ₈ at 4-divisible
moduli) — exact theorem + one graded identification. (iii) Landsberg–Schaar verified: the
archimedean Weil index ζ₈ is the exchange constant between finite places — the product
formula's machine-checkable avatar. Scope: no grammar entry derived; 2/3-adic Tate theory
named, not opened; sign-convention failure on the first run kept on the record.

**T2 (Solvability — PROVED at the papers' Tier-2 grade).** The A1 action is Gaussian, hence
second-quantizable in closed form; its measure normalisations are √(2πα) per mode (Tate's
period), Γ(½) per Gaussian unit, 1 per Berezin unit, 1/(χΓ(½)) per graded crossing; and the
marginal Green identity G(d)−G(d+1) = α(d) holds exactly (verified 10⁻¹⁵). All physical
content of the free theory lives in these normalisations. (Addendum 25.)

**T3 (Dictionary — PROVED as a completeness statement).** Every constant used anywhere in the
mass arc (Addenda 12–29) is the image of an A2 local constant; the one-rule recomputation of
the full spectrum uses no per-case number (Addendum 24). The grammar is closed over A2.

**T4 (Address-book determination; Addendum 40, restated per external reviews).** *Given the arena,
the dictionary, the derived rules (T5–T9, exclusion, flags, channel count), the instantiation
data (address book, record statuses), and D1, the observable map is unique.* Proof: U1
exactly-once (at-most-once = T5; at-least-once = completeness of the Gaussian measure, T2/T9);
U2 availability (rounds 8–13 corrected state, Addenda 53–62: **member fields** computed by one
shared rule-set on all 11 rows against the *corrected* key — the previously stored θ_23
channel count was wrong (papers: k=4) — and the rounds-8–12 **θ_C availability defect is
resolved by the A61 record-legs correction, round-13 restated (WOUNDED)** — angles read
gauge-layer states (verbatim for θ_C, template-inference for θ_23); the generation pairing
was an about-label mislabeled as legs; avail block 6 survivors = canonical + 2 duplicates +
the cross-generation-indicator fork (P1); colour rank pinned by m_b/m_τ, projection pinning
conditional on the audit-lemma corpus (M4); the classifier is a new per-row soft input;
sharpened PMNS falsifier with the repo's N_c-bearing candidates disclosed); member-field
uniqueness relative
to the declared 44-variant space with σ-classified kills — P/L/sign/channel-count slots
pinned at up to 187σ/66σ/4σ/67σ, G-flag reading 3 survivors, precedence all 6 (round 9:
vacuous on the papers' uniform expression-tree reading too — anchoring only under the four
variant readings, 13–109σ conditional; round 10: survivor freedom enumerated
by probes P1–P7 after P7 closed the P∧G gap), Family-B
2 — with the source map {19,5,14,7} held fixed as a disclosed withheld axis;
first-principles groundings at argument/identification strength only, the half-open-support
"theorem" and the T9/T6 attributions retracted); U3 member determinism (flags + T7 +
channel count + T5). Exhaustion:
every stage's naive space (1,764–7,056 assignments) filters to exactly one survivor, each
reproducing the recorded formula to ≤0.01%; the neutrino E-stage collapses to
(N_c·π², (0,1,2)). The exhaustion verifies single-valuedness against the ~60-entry table, not forcedness. The unconditional question — why *this* address book — is C1 itself, not mathematics.

**T9 (Quenched-record theorem — PROVED; Addendum 39).** For the forced Gaussian, the three
candidate meanings of "recorded value" (r.m.s. point, mean-action point, AEP-typical point)
coincide exactly (−ln f(x) − h = S(x) − ½ identically); a record's weight is the quenched
(geometric-mean) average — the almost-sure multiplicative rate of compounding records
(Kolmogorov LLN, concentration 1/√(2n)) — giving e^(±r/2) exactly at every rank r via
⟨S_r⟩ = r/2 (T5-P4). S4's entire content reduces to two identities + one LLN theorem + the
definitional clause **D1**: a measurement is a repeatable record whose weight compounds
multiplicatively over independent realizations.

**T8 (S5 as trace duality — PROVED; Addendum 36).** The su(3) roots are the units μ₆ of ℤ[ω]
(point-by-point); the measurement frame is the trace-dual lattice — the inverse different
𝔡⁻¹ = (1/√−3)ℤ[ω], which is the ring rotated exactly 30° modulo unit rotations; the su(3)
fundamental weight w₁ = e^(iπ/6)/√3 is a minimal vector of 𝔡⁻¹ (10⁻¹⁶); every minimal pairing
projects at cos(π/6), a factor unique among imaginary quadratic rings to disc = −3. Colour
multiplicity 3 and per-leg occupancy remain instantiation.

**T7 (Arithmetic sign rule — PROVED; Addendum 35).** The sign of a correction is the side of
the Cauchy–Schwarz equality manifold on which the observable's leading formula sits:
off-manifold interpolation reads gain (+) — the Gram deficit is strict midpoint log-convexity
of Γ_ℝ, i.e. Bohr–Mollerup, verified strict for all d = 1–215; at-manifold saturated overlaps
lose (−); proper coset restrictions of the peaked weight 2/Γ_ℝ under the ℤ/8 Weil grading lose
(−) — all 28 two-coset shares < 1/π under the avatar-weight pairing; **convention-conditional
per review 4: the Definition-2.1 pairing gives max 0.35001 ≥ 1/π** — the Geometric clause is
demoted. The other two clauses stand. Population-class assignment remains instantiation.

**T6 (Per-period shape theorem — PROVED conditional on marking + activation; Addendum 34).**
The twist tower carries a canonical ℤ/8 grading: the Weil index of the real quadratic
character, γ = ∫e^(iπx²)dx = ζ₈, has order 8 (arithmetic Bott, no topology). Given a marked
coset (instantiation) and source-activation of its subcritical members, the subcritical marked
set is finite and forced — {5, 13} for C = {d ≡ 5 mod 8} — and the member exponent of a
descent functional is the count of subcritical marked twists in its window: (0, 1, 2) at
(21, 13, 5), first power each. The exponent pattern of the neutrino closure is forced
counting; only the member's *value* remains unfixed.

**T5 (Arithmetic increment rule — PROVED from Tate's thesis alone; Addendum 33).** With no
cascade or physics input: the sgn character doubles the twist tower at unit shift (χ = 2 =
|μ(ℝ)|); the Gaussian achieves the L-factor (gcd fixes the rescaled family; self-duality is
a normalization convention — restated per reviews 3–4); (log Γ_ℝ)′ = E[log|x|] and (log Γ_ℝ)″ = Var[log|x|] > 0 under the twisted Gaussian
measure, so every feature of ξ's archimedean summands is order one (simplicity = variance
positivity); E[πx²] = s/2 exactly (the ½-atom = the mean action; S4's anchor); ℤ's total order gives
attach-once (the one-summand partition clause was demoted by review 4, D2). Hence: at most one member, first power, per interval
functional — a theorem of probability at the real place. What arithmetic does not supply:
P > L > G precedence, the physical occupancy assignment, the (m,k) counts — instantiation data
belonging to C1.

## 3. The conjectures (never theorems)

**C1 (The physical conjecture).** The observed universe realizes A1–A4: the Standard-Model
mass spectrum is the epsilon-factor system of the completed Riemann zeta function at the real
place, with multiplicities from the 2-adic place and phases from the cyclotomic tower. *No
formulation can make this a theorem.* It is decided only by the frozen ledger (Addendum 26 +
29D): Σm_ν = 60.9 meV, JUNO ordering, Belle II m_τ, DESI w(z), HL-LHC m_H, lattice ratios,
the forced negatives.

**C2 (The arithmetic dynamics conjecture).** The finite places enter as the prime clock
(Addenda 5–6): census convergence at rate 1/√x ⟺ GRH. The framework's dynamical side is
equivalent to the Generalized Riemann Hypothesis in the only sense available to physics:
indistinguishability of the event stream from the GRH-governed one.

## 4. Gap ledger: what stands between here and bulletproof

| # | Gap | Type | Closes when |
|---|---|---|---|
| 1 | Increment rule (A3) | **derived from arithmetic first principles** (T5, Addendum 33; supersedes the Tier-2 A32 version) | closed as mathematics; only its physical instantiation (occupancy, m/k counts) remains with C1 |
| 2 | Per-period attachment (A3) | **shape derived** (T6, A34); mechanism at Tier-2 (A38/A43, amended per external review): flip-count 4 derived (minimal torsion word), ×3 incoherence derived (factorization); **the unit normalization carrying Γ(½) is a convention, empirically anchored not arithmetically forced** (self-dual form gives E = 3, excluded by data) ⟹ E = 3π², unique colour-free form *conditional on availability assignments* | remaining: the marked-coset choice, the unit convention; JUNO tests the value (~0.6% window), cannot convict the form over its 0.1% twins |
| 3 | S4 lemma: measurement-at-typical-value | **derived** (T9, Addendum 39): typicality unambiguous (three notions coincide exactly), factor = quenched rate forced by LLN, all ranks exact | residue: definitional clause D1 (records compound multiplicatively) — no tunable content |
| 4 | S5 lemma: root-frame projection | **derived** (T8, Addendum 36): frame = trace-dual lattice (inverse different of ℚ(ζ₃)); value = 30° rotation of ℤ[ω], unique to disc −3 | colour count 3 and per-leg occupancy remain instantiation |
| 5 | Sign rule | two clauses derived (T7: Bohr–Mollerup off/at the equality manifold); **coset clause demoted** (review 4, D1: convention-conditional) | population-class assignment remains instantiation |
| 5b | P > L > G precedence | **vacuous on uniform primary readings at both layers; anchoring conditional** (round 9, M3: A52's m_τ-abs dash-fill expanded closed constituents against the papers' expression-tree predicate — the same convention keeping b/s at G=F — so on the uniform mechanical reading no row is multi-flag anywhere and the order never fires; the 13–109σ exclusions hold only under the four variant readings — m_τ-abs constituent expansion, ℓ_A window, ℓ_A kind (+109σ, round 10), sin²θ_W coupling-running; A52 script corrected). Round 8 standing: all six orders survive the U2 exhaustion; the A55 nesting argument is **reversible** (retracted "T9" anchor) | counted in the residue; on the uniform reading the item is deletable-as-vacuous — papers' adjudication of the grading would settle it |
| 6 | T4 uniqueness | **address-book determination + U2 (rounds 8–14 corrected)** (Addenda 40, 53–63): member fields computed by one shared rule-set (11/11 against the corrected key — the stored θ_23 k was wrong, papers give k=4); the rounds-8–12 θ_C availability defect **resolved by A61's record-legs correction (round-13: WOUNDED, restated)** — angles read gauge-layer states (verbatim θ_C / template-inference θ_23); avail 6 survivors incl. the indicator fork (P1); colour rank pinned, projection pinning corpus-conditional (M4); classifier = new soft input; sharpened PMNS falsifier with standing N_c candidates disclosed; member uniqueness relative to the declared space with σ-classified kills (four slots multi-σ pinned; G-flag 3 survivors; precedence all 6; Family-B 2; source map held fixed = withheld axis); collapse claim ("~60→~30") **withdrawn** (input scalars 76 > output scalars 50); first-principles groundings argument-strength only | open: extension to the full ~100-entry record; absolute forcing unavailable in principle; soft inputs: Observer k=3 (instantiation count — the \|T6-set\| upgrade was retracted, T6 forces {5,13} size 2), A13 grading, ℓ_A kind, and now the record-legs rule (identification, PMNS-falsifiable); all four source twists {19,5,14,7} convention-selected |
| 7 | χ = 2 ↔ \|μ(ℝ)\| vs χ(S^even) | bridge unformalized | show the Euler characteristic's role factors through the unit-torsion identity, or keep topology as justification |
| 8 | C1 | empirical forever | the ledger |

Items 1–6 are mathematics: each is checkable without data, and each success converts an axiom
into a theorem, shrinking the axiom system toward A1 + A2 alone. Item 8 is physics and cannot
be moved by proof.

## 5. The honest summary sentence

The framework admits exactly this formulation: **a proved kernel (T1–T3) identifying the
cascade with the log-geometry of ζ's real place and its mass grammar with adelic local
constants; the assignment rules derived as theorems (T5 increment, T6 period shape, T7 sign,
T8 projection, T9 measurement) with the activation mechanism at Tier-2; address-book
determination verified (T4, restated); one definitional clause (D1); a seven-item
non-arithmetic residue (see the standalone paper's abstract); and one physical conjecture
(C1) that no mathematics can settle.** Every number is either a theorem's output, a
convention's output (counted in the residue), or a frozen ledger entry awaiting JUNO, DESI, Belle II, the HL-LHC, and the lattice. The claim
that *our* universe instantiates the skeleton is, and will always remain, the ledger's to
decide.
