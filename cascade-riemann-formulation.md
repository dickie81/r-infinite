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

**T2 (Solvability — PROVED at the papers' Tier-2 grade).** The A1 action is Gaussian, hence
second-quantizable in closed form; its measure normalisations are √(2πα) per mode (Tate's
period), Γ(½) per Gaussian unit, 1 per Berezin unit, 1/(χΓ(½)) per graded crossing; and the
marginal Green identity G(d)−G(d+1) = α(d) holds exactly (verified 10⁻¹⁵). All physical
content of the free theory lives in these normalisations. (Addendum 25.)

**T3 (Dictionary — PROVED as a completeness statement).** Every constant used anywhere in the
mass arc (Addenda 12–29) is the image of an A2 local constant; the one-rule recomputation of
the full spectrum uses no per-case number (Addendum 24). The grammar is closed over A2.

**T4 (Conditional uniqueness — PROVED by finite exhaustion; Addendum 40).** *Given the arena,
the dictionary, the derived rules (T5–T9, exclusion, flags, channel count), the instantiation
data (address book, record statuses), and D1, the observable map is unique.* Proof: U1
exactly-once (at-most-once = T5; at-least-once = completeness of the Gaussian measure, T2/T9);
U2 availability determinism (the operation set is a function of the address; exclusion is the
negative direction); U3 member determinism (flags + T7 + channel count + T5). Exhaustion:
every stage's naive space (1,764–7,056 assignments) filters to exactly one survivor, each
reproducing the recorded formula to ≤0.01%; the neutrino E-stage collapses to
(N_c·π², (0,1,2)). Zero discrete freedom remains within the axioms. The unconditional
question — why *this* address book — is C1 itself, not mathematics.

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
(−) — all 28 two-coset shares < 1/π over the full tower. The papers' three separate sign
mechanisms are one convexity structure. Population-class assignment remains instantiation.

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
|μ(ℝ)|); the Gaussian is the unique L-factor-achieving vector (A1's dynamics discharged into
arithmetic); (log Γ_ℝ)′ = E[log|x|] and (log Γ_ℝ)″ = Var[log|x|] > 0 under the twisted Gaussian
measure, so every feature of ξ's archimedean summands is order one (simplicity = variance
positivity); E[πx²] = s/2 exactly (the ½-atom = the mean action; S4's anchor); ℤ's total order
+ the log ξ partition give attach-once. Hence: at most one member, first power, per interval
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
| 2 | Per-period attachment (A3) | **shape derived** (T6, A34); **mechanism derived** (A38 + A43): each marked crossing is the torsion flip −1 = γ⁴ (minimal word), four Fresnel units of modulus Γ(½) each (J1 = polar decomposition of ∫e^(ix²)dx = Γ(½)·ζ₈, derived), × N_gen = 3 orthogonal channels (J2 = factorization, derived) ⟹ E = 3π², the unique colour-free form | remaining: the marked-coset choice (instantiation); JUNO stake: Δm²₂₁ within ~0.6% of 7.572e-5 or the mechanism dies |
| 3 | S4 lemma: measurement-at-typical-value | **derived** (T9, Addendum 39): typicality unambiguous (three notions coincide exactly), factor = quenched rate forced by LLN, all ranks exact | residue: definitional clause D1 (records compound multiplicatively) — no tunable content |
| 4 | S5 lemma: root-frame projection | **derived** (T8, Addendum 36): frame = trace-dual lattice (inverse different of ℚ(ζ₃)); value = 30° rotation of ℤ[ω], unique to disc −3 | colour count 3 and per-leg occupancy remain instantiation |
| 5 | Sign rule | **derived** (T7, Addendum 35): one convexity structure — Bohr–Mollerup log-convexity off/at the Cauchy–Schwarz equality manifold + ℤ/8 coset computation | population-class assignment remains instantiation |
| 5b | P > L > G precedence | **derived** (Addendum 43): pole ≻ saddle ≻ arc — the dominance hierarchy of contour asymptotics (P = pole factor, L = values at features/saddles, G = window arcs) | — |
| 6 | T4 uniqueness | **PROVED conditional** (Addendum 40): finite exhaustion, every stage a singleton | residue = the conditionality itself: address book, precedence, J1/J2, closed atom list — i.e., C1's instantiation data |
| 7 | χ = 2 ↔ \|μ(ℝ)\| vs χ(S^even) | bridge unformalized | show the Euler characteristic's role factors through the unit-torsion identity, or keep topology as justification |
| 8 | C1 | empirical forever | the ledger |

Items 1–6 are mathematics: each is checkable without data, and each success converts an axiom
into a theorem, shrinking the axiom system toward A1 + A2 alone. Item 8 is physics and cannot
be moved by proof.

## 5. The honest summary sentence

The framework admits exactly this formulation: **a proved kernel (T1–T3) identifying the
cascade with the log-geometry of ζ's real place and its mass grammar with adelic local
constants; the assignment rules derived as theorems (T5 increment, T6 period shape, T7 sign,
T8 projection, T9 measurement) with the activation mechanism at Tier-2; conditional
uniqueness proved by finite exhaustion (T4); one definitional clause (D1); and one physical
conjecture (C1) that no mathematics can settle.** The skeleton is now closed: within the
axioms there is zero discrete freedom, and every number is either a theorem's output or a
frozen ledger entry awaiting JUNO, DESI, Belle II, the HL-LHC, and the lattice. The claim
that *our* universe instantiates the skeleton is, and will always remain, the ledger's to
decide.
