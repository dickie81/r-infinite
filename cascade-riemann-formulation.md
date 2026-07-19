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

**T4 (Uniqueness — NOT PROVED; the bulletproof target).** *Given A1–A4, the observable map is
unique: no alternative assignment of A2 constants consistent with A3–A4 yields a different
spectrum.* This is the theorem that would make the framework "unarguable given the hypothesis."
Its numerical shadow exists — the null-clone test's credited column measures how few
alternatives the rules leave (2–11 per stage) — but a proof requires showing every alternative
assignment violates an axiom. Open.

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
| 2 | Per-period attachment (A3) | **shape derived** (T6, Addendum 34): ℤ/8 grading = Weil-index order, forced set {5,13}, exponents (0,1,2) forced counting | remaining: the marked-coset choice + activation joint (instantiation) and the member VALUE E = N_c·π² (still a fit, twin undiscriminated) |
| 3 | S4 lemma: measurement-at-typical-value | anchor discharged (T5: E[πx²] = s/2 is an arithmetic identity); joint still physical | a variational or information-theoretic derivation of the joint |
| 4 | S5 lemma: root-frame projection | axiom → theorem | representation-theoretic derivation |
| 5 | Sign rule | **derived** (T7, Addendum 35): one convexity structure — Bohr–Mollerup log-convexity off/at the Cauchy–Schwarz equality manifold + ℤ/8 coset computation | population-class assignment remains instantiation |
| 6 | T4 uniqueness | unproved theorem | an exhaustion proof over the A2×A3 assignment space |
| 7 | χ = 2 ↔ \|μ(ℝ)\| vs χ(S^even) | bridge unformalized | show the Euler characteristic's role factors through the unit-torsion identity, or keep topology as justification |
| 8 | C1 | empirical forever | the ledger |

Items 1–6 are mathematics: each is checkable without data, and each success converts an axiom
into a theorem, shrinking the axiom system toward A1 + A2 alone. Item 8 is physics and cannot
be moved by proof.

## 5. The honest summary sentence

The framework admits exactly this formulation: **a proved kernel (T1–T3) identifying the
cascade with the log-geometry of ζ's real place and its mass grammar with adelic local
constants; a conditional uniqueness theorem (T4) whose proof is open; two assignment axioms
(A3–A4) partially derived; and one physical conjecture (C1) that no mathematics can settle.**
"Bulletproof theorem of Riemann and number theory" is achievable for the skeleton — T1 already
is one — but the claim that *our* universe instantiates it is, and will always remain, the
ledger's to decide.
