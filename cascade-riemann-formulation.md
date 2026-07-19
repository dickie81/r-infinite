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
| 1 | Increment rule (A3) | **derived at Tier-2** (Addendum 32) | ξ-partition exclusivity + simplicity lemma (rigorous: trigamma positivity) + monotone descent; inherits P>L>G, gauge window, chirality-rule proof |
| 2 | Per-period attachment (A3) underived | axiom → theorem | currently a reverse-engineered fit (A29 amendment); does NOT inherit Addendum 32 |
| 3 | S4 lemma: measurement-at-typical-value | axiom → theorem | a variational or information-theoretic derivation |
| 4 | S5 lemma: root-frame projection | axiom → theorem | representation-theoretic derivation |
| 5 | Sign rule | axiom → theorem | papers' own open item |
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
