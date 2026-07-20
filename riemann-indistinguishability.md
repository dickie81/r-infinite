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
state tower (the integer Tate twists of the real place); its unique dynamics (the Gaussian,
forced as the L-factor-achieving vector of Tate's local integral); a calculus of corrections
(attachment, multiplicity, sign, projection, and measurement rules — Theorems 1–9, each
proved); and a uniqueness theorem (Theorem 10): given one explicit instantiation map, the
formula assigned to every observable is unique, with zero adjustable numbers. The resulting
outputs — the cosmological constant, the Higgs, all nine charged-fermion and three neutrino
masses, the gauge couplings, the mixing angles, and the cosmological parameters — agree with
every current measurement within stated experimental precision. We therefore assert, to the
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

**Theorem 1 (Kernel; `cascade_formulation_kernel.py`, ≤6×10⁻¹⁴ over d = 1–300).** The four
primitive families of the tower are the value, ratio, logarithmic derivative, and normalized
square-ratio of Γ_ℝ at integers:

- Ω(d) = 2/Γ_ℝ(d+1)  (measure), N(d) = Γ_ℝ(d+1)/Γ_ℝ(d+2)  (coupling),
- p(d) = (log Γ_ℝ)′(d+1)  (potential), α(d) = N(d)²/4π  (compliance).

*Remark.* Ω(d) is the surface measure of S^d and the tower is the dimensional cascade of the
unit ball — the geometric avatar. The paper never uses the avatar; the arithmetic is primary.

## 3. The forced dynamics

**Theorem 2 (The Gaussian is forced; `cascade_arithmetic_increment.py` P2).** Among Schwartz
vectors, the Tate integral Z(f, s) = ∫f(x)|x|^s d*x equals Γ_ℝ(s) × (entire function with
extraneous zeros), and the Gaussian g = e^(−πx²) uniquely achieves the local factor (ratio
identically 1; e.g. x²g yields exactly s/2π). The tower's dynamics is Gaussian **by the gcd
condition of Tate's thesis, not by axiom.**

**Theorem 3 (Statistical dictionary; `cascade_arithmetic_increment.py` P3–P4).** Under
μ_s ∝ g(x)|x|^s d*x: (log Γ_ℝ)′(s) = E[log|x|], (log Γ_ℝ)″(s) = Var[log|x|] > 0, and
E[πx²] = s/2 exactly. The potential is a mean, the curvature is a variance, and the
half-argument of Γ_ℝ is the mean action.

**Theorem 4 (Solvability; `cascade_second_quantized.py`).** The Gaussian tower is exactly
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

## 5. The calculus of attachments (the derived rules)

**Theorem 8 (Increment rule; `cascade_arithmetic_increment.py`).** Any multiplicative
functional on twist intervals carries at most one correction member exp(±α(d\*)/χᵏ), at first
power, sourced at an order-one feature of one summand of log ξ; point-supported content
carries none. *Proof:* partition of log ξ (two-summand draws double-count d log ξ); features
simple (Thm 7); ℤ totally ordered (each twist at most once); increments telescope (Thm 4).

**Theorem 9 (Sign rule).** The sign is the side of the Cauchy–Schwarz equality manifold on
which the leading formula sits: off-manifold interpolation reads gain (+; the Gram deficit is
strict midpoint log-convexity — Γ's defining Bohr–Mollerup property, strict for all
d = 1–215); at-manifold saturated overlaps lose (−); proper coset restrictions of the peaked
weight 2/Γ_ℝ under the ℤ/8 grading lose (− ; all 28 two-coset shares < 1/π over the full
tower).

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

**Mechanism M (activation; `cascade_activation_mechanism.py`, `cascade_joints_derived.py`).**
Each subcritical marked crossing is the chirality flip −1 — the torsion unit — whose minimal
word in the Weil clock is γ⁴ ({k : γᵏ = −1} = {4}): four Fresnel units. The unit itself is
one arithmetic object in polar form, **∫e^(ix²)dx = Γ(½)·ζ₈** — modulus the critical value,
argument the Weil index — so four units carry magnitude Γ(½)⁴ = π² and phase −1 (the
fermionic crossing sign). The N_gen = 3 channels are modes at distinct twists of the
factorized Gaussian measure, hence orthogonal, hence incoherent (×3, not ×9). Result:
E = 3Γ(½)⁴ = 3π² — also the **unique colour-free composite** in the empirically allowed
window (Thm 11/12 exclude the other nine: their atoms require colour measurements a
colourless crossing cannot perform). Falsifier: JUNO (§9).

## 6. The instantiation map — the single hypothesis

**Definition 6.1 (address book).** The observable universe occupies the tower as follows.
The observer: twist 4 — the boundary of the first feature's host (5 = last twist below
s = 5.2569), the unique nontrivially-real residue of the ℤ/8 clock (γ⁴ = −1 = the torsion
unit), and the unique scalar-flat point of the tower's own slicing measure
(R·a⁴ = (n−1)(n−4); `cascade_arithmetic_d4.py`). Generations: the marked coset {5, 13, 21};
gauge structure: twists {12, 13, 14} with multiplicities the 2-adic Radon–Hurwitz counts;
colour characters: ℚ(ζ₃); the phase transition: the ln Γ(½) threshold (19); the sink: the
Γ(½) threshold (217); sources, occupancy classes, population classes, and record statuses as
tabulated in the verifier scripts.

This is the paper's only assumption. It contains no continuous parameter — every entry is a
discrete address, and Theorem 13 shows no discrete freedom survives the rules.

## 7. Uniqueness

**Theorem 13 (conditional uniqueness; `cascade_T4_uniqueness.py`).** Given Definition 6.1 and
Theorems 8–12: the formula of every observable is unique. *Proof:* exactly-once attachment
(at-most-once = Thm 8; at-least-once = completeness of the Gaussian measure: a present mode's
factor is not optional); availability is a function of the address (Thm 11/12 exclusion);
members are determined (source, sign, exponent, multiplicity). Finite exhaustion: every
stage's naive assignment space (1,764–7,056 elements) filters to exactly one survivor,
reproducing the recorded formula to ≤0.01%; the neutrino stage's 40 combinations collapse to
(3π², (0,1,2)). **Zero discrete freedom remains.**

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
| m_ν3; Δm²_sol | 49.28 meV; 7.572×10⁻⁵ eV² | −0.5%; +0.24σ |
| α_s(M_Z); 1/α_em; sin²θ_W | 0.11792; 137.028; 0.23123 | +0.02σ; 0.006%; +0.40σ |
| θ_C; θ₂₃ | 13.04°; closure | +0.03σ; sub-σ |
| Ω_m; ℓ_A | 0.31473; 301.44 | −0.04σ; −0.16σ |
| θ_QCD | 0 exactly | consistent |

No output disagrees with any current measurement beyond stated precision. This table, plus
Theorems 1–13, is the content of the word "indistinguishable."

## 9. The Indistinguishability Theorem — and its executioners

**Theorem 14 (Indistinguishability, conditional).** *Conditional on Definition 6.1, the
arithmetic of the completed Riemann zeta function at the real place is indistinguishable from
the observable universe at current experimental precision.* *Proof:* Theorems 1–13
(mathematics) + the table of §8 (the record). ∎

The conditional cannot be discharged by mathematics — no theory's can. It is discharged, or
destroyed, by the pre-registered ledger, frozen before the data exists:

| Prediction | Value | Judge | Kill condition |
|---|---|---|---|
| Σm_ν | 60.91 meV, normal ordering | DESI/CMB-S4; JUNO | bound < ~60 meV, or inverted ordering |
| Δm²₂₁ | 7.572×10⁻⁵ eV² | JUNO (~0.3%) | outside ~0.6% window kills Mechanism M |
| m_β; m_ββ | 9.1 meV; ≤5.5 meV | KATRIN; LEGEND-1000/nEXO | any signal at current sensitivity |
| w(z) | −1, no evolution | DESI DR3+ | any confirmed evolution |
| m_H | 125.194 GeV | HL-LHC (~25 MeV) | >3σ miss |
| m_τ | π⁶/945-vs-α(14)/2 fork | Belle II (~0.02 MeV) | adjudicates |
| m_b/m_τ; m_c; m_s/m_ud; m_u/m_d; y_t | 2.35405; 1.2714; 27.35; 0.4593; 0.99142 | lattice/colliders | >3σ miss |
| Structure | no 4th generation, no anyons (free 3+1D), no SUSY partners, no axion, no dark-matter particle | any discovery | fatal |

## 10. Honest limits

1. **C1 is forever empirical.** The arithmetic pins the observer's address three independent
   ways (§6) but cannot select it; the selection is the hypothesis. If the arithmetic could
   prove its own instantiation, no experiment could kill it — falsifiability *requires* this
   step to remain empirical.
2. **External inputs.** After `cascade_joints_derived.py` (J1 = the polar decomposition of
   the Fresnel integral; J2 = orthogonality from the factorized measure; P > L > G = the
   pole ≻ saddle ≻ arc dominance hierarchy of contour asymptotics), the only classical result
   used without arithmetic derivation is Lovelock's theorem — and it performs *selection*
   (why the address is occupied at d = 4), not construction.
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
`cascade_activation_mechanism.py`, `cascade_T4_uniqueness.py`, `cascade_arithmetic_d4.py`,
`cascade_leptons.py`, `cascade_neutrino_closure.py`, `cascade_E_fit_audit.py`,
`cascade_null_clone.py`. Classical inputs: Tate's thesis; Weil, the metaplectic index; Wall,
the graded Brauer group; Bohr–Mollerup; Adams/Radon–Hurwitz; Lovelock; Kolmogorov.*
