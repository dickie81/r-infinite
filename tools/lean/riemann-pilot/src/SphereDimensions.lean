import Mathlib
import BohrSphere

/-! # Every point of the unit sphere is a dimension, and the sphere is the line (round 396)

The owner wrote: "Only Euclidean infinite unit ball forces the volume to the surface, also infinite dimensions
means any point on that surface is a dimension, Euclidean is forced. The surface is the line. Prove in lean".
This file proves the parts that are theorems. "A dimension" is read as a direction of an orthonormal basis.

* **The points of the sphere are the basis directions** (**`mem_orthonormalBasis_iff`**, with
  `orthonormal_singleton_of_norm`): in a finite-dimensional inner product space a vector belongs to some
  orthonormal basis, as one of its vectors, if and only if it has norm `1`.
* **In infinite dimension too** (**`mem_hilbertBasis_iff`** and **`ell2_mem_hilbertBasis_iff`**): in a Hilbert
  space of any dimension, `ℓ²(ℕ)` included, a vector belongs to some Hilbert basis if and only if it has norm
  `1`.
* **The sphere is the line** (**`vF_mem_orthonormalBasis_iff`**): with round 391's `vF_mem_sphere_iff`, the
  normalised Bohr vector `v_F(s)` is a direction of some orthonormal basis of `ℂ^F` if and only if
  `Re s = ½`.

Not proved, because it is false: "only the Euclidean ball forces the volume to the surface". Round 394's
`tendsto_inner_fraction_cube` shows that the cube's volume concentrates at its surface in the same way, and
`addHaar_ball_fraction` shows it for the unit ball of every norm. The Euclidean ball is forced by self-duality
(round 394) and by orthogonality (round 395), not by volume. Nothing here constrains the zeros of ζ: RH is still
equivalent to their Bohr vectors lying on the sphere (`riemannHypothesis_iff_mem_sphere`), that is, to their
being basis directions.
-/

open Metric

namespace SphereDimensions

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A unit vector, as a one-point set, is orthonormal. -/
lemma orthonormal_singleton_of_norm {v : E} (hv : ‖v‖ = 1) :
    Orthonormal 𝕜 ((↑) : ({v} : Set E) → E) := by
  classical
  rw [orthonormal_subtype_iff_ite]
  intro x hx y hy
  rw [Set.mem_singleton_iff] at hx hy
  subst hx
  subst hy
  simp [inner_self_eq_norm_sq_to_K, hv]

/-- **In finite dimension the points of the unit sphere are exactly the basis directions.** -/
theorem mem_orthonormalBasis_iff [FiniteDimensional 𝕜 E] (v : E) :
    (∃ (u : Finset E) (b : OrthonormalBasis u 𝕜 E), ⇑b = ((↑) : u → E) ∧ v ∈ u) ↔ ‖v‖ = 1 := by
  constructor
  · rintro ⟨u, b, hb, hv⟩
    have h := b.norm_eq_one ⟨v, hv⟩
    rwa [show b ⟨v, hv⟩ = v from congrFun hb _] at h
  · intro hv
    obtain ⟨u, b, hsub, hb⟩ :=
      (orthonormal_singleton_of_norm (𝕜 := 𝕜) hv).exists_orthonormalBasis_extension
    exact ⟨u, b, hb, hsub (Set.mem_singleton v)⟩

/-- **In a Hilbert space of any dimension the points of the unit sphere are exactly the Hilbert-basis
directions.** -/
theorem mem_hilbertBasis_iff [CompleteSpace E] (v : E) :
    (∃ (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w → E) ∧ v ∈ w) ↔ ‖v‖ = 1 := by
  constructor
  · rintro ⟨w, b, hb, hv⟩
    have h := b.orthonormal.1 ⟨v, hv⟩
    rwa [show b ⟨v, hv⟩ = v from congrFun hb _] at h
  · intro hv
    obtain ⟨w, b, hsub, hb⟩ :=
      (orthonormal_singleton_of_norm (𝕜 := 𝕜) hv).exists_hilbertBasis_extension
    exact ⟨w, b, hb, hsub (Set.mem_singleton v)⟩

/-- **The infinite-dimensional case**: in `ℓ²(ℕ)` a vector is a direction of some Hilbert basis if and only
if it lies on the unit sphere. -/
theorem ell2_mem_hilbertBasis_iff (v : lp (fun _ : ℕ => ℂ) 2) :
    (∃ (w : Set (lp (fun _ : ℕ => ℂ) 2)) (b : HilbertBasis w ℂ (lp (fun _ : ℕ => ℂ) 2)),
      ⇑b = ((↑) : w → lp (fun _ : ℕ => ℂ) 2) ∧ v ∈ w) ↔ ‖v‖ = 1 :=
  mem_hilbertBasis_iff v

/-- **The sphere is the line**: the normalised Bohr vector `v_F(s)` is a direction of some orthonormal basis
of `ℂ^F` if and only if `Re s = ½`. -/
theorem vF_mem_orthonormalBasis_iff {F : Finset Nat.Primes} (hF : F.Nonempty) (s : ℂ) :
    (∃ (u : Finset (EuclideanSpace ℂ F)) (b : OrthonormalBasis u ℂ (EuclideanSpace ℂ F)),
      ⇑b = ((↑) : u → EuclideanSpace ℂ F) ∧ BohrSphere.vF F s ∈ u) ↔ s.re = 1 / 2 := by
  rw [mem_orthonormalBasis_iff, ← mem_sphere_zero_iff_norm, BohrSphere.vF_mem_sphere_iff hF]

end SphereDimensions

#print axioms SphereDimensions.orthonormal_singleton_of_norm
#print axioms SphereDimensions.mem_orthonormalBasis_iff
#print axioms SphereDimensions.mem_hilbertBasis_iff
#print axioms SphereDimensions.ell2_mem_hilbertBasis_iff
#print axioms SphereDimensions.vF_mem_orthonormalBasis_iff
