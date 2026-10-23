import KaiserNine
import HalfPlaneJoinsFinal

/-! Stack review 3: round 468's `λ₁` prefactor `(59/6)a` follows from round 220's `lam_nine` (`9a`). -/

open Pilot1ca in
example : type_of% @HalfPlaneJoins.lam_prefactor_eleven_twelfths := by
  obtain ⟨K, hK, h⟩ := Kaiser.lam_nine
  refine ⟨K, hK, fun a ha => (h a ha).trans ?_⟩
  gcongr
  linarith
