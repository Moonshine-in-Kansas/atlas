import Atlas.Fischer.ParkerStandardAutomorphisms
import Atlas.Fischer.ParkerMathieuLiftExistence

namespace Atlas.Fischer
open Atlas.Codes

/-- A lift chosen separately for each element; no multiplicative section is asserted. -/
noncomputable def parkerStandardLift (g : Mathieu24CodeModel) : ParkerStandardGroup :=
  ⟨parkerMathieuLift g, parkerMathieuLift_multiply g, parkerMathieuLift_fixes_sign g,
    g, parkerMathieuLift_code g⟩

theorem parkerStandardProjection_lift (g : Mathieu24CodeModel) :
    parkerStandardProjection (parkerStandardLift g) = g := by
  apply parkerCodeEquiv_faithful
  intro a
  exact (parkerStandardProjection_spec (parkerStandardLift g) (a, 0)).symm

theorem parkerStandardProjection_surjective : Function.Surjective parkerStandardProjection := by
  intro g
  exact ⟨parkerStandardLift g, parkerStandardProjection_lift g⟩

end Atlas.Fischer
