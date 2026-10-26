import Atlas.LinearGroups.ReeF4.ShortRootStarCompatibility
import Atlas.LinearGroups.ReeF4.ShortRootScalar
import Atlas.LinearGroups.ReeF4.ShortRootExactOrder
import Atlas.LinearGroups.ReeF4.PartialStabilizer

/-! The genuine order-four source operator belongs to the full stabilizer of
the actual polynomial forms and candidate partial product. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem shortRoot_mem_candidatePartialStabilizer (σ : F →+* F) :
    (⟨shortRootEquiv, shortRootEquiv_mem_polynomialStabilizer⟩ :
      traceZeroPolynomialStabilizer (F := F)) ∈ candidatePartialStabilizer σ := by
  intro u v h
  exact proposedPartialProduct_shortRoot σ u v h

end Atlas.ReeF4
