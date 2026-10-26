import Atlas.LinearGroups.ReeF4.WeylStarCompatibility
import Atlas.LinearGroups.ReeF4.WeylScalar
import Atlas.LinearGroups.ReeF4.WeylOrder
import Atlas.LinearGroups.ReeF4.PartialStabilizer

/-! Both concrete Weyl involutions belong to the full stabilizer of the actual
polynomial forms and candidate partial product. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem weyl_mem_candidatePartialStabilizer (σ : F →+* F) (g : Fin 2) :
    (⟨weylOperator g, weylOperator_mem_polynomialStabilizer g⟩ :
      traceZeroPolynomialStabilizer (F := F)) ∈ candidatePartialStabilizer σ := by
  intro u v h
  exact proposedPartialProduct_weyl g σ u v h

end Atlas.ReeF4
