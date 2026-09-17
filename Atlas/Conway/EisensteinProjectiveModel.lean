import Atlas.Conway.EisensteinScalars
import Atlas.Conway.EisensteinFrameAction

noncomputable section
namespace Atlas.Conway
open Atlas.Lattices

instance eisensteinHermitian_finite : Finite eisensteinHermitianGroup :=
  Finite.of_injective eisensteinHermitianToCo0 eisensteinHermitianToCo0_injective

/-- The quotient of the actual Co0 centralizer by its six scalar isometries.
Its definition does not assert its order or simplicity. -/
abbrev EisensteinProjectiveModel := eisensteinCentralizer ⧸ eisensteinCentralizerScalars

/-- The coordinate description of the same quotient. -/
abbrev EisensteinHermitianQuotient := eisensteinHermitianGroup ⧸ eisensteinScalarSubgroup

/-- Exact compatibility of the coordinate quotient and the actual centralizer quotient. -/
def eisensteinProjectiveComparison : EisensteinHermitianQuotient ≃* EisensteinProjectiveModel :=
  QuotientGroup.congr _ _ eisensteinCentralizerEquiv rfl

instance eisensteinProjective_finite : Finite EisensteinProjectiveModel := inferInstance

theorem eisensteinProjectiveComparison_mk (g : eisensteinHermitianGroup) :
    eisensteinProjectiveComparison (QuotientGroup.mk g) =
      QuotientGroup.mk (eisensteinCentralizerEquiv g) := rfl

end Atlas.Conway
