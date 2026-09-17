import Atlas.Fischer.CocodeReflectionRepresentation
import Atlas.Fischer.ParkerMultiplicativity

namespace Atlas.Fischer
open Atlas.Codes

/-- Reflecting roots include the extra operator properties; the two root equations
alone do not supply these hypotheses. -/
def IsReflectingRoot (r : Coordinates) : Prop :=
  IsRoot r ∧ RootMapAntiunitary r ∧ Function.Involutive (rootMap r) ∧
    ∀ x y, rootMap r (product x y) = product (rootMap r x) (rootMap r y)

theorem basicAxis_rootMap_product (i : Omega) (x y : Coordinates) :
    rootMap (basicAxis i) (product x y) =
      product (rootMap (basicAxis i) x) (rootMap (basicAxis i) y) := by
  rw [rootMap_basicAxis_eq_cocode, rootMap_basicAxis_eq_cocode,
    rootMap_basicAxis_eq_cocode, parkerCoordinateAction_product]

theorem basicAxis_isReflectingRoot (i : Omega) : IsReflectingRoot (basicAxis i) :=
  ⟨basicAxis_isRoot i, basicAxis_rootMap_antiunitary i, basicAxis_rootMap_involutive i,
    basicAxis_rootMap_product i⟩

end Atlas.Fischer
