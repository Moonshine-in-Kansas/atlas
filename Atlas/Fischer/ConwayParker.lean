import Atlas.Fischer.ParkerRightAction
import Atlas.Fischer.ReflectingRoots
import Atlas.Fischer.ParkerAlgebraRepresentation
import Atlas.Fischer.ParkerStandardOrder
import Atlas.Fischer.ParkerCenter
import Atlas.Fischer.CubicSymmetry
import Atlas.Fischer.CocodeReflectionRepresentation
import Atlas.Fischer.ScalarAutomorphisms
import Atlas.Fischer.RootPhases
import Atlas.Fischer.RootRigidity
import Atlas.Fischer.RootCovariance
import Atlas.Fischer.WittDuads

/- Public aliases for the actual coordinate construction. No group or
multiplication is replaced, and no Fischer group is assumed here. -/
noncomputable section
namespace Atlas.Fischer.ConwayParker

abbrev CoefficientField := Atlas.Fischer.Scalar
abbrev Model := Atlas.Fischer.Coordinates
abbrev CodeLoop := Atlas.Fischer.ParkerLoop
abbrev Cocode := Atlas.Fischer.Cocode
abbrev StandardGroup := Atlas.Fischer.ParkerStandardGroup
abbrev StandardPlus := Atlas.Fischer.parkerStandardPlus
abbrev ScalarPhases := Atlas.Fischer.Mu3
abbrev SemilinearAutomorphism := Atlas.Fischer.SemilinearAlgebraAutomorphism
abbrev standardEmbedding := Atlas.Fischer.parkerAlgebraRepresentation
abbrev scalarEmbedding := Atlas.Fischer.scalarAlgebraRepresentation
abbrev product : Model → Model → Model := Atlas.Fischer.product
abbrev hermitian : Model → Model → CoefficientField := Atlas.Fischer.hermitian
abbrev IsRoot : Model → Prop := Atlas.Fischer.IsRoot
abbrev IsReflectingRoot : Model → Prop := Atlas.Fischer.IsReflectingRoot
abbrev rootMap : Model → Model → Model := Atlas.Fischer.rootMap
abbrev basicRoot : Atlas.Codes.Omega → Model := Atlas.Fischer.basicAxis

theorem dimension : Module.finrank CoefficientField Model = 783 := coordinates_dimension

theorem cocode_order : Nat.card Cocode = 4096 := cocode_card

theorem standard_order : Nat.card StandardGroup = 1002795171840 := parkerStandardGroup_order_value

theorem standard_plus_order : Nat.card StandardPlus = 501397585920 := parkerStandardPlus_order_value

theorem scalar_phase_order : Nat.card ScalarPhases = 3 := mu3_card

theorem product_commutative (x y : Model) : product x y = product y x := product_comm x y

theorem product_conjugate_left (a : CoefficientField) (x y : Model) :
    product (a • x) y = star a • product x y := product_smul_left a x y

theorem product_conjugate_right (a : CoefficientField) (x y : Model) :
    product x (a • y) = star a • product x y := product_smul_right a x y

theorem standard_preserves_product (g : StandardGroup) (x y : Model) :
    parkerCoordinateAction g (product x y) =
      product (parkerCoordinateAction g x) (parkerCoordinateAction g y) :=
  parkerCoordinateAction_product g x y

theorem standard_embedding_injective : Function.Injective standardEmbedding :=
  parkerAlgebraRepresentation_injective

theorem scalar_embedding_injective : Function.Injective scalarEmbedding :=
  scalarAlgebraRepresentation_injective

theorem basic_root (i : Atlas.Codes.Omega) : IsRoot (basicRoot i) := basicAxis_isRoot i

theorem basic_reflection_involutive (i : Atlas.Codes.Omega) :
    Function.Involutive (rootMap (basicRoot i)) := basicAxis_rootMap_involutive i

theorem basic_reflection_antiunitary (i : Atlas.Codes.Omega) :
    RootMapAntiunitary (basicRoot i) := basicAxis_rootMap_antiunitary i

theorem basic_reflecting_root (i : Atlas.Codes.Omega) : IsReflectingRoot (basicRoot i) :=
  basicAxis_isReflectingRoot i

end Atlas.Fischer.ConwayParker
