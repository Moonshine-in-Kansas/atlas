import Atlas.LinearGroups.ReeF4.AlternatingCollection62
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternatingCollection_62 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a1 b1 a3 b3 : F) :
    positiveShortFactor hcard 3 a3 b3 * positiveShortFactor hcard 1 a1 b1 =
    positiveShortFactor hcard 1 (a1) (b1) * (positiveShortFactor hcard 3 (a3) (b3)) := by
  apply model_ext_of_carrier_action
  intro w
  simp only [positiveShortFactor, positiveLongFactor, modelProduct_apply,
    alternatingShortFactor_pair_val, alternatingLongFactor_val]
  exact alternatingCollection_62_formula hcard a1 b1 a3 b3 w.val
end Atlas.ReeF4
