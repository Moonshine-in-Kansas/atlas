import Atlas.LinearGroups.ReeF4.AlternatingCollection10
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternatingCollection_10 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a0 b0 u0 : F) :
    positiveLongFactor hcard 0 u0 * positiveShortFactor hcard 0 a0 b0 =
    positiveShortFactor hcard 0 (a0) (b0) * (positiveLongFactor hcard 0 (u0)) := by
  apply model_ext_of_carrier_action
  intro w
  simp only [positiveShortFactor, positiveLongFactor, modelProduct_apply,
    alternatingShortFactor_pair_val, alternatingLongFactor_val]
  exact alternatingCollection_10_formula hcard a0 b0 u0 w.val
end Atlas.ReeF4
