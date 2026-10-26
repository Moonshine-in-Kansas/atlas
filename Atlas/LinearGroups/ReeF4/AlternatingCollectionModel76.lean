import Atlas.LinearGroups.ReeF4.AlternatingCollection76
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternatingCollection_76 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a3 b3 u3 : F) :
    positiveLongFactor hcard 3 u3 * positiveShortFactor hcard 3 a3 b3 =
    positiveShortFactor hcard 3 (a3) (b3) * (positiveLongFactor hcard 3 (u3)) := by
  apply model_ext_of_carrier_action
  intro w
  simp only [positiveShortFactor, positiveLongFactor, modelProduct_apply,
    alternatingShortFactor_pair_val, alternatingLongFactor_val]
  exact alternatingCollection_76_formula hcard a3 b3 u3 w.val
end Atlas.ReeF4
