import Atlas.LinearGroups.ReeF4.AlternatingCollection71
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternatingCollection_71 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u0 u3 : F) :
    positiveLongFactor hcard 3 u3 * positiveLongFactor hcard 0 u0 =
    positiveLongFactor hcard 0 (u0) * (positiveLongFactor hcard 1 (u3*(theta F m u0)) * (positiveLongFactor hcard 2 (u0*(theta F m u3)) * (positiveLongFactor hcard 3 (u3)))) := by
  apply model_ext_of_carrier_action
  intro w
  simp only [positiveShortFactor, positiveLongFactor, modelProduct_apply,
    alternatingShortFactor_pair_val, alternatingLongFactor_val]
  exact alternatingCollection_71_formula hcard u0 u3 w.val
end Atlas.ReeF4
