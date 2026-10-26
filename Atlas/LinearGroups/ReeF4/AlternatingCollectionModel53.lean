import Atlas.LinearGroups.ReeF4.AlternatingCollection53
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternatingCollection_53 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u1 u2 : F) :
    positiveLongFactor hcard 2 u2 * positiveLongFactor hcard 1 u1 =
    positiveLongFactor hcard 1 (u1) * (positiveLongFactor hcard 2 (u2)) := by
  apply model_ext_of_carrier_action
  intro w
  simp only [positiveShortFactor, positiveLongFactor, modelProduct_apply,
    alternatingShortFactor_pair_val, alternatingLongFactor_val]
  exact alternatingCollection_53_formula hcard u1 u2 w.val
end Atlas.ReeF4
