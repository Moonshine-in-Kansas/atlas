import Atlas.LinearGroups.ReeF4.AlternatingCollection61
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternatingCollection_61 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u0 a3 b3 : F) :
    positiveShortFactor hcard 3 a3 b3 * positiveLongFactor hcard 0 u0 =
    positiveLongFactor hcard 0 (u0) * (positiveShortFactor hcard 1 (0) (a3*(theta F m u0)) * (positiveLongFactor hcard 1 ((theta F m a3)*u0) * (positiveShortFactor hcard 2 (0) (b3*u0+a3*(theta F m a3)*u0) * (positiveShortFactor hcard 3 (a3) (b3))))) := by
  apply model_ext_of_carrier_action
  intro w
  simp only [positiveShortFactor, positiveLongFactor, modelProduct_apply,
    alternatingShortFactor_pair_val, alternatingLongFactor_val]
  exact alternatingCollection_61_formula hcard u0 a3 b3 w.val
end Atlas.ReeF4
