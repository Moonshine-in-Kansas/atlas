import Atlas.LinearGroups.ReeF4.AlternatingCollection50
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternatingCollection_50 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a0 b0 u2 : F) :
    positiveLongFactor hcard 2 u2 * positiveShortFactor hcard 0 a0 b0 =
    positiveShortFactor hcard 0 (a0) (b0) * (positiveShortFactor hcard 1 (0) (b0*u2) * (positiveLongFactor hcard 1 ((theta F m a0)*u2) * (positiveShortFactor hcard 2 (0) (a0*(theta F m u2)) * (positiveLongFactor hcard 2 (u2))))) := by
  apply model_ext_of_carrier_action
  intro w
  simp only [positiveShortFactor, positiveLongFactor, modelProduct_apply,
    alternatingShortFactor_pair_val, alternatingLongFactor_val]
  exact alternatingCollection_50_formula hcard a0 b0 u2 w.val
end Atlas.ReeF4
