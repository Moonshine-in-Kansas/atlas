import Atlas.LinearGroups.ReeF4.AlternatingCollection30
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternatingCollection_30 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a0 b0 u1 : F) :
    positiveLongFactor hcard 1 u1 * positiveShortFactor hcard 0 a0 b0 =
    positiveShortFactor hcard 0 (a0) (b0) * (positiveShortFactor hcard 1 (0) (a0*u1) * (positiveLongFactor hcard 1 (u1))) := by
  apply model_ext_of_carrier_action
  intro w
  simp only [positiveShortFactor, positiveLongFactor, modelProduct_apply,
    alternatingShortFactor_pair_val, alternatingLongFactor_val]
  exact alternatingCollection_30_formula hcard a0 b0 u1 w.val
end Atlas.ReeF4
