import Atlas.LinearGroups.ReeF4.AlternatingCollection21
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternatingCollection_21 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u0 a1 b1 : F) :
    positiveShortFactor hcard 1 a1 b1 * positiveLongFactor hcard 0 u0 =
    positiveLongFactor hcard 0 (u0) * (positiveShortFactor hcard 1 (a1) (b1)) := by
  apply model_ext_of_carrier_action
  intro w
  simp only [positiveShortFactor, positiveLongFactor, modelProduct_apply,
    alternatingShortFactor_pair_val, alternatingLongFactor_val]
  exact alternatingCollection_21_formula hcard u0 a1 b1 w.val
end Atlas.ReeF4
