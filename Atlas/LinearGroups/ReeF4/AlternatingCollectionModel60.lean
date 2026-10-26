import Atlas.LinearGroups.ReeF4.AlternatingCollection60
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternatingCollection_60 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a0 b0 a3 b3 : F) :
    positiveShortFactor hcard 3 a3 b3 * positiveShortFactor hcard 0 a0 b0 =
    positiveShortFactor hcard 0 (a0) (b0) * (positiveLongFactor hcard 0 (a3*b0) * (positiveShortFactor hcard 1 (a3*(theta F m a0)) (b3*(theta F m b0)+a0*a0*b3*(theta F m a0)+a0*b0*b3+a3*(theta F m a3)*(theta F m b0)) * (positiveLongFactor hcard 1 (b0*b3+a0*b3*(theta F m a0)) * (positiveShortFactor hcard 2 (a0*(theta F m a3)) (b0*(theta F m b3)+a3*a3*b0*(theta F m a3)+a3*b0*b3+a0*a3*a3*(theta F m a0)*(theta F m a3)+a0*a3*b3*(theta F m a0)) * (positiveLongFactor hcard 2 (a0*a3*(theta F m a3)+a0*b3) * (positiveShortFactor hcard 3 (a3) (b3))))))) := by
  apply model_ext_of_carrier_action
  intro w
  simp only [positiveShortFactor, positiveLongFactor, modelProduct_apply,
    alternatingShortFactor_pair_val, alternatingLongFactor_val]
  exact alternatingCollection_60_formula hcard a0 b0 a3 b3 w.val
end Atlas.ReeF4
