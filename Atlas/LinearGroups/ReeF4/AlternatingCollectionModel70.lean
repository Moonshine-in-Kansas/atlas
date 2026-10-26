import Atlas.LinearGroups.ReeF4.AlternatingCollection70
import Atlas.LinearGroups.ReeF4.AlternatingCollectionLift
import Atlas.LinearGroups.ReeF4.PositiveRootFactors
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternatingCollection_70 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a0 b0 u3 : F) :
    positiveLongFactor hcard 3 u3 * positiveShortFactor hcard 0 a0 b0 =
    positiveShortFactor hcard 0 (a0) (b0) * (positiveLongFactor hcard 0 ((theta F m b0)*u3+a0*a0*(theta F m a0)*u3+a0*b0*u3) * (positiveShortFactor hcard 1 (b0*u3+a0*(theta F m a0)*u3) (a0*b0*b0*u3*(theta F m u3)+a0*a0*a0*(theta F m a0)*(theta F m a0)*u3*(theta F m u3)+a0*(theta F m a0)*(theta F m b0)*u3*(theta F m u3)) * (positiveLongFactor hcard 1 (b0*b0*u3*(theta F m u3)+(theta F m a0)*(theta F m b0)*u3*(theta F m u3)+a0*a0*(theta F m a0)*(theta F m a0)*u3*(theta F m u3)) * (positiveShortFactor hcard 2 (b0*(theta F m u3)) (a0*b0*b0*u3*u3*(theta F m u3)+b0*(theta F m b0)*u3*u3*(theta F m u3)+a0*(theta F m a0)*(theta F m b0)*u3*u3*(theta F m u3)+a0*a0*a0*(theta F m a0)*(theta F m a0)*u3*u3*(theta F m u3)) * (positiveLongFactor hcard 2 (a0*b0*u3*(theta F m u3)+(theta F m b0)*u3*(theta F m u3)+a0*a0*(theta F m a0)*u3*(theta F m u3)) * (positiveShortFactor hcard 3 (a0*u3) (b0*u3*(theta F m u3)) * (positiveLongFactor hcard 3 (u3)))))))) := by
  apply model_ext_of_carrier_action
  intro w
  simp only [positiveShortFactor, positiveLongFactor, modelProduct_apply,
    alternatingShortFactor_pair_val, alternatingLongFactor_val]
  exact alternatingCollection_70_formula hcard a0 b0 u3 w.val
end Atlas.ReeF4
