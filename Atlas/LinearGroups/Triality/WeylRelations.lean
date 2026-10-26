import Atlas.LinearGroups.Triality.Torus
import Atlas.LinearGroups.Triality.WeylGenerators

/-! Exact relations of the actual Weyl lifts in every characteristic. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem shortWeyl_square : shortWeyl F K * shortWeyl F K = torusMap F K (-1,1) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (shortWeyl F K).val ((shortWeyl F K).val x) = (torusMap F K (-1,1)).val x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [shortWeyl_apply,torusMap,torusWeights,diagonalEmbedding,diagonalLinear,sigmaUnit,baseUnit]

theorem longWeyl_square : longWeyl F K * longWeyl F K = torusMap F K (1,-1) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (longWeyl F K).val ((longWeyl F K).val x) = (torusMap F K (1,-1)).val x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [longWeyl_apply,torusMap,torusWeights,diagonalEmbedding,diagonalLinear,sigmaUnit,baseUnit]

theorem weyl_braid :
    shortWeyl F K * longWeyl F K * shortWeyl F K * longWeyl F K * shortWeyl F K * longWeyl F K =
    longWeyl F K * shortWeyl F K * longWeyl F K * shortWeyl F K * longWeyl F K * shortWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul,LinearEquiv.mul_apply,shortWeyl_apply,longWeyl_apply]

theorem weyl_coxeter_six : (shortWeyl F K * longWeyl F K)^6 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [pow_succ,Subgroup.coe_mul,LinearEquiv.mul_apply,shortWeyl_apply,longWeyl_apply]

end Atlas.Triality
