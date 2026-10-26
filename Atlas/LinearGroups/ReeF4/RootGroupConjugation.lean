import Atlas.LinearGroups.ReeF4.RootGroupCoordinates
import Atlas.LinearGroups.ReeF4.RootGroupGrading
import Atlas.LinearGroups.ReeF4.TorusDiagonal

/-! The parameterized short-root operator is a genuine diagonal conjugate of
Wilson's source element when the parameter is nonzero. The formula below is
a small rational identity in two units, independent of a target group order. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [CharP F 2]

set_option maxHeartbeats 3000000 in
theorem shortRootGraded_conjugation (τ : F →+* F) (u : Fˣ) (w : Carrier F) :
    rootDiagonalFormula (fun r => (shortRootGradingWeight u (Units.map τ.toMonoidHom u) r)⁻¹)
      (shortRootFormula (rootDiagonalFormula
        (shortRootGradingWeight u (Units.map τ.toMonoidHom u)) w)) =
      shortRootParameterFormula τ (u : F) w := by
  have hu : (u : F) ≠ 0 := Units.ne_zero u
  have hv : τ (u : F) ≠ 0 := Units.ne_zero (Units.map τ.toMonoidHom u)
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [rootDiagonalFormula, shortRootFormula, shortRootParameterFormula,
        shortRootGradingWeight, shortRootGrade, torusConstantExponents,
        torusThetaExponents, Units.val_zpow_eq_zpow_val] <;>
      field_simp [hu, hv] <;> ring
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootDiagonalFormula, shortRootFormula, shortRootParameterFormula,
        shortRootGradingWeight, shortRootGrade, torusConstantExponents,
        torusThetaExponents, Units.val_zpow_eq_zpow_val] <;>
      field_simp [hu, hv] <;> ring

end Atlas.ReeF4
