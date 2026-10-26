import Atlas.LinearGroups.ReeF4.RootGroupConjugation

namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [CharP F 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
 theorem shortRootParameterFormula_graded_conjugation (τ : F →+* F)
    (u : Fˣ) (a : F) (w : Carrier F) :
    rootDiagonalFormula (fun r => (shortRootGradingWeight u (Units.map τ.toMonoidHom u) r)⁻¹)
      (shortRootParameterFormula τ a (rootDiagonalFormula
        (shortRootGradingWeight u (Units.map τ.toMonoidHom u)) w)) =
      shortRootParameterFormula τ ((u : F)*a) w := by
  have hu : (u : F) ≠ 0 := Units.ne_zero u
  have hv : τ (u : F) ≠ 0 := Units.ne_zero (Units.map τ.toMonoidHom u)
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [rootDiagonalFormula, shortRootParameterFormula,
        shortRootGradingWeight, shortRootGrade, torusConstantExponents,
        torusThetaExponents, Units.val_zpow_eq_zpow_val, map_mul] <;>
      field_simp [hu, hv] <;> ring
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootDiagonalFormula, shortRootParameterFormula,
        shortRootGradingWeight, shortRootGrade, torusConstantExponents,
        torusThetaExponents, Units.val_zpow_eq_zpow_val, map_mul] <;>
      field_simp [hu, hv] <;> ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
 theorem shortRootCenterFormula_graded_conjugation (τ : F →+* F)
    (u : Fˣ) (huu : τ (τ (u : F)) = (u : F)^2) (b : F) (w : Carrier F) :
    rootDiagonalFormula (fun r => (shortRootGradingWeight u (Units.map τ.toMonoidHom u) r)⁻¹)
      (shortRootCenterFormula τ b (rootDiagonalFormula
        (shortRootGradingWeight u (Units.map τ.toMonoidHom u)) w)) =
      shortRootCenterFormula τ ((u : F)*τ (u : F)*b) w := by
  have hu : (u : F) ≠ 0 := Units.ne_zero u
  have hv : τ (u : F) ≠ 0 := Units.ne_zero (Units.map τ.toMonoidHom u)
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [rootDiagonalFormula, shortRootCenterFormula,
        shortRootGradingWeight, shortRootGrade, torusConstantExponents,
        torusThetaExponents, Units.val_zpow_eq_zpow_val, map_mul, huu] <;>
      field_simp [hu, hv] <;> ring
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootDiagonalFormula, shortRootCenterFormula,
        shortRootGradingWeight, shortRootGrade, torusConstantExponents,
        torusThetaExponents, Units.val_zpow_eq_zpow_val, map_mul, huu] <;>
      field_simp [hu, hv] <;> ring

end Atlas.ReeF4
