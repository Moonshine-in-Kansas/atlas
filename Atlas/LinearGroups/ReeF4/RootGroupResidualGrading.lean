import Atlas.LinearGroups.ReeF4.RootGroupConjugation

namespace Atlas.ReeF4
open Atlas.Albert

def shortRootResidualGrade (r : ShortRootLabel) : ℤ × ℤ :=
  ((torusConstantExponents r).2 + 2*(torusThetaExponents r).1,
   (torusConstantExponents r).1 + (torusThetaExponents r).2)

def shortRootResidualWeight {G : Type*} [CommGroup G] (u v : G)
    (r : ShortRootLabel) : G :=
  u ^ (shortRootResidualGrade r).1 * v ^ (shortRootResidualGrade r).2

theorem twistedTorusWeight_residual {G : Type*} [CommGroup G]
    (τ : G →* G) (u : G) (hu : τ (τ u) = u^2) (r : ShortRootLabel) :
    twistedTorusWeight τ (τ u) u r = shortRootResidualWeight u (τ u) r := by
  simp only [twistedTorusWeight, torusCharacter, hu, pow_two,
    shortRootResidualWeight, shortRootResidualGrade, two_mul, zpow_add, mul_zpow]
  ac_rfl

variable {F : Type*} [Field F] [CharP F 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
 theorem shortRootParameterFormula_residual_comm (τ : F →+* F) (a : F)
    (u v : Fˣ) (w : Carrier F) :
    rootDiagonalFormula (shortRootResidualWeight u v) (shortRootParameterFormula τ a w) =
      shortRootParameterFormula τ a (rootDiagonalFormula (shortRootResidualWeight u v) w) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [rootDiagonalFormula, shortRootParameterFormula,
      shortRootResidualWeight, shortRootResidualGrade, torusConstantExponents,
      torusThetaExponents]
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootDiagonalFormula, shortRootParameterFormula, shortRootResidualWeight,
        shortRootResidualGrade, torusConstantExponents, torusThetaExponents,
        Units.val_zpow_eq_zpow_val] <;> ring
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem shortRootCenterFormula_residual_comm (τ : F →+* F) (b : F)
    (u v : Fˣ) (w : Carrier F) :
    rootDiagonalFormula (shortRootResidualWeight u v) (shortRootCenterFormula τ b w) =
      shortRootCenterFormula τ b (rootDiagonalFormula (shortRootResidualWeight u v) w) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [rootDiagonalFormula, shortRootCenterFormula,
      shortRootResidualWeight, shortRootResidualGrade, torusConstantExponents,
      torusThetaExponents]
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootDiagonalFormula, shortRootCenterFormula, shortRootResidualWeight,
        shortRootResidualGrade, torusConstantExponents, torusThetaExponents,
        Units.val_zpow_eq_zpow_val] <;> ring
end Atlas.ReeF4
