import Atlas.LinearGroups.ReeF4.ShortRootCoordinateComparison

/-! The fourth power and explicit inverse of the concrete source operator.
These are uniform characteristic-two identities, independent of field size. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private theorem four_zero : (4 : F) = 0 := by
  linear_combination 2 * (CharTwo.two_eq_zero (R := F))

private theorem eight_zero : (8 : F) = 0 := by
  linear_combination 4 * (CharTwo.two_eq_zero (R := F))

private theorem sixteen_zero : (16 : F) = 0 := by
  linear_combination 8 * (CharTwo.two_eq_zero (R := F))

private theorem six_zero : (6 : F) = 0 := by
  linear_combination 3 * (CharTwo.two_eq_zero (R := F))

private theorem ten_zero : (10 : F) = 0 := by
  linear_combination 5 * (CharTwo.two_eq_zero (R := F))

private theorem fourteen_zero : (14 : F) = 0 := by
  linear_combination 7 * (CharTwo.two_eq_zero (R := F))

private theorem eighteen_zero : (18 : F) = 0 := by
  linear_combination 9 * (CharTwo.two_eq_zero (R := F))

private theorem twentyFour_zero : (24 : F) = 0 := by
  linear_combination 12 * (CharTwo.two_eq_zero (R := F))

private theorem twentySix_zero : (26 : F) = 0 := by
  linear_combination 13 * (CharTwo.two_eq_zero (R := F))

set_option maxHeartbeats 1000000 in
theorem shortRootFormula_fourth (w : Carrier F) :
    shortRootFormula (shortRootFormula (shortRootFormula (shortRootFormula w))) = w := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [shortRootFormula] <;> ring_nf <;>
      simp [CharTwo.two_eq_zero, four_zero, eight_zero, sixteen_zero,
        six_zero, ten_zero, fourteen_zero, eighteen_zero, twentyFour_zero, twentySix_zero]
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [shortRootFormula] <;> ring_nf <;>
      simp [CharTwo.two_eq_zero, four_zero, eight_zero, sixteen_zero,
        six_zero, ten_zero, fourteen_zero, eighteen_zero, twentyFour_zero, twentySix_zero]

private theorem shortRootCoordinateLinear_val (w : TraceZero F) :
    (shortRootCoordinateLinear w).val = shortRootFormula w.val := rfl

set_option maxHeartbeats 1000000 in
theorem shortRootCoordinateLinear_fourth :
    (shortRootCoordinateLinear (F := F)).comp
      (shortRootCoordinateLinear.comp (shortRootCoordinateLinear.comp shortRootCoordinateLinear)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  apply Subtype.ext
  simpa only [shortRootCoordinateLinear_val] using shortRootFormula_fourth w.val

theorem shortRootLinear_fourth :
    (shortRootLinear (F := F)).comp
      (shortRootLinear.comp (shortRootLinear.comp shortRootLinear)) = LinearMap.id := by
  rw [← shortRootCoordinateLinear_eq]
  exact shortRootCoordinateLinear_fourth

def shortRootEquiv : TraceZero F ≃ₗ[F] TraceZero F :=
  LinearEquiv.ofLinearMap shortRootLinear
    (shortRootLinear.comp (shortRootLinear.comp shortRootLinear))
    shortRootLinear_fourth
    (by simpa only [LinearMap.comp_assoc] using shortRootLinear_fourth (F := F))

@[simp] theorem shortRootEquiv_apply (w : TraceZero F) :
    shortRootEquiv w = shortRootLinear w := rfl

end Atlas.ReeF4
