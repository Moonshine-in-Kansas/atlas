import Atlas.LinearGroups.ReeF4.RootGroupCoordinates

/-! Draft uniform polynomial laws; all coefficients are checked in the ambient
characteristic-two ring. Only the square-of-twist identity enters the x-law. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private theorem four_zero : (4 : F) = 0 := by
  linear_combination 2 * (CharTwo.two_eq_zero (R := F))
private theorem six_zero : (6 : F) = 0 := by
  linear_combination 3 * (CharTwo.two_eq_zero (R := F))
private theorem eight_zero : (8 : F) = 0 := by
  linear_combination 4 * (CharTwo.two_eq_zero (R := F))
private theorem ten_zero : (10 : F) = 0 := by
  linear_combination 5 * (CharTwo.two_eq_zero (R := F))
private theorem twelve_zero : (12 : F) = 0 := by
  linear_combination 6 * (CharTwo.two_eq_zero (R := F))
private theorem sixteen_zero : (16 : F) = 0 := by
  linear_combination 8 * (CharTwo.two_eq_zero (R := F))

set_option maxHeartbeats 2000000 in
theorem shortRootCenterFormula_add (τ : F →+* F) (a b : F) (w : Carrier F) :
    shortRootCenterFormula τ a (shortRootCenterFormula τ b w) =
      shortRootCenterFormula τ (a+b) w := by
  apply Prod.ext
  · funext i
    fin_cases i <;> apply sub_eq_zero.mp <;>
      simp [shortRootCenterFormula, sub_eq_add_neg, CharTwo.neg_eq] <;>
      ring_nf <;> simp [CharTwo.two_eq_zero, four_zero, six_zero, eight_zero]
  · funext i j
    fin_cases i <;> fin_cases j <;> apply sub_eq_zero.mp <;>
      simp [shortRootCenterFormula, sub_eq_add_neg, CharTwo.neg_eq] <;>
      ring_nf <;> simp [CharTwo.two_eq_zero, four_zero, six_zero, eight_zero]

set_option maxHeartbeats 3000000 in
theorem shortRootParameterFormula_center_comm (τ : F →+* F) (a b : F) (w : Carrier F) :
    shortRootParameterFormula τ a (shortRootCenterFormula τ b w) =
      shortRootCenterFormula τ b (shortRootParameterFormula τ a w) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> apply sub_eq_zero.mp <;>
      simp [shortRootParameterFormula, shortRootCenterFormula, sub_eq_add_neg, CharTwo.neg_eq] <;>
      ring_nf <;> simp [CharTwo.two_eq_zero, four_zero, six_zero, eight_zero]
  · funext i j
    fin_cases i <;> fin_cases j <;> apply sub_eq_zero.mp <;>
      simp [shortRootParameterFormula, shortRootCenterFormula, sub_eq_add_neg, CharTwo.neg_eq] <;>
      ring_nf <;> simp [CharTwo.two_eq_zero, four_zero, six_zero, eight_zero]

set_option maxHeartbeats 4000000 in
theorem shortRootParameterFormula_mul (τ : F →+* F) (a b : F)
    (ha : τ (τ a) = a^2) (w : Carrier F) :
    shortRootParameterFormula τ a (shortRootParameterFormula τ b w) =
      shortRootParameterFormula τ (a+b) (shortRootCenterFormula τ (τ a*b) w) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> apply sub_eq_zero.mp <;>
      simp [shortRootParameterFormula, shortRootCenterFormula, ha,
        sub_eq_add_neg, CharTwo.neg_eq] <;>
      ring_nf <;> simp [CharTwo.two_eq_zero, four_zero, six_zero, eight_zero,
        ten_zero, twelve_zero, sixteen_zero]
  · funext i j
    fin_cases i <;> fin_cases j <;> apply sub_eq_zero.mp <;>
      simp [shortRootParameterFormula, shortRootCenterFormula, ha,
        sub_eq_add_neg, CharTwo.neg_eq] <;>
      ring_nf <;> simp [CharTwo.two_eq_zero, four_zero, six_zero, eight_zero,
        ten_zero, twelve_zero, sixteen_zero]

end Atlas.ReeF4
