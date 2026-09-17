import Atlas.Fischer.QuinticPointDecomposition

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem coordinateQuinticTerm_swap_first (i j k a b c p q r : CoordinateIndex) :
    coordinateQuinticTerm i j k a b c p q r = coordinateQuinticTerm j i k b a c q p r := by
  unfold coordinateQuinticTerm coordinateQuinticCubicProduct
  rw [coordinateCubic_swap_first i j k, coordinateCubic_swap_first a b c]
  ring

theorem coordinateQuinticTerm_swap_last (i j k a b c p q r : CoordinateIndex) :
    coordinateQuinticTerm i j k a b c p q r = coordinateQuinticTerm i k j a c b p r q := by
  unfold coordinateQuinticTerm coordinateQuinticCubicProduct
  rw [coordinateCubic_swap_last i j k, coordinateCubic_swap_last a b c]
  ring

theorem coordinateQuintic_swap_first (p q r : CoordinateIndex) :
    coordinateQuintic p q r = coordinateQuintic q p r := by
  classical
  simp only [coordinateQuintic_eq_sum_term]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  exact coordinateQuinticTerm_swap_first _ _ _ _ _ _ _ _ _

theorem coordinateQuintic_swap_last (p q r : CoordinateIndex) :
    coordinateQuintic p q r = coordinateQuintic p r q := by
  classical
  simp only [coordinateQuintic_eq_sum_term]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  exact coordinateQuinticTerm_swap_last _ _ _ _ _ _ _ _ _

theorem quinticPointWUW_eq_UWW (p q r : Omega) :
    quinticPointWUW p q r = quinticPointUWW q p r := by
  classical
  unfold quinticPointWUW quinticPointUWW
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  exact coordinateQuinticTerm_swap_first _ _ _ _ _ _ _ _ _

theorem quinticPointWWU_eq_UWW (p q r : Omega) :
    quinticPointWWU p q r = quinticPointUWW r p q := by
  classical
  rw [← quinticPointWUW_eq_UWW p r q]
  unfold quinticPointWWU quinticPointWUW
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  exact coordinateQuinticTerm_swap_last _ _ _ _ _ _ _ _ _

end Atlas.Fischer
