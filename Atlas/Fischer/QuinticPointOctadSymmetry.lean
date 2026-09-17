import Atlas.Fischer.QuinticPointOctadBlocks
import Atlas.Fischer.QuinticSymmetry

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- Interchanging the two internal cubic vertices does not conjugate the contraction. -/
theorem coordinateQuinticTerm_transpose (i j k a b c p q r : CoordinateIndex) :
    coordinateQuinticTerm i j k a b c p q r =
      coordinateQuinticTerm a b c i j k p q r := by
  unfold coordinateQuinticTerm coordinateQuinticCubicProduct
  rw [coordinateCubic_swap_first a i p, coordinateCubic_swap_first b j q,
    coordinateCubic_swap_first c k r]
  ring

theorem sum_three_three_swap {I J K A B C R : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype A] [Fintype B] [Fintype C]
    [AddCommMonoid R] (f : I → J → K → A → B → C → R) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, f i j k a b c) =
      ∑ a, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k, f i j k a b c := by
  have h : (∑ x : I × J × K, ∑ y : A × B × C,
      f x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2) =
      ∑ y : A × B × C, ∑ x : I × J × K,
        f x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 := Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using h

theorem quinticPointOctadUWW_UUU_eq (p : Omega) (D : Octad) :
    quinticPointOctadUWW_UUU p D = quinticPointOctadUUU_UWW p D := by
  unfold quinticPointOctadUWW_UUU quinticPointOctadUUU_UWW
  rw [sum_three_three_swap]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  exact coordinateQuinticTerm_transpose _ _ _ _ _ _ _ _ _

theorem quinticPointOctadWWW_WUW_eq (p : Omega) (D : Octad) :
    quinticPointOctadWWW_WUW p D = quinticPointOctadWUW_WWW p D := by
  unfold quinticPointOctadWWW_WUW quinticPointOctadWUW_WWW
  rw [sum_three_three_swap]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  exact coordinateQuinticTerm_transpose _ _ _ _ _ _ _ _ _

theorem quinticPointOctadWWW_WWU_eq (p : Omega) (D : Octad) :
    quinticPointOctadWWW_WWU p D = quinticPointOctadWWU_WWW p D := by
  unfold quinticPointOctadWWW_WWU quinticPointOctadWWU_WWW
  rw [sum_three_three_swap]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  exact coordinateQuinticTerm_transpose _ _ _ _ _ _ _ _ _

theorem quinticPointOctadWWU_WUW_eq (p : Omega) (D : Octad) :
    quinticPointOctadWWU_WUW p D = quinticPointOctadWUW_WWU p D := by
  unfold quinticPointOctadWWU_WUW quinticPointOctadWUW_WWU
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  exact coordinateQuinticTerm_swap_last _ _ _ _ _ _ _ _ _

theorem quinticPointOctadWWU_WWW_eq (p : Omega) (D : Octad) :
    quinticPointOctadWWU_WWW p D = quinticPointOctadWUW_WWW p D := by
  unfold quinticPointOctadWWU_WWW quinticPointOctadWUW_WWW
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  exact coordinateQuinticTerm_swap_last _ _ _ _ _ _ _ _ _

/-- Five actual contractions, with multiplicities forced by tensor symmetries. -/
theorem coordinateQuintic_point_octad_five_blocks (p : Omega) (D : Octad) :
    coordinateQuintic (.inl p) (.inr D) (.inr D) =
      2 * quinticPointOctadUUU_UWW p D + quinticPointOctadUWW_UWW p D +
      2 * quinticPointOctadWUW_WWU p D + 4 * quinticPointOctadWUW_WWW p D +
      quinticPointOctadWWW_WWW p D := by
  rw [coordinateQuintic_point_octad_blocks, quinticPointOctadUWW_UUU_eq,
    quinticPointOctadWWW_WUW_eq, quinticPointOctadWWW_WWU_eq,
    quinticPointOctadWWU_WUW_eq, quinticPointOctadWWU_WWW_eq]
  ring

end Atlas.Fischer
