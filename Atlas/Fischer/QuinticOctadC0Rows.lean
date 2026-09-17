import Atlas.Fischer.QuinticOctadC0SingleRows

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem quinticOctadBlockWUW_WWW_permute (D E F : Octad) :
    quinticOctadBlockWUW_WWW D E F = quinticOctadBlockUWW_WWW E D F := by
  unfold quinticOctadBlockWUW_WWW quinticOctadBlockUWW_WWW
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  exact coordinateQuinticTerm_swap_first _ _ _ _ _ _ _ _ _

theorem quinticOctadBlockWWU_WWW_permute (D E F : Octad) :
    quinticOctadBlockWWU_WWW D E F = quinticOctadBlockUWW_WWW F E D := by
  rw [← quinticOctadBlockWUW_WWW_permute E F D]
  unfold quinticOctadBlockWWU_WWW quinticOctadBlockWUW_WWW
  rw [sum_three_left_rotate]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum_three_left_rotate]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro a ha
  exact coordinateQuinticTerm_rotate _ _ _ _ _ _ _ _ _

/-- All three actual C0 orientations on every Golay sextet triangle. -/
theorem quinticOctad_C0_sextet (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E) :
    quinticOctadC0 D E F =
      (1125 / 16 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  have hr := octadTriangle_rotations D E F 0 (by simpa only [add_zero] using hF)
  have hD : octadWord D = octadWord F + octadWord E := by
    simpa only [add_zero, add_comm] using hr.1
  have hF' : octadWord F = octadWord E + octadWord D := by
    simpa only [add_comm] using hF
  unfold quinticOctadC0
  rw [quinticOctadBlockWUW_WWW_permute, quinticOctadBlockWWU_WWW_permute,
    quinticOctad_C0_single_sextet D E F hF,
    quinticOctad_C0_single_sextet E D F hF',
    quinticOctad_C0_single_sextet F E D hD]
  rw [coordinateCubic_swap_first (.inr E) (.inr D) (.inr F),
    coordinateCubic_swap_last (.inr F) (.inr E) (.inr D),
    coordinateCubic_swap_first (.inr F) (.inr D) (.inr E),
    coordinateCubic_swap_last (.inr D) (.inr F) (.inr E)]
  ring

/-- All three actual C0 orientations on every Golay trio, retaining its theta phase. -/
theorem quinticOctad_C0_trio (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E + golayOne) :
    quinticOctadC0 D E F =
      (1023 / 16 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  have hr := octadTriangle_rotations D E F golayOne hF
  have hD : octadWord D = octadWord F + octadWord E + golayOne := by
    simpa only [add_comm (octadWord E) (octadWord F)] using hr.1
  have hF' : octadWord F = octadWord E + octadWord D + golayOne := by
    simpa only [add_comm (octadWord D) (octadWord E)] using hF
  unfold quinticOctadC0
  rw [quinticOctadBlockWUW_WWW_permute, quinticOctadBlockWWU_WWW_permute,
    quinticOctad_C0_single_trio D E F hF,
    quinticOctad_C0_single_trio E D F hF',
    quinticOctad_C0_single_trio F E D hD]
  rw [coordinateCubic_swap_first (.inr E) (.inr D) (.inr F),
    coordinateCubic_swap_last (.inr F) (.inr E) (.inr D),
    coordinateCubic_swap_first (.inr F) (.inr D) (.inr E),
    coordinateCubic_swap_last (.inr D) (.inr F) (.inr E)]
  ring

end Atlas.Fischer
