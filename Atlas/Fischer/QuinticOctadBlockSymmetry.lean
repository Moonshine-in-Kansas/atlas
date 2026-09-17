import Atlas.Fischer.QuinticOctadBlocks
import Atlas.Fischer.QuinticPointOctadSymmetry

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

theorem quinticOctadBlockWWW_UUU_transpose (D E F : Octad) :
    quinticOctadBlockWWW_UUU D E F = quinticOctadBlockUUU_WWW D E F := by
  unfold quinticOctadBlockWWW_UUU quinticOctadBlockUUU_WWW
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

theorem quinticOctadBlockWWW_UWW_transpose (D E F : Octad) :
    quinticOctadBlockWWW_UWW D E F = quinticOctadBlockUWW_WWW D E F := by
  unfold quinticOctadBlockWWW_UWW quinticOctadBlockUWW_WWW
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

theorem quinticOctadBlockWWW_WUW_transpose (D E F : Octad) :
    quinticOctadBlockWWW_WUW D E F = quinticOctadBlockWUW_WWW D E F := by
  unfold quinticOctadBlockWWW_WUW quinticOctadBlockWUW_WWW
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

theorem quinticOctadBlockWWW_WWU_transpose (D E F : Octad) :
    quinticOctadBlockWWW_WWU D E F = quinticOctadBlockWWU_WWW D E F := by
  unfold quinticOctadBlockWWW_WWU quinticOctadBlockWWU_WWW
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

theorem quinticOctadBlockWUW_UWW_transpose (D E F : Octad) :
    quinticOctadBlockWUW_UWW D E F = quinticOctadBlockUWW_WUW D E F := by
  unfold quinticOctadBlockWUW_UWW quinticOctadBlockUWW_WUW
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

theorem quinticOctadBlockWWU_UWW_transpose (D E F : Octad) :
    quinticOctadBlockWWU_UWW D E F = quinticOctadBlockUWW_WWU D E F := by
  unfold quinticOctadBlockWWU_UWW quinticOctadBlockUWW_WWU
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

theorem quinticOctadBlockWWU_WUW_transpose (D E F : Octad) :
    quinticOctadBlockWWU_WUW D E F = quinticOctadBlockWUW_WWU D E F := by
  unfold quinticOctadBlockWWU_WUW quinticOctadBlockWUW_WWU
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

theorem quinticOctadBlockUWW_WWU_permute (D E F : Octad) :
    quinticOctadBlockUWW_WWU D E F = quinticOctadBlockUWW_WUW D F E := by
  unfold quinticOctadBlockUWW_WWU quinticOctadBlockUWW_WUW
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

theorem sum_three_left_rotate {A B C R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid R]
    (f : A → B → C → R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  have h : (∑ a : A, ∑ bc : B × C, f a bc.1 bc.2) =
      ∑ bc : B × C, ∑ a : A, f a bc.1 bc.2 := Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using h

theorem coordinateQuinticTerm_rotate (i j k a b c p q r : CoordinateIndex) :
    coordinateQuinticTerm i j k a b c p q r =
      coordinateQuinticTerm j k i b c a q r p := by
  rw [coordinateQuinticTerm_swap_first i j k a b c p q r,
    coordinateQuinticTerm_swap_last j i k b a c q p r]

theorem quinticOctadBlockWUW_WWU_permute (D E F : Octad) :
    quinticOctadBlockWUW_WWU D E F = quinticOctadBlockUWW_WUW E F D := by
  unfold quinticOctadBlockWUW_WWU quinticOctadBlockUWW_WUW
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

/-- The six actual mixed point/octet contractions in the source B row. -/
def quinticOctadB (D E F : Octad) : Scalar :=
  quinticOctadBlockUWW_WUW D E F + quinticOctadBlockUWW_WWU D E F +
  quinticOctadBlockWUW_UWW D E F + quinticOctadBlockWUW_WWU D E F +
  quinticOctadBlockWWU_UWW D E F + quinticOctadBlockWWU_WUW D E F

/-- The three actual one-point/pure-octad contractions in the source C0 row. -/
def quinticOctadC0 (D E F : Octad) : Scalar :=
  quinticOctadBlockUWW_WWW D E F + quinticOctadBlockWUW_WWW D E F +
  quinticOctadBlockWWU_WWW D E F

/-- Exact source decomposition with all ordered internal multiplicities retained. -/
theorem coordinateQuintic_octad_four_blocks (D E F : Octad) :
    coordinateQuintic (.inr D) (.inr E) (.inr F) =
      2 * quinticOctadBlockUUU_WWW D E F + quinticOctadB D E F +
      2 * quinticOctadC0 D E F + quinticOctadBlockWWW_WWW D E F := by
  rw [coordinateQuintic_octad_blocks, quinticOctadBlockWWW_UUU_transpose,
    quinticOctadBlockWWW_UWW_transpose, quinticOctadBlockWWW_WUW_transpose,
    quinticOctadBlockWWW_WWU_transpose]
  unfold quinticOctadB quinticOctadC0
  ring

end Atlas.Fischer
