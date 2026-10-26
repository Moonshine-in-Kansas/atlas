import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable.ParentLt
import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable.ParentCoordinates
import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable.WordSteps

/-! E6 minuscule certificate component: Words. -/
namespace Atlas.Chevalley.E6MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem wordAction_append (u v : List (Fin 6)) (x : Vector) : wordAction (u ++ v) x = wordAction v (wordAction u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons i u ih => exact ih (reflectSimple i x)
theorem weight_word_coordinates (a : Weight) :
    wordAction (weightWord a) (Pi.single selectedNode 1) = coordinates a := by
  induction a using Fin.strong_induction_on with
  | h a ih =>
    by_cases hz : a = 0
    · subst a; decide
    · rw [word_step a hz, wordAction_append, ih (parent a) (parent_lt a hz)]
      exact (parent_coordinates a hz).symm

end Atlas.Chevalley.E6MinusculeTable
