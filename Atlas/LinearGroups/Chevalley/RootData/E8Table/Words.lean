import Atlas.LinearGroups.Chevalley.RootData.E8Table.ParentLt
import Atlas.LinearGroups.Chevalley.RootData.E8Table.ParentCoordinates
import Atlas.LinearGroups.Chevalley.RootData.E8Table.WordSteps

/-! E8 root certificate component: Words. Split from the checked monolithic source. -/

namespace Atlas.Chevalley.E8Table
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem root_word_coordinates (a : Root) :
    wordAction (rootWord a) (Pi.single 0 1) = coordinates a := by
  induction a using Fin.strong_induction_on with
  | h a ih =>
    by_cases hz : a = 0
    · subst a; decide
    · rw [root_word_step a hz, wordAction_append, ih (parent a) (parent_lt a hz)]
      exact (parent_coordinates a hz).symm

end Atlas.Chevalley.E8Table
