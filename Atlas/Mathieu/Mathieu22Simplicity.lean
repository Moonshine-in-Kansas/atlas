import Atlas.Mathieu.Mathieu21Simplicity

namespace Atlas.Codes
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

theorem mathieu22_simple (a : Omega) (b : Mathieu23Points a) :
    IsSimpleGroup (Mathieu22PointModel a b) := by
  have := mathieu22_faithful a b
  have := mathieu22_three_transitive a b
  have : MulAction.IsMultiplyPretransitive (Mathieu22PointModel a b) (Mathieu22Points a b) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 3) (by rw [mathieu22_degree]; decide)
  obtain ⟨c⟩ := (Nat.card_pos_iff.mp (show 0 < Nat.card (Mathieu22Points a b) by
    rw [mathieu22_degree]; decide)).1
  have := mathieu21_simple a b c
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact Atlas.GroupTheory.simple_of_simple_stabilizer c 2 11 (by decide)
    (by rw [mathieu22_degree]; decide) (by rw [mathieu22_degree]; decide)

end Atlas.Codes
