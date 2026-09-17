import Atlas.Mathieu.Mathieu11PointStabilizer
import Atlas.GroupTheory.PrimeDegree

namespace Atlas.Codes

theorem mathieu11_simple (D : Dodecad) (a : Mathieu12Points D) : IsSimpleGroup (Mathieu11PointModel D a) := by
  have := mathieu11_faithful D a
  have := mathieu11_four_transitive D a
  have : MulAction.IsMultiplyPretransitive (Mathieu11PointModel D a) (Mathieu11Points D a) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 4)
      (by rw [mathieu11_degree]; decide)
  have : MulAction.IsPretransitive (Mathieu11PointModel D a) (Mathieu11Points D a) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply Atlas.GroupTheory.prime_degree_simple (G := Mathieu11PointModel D a)
    (X := Mathieu11Points D a) 11 5 144 (by decide) (by decide) (by decide)
    (mathieu11_degree D a)
  rw [mathieu11_order]

end Atlas.Codes
