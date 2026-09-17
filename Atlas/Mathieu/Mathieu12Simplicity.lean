import Atlas.Mathieu.Mathieu11Simplicity
import Atlas.GroupTheory.SimpleStabilizer

noncomputable section
namespace Atlas.Codes

theorem mathieu12_simple (D : Dodecad) : IsSimpleGroup (Mathieu12DodecadModel D) := by
  have hn : Nonempty (Mathieu12Points D) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Mathieu12Points D) by rw [mathieu12_degree]; decide)).1
  let a := Classical.choice hn
  have := mathieu12_faithful D
  have := mathieu12_five_transitive D
  have : MulAction.IsMultiplyPretransitive (Mathieu12DodecadModel D) (Mathieu12Points D) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 5)
      (by rw [mathieu12_degree]; decide)
  have : IsSimpleGroup (MulAction.stabilizer (Mathieu12DodecadModel D) a) := mathieu11_simple D a
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact Atlas.GroupTheory.simple_of_simple_stabilizer (G := Mathieu12DodecadModel D)
    (X := Mathieu12Points D) a 2 3 (by decide) (by rw [mathieu12_degree]; decide)
    (by rw [mathieu12_degree]; decide)

theorem mathieu12_noncommuting_pair (D : Dodecad) :
    ∃ g h : Mathieu12DodecadModel D, g*h ≠ h*g := by
  have hn : Nonempty (Mathieu12Points D) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Mathieu12Points D) by rw [mathieu12_degree]; decide)).1
  let a := Classical.choice hn
  obtain ⟨g,h,hgh⟩ := mathieu11_noncommuting_pair D a
  refine ⟨mathieu11_embedding D a g,mathieu11_embedding D a h,?_⟩
  intro he
  apply hgh
  apply mathieu11_embedding_injective D a
  simpa only [map_mul] using he

theorem mathieu12_nonabelian_simple (D : Dodecad) : IsSimpleGroup (Mathieu12DodecadModel D) ∧
    ∃ g h : Mathieu12DodecadModel D, g*h ≠ h*g :=
  ⟨mathieu12_simple D,mathieu12_noncommuting_pair D⟩

end Atlas.Codes
