import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Atlas.GroupTheory
open scoped BigOperators

/-- Disjoint actual finite subsets exhausting the ambient cardinality form a
cover. This counting argument makes no transitivity assumption. -/
theorem finite_families_cover_of_card_sum {X I : Type*} [Fintype X] [Fintype I]
    [DecidableEq X] (F : I → Finset X)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcard : (∑ i : I, (F i).card) = Fintype.card X) :
    ∀ x : X, ∃ i : I, x ∈ F i := by
  classical
  have hc : (Finset.univ.biUnion F).card=Fintype.card X := by
    rw [Finset.card_biUnion]
    · exact hcard
    · intro i hi j hj hij
      exact hdisjoint hij
  have hu : Finset.univ.biUnion F = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [hc,Finset.card_univ]
  intro x
  have hx : x ∈ Finset.univ.biUnion F := by rw [hu]; exact Finset.mem_univ x
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
  exact ⟨i,hi⟩

end Atlas.GroupTheory
