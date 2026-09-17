import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SymmDiff

namespace Atlas.Combinatorics
open scoped symmDiff

/-- The inclusion-exclusion formula for a finite symmetric difference. -/
theorem card_symmDiff_eq {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∆ B).card=A.card+B.card-2*(A ∩ B).card := by
  have hd : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  rw [Finset.symmDiff_def,Finset.card_union_of_disjoint hd]
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hB
  omega

end Atlas.Combinatorics
