import Atlas.LinearGroups.Orthogonal.ProjectiveEvenB
import Atlas.LinearGroups.Orthogonal.ProjectiveOddB

/-! # Uniform actual B scalar-quotient order in rank at least two -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]
open scoped Classical

theorem card_projectiveB_all_char (n : ℕ) :
    Nat.card (ProjectiveElementary (formB (n + 2) F)) =
      (Nat.card F ^ ((n + 2)*(n + 2)) *
        ∏ i ∈ Finset.range (n + 2), (Nat.card F ^ (2*(i+1))-1)) /
          (if (2 : F) = 0 then 1 else 2) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    simpa only [h2, ite_true, Nat.div_one] using (card_evenProjectiveB (F := F) (n + 2))
  · simpa only [h2, ite_false] using (card_projectiveElementaryB n h2)
end Atlas.Orthogonal
