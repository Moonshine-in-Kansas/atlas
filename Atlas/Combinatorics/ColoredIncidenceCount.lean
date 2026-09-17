import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Atlas.Combinatorics
open scoped BigOperators

/-- Counting exclusive incidences in a bipartition; useful for derived Witt graphs. -/
theorem colored_incidence_count {V : Type*} (S : Finset V) (p q c : V → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred c] :
    (S.filter (fun x => (p x ∧ ¬q x ∧ c x) ∨ (¬p x ∧ q x ∧ ¬c x))).card +
      (S.filter (fun x => p x ∧ q x)).card =
    (S.filter (fun x => p x ∧ c x)).card + (S.filter (fun x => q x ∧ ¬c x)).card := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : p x <;> by_cases hq : q x <;> by_cases hc : c x <;> simp [hp,hq,hc]

end Atlas.Combinatorics
