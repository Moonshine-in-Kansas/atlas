import Atlas.LinearGroups.Chevalley.ModelASmallExceptions
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

/-! The exact simplicity range for the actual uniform type-A Model. The
forward implication excludes the two actual rank-one small-field models;
the reverse implication uses the independent good-range simplicity theorem.
No identification with an older PSL construction is required. -/
noncomputable section
namespace Atlas.Chevalley

theorem model_A_isSimpleGroup_iff_good (r : ℕ) (hr : 1 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    IsSimpleGroup (Model (.A r hr) K) ↔ (RootType.A r hr).Good (Nat.card K) := by
  constructor
  · intro hs
    have hq : 2 ≤ Nat.card K := Finite.one_lt_card
    change 2 ≤ Nat.card K ∧ (r ≠ 1 ∨ (Nat.card K ≠ 2 ∧ Nat.card K ≠ 3))
    refine ⟨hq, ?_⟩
    by_cases hr1 : r = 1
    · subst r
      exact Or.inr ⟨fun h2 => model_A_one_two_not_simple K h2 hs,
        fun h3 => model_A_one_three_not_simple K h3 hs⟩
    · exact Or.inl hr1
  · intro hgood
    letI : Fintype K := Fintype.ofFinite K
    apply model_isSimpleGroup_of_good (.A r hr) K
    simpa only [Nat.card_eq_fintype_card (α := K)] using hgood

end Atlas.Chevalley
