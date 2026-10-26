import Atlas.LinearGroups.Chevalley.ModelBCBinaryExceptions
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

/-! Exact simplicity ranges for the actual uniform B and C models.
The two binary rank-two exclusions come from the actual six-form sign
character, and all positive cases use the independent uniform theorem. -/
noncomputable section
namespace Atlas.Chevalley

theorem model_B_isSimpleGroup_iff_good (r : ℕ) (hr : 2 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    IsSimpleGroup (Model (.B r hr) K) ↔ (RootType.B r hr).Good (Nat.card K) := by
  constructor
  · intro hs
    have hq : 2 ≤ Nat.card K := Finite.one_lt_card
    change 2 ≤ Nat.card K ∧ (r ≠ 2 ∨ Nat.card K ≠ 2)
    refine ⟨hq, ?_⟩
    by_cases hr2 : r = 2
    · subst r
      exact Or.inr (fun h2 => model_B_two_two_not_simple K h2 hs)
    · exact Or.inl hr2
  · intro hgood
    letI : Fintype K := Fintype.ofFinite K
    apply model_isSimpleGroup_of_good (.B r hr) K
    simpa only [Nat.card_eq_fintype_card (α := K)] using hgood

theorem model_C_isSimpleGroup_iff_good (r : ℕ) (hr : 2 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    IsSimpleGroup (Model (.C r hr) K) ↔ (RootType.C r hr).Good (Nat.card K) := by
  constructor
  · intro hs
    have hq : 2 ≤ Nat.card K := Finite.one_lt_card
    change 2 ≤ Nat.card K ∧ (r ≠ 2 ∨ Nat.card K ≠ 2)
    refine ⟨hq, ?_⟩
    by_cases hr2 : r = 2
    · subst r
      exact Or.inr (fun h2 => model_C_two_two_not_simple K h2 hs)
    · exact Or.inl hr2
  · intro hgood
    letI : Fintype K := Fintype.ofFinite K
    apply model_isSimpleGroup_of_good (.C r hr) K
    simpa only [Nat.card_eq_fintype_card (α := K)] using hgood

end Atlas.Chevalley
