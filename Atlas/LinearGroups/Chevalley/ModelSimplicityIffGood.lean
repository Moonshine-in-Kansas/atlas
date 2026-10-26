import Atlas.LinearGroups.Chevalley.ModelASimplicityIffGood
import Atlas.LinearGroups.Chevalley.ModelBCSimplicityIffGood
import Atlas.LinearGroups.Chevalley.ModelG2BinaryException

/-! Exact simplicity range for the same concrete adjoint model in every
untwisted root type. The excluded small parameters retain their original
groups. No derived subgroup replaces an exception. -/
noncomputable section
namespace Atlas.Chevalley

theorem model_isSimpleGroup_iff_good
    (Φ : RootType) (K : Type*) [Field K] [Finite K] :
    IsSimpleGroup (Model Φ K) ↔ Φ.Good (Nat.card K) := by
  constructor
  · intro hs
    have hq : 2 ≤ Nat.card K := Finite.one_lt_card
    cases Φ with
    | A r hr => exact (model_A_isSimpleGroup_iff_good r hr K).mp hs
    | B r hr => exact (model_B_isSimpleGroup_iff_good r hr K).mp hs
    | C r hr => exact (model_C_isSimpleGroup_iff_good r hr K).mp hs
    | D r hr => exact ⟨hq, trivial⟩
    | E6 => exact ⟨hq, trivial⟩
    | E7 => exact ⟨hq, trivial⟩
    | E8 => exact ⟨hq, trivial⟩
    | F4 => exact ⟨hq, trivial⟩
    | G2 => exact ⟨hq, fun h2 => model_G2_two_not_simple K h2 hs⟩
  · intro hgood
    let : Fintype K := Fintype.ofFinite K
    apply model_isSimpleGroup_of_good Φ K
    simpa only [Nat.card_eq_fintype_card (α := K)] using hgood

end Atlas.Chevalley
