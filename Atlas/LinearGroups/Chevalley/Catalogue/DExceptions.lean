import Atlas.LinearGroups.Chevalley.Catalogue.DSimple

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- Exact Good interface; there are no excluded finite fields in the D range. -/
theorem D_exceptions (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K]
    (hK : DFieldDomain r hr K) :
    IsSimpleGroup (D r hr K) ↔ (RootType.D r hr).Good (Nat.card K) := by
  letI : Finite K := hK
  constructor
  · intro _
    exact ⟨Finite.one_lt_card, trivial⟩
  · intro hg
    exact D_simple r hr K ⟨hK, hg⟩

end Atlas.Chevalley.Catalogue
