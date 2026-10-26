import Atlas.LinearGroups.Chevalley.Catalogue.ESeriesConstruction
import Atlas.LinearGroups.Chevalley.Catalogue.ESeriesSimple

/-! Separate catalogue exceptions evidence for the same three actual carriers. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- There are no exceptional finite-field parameters for this E family. -/
theorem E6_exceptions (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    IsSimpleGroup (E6 K) ↔ 2 ≤ Nat.card K := by
  letI : Finite K := hK
  exact ⟨fun _ => Finite.one_lt_card, fun _ => E6_simple K hK⟩

/-- There are no exceptional finite-field parameters for this E family. -/
theorem E7_exceptions (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    IsSimpleGroup (E7 K) ↔ 2 ≤ Nat.card K := by
  letI : Finite K := hK
  exact ⟨fun _ => Finite.one_lt_card, fun _ => E7_simple K hK⟩

/-- There are no exceptional finite-field parameters for this E family. -/
theorem E8_exceptions (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    IsSimpleGroup (E8 K) ↔ 2 ≤ Nat.card K := by
  letI : Finite K := hK
  exact ⟨fun _ => Finite.one_lt_card, fun _ => E8_simple K hK⟩

end Atlas.Chevalley.Catalogue
