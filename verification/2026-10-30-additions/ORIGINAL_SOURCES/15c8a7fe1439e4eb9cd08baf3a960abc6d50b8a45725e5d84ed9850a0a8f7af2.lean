import ComparisonWork.G2Construction
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

/-! Source-only G₂ registration draft; no compilation or audit is claimed. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- For finite fields the existing Good predicate is precisely q > 2. -/
def G2GoodDomain (K : Type*) [Field K] : Prop :=
  G2FieldDomain K ∧ RootType.G2.Good (Nat.card K)

theorem G2_simple (K : Type*) [Field K] (hK : G2GoodDomain K) :
    IsSimpleGroup (G2 K) := by
  letI : Finite K := hK.1
  letI : Fintype K := Fintype.ofFinite K
  apply model_isSimpleGroup_of_good .G2 K
  simpa only [Nat.card_eq_fintype_card (α := K)] using hK.2

end Atlas.Chevalley.Catalogue
