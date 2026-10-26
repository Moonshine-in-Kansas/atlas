import Atlas.LinearGroups.Chevalley.Catalogue.ACConstruction
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

def AGoodDomain (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K] : Prop :=
  AFieldDomain r hr K ∧ (RootType.A r hr).Good (Nat.card K)

def CGoodDomain (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K] : Prop :=
  CFieldDomain n hn K ∧ (RootType.C (n + 1) hn).Good (Nat.card K)

theorem A_simple (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K]
    (hK : AGoodDomain r hr K) : IsSimpleGroup (A r hr K) := by
  letI : Finite K := hK.1
  letI : Fintype K := Fintype.ofFinite K
  apply model_isSimpleGroup_of_good (.A r hr) K
  simpa only [Nat.card_eq_fintype_card (α := K)] using hK.2

theorem C_simple (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : CGoodDomain n hn K) : IsSimpleGroup (C n hn K) := by
  letI : Finite K := hK.1
  letI : Fintype K := Fintype.ofFinite K
  apply model_isSimpleGroup_of_good (.C (n + 1) hn) K
  simpa only [Nat.card_eq_fintype_card (α := K)] using hK.2

end Atlas.Chevalley.Catalogue
