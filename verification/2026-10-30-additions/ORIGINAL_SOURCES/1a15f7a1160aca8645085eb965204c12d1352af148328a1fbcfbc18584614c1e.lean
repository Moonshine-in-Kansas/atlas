import Atlas.LinearGroups.Chevalley.Catalogue.F4Construction
import Atlas.LinearGroups.Chevalley.ModelF4Order
import Atlas.LinearGroups.Chevalley.ModelFiniteCenter
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood
import Atlas.LinearGroups.Chevalley.ModelSimplicityIffGood

/-! Catalogue specializations of the adjoint F₄ properties.
No comparison or new mathematical assumption supplies these properties. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem F4_finite (K : Type*) [Field K] (hK : F4FieldDomain K) :
    Finite (F4 K) := by
  letI : Finite K := hK
  exact modelFinite .F4 K

theorem F4_order (K : Type*) [Field K] (hK : F4FieldDomain K) :
    Nat.card (F4 K) = Nat.card K ^ 24 * (Nat.card K ^ 12 - 1) *
      (Nat.card K ^ 8 - 1) * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1) := by
  letI : Finite K := hK
  simpa only [F4, mul_comm, mul_left_comm, mul_assoc] using (model_F4_card K)

theorem F4_center (K : Type*) [Field K] (hK : F4FieldDomain K) :
    Subgroup.center (F4 K) = ⊥ := by
  letI : Finite K := hK
  exact model_center_eq_bot_finiteField .F4 K

theorem F4_simple (K : Type*) [Field K] (hK : F4FieldDomain K) :
    IsSimpleGroup (F4 K) := by
  letI : Finite K := hK
  letI : Fintype K := Fintype.ofFinite K
  have hgood : RootType.F4.Good (Nat.card K) := ⟨Finite.one_lt_card, trivial⟩
  apply model_isSimpleGroup_of_good .F4 K
  simpa only [Nat.card_eq_fintype_card (α := K)] using hgood

theorem F4_nonabelian (K : Type*) [Field K] (_hK : F4FieldDomain K) :
    ¬ IsMulCommutative (F4 K) :=
  model_not_commutative .F4 K

theorem F4_exceptions (K : Type*) [Field K] (hK : F4FieldDomain K) :
    IsSimpleGroup (F4 K) ↔ RootType.F4.Good (Nat.card K) := by
  letI : Finite K := hK
  exact model_isSimpleGroup_iff_good .F4 K

end Atlas.Chevalley.Catalogue
