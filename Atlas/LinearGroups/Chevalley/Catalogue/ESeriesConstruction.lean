import Atlas.LinearGroups.Chevalley.Models

/-! Explicit catalogue carriers for the three previously uncompleted E families.
Each carrier is the existing root-generated elementary adjoint subgroup, with
its existing group operations. These names do not identify another model.
Construction evidence records the already proved faithful adjoint action. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- A finite field of arbitrary characteristic; q is always `Nat.card K`. -/
def FiniteFieldDomain (K : Type*) [Field K] : Prop := Finite K

/-- The literal root-generated E6 adjoint elementary group. -/
def E6 (K : Type*) [Field K] : Type _ := Model .E6 K

/-- Exactly the group operations of the constructed adjoint subgroup. -/
instance E6Group (K : Type*) [Field K] : Group (E6 K) :=
  inferInstanceAs (Group (Model .E6 K))

/-- The actual adjoint action of this carrier is faithful. -/
theorem E6_construction (K : Type*) [Field K] (_hK : FiniteFieldDomain K) :
    Function.Injective
      (adjointLinearRepresentation (rootDatum .E6).pairing (rootDatum .E6).base K :
        E6 K →* LinearMap.GeneralLinearGroup K
          (((rootDatum .E6).base.support ⊕ (rootDatum .E6).Root) → K)) :=
  adjointLinearRepresentation_injective (rootDatum .E6).pairing (rootDatum .E6).base K

/-- The literal root-generated E7 adjoint elementary group. -/
def E7 (K : Type*) [Field K] : Type _ := Model .E7 K

/-- Exactly the group operations of the constructed adjoint subgroup. -/
instance E7Group (K : Type*) [Field K] : Group (E7 K) :=
  inferInstanceAs (Group (Model .E7 K))

/-- The actual adjoint action of this carrier is faithful. -/
theorem E7_construction (K : Type*) [Field K] (_hK : FiniteFieldDomain K) :
    Function.Injective
      (adjointLinearRepresentation (rootDatum .E7).pairing (rootDatum .E7).base K :
        E7 K →* LinearMap.GeneralLinearGroup K
          (((rootDatum .E7).base.support ⊕ (rootDatum .E7).Root) → K)) :=
  adjointLinearRepresentation_injective (rootDatum .E7).pairing (rootDatum .E7).base K

/-- The literal root-generated E8 adjoint elementary group. -/
def E8 (K : Type*) [Field K] : Type _ := Model .E8 K

/-- Exactly the group operations of the constructed adjoint subgroup. -/
instance E8Group (K : Type*) [Field K] : Group (E8 K) :=
  inferInstanceAs (Group (Model .E8 K))

/-- The actual adjoint action of this carrier is faithful. -/
theorem E8_construction (K : Type*) [Field K] (_hK : FiniteFieldDomain K) :
    Function.Injective
      (adjointLinearRepresentation (rootDatum .E8).pairing (rootDatum .E8).base K :
        E8 K →* LinearMap.GeneralLinearGroup K
          (((rootDatum .E8).base.support ⊕ (rootDatum .E8).Root) → K)) :=
  adjointLinearRepresentation_injective (rootDatum .E8).pairing (rootDatum .E8).base K

end Atlas.Chevalley.Catalogue
