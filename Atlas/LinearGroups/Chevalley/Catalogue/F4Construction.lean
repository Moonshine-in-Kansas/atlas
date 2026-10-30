import Atlas.LinearGroups.Chevalley.Models

/-! Typed catalogue interface for the adjoint F₄ model.
The carrier and operations are those of the existing adjoint model. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

def F4FieldDomain (K : Type*) [Field K] : Prop := Finite K

def F4 (K : Type*) [Field K] : Type _ := Model .F4 K

instance F4Group (K : Type*) [Field K] : Group (F4 K) :=
  inferInstanceAs (Group (Model .F4 K))

theorem F4_construction (K : Type*) [Field K] (_hK : F4FieldDomain K) :
    Function.Injective
      (adjointLinearRepresentation (rootDatum .F4).pairing (rootDatum .F4).base K :
        F4 K →* LinearMap.GeneralLinearGroup K
          (((rootDatum .F4).base.support ⊕ (rootDatum .F4).Root) → K)) :=
  adjointLinearRepresentation_injective (rootDatum .F4).pairing (rootDatum .F4).base K

end Atlas.Chevalley.Catalogue
