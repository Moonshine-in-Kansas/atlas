import Atlas.LinearGroups.Chevalley.Models

/-! Source-only G₂ registration draft; no compilation or audit is claimed. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- Every finite field, with the same full carrier at the binary parameter. -/
def G2FieldDomain (K : Type*) [Field K] : Prop := Finite K

/-- The existing root-generated adjoint model, not its simply connected cover. -/
def G2 (K : Type*) [Field K] : Type _ := Model .G2 K

instance G2Group (K : Type*) [Field K] : Group (G2 K) :=
  inferInstanceAs (Group (Model .G2 K))

theorem G2_construction (K : Type*) [Field K] (_hK : G2FieldDomain K) :
    Function.Injective
      (adjointLinearRepresentation (rootDatum .G2).pairing (rootDatum .G2).base K :
        G2 K →* LinearMap.GeneralLinearGroup K
          (((rootDatum .G2).base.support ⊕ (rootDatum .G2).Root) → K)) :=
  adjointLinearRepresentation_injective (rootDatum .G2).pairing (rootDatum .G2).base K

end Atlas.Chevalley.Catalogue
