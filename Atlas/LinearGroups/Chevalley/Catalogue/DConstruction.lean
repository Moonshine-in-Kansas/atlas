import Atlas.LinearGroups.Chevalley.Models

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- Root rank r at least four, over an actual finite field. -/
def DFieldDomain (r : ℕ) (_hr : 4 ≤ r) (K : Type*) [Field K] : Prop := Finite K

def D (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K] : Type _ := Model (.D r hr) K

instance DGroup (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K] : Group (D r hr K) :=
  inferInstanceAs (Group (Model (.D r hr) K))

theorem D_construction (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K]
    (_hK : DFieldDomain r hr K) :
    Function.Injective
      (adjointLinearRepresentation (rootDatum (.D r hr)).pairing
        (rootDatum (.D r hr)).base K : D r hr K →*
          LinearMap.GeneralLinearGroup K
            (((rootDatum (.D r hr)).base.support ⊕ (rootDatum (.D r hr)).Root) → K)) :=
  adjointLinearRepresentation_injective (rootDatum (.D r hr)).pairing
    (rootDatum (.D r hr)).base K

end Atlas.Chevalley.Catalogue
