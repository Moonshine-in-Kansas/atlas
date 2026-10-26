import Atlas.LinearGroups.Chevalley.Models

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- Root rank n+1 at least two, over an actual finite field. -/
def BFieldDomain (n : ℕ) (_hn : 2 ≤ n + 1) (K : Type*) [Field K] : Prop := Finite K

def B (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K] : Type _ :=
  Model (.B (n + 1) hn) K

instance BGroup (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K] : Group (B n hn K) :=
  inferInstanceAs (Group (Model (.B (n + 1) hn) K))

theorem B_construction (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (_hK : BFieldDomain n hn K) :
    Function.Injective
      (adjointLinearRepresentation (rootDatum (.B (n + 1) hn)).pairing
        (rootDatum (.B (n + 1) hn)).base K : B n hn K →*
          LinearMap.GeneralLinearGroup K
            (((rootDatum (.B (n + 1) hn)).base.support ⊕
              (rootDatum (.B (n + 1) hn)).Root) → K)) :=
  adjointLinearRepresentation_injective (rootDatum (.B (n + 1) hn)).pairing
    (rootDatum (.B (n + 1) hn)).base K

end Atlas.Chevalley.Catalogue
