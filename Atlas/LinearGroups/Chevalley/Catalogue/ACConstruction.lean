import Atlas.LinearGroups.Chevalley.Models

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- Root rank r at least one, over an actual finite field. -/
def AFieldDomain (r : ℕ) (_hr : 1 ≤ r) (K : Type*) [Field K] : Prop := Finite K

/-- Root rank n+1 at least two, over an actual finite field. -/
def CFieldDomain (n : ℕ) (_hn : 2 ≤ n + 1) (K : Type*) [Field K] : Prop := Finite K

def A (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K] : Type _ := Model (.A r hr) K

instance AGroup (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K] : Group (A r hr K) :=
  inferInstanceAs (Group (Model (.A r hr) K))

def C (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K] : Type _ :=
  Model (.C (n + 1) hn) K

instance CGroup (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K] : Group (C n hn K) :=
  inferInstanceAs (Group (Model (.C (n + 1) hn) K))

theorem A_construction (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K]
    (_hK : AFieldDomain r hr K) :
    Function.Injective
      (adjointLinearRepresentation (rootDatum (.A r hr)).pairing
        (rootDatum (.A r hr)).base K : A r hr K →*
          LinearMap.GeneralLinearGroup K
            (((rootDatum (.A r hr)).base.support ⊕ (rootDatum (.A r hr)).Root) → K)) :=
  adjointLinearRepresentation_injective (rootDatum (.A r hr)).pairing
    (rootDatum (.A r hr)).base K

theorem C_construction (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (_hK : CFieldDomain n hn K) :
    Function.Injective
      (adjointLinearRepresentation (rootDatum (.C (n + 1) hn)).pairing
        (rootDatum (.C (n + 1) hn)).base K : C n hn K →*
          LinearMap.GeneralLinearGroup K
            (((rootDatum (.C (n + 1) hn)).base.support ⊕
              (rootDatum (.C (n + 1) hn)).Root) → K)) :=
  adjointLinearRepresentation_injective (rootDatum (.C (n + 1) hn)).pairing
    (rootDatum (.C (n + 1) hn)).base K

end Atlas.Chevalley.Catalogue
