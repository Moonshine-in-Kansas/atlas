import Atlas.LinearGroups.Chevalley.Catalogue.DConstruction
import Atlas.LinearGroups.Chevalley.Comparison.TypeDOrthogonalEquiv

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- Lie rank equals the old split quadratic rank; natural dimension is 2r. -/
def D_quadraticRank (r : ℕ) : ℕ := r

/-- A named value of the existing operations, not a new registered instance. -/
def DPlusGroup (r : ℕ) (K : Type*) [Field K] :
    Group (Atlas.Orthogonal.DPlus r K) := inferInstance

/-- The audited natural map, proved injective and then bijective over finite fields. -/
def D_identification (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K]
    (hK : DFieldDomain r hr K) :
    D r hr K ≃* Atlas.Orthogonal.DPlus (D_quadraticRank r) K := by
  letI : Finite K := hK
  exact Comparison.TypeD.modelDPlusEquiv r hr K

/-- Explicit link from the public rank wrapper to the marked natural map. -/
theorem D_identification_apply (n : ℕ) (hn : 4 ≤ n + 2) (K : Type*) [Field K]
    (hK : DFieldDomain (n + 2) hn K) (g : D (n + 2) hn K) :
    D_identification (n + 2) hn K hK g =
      Comparison.TypeD.modelNaturalProjectiveHom n hn K g := by
  letI : Finite K := hK
  exact Comparison.TypeD.modelNaturalProjectiveEquiv_apply n hn K g

end Atlas.Chevalley.Catalogue
