import Atlas.LinearGroups.Chevalley.Catalogue.BConstruction
import Atlas.LinearGroups.Chevalley.Comparison.TypeBProjectiveEquiv

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- The predecessor index n maps to Lie/quadratic rank n+1, dimension 2(n+1)+1. -/
def B_quadraticRank (n : ℕ) : ℕ := n + 1

/-- A named value of the existing target operations, not a new registered instance. -/
def BQuadraticGroup (r : ℕ) (K : Type*) [Field K] :
    Group (Atlas.Orthogonal.B r K) := inferInstance

/-- The literal marked spin-vector map descended through its proved full center. -/
def B_identification (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : BFieldDomain n hn K) :
    B n hn K ≃* Atlas.Orthogonal.B (B_quadraticRank n) K := by
  letI : Finite K := hK
  exact Comparison.TypeB.projectiveEquiv n hn K

/-- This registration witness is the concrete elementary map on companion lifts. -/
theorem B_identification_rho (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : BFieldDomain n hn K)
    (g : SelectedWeightCompanion (.B (n + 1) hn) K) :
    B_identification n hn K hK (selectedWeightCompanionRho (.B (n + 1) hn) K g) =
      Atlas.Orthogonal.projectiveElementaryMap (Atlas.Orthogonal.formB (n + 1) K)
        (Comparison.TypeB.elementaryHom n hn K g) := by
  letI : Finite K := hK
  exact Comparison.TypeB.projectiveEquiv_rho n hn K g

end Atlas.Chevalley.Catalogue
