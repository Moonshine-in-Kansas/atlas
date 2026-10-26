import Atlas.LinearGroups.Chevalley.Catalogue.ACConstruction
import Atlas.LinearGroups.Chevalley.Comparison.TypeAProjectiveEquiv
import Atlas.LinearGroups.Chevalley.Comparison.TypeCProjectiveEquiv

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- Lie rank r maps to the existing PSL matrix dimension r+1. -/
def A_matrixDimension (r : ℕ) : ℕ := r + 1

/-- The existing type-C comparison uses rank n+1, with natural dimension 2(n+1). -/
def C_symplecticRank (n : ℕ) : ℕ := n + 1

/-- A named value of the existing operations; not a new registered instance. -/
def PSLGroup (d : ℕ) (K : Type*) [Field K] :
    Group (Matrix.ProjectiveSpecialLinearGroup (Fin d) K) := inferInstance

/-- A named value of the existing operations; not a new registered instance. -/
def PSpGroup (r : ℕ) (K : Type*) [Field K] :
    Group (Atlas.Symplectic.PSp r K) := inferInstance

/-- The already proved defining-weight map, descended through both full centers. -/
def A_identification (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K]
    (hK : AFieldDomain r hr K) :
    A r hr K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (A_matrixDimension r)) K := by
  letI : Finite K := hK
  exact Comparison.TypeA.projectiveEquiv r hr K

/-- The already proved signed-weight map, descended through both full centers. -/
def C_identification (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : CFieldDomain n hn K) :
    C n hn K ≃* Atlas.Symplectic.PSp (C_symplecticRank n) K := by
  letI : Finite K := hK
  exact Comparison.TypeC.projectiveEquiv n hn K

end Atlas.Chevalley.Catalogue
