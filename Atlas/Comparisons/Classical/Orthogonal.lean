import Atlas.LinearGroups.Orthogonal.B1ConjugationComparison
import Atlas.LinearGroups.Orthogonal.B2ExteriorComparison
import Atlas.LinearGroups.Orthogonal.ProjectiveEvenB
import Atlas.LinearGroups.Orthogonal.D2MatrixComparison
import Atlas.LinearGroups.Orthogonal.D3ExteriorComparison
import Atlas.LinearGroups.Orthogonal.DFamilyTransport

/-! # Actual orthogonal comparison interfaces

Each map retains the quadratic-form carrier. Rank in B and D is Lie rank;
PSL uses natural dimension and PSp uses half the natural dimension.
These interfaces do not identify groups merely by equal orders.
-/
noncomputable section
namespace Atlas.Comparisons.Classical
open Atlas.Orthogonal
variable {F K : Type*} [Field F] [Field K]

/-- The actual trace-zero conjugation comparison in rank one, over every field. -/
def b1EquivA1 : ProjectiveElementary (formB 1 F) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := B1Conjugation.projectiveEquivPSL

/-- The characteristic-two comparison, using the actual radical quotient and unique lift. -/
def evenBEquivC [Finite F] [CharP F 2] (n : ℕ) (hn : 1 ≤ n) :
    ProjectiveElementary (formB n F) ≃* Atlas.Symplectic.PSp n F :=
  evenProjectiveBEquivPSp hn

/-- The rank-two comparison in every finite characteristic. -/
def b2EquivC2 [Finite F] :
    ProjectiveElementary (formB 2 F) ≃* Atlas.Symplectic.PSp 2 F := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact evenBEquivC 2 (by decide)
  · exact B2Exterior.projectiveBEquivPSp h2

/-- Split rank two is the product of the two actual PSL2 models. -/
def d2EquivProduct : ProjectiveElementary (formD 2 F) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ×
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  D2Matrix.projectiveEquivProduct

/-- Split rank three is the actual PSL4 model via exterior square. -/
def d3EquivA3 [Finite F] : ProjectiveElementary (formD 3 F) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 4) F :=
  D3Exterior.d3EquivPSL4

/-- Field transport preserves the actual B construction. -/
def bFieldEquiv (n : ℕ) (e : F ≃+* K) :
    ProjectiveElementary (formB n F) ≃* ProjectiveElementary (formB n K) :=
  fieldEquivProjectiveElementaryB e

/-- Field transport preserves the actual split D construction. -/
def dFieldEquiv (n : ℕ) (e : F ≃+* K) :
    ProjectiveElementary (formD n F) ≃* ProjectiveElementary (formD n K) :=
  fieldEquivProjectiveElementaryD e
end Atlas.Comparisons.Classical
