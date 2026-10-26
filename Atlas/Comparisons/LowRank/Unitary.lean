import Atlas.LinearGroups.Unitary.RankOneProjective
import Atlas.Comparisons.LowRank.Symplectic
import Atlas.Comparisons.Classical.Orthogonal

/-! Dimension two uses the base field, not the quadratic scalar field. -/
noncomputable section
namespace Atlas.Comparisons.Classical
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def psuTwoEquivA1 (hdeg : Module.finrank F K = 2) :
    Atlas.Unitary.PSU F K 2 hdeg ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  (Atlas.Unitary.projectiveUnitaryTwoEquiv hdeg).symm

def psuTwoEquivC1 (hdeg : Module.finrank F K = 2) :
    Atlas.Unitary.PSU F K 2 hdeg ≃* Atlas.Symplectic.PSp 1 F :=
  (psuTwoEquivA1 hdeg).trans c1EquivA1.symm

def psuTwoEquivB1 (hdeg : Module.finrank F K = 2) :
    Atlas.Unitary.PSU F K 2 hdeg ≃*
      Atlas.Orthogonal.ProjectiveElementary (Atlas.Orthogonal.formB 1 F) :=
  (psuTwoEquivA1 hdeg).trans b1EquivA1.symm

@[simp] theorem psuTwoEquivC1_coherence (hdeg : Module.finrank F K = 2)
    (g : Atlas.Unitary.PSU F K 2 hdeg) :
    c1EquivA1 (psuTwoEquivC1 hdeg g) = psuTwoEquivA1 hdeg g := by
  simp [psuTwoEquivC1]

@[simp] theorem psuTwoEquivB1_coherence (hdeg : Module.finrank F K = 2)
    (g : Atlas.Unitary.PSU F K 2 hdeg) :
    b1EquivA1 (psuTwoEquivB1 hdeg g) = psuTwoEquivA1 hdeg g := by
  simp [psuTwoEquivB1]
end Atlas.Comparisons.Classical
