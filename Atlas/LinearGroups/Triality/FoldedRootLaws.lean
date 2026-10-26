import Atlas.LinearGroups.Triality.FoldedGenerators
import Atlas.LinearGroups.Triality.RootLaws
import Atlas.LinearGroups.Triality.OuterCommutation

noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

private theorem regroup {G : Type*} [Semigroup G] (a b c d e f : G)
    (hcd : Commute c d) (hbd : Commute b d) (hce : Commute c e) :
    (a*d)*(b*e)*(c*f) = (a*b*c)*(d*e*f) := by
  simp only [mul_assoc]
  rw [hcd.left_comm, hbd.left_comm, hce.left_comm]

theorem shortRoot_add (a b : K) :
    shortRoot F K (a+b) = shortRoot F K a * shortRoot F K b := by
  simp only [shortRoot, map_add, pinnedRoot_add]
  apply regroup
  · exact pinnedRoot_outer_commute 3 0 (by decide) (by decide) _ _
  · exact pinnedRoot_outer_commute 2 0 (by decide) (by decide) _ _
  · exact pinnedRoot_outer_commute 3 2 (by decide) (by decide) _ _

theorem shortNegativeRoot_add (a b : K) :
    shortNegativeRoot F K (a+b) = shortNegativeRoot F K a * shortNegativeRoot F K b := by
  simp only [shortNegativeRoot, map_add, pinnedNegativeRoot_add]
  apply regroup
  · exact pinnedNegativeRoot_outer_commute 3 0 (by decide) (by decide) _ _
  · exact pinnedNegativeRoot_outer_commute 2 0 (by decide) (by decide) _ _
  · exact pinnedNegativeRoot_outer_commute 3 2 (by decide) (by decide) _ _

theorem longRoot_add (a b : F) :
    longRoot F K (a+b) = longRoot F K a * longRoot F K b := by
  simp only [longRoot, map_add, pinnedRoot_add]

theorem longNegativeRoot_add (a b : F) :
    longNegativeRoot F K (a+b) = longNegativeRoot F K a * longNegativeRoot F K b := by
  simp only [longNegativeRoot, map_add, pinnedNegativeRoot_add]

@[simp] theorem shortRoot_zero : shortRoot F K 0 = 1 := by simp [shortRoot]
@[simp] theorem shortNegativeRoot_zero : shortNegativeRoot F K 0 = 1 := by simp [shortNegativeRoot]
@[simp] theorem longRoot_zero : longRoot F K 0 = 1 := by simp [longRoot]
@[simp] theorem longNegativeRoot_zero : longNegativeRoot F K 0 = 1 := by simp [longNegativeRoot]

end Atlas.Triality
