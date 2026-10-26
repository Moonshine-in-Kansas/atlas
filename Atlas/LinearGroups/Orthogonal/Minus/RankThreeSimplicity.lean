import Atlas.LinearGroups.Orthogonal.Minus.RankThreeComparison
import Atlas.LinearGroups.Unitary.Family

/-! Rank-three minus simplicity through the actual, independently built unitary comparison. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem rankThree_simple (hdeg : Module.finrank F K = 2) :
    IsSimpleGroup (ProjectiveElementary (form hdeg 2)) := by
  let := Atlas.Unitary.simple_of_good hdeg
    (show Atlas.Unitary.Good 4 (Nat.card F) by simp [Atlas.Unitary.Good])
  exact (rankThreeUnitaryEquiv hdeg).symm.isSimpleGroup

theorem rankThree_noncommutative (hdeg : Module.finrank F K = 2) :
    ¬ IsMulCommutative (ProjectiveElementary (form hdeg 2)) := by
  intro h
  apply Atlas.Unitary.noncommutative_of_good hdeg
    (show Atlas.Unitary.Good 4 (Nat.card F) by simp [Atlas.Unitary.Good])
  apply IsMulCommutative.of_comm
  intro x y
  apply (rankThreeUnitaryEquiv hdeg).injective
  simp only [map_mul]
  exact isMulCommutative_iff.mp h _ _

end Atlas.Orthogonal.Minus
