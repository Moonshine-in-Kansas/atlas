import Atlas.LinearGroups.Orthogonal.SingularPrimitiveB
import Atlas.LinearGroups.Orthogonal.RootPointStabilizer
import Atlas.LinearGroups.Orthogonal.RootNormalGeneration
import Atlas.LinearGroups.Orthogonal.PerfectStable
import Atlas.LinearGroups.Orthogonal.ProjectiveOddB
import Atlas.GroupTheory.IwasawaStabilizer

/-! # Uniform simplicity of the actual odd B models in rank at least three -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem elementaryB_simple_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    IsSimpleGroup (elementarySubgroup (formB (n + 3) F)) := by
  let Q := formB (n + 3) F
  let H := wittTwoFrameB (n + 1) (F := F)
  let p := singularPointMk Q H.e₁ (Atlas.Quadratic.WittTwoFrame.first_ne_zero Q H) H.qe₁
  let A := (rootSubgroup Q p.val.rep p.prop).subgroupOf (elementarySubgroup Q)
  letI := singularPointsB_faithful (n + 1) h2
  letI := singularPointsB_primitive n h2
  letI := elementaryB_perfect_stable n h2
  haveI : Nontrivial (elementarySubgroup Q) := by
    by_contra hn
    haveI := not_nontrivial_iff_subsingleton.mp hn
    exact elementaryB_noncommutative (n + 1) h2 inferInstance
  exact Atlas.GroupTheory.iwasawa_stabilizer_simple p A
    (elementaryRoot_le_point_stabilizer Q p) (elementaryRoot_normal_point_stabilizer Q p)
    inferInstance (rootB_normalClosure_eq_top (n + 1) h2 p.val.rep p.prop p.val.rep_nonzero)

theorem projectiveElementaryB_simple_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    IsSimpleGroup (ProjectiveElementary (formB (n + 3) F)) := by
  letI := elementaryB_simple_stable n h2
  exact (projectiveElementaryBEquiv (n + 1) h2).isSimpleGroup

theorem oddSpinorKernelB_simple_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    IsSimpleGroup (oddSpinorKernelB (n + 3) h2) := by
  letI := elementaryB_simple_stable n h2
  exact (elementaryB_kernelEquiv (n + 1) h2).symm.isSimpleGroup
end Atlas.Orthogonal
