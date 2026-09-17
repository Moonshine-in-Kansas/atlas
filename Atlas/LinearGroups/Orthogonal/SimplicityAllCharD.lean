import Atlas.LinearGroups.Orthogonal.SingularPrimitiveD
import Atlas.LinearGroups.Orthogonal.ProjectiveRootNormalGeneration
import Atlas.LinearGroups.Orthogonal.PerfectAllCharD
import Atlas.LinearGroups.Orthogonal.CenterStandard
import Atlas.GroupTheory.IwasawaStabilizer

/-! # Simplicity of the actual projective split-D model in every characteristic -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

theorem projectiveD_nontrivial_all_char (n : ℕ) :
    Nontrivial (ProjectiveElementary (formD (n + 2) F)) := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hs
  have hk (g : elementarySubgroup (formD (n + 2) F)) :
      g ∈ elementaryScalarSubgroup (formD (n + 2) F) := by
    rw [← projectiveElementaryMap_kernel]
    exact @Subsingleton.elim _ hs (projectiveElementaryMap _ g) 1
  have hc : Subgroup.center (elementarySubgroup (formD (n + 2) F)) = ⊤ := by
    apply top_unique
    intro g _
    exact elementaryScalarSubgroup_le_center _ (hk g)
  exact elementaryD_noncommutative n (Subgroup.center_eq_top_iff.mp hc)

theorem projectiveD_perfect_all_char (n : ℕ) :
    Group.IsPerfect (ProjectiveElementary (formD (n + 3) F)) := by
  letI := elementaryD_perfect_all_char (F := F) n
  exact projectiveElementary_perfect _

theorem projectiveD_simple_all_char (n : ℕ) :
    IsSimpleGroup (ProjectiveElementary (formD (n + 3) F)) := by
  let Q := formD (n + 3) F
  let H := wittTwoFrameD (F := F) (n + 1)
  let p := singularPointMk Q H.e₁ (Atlas.Quadratic.WittTwoFrame.first_ne_zero Q H) H.qe₁
  letI := projectiveSingularD_faithful (F := F) (n + 1)
  letI := projectiveSingularD_primitive (F := F) n
  letI := projectiveD_perfect_all_char (F := F) n
  letI := projectiveD_nontrivial_all_char (F := F) (n + 1)
  exact Atlas.GroupTheory.iwasawa_stabilizer_simple p (projectiveRootSubgroup Q p)
    (projectiveRoot_le_point_stabilizer Q p) (projectiveRoot_normal_point_stabilizer Q p)
    inferInstance (projectiveRootD_normalClosure_eq_top (n + 1) p)

theorem projectiveD_noncommutative_all_char (n : ℕ) :
    ¬ IsMulCommutative (ProjectiveElementary (formD (n + 3) F)) := by
  letI := projectiveD_nontrivial_all_char (F := F) (n + 1)
  letI := projectiveD_perfect_all_char (F := F) n
  exact Group.IsPerfect.not_isMulCommutative _

end Atlas.Orthogonal
