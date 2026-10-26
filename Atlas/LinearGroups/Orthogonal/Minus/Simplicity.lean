import Atlas.LinearGroups.Orthogonal.Minus.SingularPrimitive
import Atlas.LinearGroups.Orthogonal.Minus.Perfect
import Atlas.LinearGroups.Orthogonal.ProjectiveRootNormalGeneration
import Atlas.LinearGroups.Orthogonal.Center
import Atlas.GroupTheory.IwasawaStabilizer

/-! Simplicity of the actual elementary scalar quotient in stable minus rank.
Intrinsic Omega identification and order remain separate obligations. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem elementary_noncommutative (hdeg : Module.finrank F K = 2) (n : ℕ) :
    ¬ IsMulCommutative (E hdeg (n+2)) :=
  elementary_noncommutative_of_frame _ (wittTwoFrame hdeg n) (polar_nondegenerate hdeg (n+2))

theorem center_scalar (hdeg : Module.finrank F K = 2) (n : ℕ) :
    elementaryScalarSubgroup (form hdeg (n+2)) = Subgroup.center (E hdeg (n+2)) :=
  elementaryScalarSubgroup_eq_center _ (wittTwoFrame hdeg n) (polar_nondegenerate hdeg (n+2))

theorem projective_nontrivial (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nontrivial (ProjectiveElementary (form hdeg (n+2))) := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hs
  have hk (g : E hdeg (n+2)) : g ∈ elementaryScalarSubgroup (form hdeg (n+2)) := by
    rw [← projectiveElementaryMap_kernel]
    exact @Subsingleton.elim _ hs (projectiveElementaryMap _ g) 1
  have hc : Subgroup.center (E hdeg (n+2)) = ⊤ := by
    apply top_unique
    intro g _
    exact elementaryScalarSubgroup_le_center _ (hk g)
  exact elementary_noncommutative hdeg n (Subgroup.center_eq_top_iff.mp hc)

theorem projective_perfect (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Group.IsPerfect (ProjectiveElementary (form hdeg (n+3))) := by
  letI := elementary_perfect hdeg n
  exact projectiveElementary_perfect _

theorem projective_simple (hdeg : Module.finrank F K = 2) (n : ℕ) :
    IsSimpleGroup (ProjectiveElementary (form hdeg (n+3))) := by
  let Q := form hdeg (n+3)
  let H := wittTwoFrame hdeg (n+1)
  let p := singularPointMk Q H.e₁ (Atlas.Quadratic.WittTwoFrame.first_ne_zero Q H) H.qe₁
  letI := projectiveSingular_faithful_minus hdeg (n+1)
  letI := projectiveSingular_primitive hdeg n
  letI := projective_perfect hdeg n
  letI := projective_nontrivial hdeg (n+1)
  have hn := projectiveRoot_normalClosure_eq_top Q p (fun u hu hqu =>
    elementary_singular_transport hdeg (n+1) p.val.rep u p.val.rep_nonzero hu p.prop hqu)
  exact Atlas.GroupTheory.iwasawa_stabilizer_simple p (projectiveRootSubgroup Q p)
    (projectiveRoot_le_point_stabilizer Q p) (projectiveRoot_normal_point_stabilizer Q p)
    inferInstance hn

theorem projective_noncommutative (hdeg : Module.finrank F K = 2) (n : ℕ) :
    ¬ IsMulCommutative (ProjectiveElementary (form hdeg (n+3))) := by
  letI := projective_nontrivial hdeg (n+1)
  letI := projective_perfect hdeg n
  exact Group.IsPerfect.not_isMulCommutative _
end Atlas.Orthogonal.Minus
