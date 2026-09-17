import Atlas.Conway.IcosianLineReflections
import Atlas.Conway.IcosianRootPointAction
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Lattice

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianRootReflectionOf_conjugate (g : icosianHermitianGroup) (r : IcosianRoot) :
    g * icosianRootReflectionOf r * g⁻¹ = icosianRootReflectionOf (g • r) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (icosianReflection (icosianCoordinateEmbedding r.val) (g.val.symm x)) =
    icosianReflection (icosianCoordinateEmbedding (icosianHermitianRoot g r).val) x
  rw [icosianHermitianRoot_embedding, icosianReflection_covariance, g.val.apply_symm_apply]

theorem icosianLineReflection_conjugate (g : icosianHermitianGroup) (p : IcosianRootPoint) :
    g * icosianLineReflection p * g⁻¹ = icosianLineReflection (g • p) := by
  obtain ⟨r, hr⟩ := p.property
  have hp : icosianRootToPoint r = p := Subtype.ext hr
  rw [← hp, ← icosianRootToPoint_smul, icosianLineReflection_root,
    icosianLineReflection_root, icosianRootReflectionOf_conjugate]

/-- An isometry fixing every root line centralizes the entire reflection group. -/
theorem icosian_fix_rootPoints_commutes_reflections (g : icosianHermitianGroup)
    (hg : ∀ p : IcosianRootPoint, g • p = p)
    (w : icosianHermitianGroup) (hw : w ∈ icosianReflectionGroup) : g*w=w*g := by
  have hle : icosianReflectionGroup ≤ Subgroup.centralizer ({g} : Set icosianHermitianGroup) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨p,rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := icosianLineReflection_conjugate g p
    rw [hg] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hw)).symm

end Atlas.Conway
