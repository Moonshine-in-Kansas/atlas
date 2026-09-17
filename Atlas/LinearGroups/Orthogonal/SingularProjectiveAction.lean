import Atlas.LinearGroups.Orthogonal.SingularPoints
import Atlas.LinearGroups.Orthogonal.SingularLineKernel
import Atlas.LinearGroups.Orthogonal.ProjectiveElementary

/-! # The faithful actual singular-point action of the scalar quotient -/
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)

theorem scalar_fixes_singularPoints (g : elementarySubgroup Q)
    (hg : g ∈ elementaryScalarSubgroup Q) (p : SingularPoints Q) : g • p = p := by
  obtain ⟨c, _, hc⟩ := hg
  apply Subtype.ext
  change g.val.val • p.val = p.val
  rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff']
  exact ⟨c, (hc p.val.rep).symm⟩

include H in
theorem fixes_singularPoints_iff_scalar (g : elementarySubgroup Q) :
    (∀ p : SingularPoints Q, g • p = p) ↔ g ∈ elementaryScalarSubgroup Q := by
  constructor
  · intro hg
    apply singular_projective_kernel_scalar Q H g.val
    intro v hv hq
    have h := congrArg Subtype.val (hg (singularPointMk Q v hv hq))
    change g.val.val • Projectivization.mk F v hv = Projectivization.mk F v hv at h
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, _, hc⟩ p
    apply Subtype.ext
    change g.val.val • p.val = p.val
    rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk,
      Projectivization.mk_eq_mk_iff']
    exact ⟨c, (hc p.val.rep).symm⟩

def singularPointPerm : elementarySubgroup Q →* Equiv.Perm (SingularPoints Q) :=
  MulAction.toPermHom _ _

include H in
theorem singularPointPerm_kernel : (singularPointPerm Q).ker = elementaryScalarSubgroup Q := by
  ext g
  change singularPointPerm Q g = 1 ↔ _
  rw [Equiv.Perm.ext_iff]
  exact fixes_singularPoints_iff_scalar Q H g

def projectiveSingularPerm : ProjectiveElementary Q →* Equiv.Perm (SingularPoints Q) :=
QuotientGroup.lift _ (singularPointPerm Q) (by
  intro g hg
  change singularPointPerm Q g = 1
  apply Equiv.Perm.ext
  intro p
  exact scalar_fixes_singularPoints Q g hg p)

instance projectiveSingularAction : MulAction (ProjectiveElementary Q) (SingularPoints Q) :=
  MulAction.compHom (SingularPoints Q) (projectiveSingularPerm Q)

theorem projectiveSingular_projection_smul (g : elementarySubgroup Q) (p : SingularPoints Q) :
    projectiveElementaryMap Q g • p = g • p := rfl

include H in
theorem projectiveSingular_faithful : FaithfulSMul (ProjectiveElementary Q) (SingularPoints Q) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  obtain ⟨z, rfl⟩ := projectiveElementaryMap_surjective Q g
  apply (QuotientGroup.eq_one_iff z).mpr
  exact (fixes_singularPoints_iff_scalar Q H z).mp hg

theorem projectiveSingular_pretransitive
    [MulAction.IsPretransitive (elementarySubgroup Q) (SingularPoints Q)] :
    MulAction.IsPretransitive (ProjectiveElementary Q) (SingularPoints Q) where
  exists_smul_eq p r := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (elementarySubgroup Q) p r
    exact ⟨projectiveElementaryMap Q g, hg⟩
theorem projectiveSingularB_faithful (n : ℕ) :
    FaithfulSMul (ProjectiveElementary (formB (n+2) F)) (SingularPoints (formB (n+2) F)) :=
  projectiveSingular_faithful _ (wittTwoFrameB n)

theorem projectiveSingularB_pretransitive (n : ℕ) (h2 : (2 : F) ≠ 0) :
    MulAction.IsPretransitive (ProjectiveElementary (formB (n+2) F))
      (SingularPoints (formB (n+2) F)) := by
  letI := singularPointsB_pretransitive n h2
  exact projectiveSingular_pretransitive _
end Atlas.Orthogonal

