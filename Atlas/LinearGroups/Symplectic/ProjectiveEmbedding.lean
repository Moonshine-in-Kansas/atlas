import Atlas.LinearGroups.Symplectic.Projective
import Atlas.LinearGroups.ProjectiveGeneralLinear

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

/-- The projectivization of the retained inclusion into the full general linear group. -/
def toPGLUp : Sp n F →* Matrix.ProjGenLinGroup (Index n) F :=
  Matrix.ProjGenLinGroup.mk.comp toGL

@[simp] theorem toPGLUp_action (g : Sp n F) (p : Points n F) : toPGLUp g • p=g • p := rfl

theorem toPGLUp_kernel : (toPGLUp (n := n) (F := F)).ker = Subgroup.center (Sp n F) := by
  ext g
  change toPGLUp g=1 ↔ g ∈ Subgroup.center (Sp n F)
  rw [← fixes_points_iff_central]
  constructor
  · intro h p
    rw [← toPGLUp_action,h,one_smul]
  · intro h
    apply (faithfulSMul_iff.mp (Atlas.pgl_faithful (ι := Index n) (F := F)))
    intro p
    rw [toPGLUp_action,h]

/-- The actual central quotient embeds into the existing PGL model. -/
def toPGL : PSp n F →* Matrix.ProjGenLinGroup (Index n) F :=
  QuotientGroup.lift _ toPGLUp (by rw [toPGLUp_kernel])

@[simp] theorem toPGL_projection (g : Sp n F) : toPGL (projection g)=toPGLUp g := rfl

theorem toPGL_injective : Function.Injective (toPGL (n := n) (F := F)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  ext p
  rw [MonoidHom.mem_ker,Subgroup.mem_bot]
  obtain ⟨g,rfl⟩ := projection_surjective p
  rw [toPGL_projection]
  change g ∈ (toPGLUp (n := n) (F := F)).ker ↔ projection g=1
  rw [toPGLUp_kernel]
  exact (QuotientGroup.eq_one_iff g).symm

theorem toPGL_action (g : PSp n F) (p : Points n F) : toPGL g • p=g • p := by
  obtain ⟨g,rfl⟩ := projection_surjective g
  rfl

end Atlas.Symplectic
