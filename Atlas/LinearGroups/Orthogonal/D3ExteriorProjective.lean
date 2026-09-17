import Atlas.LinearGroups.Orthogonal.D3ExteriorKernel
import Atlas.LinearGroups.Orthogonal.D3ExteriorImage
import Atlas.LinearGroups.Orthogonal.ProjectiveElementary

/-! # Structural projective kernel of the actual SL₄ exterior-square action -/
noncomputable section
namespace Atlas.Orthogonal.D3Exterior
open B2Exterior Matrix
variable {F : Type*} [Field F] [Finite F]

def toProjective : Matrix.SpecialLinearGroup (Fin 4) F →* ProjectiveElementary (formD 3 F) :=
  (projectiveElementaryMap _).comp toElementary

/-- Scalar bivector action forces the original determinant-one matrix to be central. -/
theorem toProjective_eq_one_iff_center (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    toProjective g = 1 ↔ g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F) := by
  change (QuotientGroup.mk (toElementary g) : ProjectiveElementary (formD 3 F)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨c,hc,hg⟩
    have hc0 : c ≠ 0 := by intro hz; simp [hz] at hc
    obtain ⟨a,ha,hga⟩ := scalar_of_exteriorMap_scalar g.val c hc0
      ((toOrthogonal_scalar_iff g c).mp hg)
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨a, ?_, ?_⟩
    · have hd := g.det_coe
      rw [hga, Matrix.det_smul] at hd
      simpa using hd
    · simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using hga.symm
  · intro hg
    obtain ⟨a,ha,hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
    have hm : g.val = a • (1 : Matrix (Fin 4) (Fin 4) F) := by
      simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using hga.symm
    refine ⟨a^2, ?_, ?_⟩
    · norm_num only [Fintype.card_fin] at ha
      simpa only [← pow_mul] using ha
    · apply (toOrthogonal_scalar_iff g (a^2)).mpr
      intro w
      rw [hm, exteriorMap_scalar, LinearMap.smul_apply, LinearMap.id_apply]

theorem toProjective_kernel :
    (toProjective (F := F)).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F) := by
  ext g
  exact toProjective_eq_one_iff_center g

/-- The actual exterior-square action descends along the already defined PSL quotient. -/
def projectiveHom : Matrix.ProjectiveSpecialLinearGroup (Fin 4) F →*
    ProjectiveElementary (formD 3 F) :=
  QuotientGroup.lift _ toProjective (by
    intro g hg
    exact (toProjective_eq_one_iff_center g).mpr hg)

theorem projectiveHom_projection (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    projectiveHom (QuotientGroup.mk g) = projectiveElementaryMap _ (toElementary g) := rfl

theorem projectiveHom_injective : Function.Injective (projectiveHom (F := F)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F)) x
  change projectiveHom (QuotientGroup.mk g) = 1 at hx
  change QuotientGroup.mk g = (1 : Matrix.ProjectiveSpecialLinearGroup (Fin 4) F)
  apply (QuotientGroup.eq_one_iff g).mpr
  exact (toProjective_eq_one_iff_center g).mp hx

end Atlas.Orthogonal.D3Exterior
