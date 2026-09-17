import Atlas.LinearGroups.Symplectic.RankOne
import Atlas.LinearGroups.Symplectic.Projective

noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Symplectic
variable {F : Type*} [Field F]

/-- Projective transport retaining the rank-one coordinate marking. -/
def rankOnePoints : Points 1 F ≃ ℙ F (Fin 2 → F) where
  toFun := Projectivization.map rankOneVector.toLinearMap rankOneVector.injective
  invFun := Projectivization.map rankOneVector.symm.toLinearMap rankOneVector.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [Projectivization.map_mk, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  right_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [Projectivization.map_mk, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

theorem rankOnePSL_action (g : PSp 1 F) (p : Points 1 F) :
    rankOnePoints (g • p) = rankOnePSL g • rankOnePoints p := by
  obtain ⟨g,rfl⟩ := projection_surjective g
  rw [projection_smul,rankOnePSL_projection]
  change rankOnePoints (g • p) = rankOneSL g • rankOnePoints p
  induction p using Projectivization.ind with | h v hv =>
  change Projectivization.map rankOneVector.toLinearMap rankOneVector.injective
    (g • Projectivization.mk F v hv) = _
  simp only [Projectivization.smul_mk,Projectivization.map_mk]
  change Projectivization.mk F (rankOneVector (g • v)) _ =
    Projectivization.mk F (rankOneSL g • rankOneVector v) _
  congr 1

end Atlas.Symplectic
