import Atlas.Conway.IcosianRootPointAngleLevels
import Atlas.Conway.IcosianProjectiveGeometryTransport

noncomputable section
namespace Atlas.Conway

theorem icosianRootPointAngle_projective_smul (g : IcosianProjectiveModel)
    (p q : IcosianRootPoint) :
    icosianRootPointAngle (g • p) (g • q) = icosianRootPointAngle p q := by
  obtain ⟨c,rfl⟩ := icosianProjectiveProjection_surjective g
  rw [icosianProjectivePointAction_mk,icosianProjectivePointAction_mk]
  exact icosianRootPointAngle_smul c p q

theorem icosianRootPointAngle_projective_stabilizer (p q : IcosianRootPoint)
    (g : MulAction.stabilizer IcosianProjectiveModel p) :
    icosianRootPointAngle p (g • q) = icosianRootPointAngle p q := by
  have h := icosianRootPointAngle_projective_smul g.val p q
  rw [g.property] at h
  exact h

end Atlas.Conway
