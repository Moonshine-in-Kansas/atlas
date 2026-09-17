import Atlas.Conway.IcosianRootPointNormWord
import Atlas.Conway.IcosianAxisRootGeometry
import Atlas.Lattices.IcosianHermitianIdentities

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Every element of the full line stabilizer preserves the coordinate norm
at that axis. This uses the actual quaternionic Hermitian form and the proved
unit saturation of root lines. -/
theorem icosianAxisStabilizer_root_norm (g : icosianHermitianGroup)
    (hg : g • icosianRootAxisPoint 0=icosianRootAxisPoint 0) (r : IcosianRoot) :
    icosianRootNormWord (g • r) 0=icosianRootNormWord r 0 := by
  let a : IcosianRoot := icosianAxisRoot (0,1)
  have hp : icosianRootPoint (g • a)=icosianRootPoint a := by
    rw [icosianRootPoint_smul]
    exact congrArg Subtype.val hg
  obtain ⟨u,hu⟩ := (icosianRootPoint_eq_iff a (g • a)).mp hp
  have hh : icosianHermitian (icosianCoordinateEmbedding (g • a).val)
      (icosianCoordinateEmbedding (g • r).val)=
      icosianHermitian (icosianCoordinateEmbedding a.val) (icosianCoordinateEmbedding r.val) := by
    change icosianHermitian (icosianCoordinateEmbedding (icosianHermitianRoot g a).val)
      (icosianCoordinateEmbedding (icosianHermitianRoot g r).val)=_
    rw [icosianHermitianRoot_embedding,icosianHermitianRoot_embedding,g.property.2.1]
  rw [hu] at hh
  change icosianHermitian (icosianRightMul (icosianCoordinateEmbedding a.val) u.val.val)
      (icosianCoordinateEmbedding (g • r).val)=
      icosianHermitian (icosianCoordinateEmbedding a.val) (icosianCoordinateEmbedding r.val) at hh
  rw [icosianHermitian_rightMul_left,icosianAxisRoot_hermitian,
    icosianAxisRoot_hermitian] at hh
  apply goldenIntegerToRational_injective
  simp only [icosianRootNormWord,icosianIntegralNorm_spec]
  have hn := congrArg icosianNorm hh
  rw [icosianNorm_mul,show icosianNorm (star u.val.val)=1 from
    (Quaternion.normSq_star _).trans (icosianNormOneGroup_norm u),one_mul] at hn
  exact hn

theorem icosianAxisStabilizer_point_norm (g : icosianHermitianGroup)
    (hg : g • icosianRootAxisPoint 0=icosianRootAxisPoint 0) (p : IcosianRootPoint) :
    icosianRootPointNormWord (g • p) 0=icosianRootPointNormWord p 0 := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  rw [← icosianRootToPoint_smul]
  simp only [icosianRootPointNormWord_toPoint]
  exact icosianAxisStabilizer_root_norm g hg r

end Atlas.Conway
