import Atlas.Conway.IcosianRootPointShapes
import Atlas.Conway.IcosianRootPointAction
import Atlas.Conway.IcosianFullFrameStabilizer

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianMonomialRoot_coordinates (g : icosianLiftedMonomial) (r : IcosianRoot)
    (i : Fin 3) : ((icosianMonomialToHermitian g • r).val i).val=
      (g.val.left i).val.val*(r.val (g.val.right.symm i)).val := by
  have h := congrFun (icosianHermitianRoot_embedding (icosianMonomialToHermitian g) r) i
  exact h

theorem icosianMonomialRoot_norm_word (g : icosianLiftedMonomial) (r : IcosianRoot)
    (i : Fin 3) : icosianRootNormWord (icosianMonomialToHermitian g • r) i=
      icosianRootNormWord r (g.val.right.symm i) := by
  apply goldenIntegerToRational_injective
  simp only [icosianRootNormWord,icosianIntegralNorm_spec]
  rw [icosianMonomialRoot_coordinates,icosianNorm_mul,icosianNormOneGroup_norm,one_mul]

theorem icosianMonomialRoot_shape (g : icosianLiftedMonomial) (r : IcosianRoot)
    (i : Fin 4) : HasIcosianRootShape (icosianMonomialToHermitian g • r) i ↔
      HasIcosianRootShape r i := by
  have hp := Atlas.triple_perm_reindex g.val.right (icosianRootNormWord r)
  simp only [HasIcosianRootShape,icosianMonomialRoot_norm_word]
  exact ⟨fun h => hp.symm.trans h,fun h => hp.trans h⟩

theorem icosianCoordinateFrame_root_shape (g : icosianCoordinateFrameStabilizer)
    (r : IcosianRoot) (i : Fin 4) : HasIcosianRootShape (g.val • r) i ↔
      HasIcosianRootShape r i := by
  obtain ⟨m,hm⟩ := (show g.val∈icosianMonomialToHermitian.range from
    icosianMonomial_range_eq_frameStabilizer.symm ▸ g.property)
  rw [← hm]
  exact icosianMonomialRoot_shape m r i

theorem icosianCoordinateFrame_rootPoint_shape (g : icosianCoordinateFrameStabilizer)
    (p : IcosianRootPoint) (i : Fin 4) : HasIcosianRootPointShape (g.val • p) i ↔
      HasIcosianRootPointShape p i := by
  have hf (g : icosianCoordinateFrameStabilizer) (p : IcosianRootPoint)
      (hp : HasIcosianRootPointShape p i) : HasIcosianRootPointShape (g.val • p) i := by
    obtain ⟨r,hr,hi⟩ := hp
    refine ⟨g.val • r,?_,(icosianCoordinateFrame_root_shape g r i).mpr hi⟩
    exact (icosianRootPoint_smul _ _).trans (congrArg (g.val • ·) hr)
  refine ⟨fun h => ?_,hf g p⟩
  have h' := hf g⁻¹ (g.val • p) h
  simpa only [Subgroup.coe_inv,inv_smul_smul] using h'

end Atlas.Conway
