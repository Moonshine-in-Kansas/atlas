import Atlas.Conway.IcosianAxisRootGeometry

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Quaternion BigOperators

/-- Negating the second nonzero coordinate preserves the actual edge glue. -/
def icosianEdgePartner (p : IcosianEdgePair) : IcosianEdgePair := by
  refine ⟨(p.val.1,⟨-p.val.2.val,?_⟩),?_,p.property.2⟩
  · change Quaternion.normSq (-p.val.2.val.val)=(2 : GoldenRational)
    rw [Quaternion.normSq_neg]
    exact p.val.2.property
  · change icosianModuloTwo p.val.1.val=icosianModuloTwo (-p.val.2.val)
    rw [map_neg icosianModuloTwo p.val.2.val,p.property.1]
    funext i j
    ext <;> simp [CharTwo.neg_eq]

theorem icosianEdgeRootBase_orthogonal_partner (p : IcosianEdgePair) :
    icosianHermitian (icosianCoordinateEmbedding (icosianEdgeRootBase p).val)
      (icosianCoordinateEmbedding (icosianEdgeRootBase (icosianEdgePartner p)).val)=0 := by
  change (1/2 : ℚ) • (∑ i,
    star (icosianCoordinateEmbedding (icosianEdgeRootBase p).val i)*
      icosianCoordinateEmbedding (icosianEdgeRootBase (icosianEdgePartner p)).val i)=0
  simp [icosianCoordinateEmbedding,icosianEdgeRootBase,icosianEdgePartner,Fin.sum_univ_succ,
    Quaternion.star_mul_self,show Quaternion.normSq p.val.1.val.val=(2 : GoldenRational) from p.val.1.property,
    show Quaternion.normSq p.val.2.val.val=(2 : GoldenRational) from p.val.2.property]

/-- In the axis coordinate plane, every root orthogonal to an edge root
lies on the explicitly constructed partner line. -/
theorem icosianEdgeRootBase_complement_unique (p : IcosianEdgePair) (r : IcosianRoot)
    (hz : r.val 0=0)
    (hh : icosianHermitian (icosianCoordinateEmbedding (icosianEdgeRootBase p).val)
      (icosianCoordinateEmbedding r.val)=0) :
    icosianRootPoint r=icosianRootPoint (icosianEdgeRootBase (icosianEdgePartner p)) := by
  have hpair : star p.val.1.val.val*(r.val 1).val+star p.val.2.val.val*(r.val 2).val=0 := by
    have he := congrArg (fun z : IcosianQuaternion => (2 : ℚ) • z) hh
    simpa [icosianHermitian,icosianCoordinateEmbedding,icosianEdgeRootBase,
      Fin.sum_univ_succ,smul_smul] using he
  obtain ⟨a,ha,hb⟩ := icosianNormTwoPair_orthogonal _ _ _ _
    p.val.1.property p.val.2.property hpair
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  refine ⟨MulOpposite.op a,?_⟩
  funext i
  fin_cases i
  · change (0 : IcosianQuaternion)*a=(r.val 0).val
    rw [hz]; simp
  · exact ha.symm
  · exact hb.symm

end Atlas.Conway
