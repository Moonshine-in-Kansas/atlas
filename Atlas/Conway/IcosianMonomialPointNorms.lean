import Atlas.Conway.IcosianRootPointNormWord
import Atlas.Conway.IcosianLocalAOrbit

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianMonomialPoint_norm_word (g : icosianLiftedMonomial)
    (p : IcosianRootPoint) (i : Fin 3) :
    icosianRootPointNormWord (icosianMonomialToHermitian g • p) i =
      icosianRootPointNormWord p (g.val.right.symm i) := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  rw [← icosianRootToPoint_smul]
  simp only [icosianRootPointNormWord_toPoint,icosianMonomialRoot_norm_word]

/-- The scalar norm at an axis is an invariant relation for the complete
monomial group, not only for its diagonal subgroup. -/
theorem icosianMonomialPoint_norm_invariant (g : icosianLiftedMonomial)
    (p : IcosianRootPoint) (i : Fin 3) :
    icosianRootPointNormWord (icosianMonomialToHermitian g • p) (g.val.right i)=
      icosianRootPointNormWord p i := by
  rw [icosianMonomialPoint_norm_word,g.val.right.symm_apply_apply]

end Atlas.Conway
