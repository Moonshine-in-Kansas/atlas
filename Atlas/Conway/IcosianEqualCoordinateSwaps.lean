import Atlas.Conway.IcosianLocalAOrbit

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Equal coordinates give an actual monomial line stabilizer element. -/
theorem icosianEqualCoordinate_swap_fixes (r : IcosianRoot) (i j : Fin 3)
    (h : r.val i=r.val j) :
    icosianMonomialToHermitian (icosianPureBlockPermutation (Equiv.swap i j)) •
      icosianRootPoint r=icosianRootPoint r := by
  apply (icosianMonomial_line_iff _ _).mpr
  refine ⟨1,?_⟩
  intro k
  change (1 : IcosianQuaternion)*(r.val ((Equiv.swap i j).symm k)).val=
    (r.val k).val*1
  simp only [one_mul,mul_one,Equiv.symm_swap]
  by_cases hki : k=i
  · subst k; simp [h]
  by_cases hkj : k=j
  · subst k; simp [h]
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

end Atlas.Conway
