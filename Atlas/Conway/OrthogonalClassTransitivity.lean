import Atlas.Conway.OrthogonalMinimumClasses
import Atlas.Conway.OrthogonalDisjointOrbits
import Atlas.Conway.OrthogonalContainingOctadOrbit
import Atlas.Conway.OrthogonalOddOrbit

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem orthogonalClass_transitive (i j : Omega) (hij : i ≠ j) (t : Fin 5)
    (x y : OrthogonalClassType i j t) :
    ∃ r : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j),
      r.val.val.val (orthogonalClassValue i j t x) = orthogonalClassValue i j t y := by
  fin_cases t
  · change ∃ r : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j),
      r.val.val.val x.val = y.val
    obtain ⟨s,hs⟩ := monomial_pair_sign_swap i j hij
    rcases x.prop with hx | hx <;> rcases y.prop with hy | hy
    · exact ⟨1,by change x.val = y.val; exact hx.trans hy.symm⟩
    · exact ⟨s,by simpa only [hx,hy] using hs⟩
    · exact ⟨s,by rw [hx,hy,map_neg,hs,neg_neg]⟩
    · exact ⟨1,by change x.val = y.val; exact hx.trans hy.symm⟩
  · exact orthogonal_disjoint_four_transitive i j hij x.val y.val x.prop.1 y.prop.1
      (x.prop.2 i (by simp)) (x.prop.2 j (by simp))
      (y.prop.2 i (by simp)) (y.prop.2 j (by simp))
  · exact orthogonal_disjoint_octad_transitive i j hij x.val y.val x.prop.1 y.prop.1
      (x.prop.2 i (by simp)) (x.prop.2 j (by simp))
      (y.prop.2 i (by simp)) (y.prop.2 j (by simp))
  · exact orthogonal_containing_octad_transitive i j hij x.val y.val x.prop.1 y.prop.1
      x.prop.2.1 y.prop.2.1 x.prop.2.2 y.prop.2.2
  · exact orthogonal_odd_minimum_transitive i j hij x.val y.val x.prop.1 y.prop.1
      x.prop.2 y.prop.2

end Atlas.Conway
