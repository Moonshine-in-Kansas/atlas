import Atlas.Conway.MonomialStabilizer

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- SO1: fixing any lattice coordinate axis vector forces membership in the actual monomial group. -/
theorem coordinateEight_fixer_mem_monomial (g : LeechIsometryGroup) (a : Omega)
    (hg : g.val (coordinateEight a) = coordinateEight a) : g ∈ monomialSubgroup := by
  rw [← standardCrossStabilizer_eq_monomial,standardCrossStabilizer_mem]
  have hs : standardCross = standardCrossAt a := standardCross_independent _ _
  rw [hs]
  apply Subtype.ext
  change leechModTwoRepresentation g (leechReduction (coordinateEight a)) =
    leechReduction (coordinateEight a)
  rw [leechModTwoRepresentation_reduce,hg]

/-- Pointwise fixation of a pair whose sum is an axis forces the same conclusion. -/
theorem axis_sum_pair_fixer_mem_monomial (g : LeechIsometryGroup) (a : Omega) (x y : leech)
    (hxy : x + y = coordinateEight a) (hx : g.val x = x) (hy : g.val y = y) :
    g ∈ monomialSubgroup := by
  apply coordinateEight_fixer_mem_monomial g a
  rw [← hxy,map_add,hx,hy]

end Atlas.Conway
