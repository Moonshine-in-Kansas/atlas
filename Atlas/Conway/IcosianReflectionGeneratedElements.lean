import Atlas.Conway.IcosianLineReflections
import Atlas.Conway.IcosianReflectionUnipotent

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Every reflection in an actual norm-two lattice vector belongs to the
root-line reflection group, independently of a chosen integral representative. -/
theorem icosianRootReflection_mem (r : IcosianRationalCoordinates)
    (hr : icosianHermitian r r = 2) (hL : r ∈ rationalIcosianLattice) :
    icosianRootReflection r hr hL ∈ icosianReflectionGroup := by
  have hL' := hL
  obtain ⟨x,hx,he⟩ := hL
  let s : IcosianRoot := ⟨x,hx,by rw [he]; exact hr⟩
  have hs : icosianRootReflectionOf s = icosianRootReflection r hr hL' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change icosianReflection (icosianCoordinateEmbedding x) v = icosianReflection r v
    rw [he]
  rw [← hs]
  exact icosianRootReflectionOf_mem s

theorem icosianReflectionDiagonalGenerator_mem (k : Fin 3) :
    icosianReflectionDiagonalGenerator k ∈ icosianReflectionGroup :=
  icosianRootReflection_mem _ _ _

theorem icosianReflectionDiagonalWord_mem_reflections :
    icosianReflectionDiagonalWord ∈ icosianReflectionGroup :=
  icosianReflectionDiagonalWord_mem _ icosianReflectionDiagonalGenerator_mem

theorem icosianReflectionEdgeGenerator_mem (k : Fin 3) (p : Fin 2) :
    icosianReflectionEdgeGenerator k p ∈ icosianReflectionGroup :=
  icosianRootReflection_mem _ _ _

theorem icosianReflectionEdgeWord_mem_reflections (k : Fin 3) (p : Fin 2) :
    icosianReflectionEdgeWord k p ∈ icosianReflectionGroup :=
  icosianReflectionGroup.mul_mem (icosianReflectionEdgeGenerator_mem k p)
    (icosianReflectionEdgeGenerator_mem 0 p)

end Atlas.Conway
