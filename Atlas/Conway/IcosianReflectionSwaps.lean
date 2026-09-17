import Atlas.Conway.IcosianReflectionGeneratedElements

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

def icosianReflectionSwapMonomial (p : Fin 2) : IcosianUnitMonomial :=
  ⟨1, Equiv.swap 0 (icosianReflectionEdgePartner p)⟩

theorem icosianReflectionSwapMonomial_apply (p : Fin 2)
    (x : IcosianRationalCoordinates) (j : Fin 3) :
    icosianMonomialRepresentation (icosianReflectionSwapMonomial p) x j =
      x (Equiv.swap 0 (icosianReflectionEdgePartner p) j) := by
  rw [icosianReflectionMonomial_apply]
  simp [icosianReflectionSwapMonomial, icosianMonomialUnits]

set_option maxHeartbeats 500000 in
-- Only the three quaternionic basis vectors for each of two swaps are checked.
theorem icosianReflectionSwap_axes : ∀ p i j,
    icosianReflection (icosianReflectionEdgeRoot 0 p) (Pi.single i 1) j =
      (Pi.single i 1 : IcosianRationalCoordinates)
        (Equiv.swap 0 (icosianReflectionEdgePartner p) j) := by
  intro p i j
  fin_cases p <;> fin_cases i <;> fin_cases j <;>
    apply QuaternionAlgebra.ext <;> decide +kernel

/-- The two coordinate transpositions are actual edge-root reflections. -/
theorem icosianReflectionSwap_linear (p : Fin 2) :
    (icosianReflectionEdgeGenerator 0 p).val =
      icosianMonomialRepresentation (icosianReflectionSwapMonomial p) := by
  apply icosian_right_linear_ext
  · exact (icosianReflectionEdgeGenerator 0 p).property.1
  · exact icosianMonomialRepresentation_right_linear _
  · intro i
    funext j
    rw [icosianReflectionEdgeGenerator_apply, icosianReflectionSwapMonomial_apply]
    exact icosianReflectionSwap_axes p i j

end Atlas.Conway
