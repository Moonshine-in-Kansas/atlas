import Atlas.Lattices.IcosianComparisonReverse
import Atlas.Lattices.IcosianComparisonForwardChecks
import Atlas.Lattices.IcosianGenerators

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

/-- Every vector of the specified right-icosian module maps into the retained Golay Leech lattice. -/
theorem icosianComparison_forward (z : IcosianRationalCoordinates)
    (hz : z ∈ rationalIcosianLattice) : icosianComparison z ∈ rationalLeech := by
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hz
  let S : Submodule ℤ IcosianCoordinates := rationalLeech.comap
    ((icosianComparison.toLinearMap.restrictScalars ℤ).comp icosianCoordinateEmbedding)
  have h (j : Fin 36) : icosianComparisonSourceGenerator j ∈ S := by
    obtain ⟨x,hx,he⟩ := icosianComparison_generator_check j
    change icosianComparison (icosianCoordinateEmbedding _) ∈ rationalLeech
    rw [he]
    exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩
  exact (icosianLeechModule_le_of_generators S h) hv

/-- Both actual containments, with the specified integral module and retained Golay construction. -/
theorem icosianComparison_lattice_iff (z : IcosianRationalCoordinates) :
    z ∈ rationalIcosianLattice ↔ icosianComparison z ∈ rationalLeech := by
  constructor
  · exact icosianComparison_forward z
  · intro h
    simpa only [LinearEquiv.symm_apply_apply] using
      icosianComparison_reverse (icosianComparison z) h

/-- The specified module maps onto every retained Leech vector. -/
theorem icosianComparison_lattice_surjective (x : RationalCoordinates)
    (hx : x ∈ rationalLeech) :
    ∃ z ∈ rationalIcosianLattice, icosianComparison z=x :=
  ⟨icosianComparison.symm x,icosianComparison_reverse x hx,icosianComparison.apply_symm_apply x⟩

end Atlas.Lattices
