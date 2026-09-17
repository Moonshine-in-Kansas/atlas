import Atlas.Lattices.EisensteinRational

namespace Atlas.Lattices
open Atlas.Algebra

/-- Integral scalar multiplication agrees with the rational scalar rotation. -/
theorem eisensteinCoordinateEmbedding_omega (z : EisensteinCoordinates) :
    eisensteinCoordinateEmbedding (eisensteinOmega • z) =
      eisensteinRotation (eisensteinCoordinateEmbedding z) := by
  funext i
  change eisensteinToRational (eisensteinOmega * z i) =
    rationalOmega * eisensteinToRational (z i)
  rw [map_mul]
  rfl

/-- The actual integral congruence lattice is invariant under omega. -/
theorem eisensteinRotation_mem_rationalLattice
    {z : EisensteinRationalCoordinates} (hz : z ∈ rationalEisensteinLattice) :
    eisensteinRotation z ∈ rationalEisensteinLattice := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨eisensteinOmega • w, eisensteinLeechModule.smul_mem eisensteinOmega hw,
    eisensteinCoordinateEmbedding_omega w⟩

/-- Rotation preserves the rational image of the integral lattice in both directions. -/
theorem eisensteinRotation_lattice_iff (z : EisensteinRationalCoordinates) :
    z ∈ rationalEisensteinLattice ↔ eisensteinRotation z ∈ rationalEisensteinLattice := by
  constructor
  · exact eisensteinRotation_mem_rationalLattice
  · intro hz
    have h := eisensteinRotation_mem_rationalLattice
      (eisensteinRotation_mem_rationalLattice hz)
    rwa [eisensteinRotation_cube] at h

end Atlas.Lattices
