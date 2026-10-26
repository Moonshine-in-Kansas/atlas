import Atlas.Rudvalis.GaussianOrbitFrame
import Atlas.Rudvalis.CoordinateLocalOrbits

namespace Atlas.Rudvalis

/-- Fusion from a coordinate row to outside that row rules out a 27-point
orbit equal to the coordinate-frame complement. This uses the actual full
frame stabilizer, not a presumed final order of the Gaussian group. -/
theorem gaussian_no_coordinate_complement_orbit (K : Subgroup gaussianLatticeGroup)
    (p : Point) (x : E) (y z : MinimalCross)
    (hy : y∈coordinateRowFrame p) (hz : z∉coordinateRowFrame p)
    (hfix : ∀g : K,g • coordinateCross (p,x)=coordinateCross (p,x))
    (hmove : ∃g : K,g • y=z) :
    MulAction.orbit K y≠coordinateFrame\{coordinateCross (p,x)} := by
  intro ho
  have hK := gaussian_orbit_coordinate_complement K (coordinateCross (p,x)) y
    (coordinateCross_mem _) hfix ho
  obtain ⟨g,hg⟩ := hmove
  obtain ⟨a,ha⟩ := hK g.prop
  have hax : a • coordinateCross (p,x)=coordinateCross (p,x) := by
    rw [←codeGaussianHom_cross,ha]
    exact hfix g
  let b : MulAction.stabilizer codeGroup (coordinateCross (p,x)) := ⟨a,hax⟩
  have hh := coordinateCross_stabilizer_row_mem p x b y hy
  apply hz
  change a • y∈coordinateRowFrame p at hh
  rw [←codeGaussianHom_cross,ha] at hh
  exact hg ▸ hh

end Atlas.Rudvalis
