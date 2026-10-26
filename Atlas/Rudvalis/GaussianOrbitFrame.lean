import Atlas.Rudvalis.GaussianFrame

namespace Atlas.Rudvalis

/-- If a point-fixing group has precisely the remaining coordinate frame as an
orbit, then it lies in the already identified full code-frame stabilizer. -/
theorem gaussian_orbit_coordinate_complement (K : Subgroup gaussianLatticeGroup)
    (x y : MinimalCross) (hx : x∈coordinateFrame)
    (hfix : ∀g : K,g • x=x)
    (horbit : MulAction.orbit K y=coordinateFrame\{x}) :
    K≤codeGaussianHom.range := by
  have hstable (g : K) (c : MinimalCross) (hc : c∈coordinateFrame) :
      g • c∈coordinateFrame := by
    by_cases he : c=x
    · simpa [he,hfix g] using hx
    · have ho : c∈MulAction.orbit K y := by rw [horbit]; exact ⟨hc,he⟩
      have ht := MulAction.mapsTo_smul_orbit g y ho
      rw [horbit] at ht
      exact ht.1
  intro g hg
  let k : K := ⟨g,hg⟩
  apply (gaussian_frame_stabilizer g).mp
  intro c
  constructor
  · exact hstable k c
  · intro hc
    have h := hstable k⁻¹ (k • c) hc
    simpa using h

end Atlas.Rudvalis
