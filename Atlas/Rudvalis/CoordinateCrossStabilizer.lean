import Atlas.Rudvalis.GaussianFrameOrder
import Atlas.Rudvalis.LatticeCrossOrbits

namespace Atlas.Rudvalis

theorem coordinateCross_orbit (x : MinimalCross) (hx : x∈coordinateFrame) :
    MulAction.orbit codeGroup x=coordinateFrame := by
  apply Set.ext
  intro y
  constructor
  · intro hy
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hy
    exact coordinateFrame_code_stable g x hx
  · intro hy
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    exact MulAction.mem_orbit_iff.mpr (coordinateCrosses_transitive a b)

theorem coordinateCross_stabilizer_order (x : MinimalCross) (hx : x∈coordinateFrame) :
    Nat.card (MulAction.stabilizer codeGroup x)=49152 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup codeGroup x)
  rw [Nat.card_prod,coordinateCross_orbit x hx,coordinateFrame_card,codeGroup_order] at h
  omega

end Atlas.Rudvalis
