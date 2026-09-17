import Atlas.Conway.EisensteinNineHexadRecognition
import Atlas.Conway.EisensteinNineHexadTransitive
import Atlas.Conway.EisensteinGeneratedUnitFrames
import Atlas.Conway.EisensteinConstantFourier

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Lattices
attribute [local irreducible] eisensteinNineHexadFamily

theorem eisensteinCrossingNineFrame_mem (b : ZMod 3) (hb : b≠0) :
    eisensteinFrameOfVector (eisensteinCrossingNineVector b hb) ∈
      eisensteinNineHexadFamily b hb := by
  unfold eisensteinCrossingNineVector
  exact eisensteinNineHexadFrame_mem_family _ _ _ _ _ _ b hb

/-- Both correction signs are reached by the actual Fourier edges into the
nonzero-residue frames, followed by their proved full local orbits. -/
theorem eisensteinGeneratedFrames_nineHexad (b : ZMod 3) (hb : b≠0) :
    (eisensteinNineHexadFamily b hb : Set EisensteinFrame) ⊆ eisensteinGeneratedFrames := by
  have hF : eisensteinFrameOfVector (eisensteinCrossingNineVector b hb) ∈
      eisensteinGeneratedFrames := by
    apply (eisensteinGeneratedFrames_fourier_iff _).mp
    exact eisensteinGeneratedFrames_unit (eisensteinFourier_constantNine_mem_unit b hb)
  change {G | G ∈ eisensteinNineHexadFamily b hb} ⊆ eisensteinGeneratedFrames
  rw [← eisensteinNineHexadFamily_orbit b hb _ (eisensteinCrossingNineFrame_mem b hb)]
  exact eisensteinGeneratedFrames_localOrbit _ hF

end Atlas.Conway
