import Atlas.Conway.EisensteinBalancedNineFamilyCount
import Atlas.Conway.EisensteinGeneratedFrames

set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Lattices

/-- The actual Fourier bridge puts the full53460-frame local orbit into the
orbit of the standard frame under the generated Hermitian subgroup. -/
theorem eisensteinGeneratedFrames_balancedNine :
    (eisensteinBalancedNineFamily : Set EisensteinFrame) ⊆ eisensteinGeneratedFrames := by
  obtain ⟨F,hF,hG⟩ := eisensteinBalancedNineFamily_Fourier_edge
  rw [← eisensteinBalancedNineFamily_orbit _ hG]
  exact eisensteinGeneratedFrames_localOrbit _
    (eisensteinGeneratedFrames_fourier F (eisensteinGeneratedFrames_balanced hF))

end Atlas.Conway
