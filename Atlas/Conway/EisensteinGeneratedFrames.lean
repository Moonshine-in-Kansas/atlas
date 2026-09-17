import Atlas.Conway.EisensteinBalancedFourier
import Atlas.GroupTheory.TransitiveFullStabilizer
set_option maxRecDepth 10000

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction

/-- The subgroup generated inside the full Hermitian group by the full local
stabilizer and the actual corrected Fourier isometry. -/
def eisensteinGeneratedGroup : Subgroup eisensteinHermitianGroup :=
  Subgroup.closure ((eisensteinCoordinateFrameStabilizer : Set eisensteinHermitianGroup) ∪
    {eisensteinFourierIsometry})

theorem eisensteinLocal_le_generated :
    eisensteinCoordinateFrameStabilizer ≤ eisensteinGeneratedGroup := by
  intro g hg
  exact Subgroup.subset_closure (Or.inl hg)

theorem eisensteinFourier_mem_generated : eisensteinFourierIsometry ∈ eisensteinGeneratedGroup :=
  Subgroup.subset_closure (Or.inr rfl)

def eisensteinGeneratedFrames : Set EisensteinFrame :=
  orbit eisensteinGeneratedGroup eisensteinStandardFrame

theorem eisensteinGeneratedFrames_standard : eisensteinStandardFrame ∈ eisensteinGeneratedFrames :=
  mem_orbit_self _

theorem eisensteinGeneratedFrames_local (g : eisensteinCoordinateFrameStabilizer)
    (F : EisensteinFrame) (hF : F ∈ eisensteinGeneratedFrames) :
    g.val • F ∈ eisensteinGeneratedFrames :=
  mapsTo_smul_orbit (⟨g.val,eisensteinLocal_le_generated g.property⟩ : eisensteinGeneratedGroup)
    eisensteinStandardFrame hF

theorem eisensteinGeneratedFrames_fourier (F : EisensteinFrame)
    (hF : F ∈ eisensteinGeneratedFrames) :
    eisensteinFourierIsometry • F ∈ eisensteinGeneratedFrames :=
  mapsTo_smul_orbit (⟨_,eisensteinFourier_mem_generated⟩ : eisensteinGeneratedGroup)
    eisensteinStandardFrame hF

theorem eisensteinGeneratedFrames_fourier_iff (F : EisensteinFrame) :
    eisensteinFourierIsometry • F ∈ eisensteinGeneratedFrames ↔ F ∈ eisensteinGeneratedFrames := by
  constructor
  · intro h
    have hx := mapsTo_smul_orbit
      (⟨eisensteinFourierIsometry⁻¹,eisensteinGeneratedGroup.inv_mem
        eisensteinFourier_mem_generated⟩ : eisensteinGeneratedGroup) eisensteinStandardFrame h
    change eisensteinFourierIsometry⁻¹ • (eisensteinFourierIsometry • F) ∈
      eisensteinGeneratedFrames at hx
    simpa only [inv_smul_smul] using hx
  · exact eisensteinGeneratedFrames_fourier F

theorem eisensteinGeneratedFrames_localOrbit (F : EisensteinFrame)
    (hF : F ∈ eisensteinGeneratedFrames) :
    orbit eisensteinCoordinateFrameStabilizer F ⊆ eisensteinGeneratedFrames := by
  rintro G ⟨g,rfl⟩
  exact eisensteinGeneratedFrames_local g F hF

theorem eisensteinGeneratedFrames_triad :
    (eisensteinTriadFamily : Set EisensteinFrame) ⊆ eisensteinGeneratedFrames := by
  rw [← eisensteinTriadFamily_orbit _ eisensteinFourier_standard_mem_triad]
  exact eisensteinGeneratedFrames_localOrbit _
    (eisensteinGeneratedFrames_fourier _ eisensteinGeneratedFrames_standard)

theorem eisensteinGeneratedFrames_balanced :
    (eisensteinBalancedFamily : Set EisensteinFrame) ⊆ eisensteinGeneratedFrames := by
  have h : eisensteinTriadFrame {0,1,7} (by decide) 0 ∈ eisensteinGeneratedFrames :=
    eisensteinGeneratedFrames_triad (eisensteinTriadFrame_mem_family _ _ _)
  have hh := eisensteinGeneratedFrames_fourier _ h
  rw [← eisensteinBalancedFamily_orbit _ eisensteinFourier_triad_mem_balanced]
  exact eisensteinGeneratedFrames_localOrbit _ hh

end Atlas.Conway
