import Atlas.Rudvalis.CanonicalFrames

namespace Atlas.Rudvalis

/-- Intrinsic canonical frames identify the generated group with the full Gaussian lattice group. -/
theorem full_gaussian_mem_generated (g : gaussianLatticeGroup) : g∈generatedGaussianGroup := by
  have hF : gaussianImage g coordinateFrame∈canonicalBases := by
    obtain ⟨Q,hQ,hQF⟩ := coordinateFrame_isCanonicalBase
    refine ⟨gaussianImage g Q,(isQuartet_gaussianImage g Q).mpr hQ,?_⟩
    rw [←canonicalBase_gaussianImage,hQF]
  obtain ⟨a,ha⟩ := canonicalFrame_generated_transport _ hF
  have hfix : gaussianImage (a.val⁻¹*g) coordinateFrame=coordinateFrame := by
    rw [gaussianImage_mul,←ha,gaussianImage_inv]
  have hstab : ∀c : MinimalCross,c∈coordinateFrame ↔ (a.val⁻¹*g) • c∈coordinateFrame := by
    intro c
    have h := gaussianImage_mem (a.val⁻¹*g) coordinateFrame c
    rw [hfix] at h
    exact h.symm
  obtain ⟨b,hb⟩ := (gaussian_frame_stabilizer (a.val⁻¹*g)).mp hstab
  have hmem := generatedGaussianGroup.mul_mem a.prop (codeGaussianHom_mem_generated b)
  rwa [hb,mul_inv_cancel_left] at hmem

theorem generatedGaussianGroup_eq_top : generatedGaussianGroup=⊤ := by
  apply top_unique
  intro g _
  exact full_gaussian_mem_generated g

end Atlas.Rudvalis
