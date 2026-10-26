import Atlas.Rudvalis.ReferenceQuartetExhaustion
import Atlas.Rudvalis.CoordinateCanonicalFrames
import Atlas.Rudvalis.CoupleQuartetOrbit
import Atlas.Rudvalis.LocalFusionObstruction

namespace Atlas.Rudvalis

theorem gaussianImage_one (s : Set MinimalCross) : gaussianImage 1 s=s := by
  simp [gaussianImage]

theorem gaussianImage_mul (g h : gaussianLatticeGroup) (s : Set MinimalCross) :
    gaussianImage (g*h) s=gaussianImage g (gaussianImage h s) := by
  simp only [gaussianImage,Set.image_image,mul_smul]

/-- An actual Gaussian stabilizer of a coordinate row quartet is already a code automorphism. -/
theorem gaussian_coordinateRow_stabilizer_le_code (g : gaussianLatticeGroup) (p : Point)
    (hg : gaussianImage g (coordinateRowFrame p)=coordinateRowFrame p) :
    ∃h : codeGroup,codeGaussianHom h=g := by
  have hF : gaussianImage g coordinateFrame=coordinateFrame := by
    rw [←coordinateRow_canonicalBase_eq p,canonicalBase_gaussianImage,hg]
  apply (gaussian_frame_stabilizer g).mp
  intro c
  have h := gaussianImage_mem g coordinateFrame c
  rw [hF] at h
  exact h.symm

theorem localFusionT_moves_coordinateRow (p : Point) :
    gaussianImage localFusionT (coordinateRowFrame p)≠coordinateRowFrame p := by
  intro h
  exact localFusionT_not_codeGroup (gaussian_coordinateRow_stabilizer_le_code localFusionT p h)

/-- The actual pointwise couple group is transitive on its five intrinsic quartets. -/
theorem coupleFusion_reference_quartet_transport (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (hc : referenceCouple⊆Q) :
    ∃g : coupleFusionGroup,gaussianImage g.val (coordinateRowFrame (rowLabel 0))=Q := by
  classical
  by_cases hrow : Q=coordinateRowFrame (rowLabel 0)
  · exact ⟨1,by rw [hrow];exact gaussianImage_one _⟩
  let S := gaussianImage localFusionT (coordinateRowFrame (rowLabel 0))
  have hS : IsQuartet S := (isQuartet_gaussianImage _ _).mpr (coordinateRowFrame_isQuartet _)
  have hc0 : referenceCouple⊆coordinateRowFrame (rowLabel 0) :=
    (referenceCouple_subset_row_iff _).mpr rfl
  have hcS : referenceCouple⊆S := by
    have h := Set.image_mono (f:=fun c : MinimalCross=>localFusionT • c) hc0
    change gaussianImage localFusionT referenceCouple⊆S at h
    rw [coupleFusionGroup_preserves_referenceCouple ⟨localFusionT,localFusionT_mem_coupleFusionGroup⟩] at h
    exact h
  have subsetFrame (R : Set MinimalCross) (hR : IsQuartet R) (hcR : referenceCouple⊆R) :
      R⊆coordinateFrame := by
    intro c hc
    have hd : c∈intrinsicDozen referenceCouple := ⟨R,hR,hcR,hc⟩
    rw [reference_intrinsicDozen_eq] at hd
    exact referenceCoordinateDozen_subset hd
  obtain ⟨k,hk⟩ := referenceCoordinateQuartets_nonrow_transitive S Q hS hQ
    (subsetFrame S hS hcS) (subsetFrame Q hQ hc) hcS hc
    (localFusionT_moves_coordinateRow _) hrow
  refine ⟨⟨coupleGaussianHom k*localFusionT,
    coupleFusionGroup.mul_mem (coupleGaussianHom_mem k) localFusionT_mem_coupleFusionGroup⟩,?_⟩
  rw [gaussianImage_mul]
  change gaussianImage (codeGaussianHom k.val) S=Q
  simpa only [gaussianImage,codeGaussianHom_cross] using hk

end Atlas.Rudvalis
