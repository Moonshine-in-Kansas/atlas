import Atlas.Fischer.SemilinearGeneratedNormalizer
import Atlas.Fischer.BasicFrameCoordinateHom

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Full frame-stabilizing operators whose actual ray action belongs to the
root-generated group. Scalars may occur in this inverse image. -/
def generatedBasicFrameStabilizer : Subgroup basicFrameStabilizer :=
  generatedRayPreimage.comap basicFrameStabilizer.subtype

instance generatedBasicFrameStabilizerNormal : generatedBasicFrameStabilizer.Normal :=
  Subgroup.Normal.comap inferInstance basicFrameStabilizer.subtype

/-- The actual induced coordinate image L0 in the retained Mathieu group. -/
def generatedFrameMathieuImage : Subgroup Mathieu24CodeModel :=
  generatedBasicFrameStabilizer.map basicFrameCoordinateHom

instance generatedFrameMathieuImageNormal : generatedFrameMathieuImage.Normal :=
  Subgroup.Normal.map inferInstance basicFrameCoordinateHom basicFrameCoordinateHom_surjective

theorem generatedFrameMathieuImage_mem_of_generated (e : SemilinearAlgebraAutomorphism)
    (he : e ∈ rootGeneratedAlgebraGroup) (hf : e ∈ basicFrameStabilizer) :
    basicFrameCoordinateHom ⟨e,hf⟩ ∈ generatedFrameMathieuImage := by
  refine ⟨⟨e,hf⟩,?_,rfl⟩
  change semilinearDisplayedRayAction e ∈ rootGeneratedRayGroup
  rw [← rootGeneratedAlgebraGroup_ray_image]
  exact ⟨e,he,rfl⟩

/-- A literal moved basic ray witnesses nontriviality of the coordinate image. -/
theorem generatedFrameMathieuImage_ne_bot_of_moved (e : SemilinearAlgebraAutomorphism)
    (he : e ∈ rootGeneratedAlgebraGroup) (hf : e ∈ basicFrameStabilizer) (i : Omega)
    (hi : rootRay (e.val (basicAxis i)) ≠ rootRay (basicAxis i)) :
    generatedFrameMathieuImage ≠ ⊥ := by
  intro hb
  have hm := generatedFrameMathieuImage_mem_of_generated e he hf
  rw [hb] at hm
  have h := basicFrameCoordinate_ray ⟨e,hf⟩ i
  change basicFrameCoordinate ⟨e,hf⟩=1 at hm
  rw [hm] at h
  exact hi h

end Atlas.Fischer
