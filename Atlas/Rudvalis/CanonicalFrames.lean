import Atlas.Rudvalis.CanonicalFrameFibres
import Atlas.Rudvalis.QuartetGlobalTransitivity

namespace Atlas.Rudvalis

theorem quartetsDetermining_coordinateFrame :
    quartetsDetermining coordinateFrame=Set.range coordinateRowFrame :=
  quartetsDetermining_coordinateFrame_of_transport generated_quartet_transport

theorem quartetsDetermining_coordinateFrame_card :
    Nat.card (quartetsDetermining coordinateFrame)=7 :=
  quartetsDetermining_coordinateFrame_card_of_transport generated_quartet_transport

theorem canonicalBase_generated_transport (Q : Set MinimalCross) (hQ : IsQuartet Q) :
    ∃g : generatedGaussianGroup,canonicalBase Q=gaussianImage g.val coordinateFrame :=
  canonicalBase_transport_of_quartet_transport generated_quartet_transport Q hQ

theorem canonicalFrame_generated_transport (F : Set MinimalCross) (hF : F∈canonicalBases) :
    ∃g : generatedGaussianGroup,gaussianImage g.val coordinateFrame=F :=
  canonicalFrame_generated_transport_of_quartet_transport generated_quartet_transport F hF

theorem canonicalFrame_isFrame (F : Set MinimalCross) (hF : F∈canonicalBases) : IsFrame F :=
  canonicalFrame_isFrame_of_quartet_transport generated_quartet_transport F hF

theorem canonicalBase_isFrame (Q : Set MinimalCross) (hQ : IsQuartet Q) : IsFrame (canonicalBase Q) :=
  canonicalFrame_isFrame _ ⟨Q,hQ,rfl⟩

/-- Exactly seven quartets determine each canonical frame. -/
theorem quartetsDetermining_card (F : Set MinimalCross) (hF : F∈canonicalBases) :
    Nat.card (quartetsDetermining F)=7 :=
  quartetsDetermining_card_of_quartet_transport generated_quartet_transport F hF

theorem canonicalFrames_generated_transitive (F F' : Set MinimalCross)
    (hF : F∈canonicalBases) (hF' : F'∈canonicalBases) :
    ∃g : generatedGaussianGroup,gaussianImage g.val F=F' := by
  obtain ⟨g,rfl⟩ := canonicalFrame_generated_transport F hF
  obtain ⟨h,rfl⟩ := canonicalFrame_generated_transport F' hF'
  refine ⟨h*g⁻¹,?_⟩
  change ((fun c : MinimalCross => (h.val*g.val⁻¹) • c) '' ((fun c : MinimalCross=>g.val • c) '' coordinateFrame))=_
  rw [Set.image_image]
  have he : (fun c : MinimalCross => (h.val*g.val⁻¹) • (g.val • c))=(fun c=>h.val • c) := by
    funext c; rw [mul_smul,inv_smul_smul]
  rw [he]
  rfl

end Atlas.Rudvalis
