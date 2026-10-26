import Atlas.Rudvalis.CoordinateRowOrbit

namespace Atlas.Rudvalis

/-- Quartets determining a frame, distinguished from all quartets contained in it. -/
def quartetsDetermining (F : Set MinimalCross) : Set (Set MinimalCross) :=
  {Q | IsQuartet Q ∧ canonicalBase Q=F}

noncomputable def quartetsDeterminingEquiv (g : gaussianLatticeGroup) (F : Set MinimalCross) :
    quartetsDetermining F ≃ quartetsDetermining (gaussianImage g F) where
  toFun Q := ⟨gaussianImage g Q.val,(isQuartet_gaussianImage g Q.val).mpr Q.prop.1,by
    rw [←canonicalBase_gaussianImage,Q.prop.2]⟩
  invFun Q := ⟨gaussianImage g⁻¹ Q.val,(isQuartet_gaussianImage g⁻¹ Q.val).mpr Q.prop.1,by
    rw [←canonicalBase_gaussianImage,Q.prop.2,gaussianImage_inv]⟩
  left_inv Q := Subtype.ext (gaussianImage_inv g Q.val)
  right_inv Q := Subtype.ext (gaussianImage_inv_right g Q.val)

section Transport
variable (htrans : ∀Q : Set MinimalCross,IsQuartet Q →
  ∃g : generatedGaussianGroup,gaussianImage g.val (coordinateRowFrame (rowLabel 0))=Q)
include htrans

theorem quartetsDetermining_coordinateFrame_of_transport :
    quartetsDetermining coordinateFrame=Set.range coordinateRowFrame := by
  ext Q
  constructor
  · rintro ⟨hQ,hB⟩
    obtain ⟨g,hg⟩ := htrans Q hQ
    have hF : gaussianImage g.val coordinateFrame=coordinateFrame := by
      rw [←coordinateRow_canonicalBase_eq (rowLabel 0),canonicalBase_gaussianImage,hg,hB]
      exact (coordinateRow_canonicalBase_eq _).symm
    have hf : ∀c,c∈coordinateFrame ↔ g.val • c∈coordinateFrame := by
      intro c
      simpa only [hF] using (gaussianImage_mem g.val coordinateFrame c).symm
    obtain ⟨k,hk⟩ := (gaussian_frame_stabilizer g.val).mp hf
    refine ⟨codeRowImage k (rowLabel 0),?_⟩
    rw [←coordinateRowFrame_code_image,hk,hg]
  · rintro ⟨p,rfl⟩
    exact ⟨coordinateRowFrame_isQuartet p,coordinateRow_canonicalBase_eq p⟩

theorem quartetsDetermining_coordinateFrame_card_of_transport :
    Nat.card (quartetsDetermining coordinateFrame)=7 := by
  rw [quartetsDetermining_coordinateFrame_of_transport htrans,coordinateRowFrames_card]

theorem canonicalBase_transport_of_quartet_transport (Q : Set MinimalCross) (hQ : IsQuartet Q) :
    ∃g : generatedGaussianGroup,canonicalBase Q=gaussianImage g.val coordinateFrame := by
  obtain ⟨g,hg⟩ := htrans Q hQ
  refine ⟨g,?_⟩
  rw [←coordinateRow_canonicalBase_eq (rowLabel 0),canonicalBase_gaussianImage,hg]

theorem canonicalFrame_generated_transport_of_quartet_transport
    (F : Set MinimalCross) (hF : F∈canonicalBases) :
    ∃g : generatedGaussianGroup,gaussianImage g.val coordinateFrame=F := by
  obtain ⟨Q,hQ,rfl⟩ := hF
  obtain ⟨g,hg⟩ := canonicalBase_transport_of_quartet_transport htrans Q hQ
  exact ⟨g,hg.symm⟩

theorem canonicalFrame_isFrame_of_quartet_transport
    (F : Set MinimalCross) (hF : F∈canonicalBases) : IsFrame F := by
  obtain ⟨g,rfl⟩ := canonicalFrame_generated_transport_of_quartet_transport htrans F hF
  exact (isFrame_gaussianImage g.val coordinateFrame).mpr coordinateFrame_isFrame

theorem quartetsDetermining_card_of_quartet_transport
    (F : Set MinimalCross) (hF : F∈canonicalBases) : Nat.card (quartetsDetermining F)=7 := by
  obtain ⟨g,rfl⟩ := canonicalFrame_generated_transport_of_quartet_transport htrans F hF
  rw [←Nat.card_congr (quartetsDeterminingEquiv g.val coordinateFrame)]
  exact quartetsDetermining_coordinateFrame_card_of_transport htrans

end Transport
end Atlas.Rudvalis
