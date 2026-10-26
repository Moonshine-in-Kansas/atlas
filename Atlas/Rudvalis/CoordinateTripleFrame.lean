import Atlas.Rudvalis.CoordinateQuartetClassification

namespace Atlas.Rudvalis

theorem no_cross_orthogonal_coordinateFrame (w : MinimalCross) :
    ¬∀z∈coordinateFrame,CrossOrthogonal z w := by
  intro h
  obtain ⟨v,rfl⟩ := Quotient.exists_rep w
  have hv (i : Coordinate) : v.val.val i=0 := by
    have hi := h (coordinateCross i) (coordinateCross_mem i)
    change CrossOrthogonal (minimalCross (coordinateShellLift (i,true))) (minimalCross v) at hi
    rw [crossOrthogonal_mk] at hi
    change HermitianOrthogonal (coordinateMinimum i) v.val.val at hi
    exact ((coordinate_hermitianOrthogonal_pair i.1 i.2 v.val.val).mp hi).1
  have hz : v.val.val=0 := funext hv
  have hn := v.prop
  rw [hz] at hn
  norm_num [rationalDot] at hn

/-- If all but one member of an intrinsic quartet lie in the coordinate frame,
then the remaining member also lies in that frame. -/
theorem quartet_three_in_coordinateFrame (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (w : MinimalCross) (hw : w∈Q)
    (hthree : ∀q∈Q,q≠w → q∈coordinateFrame) : w∈coordinateFrame := by
  by_contra hnot
  apply no_cross_orthogonal_coordinateFrame w
  intro z hz
  by_cases hzQ : z∈Q
  · exact hQ.2.1 hzQ hw (by intro he;subst z;exact hnot hz)
  · apply hQ.2.2 z hzQ w hw
    intro y hy hyw
    exact (coordinateFrame_orthogonal_iff z y hz (hthree y hy hyw)).mpr
      (by intro he;subst z;exact hzQ hy)

/-- The same triple-in-frame principle holds in every actual Gaussian translate. -/
theorem quartet_three_in_gaussian_coordinateFrame (g : gaussianLatticeGroup)
    (Q : Set MinimalCross) (hQ : IsQuartet Q) (w : MinimalCross) (hw : w∈Q)
    (hthree : ∀q∈Q,q≠w → q∈gaussianImage g coordinateFrame) :
    w∈gaussianImage g coordinateFrame := by
  have hQ' := (isQuartet_gaussianImage g⁻¹ Q).mpr hQ
  have hw' : g⁻¹ • w∈gaussianImage g⁻¹ Q := Set.mem_image_of_mem _ hw
  have hthree' : ∀q∈gaussianImage g⁻¹ Q,q≠g⁻¹ • w → q∈coordinateFrame := by
    rintro q ⟨z,hz,rfl⟩ hne
    have hz' := hthree z hz (by intro he;subst z;exact hne rfl)
    obtain ⟨u,hu,he⟩ := hz'
    rw [←he]
    change g⁻¹ • (g • u)∈coordinateFrame
    rwa [inv_smul_smul]
  have h := quartet_three_in_coordinateFrame _ hQ' _ hw' hthree'
  have hh : g • (g⁻¹ • w)∈gaussianImage g coordinateFrame := Set.mem_image_of_mem _ h
  simpa only [smul_inv_smul] using hh

end Atlas.Rudvalis
