import Atlas.Rudvalis.CoordinateCanonicalFrames

namespace Atlas.Rudvalis

theorem coordinateRowFrame_code_image (g : codeGroup) (p : Point) :
    gaussianImage (codeGaussianHom g) (coordinateRowFrame p)=coordinateRowFrame (codeRowImage g p) := by
  ext c
  constructor
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    change codeGaussianHom g • coordinateCross (p,x)∈coordinateRowFrame (codeRowImage g p)
    rw [codeGaussianHom_cross,coordinateCross_action,codeInnerEquiv_coordinates]
    exact ⟨codeInnerEquiv g p x,rfl⟩
  · rintro ⟨x,rfl⟩
    refine ⟨coordinateCross (p,(codeInnerEquiv g p).symm x),⟨_,rfl⟩,?_⟩
    change codeGaussianHom g • coordinateCross (p,(codeInnerEquiv g p).symm x)=_
    rw [codeGaussianHom_cross,coordinateCross_action,codeInnerEquiv_coordinates,Equiv.apply_symm_apply]

theorem coordinateRowFrame_code_transitive (p q : Point) :
    ∃g : codeGroup,gaussianImage (codeGaussianHom g) (coordinateRowFrame p)=coordinateRowFrame q := by
  have ho : coordinateCross (q,0)∈MulAction.orbit codeGroup (coordinateCross (p,0)) := by
    rw [coordinateCross_orbit _ (coordinateCross_mem _)]
    exact coordinateCross_mem _
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp ho
  rw [coordinateCross_action] at hg
  have hr := coordinateCross_row_of_eq hg
  rw [codeRowImage_coordinates] at hr
  exact ⟨g,by rw [coordinateRowFrame_code_image,hr]⟩

theorem coordinateRowFrame_code_images (p : Point) :
    {Q | ∃g : codeGroup,gaussianImage (codeGaussianHom g) (coordinateRowFrame p)=Q}=
      Set.range coordinateRowFrame := by
  ext Q
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨codeRowImage g p,(coordinateRowFrame_code_image g p).symm⟩
  · rintro ⟨q,rfl⟩
    exact coordinateRowFrame_code_transitive p q

theorem coordinateRowFrames_card : Nat.card (Set.range coordinateRowFrame)=7 := by
  rw [←Nat.card_congr (Equiv.ofInjective coordinateRowFrame coordinateRowFrame_injective)]
  simpa only [Nat.card_eq_fintype_card] using card_Point

end Atlas.Rudvalis
