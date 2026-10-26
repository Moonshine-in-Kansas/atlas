import Atlas.Rudvalis.CanonicalFrames

namespace Atlas.Rudvalis

/-- The distinct intrinsic dozens determined by couples in a set of crosses. -/
def quartetDozens (Q : Set MinimalCross) : Set (Set MinimalCross) :=
  {D | ∃c : Set MinimalCross,IsCouple c ∧ c⊆Q ∧ intrinsicDozen c=D}

theorem quartetDozens_gaussianImage_forward (g : gaussianLatticeGroup) (Q D : Set MinimalCross)
    (hD : D∈quartetDozens Q) : gaussianImage g D∈quartetDozens (gaussianImage g Q) := by
  obtain ⟨c,hc,hQ,rfl⟩ := hD
  exact ⟨gaussianImage g c,(isCouple_gaussianImage g c).mpr hc,Set.image_mono hQ,
    (intrinsicDozen_gaussianImage g c).symm⟩

theorem quartetDozens_gaussianImage_iff (g : gaussianLatticeGroup) (Q D : Set MinimalCross) :
    gaussianImage g D∈quartetDozens (gaussianImage g Q) ↔ D∈quartetDozens Q := by
  constructor
  · intro h
    have hi := quartetDozens_gaussianImage_forward g⁻¹ _ _ h
    simpa only [gaussianImage_inv] using hi
  · exact quartetDozens_gaussianImage_forward g Q D

noncomputable def gaussianConfigurationEquiv (g : gaussianLatticeGroup) : Equiv.Perm (Set MinimalCross) where
  toFun := gaussianImage g
  invFun := gaussianImage g⁻¹
  left_inv := gaussianImage_inv g
  right_inv := gaussianImage_inv_right g

noncomputable def quartetDozensEquiv (g : gaussianLatticeGroup) (Q : Set MinimalCross) :
    quartetDozens Q ≃ quartetDozens (gaussianImage g Q) :=
  Equiv.subtypeEquiv (gaussianConfigurationEquiv g)
    (fun D => (quartetDozens_gaussianImage_iff g Q D).symm)

theorem quartetDozens_image_exists (g : gaussianLatticeGroup) (Q D : Set MinimalCross)
    (hD : D∈quartetDozens (gaussianImage g Q)) :
    ∃E∈quartetDozens Q,gaussianImage g E=D := by
  obtain ⟨E,hE⟩ := (quartetDozensEquiv g Q).surjective ⟨D,hD⟩
  exact ⟨E.val,E.prop,congrArg Subtype.val hE⟩

theorem quartetDozens_card (Q : Set MinimalCross) (hQ : IsQuartet Q) : Nat.card (quartetDozens Q)=3 := by
  obtain ⟨g,rfl⟩ := generated_quartet_transport Q hQ
  rw [←Nat.card_congr (quartetDozensEquiv g.val (coordinateRowFrame (rowLabel 0)))]
  exact rowCoupleDozens_card (rowLabel 0)

theorem quartetDozen_card (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (D : Set MinimalCross) (hD : D∈quartetDozens Q) : Nat.card D=12 := by
  obtain ⟨g,rfl⟩ := generated_quartet_transport Q hQ
  obtain ⟨E,hE,rfl⟩ := quartetDozens_image_exists g.val _ D hD
  change (gaussianImage g.val E).ncard=12
  rw [gaussianImage_ncard]
  exact (coordinateRow_three_dozen_geometry (rowLabel 0)).2.1 E hE

theorem gaussianImage_inter (g : gaussianLatticeGroup) (D E : Set MinimalCross) :
    gaussianImage g (D∩E)=gaussianImage g D∩gaussianImage g E :=
  Set.image_inter (MulAction.injective g)

theorem quartetDozens_intersection (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (D E : Set MinimalCross) (hD : D∈quartetDozens Q) (hE : E∈quartetDozens Q) (hne : D≠E) :
    D∩E=Q := by
  obtain ⟨g,rfl⟩ := generated_quartet_transport Q hQ
  obtain ⟨D',hD',rfl⟩ := quartetDozens_image_exists g.val _ D hD
  obtain ⟨E',hE',rfl⟩ := quartetDozens_image_exists g.val _ E hE
  have hn : D'≠E' := fun h=>hne (congrArg (gaussianImage g.val) h)
  rw [←gaussianImage_inter,(coordinateRow_three_dozen_geometry (rowLabel 0)).2.2.1 D' hD' E' hE' hn]

theorem quartetDozens_union (Q : Set MinimalCross) :
    {x | ∃D∈quartetDozens Q,x∈D}=canonicalBase Q := by
  ext x
  constructor
  · rintro ⟨D,⟨c,hc,hQ,rfl⟩,hx⟩
    exact ⟨c,hc,hQ,hx⟩
  · rintro ⟨c,hc,hQ,hx⟩
    exact ⟨intrinsicDozen c,⟨c,hc,hQ,rfl⟩,hx⟩

/-- Every intrinsic quartet determines three twelve-cross dozens, meeting in that quartet,
and their union is its genuine canonical Gaussian frame. -/
theorem quartet_three_dozen_geometry (Q : Set MinimalCross) (hQ : IsQuartet Q) :
    Nat.card (quartetDozens Q)=3 ∧
    (∀D∈quartetDozens Q,Nat.card D=12) ∧
    (∀D∈quartetDozens Q,∀E∈quartetDozens Q,D≠E → D∩E=Q) ∧
    {x | ∃D∈quartetDozens Q,x∈D}=canonicalBase Q ∧ IsFrame (canonicalBase Q) :=
  ⟨quartetDozens_card Q hQ,fun D=>quartetDozen_card Q hQ D,
    fun D hD E hE=>quartetDozens_intersection Q hQ D E hD hE,
    quartetDozens_union Q,canonicalBase_isFrame Q hQ⟩

end Atlas.Rudvalis
