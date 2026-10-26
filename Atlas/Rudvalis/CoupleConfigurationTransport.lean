import Atlas.Rudvalis.CoupleQuartetOrbitExclusion

namespace Atlas.Rudvalis

abbrev QuartetsThrough (c : Set MinimalCross) :=
  {Q : Set MinimalCross // IsQuartet Q ∧ c⊆Q}

noncomputable def quartetsThroughTransport (g : gaussianLatticeGroup) (c : Set MinimalCross) :
    QuartetsThrough c ≃ QuartetsThrough (gaussianImage g c) :=
  { toFun := fun Q=>⟨gaussianImage g Q.val,(isQuartet_gaussianImage g Q.val).mpr Q.prop.1,
      Set.image_mono Q.prop.2⟩
    invFun := fun Q=>⟨gaussianImage g⁻¹ Q.val,(isQuartet_gaussianImage g⁻¹ Q.val).mpr Q.prop.1,by
      have h := Set.image_mono (f:=fun z:MinimalCross=>g⁻¹ • z) Q.prop.2
      change gaussianImage g⁻¹ (gaussianImage g c)⊆gaussianImage g⁻¹ Q.val at h
      rwa [gaussianImage_inv] at h⟩
    left_inv := fun Q=>Subtype.ext (gaussianImage_inv g Q.val)
    right_inv := fun Q=>Subtype.ext (gaussianImage_inv_right g Q.val) }

theorem generated_couple_transport (c : Set MinimalCross) (hc : IsCouple c) :
    ∃g : generatedGaussianGroup,gaussianImage g.val referenceCouple=c := by
  obtain ⟨x,y,hxy,hcxy⟩ := Set.ncard_eq_two.mp hc.1
  have hxo : CrossOrthogonal x y := hc.2
    (by rw [hcxy]; exact Or.inl rfl) (by rw [hcxy]; exact Or.inr rfl) hxy
  let := rudvalis_generated_orthogonal_pairs_transitive
  let a : OrthogonalPairs := ⟨(localReferenceCross,referenceSecondCross),reference_crosses_orthogonal⟩
  let b : OrthogonalPairs := ⟨(x,y),hxo⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq generatedGaussianGroup a b
  have hx : g.val • localReferenceCross=x := congrArg (fun z : OrthogonalPairs=>z.val.1) hg
  have hy : g.val • referenceSecondCross=y := congrArg (fun z : OrthogonalPairs=>z.val.2) hg
  refine ⟨g,?_⟩
  rw [hcxy]
  simp only [gaussianImage,referenceCouple,Set.image_insert_eq,Set.image_singleton,hx,hy]

theorem quartetsThrough_card_transport (c : Set MinimalCross) (hc : IsCouple c) :
    Nat.card (QuartetsThrough c)=Nat.card (QuartetsThrough referenceCouple) := by
  obtain ⟨g,hg⟩ := generated_couple_transport c hc
  rw [←hg]
  exact (Nat.card_congr (quartetsThroughTransport g.val referenceCouple)).symm

theorem intrinsicDozen_card_transport (c : Set MinimalCross) (hc : IsCouple c) :
    Nat.card (intrinsicDozen c)=Nat.card (intrinsicDozen referenceCouple) := by
  obtain ⟨g,hg⟩ := generated_couple_transport c hc
  rw [←hg,←intrinsicDozen_gaussianImage]
  exact gaussianImage_ncard g.val (intrinsicDozen referenceCouple)

theorem reference_quartets_card_of_dozen_equality
    (hd : intrinsicDozen referenceCouple=referenceCoordinateDozen) :
    Nat.card (QuartetsThrough referenceCouple)=5 := by
  let e : QuartetsThrough referenceCouple ≃ ReferenceCoordinateQuartets :=
    { toFun := fun Q=>⟨⟨Q.val,Q.prop.1,by
        intro z hz
        apply referenceCoordinateDozen_subset
        rw [←hd]
        exact ⟨Q.val,Q.prop.1,Q.prop.2,hz⟩⟩,Q.prop.2⟩
      invFun := fun Q=>⟨Q.val.val,Q.val.prop.1,Q.prop⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  rw [Nat.card_congr e]
  exact referenceCoordinateQuartets_card

end Atlas.Rudvalis
