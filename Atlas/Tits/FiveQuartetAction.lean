import Atlas.Tits.LocalOrders
import Atlas.Rudvalis.QuartetLocalTransitivity
import Atlas.Rudvalis.CoordinateRowOrbit

/-! The actual projective pair stabilizer acts on its five intrinsic quartets.
The distinguished quartet stabilizer is precisely the inherited monomial pair group. -/
namespace Atlas.Tits
open Atlas.Rudvalis

abbrev FiveQuartets := QuartetsThrough referenceCouple

noncomputable def referenceQuartet : FiveQuartets :=
  ⟨coordinateRowFrame (rowLabel 0),coordinateRowFrame_isQuartet _,
    (referenceCouple_subset_row_iff _).mpr rfl⟩

theorem cardFiveQuartets : Nat.card FiveQuartets=5 := reference_quartets_card

theorem projective_quartet_image (g : RudvalisGroup) (Q : Set MinimalCross) :
    IsQuartet ((fun c=>g • c) '' Q) ↔ IsQuartet Q := by
  induction g using QuotientGroup.induction_on with
  | H g => exact isQuartet_gaussianImage g Q

theorem pair_referenceCouple_image (g : pairStabilizer) :
    (fun c : MinimalCross=>g.val.val • c) '' referenceCouple=referenceCouple := by
  have hx : g.val.val • localReferenceCross=localReferenceCross := g.val.prop
  have hy : g.val.val • referenceSecondCross=referenceSecondCross := congrArg Subtype.val g.prop
  simp only [referenceCouple,Set.image_insert_eq,Set.image_singleton,hx,hy]

noncomputable instance fiveQuartetAction : MulAction pairStabilizer FiveQuartets where
  smul g Q := ⟨(fun c=>g.val.val • c) '' Q.val,
    (projective_quartet_image _ _).mpr Q.prop.1,by
      have h := Set.image_mono (f := fun c : MinimalCross=>g.val.val • c) Q.prop.2
      rwa [pair_referenceCouple_image] at h⟩
  one_smul Q := Subtype.ext (by
    change (fun c : MinimalCross=>(1 : RudvalisGroup) • c) '' Q.val=Q.val
    simp only [one_smul]
    exact Set.image_id _)
  mul_smul g h Q := Subtype.ext (by
    change (fun c : MinimalCross=>(g.val.val*h.val.val) • c) '' Q.val=
      (fun c : MinimalCross=>g.val.val • c) '' ((fun c : MinimalCross=>h.val.val • c) '' Q.val)
    simp only [mul_smul,Set.image_image])

@[simp] theorem fiveQuartet_smul_val (g : pairStabilizer) (Q : FiveQuartets) :
    (g • Q).val=(fun c=>g.val.val • c) '' Q.val := rfl

noncomputable def fiveQuartetHom : pairStabilizer →* Equiv.Perm FiveQuartets :=
  MulAction.toPermHom _ _

/-- This is an actual action image; no abstract group of order twenty is substituted. -/
noncomputable def fiveQuartetImage : Subgroup (Equiv.Perm FiveQuartets) := fiveQuartetHom.range

theorem fiveQuartet_reference_transport (Q : FiveQuartets) :
    ∃g : pairStabilizer,g • referenceQuartet=Q := by
  obtain ⟨g,hg⟩ := coupleFusion_reference_quartet_transport Q.val Q.prop.1 Q.prop.2
  exact ⟨coupleProjection g,Subtype.ext hg⟩

noncomputable instance fiveQuartetsTransitive : MulAction.IsPretransitive pairStabilizer FiveQuartets where
  exists_smul_eq Q R := by
    obtain ⟨g,hg⟩ := fiveQuartet_reference_transport Q
    obtain ⟨h,hh⟩ := fiveQuartet_reference_transport R
    exact ⟨h*g⁻¹,by rw [mul_smul,←hg,inv_smul_smul,hh]⟩

theorem referenceQuartet_stabilizer_eq_monomial :
    MulAction.stabilizer pairStabilizer referenceQuartet=monomialPairGroup := by
  apply le_antisymm
  · intro g hg
    obtain ⟨a,ha⟩ := coupleProjection_surjective g
    have he : gaussianImage a.val (coordinateRowFrame (rowLabel 0))=
        coordinateRowFrame (rowLabel 0) := by
      have h : coupleProjection a • referenceQuartet=referenceQuartet := by
        rw [ha];exact hg
      exact congrArg Subtype.val h
    obtain ⟨k,hk⟩ := gaussian_coordinateRow_stabilizer_le_code a.val (rowLabel 0) he
    have hp : k∈codeCoupleStabilizer := by
      constructor
      · have h := (coupleFusionGroup_fix a).1
        rw [←hk,codeGaussianHom_cross] at h
        exact h
      · have h := (coupleFusionGroup_fix a).2
        rw [←hk,codeGaussianHom_cross] at h
        exact h
    refine ⟨⟨k,hp⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (QuotientGroup.mk (codeGaussianHom k) : RudvalisGroup)=g.val.val
    rw [hk]
    exact congrArg (fun z : pairStabilizer=>z.val.val) ha
  · rintro g ⟨k,rfl⟩
    change codePairHom k • referenceQuartet=referenceQuartet
    apply Subtype.ext
    change gaussianImage (codeGaussianHom k.val) (coordinateRowFrame (rowLabel 0))=
      coordinateRowFrame (rowLabel 0)
    rw [coordinateRowFrame_code_image]
    have h := k.prop.1
    change k.val • localReferenceCross=localReferenceCross at h
    rw [localReferenceCross_eq,coordinateCross_action] at h
    have hr := coordinateCross_row_of_eq h
    rw [codeRowImage_coordinates] at hr
    rw [hr]

theorem cardFiveQuartetStabilizer :
    Nat.card (MulAction.stabilizer pairStabilizer referenceQuartet)=4096 := by
  rw [referenceQuartet_stabilizer_eq_monomial,cardMonomialPairGroup]

end Atlas.Tits
